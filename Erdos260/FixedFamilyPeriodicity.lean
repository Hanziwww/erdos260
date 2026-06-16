import Erdos260.DensityBootstrap

/-!
# Fixed-family periodicity: the orbit-to-word dictionary at the five surviving data

This module (NEW; it edits no existing file) works the supply side of the manuscript's
section-24.3 fixed-cycle instantiation (subsection "Fixed-cycle instantiation of
Proposition 24.3" + the E.7 remark "(band-saturated fixed cycles)"): the transcription of
the E.6/E.7 unique clean continuation from the ORBIT language (`slopeOrbit`, `canonGap`)
into WORD periodicity (`WindowPeriodic`) at the five surviving fixed data
`(q, K₀) ∈ {(3,1), (21,3), (15,1), (15,2), (105,7)}` — the missing atom named
`DeepFixedFamilyWindowPeriodicity` in `DensityBootstrap.lean`, whose payoff side
(`pinnedValue_windowPeriodic_void`) is already machine-verified.

## THE ORBIT-TO-WORD DICTIONARY VERDICT (exact)

The in-tree formalization carries NO unconditional identification between the canonical
gaps of the recurrent slope orbit and the actual hit gaps of the digit word:

* The fixed-family hit (`FixedFamilyHit`) is a property of the DATUM `(q, K₀)` of the
  constructed `CarryAPSubfibre` (`class1SlopeDatum`) alone; the orbit
  `slopeOrbit q K₀` is autonomous (iterated `boundedSlopeStep`), never driven by `d`.
* The fibre memberships (`mem_class1Fibre_iff`, `mem_class4Fibre_iff`) tie, at the SHARED
  index `k` only, an orbit-side band pin `canonGap q K_k = band` to a word-side
  gap-WINDOW pin on `gapWindow (hitGap a) k r` — a constraint on the SUM of `r + 1`
  consecutive hit gaps, never on an individual gap.  Even at the pinned index no per-gap
  identity `hitGap a k = canonGap q K_k` exists in the model.
* The ONLY formalized hit/orbit bridge is the conditional
  `integerCarry_realizes_boundedSlopeStep` / `carry_tracks_slopeOrbit`
  (`TowerCycleRealization` / `TowerAPSubfibreLanding`), whose hypothesis demands the
  actual digits be ZERO across every canonical gap `(N_j, N_j + g_j]` of the orbit —
  INCLUDING the right endpoints `N_{j+1}`.

**The decisive new negative (PROVED here):** since `canonGap ≥ 1`, the intervals
`(N_j, N_{j+1}]` tile `(N₀, ∞)`, so the full zero-run hypothesis forces the word to
TERMINATE (`eventuallyZero_of_gapOrbit_zeroRun`) — contradicting the non-termination
`ctx.hnonterm` carried by EVERY actual failure context.  Hence the wave-2..5 conditional
bridge is not merely ungrounded at the fixed data: its hypothesis class is EMPTY at every
actual context (`actual_zeroRun_void`, `carry_tracks_hzero_void`,
`classOneDatum_zeroRun_void`).  The zero-run condition is therefore NOT what the
fixed-cycle E.6 uniqueness supplies — E.6/E.7's clean continuation pins ONES at the cycle
returns (the `−Q·y_s` term of the labelled-fibre transition E.11), exactly the positions
the formalized zero-run forbids.  The formalized bridge reads E.11 with `d ≡ 0` (pure
carry doubling mod `q`, where the `−q` of `boundedSlopeStep` is invisible); the manuscript
chain needs E.11 with hits AT the gap ends (where the `−q` is real).  These are different
transcriptions, and only the first exists in tree.

## What IS proved here (all unconditional, no fabrication)

### The orbit side of the dictionary is COMPLETE at the five data

At each surviving pair the recurrent band is computed and the orbit-tracked positions
form an exact arithmetic progression:

* bands: `(3,1) ↦ 2`, `(21,3) ↦ 3`, `(15,1) ↦ 4`, `(15,2) ↦ 4` (from index 1; the
  pre-period base reads band 3), `(105,7) ↦ 4` (`fixedFamilyBand_*`,
  `fixedFamilyRecurrentBand_bounds`: the band is always in `{2, 3, 4}`);
* orbit constancy: `slopeOrbit_fifteen_one_const`, `slopeOrbit_fifteen_two_tail`,
  `slopeOrbit_oneOhFive_seven_const` (NEW; `(3,1)`/`(21,3)` were in tree);
* the AP forms: `gapOrbit_three_one` (`N₀ + 2j`), `gapOrbit_twentyone_three`
  (`N₀ + 3j`), `gapOrbit_fifteen_one` (`N₀ + 4j`), `gapOrbit_fifteen_two`
  (`N₀ + 3 + 4j` from index 1), `gapOrbit_oneOhFive_seven` (`N₀ + 4j`).

So ONLY the identification of the hit positions with these APs is missing — the word side.

### The word side: the formalizable half of the conjectured dictionary, PROVED

"Constant orbit ⟹ all subsequent hit gaps equal `g` ⟹ the hit positions are an AP ⟹ the
word is eventually `g`-periodic": the second and third implications are pure
combinatorics of the hit enumeration and are proved outright —

* `hitSequence_succ_of_const_gaps` / `hitSequence_AP_of_const_gaps`: constant gaps from
  `k₀` make `a (k₀ + m) = a k₀ + m·g` exactly;
* `digit_periodic_of_const_gaps`: then `d (n + g) = d n` for EVERY `n > a k₀` — exact
  word periodicity (both digit values, via completeness of the enumeration).

The FIRST implication ("fixed datum ⟹ the actual hit gaps are eventually the band") is
the genuine E.6/E.7 content and is exactly what remains.

### The sharpest named bridge and the conditional chain

* `FixedFamilyCleanContinuation ctx` — the E.6/E.7 unique-clean-continuation transcribed
  to the word: some hit index `k₀` with window-compatible onset `a k₀ ≤ X` has ALL later
  hit gaps equal to the recurrent band of the datum.
* `DeepFixedFamilyCleanContinuation` — demanded only at `X > 2^493443` on fixed-family
  hits.  Under it: `windowPeriodic_of_cleanContinuation` (the supply),
  `deepFixedFamilyWindowPeriodicity_of_cleanContinuation` (discharges the bootstrap
  successor Prop), `fixedFamilyHit_void_of_cleanContinuation` (ALL FIVE families void at
  every scale), per-family voidings, and the collapsed surfaces
  `towerEscapeLever_of_cleanContinuation` (the `(105,7)` branch leaves `TowerEscape`),
  `towerFixedPointResidual_of_cleanContinuation`.

### The honest no-free-lunch characterization

`pinnedValue_windowPeriodic_void` makes ANY supply of window periodicity at the pinned
families logically equivalent to the voiding it feeds:
`deepFixedFamilyWindowPeriodicity_iff_void`, `deepFixedFamilyCleanContinuation_iff_void`,
`deepFixedFamilyCleanContinuation_iff_windowPeriodicity` (one direction is the chain
above; the other is vacuity, because the voiding empties the hypothesis class — the same
phenomenon `TailMatchSupply` proved for the tail-match Props).  The clean-continuation
Prop is therefore not a waypoint but the exact manuscript-language form of the residual:
what would supply it is the FULL Appendix-E machinery behind E.6 outgoing-uniqueness
(labelled towers, the dirty package P4, the run package L.4, the tower-exit estimates
L.3/M.5) — a hit-to-hit carry analysis `R_{a(k+1)} = 2^{hitGap} R_{a k} − Q·a(k+1)`
forcing the next gap to be the canonical band while the recurrence persists, which no
in-tree lemma performs.

No `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 1.  The orbit side at the five data: bands, constancy, and the exact APs -/

/-- `canonGap 3 1 = 2` (band 2: `3 < 2²·1 < 6`). -/
theorem fixedCycleGap_3_1 : canonGap 3 1 = 2 :=
  canonGap_eval (g := 1) (by norm_num) (by norm_num) (by norm_num)

/-- `canonGap 21 3 = 3` (band 3: `21 < 2³·3 < 42`). -/
theorem fixedCycleGap_21_3 : canonGap 21 3 = 3 :=
  canonGap_eval (g := 2) (by norm_num) (by norm_num) (by norm_num)

/-- `canonGap 15 1 = 4` (band 4: `15 < 2⁴·1 < 30`). -/
theorem fixedCycleGap_15_1 : canonGap 15 1 = 4 :=
  canonGap_eval (g := 3) (by norm_num) (by norm_num) (by norm_num)

/-- `canonGap 15 2 = 3` (the pre-period base of `(15,2)` reads band 3). -/
theorem fixedCycleGap_15_2 : canonGap 15 2 = 3 :=
  canonGap_eval (g := 2) (by norm_num) (by norm_num) (by norm_num)

/-- `canonGap 105 7 = 4` (band 4: `105 < 2⁴·7 < 210`). -/
theorem fixedCycleGap_105_7 : canonGap 105 7 = 4 :=
  canonGap_eval (g := 3) (by norm_num) (by norm_num) (by norm_num)

/-- The E.13 step fixes `1` at `q = 15`: `2⁴·1 − 15 = 1`. -/
theorem fixedCycleStep_15_1 : boundedSlopeStep 15 1 = 1 := by
  unfold boundedSlopeStep
  rw [fixedCycleGap_15_1]
  norm_num

/-- The E.13 step at `q = 15` sends the even base `2 ↦ 1`: `2³·2 − 15 = 1`. -/
theorem fixedCycleStep_15_2 : boundedSlopeStep 15 2 = 1 := by
  unfold boundedSlopeStep
  rw [fixedCycleGap_15_2]
  norm_num

/-- The E.13 step fixes `7` at `q = 105`: `2⁴·7 − 105 = 7`. -/
theorem fixedCycleStep_105_7 : boundedSlopeStep 105 7 = 7 := by
  unfold boundedSlopeStep
  rw [fixedCycleGap_105_7]
  norm_num

/-- **The `(15, 1)` orbit is CONSTANT**: `K_j = 1` at every index. -/
theorem slopeOrbit_fifteen_one_const : ∀ j, slopeOrbit 15 1 j = 1 := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
      show boundedSlopeStep 15 (slopeOrbit 15 1 j) = 1
      rw [ih]
      exact fixedCycleStep_15_1

/-- **The `(15, 2)` orbit is constant `1` from index `1`** (the even base has a one-step
pre-period `2 ↦ 1`). -/
theorem slopeOrbit_fifteen_two_tail : ∀ j, slopeOrbit 15 2 (j + 1) = 1 := by
  intro j
  induction j with
  | zero =>
      show boundedSlopeStep 15 (slopeOrbit 15 2 0) = 1
      rw [show slopeOrbit 15 2 0 = 2 from rfl]
      exact fixedCycleStep_15_2
  | succ j ih =>
      show boundedSlopeStep 15 (slopeOrbit 15 2 (j + 1)) = 1
      rw [ih]
      exact fixedCycleStep_15_1

/-- **The `(105, 7)` orbit is CONSTANT**: `K_j = 7` at every index. -/
theorem slopeOrbit_oneOhFive_seven_const : ∀ j, slopeOrbit 105 7 j = 7 := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
      show boundedSlopeStep 105 (slopeOrbit 105 7 j) = 7
      rw [ih]
      exact fixedCycleStep_105_7

/-- The recurrent band of `(3, 1)` is `2`. -/
theorem fixedFamilyBand_3_1 : canonGap 3 (slopeOrbit 3 1 1) = 2 := by
  rw [slopeOrbit_three_one_const 1]
  exact fixedCycleGap_3_1

/-- The recurrent band of `(21, 3)` is `3`. -/
theorem fixedFamilyBand_21_3 : canonGap 21 (slopeOrbit 21 3 1) = 3 := by
  rw [slopeOrbit_twentyone_three_const 1]
  exact fixedCycleGap_21_3

/-- The recurrent band of `(15, 1)` is `4`. -/
theorem fixedFamilyBand_15_1 : canonGap 15 (slopeOrbit 15 1 1) = 4 := by
  rw [slopeOrbit_fifteen_one_const 1]
  exact fixedCycleGap_15_1

/-- The recurrent band of `(15, 2)` is `4` (read at index `1`, past the pre-period). -/
theorem fixedFamilyBand_15_2 : canonGap 15 (slopeOrbit 15 2 1) = 4 := by
  rw [slopeOrbit_fifteen_two_tail 0]
  exact fixedCycleGap_15_1

/-- The recurrent band of `(105, 7)` is `4`. -/
theorem fixedFamilyBand_105_7 : canonGap 105 (slopeOrbit 105 7 1) = 4 := by
  rw [slopeOrbit_oneOhFive_seven_const 1]
  exact fixedCycleGap_105_7

/-- **The `(3,1)` tracked positions are the exact AP `N₀ + 2j`** — the orbit side of the
dictionary at band 2 is complete; only the identification with hit positions is missing. -/
theorem gapOrbit_three_one (N₀ : ℕ) : ∀ j, gapOrbit 3 1 N₀ j = N₀ + 2 * j := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
      have hstep : gapOrbit 3 1 N₀ (j + 1)
          = gapOrbit 3 1 N₀ j + canonGap 3 (slopeOrbit 3 1 j) := rfl
      rw [hstep, ih, slopeOrbit_three_one_const j, fixedCycleGap_3_1]
      omega

/-- The `(21,3)` tracked positions are the exact AP `N₀ + 3j`. -/
theorem gapOrbit_twentyone_three (N₀ : ℕ) : ∀ j, gapOrbit 21 3 N₀ j = N₀ + 3 * j := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
      have hstep : gapOrbit 21 3 N₀ (j + 1)
          = gapOrbit 21 3 N₀ j + canonGap 21 (slopeOrbit 21 3 j) := rfl
      rw [hstep, ih, slopeOrbit_twentyone_three_const j, fixedCycleGap_21_3]
      omega

/-- The `(15,1)` tracked positions are the exact AP `N₀ + 4j`. -/
theorem gapOrbit_fifteen_one (N₀ : ℕ) : ∀ j, gapOrbit 15 1 N₀ j = N₀ + 4 * j := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
      have hstep : gapOrbit 15 1 N₀ (j + 1)
          = gapOrbit 15 1 N₀ j + canonGap 15 (slopeOrbit 15 1 j) := rfl
      rw [hstep, ih, slopeOrbit_fifteen_one_const j, fixedCycleGap_15_1]
      omega

/-- The `(15,2)` tracked positions are the exact AP `N₀ + 3 + 4j` from index `1` (the
pre-period contributes the band-3 first gap). -/
theorem gapOrbit_fifteen_two (N₀ : ℕ) :
    ∀ j, gapOrbit 15 2 N₀ (j + 1) = N₀ + 3 + 4 * j := by
  intro j
  induction j with
  | zero =>
      have hstep : gapOrbit 15 2 N₀ 1
          = gapOrbit 15 2 N₀ 0 + canonGap 15 (slopeOrbit 15 2 0) := rfl
      rw [hstep, show gapOrbit 15 2 N₀ 0 = N₀ from rfl,
        show slopeOrbit 15 2 0 = 2 from rfl, fixedCycleGap_15_2]
  | succ j ih =>
      have hstep : gapOrbit 15 2 N₀ (j + 1 + 1)
          = gapOrbit 15 2 N₀ (j + 1) + canonGap 15 (slopeOrbit 15 2 (j + 1)) := rfl
      rw [hstep, ih, slopeOrbit_fifteen_two_tail j, fixedCycleGap_15_1]
      omega

/-- The `(105,7)` tracked positions are the exact AP `N₀ + 4j`. -/
theorem gapOrbit_oneOhFive_seven (N₀ : ℕ) : ∀ j, gapOrbit 105 7 N₀ j = N₀ + 4 * j := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
      have hstep : gapOrbit 105 7 N₀ (j + 1)
          = gapOrbit 105 7 N₀ j + canonGap 105 (slopeOrbit 105 7 j) := rfl
      rw [hstep, ih, slopeOrbit_oneOhFive_seven_const j, fixedCycleGap_105_7]
      omega

/-! ## Part 2.  The zero-run refutation: the wave-2..5 conditional bridge is EMPTY at
every actual context

The hypothesis of `carry_tracks_slopeOrbit` (the only formalized hit/orbit bridge,
restating `integerCarry_realizes_boundedSlopeStep` along the orbit) demands `d i = 0` on
every interval `(N_j, N_j + g_j]` with `N_{j+1} = N_j + g_j` and `g_j = canonGap ≥ 1`.
These intervals tile `(N₀, ∞)`, so the hypothesis forces the word to terminate — which
`ctx.hnonterm` forbids.  The bridge hypothesis is NOT the E.6/E.7 clean continuation
(that one pins ones AT the tracked positions); it is its all-zero degeneration, and it is
unsatisfiable on every actual failing context. -/

/-- The tracked positions grow at least linearly: `N₀ + j ≤ gapOrbit q K₀ N₀ j`
(`canonGap ≥ 1` at every step). -/
theorem gapOrbit_ge (q K₀ N₀ : ℕ) : ∀ j, N₀ + j ≤ gapOrbit q K₀ N₀ j := by
  intro j
  induction j with
  | zero => exact Nat.le_refl N₀
  | succ j ih =>
      have hstep : gapOrbit q K₀ N₀ (j + 1)
          = gapOrbit q K₀ N₀ j + canonGap q (slopeOrbit q K₀ j) := rfl
      have hpos := canonGap_pos q (slopeOrbit q K₀ j)
      omega

/-- **The canonical-gap intervals tile the ray**: the zero-run hypothesis of
`carry_tracks_slopeOrbit` (digits zero on every `(N_j, N_j + g_j]`) forces the whole word
to vanish beyond `N₀` — i.e. the word TERMINATES. -/
theorem eventuallyZero_of_gapOrbit_zeroRun {q K₀ N₀ : ℕ} {d : ℕ → ℕ}
    (hzero : ∀ j i : ℕ, gapOrbit q K₀ N₀ j < i →
      i ≤ gapOrbit q K₀ N₀ j + canonGap q (slopeOrbit q K₀ j) → d i = 0) :
    EventuallyZero d := by
  have hcover : ∀ j, ∀ i, N₀ < i → i ≤ gapOrbit q K₀ N₀ j → d i = 0 := by
    intro j
    induction j with
    | zero =>
        intro i hi1 hi2
        exfalso
        have h00 : gapOrbit q K₀ N₀ 0 = N₀ := rfl
        omega
    | succ j ih =>
        intro i hi1 hi2
        by_cases hle : i ≤ gapOrbit q K₀ N₀ j
        · exact ih i hi1 hle
        · push Not at hle
          refine hzero j i hle ?_
          have hstep : gapOrbit q K₀ N₀ (j + 1)
              = gapOrbit q K₀ N₀ j + canonGap q (slopeOrbit q K₀ j) := rfl
          omega
  refine ⟨N₀ + 1, fun n hn => ?_⟩
  have hge := gapOrbit_ge q K₀ N₀ n
  exact hcover n n (by omega) (by omega)

/-- **THE BRIDGE-HYPOTHESIS VOIDING**: at EVERY actual failure context, for EVERY datum
`(q, K₀)` and every base position `N₀`, the canonical-gap zero-run hypothesis is FALSE
(the context's word is non-terminating, `ctx.hnonterm`). -/
theorem actual_zeroRun_void (ctx : ActualFailureContext) (q K₀ N₀ : ℕ)
    (hzero : ∀ j i : ℕ, gapOrbit q K₀ N₀ j < i →
      i ≤ gapOrbit q K₀ N₀ j + canonGap q (slopeOrbit q K₀ j) → ctx.d i = 0) :
    False :=
  ctx.hnonterm (eventuallyZero_of_gapOrbit_zeroRun hzero)

/-- **The `carry_tracks_slopeOrbit` hypothesis class is EMPTY at actual contexts**: for
every AP-subfibre datum `S` of the context's `(Q, P)`, the zero-run hypothesis `hzero`
of `carry_tracks_slopeOrbit` is refutable.  The conditional bridge of waves 2–5 can
never fire on an actual failing shell — it is the WRONG transcription of E.6/E.7 (the
clean continuation pins ones AT the cycle returns; the zero-run forbids them all). -/
theorem carry_tracks_hzero_void (ctx : ActualFailureContext) (P : ℤ)
    (S : CarryAPSubfibre ctx.shell.Q P)
    (hzero : ∀ j i : ℕ, gapOrbit S.q S.K₀ 0 j < i →
      i ≤ gapOrbit S.q S.K₀ 0 j + canonGap S.q (slopeOrbit S.q S.K₀ j) →
      ctx.shell.d i = 0) :
    False :=
  actual_zeroRun_void ctx S.q S.K₀ 0 hzero

/-- The bridge-hypothesis voiding at the ACTUAL routed datum (`class1SlopeDatum`) — in
particular at all five fixed families. -/
theorem classOneDatum_zeroRun_void (ctx : ActualFailureContext)
    (hzero : ∀ j i : ℕ,
      gapOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 0 j < i →
      i ≤ gapOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 0 j
          + canonGap (class1SlopeDatum ctx).q
              (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) →
      ctx.shell.d i = 0) :
    False :=
  actual_zeroRun_void ctx (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 0 hzero

/-! ## Part 3.  The word side: constant hit gaps force exact periodicity (PROVED)

The formalizable half of the conjectured dictionary: IF all hit gaps beyond an index are
the constant `g`, the hit positions are an exact AP and the word is exactly `g`-periodic
past the onset.  Pure combinatorics of the strictly-increasing complete enumeration. -/

/-- Constant gaps step the enumeration additively: `a (k+1) = a k + g` for `k ≥ k₀`. -/
theorem hitSequence_succ_of_const_gaps {d a : ℕ → ℕ} (hseq : HitSequence d a)
    {k₀ g : ℕ} (hg : ∀ k, k₀ ≤ k → hitGap a k = g) :
    ∀ k, k₀ ≤ k → a (k + 1) = a k + g := by
  intro k hk
  have hlt : a k < a (k + 1) := hseq.strict (Nat.lt_succ_self k)
  have hgap := hg k hk
  unfold hitGap at hgap
  omega

/-- **Constant gaps make the hit positions an exact AP**: `a (k₀ + m) = a k₀ + m·g`. -/
theorem hitSequence_AP_of_const_gaps {d a : ℕ → ℕ} (hseq : HitSequence d a)
    {k₀ g : ℕ} (hg : ∀ k, k₀ ≤ k → hitGap a k = g) :
    ∀ m, a (k₀ + m) = a k₀ + m * g := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      have hsucc := hitSequence_succ_of_const_gaps hseq hg (k₀ + m) (Nat.le_add_right _ _)
      have hidx : k₀ + (m + 1) = (k₀ + m) + 1 := by omega
      rw [hidx, hsucc, ih]
      ring

/-- **Constant hit gaps force EXACT word periodicity past the onset**: if every hit gap
from index `k₀` equals `g`, then `d (n + g) = d n` for every `n > a k₀` (ones map to ones
along the AP; zeros map to zeros by completeness of the enumeration). -/
theorem digit_periodic_of_const_gaps {d a : ℕ → ℕ} (hd : BinaryDigits d)
    (hseq : HitSequence d a) {k₀ g : ℕ} (hg : ∀ k, k₀ ≤ k → hitGap a k = g) :
    ∀ n, a k₀ < n → d (n + g) = d n := by
  intro n hn
  have hsucc := hitSequence_succ_of_const_gaps hseq hg
  rcases hd n with h0 | h1
  · rcases hd (n + g) with h0' | h1'
    · rw [h0', h0]
    · exfalso
      obtain ⟨k, hk⟩ := hseq.complete (n + g) h1'
      have hk01 : a (k₀ + 1) = a k₀ + g := hsucc k₀ le_rfl
      have hgt : a (k₀ + 1) < a k := by omega
      have hkgt : k₀ + 1 < k := hseq.strict.lt_iff_lt.mp hgt
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hj : k₀ ≤ j := by omega
      have hstep : a (j + 1) = a j + g := hsucc j hj
      have hna : n = a j := by omega
      have hhit := hseq.hit j
      rw [hna] at h0
      omega
  · obtain ⟨k, hk⟩ := hseq.complete n h1
    have hkgt : k₀ < k := hseq.strict.lt_iff_lt.mp (by omega : a k₀ < a k)
    have hstep : a (k + 1) = a k + g := hsucc k (Nat.le_of_lt hkgt)
    have hhit := hseq.hit (k + 1)
    rw [h1]
    rwa [show a (k + 1) = n + g from by omega] at hhit

/-! ## Part 4.  The sharpest named bridge: the E.6/E.7 clean continuation, word-side -/

/-- The recurrent band of the actual datum: the canonical gap read at orbit index `1`
(past the at-most-one-step pre-period — exactly where the five fixed cycles live). -/
def fixedFamilyRecurrentBand (ctx : ActualFailureContext) : ℕ :=
  canonGap (class1SlopeDatum ctx).q
    (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 1)

/-- **At every fixed-family hit the recurrent band is in `{2, 3, 4}`** — the five data
read bands `2, 3, 4, 4, 4`, so the would-be word period is at most `4`. -/
theorem fixedFamilyRecurrentBand_bounds (ctx : ActualFailureContext)
    (hhit : FixedFamilyHit ctx) :
    2 ≤ fixedFamilyRecurrentBand ctx ∧ fixedFamilyRecurrentBand ctx ≤ 4 := by
  unfold fixedFamilyRecurrentBand
  rcases hhit with ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ <;> rw [hq, hK]
  · rw [fixedFamilyBand_3_1]; omega
  · rw [fixedFamilyBand_21_3]; omega
  · rw [fixedFamilyBand_15_1]; omega
  · rw [fixedFamilyBand_15_2]; omega
  · rw [fixedFamilyBand_105_7]; omega

/-- **The E.6/E.7 unique clean continuation, transcribed to the word**: some hit index
`k₀` of the context's canonical hit enumeration has window-compatible onset
(`a k₀ ≤ X`) and ALL LATER HIT GAPS EQUAL TO THE RECURRENT BAND of the datum.  This is
the exact supply statement of the manuscript's fixed-cycle instantiation of
Proposition 24.3: "while the recurrence persists, the word is pinned to the periodic
continuation of the cycle block". -/
def FixedFamilyCleanContinuation (ctx : ActualFailureContext) : Prop :=
  ∃ k₀ : ℕ, ctx.n24CarryData.a k₀ ≤ ctx.X ∧
    ∀ k, k₀ ≤ k → hitGap ctx.n24CarryData.a k = fixedFamilyRecurrentBand ctx

/-- **The supply theorem**: at a fixed-family hit on a scale `X ≥ 8`, the clean
continuation yields window periodicity outright (period = the recurrent band `≤ 4`,
onset = the continuation onset). -/
theorem windowPeriodic_of_cleanContinuation (ctx : ActualFailureContext)
    (hhit : FixedFamilyHit ctx) (hX8 : 8 ≤ ctx.X)
    (hcc : FixedFamilyCleanContinuation ctx) : WindowPeriodic ctx := by
  obtain ⟨k₀, honset, hg⟩ := hcc
  obtain ⟨hb2, hb4⟩ := fixedFamilyRecurrentBand_bounds ctx hhit
  have hseq : HitSequence ctx.d ctx.n24CarryData.a := ctx.n24CarryData.carry.hits
  exact ⟨ctx.n24CarryData.a k₀, fixedFamilyRecurrentBand ctx, honset, by omega, by omega,
    digit_periodic_of_const_gaps ctx.hd hseq hg⟩

/-- **The deep clean-continuation successor** (one Prop for all five families): every
DEEP (`X > 2^493443`) fixed-family context has the E.6/E.7 clean continuation. -/
def DeepFixedFamilyCleanContinuation : Prop :=
  ∀ ctx : ActualFailureContext, 2 ^ 493443 < ctx.X → FixedFamilyHit ctx →
    FixedFamilyCleanContinuation ctx

/-- A deep scale is at least `8` (`2³ ≤ 2^493443 < X`). -/
theorem eight_le_of_deepScale {X : ℕ} (hX : 2 ^ 493443 < X) : 8 ≤ X := by
  have hle : (2 : ℕ) ^ 3 ≤ 2 ^ 493443 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have h8 : (8 : ℕ) = 2 ^ 3 := by norm_num
  omega

/-- **The clean continuation discharges the bootstrap successor Prop**
`DeepFixedFamilyWindowPeriodicity` — the missing supply atom of `DensityBootstrap`. -/
theorem deepFixedFamilyWindowPeriodicity_of_cleanContinuation
    (h : DeepFixedFamilyCleanContinuation) : DeepFixedFamilyWindowPeriodicity :=
  fun ctx hX hhit =>
    windowPeriodic_of_cleanContinuation ctx hhit (eight_le_of_deepScale hX) (h ctx hX hhit)

/-- **Under the clean continuation ALL FIVE fixed families are void at EVERY scale**
(deep scales by the section-24 floor, shallow scales by the wave-6/8 rigidity). -/
theorem fixedFamilyHit_void_of_cleanContinuation (h : DeepFixedFamilyCleanContinuation)
    (ctx : ActualFailureContext) : ¬ FixedFamilyHit ctx :=
  fixedFamilyHit_void_of_windowPeriodicity
    (deepFixedFamilyWindowPeriodicity_of_cleanContinuation h) ctx

/-- The clean continuation discharges the wave-6 deep family voiding Prop. -/
theorem deepFixedFamilyVoid_of_cleanContinuation (h : DeepFixedFamilyCleanContinuation) :
    DeepFixedFamilyVoid :=
  deepFixedFamilyVoid_of_windowPeriodicity
    (deepFixedFamilyWindowPeriodicity_of_cleanContinuation h)

/-- Band-2 `(3,1)` void under the clean continuation. -/
theorem returnFixedFamily_void_of_cleanContinuation
    (h : DeepFixedFamilyCleanContinuation) (ctx : ActualFailureContext) :
    ¬((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1) :=
  fun hh => fixedFamilyHit_void_of_cleanContinuation h ctx (Or.inl hh)

/-- Band-3 `(21,3)` void under the clean continuation. -/
theorem densePackFixedFamily_void_of_cleanContinuation
    (h : DeepFixedFamilyCleanContinuation) (ctx : ActualFailureContext) :
    ¬((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3) :=
  fun hh => fixedFamilyHit_void_of_cleanContinuation h ctx (Or.inr (Or.inl hh))

/-- Band-4 `(15,1)` void under the clean continuation. -/
theorem towerFP15_1Family_void_of_cleanContinuation
    (h : DeepFixedFamilyCleanContinuation) (ctx : ActualFailureContext) :
    ¬((class1SlopeDatum ctx).q = 15 ∧ (class1SlopeDatum ctx).K₀ = 1) :=
  fun hh => fixedFamilyHit_void_of_cleanContinuation h ctx (Or.inr (Or.inr (Or.inl hh)))

/-- Band-4 `(15,2)` void under the clean continuation. -/
theorem towerFP15_2Family_void_of_cleanContinuation
    (h : DeepFixedFamilyCleanContinuation) (ctx : ActualFailureContext) :
    ¬((class1SlopeDatum ctx).q = 15 ∧ (class1SlopeDatum ctx).K₀ = 2) :=
  fun hh =>
    fixedFamilyHit_void_of_cleanContinuation h ctx (Or.inr (Or.inr (Or.inr (Or.inl hh))))

/-- Band-4 `(105,7)` void under the clean continuation. -/
theorem towerFP105Family_void_of_cleanContinuation
    (h : DeepFixedFamilyCleanContinuation) (ctx : ActualFailureContext) :
    ¬((class1SlopeDatum ctx).q = 105 ∧ (class1SlopeDatum ctx).K₀ = 7) :=
  fun hh =>
    fixedFamilyHit_void_of_cleanContinuation h ctx (Or.inr (Or.inr (Or.inr (Or.inr hh))))

/-- **The collapsed tower escape surface**: under the clean continuation the `(105, 7)`
branch leaves `TowerEscape` (the surface shrinks to `TowerEscapeLever`). -/
theorem towerEscapeLever_of_cleanContinuation (h : DeepFixedFamilyCleanContinuation)
    (ctx : ActualFailureContext) (hesc : TowerEscape ctx) : TowerEscapeLever ctx :=
  towerEscapeLever_of_towerEscape_deepFamilies
    (deepFixedFamilyVoid_of_cleanContinuation h) ctx hesc

/-- The tower capstone field bridge under the clean continuation: the lever residual
rebuilds the full wave-4 `TowerFixedPointResidual`. -/
theorem towerFixedPointResidual_of_cleanContinuation
    (h : DeepFixedFamilyCleanContinuation) (hres : TowerLeverResidual) :
    TowerFixedPointResidual :=
  towerFixedPointResidual_of_deepFamilies (deepFixedFamilyVoid_of_cleanContinuation h) hres

/-! ## Part 5.  The honest no-free-lunch equivalences

`pinnedValue_windowPeriodic_void` voids every window-periodic pinned context, so the
supply Props are logically EQUIVALENT to the voidings they feed: the forward directions
are the chains above, the backward directions are vacuity (the voiding empties the
hypothesis class).  The clean continuation is therefore not a waypoint — it is the exact
manuscript-language form of the residual itself. -/

/-- `DeepFixedFamilyWindowPeriodicity` is EQUIVALENT to the deep family voiding (the
backward direction was missing in tree; the Prop is exactly as strong as the voiding). -/
theorem deepFixedFamilyWindowPeriodicity_iff_void :
    DeepFixedFamilyWindowPeriodicity ↔ DeepFixedFamilyVoid := by
  constructor
  · exact deepFixedFamilyVoid_of_windowPeriodicity
  · intro hvoid ctx hX hhit
    exact absurd hhit (hvoid ctx hX)

/-- `DeepFixedFamilyCleanContinuation` is EQUIVALENT to the deep family voiding. -/
theorem deepFixedFamilyCleanContinuation_iff_void :
    DeepFixedFamilyCleanContinuation ↔ DeepFixedFamilyVoid := by
  constructor
  · exact deepFixedFamilyVoid_of_cleanContinuation
  · intro hvoid ctx hX hhit
    exact absurd hhit (hvoid ctx hX)

/-- The two supply Props have identical strength. -/
theorem deepFixedFamilyCleanContinuation_iff_windowPeriodicity :
    DeepFixedFamilyCleanContinuation ↔ DeepFixedFamilyWindowPeriodicity := by
  rw [deepFixedFamilyCleanContinuation_iff_void, deepFixedFamilyWindowPeriodicity_iff_void]

/-! ## Part 6.  Machine-readable status (honest) -/

/-- The precise status of the fixed-family orbit-to-word dictionary after this module. -/
def fixedFamilyPeriodicityStatus : List String :=
  [ "DICTIONARY VERDICT (exact): the formalization carries NO unconditional " ++
      "identification between canonGap along the slope orbit and hitGap of the actual " ++
      "word.  FixedFamilyHit constrains only the autonomous datum (q, K0); the fibre " ++
      "memberships (mem_class1Fibre_iff / mem_class4Fibre_iff) pin, at the shared index " ++
      "k only, the orbit band AND a gap-WINDOW SUM (gapWindow (hitGap a) k r), never an " ++
      "individual hit gap.  The only hit/orbit bridge in tree is the conditional " ++
      "integerCarry_realizes_boundedSlopeStep / carry_tracks_slopeOrbit.",
    "THE BRIDGE HYPOTHESIS IS REFUTED AT EVERY ACTUAL CONTEXT (NEW, decisive): the " ++
      "canonical-gap zero-run hzero demands d = 0 on every (N_j, N_j + g_j] INCLUDING " ++
      "the tracked endpoints; canonGap >= 1 makes these intervals tile (N0, infinity), " ++
      "so hzero forces EventuallyZero d (eventuallyZero_of_gapOrbit_zeroRun), " ++
      "contradicting ctx.hnonterm: actual_zeroRun_void / carry_tracks_hzero_void / " ++
      "classOneDatum_zeroRun_void.  Hence the wave-2..5 conditional bridge can NEVER " ++
      "fire on an actual shell: its hypothesis is NOT what E.6 uniqueness supplies (the " ++
      "clean continuation pins ONES at the cycle returns - the -Q*y term of E.11; the " ++
      "zero-run is the all-zero degeneration that forbids them).",
    "ORBIT SIDE COMPLETE AT THE FIVE DATA (NEW where missing): recurrent bands 2/3/4/4/4 " ++
      "(fixedFamilyBand_3_1/_21_3/_15_1/_15_2/_105_7, fixedFamilyRecurrentBand_bounds), " ++
      "orbit constancy at (15,1), (15,2) tail, (105,7) " ++
      "(slopeOrbit_fifteen_one_const, slopeOrbit_fifteen_two_tail, " ++
      "slopeOrbit_oneOhFive_seven_const), and the tracked positions are EXACT APs: " ++
      "gapOrbit_three_one (N0+2j), gapOrbit_twentyone_three (N0+3j), gapOrbit_fifteen_one " ++
      "(N0+4j), gapOrbit_fifteen_two (N0+3+4j from index 1), gapOrbit_oneOhFive_seven " ++
      "(N0+4j).  Only the identification of HIT positions with these APs is missing.",
    "WORD SIDE PROVED (the formalizable half of the dictionary): constant hit gaps from " ++
      "k0 make the hit positions an exact AP (hitSequence_succ_of_const_gaps, " ++
      "hitSequence_AP_of_const_gaps) and force EXACT word periodicity past the onset " ++
      "(digit_periodic_of_const_gaps: d(n+g) = d(n) for all n > a(k0), both digit values, " ++
      "via completeness of the hit enumeration).",
    "THE SHARPEST NAMED BRIDGE (the conditional chain, verdict (ii)): " ++
      "FixedFamilyCleanContinuation ctx - some hit index k0 with onset a(k0) <= X has ALL " ++
      "later hit gaps equal to the recurrent band of the datum (the exact word-side " ++
      "transcription of the manuscript's E.6/E.7 unique clean continuation).  Under " ++
      "DeepFixedFamilyCleanContinuation: windowPeriodic_of_cleanContinuation, " ++
      "deepFixedFamilyWindowPeriodicity_of_cleanContinuation (discharges the bootstrap " ++
      "successor), fixedFamilyHit_void_of_cleanContinuation (ALL FIVE families void at " ++
      "every scale; per-family forms returnFixedFamily_void_of_cleanContinuation etc.), " ++
      "towerEscapeLever_of_cleanContinuation (the (105,7) branch leaves TowerEscape), " ++
      "towerFixedPointResidual_of_cleanContinuation.",
    "NO FREE LUNCH (honest): pinnedValue_windowPeriodic_void makes every supply Prop " ++
      "equivalent to the voiding it feeds - deepFixedFamilyWindowPeriodicity_iff_void " ++
      "(backward direction NEW), deepFixedFamilyCleanContinuation_iff_void, " ++
      "deepFixedFamilyCleanContinuation_iff_windowPeriodicity.  The clean continuation " ++
      "is the manuscript-language form of the residual, not a strictly weaker waypoint.",
    "WHAT WOULD SUPPLY IT (honest characterization): a hit-to-hit carry analysis " ++
      "R_{a(k+1)} = 2^{hitGap k} * R_{a k} - Q * a(k+1) (integerCarry_succ_of_one + " ++
      "doubling across the interior zeros) showing that while the REAL carry stays in " ++
      "the E.14 recurrence window the next gap is forced to the canonical band - the " ++
      "E.6 outgoing-uniqueness, which rests on the unformalized Appendix-E machinery " ++
      "(labelled towers, dirty package P4, run package L.4, tower exits L.3/M.5).  The " ++
      "needed forcing is about the REAL carry magnitude, not its residue mod q: no " ++
      "mod-q argument can pin the gap, since doubling mod q is gap-blind.  NOT claimed.",
    "NOT CLOSED (honest): the five families are NOT voided unconditionally here; the " ++
      "deliverable is verdict (ii) - the sharpest named bridge plus the conditional " ++
      "chain plus the proof that the previously recorded zero-run bridge hypothesis is " ++
      "unsatisfiable at every actual context (so future work must target the " ++
      "hit-to-hit form, not the zero-run form)." ]

theorem fixedFamilyPeriodicityStatus_nonempty : fixedFamilyPeriodicityStatus ≠ [] := by
  simp [fixedFamilyPeriodicityStatus]

/-! ## Part 7.  Axiom-cleanliness audit -/

#print axioms fixedCycleGap_3_1
#print axioms fixedCycleGap_21_3
#print axioms fixedCycleGap_15_1
#print axioms fixedCycleGap_15_2
#print axioms fixedCycleGap_105_7
#print axioms fixedCycleStep_15_1
#print axioms fixedCycleStep_15_2
#print axioms fixedCycleStep_105_7
#print axioms slopeOrbit_fifteen_one_const
#print axioms slopeOrbit_fifteen_two_tail
#print axioms slopeOrbit_oneOhFive_seven_const
#print axioms fixedFamilyBand_3_1
#print axioms fixedFamilyBand_21_3
#print axioms fixedFamilyBand_15_1
#print axioms fixedFamilyBand_15_2
#print axioms fixedFamilyBand_105_7
#print axioms gapOrbit_three_one
#print axioms gapOrbit_twentyone_three
#print axioms gapOrbit_fifteen_one
#print axioms gapOrbit_fifteen_two
#print axioms gapOrbit_oneOhFive_seven
#print axioms gapOrbit_ge
#print axioms eventuallyZero_of_gapOrbit_zeroRun
#print axioms actual_zeroRun_void
#print axioms carry_tracks_hzero_void
#print axioms classOneDatum_zeroRun_void
#print axioms hitSequence_succ_of_const_gaps
#print axioms hitSequence_AP_of_const_gaps
#print axioms digit_periodic_of_const_gaps
#print axioms fixedFamilyRecurrentBand_bounds
#print axioms windowPeriodic_of_cleanContinuation
#print axioms eight_le_of_deepScale
#print axioms deepFixedFamilyWindowPeriodicity_of_cleanContinuation
#print axioms fixedFamilyHit_void_of_cleanContinuation
#print axioms deepFixedFamilyVoid_of_cleanContinuation
#print axioms returnFixedFamily_void_of_cleanContinuation
#print axioms densePackFixedFamily_void_of_cleanContinuation
#print axioms towerFP15_1Family_void_of_cleanContinuation
#print axioms towerFP15_2Family_void_of_cleanContinuation
#print axioms towerFP105Family_void_of_cleanContinuation
#print axioms towerEscapeLever_of_cleanContinuation
#print axioms towerFixedPointResidual_of_cleanContinuation
#print axioms deepFixedFamilyWindowPeriodicity_iff_void
#print axioms deepFixedFamilyCleanContinuation_iff_void
#print axioms deepFixedFamilyCleanContinuation_iff_windowPeriodicity
#print axioms fixedFamilyPeriodicityStatus_nonempty

end

end Erdos260
