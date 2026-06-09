import Mathlib
import Erdos260.Periodic
import Erdos260.DirtyCrossing
import Erdos260.AppendixM

/-!
# Appendix K.2.1: oriented semiperiodic overlap via the Fine–Wilf theorem

This file formalises the periodicity content underlying manuscript Lemma K.2.1
("oriented semiperiodic overlap alternative", `proof_v4.tex` §K.2, lines ~4175–4226).

The manuscript argument hinges on the **Fine–Wilf theorem**: if two long
semiperiodic arm patches with primitive semiperiods `q₁, q₂` overlap on an
interval `O` of length at least the Fine–Wilf threshold
`q₁ + q₂ - gcd(q₁, q₂)` (the manuscript overlap hypothesis (K.5)
`|O| ≥ q₁ + q₂ + C_FW·L` is even stronger), then both descriptions agree with the
common primitive period `q₀ = gcd(q₁, q₂)` on the clean overlap.

Mathlib already contains the Fine–Wilf / Periodicity Lemma for lists,
`List.HasPeriod.gcd` (`Mathlib/Data/List/PeriodicityLemma.lean`).  We bridge the
project's finite-word vocabulary (`PeriodicOn`, `ShortSemiperiodic`,
`SemiperiodicBlock` from `Residual.lean`/`LocalClosure.lean`) to `List.HasPeriod`
and transport that verified theorem.  The resulting Fine–Wilf statements
(`PeriodicOn.fineWilf`, `PeriodicOn.eq_of_modEq_gcd`,
`SemiperiodicBlock.fineWilf_overlap`, `ShortSemiperiodic.commonPeriod`) are
**unconditional real theorems**.

The full manuscript trichotomy of K.2.1 (run-merge / earlier anchored dirty
datum / identical anchored datum) depends on the dirty-crossing classification
(Theorem M.1.1), the priority ledger, and run/tower deletions; that genuinely
deep manuscript-specific continuation step is isolated as an explicit field.
The finite anchored-datum priority comparison itself is now a closed theorem on
`AnchoredFirstDirtyDatum`.
-/

namespace Erdos260

open Finset

/-! ## Bridge between `PeriodicOn` windows and `List.HasPeriod` -/

/-- The finite word read off `w` on the window `[start, start + n)`, as a `List`. -/
def wordOn (w : ℕ → ℕ) (start n : ℕ) : List ℕ :=
  (List.range n).map (fun i => w (start + i))

@[simp] theorem wordOn_length (w : ℕ → ℕ) (start n : ℕ) :
    (wordOn w start n).length = n := by
  simp [wordOn]

theorem wordOn_getElem? (w : ℕ → ℕ) (start n i : ℕ) (hi : i < n) :
    (wordOn w start n)[i]? = some (w (start + i)) := by
  unfold wordOn
  rw [List.getElem?_map, List.getElem?_range hi]
  rfl

/-- The functional content of `PeriodicOn w start n p` is exactly
`List.HasPeriod (wordOn w start n) p`. -/
theorem hasPeriod_wordOn_iff (w : ℕ → ℕ) (start n p : ℕ) :
    List.HasPeriod (wordOn w start n) p ↔
      ∀ i, i + p < n → w (start + i + p) = w (start + i) := by
  rw [List.hasPeriod_iff_getElem?]
  simp only [wordOn_length]
  constructor
  · intro h i hipn
    have hin : i < n := by omega
    have hlt : i < n - p := by omega
    have heq := h i hlt
    rw [wordOn_getElem? w start n i hin,
        wordOn_getElem? w start n (i + p) (by omega)] at heq
    have hval : w (start + i) = w (start + (i + p)) := Option.some_inj.mp heq
    rw [Nat.add_assoc]
    exact hval.symm
  · intro h i hlt
    have hipn : i + p < n := by omega
    have hin : i < n := by omega
    rw [wordOn_getElem? w start n i hin,
        wordOn_getElem? w start n (i + p) hipn]
    have heq := h i hipn
    rw [Nat.add_assoc] at heq
    rw [heq]

theorem PeriodicOn.hasPeriod {w : ℕ → ℕ} {start n p : ℕ}
    (h : PeriodicOn w start n p) : List.HasPeriod (wordOn w start n) p :=
  (hasPeriod_wordOn_iff w start n p).2 h.2

theorem PeriodicOn.of_hasPeriod {w : ℕ → ℕ} {start n p : ℕ} (hp : 0 < p)
    (h : List.HasPeriod (wordOn w start n) p) : PeriodicOn w start n p :=
  ⟨hp, (hasPeriod_wordOn_iff w start n p).1 h⟩

/-! ## Fine–Wilf for finite words (faithful, unconditional) -/

/--
**Fine–Wilf theorem for `PeriodicOn` (faithful, unconditional).**

If a finite word `w` has periods `p` and `q` on the window `[start, start + n)`
and the window is at least the Fine–Wilf threshold long,
`p + q - gcd(p, q) ≤ n`, then `w` has period `gcd(p, q)` on the same window.

This is the exact periodicity statement invoked in the proof of manuscript
Lemma K.2.1 (the clean-overlap step).  It is transported from Mathlib's verified
`List.HasPeriod.gcd` via the `wordOn` bridge, so it is a genuine unconditional
theorem (no `sorry`/`axiom`).
-/
theorem PeriodicOn.fineWilf {w : ℕ → ℕ} {start n p q : ℕ}
    (hp : PeriodicOn w start n p) (hq : PeriodicOn w start n q)
    (hlen : p + q - Nat.gcd p q ≤ n) :
    PeriodicOn w start n (Nat.gcd p q) := by
  have hlen' : p + q - Nat.gcd p q ≤ (wordOn w start n).length := by
    rw [wordOn_length]; exact hlen
  have Hg : List.HasPeriod (wordOn w start n) (Nat.gcd p q) :=
    (hp.hasPeriod).gcd (hq.hasPeriod) hlen'
  have hpos : 0 < Nat.gcd p q := Nat.gcd_pos_of_pos_left q hp.1
  exact PeriodicOn.of_hasPeriod hpos Hg

/--
**Strong Fine–Wilf (faithful, unconditional).**

Under the same hypotheses, any two positions `i, j` in the window that are
congruent modulo `gcd(p, q)` carry the same letter.  This is the manuscript's
statement that "both semiperiodic descriptions agree with the common primitive
period `q₀ = gcd(q₁, q₂)` on the clean overlap".
-/
theorem PeriodicOn.eq_of_modEq_gcd {w : ℕ → ℕ} {start n p q : ℕ}
    (hp : PeriodicOn w start n p) (hq : PeriodicOn w start n q)
    (hlen : p + q - Nat.gcd p q ≤ n)
    {i j : ℕ} (hi : i < n) (hj : j < n)
    (hmod : i ≡ j [MOD Nat.gcd p q]) :
    w (start + i) = w (start + j) := by
  have hlen' : p + q - Nat.gcd p q ≤ (wordOn w start n).length := by
    rw [wordOn_length]; exact hlen
  have Hg : List.HasPeriod (wordOn w start n) (Nat.gcd p q) :=
    (hp.hasPeriod).gcd (hq.hasPeriod) hlen'
  rw [List.hasPeriod_iff_forall_getElem?_mod] at Hg
  have ei := Hg i (by rw [wordOn_length]; exact hi)
  have ej := Hg j (by rw [wordOn_length]; exact hj)
  have hmg : i % Nat.gcd p q = j % Nat.gcd p q := hmod
  rw [wordOn_getElem? w start n i hi] at ei
  rw [wordOn_getElem? w start n j hj] at ej
  rw [hmg] at ei
  rw [← ej] at ei
  exact Option.some_inj.mp ei

/-! ## Oriented semiperiodic overlap (manuscript K.2.1 core) -/

/--
**K.2.1 Fine–Wilf overlap core (faithful, unconditional).**

Two valid semiperiodic blocks `B₁, B₂` (with primitive periods `q₁ = B₁.period`,
`q₂ = B₂.period`) whose patches both contain a common overlap interval `O` of
length at least the Fine–Wilf threshold `q₁ + q₂ - gcd(q₁, q₂)` agree with the
common primitive period `gcd(q₁, q₂)` on `O`.

This is the periodicity heart of the manuscript's "oriented semiperiodic overlap
alternative".
-/
theorem SemiperiodicBlock.fineWilf_overlap {w : ℕ → ℕ}
    {B₁ B₂ : SemiperiodicBlock} {O : IntervalBlock}
    (h₁ : B₁.Valid w) (h₂ : B₂.Valid w)
    (hO₁ : IntervalBlock.Contains B₁.block O)
    (hO₂ : IntervalBlock.Contains B₂.block O)
    (hlen : B₁.period + B₂.period - Nat.gcd B₁.period B₂.period ≤ O.length) :
    PeriodicOn w O.start O.length (Nat.gcd B₁.period B₂.period) :=
  PeriodicOn.fineWilf
    (SemiperiodicBlock.valid_of_contains h₁ hO₁)
    (SemiperiodicBlock.valid_of_contains h₂ hO₂) hlen

/--
Manuscript overlap hypothesis (K.5) form: an overlap with the extra `C_FW·L`
terminal/complete-block margin still forces the common gcd period, since the
margin only strengthens the Fine–Wilf threshold (this is the manuscript's
"discard the fixed `O(L)` margins" step).
-/
theorem SemiperiodicBlock.fineWilf_overlap_of_margin {w : ℕ → ℕ}
    {B₁ B₂ : SemiperiodicBlock} {O : IntervalBlock}
    (h₁ : B₁.Valid w) (h₂ : B₂.Valid w)
    (hO₁ : IntervalBlock.Contains B₁.block O)
    (hO₂ : IntervalBlock.Contains B₂.block O)
    (CFW L : ℕ)
    (hlen : B₁.period + B₂.period + CFW * L ≤ O.length) :
    PeriodicOn w O.start O.length (Nat.gcd B₁.period B₂.period) := by
  refine SemiperiodicBlock.fineWilf_overlap h₁ h₂ hO₁ hO₂ ?_
  have h1 : B₁.period + B₂.period - Nat.gcd B₁.period B₂.period
      ≤ B₁.period + B₂.period := Nat.sub_le _ _
  have h2 : B₁.period + B₂.period ≤ O.length :=
    le_trans (Nat.le_add_right _ _) hlen
  exact le_trans h1 h2

/--
**K.2.1 for short-semiperiodic descriptions (faithful, unconditional).**

If `w` is short-semiperiodic on `[start, start + n)` with two period bounds
`b₁, b₂` and the window is long enough (`b₁ + b₂ ≤ n`), then the two descriptions
share a single common period `g` (the gcd of their existential primitive
periods), satisfying `0 < g`, `g < b₁`, `g < b₂`, and `PeriodicOn w start n g`.
-/
theorem ShortSemiperiodic.commonPeriod {w : ℕ → ℕ} {start n b₁ b₂ : ℕ}
    (h₁ : ShortSemiperiodic w start n b₁) (h₂ : ShortSemiperiodic w start n b₂)
    (hlen : b₁ + b₂ ≤ n) :
    ∃ g, 0 < g ∧ g < b₁ ∧ g < b₂ ∧ PeriodicOn w start n g := by
  obtain ⟨p, hp, hpb⟩ := h₁
  obtain ⟨q, hq, hqb⟩ := h₂
  have hgcd_le_p : Nat.gcd p q ≤ p := Nat.le_of_dvd hp.1 (Nat.gcd_dvd_left p q)
  have hgcd_le_q : Nat.gcd p q ≤ q := Nat.le_of_dvd hq.1 (Nat.gcd_dvd_right p q)
  have hthr : p + q - Nat.gcd p q ≤ n := by
    have hsub : p + q - Nat.gcd p q ≤ p + q := Nat.sub_le _ _
    omega
  refine ⟨Nat.gcd p q, Nat.gcd_pos_of_pos_left q hp.1, ?_, ?_,
    PeriodicOn.fineWilf hp hq hthr⟩
  · exact lt_of_le_of_lt hgcd_le_p hpb
  · exact lt_of_le_of_lt hgcd_le_q hqb

/-! ## Manuscript Lemma K.2.1 trichotomy (conditional packaging) -/

/--
The first manuscript-specific step of K.2.1 after the Fine-Wilf common period
has been produced.

The common-period continuation either extends through the two semiperiodic arms
and hence merges into a deleted run, or it has a first anchored failure datum.
-/
structure OrientedSemiperiodicOverlapContinuationData
    {w : ℕ → ℕ} (B₁ B₂ : SemiperiodicBlock) (O : IntervalBlock)
    (Merged : Prop) (target : AnchoredFirstDirtyDatum) where
  failure : AnchoredFirstDirtyDatum
  continuation :
    PeriodicOn w O.start O.length (Nat.gcd B₁.period B₂.period) →
      Merged ∨ ¬ AnchoredFirstDirtyDatum.Earlier target failure

/--
The manuscript-specific trichotomy input for K.2.1 after the Fine-Wilf common
period has been produced.

The field packages the priority-ledger/dirty-crossing continuation step from
the proof: the common-period continuation either merges into a deleted run or
has a first anchored failure which is not later than the target anchored datum.
The finite lexicographic comparison from "not later" to "earlier or same" is
closed by `AnchoredFirstDirtyDatum.priority_of_not_later`.
-/
structure OrientedSemiperiodicOverlapAlternativeData
    {w : ℕ → ℕ} (B₁ B₂ : SemiperiodicBlock) (O : IntervalBlock)
    (Merged : Prop) (target : AnchoredFirstDirtyDatum) where
  continuation :
    OrientedSemiperiodicOverlapContinuationData (w := w) B₁ B₂ O Merged
      target

namespace OrientedSemiperiodicOverlapAlternativeData

/-- The anchored first-failure datum supplied by the continuation certificate. -/
def failure
    {w : ℕ → ℕ} {B₁ B₂ : SemiperiodicBlock} {O : IntervalBlock}
    {Merged : Prop} {target : AnchoredFirstDirtyDatum}
    (data :
      OrientedSemiperiodicOverlapAlternativeData (w := w) B₁ B₂ O Merged
        target) : AnchoredFirstDirtyDatum :=
  data.continuation.failure

/--
Projection of the manuscript K.2.1 trichotomy certificate once the Fine–Wilf
common period is available.
-/
theorem conclusion
    {w : ℕ → ℕ} {B₁ B₂ : SemiperiodicBlock} {O : IntervalBlock}
    {Merged : Prop} {target : AnchoredFirstDirtyDatum}
    (data :
      OrientedSemiperiodicOverlapAlternativeData (w := w) B₁ B₂ O Merged
        target)
    (commonPeriod :
      PeriodicOn w O.start O.length (Nat.gcd B₁.period B₂.period)) :
    Merged ∨
      AnchoredFirstDirtyDatum.Earlier data.failure target ∨
        AnchoredFirstDirtyDatum.SamePriorityKey data.failure target :=
  match data.continuation.continuation commonPeriod with
  | Or.inl hmerged => Or.inl hmerged
  | Or.inr hnot_later =>
      Or.inr (AnchoredFirstDirtyDatum.priority_of_not_later hnot_later)

end OrientedSemiperiodicOverlapAlternativeData

/--
**Manuscript Lemma K.2.1 (oriented semiperiodic overlap alternative).**

The Fine–Wilf engine is supplied unconditionally: from the overlap hypothesis
(K.5) `|O| ≥ q₁ + q₂ + C_FW·L` we obtain the common primitive period
`gcd(q₁, q₂)` on the clean overlap via
`SemiperiodicBlock.fineWilf_overlap_of_margin`.

The manuscript's trichotomy conclusion — (1) the two returns merge into a deleted
maximal run, (2) the overlap exposes an anchored first-dirty datum strictly
earlier than `𝔡̂`, or (3) the only exposed obstruction has the same anchored
priority key as `𝔡̂` — follows from the dirty-crossing classification
(Theorem M.1.1), the priority ledger, and the run/tower deletions.  The deep
continuation/first-failure step is still explicit in
`OrientedSemiperiodicOverlapAlternativeData`; the finite priority comparison is
proved by `AnchoredFirstDirtyDatum.priority_of_not_later`.
-/
theorem orientedSemiperiodicOverlap_alternative
    {w : ℕ → ℕ} {B₁ B₂ : SemiperiodicBlock} {O : IntervalBlock}
    (h₁ : B₁.Valid w) (h₂ : B₂.Valid w)
    (hO₁ : IntervalBlock.Contains B₁.block O)
    (hO₂ : IntervalBlock.Contains B₂.block O)
    {CFW L : ℕ}
    (hlen : B₁.period + B₂.period + CFW * L ≤ O.length)
    {Merged : Prop} {target : AnchoredFirstDirtyDatum}
    (data :
      OrientedSemiperiodicOverlapAlternativeData (w := w) B₁ B₂ O Merged
        target) :
    Merged ∨
      AnchoredFirstDirtyDatum.Earlier data.failure target ∨
        AnchoredFirstDirtyDatum.SamePriorityKey data.failure target :=
  data.conclusion
    (SemiperiodicBlock.fineWilf_overlap_of_margin h₁ h₂ hO₁ hO₂ CFW L hlen)

end Erdos260
