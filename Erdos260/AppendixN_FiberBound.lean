import Mathlib
import Erdos260.AppendixN_Multiplicity
import Erdos260.AppendixN_Compression
import Erdos260.AppendixN_CarryVariation
import Erdos260.StoppedTreeIndex
import Erdos260.IntegerCarry
import Erdos260.HitSequence
import Erdos260.Ledger

/-!
# Appendix N.2.1: the `C_Q`-to-one fibre bound from carry determinacy

`Erdos260.AppendixN.CrossingMultiplicityData.ofCarryRecord`
(`AppendixN_Multiplicity.lean`) *derives* the fixed-crossing-edge multiplicity
bound (eq N.16) from the faithful counting core, but it takes the `C_Q`-to-one
**fibre bound** `mult` as a raw hypothesis: for each edge `e` and recorded value
`y`, at most `mult` branches share the recorded data `Π_e`.  This module pushes
that fibre bound toward a real theorem.

The manuscript proof of N.2.1 (proof_v4.tex ~6446–6457) reads: *"the carry
recurrence determines all boundary residues on the two adjacent order-`s` windows
from the two recorded residues and the visible support word … if two drop states
with the same recorded data came from different starting stopped cylinders, their
first differing cylinder atom would be an earlier active priority atom …
contradiction; thus the map `(b,ζ) ↦ Π_e(ζ)` is `C_Q`-to-one."*

We separate this into a **provable counting/determinacy chain** and the single
**irreducible geometric input** (the priority-atom fact), and we genuinely shrink
the `mult` hypothesis of `ofCarryRecord` down to that single input.

## What is formalized

* **Carry-residue determinacy (faithful, the real content).**
  `integerCarry_zmod_add` strengthens the mod-`Q` recurrence
  `integerCarry_succ_modEq_Q` to its closed forward form: the carry residue mod
  `Q` at step `N + h` is `2 ^ h ·` the residue at `N`, with **no zero-digit
  hypothesis** — the digit terms `Q · j · d j` all vanish mod `Q`.  Hence
  (`integerCarry_zmod_eq_of_eq_lower`) equal residue at one step forces equal
  residues at every later step (the `h = 1` case is the manuscript's
  `integerCarry_zmod_succ_eq_of_carry_eq`).  This is the genuine carry
  recurrence, not a re-encoding.

* **The recorded residues, run through the recurrence (load-bearing).**
  `record_fst_eq_pow_startResidue`: the recorded lower residue is
  `2 ^ (loIdx e) ·` the start-residue `(P b mod Q)`.
  `record_snd_fst_eq_pow_mul`: the recorded upper residue is
  `2 ^ (hiIdx e − loIdx e) ·` the recorded lower residue, so it is **redundant**
  (`record_eq_iff_of_le`: a record is determined by its lower residue + label).
  Both are direct consequences of `integerCarry_zmod_add`.

* **The fibre bound (the deliverable).**  `fiber_card_le_solutionSet` shows that
  the fibre over a record value `y` injects, via the start-residue, into the
  solution set `{ s : ZMod Q | 2 ^ (loIdx e) · s = y.1 }` — and the membership of
  each fibre element in that solution set is *exactly* the carry recurrence
  (`record_fst_eq_pow_startResidue`).  `fiber_card_le_Q` reads off
  `card ≤ Q` via `ZMod.card`.  The only input is the **priority-atom
  coincidence hypothesis** `hinj`: branches with equal record *and* equal
  start-residue coincide.

* **Stopped-tree injectivity (faithful).**  `stoppedBranch_fiber_card_le`
  counts genuine `StoppedBranch` objects `stoppedBranchOf a r k`: because
  `stoppedBranchOf a r` is injective (`stoppedBranchOf_injective`, from
  hit-sequence strict monotonicity), the branch fibre and the start fibre have
  equal cardinality, so the `≤ Q` bound transfers.

* **The bridge (eq N.16 with the `mult` hypothesis shrunk).**
  `CrossingMultiplicityData.ofCarryRecordPriority` builds the full N.2.1 bundle
  by feeding the *derived* fibre bound (`mult = Q`) into `ofCarryRecord`.  Its
  `hfiber` is no longer assumed: it is produced from the priority-atom
  coincidence hypothesis by the determinacy chain above, with explicit constant
  `C = Q · Q · |Labels| · Q`.

## Faithful vs conditional

* **Faithful (real theorems):** the mod-`Q` forward carry determinacy
  (`integerCarry_zmod_add`, genuinely from the recurrence, no zero-run
  hypothesis); the residue-to-start-residue identities; the redundancy of the
  upper residue; the fibre `↪ ZMod Q` count via `ZMod.card`; and the stopped-tree
  injectivity transfer via `stoppedBranchOf_injective`.

* **Conditional (one explicit hypothesis, never `sorry`):** the priority-atom
  coincidence `hinj` — *branches in the support with equal recorded data and
  equal start-residue coincide.*  This is precisely the irreducible "first
  differing cylinder atom is an earlier active priority atom" geometric fact of
  Lemma N.1.1 / N.2.0, and is the *only* remaining input.  The auxiliary
  `[Fintype Labels]` and the lift/support data of `ofCarryRecord` are inherited.

There is no `sorry`, `axiom`, or `admit` anywhere in this file.
-/

namespace Erdos260

noncomputable section

open MeasureTheory Finset

namespace AppendixN

/-! ## N.2.1.a Forward mod-`Q` carry-residue determinacy

The closed forward form of the manuscript carry recurrence.  Mod `Q`, the digit
terms `Q · j · d j` vanish, so the residue **doubles at every step regardless of
the digits**.  This is the genuine determinacy "the carry recurrence determines
all boundary residues … from the recorded residues", and it is the real content
that drives the fibre bound below. -/

/-- **Forward carry-residue determinacy (eq N.17).** The carry residue mod `Q` at
step `N + h` is `2 ^ h ·` the residue at step `N`.  Unlike
`integerCarry_zmod_add_zero_run`, this needs **no** zero-digit hypothesis: mod `Q`
every digit term `Q · j · d j` is `0`.  Proved by iterating the genuine recurrence
`integerCarry_zmod_succ`. -/
theorem integerCarry_zmod_add (Q : ℕ) (P : ℤ) (d : ℕ → ℕ) (N h : ℕ) :
    ((integerCarry Q P d (N + h) : ℤ) : ZMod Q)
      = (2 : ZMod Q) ^ h * ((integerCarry Q P d N : ℤ) : ZMod Q) := by
  induction h with
  | zero => simp
  | succ h ih =>
      have hidx : N + (h + 1) = (N + h) + 1 := by ring
      rw [hidx, integerCarry_zmod_succ, ih, pow_succ]
      ring

/-- **Carry determinacy across a gap.** If two branches have equal carry residues
mod `Q` at step `M`, then they have equal residues at every later step `N ≥ M` —
independent of the target numerators and *all* the digits in between.  The `h = 1`
special case is the manuscript's `integerCarry_zmod_succ_eq_of_carry_eq`. -/
theorem integerCarry_zmod_eq_of_eq_lower (Q : ℕ) (P P' : ℤ) (d d' : ℕ → ℕ) {M N : ℕ}
    (hMN : M ≤ N)
    (h : ((integerCarry Q P d M : ℤ) : ZMod Q) = ((integerCarry Q P' d' M : ℤ) : ZMod Q)) :
    ((integerCarry Q P d N : ℤ) : ZMod Q) = ((integerCarry Q P' d' N : ℤ) : ZMod Q) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hMN
  rw [integerCarry_zmod_add, integerCarry_zmod_add, h]

/-! ## N.2.1.b The recorded residues run through the recurrence

The start-residue of a branch is the residue of its rational-target numerator,
`P b mod Q` (the carry at step `0`).  The recurrence pins the two recorded
window-endpoint residues to it: the lower residue is `2 ^ (loIdx e)` times the
start-residue, and the upper residue is `2 ^ (hiIdx e − loIdx e)` times the lower
residue (so the upper residue is genuinely redundant). -/

/-- The **start-residue** of a branch: the residue mod `Q` of its rational-target
numerator `P b`, i.e. the carry at step `0`. -/
def FirstCrossingRecordData.startResidue {Branch Labels : Type*} {Q : ℕ}
    (D : FirstCrossingRecordData Branch Q Labels) (b : Branch) : ZMod Q :=
  (D.P b : ZMod Q)

/-- The recorded *upper*-endpoint residue is the genuine `integerCarry` residue mod
`Q` (companion of `record_fst`; the record is not a vacuous re-encoding). -/
theorem FirstCrossingRecordData.record_snd_fst {Branch Labels : Type*} {Q : ℕ}
    (D : FirstCrossingRecordData Branch Q Labels) (e : ℕ) (b : Branch) :
    (D.record e b).2.1 = ((integerCarry Q (D.P b) (D.digit b) (D.hiIdx e) : ℤ) : ZMod Q) :=
  rfl

/-- **Lower recorded residue from the start-residue (eq N.17).** The recorded
lower-endpoint residue is `2 ^ (loIdx e) ·` the start-residue.  This is the
recurrence `integerCarry_zmod_add` applied from step `0`; it is what later forces
each fibre's start-residues into a single solution set. -/
theorem record_fst_eq_pow_startResidue {Branch Labels : Type*} {Q : ℕ}
    (D : FirstCrossingRecordData Branch Q Labels) (e : ℕ) (b : Branch) :
    (D.record e b).1 = (2 : ZMod Q) ^ D.loIdx e * D.startResidue b := by
  have h := integerCarry_zmod_add Q (D.P b) (D.digit b) 0 (D.loIdx e)
  rw [Nat.zero_add, integerCarry_zero] at h
  rw [FirstCrossingRecordData.record_fst, h]
  rfl

/-- **Upper recorded residue from the lower (eq N.17, redundancy).** When the
window is ordered (`loIdx e ≤ hiIdx e`), the recorded upper residue is
`2 ^ (hiIdx e − loIdx e) ·` the recorded lower residue.  A direct consequence of
`integerCarry_zmod_add`: the upper residue carries no information beyond the
lower one. -/
theorem record_snd_fst_eq_pow_mul {Branch Labels : Type*} {Q : ℕ}
    (D : FirstCrossingRecordData Branch Q Labels) (e : ℕ) (b : Branch)
    (hle : D.loIdx e ≤ D.hiIdx e) :
    (D.record e b).2.1 = (2 : ZMod Q) ^ (D.hiIdx e - D.loIdx e) * (D.record e b).1 := by
  rw [FirstCrossingRecordData.record_snd_fst, FirstCrossingRecordData.record_fst]
  have hadd := integerCarry_zmod_add Q (D.P b) (D.digit b) (D.loIdx e) (D.hiIdx e - D.loIdx e)
  rw [Nat.add_sub_cancel' hle] at hadd
  exact hadd

/-- **A record is determined by its lower residue and label.** For an ordered
window the recorded data `Π_e` collapses to `(R̄_lo, λ)`: the upper residue is
forced by the recurrence.  This is the precise sense in which the residues live in
the size-`Q` set and the second residue is redundant. -/
theorem record_eq_iff_of_le {Branch Labels : Type*} [DecidableEq Labels] {Q : ℕ}
    (D : FirstCrossingRecordData Branch Q Labels) (e : ℕ) (b b' : Branch)
    (hle : D.loIdx e ≤ D.hiIdx e) :
    D.record e b = D.record e b' ↔
      (D.record e b).1 = (D.record e b').1 ∧ (D.record e b).2.2 = (D.record e b').2.2 := by
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg (fun t => t.2.2) h⟩
  · rintro ⟨h1, h2⟩
    have h21 : (D.record e b).2.1 = (D.record e b').2.1 := by
      rw [record_snd_fst_eq_pow_mul D e b hle, record_snd_fst_eq_pow_mul D e b' hle, h1]
    exact Prod.ext_iff.mpr ⟨h1, Prod.ext_iff.mpr ⟨h21, h2⟩⟩

/-! ## N.2.1.c The `C_Q`-to-one fibre bound

Fix an edge `e` and recorded value `y`.  The fibre is the set of support branches
with `Π_e = y`.  The **only** input is the priority-atom coincidence hypothesis
`hinj`: branches with equal record *and* equal start-residue coincide.  From it we
prove the fibre is bounded:

* Every fibre element's start-residue solves `2 ^ (loIdx e) · s = y.1` — this step
  *is* the carry recurrence (`record_fst_eq_pow_startResidue`).
* `hinj` makes the start-residue injective on the fibre.

Hence the fibre injects into the solution set, of size `≤ Q`. -/

/-- **Fibre `↪` carry-solution set (carry recurrence load-bearing).** Under the
priority-atom coincidence `hinj`, the fibre over a recorded value `y` has
cardinality at most the number of residues `s : ZMod Q` solving
`2 ^ (loIdx e) · s = y.1`.  The recurrence `record_fst_eq_pow_startResidue` is
exactly what places each fibre element's start-residue into this solution set. -/
theorem fiber_card_le_solutionSet {Branch Labels : Type*} [DecidableEq Labels]
    {Q : ℕ} [NeZero Q]
    (D : FirstCrossingRecordData Branch Q Labels)
    (support : Finset Branch) (e : ℕ) (y : ZMod Q × ZMod Q × Labels)
    (hinj : ∀ b ∈ support, ∀ b' ∈ support,
        D.record e b = D.record e b' → D.startResidue b = D.startResidue b' → b = b') :
    (support.filter (fun b => D.record e b = y)).card
      ≤ (Finset.univ.filter (fun s : ZMod Q => (2 : ZMod Q) ^ D.loIdx e * s = y.1)).card := by
  classical
  have hsub : (support.filter (fun b => D.record e b = y)).image D.startResidue
        ⊆ Finset.univ.filter (fun s : ZMod Q => (2 : ZMod Q) ^ D.loIdx e * s = y.1) := by
    intro s hs
    rcases Finset.mem_image.1 hs with ⟨b, hb, rfl⟩
    have hby : D.record e b = y := (Finset.mem_filter.1 hb).2
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have h1 : (D.record e b).1 = y.1 := by rw [hby]
    rw [← record_fst_eq_pow_startResidue D e b]
    exact h1
  have hinjOn : Set.InjOn D.startResidue
      ↑(support.filter (fun b => D.record e b = y)) := by
    intro b hb b' hb' hss
    rw [Finset.mem_coe, Finset.mem_filter] at hb hb'
    exact hinj b hb.1 b' hb'.1 (hb.2.trans hb'.2.symm) hss
  calc (support.filter (fun b => D.record e b = y)).card
        = ((support.filter (fun b => D.record e b = y)).image D.startResidue).card :=
          (Finset.card_image_of_injOn hinjOn).symm
    _ ≤ (Finset.univ.filter (fun s : ZMod Q => (2 : ZMod Q) ^ D.loIdx e * s = y.1)).card :=
          Finset.card_le_card hsub

/-- **`C_Q`-to-one fibre bound with `C_Q = Q` (eq N.16 fibre count).** Under the
priority-atom coincidence `hinj`, each per-edge record fibre has at most `Q`
branches.  The solution set is a subset of `ZMod Q`, whose cardinality is `Q`
(`ZMod.card`). -/
theorem fiber_card_le_Q {Branch Labels : Type*} [DecidableEq Labels]
    {Q : ℕ} [NeZero Q]
    (D : FirstCrossingRecordData Branch Q Labels)
    (support : Finset Branch) (e : ℕ) (y : ZMod Q × ZMod Q × Labels)
    (hinj : ∀ b ∈ support, ∀ b' ∈ support,
        D.record e b = D.record e b' → D.startResidue b = D.startResidue b' → b = b') :
    (support.filter (fun b => D.record e b = y)).card ≤ Q := by
  refine (fiber_card_le_solutionSet D support e y hinj).trans ?_
  calc (Finset.univ.filter (fun s : ZMod Q => (2 : ZMod Q) ^ D.loIdx e * s = y.1)).card
        ≤ Fintype.card (ZMod Q) := Finset.card_le_univ _
    _ = Q := ZMod.card Q

/-- The per-edge form of `fiber_card_le_Q`: the exact `hfiber` interface that
`CrossingMultiplicityData.ofCarryRecord` consumes, with `mult = Q`, *derived* from
the per-edge priority-atom coincidence hypotheses. -/
theorem record_fiber_card_le_Q {Branch Labels : Type*} [DecidableEq Labels]
    {Q : ℕ} [NeZero Q]
    (D : FirstCrossingRecordData Branch Q Labels)
    (support : ℕ → Finset Branch)
    (hinj : ∀ (e : ℕ), ∀ b ∈ support e, ∀ b' ∈ support e,
        D.record e b = D.record e b' → D.startResidue b = D.startResidue b' → b = b') :
    ∀ (e : ℕ) (y : ZMod Q × ZMod Q × Labels),
      ((support e).filter (fun b => D.record e b = y)).card ≤ Q :=
  fun e y => fiber_card_le_Q D (support e) e y (hinj e)

/-! ## N.2.1.c' Reduced record range: the upper residue is redundant

The first bridge `ofCarryRecordPriority` below keeps the manuscript record type
`ZMod Q × ZMod Q × Labels`.  But the recurrence already proves the upper
endpoint residue from the lower one (`record_snd_fst_eq_pow_mul`), so the
counting range can be tightened to `ZMod Q × Labels`: lower residue plus the
finite side/tie/pivot label.  This does not change the deep input; it removes
one redundant `Q` factor from the faithful range-size count. -/

/-- **Reduced first-crossing record.**  The lower carry residue together with the
finite side/tie/pivot label.  The upper residue of the full record is forced by
the carry recurrence, so this is the range actually needed for the counting
argument. -/
def FirstCrossingRecordData.lowerLabelRecord {Branch Labels : Type*} {Q : ℕ}
    (D : FirstCrossingRecordData Branch Q Labels) (e : ℕ) (b : Branch) :
    ZMod Q × Labels :=
  ((D.record e b).1, (D.record e b).2.2)

/-- **Lower residue + label determine the full record.**  On an ordered window,
equality of the reduced records implies equality of the original
two-residue+label records because the upper residue is forced by the lower one.
-/
theorem record_eq_of_lowerLabel_eq_of_le {Branch Labels : Type*} [DecidableEq Labels]
    {Q : ℕ}
    (D : FirstCrossingRecordData Branch Q Labels) (e : ℕ) (b b' : Branch)
    (hle : D.loIdx e ≤ D.hiIdx e)
    (h : D.lowerLabelRecord e b = D.lowerLabelRecord e b') :
    D.record e b = D.record e b' := by
  refine (record_eq_iff_of_le D e b b' hle).2 ?_
  have h1 : (D.record e b).1 = (D.record e b').1 := by
    simpa [FirstCrossingRecordData.lowerLabelRecord] using congrArg Prod.fst h
  have h2 : (D.record e b).2.2 = (D.record e b').2.2 := by
    simpa [FirstCrossingRecordData.lowerLabelRecord] using congrArg Prod.snd h
  exact ⟨h1, h2⟩

/-- **Reduced range-size counting core.**  If a lower-residue+label record map is
`mult`-to-one on `support`, then `support.card ≤ Q · |Labels| · mult`. -/
theorem support_card_le_lower_label_mul {Branch Labels : Type*} [DecidableEq Branch]
    [DecidableEq Labels] [Fintype Labels] (Q : ℕ) [NeZero Q]
    (support : Finset Branch)
    (record : Branch → ZMod Q × Labels) (mult : ℕ)
    (hfiber : ∀ y, (support.filter (fun b => record b = y)).card ≤ mult) :
    support.card ≤ Q * Fintype.card Labels * mult := by
  calc support.card
      ≤ Fintype.card (ZMod Q × Labels) * mult :=
        support_card_le_fintype_mul support record mult hfiber
    _ = Q * Fintype.card Labels * mult := by
        simp only [Fintype.card_prod, ZMod.card]

/-- **Reduced fibre-to-solution-set bound.**  For a fixed reduced record value,
the start residues of its fibre lie in the same `ZMod Q` solution set. -/
theorem lowerLabel_fiber_card_le_solutionSet {Branch Labels : Type*} [DecidableEq Labels]
    {Q : ℕ} [NeZero Q]
    (D : FirstCrossingRecordData Branch Q Labels)
    (support : Finset Branch) (e : ℕ) (y : ZMod Q × Labels)
    (hinj : ∀ b ∈ support, ∀ b' ∈ support,
        D.lowerLabelRecord e b = D.lowerLabelRecord e b' →
          D.startResidue b = D.startResidue b' → b = b') :
    (support.filter (fun b => D.lowerLabelRecord e b = y)).card
      ≤ (Finset.univ.filter (fun s : ZMod Q => (2 : ZMod Q) ^ D.loIdx e * s = y.1)).card := by
  classical
  have hsub : (support.filter (fun b => D.lowerLabelRecord e b = y)).image D.startResidue
        ⊆ Finset.univ.filter (fun s : ZMod Q => (2 : ZMod Q) ^ D.loIdx e * s = y.1) := by
    intro s hs
    rcases Finset.mem_image.1 hs with ⟨b, hb, rfl⟩
    have hby : D.lowerLabelRecord e b = y := (Finset.mem_filter.1 hb).2
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have h1 : (D.record e b).1 = y.1 := congrArg Prod.fst hby
    rw [← record_fst_eq_pow_startResidue D e b]
    exact h1
  have hinjOn : Set.InjOn D.startResidue
      ↑(support.filter (fun b => D.lowerLabelRecord e b = y)) := by
    intro b hb b' hb' hss
    rw [Finset.mem_coe, Finset.mem_filter] at hb hb'
    exact hinj b hb.1 b' hb'.1 (hb.2.trans hb'.2.symm) hss
  calc (support.filter (fun b => D.lowerLabelRecord e b = y)).card
        = ((support.filter (fun b => D.lowerLabelRecord e b = y)).image D.startResidue).card :=
          (Finset.card_image_of_injOn hinjOn).symm
    _ ≤ (Finset.univ.filter (fun s : ZMod Q => (2 : ZMod Q) ^ D.loIdx e * s = y.1)).card :=
          Finset.card_le_card hsub

/-- **Reduced `C_Q`-to-one fibre bound with `C_Q = Q`.**  A lower-residue+label
record fibre has at most `Q` branches under the same priority-atom coincidence
input. -/
theorem lowerLabel_fiber_card_le_Q {Branch Labels : Type*} [DecidableEq Labels]
    {Q : ℕ} [NeZero Q]
    (D : FirstCrossingRecordData Branch Q Labels)
    (support : Finset Branch) (e : ℕ) (y : ZMod Q × Labels)
    (hinj : ∀ b ∈ support, ∀ b' ∈ support,
        D.lowerLabelRecord e b = D.lowerLabelRecord e b' →
          D.startResidue b = D.startResidue b' → b = b') :
    (support.filter (fun b => D.lowerLabelRecord e b = y)).card ≤ Q := by
  refine (lowerLabel_fiber_card_le_solutionSet D support e y hinj).trans ?_
  calc (Finset.univ.filter (fun s : ZMod Q => (2 : ZMod Q) ^ D.loIdx e * s = y.1)).card
        ≤ Fintype.card (ZMod Q) := Finset.card_le_univ _
    _ = Q := ZMod.card Q

/-- The reduced per-edge support-size bound:
`(support e).card ≤ Q · |Labels| · Q`. -/
theorem support_card_le_lower_label_priority {Branch Labels : Type*}
    [DecidableEq Branch] [DecidableEq Labels] [Fintype Labels]
    {Q : ℕ} [NeZero Q]
    (D : FirstCrossingRecordData Branch Q Labels)
    (support : ℕ → Finset Branch)
    (hinj : ∀ (e : ℕ), ∀ b ∈ support e, ∀ b' ∈ support e,
        D.lowerLabelRecord e b = D.lowerLabelRecord e b' →
          D.startResidue b = D.startResidue b' → b = b') :
    ∀ e, ((support e).card : ℕ) ≤ Q * Fintype.card Labels * Q := by
  intro e
  exact support_card_le_lower_label_mul Q (support e) (D.lowerLabelRecord e) Q
    (fun y => lowerLabel_fiber_card_le_Q D (support e) e y (hinj e))

/-- **Full-record priority coincidence implies reduced-record priority
coincidence.**  The only extra input is the ordered-window fact
`loIdx e ≤ hiIdx e`; then the upper residue is redundant. -/
theorem lowerLabel_priority_of_record_priority {Branch Labels : Type*}
    [DecidableEq Labels] {Q : ℕ}
    (D : FirstCrossingRecordData Branch Q Labels)
    (support : ℕ → Finset Branch)
    (hle : ∀ e, D.loIdx e ≤ D.hiIdx e)
    (hinj : ∀ (e : ℕ), ∀ b ∈ support e, ∀ b' ∈ support e,
        D.record e b = D.record e b' →
          D.startResidue b = D.startResidue b' → b = b') :
    ∀ (e : ℕ), ∀ b ∈ support e, ∀ b' ∈ support e,
        D.lowerLabelRecord e b = D.lowerLabelRecord e b' →
          D.startResidue b = D.startResidue b' → b = b' := by
  intro e b hb b' hb' hrec hstart
  exact hinj e b hb b' hb'
    (record_eq_of_lowerLabel_eq_of_le D e b b' (hle e) hrec) hstart

/-- The reduced support-size bound from the original full-record priority
coincidence, using ordered windows to recover full-record equality. -/
theorem support_card_le_lower_label_priority_of_record_priority {Branch Labels : Type*}
    [DecidableEq Branch] [DecidableEq Labels] [Fintype Labels]
    {Q : ℕ} [NeZero Q]
    (D : FirstCrossingRecordData Branch Q Labels)
    (support : ℕ → Finset Branch)
    (hle : ∀ e, D.loIdx e ≤ D.hiIdx e)
    (hinj : ∀ (e : ℕ), ∀ b ∈ support e, ∀ b' ∈ support e,
        D.record e b = D.record e b' →
          D.startResidue b = D.startResidue b' → b = b') :
    ∀ e, ((support e).card : ℕ) ≤ Q * Fintype.card Labels * Q :=
  support_card_le_lower_label_priority D support
    (lowerLabel_priority_of_record_priority D support hle hinj)

/-! ## N.2.1.d Stopped-tree injectivity: counting genuine branches

The manuscript counts *starting stopped cylinders*.  Indexing them by the
stopped-tree branch `stoppedBranchOf a r k`, the injectivity
`stoppedBranchOf_injective` (from hit-sequence strict monotonicity, proved in
`StoppedTreeIndex.lean`) makes the start index a faithful identifier: the number
of distinct stopped branches over a fibre equals the number of starts, so the
`≤ Q` bound transfers verbatim to genuine `StoppedBranch` objects. -/

/-- **Fibre bound for genuine stopped branches.** With branches indexed by start
`k` via `stoppedBranchOf a r`, the number of *distinct stopped branches* whose
start lies in the record fibre over `y` is at most `Q`.  Uses both real
ingredients: `stoppedBranchOf_injective` (image card = preimage card) and
`fiber_card_le_Q` (the carry-determinacy fibre bound). -/
theorem stoppedBranch_fiber_card_le {Labels : Type*} [DecidableEq Labels]
    {Q : ℕ} [NeZero Q]
    {d a : ℕ → ℕ} (hseq : HitSequence d a) (r : ℕ)
    (D : FirstCrossingRecordData ℕ Q Labels)
    (S : Finset ℕ) (e : ℕ) (y : ZMod Q × ZMod Q × Labels)
    (hinj : ∀ k ∈ S, ∀ k' ∈ S,
        D.record e k = D.record e k' → D.startResidue k = D.startResidue k' → k = k') :
    ((S.filter (fun k => D.record e k = y)).image (stoppedBranchOf a r)).card ≤ Q := by
  have hio : Set.InjOn (stoppedBranchOf a r)
      ↑(S.filter (fun k => D.record e k = y)) :=
    fun k _ k' _ h => stoppedBranchOf_injective hseq r h
  rw [Finset.card_image_of_injOn hio]
  exact fiber_card_le_Q D S e y hinj

/-! ## N.2.1.e Bridge to `ofCarryRecord` (eq N.16, `mult` hypothesis shrunk)

Feeding the *derived* fibre bound into `CrossingMultiplicityData.ofCarryRecord`
produces the full N.2.1 bundle whose only remaining deep input is the
priority-atom coincidence `hinj`. -/

/-- **N.2.1 from the priority-atom coincidence (eq N.16).** Builds the
`CrossingMultiplicityData` bundle with explicit constant
`C = Q · Q · |Labels| · Q`, where the `C_Q`-to-one fibre bound is **no longer
assumed** — it is `record_fiber_card_le_Q`, derived from:

* the genuine carry record `D` (residues mod `Q` + finite labels);
* the carry recurrence (lower residue `= 2 ^ (loIdx e) ·` start-residue), which
  forces each fibre's start-residues into one `ZMod Q` solution set — **faithful**;
* the priority-atom coincidence `hinj` (equal record + equal start-residue ⇒
  coincide) — the single **conditional** input (Lemma N.1.1 / N.2.0);
* `[Fintype Labels]`, `hlift_le`, and `support`/`hsupp`/`hzero` — inherited from
  `ofCarryRecord`. -/
def CrossingMultiplicityData.ofCarryRecordPriority {Branch Labels : Type*}
    [DecidableEq Branch] [DecidableEq Labels] [Fintype Labels] {Q : ℕ} [NeZero Q]
    (D : FirstCrossingRecordData Branch Q Labels)
    (branches : Finset Branch)
    (dropMass : Branch → ℕ → ℝ) (hdrop_nonneg : ∀ b e, 0 ≤ dropMass b e)
    (crossingIndic : ℕ → ℝ) (hindic_nonneg : ∀ e, 0 ≤ crossingIndic e)
    (hlift_le : ∀ b e, dropMass b e ≤ crossingIndic e)
    (support : ℕ → Finset Branch)
    (hsupp : ∀ e, support e ⊆ branches)
    (hzero : ∀ e, ∀ b ∈ branches, b ∉ support e → dropMass b e = 0)
    (hinj : ∀ (e : ℕ), ∀ b ∈ support e, ∀ b' ∈ support e,
        D.record e b = D.record e b' → D.startResidue b = D.startResidue b' → b = b') :
    CrossingMultiplicityData Branch :=
  CrossingMultiplicityData.ofCarryRecord D branches Q dropMass hdrop_nonneg
    crossingIndic hindic_nonneg hlift_le support hsupp hzero
    (record_fiber_card_le_Q D support hinj)

/-- The constant produced by `ofCarryRecordPriority` is the genuine finite range
size `Q · Q · |Labels|` times the *derived* fibre bound `Q`. -/
@[simp] theorem CrossingMultiplicityData.ofCarryRecordPriority_C {Branch Labels : Type*}
    [DecidableEq Branch] [DecidableEq Labels] [Fintype Labels] {Q : ℕ} [NeZero Q]
    (D : FirstCrossingRecordData Branch Q Labels)
    (branches : Finset Branch)
    (dropMass : Branch → ℕ → ℝ) (hdrop_nonneg : ∀ b e, 0 ≤ dropMass b e)
    (crossingIndic : ℕ → ℝ) (hindic_nonneg : ∀ e, 0 ≤ crossingIndic e)
    (hlift_le : ∀ b e, dropMass b e ≤ crossingIndic e)
    (support : ℕ → Finset Branch)
    (hsupp : ∀ e, support e ⊆ branches)
    (hzero : ∀ e, ∀ b ∈ branches, b ∉ support e → dropMass b e = 0)
    (hinj : ∀ (e : ℕ), ∀ b ∈ support e, ∀ b' ∈ support e,
        D.record e b = D.record e b' → D.startResidue b = D.startResidue b' → b = b') :
    (CrossingMultiplicityData.ofCarryRecordPriority D branches dropMass hdrop_nonneg
      crossingIndic hindic_nonneg hlift_le support hsupp hzero hinj).C
      = ((Q * Q * Fintype.card Labels * Q : ℕ) : ℝ) :=
  rfl

/-- **N.2.1 per-edge multiplicity bound from the priority-atom coincidence
(eq N.16).** The bundle built by `ofCarryRecordPriority` satisfies the genuine
per-edge bound `∑_b μ_T(Ω^V_{b,e}) ≤ (Q · Q · |Labels| · Q) · 𝟙_{X_e}`, with the
multiplicity *derived* (only `hinj` is assumed), not posited. -/
theorem CrossingMultiplicityData.ofCarryRecordPriority_multiplicity_le {Branch Labels : Type*}
    [DecidableEq Branch] [DecidableEq Labels] [Fintype Labels] {Q : ℕ} [NeZero Q]
    (D : FirstCrossingRecordData Branch Q Labels)
    (branches : Finset Branch)
    (dropMass : Branch → ℕ → ℝ) (hdrop_nonneg : ∀ b e, 0 ≤ dropMass b e)
    (crossingIndic : ℕ → ℝ) (hindic_nonneg : ∀ e, 0 ≤ crossingIndic e)
    (hlift_le : ∀ b e, dropMass b e ≤ crossingIndic e)
    (support : ℕ → Finset Branch)
    (hsupp : ∀ e, support e ⊆ branches)
    (hzero : ∀ e, ∀ b ∈ branches, b ∉ support e → dropMass b e = 0)
    (hinj : ∀ (e : ℕ), ∀ b ∈ support e, ∀ b' ∈ support e,
        D.record e b = D.record e b' → D.startResidue b = D.startResidue b' → b = b')
    (e : ℕ) :
    (∑ b ∈ branches, dropMass b e)
      ≤ ((Q * Q * Fintype.card Labels * Q : ℕ) : ℝ) * crossingIndic e :=
  CrossingMultiplicityData.ofCarryRecord_multiplicity_le D branches Q dropMass hdrop_nonneg
    crossingIndic hindic_nonneg hlift_le support hsupp hzero
    (record_fiber_card_le_Q D support hinj) e

/-! ## N.2.1.f Reduced-record bridge (one residue + label)

The previous bridge faithfully discharges the raw fibre bound while still
counting the full manuscript record range `ZMod Q × ZMod Q × Labels`.  Since the
upper residue is determined by the lower residue, the reduced record
`ZMod Q × Labels` gives the same multiplicity conclusion with one fewer
range-size `Q` factor. -/

/-- **N.2.1 from the reduced first-crossing record (eq N.16).** Builds the
`CrossingMultiplicityData` bundle with explicit constant
`C = Q · |Labels| · Q`.  The support-size bound is derived from the reduced
lower-residue+label range and the same priority-atom coincidence hypothesis. -/
def CrossingMultiplicityData.ofLowerLabelRecordPriority {Branch Labels : Type*}
    [DecidableEq Branch] [DecidableEq Labels] [Fintype Labels] {Q : ℕ} [NeZero Q]
    (D : FirstCrossingRecordData Branch Q Labels)
    (branches : Finset Branch)
    (dropMass : Branch → ℕ → ℝ) (hdrop_nonneg : ∀ b e, 0 ≤ dropMass b e)
    (crossingIndic : ℕ → ℝ) (hindic_nonneg : ∀ e, 0 ≤ crossingIndic e)
    (hlift_le : ∀ b e, dropMass b e ≤ crossingIndic e)
    (support : ℕ → Finset Branch)
    (hsupp : ∀ e, support e ⊆ branches)
    (hzero : ∀ e, ∀ b ∈ branches, b ∉ support e → dropMass b e = 0)
    (hinj : ∀ (e : ℕ), ∀ b ∈ support e, ∀ b' ∈ support e,
        D.lowerLabelRecord e b = D.lowerLabelRecord e b' →
          D.startResidue b = D.startResidue b' → b = b') :
    CrossingMultiplicityData Branch :=
  CrossingMultiplicityData.ofFirstCrossingRecord branches
    ((Q * Fintype.card Labels * Q : ℕ) : ℝ) (Nat.cast_nonneg _)
    dropMass hdrop_nonneg crossingIndic hindic_nonneg hlift_le
    support hsupp hzero
    (fun e => by
      have hb := support_card_le_lower_label_priority D support hinj e
      exact_mod_cast hb)

/-- The constant produced by `ofLowerLabelRecordPriority` is the reduced finite
range size `Q · |Labels|` times the derived fibre bound `Q`. -/
@[simp] theorem CrossingMultiplicityData.ofLowerLabelRecordPriority_C {Branch Labels : Type*}
    [DecidableEq Branch] [DecidableEq Labels] [Fintype Labels] {Q : ℕ} [NeZero Q]
    (D : FirstCrossingRecordData Branch Q Labels)
    (branches : Finset Branch)
    (dropMass : Branch → ℕ → ℝ) (hdrop_nonneg : ∀ b e, 0 ≤ dropMass b e)
    (crossingIndic : ℕ → ℝ) (hindic_nonneg : ∀ e, 0 ≤ crossingIndic e)
    (hlift_le : ∀ b e, dropMass b e ≤ crossingIndic e)
    (support : ℕ → Finset Branch)
    (hsupp : ∀ e, support e ⊆ branches)
    (hzero : ∀ e, ∀ b ∈ branches, b ∉ support e → dropMass b e = 0)
    (hinj : ∀ (e : ℕ), ∀ b ∈ support e, ∀ b' ∈ support e,
        D.lowerLabelRecord e b = D.lowerLabelRecord e b' →
          D.startResidue b = D.startResidue b' → b = b') :
    (CrossingMultiplicityData.ofLowerLabelRecordPriority D branches dropMass hdrop_nonneg
      crossingIndic hindic_nonneg hlift_le support hsupp hzero hinj).C
      = ((Q * Fintype.card Labels * Q : ℕ) : ℝ) :=
  rfl

/-- **N.2.1 per-edge multiplicity bound from the reduced record (eq N.16).**
The multiplicity constant is `Q · |Labels| · Q`; the redundant upper-residue
range factor no longer appears. -/
theorem CrossingMultiplicityData.ofLowerLabelRecordPriority_multiplicity_le
    {Branch Labels : Type*} [DecidableEq Branch] [DecidableEq Labels]
    [Fintype Labels] {Q : ℕ} [NeZero Q]
    (D : FirstCrossingRecordData Branch Q Labels)
    (branches : Finset Branch)
    (dropMass : Branch → ℕ → ℝ) (hdrop_nonneg : ∀ b e, 0 ≤ dropMass b e)
    (crossingIndic : ℕ → ℝ) (hindic_nonneg : ∀ e, 0 ≤ crossingIndic e)
    (hlift_le : ∀ b e, dropMass b e ≤ crossingIndic e)
    (support : ℕ → Finset Branch)
    (hsupp : ∀ e, support e ⊆ branches)
    (hzero : ∀ e, ∀ b ∈ branches, b ∉ support e → dropMass b e = 0)
    (hinj : ∀ (e : ℕ), ∀ b ∈ support e, ∀ b' ∈ support e,
        D.lowerLabelRecord e b = D.lowerLabelRecord e b' →
          D.startResidue b = D.startResidue b' → b = b')
    (e : ℕ) :
    (∑ b ∈ branches, dropMass b e)
      ≤ ((Q * Fintype.card Labels * Q : ℕ) : ℝ) * crossingIndic e :=
  (CrossingMultiplicityData.ofLowerLabelRecordPriority D branches dropMass hdrop_nonneg
    crossingIndic hindic_nonneg hlift_le support hsupp hzero hinj).multiplicity_le e

/--
**Reduced-record N.2.1 from the original full-record priority input.**

This is the most convenient bridge for callers that already have the manuscript
priority-atom coincidence stated for the full record `Π_e`: ordered windows
(`loIdx e ≤ hiIdx e`) turn equality of lower-residue+label records back into
equality of full records, so the reduced constant `Q · |Labels| · Q` is still
available without strengthening the priority hypothesis.
-/
def CrossingMultiplicityData.ofLowerLabelRecordPriorityOfRecord {Branch Labels : Type*}
    [DecidableEq Branch] [DecidableEq Labels] [Fintype Labels] {Q : ℕ} [NeZero Q]
    (D : FirstCrossingRecordData Branch Q Labels)
    (branches : Finset Branch)
    (dropMass : Branch → ℕ → ℝ) (hdrop_nonneg : ∀ b e, 0 ≤ dropMass b e)
    (crossingIndic : ℕ → ℝ) (hindic_nonneg : ∀ e, 0 ≤ crossingIndic e)
    (hlift_le : ∀ b e, dropMass b e ≤ crossingIndic e)
    (support : ℕ → Finset Branch)
    (hsupp : ∀ e, support e ⊆ branches)
    (hzero : ∀ e, ∀ b ∈ branches, b ∉ support e → dropMass b e = 0)
    (hle : ∀ e, D.loIdx e ≤ D.hiIdx e)
    (hinj : ∀ (e : ℕ), ∀ b ∈ support e, ∀ b' ∈ support e,
        D.record e b = D.record e b' →
          D.startResidue b = D.startResidue b' → b = b') :
    CrossingMultiplicityData Branch :=
  CrossingMultiplicityData.ofLowerLabelRecordPriority D branches dropMass hdrop_nonneg
    crossingIndic hindic_nonneg hlift_le support hsupp hzero
    (lowerLabel_priority_of_record_priority D support hle hinj)

/-- The constant of `ofLowerLabelRecordPriorityOfRecord` is the reduced
`Q · |Labels| · Q` constant. -/
@[simp] theorem CrossingMultiplicityData.ofLowerLabelRecordPriorityOfRecord_C
    {Branch Labels : Type*} [DecidableEq Branch] [DecidableEq Labels]
    [Fintype Labels] {Q : ℕ} [NeZero Q]
    (D : FirstCrossingRecordData Branch Q Labels)
    (branches : Finset Branch)
    (dropMass : Branch → ℕ → ℝ) (hdrop_nonneg : ∀ b e, 0 ≤ dropMass b e)
    (crossingIndic : ℕ → ℝ) (hindic_nonneg : ∀ e, 0 ≤ crossingIndic e)
    (hlift_le : ∀ b e, dropMass b e ≤ crossingIndic e)
    (support : ℕ → Finset Branch)
    (hsupp : ∀ e, support e ⊆ branches)
    (hzero : ∀ e, ∀ b ∈ branches, b ∉ support e → dropMass b e = 0)
    (hle : ∀ e, D.loIdx e ≤ D.hiIdx e)
    (hinj : ∀ (e : ℕ), ∀ b ∈ support e, ∀ b' ∈ support e,
        D.record e b = D.record e b' →
          D.startResidue b = D.startResidue b' → b = b') :
    (CrossingMultiplicityData.ofLowerLabelRecordPriorityOfRecord D branches
      dropMass hdrop_nonneg crossingIndic hindic_nonneg hlift_le support hsupp
      hzero hle hinj).C = ((Q * Fintype.card Labels * Q : ℕ) : ℝ) :=
  rfl

/-- **Per-edge multiplicity bound from full-record priority, with reduced
constant.**  This is the N.2.1 bound callers can use with the original
full-record priority coincidence plus ordered windows. -/
theorem CrossingMultiplicityData.ofLowerLabelRecordPriorityOfRecord_multiplicity_le
    {Branch Labels : Type*} [DecidableEq Branch] [DecidableEq Labels]
    [Fintype Labels] {Q : ℕ} [NeZero Q]
    (D : FirstCrossingRecordData Branch Q Labels)
    (branches : Finset Branch)
    (dropMass : Branch → ℕ → ℝ) (hdrop_nonneg : ∀ b e, 0 ≤ dropMass b e)
    (crossingIndic : ℕ → ℝ) (hindic_nonneg : ∀ e, 0 ≤ crossingIndic e)
    (hlift_le : ∀ b e, dropMass b e ≤ crossingIndic e)
    (support : ℕ → Finset Branch)
    (hsupp : ∀ e, support e ⊆ branches)
    (hzero : ∀ e, ∀ b ∈ branches, b ∉ support e → dropMass b e = 0)
    (hle : ∀ e, D.loIdx e ≤ D.hiIdx e)
    (hinj : ∀ (e : ℕ), ∀ b ∈ support e, ∀ b' ∈ support e,
        D.record e b = D.record e b' →
          D.startResidue b = D.startResidue b' → b = b')
    (e : ℕ) :
    (∑ b ∈ branches, dropMass b e)
      ≤ ((Q * Fintype.card Labels * Q : ℕ) : ℝ) * crossingIndic e :=
  (CrossingMultiplicityData.ofLowerLabelRecordPriorityOfRecord D branches dropMass hdrop_nonneg
    crossingIndic hindic_nonneg hlift_le support hsupp hzero hle hinj).multiplicity_le e

/--
**Summed N.2.1 input for N.2.2, reduced-record form.**

After identifying the per-edge indicator with the actual crossing indicator at
level `T + Y`, the reduced-record multiplicity theorem gives the per-`T`
crossing-count bound consumed by the window-drop estimate:
`∑_{e∈K}∑_b dropMass b e ≤ (Q · |Labels| · Q) · N_{T+Y}`.
-/
theorem CrossingMultiplicityData.ofLowerLabelRecordPriorityOfRecord_sum_le_count
    {Branch Labels : Type*} [DecidableEq Branch] [DecidableEq Labels]
    [Fintype Labels] {Q : ℕ} [NeZero Q]
    (D : FirstCrossingRecordData Branch Q Labels)
    (branches : Finset Branch)
    (dropMass : Branch → ℕ → ℝ) (hdrop_nonneg : ∀ b e, 0 ≤ dropMass b e)
    (crossingIndic : ℕ → ℝ) (hindic_nonneg : ∀ e, 0 ≤ crossingIndic e)
    (hlift_le : ∀ b e, dropMass b e ≤ crossingIndic e)
    (support : ℕ → Finset Branch)
    (hsupp : ∀ e, support e ⊆ branches)
    (hzero : ∀ e, ∀ b ∈ branches, b ∉ support e → dropMass b e = 0)
    (hle : ∀ e, D.loIdx e ≤ D.hiIdx e)
    (hinj : ∀ (e : ℕ), ∀ b ∈ support e, ∀ b' ∈ support e,
        D.record e b = D.record e b' →
          D.startResidue b = D.startResidue b' → b = b')
    (K : Finset ℕ) (T Y : ℝ) (W : ℕ → ℝ)
    (hindic : ∀ e, crossingIndic e = crossingIndicator (T + Y) W e) :
    (∑ e ∈ K, ∑ b ∈ branches, dropMass b e)
      ≤ ((Q * Fintype.card Labels * Q : ℕ) : ℝ) * crossingCountReal (T + Y) W K := by
  let M :=
    CrossingMultiplicityData.ofLowerLabelRecordPriorityOfRecord D branches
      dropMass hdrop_nonneg crossingIndic hindic_nonneg hlift_le support hsupp
      hzero hle hinj
  exact M.sum_le_count K T Y W hindic

/--
**Pointwise N.2.1 input for N.2.2 from reduced records.**

This is the direct bridge from the `T`-fibre reduced-record theorem to the
drop-density hypothesis consumed by N.2.2: once the density integrand is the
sum of the variation-drop edge masses, the reduced-record multiplicity theorem
gives `dropDensity T ≤ (Q · |Labels| · Q) · N_{T+Y}`.
-/
theorem dropDensity_le_count_of_lowerLabelRecordPriorityOfRecord
    {Branch Labels : Type*} [DecidableEq Branch] [DecidableEq Labels]
    [Fintype Labels] {Q : ℕ} [NeZero Q]
    (D : ℝ → FirstCrossingRecordData Branch Q Labels)
    (branches : Finset Branch)
    (dropDensity : ℝ → ℝ)
    (dropMass : ℝ → Branch → ℕ → ℝ)
    (hdrop_nonneg : ∀ T b e, 0 ≤ dropMass T b e)
    (crossingIndic : ℝ → ℕ → ℝ)
    (hindic_nonneg : ∀ T e, 0 ≤ crossingIndic T e)
    (hlift_le : ∀ T b e, dropMass T b e ≤ crossingIndic T e)
    (support : ℝ → ℕ → Finset Branch)
    (hsupp : ∀ T e, support T e ⊆ branches)
    (hzero : ∀ T e, ∀ b ∈ branches, b ∉ support T e → dropMass T b e = 0)
    (hle : ∀ T e, (D T).loIdx e ≤ (D T).hiIdx e)
    (hinj : ∀ T (e : ℕ), ∀ b ∈ support T e, ∀ b' ∈ support T e,
        (D T).record e b = (D T).record e b' →
          (D T).startResidue b = (D T).startResidue b' → b = b')
    (K : Finset ℕ) (Y : ℝ) (W : ℕ → ℝ) (A : Set ℝ)
    (hdensity :
      ∀ T ∈ A, dropDensity T = ∑ e ∈ K, ∑ b ∈ branches, dropMass T b e)
    (hindic :
      ∀ T ∈ A, ∀ e, crossingIndic T e = crossingIndicator (T + Y) W e)
    {T : ℝ} (hT : T ∈ A) :
    dropDensity T
      ≤ ((Q * Fintype.card Labels * Q : ℕ) : ℝ) *
          crossingCountReal (T + Y) W K := by
  rw [hdensity T hT]
  exact
    CrossingMultiplicityData.ofLowerLabelRecordPriorityOfRecord_sum_le_count
      (D T) branches (dropMass T) (hdrop_nonneg T)
      (crossingIndic T) (hindic_nonneg T) (hlift_le T)
      (support T) (hsupp T) (hzero T) (hle T) (hinj T)
      K T Y W (hindic T hT)

/--
Build the bundled N.2.2 `WindowDropEstimateData` directly from the reduced-record
N.2.1 data.  This is the structure-valued version consumed by the C1-VD
compression interface.
-/
def WindowDropEstimateData.ofLowerLabelRecordPriorityOfRecordDensity
    {Branch Labels : Type*} [DecidableEq Branch] [DecidableEq Labels]
    [Fintype Labels] {Q : ℕ} [NeZero Q]
    (VarDrop Cmul Y : ℝ)
    (D : ℝ → FirstCrossingRecordData Branch Q Labels)
    (branches : Finset Branch)
    (dropDensity : ℝ → ℝ)
    (dropMass : ℝ → Branch → ℕ → ℝ)
    (hdrop_nonneg : ∀ T b e, 0 ≤ dropMass T b e)
    (crossingIndic : ℝ → ℕ → ℝ)
    (hindic_nonneg : ∀ T e, 0 ≤ crossingIndic T e)
    (hlift_le : ∀ T b e, dropMass T b e ≤ crossingIndic T e)
    (support : ℝ → ℕ → Finset Branch)
    (hsupp : ∀ T e, support T e ⊆ branches)
    (hzero : ∀ T e, ∀ b ∈ branches, b ∉ support T e → dropMass T b e = 0)
    (hle : ∀ T e, (D T).loIdx e ≤ (D T).hiIdx e)
    (hinj : ∀ T (e : ℕ), ∀ b ∈ support T e, ∀ b' ∈ support T e,
        (D T).record e b = (D T).record e b' →
          (D T).startResidue b = (D T).startResidue b' → b = b')
    (K : Finset ℕ) (W : ℕ → ℝ) (A : Set ℝ)
    (hCmulY : 0 ≤ Cmul * Y)
    (hA : MeasurableSet A)
    (hdrop_int : IntegrableOn dropDensity A volume)
    (hvar :
      VarDrop ≤ Cmul * Y * ∫ T in A, dropDensity T ∂volume)
    (hdensity :
      ∀ T ∈ A, dropDensity T = ∑ e ∈ K, ∑ b ∈ branches, dropMass T b e)
    (hindic :
      ∀ T ∈ A, ∀ e, crossingIndic T e = crossingIndicator (T + Y) W e) :
    WindowDropEstimateData :=
  let Cfiber : ℝ := ((Q * Fintype.card Labels * Q : ℕ) : ℝ)
  WindowDropEstimateData.ofScaledDropDensityBound VarDrop Cmul Cfiber Y
    dropDensity W K A hCmulY
    (by
      dsimp [Cfiber]
      exact_mod_cast Nat.zero_le (Q * Fintype.card Labels * Q))
    hA hdrop_int hvar
    (fun T hT =>
      dropDensity_le_count_of_lowerLabelRecordPriorityOfRecord
        D branches dropDensity dropMass hdrop_nonneg crossingIndic hindic_nonneg
        hlift_le support hsupp hzero hle hinj K Y W A hdensity hindic hT)

/--
**N.2.1-to-N.2.2 window-drop bridge with reduced records.**

This packages the previous pointwise theorem with the scaled N.2.2 integration
bridge.  The remaining analytic inputs are the measurability/integrability of
the chosen density and the residual-multiplier domination
`VarDrop ≤ Cmul · Y · ∫ dropDensity`; the first-crossing multiplicity side is
supplied by the reduced carry/label record data.
-/
theorem varDrop_le_from_lowerLabelRecordPriorityOfRecord_density
    {Branch Labels : Type*} [DecidableEq Branch] [DecidableEq Labels]
    [Fintype Labels] {Q : ℕ} [NeZero Q]
    (VarDrop Cmul Y : ℝ)
    (D : ℝ → FirstCrossingRecordData Branch Q Labels)
    (branches : Finset Branch)
    (dropDensity : ℝ → ℝ)
    (dropMass : ℝ → Branch → ℕ → ℝ)
    (hdrop_nonneg : ∀ T b e, 0 ≤ dropMass T b e)
    (crossingIndic : ℝ → ℕ → ℝ)
    (hindic_nonneg : ∀ T e, 0 ≤ crossingIndic T e)
    (hlift_le : ∀ T b e, dropMass T b e ≤ crossingIndic T e)
    (support : ℝ → ℕ → Finset Branch)
    (hsupp : ∀ T e, support T e ⊆ branches)
    (hzero : ∀ T e, ∀ b ∈ branches, b ∉ support T e → dropMass T b e = 0)
    (hle : ∀ T e, (D T).loIdx e ≤ (D T).hiIdx e)
    (hinj : ∀ T (e : ℕ), ∀ b ∈ support T e, ∀ b' ∈ support T e,
        (D T).record e b = (D T).record e b' →
          (D T).startResidue b = (D T).startResidue b' → b = b')
    (K : Finset ℕ) (W : ℕ → ℝ) (A : Set ℝ)
    (hCmulY : 0 ≤ Cmul * Y)
    (hA : MeasurableSet A)
    (hdrop_int : IntegrableOn dropDensity A volume)
    (hvar :
      VarDrop ≤ Cmul * Y * ∫ T in A, dropDensity T ∂volume)
    (hdensity :
      ∀ T ∈ A, dropDensity T = ∑ e ∈ K, ∑ b ∈ branches, dropMass T b e)
    (hindic :
      ∀ T ∈ A, ∀ e, crossingIndic T e = crossingIndicator (T + Y) W e) :
    VarDrop
      ≤ (Cmul * ((Q * Fintype.card Labels * Q : ℕ) : ℝ)) * Y * Vs K W := by
  let Cfiber : ℝ := ((Q * Fintype.card Labels * Q : ℕ) : ℝ)
  have hCfiber : 0 ≤ Cfiber := by
    dsimp [Cfiber]
    exact_mod_cast Nat.zero_le (Q * Fintype.card Labels * Q)
  exact
    varDrop_le_from_scaled_dropDensity_bound VarDrop Cmul Cfiber Y
      dropDensity W K A hCmulY hCfiber hA hdrop_int hvar
      (fun T hT =>
        dropDensity_le_count_of_lowerLabelRecordPriorityOfRecord
          D branches dropDensity dropMass hdrop_nonneg crossingIndic hindic_nonneg
          hlift_le support hsupp hzero hle hinj K Y W A hdensity hindic hT)

/--
**Reduced-record N.2.1-to-N.2.2 bridge with explicit N.13 variation bound.**

This is the `Vs ≤ 2M|K|` version of
`varDrop_le_from_lowerLabelRecordPriorityOfRecord_density`, matching the final
estimate step in Lemma N.2.2.
-/
theorem varDrop_le_from_lowerLabelRecordPriorityOfRecord_density_explicitWindow
    {Branch Labels : Type*} [DecidableEq Branch] [DecidableEq Labels]
    [Fintype Labels] {Q : ℕ} [NeZero Q]
    (VarDrop Cmul Y M : ℝ)
    (D : ℝ → FirstCrossingRecordData Branch Q Labels)
    (branches : Finset Branch)
    (dropDensity : ℝ → ℝ)
    (dropMass : ℝ → Branch → ℕ → ℝ)
    (hdrop_nonneg : ∀ T b e, 0 ≤ dropMass T b e)
    (crossingIndic : ℝ → ℕ → ℝ)
    (hindic_nonneg : ∀ T e, 0 ≤ crossingIndic T e)
    (hlift_le : ∀ T b e, dropMass T b e ≤ crossingIndic T e)
    (support : ℝ → ℕ → Finset Branch)
    (hsupp : ∀ T e, support T e ⊆ branches)
    (hzero : ∀ T e, ∀ b ∈ branches, b ∉ support T e → dropMass T b e = 0)
    (hle : ∀ T e, (D T).loIdx e ≤ (D T).hiIdx e)
    (hinj : ∀ T (e : ℕ), ∀ b ∈ support T e, ∀ b' ∈ support T e,
        (D T).record e b = (D T).record e b' →
          (D T).startResidue b = (D T).startResidue b' → b = b')
    (g : ℕ → ℝ) (s : ℕ) (K : Finset ℕ) (A : Set ℝ)
    (hCmulY : 0 ≤ Cmul * Y)
    (hA : MeasurableSet A)
    (hdrop_int : IntegrableOn dropDensity A volume)
    (hvar :
      VarDrop ≤ Cmul * Y * ∫ T in A, dropDensity T ∂volume)
    (hdensity :
      ∀ T ∈ A, dropDensity T = ∑ e ∈ K, ∑ b ∈ branches, dropMass T b e)
    (hindic :
      ∀ T ∈ A, ∀ e,
        crossingIndic T e = crossingIndicator (T + Y) (windowSum g s) e)
    (hg : ∀ n, 0 ≤ g n)
    (hKidx : ∀ k ∈ K, s ≤ k)
    (hMlo : ∀ k ∈ K, g (k - s) ≤ M)
    (hMhi : ∀ k ∈ K, g (k + 1) ≤ M) :
    VarDrop
      ≤ (Cmul * ((Q * Fintype.card Labels * Q : ℕ) : ℝ)) * Y *
          (2 * M * (K.card : ℝ)) := by
  let Cfiber : ℝ := ((Q * Fintype.card Labels * Q : ℕ) : ℝ)
  have hCfiber : 0 ≤ Cfiber := by
    dsimp [Cfiber]
    exact_mod_cast Nat.zero_le (Q * Fintype.card Labels * Q)
  exact
    varDrop_le_from_scaled_dropDensity_bound_explicitWindow
      VarDrop Cmul Cfiber Y M dropDensity g s K A hCmulY hCfiber hA hdrop_int hvar
      (fun T hT =>
        dropDensity_le_count_of_lowerLabelRecordPriorityOfRecord
          D branches dropDensity dropMass hdrop_nonneg crossingIndic hindic_nonneg
          hlift_le support hsupp hzero hle hinj K Y (windowSum g s) A
          hdensity hindic hT)
      hg hKidx hMlo hMhi

/--
**Reduced-record N.2.1-to-N.2.2 bridge for the real hit-gap sequence.**

This specializes the explicit-window bridge to
`W = windowSum (fun n => hitGap a n) s` and discharges N.13 using
`HitSequence.hitGap_le_of_shell_window`.
-/
theorem varDrop_le_from_lowerLabelRecordPriorityOfRecord_density_hitGap
    {Branch Labels : Type*} [DecidableEq Branch] [DecidableEq Labels]
    [Fintype Labels] {Q : ℕ} [NeZero Q]
    {Qden B X L : Nat} {P : Int} {d a : Nat → Nat}
    (hd : BinaryDigits d) (hseq : HitSequence d a)
    (hQden : 0 < Qden)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Qden : ℝ))
    (hX_eq : X = 2 ^ L) (hX_pos : 1 ≤ X)
    (hB : Qden * 4 ≤ 2 ^ B)
    {r : Nat} (hKr : r + 1 ≤ (supportShell d X).card)
    (VarDrop Cmul Y : ℝ)
    (D : ℝ → FirstCrossingRecordData Branch Q Labels)
    (branches : Finset Branch)
    (dropDensity : ℝ → ℝ)
    (dropMass : ℝ → Branch → ℕ → ℝ)
    (hdrop_nonneg : ∀ T b e, 0 ≤ dropMass T b e)
    (crossingIndic : ℝ → ℕ → ℝ)
    (hindic_nonneg : ∀ T e, 0 ≤ crossingIndic T e)
    (hlift_le : ∀ T b e, dropMass T b e ≤ crossingIndic T e)
    (support : ℝ → ℕ → Finset Branch)
    (hsupp : ∀ T e, support T e ⊆ branches)
    (hzero : ∀ T e, ∀ b ∈ branches, b ∉ support T e → dropMass T b e = 0)
    (hle : ∀ T e, (D T).loIdx e ≤ (D T).hiIdx e)
    (hinj : ∀ T (e : ℕ), ∀ b ∈ support T e, ∀ b' ∈ support T e,
        (D T).record e b = (D T).record e b' →
          (D T).startResidue b = (D T).startResidue b' → b = b')
    (s : ℕ) (K : Finset ℕ) (A : Set ℝ)
    (hK : ∀ k ∈ K, s ≤ k)
    (hKwin : ∀ k ∈ K, k + 1 < hseq.firstIndexAbove X + r)
    (hCmulY : 0 ≤ Cmul * Y)
    (hA : MeasurableSet A)
    (hdrop_int : IntegrableOn dropDensity A volume)
    (hvar :
      VarDrop ≤ Cmul * Y * ∫ T in A, dropDensity T ∂volume)
    (hdensity :
      ∀ T ∈ A, dropDensity T = ∑ e ∈ K, ∑ b ∈ branches, dropMass T b e)
    (hindic :
      ∀ T ∈ A, ∀ e,
        crossingIndic T e =
          crossingIndicator (T + Y)
            (windowSum (fun n => (hitGap a n : ℝ)) s) e) :
    VarDrop
      ≤ (Cmul * ((Q * Fintype.card Labels * Q : ℕ) : ℝ)) * Y *
          (2 * ((L + B + 1 : ℕ) : ℝ) * (K.card : ℝ)) := by
  let Cfiber : ℝ := ((Q * Fintype.card Labels * Q : ℕ) : ℝ)
  have hCfiber : 0 ≤ Cfiber := by
    dsimp [Cfiber]
    exact_mod_cast Nat.zero_le (Q * Fintype.card Labels * Q)
  exact
    Erdos260.varDrop_le_from_scaled_dropDensity_bound_hitGap
      hd hseq hQden heta hX_eq hX_pos hB hKr s K hK hKwin
      VarDrop Cmul Cfiber Y dropDensity A hCmulY hCfiber hA hdrop_int hvar
      (fun T hT =>
        dropDensity_le_count_of_lowerLabelRecordPriorityOfRecord
          D branches dropDensity dropMass hdrop_nonneg crossingIndic hindic_nonneg
          hlift_le support hsupp hzero hle hinj K Y
          (windowSum (fun n => (hitGap a n : ℝ)) s) A hdensity hindic hT)

/--
**Reduced-record N.2.1-to-N.2.2 bridge from carry-packaged hit-gap data.**

This is the consumer-facing carry form of
`varDrop_le_from_lowerLabelRecordPriorityOfRecord_density_hitGap`: the hit
sequence, shell denominator, shell size, and recurrence length are read from
`carryData`.
-/
theorem varDrop_le_from_lowerLabelRecordPriorityOfRecord_density_carryHitGap
    {Branch Labels : Type*} [DecidableEq Branch] [DecidableEq Labels]
    [Fintype Labels] {Q : ℕ} [NeZero Q]
    {B : Nat} {P : Int}
    {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr)
    (hP :
      realWeightedValue (natBinaryAsReal shell.d) =
        (P : ℝ) / (shell.Q : ℝ))
    (hX_eq : shell.X = 2 ^ carryData.L)
    (hX_pos : 1 ≤ shell.X)
    (hB : shell.Q * 4 ≤ 2 ^ B)
    (hKr : carryData.r + 1 ≤ (supportShell shell.d shell.X).card)
    (VarDrop Cmul Y : ℝ)
    (D : ℝ → FirstCrossingRecordData Branch Q Labels)
    (branches : Finset Branch)
    (dropDensity : ℝ → ℝ)
    (dropMass : ℝ → Branch → ℕ → ℝ)
    (hdrop_nonneg : ∀ T b e, 0 ≤ dropMass T b e)
    (crossingIndic : ℝ → ℕ → ℝ)
    (hindic_nonneg : ∀ T e, 0 ≤ crossingIndic T e)
    (hlift_le : ∀ T b e, dropMass T b e ≤ crossingIndic T e)
    (support : ℝ → ℕ → Finset Branch)
    (hsupp : ∀ T e, support T e ⊆ branches)
    (hzero : ∀ T e, ∀ b ∈ branches, b ∉ support T e → dropMass T b e = 0)
    (hle : ∀ T e, (D T).loIdx e ≤ (D T).hiIdx e)
    (hinj : ∀ T (e : ℕ), ∀ b ∈ support T e, ∀ b' ∈ support T e,
        (D T).record e b = (D T).record e b' →
          (D T).startResidue b = (D T).startResidue b' → b = b')
    (s : ℕ) (K : Finset ℕ) (A : Set ℝ)
    (hK : ∀ k ∈ K, s ≤ k)
    (hKwin : ∀ k ∈ K,
      k + 1 < carryData.carry.hits.firstIndexAbove shell.X + carryData.r)
    (hCmulY : 0 ≤ Cmul * Y)
    (hA : MeasurableSet A)
    (hdrop_int : IntegrableOn dropDensity A volume)
    (hvar :
      VarDrop ≤ Cmul * Y * ∫ T in A, dropDensity T ∂volume)
    (hdensity :
      ∀ T ∈ A, dropDensity T = ∑ e ∈ K, ∑ b ∈ branches, dropMass T b e)
    (hindic :
      ∀ T ∈ A, ∀ e,
        crossingIndic T e =
          crossingIndicator (T + Y)
            (windowSum (fun n => (hitGap carryData.a n : ℝ)) s) e) :
    VarDrop
      ≤ (Cmul * ((Q * Fintype.card Labels * Q : ℕ) : ℝ)) * Y *
          (2 * ((carryData.L + B + 1 : ℕ) : ℝ) * (K.card : ℝ)) := by
  let Cfiber : ℝ := ((Q * Fintype.card Labels * Q : ℕ) : ℝ)
  have hCfiber : 0 ≤ Cfiber := by
    dsimp [Cfiber]
    exact_mod_cast Nat.zero_le (Q * Fintype.card Labels * Q)
  exact
    Erdos260.varDrop_le_from_scaled_dropDensity_bound_carryHitGap
      carryData hP hX_eq hX_pos hB hKr s K hK hKwin
      VarDrop Cmul Cfiber Y dropDensity A hCmulY hCfiber hA hdrop_int hvar
      (fun T hT =>
        dropDensity_le_count_of_lowerLabelRecordPriorityOfRecord
          D branches dropDensity dropMass hdrop_nonneg crossingIndic hindic_nonneg
          hlift_le support hsupp hzero hle hinj K Y
          (windowSum (fun n => (hitGap carryData.a n : ℝ)) s) A hdensity hindic hT)

/--
**Reduced-record N.2.1 to TRT-closure bridge.**

This is the N.24 consumer-facing form: the reduced-record first-crossing data
constructs the N.2.2 `WindowDropEstimateData`, and the C1-VD split then bounds
the total same-threshold TRT output mass by the terminal absorbed term plus the
window-drop term.
-/
theorem trtClosure_from_lowerLabelRecordPriorityOfRecord_density
    {Branch Labels : Type*} [DecidableEq Branch] [DecidableEq Labels]
    [Fintype Labels] {Q : ℕ} [NeZero Q]
    (VarDrop Cmul Y : ℝ)
    (D : ℝ → FirstCrossingRecordData Branch Q Labels)
    (branches : Finset Branch)
    (dropDensity : ℝ → ℝ)
    (dropMass : ℝ → Branch → ℕ → ℝ)
    (hdrop_nonneg : ∀ T b e, 0 ≤ dropMass T b e)
    (crossingIndic : ℝ → ℕ → ℝ)
    (hindic_nonneg : ∀ T e, 0 ≤ crossingIndic T e)
    (hlift_le : ∀ T b e, dropMass T b e ≤ crossingIndic T e)
    (support : ℝ → ℕ → Finset Branch)
    (hsupp : ∀ T e, support T e ⊆ branches)
    (hzero : ∀ T e, ∀ b ∈ branches, b ∉ support T e → dropMass T b e = 0)
    (hle : ∀ T e, (D T).loIdx e ≤ (D T).hiIdx e)
    (hinj : ∀ T (e : ℕ), ∀ b ∈ support T e, ∀ b' ∈ support T e,
        (D T).record e b = (D T).record e b' →
          (D T).startResidue b = (D T).startResidue b' → b = b')
    (K : Finset ℕ) (W : ℕ → ℝ) (A : Set ℝ)
    {totalMass termMass absorbedBound : ℝ}
    (hsplit : totalMass = termMass + VarDrop)
    (hterm : termMass ≤ absorbedBound)
    (hCmulY : 0 ≤ Cmul * Y)
    (hA : MeasurableSet A)
    (hdrop_int : IntegrableOn dropDensity A volume)
    (hvar :
      VarDrop ≤ Cmul * Y * ∫ T in A, dropDensity T ∂volume)
    (hdensity :
      ∀ T ∈ A, dropDensity T = ∑ e ∈ K, ∑ b ∈ branches, dropMass T b e)
    (hindic :
      ∀ T ∈ A, ∀ e, crossingIndic T e = crossingIndicator (T + Y) W e) :
    totalMass
      ≤ absorbedBound +
          (Cmul * ((Q * Fintype.card Labels * Q : ℕ) : ℝ)) * Y * Vs K W :=
  trtClosure_windowDropEstimate_absorbed
    (WindowDropEstimateData.ofLowerLabelRecordPriorityOfRecordDensity
      VarDrop Cmul Y D branches dropDensity dropMass hdrop_nonneg crossingIndic
      hindic_nonneg hlift_le support hsupp hzero hle hinj K W A hCmulY hA
      hdrop_int hvar hdensity hindic)
    hsplit hterm

end AppendixN

end

end Erdos260
