import Mathlib
import Erdos260.AppendixN_Variation
import Erdos260.IntegerCarry
import Erdos260.Ledger
import Erdos260.HitSequence
import Erdos260.CNL

/-!
# Appendix N.2.1: fixed-crossing-edge multiplicity from carry determinacy

This module pushes the **N.2.1 fixed-crossing-edge multiplicity** bound of
`proof_v4.tex` (Lemma N.2.1, eq N.16/N.17) toward a real theorem.

`Erdos260.AppendixN.CrossingMultiplicityData.ofFirstCrossingRecord`
(in `AppendixN_Variation.lean`) already *derives* the per-edge multiplicity bound
`∑_b μ_T(Ω^V_{b,e}) ≤ C · 𝟙_{X_e}` from two facts: (i) each variation-drop lift
has mass at most the unit represented-edge mass, and (ii) a per-edge
`support : ℕ → Finset Branch` with `(support e).card ≤ C` (the `C`-to-one count)
and `dropMass = 0` off the support.  What that interface *assumes* is the
`C`-to-one count itself.

Here we **produce** such a bounded support / `C`-to-one count from the
**carry congruences** of `Erdos260.IntegerCarry`.  The manuscript records, for a
drop state `ζ` assigned to edge `e`, the first-crossing data (eq N.17)
`Π_e(ζ) = (e, R̄_{k-s}, R̄_{k+1}, λ_side, λ_tie, λ_piv)`, where the carries
`R̄` are taken **modulo the denominator `Q`**, and `λ_side, λ_tie, λ_piv` range
over finite sets (the side/tie/pivot labels, finite by Lemma N.2.0).  The map
`b ↦ Π_e(b)` is `C_Q`-to-one and its range has `O_Q(1)` elements, so at most
`C_Q · (range size)` branches share a fixed record (eq N.16 follows).

## What is formalized

* `support_card_le_image_mul`, `support_card_le_fintype_mul`,
  `support_card_le_residue_label` — the **faithful counting core**: a record map
  `record : Branch → ρ` whose fibres on `support` each have at most `mult`
  branches (the `C_Q`-to-one count) forces `support.card ≤ |range| · mult`, and
  when `ρ = ZMod Q × ZMod Q × Labels` the range size is the genuine finite number
  `Q · Q · |Labels|`.  Built on `card_le_card_image_mul_of_fiber_card_le`
  (`CNL.lean`), `Finset.card_le_univ`, and `ZMod.card`.
* `integerCarry_zmod_succ`, `integerCarry_zmod_succ_eq_of_carry_eq`,
  `integerCarry_zmod_add_zero_run` — the **carry-residue determinacy** connecting
  the recorded residues to `IntegerCarry`: the residue mod `Q` at step `N+1` is
  always `2 ·` the residue at `N` (the digit `d (N+1)` drops out mod `Q`,
  `integerCarry_succ_modEq_Q`), hence the recorded residue is genuinely
  determined by the previous residue alone, and over a zero run it is
  `2^h ·` the prior residue (`integerCarry_add_of_zero_digits`).  This is the
  real content that the carry residues live in the size-`Q` set `ZMod Q`.
* `FirstCrossingRecordData`, `FirstCrossingRecordData.record` — the genuine
  first-crossing record (eq N.17), with the residue components built **literally**
  from `integerCarry … : ZMod Q` (so the count is real content, not a vacuous
  re-encoding of the branch index).
* `CrossingMultiplicityData.ofCarryRecord` — the bridge: feeds the faithful
  counting core + genuine residue range into `ofFirstCrossingRecord` to build the
  full N.2.1 bundle with explicit constant `C = Q · Q · |Labels| · mult`.

## Faithful vs conditional

* **Faithful (real theorems):** the fibre-counting core, the range-size
  computation `Q · Q · |Labels|` via `ZMod.card`, and the mod-`Q` carry
  determinacy from `integerCarry_succ_modEq_Q`.
* **Conditional (explicit hypotheses, never `sorry`):** the `C_Q`-to-one fibre
  bound `mult` (the deep injectivity-up-to-`C` from "distinct cylinders ⇒ earlier
  differing active atom"), the finiteness `[Fintype Labels]` of the side/tie/pivot
  labels (Lemma N.2.0 / Appendix L), and the support identification together with
  the unit-lift bound.

There is no `sorry`, `axiom`, or `admit` anywhere in this file.
-/

namespace Erdos260

noncomputable section

open Finset

namespace AppendixN

/-! ## N.2.1.a Faithful counting core (the `C_Q`-to-one × range-size identity)

The combinatorial heart of eq N.16: if a record map is `mult`-to-one on a finite
branch family (each record value carried by at most `mult` branches), then the
family has at most `(range size) · mult` members.  This is the precise meaning of
"the map `(b,ζ) ↦ Π_e(ζ)` is `C_Q`-to-one and its range has `O_Q(1)` elements". -/

/-- **Faithful counting core, general form.** A record map `record : Branch → ρ`
whose fibres over `support` each have at most `mult` branches forces
`support.card ≤ (range size) · mult`, where the range size is the number of record
values actually attained.  Direct application of
`card_le_card_image_mul_of_fiber_card_le`. -/
theorem support_card_le_image_mul {Branch ρ : Type*} [DecidableEq Branch] [DecidableEq ρ]
    (support : Finset Branch) (record : Branch → ρ) (mult : ℕ)
    (hfiber : ∀ y ∈ support.image record,
        (support.filter (fun b => record b = y)).card ≤ mult) :
    support.card ≤ (support.image record).card * mult :=
  card_le_card_image_mul_of_fiber_card_le support record hfiber

/-- **Faithful counting core, finite-record form.** When the record type `ρ` is
finite, the range size is at most `|ρ|`, so a `mult`-to-one record map forces
`support.card ≤ |ρ| · mult`.  This is eq N.16's "`C_Q`-to-one with `O_Q(1)`-size
range". -/
theorem support_card_le_fintype_mul {Branch ρ : Type*} [DecidableEq Branch]
    [DecidableEq ρ] [Fintype ρ]
    (support : Finset Branch) (record : Branch → ρ) (mult : ℕ)
    (hfiber : ∀ y, (support.filter (fun b => record b = y)).card ≤ mult) :
    support.card ≤ Fintype.card ρ * mult := by
  refine (support_card_le_image_mul support record mult
      (fun y _ => hfiber y)).trans ?_
  exact mul_le_mul_left (Finset.card_le_univ _) mult

/-- **Faithful counting core, carry-residue form (eq N.16 / N.17).** Specialising
the finite record type to `ZMod Q × ZMod Q × Labels` — the two window-endpoint
carry residues mod `Q` (eq N.17) together with the finite side/tie/pivot label —
the range size is the genuine finite number `Q · Q · |Labels|` (via `ZMod.card`),
so a `mult`-to-one record map forces `support.card ≤ Q · Q · |Labels| · mult`. -/
theorem support_card_le_residue_label {Branch Labels : Type*} [DecidableEq Branch]
    [DecidableEq Labels] [Fintype Labels] (Q : ℕ) [NeZero Q]
    (support : Finset Branch) (record : Branch → ZMod Q × ZMod Q × Labels) (mult : ℕ)
    (hfiber : ∀ y, (support.filter (fun b => record b = y)).card ≤ mult) :
    support.card ≤ Q * Q * Fintype.card Labels * mult := by
  calc support.card
      ≤ Fintype.card (ZMod Q × ZMod Q × Labels) * mult :=
        support_card_le_fintype_mul support record mult hfiber
    _ = Q * Q * Fintype.card Labels * mult := by
        simp only [Fintype.card_prod, ZMod.card]; ring

/-! ## N.2.1.b Carry-residue determinacy from `IntegerCarry` (eq N.17)

The recorded carries are taken **modulo `Q`**.  The mod-`Q` carry recurrence
(`integerCarry_succ_modEq_Q`) collapses the digit: `R̄_{N+1} = 2 R̄_N` in
`ZMod Q`, *independent of the digit `d (N+1)`*.  Thus the recorded residue is
genuinely determined by the previous residue alone, and over a run of zero digits
it is `2^h ·` the prior residue.  This is the precise sense in which "the carry
recurrence determines all boundary residues … from the recorded residues and the
visible support word", and it pins the residues to the size-`Q` set `ZMod Q`. -/

/-- **Mod-`Q` carry recurrence (eq N.17).** The carry residue mod `Q` doubles at
each step, `R̄_{N+1} = 2 · R̄_N` in `ZMod Q` — the digit `d (N+1)` drops out mod
`Q`.  Real consequence of `integerCarry_succ_modEq_Q`. -/
theorem integerCarry_zmod_succ (Q : ℕ) (P : ℤ) (d : ℕ → ℕ) (N : ℕ) :
    ((integerCarry Q P d (N + 1) : ℤ) : ZMod Q)
      = 2 * ((integerCarry Q P d N : ℤ) : ZMod Q) := by
  have h : ((integerCarry Q P d (N + 1) : ℤ) : ZMod Q)
      = ((2 * integerCarry Q P d N : ℤ) : ZMod Q) :=
    (ZMod.intCast_eq_intCast_iff _ _ _).mpr (integerCarry_succ_modEq_Q Q P d N)
  rw [h]; push_cast; ring

/-- **Carry determinacy (eq N.17).** If two branches have equal carry residues mod
`Q` at step `N`, then they have equal residues at step `N+1`.  Hence the recorded
residue is genuinely determined by the previous residue alone — independent of the
target numerator and the digit at `N+1`.  This is the carry-recurrence determinacy
the first-crossing record relies on. -/
theorem integerCarry_zmod_succ_eq_of_carry_eq (Q : ℕ) (P P' : ℤ) (d d' : ℕ → ℕ) (N : ℕ)
    (h : ((integerCarry Q P d N : ℤ) : ZMod Q) = ((integerCarry Q P' d' N : ℤ) : ZMod Q)) :
    ((integerCarry Q P d (N + 1) : ℤ) : ZMod Q)
      = ((integerCarry Q P' d' (N + 1) : ℤ) : ZMod Q) := by
  rw [integerCarry_zmod_succ, integerCarry_zmod_succ, h]

/-- **Mod-`Q` carry over a zero run (eq N.17).** If all digits in `(N, N+h]`
vanish, the carry residue mod `Q` is `2^h ·` the residue at `N` — the residue on a
window is determined by the boundary residue and the visible support word.  Real
consequence of `integerCarry_add_of_zero_digits`. -/
theorem integerCarry_zmod_add_zero_run (Q : ℕ) (P : ℤ) (d : ℕ → ℕ) (N h : ℕ)
    (hzero : ∀ j : ℕ, N < j → j ≤ N + h → d j = 0) :
    ((integerCarry Q P d (N + h) : ℤ) : ZMod Q)
      = (2 : ZMod Q) ^ h * ((integerCarry Q P d N : ℤ) : ZMod Q) := by
  rw [integerCarry_add_of_zero_digits Q P d N h hzero]; push_cast; ring

/-! ## N.2.1.c The genuine first-crossing record `Π_e` (eq N.17)

The recorded data is built **literally** from `integerCarry … : ZMod Q`, so the
fibre count is real content (the residues range over the size-`Q` set `ZMod Q`),
not a vacuous re-encoding of the branch index. -/

/-- **First-crossing record data (eq N.17).** Per-branch carry data: each branch
carries its rational-target numerator `P` and visible support word `digit` (so its
window-endpoint carry residues are the genuine `integerCarry` residues mod `Q`),
plus the finite side/tie/pivot label `label` of eq N.17/N.17a.  `loIdx`/`hiIdx`
are the two order-`s` window endpoints `k-s`, `k+1` of an edge. -/
structure FirstCrossingRecordData (Branch : Type*) (Q : ℕ) (Labels : Type*) where
  /-- The rational-target numerator of a branch (so `P / Q` is its target). -/
  P : Branch → ℤ
  /-- The visible support word (binary digit sequence) of a branch. -/
  digit : Branch → ℕ → ℕ
  /-- The lower window endpoint `k - s` of edge `e`. -/
  loIdx : ℕ → ℕ
  /-- The upper window endpoint `k + 1` of edge `e`. -/
  hiIdx : ℕ → ℕ
  /-- The finite side/tie/pivot label `(λ_side, λ_tie, λ_piv)` (eq N.17a). -/
  label : Branch → ℕ → Labels

/-- **The recorded data `Π_e(b)` (eq N.17).** The two window-endpoint carry
residues mod `Q` (built genuinely from `integerCarry`) together with the finite
side/tie/pivot label. -/
def FirstCrossingRecordData.record {Branch Labels : Type*} {Q : ℕ}
    (D : FirstCrossingRecordData Branch Q Labels) (e : ℕ) (b : Branch) :
    ZMod Q × ZMod Q × Labels :=
  ((integerCarry Q (D.P b) (D.digit b) (D.loIdx e) : ZMod Q),
   (integerCarry Q (D.P b) (D.digit b) (D.hiIdx e) : ZMod Q),
   D.label b e)

/-- The recorded lower-endpoint residue is the genuine `integerCarry` residue mod
`Q` (the record is not a vacuous re-encoding). -/
@[simp] theorem FirstCrossingRecordData.record_fst {Branch Labels : Type*} {Q : ℕ}
    (D : FirstCrossingRecordData Branch Q Labels) (e : ℕ) (b : Branch) :
    (D.record e b).1 = ((integerCarry Q (D.P b) (D.digit b) (D.loIdx e) : ℤ) : ZMod Q) :=
  rfl

/-! ## N.2.1.d The bridge: produce `CrossingMultiplicityData` (eq N.16)

Feeding the faithful counting core and the genuine residue range into
`CrossingMultiplicityData.ofFirstCrossingRecord` builds the full N.2.1 bundle,
**deriving** the multiplicity bound `∑_b μ_T(Ω^V_{b,e}) ≤ C · 𝟙_{X_e}` with the
explicit constant `C = Q · Q · |Labels| · mult` produced from the carry record. -/

/-- **N.2.1 from the carry record (eq N.16).** Builds the `CrossingMultiplicityData`
bundle with explicit constant `C = Q · Q · |Labels| · mult`, derived from:

* the genuine first-crossing record `D` (carry residues mod `Q` + finite labels);
* the `C_Q`-to-one fibre bound `hfiber` (at most `mult` branches share a recorded
  value on each edge's support) — **conditional** (deep cylinder-injectivity);
* `[Fintype Labels]` — **conditional** (finite pivot/side/tie labels, Lemma N.2.0);
* `hlift_le` — each variation-drop lift `≤` the unit represented-edge mass;
* `support`/`hsupp`/`hzero` — the per-edge support carries all nonzero drop mass.

The `C`-to-one count `(support e).card ≤ C` is the **faithful**
`support_card_le_residue_label`; only `mult`, `[Fintype Labels]`, the lift bound,
and the support identification remain conditional. -/
def CrossingMultiplicityData.ofCarryRecord {Branch Labels : Type*} [DecidableEq Branch]
    [DecidableEq Labels] [Fintype Labels] {Q : ℕ} [NeZero Q]
    (D : FirstCrossingRecordData Branch Q Labels)
    (branches : Finset Branch) (mult : ℕ)
    (dropMass : Branch → ℕ → ℝ) (hdrop_nonneg : ∀ b e, 0 ≤ dropMass b e)
    (crossingIndic : ℕ → ℝ) (hindic_nonneg : ∀ e, 0 ≤ crossingIndic e)
    (hlift_le : ∀ b e, dropMass b e ≤ crossingIndic e)
    (support : ℕ → Finset Branch)
    (hsupp : ∀ e, support e ⊆ branches)
    (hzero : ∀ e, ∀ b ∈ branches, b ∉ support e → dropMass b e = 0)
    (hfiber : ∀ (e : ℕ) (y : ZMod Q × ZMod Q × Labels),
        ((support e).filter (fun b => D.record e b = y)).card ≤ mult) :
    CrossingMultiplicityData Branch :=
  CrossingMultiplicityData.ofFirstCrossingRecord branches
    ((Q * Q * Fintype.card Labels * mult : ℕ) : ℝ) (Nat.cast_nonneg _)
    dropMass hdrop_nonneg crossingIndic hindic_nonneg hlift_le
    support hsupp hzero
    (fun e => by
      have hb := support_card_le_residue_label Q (support e) (D.record e) mult (hfiber e)
      exact_mod_cast hb)

/-- The constant produced by `ofCarryRecord` is the genuine finite range size
`Q · Q · |Labels|` times the `C_Q`-to-one fibre bound `mult`. -/
@[simp] theorem CrossingMultiplicityData.ofCarryRecord_C {Branch Labels : Type*}
    [DecidableEq Branch] [DecidableEq Labels] [Fintype Labels] {Q : ℕ} [NeZero Q]
    (D : FirstCrossingRecordData Branch Q Labels)
    (branches : Finset Branch) (mult : ℕ)
    (dropMass : Branch → ℕ → ℝ) (hdrop_nonneg : ∀ b e, 0 ≤ dropMass b e)
    (crossingIndic : ℕ → ℝ) (hindic_nonneg : ∀ e, 0 ≤ crossingIndic e)
    (hlift_le : ∀ b e, dropMass b e ≤ crossingIndic e)
    (support : ℕ → Finset Branch)
    (hsupp : ∀ e, support e ⊆ branches)
    (hzero : ∀ e, ∀ b ∈ branches, b ∉ support e → dropMass b e = 0)
    (hfiber : ∀ (e : ℕ) (y : ZMod Q × ZMod Q × Labels),
        ((support e).filter (fun b => D.record e b = y)).card ≤ mult) :
    (CrossingMultiplicityData.ofCarryRecord D branches mult dropMass hdrop_nonneg
      crossingIndic hindic_nonneg hlift_le support hsupp hzero hfiber).C
      = ((Q * Q * Fintype.card Labels * mult : ℕ) : ℝ) :=
  rfl

/-- **N.2.1 per-edge multiplicity bound from the carry record (eq N.16).** The
bundle built by `ofCarryRecord` satisfies the genuine per-edge bound
`∑_b μ_T(Ω^V_{b,e}) ≤ (Q · Q · |Labels| · mult) · 𝟙_{X_e}` — the multiplicity is
*derived* from the carry record, not assumed. -/
theorem CrossingMultiplicityData.ofCarryRecord_multiplicity_le {Branch Labels : Type*}
    [DecidableEq Branch] [DecidableEq Labels] [Fintype Labels] {Q : ℕ} [NeZero Q]
    (D : FirstCrossingRecordData Branch Q Labels)
    (branches : Finset Branch) (mult : ℕ)
    (dropMass : Branch → ℕ → ℝ) (hdrop_nonneg : ∀ b e, 0 ≤ dropMass b e)
    (crossingIndic : ℕ → ℝ) (hindic_nonneg : ∀ e, 0 ≤ crossingIndic e)
    (hlift_le : ∀ b e, dropMass b e ≤ crossingIndic e)
    (support : ℕ → Finset Branch)
    (hsupp : ∀ e, support e ⊆ branches)
    (hzero : ∀ e, ∀ b ∈ branches, b ∉ support e → dropMass b e = 0)
    (hfiber : ∀ (e : ℕ) (y : ZMod Q × ZMod Q × Labels),
        ((support e).filter (fun b => D.record e b = y)).card ≤ mult)
    (e : ℕ) :
    (∑ b ∈ branches, dropMass b e)
      ≤ ((Q * Q * Fintype.card Labels * mult : ℕ) : ℝ) * crossingIndic e :=
  (CrossingMultiplicityData.ofCarryRecord D branches mult dropMass hdrop_nonneg
    crossingIndic hindic_nonneg hlift_le support hsupp hzero hfiber).multiplicity_le e

end AppendixN

end

end Erdos260
