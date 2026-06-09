import Mathlib
import Erdos260.Constants
import Erdos260.Ledger

/-!
# Appendix N (Phase B): event-fibre transcripts and well-founded live chains

This module formalizes the **combinatorial core of Appendix N.0–N.1** of
`proof_v4.tex`, the part of the C1-VD closure Theorem
`thm:trt-chain-compression` that is finite-set / well-founded combinatorics.

The composed Return–Run–Tower map is not a branch-level function `b ↦ O`, nor a
threshold-level function `(b,T) ↦ O`; it is a map on endpoint/carry **event
fibres** `(b,T,ζ) ↦ Θ_T^0(b,ζ)` with `ζ ∈ Ω_b^{res}(T)`.  Live same-threshold
continuation is defined by *deleting priority atoms* from a fixed starting
residual fibre while routing every deleted atom to an explicit terminal output.

What is proved here, **unconditionally**:

* **N.0c–N.0d** rolled paths `γ(C,O,ζ)` with unit steps and the unique first
  crossing edge `cr_T(C,O,ζ)` (discrete intermediate-value existence);
* **N.0a / N.1** the event-fibre transcript `𝔗_T(b₀)` and **N.3** the scalar
  address `𝔞_T(C) = |𝔗_T(C)|`;
* **N.1.1** the priority-atom partition `Ξ_C = (⊔_ω Π_{C,ω}) ⊔ Ξ_C^{rem}`
  (successive-deletion disjointness + exhaustiveness, N.4/N.6);
* **N.1.2** event-containment **pivot retirement** `𝔞_T(O) < 𝔞_T(C)`
  (eqs N.9/N.10) — the `Finset.card` strict-subset core;
* **N.1.3** **termination** of same-event-fibre live chains in `≤ |𝔗_T(b₀)|`
  steps (well-foundedness of `<` on `ℕ`), and the absence of an infinite chain;
* **N.5e** the terminal routing table, with the "no residual TRT term" claim
  (`route ≠ 𝔒_V`) proved by `decide`.

What is recorded as a **conditional** structure (a hypothesis input that *is*
the manuscript claim, referencing downstream same-threshold containment from
Def. J.1.2 / L.2a):

* **N.1.0 / N.1a / N.5c–N.5d** the per-piece output containment `Π_{C,ω} ⊆
  Ω(O_ω,T)` carried by `TerminalRouting`.

The rolling-window variation (N.2) and terminal compression (N.3) live in the
companion Appendix-N variation module; this module does not depend on them.

The `EventFibre` model uses a finite state type `σ` for endpoint/carry states
`ζ` and a linearly-ordered label type `ι` for the priority atoms `ω`.
-/

namespace Erdos260
namespace AppendixN

open Finset

noncomputable section

/-! ## N.0c–N.0d.  Rolled paths and the first crossing edge

A rolled order-`s` window path `γ(C,O,ζ) = (k₀,…,k_q)` (eq. N.0c) is a vertex
sequence with unit steps `|k_{i+1}-k_i| = 1`.  When the level `T+Y` lies between
the window values at the two ends of the path, the **first crossing edge**
`cr_T(C,O,ζ)` (eq. N.0d) is the first edge along which the "above/below `T+Y`"
side flips; it is unique by the fixed orientation. -/

/-- Unit adjacency of consecutive rolled-path vertices: `b = a ± 1`. -/
def Adjacent (a b : ℤ) : Prop := b = a + 1 ∨ b = a - 1

theorem Adjacent.sub_eq_one_or {a b : ℤ} (h : Adjacent a b) :
    b - a = 1 ∨ b - a = -1 := by
  rcases h with h | h <;> omega

/-- A rolled path (eq. N.0c), as a vertex function with unit steps. -/
def IsRolledStep (k : ℕ → ℤ) : Prop := ∀ i, Adjacent (k i) (k (i + 1))

/--
**Discrete intermediate-value / first-crossing existence (eq. N.0d).**

If the side function `side` (e.g. `side i = decide (T + Y < W (k i))`) differs
at the two ends `0` and `n` of the rolled path, then some edge `(i, i+1)` is a
crossing edge.  This is the combinatorial existence of a first crossing edge.
-/
theorem exists_crossing_of_side_ne (side : ℕ → Bool) :
    ∀ n, side 0 ≠ side n → ∃ i, i < n ∧ side i ≠ side (i + 1) := by
  intro n
  induction n with
  | zero => intro h; exact absurd rfl h
  | succ k ih =>
      intro h
      by_cases hk : side k = side (k + 1)
      · have h0k : side 0 ≠ side k := by rw [hk]; exact h
        obtain ⟨i, hi, hne⟩ := ih h0k
        exact ⟨i, Nat.lt_succ_of_lt hi, hne⟩
      · exact ⟨k, Nat.lt_succ_self k, hk⟩

/-- **First crossing edge (eq. N.0d):** the `≺`-least crossing index, unique by
the fixed path orientation/tie-breaker. -/
def firstCrossing (side : ℕ → Bool) (h : ∃ i, side i ≠ side (i + 1)) : ℕ :=
  Nat.find h

theorem firstCrossing_spec (side : ℕ → Bool) (h : ∃ i, side i ≠ side (i + 1)) :
    side (firstCrossing side h) ≠ side (firstCrossing side h + 1) :=
  Nat.find_spec h

theorem firstCrossing_min (side : ℕ → Bool) (h : ∃ i, side i ≠ side (i + 1))
    {i : ℕ} (hi : side i ≠ side (i + 1)) : firstCrossing side h ≤ i :=
  Nat.find_min' h hi

/-! ## N.5e.  Terminal routing table

The finite routing table (N.5e) sends each terminal Return/Run/Tower pivot
alternative to one of the five **non-drop** output classes
`{𝔒_D, 𝔒_P, 𝔒_E, 𝔒_CNL, 𝔒_bdd}`.  We encode the table as a finite type and
prove **unconditionally** (`decide`) that it never targets the variation-drop
class `𝔒_V`, faithfully witnessing the "no residual TRT term" claim of N.1.0. -/

/-- The rows of the terminal routing table (N.5e): the finite Return/Run/Tower
terminal alternatives. -/
inductive TerminalRow where
  | returnDenseMarker | returnEndpoint | returnProgress | returnBoundedDirty
  | runShortPeriod | runDense | runEndpoint | runProgress | runCleanLow
  | towerFirstExit | towerBoundary | towerDense | towerCleanTerminal | towerBoundedSCC
deriving DecidableEq, Fintype, Repr

/-- The output class assigned to each routing-table row (table N.5e):

```
Return dirty boundary → dense marker            → 𝔒_D
                      → endpoint / progress      → 𝔒_E / 𝔒_P
                      → bounded dirty-return      → 𝔒_bdd
Run pivot  → short period / bounded realignment → 𝔒_bdd
           → dense / endpoint / progress cut     → 𝔒_D / 𝔒_E / 𝔒_P
           → clean terminal-low fibre            → 𝔒_CNL
Tower pivot → first exit / boundary leaving block→ 𝔒_E / 𝔒_P
            → dense / clean terminal fibre        → 𝔒_D / 𝔒_CNL
            → bounded recurrent SCC piece         → 𝔒_bdd
```
-/
def TerminalRow.outputClass : TerminalRow → OutputClassV4
  | .returnDenseMarker => .densePack
  | .returnEndpoint => .endpoint
  | .returnProgress => .progress
  | .returnBoundedDirty => .bdd
  | .runShortPeriod => .bdd
  | .runDense => .densePack
  | .runEndpoint => .endpoint
  | .runProgress => .progress
  | .runCleanLow => .cnl
  | .towerFirstExit => .endpoint
  | .towerBoundary => .progress
  | .towerDense => .densePack
  | .towerCleanTerminal => .cnl
  | .towerBoundedSCC => .bdd

/-- **N.5e / N.5c: every routing-table row targets a non-drop class.**  No
terminal alternative is routed to the variation-drop class `𝔒_V`; this is the
finite "no residual TRT term" witness, proved by decision. -/
theorem TerminalRow.outputClass_ne_varDrop (r : TerminalRow) :
    r.outputClass ≠ OutputClassV4.varDrop := by
  cases r <;> decide

/-- The routing table covers exactly the five non-drop output classes. -/
theorem TerminalRow.exists_outputClass_eq {c : OutputClassV4}
    (hc : c ≠ OutputClassV4.varDrop) : ∃ r : TerminalRow, r.outputClass = c := by
  cases c with
  | densePack => exact ⟨.returnDenseMarker, rfl⟩
  | progress => exact ⟨.returnProgress, rfl⟩
  | endpoint => exact ⟨.returnEndpoint, rfl⟩
  | cnl => exact ⟨.runCleanLow, rfl⟩
  | bdd => exact ⟨.returnBoundedDirty, rfl⟩
  | varDrop => exact absurd rfl hc

/-- The routing table's image is exactly the five non-drop output classes. -/
theorem TerminalRow.outputClass_range_eq_nonDrop :
    ((Finset.univ : Finset TerminalRow).image TerminalRow.outputClass) =
      (Finset.univ : Finset OutputClassV4).erase OutputClassV4.varDrop := by
  ext c
  constructor
  · intro hc
    rcases Finset.mem_image.1 hc with ⟨r, _hr, hrc⟩
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ c⟩
    rw [← hrc]
    exact r.outputClass_ne_varDrop
  · intro hc
    rw [Finset.mem_erase] at hc
    rcases TerminalRow.exists_outputClass_eq hc.1 with ⟨r, hr⟩
    exact Finset.mem_image.2 ⟨r, Finset.mem_univ r, hr⟩

/-- The routing table has exactly five distinct non-drop output classes. -/
theorem TerminalRow.outputClass_range_card :
    ((Finset.univ : Finset TerminalRow).image TerminalRow.outputClass).card = 5 := by
  rw [TerminalRow.outputClass_range_eq_nonDrop]
  decide

/-! ## N.0 / N.1.  Event-fibre transcripts and the scalar address -/

/--
**N.0a / N.1: event-fibre transcript data.**

Attached to a starting branch `b₀` and a fixed threshold `T`:

* `ground` is the residual cylinder `Ω_{b₀}^{res}(T)` (a finite set of
  endpoint/carry states `ζ`);
* `atoms` is the ordered list `𝔗_T(b₀) = {ω₁ ≺ ⋯ ≺ ω_M}` of all elementary
  Return/Run/Tower pivot atoms selectable along descendants of `b₀`;
* `pivotEvent ω` is the measurable pivot event `Ω_ω(T) ⊆ Ω_{b₀}^{res}(T)`.

The order `≺` is the linear order on `ι` (ancestor-first, ties broken by
Return `≺` Run `≺` Tower and then left-to-right gap position).  The list is
finite because the starting cylinder exposes only finitely many windows and
retained coordinates; no `O_Q(1)` bound on `M = |atoms|` is asserted.
-/
structure EventFibre (σ ι : Type*) [DecidableEq σ] [LinearOrder ι] where
  /-- The residual cylinder `Ω_{b₀}^{res}(T)`. -/
  ground : Finset σ
  /-- The full ordered priority-atom transcript `𝔗_T(b₀)`. -/
  atoms : Finset ι
  /-- The pivot event `Ω_ω(T)` of each atom. -/
  pivotEvent : ι → Finset σ
  /-- Each pivot event lies inside the starting cylinder. -/
  pivotEvent_subset_ground : ∀ ω ∈ atoms, pivotEvent ω ⊆ ground

namespace EventFibre

variable {σ ι : Type*} [DecidableEq σ] [LinearOrder ι] (E : EventFibre σ ι)

/--
**N.2: remaining transcript `𝔗_T(C)`.**

The atoms whose pivot event still meets the certificate event `Ξ`:
`𝔗_T(C) = {ω ∈ 𝔗_T(b₀) : Ξ_C(T) ∩ Ω_ω(T) ≠ ∅}`.
-/
def transcript (Ξ : Finset σ) : Finset ι :=
  E.atoms.filter (fun ω => Ξ ∩ E.pivotEvent ω ≠ ∅)

theorem mem_transcript {Ξ : Finset σ} {ω : ι} :
    ω ∈ E.transcript Ξ ↔ ω ∈ E.atoms ∧ (Ξ ∩ E.pivotEvent ω).Nonempty := by
  unfold transcript
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hω, hne⟩
    exact ⟨hω, Finset.nonempty_iff_ne_empty.2 hne⟩
  · rintro ⟨hω, hne⟩
    exact ⟨hω, Finset.nonempty_iff_ne_empty.1 hne⟩

theorem transcript_subset_atoms (Ξ : Finset σ) : E.transcript Ξ ⊆ E.atoms :=
  Finset.filter_subset _ _

/--
**N.3: scalar address `𝔞_T(C) = |𝔗_T(C)|`.**

A natural number; the live-chain order is the well-order of `ℕ` under this
address, not the unstable typed lexicographic order.
-/
def address (Ξ : Finset σ) : Nat := (E.transcript Ξ).card

theorem address_le_atoms_card (Ξ : Finset σ) : E.address Ξ ≤ E.atoms.card :=
  Finset.card_le_card (E.transcript_subset_atoms Ξ)

/-- The transcript is monotone in the event: a smaller event meets fewer pivot
atoms.  (Used for `Ξ_O ⊆ Ξ_C ⇒ 𝔗_T(O) ⊆ 𝔗_T(C)`.) -/
theorem transcript_mono {Ξ Ξ' : Finset σ} (h : Ξ ⊆ Ξ') :
    E.transcript Ξ ⊆ E.transcript Ξ' := by
  intro ω hω
  rw [mem_transcript] at hω ⊢
  refine ⟨hω.1, ?_⟩
  obtain ⟨ζ, hζ⟩ := hω.2
  rw [Finset.mem_inter] at hζ
  exact ⟨ζ, Finset.mem_inter.2 ⟨h hζ.1, hζ.2⟩⟩

/-! ### Lemma N.1.2 — event-containment pivot retirement -/

/--
**N.9 / eq. (2.3r): live same-event-fibre containment.**

A live same-threshold hand-off `C ⤳ O` with first active pivot `π` reinserts
the event subfibre `Ξ_O` satisfying
`Ξ_O ⊆ Ξ_C ∩ ⋂_{ω ≼ π} Ω_ω(T)^c`.

Concretely: `Ξ_O ⊆ Ξ_C`, and `Ξ_O` is disjoint from every pivot event up to
and including `π`.  This is the geometric output of the priority-atom
partition (N.1.1 / N.7).
-/
def LiveContainment (ΞC ΞO : Finset σ) (π : ι) : Prop :=
  ΞO ⊆ ΞC ∧ ∀ ω ∈ E.atoms, ω ≤ π → Disjoint ΞO (E.pivotEvent ω)

/--
**Lemma N.1.2 (event-containment pivot retirement).**

If `π` is an active pivot atom of the certificate `C` (so
`π ∈ 𝔗_T(C)`) and the live successor `O` satisfies the containment (N.9),
then the remaining transcript loses at least the atom `π`:
`𝔗_T(O) ⊆ {ω ∈ 𝔗_T(C) : π ≺ ω}`, hence the scalar address strictly drops
`𝔞_T(O) < 𝔞_T(C)`.

This is the unconditional `Finset.card` strict-subset core of the well-founded
descent.
-/
theorem pivot_retirement_transcript_subset
    {ΞC ΞO : Finset σ} {π : ι}
    (hcont : E.LiveContainment ΞC ΞO π) :
    E.transcript ΞO ⊆ (E.transcript ΞC).filter (fun ω => π < ω) := by
  intro ω hω
  have hωO := (E.mem_transcript).1 hω
  rw [Finset.mem_filter]
  have hωC : ω ∈ E.transcript ΞC := E.transcript_mono hcont.1 hω
  refine ⟨hωC, ?_⟩
  by_contra hle
  rw [not_lt] at hle
  -- `ω ≤ π`, so `Ξ_O` is disjoint from `Ω_ω`, contradicting `ω ∈ 𝔗_T(O)`.
  have hdisj : Disjoint ΞO (E.pivotEvent ω) := hcont.2 ω hωO.1 hle
  obtain ⟨ζ, hζ⟩ := hωO.2
  rw [Finset.mem_inter] at hζ
  exact (Finset.disjoint_left.1 hdisj hζ.1) hζ.2

theorem pivot_retirement
    {ΞC ΞO : Finset σ} {π : ι}
    (hπ : π ∈ E.transcript ΞC)
    (hcont : E.LiveContainment ΞC ΞO π) :
    E.address ΞO < E.address ΞC := by
  have hsub : E.transcript ΞO ⊆ E.transcript ΞC :=
    E.transcript_mono hcont.1
  -- `π ∈ 𝔗_T(C)` but `π ∉ 𝔗_T(O)` (it is disjoint from `Ω_π`).
  have hπO : π ∉ E.transcript ΞO := by
    intro hπO
    have hππ : π ∈ (E.transcript ΞC).filter (fun ω => π < ω) :=
      E.pivot_retirement_transcript_subset hcont hπO
    rw [Finset.mem_filter] at hππ
    exact (lt_irrefl π) hππ.2
  -- strict subset ⇒ strictly smaller cardinality
  have hss : E.transcript ΞO ⊂ E.transcript ΞC :=
    (Finset.ssubset_iff_of_subset hsub).2 ⟨π, hπ, hπO⟩
  exact Finset.card_lt_card hss

/-! ### Lemma N.1.3 — same-event-fibre live chains terminate -/

/-- A single live same-threshold reinsertion step `C ⤳ O`: there is an active
pivot `π ∈ 𝔗_T(C)` satisfying the containment (N.9). -/
def LiveStep (ΞC ΞO : Finset σ) : Prop :=
  ∃ π ∈ E.transcript ΞC, E.LiveContainment ΞC ΞO π

theorem address_lt_of_liveStep {ΞC ΞO : Finset σ} (h : E.LiveStep ΞC ΞO) :
    E.address ΞO < E.address ΞC := by
  obtain ⟨π, hπ, hcont⟩ := h
  exact E.pivot_retirement hπ hcont

/-- Auxiliary: along a live chain the address plus step count never exceeds the
initial address. -/
theorem address_add_index_le
    (Ξ : Nat → Finset σ) (n : Nat)
    (hstep : ∀ i < n, E.LiveStep (Ξ i) (Ξ (i + 1))) :
    ∀ i ≤ n, E.address (Ξ i) + i ≤ E.address (Ξ 0) := by
  intro i hi
  induction i with
  | zero => simp
  | succ k ih =>
      have hk : k ≤ n := Nat.le_of_succ_le hi
      have hklt : k < n := hi
      have hdrop : E.address (Ξ (k + 1)) < E.address (Ξ k) :=
        E.address_lt_of_liveStep (hstep k hklt)
      have hprev : E.address (Ξ k) + k ≤ E.address (Ξ 0) := ih hk
      omega

/--
**Lemma N.1.3 (same-event-fibre live chains terminate).**

Any chain of live same-threshold reinsertions `Ξ 0 ⤳ Ξ 1 ⤳ ⋯ ⤳ Ξ n` has
length `n ≤ |𝔗_T(b₀)|`: it terminates after at most `|𝔗_T(b₀)|` live steps.
The bound is the cardinality of the fixed finite atom set, never summed in the
global recurrence.
-/
theorem liveChainTerminates
    (Ξ : Nat → Finset σ) (n : Nat)
    (hstep : ∀ i < n, E.LiveStep (Ξ i) (Ξ (i + 1))) :
    n ≤ E.atoms.card := by
  have h := E.address_add_index_le Ξ n hstep n (le_refl n)
  have h0 : E.address (Ξ 0) ≤ E.atoms.card := E.address_le_atoms_card (Ξ 0)
  omega

/-- There is no infinite live same-threshold reinsertion chain. -/
theorem no_infinite_liveChain
    (Ξ : Nat → Finset σ)
    (hstep : ∀ i, E.LiveStep (Ξ i) (Ξ (i + 1))) :
    False := by
  have h := E.liveChainTerminates Ξ (E.atoms.card + 1) (fun i _ => hstep i)
  omega

/-! ### Lemma N.1.1 — priority-atom partition with explicit pivot pieces -/

/--
**N.4: pivot piece `Π_{C,ω}(T) = Ξ_C ∩ Ω_ω ∩ ⋂_{ω'≺ω} Ω_{ω'}^c`.**

The part of `Ξ` captured at the atom `ω` after all strictly earlier atoms have
been deleted ("successive deletion").
-/
def pivotPiece (Ξ : Finset σ) (ω : ι) : Finset σ :=
  (Ξ ∩ E.pivotEvent ω).filter
    (fun ζ => ∀ ω' ∈ E.atoms, ω' < ω → ζ ∉ E.pivotEvent ω')

theorem pivotPiece_subset (Ξ : Finset σ) (ω : ι) :
    E.pivotPiece Ξ ω ⊆ Ξ ∩ E.pivotEvent ω :=
  Finset.filter_subset _ _

theorem mem_pivotPiece {Ξ : Finset σ} {ω : ι} {ζ : σ} :
    ζ ∈ E.pivotPiece Ξ ω ↔
      (ζ ∈ Ξ ∧ ζ ∈ E.pivotEvent ω) ∧
        ∀ ω' ∈ E.atoms, ω' < ω → ζ ∉ E.pivotEvent ω' := by
  unfold pivotPiece
  rw [Finset.mem_filter, Finset.mem_inter]

/-- Pivot pieces are pairwise disjoint by successive deletion. -/
theorem pivotPiece_disjoint {Ξ : Finset σ} {ω₁ ω₂ : ι}
    (hω₁ : ω₁ ∈ E.atoms) (hω₂ : ω₂ ∈ E.atoms) (hne : ω₁ ≠ ω₂) :
    Disjoint (E.pivotPiece Ξ ω₁) (E.pivotPiece Ξ ω₂) := by
  rw [Finset.disjoint_left]
  intro ζ h₁ h₂
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- ω₁ < ω₂: piece₂ excludes `Ω_{ω₁}`, but piece₁ ⊆ `Ω_{ω₁}`
    have hmem₂ := (E.mem_pivotPiece).1 h₂
    have hnot := hmem₂.2 ω₁ hω₁ hlt
    have hmem₁ := (E.mem_pivotPiece).1 h₁
    exact hnot hmem₁.1.2
  · have hmem₁ := (E.mem_pivotPiece).1 h₁
    have hnot := hmem₁.2 ω₂ hω₂ hgt
    have hmem₂ := (E.mem_pivotPiece).1 h₂
    exact hnot hmem₂.1.2

theorem pairwiseDisjoint_pivotPiece (Ξ : Finset σ) :
    (E.atoms : Set ι).PairwiseDisjoint (E.pivotPiece Ξ) := by
  intro ω₁ hω₁ ω₂ hω₂ hne
  exact E.pivotPiece_disjoint hω₁ hω₂ hne

/--
**The pivot remainder.**

The states of `Ξ` captured by no pivot atom; this is `Ξ^{>π} ⊔ Ξ^{term} ⊔
Ξ^{drop}` before output routing (the live successor, terminal local
alternatives, and the drop subfibre).
-/
def pivotRemainder (Ξ : Finset σ) : Finset σ :=
  Ξ.filter (fun ζ => ∀ ω ∈ E.atoms, ζ ∉ E.pivotEvent ω)

theorem pivotRemainder_subset (Ξ : Finset σ) : E.pivotRemainder Ξ ⊆ Ξ :=
  Finset.filter_subset _ _

/-- The pivot pieces and the remainder are disjoint from each other (a pivot
piece lies in some `Ω_ω`, the remainder avoids every `Ω_ω`). -/
theorem disjoint_biUnion_pivotPiece_remainder (Ξ : Finset σ) :
    Disjoint (E.atoms.biUnion (E.pivotPiece Ξ)) (E.pivotRemainder Ξ) := by
  rw [Finset.disjoint_left]
  intro ζ hζ hrem
  rw [Finset.mem_biUnion] at hζ
  obtain ⟨ω, hω, hζω⟩ := hζ
  have hmemω := (E.mem_pivotPiece).1 hζω
  have hrem' := (Finset.mem_filter.1 hrem).2
  exact hrem' ω hω hmemω.1.2

/--
**Lemma N.1.1 (priority-atom partition, partition skeleton).**

For a fixed certificate event `Ξ_C ⊆ Ω_{b₀}^{res}(T)`, the event splits as the
disjoint union of the pivot pieces and the remainder:
`Ξ_C = (⊔_{ω ∈ 𝔗_T(b₀)} Π_{C,ω}) ⊔ Ξ_C^{rem}`.

This is the successive-deletion disjointness + exhaustiveness of (N.6); the
routing of each piece to an explicit output class is the conditional input
N.1.0.
-/
theorem pivot_partition (Ξ : Finset σ) :
    Ξ = E.atoms.biUnion (E.pivotPiece Ξ) ∪ E.pivotRemainder Ξ := by
  apply Finset.Subset.antisymm
  · intro ζ hζ
    by_cases hcap : ∃ ω ∈ E.atoms, ζ ∈ E.pivotEvent ω
    · -- first atom (least in `≺`) whose event contains `ζ`
      rw [Finset.mem_union]
      left
      rw [Finset.mem_biUnion]
      set S := E.atoms.filter (fun ω => ζ ∈ E.pivotEvent ω) with hS
      have hSne : S.Nonempty := by
        obtain ⟨ω, hω, hζω⟩ := hcap
        exact ⟨ω, Finset.mem_filter.2 ⟨hω, hζω⟩⟩
      refine ⟨S.min' hSne, ?_, ?_⟩
      · exact (Finset.mem_filter.1 (S.min'_mem hSne)).1
      · rw [mem_pivotPiece]
        have hmin := S.min'_mem hSne
        rw [Finset.mem_filter] at hmin
        refine ⟨⟨hζ, hmin.2⟩, ?_⟩
        intro ω' hω' hω'lt hζω'
        have : ω' ∈ S := Finset.mem_filter.2 ⟨hω', hζω'⟩
        have := S.min'_le ω' this
        exact absurd hω'lt (not_lt.2 this)
    · simp only [not_exists, not_and] at hcap
      rw [Finset.mem_union]
      right
      exact Finset.mem_filter.2 ⟨hζ, hcap⟩
  · intro ζ hζ
    rw [Finset.mem_union] at hζ
    rcases hζ with h | h
    · rw [Finset.mem_biUnion] at h
      obtain ⟨ω, _, hζω⟩ := h
      exact ((E.mem_pivotPiece).1 hζω).1.1
    · exact E.pivotRemainder_subset Ξ h

/-- **Cardinality form of the partition (N.6).**  The starting cylinder mass
splits exactly into the pivot-piece masses plus the remainder mass. -/
theorem card_eq_sum_pivotPiece_add_remainder (Ξ : Finset σ) :
    Ξ.card =
      (∑ ω ∈ E.atoms, (E.pivotPiece Ξ ω).card) + (E.pivotRemainder Ξ).card := by
  conv_lhs => rw [E.pivot_partition Ξ]
  rw [Finset.card_union_of_disjoint (E.disjoint_biUnion_pivotPiece_remainder Ξ)]
  congr 1
  exact Finset.card_biUnion (fun ω₁ hω₁ ω₂ hω₂ hne =>
    E.pivotPiece_disjoint hω₁ hω₂ hne)

/-! ### Lemma N.1.0 — terminal TRT routing (conditional) -/

/--
**Lemma N.1.0 (terminal TRT routing, conditional input).**

Routing data assigning every pivot atom `ω`, *before any global summation*, to
a terminal **non-drop** output class in `{𝔒_D, 𝔒_P, 𝔒_E, 𝔒_CNL, 𝔒_bdd}`
(never `𝔒_V`), together with the same-threshold containment `Π_{C,ω} ⊆
Ω(O_ω, T)` and the residual-multiplier comparison `Y_ω ≤ C_Q·Y(O_ω)`
(eqs N.5d / N.1a).

Every row of the routing table (N.5e) is a same-threshold containment of the
form (J.1b)/(L.2a); the multiplier comparison is the residual-bin comparison of
Definition J.1.2.  Both reference downstream local closure, so this is a
**conditional** structure (a hypothesis input that *is* the manuscript claim).
-/
structure TerminalRouting (E : EventFibre σ ι) where
  /-- The terminal output class `O_ω` of each pivot atom. -/
  routeClass : ι → OutputClassV4
  /-- N.5c: no pivot atom is routed to the variation-drop class. -/
  route_not_varDrop : ∀ ω ∈ E.atoms, routeClass ω ≠ OutputClassV4.varDrop
  /-- The output event `Ω(O_ω, T)` of the routed output. -/
  outputEvent : ι → Finset σ
  /-- N.5d / N.1a: same-threshold containment of each pivot event. -/
  pivot_contained : ∀ ω ∈ E.atoms, E.pivotEvent ω ⊆ outputEvent ω

/--
**N.1.0 consequence: no residual TRT term.**

Under the routing data, every pivot piece is contained in its routed
**non-drop** output event.  Thus the sum of all terminal one-step TRT / pivot
charges is already included in the DensePack / Progress / Endpoint / clean-CNL /
bounded-scale output sums; no separate terminal-TRT summand survives into the
global recurrence (I.9).
-/
theorem terminalRouting (R : TerminalRouting E) {Ξ : Finset σ} {ω : ι}
    (hω : ω ∈ E.atoms) :
    E.pivotPiece Ξ ω ⊆ R.outputEvent ω ∧ R.routeClass ω ≠ OutputClassV4.varDrop := by
  refine ⟨?_, R.route_not_varDrop ω hω⟩
  intro ζ hζ
  have hmem := (E.mem_pivotPiece).1 hζ
  exact R.pivot_contained ω hω hmem.1.2

/--
**Routing via the table (N.5e).**

A `TerminalRouting` whose class assignment factors through the routing table
`TerminalRow.outputClass`.  The non-drop property `route_not_varDrop` is then a
*theorem* (proved by decision via `TerminalRow.outputClass_ne_varDrop`), not a
hypothesis; only the same-threshold containment `pivot_contained` remains a
conditional input.
-/
def TerminalRouting.ofTable (row : ι → TerminalRow) (outputEvent : ι → Finset σ)
    (pivot_contained : ∀ ω ∈ E.atoms, E.pivotEvent ω ⊆ outputEvent ω) :
    TerminalRouting E where
  routeClass ω := (row ω).outputClass
  route_not_varDrop ω _ := (row ω).outputClass_ne_varDrop
  outputEvent := outputEvent
  pivot_contained := pivot_contained

/-- **N.1.0, table-routed form.**  Once the same-threshold containment
`pivot_contained` is supplied, the routing-table part of N.1.0 is automatic:
every pivot piece is contained in its routed terminal event and its routed class
is one of the five non-drop classes. -/
theorem TerminalRouting.ofTable_terminalRouting
    (row : ι → TerminalRow) (outputEvent : ι → Finset σ)
    (pivot_contained : ∀ ω ∈ E.atoms, E.pivotEvent ω ⊆ outputEvent ω)
    {Ξ : Finset σ} {ω : ι} (hω : ω ∈ E.atoms) :
    E.pivotPiece Ξ ω ⊆ outputEvent ω ∧
      (row ω).outputClass ≠ OutputClassV4.varDrop := by
  simpa [TerminalRouting.ofTable] using
    E.terminalRouting (TerminalRouting.ofTable (E := E) row outputEvent pivot_contained)
      (Ξ := Ξ) hω

/-- N.1.0/N.5d routing data retaining the residual-multiplier comparison.

The older `TerminalRouting` interface records the same-threshold containment
and the no-variation-drop output class.  Proof-v4's N.5d also records the
comparison `Y_omega <= C_Q * Y(O_omega)`, which is the multiplier input later
used by terminal compression.  This structure keeps that comparison attached to
the same table-routed pivot atom without changing the older API. -/
structure TerminalRoutingWithMultiplier (E : EventFibre σ ι) where
  /-- The terminal output class assigned to each pivot atom. -/
  routeClass : ι → OutputClassV4
  /-- N.5c: no pivot atom is routed to the variation-drop class. -/
  route_not_varDrop : ∀ ω ∈ E.atoms, routeClass ω ≠ OutputClassV4.varDrop
  /-- The output event `Omega(O_omega, T)` of the routed output. -/
  outputEvent : ι → Finset σ
  /-- N.5d/N.1a: same-threshold containment of each pivot event. -/
  pivot_contained : ∀ ω ∈ E.atoms, E.pivotEvent ω ⊆ outputEvent ω
  /-- The residual multiplier `Y_omega` carried by the pivot atom. -/
  pivotMultiplier : ι → Real
  /-- The routed output multiplier scale `Y(O_omega)`. -/
  outputMultiplier : ι → Real
  /-- The fixed same-threshold fibre constant `C_Q`. -/
  CQ : Real
  /-- N.5d: residual-bin comparison `Y_omega <= C_Q * Y(O_omega)`. -/
  multiplier_le : ∀ ω ∈ E.atoms, pivotMultiplier ω ≤ CQ * outputMultiplier ω

/-- Forget the multiplier bookkeeping to the older N.1.0 routing interface. -/
def TerminalRoutingWithMultiplier.toTerminalRouting
    {E : EventFibre σ ι} (R : TerminalRoutingWithMultiplier E) :
    TerminalRouting E where
  routeClass := R.routeClass
  route_not_varDrop := R.route_not_varDrop
  outputEvent := R.outputEvent
  pivot_contained := R.pivot_contained

/-- N.1.0 consequence with the residual multiplier comparison kept available. -/
theorem terminalRoutingWithMultiplier
    (R : TerminalRoutingWithMultiplier E) {Ξ : Finset σ} {ω : ι}
    (hω : ω ∈ E.atoms) :
    E.pivotPiece Ξ ω ⊆ R.outputEvent ω ∧
      R.routeClass ω ≠ OutputClassV4.varDrop ∧
      R.pivotMultiplier ω ≤ R.CQ * R.outputMultiplier ω := by
  have hroute :=
    E.terminalRouting R.toTerminalRouting (Ξ := Ξ) hω
  exact ⟨hroute.1, hroute.2, R.multiplier_le ω hω⟩

/-- Table-routed N.1.0 data with the N.5d multiplier comparison attached.

The no-drop part is still proved from the finite routing table by cases; the
remaining provider inputs are exactly the concrete same-threshold containment
and residual-bin comparison from proof-v4. -/
def TerminalRoutingWithMultiplier.ofTable
    (row : ι → TerminalRow) (outputEvent : ι → Finset σ)
    (pivotMultiplier outputMultiplier : ι → Real) (CQ : Real)
    (pivot_contained : ∀ ω ∈ E.atoms, E.pivotEvent ω ⊆ outputEvent ω)
    (multiplier_le :
      ∀ ω ∈ E.atoms, pivotMultiplier ω ≤ CQ * outputMultiplier ω) :
    TerminalRoutingWithMultiplier E where
  routeClass ω := (row ω).outputClass
  route_not_varDrop ω _ := (row ω).outputClass_ne_varDrop
  outputEvent := outputEvent
  pivot_contained := pivot_contained
  pivotMultiplier := pivotMultiplier
  outputMultiplier := outputMultiplier
  CQ := CQ
  multiplier_le := multiplier_le

/-- Table-routed N.1.0 consequence with both containment and multiplier data. -/
theorem TerminalRoutingWithMultiplier.ofTable_terminalRouting
    (row : ι → TerminalRow) (outputEvent : ι → Finset σ)
    (pivotMultiplier outputMultiplier : ι → Real) (CQ : Real)
    (pivot_contained : ∀ ω ∈ E.atoms, E.pivotEvent ω ⊆ outputEvent ω)
    (multiplier_le :
      ∀ ω ∈ E.atoms, pivotMultiplier ω ≤ CQ * outputMultiplier ω)
    {Ξ : Finset σ} {ω : ι} (hω : ω ∈ E.atoms) :
    E.pivotPiece Ξ ω ⊆ outputEvent ω ∧
      (row ω).outputClass ≠ OutputClassV4.varDrop ∧
      pivotMultiplier ω ≤ CQ * outputMultiplier ω := by
  simpa [TerminalRoutingWithMultiplier.ofTable] using
    E.terminalRoutingWithMultiplier
      (TerminalRoutingWithMultiplier.ofTable (E := E) row outputEvent
        pivotMultiplier outputMultiplier CQ pivot_contained multiplier_le)
      (Ξ := Ξ) hω

/-- The variation-drop residual mass of a table-routed output collection is
`0`: the routing table never emits a variation-drop output, so the
`Ledger.variationDropMass` of any collection drawn from it vanishes (the
finite-set "no residual TRT term" statement, connected to the Phase A ledger
interface). -/
theorem variationDropMass_routedOutputs_eq_zero
    (row : ι → TerminalRow) (supp thr : ι → Nat)
    (weight : OutputObjectV4 → ℝ) :
    variationDropMass
        (E.atoms.image
          (fun ω => (⟨(row ω).outputClass, supp ω, thr ω⟩ : OutputObjectV4))) weight
      = 0 := by
  apply variationDropMass_eq_zero_of_no_varDrop
  intro o ho
  rw [Finset.mem_image] at ho
  obtain ⟨ω, _, rfl⟩ := ho
  exact (row ω).outputClass_ne_varDrop

end EventFibre

/-! ## N.3.  Terminal event-fibre compression (eqs N.19–N.24)

The composed same-threshold Return–Run–Tower map sends event fibres to terminal
**non-drop** outputs.  Section N.3 of `proof_v4.tex` shows that the aggregate
mass of these terminal outputs is absorbed into the already-estimated output
classes, with no separate terminal-TRT summand surviving into the global
recurrence (I.9).

The combinatorial / real-analytic content is proved here **unconditionally**:

* **N.3.1** the **disjoint-union mass domination** `∑_b μ(𝒟_b) ≤ μ(Ω)` (the
  Fubini / finite-additivity step of eq. N.21) together with the `C_Q Y(O)`
  multiplier arithmetic giving `∑_b wt_O(b) ≤ C_Q wt(O)`;
* **N.3.2** the Lemma L.6.1–L.6.3 low/paid combination
  `BddTerm ≤ C_Q X|I_j|2^{-cY} + o(sX|I_j|)` (eqs N.23d–N.23f / N.23b);
* **N.3.3** the real fiberwise five-class decomposition of a terminal non-drop
  family and the linear combination of the per-class bounds (I.4.1, I.4.2,
  the clean-CNL Kraft tail + Lemma 22.1A, N.3.2) giving the aggregate
  absorption (eq. N.24).

The genuinely-deep geometric inputs — the per-piece containment
`𝒟_b(O,T) ⊆ Ω(O,T)` (eq. N.23, from Def. J.1.2 / L.2a) and the residual
multiplier bound `Y_res(b,ζ) ≤ C_Q Y(O)` (Def. J.1.2) — are taken as
hypotheses / structure fields.  The `∫_{I_j} μ_T(·)\,dT` bin charge is modelled
as a finite fibre measure `∑_{ζ} μ ζ`, faithful to the manuscript's
"constant on the bin" reduction `wt_O(b) = Y_res(b)|𝒟_b(O,·)|` (eq. N.20). -/

/--
**Disjoint-union mass domination (Fubini core of N.3.1).**

If finitely many terminal subfibres `D b ⊆ Ω` are pairwise disjoint, the total
fibre mass they carry is at most the mass of `Ω`:
`∑_b (∑_{ζ∈D b} μ ζ) ≤ ∑_{ζ∈Ω} μ ζ`.  This is the finite-additivity /
disjoint-union step `∑_b μ_T(𝒟_b(O,T)) ≤ μ_T(Ω(O,T))` of the Fubini estimate in
eq. N.21, proved as a real, unconditional `Finset` theorem.
-/
theorem terminalMass_sum_le {β σ : Type*} [DecidableEq σ]
    (branches : Finset β) (Ω : Finset σ) (D : β → Finset σ) (μ : σ → ℝ)
    (hμ : ∀ ζ ∈ Ω, 0 ≤ μ ζ)
    (hsub : ∀ b ∈ branches, D b ⊆ Ω)
    (hdisj : (↑branches : Set β).PairwiseDisjoint D) :
    (∑ b ∈ branches, ∑ ζ ∈ D b, μ ζ) ≤ ∑ ζ ∈ Ω, μ ζ := by
  rw [← Finset.sum_biUnion hdisj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro ζ hζ
    rw [Finset.mem_biUnion] at hζ
    obtain ⟨b, hb, hζb⟩ := hζ
    exact hsub b hb hζb
  · intro ζ hζ _
    exact hμ ζ hζ

/--
**Lemma N.3.1 (fixed terminal output estimate, eq. N.21).**

`∑_b wt_O(b) ≤ C_Q · wt(O)`, where `wt(O) = Y(O) · μ(Ω(O,T))` is the output
weight (eq. N.20).

The inputs are the geometric containment `𝒟_b(O,T) ⊆ Ω(O,T)` (`hsub`, eq. N.23)
with the pairwise disjointness of the subfibres (`hdisj`) — the conditional
Def. J.1.2 / L.2a / N.1.1 inputs — and the per-branch multiplier bound
`wt_O(b) ≤ C_Q Y(O) · μ(𝒟_b)` (`hmult`, the `Y_res ≤ C_Q Y(O)` input combined
with the definition N.20 of `wt_O`).  The summation inequality is then a **real
theorem**, assembled from the disjoint-union mass domination
`terminalMass_sum_le` and the `C_Q Y(O)` arithmetic.
-/
theorem terminalCompression {β σ : Type*} [DecidableEq σ]
    (branches : Finset β) (Ω : Finset σ) (D : β → Finset σ) (μ : σ → ℝ)
    (CQ YO : ℝ) (wtO : β → ℝ)
    (hμ : ∀ ζ ∈ Ω, 0 ≤ μ ζ)
    (hCQYO : 0 ≤ CQ * YO)
    (hsub : ∀ b ∈ branches, D b ⊆ Ω)
    (hdisj : (↑branches : Set β).PairwiseDisjoint D)
    (hmult : ∀ b ∈ branches, wtO b ≤ CQ * YO * (∑ ζ ∈ D b, μ ζ)) :
    (∑ b ∈ branches, wtO b) ≤ CQ * (YO * ∑ ζ ∈ Ω, μ ζ) := by
  calc (∑ b ∈ branches, wtO b)
      ≤ ∑ b ∈ branches, CQ * YO * (∑ ζ ∈ D b, μ ζ) := Finset.sum_le_sum hmult
    _ = CQ * YO * (∑ b ∈ branches, ∑ ζ ∈ D b, μ ζ) := by rw [← Finset.mul_sum]
    _ ≤ CQ * YO * (∑ ζ ∈ Ω, μ ζ) :=
        mul_le_mul_of_nonneg_left (terminalMass_sum_le branches Ω D μ hμ hsub hdisj) hCQYO
    _ = CQ * (YO * ∑ ζ ∈ Ω, μ ζ) := by ring

/--
**Lemma N.3.1 input bundle (eqs N.19–N.23) — CONDITIONAL.**

Bundles the data of a terminal non-drop output `O`: the residual cylinder
`Ω(O,T)` (`ground`), the per-branch terminal subfibres `𝒟_b(O,T)` (eq. N.19,
`subfibre`), the bin fibre measure `μ_T` (`fibreMass`, with the `∫_{I_j}\,dT`
integration folded in), the residual-multiplier scale `Y(O)` (`YO`), the
per-branch charges `wt_O(b)` (`wtO`), and the two conditional geometric inputs:
the same-threshold containment (eq. N.23) and the residual-multiplier bound
(`Y_res ≤ C_Q Y(O)`, Def. J.1.2).
-/
structure TerminalOutputData (β σ : Type*) [DecidableEq σ] where
  /-- The (finite) starting branch family. -/
  branches : Finset β
  /-- The output event `Ω(O,T)`. -/
  ground : Finset σ
  /-- The terminal event subfibre `𝒟_b(O,T)` (eq. N.19). -/
  subfibre : β → Finset σ
  /-- The bin fibre measure `μ_T` (with `∫_{I_j}\,dT` folded in). -/
  fibreMass : σ → ℝ
  /-- The multiplicity constant `C_Q`. -/
  CQ : ℝ
  /-- The residual-multiplier scale `Y(O)`. -/
  YO : ℝ
  /-- The per-branch terminal charge `wt_O(b)` (eq. N.20). -/
  wtO : β → ℝ
  fibreMass_nonneg : ∀ ζ ∈ ground, 0 ≤ fibreMass ζ
  CQYO_nonneg : 0 ≤ CQ * YO
  /-- eq. N.23: same-threshold containment `𝒟_b(O,T) ⊆ Ω(O,T)`. -/
  subfibre_subset : ∀ b ∈ branches, subfibre b ⊆ ground
  /-- The subfibres are pairwise disjoint across branches. -/
  subfibre_disjoint : (↑branches : Set β).PairwiseDisjoint subfibre
  /-- `Y_res ≤ C_Q Y(O)` (Def. J.1.2) combined with eq. N.20. -/
  wtO_le : ∀ b ∈ branches, wtO b ≤ CQ * YO * (∑ ζ ∈ subfibre b, fibreMass ζ)

/-- **Lemma N.3.1 (eq. N.21), bundled form.**  `∑_b wt_O(b) ≤ C_Q wt(O)`. -/
theorem TerminalOutputData.compression {β σ : Type*} [DecidableEq σ]
    (D : TerminalOutputData β σ) :
    (∑ b ∈ D.branches, D.wtO b) ≤ D.CQ * (D.YO * ∑ ζ ∈ D.ground, D.fibreMass ζ) :=
  terminalCompression D.branches D.ground D.subfibre D.fibreMass D.CQ D.YO D.wtO
    D.fibreMass_nonneg D.CQYO_nonneg D.subfibre_subset D.subfibre_disjoint D.wtO_le

/--
**Lemma N.3.2 (bounded-scale terminal output estimate, eq. N.23b).**

`BddTerm_{s,j}(Y) = ∑_{O∈𝔒_bdd} wt(O) ≤ C_Q X|I_j|2^{-cY} + o(sX|I_j|)`.

The bounded-scale fibre is split by Lemma L.6.1 into low-residual and paid parts
(eq. N.23d, taken here as the **pointwise** split `wt(O) = wt^low(O)+wt^paid(O)`,
`hsplit`); Lemma L.6.3 bounds the low part by `o(sX|I_j|)` (`remLow`, eq. N.23e,
`hlow`) and Lemma L.6.2 bounds the paid part by `C_Q X|I_j|2^{-cY} + o(sX|I_j|)`
(`mainPaid + remPaid`, eq. N.23f, `hpaid`).  The sum-split identity is real
(`Finset.sum_add_distrib`) and the combination is real arithmetic; the two
analytic bounds are the conditional Lemma L.6 inputs.
-/
theorem bddTerm {O : Type*} (bddOutputs : Finset O) (wt wtLow wtPaid : O → ℝ)
    (mainPaid remLow remPaid : ℝ)
    (hsplit : ∀ o ∈ bddOutputs, wt o = wtLow o + wtPaid o)
    (hlow : (∑ o ∈ bddOutputs, wtLow o) ≤ remLow)
    (hpaid : (∑ o ∈ bddOutputs, wtPaid o) ≤ mainPaid + remPaid) :
    (∑ o ∈ bddOutputs, wt o) ≤ mainPaid + (remLow + remPaid) := by
  have hsum : (∑ o ∈ bddOutputs, wt o)
      = (∑ o ∈ bddOutputs, wtLow o) + (∑ o ∈ bddOutputs, wtPaid o) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hsplit
  rw [hsum]; linarith

/-- Class-restricted v4 charged mass: the total weight of the outputs of class
`c` in a finite v4 output family.  The five non-drop slices
(`densePack/progress/endpoint/cnl/bdd`) are the destinations of the N.1.0
terminal routing; `varDrop` is the variation-drop class `𝔒_V`. -/
def classMassV4 (objects : Finset OutputObjectV4) (weight : OutputObjectV4 → ℝ)
    (c : OutputClassV4) : ℝ :=
  ∑ o ∈ objects.filter (fun o => o.cls = c), weight o

/-- **Fiberwise class decomposition (real).**  A finite v4 output family's total
weight is the sum of its six output-class masses (eq. N.24 setup). -/
theorem terminalMassV4_eq_sum_classes (objects : Finset OutputObjectV4)
    (weight : OutputObjectV4 → ℝ) :
    (∑ o ∈ objects, weight o) = ∑ c : OutputClassV4, classMassV4 objects weight c := by
  unfold classMassV4
  exact (Finset.sum_fiberwise objects (fun o => o.cls) weight).symm

/-- Expansion of a real sum over the six v4 output classes. -/
theorem outputClassV4_sum_univ (F : OutputClassV4 → ℝ) :
    (∑ c : OutputClassV4, F c)
      = F OutputClassV4.densePack + F OutputClassV4.progress + F OutputClassV4.endpoint
        + F OutputClassV4.cnl + F OutputClassV4.bdd + F OutputClassV4.varDrop := by
  have huniv : (Finset.univ : Finset OutputClassV4)
      = {OutputClassV4.densePack, OutputClassV4.progress, OutputClassV4.endpoint,
         OutputClassV4.cnl, OutputClassV4.bdd, OutputClassV4.varDrop} := by decide
  rw [show (∑ c : OutputClassV4, F c)
        = ∑ c ∈ (Finset.univ : Finset OutputClassV4), F c from rfl, huniv]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

/-- **Five-class decomposition of a terminal non-drop family (real).**  If every
output in the family is non-drop (the N.1.0 routing target, never `𝔒_V`), its
total weight is the sum of the five non-drop class masses — the variation-drop
slice `classMassV4 _ _ 𝔒_V` is empty. -/
theorem terminalMassV4_nonDrop_eq (objects : Finset OutputObjectV4)
    (weight : OutputObjectV4 → ℝ)
    (hnd : ∀ o ∈ objects, o.cls ≠ OutputClassV4.varDrop) :
    (∑ o ∈ objects, weight o)
      = classMassV4 objects weight OutputClassV4.densePack
        + classMassV4 objects weight OutputClassV4.progress
        + classMassV4 objects weight OutputClassV4.endpoint
        + classMassV4 objects weight OutputClassV4.cnl
        + classMassV4 objects weight OutputClassV4.bdd := by
  rw [terminalMassV4_eq_sum_classes, outputClassV4_sum_univ]
  have hvd : classMassV4 objects weight OutputClassV4.varDrop = 0 := by
    unfold classMassV4
    rw [Finset.filter_false_of_mem (fun o ho => hnd o ho), Finset.sum_empty]
  rw [hvd, add_zero]

/--
**Lemma N.3.3 (aggregate absorption of terminal non-drop outputs, eq. N.24).**

`∑_{O∈𝔒_term^0} ∑_b wt_O(b) ≤ C_Q·DensePack_{s,j}(Y) + C_Q X|I_j|2^{-cY}
  + o(sX|I_j|)`.

By Lemma N.1.0 every terminal non-drop subfibre lies in one of the five disjoint
classes `𝔒_D, 𝔒_P, 𝔒_E, 𝔒_CNL, 𝔒_bdd`; applying Lemma N.3.1 within each class
gives the five per-class masses `massD,…,massBdd` (whose sum is the family total,
by the real `terminalMassV4_nonDrop_eq` decomposition).  Summing the per-class
bounds — `𝔒_D` by Lemma I.4.1 (the `C_Q·DensePack` term `densePackTerm`),
`𝔒_P/𝔒_E` by Lemma I.4.2 (the `o(·)` terms `remP/remE`), `𝔒_CNL` by the clean
Kraft-weighted CNL tail with shell-paid pieces covered by Lemma 22.1A
(`shellCNL + remCNL`), and `𝔒_bdd` by Lemma N.3.2 (`shellBdd + remBdd`) — is a
**real linear combination**.  The two shell terms `shellCNL + shellBdd` combine
into the single `C_Q X|I_j|2^{-cY}` term `shellTerm` (`hshell`, constant
absorption) and the four `o(·)` remainders into `remTerm` (`hrem`).  The
per-class bounds are the conditional package inputs.
-/
theorem aggregateAbsorption
    (massD massP massE massCNL massBdd : ℝ)
    (densePackTerm shellTerm remTerm
      shellCNL shellBdd remP remE remCNL remBdd : ℝ)
    (hD : massD ≤ densePackTerm)
    (hP : massP ≤ remP)
    (hE : massE ≤ remE)
    (hCNL : massCNL ≤ shellCNL + remCNL)
    (hBdd : massBdd ≤ shellBdd + remBdd)
    (hshell : shellCNL + shellBdd ≤ shellTerm)
    (hrem : remP + remE + remCNL + remBdd ≤ remTerm) :
    massD + massP + massE + massCNL + massBdd
      ≤ densePackTerm + shellTerm + remTerm := by
  linarith

end

end AppendixN
end Erdos260
