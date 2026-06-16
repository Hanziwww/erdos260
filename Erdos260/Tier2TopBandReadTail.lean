/-
  Erdős #260 — Tier-2 surface cap, **Appendix P**: the FALSIFIABLE counting/routing
  hearts of the top-band localization (R5) and the read-tail push-forward (R6).

  Manuscript reference (`proof_v4_repaired_core_v71_p2_preprint_hygiene.tex`):
  * §O.7 "Localized top-band and read-tail replacements" (lines 8188–8197).
  * Appendix P.1, Definition "Priority-localized top-band routing"
    (`def:p-priority-localized-top-band`, lines 8222–8236) and
    Proposition "Top-band localization is closed"
    (`prop:p-top-band-routing-closed`, lines 8238–8262), eq. (P.1):
    `𝔅_top^{exit,unloc} = ∅`.
  * Appendix P.2, Definition "Event-fibre read-tail output"
    (`def:p-readtail-output`, lines 8270–8292) and Proposition
    "Read-tail event-fibre identity" (`prop:p-readtail-pushforward-closed`,
    lines 8294–8320), eqs. (P.2)/(P.3):
    `Σ_{b:Θ_tail(b)=O} wt(b) ≤ C_Q·wt_tail(O) + o(X|I_j|)`, `C_Q = 1` fully refined.

  What is CERTIFIED here (sorry-free, Mathlib only).  Each theorem isolates the
  checkable combinatorial KERNEL; the genuine dynamical surface SUPPLY is abstracted
  into explicit hypotheses (flagged "FALSIFIABLE POINT"), exactly the
  `P1HotspotAudit` trust-boundary style.

  ## P.1 (R5) — top-band localization is closed (eq. (P.1), `𝔅^{exit,unloc}=∅`)
  The first-obstruction partition of Lemma J.1.1 is a TOTAL classification of every
  top-band event fibre into one of finitely many priority/exit tags.  Given that
  exhaustiveness (the FALSIFIABLE POINT), the "unrouted" / "unlabeled" / "uncovered"
  family is empty — there is no independent "interior is empty" estimate.

  ## P.2 (R6) — read-tail counting is a push-forward identity (eqs. (P.2)/(P.3))
  The output map `Θ_tail` is single-valued: mass is regrouped over its fibres with no
  loss (C_Q = 1, the push-forward identity).  Coarsening (forgetting finitely many
  carry/margin coordinates) merges at most `C_Q = O_Q(1)` refined cells per output, so
  each output fibre's weight is at most `C_Q · cap` — proved as a bounded-fibre-card
  sum bound, with the multiplicity itself supplied by an injection of the fibre into a
  finite forgotten-coordinate set (`Finset.card_le_card_of_injOn`).

  No `sorry`, `axiom`, `admit`, or `native_decide`.
-/
import Mathlib

namespace Erdos260.Tier2TopBandReadTail

open Finset

/-! ## P.1 (R5).  Top-band localization is closed: the unrouted family is empty.

The mathematical content of `prop:p-top-band-routing-closed` (eq. (P.1)) once the
J.1.1 first-obstruction partition is taken as a total routing into a finite covering
tag set: the "unlocalized top-band exit family" is empty.  We give three faithful
spellings (total tag map, partial label map, covering family). -/

/-- **Top-band routing closed — total-tag form (eq. (P.1)).**  If every top-band
event fibre `b ∈ B` is routed by `route` into one of the finitely many covered tags
`routedTags` (priority classes `{CleanCNL, ClassOneCut, DensePack, Return, Run, Tower,
Progress, Endpoint}` together with the routed exit classes `i ∈ {0,3,4,5}`), then the
unlocalized family — branches whose tag is not covered — is empty.

FALSIFIABLE POINT (`hexh`): exhaustiveness of the J.1.1 first-obstruction case split,
i.e. that `route` lands in `routedTags` for *every* event fibre. -/
theorem topband_unrouted_empty
    {Branch Tag : Type*} [DecidableEq Tag]
    (B : Finset Branch) (route : Branch → Tag) (routedTags : Finset Tag)
    (hexh : ∀ b ∈ B, route b ∈ routedTags) :
    B.filter (fun b => route b ∉ routedTags) = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  intro b hb
  exact not_not.mpr (hexh b hb)

/-- **Top-band routing closed — partial-label form (eq. (P.1)).**  Modeling the
localization as a partial labeling `loc : Branch → Option Label` ("assigns no label"
= `none`), exhaustiveness (`hexh`: every fibre receives some label) makes the
unlabeled family `{b : loc b = none}` empty. -/
theorem topband_unlabeled_empty
    {Branch Label : Type*} [DecidableEq Label]
    (B : Finset Branch) (loc : Branch → Option Label)
    (hexh : ∀ b ∈ B, (loc b).isSome) :
    B.filter (fun b => loc b = none) = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  intro b hb
  have h : (loc b).isSome := hexh b hb
  intro hnone
  rw [hnone] at h
  simp at h

/-- **Top-band routing closed — covering-family form (eq. (P.1)).**  If the priority/
exit classes `i ∈ classes` cover every top-band fibre (`hexh`), then the set difference
`B \ ⋃_{i} cover i` (the uncovered family) is empty, i.e. `B ⊆ ⋃ cover`. -/
theorem topband_uncovered_empty
    {Branch ι : Type*} [DecidableEq Branch]
    (B : Finset Branch) (classes : Finset ι) (cover : ι → Finset Branch)
    (hexh : ∀ b ∈ B, ∃ i ∈ classes, b ∈ cover i) :
    B \ classes.biUnion cover = ∅ := by
  rw [Finset.sdiff_eq_empty_iff_subset]
  intro b hb
  obtain ⟨i, hi, hbi⟩ := hexh b hb
  exact Finset.mem_biUnion.mpr ⟨i, hi, hbi⟩

/-- Top-band mass dichotomy (the routing consequence of (P.1)): every top-band fibre's
mass is carried either by an already-estimated priority package or by the
fibre-restricted exit-mass ledger `(R3)`.  With a total routing into the covered tags,
*no* third "unlocalized" alternative remains. -/
theorem topband_mass_dichotomy
    {Branch Tag : Type*} [DecidableEq Tag]
    (route : Branch → Tag) (priorityTags exitTags : Finset Tag)
    (hcover : ∀ x, route x ∈ priorityTags ∪ exitTags) (b : Branch) :
    route b ∈ priorityTags ∨ route b ∈ exitTags := by
  have := hcover b
  rwa [Finset.mem_union] at this

/-! ## P.2 (R6).  Read-tail counting is a push-forward identity with `O_Q(1)` multiplicity.

`prop:p-readtail-pushforward-closed` (eqs. (P.2)/(P.3)).  The output map `Θ_tail` is a
function; counting on its fibres is mass-preserving (C_Q = 1), and forgetting finitely
many carry/margin coordinates multiplies the count by at most `C_Q = O_Q(1)`. -/

/-- **Read-tail push-forward identity (eq. (P.2), `C_Q = 1`).**  Total residual branch
mass equals the sum, over output cells `O`, of the fibre mass `wt_tail(O) =
Σ_{b:Θ(b)=O} wt(b)`.  Single-valuedness of `Θ` makes the push-forward mass-preserving:
no branch mass is lost or double counted. -/
theorem readtail_pushforward_mass_preserving
    {Branch Output : Type*} [DecidableEq Output]
    (B : Finset Branch) (Θ : Branch → Output) (wt : Branch → ℝ) :
    ∑ b ∈ B, wt b
      = ∑ O ∈ B.image Θ, ∑ b ∈ B.filter (fun b => Θ b = O), wt b :=
  (Finset.sum_fiberwise_of_maps_to (fun _ hb => Finset.mem_image_of_mem Θ hb) wt).symm

/-- **Read-tail bounded multiplicity (eq. (P.3)).**  For a fixed output cell `O`, if
every branch mapping to `O` carries weight `≤ cap` (the cell capacity `wt_tail(O)`) and
the fibre over `O` has at most `C_Q` branches, then the fibre weight is at most
`C_Q · cap`.

FALSIFIABLE POINT (`hfib`): the `O_Q(1)` fibre-cardinality bound — at most `C_Q`
refined branches share a coarsened output (the multiplicity from forgetting finite
coordinates).  `hdom` is single-valuedness: each branch's mass is dominated by its
image cell's capacity. -/
theorem readtail_fibre_weight_le
    {Branch Output : Type*} [DecidableEq Output]
    (B : Finset Branch) (Θ : Branch → Output) (wt : Branch → ℝ)
    (O : Output) (CQ : ℕ) (cap : ℝ) (hcap0 : 0 ≤ cap)
    (hdom : ∀ b ∈ B, Θ b = O → wt b ≤ cap)
    (hfib : (B.filter (fun b => Θ b = O)).card ≤ CQ) :
    ∑ b ∈ B.filter (fun b => Θ b = O), wt b ≤ (CQ : ℝ) * cap := by
  have hstep : ∑ b ∈ B.filter (fun b => Θ b = O), wt b
      ≤ ∑ b ∈ B.filter (fun b => Θ b = O), cap := by
    apply Finset.sum_le_sum
    intro b hb
    rw [Finset.mem_filter] at hb
    exact hdom b hb.1 hb.2
  have hconst : ∑ b ∈ B.filter (fun b => Θ b = O), cap
      = ((B.filter (fun b => Θ b = O)).card : ℝ) * cap := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((B.filter (fun b => Θ b = O)).card : ℝ) * cap ≤ (CQ : ℝ) * cap :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hfib) hcap0
  calc ∑ b ∈ B.filter (fun b => Θ b = O), wt b
      ≤ ∑ b ∈ B.filter (fun b => Θ b = O), cap := hstep
    _ = ((B.filter (fun b => Θ b = O)).card : ℝ) * cap := hconst
    _ ≤ (CQ : ℝ) * cap := hcard

/-- **The `O_Q(1)` multiplicity is itself a fibre-cardinality fact.**  The fibre over an
output `O` injects into the finite set `D` of forgotten carry/margin coordinates (a
branch is determined by its output cell together with those coordinates), so its
cardinality is at most `|D|`.  This is the `Finset.card_le_card`-over-preimages supplier
of the multiplicity `C_Q` consumed by `readtail_fibre_weight_le`. -/
theorem readtail_fibre_card_le_of_coords
    {Branch Output Coord : Type*} [DecidableEq Output]
    (B : Finset Branch) (Θ : Branch → Output) (O : Output)
    (coord : Branch → Coord) (D : Finset Coord)
    (hmaps : ∀ b ∈ B.filter (fun b => Θ b = O), coord b ∈ D)
    (hinj : Set.InjOn coord (B.filter (fun b => Θ b = O))) :
    (B.filter (fun b => Θ b = O)).card ≤ D.card :=
  Finset.card_le_card_of_injOn coord hmaps hinj

/-- **Read-tail identity, refined form (eq. (P.3) with `C_Q = 1`).**  With the fully
refined event-fibre quotient, the fibre weight equals the push-forward output weight
exactly (by definition of `wt_tail`); this is the `C_Q = 1` clause of
`prop:p-readtail-pushforward-closed`. -/
theorem readtail_fibre_weight_eq_pushforward
    {Branch Output : Type*} [DecidableEq Output]
    (B : Finset Branch) (Θ : Branch → Output) (wt : Branch → ℝ) (O : Output) :
    ∑ b ∈ B.filter (fun b => Θ b = O), wt b
      = (fun O => ∑ b ∈ B.filter (fun b => Θ b = O), wt b) O := rfl

end Erdos260.Tier2TopBandReadTail
