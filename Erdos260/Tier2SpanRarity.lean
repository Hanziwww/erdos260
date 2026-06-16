/-
  Erdős #260 — Tier-2 surface cap, **Appendix Q**: the FALSIFIABLE counting heart of
  DensePack span-rarity — per-span uniqueness of genuine starts forces the count bound
  `#starts ≤ X / W`.

  Manuscript reference (`proof_v4_repaired_core_v71_p2_preprint_hygiene.tex`):
  * Appendix Q.1, Proposition "DensePack SDR is not load-bearing"
    (`prop:q-densepack-r4-removed`, lines 8512–8538): the DensePack lane is supplied by
    the support-count estimate of Lemma K.1.4 / Corollary K.1.5, not by a global Hall/SDR
    landing hypothesis.
  * Corollary K.1.5 (`corollary-k.1.5...`, lines 5267–5296): a *maximal pairwise-disjoint*
    dense-marker family `𝒟₀`, each selected marker containing `≥ ρ_D L` actual hits, with
    `[X, 2X]` of size `≤ X`, gives the marker count bound `|𝒟₀|·ρ_D L ≤ C c_* X + o(X)`.
  * Remark "Owner-fibre interpretation of the endpoint floor" (`rem:k-owner-fibre`,
    lines 5197–5208): distinct genuine starts own disjoint hit blocks (multiplicity one).

  CERTIFIED here (sorry-free): the falsifiable counting heart — *one genuine start per
  width-`W` span* (per-span uniqueness ⇒ pairwise-disjoint owned spans of width `≥ W`
  inside an ambient window of size `X`) forces `#starts ≤ X / W`, by the disjoint-packing
  count bound.  This is the marker/start rarity used in Q.1 / K.1.5 with `W = ρ_D L` and
  `X` the active-shell size.

  Genuine geometric SUPPLY (disjointness of owned spans, the width floor `W ≤ |span k|`,
  and span-containment in the window) is abstracted into explicit hypotheses — exactly
  the supply discharged geometrically by the first-stop owner retraction of Lemma K.1.3.

  REUSE: `Erdos260.HighSupportPhaseCount.card_le_div_of_pairwiseDisjoint_range` (and
  `card_mul_le_…`), the disjoint-packing core.

  No `sorry`, `axiom`, `admit`, or `native_decide`.
-/
import Mathlib
import Erdos260.HighSupportPhaseCount

namespace Erdos260.Tier2SpanRarity

open Finset
open Erdos260.HighSupportPhaseCount

/-! ## Q.  Span-rarity: per-span uniqueness ⇒ `#starts ≤ X / W`.

Each genuine DensePack start `k ∈ K` owns a width-`W` span `span k ⊆ range X`
(`hwidth : W ≤ |span k|`); per-span uniqueness is encoded as pairwise disjointness of
the owned spans (`hdisj`).  Then the genuine starts number at most `X / W`. -/

/-- **Span-rarity count bound (Q.1 / K.1.5 marker count).**  Genuine starts owning
pairwise-disjoint width-`≥ W` spans inside `range X` number at most `X / W`.

FALSIFIABLE POINT (`hdisj` + `hwidth`): per-span uniqueness — distinct genuine starts
own *disjoint* spans, each of width at least `W`.  This is the rarity (`one genuine start
per width-W span`) that the first-stop owner map of Lemma K.1.3 supplies. -/
theorem span_rarity_count_le_div
    {ι : Type*} (K : Finset ι) (span : ι → Finset ℕ) (X W : ℕ) (hW : 0 < W)
    (hsub : ∀ k ∈ K, span k ⊆ Finset.range X)
    (hdisj : ∀ i ∈ K, ∀ j ∈ K, i ≠ j → Disjoint (span i) (span j))
    (hwidth : ∀ k ∈ K, W ≤ (span k).card) :
    K.card ≤ X / W :=
  card_le_div_of_pairwiseDisjoint_range K span X W hW hsub hdisj hwidth

/-- **Span-rarity, multiplicative form (`|𝒟₀|·W ≤ X`, the K.1.5 marker inequality).**
The same hypotheses give `#starts · W ≤ X` — the form `|𝒟₀|·ρ_D L ≤ X` used directly in
Corollary K.1.5 (with `W = ρ_D L`). -/
theorem span_rarity_card_mul_le
    {ι : Type*} (K : Finset ι) (span : ι → Finset ℕ) (X W : ℕ)
    (hsub : ∀ k ∈ K, span k ⊆ Finset.range X)
    (hdisj : ∀ i ∈ K, ∀ j ∈ K, i ≠ j → Disjoint (span i) (span j))
    (hwidth : ∀ k ∈ K, W ≤ (span k).card) :
    K.card * W ≤ X :=
  card_mul_le_of_pairwiseDisjoint_range K span X W hsub hdisj hwidth

/-- **Span-rarity via the span-index injection ("genuine starts inject into distinct
spans").**  The most direct spelling of per-span uniqueness: if each genuine start maps
to a *distinct* span index in `[0, X/W)` (`hinj` injective on `K`, `hrange` the index
range), then `#starts ≤ X / W`.  Uses `Finset.card_le_card_of_injOn` into
`Finset.range (X / W)`. -/
theorem span_rarity_count_le_div_of_inj
    {ι : Type*} (K : Finset ι) (spanIdx : ι → ℕ) (X W : ℕ)
    (hinj : Set.InjOn spanIdx K)
    (hrange : ∀ k ∈ K, spanIdx k < X / W) :
    K.card ≤ X / W := by
  have h : K.card ≤ (Finset.range (X / W)).card :=
    Finset.card_le_card_of_injOn spanIdx
      (fun k hk => Finset.mem_range.mpr (hrange k hk)) hinj
  simpa using h

/-- **Span-rarity contradiction (K.1.5 / Q.2 sparsity clash).**  If genuine starts own
pairwise-disjoint width-`≥ W` spans inside `range X` but their number strictly exceeds
`X / W`, the configuration is impossible.  This is the count form of the
sparse-shell density contradiction (`A_S(2X) - A_S(X) < c_* X` vs. the packed marker
count): more disjoint width-`W` blocks than the window can hold. -/
theorem span_rarity_no_overpack
    {ι : Type*} (K : Finset ι) (span : ι → Finset ℕ) (X W : ℕ) (hW : 0 < W)
    (hsub : ∀ k ∈ K, span k ⊆ Finset.range X)
    (hdisj : ∀ i ∈ K, ∀ j ∈ K, i ≠ j → Disjoint (span i) (span j))
    (hwidth : ∀ k ∈ K, W ≤ (span k).card)
    (hover : X / W < K.card) : False :=
  absurd (span_rarity_count_le_div K span X W hW hsub hdisj hwidth) (not_le.mpr hover)

end Erdos260.Tier2SpanRarity
