/-
  Erdős #260 — O2 SUPPLY side: explicit construction of the start/threshold
  rectangle and the faithful base projection of Appendix AK, discharging the
  rectangle-size and `π_st`-injection HYPOTHESES that `O2AmbientInjection`
  abstracted.  NEW module; it edits no existing file.

  Where `O2AmbientInjection.base_carrier_mass_bound` / `o2_ambient_support_summed`
  *assume*
    (hrect) `rect.card ≤ X·|I_j|`              -- the start/threshold rectangle size
    (hinj)  `Set.InjOn π_st carrier`           -- faithful start/threshold indexing
    (hmaps) `∀ ω ∈ carrier, π_st ω ∈ rect`     -- post-collar carrier lands in the shell
  this module:

  * AK.1 / AB.3 rectangle.  Builds the concrete active-shell start/threshold
    rectangle `[X,2X) × I_j = Finset.Ico X (2X) ×ˢ I_j` and proves its size is
    EXACTLY `X·|I_j|` (`startThresholdRect_card`).  This discharges (hrect) from a
    construction, matching `lem:ak-base-carrier-mass-bound`'s "the underlying
    start/threshold event set has measure `X|I_j|`".

  * AK.2 faithful indexing.  Reduces (hinj) to the already-proved carry
    faithfulness `CarryFaithfulIndexing.o2_carry_transcript_injective`: if the
    start/threshold projection refines the carry-transcript key — i.e. `(x,T)`
    determines `(d_0, R_•)` (`hkey`) — then `π_st` is injective
    (`piSt_injective_via_carry`, `piSt_injOn_via_carry`).  This is the exact
    mechanism of `lem:ak-faithful-start-threshold-indexing`: "the carry recurrence
    determines the carry states ... fixed functions of these carries and of
    `(x,T)`".

  * AK.1 base bound + collar.  `base_carrier_mass_le_rect` discharges (hrect) and
    gives `Mass ≤ X·|I_j|`; `mass_le_rect_plus_collar` adds the deleted
    endpoint/carry/tie collar as an explicit additive remainder
    `Mass ≤ X·|I_j| + |collar|` (AK.1 / AB.3, `|collar| = O_Q(L³|I_j|)`).

  * AK.3 / AD.2 summed support.  `o2_ambient_support_summed_constructed` proves the
    disjoint-cell aggregation `∑_{λ} M_tot(λ) ≤ X·|I_j|` with the rectangle now
    CONSTRUCTED, reusing the faithfulness-driven disjointness of
    `O2AmbientInjection`.

  Honest scope.  The genuinely irreducible analytic/geometric inputs remain
  hypotheses (and only these):
    - `hkey : keyOf (π_st d) = (d 0, carry P₀ Q d)` — that the start/threshold pair
       determines the carry transcript (the recurrence is driven by `(x,T)`);
       everything downstream of it (the injectivity) is then proved;
    - `hmaps` — that post-collar carrier starts lie in the active shell `[X,2X)`
       and thresholds in `I_j` (window membership);
    - `|collar| = O_Q(L³|I_j|) = o(X|I_j|)` — the deleted-collar size (asymptotic,
       `L = log₂ X`); the additive remainder is certified, the little-oh is not a
       finite inequality;
    - the cell/fibre structure (`hfib`, `hcell`) — the recurrent-cell map of
       Appendix AK, whose disjointness is already supplied by carry faithfulness.

  No `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/
import Mathlib
import Erdos260.O2AmbientInjection
import Erdos260.CarryFaithfulIndexing
import Erdos260.CarryRecurrence21
import Erdos260.P1HotspotAudit

namespace Erdos260.O2SupplyEmbedding

open Finset
open Erdos260.CarryRecurrence21
open Erdos260.CarryFaithfulIndexing

/-! ===========================================================================
    ## Section A.  The active-shell start/threshold rectangle has size `X·|I_j|`.
                                                          (AK.1 / AB.3 rectangle)

    Manuscript: App AK Def `def:ak-base-event-carrier` (line 11400):
    `π_st : Ω^post → [X,2X) × I_j`; `lem:ak-base-carrier-mass-bound` (AK.1,
    line 11426): "the underlying start/threshold event set has measure `X|I_j|`".
    We realize the shell `[X,2X)` as `Finset.Ico X (2X)` (size `X`) and the
    rectangle as its product with the threshold band `I_j` (size `|I_j|`).
    =========================================================================== -/

/-- The active-shell start window `[X, 2X)` has exactly `X` starts. -/
theorem shell_card (X : ℕ) : (Finset.Ico X (2 * X)).card = X := by
  rw [Nat.card_Ico]; omega

/-- **The start/threshold rectangle `[X,2X) × I_j` has size exactly `X·|I_j|`.**
    Discharges the `hrect` hypothesis (`rect.card ≤ X·|I_j|`) by an explicit
    construction with an equality. -/
theorem startThresholdRect_card {β : Type*} (Ij : Finset β) (X : ℕ) :
    ((Finset.Ico X (2 * X)) ×ˢ Ij).card = X * Ij.card := by
  rw [Finset.card_product, shell_card]

/-! ===========================================================================
    ## Section B.  Faithful start/threshold indexing, from carry faithfulness.
                                              (`lem:ak-faithful-start-threshold-indexing`)

    Manuscript: App AK `lem:ak-faithful-start-threshold-indexing` (AK.2, line 11407):
    "Starting from an actual row `(x,T)`, the carry recurrence determines the carry
    states ... The endpoint quotient, carry quotient, side label, and threshold
    layer are fixed functions of these carries and of `(x,T)`. ... two
    post-priority records with the same `(x,T)` ... are the same event-state
    record."  We turn this into a reduction: if `π_st` refines the carry-transcript
    key `(d_0, R_•)`, then `o2_carry_transcript_injective` gives injectivity.
    =========================================================================== -/

/-- **Faithful start/threshold indexing (`lem:ak-faithful-start-threshold-indexing`).**
    If the start/threshold projection `π_st` refines the carry-transcript key — i.e.
    there is `keyOf` reading `(d_0, carry P₀ Q d)` back from `π_st d` (the genuine
    analytic input: `(x,T)` determines the carry transcript) — then `π_st` is
    injective on digit sequences.  Routed through the proved carry faithfulness
    `o2_carry_transcript_injective`.  Discharges (hinj). -/
theorem piSt_injective_via_carry (P₀ Q : ℤ) (hQ : Q ≠ 0) {β : Type*}
    (πst : (ℕ → ℤ) → β) (keyOf : β → ℤ × (ℕ → ℤ))
    (hkey : ∀ d : ℕ → ℤ, keyOf (πst d) = (d 0, carry P₀ Q d)) :
    Function.Injective πst := by
  intro d d' h
  have hk : (d 0, carry P₀ Q d) = (d' 0, carry P₀ Q d') := by
    rw [← hkey d, ← hkey d', h]
  exact o2_carry_transcript_injective P₀ Q hQ hk

/-- `Set.InjOn` form on any carrier. -/
theorem piSt_injOn_via_carry (P₀ Q : ℤ) (hQ : Q ≠ 0) {β : Type*}
    (πst : (ℕ → ℤ) → β) (keyOf : β → ℤ × (ℕ → ℤ))
    (hkey : ∀ d : ℕ → ℤ, keyOf (πst d) = (d 0, carry P₀ Q d))
    (carrier : Finset (ℕ → ℤ)) :
    Set.InjOn πst ↑carrier :=
  fun _a _ _b _ hab => piSt_injective_via_carry P₀ Q hQ πst keyOf hkey hab

/-! ===========================================================================
    ## Section C.  Base-carrier mass bound from the constructed rectangle.  (AK.1)

    Manuscript: App AK `lem:ak-base-carrier-mass-bound` (AK.1, line 11426).  The
    injection `π_st` sends the post-collar carrier into the rectangle of size
    `X·|I_j|`, so `Mass(Ω^post) ≤ X·|I_j|`.  We reuse the injection kernel
    `P1HotspotAudit.o2_faithful_mass_bound` with the *constructed* rectangle.
    =========================================================================== -/

/-- **Base-carrier mass bound with constructed rectangle (AK.1).**  `π_st`
    injective into `[X,2X) × I_j` (size `X·|I_j|`) gives `|carrier| ≤ X·|I_j|`.
    Discharges (hrect): the rectangle size is no longer assumed but computed. -/
theorem base_carrier_mass_le_rect {Ω β : Type*} (carrier : Finset Ω) (Ij : Finset β)
    (πst : Ω → ℕ × β) (X : ℕ)
    (hmaps : ∀ ω ∈ carrier, πst ω ∈ (Finset.Ico X (2 * X)) ×ˢ Ij)
    (hinj : Set.InjOn πst ↑carrier) :
    carrier.card ≤ X * Ij.card := by
  have h := Erdos260.P1HotspotAudit.o2_faithful_mass_bound carrier
    ((Finset.Ico X (2 * X)) ×ˢ Ij) πst hmaps hinj
  rwa [startThresholdRect_card] at h

/-- **Base-carrier mass bound, both `hrect` and `hinj` discharged.**  Specialized to
    digit-sequence event states, the injection comes from carry faithfulness
    (`hkey`) and the rectangle from the construction.  Only window membership
    (`hmaps`) and the `(x,T) → transcript` refinement (`hkey`) remain. -/
theorem base_carrier_mass_via_carry (P₀ Q : ℤ) (hQ : Q ≠ 0) {β : Type*}
    (carrier : Finset (ℕ → ℤ)) (Ij : Finset β) (X : ℕ)
    (πst : (ℕ → ℤ) → ℕ × β) (keyOf : ℕ × β → ℤ × (ℕ → ℤ))
    (hkey : ∀ d : ℕ → ℤ, keyOf (πst d) = (d 0, carry P₀ Q d))
    (hmaps : ∀ d ∈ carrier, πst d ∈ (Finset.Ico X (2 * X)) ×ˢ Ij) :
    carrier.card ≤ X * Ij.card :=
  base_carrier_mass_le_rect carrier Ij πst X hmaps
    (piSt_injOn_via_carry P₀ Q hQ πst keyOf hkey carrier)

/-! ===========================================================================
    ## Section D.  The deleted-collar additive remainder.  (AK.1 / AB.3 `o(·)`)

    Manuscript: App AK `lem:ak-base-carrier-mass-bound` (AK.1, line 11430):
    `Mass(Ω^post) ≤ X|I_j| + O_Q(L³|I_j|) = X|I_j| + o(X|I_j|)`; App AB
    `lem:ab-ambient-support-bound` (AB.3, line 10800): "the deleted endpoint/
    carry/tie collars contribute `o(X|I_j|)`".  We certify the explicit additive
    decomposition; the collar's `O_Q(L³|I_j|)` magnitude is the analytic residual.
    =========================================================================== -/

/-- **Mass bound with the collar as an explicit remainder (AK.1 / AB.3).**  If the
    full carrier is covered by the post-collar part (which injects into the
    rectangle) and the deleted collar, then `Mass ≤ X·|I_j| + |collar|`.  With
    `|collar| = O_Q(L³|I_j|) = o(X|I_j|)` this is AK.1. -/
theorem mass_le_rect_plus_collar {Ω β : Type*} [DecidableEq Ω]
    (carrier post collar : Finset Ω) (Ij : Finset β) (πst : Ω → ℕ × β) (X : ℕ)
    (hcover : carrier ⊆ post ∪ collar)
    (hmaps : ∀ ω ∈ post, πst ω ∈ (Finset.Ico X (2 * X)) ×ˢ Ij)
    (hinj : Set.InjOn πst ↑post) :
    carrier.card ≤ X * Ij.card + collar.card := by
  calc carrier.card ≤ (post ∪ collar).card := Finset.card_le_card hcover
    _ ≤ post.card + collar.card := Finset.card_union_le _ _
    _ ≤ X * Ij.card + collar.card :=
        Nat.add_le_add_right (base_carrier_mass_le_rect post Ij πst X hmaps hinj) _

/-! ===========================================================================
    ## Section E.  Summed ambient support with constructed rectangle.
                                                          (AK.3 / AD.2 / AB.3)

    Manuscript: App AK `lem:ak-ambient-support-sum` (AK.3, line 11489) /
    App AD `lem:ad-summed-ambient-support` (AD.2, line 11261): the disjoint
    selected cells aggregate to `∑_λ M_tot(λ) ≤ X|I_j| + o(X|I_j|)`.  Here the
    rectangle is CONSTRUCTED; disjointness is supplied by the recurrent-cell map
    (`hfib`), itself justified by carry faithfulness in `O2AmbientInjection`.
    =========================================================================== -/

/-- **Summed ambient support with constructed rectangle (AK.3 / AD.2).**  Per-cell
    geometric supply `M_tot(λ) ≤ |Ω_λ|` over disjoint fibre-like cells inside the
    carrier, whose faithful `π_st` injects into the *constructed* rectangle
    `[X,2X) × I_j`, aggregates to `∑_λ M_tot(λ) ≤ X·|I_j|`.  This is
    `o2_ambient_support_summed` with the `hrect` hypothesis discharged. -/
theorem o2_ambient_support_summed_constructed {Ω β A : Type*} [DecidableEq Ω]
    (S : Finset A) (Ω_ : A → Finset Ω) (Λ : Ω → A) (Mtot : A → ℕ)
    (carrier : Finset Ω) (Ij : Finset β) (πst : Ω → ℕ × β) (X : ℕ)
    (hsub : ∀ a ∈ S, Ω_ a ⊆ carrier)
    (hfib : ∀ a ∈ S, ∀ ω ∈ Ω_ a, Λ ω = a)
    (hcell : ∀ a ∈ S, Mtot a ≤ (Ω_ a).card)
    (hmaps : ∀ ω ∈ carrier, πst ω ∈ (Finset.Ico X (2 * X)) ×ˢ Ij)
    (hinj : Set.InjOn πst ↑carrier) :
    ∑ a ∈ S, Mtot a ≤ X * Ij.card :=
  Erdos260.O2AmbientInjection.ambient_mass_le_weighted S Ω_ Λ Mtot carrier X Ij.card
    hsub hfib hcell (base_carrier_mass_le_rect carrier Ij πst X hmaps hinj)

/-- **End-to-end O2 supply capstone.**  On digit-sequence event states: per-cell
    geometric supply over disjoint cells, faithful `π_st` whose injectivity is the
    proved carry faithfulness (via `hkey`) and whose target is the constructed
    rectangle, give `∑_λ M_tot(λ) ≤ X·|I_j|`.  Both (hrect) and (hinj) are
    discharged; only `hkey` (the `(x,T)→transcript` refinement), window membership
    `hmaps`, and the cell structure `hfib`,`hcell` remain — the genuine supply. -/
theorem o2_supply_capstone (P₀ Q : ℤ) (hQ : Q ≠ 0) {β A : Type*}
    (S : Finset A) (Ω_ : A → Finset (ℕ → ℤ)) (Λ : (ℕ → ℤ) → A) (Mtot : A → ℕ)
    (carrier : Finset (ℕ → ℤ)) (Ij : Finset β) (X : ℕ)
    (πst : (ℕ → ℤ) → ℕ × β) (keyOf : ℕ × β → ℤ × (ℕ → ℤ))
    (hkey : ∀ d : ℕ → ℤ, keyOf (πst d) = (d 0, carry P₀ Q d))
    (hsub : ∀ a ∈ S, Ω_ a ⊆ carrier)
    (hfib : ∀ a ∈ S, ∀ ω ∈ Ω_ a, Λ ω = a)
    (hcell : ∀ a ∈ S, Mtot a ≤ (Ω_ a).card)
    (hmaps : ∀ d ∈ carrier, πst d ∈ (Finset.Ico X (2 * X)) ×ˢ Ij) :
    ∑ a ∈ S, Mtot a ≤ X * Ij.card := by
  classical
  exact o2_ambient_support_summed_constructed S Ω_ Λ Mtot carrier Ij πst X
    hsub hfib hcell hmaps (piSt_injOn_via_carry P₀ Q hQ πst keyOf hkey carrier)

end Erdos260.O2SupplyEmbedding
