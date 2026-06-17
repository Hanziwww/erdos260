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

/-- Carrier-local `Set.InjOn` form.  The AK faithful-indexing argument only
    needs the `(x,T) -> transcript` refinement on the post-collar carrier being
    counted, not on all digit sequences. -/
theorem piSt_injOn_via_carry_on (P₀ Q : ℤ) (hQ : Q ≠ 0) {β : Type*}
    (πst : (ℕ → ℤ) → β) (keyOf : β → ℤ × (ℕ → ℤ))
    (carrier : Finset (ℕ → ℤ))
    (hkey : ∀ d : ℕ → ℤ, d ∈ carrier →
      keyOf (πst d) = (d 0, carry P₀ Q d)) :
    Set.InjOn πst ↑carrier := by
  intro d hd d' hd' h
  have hk : (d 0, carry P₀ Q d) = (d' 0, carry P₀ Q d') := by
    rw [← hkey d hd, ← hkey d' hd', h]
  exact o2_carry_transcript_injective P₀ Q hQ hk

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

/-- Carrier-local version of `base_carrier_mass_via_carry`: the transcript key is
    only required on the counted carrier. -/
theorem base_carrier_mass_via_carry_on (P₀ Q : ℤ) (hQ : Q ≠ 0) {β : Type*}
    (carrier : Finset (ℕ → ℤ)) (Ij : Finset β) (X : ℕ)
    (πst : (ℕ → ℤ) → ℕ × β) (keyOf : ℕ × β → ℤ × (ℕ → ℤ))
    (hkey : ∀ d : ℕ → ℤ, d ∈ carrier →
      keyOf (πst d) = (d 0, carry P₀ Q d))
    (hmaps : ∀ d ∈ carrier, πst d ∈ (Finset.Ico X (2 * X)) ×ˢ Ij) :
    carrier.card ≤ X * Ij.card :=
  base_carrier_mass_le_rect carrier Ij πst X hmaps
    (piSt_injOn_via_carry_on P₀ Q hQ πst keyOf carrier hkey)

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

/-- **Carrier-local carry form of the deleted-collar bound (AK.1 / AB.3).**
    On digit-sequence event states, the post-collar part injects into the
    constructed start/threshold rectangle by the carry-transcript key, while the
    deleted collar remains as the explicit additive finite remainder. -/
theorem mass_le_rect_plus_collar_via_carry_on (P₀ Q : ℤ) (hQ : Q ≠ 0) {β : Type*}
    [DecidableEq (ℕ → ℤ)]
    (carrier post collar : Finset (ℕ → ℤ)) (Ij : Finset β) (πst : (ℕ → ℤ) → ℕ × β)
    (keyOf : ℕ × β → ℤ × (ℕ → ℤ)) (X : ℕ)
    (hkey : ∀ d : ℕ → ℤ, d ∈ post → keyOf (πst d) = (d 0, carry P₀ Q d))
    (hcover : carrier ⊆ post ∪ collar)
    (hmaps : ∀ d ∈ post, πst d ∈ (Finset.Ico X (2 * X)) ×ˢ Ij) :
    carrier.card ≤ X * Ij.card + collar.card :=
  mass_le_rect_plus_collar carrier post collar Ij πst X hcover hmaps
    (piSt_injOn_via_carry_on P₀ Q hQ πst keyOf post hkey)

/-- Residual input surface for the AK.1 deleted-collar carrier bound.  The
rectangle size and post-collar injectivity are discharged here; the remaining
inputs are exactly the post/collar cover, post-window membership, and the
carrier-local transcript key on the post-collar carrier. -/
structure O2CollarInputs (P₀ Q : ℤ) {β : Type*} [DecidableEq (ℕ → ℤ)]
    (carrier post collar : Finset (ℕ → ℤ)) (Ij : Finset β) (X : ℕ)
    (piSt : (ℕ → ℤ) → ℕ × β) (keyOf : ℕ × β → ℤ × (ℕ → ℤ)) where
  hQ : Q ≠ 0
  hkey : ∀ d : ℕ → ℤ, d ∈ post → keyOf (piSt d) = (d 0, carry P₀ Q d)
  hcover : carrier ⊆ post ∪ collar
  hmaps : ∀ d ∈ post, piSt d ∈ (Finset.Ico X (2 * X)) ×ˢ Ij

namespace O2CollarInputs

/-- Packaged AK.1 deleted-collar bound:
`|carrier| ≤ X |I_j| + |collar|`. -/
theorem card_bound (P₀ Q : ℤ) {β : Type*}
    [DecidableEq (ℕ → ℤ)]
    (carrier post collar : Finset (ℕ → ℤ)) (Ij : Finset β) (X : ℕ)
    (piSt : (ℕ → ℤ) → ℕ × β) (keyOf : ℕ × β → ℤ × (ℕ → ℤ))
    (I : O2CollarInputs P₀ Q carrier post collar Ij X piSt keyOf) :
    carrier.card ≤ X * Ij.card + collar.card :=
  mass_le_rect_plus_collar_via_carry_on P₀ Q I.hQ carrier post collar Ij piSt keyOf X
    I.hkey I.hcover I.hmaps

/-- Packaged AK.1 deleted-collar bound after an explicit finite collar estimate:
if the deleted collar has size at most `E`, then `|carrier| ≤ X |I_j| + E`.
This is the finite Lean handoff for the manuscript's later `o(X|I_j|)` collar
estimate. -/
theorem card_bound_with_error (P₀ Q : ℤ) {β : Type*}
    [DecidableEq (ℕ → ℤ)]
    (carrier post collar : Finset (ℕ → ℤ)) (Ij : Finset β) (X E : ℕ)
    (piSt : (ℕ → ℤ) → ℕ × β) (keyOf : ℕ × β → ℤ × (ℕ → ℤ))
    (I : O2CollarInputs P₀ Q carrier post collar Ij X piSt keyOf)
    (hcollar : collar.card ≤ E) :
    carrier.card ≤ X * Ij.card + E :=
  le_trans
    (card_bound P₀ Q carrier post collar Ij X piSt keyOf I)
    (Nat.add_le_add_left hcollar _)

/-- A global AK.2 transcript refinement is a special case of the post-collar
local key required by the deleted-collar carrier package. -/
def ofGlobalKey (P₀ Q : ℤ) {β : Type*} [DecidableEq (ℕ → ℤ)]
    (carrier post collar : Finset (ℕ → ℤ)) (Ij : Finset β) (X : ℕ)
    (piSt : (ℕ → ℤ) → ℕ × β) (keyOf : ℕ × β → ℤ × (ℕ → ℤ))
    (hQ : Q ≠ 0)
    (hkey : ∀ d : ℕ → ℤ, keyOf (piSt d) = (d 0, carry P₀ Q d))
    (hcover : carrier ⊆ post ∪ collar)
    (hmaps : ∀ d : ℕ → ℤ, d ∈ post -> piSt d ∈ (Finset.Ico X (2 * X)) ×ˢ Ij) :
    O2CollarInputs P₀ Q carrier post collar Ij X piSt keyOf where
  hQ := hQ
  hkey := fun d _hd => hkey d
  hcover := hcover
  hmaps := hmaps

end O2CollarInputs

/-- Coordinate-split deleted-collar carrier surface.  This is the AK.1 base
projection written in TeX coordinates: start in `[X,2X)` and threshold in `I_j`,
instead of as one product-membership hypothesis. -/
structure O2CollarCoordinateInputs (P0 Q : Int) {β : Type*}
    [DecidableEq (Nat -> Int)]
    (carrier post collar : Finset (Nat -> Int)) (Ij : Finset β) (X : Nat)
    (piSt : (Nat -> Int) -> Nat × β) (keyOf : Nat × β -> Int × (Nat -> Int)) where
  hQ : Q ≠ 0
  hkey : forall d : Nat -> Int, d ∈ post ->
    keyOf (piSt d) = (d 0, carry P0 Q d)
  hcover : carrier ⊆ post ∪ collar
  hstart : forall d, d ∈ post -> (piSt d).1 ∈ Finset.Ico X (2 * X)
  hthreshold : forall d, d ∈ post -> (piSt d).2 ∈ Ij

namespace O2CollarCoordinateInputs

/-- Product-rectangle membership projects back to the two coordinate facts used
by the coordinate-split deleted-collar surface. -/
def ofProductInputs (P0 Q : Int) {B : Type*} [DecidableEq (Nat -> Int)]
    (carrier post collar : Finset (Nat -> Int)) (Ij : Finset B) (X : Nat)
    (piSt : (Nat -> Int) -> Prod Nat B) (keyOf : Prod Nat B -> Prod Int (Nat -> Int))
    (I : O2CollarInputs P0 Q carrier post collar Ij X piSt keyOf) :
    O2CollarCoordinateInputs P0 Q carrier post collar Ij X piSt keyOf where
  hQ := I.hQ
  hkey := I.hkey
  hcover := I.hcover
  hstart := by
    intro d hd
    exact (Finset.mem_product.mp (I.hmaps d hd)).1
  hthreshold := by
    intro d hd
    exact (Finset.mem_product.mp (I.hmaps d hd)).2

/-- Coordinate membership assembles to the product-rectangle membership used by
`O2CollarInputs`. -/
def toCollarInputs (P0 Q : Int) {β : Type*} [DecidableEq (Nat -> Int)]
    (carrier post collar : Finset (Nat -> Int)) (Ij : Finset β) (X : Nat)
    (piSt : (Nat -> Int) -> Nat × β) (keyOf : Nat × β -> Int × (Nat -> Int))
    (I : O2CollarCoordinateInputs P0 Q carrier post collar Ij X piSt keyOf) :
    O2CollarInputs P0 Q carrier post collar Ij X piSt keyOf where
  hQ := I.hQ
  hkey := I.hkey
  hcover := I.hcover
  hmaps := by
    intro d hd
    exact Finset.mem_product.mpr ⟨I.hstart d hd, I.hthreshold d hd⟩

/-- Coordinate-split AK.1 deleted-collar bound:
`|carrier| <= X |I_j| + |collar|`. -/
theorem card_bound (P0 Q : Int) {β : Type*} [DecidableEq (Nat -> Int)]
    (carrier post collar : Finset (Nat -> Int)) (Ij : Finset β) (X : Nat)
    (piSt : (Nat -> Int) -> Nat × β) (keyOf : Nat × β -> Int × (Nat -> Int))
    (I : O2CollarCoordinateInputs P0 Q carrier post collar Ij X piSt keyOf) :
    carrier.card <= X * Ij.card + collar.card :=
  O2CollarInputs.card_bound P0 Q carrier post collar Ij X piSt keyOf
    (toCollarInputs P0 Q carrier post collar Ij X piSt keyOf I)

/-- Coordinate-split AK.1 deleted-collar bound with an explicit finite error. -/
theorem card_bound_with_error (P0 Q : Int) {β : Type*}
    [DecidableEq (Nat -> Int)]
    (carrier post collar : Finset (Nat -> Int)) (Ij : Finset β) (X E : Nat)
    (piSt : (Nat -> Int) -> Nat × β) (keyOf : Nat × β -> Int × (Nat -> Int))
    (I : O2CollarCoordinateInputs P0 Q carrier post collar Ij X piSt keyOf)
    (hcollar : collar.card <= E) :
    carrier.card <= X * Ij.card + E :=
  O2CollarInputs.card_bound_with_error P0 Q carrier post collar Ij X E piSt keyOf
    (toCollarInputs P0 Q carrier post collar Ij X piSt keyOf I) hcollar

/-- A global AK.2 transcript refinement is a special case of the post-collar
local key required by the coordinate-split deleted-collar package. -/
def ofGlobalKey (P0 Q : Int) {β : Type*} [DecidableEq (Nat -> Int)]
    (carrier post collar : Finset (Nat -> Int)) (Ij : Finset β) (X : Nat)
    (piSt : (Nat -> Int) -> Nat × β) (keyOf : Nat × β -> Int × (Nat -> Int))
    (hQ : Q ≠ 0)
    (hkey : forall d : Nat -> Int, keyOf (piSt d) = (d 0, carry P0 Q d))
    (hcover : carrier ⊆ post ∪ collar)
    (hstart : forall d, d ∈ post -> (piSt d).1 ∈ Finset.Ico X (2 * X))
    (hthreshold : forall d, d ∈ post -> (piSt d).2 ∈ Ij) :
    O2CollarCoordinateInputs P0 Q carrier post collar Ij X piSt keyOf where
  hQ := hQ
  hkey := fun d _hd => hkey d
  hcover := hcover
  hstart := hstart
  hthreshold := hthreshold

/-- Global-key coordinate form of the AK.1 deleted-collar bound. -/
theorem card_bound_ofGlobalKey (P0 Q : Int) {β : Type*} [DecidableEq (Nat -> Int)]
    (carrier post collar : Finset (Nat -> Int)) (Ij : Finset β) (X : Nat)
    (piSt : (Nat -> Int) -> Nat × β) (keyOf : Nat × β -> Int × (Nat -> Int))
    (hQ : Q ≠ 0)
    (hkey : forall d : Nat -> Int, keyOf (piSt d) = (d 0, carry P0 Q d))
    (hcover : carrier ⊆ post ∪ collar)
    (hstart : forall d, d ∈ post -> (piSt d).1 ∈ Finset.Ico X (2 * X))
    (hthreshold : forall d, d ∈ post -> (piSt d).2 ∈ Ij) :
    carrier.card <= X * Ij.card + collar.card :=
  card_bound P0 Q carrier post collar Ij X piSt keyOf
    (ofGlobalKey P0 Q carrier post collar Ij X piSt keyOf
      hQ hkey hcover hstart hthreshold)

/-- Global-key coordinate form of the AK.1 deleted-collar bound with an
explicit finite collar estimate. -/
theorem card_bound_with_error_ofGlobalKey (P0 Q : Int) {β : Type*}
    [DecidableEq (Nat -> Int)]
    (carrier post collar : Finset (Nat -> Int)) (Ij : Finset β) (X E : Nat)
    (piSt : (Nat -> Int) -> Nat × β) (keyOf : Nat × β -> Int × (Nat -> Int))
    (hQ : Q ≠ 0)
    (hkey : forall d : Nat -> Int, keyOf (piSt d) = (d 0, carry P0 Q d))
    (hcover : carrier ⊆ post ∪ collar)
    (hstart : forall d, d ∈ post -> (piSt d).1 ∈ Finset.Ico X (2 * X))
    (hthreshold : forall d, d ∈ post -> (piSt d).2 ∈ Ij)
    (hcollar : collar.card <= E) :
    carrier.card <= X * Ij.card + E :=
  card_bound_with_error P0 Q carrier post collar Ij X E piSt keyOf
    (ofGlobalKey P0 Q carrier post collar Ij X piSt keyOf
      hQ hkey hcover hstart hthreshold)
    hcollar

end O2CollarCoordinateInputs

/-! ---------------------------------------------------------------------------
    ## Section D'.  Summed ambient support with the same deleted-collar error.

    App AK/AD usually consumes the support statement in summed form:
    selected cells pack into one carrier, the post-collar part injects into the
    start/threshold rectangle, and the deleted endpoint/carry/tie collar is added
    once as an explicit finite remainder.  The theorem below is exactly that
    composition of the already-proved disjoint-packing and collar bounds.
    --------------------------------------------------------------------------- -/

/-- **Summed ambient support with one deleted-collar remainder (AK.3 / AD.2).**
    Per-cell geometric weights `Mtot a ≤ |Omega a|` over fibre-like selected cells
    inside a carrier covered by `post ∪ collar` satisfy
    `∑ Mtot ≤ X * |I_j| + |collar|`, provided the post-collar carrier injects into
    the constructed start/threshold rectangle. -/
theorem o2_ambient_support_summed_with_collar_constructed {Ω β A : Type*}
    [DecidableEq Ω]
    (S : Finset A) (Omega : A → Finset Ω) (Lambda : Ω → A) (Mtot : A → ℕ)
    (carrier post collar : Finset Ω) (Ij : Finset β) (piSt : Ω → ℕ × β) (X : ℕ)
    (hsub : ∀ a ∈ S, Omega a ⊆ carrier)
    (hfib : ∀ a ∈ S, ∀ omega ∈ Omega a, Lambda omega = a)
    (hcell : ∀ a ∈ S, Mtot a ≤ (Omega a).card)
    (hcover : carrier ⊆ post ∪ collar)
    (hmaps : ∀ omega ∈ post, piSt omega ∈ (Finset.Ico X (2 * X)) ×ˢ Ij)
    (hinj : Set.InjOn piSt ↑post) :
    ∑ a ∈ S, Mtot a ≤ X * Ij.card + collar.card := by
  have hpack :
      ∑ a ∈ S, (Omega a).card ≤ carrier.card :=
    Erdos260.O2AmbientInjection.sum_card_le_of_disjoint_ground S Omega carrier hsub
      (Erdos260.O2AmbientInjection.slices_disjoint_of_label_coherent S Omega Lambda hfib)
  have hweighted : ∑ a ∈ S, Mtot a ≤ carrier.card :=
    le_trans (Finset.sum_le_sum hcell) hpack
  exact le_trans hweighted
    (mass_le_rect_plus_collar carrier post collar Ij piSt X hcover hmaps hinj)

/-- **Carry-faithful form of the summed collar bound.**  The post-collar
    injectivity required above is discharged from the carrier-local transcript key
    `(x,T) ↦ (d₀, carry P₀ Q d)`. -/
theorem o2_ambient_support_summed_with_collar_via_carry_on
    (P₀ Q : ℤ) (hQ : Q ≠ 0) {β A : Type*} [DecidableEq (ℕ → ℤ)]
    (S : Finset A) (Omega : A → Finset (ℕ → ℤ)) (Lambda : (ℕ → ℤ) → A)
    (Mtot : A → ℕ) (carrier post collar : Finset (ℕ → ℤ)) (Ij : Finset β)
    (X : ℕ) (piSt : (ℕ → ℤ) → ℕ × β)
    (keyOf : ℕ × β → ℤ × (ℕ → ℤ))
    (hkey : ∀ d : ℕ → ℤ, d ∈ post → keyOf (piSt d) = (d 0, carry P₀ Q d))
    (hsub : ∀ a ∈ S, Omega a ⊆ carrier)
    (hfib : ∀ a ∈ S, ∀ omega ∈ Omega a, Lambda omega = a)
    (hcell : ∀ a ∈ S, Mtot a ≤ (Omega a).card)
    (hcover : carrier ⊆ post ∪ collar)
    (hmaps : ∀ d ∈ post, piSt d ∈ (Finset.Ico X (2 * X)) ×ˢ Ij) :
    ∑ a ∈ S, Mtot a ≤ X * Ij.card + collar.card :=
  o2_ambient_support_summed_with_collar_constructed S Omega Lambda Mtot carrier post
    collar Ij piSt X hsub hfib hcell hcover hmaps
    (piSt_injOn_via_carry_on P₀ Q hQ piSt keyOf post hkey)

/-- Residual input surface for the AK/AD summed support statement with the
deleted collar kept as the single additive error term. -/
structure O2CollarSupplyInputs (P₀ Q : ℤ) {β A : Type*}
    [DecidableEq (ℕ → ℤ)]
    (S : Finset A) (Omega : A → Finset (ℕ → ℤ)) (Lambda : (ℕ → ℤ) → A)
    (Mtot : A → ℕ) (carrier post collar : Finset (ℕ → ℤ)) (Ij : Finset β)
    (X : ℕ) (piSt : (ℕ → ℤ) → ℕ × β)
    (keyOf : ℕ × β → ℤ × (ℕ → ℤ)) where
  hQ : Q ≠ 0
  hkey : ∀ d : ℕ → ℤ, d ∈ post → keyOf (piSt d) = (d 0, carry P₀ Q d)
  hsub : ∀ a ∈ S, Omega a ⊆ carrier
  hfib : ∀ a ∈ S, ∀ omega ∈ Omega a, Lambda omega = a
  hcell : ∀ a ∈ S, Mtot a ≤ (Omega a).card
  hcover : carrier ⊆ post ∪ collar
  hmaps : ∀ d ∈ post, piSt d ∈ (Finset.Ico X (2 * X)) ×ˢ Ij

namespace O2CollarSupplyInputs

/-- Packaged AK/AD summed support with the single deleted-collar error:
`∑ Mtot ≤ X |I_j| + |collar|`. -/
theorem summed_bound (P₀ Q : ℤ) {β A : Type*} [DecidableEq (ℕ → ℤ)]
    (S : Finset A) (Omega : A → Finset (ℕ → ℤ)) (Lambda : (ℕ → ℤ) → A)
    (Mtot : A → ℕ) (carrier post collar : Finset (ℕ → ℤ)) (Ij : Finset β)
    (X : ℕ) (piSt : (ℕ → ℤ) → ℕ × β)
    (keyOf : ℕ × β → ℤ × (ℕ → ℤ))
    (I : O2CollarSupplyInputs P₀ Q S Omega Lambda Mtot carrier post collar Ij X piSt keyOf) :
    ∑ a ∈ S, Mtot a ≤ X * Ij.card + collar.card :=
  o2_ambient_support_summed_with_collar_via_carry_on P₀ Q I.hQ S Omega Lambda Mtot
    carrier post collar Ij X piSt keyOf I.hkey I.hsub I.hfib I.hcell I.hcover I.hmaps

/-- Packaged AK/AD summed support after an explicit finite collar estimate:
`∑ Mtot ≤ X |I_j| + E` whenever the deleted collar has size at most `E`. -/
theorem summed_bound_with_error (P₀ Q : ℤ) {β A : Type*} [DecidableEq (ℕ → ℤ)]
    (S : Finset A) (Omega : A → Finset (ℕ → ℤ)) (Lambda : (ℕ → ℤ) → A)
    (Mtot : A → ℕ) (carrier post collar : Finset (ℕ → ℤ)) (Ij : Finset β)
    (X E : ℕ) (piSt : (ℕ → ℤ) → ℕ × β)
    (keyOf : ℕ × β → ℤ × (ℕ → ℤ))
    (I : O2CollarSupplyInputs P₀ Q S Omega Lambda Mtot carrier post collar Ij X piSt keyOf)
    (hcollar : collar.card ≤ E) :
    ∑ a ∈ S, Mtot a ≤ X * Ij.card + E :=
  le_trans
    (summed_bound P₀ Q S Omega Lambda Mtot carrier post collar Ij X piSt keyOf I)
    (Nat.add_le_add_left hcollar _)

/-- A global AK.2 transcript refinement is a special case of the post-collar
local key required by the summed deleted-collar package. -/
def ofGlobalKey (P₀ Q : ℤ) {β A : Type*} [DecidableEq (ℕ → ℤ)]
    (S : Finset A) (Omega : A → Finset (ℕ → ℤ)) (Lambda : (ℕ → ℤ) → A)
    (Mtot : A → ℕ) (carrier post collar : Finset (ℕ → ℤ)) (Ij : Finset β)
    (X : ℕ) (piSt : (ℕ → ℤ) → ℕ × β)
    (keyOf : ℕ × β → ℤ × (ℕ → ℤ))
    (hQ : Q ≠ 0)
    (hkey : ∀ d : ℕ → ℤ, keyOf (piSt d) = (d 0, carry P₀ Q d))
    (hsub : ∀ a, a ∈ S -> Omega a ⊆ carrier)
    (hfib : ∀ a, a ∈ S -> ∀ omega, omega ∈ Omega a -> Lambda omega = a)
    (hcell : ∀ a, a ∈ S -> Mtot a <= (Omega a).card)
    (hcover : carrier ⊆ post ∪ collar)
    (hmaps : ∀ d : ℕ → ℤ, d ∈ post -> piSt d ∈ (Finset.Ico X (2 * X)) ×ˢ Ij) :
    O2CollarSupplyInputs P₀ Q S Omega Lambda Mtot carrier post collar Ij X piSt keyOf where
  hQ := hQ
  hkey := fun d _hd => hkey d
  hsub := hsub
  hfib := hfib
  hcell := hcell
  hcover := hcover
  hmaps := hmaps

end O2CollarSupplyInputs

/-- Coordinate-split AK/AD summed support surface with the deleted collar kept
as the single additive error.  This mirrors `O2CollarSupplyInputs` but records
the base projection target as its two TeX coordinates. -/
structure O2CollarSupplyCoordinateInputs (P0 Q : Int) {β A : Type*}
    [DecidableEq (Nat -> Int)]
    (S : Finset A) (Omega : A -> Finset (Nat -> Int)) (Lambda : (Nat -> Int) -> A)
    (Mtot : A -> Nat) (carrier post collar : Finset (Nat -> Int)) (Ij : Finset β)
    (X : Nat) (piSt : (Nat -> Int) -> Nat × β)
    (keyOf : Nat × β -> Int × (Nat -> Int)) where
  hQ : Q ≠ 0
  hkey : forall d : Nat -> Int, d ∈ post ->
    keyOf (piSt d) = (d 0, carry P0 Q d)
  hsub : forall a, a ∈ S -> Omega a ⊆ carrier
  hfib : forall a, a ∈ S -> forall omega, omega ∈ Omega a -> Lambda omega = a
  hcell : forall a, a ∈ S -> Mtot a <= (Omega a).card
  hcover : carrier ⊆ post ∪ collar
  hstart : forall d, d ∈ post -> (piSt d).1 ∈ Finset.Ico X (2 * X)
  hthreshold : forall d, d ∈ post -> (piSt d).2 ∈ Ij

namespace O2CollarSupplyCoordinateInputs

/-- Product-rectangle membership projects back to the coordinate-split summed
deleted-collar surface. -/
def ofProductInputs (P0 Q : Int) {B A : Type*} [DecidableEq (Nat -> Int)]
    (S : Finset A) (Omega : A -> Finset (Nat -> Int)) (Lambda : (Nat -> Int) -> A)
    (Mtot : A -> Nat) (carrier post collar : Finset (Nat -> Int)) (Ij : Finset B)
    (X : Nat) (piSt : (Nat -> Int) -> Prod Nat B)
    (keyOf : Prod Nat B -> Prod Int (Nat -> Int))
    (I : O2CollarSupplyInputs P0 Q S Omega Lambda Mtot carrier post collar Ij X
      piSt keyOf) :
    O2CollarSupplyCoordinateInputs P0 Q S Omega Lambda Mtot carrier post collar Ij X
      piSt keyOf where
  hQ := I.hQ
  hkey := I.hkey
  hsub := I.hsub
  hfib := I.hfib
  hcell := I.hcell
  hcover := I.hcover
  hstart := by
    intro d hd
    exact (Finset.mem_product.mp (I.hmaps d hd)).1
  hthreshold := by
    intro d hd
    exact (Finset.mem_product.mp (I.hmaps d hd)).2

/-- Coordinate membership assembles to the product-rectangle membership used by
`O2CollarSupplyInputs`. -/
def toCollarSupplyInputs (P0 Q : Int) {β A : Type*} [DecidableEq (Nat -> Int)]
    (S : Finset A) (Omega : A -> Finset (Nat -> Int)) (Lambda : (Nat -> Int) -> A)
    (Mtot : A -> Nat) (carrier post collar : Finset (Nat -> Int)) (Ij : Finset β)
    (X : Nat) (piSt : (Nat -> Int) -> Nat × β)
    (keyOf : Nat × β -> Int × (Nat -> Int))
    (I : O2CollarSupplyCoordinateInputs P0 Q S Omega Lambda Mtot carrier post
      collar Ij X piSt keyOf) :
    O2CollarSupplyInputs P0 Q S Omega Lambda Mtot carrier post collar Ij X piSt keyOf where
  hQ := I.hQ
  hkey := I.hkey
  hsub := I.hsub
  hfib := I.hfib
  hcell := I.hcell
  hcover := I.hcover
  hmaps := by
    intro d hd
    exact Finset.mem_product.mpr ⟨I.hstart d hd, I.hthreshold d hd⟩

/-- Coordinate-split AK/AD summed support with the single deleted-collar error:
`sum Mtot <= X |I_j| + |collar|`. -/
theorem summed_bound (P0 Q : Int) {β A : Type*} [DecidableEq (Nat -> Int)]
    (S : Finset A) (Omega : A -> Finset (Nat -> Int)) (Lambda : (Nat -> Int) -> A)
    (Mtot : A -> Nat) (carrier post collar : Finset (Nat -> Int)) (Ij : Finset β)
    (X : Nat) (piSt : (Nat -> Int) -> Nat × β)
    (keyOf : Nat × β -> Int × (Nat -> Int))
    (I : O2CollarSupplyCoordinateInputs P0 Q S Omega Lambda Mtot carrier post
      collar Ij X piSt keyOf) :
    ∑ a ∈ S, Mtot a <= X * Ij.card + collar.card :=
  O2CollarSupplyInputs.summed_bound P0 Q S Omega Lambda Mtot carrier post collar
    Ij X piSt keyOf
    (toCollarSupplyInputs P0 Q S Omega Lambda Mtot carrier post collar Ij X piSt keyOf I)

/-- Coordinate-split AK/AD summed support after an explicit finite collar
estimate. -/
theorem summed_bound_with_error (P0 Q : Int) {β A : Type*}
    [DecidableEq (Nat -> Int)]
    (S : Finset A) (Omega : A -> Finset (Nat -> Int)) (Lambda : (Nat -> Int) -> A)
    (Mtot : A -> Nat) (carrier post collar : Finset (Nat -> Int)) (Ij : Finset β)
    (X E : Nat) (piSt : (Nat -> Int) -> Nat × β)
    (keyOf : Nat × β -> Int × (Nat -> Int))
    (I : O2CollarSupplyCoordinateInputs P0 Q S Omega Lambda Mtot carrier post
      collar Ij X piSt keyOf)
    (hcollar : collar.card <= E) :
    ∑ a ∈ S, Mtot a <= X * Ij.card + E :=
  O2CollarSupplyInputs.summed_bound_with_error P0 Q S Omega Lambda Mtot carrier post
    collar Ij X E piSt keyOf
    (toCollarSupplyInputs P0 Q S Omega Lambda Mtot carrier post collar Ij X piSt keyOf I)
    hcollar

/-- A global AK.2 transcript refinement is a special case of the post-collar
local key required by the coordinate-split summed deleted-collar package. -/
def ofGlobalKey (P0 Q : Int) {β A : Type*} [DecidableEq (Nat -> Int)]
    (S : Finset A) (Omega : A -> Finset (Nat -> Int)) (Lambda : (Nat -> Int) -> A)
    (Mtot : A -> Nat) (carrier post collar : Finset (Nat -> Int)) (Ij : Finset β)
    (X : Nat) (piSt : (Nat -> Int) -> Nat × β)
    (keyOf : Nat × β -> Int × (Nat -> Int))
    (hQ : Q ≠ 0)
    (hkey : forall d : Nat -> Int, keyOf (piSt d) = (d 0, carry P0 Q d))
    (hsub : forall a, a ∈ S -> Omega a ⊆ carrier)
    (hfib : forall a, a ∈ S -> forall omega, omega ∈ Omega a -> Lambda omega = a)
    (hcell : forall a, a ∈ S -> Mtot a <= (Omega a).card)
    (hcover : carrier ⊆ post ∪ collar)
    (hstart : forall d, d ∈ post -> (piSt d).1 ∈ Finset.Ico X (2 * X))
    (hthreshold : forall d, d ∈ post -> (piSt d).2 ∈ Ij) :
    O2CollarSupplyCoordinateInputs P0 Q S Omega Lambda Mtot carrier post collar Ij X
      piSt keyOf where
  hQ := hQ
  hkey := fun d _hd => hkey d
  hsub := hsub
  hfib := hfib
  hcell := hcell
  hcover := hcover
  hstart := hstart
  hthreshold := hthreshold

/-- Global-key coordinate form of the AK/AD summed support bound with the
deleted collar kept as the single finite remainder. -/
theorem summed_bound_ofGlobalKey (P0 Q : Int) {β A : Type*}
    [DecidableEq (Nat -> Int)]
    (S : Finset A) (Omega : A -> Finset (Nat -> Int)) (Lambda : (Nat -> Int) -> A)
    (Mtot : A -> Nat) (carrier post collar : Finset (Nat -> Int)) (Ij : Finset β)
    (X : Nat) (piSt : (Nat -> Int) -> Nat × β)
    (keyOf : Nat × β -> Int × (Nat -> Int))
    (hQ : Q ≠ 0)
    (hkey : forall d : Nat -> Int, keyOf (piSt d) = (d 0, carry P0 Q d))
    (hsub : forall a, a ∈ S -> Omega a ⊆ carrier)
    (hfib : forall a, a ∈ S -> forall omega, omega ∈ Omega a -> Lambda omega = a)
    (hcell : forall a, a ∈ S -> Mtot a <= (Omega a).card)
    (hcover : carrier ⊆ post ∪ collar)
    (hstart : forall d, d ∈ post -> (piSt d).1 ∈ Finset.Ico X (2 * X))
    (hthreshold : forall d, d ∈ post -> (piSt d).2 ∈ Ij) :
    ∑ a ∈ S, Mtot a <= X * Ij.card + collar.card :=
  summed_bound P0 Q S Omega Lambda Mtot carrier post collar Ij X piSt keyOf
    (ofGlobalKey P0 Q S Omega Lambda Mtot carrier post collar Ij X piSt keyOf
      hQ hkey hsub hfib hcell hcover hstart hthreshold)

/-- Global-key coordinate form of the AK/AD summed support bound after an
explicit finite collar estimate. -/
theorem summed_bound_with_error_ofGlobalKey (P0 Q : Int) {β A : Type*}
    [DecidableEq (Nat -> Int)]
    (S : Finset A) (Omega : A -> Finset (Nat -> Int)) (Lambda : (Nat -> Int) -> A)
    (Mtot : A -> Nat) (carrier post collar : Finset (Nat -> Int)) (Ij : Finset β)
    (X E : Nat) (piSt : (Nat -> Int) -> Nat × β)
    (keyOf : Nat × β -> Int × (Nat -> Int))
    (hQ : Q ≠ 0)
    (hkey : forall d : Nat -> Int, keyOf (piSt d) = (d 0, carry P0 Q d))
    (hsub : forall a, a ∈ S -> Omega a ⊆ carrier)
    (hfib : forall a, a ∈ S -> forall omega, omega ∈ Omega a -> Lambda omega = a)
    (hcell : forall a, a ∈ S -> Mtot a <= (Omega a).card)
    (hcover : carrier ⊆ post ∪ collar)
    (hstart : forall d, d ∈ post -> (piSt d).1 ∈ Finset.Ico X (2 * X))
    (hthreshold : forall d, d ∈ post -> (piSt d).2 ∈ Ij)
    (hcollar : collar.card <= E) :
    ∑ a ∈ S, Mtot a <= X * Ij.card + E :=
  summed_bound_with_error P0 Q S Omega Lambda Mtot carrier post collar Ij X E piSt keyOf
    (ofGlobalKey P0 Q S Omega Lambda Mtot carrier post collar Ij X piSt keyOf
      hQ hkey hsub hfib hcell hcover hstart hthreshold)
    hcollar

end O2CollarSupplyCoordinateInputs

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

/-- **Carrier-local O2 supply capstone.**  This is the exact packaged form used
    below: the carry-key refinement is required only for event states in the
    post-collar carrier. -/
theorem o2_supply_capstone_on (P₀ Q : ℤ) (hQ : Q ≠ 0) {β A : Type*}
    (S : Finset A) (Ω_ : A → Finset (ℕ → ℤ)) (Λ : (ℕ → ℤ) → A) (Mtot : A → ℕ)
    (carrier : Finset (ℕ → ℤ)) (Ij : Finset β) (X : ℕ)
    (πst : (ℕ → ℤ) → ℕ × β) (keyOf : ℕ × β → ℤ × (ℕ → ℤ))
    (hkey : ∀ d : ℕ → ℤ, d ∈ carrier →
      keyOf (πst d) = (d 0, carry P₀ Q d))
    (hsub : ∀ a ∈ S, Ω_ a ⊆ carrier)
    (hfib : ∀ a ∈ S, ∀ ω ∈ Ω_ a, Λ ω = a)
    (hcell : ∀ a ∈ S, Mtot a ≤ (Ω_ a).card)
    (hmaps : ∀ d ∈ carrier, πst d ∈ (Finset.Ico X (2 * X)) ×ˢ Ij) :
    ∑ a ∈ S, Mtot a ≤ X * Ij.card := by
  classical
  exact o2_ambient_support_summed_constructed S Ω_ Λ Mtot carrier Ij πst X
    hsub hfib hcell hmaps (piSt_injOn_via_carry_on P₀ Q hQ πst keyOf carrier hkey)

/-! ===========================================================================
    ## Section F.  Packaged O2 residual surface.

    The previous theorem proves all algebraic/cardinality steps after the genuine
    O2 construction supplies the carry refinement, cell fibres, cell weights, and
    shell membership.  This structure names exactly those residual inputs so the
    TeX--Lean map can distinguish proved O2 mechanics from the still-external
    geometric construction of the selected recurrent cells.
    =========================================================================== -/

/-- Residual O2 supply inputs after the rectangle count and carry-faithfulness
    arguments have been discharged. -/
structure O2SupplyInputs (P₀ Q : ℤ) {β A : Type*}
    (S : Finset A) (Omega : A → Finset (ℕ → ℤ)) (Lambda : (ℕ → ℤ) → A)
    (Mtot : A → ℕ) (carrier : Finset (ℕ → ℤ)) (Ij : Finset β) (X : ℕ)
    (piSt : (ℕ → ℤ) → ℕ × β) (keyOf : ℕ × β → ℤ × (ℕ → ℤ)) where
  hQ : Q ≠ 0
  hkey : ∀ d : ℕ → ℤ, d ∈ carrier → keyOf (piSt d) = (d 0, carry P₀ Q d)
  hsub : ∀ a ∈ S, Omega a ⊆ carrier
  hfib : ∀ a ∈ S, ∀ omega ∈ Omega a, Lambda omega = a
  hcell : ∀ a ∈ S, Mtot a ≤ (Omega a).card
  hmaps : ∀ d ∈ carrier, piSt d ∈ (Finset.Ico X (2 * X)) ×ˢ Ij

namespace O2SupplyInputs

/-- A global AK.2 transcript refinement is a special case of the carrier-local
    O2 supply surface.  This keeps the sharper local package while preserving a
    direct entry point for TeX statements phrased as "the start/threshold pair
    determines the carry transcript" for every digit row. -/
def ofGlobalKey (P₀ Q : ℤ) {β A : Type*}
    (S : Finset A) (Omega : A → Finset (ℕ → ℤ)) (Lambda : (ℕ → ℤ) → A)
    (Mtot : A → ℕ) (carrier : Finset (ℕ → ℤ)) (Ij : Finset β) (X : ℕ)
    (piSt : (ℕ → ℤ) → ℕ × β) (keyOf : ℕ × β → ℤ × (ℕ → ℤ))
    (hQ : Q ≠ 0)
    (hkey : ∀ d : ℕ → ℤ, keyOf (piSt d) = (d 0, carry P₀ Q d))
    (hsub : ∀ a ∈ S, Omega a ⊆ carrier)
    (hfib : ∀ a ∈ S, ∀ omega ∈ Omega a, Lambda omega = a)
    (hcell : ∀ a ∈ S, Mtot a ≤ (Omega a).card)
    (hmaps : ∀ d ∈ carrier, piSt d ∈ (Finset.Ico X (2 * X)) ×ˢ Ij) :
    O2SupplyInputs P₀ Q S Omega Lambda Mtot carrier Ij X piSt keyOf where
  hQ := hQ
  hkey := fun d _hd => hkey d
  hsub := hsub
  hfib := hfib
  hcell := hcell
  hmaps := hmaps

/-- Packaged O2 capstone: the residual construction inputs imply the summed
    ambient support bound of Appendix AK/AD. -/
theorem capstone (P₀ Q : ℤ) {β A : Type*}
    (S : Finset A) (Omega : A → Finset (ℕ → ℤ)) (Lambda : (ℕ → ℤ) → A)
    (Mtot : A → ℕ) (carrier : Finset (ℕ → ℤ)) (Ij : Finset β) (X : ℕ)
    (piSt : (ℕ → ℤ) → ℕ × β) (keyOf : ℕ × β → ℤ × (ℕ → ℤ))
    (I : O2SupplyInputs P₀ Q S Omega Lambda Mtot carrier Ij X piSt keyOf) :
    ∑ a ∈ S, Mtot a ≤ X * Ij.card :=
  o2_supply_capstone_on P₀ Q I.hQ S Omega Lambda Mtot carrier Ij X piSt keyOf
    I.hkey I.hsub I.hfib I.hcell I.hmaps

/-- Global-key form of the packaged O2 capstone.  This is definitionally the
    existing AK capstone, routed through `O2SupplyInputs` so downstream files can
    use one residual-surface API. -/
theorem capstone_ofGlobalKey (P₀ Q : ℤ) {β A : Type*}
    (S : Finset A) (Omega : A → Finset (ℕ → ℤ)) (Lambda : (ℕ → ℤ) → A)
    (Mtot : A → ℕ) (carrier : Finset (ℕ → ℤ)) (Ij : Finset β) (X : ℕ)
    (piSt : (ℕ → ℤ) → ℕ × β) (keyOf : ℕ × β → ℤ × (ℕ → ℤ))
    (hQ : Q ≠ 0)
    (hkey : ∀ d : ℕ → ℤ, keyOf (piSt d) = (d 0, carry P₀ Q d))
    (hsub : ∀ a ∈ S, Omega a ⊆ carrier)
    (hfib : ∀ a ∈ S, ∀ omega ∈ Omega a, Lambda omega = a)
    (hcell : ∀ a ∈ S, Mtot a ≤ (Omega a).card)
    (hmaps : ∀ d ∈ carrier, piSt d ∈ (Finset.Ico X (2 * X)) ×ˢ Ij) :
    ∑ a ∈ S, Mtot a ≤ X * Ij.card :=
  capstone P₀ Q S Omega Lambda Mtot carrier Ij X piSt keyOf
    (ofGlobalKey P₀ Q S Omega Lambda Mtot carrier Ij X piSt keyOf
      hQ hkey hsub hfib hcell hmaps)

end O2SupplyInputs

/-- Coordinate-split O2 supply surface for the AK base projection
`piSt : Omega_post -> [X,2X) x I_j`.  The previous packaged surface used one
rectangle-membership field `hmaps`; this version records the two TeX coordinate
facts separately: the start lies in the active shell and the threshold lies in
the threshold band. -/
structure O2SupplyCoordinateInputs (P0 Q : Int) {β A : Type*}
    (S : Finset A) (Omega : A -> Finset (Nat -> Int)) (Lambda : (Nat -> Int) -> A)
    (Mtot : A -> Nat) (carrier : Finset (Nat -> Int)) (Ij : Finset β) (X : Nat)
    (piSt : (Nat -> Int) -> Nat × β) (keyOf : Nat × β -> Int × (Nat -> Int)) where
  hQ : Q ≠ 0
  hkey : forall d : Nat -> Int, d ∈ carrier ->
    keyOf (piSt d) = (d 0, carry P0 Q d)
  hsub : forall a, a ∈ S -> Omega a ⊆ carrier
  hfib : forall a, a ∈ S -> forall omega, omega ∈ Omega a -> Lambda omega = a
  hcell : forall a, a ∈ S -> Mtot a ≤ (Omega a).card
  hstart : forall d, d ∈ carrier -> (piSt d).1 ∈ Finset.Ico X (2 * X)
  hthreshold : forall d, d ∈ carrier -> (piSt d).2 ∈ Ij

namespace O2SupplyCoordinateInputs

/-- Product-rectangle membership projects back to the coordinate-split O2 supply
surface. -/
def ofProductInputs (P0 Q : Int) {B A : Type*}
    (S : Finset A) (Omega : A -> Finset (Nat -> Int)) (Lambda : (Nat -> Int) -> A)
    (Mtot : A -> Nat) (carrier : Finset (Nat -> Int)) (Ij : Finset B) (X : Nat)
    (piSt : (Nat -> Int) -> Prod Nat B) (keyOf : Prod Nat B -> Prod Int (Nat -> Int))
    (I : O2SupplyInputs P0 Q S Omega Lambda Mtot carrier Ij X piSt keyOf) :
    O2SupplyCoordinateInputs P0 Q S Omega Lambda Mtot carrier Ij X piSt keyOf where
  hQ := I.hQ
  hkey := I.hkey
  hsub := I.hsub
  hfib := I.hfib
  hcell := I.hcell
  hstart := by
    intro d hd
    exact (Finset.mem_product.mp (I.hmaps d hd)).1
  hthreshold := by
    intro d hd
    exact (Finset.mem_product.mp (I.hmaps d hd)).2

/-- The coordinate-split active-shell/threshold-band facts assemble to the
product-rectangle membership used by `O2SupplyInputs`. -/
def toSupplyInputs (P0 Q : Int) {β A : Type*}
    (S : Finset A) (Omega : A -> Finset (Nat -> Int)) (Lambda : (Nat -> Int) -> A)
    (Mtot : A -> Nat) (carrier : Finset (Nat -> Int)) (Ij : Finset β) (X : Nat)
    (piSt : (Nat -> Int) -> Nat × β) (keyOf : Nat × β -> Int × (Nat -> Int))
    (I : O2SupplyCoordinateInputs P0 Q S Omega Lambda Mtot carrier Ij X piSt keyOf) :
    O2SupplyInputs P0 Q S Omega Lambda Mtot carrier Ij X piSt keyOf where
  hQ := I.hQ
  hkey := I.hkey
  hsub := I.hsub
  hfib := I.hfib
  hcell := I.hcell
  hmaps := by
    intro d hd
    exact Finset.mem_product.mpr ⟨I.hstart d hd, I.hthreshold d hd⟩

/-- Coordinate-split O2 capstone: the two projection-coordinate facts imply the
same AK/AD summed ambient support bound as the product-rectangle surface. -/
theorem capstone (P0 Q : Int) {β A : Type*}
    (S : Finset A) (Omega : A -> Finset (Nat -> Int)) (Lambda : (Nat -> Int) -> A)
    (Mtot : A -> Nat) (carrier : Finset (Nat -> Int)) (Ij : Finset β) (X : Nat)
    (piSt : (Nat -> Int) -> Nat × β) (keyOf : Nat × β -> Int × (Nat -> Int))
    (I : O2SupplyCoordinateInputs P0 Q S Omega Lambda Mtot carrier Ij X piSt keyOf) :
    ∑ a ∈ S, Mtot a ≤ X * Ij.card :=
  O2SupplyInputs.capstone P0 Q S Omega Lambda Mtot carrier Ij X piSt keyOf
    (toSupplyInputs P0 Q S Omega Lambda Mtot carrier Ij X piSt keyOf I)

/-- A global AK.2 transcript refinement is a special case of the carrier-local
coordinate-split O2 supply surface. -/
def ofGlobalKey (P0 Q : Int) {β A : Type*}
    (S : Finset A) (Omega : A -> Finset (Nat -> Int)) (Lambda : (Nat -> Int) -> A)
    (Mtot : A -> Nat) (carrier : Finset (Nat -> Int)) (Ij : Finset β) (X : Nat)
    (piSt : (Nat -> Int) -> Nat × β) (keyOf : Nat × β -> Int × (Nat -> Int))
    (hQ : Q ≠ 0)
    (hkey : forall d : Nat -> Int, keyOf (piSt d) = (d 0, carry P0 Q d))
    (hsub : forall a, a ∈ S -> Omega a ⊆ carrier)
    (hfib : forall a, a ∈ S -> forall omega, omega ∈ Omega a -> Lambda omega = a)
    (hcell : forall a, a ∈ S -> Mtot a <= (Omega a).card)
    (hstart : forall d, d ∈ carrier -> (piSt d).1 ∈ Finset.Ico X (2 * X))
    (hthreshold : forall d, d ∈ carrier -> (piSt d).2 ∈ Ij) :
    O2SupplyCoordinateInputs P0 Q S Omega Lambda Mtot carrier Ij X piSt keyOf where
  hQ := hQ
  hkey := fun d _hd => hkey d
  hsub := hsub
  hfib := hfib
  hcell := hcell
  hstart := hstart
  hthreshold := hthreshold

/-- Global-key coordinate-split O2 capstone. -/
theorem capstone_ofGlobalKey (P0 Q : Int) {β A : Type*}
    (S : Finset A) (Omega : A -> Finset (Nat -> Int)) (Lambda : (Nat -> Int) -> A)
    (Mtot : A -> Nat) (carrier : Finset (Nat -> Int)) (Ij : Finset β) (X : Nat)
    (piSt : (Nat -> Int) -> Nat × β) (keyOf : Nat × β -> Int × (Nat -> Int))
    (hQ : Q ≠ 0)
    (hkey : forall d : Nat -> Int, keyOf (piSt d) = (d 0, carry P0 Q d))
    (hsub : forall a, a ∈ S -> Omega a ⊆ carrier)
    (hfib : forall a, a ∈ S -> forall omega, omega ∈ Omega a -> Lambda omega = a)
    (hcell : forall a, a ∈ S -> Mtot a <= (Omega a).card)
    (hstart : forall d, d ∈ carrier -> (piSt d).1 ∈ Finset.Ico X (2 * X))
    (hthreshold : forall d, d ∈ carrier -> (piSt d).2 ∈ Ij) :
    ∑ a ∈ S, Mtot a <= X * Ij.card :=
  capstone P0 Q S Omega Lambda Mtot carrier Ij X piSt keyOf
    (ofGlobalKey P0 Q S Omega Lambda Mtot carrier Ij X piSt keyOf
      hQ hkey hsub hfib hcell hstart hthreshold)

end O2SupplyCoordinateInputs

/-- Machine-readable summary of O2 items now closed in Lean. -/
def o2SupplyEmbeddingClosedItems : List String :=
  [ "active-shell rectangle has cardinality X * |I_j|"
  , "start-threshold injectivity follows from carrier-local carry transcript faithfulness"
  , "base carrier mass is bounded by the constructed rectangle"
  , "deleted collar is isolated as an additive finite remainder"
  , "deleted-collar additive bound is packaged with carrier-local carry faithfulness"
  , "summed ambient support bound with one deleted-collar finite remainder"
  , "finite collar-size estimates transfer the carrier and summed bounds to an explicit error E"
  , "summed ambient support bound with constructed rectangle"
  , "packaged O2 capstone from residual construction inputs"
  , "global carry-transcript key packages into the carrier-local O2 surface"
  , "global carry-transcript key packages into deleted-collar O2 surfaces"
  , "coordinate-split start/threshold membership packages into the O2 surface"
  , "coordinate-split start/threshold membership packages into deleted-collar O2 surfaces"
  , "product-rectangle O2 surfaces project back to coordinate-split surfaces"
  , "coordinate-split global-key packages give direct O2 capstones and collar bounds"
  ]

/-- Machine-readable summary of O2 inputs still external to this file. -/
def o2SupplyEmbeddingOpenItems : List String :=
  [ "actual start-threshold pair determines the carry transcript"
  , "post-collar starts lie in the active shell and thresholds lie in the band I_j"
  , "selected recurrent-cell fibres and per-cell supply weights"
  , "asymptotic little-o estimate for the deleted collar"
  ]

theorem o2SupplyEmbeddingClosedItems_length :
    o2SupplyEmbeddingClosedItems.length = 15 := by
  rfl

theorem o2SupplyEmbeddingOpenItems_length :
    o2SupplyEmbeddingOpenItems.length = 4 := by
  rfl

end Erdos260.O2SupplyEmbedding
