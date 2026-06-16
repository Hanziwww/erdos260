import Mathlib
import Erdos260.CarryFaithfulIndexing
import Erdos260.HighSupportPhaseCount
import Erdos260.P1HotspotAudit

/-!
# O2 ambient phase-mass bound: the falsifiable injection/packing core (RISK b)

This module formalizes the **checkable arithmetic hearts** of the Erdős-#260
*ambient phase-mass support bound* `M_tot ≤ X·|I_j|` (the former obligation
`(O2)`, RISK b) of `proof_v4_repaired_core_v71_p2_preprint_hygiene.tex`:

* App AB, **`lem:ab-ambient-support-bound`** (AB.3, line 10773): the phase slices
  `Ω_a = {ω ∈ Ω_cyc : phase ω = a}` are disjoint with union `Ω_cyc`, so
  `M_tot = Σ_a Mass(Ω_a) = Mass(Ω_cyc)`; forgetting the recurrent-cycle
  certificate injects `Ω_cyc` into the start/threshold event set "because the
  phase is determined by the same endpoint/carry transcript".
* App AD, **`lem:ad-summed-ambient-support`** (AD.2, line 11261):
  `Σ_{λ∈P_i} M_tot(λ) ≤ X|I_j| + o(X|I_j|)`; the cells are the fibres of the
  canonical selected recurrent-cell map, hence disjoint, and the forgetful map to
  the start/threshold carrier is injective on their disjoint union.
* App AK, **`lem:ak-faithful-start-threshold-indexing`** (line 11408),
  **`lem:ak-selected-cells-disjoint`** (line 11470),
  **`lem:ak-ambient-support-sum`** (AK.3, line 11489),
  **`lem:ak-base-carrier-mass-bound`** (AK.1, line 11426).

The single genuinely analytic/geometric input — that the start/threshold rectangle
has size `X·|I_j|` and that the post-collar carrier injects into it — is abstracted
into **explicit hypotheses** (`hrect`, `hmaps`, `hinj`).  Everything else (the
disjoint-packing aggregation and the disjointness-from-faithfulness bridge) is
proved `sorry`-free here.

The load-bearing *faithfulness* claim ("the phase is determined by the carry
transcript") is **not re-assumed**: it is imported as
`Erdos260.CarryFaithfulIndexing.o2_carry_transcript_injective` and turned, in
`phase_factors_through_transcript`, into the statement that any phase assignment on
digit sequences factors through the carry transcript.  This is what *guarantees*
the disjointness used by the packing bound, exactly as the manuscript asserts.

Reused, sorry-free, imported lemmas:
* `Erdos260.CarryFaithfulIndexing.o2_carry_transcript_injective` — forgetful map
  `d ↦ (d 0, carry P₀ Q d)` injective (`Q ≠ 0`);
* `Erdos260.CarryRecurrence21.carry` — the §21.1 carry transcript;
* `Erdos260.HighSupportPhaseCount.sum_card_le_of_pairwiseDisjoint_range` — disjoint
  packing inside the literal source-start window;
* `Erdos260.P1HotspotAudit.o2_faithful_mass_bound` — injection into a finite
  rectangle bounds carrier card.
-/

namespace Erdos260.O2AmbientInjection

open Erdos260.CarryRecurrence21
open Erdos260.CarryFaithfulIndexing

/-! ## Hotspot 2. Forgetful-injectivity ⇒ disjointness bridge

`lem:ak-selected-cells-disjoint` (line 11470): the recurrent cells are the fibres
`F_λ = Λ⁻¹(λ)` of one deterministic label function `Λ`.  Distinct fibres of a
function are disjoint, and the forgetful map from their disjoint union to the
underlying carrier is injective.  This is the precise combinatorial form of "phase
determined by the endpoint/carry transcript ⇒ cells genuinely disjoint". -/

/-- **Distinct phase slices are disjoint.**  If every element of a slice `Ω_ a`
carries label `a` under a single label function `lbl` (the slices are *fibre-like*
for `lbl`), then slices with different labels are disjoint.  No metric/geometric
input is used: this is the disjointness the manuscript derives from faithful
indexing. -/
theorem slices_disjoint_of_label_coherent
    {Ω A : Type*} (S : Finset A) (Ω_ : A → Finset Ω) (lbl : Ω → A)
    (hcoh : ∀ a ∈ S, ∀ ω ∈ Ω_ a, lbl ω = a) :
    ∀ a ∈ S, ∀ a' ∈ S, a ≠ a' → Disjoint (Ω_ a) (Ω_ a') := by
  intro a ha a' ha' hne
  rw [Finset.disjoint_left]
  intro ω hω hω'
  exact hne ((hcoh a ha ω hω).symm.trans (hcoh a' ha' ω hω'))

/-- **Forgetful map injective on the disjoint union** (`lem:ak-selected-cells-disjoint`,
sigma form).  The map `⟨a, ω⟩ ↦ ω` from `⊔_{a∈S} Ω_ a` to the underlying carrier is
injective: two records that forget to the same event state `ω` have the same label
`lbl ω`, hence are the same point of the same fibre. -/
theorem forgetful_sigma_injOn
    {Ω A : Type*} (S : Finset A) (Ω_ : A → Finset Ω) (lbl : Ω → A)
    (hcoh : ∀ a ∈ S, ∀ ω ∈ Ω_ a, lbl ω = a) :
    Set.InjOn (fun p : (_ : A) × Ω => p.2) (↑(S.sigma Ω_)) := by
  rintro ⟨a, ω⟩ hp ⟨a', ω'⟩ hq hpq
  rw [Finset.mem_coe, Finset.mem_sigma] at hp hq
  obtain ⟨ha, hω⟩ := hp
  obtain ⟨ha', hω'⟩ := hq
  have hωω : ω = ω' := hpq
  subst hωω
  have haa : a = a' := (hcoh a ha ω hω).symm.trans (hcoh a' ha' ω hω')
  subst haa
  rfl

/-- **Cardinality form of "forgetful injective on disjoint union".**  The size of
the union of fibre-like slices is the sum of their sizes — i.e. no element is
double-counted across phases. -/
theorem card_biUnion_slices
    {Ω A : Type*} [DecidableEq Ω] (S : Finset A) (Ω_ : A → Finset Ω) (lbl : Ω → A)
    (hcoh : ∀ a ∈ S, ∀ ω ∈ Ω_ a, lbl ω = a) :
    (S.biUnion Ω_).card = ∑ a ∈ S, (Ω_ a).card :=
  Finset.card_biUnion (slices_disjoint_of_label_coherent S Ω_ lbl hcoh)

/-! ## Hotspot 1. Disjoint phase-slice injection ⇒ ambient bound

The core falsifiable step (`lem:ak-ambient-support-sum`, AK.3 / `lem:ad-summed-ambient-support`,
AD.2 / `lem:ab-ambient-support-bound`, AB.3): pairwise-disjoint slices `Ω_ a` inside
the ambient start/threshold carrier `U` with `|U| ≤ X·|I_j|` have total mass
`M_tot = Σ_a |Ω_ a| ≤ |U| ≤ X·|I_j|`. -/

/-- **Disjoint packing, general ambient carrier.**  Pairwise-disjoint slices, each
contained in a common ground finset `U`, have total card `≤ |U|`.  (Generic-`Ω`
twin of `HighSupportPhaseCount.sum_card_le_of_pairwiseDisjoint_ground`, needed
because the ambient carrier of transcripts/event states is not `ℕ`.) -/
theorem sum_card_le_of_disjoint_ground
    {Ω A : Type*} [DecidableEq Ω]
    (S : Finset A) (Ω_ : A → Finset Ω) (U : Finset Ω)
    (hsub : ∀ a ∈ S, Ω_ a ⊆ U)
    (hdisj : ∀ a ∈ S, ∀ a' ∈ S, a ≠ a' → Disjoint (Ω_ a) (Ω_ a')) :
    ∑ a ∈ S, (Ω_ a).card ≤ U.card := by
  rw [← Finset.card_biUnion hdisj]
  exact Finset.card_le_card (Finset.biUnion_subset.2 hsub)

/-- **Ambient phase-mass bound from disjointness** (AB.3 / AD.2 / AK.3).  Disjoint
slices inside `U` with `|U| ≤ X·|I_j|` give `M_tot = Σ_a |Ω_ a| ≤ X·|I_j|`. -/
theorem ambient_mass_le_of_disjoint_slices
    {Ω A : Type*} [DecidableEq Ω]
    (S : Finset A) (Ω_ : A → Finset Ω) (U : Finset Ω) (X cardIj : ℕ)
    (hsub : ∀ a ∈ S, Ω_ a ⊆ U)
    (hdisj : ∀ a ∈ S, ∀ a' ∈ S, a ≠ a' → Disjoint (Ω_ a) (Ω_ a'))
    (hU : U.card ≤ X * cardIj) :
    ∑ a ∈ S, (Ω_ a).card ≤ X * cardIj :=
  le_trans (sum_card_le_of_disjoint_ground S Ω_ U hsub hdisj) hU

/-- **Ambient phase-mass bound, disjointness supplied by faithful indexing.**  Here
the disjointness — the load-bearing claim — is *not assumed*; it is derived from the
slices being fibre-like for a label function `lbl` (the phase reader).  This is the
precise statement "phase determined by the transcript ⇒ slices disjoint ⇒
`M_tot ≤ X·|I_j|`". -/
theorem ambient_mass_le_of_label_coherent
    {Ω A : Type*} [DecidableEq Ω]
    (S : Finset A) (Ω_ : A → Finset Ω) (lbl : Ω → A) (U : Finset Ω) (X cardIj : ℕ)
    (hsub : ∀ a ∈ S, Ω_ a ⊆ U)
    (hcoh : ∀ a ∈ S, ∀ ω ∈ Ω_ a, lbl ω = a)
    (hU : U.card ≤ X * cardIj) :
    ∑ a ∈ S, (Ω_ a).card ≤ X * cardIj :=
  ambient_mass_le_of_disjoint_slices S Ω_ U X cardIj hsub
    (slices_disjoint_of_label_coherent S Ω_ lbl hcoh) hU

/-- **Reuse of the `range X` shell packing** (`HighSupportPhaseCount`).  When the
ambient carrier is the literal source-start window `Finset.range (X·|I_j|)`, the
bound is exactly `sum_card_le_of_pairwiseDisjoint_range`. -/
theorem ambient_mass_le_shell
    {A : Type*} (S : Finset A) (Ω_ : A → Finset ℕ) (X cardIj : ℕ)
    (hsub : ∀ a ∈ S, Ω_ a ⊆ Finset.range (X * cardIj))
    (hdisj : ∀ a ∈ S, ∀ a' ∈ S, a ≠ a' → Disjoint (Ω_ a) (Ω_ a')) :
    ∑ a ∈ S, (Ω_ a).card ≤ X * cardIj :=
  HighSupportPhaseCount.sum_card_le_of_pairwiseDisjoint_range S Ω_ (X * cardIj) hsub hdisj

/-! ## Hotspot 3. Per-cell ambient support bound (AB.3, summed form)

`lem:ab-ambient-support-bound` / `lem:ad-summed-ambient-support`: each cell `λ`
carries ambient phase mass `M_tot(λ)` bounded by the geometric cell size
`|Ω_ λ|` (the genuine per-cell *geometric supply*, taken as a hypothesis), and the
disjoint cells aggregate to `Σ_λ M_tot(λ) ≤ X·|I_j|`. -/

/-- **Weighted ambient support sum (AB.3, summed).**  Per-cell ambient mass
`M_tot a ≤ |Ω_ a|` (geometric supply) over disjoint fibre-like slices in `U`,
`|U| ≤ X·|I_j|`, aggregates to `Σ_a M_tot a ≤ X·|I_j|`. -/
theorem ambient_mass_le_weighted
    {Ω A : Type*} [DecidableEq Ω]
    (S : Finset A) (Ω_ : A → Finset Ω) (lbl : Ω → A) (Mtot : A → ℕ)
    (U : Finset Ω) (X cardIj : ℕ)
    (hsub : ∀ a ∈ S, Ω_ a ⊆ U)
    (hcoh : ∀ a ∈ S, ∀ ω ∈ Ω_ a, lbl ω = a)
    (hcell : ∀ a ∈ S, Mtot a ≤ (Ω_ a).card)
    (hU : U.card ≤ X * cardIj) :
    ∑ a ∈ S, Mtot a ≤ X * cardIj :=
  le_trans (Finset.sum_le_sum hcell)
    (ambient_mass_le_of_label_coherent S Ω_ lbl U X cardIj hsub hcoh hU)

/-- **Base carrier mass bound (AK.1, `lem:ak-base-carrier-mass-bound`).**  Reuses
`P1HotspotAudit.o2_faithful_mass_bound`: the faithful start/threshold projection
`π_st` injective on the post-collar carrier sends it into the rectangle
`[X,2X)×I_j` of card `≤ X·|I_j|`, so `|Ω_post| ≤ X·|I_j|`. -/
theorem base_carrier_mass_bound
    {Ω β : Type*} (carrier : Finset Ω) (rect : Finset β) (πst : Ω → β) (X cardIj : ℕ)
    (hmaps : ∀ ω ∈ carrier, πst ω ∈ rect)
    (hinj : Set.InjOn πst carrier)
    (hrect : rect.card ≤ X * cardIj) :
    carrier.card ≤ X * cardIj :=
  le_trans (Erdos260.P1HotspotAudit.o2_faithful_mass_bound carrier rect πst hmaps hinj) hrect

/-- **Full App AK chain (`prop:ak-former-o2-discharged`).**  Combining faithful
start/threshold indexing (`hmaps`, `hinj` ⇒ base-carrier bound, AK.1), selected-cell
disjointness (fibre-coherence `hfib` of the canonical recurrent-cell map `Λ`,
AK.2/`lem:ak-selected-cells-disjoint`), and the per-cell geometric supply
(`hcell`), the summed ambient support is bounded:
`Σ_{λ∈S} M_tot(λ) ≤ X·|I_j|` (AK.3 / AD.2 / AB.3, dropping the `o(X|I_j|)` collar
remainder which is the abstracted analytic input). -/
theorem o2_ambient_support_summed
    {Ω β A : Type*} [DecidableEq Ω]
    (S : Finset A) (Ω_ : A → Finset Ω) (Λ : Ω → A) (Mtot : A → ℕ)
    (carrier : Finset Ω) (rect : Finset β) (πst : Ω → β) (X cardIj : ℕ)
    (hsub : ∀ a ∈ S, Ω_ a ⊆ carrier)
    (hfib : ∀ a ∈ S, ∀ ω ∈ Ω_ a, Λ ω = a)
    (hcell : ∀ a ∈ S, Mtot a ≤ (Ω_ a).card)
    (hmaps : ∀ ω ∈ carrier, πst ω ∈ rect)
    (hinj : Set.InjOn πst carrier)
    (hrect : rect.card ≤ X * cardIj) :
    ∑ a ∈ S, Mtot a ≤ X * cardIj :=
  ambient_mass_le_weighted S Ω_ Λ Mtot carrier X cardIj hsub hfib hcell
    (base_carrier_mass_bound carrier rect πst X cardIj hmaps hinj hrect)

/-! ## Hotspot 2, genuine wiring. Carry transcript determines the phase

`lem:ak-faithful-start-threshold-indexing` (line 11408): "the carry recurrence
determines the carry states ... the endpoint quotient, carry quotient, side label,
and threshold layer are fixed functions of these carries and of `(x,T)`."  Here we
turn the imported injectivity `o2_carry_transcript_injective` into exactly this: any
phase assignment on digit sequences factors through the carry transcript, hence the
phase-reading label function used above is genuinely a function of the underlying
event row.  This is what *justifies* the fibre-coherence hypotheses, so the
disjointness is supplied by faithfulness rather than assumed. -/

/-- **Phase is a function of the carry transcript.**  Since the forgetful map
`d ↦ (d 0, carry P₀ Q d)` is injective for `Q ≠ 0`
(`o2_carry_transcript_injective`), any phase assignment `phase : (ℕ → ℤ) → A`
factors through the transcript: there is `ph` with
`phase d = ph (d 0, carry P₀ Q d)`.  Machine-checked form of "the phase is
determined by the endpoint/carry transcript". -/
theorem phase_factors_through_transcript
    (P₀ Q : ℤ) (hQ : Q ≠ 0) {A : Type*} (phase : (ℕ → ℤ) → A) :
    ∃ ph : ℤ × (ℕ → ℤ) → A, ∀ d : ℕ → ℤ, phase d = ph (d 0, carry P₀ Q d) := by
  classical
  haveI : Nonempty (ℕ → ℤ) := ⟨fun _ => 0⟩
  have hinj : Function.Injective (fun d : ℕ → ℤ => (d 0, carry P₀ Q d)) :=
    o2_carry_transcript_injective P₀ Q hQ
  refine ⟨fun t => phase (Function.invFun (fun d : ℕ → ℤ => (d 0, carry P₀ Q d)) t),
    fun d => ?_⟩
  have hli : Function.invFun (fun d : ℕ → ℤ => (d 0, carry P₀ Q d)) (d 0, carry P₀ Q d) = d :=
    Function.leftInverse_invFun hinj d
  show phase d
      = phase (Function.invFun (fun d : ℕ → ℤ => (d 0, carry P₀ Q d)) (d 0, carry P₀ Q d))
  rw [hli]

/-- **Ambient phase-mass bound, disjointness from carry faithfulness (end-to-end).**
The genuine combination: the user supplies only the *geometric realness* of each
slice — every transcript in slice `a` is the transcript of some digit sequence whose
phase is `a` (`hreal`) — plus the rectangle bound `|U| ≤ X·|I_j|`.  Disjointness is
*derived*: `phase_factors_through_transcript` (hence `o2_carry_transcript_injective`)
makes the phase a function `ph` of the transcript, the slices are `ph`-coherent, so
they are pairwise disjoint and pack into `U`.  Conclusion: `Σ_a |Ω_ a| ≤ X·|I_j|`
(`M_tot ≤ X·|I_j|`, AB.3). -/
theorem o2_ambient_bound_via_phase
    (P₀ Q : ℤ) (hQ : Q ≠ 0) {A : Type*}
    (phase : (ℕ → ℤ) → A)
    (S : Finset A) (Ω_ : A → Finset (ℤ × (ℕ → ℤ))) (U : Finset (ℤ × (ℕ → ℤ)))
    (X cardIj : ℕ)
    (hsub : ∀ a ∈ S, Ω_ a ⊆ U)
    (hreal : ∀ a ∈ S, ∀ t ∈ Ω_ a, ∃ d : ℕ → ℤ, t = (d 0, carry P₀ Q d) ∧ phase d = a)
    (hU : U.card ≤ X * cardIj) :
    ∑ a ∈ S, (Ω_ a).card ≤ X * cardIj := by
  classical
  obtain ⟨ph, hph⟩ := phase_factors_through_transcript P₀ Q hQ phase
  refine ambient_mass_le_of_label_coherent S Ω_ ph U X cardIj hsub ?_ hU
  intro a ha t ht
  obtain ⟨d, rfl, hd⟩ := hreal a ha t ht
  rw [← hph d]
  exact hd

end Erdos260.O2AmbientInjection
