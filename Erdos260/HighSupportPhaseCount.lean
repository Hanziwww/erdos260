/-
  Erdős #260 — checkable combinatorial CORE of the high-support cycle
  phase-count bound (the "P0.1" incomplete-lap boundary lever for O1,
  manuscript v70/v71).

  Manuscript reference
  --------------------
  `proof_v4_repaired_core_v71_p2_preprint_hygiene.tex`,
  Appendix I, Lemma "High-support bound for recurrent cycle phases"
  (`\label{lem:i-high-support-cycle-phase-count}`, line 3842), equation (I.2a)
  (line 3849):

      ∑_{λ ∈ P_i} c_λ ≤ C_Q · X / R     (= O_Q(X^{1/2-ρ})).

  Here `c_λ` is the number of phases of the selected recurrent cycle `λ`, `X`
  is the active-shell window size (number of possible source starts, `O_Q(X)`),
  and `R = X^{1/2+ρ}` is the high-support threshold (each selected recurrent
  phase owns at least `R` realized source starts).

  Combinatorial essence of the proof (lines 3862–3873): each selected phase owns
  `≥ R` *disjoint* realized source starts inside an ambient set of size `≤ X`
  ("distinct recurrent phase records are disjoint on the post-priority event
  carrier"; "the active shell contains O_Q(X) possible source starts"); hence the
  number of phases — i.e. `∑_λ c_λ` — is at most `X / R`.  This is an AGGREGATE
  (disjoint-packing) bound, *not* a pointwise per-cycle length bound: cf. App AL
  (`lem:al-incomplete-lap`, used at lines 11700–11704, `∑_λ c_λ ≤ X/R`) and
  App AQ (`prop:aq-ap1-closed`, lines 12396–12397, "uses the high-support
  phase-count bound ... not a pointwise cycle-length bound").

  This file formalizes that combinatorial core as self-contained `Finset ℕ`
  packing lemmas: finitely many pairwise-disjoint blocks inside `Finset.range X`,
  each of size `≥ R`, can number at most `X / R`, and the sum of any per-block
  weights bounded by the block sizes is at most `X`.
-/
import Mathlib

namespace Erdos260.HighSupportPhaseCount

open Finset

variable {ι κ : Type*}

/-! ### Aggregate disjoint-packing core

The single mathematical fact underlying (I.2a): pairwise-disjoint blocks sitting
inside a common ground set have total size bounded by the ground set's size. -/

/-- **Disjoint packing, general ground set.**  If `S`-many finsets `B i` are
pairwise disjoint and each contained in a common ground finset `U`, their sizes
sum to at most `|U|`.  (The `B i` model the per-phase realized source-start
supports of the manuscript; `U` is the ambient event carrier.) -/
theorem sum_card_le_of_pairwiseDisjoint_ground
    (S : Finset ι) (B : ι → Finset ℕ) (U : Finset ℕ)
    (hsub : ∀ i ∈ S, B i ⊆ U)
    (hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (B i) (B j)) :
    ∑ i ∈ S, (B i).card ≤ U.card := by
  rw [← Finset.card_biUnion hdisj]
  exact Finset.card_le_card (Finset.biUnion_subset.2 hsub)

/-- **Disjoint packing inside a window `range X`.**  The aggregate
`∑ |B i| ≤ X` form of the bound: pairwise-disjoint blocks inside `Finset.range X`
have total size at most `X`. -/
theorem sum_card_le_of_pairwiseDisjoint_range
    (S : Finset ι) (B : ι → Finset ℕ) (X : ℕ)
    (hsub : ∀ i ∈ S, B i ⊆ Finset.range X)
    (hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (B i) (B j)) :
    ∑ i ∈ S, (B i).card ≤ X := by
  have h := sum_card_le_of_pairwiseDisjoint_ground S B (Finset.range X) hsub hdisj
  rwa [Finset.card_range] at h

/-- **Same statement with `Set.PairwiseDisjoint`** (the idiomatic spelling of
"pairwise disjoint"). -/
theorem sum_card_le_of_setPairwiseDisjoint_range
    (S : Finset ι) (B : ι → Finset ℕ) (X : ℕ)
    (hsub : ∀ i ∈ S, B i ⊆ Finset.range X)
    (hdisj : (↑S : Set ι).PairwiseDisjoint B) :
    ∑ i ∈ S, (B i).card ≤ X :=
  sum_card_le_of_pairwiseDisjoint_range S B X hsub
    (fun i hi j hj hij => by
      have h := hdisj (Finset.mem_coe.2 hi) (Finset.mem_coe.2 hj) hij
      simpa [Function.onFun] using h)

/-! ### Weighted aggregate form: `∑ c_λ ≤ X`

Target statement: `∑_{λ ∈ S} c_λ ≤ X` when the cycles occupy disjoint subsets of
`range X` with `c_λ ≤ |subset_λ|`.  This is the aggregate boundary contribution
*before* dividing by the high-support threshold `R`. -/

/-- **Weighted disjoint packing.**  If each cycle `λ ∈ S` carries a weight
`c λ ≤ |B λ|` and the `B λ` are pairwise disjoint inside `range X`, then
`∑ c λ ≤ X`. -/
theorem sum_weight_le_of_pairwiseDisjoint_range
    (S : Finset ι) (B : ι → Finset ℕ) (c : ι → ℕ) (X : ℕ)
    (hsub : ∀ i ∈ S, B i ⊆ Finset.range X)
    (hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (B i) (B j))
    (hc : ∀ i ∈ S, c i ≤ (B i).card) :
    ∑ i ∈ S, c i ≤ X :=
  le_trans (Finset.sum_le_sum hc)
    (sum_card_le_of_pairwiseDisjoint_range S B X hsub hdisj)

/-! ### Phase-count form: `#cycles ≤ X / R`

Target statement: if each retained cycle has length `≥ R` and the cycles are
disjoint in `range X`, then `(#cycles) ≤ X / R`.  Proved via the disjoint-card
bound `(#cycles)·R ≤ X` and `Nat.le_div_iff_mul_le`. -/

/-- **Packing count, multiplicative form.**  If `S`-many pairwise-disjoint blocks
inside `range X` each have size `≥ R`, then `(#S)·R ≤ X`. -/
theorem card_mul_le_of_pairwiseDisjoint_range
    (S : Finset ι) (B : ι → Finset ℕ) (X R : ℕ)
    (hsub : ∀ i ∈ S, B i ⊆ Finset.range X)
    (hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (B i) (B j))
    (hR : ∀ i ∈ S, R ≤ (B i).card) :
    S.card * R ≤ X := by
  have hconst : ∑ i ∈ S, R = S.card * R := by
    simp [Finset.sum_const]
  have h1 : ∑ i ∈ S, R ≤ ∑ i ∈ S, (B i).card := Finset.sum_le_sum hR
  have h2 : ∑ i ∈ S, (B i).card ≤ X :=
    sum_card_le_of_pairwiseDisjoint_range S B X hsub hdisj
  rw [hconst] at h1
  exact le_trans h1 h2

/-- **Phase-count bound (I.2a, count form).**  If `R ≥ 1` and `S`-many
pairwise-disjoint blocks inside `range X` each have size `≥ R`, then the number
of blocks satisfies `#S ≤ X / R`.  With `B λ` = the realized source-start support
of cycle `λ` and `R` the high-support threshold, this is the manuscript's
"number of selected realized high phases is at most `C_Q X / R`". -/
theorem card_le_div_of_pairwiseDisjoint_range
    (S : Finset ι) (B : ι → Finset ℕ) (X R : ℕ) (hR1 : 0 < R)
    (hsub : ∀ i ∈ S, B i ⊆ Finset.range X)
    (hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (B i) (B j))
    (hR : ∀ i ∈ S, R ≤ (B i).card) :
    S.card ≤ X / R := by
  rw [Nat.le_div_iff_mul_le hR1]
  exact card_mul_le_of_pairwiseDisjoint_range S B X R hsub hdisj hR

/-! ### Manuscript form (I.2a): `∑_{λ ∈ S} c_λ ≤ X / R`

The exposure-weighted incomplete-lap boundary corollary in the manuscript
normalization `C_Q = 1`.  Each cycle `λ` occupies a region `seg λ ⊆ range X`, the
regions are pairwise disjoint, and the `c λ` phases of cycle `λ` each own `≥ R`
disjoint source starts within `seg λ` — encoded as `c λ · R ≤ |seg λ|`.  Then
`∑_λ c_λ ≤ X / R`. -/

/-- **Manuscript (I.2a).**  `∑_{λ ∈ S} c λ ≤ X / R` under disjoint per-cycle
regions `seg λ ⊆ range X` with `c λ · R ≤ |seg λ|`. -/
theorem sum_phasecount_le_div
    (S : Finset ι) (seg : ι → Finset ℕ) (c : ι → ℕ) (X R : ℕ) (hR1 : 0 < R)
    (hsub : ∀ i ∈ S, seg i ⊆ Finset.range X)
    (hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (seg i) (seg j))
    (hcR : ∀ i ∈ S, c i * R ≤ (seg i).card) :
    ∑ i ∈ S, c i ≤ X / R := by
  rw [Nat.le_div_iff_mul_le hR1, Finset.sum_mul]
  calc ∑ i ∈ S, c i * R ≤ ∑ i ∈ S, (seg i).card := Finset.sum_le_sum hcR
    _ ≤ X := sum_card_le_of_pairwiseDisjoint_range S seg X hsub hdisj

/-- **Manuscript (I.2a), fully unpacked.**  Phases are genuinely double-indexed by
`(cycle, phase)`: cycle `i ∈ S` has phase set `P i`, each phase `(i, p)` owns a
support `B i p ⊆ range X` of size `≥ R`, and *all* phase supports (across cycles
and phases) are pairwise disjoint.  Then the total phase count
`∑_{i ∈ S} |P i| = ∑_λ c_λ` is at most `X / R`. -/
theorem sum_phasecount_le_div_of_phases
    (S : Finset ι) (P : ι → Finset κ) (B : ι → κ → Finset ℕ)
    (X R : ℕ) (hR1 : 0 < R)
    (hsub : ∀ i ∈ S, ∀ p ∈ P i, B i p ⊆ Finset.range X)
    (hdisj : ∀ q ∈ S.sigma P, ∀ q' ∈ S.sigma P, q ≠ q' →
        Disjoint (B q.1 q.2) (B q'.1 q'.2))
    (hR : ∀ i ∈ S, ∀ p ∈ P i, R ≤ (B i p).card) :
    ∑ i ∈ S, (P i).card ≤ X / R := by
  have key := card_le_div_of_pairwiseDisjoint_range (S.sigma P)
      (fun q => B q.1 q.2) X R hR1
      (by
        intro q hq
        rw [Finset.mem_sigma] at hq
        exact hsub q.1 hq.1 q.2 hq.2)
      hdisj
      (by
        intro q hq
        rw [Finset.mem_sigma] at hq
        exact hR q.1 hq.1 q.2 hq.2)
  rwa [Finset.card_sigma] at key

end Erdos260.HighSupportPhaseCount
