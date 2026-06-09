import Mathlib
import Erdos260.AppendixG_CNL
import Erdos260.AppendixG_Ladder
import Erdos260.AppendixL
import Erdos260.CarryDataFactory

/-!
# Appendix K.3 / L.1 CNL encoding interface

`CNL.lean` proves the finite priority-scan skeleton.  `AppendixG_CNL.lean`
defines `CNLEntropyData`, whose essential mathematical field is the Kraft
bound

`cleanCNLKraftSum paths BNDHeight c <= CQ ^ M`.

This file isolates the remaining manuscript content of K.3 and L.1 as a
cluster-encoding data structure and provides the canonical constructor into
`CNLEntropyData`.  The proof object below now derives `kraftSum_le` from the
abstract G.2/G.6 ladder bound; the remaining manuscript input is the
identification of the concrete selected-transition cluster with that ladder
Kraft sum.
The selector/normal-form obligations are kept as a separate target below; they
are not carried by the final CNL entropy package once the Kraft inequality has
been supplied.
-/

namespace Erdos260

open Finset

noncomputable section

/--
The one-step normal-form selector obligations used in L.1.1.

The first field is the already-proved deterministic skeleton.  The remaining
fields name the two manuscript-specific facts that are not present in the
skeleton: every clean visible transition must have a selected class, and the
chosen exact normal form must be coherent with the selected class.
-/
structure CNLNormalFormSelectorData where
  transitions : Finset CNLTransition
  selectorSkeleton : CNLSelectorSkeletonV2
  clean_visible :
    ∀ t ∈ transitions, t.available.Nonempty
  normalFormCoherent :
    ∀ t ∈ transitions, ∀ cls : CNLClass,
      canonicalCNLSelector t = some cls ->
        (t.normalForm = CNLNormalForm.positiveLift ∨
          t.normalForm = CNLNormalForm.childResidue)

/-- Build the K.3.0--K.3.4 selector package from clean visibility.

The deterministic selector skeleton is already closed in `CNLSelectorSkeletonV2_proved`,
and the exact-normal-form coherence is the exhaustive two-constructor split of
`CNLNormalForm`.
-/
def CNLNormalFormSelectorData.ofCleanVisible
    (transitions : Finset CNLTransition)
    (clean_visible : ∀ t ∈ transitions, t.available.Nonempty) :
    CNLNormalFormSelectorData where
  transitions := transitions
  selectorSkeleton := CNLSelectorSkeletonV2_proved
  clean_visible := clean_visible
  normalFormCoherent := by
    intro t _ht _cls _hsel
    exact CNLTransition.normalForm_exhaustive t

/-- Build the selector package on the already-selected transition family.
Clean visibility is automatic for this filtered family. -/
def CNLNormalFormSelectorData.ofSelectedTransitions
    (transitions : Finset CNLTransition) :
    CNLNormalFormSelectorData :=
  CNLNormalFormSelectorData.ofCleanVisible (selectedTransitions transitions)
    (fun _t ht => available_nonempty_of_mem_selectedTransitions ht)

theorem CNLNormalFormSelectorData.exists_selected
    (data : CNLNormalFormSelectorData) {t : CNLTransition}
    (ht : t ∈ data.transitions) :
    ∃ cls : CNLClass, canonicalCNLSelector t = some cls :=
  data.selectorSkeleton.2.1 (data.clean_visible t ht)

theorem CNLNormalFormSelectorData.selected_normalFormCoherent
    (data : CNLNormalFormSelectorData) {t : CNLTransition}
    (ht : t ∈ data.transitions) {cls : CNLClass}
    (hsel : canonicalCNLSelector t = some cls) :
    t.normalForm = CNLNormalForm.positiveLift ∨
      t.normalForm = CNLNormalForm.childResidue :=
  data.normalFormCoherent t ht cls hsel

/--
K.3.5 / L.1.1 selector classifier for every clean visible transition in the
normal-form selector package.

Clean visibility supplies the nonempty available-class set; the closed priority
scan theorem then gives a unique selected class together with membership and
priority minimality among all available classes.
-/
theorem CNLNormalFormSelectorData.transitionClassifier
    (data : CNLNormalFormSelectorData) {t : CNLTransition}
    (ht : t ∈ data.transitions) :
    ∃! cls : CNLClass,
      canonicalCNLSelector t = some cls ∧
        cls ∈ t.available ∧
        ∀ other ∈ t.available,
          CNLClass.priorityRank cls <= CNLClass.priorityRank other :=
  propositionK3_5_cnlTransitionClassifier t (data.clean_visible t ht)

/--
The Kraft-weighted cluster encoding produced by K.3/L.1.

This is the focused target for formalizing Proposition K.3.5 and Lemma L.1.2:
construct the path family, BND-height function, constants, and the weighted
Kraft inequality.
-/
structure CNLClusterEncodingData (cStar ξ X : ℝ) where
  α : Type
  paths : Finset α
  BNDHeight : α -> ℝ
  c : ℝ
  CQ : ℝ
  M : Nat
  shellFactor : ℝ
  Ij : ℝ
  shellFactor_nonneg : 0 <= shellFactor
  Ij_nonneg : 0 <= Ij
  kraftSum_le :
    cleanCNLKraftSum paths BNDHeight c <= CQ ^ M
  manuscript_bound :
    CQ ^ M * shellFactor * X * Ij <= cStar * ξ * X / 6

/--
Direct proof-v4 G.35/L.1w weighted CNL entropy certificate.

This is the manuscript-facing cluster input: the surviving clean unclassified
CNL paths, with BND heights inserted as Kraft weights, have total weighted
entropy at most `C_Q^M`; the shell-factor arithmetic then pays the CNL term in
the stopped recurrence.
-/
structure CNLWeightedEntropyData {α : Type} (paths : Finset α)
    (BNDHeight : α -> ℝ) (c CQ shellFactor X Ij cStar ξ : ℝ) (M : Nat) where
  c_pos : 0 < c
  kraftSum_le :
    cleanCNLKraftSum paths BNDHeight c <= CQ ^ M
  manuscript_bound :
    CQ ^ M * shellFactor * X * Ij <= cStar * ξ * X / 6

namespace CNLWeightedEntropyData

/-- Projection of the proof-v4 G.35/L.1w weighted entropy bound. -/
theorem kraft_bound
    {cStar ξ X : ℝ}
    {α : Type} {paths : Finset α} {BNDHeight : α -> ℝ}
    {c CQ shellFactor Ij : ℝ} {M : Nat}
    (data :
      CNLWeightedEntropyData paths BNDHeight c CQ shellFactor X Ij cStar ξ M) :
    cleanCNLKraftSum paths BNDHeight c <= CQ ^ M :=
  data.kraftSum_le

/-- Projection of the weighted CNL cluster contribution bound after shell factors. -/
theorem weighted_bound
    {cStar ξ X : ℝ}
    {α : Type} {paths : Finset α} {BNDHeight : α -> ℝ}
    {c CQ shellFactor Ij : ℝ} {M : Nat}
    (data :
      CNLWeightedEntropyData paths BNDHeight c CQ shellFactor X Ij cStar ξ M) :
    CQ ^ M * shellFactor * X * Ij <= cStar * ξ * X / 6 :=
  data.manuscript_bound

end CNLWeightedEntropyData

/-
The L.1.2 proof obligations separated from the ambient CNL cluster data.

This structure packages the Kraft and shell-factor bounds consumed by the final
CNL entropy package.  Selector/normal-form facts remain available as
`CNLNormalFormSelectorData`, but are not duplicated here.
-/
/-- L.1w/G.6 cluster Kraft certificate before shell-factor bookkeeping. -/
structure CNLClusterKraftData {α : Type} (paths : Finset α)
    (BNDHeight : α -> ℝ) (c CQ : ℝ) (M : Nat) where
  ladderChildren : Nat -> Finset Nat
  ladderHeight : Nat -> ℝ
  ladderRoot : Nat
  hc_pos : 0 < c
  hCQ_dom :
    (1 - (2 : ℝ) ^ (-c))⁻¹ <= CQ
  ladderHeight_dom :
    ∀ δ : Nat, (δ : ℝ) <= ladderHeight δ
  cluster_le_pathKraft :
    cleanCNLKraftSum paths BNDHeight c <=
      pathKraft ladderChildren
        (fun δ => (2 : ℝ) ^ (-(c * ladderHeight δ))) M ladderRoot

/-- Final shell/interval manuscript budget for the encoded CNL cluster. -/
structure CNLClusterBudgetData (CQ shellFactor X Ij cStar ξ : ℝ) (M : Nat) where
  manuscript_bound :
    CQ ^ M * shellFactor * X * Ij <= cStar * ξ * X / 6

structure CNLClusterEncodingProof {α : Type} (paths : Finset α)
    (BNDHeight : α -> ℝ) (c CQ shellFactor X Ij cStar ξ : ℝ) (M : Nat) where
  kraft :
    CNLClusterKraftData paths BNDHeight c CQ M
  budget :
    CNLClusterBudgetData CQ shellFactor X Ij cStar ξ M

/-- Project the L.1w ladder children from the Kraft certificate. -/
def CNLClusterEncodingProof.ladderChildren
    {cStar ξ X : ℝ}
    {α : Type} {paths : Finset α} {BNDHeight : α -> ℝ}
    {c CQ shellFactor Ij : ℝ} {M : Nat}
    (proof :
      CNLClusterEncodingProof paths BNDHeight c CQ shellFactor X Ij cStar ξ M) :
    Nat -> Finset Nat :=
  proof.kraft.ladderChildren

/-- Project the L.1w ladder-height function from the Kraft certificate. -/
def CNLClusterEncodingProof.ladderHeight
    {cStar ξ X : ℝ}
    {α : Type} {paths : Finset α} {BNDHeight : α -> ℝ}
    {c CQ shellFactor Ij : ℝ} {M : Nat}
    (proof :
      CNLClusterEncodingProof paths BNDHeight c CQ shellFactor X Ij cStar ξ M) :
    Nat -> ℝ :=
  proof.kraft.ladderHeight

/-- Project the L.1w ladder root from the Kraft certificate. -/
def CNLClusterEncodingProof.ladderRoot
    {cStar ξ X : ℝ}
    {α : Type} {paths : Finset α} {BNDHeight : α -> ℝ}
    {c CQ shellFactor Ij : ℝ} {M : Nat}
    (proof :
      CNLClusterEncodingProof paths BNDHeight c CQ shellFactor X Ij cStar ξ M) :
    Nat :=
  proof.kraft.ladderRoot

/-- Project positivity of the CNL entropy exponent. -/
theorem CNLClusterEncodingProof.hc_pos
    {cStar ξ X : ℝ}
    {α : Type} {paths : Finset α} {BNDHeight : α -> ℝ}
    {c CQ shellFactor Ij : ℝ} {M : Nat}
    (proof :
      CNLClusterEncodingProof paths BNDHeight c CQ shellFactor X Ij cStar ξ M) :
    0 < c :=
  proof.kraft.hc_pos

/-- Project the one-step `C_Q` domination. -/
theorem CNLClusterEncodingProof.hCQ_dom
    {cStar ξ X : ℝ}
    {α : Type} {paths : Finset α} {BNDHeight : α -> ℝ}
    {c CQ shellFactor Ij : ℝ} {M : Nat}
    (proof :
      CNLClusterEncodingProof paths BNDHeight c CQ shellFactor X Ij cStar ξ M) :
    (1 - (2 : ℝ) ^ (-c))⁻¹ <= CQ :=
  proof.kraft.hCQ_dom

/-- Project domination of each ladder height by its index. -/
theorem CNLClusterEncodingProof.ladderHeight_dom
    {cStar ξ X : ℝ}
    {α : Type} {paths : Finset α} {BNDHeight : α -> ℝ}
    {c CQ shellFactor Ij : ℝ} {M : Nat}
    (proof :
      CNLClusterEncodingProof paths BNDHeight c CQ shellFactor X Ij cStar ξ M) :
    ∀ δ : Nat, (δ : ℝ) <= proof.ladderHeight δ :=
  proof.kraft.ladderHeight_dom

/-- Project the cluster-to-path-Kraft comparison from the Kraft certificate. -/
theorem CNLClusterEncodingProof.cluster_le_pathKraft
    {cStar ξ X : ℝ}
    {α : Type} {paths : Finset α} {BNDHeight : α -> ℝ}
    {c CQ shellFactor Ij : ℝ} {M : Nat}
    (proof :
      CNLClusterEncodingProof paths BNDHeight c CQ shellFactor X Ij cStar ξ M) :
    cleanCNLKraftSum paths BNDHeight c <=
      pathKraft proof.ladderChildren
        (fun δ => (2 : ℝ) ^ (-(c * proof.ladderHeight δ))) M proof.ladderRoot :=
  proof.kraft.cluster_le_pathKraft

/-- Project the final shell/interval CNL budget. -/
theorem CNLClusterEncodingProof.manuscript_bound
    {cStar ξ X : ℝ}
    {α : Type} {paths : Finset α} {BNDHeight : α -> ℝ}
    {c CQ shellFactor Ij : ℝ} {M : Nat}
    (proof :
      CNLClusterEncodingProof paths BNDHeight c CQ shellFactor X Ij cStar ξ M) :
    CQ ^ M * shellFactor * X * Ij <= cStar * ξ * X / 6 :=
  proof.budget.manuscript_bound

/-- The CNL slope exponent is positive once the manuscript normalization has
`c >= 1`. -/
theorem CNLClusterEncodingProof.c_pos
    {cStar ξ X : ℝ}
    {α : Type} {paths : Finset α} {BNDHeight : α -> ℝ}
    {c CQ shellFactor Ij : ℝ} {M : Nat}
    (proof :
      CNLClusterEncodingProof paths BNDHeight c CQ shellFactor X Ij cStar ξ M) :
    0 < c :=
  proof.hc_pos

/-- G.6 one-step constant comparison from the standard manuscript inequalities
`c >= 1` and `C_Q >= 2`. -/
theorem cnl_cq_dominates_of_c_ge_one
    {c CQ : ℝ} (hc : 1 <= c) (hCQ : 2 <= CQ) :
    (1 - (2 : ℝ) ^ (-c))⁻¹ <= CQ := by
  have hpow : (2 : ℝ) ^ (-c) <= (1 / 2 : ℝ) := by
    calc
      (2 : ℝ) ^ (-c) <= (2 : ℝ) ^ (-1 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        linarith
      _ = (1 / 2 : ℝ) := by norm_num [Real.rpow_neg_one]
  have hden_ge : (1 / 2 : ℝ) <= 1 - (2 : ℝ) ^ (-c) := by linarith
  have hdiv : 1 / (1 - (2 : ℝ) ^ (-c)) <= 1 / (1 / 2 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hden_ge
  have hhalf : 1 / (1 / 2 : ℝ) = 2 := by norm_num
  have hdiv_two : 1 / (1 - (2 : ℝ) ^ (-c)) <= 2 := by
    simpa [hhalf] using hdiv
  simpa [one_div] using hdiv_two.trans hCQ

/-- The separated CNL proof package derives the one-step `C_Q` domination. -/
theorem CNLClusterEncodingProof.cq_dominates
    {cStar ξ X : ℝ}
    {α : Type} {paths : Finset α} {BNDHeight : α -> ℝ}
    {c CQ shellFactor Ij : ℝ} {M : Nat}
    (proof :
      CNLClusterEncodingProof paths BNDHeight c CQ shellFactor X Ij cStar ξ M) :
    (1 - (2 : ℝ) ^ (-c))⁻¹ <= CQ :=
  proof.hCQ_dom

/--
Constructor for the previous standard-normalization interface.  This keeps the
old `c >= 1`, `C_Q >= 2` route available, but the core CNL proof object now
only stores the weaker G.35 requirements `c > 0` and
`(1 - 2^{-c})^{-1} <= C_Q`.
-/
def CNLClusterEncodingProof.ofStandardConstants
    {cStar ξ X : ℝ}
    {α : Type} {paths : Finset α} {BNDHeight : α -> ℝ}
    {c CQ shellFactor Ij : ℝ} {M : Nat}
    (ladderChildren : Nat -> Finset Nat)
    (ladderHeight : Nat -> ℝ) (ladderRoot : Nat)
    (c_ge_one : 1 <= c) (CQ_ge_two : 2 <= CQ)
    (ladderHeight_dom : ∀ δ : Nat, (δ : ℝ) <= ladderHeight δ)
    (cluster_le_pathKraft :
      cleanCNLKraftSum paths BNDHeight c <=
        pathKraft ladderChildren
          (fun δ => (2 : ℝ) ^ (-(c * ladderHeight δ))) M ladderRoot)
    (manuscript_bound :
      CQ ^ M * shellFactor * X * Ij <= cStar * ξ * X / 6) :
    CNLClusterEncodingProof paths BNDHeight c CQ shellFactor X Ij cStar ξ M where
  kraft := {
    ladderChildren := ladderChildren
    ladderHeight := ladderHeight
    ladderRoot := ladderRoot
    hc_pos := by linarith
    hCQ_dom := cnl_cq_dominates_of_c_ge_one c_ge_one CQ_ge_two
    ladderHeight_dom := ladderHeight_dom
    cluster_le_pathKraft := cluster_le_pathKraft }
  budget := {
    manuscript_bound := manuscript_bound }

/-- The one-step G.6 constant domination lifts to the depth-`M` constant. -/
theorem CNLClusterEncodingProof.cq_pow_dominates
    {cStar ξ X : ℝ}
    {α : Type} {paths : Finset α} {BNDHeight : α -> ℝ}
    {c CQ shellFactor Ij : ℝ} {M : Nat}
    (proof :
      CNLClusterEncodingProof paths BNDHeight c CQ shellFactor X Ij cStar ξ M) :
    ((1 - (2 : ℝ) ^ (-c))⁻¹) ^ M <= CQ ^ M := by
  have hlt1 : (2 : ℝ) ^ (-c) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith [proof.c_pos])
  have hCcpos : (0 : ℝ) < (1 - (2 : ℝ) ^ (-c))⁻¹ := by
    apply inv_pos.mpr
    linarith
  exact pow_le_pow_left₀ (le_of_lt hCcpos) proof.cq_dominates M

/-- The G.2/G.6 ladder proof supplies the CNL cluster Kraft inequality. -/
theorem CNLClusterEncodingProof.kraftSum_le
    {cStar ξ X : ℝ}
    {α : Type} {paths : Finset α} {BNDHeight : α -> ℝ}
    {c CQ shellFactor Ij : ℝ} {M : Nat}
    (proof :
      CNLClusterEncodingProof paths BNDHeight c CQ shellFactor X Ij cStar ξ M) :
    cleanCNLKraftSum paths BNDHeight c <= CQ ^ M :=
  proof.cluster_le_pathKraft.trans
    ((liftPathKraft_le proof.c_pos proof.ladderChildren proof.ladderHeight
      proof.ladderHeight_dom M proof.ladderRoot).trans proof.cq_pow_dominates)

/-- Build `CNLClusterEncodingData` from separated encoding proofs. -/
def CNLClusterEncodingData.ofProof
    {cStar ξ X : ℝ}
    {α : Type}
    (paths : Finset α) (BNDHeight : α -> ℝ)
    (c CQ : ℝ) (M : Nat) (shellFactor Ij : ℝ)
    (shellFactor_nonneg : 0 <= shellFactor) (Ij_nonneg : 0 <= Ij)
    (proof :
      CNLClusterEncodingProof paths BNDHeight c CQ shellFactor X Ij cStar ξ M) :
    CNLClusterEncodingData cStar ξ X where
  α := α
  paths := paths
  BNDHeight := BNDHeight
  c := c
  CQ := CQ
  M := M
  shellFactor := shellFactor
  Ij := Ij
  shellFactor_nonneg := shellFactor_nonneg
  Ij_nonneg := Ij_nonneg
  kraftSum_le := CNLClusterEncodingProof.kraftSum_le proof
  manuscript_bound := proof.manuscript_bound

/-- Build `CNLClusterEncodingData` directly from the proof-v4 G.35/L.1w
weighted entropy certificate. -/
def CNLClusterEncodingData.ofWeightedEntropy
    {cStar ξ X : ℝ}
    {α : Type}
    (paths : Finset α) (BNDHeight : α -> ℝ)
    (c CQ : ℝ) (M : Nat) (shellFactor Ij : ℝ)
    (shellFactor_nonneg : 0 <= shellFactor) (Ij_nonneg : 0 <= Ij)
    (data :
      CNLWeightedEntropyData paths BNDHeight c CQ shellFactor X Ij cStar ξ M) :
    CNLClusterEncodingData cStar ξ X where
  α := α
  paths := paths
  BNDHeight := BNDHeight
  c := c
  CQ := CQ
  M := M
  shellFactor := shellFactor
  Ij := Ij
  shellFactor_nonneg := shellFactor_nonneg
  Ij_nonneg := Ij_nonneg
  kraftSum_le := data.kraft_bound
  manuscript_bound := data.weighted_bound

/-- Convert the K.3/L.1 cluster encoding package into Phase-5 CNL data. -/
def CNLClusterEncodingData.toCNLEntropyData
    {cStar ξ X : ℝ}
    (data : CNLClusterEncodingData cStar ξ X) :
    CNLEntropyData cStar ξ X where
  α := data.α
  paths := data.paths
  BNDHeight := data.BNDHeight
  c := data.c
  CQ := data.CQ
  M := data.M
  shellFactor := data.shellFactor
  Ij := data.Ij
  shellFactor_nonneg := data.shellFactor_nonneg
  Ij_nonneg := data.Ij_nonneg
  kraftSum_le := data.kraftSum_le
  manuscript_bound := data.manuscript_bound

/--
Phase-5 CNL entropy bound obtained from the explicit K.3/L.1 cluster
encoding package.
-/
theorem cnlEntropy_of_clusterEncoding
    {cStar ξ X : ℝ}
    (data : CNLClusterEncodingData cStar ξ X)
    (hX_nonneg : 0 <= X) :
    ∃ CleanTerm : ℝ,
      0 <= CleanTerm ∧
      CleanTerm <= cStar * ξ * X / 6 :=
  cnlEntropy data.toCNLEntropyData hX_nonneg

/-- Per-shell provider for the K.3/L.1 CNL cluster encoding. -/
structure CNLClusterEncodingProvider where
  constants : Erdos260Constants
  data :
    ∀ shell : FailingDyadicShell,
      shell.cQ = constants.cQ ->
        CNLClusterEncodingData constants.cStar constants.ξ (shell.X : ℝ)

theorem CNLClusterEncodingProvider.bound
    (provider : CNLClusterEncodingProvider)
    {shell : FailingDyadicShell}
    (hcQ : shell.cQ = provider.constants.cQ) :
    ∃ CleanTerm : ℝ,
      0 <= CleanTerm ∧
      CleanTerm <= provider.constants.cStar * provider.constants.ξ * (shell.X : ℝ) / 6 :=
  by
    have hX_nonneg : 0 <= (shell.X : ℝ) := by
      exact_mod_cast Nat.zero_le shell.X
    exact cnlEntropy_of_clusterEncoding (provider.data shell hcQ) hX_nonneg

end

end Erdos260
