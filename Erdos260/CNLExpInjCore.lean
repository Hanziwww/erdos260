import Mathlib
import Erdos260.CNLLiftFaithfulCore

/-!
# Appendix G.7 / L.1.2 — the irreducible heart of lift-state faithfulness: `exp_injOn`

`CNLLiftFaithfulCore.lean` (wave-16) reduced the carry-resolved lift faithfulness atom `hlift` to a
single irreducible field of `LiftStateCluster`:

```
exp_injOn : ∀ t₁ ∈ selectedTransitions T, ∀ t₂ ∈ selectedTransitions T,
              (liftNode t₁ M).δ = (liftNode t₂ M).δ → t₁ = t₂
```

i.e. *distinct surviving clean transitions receive distinct terminal lift exponents*
`(liftNode · M).δ` (manuscript `δ_k = V_k - h_k`).  This module **audits and sharpens** that atom —
the deepest CNL fact, the "2-adic nonseparation rigidity" of §G.7 / §L.1.2.

## Audit verdict (honest)

**`exp_injOn` is the genuine irreducible heart, given the present abstraction.**  `CNLTransition =
⟨normalForm, available⟩` carries *no* gap / lift-state geometry, so a constant terminal exponent
already collapses the genuine two-element selected family `exFamily` (`expInjOn_not_automatic`).  The
labelling must therefore be *supplied* by the cluster's gap structure; it cannot be conjured from the
structure fields (exactly the position of `liftPathFaithful_not_automatic` / `sym_injOn`).

So the deliverable is the **sharpest characterization**, not a fake closure.  The headline is a clean
*factoring* of the atom that isolates precisely what the 2-adic geometry contributes:

```
        exp_injOn
   ⟺  (pure logic)        pairwise-distinct terminal exponents          [PairwiseDistinctExp]
   ⟺  (G.7 common centre) pairwise 2-adically SEPARATED exponents        [PairwiseSeparated]
   ⟺  (finite family)     a classifier decoding the transition from δ    [exists_decode]
```

The middle equivalence is the manuscript's Lemma G.1 made into an *iff*: under the G.7 common 2-adic
centre `Ξ`, distinctness of the terminal exponents is **equivalent** to their being forced apart by a
full lift gap `2^δ` (`twoAdic_separation` upgrades distinct ↦ separated; `2^δ ≥ 1` gives separated ↦
distinct).  Hence **the entire 2-adic geometry serves only to make bare distinctness equivalent to
genuine separation** — the *magnitude* `2^δ` of the separation is free, and the irreducible residue
is exactly the bare distinctness of the gap-structure labelling.

## What is genuinely proved here (no `sorry`/`axiom`/`admit`/`native_decide`)

1. `expInjOn_iff_pairwiseDistinct` — pure-logic factoring (injective ⟺ distinct ↦ distinct).
2. `expSeparated_of_compatible` / `ExpSeparated.ne` — the symmetric 2-adic separation content of
   `twoAdic_separation` and its converse-free distinctness.
3. **`expInjOn_iff_pairwiseSeparated`** (headline) — under the G.7 common centre, `exp_injOn` is
   *equivalent* to pairwise 2-adic separation.  `LiftStateCluster.exp_injOn_iff_separated` /
   `…pairwiseSeparated` package it for a real cluster.
4. `expInjOn_iff_setInjOn` — the atom is exactly `Set.InjOn` of the exponent readout.
5. `expInjOn_iff_exists_decode` — the atom is *equivalent* to the existence of the manuscript's
   classifier `decode : ℕ → CNLTransition` reading the transition back off its terminal lift
   exponent (the sharpest "complete invariant" form of irreducibility).
6. `expInjOn_not_automatic` — the verdict witness: the atom is false for a geometry-free `liftNode`.
7. Non-vacuous `μ = 2` firing (`exLiftCluster_pairwiseSeparated`, `ex_expSeparated`, `ex_selected_two`)
   on wave-14's genuine two-to-one family `exFamily`, terminal exponents `0 ≠ 1` separated by `2^0`.

## The sharpest residual (what is *not* closable here, and how it would close)

`exp_injOn` reduces to **bare distinctness of the terminal lift-exponent labelling**.  To reduce
*that* further one must expose the gap sequence: enrich `CNLTransition` (or the cluster datum) with
the reverse window `(σ_i)` and define `liftNode` by the genuine slide (`shadowC_slide` /
`shadowD_slide`, §G.4–G.5), whereupon distinctness becomes a *theorem* — distinct clean gap
sequences slide to distinct exponents.  That is a source-level enrichment (reported below), not
derivable from the geometry-free `CNLTransition` of the present development.
-/

namespace Erdos260

open Finset

set_option linter.unusedVariables false

/-! ## Part 1.  The atom as a standalone predicate -/

/-- **The lift-exponent injectivity atom** — the standalone form of `LiftStateCluster.exp_injOn`:
distinct surviving clean transitions receive distinct terminal lift exponents `(liftNode · M).δ`. -/
def ExpInjOn (T : Finset CNLTransition) (M : ℕ)
    (liftNode : CNLTransition → ℕ → LiftState) : Prop :=
  ∀ t₁ ∈ selectedTransitions T, ∀ t₂ ∈ selectedTransitions T,
    (liftNode t₁ M).δ = (liftNode t₂ M).δ → t₁ = t₂

/-- The `LiftStateCluster` field is exactly this predicate. -/
theorem LiftStateCluster.expInjOn {T : Finset CNLTransition} {M : ℕ}
    (R : LiftStateCluster T M) : ExpInjOn T M R.liftNode := R.exp_injOn

/-! ## Part 2.  Pure-logic factoring: injectivity ⟺ distinctness

The first equivalence is bare logic: an injective labelling is exactly one that never collapses two
distinct transitions.  No 2-adic input is used. -/

/-- Distinctness of the terminal exponent labelling on the selected family. -/
def PairwiseDistinctExp (T : Finset CNLTransition) (M : ℕ)
    (liftNode : CNLTransition → ℕ → LiftState) : Prop :=
  ∀ t₁ ∈ selectedTransitions T, ∀ t₂ ∈ selectedTransitions T,
    t₁ ≠ t₂ → (liftNode t₁ M).δ ≠ (liftNode t₂ M).δ

/-- **`exp_injOn` ⟺ pairwise-distinct terminal exponents** (pure logic). -/
theorem expInjOn_iff_pairwiseDistinct (T : Finset CNLTransition) (M : ℕ)
    (liftNode : CNLTransition → ℕ → LiftState) :
    ExpInjOn T M liftNode ↔ PairwiseDistinctExp T M liftNode := by
  constructor
  · intro h t₁ ht₁ t₂ ht₂ hne heq
    exact hne (h t₁ ht₁ t₂ ht₂ heq)
  · intro h t₁ ht₁ t₂ ht₂ heq
    by_contra hne
    exact h t₁ ht₁ t₂ ht₂ hne heq

/-! ## Part 3.  The 2-adic separation predicate and its content (Lemma G.1, symmetrized) -/

/-- **Manuscript 2-adic separation of two lift exponents** (Lemma G.1 conclusion): the smaller
exponent plus its full lift gap `2^δ` does not exceed the larger — the two exponents are forced apart
by an entire lift gap. -/
def ExpSeparated (a b : ℕ) : Prop := a + 2 ^ a ≤ b ∨ b + 2 ^ b ≤ a

/-- Separation forces distinctness: the lift gap `2^δ ≥ 1` is positive, so separated exponents differ.
(Note this direction needs no 2-adic compatibility.) -/
theorem ExpSeparated.ne {a b : ℕ} (h : ExpSeparated a b) : a ≠ b := by
  rcases h with h | h
  · have hp : 0 < 2 ^ a := pow_pos (by norm_num) a
    omega
  · have hp : 0 < 2 ^ b := pow_pos (by norm_num) b
    omega

/-- **Under the G.7 common 2-adic centre, distinct exponents are separated** — `twoAdic_separation`
(Lemma G.1) packaged symmetrically. -/
theorem expSeparated_of_compatible {Ξ : ℤ} {a b : ℕ}
    (ha : TwoAdicCompatible Ξ a) (hb : TwoAdicCompatible Ξ b) (hne : a ≠ b) :
    ExpSeparated a b := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact Or.inl (twoAdic_separation ha hb hlt)
  · exact Or.inr (twoAdic_separation hb ha hgt)

/-! ## Part 4.  The headline: `exp_injOn` ⟺ pairwise 2-adic separation -/

/-- Pairwise 2-adic separation of the terminal lift exponents on the selected family. -/
def PairwiseSeparated (T : Finset CNLTransition) (M : ℕ)
    (liftNode : CNLTransition → ℕ → LiftState) : Prop :=
  ∀ t₁ ∈ selectedTransitions T, ∀ t₂ ∈ selectedTransitions T,
    t₁ ≠ t₂ → ExpSeparated (liftNode t₁ M).δ (liftNode t₂ M).δ

/-- **Under the G.7 common centre, distinctness ⟺ separation.**  The forward direction is
`twoAdic_separation` (the 2-adic content); the reverse is free (`2^δ ≥ 1`).  This isolates exactly
what the 2-adic geometry contributes: it upgrades bare distinctness to genuine separation. -/
theorem pairwiseDistinct_iff_pairwiseSeparated
    (T : Finset CNLTransition) (M : ℕ) (liftNode : CNLTransition → ℕ → LiftState) (Ξ : ℤ)
    (hcompat : ∀ t ∈ selectedTransitions T, TwoAdicCompatible Ξ (liftNode t M).δ) :
    PairwiseDistinctExp T M liftNode ↔ PairwiseSeparated T M liftNode := by
  constructor
  · intro h t₁ ht₁ t₂ ht₂ hne
    exact expSeparated_of_compatible (hcompat t₁ ht₁) (hcompat t₂ ht₂) (h t₁ ht₁ t₂ ht₂ hne)
  · intro h t₁ ht₁ t₂ ht₂ hne
    exact (h t₁ ht₁ t₂ ht₂ hne).ne

/--
**The headline characterization: faithfulness of the lift state IS 2-adic nonseparation rigidity.**

Under the manuscript G.7 common 2-adic centre `Ξ` (`hcompat`), the irreducible atom `exp_injOn`
(injective terminal lift-exponent labelling) is **equivalent** to the terminal lift states being
pairwise 2-adically *separated* — the manuscript's "2-adic compatible nonseparation data".  This is
the sharpest reduction: the atom does not depend on the *size* of the gaps (separation by `2^δ` is
free from compatibility), only on the bare *distinctness* of the exponent labelling. -/
theorem expInjOn_iff_pairwiseSeparated
    (T : Finset CNLTransition) (M : ℕ) (liftNode : CNLTransition → ℕ → LiftState) (Ξ : ℤ)
    (hcompat : ∀ t ∈ selectedTransitions T, TwoAdicCompatible Ξ (liftNode t M).δ) :
    ExpInjOn T M liftNode ↔ PairwiseSeparated T M liftNode :=
  (expInjOn_iff_pairwiseDistinct T M liftNode).trans
    (pairwiseDistinct_iff_pairwiseSeparated T M liftNode Ξ hcompat)

/-! ## Part 5.  The atom packaged for a genuine lift-state cluster -/

namespace LiftStateCluster

variable {T : Finset CNLTransition} {M : ℕ}

/-- For any `LiftState`-valued cluster (carrying its G.7 common centre), the atom `exp_injOn` is
*equivalent* to pairwise 2-adic separation of the terminal lift states. -/
theorem exp_injOn_iff_separated (R : LiftStateCluster T M) :
    ExpInjOn T M R.liftNode ↔ PairwiseSeparated T M R.liftNode :=
  expInjOn_iff_pairwiseSeparated T M R.liftNode R.centre R.compat

/-- Hence every lift-state cluster's terminal exponents are pairwise 2-adically separated — the
manuscript rigidity, obtained from the supplied injective labelling and the G.7 compatibility. -/
theorem pairwiseSeparated (R : LiftStateCluster T M) : PairwiseSeparated T M R.liftNode :=
  R.exp_injOn_iff_separated.mp R.expInjOn

end LiftStateCluster

/-! ## Part 6.  The atom as `Set.InjOn`, and as a complete invariant (classifier) -/

/-- **`exp_injOn` is exactly `Set.InjOn` of the terminal lift-exponent readout** on the selected
family — the abstract restatement of the atom. -/
theorem expInjOn_iff_setInjOn (T : Finset CNLTransition) (M : ℕ)
    (liftNode : CNLTransition → ℕ → LiftState) :
    ExpInjOn T M liftNode ↔
      Set.InjOn (fun t => (liftNode t M).δ) (↑(selectedTransitions T) : Set CNLTransition) := by
  constructor
  · intro h a ha b hb hab
    exact h a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb) hab
  · intro h a ha b hb hab
    exact h (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab

/--
**`exp_injOn` ⟺ the terminal lift exponent is a complete invariant (a classifier exists).**

The atom holds iff there is a `decode : ℕ → CNLTransition` reading the surviving clean transition
back off its terminal lift exponent on the selected family (`decode ((liftNode t M).δ) = t`).  This
is the manuscript's reconstruction map, and is the sharpest "irreducible content" statement: a
faithful exponent labelling *is* an exponent that classifies the transition.  (⟸) is immediate;
(⟹) builds the classifier by choice over the finite selected family. -/
theorem expInjOn_iff_exists_decode (T : Finset CNLTransition) (M : ℕ)
    (liftNode : CNLTransition → ℕ → LiftState) :
    ExpInjOn T M liftNode ↔
      ∃ decode : ℕ → CNLTransition,
        ∀ t ∈ selectedTransitions T, decode ((liftNode t M).δ) = t := by
  constructor
  · intro h
    classical
    refine ⟨fun n => if hex : ∃ t ∈ selectedTransitions T, (liftNode t M).δ = n
              then hex.choose else exT0, ?_⟩
    intro t ht
    have hex : ∃ t' ∈ selectedTransitions T, (liftNode t' M).δ = (liftNode t M).δ := ⟨t, ht, rfl⟩
    show (if hex' : ∃ t' ∈ selectedTransitions T, (liftNode t' M).δ = (liftNode t M).δ
            then hex'.choose else exT0) = t
    rw [dif_pos hex]
    obtain ⟨hmem, hval⟩ := hex.choose_spec
    exact h _ hmem t ht hval
  · rintro ⟨decode, hdec⟩ t₁ ht₁ t₂ ht₂ heq
    rw [← hdec t₁ ht₁, ← hdec t₂ ht₂, heq]

/-! ## Part 7.  Audit verdict: the atom is not automatic (genuine irreducible heart) -/

/-- **`exp_injOn` is NOT a logical consequence of the `CNLTransition` structure.**  A constant
terminal lift exponent (a `liftNode` carrying no gap geometry) collapses the genuine two-element
selected family `exFamily`, violating `ExpInjOn`.  Hence the injective lift-exponent labelling is a
genuine *supplied* gap-structure invariant — the irreducible heart of lift-state faithfulness, the
same honest position as `liftPathFaithful_not_automatic` / `sym_injOn`. -/
theorem expInjOn_not_automatic :
    ∃ (M : ℕ) (liftNode : CNLTransition → ℕ → LiftState),
      ¬ ExpInjOn exFamily M liftNode := by
  refine ⟨0, (fun _ _ => ⟨0, 0⟩), ?_⟩
  intro h
  have hcontra : exT0 = exT1 := h exT0 (by decide) exT1 (by decide) rfl
  exact absurd hcontra (by decide)

/-! ## Part 8.  Non-vacuous `μ = 2` firing in the genuine `LiftState` geometry

Reusing wave-14's two-to-one family `exFamily = {exT0, exT1}` and the genuine `LiftState` cluster
`exLiftCluster` (terminal exponents `0` for the positive-lift form, `1` for the child-residue form),
the characterizations fire non-vacuously: the family genuinely has two distinct members whose
terminal exponents are 2-adically separated. -/

/-- The two genuine members are distinct and both selected (the firing is non-vacuous). -/
theorem ex_selected_two :
    exT0 ∈ selectedTransitions exFamily ∧ exT1 ∈ selectedTransitions exFamily ∧ exT0 ≠ exT1 :=
  ⟨by decide, by decide, by decide⟩

/-- The two terminal lift exponents `0` and `1` are 2-adically separated by the full lift gap `2^0`
(manuscript Lemma G.1): `0 + 2^0 = 1 ≤ 1`. -/
theorem ex_expSeparated : ExpSeparated (exLiftNode exT0 1).δ (exLiftNode exT1 1).δ := by
  rw [exLiftNode_T0_delta, exLiftNode_T1_delta]
  exact Or.inl (by decide)

/-- **The genuine cluster's terminal exponents are pairwise 2-adically separated** — the headline
rigidity, fired on the real `LiftState` geometry of `exLiftCluster`. -/
theorem exLiftCluster_pairwiseSeparated :
    PairwiseSeparated exFamily 1 exLiftCluster.liftNode :=
  exLiftCluster.pairwiseSeparated

/-- **The headline iff fires on the genuine cluster**: on `exLiftCluster`, `exp_injOn` is equivalent
to pairwise 2-adic separation. -/
theorem exLiftCluster_expInjOn_iff :
    ExpInjOn exFamily 1 exLiftCluster.liftNode ↔ PairwiseSeparated exFamily 1 exLiftCluster.liftNode :=
  exLiftCluster.exp_injOn_iff_separated

/-! ## Part 9.  Honest residual inventory -/

/-- The precise status of the §G.7 / §L.1.2 lift-exponent injectivity atom `exp_injOn` after this
module. -/
def cnlExpInjCoreResiduals : List String :=
  [ "AUDIT VERDICT (proved) — expInjOn_not_automatic: exp_injOn is FALSE for a geometry-free " ++
      "liftNode (constant terminal exponent) on the genuine two-element family exFamily. " ++
      "CNLTransition = ⟨normalForm, available⟩ carries NO gap / lift geometry, so the injective " ++
      "terminal lift-exponent labelling cannot be derived from the structure; it is a SUPPLIED " ++
      "gap-structure invariant — the genuine irreducible heart (cf. liftPathFaithful_not_automatic).",
    "PURE-LOGIC FACTORING (proved) — expInjOn_iff_pairwiseDistinct: exp_injOn ⟺ the terminal " ++
      "exponents are pairwise DISTINCT on the selected family (an injective labelling never " ++
      "collapses two transitions). No 2-adic input is used here.",
    "HEADLINE 2-ADIC RIGIDITY (proved, sharp iff) — expInjOn_iff_pairwiseSeparated: under the G.7 " ++
      "common 2-adic centre Ξ (TwoAdicCompatible), exp_injOn ⟺ the terminal lift states are " ++
      "pairwise 2-adically SEPARATED (a + 2^a ≤ b for the ordered pair), via twoAdic_separation " ++
      "(Lemma G.1) forward and 2^δ ≥ 1 backward. So faithfulness of the lift state IS 2-adic " ++
      "nonseparation rigidity. Packaged for a real cluster as LiftStateCluster.exp_injOn_iff_" ++
      "separated / .pairwiseSeparated.",
    "SHARP CONSEQUENCE — the 2-adic geometry contributes ONLY the upgrade distinct ⟺ separated " ++
      "(pairwiseDistinct_iff_pairwiseSeparated): the separation MAGNITUDE 2^δ is FREE from " ++
      "compatibility, so the irreducible residue of exp_injOn is exactly BARE DISTINCTNESS of the " ++
      "terminal lift-exponent labelling.",
    "COMPLETE-INVARIANT FORM (proved) — expInjOn_iff_exists_decode / expInjOn_iff_setInjOn: " ++
      "exp_injOn ⟺ Set.InjOn of the readout ⟺ the existence of a classifier decode : ℕ → " ++
      "CNLTransition reading the transition back off its terminal lift exponent. The atom is " ++
      "precisely 'the terminal lift exponent is a complete invariant of the surviving transition'.",
    "NON-VACUOUS μ = 2 (proved) — exLiftCluster_pairwiseSeparated / ex_expSeparated / ex_selected_" ++
      "two: on wave-14's genuine two-to-one family exFamily the headline fires with two DISTINCT " ++
      "selected members whose terminal exponents 0 ≠ 1 are separated by the lift gap 2^0. Never the " ++
      "injective/∅/singleton shortcut.",
    "SHARPEST RESIDUAL (not closable here; needs source enrichment) — exp_injOn reduces to bare " ++
      "DISTINCTNESS of the terminal lift-exponent labelling. To prove THAT one must expose the gap " ++
      "sequence: enrich CNLTransition / the cluster datum with the reverse window (σ_i) and define " ++
      "liftNode by the genuine slide (shadowC_slide / shadowD_slide, §G.4–G.5), whereupon distinct " ++
      "clean gap sequences slide to distinct exponents. That is a SOURCE-LEVEL enrichment, not " ++
      "derivable from the geometry-free CNLTransition of the present development." ]

theorem cnlExpInjCoreResiduals_nonempty : cnlExpInjCoreResiduals ≠ [] := by
  simp [cnlExpInjCoreResiduals]

/-! ## Part 10.  Axiom-cleanliness audit -/

#print axioms expInjOn_iff_pairwiseDistinct
#print axioms ExpSeparated.ne
#print axioms expSeparated_of_compatible
#print axioms pairwiseDistinct_iff_pairwiseSeparated
#print axioms expInjOn_iff_pairwiseSeparated
#print axioms LiftStateCluster.exp_injOn_iff_separated
#print axioms LiftStateCluster.pairwiseSeparated
#print axioms expInjOn_iff_setInjOn
#print axioms expInjOn_iff_exists_decode
#print axioms expInjOn_not_automatic
#print axioms ex_selected_two
#print axioms ex_expSeparated
#print axioms exLiftCluster_pairwiseSeparated
#print axioms exLiftCluster_expInjOn_iff
#print axioms cnlExpInjCoreResiduals_nonempty

end Erdos260
