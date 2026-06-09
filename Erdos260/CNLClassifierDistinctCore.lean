import Mathlib
import Erdos260.CNLGapEnrichCore
import Erdos260.CNLClusterCoordinatization
import Erdos260.AppendixG_CNLClassifier

/-!
# Lemma L.1.1 / J.5 -- DERIVING `gapData_injOn` (the CNL classifier window-distinctness)

`CNLGapEnrichCore.lean` (wave-18) reduced the G.7 / L.1.2 lift-exponent injectivity atom
`exp_injOn` to a single combinatorial input field of `GapLiftCluster`:

```
gapData_injOn : forall t1 in selectedTransitions T, forall t2 in selectedTransitions T,
                  gapData t1 = gapData t2 -> t1 = t2
```

i.e. distinct surviving clean transitions carry distinct reverse gap windows.  Wave-18 could only
assume this field (or discharge it by `decide` on the toy two-element family).  This module
derives and sharply characterizes it -- the Lemma L.1.1 / J.5 classifier window-distinctness.

## The genuine mechanism (manuscript L.1.1 / L.1.2a-c)

The reverse gap window of a transition is, by manuscript (G.1), the reverse partial-sum exponent set
`{sigma_0(k), ..., sigma_{r-1}(k)}` of its gap code (the recorded clean ladder word).  The L.1.1 /
J.5 exhaustive priority classification (BND/SEP/TC/VS/DS/TP/PKG) strips exactly the coincidence cases:
Lemma L.1.2a (SEP), L.1.2b (VS), L.1.2c (DS) and the PKG exit each show those transitions are not
counted as clean unclassified CNL choices -- and each removed class records boundary/carry residues
that "recover the CNL transition up to O_Q(1) choices".  So the surviving clean family carries a
faithful recorded gap code, and a faithful clean gap code forces distinct windows.

The window-to-gaps step is a genuine theorem (already proved in `CNLGapEnrichCore`): a clean
window has positive gaps => strictly increasing partial sums => the reverse-window set recovers the
partial-sum enumeration (`strictMono_eq_of_image_eq`) => the gaps (`gaps_eq_of_sigma_eq`).  Hence

```
clean gap-code faithfulness  =>  window-distinctness  (gapData_injOn)
```

is a theorem, and clean gap-code faithfulness is exactly `CleanClusterReconstruction.sym_injOn`,
the already-isolated irreducible CNL atom (`CNLClusterCoordinatization`).  Therefore this module
unifies the CNL irreducible core: `gapData_injOn` joins `path_injOn` and (through wave-18's
`exp_injOn_derived`) `exp_injOn` as a consequence of the single atom `sym_injOn`.

## What is genuinely proved here (no `sorry`/`axiom`/`admit`/`native_decide`)

1. `gapDataInjOn_iff_pairwiseDistinct` / `gapDataInjOn_iff_setInjOn` / `gapDataInjOn_iff_exists_decode`
   -- the atom is exactly `Set.InjOn` of the window readout, equivalently the existence of the L.1.1
   classifier reconstruction map `decode : Finset Nat -> CNLTransition` reading the transition back
   off its window (the "complete invariant" form).
2. `gapDataInjOn_of_gapCode_injOn` (the genuine core) -- for a clean gap code, faithfulness of the
   code on the selected family derives window-distinctness, via the proved window-to-gaps recovery.
3. `gapDataInjOn_ofReconstruction` -- the same derivation fed by `CleanClusterReconstruction.sym_injOn`:
   `gapData_injOn` is a theorem given the cluster reconstruction's code-faithfulness atom.
4. `GapLiftCluster.ofCleanReconstruction` -- assembles a genuine `GapLiftCluster` whose
   `gapData_injOn` field is derived (not assumed) from `sym_injOn`; `exp_injOn` then follows through
   wave-18's `exp_injOn_derived` (`exp_injOn_ofCleanReconstruction`).
5. `gapDataInjOn_not_automatic` -- the verdict witness: window-distinctness is FALSE for a
   geometry-free constant window on the genuine two-element family, so it is a genuine supplied
   gap-structure invariant (the irreducible atom is `sym_injOn`, not derivable from `CNLTransition`).
6. Non-vacuous mu = 2 firing (`exGapDataInjOn`, `exGapWindow_distinct`) on wave-14's genuine
   two-element family with a clean gap code: `exT0 |-> {0,1}`, `exT1 |-> {0,2}` (two DISTINCT,
   same-cardinality windows), and `gapData_injOn` is derived from the gap-code faithfulness,
   never the empty/singleton/different-cardinality shortcut.

## The sharpest residual (honest)

After this module, `gapData_injOn` is derived from `sym_injOn` (clean-survivor gap-code
faithfulness) -- the same irreducible atom on which `path_injOn` already rests.  That atom is the
genuine irreducible heart: `CNLTransition = (normalForm, available)` carries no gap geometry, so the
window readout must be supplied (the manuscript L.1.2a-c "recover the transition up to O_Q(1)",
sharpened to injective on the clean subfamily).  The G.7 common-2-adic-centre `compat` remains a
supplied hypothesis (as in wave-18).  A noted tension: a uniform-length clean window forces equal
window cardinality, while the G.7 `compat` 2-adically separates the surviving shadow numerators; the
manuscript reconciles these through depth-varying window lengths `r = r(k)`, which the uniform
`CleanClusterReconstruction.M` does not model (reported as a source enrichment, not applied).
-/

namespace Erdos260

open Finset

set_option linter.unusedVariables false

/-! ## Part 1.  The atom as a standalone predicate, and its `Set.InjOn` / decode characterizations -/

/-- **The window-distinctness atom** -- the standalone form of `GapLiftCluster.gapData_injOn`:
distinct surviving clean transitions carry distinct reverse gap windows.  This is the Lemma L.1.1 /
J.5 classifier window-distinctness. -/
def GapDataInjOn (T : Finset CNLTransition) (gapData : CNLTransition → Finset ℕ) : Prop :=
  ∀ t₁ ∈ selectedTransitions T, ∀ t₂ ∈ selectedTransitions T,
    gapData t₁ = gapData t₂ → t₁ = t₂

/-- The `GapLiftCluster` field is exactly this predicate. -/
theorem GapLiftCluster.gapDataInjOn {T : Finset CNLTransition} {M : ℕ}
    (G : GapLiftCluster T M) : GapDataInjOn T G.gapData := G.gapData_injOn

/-- Window distinctness in the contrapositive (distinct survivors get distinct windows). -/
def PairwiseDistinctWindow (T : Finset CNLTransition) (gapData : CNLTransition → Finset ℕ) : Prop :=
  ∀ t₁ ∈ selectedTransitions T, ∀ t₂ ∈ selectedTransitions T,
    t₁ ≠ t₂ → gapData t₁ ≠ gapData t₂

/-- **`gapData_injOn` iff pairwise-distinct windows** (pure logic). -/
theorem gapDataInjOn_iff_pairwiseDistinct (T : Finset CNLTransition)
    (gapData : CNLTransition → Finset ℕ) :
    GapDataInjOn T gapData ↔ PairwiseDistinctWindow T gapData := by
  constructor
  · intro h t₁ ht₁ t₂ ht₂ hne heq
    exact hne (h t₁ ht₁ t₂ ht₂ heq)
  · intro h t₁ ht₁ t₂ ht₂ heq
    by_contra hne
    exact h t₁ ht₁ t₂ ht₂ hne heq

/-- **`gapData_injOn` is exactly `Set.InjOn` of the window readout** on the selected family. -/
theorem gapDataInjOn_iff_setInjOn (T : Finset CNLTransition)
    (gapData : CNLTransition → Finset ℕ) :
    GapDataInjOn T gapData ↔
      Set.InjOn gapData (↑(selectedTransitions T) : Set CNLTransition) := by
  constructor
  · intro h a ha b hb hab
    exact h a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb) hab
  · intro h a ha b hb hab
    exact h (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab

/--
**`gapData_injOn` iff the reverse gap window is a complete invariant (the L.1.1 classifier decoder).**

The atom holds iff there is a `decode : Finset Nat -> CNLTransition` reading the surviving clean
transition back off its reverse gap window on the selected family (`decode (gapData t) = t`).  This is
the manuscript's L.1.2a-c reconstruction map (each removed coincidence class records exactly the
residues recovering the transition); it is the sharpest "irreducible content" statement.  The reverse
direction is immediate; the forward builds the decoder by choice over the finite selected family. -/
theorem gapDataInjOn_iff_exists_decode (T : Finset CNLTransition)
    (gapData : CNLTransition → Finset ℕ) :
    GapDataInjOn T gapData ↔
      ∃ decode : Finset ℕ → CNLTransition,
        ∀ t ∈ selectedTransitions T, decode (gapData t) = t := by
  constructor
  · intro h
    classical
    refine ⟨fun w => if hex : ∃ t ∈ selectedTransitions T, gapData t = w
              then hex.choose else exT0, ?_⟩
    intro t ht
    have hex : ∃ t' ∈ selectedTransitions T, gapData t' = gapData t := ⟨t, ht, rfl⟩
    show (if hex' : ∃ t' ∈ selectedTransitions T, gapData t' = gapData t
            then hex'.choose else exT0) = t
    rw [dif_pos hex]
    obtain ⟨hmem, hval⟩ := hex.choose_spec
    exact h _ hmem t ht hval
  · rintro ⟨decode, hdec⟩ t₁ ht₁ t₂ ht₂ heq
    rw [← hdec t₁ ht₁, ← hdec t₂ ht₂, heq]

/-! ## Part 2.  The genuine core -- clean gap-code faithfulness implies window-distinctness

The reverse gap window of a transition is the reverse partial-sum exponent set `{sigma_0, ..., sigma_r}`
of its gap code (manuscript G.1).  For a clean window (positive gaps) the partial sums are strictly
increasing, so the window set recovers the partial-sum enumeration and hence the gaps.  Therefore a
faithful clean gap code forces distinct windows -- the Lemma L.1.1 removal-completeness conclusion. -/

/-- **The reverse gap window of a gap code** -- the manuscript (G.1) reverse partial-sum exponent set
`{sigma_0(k), ..., sigma_r(k)}` (with `sigma_i = g_0 + ... + g_{i-1}`, `sigma_0 = 0`) over `r + 1`
positions. -/
def windowOfGapCode (gapCode : CNLTransition → ℕ → ℕ) (r : ℕ) (t : CNLTransition) : Finset ℕ :=
  (Finset.range (r + 1)).image (sigmaOfGaps (gapCode t))

/--
**The genuine core: clean gap-code faithfulness DERIVES window-distinctness.**

If every selected survivor has a clean gap code (all gaps positive, manuscript "clean window") and
the gap code is faithful on the selected family (the L.1.2a-c surviving-clean-code property --
distinct survivors have distinct gap words on the window), then the reverse gap windows are distinct.

The proof is the manuscript window-to-gaps recovery, here genuine theorems: positive gaps give a
strictly monotone partial-sum `sigma` (`sigmaOfGaps_strictMono`); equal window sets of strictly
monotone `sigma` force equal `sigma` enumerations (`strictMono_eq_of_image_eq`); equal `sigma`
enumerations force equal gaps (`gaps_eq_of_sigma_eq`); faithfulness then forces equal transitions. -/
theorem gapDataInjOn_of_gapCode_injOn
    {T : Finset CNLTransition} {gapCode : CNLTransition → ℕ → ℕ} {r : ℕ}
    (hclean : ∀ t ∈ selectedTransitions T, ∀ j, 0 < gapCode t j)
    (hfaithful : ∀ t₁ ∈ selectedTransitions T, ∀ t₂ ∈ selectedTransitions T,
        (∀ j, j < r → gapCode t₁ j = gapCode t₂ j) → t₁ = t₂) :
    GapDataInjOn T (windowOfGapCode gapCode r) := by
  intro t₁ ht₁ t₂ ht₂ hwin
  have hs₁ : StrictMono (sigmaOfGaps (gapCode t₁)) := sigmaOfGaps_strictMono (hclean t₁ ht₁)
  have hs₂ : StrictMono (sigmaOfGaps (gapCode t₂)) := sigmaOfGaps_strictMono (hclean t₂ ht₂)
  have himg : (Finset.range (r + 1)).image (sigmaOfGaps (gapCode t₁))
            = (Finset.range (r + 1)).image (sigmaOfGaps (gapCode t₂)) := hwin
  have hsig := strictMono_eq_of_image_eq hs₁ hs₂ himg
  have hgap := gaps_eq_of_sigma_eq hsig
  refine hfaithful t₁ ht₁ t₂ ht₂ ?_
  intro j hj
  exact hgap j (by omega)

/-! ## Part 3.  Fed by the cluster reconstruction's code-faithfulness atom `sym_injOn`

`CleanClusterReconstruction` (`CNLClusterCoordinatization`) already isolates the irreducible CNL atom
`sym_injOn` -- the recorded clean ladder code is faithful on the selected family.  When that recorded
code is the clean gap word (positive symbols), the window readout `windowOfGapCode R.sym R.M`
inherits `gapData_injOn` directly: the same atom that delivers `path_injOn`. -/

/-- **`gapData_injOn` from the cluster reconstruction's code-faithfulness.**  If the recorded clean
ladder code `R.sym` is a clean gap word (positive on the selected family), then its reverse gap
window is distinct on survivors -- a theorem of `R.sym_injOn`. -/
theorem gapDataInjOn_ofReconstruction
    {T : Finset CNLTransition} {BNDHeight : CNLTransition → ℝ} {c CQ : ℝ}
    (R : CleanClusterReconstruction T BNDHeight c CQ)
    (hclean : ∀ t ∈ selectedTransitions T, ∀ j, 0 < R.sym t j) :
    GapDataInjOn T (windowOfGapCode R.sym R.M) :=
  gapDataInjOn_of_gapCode_injOn hclean R.sym_injOn

/--
**A `GapLiftCluster` whose `gapData_injOn` is DERIVED from `sym_injOn`.**

Assembles a genuine `GapLiftCluster` from a clean-gap-word `CleanClusterReconstruction`: the window
readout is `windowOfGapCode R.sym R.M`, the `gapData_injOn` field is the theorem
`gapDataInjOn_ofReconstruction` (not an assumption), and the G.7 common-2-adic-centre `compat` is the
supplied hypothesis (as in wave-18).  From this, wave-18's `exp_injOn_derived` gives `exp_injOn`. -/
def GapLiftCluster.ofCleanReconstruction
    {T : Finset CNLTransition} {BNDHeight : CNLTransition → ℝ} {c CQ : ℝ}
    (R : CleanClusterReconstruction T BNDHeight c CQ) (M : ℕ)
    (hclean : ∀ t ∈ selectedTransitions T, ∀ j, 0 < R.sym t j)
    (centre : ℤ)
    (compat : ∀ t ∈ selectedTransitions T,
        TwoAdicCompatible centre (shadowNat (windowOfGapCode R.sym R.M t))) :
    GapLiftCluster T M where
  gapData := windowOfGapCode R.sym R.M
  centre := centre
  compat := compat
  gapData_injOn := gapDataInjOn_ofReconstruction R hclean

/-- **The full CNL chain `sym_injOn => gapData_injOn => exp_injOn`, assembled.**  The terminal
lift-exponent injectivity atom is derived for the gap-enriched cluster built from the cluster
reconstruction's code-faithfulness. -/
theorem exp_injOn_ofCleanReconstruction
    {T : Finset CNLTransition} {BNDHeight : CNLTransition → ℝ} {c CQ : ℝ}
    (R : CleanClusterReconstruction T BNDHeight c CQ) (M : ℕ)
    (hclean : ∀ t ∈ selectedTransitions T, ∀ j, 0 < R.sym t j)
    (centre : ℤ)
    (compat : ∀ t ∈ selectedTransitions T,
        TwoAdicCompatible centre (shadowNat (windowOfGapCode R.sym R.M t))) :
    ExpInjOn T M (GapLiftCluster.ofCleanReconstruction R M hclean centre compat).liftNode :=
  (GapLiftCluster.ofCleanReconstruction R M hclean centre compat).exp_injOn_derived

/-! ## Part 4.  Audit verdict: window-distinctness is not automatic (genuine supplied invariant) -/

/-- **`gapData_injOn` is NOT a logical consequence of the `CNLTransition` structure.**  A constant
(geometry-free) window collapses the genuine two-element selected family `exFamily`, violating
`GapDataInjOn`.  Hence the window readout is a genuine supplied gap-structure invariant -- the
irreducible heart is the gap-code faithfulness atom `sym_injOn`, not the structure of `CNLTransition`.
This is the same honest position as `expInjOn_not_automatic` / `sym_injOn`. -/
theorem gapDataInjOn_not_automatic :
    ∃ gapData : CNLTransition → Finset ℕ, ¬ GapDataInjOn exFamily gapData := by
  refine ⟨fun _ => ∅, ?_⟩
  intro h
  have hcontra : exT0 = exT1 := h exT0 (by decide) exT1 (by decide) rfl
  exact absurd hcontra (by decide)

/-! ## Part 5.  Non-vacuous mu = 2 firing in the genuine geometry

Wave-14's two-element surviving family `exFamily = {exT0, exT1}` with a genuine clean gap code:
positive-lift |-> constant gap `1` (window `{0,1}`); child-residue |-> constant gap `2` (window
`{0,2}`).  The two windows are DISTINCT and of the same cardinality `2` (so this is not the empty /
singleton / different-cardinality shortcut), and `gapData_injOn` is DERIVED from the gap-code
faithfulness. -/

/-- A genuine clean gap code on `exFamily`: positive-lift survivors record gap `1`, child-residue
survivors record gap `2`.  Both gaps are positive (clean window). -/
def exGapCode (t : CNLTransition) (j : ℕ) : ℕ :=
  if t.normalForm = CNLNormalForm.positiveLift then 1 else 2

theorem exGapCode_T0_zero : exGapCode exT0 0 = 1 := by simp [exGapCode, exT0]

theorem exGapCode_T1_zero : exGapCode exT1 0 = 2 := by simp [exGapCode, exT1]

/-- **The gap-code faithfulness DERIVES window-distinctness on the genuine family.**  Both survivors
are clean (positive gaps) and the gap code is faithful (the only positive-lift survivor is `exT0`, the
only child-residue survivor is `exT1`), so the reverse gap windows are distinct on survivors. -/
theorem exGapDataInjOn : GapDataInjOn exFamily (windowOfGapCode exGapCode 1) := by
  refine gapDataInjOn_of_gapCode_injOn (r := 1) ?_ ?_
  · intro t ht j
    unfold exGapCode
    split <;> norm_num
  · intro t₁ ht₁ t₂ ht₂ hcode
    have h0 := hcode 0 (by norm_num)
    have hm₁ := selectedTransitions_subset _ ht₁
    have hm₂ := selectedTransitions_subset _ ht₂
    simp only [exFamily, Finset.mem_insert, Finset.mem_singleton] at hm₁ hm₂
    rcases hm₁ with rfl | rfl <;> rcases hm₂ with rfl | rfl
    · rfl
    · rw [exGapCode_T0_zero, exGapCode_T1_zero] at h0; exact absurd h0 (by norm_num)
    · rw [exGapCode_T1_zero, exGapCode_T0_zero] at h0; exact absurd h0 (by norm_num)
    · rfl

/-- **The two derived windows are genuinely distinct** (`{0,1} != {0,2}`), of the same cardinality
`2` -- the firing is genuinely two-to-one, never an empty / singleton / cardinality shortcut. -/
theorem exGapWindow_distinct :
    windowOfGapCode exGapCode 1 exT0 ≠ windowOfGapCode exGapCode 1 exT1 := by
  intro h
  have h1mem : (1 : ℕ) ∈ windowOfGapCode exGapCode 1 exT0 := by
    rw [windowOfGapCode, Finset.mem_image]
    refine ⟨1, Finset.mem_range.mpr (by norm_num), ?_⟩
    simp [sigmaOfGaps, exGapCode_T0_zero]
  rw [h, windowOfGapCode, Finset.mem_image] at h1mem
  obtain ⟨i, hi, hval⟩ := h1mem
  rw [Finset.mem_range] at hi
  interval_cases i
  · simp [sigmaOfGaps] at hval
  · rw [sigmaOfGaps, Finset.sum_range_one, exGapCode_T1_zero] at hval
    exact absurd hval (by norm_num)

/-- The two genuine survivors are distinct and both selected (the firing is non-vacuous). -/
theorem exGap_selected_two :
    exT0 ∈ selectedTransitions exFamily ∧ exT1 ∈ selectedTransitions exFamily ∧ exT0 ≠ exT1 :=
  ⟨by decide, by decide, by decide⟩

/-! ## Part 6.  Honest residual inventory -/

/-- The precise status of the Lemma L.1.1 / J.5 classifier window-distinctness atom `gapData_injOn`
after this module. -/
def cnlClassifierDistinctCoreResiduals : List String :=
  [ "GENUINE CORE (proved) -- gapDataInjOn_of_gapCode_injOn: clean gap-code faithfulness DERIVES " ++
      "window-distinctness gapData_injOn. The reverse gap window is the partial-sum exponent SET of " ++
      "the gap code (manuscript G.1); for a CLEAN window (positive gaps) sigma is strictly " ++
      "increasing, so the window set recovers the sigma-enumeration (strictMono_eq_of_image_eq) and " ++
      "hence the gaps (gaps_eq_of_sigma_eq); faithfulness then forces equal transitions. The " ++
      "window-to-gaps step is a genuine theorem, so classifier removal-completeness implies " ++
      "window-distinctness is DERIVED.",
    "FED BY THE IRREDUCIBLE ATOM (proved) -- gapDataInjOn_ofReconstruction: clean gap-code " ++
      "faithfulness IS CleanClusterReconstruction.sym_injOn, the already-isolated irreducible CNL " ++
      "atom (CNLClusterCoordinatization). So gapData_injOn is a THEOREM given sym_injOn, the SAME " ++
      "atom that delivers path_injOn. This UNIFIES the CNL irreducible core: gapData_injOn joins " ++
      "path_injOn and (via wave-18 exp_injOn_derived) exp_injOn, all consequences of sym_injOn.",
    "FULL CHAIN ASSEMBLED (proved) -- GapLiftCluster.ofCleanReconstruction / " ++
      "exp_injOn_ofCleanReconstruction: a GapLiftCluster whose gapData_injOn field is DERIVED (not " ++
      "assumed) from sym_injOn, with the G.7 common-2-adic-centre compat supplied; wave-18's " ++
      "exp_injOn_derived then yields exp_injOn. The chain sym_injOn => gapData_injOn => exp_injOn is " ++
      "a constructed cluster.",
    "COMPLETE-INVARIANT FORM (proved) -- gapDataInjOn_iff_exists_decode / _iff_setInjOn / " ++
      "_iff_pairwiseDistinct: gapData_injOn iff Set.InjOn of the window readout iff the existence of " ++
      "the L.1.1 classifier decoder decode : Finset Nat -> CNLTransition reading the transition off " ++
      "its reverse gap window (the manuscript L.1.2a-c residue reconstruction, sharpened to injective).",
    "AUDIT VERDICT (proved) -- gapDataInjOn_not_automatic: gapData_injOn is FALSE for a geometry-free " ++
      "constant window on exFamily. CNLTransition = (normalForm, available) carries NO gap geometry, " ++
      "so the window readout is a genuine SUPPLIED invariant; the irreducible heart is the gap-code " ++
      "faithfulness atom sym_injOn, not the structure of CNLTransition.",
    "NON-VACUOUS mu = 2 (proved) -- exGapDataInjOn / exGapWindow_distinct: on wave-14's two-element " ++
      "family exFamily with a clean gap code, positive-lift |-> window {0,1} and child-residue |-> " ++
      "window {0,2}; the two windows are DISTINCT and of the SAME cardinality 2, and gapData_injOn " ++
      "is DERIVED from gap-code faithfulness -- never the empty/singleton/different-cardinality " ++
      "shortcut.",
    "SHARPEST RESIDUAL (characterised) -- gapData_injOn is DERIVED from sym_injOn (clean-survivor " ++
      "gap-code faithfulness), the same irreducible atom on which path_injOn rests. That atom is the " ++
      "genuine irreducible heart (geometry-free CNLTransition cannot determine the window; the " ++
      "manuscript supplies it via L.1.2a-c 'recover the transition up to O_Q(1)', sharpened to the " ++
      "clean subfamily). The G.7 compat remains a supplied hypothesis.",
    "SOURCE NOTE (reported, not applied) -- a UNIFORM-length clean window forces equal window " ++
      "cardinality, while the G.7 compat 2-adically SEPARATES the surviving shadow numerators (a + " ++
      "2^a <= b, twoAdic_separation); the manuscript reconciles these through DEPTH-VARYING window " ++
      "lengths r = r(k) (the reverse window of the depth-k transition), which the uniform " ++
      "CleanClusterReconstruction.M does not model. A source enrichment exposing r(k) per transition " ++
      "would make GapLiftCluster.ofCleanReconstruction fire with a compat-feasible distinct-window " ++
      "family. Also: selectedTransitions keeps every nonempty-available transition; the L.1.1 " ++
      "per-class removal of SEP/VS/DS/PKG is upstream and is reflected in the supplied faithfulness.",
    "WAVE-20 (closed via structural enrichment) -- CNLGapWindowEnrichCore makes window-distinctness a " ++
      "STRUCTURAL consequence of a faithful coordinate, no longer an assumed code-faithfulness: " ++
      "GapWindowDatum.window_injective proves the reverse partial-sum window is a faithful coordinate " ++
      "of the clean gap code (the proved G.4 slide), so the window readout is injective BY " ++
      "CONSTRUCTION and gapData_injOn is DERIVED (gapDataInjOn_ofWindowData) the moment the slide-map " ++
      "reconstruction is a retraction recover (datumOf t) = t -- a RECONSTRUCTION statement equivalent " ++
      "to this sym_injOn / gapDataInjOn_iff_exists_decode atom, presented structurally. The " ++
      "depth-varying window length r = r(k) flagged in the SOURCE NOTE above is now modelled PER " ++
      "ELEMENT by GapWindowDatum.r, resolving the wave-19 uniform-length-vs-G.7-2-adic-separation " ++
      "tension; for the concrete family the retraction is a definitional rfl. The remaining future " ++
      "refactor -- enriching CNLTransition with a GapWindowDatum field to make gapData_injOn fully " ++
      "primitive-closed -- is FLAGGED, not applied here.",
    "WAVE-21 (the standing decode retraction is now DISCHARGED for the ACTUAL family) -- " ++
      "CNLGapFaithfulCore.recoverFromDatum_carryDatum proves recover (datumOf t) = t for EVERY " ++
      "transition, so the wave-20 standing input (equivalently this sym_injOn / " ++
      "gapDataInjOn_iff_exists_decode atom) is discharged for the actual surviving family " ++
      "selectedTransitions (liftTransitionsOfShell ctx): gapData_injOn (liftTransitions_gapDataInjOn) " ++
      "and exp_injOn (liftTransitions_expInjOn) hold with ONLY the G.7 compat supplied. FIDELITY " ++
      "CAVEAT: CNLTransition is a TWO-RESIDUE summary, so a literal full gap-code field " ++
      "gapCode : Nat -> Nat would break Fintype CNLTransition (used by the Kraft counts); the clean " ++
      "manuscript-fidelity path is a SEPARATE enriched CNLGapTransition type at the gap-cluster layer, " ++
      "NOT a field on CNLTransition." ]

theorem cnlClassifierDistinctCoreResiduals_nonempty : cnlClassifierDistinctCoreResiduals ≠ [] := by
  simp [cnlClassifierDistinctCoreResiduals]

/-! ## Part 7.  Axiom-cleanliness audit -/

#print axioms gapDataInjOn_iff_pairwiseDistinct
#print axioms gapDataInjOn_iff_setInjOn
#print axioms gapDataInjOn_iff_exists_decode
#print axioms gapDataInjOn_of_gapCode_injOn
#print axioms gapDataInjOn_ofReconstruction
#print axioms GapLiftCluster.ofCleanReconstruction
#print axioms exp_injOn_ofCleanReconstruction
#print axioms gapDataInjOn_not_automatic
#print axioms exGapDataInjOn
#print axioms exGapWindow_distinct
#print axioms exGap_selected_two
#print axioms cnlClassifierDistinctCoreResiduals_nonempty

end Erdos260
