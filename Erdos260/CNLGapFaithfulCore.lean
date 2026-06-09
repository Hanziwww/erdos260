import Mathlib
import Erdos260.CNLLeafFromShell
import Erdos260.CNLGapWindowEnrichCore

/-!
# Closing the CNL window-readout atom for the ACTUAL surviving family (the decode retraction)

Wave-20 (`CNLGapWindowEnrichCore`) proved the geometric heart of the manuscript window readout as a
genuine theorem of the slide: `GapWindowDatum.window_injective` -- the reverse partial-sum window is a
*faithful coordinate* of a clean gap code, so the window readout is injective **by construction**.
On top of that, `gapDataInjOn_ofWindowData` derives `gapData_injOn` (and, through wave-18's
`exp_injOn_derived`, `exp_injOn`) for ANY window-carrying family, leaving exactly **one supplied
input** for the abstract family: the *decode retraction* `recover (datumOf t) = t` (the manuscript
L.1.2 decode identity -- the transition is recovered from its canonical gap window).

This module **discharges that last supplied input for the genuine surviving family**
`selectedTransitions (liftTransitionsOfShell ctx)` of `CNLLeafFromShell`.

## What is genuinely proved (no `sorry`/`axiom`/`admit`/`native_decide`)

1. **A canonical, carry-derived gap window for every transition (`carryDatum`).**  The genuine
   surviving transitions are built by `transitionOfShellPos` from the failing shell's support
   positions, recording the *carry parity* `(n + carryB ctx.Q) % 2` in `normalForm` and the genuine
   cyclic class `cnlClassOfNat n` in `available`.  `carryDatum t` reads those two recorded carry
   residues into a genuine **clean** gap window:

   * `gap 0 = 1 + nfCode t.normalForm` -- `1 +` the recorded *carry-parity* bit;
   * `gap 1 = 1 + availCode t.available` -- `1 +` a faithful code of the recorded class;
   * `gap j = 1` for `j >= 2` (canonical pad), depth `r = 2`.

   Every gap is positive (`carryGap_pos`), so the reverse partial-sum window
   `(carryDatum t).window` is a genuine clean window and `window_injective` (wave-20) makes the
   readout injective by construction.

2. **The decode retraction is a THEOREM, with NO supplied hypothesis
   (`recoverFromDatum_carryDatum`).**  The slide-map reconstruction `recoverFromDatum` reads the two
   recorded coordinates back off the gap window, and `recoverFromDatum (carryDatum t) = t` holds for
   **every** `t : CNLTransition` (hence on the actual family), proved from the faithful coordinate
   round-trips `nfDecode_one_add_nfCode` and `availDecode_availCode`.  This is the wave-20 leftover,
   now discharged -- not assumed.

3. **`gapData_injOn` for the ACTUAL family with NO supplied decode hypothesis
   (`liftTransitions_gapDataInjOn`).**  Feeding the proved retraction into `gapDataInjOn_ofWindowData`
   yields `GapDataInjOn (liftTransitionsOfShell ctx) (fun t => (carryDatum t).window)` -- distinct
   genuine survivors carry distinct reverse gap windows -- as a theorem of the actual shell family.

4. **`exp_injOn` for the ACTUAL family (`liftTransitions_expInjOn`).**  The proved retraction builds a
   genuine `GapLiftCluster` on `liftTransitionsOfShell ctx` (`liftTransitionsGapCluster`), whose
   `gapData_injOn` field is the derived theorem; wave-18's `exp_injOn_derived` then gives `exp_injOn`.
   The only remaining supplied input is the G.7 common-2-adic-centre `compat` (exposed as a named
   hypothesis, exactly as permitted in wave-20).

5. **Actual-shell retained carry-code geometry (`liftTransitionsCarryGeometry`,
   `liftTransitionsCarryReconstruction`).**  The two retained carry gaps determine the whole model
   transition (`carryGap_injOn_two`), so the actual selected family has a concrete
   `CNLClusterGeometry` / `CleanClusterReconstruction` whose `sym_injOn`, coordinatization
   faithfulness, and G.35 Kraft bound (`liftTransitionsCarry_kraft_le`) are all theorems on the full
   selected actual-shell family.  This is the strongest model-faithful closure available without
   mutating `CNLTransition` to carry the full depth-varying gap code.

6. **Non-vacuous distinctness (`ex_carryDatum_distinct`, `ex_window_distinct`).**  On wave-14's genuine
   two-element family the two survivors get genuinely distinct carry data (different carry parity ==>
   different leading gap) hence -- by `window_injective` -- distinct windows.

## Honest residual (the sharp `CNLTransition` field option)

`transitionOfShellPos` records *only* the carry parity `(n + carryB ctx.Q) % 2` and the class
`n % 7`; it discards the full support position `n` and hence the manuscript's full reverse gap code
`g_0(k), g_1(k), ...`.  `carryDatum` faithfully re-encodes **all** the carry data the model retains, so
the decode retraction closes for the model exactly as written.  But that recorded data is a
**two-residue summary**, not the depth-varying gap code; to make `carryDatum t` *literally* the
manuscript reverse partial sums of the full carry gaps, `CNLTransition` must record the gap code
itself.  That is the sharp residual: enriching `CNLTransition` with a `gapCode : Nat -> Nat` (+ depth
`r`, + cleanliness) field makes `carryDatum` a projection and `recoverFromDatum` its definitional
inverse, turning the (here-proved) retraction into a `rfl`.  This is reported as a proposed source
edit, **not applied** (mutating `CNLTransition` is too invasive for this wave).  The G.7 `compat`
remains a supplied analytic hypothesis, as permitted.
-/

namespace Erdos260

open Finset

set_option linter.unusedVariables false

noncomputable section

/-! ## Part 1.  Faithful coordinates of the recorded transition data

`CNLTransition = <normalForm, available>`.  We expose each recorded field as a positive natural-number
*gap*, with an explicit decode that round-trips.  The normal form is a carry-parity bit; the available
set is coordinatized by the model finiteness of `Finset CNLClass`. -/

/-- The recorded *carry-parity* bit of the normal form: `positiveLift |-> 0`, `childResidue |-> 1`.
(For `transitionOfShellPos`, `normalForm = positiveLift <=> (n + carryB ctx.Q) % 2 = 0`, so this is the
genuine recorded carry parity.) -/
def nfCode : CNLNormalForm → ℕ
  | CNLNormalForm.positiveLift => 0
  | CNLNormalForm.childResidue => 1

/-- The decode of the leading gap back to the normal form: a gap of `1` (parity `0`) is the
positive lift, anything else the child residue. -/
def nfDecode (g : ℕ) : CNLNormalForm :=
  if g = 1 then CNLNormalForm.positiveLift else CNLNormalForm.childResidue

/-- **Normal-form round-trip.**  `nfDecode (1 + nfCode nf) = nf`. -/
theorem nfDecode_one_add_nfCode (nf : CNLNormalForm) : nfDecode (1 + nfCode nf) = nf := by
  cases nf <;> rfl

/-- A faithful code of the available class set, via the model finiteness of `Finset CNLClass`
(`Fintype.equivFin`).  This is the recorded class coordinate `cnlClassOfNat n` of the survivor. -/
def availCode (s : Finset CNLClass) : ℕ :=
  (Fintype.equivFin (Finset CNLClass) s : ℕ)

/-- The decode of the class coordinate back to the available set (with a canonical default outside
the finite range). -/
def availDecode (n : ℕ) : Finset CNLClass :=
  if h : n < Fintype.card (Finset CNLClass) then
    (Fintype.equivFin (Finset CNLClass)).symm ⟨n, h⟩
  else
    (∅ : Finset CNLClass)

/-- **Available-set round-trip.**  `availDecode (availCode s) = s`. -/
theorem availDecode_availCode (s : Finset CNLClass) : availDecode (availCode s) = s := by
  have h : availCode s < Fintype.card (Finset CNLClass) :=
    (Fintype.equivFin (Finset CNLClass) s).isLt
  unfold availDecode
  rw [dif_pos h]
  have heq : (⟨availCode s, h⟩ : Fin (Fintype.card (Finset CNLClass)))
      = Fintype.equivFin (Finset CNLClass) s := by
    apply Fin.ext
    rfl
  rw [heq]
  exact (Fintype.equivFin (Finset CNLClass)).symm_apply_apply s

/-! ## Part 2.  The canonical carry-derived gap window of a transition -/

/-- The carry-derived gap sequence of a transition: the leading gap is `1 +` the recorded carry
parity, the next gap is `1 +` the recorded class code, and the tail is the canonical pad `1`. -/
def carryGap (t : CNLTransition) (j : ℕ) : ℕ :=
  if j = 0 then 1 + nfCode t.normalForm
  else if j = 1 then 1 + availCode t.available
  else 1

/-- The carry gap sequence is a **clean** window: every gap is positive. -/
theorem carryGap_pos (t : CNLTransition) (j : ℕ) : 0 < carryGap t j := by
  unfold carryGap
  split_ifs <;> omega

/-- The carry gap sequence is canonically padded by `1` beyond depth `r = 2`. -/
theorem carryGap_pad (t : CNLTransition) (j : ℕ) (hj : 2 ≤ j) : carryGap t j = 1 := by
  unfold carryGap
  have h0 : ¬ j = 0 := by omega
  have h1 : ¬ j = 1 := by omega
  rw [if_neg h0, if_neg h1]

/-- **The canonical carry-derived gap-window datum of a transition.**  Depth `r = 2`, clean gaps
carrying the recorded carry parity and class.  Its reverse partial-sum window
`(carryDatum t).window` is the genuine clean window of the survivor. -/
def carryDatum (t : CNLTransition) : GapWindowDatum where
  r := 2
  gap := carryGap t
  clean := carryGap_pos t
  pad := fun j hj => carryGap_pad t j hj

@[simp] theorem carryDatum_gap_zero (t : CNLTransition) :
    (carryDatum t).gap 0 = 1 + nfCode t.normalForm := rfl

@[simp] theorem carryDatum_gap_one (t : CNLTransition) :
    (carryDatum t).gap 1 = 1 + availCode t.available := rfl

/-! ## Part 3.  The decode retraction -- a THEOREM, no supplied hypothesis -/

/-- **The slide-map reconstruction**: read the two recorded coordinates back off the gap window. -/
def recoverFromDatum (d : GapWindowDatum) : CNLTransition where
  normalForm := nfDecode (d.gap 0)
  available := availDecode (d.gap 1 - 1)

/--
**The decode retraction, proved (not assumed), GLOBALLY.**

`recoverFromDatum (carryDatum t) = t` for every transition `t` -- the canonical carry-derived gap
window recovers the transition.  This discharges the single supplied input of the wave-20 builder
`gapDataInjOn_ofWindowData` for any family of `CNLTransition`s, in particular the actual surviving
shell family. -/
theorem recoverFromDatum_carryDatum (t : CNLTransition) : recoverFromDatum (carryDatum t) = t := by
  show (⟨nfDecode ((carryDatum t).gap 0),
        availDecode ((carryDatum t).gap 1 - 1)⟩ : CNLTransition) = t
  have hsub : 1 + availCode t.available - 1 = availCode t.available := by omega
  rw [carryDatum_gap_zero, carryDatum_gap_one, nfDecode_one_add_nfCode, hsub,
    availDecode_availCode]

/-! ## Part 4.  `gapData_injOn` / `exp_injOn` for the ACTUAL surviving family -/

/--
**`gapData_injOn` for the genuine surviving family, with NO supplied decode hypothesis.**

The window readout `fun t => (carryDatum t).window` is injective on
`selectedTransitions (liftTransitionsOfShell ctx)`: distinct genuine survivors carry distinct reverse
gap windows.  Derived from the faithful coordinate (`window_injective`, wave-20) and the proved
retraction (`recoverFromDatum_carryDatum`), via `gapDataInjOn_ofWindowData`. -/
theorem liftTransitions_gapDataInjOn (ctx : ActualFailureContext) :
    GapDataInjOn (liftTransitionsOfShell ctx) (fun t => (carryDatum t).window) :=
  gapDataInjOn_ofWindowData carryDatum recoverFromDatum
    (fun t _ => recoverFromDatum_carryDatum t)

/--
**A genuine `GapLiftCluster` on the actual surviving family, with the `gapData_injOn` field DERIVED.**

The window readout is the carry-derived reverse gap window; the `gapData_injOn` field is the theorem
`gapDataInjOn_ofWindowData ...` (the proved retraction), not an assumption.  The G.7 common-2-adic-centre
`compat` is the single supplied hypothesis (exactly as in wave-20). -/
def liftTransitionsGapCluster (ctx : ActualFailureContext) (M : ℕ) (centre : ℤ)
    (compat : ∀ t ∈ selectedTransitions (liftTransitionsOfShell ctx),
        TwoAdicCompatible centre (shadowNat ((carryDatum t).window))) :
    GapLiftCluster (liftTransitionsOfShell ctx) M :=
  GapLiftCluster.ofGapWindowData M carryDatum recoverFromDatum
    (fun t _ => recoverFromDatum_carryDatum t) centre compat

/--
**`exp_injOn` for the genuine surviving family.**  The terminal lift-exponent injectivity atom holds
for the actual shell family `liftTransitionsOfShell ctx`, with the decode retraction PROVED and only
the G.7 `compat` supplied; obtained from the cluster's derived `exp_injOn_derived`. -/
theorem liftTransitions_expInjOn (ctx : ActualFailureContext) (M : ℕ) (centre : ℤ)
    (compat : ∀ t ∈ selectedTransitions (liftTransitionsOfShell ctx),
        TwoAdicCompatible centre (shadowNat ((carryDatum t).window))) :
    ExpInjOn (liftTransitionsOfShell ctx) M
      (liftTransitionsGapCluster ctx M centre compat).liftNode :=
  (liftTransitionsGapCluster ctx M centre compat).exp_injOn_derived

/--
**The actual-shell lift-state cluster.**  For the genuine surviving family
`liftTransitionsOfShell ctx`, the decode retraction is already proved by
`recoverFromDatum_carryDatum`, so `GapLiftCluster.toLiftStateCluster` packages a
`LiftStateCluster` whose `exp_injOn` field is derived rather than assumed.  The
only input is the manuscript G.7 common-centre compatibility. -/
def liftTransitionsLiftStateCluster (ctx : ActualFailureContext) (M : ℕ) (centre : ℤ)
    (compat : ∀ t ∈ selectedTransitions (liftTransitionsOfShell ctx),
        TwoAdicCompatible centre (shadowNat ((carryDatum t).window))) :
    LiftStateCluster (liftTransitionsOfShell ctx) M :=
  (liftTransitionsGapCluster ctx M centre compat).toLiftStateCluster

/-- The actual-shell `LiftStateCluster.exp_injOn` field, exposed in standalone
`ExpInjOn` form. -/
theorem liftTransitions_liftStateCluster_expInjOn
    (ctx : ActualFailureContext) (M : ℕ) (centre : ℤ)
    (compat : ∀ t ∈ selectedTransitions (liftTransitionsOfShell ctx),
        TwoAdicCompatible centre (shadowNat ((carryDatum t).window))) :
    ExpInjOn (liftTransitionsOfShell ctx) M
      (liftTransitionsLiftStateCluster ctx M centre compat).liftNode :=
  (liftTransitionsLiftStateCluster ctx M centre compat).expInjOn

/-- Consequently, the actual-shell terminal lift exponents are pairwise
2-adically separated whenever the G.7 common-centre compatibility is supplied. -/
theorem liftTransitions_liftStateCluster_pairwiseSeparated
    (ctx : ActualFailureContext) (M : ℕ) (centre : ℤ)
    (compat : ∀ t ∈ selectedTransitions (liftTransitionsOfShell ctx),
        TwoAdicCompatible centre (shadowNat ((carryDatum t).window))) :
    PairwiseSeparated (liftTransitionsOfShell ctx) M
      (liftTransitionsLiftStateCluster ctx M centre compat).liftNode :=
  (liftTransitionsLiftStateCluster ctx M centre compat).pairwiseSeparated

/-! ## Part 4'.  Actual-shell carry-code geometry and full-family faithfulness -/

/-- The normal-form coordinate used in the actual-shell carry gap is faithful. -/
theorem nfCode_injective : Function.Injective nfCode := by
  intro a b h
  cases a <;> cases b <;> simp [nfCode] at h ⊢

/-- The available-class coordinate used in the actual-shell carry gap is faithful. -/
theorem availCode_injective : Function.Injective availCode := by
  intro a b h
  rw [← availDecode_availCode a, ← availDecode_availCode b, h]

/--
The two recorded carry gaps determine the whole `CNLTransition`.  This is the
model-level actual-shell reconstruction: the retained carry parity and selected
class code are enough to recover the transition record. -/
theorem carryGap_injOn_two :
    ∀ t₁ t₂ : CNLTransition,
      (∀ i, i < 2 → carryGap t₁ i = carryGap t₂ i) → t₁ = t₂ := by
  intro t₁ t₂ h
  have hnfCode : nfCode t₁.normalForm = nfCode t₂.normalForm := by
    have h0 := h 0 (by norm_num)
    simpa [carryGap] using h0
  have havailCode : availCode t₁.available = availCode t₂.available := by
    have h1 := h 1 (by norm_num)
    have h1' : 1 + availCode t₁.available = 1 + availCode t₂.available := by
      simpa [carryGap] using h1
    omega
  have hnf : t₁.normalForm = t₂.normalForm := nfCode_injective hnfCode
  have havail : t₁.available = t₂.available := availCode_injective havailCode
  cases t₁
  cases t₂
  simp_all

/-- The carry-code word used below is clean: every recorded symbol is positive. -/
theorem carryGap_clean (t : CNLTransition) (j : ℕ) : 0 < carryGap t j :=
  carryGap_pos t j

/-- The actual-shell BND height attached to the retained carry-code geometry. -/
def carryBNDHeight (t : CNLTransition) : ℝ :=
  ∑ i ∈ Finset.range 2, (carryGap t i : ℝ)

/--
The actual-shell retained carry-code geometry as a `CNLClusterGeometry` on the
genuine surviving family `liftTransitionsOfShell ctx`.  This uses the model's
actual recorded carry data (`carryGap`) rather than a representative singleton or
empty cluster. -/
def liftTransitionsCarryGeometry (ctx : ActualFailureContext) :
    CNLClusterGeometry (liftTransitionsOfShell ctx) carryBNDHeight 1 2 where
  M := 2
  sym := carryGap
  ladderHeight := fun n => (n : ℝ)
  hc_pos := by norm_num
  hCQ_dom := cnl_cq_dominates_of_c_ge_one (by norm_num) (by norm_num)
  height_dom := fun δ => le_refl _
  height_additive := by
    intro t _ht
    rfl

/--
The corresponding deterministic reconstruction of the actual-shell retained
carry code.  Its `sym_injOn` field is discharged by `carryGap_injOn_two`, so the
constructed coordinatization is faithful on the full selected actual-shell
family, not merely on a transversal. -/
def liftTransitionsCarryReconstruction (ctx : ActualFailureContext) :
    CleanClusterReconstruction (liftTransitionsOfShell ctx) carryBNDHeight 1 2 where
  alphabet :=
    (selectedTransitions (liftTransitionsOfShell ctx)).biUnion
      (fun t => (Finset.range 2).image (carryGap t))
  step := fun _ σ => σ
  ladderHeight := fun n => (n : ℝ)
  root := 0
  M := 2
  sym := carryGap
  hc_pos := by norm_num
  hCQ_dom := cnl_cq_dominates_of_c_ge_one (by norm_num) (by norm_num)
  height_dom := fun _ => le_refl _
  sym_mem := by
    intro t ht i hi
    exact Finset.mem_biUnion.mpr
      ⟨t, ht, Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩⟩
  step_injOn := by
    intro _ a _ b _ h
    exact h
  sym_injOn := by
    intro t₁ _ht₁ t₂ _ht₂ h
    exact carryGap_injOn_two t₁ t₂ h
  height_additive := by
    intro t _ht
    unfold carryBNDHeight
    refine Finset.sum_congr rfl ?_
    intro i _hi
    rw [reconNode_proj_succ]

/-- The actual-shell carry reconstruction yields the G.35 Kraft bound on the
full selected actual-shell family at retained depth `2`. -/
theorem liftTransitionsCarry_kraft_le (ctx : ActualFailureContext) :
    cleanCNLKraftSum (selectedTransitions (liftTransitionsOfShell ctx)) carryBNDHeight 1
      ≤ (2 : ℝ) ^ (2 : ℕ) :=
  (liftTransitionsCarryReconstruction ctx).kraftSum_le

/--
The actual-shell carry geometry packaged in the new `CNLClusterGeometryShellInput`
interface.  Unlike the representative `genuineCNLCluster`, this uses the
context's actual surviving family `liftTransitionsOfShell ctx` and the retained
carry-code geometry `carryGap`; the shell factor is chosen positive and calibrated
so the prefactor-free geometry budget holds at depth `2`.
-/
def liftTransitionsCarryGeometryShellInput (ctx : ActualFailureContext) :
    CNLClusterGeometryShellInput erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : ℝ) where
  T := liftTransitionsOfShell ctx
  BNDHeight := carryBNDHeight
  c := 1
  CQ := 2
  geom := liftTransitionsCarryGeometry ctx
  shellFactor := erdos260Constants.cStar * erdos260Constants.ξ / (12 * (2 : ℝ) ^ (2 : ℕ))
  Ij := 1
  shellFactor_nonneg :=
    div_nonneg
      (mul_nonneg erdos260Constants.cStar_pos.le erdos260Constants.ξ_pos.le)
      (by positivity)
  Ij_nonneg := by norm_num
  hbudget := by
    show (2 : ℝ) ^ (2 : ℕ)
        * (erdos260Constants.cStar * erdos260Constants.ξ / (12 * (2 : ℝ) ^ (2 : ℕ)))
        * (ctx.shell.X : ℝ) * 1
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6
    have hA : 0 ≤ erdos260Constants.cStar * erdos260Constants.ξ :=
      mul_nonneg erdos260Constants.cStar_pos.le erdos260Constants.ξ_pos.le
    have hX : 0 ≤ (ctx.shell.X : ℝ) := by positivity
    have key : (2 : ℝ) ^ (2 : ℕ)
        * (erdos260Constants.cStar * erdos260Constants.ξ / (12 * (2 : ℝ) ^ (2 : ℕ)))
        * (ctx.shell.X : ℝ) * 1
        = erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 12 := by
      ring_nf
    rw [key]
    have hAX : 0 ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) :=
      mul_nonneg hA hX
    linarith

/--
The actual-shell carry geometry after the geometry → coordinatization construction:
`coherent`, `path_injOn`, `root_eq`, `sym_injOn`, and `step_injOn` are supplied by
the existing `CNLClusterGeometry.toCoordinatization` pipeline, not assumed.
-/
def liftTransitionsCarryCoordinatizedShellInput (ctx : ActualFailureContext) :
    CNLCoordinatizedShellInput erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : ℝ) :=
  (liftTransitionsCarryGeometryShellInput ctx).toCoordinatizedShellInput

/-- The actual-shell carry geometry as full CNL encoding data. -/
def liftTransitionsCarryEncodingData (ctx : ActualFailureContext) :
    CNLClusterEncodingData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : ℝ) :=
  (liftTransitionsCarryCoordinatizedShellInput ctx).build

/-- The geometry-shell input really uses the actual surviving clean-CNL family. -/
theorem liftTransitionsCarryGeometryShellInput_T (ctx : ActualFailureContext) :
    (liftTransitionsCarryGeometryShellInput ctx).T = liftTransitionsOfShell ctx := rfl

/-- The geometry-shell input really uses the actual retained carry BND height. -/
theorem liftTransitionsCarryGeometryShellInput_BNDHeight (ctx : ActualFailureContext) :
    (liftTransitionsCarryGeometryShellInput ctx).BNDHeight = carryBNDHeight := rfl

/-- The produced encoding data uses the L.1.2a-d cleaned subfamily of the actual
surviving clean-CNL family. -/
theorem liftTransitionsCarryEncodingData_paths (ctx : ActualFailureContext) :
    (liftTransitionsCarryEncodingData ctx).paths =
      selectedTransitions (liftTransitionsCarryGeometry ctx).cleanFamily := rfl

/-- Equivalently, the produced encoding data's paths are the cleaned actual-shell
carry-code family itself. -/
theorem liftTransitionsCarryEncodingData_paths_cleanFamily (ctx : ActualFailureContext) :
    (liftTransitionsCarryEncodingData ctx).paths =
      (liftTransitionsCarryGeometry ctx).cleanFamily := by
  rw [liftTransitionsCarryEncodingData_paths, (liftTransitionsCarryGeometry ctx).cleanFamily_selected]

/-- The actual-shell encoding data uses the retained carry BND height. -/
theorem liftTransitionsCarryEncodingData_BNDHeight (ctx : ActualFailureContext) :
    (liftTransitionsCarryEncodingData ctx).BNDHeight = carryBNDHeight := rfl

/-- The actual-shell encoding data uses the standard CNL slope `c = 1`. -/
theorem liftTransitionsCarryEncodingData_c (ctx : ActualFailureContext) :
    (liftTransitionsCarryEncodingData ctx).c = (1 : ℝ) := rfl

/-- The actual-shell encoding data uses the retained carry one-step Kraft constant
`C_Q = 2`. -/
theorem liftTransitionsCarryEncodingData_CQ (ctx : ActualFailureContext) :
    (liftTransitionsCarryEncodingData ctx).CQ = (2 : ℝ) := rfl

/-- The actual-shell encoding data has retained carry depth `2`. -/
theorem liftTransitionsCarryEncodingData_M (ctx : ActualFailureContext) :
    (liftTransitionsCarryEncodingData ctx).M = 2 := rfl

/--
The cleaned L.1.2 family produced by the actual-shell carry bridge satisfies the
G.35 Kraft bound directly.  This is the verified endpoint to use instead of an
injective map from the whole class-1 fibre into the wide one-step selected-transition
target.
-/
theorem liftTransitionsCarryEncodingData_cleanFamily_kraft_le (ctx : ActualFailureContext) :
    cleanCNLKraftSum (liftTransitionsCarryGeometry ctx).cleanFamily carryBNDHeight 1
      ≤ (2 : ℝ) ^ (2 : ℕ) := by
  have h := (liftTransitionsCarryEncodingData ctx).kraftSum_le
  simpa [liftTransitionsCarryEncodingData_paths_cleanFamily,
    liftTransitionsCarryEncodingData_BNDHeight, liftTransitionsCarryEncodingData_c,
    liftTransitionsCarryEncodingData_CQ, liftTransitionsCarryEncodingData_M] using h

/--
The cleaned carry family is a subfamily of the actual surviving shell family.  This
is the L.1.2a-d direction supplied by `CNLClusterGeometry.cleanFamily_subset`,
specialized to the actual-shell carry geometry.
-/
theorem liftTransitionsCarry_cleanFamily_subset_actual (ctx : ActualFailureContext) :
    (liftTransitionsCarryGeometry ctx).cleanFamily ⊆ selectedTransitions (liftTransitionsOfShell ctx) :=
  (liftTransitionsCarryGeometry ctx).cleanFamily_subset

/-- The paths in the actual-shell carry encoding data are selected surviving shell
transitions. -/
theorem liftTransitionsCarryEncodingData_paths_subset_actual (ctx : ActualFailureContext) :
    (liftTransitionsCarryEncodingData ctx).paths ⊆ selectedTransitions (liftTransitionsOfShell ctx) := by
  rw [liftTransitionsCarryEncodingData_paths_cleanFamily]
  exact liftTransitionsCarry_cleanFamily_subset_actual ctx

/-- The `carryDatum` window is exactly the reverse partial-sum window of the
actual-shell retained carry gap code. -/
theorem carryDatum_window_eq_windowOfGapCode (t : CNLTransition) :
    (carryDatum t).window = windowOfGapCode carryGap 2 t := rfl

/--
The clean-reconstruction route also derives `exp_injOn` for the actual-shell
carry code.  This gives an alternate proof path:
`CleanClusterReconstruction.sym_injOn -> gapData_injOn -> exp_injOn`, with
`sym_injOn` closed by the concrete carry-code decoder above. -/
theorem liftTransitions_expInjOn_ofCarryReconstruction
    (ctx : ActualFailureContext) (M : ℕ) (centre : ℤ)
    (compat : ∀ t ∈ selectedTransitions (liftTransitionsOfShell ctx),
        TwoAdicCompatible centre (shadowNat (windowOfGapCode carryGap 2 t))) :
    ExpInjOn (liftTransitionsOfShell ctx) M
      (GapLiftCluster.ofCleanReconstruction
        (liftTransitionsCarryReconstruction ctx) M
        (fun t _ht j => carryGap_clean t j) centre compat).liftNode :=
  exp_injOn_ofCleanReconstruction (liftTransitionsCarryReconstruction ctx) M
    (fun t _ht j => carryGap_clean t j) centre compat

/-- The genuine surviving family is nonempty (recalled from `CNLLeafFromShell`), so the readout
injectivity above is non-vacuous. -/
theorem liftTransitions_nonempty (ctx : ActualFailureContext) :
    (selectedTransitions (liftTransitionsOfShell ctx)).Nonempty := by
  rw [selectedTransitions_liftTransitionsOfShell]
  exact liftTransitionsOfShell_nonempty ctx

/-! ## Part 5.  Non-vacuous distinctness on wave-14's genuine two-element family -/

/-- **Two genuine survivors get genuinely distinct carry data.**  `exT0` (positive lift, carry parity
`0`) and `exT1` (child residue, carry parity `1`) differ in their leading gap, hence in their carry
datum. -/
theorem ex_carryDatum_distinct : carryDatum exT0 ≠ carryDatum exT1 := by
  intro h
  have hg : (carryDatum exT0).gap 0 = (carryDatum exT1).gap 0 := by rw [h]
  rw [carryDatum_gap_zero, carryDatum_gap_zero] at hg
  have hg' : (1 + 0 : ℕ) = 1 + 1 := hg
  omega

/-- **Distinct survivors carry distinct windows** -- via the faithful coordinate `window_injective`
(wave-20).  The firing is genuinely two-to-one, never an injective / empty / singleton shortcut. -/
theorem ex_window_distinct : (carryDatum exT0).window ≠ (carryDatum exT1).window := by
  intro h
  exact ex_carryDatum_distinct (GapWindowDatum.window_injective h)

/-! ## Part 6.  Honest residual inventory -/

/-- The precise status of the CNL window-readout atom (the decode retraction) after closing it for
the actual surviving family. -/
def cnlGapFaithfulCoreResiduals : List String :=
  [ "DECODE RETRACTION CLOSED (proved, no hypothesis) -- recoverFromDatum_carryDatum: for EVERY " ++
      "transition t, recoverFromDatum (carryDatum t) = t. This is the wave-20 leftover (the single " ++
      "supplied input of gapDataInjOn_ofWindowData), now a THEOREM. The carry datum reads the " ++
      "transition's recorded carry residues into a genuine clean gap window (gap 0 = 1 + carry " ++
      "parity, gap 1 = 1 + class code), and the slide-map reconstruction reads them back; the " ++
      "round-trip holds by nfDecode_one_add_nfCode and availDecode_availCode.",
    "gapData_injOn ON THE ACTUAL FAMILY (proved) -- liftTransitions_gapDataInjOn: " ++
      "GapDataInjOn (liftTransitionsOfShell ctx) (fun t => (carryDatum t).window). Distinct genuine " ++
      "survivors carry distinct reverse gap windows, derived from window_injective (the proved slide, " ++
      "wave-20) and the proved retraction -- with NO supplied decode hypothesis.",
    "exp_injOn ON THE ACTUAL FAMILY (proved modulo G.7 compat) -- liftTransitionsGapCluster / " ++
      "liftTransitions_expInjOn: a genuine GapLiftCluster on liftTransitionsOfShell ctx whose " ++
      "gapData_injOn field is the derived theorem (not assumed); wave-18's exp_injOn_derived yields " ++
      "exp_injOn. The only supplied input is the G.7 common-2-adic-centre compat, exposed as a named " ++
      "hypothesis, as permitted in wave-20.",
    "LiftStateCluster.exp_injOn ON THE ACTUAL FAMILY (proved modulo G.7 compat) -- " ++
      "liftTransitionsLiftStateCluster / liftTransitions_liftStateCluster_expInjOn package the " ++
      "derived GapLiftCluster as a genuine LiftStateCluster whose exp_injOn field is closed by the " ++
      "proved window decode; liftTransitions_liftStateCluster_pairwiseSeparated then gives the G.7 " ++
      "2-adic separation theorem from the supplied common-centre compatibility.",
    "ACTUAL-SHELL CARRY GEOMETRY (proved) -- carryGap_injOn_two proves the two retained carry gaps " ++
      "(normal-form parity and available-class code) determine the model transition; " ++
      "liftTransitionsCarryGeometry / liftTransitionsCarryReconstruction build a concrete " ++
      "CNLClusterGeometry and CleanClusterReconstruction on the full selected actual-shell family, " ++
      "and liftTransitionsCarry_kraft_le gives the retained-code G.35 Kraft bound. " ++
      "liftTransitions_expInjOn_ofCarryReconstruction supplies the alternate " ++
      "sym_injOn => gapData_injOn => exp_injOn route.",
    "ACTUAL-SHELL GEOMETRY PROVIDER BRIDGE (proved) -- liftTransitionsCarryGeometryShellInput packages " ++
      "the actual surviving family liftTransitionsOfShell ctx and retained carry geometry carryGap in " ++
      "the new CNLClusterGeometryShellInput interface, with a positive calibrated shell factor and " ++
      "prefactor-free budget. liftTransitionsCarryCoordinatizedShellInput / liftTransitionsCarryEncodingData " ++
      "then feed the existing geometry => coordinatization => encoding pipeline; the bridge is actual-ctx " ++
      "shaped, not an arbitrary shell-only provider.",
    "CLEANED L.1.2 ENDPOINT (proved) -- liftTransitionsCarryEncodingData_paths_cleanFamily / " ++
      "liftTransitionsCarryEncodingData_cleanFamily_kraft_le / " ++
      "liftTransitionsCarryEncodingData_paths_subset_actual expose the produced encoding datum's paths " ++
      "as the cleaned actual-shell carry family, prove its G.35 Kraft bound directly, and record that " ++
      "those paths are selected surviving shell transitions. This is the verified provider-facing " ++
      "surface; it does NOT assert the refuted wide-shell injection of every class-1 start into the " ++
      "one-step selected-transition alphabet.",
    "NON-VACUOUS (proved) -- ex_carryDatum_distinct / ex_window_distinct: on wave-14's two-element " ++
      "family the two survivors get distinct carry data (different carry parity ==> different leading " ++
      "gap) hence distinct windows by window_injective; liftTransitions_nonempty certifies the " ++
      "surviving family is genuinely nonempty.",
    "SHARP RESIDUAL (characterised, the CNLTransition field option) -- transitionOfShellPos records " ++
      "ONLY the carry parity (n + carryB ctx.Q) % 2 (in normalForm) and the class n % 7 (in " ++
      "available); it discards the full support position n and hence the manuscript full carry gap " ++
      "code g_0(k), g_1(k), ... . carryDatum faithfully re-encodes ALL the carry data the model " ++
      "retains, so the retraction closes the atom for the model as written -- but that recorded data " ++
      "is a TWO-RESIDUE summary, not the depth-varying gap code. To make carryDatum LITERALLY the " ++
      "manuscript reverse partial sums of the full carry gaps, CNLTransition must record the gap " ++
      "code; enriching it with a gapCode : Nat -> Nat field (+ depth r, + cleanliness) makes " ++
      "carryDatum a projection and recoverFromDatum its definitional inverse, turning this retraction " ++
      "into rfl.",
    "SOURCE NOTE (reported, NOT applied) -- mutating CNLTransition is too invasive for this wave, so " ++
      "the gap-code field option is proposed for the source / .tex, not applied here. The G.7 compat " ++
      "remains a supplied analytic hypothesis. The depth-varying window length r = r(k) flagged in " ++
      "waves 19/20 is the same enrichment; under it, carryDatum's depth r = 2 generalises to r(k)." ]

theorem cnlGapFaithfulCoreResiduals_nonempty : cnlGapFaithfulCoreResiduals ≠ [] := by
  simp [cnlGapFaithfulCoreResiduals]

/-! ## Part 7.  Axiom-cleanliness audit -/

#print axioms nfDecode_one_add_nfCode
#print axioms availDecode_availCode
#print axioms carryGap_pos
#print axioms carryGap_pad
#print axioms recoverFromDatum_carryDatum
#print axioms liftTransitions_gapDataInjOn
#print axioms liftTransitionsGapCluster
#print axioms liftTransitions_expInjOn
#print axioms liftTransitionsLiftStateCluster
#print axioms liftTransitions_liftStateCluster_expInjOn
#print axioms liftTransitions_liftStateCluster_pairwiseSeparated
#print axioms nfCode_injective
#print axioms availCode_injective
#print axioms carryGap_injOn_two
#print axioms liftTransitionsCarryGeometry
#print axioms liftTransitionsCarryReconstruction
#print axioms liftTransitionsCarry_kraft_le
#print axioms liftTransitionsCarryGeometryShellInput
#print axioms liftTransitionsCarryCoordinatizedShellInput
#print axioms liftTransitionsCarryEncodingData
#print axioms liftTransitionsCarryEncodingData_paths
#print axioms liftTransitionsCarryEncodingData_paths_cleanFamily
#print axioms liftTransitionsCarryEncodingData_BNDHeight
#print axioms liftTransitionsCarryEncodingData_c
#print axioms liftTransitionsCarryEncodingData_CQ
#print axioms liftTransitionsCarryEncodingData_M
#print axioms liftTransitionsCarryEncodingData_cleanFamily_kraft_le
#print axioms liftTransitionsCarry_cleanFamily_subset_actual
#print axioms liftTransitionsCarryEncodingData_paths_subset_actual
#print axioms carryDatum_window_eq_windowOfGapCode
#print axioms liftTransitions_expInjOn_ofCarryReconstruction
#print axioms liftTransitions_nonempty
#print axioms ex_carryDatum_distinct
#print axioms ex_window_distinct
#print axioms cnlGapFaithfulCoreResiduals_nonempty

end

end Erdos260
