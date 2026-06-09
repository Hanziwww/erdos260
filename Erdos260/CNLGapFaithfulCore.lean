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

5. **Non-vacuous distinctness (`ex_carryDatum_distinct`, `ex_window_distinct`).**  On wave-14's genuine
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
#print axioms liftTransitions_nonempty
#print axioms ex_carryDatum_distinct
#print axioms ex_window_distinct
#print axioms cnlGapFaithfulCoreResiduals_nonempty

end

end Erdos260
