import Mathlib
import Erdos260.AppendixN
import Erdos260.AppendixN_Variation
import Erdos260.StoppedTree
import Erdos260.AppendixL

/-!
# C1-VD assembly: Theorem `thm:trt-chain-compression` (Phase E)

This module assembles the manuscript's top-level C1-VD closure theorem
`thm:trt-chain-compression` (`proof_v4.tex` lines 287–376) from the three
Appendix-N pillars, each proved in the sibling modules (this file does **not**
re-prove N.3; the terminal-compression lemmas N.3.1–N.3.3 live in
`Erdos260.AppendixN`):

* **N.1.3** same-event-fibre live chains terminate
  (`EventFibre.liveChainTerminates`, `Erdos260.AppendixN`);
* **N.2.2** the window-drop estimate `VarDrop ≤ C_Q·Y·V_s`
  (`WindowDropEstimateData.bound`, `Erdos260.AppendixN_Variation`);
* **N.3.1** the fixed terminal-output compression `∑_b wt_O(b) ≤ C_Q·wt(O)`
  (`TerminalOutputData.compression`, `Erdos260.AppendixN`).

It then records the closure bridge `trtClosure_outputMass_absorbed` /
`trtClosure_variationDropMass_absorbed` /
`trtClosure_tableRouted_absorbed` (eq. N.24 / 2.3b): the composed
same-threshold TRT output mass splits into the five-class absorbed terminal mass
(Lemma N.3.3, `AppendixN.aggregateAbsorption`) plus the separately-vanishing
variation-drop mass `𝔒_V` — the shape consumed by the `highExcessCharge` /
`ledger` providers, so no independent terminal-TRT summand and no same-layer
circularity survive into the global recurrence (I.9).

No `sorry`, `axiom`, or `admit`.
-/

namespace Erdos260
namespace AppendixN

open MeasureTheory Finset

noncomputable section

/-! ## Proof of Theorem `thm:trt-chain-compression` (Phase E) -/

/--
**Theorem `thm:trt-chain-compression` (C1-VD closure), packaged form.**

Combining the three pillars of Appendix N gives the three conclusions of the
manuscript theorem (statement, lines 287–376):

1. **Live same-event-fibre continuation (2.3r).**  Every live same-threshold
   reinsertion chain terminates after `≤ |𝔗_T(b₀)|` steps (Lemma N.1.3,
   `AppendixN`), because the scalar address strictly decreases at every live
   hand-off (Lemma N.1.2).
2. **Window-drop termination (2.3v).**  The variation-drop mass satisfies
   `VarDrop ≤ C_Q·Y·V_s` (Lemma N.2.2, `AppendixN_Variation`).
3. **Fibrewise terminal compression (2.3b).**  `∑_b wt_O(b) ≤ C_Q·wt(O)`
   (Lemma N.3.1, `AppendixN.TerminalOutputData.compression`).

Consequently Return–Run–Tower chains create neither same-layer circularity nor
multiplicative `C^{J_X(s)}`, linear `J_X(s)`, or chain-length losses.
-/
theorem theorem_trtChainCompression
    {σ ι β : Type*} [DecidableEq σ] [LinearOrder ι]
    (E : EventFibre σ ι)
    (drop : WindowDropEstimateData)
    (comp : TerminalOutputData β σ) :
    (∀ (Ξ : Nat → Finset σ) (n : Nat),
        (∀ i < n, E.LiveStep (Ξ i) (Ξ (i + 1))) → n ≤ E.atoms.card) ∧
    (drop.varDrop ≤ drop.CQ * drop.Y * Vs drop.K drop.W) ∧
    (∑ b ∈ comp.branches, comp.wtO b
        ≤ comp.CQ * (comp.YO * ∑ ζ ∈ comp.ground, comp.fibreMass ζ)) :=
  ⟨fun Ξ n h => E.liveChainTerminates Ξ n h, drop.bound, comp.compression⟩

/--
**Closure bridge (eq. N.24 / 2.3b → global recurrence).**

The composed same-threshold TRT output mass splits into the terminal non-drop
mass — absorbed into the existing five output classes `𝔒_D/P/E/CNL/bdd` by the
aggregate absorption N.3.3 — plus the variation-drop mass `𝔒_V`, bounded by the
window-drop estimate N.2.2.  Hence the total output mass inherits an absorbed
bound plus a separately-vanishing drop term, exactly the shape consumed by the
`highExcessCharge`/`ledger` providers: no independent terminal-TRT summand and
no same-layer circularity survive into the global recurrence (I.9).
-/
theorem trtClosure_outputMass_absorbed
    {totalMass termMass varMass absorbedBound windowBound : ℝ}
    (hsplit : totalMass = termMass + varMass)
    (hterm : termMass ≤ absorbedBound)
    (hvar : varMass ≤ windowBound) :
    totalMass ≤ absorbedBound + windowBound := by
  rw [hsplit]; linarith

/--
**Closure bridge from the bundled N.2.2 input.**

This is the N.24 bridge in the form used by the structured
`thm:trt-chain-compression` interface: once the C1-VD split identifies the
variation-drop summand with `drop.varDrop`, the `WindowDropEstimateData` bundle
supplies the window-drop term directly.
-/
theorem trtClosure_windowDropEstimate_absorbed
    (drop : WindowDropEstimateData)
    {totalMass termMass absorbedBound : ℝ}
    (hsplit : totalMass = termMass + drop.varDrop)
    (hterm : termMass ≤ absorbedBound) :
    totalMass ≤ absorbedBound + drop.CQ * drop.Y * Vs drop.K drop.W :=
  trtClosure_outputMass_absorbed hsplit hterm drop.bound

/--
**Closure bridge from scaled drop-density data.**

This composes the N.2.2 scaled drop-density constructor with the N.24 split:
the residual multiplier and the fixed-threshold multiplicity constant are
absorbed into the product constant before the variation-drop term is added to the
terminal absorbed mass.
-/
theorem trtClosure_scaledDropDensity_absorbed
    (VarDrop Cmul Cfiber Y : ℝ) (dropDensity : ℝ → ℝ)
    (W : ℕ → ℝ) (K : Finset ℕ) (A : Set ℝ)
    {totalMass termMass absorbedBound : ℝ}
    (hsplit : totalMass = termMass + VarDrop)
    (hterm : termMass ≤ absorbedBound)
    (hCmulY : 0 ≤ Cmul * Y)
    (hCfiber : 0 ≤ Cfiber)
    (hA : MeasurableSet A)
    (hdrop_int : IntegrableOn dropDensity A volume)
    (hvar :
      VarDrop ≤ Cmul * Y * ∫ T in A, dropDensity T ∂volume)
    (hpoint :
      ∀ T ∈ A, dropDensity T ≤ Cfiber * crossingCountReal (T + Y) W K) :
    totalMass ≤ absorbedBound + (Cmul * Cfiber) * Y * Vs K W :=
  trtClosure_windowDropEstimate_absorbed
    (WindowDropEstimateData.ofScaledDropDensityBound VarDrop Cmul Cfiber Y
      dropDensity W K A hCmulY hCfiber hA hdrop_int hvar hpoint)
    hsplit hterm

/--
**Closure bridge, ledger form (eq. N.24 / 2.3b).**

Specialized to the Phase-A `Ledger.variationDropMass` interface: if the total
composed-TRT output mass is the absorbed terminal mass plus the variation-drop
ledger mass, then it is bounded by the absorbed package bound plus the
window-drop estimate `C_Q·Y·V_s`. -/
theorem trtClosure_variationDropMass_absorbed
    (objects : Finset OutputObjectV4) (weight : OutputObjectV4 → ℝ)
    {totalMass termMass absorbedBound CQ Y : ℝ} (W : ℕ → ℝ) (K : Finset ℕ) (A : Set ℝ)
    (hsplit : totalMass = termMass + variationDropMass objects weight)
    (hterm : termMass ≤ absorbedBound)
    (hCQY : 0 ≤ CQ * Y)
    (hvar : variationDropMass objects weight ≤
              CQ * Y * ∫ T in A, crossingCountReal (T + Y) W K ∂MeasureTheory.volume) :
    totalMass ≤ absorbedBound + CQ * Y * Vs K W := by
  have hvarVs : variationDropMass objects weight ≤ CQ * Y * Vs K W :=
    variationDropMass_le_Vs objects weight CQ Y W K A hCQY hvar
  rw [hsplit]; linarith

/--
**Closure bridge, table-routed no-drop form (N.1.0/N.5e → N.24).**

If the composed TRT output family is drawn from the terminal routing table, then
its variation-drop ledger mass is definitionally zero by
`EventFibre.variationDropMass_routedOutputs_eq_zero`.  Thus the closure bridge
needs only the terminal non-drop absorption bound; there is no independent
terminal-TRT or table-routed variation-drop summand left.
-/
theorem trtClosure_tableRouted_absorbed
    {sigma iota : Type*} [DecidableEq sigma] [LinearOrder iota]
    (E : EventFibre sigma iota)
    (row : iota → TerminalRow) (supp thr : iota → Nat)
    (weight : OutputObjectV4 → ℝ)
    {totalMass termMass absorbedBound : ℝ}
    (hsplit :
      totalMass =
        termMass +
          variationDropMass
            (E.atoms.image
              (fun omega =>
                OutputObjectV4.mk (row omega).outputClass (supp omega) (thr omega)))
            weight)
    (hterm : termMass ≤ absorbedBound) :
    totalMass ≤ absorbedBound := by
  have hzero := E.variationDropMass_routedOutputs_eq_zero row supp thr weight
  rw [hzero, add_zero] at hsplit
  rw [hsplit]
  exact hterm

end

end AppendixN
end Erdos260
