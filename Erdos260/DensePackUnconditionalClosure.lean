import Mathlib
import Erdos260.UnconditionalAssemblyFinal3
import Erdos260.ShellRegimeClosure
import Erdos260.DensePackFactoryConstruction
import Erdos260.GlobalDensePackAssembly
import Erdos260.GlobalClosureAssembly

/-!
# Genuine in-regime DensePack closure for above-threshold failing shells

The capstone `Erdos260.UnconditionalAssemblyFinal3` consumes a per-shell
`densePackRegime : ∀ shell, shell.cQ = … → DensePackRegimeInput shell` field, where
(`Erdos260.DensePackFactoryConstruction`)

```
DensePackRegimeInput shell :=
  PLift (shell.c0 ≤ manuscriptKappa/16 ∧ carryB shell.Q + 25 ≤ Classical.choose shell.hXdyadic)
    ⊕ DensePackFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)
```

The adversarial audit `Erdos260.AuditAnalyticInputs` (TARGET 4) records that the *existing*
all-shells witness `final3_densePackRegime_inhabited` rides on the RIGHT (fallback) summand
`Sum.inr (densePackFactoryData_trivial …)` — an **empty** DensePack point set (`spread = 0`,
`cStarSmall = 0`, `densePackPoints = ∅`, zero mass): type-total but degenerate.

This file (NEW; it edits no existing file) supplies the **genuine LEFT (in-regime) summand** for
**above-threshold** failing shells, with **real manuscript geometry**:

* the point set is the genuine actual-support marker set `proofV4DensePackActualPoints shell`
  (a filter of `Finset.Icc 0 (3X + spread)` by the support-window hit count), **not** the
  hard-coded `∅`;
* the spread is `proofV4DensePackSpread shell = L + carryB Q + 1 ≥ 1` (**positive**);
* the density constant is `cStarSmall = c0 / proofV4DensePackMinHits shell` (**positive**, since
  the carry-large gate makes `proofV4DensePackMinHits shell > 0`);
* the marker count is the genuine greedy maximal-separated marker count;
* the constructed point count obeys the manuscript I.4.1 / Corollary K.1.3 budget
  `densePackPoints.card ≤ c_*·ξ·X/6` (`densePackRegime_genuine_card_le_budget`).

All four DensePack inequalities (cover K.1.2, count K.1.3-under-failure, smallness I.4.1, packing
K.1.5) are **derived** through the already-proved `DensePackFactoryConstruction` /
`GlobalDensePackAssembly` machinery; in regime the entire datum is built from shell geometry alone.

## Manuscript reference
* Appendix I.4 (Lemma I.4.1, "Dense-marker packing under the positive-density failure hypothesis"):
  under the contradictory failure `A_S(2X) − A_S(X) ≤ c_*X`, the selected-marker count obeys
  `|𝒟₀| ≤ C·c_*X/(ρ_D L)`, giving `DensePack_{s,j} ≤ ξ sX|I_j| + o(…)` once `c_* ≪_Q ρ_D κ ξ`.
* Appendix K.1 (Coarea normalization + endpoint-disjoint DensePack support), Corollary K.1.3
  (`densePackPoints.card ≤ …`): the key per-phase budget reproduced by
  `densePackRegime_genuine_card_le_budget`.

## Honest residual (sharpest explicit hypotheses, never `sorry`)
The genuine in-regime branch needs exactly two side conditions; both are isolated to the sharpest
explicit hypotheses, neither is faked:

1. `hpin : shell.c0 = manuscriptC0` — the manuscript **K.4 failure-constant pin** `c0 = κ/64`.
   A bare `FailingDyadicShell` carries only `c0 < κ` (`hc0_lt_kappa`), which does **not** give
   `c0 ≤ κ/16`; the pin discharges it (`failingShell_c0_le_kappa_div_sixteen_of_pin`).
2. `hlarge : shell.aboveCarryThreshold` — the genuine large-scale gate, discharged into
   `carryB Q + 25 ≤ L` (`failingShell_carryLarge_of_aboveCarryThreshold`). At the global assembly
   this gate is supplied by the per-failure `startThreshold ≤ X` hypothesis.

Sub-threshold shells lie **outside** the in-regime scope: the in-regime conditions provably force
`X ≥ 2^25` (`AuditAnalyticInputs.audit_densePack_inRegime_forces_scale`), so for them no large-scale
dense packing exists and the faithful fallback is the only available datum — used **only** there.

No `sorry`, `admit`, `native_decide`, or new `axiom`; no degenerate witness is used to fake closure.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 1. The genuine in-regime DensePack regime input -/

/-- The two structural side conditions of the in-regime DensePack branch, derived from the
manuscript failure-constant pin (`c0 ≤ κ/16`) and the large-scale gate (`carryB Q + 25 ≤ L`). -/
theorem densePackRegime_genuine_conditions (shell : FailingDyadicShell)
    (hpin : shell.c0 = manuscriptC0) (hlarge : shell.aboveCarryThreshold) :
    shell.c0 ≤ manuscriptKappa / 16 ∧
      carryB shell.Q + 25 ≤ Classical.choose shell.hXdyadic :=
  ⟨failingShell_c0_le_kappa_div_sixteen_of_pin shell hpin,
   failingShell_carryLarge_of_aboveCarryThreshold shell hlarge⟩

/--
**Main deliverable — the genuine in-regime DensePack regime input.**

For an above-threshold failing shell under the manuscript `c0 = κ/64` pin, this produces the
`DensePackRegimeInput` via the **LEFT (`Sum.inl`) in-regime branch**, so that
`DensePackRegimeInput.build` constructs the full canonical factory datum
(`densePackFactoryDataCanonical`) — real point set, positive spread, positive density constant,
genuine greedy marker count, all three inequalities derived. This is *not* the empty
`Sum.inr (densePackFactoryData_trivial …)` fallback. -/
def densePackRegime_genuine (shell : FailingDyadicShell)
    (_hcQ : shell.cQ = erdos260Constants.cQ)
    (hpin : shell.c0 = manuscriptC0)
    (hlarge : shell.aboveCarryThreshold) :
    DensePackRegimeInput shell :=
  Sum.inl (PLift.up
    ⟨failingShell_c0_le_kappa_div_sixteen_of_pin shell hpin,
     failingShell_carryLarge_of_aboveCarryThreshold shell hlarge⟩)

/-- The genuine input takes the in-regime `Sum.inl` branch — never the empty `Sum.inr` fallback. -/
theorem densePackRegime_genuine_is_inl (shell : FailingDyadicShell)
    (hcQ : shell.cQ = erdos260Constants.cQ)
    (hpin : shell.c0 = manuscriptC0) (hlarge : shell.aboveCarryThreshold) :
    densePackRegime_genuine shell hcQ hpin hlarge
      = Sum.inl (PLift.up
          ⟨failingShell_c0_le_kappa_div_sixteen_of_pin shell hpin,
           failingShell_carryLarge_of_aboveCarryThreshold shell hlarge⟩) :=
  rfl

/-- The built factory datum is the **canonical** datum (real geometry), not a fallback. -/
theorem densePackRegime_genuine_build (shell : FailingDyadicShell)
    (hcQ : shell.cQ = erdos260Constants.cQ)
    (hpin : shell.c0 = manuscriptC0) (hlarge : shell.aboveCarryThreshold) :
    (densePackRegime_genuine shell hcQ hpin hlarge).build
      = densePackFactoryDataCanonical shell
          (failingShell_c0_le_kappa_div_sixteen_of_pin shell hpin)
          (failingShell_carryLarge_of_aboveCarryThreshold shell hlarge) :=
  rfl

/-! ## 2. Genuineness certificates (real geometry, not the degenerate fallback) -/

/-- **Genuine point set.**  The built datum's point set is the actual support-window marker set
`proofV4DensePackActualPoints shell`, the genuine manuscript object — **not** the empty `∅`. -/
theorem densePackRegime_genuine_points (shell : FailingDyadicShell)
    (hcQ : shell.cQ = erdos260Constants.cQ)
    (hpin : shell.c0 = manuscriptC0) (hlarge : shell.aboveCarryThreshold) :
    (densePackRegime_genuine shell hcQ hpin hlarge).build.densePackPoints
      = proofV4DensePackActualPoints shell :=
  rfl

/-- **Genuine spread.**  The built datum's spread is `proofV4DensePackSpread shell = L + carryB Q + 1`. -/
theorem densePackRegime_genuine_spread (shell : FailingDyadicShell)
    (hcQ : shell.cQ = erdos260Constants.cQ)
    (hpin : shell.c0 = manuscriptC0) (hlarge : shell.aboveCarryThreshold) :
    (densePackRegime_genuine shell hcQ hpin hlarge).build.spread
      = proofV4DensePackSpread shell :=
  rfl

/-- The genuine spread is **positive** (the degenerate fallback has spread `0`). -/
theorem densePackRegime_genuine_spread_pos (shell : FailingDyadicShell)
    (hcQ : shell.cQ = erdos260Constants.cQ)
    (hpin : shell.c0 = manuscriptC0) (hlarge : shell.aboveCarryThreshold) :
    0 < (densePackRegime_genuine shell hcQ hpin hlarge).build.spread := by
  rw [densePackRegime_genuine_spread]
  unfold proofV4DensePackSpread
  omega

/-- **Genuine density constant.**  The built datum's `cStarSmall` is `c0 / proofV4DensePackMinHits shell`. -/
theorem densePackRegime_genuine_cStarSmall (shell : FailingDyadicShell)
    (hcQ : shell.cQ = erdos260Constants.cQ)
    (hpin : shell.c0 = manuscriptC0) (hlarge : shell.aboveCarryThreshold) :
    (densePackRegime_genuine shell hcQ hpin hlarge).build.cStarSmall
      = shell.c0 / (proofV4DensePackMinHits shell : ℝ) :=
  rfl

/-- The genuine density constant is **positive** (the degenerate fallback has `cStarSmall = 0`):
`c0 > 0` and the carry-large gate gives `proofV4DensePackMinHits shell > 0`. -/
theorem densePackRegime_genuine_cStarSmall_pos (shell : FailingDyadicShell)
    (hcQ : shell.cQ = erdos260Constants.cQ)
    (hpin : shell.c0 = manuscriptC0) (hlarge : shell.aboveCarryThreshold) :
    0 < (densePackRegime_genuine shell hcQ hpin hlarge).build.cStarSmall := by
  rw [densePackRegime_genuine_cStarSmall]
  apply div_pos shell.hc0_pos
  have hpos : 0 < proofV4DensePackMinHits shell :=
    proofV4DensePackMinHits_pos_of_carryLarge
      (failingShell_carryLarge_of_aboveCarryThreshold shell hlarge)
  exact_mod_cast hpos

/--
**Key estimate — manuscript I.4.1 / Corollary K.1.3 budget.**

The genuine constructed point count obeys the per-phase budget `c_*·ξ·X/6`, reusing the proved
`densePackFactoryDataOfDensity_card_le_budget` (itself `corollaryK1_3_densePackUnderFailure` plus the
pinned-constant smallness). This is the genuine dense-pack-under-failure bound, on the real
actual-support marker set. -/
theorem densePackRegime_genuine_card_le_budget (shell : FailingDyadicShell)
    (hcQ : shell.cQ = erdos260Constants.cQ)
    (hpin : shell.c0 = manuscriptC0) (hlarge : shell.aboveCarryThreshold) :
    ((densePackRegime_genuine shell hcQ hpin hlarge).build.densePackPoints.card : ℝ)
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (shell.X : ℝ) / 6 := by
  rw [densePackRegime_genuine_build]
  exact densePackFactoryDataOfDensity_card_le_budget
    (DensePackProofV4ShellGreedyInputData.ofActualSupportWindows shell)
    (failingShell_c0_le_kappa_div_sixteen_of_pin shell hpin)
    (failingShell_carryLarge_of_aboveCarryThreshold shell hlarge)

/-! ## 3. Reusing the `ShellScalarRegime` bundle

The genuine input coincides with the bundle's DensePack input / factory datum, confirming it is the
same canonical object that `ShellRegimeClosure` certifies. -/

/-- The genuine input equals the `ShellScalarRegime` bundle's DensePack regime input. -/
theorem densePackRegime_genuine_eq_shellRegime (shell : FailingDyadicShell)
    (hcQ : shell.cQ = erdos260Constants.cQ)
    (hpin : shell.c0 = manuscriptC0) (hlarge : shell.aboveCarryThreshold)
    (hSupport : 1 ≤ supportCount shell.d shell.X) :
    densePackRegime_genuine shell hcQ hpin hlarge
      = (shellRegime_of_aboveCarryThreshold shell hpin hlarge hSupport).densePackRegimeInput :=
  rfl

/-- The genuine built datum equals the `ShellScalarRegime` bundle's canonical factory datum. -/
theorem densePackRegime_genuine_build_eq_shellRegime (shell : FailingDyadicShell)
    (hcQ : shell.cQ = erdos260Constants.cQ)
    (hpin : shell.c0 = manuscriptC0) (hlarge : shell.aboveCarryThreshold)
    (hSupport : 1 ≤ supportCount shell.d shell.X) :
    (densePackRegime_genuine shell hcQ hpin hlarge).build
      = (shellRegime_of_aboveCarryThreshold shell hpin hlarge hSupport).densePackFactoryData :=
  rfl

/-! ## 4. Contrast with the degenerate fallback (what we removed) -/

/-- The always-available **degenerate** fallback (empty point set), shown only for contrast — this
is the crutch the genuine branch replaces for above-threshold shells. -/
def densePackRegime_fallback (shell : FailingDyadicShell) : DensePackRegimeInput shell :=
  Sum.inr (densePackFactoryData_trivial
    (div_nonneg
      (mul_nonneg
        (mul_nonneg erdos260Constants.cStar_pos.le erdos260Constants.ξ_pos.le)
        shell.X_nonneg_real)
      (by norm_num)))

theorem densePackRegime_fallback_build_empty (shell : FailingDyadicShell) :
    (densePackRegime_fallback shell).build.densePackPoints = (∅ : Finset ℕ) := rfl

theorem densePackRegime_fallback_spread_zero (shell : FailingDyadicShell) :
    (densePackRegime_fallback shell).build.spread = 0 := rfl

theorem densePackRegime_fallback_cStarSmall_zero (shell : FailingDyadicShell) :
    (densePackRegime_fallback shell).build.cStarSmall = 0 := rfl

/-! ## 5. Genuine inhabitation of the capstone field shape -/

/-- **Genuine** inhabitation of the `densePackRegime` field type for above-threshold pinned shells.
This replaces the empty-fallback `UnconditionalAssemblyFinal3.final3_densePackRegime_inhabited`
(which used `Sum.inr (densePackFactoryData_trivial …)`) by the genuine in-regime datum. -/
theorem densePackRegime_genuine_inhabited (shell : FailingDyadicShell)
    (hcQ : shell.cQ = erdos260Constants.cQ)
    (hpin : shell.c0 = manuscriptC0) (hlarge : shell.aboveCarryThreshold) :
    Nonempty (DensePackRegimeInput shell) :=
  ⟨densePackRegime_genuine shell hcQ hpin hlarge⟩

open Classical in
/--
**Total DensePack field built genuinely on the whole carry-large regime.**

Under the manuscript K.4 pin (every `cQ`-shell has `c0 = κ/64`), this inhabits the exact capstone
field `∀ shell, shell.cQ = … → DensePackRegimeInput shell`, using the **genuine** in-regime datum on
every above-threshold shell and the faithful fallback **only** on sub-threshold shells (where the
in-regime conditions provably fail, so no large-scale packing exists). -/
def densePackRegime_field_of_pin
    (hpin : ∀ s : FailingDyadicShell, s.cQ = erdos260Constants.cQ → s.c0 = manuscriptC0) :
    ∀ shell : FailingDyadicShell, shell.cQ = erdos260Constants.cQ → DensePackRegimeInput shell :=
  fun shell hcQ =>
    if hlarge : shell.aboveCarryThreshold then
      densePackRegime_genuine shell hcQ (hpin shell hcQ) hlarge
    else
      densePackRegime_fallback shell

/-- On every above-threshold shell the total field uses the **genuine** in-regime datum. -/
theorem densePackRegime_field_of_pin_eq_genuine
    (hpin : ∀ s : FailingDyadicShell, s.cQ = erdos260Constants.cQ → s.c0 = manuscriptC0)
    (shell : FailingDyadicShell) (hcQ : shell.cQ = erdos260Constants.cQ)
    (hlarge : shell.aboveCarryThreshold) :
    densePackRegime_field_of_pin hpin shell hcQ
      = densePackRegime_genuine shell hcQ (hpin shell hcQ) hlarge := by
  simp only [densePackRegime_field_of_pin, dif_pos hlarge]

/-- Consequently, on every above-threshold shell the total field's built point set is the genuine
actual-support marker set — never the empty fallback. -/
theorem densePackRegime_field_of_pin_points
    (hpin : ∀ s : FailingDyadicShell, s.cQ = erdos260Constants.cQ → s.c0 = manuscriptC0)
    (shell : FailingDyadicShell) (hcQ : shell.cQ = erdos260Constants.cQ)
    (hlarge : shell.aboveCarryThreshold) :
    (densePackRegime_field_of_pin hpin shell hcQ).build.densePackPoints
      = proofV4DensePackActualPoints shell := by
  rw [densePackRegime_field_of_pin_eq_genuine hpin shell hcQ hlarge]
  exact densePackRegime_genuine_points shell hcQ (hpin shell hcQ) hlarge

/-! ## 6. Honest residual inventory -/

/-- The honest status of the DensePack leaf after this file. -/
def densePackUnconditionalClosureResidual : List String :=
  [ "In-regime branch GENUINE: for above-threshold shells under the c0 = κ/64 pin, " ++
      "densePackRegime_genuine takes Sum.inl, so .build = densePackFactoryDataCanonical with the " ++
      "REAL actual-support marker set proofV4DensePackActualPoints shell (densePackRegime_genuine_points), " ++
      "positive spread = L + carryB Q + 1 (densePackRegime_genuine_spread_pos), positive density " ++
      "constant c0/proofV4DensePackMinHits (densePackRegime_genuine_cStarSmall_pos), genuine greedy " ++
      "marker count, and the I.4.1/K.1.3 budget card ≤ c_*ξX/6 (densePackRegime_genuine_card_le_budget). " ++
      "NOT the empty Sum.inr (densePackFactoryData_trivial) fallback.",
    "hcover (K.1.2 marker-neighbourhood cover), hcount (K.1.3 density-under-failure), hsmall (I.4.1 " ++
      "budget), and marker_count_mul_le_shell (K.1.5 disjoint one-sided support packing): all DERIVED, " ++
      "none assumed (via DensePackFactoryConstruction / GlobalDensePackAssembly).",
    "Residual 1 (sharpest hypothesis, NOT sorry): hpin : shell.c0 = manuscriptC0 — the manuscript " ++
      "K.4 failure-constant pin c0 = κ/64. A bare FailingDyadicShell gives only c0 < κ " ++
      "(hc0_lt_kappa), insufficient for c0 ≤ κ/16; the pin closes it " ++
      "(failingShell_c0_le_kappa_div_sixteen_of_pin).",
    "Residual 2 (sharpest hypothesis, NOT sorry): hlarge : shell.aboveCarryThreshold — the genuine " ++
      "large-scale gate, discharged into carryB Q + 25 ≤ L " ++
      "(failingShell_carryLarge_of_aboveCarryThreshold); at the global assembly it is supplied by the " ++
      "per-failure startThreshold ≤ X hypothesis.",
    "Sub-threshold shells: OUTSIDE the in-regime scope. The in-regime conditions force X ≥ 2^25 " ++
      "(AuditAnalyticInputs.audit_densePack_inRegime_forces_scale), so no large-scale dense packing " ++
      "exists there; densePackRegime_field_of_pin uses the faithful fallback ONLY on those shells." ]

theorem densePackUnconditionalClosureResidual_nonempty :
    densePackUnconditionalClosureResidual ≠ [] := by
  simp [densePackUnconditionalClosureResidual]

#print axioms densePackRegime_genuine
#print axioms densePackRegime_genuine_card_le_budget
#print axioms densePackRegime_genuine_points
#print axioms densePackRegime_field_of_pin

end

end Erdos260
