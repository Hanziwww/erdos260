import Mathlib
import Erdos260.PackageLedgerFactory
import Erdos260.ReturnNestingConstruction
import Erdos260.ResidualScalarBudgets
import Erdos260.CarryDataFactory

/-!
# Return factory datum CONSTRUCTED from the proved M.2.1 nesting + I.5.1 routing + `M_L` budget

The capstone `erdos260_reduced_minimal''` (`UnconditionalAssemblyTight2.lean`) still
takes the per-shell `ReturnFactoryData` as an **assumed atom** (the `returnPkg`
field of `Erdos260MinimalAtoms''`).  This file (NEW; it edits no existing file)
converts that atom into a *builder*, so it is no longer assumed but **derived from
the already-proved Return CORE**:

* the **M.2.1 OLC crossing/nesting counting** `OLCEndpointMultiplicity.card_le`
  (`|endpoints| ≤ M_L·|baseSet|`), with the per-anchor nesting `≤ M_L` and the I.5.1
  routing `|baseSet| ≤ X·|I_j|` discharged as theorems inside
  `ReturnNesting.ReturnNestingCore` (`ReturnNestingConstruction.lean`);
* the **Cor. M.2.2 OLC return-slot collapse** `OLCEndpointMultiplicity.olc_le_returnScale`
  (`|endpoints| ≤ s·X·|I_j|`), reusing the proved `AppendixM` algebra
  (`ReturnRunFamily.lean`);
* the **`M_L` scalar budget** `mL_budget_of_scale` (`ResidualScalarBudgets.lean`):
  `M_L·X·|I_j| ≤ s·X·|I_j|/2` under the clean dimensionless regime `2·M_L ≤ s`.

## What this file does (honest)

* **`returnFactoryDataOfNesting : ReturnNestingCore cStar ξ X → ReturnFactoryData cStar ξ X`** —
  the core reduction.  The OLC field `olc` is set to the **genuine cleaned OLC
  endpoint count** `|dirtyFamily|` (NOT a free scalar), and its bound `hOLC` is
  *proved* from the M.2.1 counting + I.5.1 routing + the `M_L`/M.2 budgets.  The
  other three pieces and the K.4 smallness are forwarded verbatim.  So the
  `returnPkg` atom is **REDUCED** from a free `ReturnFactoryData` to a
  `ReturnNestingCore`, whose M.2.1 nesting and I.5.1 routing are theorems.
* **`ReturnFactoryReducedInput`** + `toFactoryData` — pushes the residue one step
  further: the J.4 envelope budget field `olc_ML_budget` is replaced by the cleaner
  `ml_regime : 2·M_L ≤ s` (and the nonnegativity `hsXij` is *derived*), with the
  budget reconstructed via `ResidualScalarBudgets.mL_budget_of_scale`.
* **`returnPkgOfNestingProvider` / `returnPkgOfReducedProvider`** — the per-shell
  wrappers whose output type is *exactly* the capstone `Erdos260MinimalAtoms''.returnPkg`
  field.  Plugging a per-shell `ReturnNestingCore` (resp. `ReturnFactoryReducedInput`)
  provider into them yields the `returnPkg` field — no longer an assumed atom.
* **`returnDataProviderOfNesting`** — the same for the older `ReturnDataProvider`
  interface (`PackageLedgerFactory.lean`).
* Non-vacuity witnesses (`returnFactoryDataTrivial`, `returnFactoryReducedInputTrivial`)
  confirm the builders are inhabited, so the construction is not vacuous.

## Honest residual status of `returnPkg`

**REDUCED, not closed.**  After this file the assumed `ReturnFactoryData` atom is
replaced by the genuinely smaller `ReturnNestingCore` / `ReturnFactoryReducedInput`,
whose *only* remaining genuine inputs are:

* the **cleaned dirty-return family** `dirtyFamily : Finset DirtyCrossing` with its
  K.2.5 envelope `dirtyFamily.card ≤ M_L` and the I.5.1 shell containment
  (`anchor_lt_shell` + `shell_route`) — the geometric realization;
* the **clean regime** `2·M_L ≤ s` (manuscript `M_L = o(r)`) and the M.2 return-slot
  routing `olc_return_budget`;
* the three **non-OLC return counts** (`ordinaryShort_bound` / `semiperiodic_bound` /
  `nonlocalLong_bound`, L.2.2) and the **K.4 numerical smallness** `hSmall`.

No `sorry`, `admit`, `native_decide`, or new `axiom`; no false/vacuous hypotheses.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## Part A — the OLC return-slot bound for the nesting core's own dirty family

`ReturnNesting.ReturnNestingCore` already carries the M.2.1 per-anchor nesting and the
I.5.1 anchor routing as *theorems* (built from the K.2.5 envelope).  Specializing the
proved `OLCEndpointMultiplicity.olc_le_returnScale` (Cor. M.2.2) to the core's own
geometry collapses the genuine OLC endpoint count `|dirtyFamily|` to the return scale
`s·X·|I_j|`. -/

/--
**OLC endpoint count `≤ s·X·|I_j|` for a nesting core (genuinely PROVED).**

The cleaned OLC endpoint count `|dirtyFamily|` is bounded by the return scale via the
M.2.1 counting core (`OLCEndpointMultiplicity.olc_le_returnScale`), fed the proved
I.5.1 routing `olc_route`, the K.2.5/J.4 envelope budget `olc_ML_budget`, and the
scale nonnegativity `hsXij`.
-/
theorem ReturnNesting.ReturnNestingCore.dirtyFamily_card_le_returnScale
    {cStar ξ X : ℝ} (core : ReturnNesting.ReturnNestingCore cStar ξ X) :
    (core.dirtyFamily.card : ℝ) ≤ core.s * X * core.ij := by
  have hroute : ((core.toOLCGeom).baseSet.card : ℝ) ≤ X * core.ij :=
    core.toReturnFamilyCore.olc_route
  have holc := core.toOLCGeom.olc_le_returnScale hroute core.olc_ML_budget core.hsXij
  simpa [ReturnNesting.ReturnNestingCore.toOLCGeom] using holc

/-! ## Part B — core builder `ReturnNestingCore → ReturnFactoryData`

The assumed `ReturnFactoryData` atom is *constructed*: the OLC piece is the genuine
cleaned endpoint count, with its bound proved from Part A and the M.2 return-slot
routing; the three non-OLC pieces and the K.4 smallness are forwarded verbatim. -/

/--
**Build the assumed `ReturnFactoryData` atom from the proved Return CORE.**

`olc` is set to the **genuine cleaned OLC endpoint count** `(dirtyFamily.card : ℝ)`,
and `hOLC` is *proved* (Part A + the M.2 return-slot routing `olc_return_budget`).
The remaining fields are the L.2.2 non-OLC counts and the K.4 smallness, carried
verbatim.  So `returnPkg` is no longer an assumed `ReturnFactoryData`; it is derived
from a `ReturnNestingCore` whose M.2.1 nesting and I.5.1 routing are theorems.
-/
def returnFactoryDataOfNesting {cStar ξ X : ℝ}
    (core : ReturnNesting.ReturnNestingCore cStar ξ X) :
    ReturnFactoryData cStar ξ X where
  ordinaryShort := core.ordinaryShort
  semiperiodic := core.semiperiodic
  olc := (core.dirtyFamily.card : ℝ)
  nonlocalLong := core.nonlocalLong
  c1 := core.c1
  c2 := core.c2
  c3 := core.c3
  c4 := core.c4
  s := core.s
  ij := core.ij
  smallError := core.smallError
  hOrdinaryShort := core.ordinaryShort_bound
  hSemiperiodic := core.semiperiodic_bound
  hOLC := by
    have h := core.dirtyFamily_card_le_returnScale
    have hb := core.olc_return_budget
    linarith
  hNonlocalLong := core.nonlocalLong_bound
  hSmall := core.hSmall

@[simp] theorem returnFactoryDataOfNesting_olc {cStar ξ X : ℝ}
    (core : ReturnNesting.ReturnNestingCore cStar ξ X) :
    (returnFactoryDataOfNesting core).olc = (core.dirtyFamily.card : ℝ) := rfl

/--
**The constructed OLC mass is the genuine cleaned OLC endpoint count.**

The four-piece sum of the built factory datum is *definitionally* the proved M.2.1 /
I.5.1 family sum with the OLC slot equal to `|dirtyFamily|` — confirming the OLC piece
is the genuine geometric count, not a free scalar.
-/
theorem returnFactoryDataOfNesting_matches_termReturn {cStar ξ X : ℝ}
    (core : ReturnNesting.ReturnNestingCore cStar ξ X) :
    (returnFactoryDataOfNesting core).ordinaryShort
        + (returnFactoryDataOfNesting core).semiperiodic
        + (returnFactoryDataOfNesting core).olc
        + (returnFactoryDataOfNesting core).nonlocalLong
      = core.ordinaryShort + core.semiperiodic + (core.dirtyFamily.card : ℝ)
        + core.nonlocalLong := rfl

/--
**Prop. I.5.1 budget for the constructed datum (reusing the proved `nonRunReturnBound`).**

The constructed `ReturnFactoryData` satisfies the manuscript four-piece return budget
`ordinaryShort + semiperiodic + olc + nonlocalLong ≤ cStar·ξ·X/6`, with the OLC slot
the genuine cleaned endpoint count.
-/
theorem returnFactoryDataOfNesting_nonRunReturn_bound {cStar ξ X : ℝ}
    (core : ReturnNesting.ReturnNestingCore cStar ξ X) :
    (returnFactoryDataOfNesting core).ordinaryShort
        + (returnFactoryDataOfNesting core).semiperiodic
        + (returnFactoryDataOfNesting core).olc
        + (returnFactoryDataOfNesting core).nonlocalLong
      ≤ cStar * ξ * X / 6 :=
  nonRunReturnBound_of_factory (returnFactoryDataOfNesting core)

/-! ## Part C — the smallest genuine input: the `2·M_L ≤ s` regime

`ReturnNestingCore` is already the minimal geometric bundle.  Its sole *scalar*
analytic field beyond the L.2.2/K.4 residue is the J.4 envelope budget
`olc_ML_budget : M_L·X·|I_j| ≤ s·X·|I_j|/2`.  This part replaces it with the cleaner
dimensionless regime `2·M_L ≤ s` (manuscript `M_L = o(r)`), reconstructing the budget
via `ResidualScalarBudgets.mL_budget_of_scale`, and *derives* the scale
nonnegativity. -/

/--
**Return factory reduced input — the genuinely smallest Return residue.**

Identical to `ReturnNestingCore` except the J.4 envelope budget field is replaced by
the dimensionless regime `ml_regime : 2·M_L ≤ s` plus the trivial area nonnegativity
`hXij_area : 0 ≤ X·|I_j|`; the scale nonnegativity `hsXij` is then *derived*.
-/
structure ReturnFactoryReducedInput (cStar ξ X : ℝ) where
  /-- The cleaned OLC dirty-return family `𝓡^cl(𝔡̂)`. -/
  dirtyFamily : Finset DirtyCrossing
  /-- The K.2.5 dirty multiplicity envelope `M_L`. -/
  ML : ℕ
  /-- **K.2.5 (proved/assembled):** `|𝓡^cl(𝔡̂)| ≤ M_L`. -/
  envelope : dirtyFamily.card ≤ ML
  /-- The integer size of the dyadic shell hosting the anchors. -/
  shellSize : ℕ
  /-- **I.5.1 routing input:** every anchor lies inside the shell `[0, shellSize)`. -/
  anchor_lt_shell : ∀ x ∈ dirtyFamily, x.anchor < shellSize
  ordinaryShort : ℝ
  semiperiodic : ℝ
  nonlocalLong : ℝ
  c1 : ℝ
  c2 : ℝ
  c3 : ℝ
  c4 : ℝ
  s : ℝ
  ij : ℝ
  smallError : ℝ
  /-- **I.5.1 routing budget:** the shell size fits `X·|I_j|`. -/
  shell_route : (shellSize : ℝ) ≤ X * ij
  /-- Area nonnegativity `0 ≤ X·|I_j|` (a shell side-condition). -/
  hXij_area : 0 ≤ X * ij
  /-- **Clean regime (replaces the J.4 envelope budget):** `2·M_L ≤ s` (`M_L = o(r)`). -/
  ml_regime : 2 * (ML : ℝ) ≤ s
  /-- **M.2/Prop. 23.1 residue:** the OLC return-slot routing. -/
  olc_return_budget : s * X * ij ≤ c3 * ξ * s * X * ij + smallError / 4
  /-- **L.2.2 residue:** ordinary short non-run return count. -/
  ordinaryShort_bound : ordinaryShort ≤ c1 * ξ * s * X * ij + smallError / 4
  /-- **L.2.2 residue:** semiperiodic short non-run return count. -/
  semiperiodic_bound : semiperiodic ≤ c2 * ξ * s * X * ij + smallError / 4
  /-- **L.2.2 residue:** nonlocal long return count. -/
  nonlocalLong_bound : nonlocalLong ≤ c4 * ξ * s * X * ij + smallError / 4
  /-- **K.4 residue:** numerical smallness for the I.5.1 budget. -/
  hSmall : (c1 + c2 + c3 + c4) * ξ * s * X * ij + smallError ≤ cStar * ξ * X / 6

namespace ReturnFactoryReducedInput

variable {cStar ξ X : ℝ}

/-- The scale `s` is nonnegative: it dominates `2·M_L ≥ 0`. -/
theorem s_nonneg (r : ReturnFactoryReducedInput cStar ξ X) : 0 ≤ r.s :=
  le_trans (by positivity) r.ml_regime

/--
**Recover the proved `ReturnNestingCore` from the reduced input.**

The J.4 envelope budget is reconstructed from the regime `2·M_L ≤ s` via
`ResidualScalarBudgets.mL_budget_of_scale`, and the scale nonnegativity is derived.
-/
def toNestingCore (r : ReturnFactoryReducedInput cStar ξ X) :
    ReturnNesting.ReturnNestingCore cStar ξ X where
  dirtyFamily := r.dirtyFamily
  ML := r.ML
  envelope := r.envelope
  shellSize := r.shellSize
  anchor_lt_shell := r.anchor_lt_shell
  ordinaryShort := r.ordinaryShort
  semiperiodic := r.semiperiodic
  nonlocalLong := r.nonlocalLong
  c1 := r.c1
  c2 := r.c2
  c3 := r.c3
  c4 := r.c4
  s := r.s
  ij := r.ij
  smallError := r.smallError
  shell_route := r.shell_route
  olc_ML_budget := mL_budget_of_scale (by linarith [r.ml_regime]) r.hXij_area
  olc_return_budget := r.olc_return_budget
  hsXij := by
    have h : (0 : ℝ) ≤ r.s * (X * r.ij) := mul_nonneg r.s_nonneg r.hXij_area
    calc (0 : ℝ) ≤ r.s * (X * r.ij) := h
      _ = r.s * X * r.ij := by ring
  ordinaryShort_bound := r.ordinaryShort_bound
  semiperiodic_bound := r.semiperiodic_bound
  nonlocalLong_bound := r.nonlocalLong_bound
  hSmall := r.hSmall

/-- Build the `ReturnFactoryData` atom from the reduced input. -/
def toFactoryData (r : ReturnFactoryReducedInput cStar ξ X) :
    ReturnFactoryData cStar ξ X :=
  returnFactoryDataOfNesting r.toNestingCore

/-- The reduced-input factory datum satisfies the Prop. I.5.1 budget. -/
theorem nonRunReturn_bound (r : ReturnFactoryReducedInput cStar ξ X) :
    r.toFactoryData.ordinaryShort + r.toFactoryData.semiperiodic
        + r.toFactoryData.olc + r.toFactoryData.nonlocalLong
      ≤ cStar * ξ * X / 6 :=
  nonRunReturnBound_of_factory r.toFactoryData

end ReturnFactoryReducedInput

/-! ## Part D — per-shell wrappers feeding the capstone `returnPkg` field

These produce *exactly* the type of `Erdos260MinimalAtoms''.returnPkg`
(`UnconditionalAssemblyTight2.lean`) and of `Erdos260MinimalAtoms.returnPkg`
(`UnconditionalAssembly.lean`): a per-failing-shell `ReturnFactoryData` at the global
constants.  A per-shell `ReturnNestingCore` (resp. `ReturnFactoryReducedInput`)
provider therefore *builds* the `returnPkg` field instead of assuming it. -/

/--
**Per-shell `returnPkg` field from a per-shell `ReturnNestingCore` provider.**

The output type is precisely the capstone `Erdos260MinimalAtoms''.returnPkg` field.
-/
def returnPkgOfNestingProvider
    (provider : ∀ shell : FailingDyadicShell, shell.cQ = erdos260Constants.cQ →
        ReturnNesting.ReturnNestingCore erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : ℝ)) :
    ∀ shell : FailingDyadicShell, shell.cQ = erdos260Constants.cQ →
        ReturnFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ) :=
  fun shell hcQ => returnFactoryDataOfNesting (provider shell hcQ)

/--
**Per-shell `returnPkg` field from a per-shell `ReturnFactoryReducedInput` provider.**
-/
def returnPkgOfReducedProvider
    (provider : ∀ shell : FailingDyadicShell, shell.cQ = erdos260Constants.cQ →
        ReturnFactoryReducedInput erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : ℝ)) :
    ∀ shell : FailingDyadicShell, shell.cQ = erdos260Constants.cQ →
        ReturnFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ) :=
  fun shell hcQ => (provider shell hcQ).toFactoryData

/--
**Older `ReturnDataProvider` interface built from a per-shell `ReturnNestingCore` provider.**
-/
def returnDataProviderOfNesting
    (provider : ∀ shell : FailingDyadicShell, shell.cQ = erdos260Constants.cQ →
        ReturnNesting.ReturnNestingCore erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : ℝ)) :
    ReturnDataProvider where
  constants := erdos260Constants
  data := fun shell hcQ => returnFactoryDataOfNesting (provider shell hcQ)

/-! ## Part E — non-vacuity witnesses

Degenerate all-zero instances confirm the builders are inhabited, so the constructed
budgets are genuinely realizable rather than vacuous. -/

/-- A degenerate factory datum built from the degenerate nesting core. -/
def returnFactoryDataTrivial : ReturnFactoryData 0 0 0 :=
  returnFactoryDataOfNesting ReturnNesting.returnNestingCoreTrivial

/-- The degenerate datum's OLC slot is the empty-family count `0`. -/
theorem returnFactoryDataTrivial_olc : returnFactoryDataTrivial.olc = 0 := by
  simp [returnFactoryDataTrivial, returnFactoryDataOfNesting,
    ReturnNesting.returnNestingCoreTrivial]

theorem returnFactoryData_nonempty : Nonempty (ReturnFactoryData 0 0 0) :=
  ⟨returnFactoryDataTrivial⟩

/-- A degenerate reduced input (empty family, all scales `0`, regime `0 ≤ 0`). -/
def returnFactoryReducedInputTrivial : ReturnFactoryReducedInput 0 0 0 where
  dirtyFamily := ∅
  ML := 0
  envelope := by simp
  shellSize := 0
  anchor_lt_shell := by intro x hx; simp at hx
  ordinaryShort := 0
  semiperiodic := 0
  nonlocalLong := 0
  c1 := 0
  c2 := 0
  c3 := 0
  c4 := 0
  s := 0
  ij := 0
  smallError := 0
  shell_route := by norm_num
  hXij_area := by norm_num
  ml_regime := by norm_num
  olc_return_budget := by norm_num
  ordinaryShort_bound := by norm_num
  semiperiodic_bound := by norm_num
  nonlocalLong_bound := by norm_num
  hSmall := by norm_num

theorem returnFactoryReducedInput_nonempty :
    Nonempty (ReturnFactoryReducedInput 0 0 0) :=
  ⟨returnFactoryReducedInputTrivial⟩

/-- The reduced-input builder yields a factory datum with OLC slot `0`. -/
theorem returnFactoryReducedInputTrivial_olc :
    returnFactoryReducedInputTrivial.toFactoryData.olc = 0 := by
  simp [ReturnFactoryReducedInput.toFactoryData, ReturnFactoryReducedInput.toNestingCore,
    returnFactoryDataOfNesting, returnFactoryReducedInputTrivial]

/-! ## Part F — honest status inventory -/

/-- The Return-factory inputs now CONSTRUCTED (no longer assumed) in this file. -/
def returnFactoryConstructedItems : List String :=
  [ "returnFactoryDataOfNesting: ReturnFactoryData built from ReturnNestingCore " ++
      "(M.2.1 nesting + I.5.1 routing PROVED; olc = genuine cleaned endpoint count)",
    "ReturnFactoryReducedInput.toFactoryData: J.4 envelope budget reduced to the " ++
      "clean regime 2·M_L ≤ s (via mL_budget_of_scale); hsXij derived",
    "returnPkgOfNestingProvider / returnPkgOfReducedProvider: the capstone " ++
      "Erdos260MinimalAtoms''.returnPkg field, built per-shell rather than assumed" ]

/-- The honest residue feeding the reduced Return input (smallest genuine inputs). -/
def returnFactoryReducedResidue : List String :=
  [ "cleaned dirty family + K.2.5 envelope (dirtyFamily, ML, envelope)",
    "I.5.1 shell containment (anchor_lt_shell, shell_route)",
    "clean regime 2·M_L ≤ s + M.2 return-slot routing (ml_regime, olc_return_budget)",
    "L.2.2 non-OLC counts + K.4 smallness (ordinaryShort/semiperiodic/nonlocalLong_bound, hSmall)" ]

theorem returnFactoryConstructedItems_nonempty : returnFactoryConstructedItems ≠ [] := by
  simp [returnFactoryConstructedItems]

theorem returnFactoryReducedResidue_nonempty : returnFactoryReducedResidue ≠ [] := by
  simp [returnFactoryReducedResidue]

end

end Erdos260
