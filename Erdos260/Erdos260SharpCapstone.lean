import Erdos260.Erdos260SixAtomCapstone
import Erdos260.ChernoffClass0Routing
import Erdos260.CNLClass1Closure
import Erdos260.TowerDeepWindowClosure
import Erdos260.DensePackCorrectedClosure
import Erdos260.ReturnClass4Closure
import Erdos260.RunClass5Routing

/-!
# Erdős 260 — the sharpened capstone on the wave-2 surfaces

This module consolidates the 2026-06-10 wave-2 routing-pin closure effort.  It defines
`Erdos260SharpResidual`, the strictly sharpened successor of `Erdos260SixAtomResidual`,
and proves the new final endpoint

`erdos260_of_sharpResidual : Erdos260SharpResidual → Erdos260Statement`

by composing ONLY existing public bridges of the six wave-2 modules into the wave-1
capstone `erdos260_of_sixAtoms`.  Nothing is re-proved here.  All six atoms carry their
wave-2 sharpened surface; no atom fell back to its wave-1 field.

The six sharpened atoms:

1. **Tower / class 2** — `Class2DeepShellCountBound`: one `ℕ` counting inequality
   `m₀ · #fibre₂ ≤ |supportShell|` per deep shell (`L > 328965`), proved EQUIVALENT to
   the wave-1 `Class2DeepShellResidual` (`towerDeepResidual_iff_countBound`); consumed
   through `towerDeepResidual_ofCountBound`.
2. **Run / class 5** — `RunClass5SplitBoundary`: an ungated boundary window-excess bound
   `M` on the top `r + 1` band plus ONE Section 26 numeric at the split multiplier
   `max (runDyadicMult ctx) M`; consumed through `runCoreOfSplitBoundary` (interior
   starts are absorbed by the proved matched ceiling
   `class5_windowExcess_le_runDyadicMult_of_interior`).
3. **Return / class 4** — `Class4FibreSmall` (the population bound `|olcFibre| ≤ r + 1`,
   a THEOREM on all gated shells) plus the three-field `ReturnClass4DigitResidual`
   (`hzero`/`hcleanStep`/`class4Interior`; `hgapDiv` and `hnumeric` are theorems given
   the count); consumed through `returnZResidualsOfDigitAndCount`, an equivalence by
   `nonempty_selfRef_iff_digit_of_card_le`.
4. **Chernoff / class 0** — the budget-free pinned arithmetic: no carry-window start
   realizes the gap-window floor `129L + 64 ≤ 64·gW` AND the deep E.13 band
   `16·K_k ≤ q` simultaneously — necessary AND sufficient by
   `v3_class0FibreEmpty_iff_pinned`; consumed through
   `class0FibreEmpty_of_genuineRoute_pinned` (the capstone budget routes through
   `genuineChargeRoute` by `rfl`).
5. **CNL / class 1** — the budget-free sharp pinned arithmetic with EVERY proved wave-2
   obstruction folded in as a given (`1 ≤ k`, `64 ∣ L`, `9 ≤ q`, the parity window
   `q ≤ 15 ∨ 25 ≤ q`, `Odd K_k`): refute `canonGap = 4` at the exact pin
   `64·gW = 129L + 64` — strictly weaker than the wave-1 emptiness field; consumed
   through `class1FibreEmpty_of_pinned_arithmetic_sharp`.
6. **DensePack / class 3** — `DensePackRegimeSplitResidual`: gated shells (including ALL
   `r = 0`) reduced to the single emptiness Prop, ungated shells carrying exactly the
   corrected K.1.1 density + K.1 interior + K.1.2 amortized cover — proved EQUIVALENT to
   the wave-1 `DensePackCorrectedResidue` (`nonempty_densePackCorrected_iff_regimeSplit`);
   consumed through `DensePackRegimeSplitResidual.toCorrected`.

Dependency order mirrors the wave-1 capstone: the Tower/Run/Return fields define the
canonical budget `sharpAtomBudget` (a `sixAtomBudget`, hence a `v3Budget`, by `rfl`),
and the class-0/class-1/class-3 fields are stated at (or independently of) that budget.
-/

namespace Erdos260

noncomputable section

/-- **Run / class 5, the wave-2 split-boundary surface** (ungated): a boundary
window-excess bound `M` on the top `r + 1` band of the carry window, plus the single
Section 26 numeric at the split multiplier `max (runDyadicMult ctx) M`.  Interior starts
need no hypothesis: their window excess is absorbed by the proved matched ceiling
`class5_windowExcess_le_runDyadicMult_of_interior`. -/
structure RunClass5SplitBoundary (ctx : ActualFailureContext) where
  /-- The boundary window-excess multiplier. -/
  M : ℝ
  /-- Every start in the top `r + 1` boundary band has window excess at most `M`. -/
  hM : ∀ k : ℕ,
    ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
        + (supportShell ctx.shell.d ctx.shell.X).card ≤ k + ctx.n24CarryData.r + 1 →
    k < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
        + (supportShell ctx.shell.d ctx.shell.X).card →
    windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
      ≤ M
  /-- The single Section 26 linear numeric at the split multiplier. -/
  hcount : erdos260Constants.c0
        * ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card : ℝ)
        * max (runDyadicMult ctx) M
      ≤ (erdos260Constants.cStar * erdos260Constants.ξ / 12)
        * ((supportShell ctx.d ctx.X).card : ℝ)

/-- The split-boundary surface discharges the wave-1 Run max-core residual, with no gate
hypothesis (`runCoreOfSplitBoundary`). -/
def RunClass5SplitBoundary.toCore {ctx : ActualFailureContext}
    (S : RunClass5SplitBoundary ctx) : RunClass5LeafSupportMaxCoreResidual ctx :=
  runCoreOfSplitBoundary ctx S.hM S.hcount

/-- The canonical sharp budget: the `sixAtomBudget` of the bridged wave-2 Tower, Run and
Return surfaces.  It is a `v3Budget` routing through `genuineChargeRoute`, by `rfl`. -/
def sharpAtomBudget
    (towerCount : Class2DeepShellCountBound)
    (runSplit : ∀ ctx : ActualFailureContext, RunClass5SplitBoundary ctx)
    (returnSmall : Class4FibreSmall)
    (returnDigit : ∀ ctx : ActualFailureContext, ReturnClass4DigitResidual ctx) :
    ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx :=
  sixAtomBudget (towerDeepResidual_ofCountBound towerCount)
    (fun ctx => (runSplit ctx).toCore)
    (returnZResidualsOfDigitAndCount returnSmall returnDigit)

/-- **The sharpened final residual.**  Each field is the sharpest proven-equivalent (or
strictly weaker sufficient) wave-2 surface of its atom; the Tower/Run/Return fields
define the canonical `sharpAtomBudget`, the class-0/class-1 fields are budget-free
pinned arithmetic, and the class-3 regime split is stated at that budget. -/
structure Erdos260SharpResidual where
  /-- Tower / class 2: the deep-shell counting inequality `m₀ · #fibre₂ ≤ |supportShell|`
  (equivalent to the wave-1 deep-shell Hall residual). -/
  towerCount : Class2DeepShellCountBound
  /-- Run / class 5: the ungated split-boundary surface (boundary bound `M` + one
  numeric at `max (runDyadicMult ctx) M`). -/
  runSplit : ∀ ctx : ActualFailureContext, RunClass5SplitBoundary ctx
  /-- Return / class 4: the population bound `|olcFibre ctx| ≤ r + 1` (a theorem on all
  gated shells; open only on gate-violating deep shells). -/
  returnSmall : Class4FibreSmall
  /-- Return / class 4: the three-field digit residual (`hzero`/`hcleanStep`/interior);
  `hgapDiv` and `hnumeric` are theorems given `returnSmall`. -/
  returnDigit : ∀ ctx : ActualFailureContext, ReturnClass4DigitResidual ctx
  /-- Chernoff / class 0: the budget-free pinned arithmetic — no carry-window start
  realizes the gap-window floor and the deep band `16·K_k ≤ q` simultaneously
  (necessary AND sufficient for the wave-1 emptiness field). -/
  class0Pinned : ∀ ctx : ActualFailureContext, ∀ k ∈ ctx.n24CarryData.starts,
    ¬(129 * shellLadderDepth ctx + 64
        ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
      ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
          ≤ (class1SlopeDatum ctx).q)
  /-- Clean-CNL / class 1: the sharp pinned arithmetic with every proved obstruction
  folded in as a given (`1 ≤ k`, `64 ∣ L`, `9 ≤ q`, the parity window, `Odd K_k`) —
  strictly weaker than the wave-1 emptiness field. -/
  class1Pinned : ∀ ctx : ActualFailureContext, ∀ k ∈ ctx.n24CarryData.starts,
    1 ≤ k →
    64 ∣ shellLadderDepth ctx →
    9 ≤ (class1SlopeDatum ctx).q →
    ((class1SlopeDatum ctx).q ≤ 15 ∨ 25 ≤ (class1SlopeDatum ctx).q) →
    Odd (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) →
    64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        = 129 * shellLadderDepth ctx + 64 →
    canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) ≠ 4
  /-- DensePack / class 3: the regime-split residual at the canonical sharp budget —
  gated emptiness + ungated K.1.1/K.1/K.1.2 (equivalent to the wave-1 corrected
  residue). -/
  densePackSplit : DensePackRegimeSplitResidual
    (sharpAtomBudget towerCount runSplit returnSmall returnDigit)

namespace Erdos260SharpResidual

/-- The canonical budget of a sharp residual. -/
def budget (R : Erdos260SharpResidual) :
    ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx :=
  sharpAtomBudget R.towerCount R.runSplit R.returnSmall R.returnDigit

/-- **The bridge into the wave-1 capstone**: every field of `Erdos260SixAtomResidual`
is rebuilt from the sharp surfaces through existing public bridges — nothing is
re-proved.

* Tower — `towerDeepResidual_ofCountBound` (lossless by `towerDeepResidual_iff_countBound`);
* Run — `runCoreOfSplitBoundary` (the ungated split entry);
* Return — `returnZResidualsOfDigitAndCount` (count + digit residual ⇒ Z-family);
* class 0 — `class0FibreEmpty_of_genuineRoute_pinned` at the `rfl` route of the budget;
* class 1 — `class1FibreEmpty_of_pinned_arithmetic_sharp` (all closures folded in);
* class 3 — `DensePackRegimeSplitResidual.toCorrected` (lossless by
  `nonempty_densePackCorrected_iff_regimeSplit`). -/
def toSixAtom (R : Erdos260SharpResidual) : Erdos260SixAtomResidual where
  towerDeep := towerDeepResidual_ofCountBound R.towerCount
  runCore := fun ctx => (R.runSplit ctx).toCore
  returnZ := returnZResidualsOfDigitAndCount R.returnSmall R.returnDigit
  class0Empty :=
    class0FibreEmpty_of_genuineRoute_pinned
      (sixAtomBudget (towerDeepResidual_ofCountBound R.towerCount)
        (fun ctx => (R.runSplit ctx).toCore)
        (returnZResidualsOfDigitAndCount R.returnSmall R.returnDigit))
      (fun _ => rfl) R.class0Pinned
  class1Empty :=
    class1FibreEmpty_of_pinned_arithmetic_sharp
      (p9V3TowerCount_ofShallowDeep (towerDeepResidual_ofCountBound R.towerCount))
      (p9V3RunChainOfResidual (runClass5LeafResidual_ofSupportMaxCoreResidual
        (fun ctx => (R.runSplit ctx).toCore)))
      (returnChargeOfZResiduals (returnZResidualsOfDigitAndCount R.returnSmall R.returnDigit))
      R.class1Pinned
  densePack := R.densePackSplit.toCorrected

/-- The final statement from the sharp residual, through the wave-1 six-atom capstone
and the ctx-pinned P9 ledger. -/
theorem toStatement (R : Erdos260SharpResidual) : Erdos260Statement :=
  erdos260_of_sixAtoms R.toSixAtom

end Erdos260SharpResidual

/-- **The sharpened final endpoint.**  `Erdos260Statement` from the six wave-2 sharpened
per-atom surfaces, composed through the wave-1 six-atom capstone with no re-proving and
no over-strong scalar anywhere on the route. -/
theorem erdos260_of_sharpResidual (R : Erdos260SharpResidual) : Erdos260Statement :=
  R.toStatement

/-- Machine-readable status of the sharpened capstone. -/
def erdos260SharpCapstoneStatus : List String :=
  [ "FINAL ENDPOINT (wave 2): erdos260_of_sharpResidual (R : Erdos260SharpResidual) : " ++
      "Erdos260Statement, composed through toSixAtom into erdos260_of_sixAtoms and the " ++
      "ctx-pinned P9 ledger; only existing public bridges are consumed, nothing re-proved.",
    "ALL SIX ATOMS SHARPENED; NO WAVE-1 FALLBACKS.",
    "ATOM Tower/class 2 (SHARPENED, lossless): Class2DeepShellCountBound - one Nat " ++
      "counting inequality m0 * #fibre2 <= |supportShell| per deep shell (L > 328965); " ++
      "equivalent to the wave-1 Class2DeepShellResidual (towerDeepResidual_iff_countBound); " ++
      "consumed via towerDeepResidual_ofCountBound.",
    "ATOM Run/class 5 (SHARPENED, ungated): RunClass5SplitBoundary - boundary " ++
      "window-excess bound M on the top r+1 band + ONE Section 26 numeric at " ++
      "max(runDyadicMult, M); interior starts absorbed by the proved matched ceiling; " ++
      "consumed via runCoreOfSplitBoundary into RunClass5LeafSupportMaxCoreResidual.",
    "ATOM Return/class 4 (SHARPENED): Class4FibreSmall (|olcFibre| <= r+1; a THEOREM on " ++
      "all gated shells, open only on gate-violating deep shells) + the three-field " ++
      "ReturnClass4DigitResidual (hzero/hcleanStep/class4Interior; hgapDiv and hnumeric " ++
      "are theorems given the count); consumed via returnZResidualsOfDigitAndCount; " ++
      "equivalence given the count: nonempty_selfRef_iff_digit_of_card_le.",
    "ATOM Chernoff/class 0 (SHARPENED, budget-free, necessary AND sufficient): the pinned " ++
      "arithmetic - no carry-window start realizes the floor 129L+64 <= 64*gW AND the deep " ++
      "band 16*K_k <= q simultaneously (v3_class0FibreEmpty_iff_pinned); consumed via " ++
      "class0FibreEmpty_of_genuineRoute_pinned at the rfl route of sharpAtomBudget.",
    "ATOM CNL/class 1 (SHARPENED, budget-free, strictly weaker than wave-1): refute " ++
      "canonGap = 4 at the exact pin 64*gW = 129L+64 GIVEN 1 <= k, 64 | L, 9 <= q, " ++
      "q <= 15 or 25 <= q, and Odd K_k (every proved wave-2 obstruction folded in); " ++
      "consumed via class1FibreEmpty_of_pinned_arithmetic_sharp.",
    "ATOM DensePack/class 3 (SHARPENED, lossless): DensePackRegimeSplitResidual at " ++
      "sharpAtomBudget - gated shells (incl. ALL r = 0) reduced to the single emptiness " ++
      "Prop, ungated shells carrying exactly K.1.1 density + K.1 interior + corrected " ++
      "K.1.2 amortized cover; equivalent to the wave-1 DensePackCorrectedResidue " ++
      "(nonempty_densePackCorrected_iff_regimeSplit); consumed via toCorrected.",
    "BAND MAP (all proved, wave 2): every atom shares the gap-window floor " ++
      "129L+64 <= 64*gW; class 1 = band 4 at the exact pin 64*gW = 129L+64; class 4 = " ++
      "band 2; class 3 = band 3; class 0 = bands >= 5 (16K <= q); class 5 = band 1 or " ++
      "heavy band 4 (130L+64 <= 64*gW) or the cnlTail spike; class 2 = the open strip " ++
      "129L+64 < 64*gW < 130L+64 with canonGap = 4.",
    "CLOSED INSIDE the composition (unchanged from wave 1): carry floor, faithful " ++
      "phases, mass nonnegativity, the class-6 old-residual vacancy, the joint TRT " ++
      "ledger bound, the Kraft sum, and the hne/hcard counts." ]

theorem erdos260SharpCapstoneStatus_nonempty : erdos260SharpCapstoneStatus ≠ [] := by
  simp [erdos260SharpCapstoneStatus]

#print axioms RunClass5SplitBoundary.toCore
#print axioms sharpAtomBudget
#print axioms Erdos260SharpResidual.budget
#print axioms Erdos260SharpResidual.toSixAtom
#print axioms Erdos260SharpResidual.toStatement
#print axioms erdos260_of_sharpResidual
#print axioms erdos260SharpCapstoneStatus_nonempty

end

end Erdos260
