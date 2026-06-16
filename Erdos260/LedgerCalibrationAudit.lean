import Erdos260.P9CtxPinnedReduction
import Erdos260.CNLMultiChargeUnconditional
import Erdos260.CNLClass1PairClosure

/-!
# Ledger calibration audit: the P9 per-class capacity terms vs the manuscript budgets

This module (NEW; it edits no existing file) is a COMPARISON AUDIT between the formalized
P9 ledger calibration and its source-text counterpart
(`proof_v4_unconditional_clean_v5.tex`), looking for a transcription mismatch of the same
genre as the two previously found and corrected instances (a scale inequality that was the
formalization's transcription rather than the source's claim, and a global digit demand
where the source used a routing predicate).

## The object audited: the class-1 (clean-CNL) capacity term of the P9 ledger

**Formal side (in-tree provenance).**  The P9 ledger residual
`P9CtxPinnedLedgerResidual` (`P9CtxPinnedReduction.lean`) demands, per context,

```
hCnl : routedClassMassOf ctx.n24CarryData (budget ctx).route 1
         <= termCnl (faithfulCapacityPhases budget ctx).toClosurePhaseData
```

and its `toStatement` consumes the five ledger bounds through
`erdos260_charge_reduced_of_routing` / `RoutedHighExcessChargeDataOldRes
.highExcess_le_phaseMass_add_oldRes` (`ChargeBridgeReduction.lean`) -- the formal
transcription of the stopped charged-ledger recurrence (manuscript (H.1)/(I.11')) -- and
the carry/pressure bridge at the floor `cPr * X` (the formal Lemma 21.1 / H.5 floor).  The
final contradiction is the floor `cPr*X = X/2` against the six per-phase budget caps
`manuscript_bound : CQ^M * shellFactor * X * Ij <= cStar*xi*X/6` (`AppendixG_CNL.lean`,
`AppendixK3_CNL.lean`), totalling `cStar*xi*X = (31/256)*X < X/2` (`Constants.lean`,
`manuscriptCstar_mul_xi_eq_31_256`).

The faithful class-1 term is pinned (all `rfl`-level, re-proved below):

* `termCnl = cleanCNLKraftSum(family) * shellFactor * X * |I_j|`
  (`AppendixI_PhaseMass.lean`);
* `shellFactor = 2^(-(c0*eta*X))` -- the shell-Chernoff weight with the exponent taken at
  `Y := X = 2^L` (`CNLScalarBudgetCore.cnlShellFactorOfShell`; the in-file comment says
  verbatim "taken at the genuine shell *order* `Y := X`");
* `|I_j| = 2^(-M)`, `M = L + |CNLTransition| >= L` -- the measure of ONE length-`M`
  codeword cylinder (`CNLScalarBudgetCore.cnlIjOfShell`, `cnlLeafShellM`), so
  `X*|I_j| <= 1` (`faithful_X_mul_Ij_le_one`);
* hence `termCnl <= 14 * (1/64) * 1 = 7/32` (`termCnl_faithful_le_7_32`) -- BELOW the
  single-start excess `Y = L/64 >= 7/16` (`n24CarryData_Y_ge`), so the class-1 ledger
  bound is EQUIVALENT to fibre emptiness (`class1Ledger_iff_fibre_empty` -- the razor).

**Source side (tex provenance; line numbers in `proof_v4_unconditional_clean_v5.tex`).**

* `I_j` is the THRESHOLD interval `I_j = [T_0^(j), T_0^(j) + c_I*L]` of length
  `|I_j| = c_I*L` -- eq. (2.0), lines 289--298; restated as (K.20), lines 5363--5372.
  It is NOT a dyadic codeword cylinder; the Kraft normalization `sum_j |I_j| = 1` of the
  cylinder family is a DIFFERENT object (G.35 box, lines 2645--2652).
* The stopped recurrence (H.1), lines 2725--2740, budgets the clean-CNL class per stage
  `s` and interval `I_j` by the term `X*|I_j|*2^(-c*Y)`, with the exponent LINEAR IN THE
  ACTIVE FLOOR `Y` (`c_Y*L <= Y <= C_Y*L`): the constant `c` is fixed in K.4 item 3,
  lines 5378--5385 (`C_Q^(c_1*Y) * 2^(-c_0*eta*Y) <= 2^(-c*Y)`); same shape in H.2,
  lines 2709--2724, and in the proved shell bound (I.0c'''), lines 3085--3091, and the
  charging direction "Clean CNL terminal outputs are bounded by the CNL tail
  `X|I_j|2^{-cY}`", line 3382.
* The per-class P-budgets grow linearly in the stage: (H.2'), lines 2755--2768, and
  (H.3'), lines 2786--2795, allot `C_Q*xi*s*X*|I_j|` at stage `s`; the ledger is
  EVALUATED at the contradiction stage `s = r = floor(kappa*L)`, `j = 0`, `Y_0 = eps*L`
  ((H.4'), lines 2838--2848; K.4 items 4--5, lines 5386--5400), against the pressure
  floor `c_pr*r*X*|I_0|` ((H.5), lines 2851--2868; K.5 display, lines 5455--5469:
  `A_r >> rXL` vs `A_r <= C*xi*rXL + C_Q*c_**rXL + o(rXL)`).
* The ledger assembly / charged summability backing the per-class terms: J.6
  (lines 4319+), L.1 (lines 5482+), L.2 (lines 5891+), I.2 (lines 3233+).

**The comparison at the evaluation point** (`s = r`, `j = 0`, `Y = eps*L = L/64`), per
unit threshold-fibre (the formal `routedClassMassOf` carries no `dT`-integral, so the
like-for-like source quantity is the (H.1) CNL term divided by `|I_j|`):

* source budget: `X * 2^(-c*eps*L)` -- at the in-tree pinned constants the exponent is
  `c0*eta*eps*L = (17/2^34)*L <= L/2`, so the budget is `>= 2^(L/2) -> infinity`; it
  EXCEEDS one full pinned excess `Y` on every shell (`Y_lt_sourceH1CnlBudgetPerFibre`
  below).  The source ledger at the evaluation stage therefore NEVER forces class-1
  fibre emptiness -- it admits `~ 2^((1-c*eps)L) * 64/L` surviving class-1 starts.
* formal frozen term: `<= 7/32 < 7/16 <= Y` -- the exponent was frozen at `Y := X`
  (`2^(-c0*eta*2^L)` instead of `2^(-c0*eta*Y)`, `auditFrozenExponent_gt_source`), and
  `|I_j|` was frozen to the single Kraft cylinder `2^(-M)` (instead of the threshold
  interval `c_I*L` of (2.0)/(K.20)); no stage factor at all (stage-frozen).

## VERDICT: the formalized faithful term is a SMALLER FROZEN VALUE, not the source's
## budget at the evaluation stage

Both substitutions (`Y := X` in the exponent; `|I_j| := 2^(-M)` for the threshold
interval) shrink the class-1 capacity below ONE single excess, so the formal ledger
demand `hCnl` degenerates to outright fibre emptiness (the razor) -- a demand the source
text never makes at any stage.  This is a calibration artifact of the transcription, the
same pattern as the two previously corrected instances.

## The corrected term, the re-based ledger bridge, and the enabled survivor closures

The formal global ledger fixes its own absolute scale (floor `cPr*X = X/2`, total phase
budget `cStar*xi*X = (31/256)*X`; both in `X`-units, internally consistent, while the
source works in `r*X*|I_0| ~ L^2*X`-units).  Within that in-tree calibration the maximal
admissible class-1 capacity is the FULL per-class share `(cStar*xi/6)*X = (31/1536)*X` --
the largest value the consumed budget cap `manuscript_bound` allows.  We construct:

* `correctedCnlData` -- a `CNLClusterEncodingData` over the SAME genuine surviving
  clean-CNL family (`selectedTransitions (liftTransitionsOfShell ctx)`), with the
  shell/interval normalization re-scaled so the realized term SATURATES the per-class
  share exactly: `termCnl(corrected) = (cStar*xi/6)*X` (`termCnl_corrected_eq`); its
  `manuscript_bound` holds with equality, so the corrected phases remain consumable by
  the global budget contradiction;
* `correctedCapacityPhases` -- `faithfulCapacityPhases` with only the `cnl` slot
  replaced; the other five phase terms are unchanged (`rfl`-level transports);
* `CorrectedP9CtxPinnedLedgerResidual` -- the P9 ledger residual re-based on the
  corrected term, with the complete bridge `toStatement : ... -> Erdos260Statement`
  through `RoutedHighExcessChargeDataOldRes` (`oldResMass = 0`) and
  `erdos260_final_actual` -- no transport through the frozen-term consumers needed;
* the monotone weakening `ofPinnedRoutingZero` -- the OLD (frozen) pinned residual
  implies the corrected one (`7/32 <= (31/1536)*X` for `X >= 2^28`), so the corrected
  surface is genuinely never harder;
* **survivor closures enabled by the correction** (`Y < termCnl(corrected)`,
  `Y_lt_termCnl_corrected`):
  - on EVERY `r = floor(kappa*L) = 0` shell (ALL `L <= 15420`) the class-1 ledger bound
    over the corrected term is CLOSED OUTRIGHT (`correctedHCnl_of_r_eq_zero`,
    `correctedHCnl_of_L_le`, via the proved cap `|fibre_1| <= 1`,
    `class1Fibre_card_le_one_of_r_eq_zero`) -- the frozen term required outright
    emptiness even there;
  - on every context whose wave-14 per-pair count cap `|fibre_1| <= b_4 * ceil(W/c)`
    (`class1Fibre_card_le_cycleDensity`, `CNLClass1PairClosure.lean`) numerically fits
    under the share, the bound closes (`correctedHCnl_of_cycleDensity`,
    `correctedHCnl_of_card_cap`);
  - `ofGenuineCaps` packages this: over any genuine-route budget the corrected residual
    needs only the class-0/3 charging bounds plus the count-cap absorption -- `hTRT` and
    `hOldRes` are closed generically (`seedHTRT`, `genuineChargeRoute_routed6_zero`).

## Honest accounting

* The corrected term equals the formal calibration's own per-class CAP; it does NOT
  reproduce the source's `xi*s*X*|I_j|` absolute scale (in source units the budget at the
  evaluation point is larger still).  Re-basing the whole formal ledger to the source's
  `r*X*|I_0|`-units would require touching the pressure-floor spine -- out of additive
  scope and NOT needed: the per-class cap already absorbs every proved survivor count cap
  with `count*Y <= (31/1536)*X`.
* The closures above are exactly what the correction enables today: unconditional on
  `r = 0` shells; conditional on the numeric absorption gate elsewhere.  Deep shells
  (`L > 15420`) with count caps exceeding `(31/24)*X/L` remain open on the class-1 axis,
  as they were (but now under an honest, non-vacuous capacity instead of a sub-excess
  frozen one).
* Nothing here closes the global P9 residual; the corrected surface is offered as the
  faithful re-calibration plus its proved partial closures.

**Source-patch recommendation:** none for the source text -- the source's (H.1)/(K.4)
calibration is the consistent one.  The PATCH TARGET is the formal frozen choice
`cnlShellFactorOfShell`/`cnlIjOfShell` (`CNLScalarBudgetCore.lean`): the exponent should
be read at the active floor `Y` (`K.4` item 3, tex lines 5378--5385) and `|I_j|` at the
threshold-interval scale of (2.0) -- which, inside the in-tree `X`-unit ledger, is
exactly the `correctedCnlData` re-scaling below.

No `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace Erdos260

open Finset

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 1.  Provenance pins of the FROZEN (in-tree faithful) class-1 term

All three pins are `rfl`-level: they record exactly what the consumed faithful term is.
Manuscript counterparts: shell factor `2^{-c0*eta*Y}` at the active floor `Y` (K.4 item 3,
tex lines 5378--5385; H.2, lines 2709--2724); `|I_j| = c_I*L` (eq. (2.0), lines 289--298;
(K.20), lines 5363--5372). -/

/-- **Pin 1 (frozen shell factor).**  The consumed faithful clean-CNL shell factor is
`2^(-(c0*eta*X))` -- the manuscript shell-Chernoff weight with the exponent frozen at
`Y := X = 2^L`, NOT at the manuscript active floor `Y = eps*L` (K.4 item 3, tex lines
5378--5385). -/
theorem auditFrozenShellFactor
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    (faithfulCnlData budget ctx).shellFactor
      = (2 : ℝ) ^ (-(erdos260Constants.c0 * manuscriptEta * (ctx.shell.X : ℝ))) := rfl

/-- **Pin 2 (frozen interval).**  The consumed faithful clean-CNL interval length is
`(1/2)^M` with `M = cnlLeafShellM ctx = L + |CNLTransition|` -- the measure of ONE
length-`M` codeword cylinder, NOT the manuscript threshold interval `|I_j| = c_I*L`
(eq. (2.0), tex lines 289--298). -/
theorem auditFrozenIj
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    (faithfulCnlData budget ctx).Ij = ((1 : ℝ) / 2) ^ cnlLeafShellM ctx := rfl

/-- **Pin 3 (frozen family).**  The consumed faithful clean-CNL path family is the genuine
surviving clean-CNL transition family (so the freeze is in the scalar normalization, not in
the family). -/
theorem auditFrozenFamily
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    (faithfulCnlData budget ctx).paths
      = selectedTransitions (liftTransitionsOfShell ctx) :=
  faithfulCnlData_paths budget ctx

/-- **Pin 4 (the Kraft tiling collapse).**  The frozen interval tiles the shell scale away:
`X * |I_j| <= 1` -- versus the source's `X * |I_j| = c_I * L * X` at the threshold-interval
length of (2.0)/(K.20).  Re-export of the in-tree `faithful_X_mul_Ij_le_one`. -/
theorem auditFrozenTiling
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    (ctx.shell.X : ℝ) * (faithfulCnlData budget ctx).Ij ≤ 1 :=
  faithful_X_mul_Ij_le_one budget ctx

/-- **The exponent freeze, quantified**: the frozen Chernoff exponent `c0*eta*X` strictly
exceeds the manuscript exponent `c0*eta*(eps*L)` read at the evaluation-point active floor
`Y = eps*L` (H.4'/K.4 item 4, tex lines 2838--2848 / 5386--5392).  Hence the frozen shell
factor strictly undersells the source factor `2^{-c*Y}` on every shell. -/
theorem auditFrozenExponent_gt_source (ctx : ActualFailureContext) :
    erdos260Constants.c0 * manuscriptEta * (manuscriptEps * (shellLadderDepth ctx : ℝ))
      < erdos260Constants.c0 * manuscriptEta * (ctx.shell.X : ℝ) := by
  have hc : erdos260Constants.c0 * manuscriptEta = 17 / 268435456 := by
    rw [show erdos260Constants.c0 = manuscriptC0 from rfl]
    unfold manuscriptC0 manuscriptKappa manuscriptCdrop manuscriptC1 manuscriptEps
      manuscriptEta
    norm_num
  have hXeq : ctx.shell.X = 2 ^ shellLadderDepth ctx :=
    Classical.choose_spec ctx.shell.hXdyadic
  have hL : shellLadderDepth ctx < ctx.shell.X := by
    rw [hXeq]; exact Nat.lt_two_pow_self
  have hLr : (shellLadderDepth ctx : ℝ) < (ctx.shell.X : ℝ) := by exact_mod_cast hL
  have hL0 : (0 : ℝ) ≤ (shellLadderDepth ctx : ℝ) := Nat.cast_nonneg _
  have heps : manuscriptEps * (shellLadderDepth ctx : ℝ) < (ctx.shell.X : ℝ) := by
    unfold manuscriptEps
    linarith
  rw [hc]
  linarith

/-- **The razor, re-recorded**: over the FROZEN term the per-context class-1 ledger bound
is equivalent to outright fibre emptiness -- the formal demand the source never makes.
Re-export of `class1Ledger_iff_fibre_empty` for the audit's axiom block. -/
theorem auditRazor
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    (routedClassMassOf ctx.n24CarryData (budget ctx).route 1
        ≤ termCnl (faithfulCapacityPhases budget ctx).toClosurePhaseData)
      ↔ routedFibre ctx.n24CarryData (budget ctx).route 1 = ∅ :=
  class1Ledger_iff_fibre_empty budget ctx

/-! ## Part 2.  The source budget at the evaluation point, formalized per threshold fibre

The (H.1) clean-CNL ledger term is `X * |I_j| * 2^{-cY}` (tex lines 2725--2740), with the
exponent linear in the active floor `Y` (K.4 item 3).  The formal `routedClassMassOf`
carries no `dT`-integral over `I_j`, so the like-for-like comparison object is the source
term per unit threshold length: `X * 2^{-cY}` at `Y = eps*L`, with the in-tree exponent
constant `c = c0*eta` (the K.4 chain before the `C_Q^{c_1 Y}` give-back, i.e. the LARGEST
honest reading of the discount -- using a smaller `c` only enlarges the source budget). -/

/-- The source (H.1)/(K.4 item 3) clean-CNL budget at the evaluation point
(`Y = eps*L`, stage- and `dT`-normalized): `X * 2^(-(c0*eta*(eps*L)))`. -/
def sourceH1CnlBudgetPerFibre (ctx : ActualFailureContext) : ℝ :=
  (ctx.shell.X : ℝ)
    * (2 : ℝ) ^ (-(erdos260Constants.c0 * manuscriptEta
        * (manuscriptEps * (shellLadderDepth ctx : ℝ))))

/-- The evaluation-point exponent is at most `L/2`:
`c0*eta*eps = 17/2^34 <= 1/2`. -/
theorem sourceH1_exponent_le_half (ctx : ActualFailureContext) :
    erdos260Constants.c0 * manuscriptEta * (manuscriptEps * (shellLadderDepth ctx : ℝ))
      ≤ (shellLadderDepth ctx : ℝ) / 2 := by
  have h2 : erdos260Constants.c0 * manuscriptEta
        * (manuscriptEps * (shellLadderDepth ctx : ℝ))
      = (17 / 17179869184) * (shellLadderDepth ctx : ℝ) := by
    rw [show erdos260Constants.c0 = manuscriptC0 from rfl]
    unfold manuscriptC0 manuscriptKappa manuscriptCdrop manuscriptC1 manuscriptEps
      manuscriptEta
    ring
  have hL0 : (0 : ℝ) ≤ (shellLadderDepth ctx : ℝ) := Nat.cast_nonneg _
  rw [h2]
  linarith

/-- **The source side of the comparison**: at the evaluation point the source clean-CNL
budget EXCEEDS one full pinned class-1 excess `Y = L/64` on every shell
(`X * 2^{-c*eps*L} >= 2^{L/2} > L/64`).  So the source ledger never forces class-1 fibre
emptiness -- it admits unboundedly many surviving class-1 starts as `L` grows. -/
theorem Y_lt_sourceH1CnlBudgetPerFibre (ctx : ActualFailureContext) :
    ctx.n24CarryData.Y < sourceH1CnlBudgetPerFibre ctx := by
  rw [n24CarryData_Y_eq_div]
  unfold sourceH1CnlBudgetPerFibre
  have hexp := sourceH1_exponent_le_half ctx
  have hfac : (2 : ℝ) ^ (-((shellLadderDepth ctx : ℝ) / 2))
      ≤ (2 : ℝ) ^ (-(erdos260Constants.c0 * manuscriptEta
          * (manuscriptEps * (shellLadderDepth ctx : ℝ)))) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    linarith
  have hXeq : ctx.shell.X = 2 ^ shellLadderDepth ctx :=
    Classical.choose_spec ctx.shell.hXdyadic
  have hXr : (ctx.shell.X : ℝ) = (2 : ℝ) ^ ((shellLadderDepth ctx : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    rw [hXeq]
    exact_mod_cast rfl
  have hhalf : (ctx.shell.X : ℝ) * (2 : ℝ) ^ (-((shellLadderDepth ctx : ℝ) / 2))
      = (2 : ℝ) ^ ((shellLadderDepth ctx : ℝ) / 2) := by
    rw [hXr, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hm : (shellLadderDepth ctx : ℝ) / 64
      < (2 : ℝ) ^ ((shellLadderDepth ctx : ℝ) / 2) := by
    have h1 : shellLadderDepth ctx / 2 < 2 ^ (shellLadderDepth ctx / 2) :=
      Nat.lt_two_pow_self
    have hmnat : shellLadderDepth ctx < 64 * 2 ^ (shellLadderDepth ctx / 2) := by
      omega
    have hcast : (shellLadderDepth ctx : ℝ)
        < 64 * (2 : ℝ) ^ (shellLadderDepth ctx / 2) := by
      exact_mod_cast hmnat
    have hpow : (2 : ℝ) ^ (shellLadderDepth ctx / 2)
        ≤ (2 : ℝ) ^ ((shellLadderDepth ctx : ℝ) / 2) := by
      rw [← Real.rpow_natCast 2 (shellLadderDepth ctx / 2)]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      have h2 : (shellLadderDepth ctx / 2) * 2 ≤ shellLadderDepth ctx :=
        Nat.div_mul_le_self _ 2
      have h3 : ((shellLadderDepth ctx / 2 : ℕ) : ℝ) * 2 ≤ (shellLadderDepth ctx : ℝ) := by
        exact_mod_cast h2
      linarith
    linarith
  have hX0 : (0 : ℝ) ≤ (ctx.shell.X : ℝ) := Nat.cast_nonneg _
  calc (shellLadderDepth ctx : ℝ) / 64
      < (2 : ℝ) ^ ((shellLadderDepth ctx : ℝ) / 2) := hm
    _ = (ctx.shell.X : ℝ) * (2 : ℝ) ^ (-((shellLadderDepth ctx : ℝ) / 2)) := hhalf.symm
    _ ≤ (ctx.shell.X : ℝ)
          * (2 : ℝ) ^ (-(erdos260Constants.c0 * manuscriptEta
              * (manuscriptEps * (shellLadderDepth ctx : ℝ)))) :=
        mul_le_mul_of_nonneg_left hfac hX0

/-- **The two-sided comparison, concluded**: the frozen formal term sits strictly BELOW
the source budget at the evaluation point (indeed below one excess `Y`, which itself sits
below the source budget).  `termCnl(frozen) <= 7/32 < 7/16 <= Y < source`. -/
theorem termCnl_frozen_lt_sourceH1
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    termCnl (faithfulCapacityPhases budget ctx).toClosurePhaseData
      < sourceH1CnlBudgetPerFibre ctx :=
  lt_trans (termCnl_faithful_lt_Y budget ctx) (Y_lt_sourceH1CnlBudgetPerFibre ctx)

/-! ## Part 3.  The corrected class-1 capacity term

The formal global ledger consumes the per-phase cap `manuscript_bound :
CQ^M * shellFactor * X * Ij <= cStar*xi*X/6`; the corrected datum keeps the GENUINE
surviving clean-CNL family and re-scales the shell/interval normalization so the realized
term saturates that cap exactly: `termCnl(corrected) = (cStar*xi/6) * X = (31/1536)*X`.
This is the maximal class-1 capacity the in-tree calibration admits, and it is dominated
by the source budget shape at the evaluation point throughout the manuscript regime. -/

/-- The per-class share of the formal global phase budget: `cStar*xi/6 = 31/1536`. -/
theorem correctedCnlShare_eq :
    erdos260Constants.cStar * erdos260Constants.ξ / 6 = 31 / 1536 := by
  have h1 : erdos260Constants.cStar = manuscriptCstar := rfl
  have h2 : erdos260Constants.ξ = manuscriptXi := rfl
  rw [h1, h2]
  unfold manuscriptCstar manuscriptXi
  norm_num

/-- The share numerator is nonnegative. -/
theorem correctedCnlShare_num_nonneg :
    (0 : ℝ) ≤ erdos260Constants.cStar * erdos260Constants.ξ := by
  have h1 : erdos260Constants.cStar = manuscriptCstar := rfl
  have h2 : erdos260Constants.ξ = manuscriptXi := rfl
  rw [h1, h2]
  unfold manuscriptCstar manuscriptXi
  norm_num

/-- At Kraft slope `c = 0` the weighted Kraft sum is the raw family count. -/
theorem cleanCNLKraftSum_c_zero {α : Type _} (paths : Finset α) (H : α → ℝ) :
    cleanCNLKraftSum paths H 0 = (paths.card : ℝ) := by
  unfold cleanCNLKraftSum
  have h : ∀ p ∈ paths, (2 : ℝ) ^ (-(0 * H p)) = 1 := by
    intro p _
    rw [zero_mul, neg_zero, Real.rpow_zero]
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- The genuine surviving clean-CNL family count is positive (in `ℝ`). -/
theorem auditFamilyCard_pos (ctx : ActualFailureContext) :
    (0 : ℝ) < ((selectedTransitions (liftTransitionsOfShell ctx)).card : ℝ) := by
  exact_mod_cast cnl_target_card_pos ctx

/-- The corrected normalization collapse: `card * (share / (6*card)) = share / 6`. -/
theorem correctedCnl_collapse (ctx : ActualFailureContext) :
    ((selectedTransitions (liftTransitionsOfShell ctx)).card : ℝ)
        * (erdos260Constants.cStar * erdos260Constants.ξ
            / (6 * ((selectedTransitions (liftTransitionsOfShell ctx)).card : ℝ)))
      = erdos260Constants.cStar * erdos260Constants.ξ / 6 := by
  have hK : ((selectedTransitions (liftTransitionsOfShell ctx)).card : ℝ) ≠ 0 :=
    ne_of_gt (auditFamilyCard_pos ctx)
  field_simp

/-- **The corrected clean-CNL phase datum.**  Same genuine surviving family; the scalar
normalization re-scaled to the full per-class budget share (the manuscript-faithful
calibration inside the in-tree `X`-unit ledger): `shellFactor = share/(6*card)`,
`|I_j| = 1`, Kraft slope `0` (raw count -- the G.35 constant-base bound holds a
fortiori), so `termCnl = (cStar*xi/6)*X` exactly and `manuscript_bound` holds with
equality. -/
def correctedCnlData (ctx : ActualFailureContext) :
    CNLClusterEncodingData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : ℝ) where
  α := CNLTransition
  paths := selectedTransitions (liftTransitionsOfShell ctx)
  BNDHeight := fun t => (bndHeightNatOfShell ctx t : ℝ)
  c := 0
  CQ := ((selectedTransitions (liftTransitionsOfShell ctx)).card : ℝ)
  M := 1
  shellFactor := erdos260Constants.cStar * erdos260Constants.ξ
      / (6 * ((selectedTransitions (liftTransitionsOfShell ctx)).card : ℝ))
  Ij := 1
  shellFactor_nonneg := by
    apply div_nonneg correctedCnlShare_num_nonneg
    positivity
  Ij_nonneg := by norm_num
  kraftSum_le := by
    rw [cleanCNLKraftSum_c_zero, pow_one]
  manuscript_bound := by
    rw [pow_one, correctedCnl_collapse, mul_one]
    exact le_of_eq (by ring)

/-- **The corrected six-phase assembly**: `faithfulCapacityPhases` with ONLY the `cnl`
slot replaced by the corrected datum.  The other five phase data are untouched. -/
def correctedCapacityPhases
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : ℝ) :=
  { faithfulCapacityPhases budget ctx with cnl := correctedCnlData ctx }

/-- The Chernoff term is unchanged by the correction (`rfl`). -/
theorem termChernoff_corrected
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    termChernoff (correctedCapacityPhases budget ctx).toClosurePhaseData
      = termChernoff (faithfulCapacityPhases budget ctx).toClosurePhaseData := rfl

/-- The DensePack term is unchanged by the correction (`rfl`). -/
theorem termDensePack_corrected
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    termDensePack (correctedCapacityPhases budget ctx).toClosurePhaseData
      = termDensePack (faithfulCapacityPhases budget ctx).toClosurePhaseData := rfl

/-- The Tower term is unchanged by the correction (`rfl`). -/
theorem termTower_corrected
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    termTower (correctedCapacityPhases budget ctx).toClosurePhaseData
      = termTower (faithfulCapacityPhases budget ctx).toClosurePhaseData := rfl

/-- The Return term is unchanged by the correction (`rfl`). -/
theorem termReturn_corrected
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    termReturn (correctedCapacityPhases budget ctx).toClosurePhaseData
      = termReturn (faithfulCapacityPhases budget ctx).toClosurePhaseData := rfl

/-- The Run term is unchanged by the correction (`rfl`). -/
theorem termRun_corrected
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    termRun (correctedCapacityPhases budget ctx).toClosurePhaseData
      = termRun (faithfulCapacityPhases budget ctx).toClosurePhaseData := rfl

/-- **The corrected class-1 term, evaluated exactly**:
`termCnl(corrected) = (cStar*xi/6) * X` -- the full per-class share of the formal global
phase budget, `(31/1536)*X`. -/
theorem termCnl_corrected_eq
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    termCnl (correctedCapacityPhases budget ctx).toClosurePhaseData
      = erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have h0 : termCnl (correctedCapacityPhases budget ctx).toClosurePhaseData
      = cleanCNLKraftSum (selectedTransitions (liftTransitionsOfShell ctx))
          (fun t => (bndHeightNatOfShell ctx t : ℝ)) 0
        * (erdos260Constants.cStar * erdos260Constants.ξ
            / (6 * ((selectedTransitions (liftTransitionsOfShell ctx)).card : ℝ)))
        * (ctx.shell.X : ℝ) * 1 := rfl
  rw [h0, cleanCNLKraftSum_c_zero, mul_one, correctedCnl_collapse]

/-- **The correction only enlarges the term**: the frozen faithful term is dominated by
the corrected one on every shell (`7/32 <= (31/1536)*X` for `X >= 2^28`).  Hence every
discharge of the frozen class-1 bound transports to the corrected surface. -/
theorem termCnl_frozen_le_corrected
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    termCnl (faithfulCapacityPhases budget ctx).toClosurePhaseData
      ≤ termCnl (correctedCapacityPhases budget ctx).toClosurePhaseData := by
  have h1 := termCnl_faithful_le_7_32 budget ctx
  rw [termCnl_corrected_eq budget ctx, correctedCnlShare_eq]
  have hX := shell_X_ge_real ctx
  linarith

/-- **The de-razoring inequality**: the corrected class-1 capacity absorbs a FULL pinned
excess on every shell, `Y < termCnl(corrected)` (`L/64 < X/64 <= (31/1536)*X`) -- in sharp
contrast with the frozen term (`termCnl(frozen) < Y`, the razor). -/
theorem Y_lt_termCnl_corrected
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    ctx.n24CarryData.Y < termCnl (correctedCapacityPhases budget ctx).toClosurePhaseData := by
  rw [termCnl_corrected_eq budget ctx, correctedCnlShare_eq, n24CarryData_Y_eq_div]
  have hXeq : ctx.shell.X = 2 ^ shellLadderDepth ctx :=
    Classical.choose_spec ctx.shell.hXdyadic
  have hL : shellLadderDepth ctx < ctx.shell.X := by
    rw [hXeq]; exact Nat.lt_two_pow_self
  have hLr : (shellLadderDepth ctx : ℝ) < (ctx.shell.X : ℝ) := by exact_mod_cast hL
  have hX0 : (0 : ℝ) ≤ (ctx.shell.X : ℝ) := Nat.cast_nonneg _
  linarith

/-! ## Part 4.  Survivor closures enabled by the corrected term

The class-1 routed mass on the genuine route is EXACTLY `card * Y`
(`routedClassMass_one_eq_card_mul_Y`), so every proved per-context count cap `card <= n`
closes the corrected ledger bound as soon as `n * Y <= (31/1536)*X`.  The wave-14 caps:
`|fibre_1| <= 1` on every `r = 0` shell (all `L <= 15420`,
`class1Fibre_card_le_one_of_r_eq_zero`), and the per-pair cycle-density caps
`|fibre_1| <= b_4 * ceil(W/c)` (`class1Fibre_card_le_cycleDensity`). -/

/-- **Generic count-cap absorption** for the corrected class-1 ledger bound, over any
budget routed by the genuine first-obstruction route. -/
theorem correctedHCnl_of_card_cap
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext)
    (hroute : (budget ctx).route = genuineChargeRoute ctx)
    (n : ℕ)
    (hcard : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card ≤ n)
    (habs : (n : ℝ) * ctx.n24CarryData.Y
        ≤ termCnl (correctedCapacityPhases budget ctx).toClosurePhaseData) :
    routedClassMassOf ctx.n24CarryData (budget ctx).route 1
      ≤ termCnl (correctedCapacityPhases budget ctx).toClosurePhaseData := by
  rw [hroute, routedClassMass_one_eq_card_mul_Y]
  have hY : (0 : ℝ) ≤ ctx.n24CarryData.Y := le_of_lt (n24CarryData_Y_pos ctx)
  have hn : ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
      ≤ (n : ℝ) := by exact_mod_cast hcard
  calc ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ (n : ℝ) * ctx.n24CarryData.Y := mul_le_mul_of_nonneg_right hn hY
    _ ≤ termCnl (correctedCapacityPhases budget ctx).toClosurePhaseData := habs

/-- **Survivor closure 1 (`r = 0` shells, UNCONDITIONAL)**: on every shell with carry
order `r = floor(kappa*L) = 0`, the corrected class-1 ledger bound is closed outright --
the proved cap `|fibre_1| <= 1` and `Y < (31/1536)*X`.  The frozen term demanded outright
emptiness even here. -/
theorem correctedHCnl_of_r_eq_zero
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext)
    (hroute : (budget ctx).route = genuineChargeRoute ctx)
    (hr : ctx.n24CarryData.r = 0) :
    routedClassMassOf ctx.n24CarryData (budget ctx).route 1
      ≤ termCnl (correctedCapacityPhases budget ctx).toClosurePhaseData :=
  correctedHCnl_of_card_cap budget ctx hroute 1
    (class1Fibre_card_le_one_of_r_eq_zero ctx hr)
    (by
      rw [Nat.cast_one, one_mul]
      exact le_of_lt (Y_lt_termCnl_corrected budget ctx))

/-- **Survivor closure 1' (explicit shell range)**: every shell with `L <= 15420` closes
(the `r = floor(kappa*L) = 0` regime, `kappa = 17/2^18`). -/
theorem correctedHCnl_of_L_le
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext)
    (hroute : (budget ctx).route = genuineChargeRoute ctx)
    (hL : shellLadderDepth ctx ≤ 15420) :
    routedClassMassOf ctx.n24CarryData (budget ctx).route 1
      ≤ termCnl (correctedCapacityPhases budget ctx).toClosurePhaseData :=
  correctedHCnl_of_r_eq_zero budget ctx hroute (n24_r_eq_zero_of_L_le ctx hL)

/-- **Survivor closure 2 (wave-14 cycle-density caps)**: on any context carrying a
certified orbit period `c`, the per-pair count cap
`|fibre_1| <= #band4 * ceil(W/c)` (`class1Fibre_card_le_cycleDensity`) closes the
corrected bound whenever it numerically fits under the share
(`cap * Y <= (31/1536)*X` -- the absorption gate `habs`). -/
theorem correctedHCnl_of_cycleDensity
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext)
    (hroute : (budget ctx).route = genuineChargeRoute ctx)
    {c : ℕ} (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (habs : (((class1Band4CycleBand ctx c).card
          * (((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c) : ℕ) : ℝ)
        * ctx.n24CarryData.Y
        ≤ termCnl (correctedCapacityPhases budget ctx).toClosurePhaseData) :
    routedClassMassOf ctx.n24CarryData (budget ctx).route 1
      ≤ termCnl (correctedCapacityPhases budget ctx).toClosurePhaseData :=
  correctedHCnl_of_card_cap budget ctx hroute _
    (class1Fibre_card_le_cycleDensity ctx hc hper) habs

/-! ## Part 5.  The re-based ledger bridge

The corrected residual surface, with the COMPLETE bridge to `Erdos260Statement` through
the polymorphic assembly (`RoutedHighExcessChargeDataOldRes` at `oldResMass = 0`,
`GlobalAssemblyActualInputs`, `erdos260_final_actual`) -- no transport through the
frozen-term consumers is needed. -/

/-- **The corrected ctx-pinned P9 ledger residual**: the five per-context ledger bounds
over `budget ctx`, `ctx.n24CarryData`, and the CORRECTED phases
`correctedCapacityPhases budget ctx`, plus class-6 vacancy.  Identical to
`P9CtxPinnedLedgerResidual` except (i) the class-1 capacity is the corrected share
`(31/1536)*X` instead of the frozen `<= 7/32`, and (ii) the class-6 bound is the genuine
vacancy `<= 0` (automatic on the genuine route,
`genuineChargeRoute_routed6_zero`). -/
structure CorrectedP9CtxPinnedLedgerResidual where
  /-- The shared seven-class routed budget and the class 2/4/5 capacity slots. -/
  budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx
  /-- Class 0, Chernoff/shell-paid progress, against the corrected phases. -/
  hChernoff : ∀ ctx : ActualFailureContext,
    routedClassMassOf ctx.n24CarryData (budget ctx).route 0
      ≤ termChernoff (correctedCapacityPhases budget ctx).toClosurePhaseData
  /-- Class 1, clean-CNL, against the CORRECTED capacity term `(31/1536)*X`. -/
  hCnl : ∀ ctx : ActualFailureContext,
    routedClassMassOf ctx.n24CarryData (budget ctx).route 1
      ≤ termCnl (correctedCapacityPhases budget ctx).toClosurePhaseData
  /-- Class 3, DensePack marker mass, against the corrected phases. -/
  hDensePack : ∀ ctx : ActualFailureContext,
    routedClassMassOf ctx.n24CarryData (budget ctx).route 3
      ≤ termDensePack (correctedCapacityPhases budget ctx).toClosurePhaseData
  /-- Classes 2+4+5, Tower+Return+Run, bounded jointly by N.24 TRT. -/
  hTRT : ∀ ctx : ActualFailureContext,
    routedClassMassOf ctx.n24CarryData (budget ctx).route 2
        + routedClassMassOf ctx.n24CarryData (budget ctx).route 4
        + routedClassMassOf ctx.n24CarryData (budget ctx).route 5
      ≤ termTower (correctedCapacityPhases budget ctx).toClosurePhaseData
        + termReturn (correctedCapacityPhases budget ctx).toClosurePhaseData
        + termRun (correctedCapacityPhases budget ctx).toClosurePhaseData
  /-- Class 6, the old-residual class, genuinely vacant. -/
  hOldRes : ∀ ctx : ActualFailureContext,
    routedClassMassOf ctx.n24CarryData (budget ctx).route 6 ≤ 0

namespace CorrectedP9CtxPinnedLedgerResidual

/-- The corrected residual's per-context seven-class routed package at
`oldResMass = 0`, over the corrected phases. -/
def routingZero (R : CorrectedP9CtxPinnedLedgerResidual) (ctx : ActualFailureContext) :
    RoutedHighExcessChargeDataOldRes (correctedCapacityPhases R.budget ctx)
      ctx.n24CarryData 0 where
  route := (R.budget ctx).route
  hChernoff := R.hChernoff ctx
  hCnl := R.hCnl ctx
  hDensePack := R.hDensePack ctx
  hTRT := R.hTRT ctx
  hOldRes := R.hOldRes ctx

/-- The corrected actual-assembly inputs: the canonical carry data and the corrected
phase package, with the high-excess charge from the corrected routing at zero
old-residual mass. -/
def toActualInputs (R : CorrectedP9CtxPinnedLedgerResidual) :
    GlobalAssemblyActualInputs where
  carryData := fun ctx => ctx.n24CarryData
  chernoff := fun ctx => (correctedCapacityPhases R.budget ctx).chernoff
  cnl := fun ctx => (correctedCapacityPhases R.budget ctx).cnl
  densePack := fun ctx => (correctedCapacityPhases R.budget ctx).densePack
  tower := fun ctx => (correctedCapacityPhases R.budget ctx).tower
  returnPkg := fun ctx => (correctedCapacityPhases R.budget ctx).returnPkg
  run := fun ctx => (correctedCapacityPhases R.budget ctx).run
  highExcessCharge := fun ctx => by
    change HighExcessChargeData (correctedCapacityPhases R.budget ctx) ctx.n24CarryData
    exact (R.routingZero ctx).toHighExcessChargeData_of_oldRes_nonpos le_rfl

/-- **The re-based ledger bridge**: the corrected residual proves `Erdos260Statement`
through the polymorphic actual assembly. -/
theorem toStatement (R : CorrectedP9CtxPinnedLedgerResidual) : Erdos260Statement :=
  erdos260_final_actual R.toActualInputs

/-- **Monotone weakening**: the OLD (frozen-term) routed-zero pinned residual implies the
corrected residual -- the corrected surface is never harder.  (Classes 0/3/TRT/6
transport unchanged; class 1 by `termCnl(frozen) <= termCnl(corrected)`.) -/
def ofPinnedRoutingZero (R : P9CtxPinnedRoutingZeroResidual) :
    CorrectedP9CtxPinnedLedgerResidual where
  budget := R.budget
  hChernoff := fun ctx => by
    have h := (R.routingZero ctx).hChernoff
    rw [R.route_eq ctx] at h
    rw [termChernoff_corrected]
    exact h
  hCnl := fun ctx => by
    have h := (R.routingZero ctx).hCnl
    rw [R.route_eq ctx] at h
    exact le_trans h (termCnl_frozen_le_corrected R.budget ctx)
  hDensePack := fun ctx => by
    have h := (R.routingZero ctx).hDensePack
    rw [R.route_eq ctx] at h
    rw [termDensePack_corrected]
    exact h
  hTRT := fun ctx => by
    have h := (R.routingZero ctx).hTRT
    rw [R.route_eq ctx] at h
    rw [termTower_corrected, termReturn_corrected, termRun_corrected]
    exact h
  hOldRes := fun ctx => by
    have h := (R.routingZero ctx).hOldRes
    rw [R.route_eq ctx] at h
    exact h

/-- **The corrected residual from genuine-route caps**: over any budget routed by the
genuine first-obstruction route, the corrected residual needs only (i) the class-0 and
class-3 charging bounds (stated against the faithful = corrected terms) and (ii) the
class-1 count-cap absorption `card * Y <= termCnl(corrected)`; `hTRT` is closed
generically by the N.24 compression (`seedHTRT`) and `hOldRes` by the genuine route's
class-6 vacancy.  On `r = 0` shells the class-1 input (ii) is automatic
(`correctedHCnl_of_r_eq_zero`). -/
def ofGenuineCaps
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (hroute : ∀ ctx : ActualFailureContext, (budget ctx).route = genuineChargeRoute ctx)
    (hChernoff : ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (budget ctx).route 0
        ≤ termChernoff (faithfulCapacityPhases budget ctx).toClosurePhaseData)
    (hDensePack : ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (budget ctx).route 3
        ≤ termDensePack (faithfulCapacityPhases budget ctx).toClosurePhaseData)
    (hcap : ∀ ctx : ActualFailureContext,
      ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
          * ctx.n24CarryData.Y
        ≤ termCnl (correctedCapacityPhases budget ctx).toClosurePhaseData) :
    CorrectedP9CtxPinnedLedgerResidual where
  budget := budget
  hChernoff := fun ctx => by
    rw [termChernoff_corrected]
    exact hChernoff ctx
  hCnl := fun ctx => by
    rw [hroute ctx, routedClassMass_one_eq_card_mul_Y]
    exact hcap ctx
  hDensePack := fun ctx => by
    rw [termDensePack_corrected]
    exact hDensePack ctx
  hTRT := fun ctx => by
    rw [termTower_corrected, termReturn_corrected, termRun_corrected]
    exact seedHTRT budget ctx
  hOldRes := fun ctx => by
    rw [hroute ctx]
    exact le_of_eq (genuineChargeRoute_routed6_zero ctx)

end CorrectedP9CtxPinnedLedgerResidual

/-- Final endpoint from the corrected ctx-pinned P9 ledger residual. -/
theorem erdos260_of_correctedP9Ledger
    (R : CorrectedP9CtxPinnedLedgerResidual) : Erdos260Statement :=
  R.toStatement

/-- Sanity commutation: the old pinned routed-zero residual reaches the statement through
the corrected bridge as well. -/
theorem erdos260_of_pinnedRoutingZero_via_corrected
    (R : P9CtxPinnedRoutingZeroResidual) : Erdos260Statement :=
  (CorrectedP9CtxPinnedLedgerResidual.ofPinnedRoutingZero R).toStatement

/-- The wave-12 v3 budget instantiation of the unconditional `r = 0` survivor closure:
on every `r = 0` shell the corrected class-1 ledger bound over the v3 budget is closed
outright (no emptiness demand). -/
theorem correctedHCnl_v3_of_r_eq_zero
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runChain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0) :
    routedClassMassOf ctx.n24CarryData
        ((v3Budget towerCount runChain returnCharge ctx).route) 1
      ≤ termCnl (correctedCapacityPhases (v3Budget towerCount runChain returnCharge)
          ctx).toClosurePhaseData :=
  correctedHCnl_of_r_eq_zero (v3Budget towerCount runChain returnCharge) ctx
    (v3Budget_route towerCount runChain returnCharge ctx) hr

/-! ## Part 6.  Honest status inventory and the audit block -/

/-- Machine-readable, honest status of the ledger calibration audit. -/
def ledgerCalibrationAuditStatus : List String :=
  [ "OBJECT: the class-1 (clean-CNL) capacity term of the P9 ledger " ++
      "(P9CtxPinnedLedgerResidual.hCnl over faithfulCapacityPhases), consumed by " ++
      "toStatement through erdos260_charge_reduced_of_routing / " ++
      "RoutedHighExcessChargeDataOldRes.highExcess_le_phaseMass_add_oldRes (the H.1/I.11' " ++
      "transcription) against the cPr*X floor and the cStar*xi*X/6 per-phase caps.",
    "PROVENANCE PINS (rfl, PROVED): the consumed faithful term has shellFactor = " ++
      "2^(-(c0*eta*X)) (exponent frozen at Y := X; auditFrozenShellFactor) and |I_j| = " ++
      "2^(-M), M = L + |CNLTransition| (one Kraft cylinder; auditFrozenIj, " ++
      "auditFrozenTiling X*|I_j| <= 1) over the genuine surviving family " ++
      "(auditFrozenFamily); hence termCnl <= 14/64 = 7/32 < 7/16 <= Y and the ledger " ++
      "bound IS fibre emptiness (auditRazor, re-export of class1Ledger_iff_fibre_empty).",
    "SOURCE COUNTERPART (tex, proof_v4_unconditional_clean_v5.tex): |I_j| = c_I*L is the " ++
      "THRESHOLD interval of (2.0) lines 289-298 / (K.20) lines 5363-5372; the H.1 CNL " ++
      "term is X*|I_j|*2^(-c*Y) with the exponent AT THE ACTIVE FLOOR Y in [c_Y*L, C_Y*L] " ++
      "(H.1 lines 2725-2740, H.2 lines 2709-2724, K.4 item 3 lines 5378-5385, I.0c''' " ++
      "lines 3085-3091, charging direction line 3382); per-class budgets xi*s*X*|I_j| " ++
      "GROW in the stage s (H.2' lines 2755-2768, H.3' lines 2786-2795); evaluation at " ++
      "the contradiction stage s = r = floor(kappa*L), j = 0, Y = eps*L (H.4' lines " ++
      "2838-2848) against the floor c_pr*r*X*|I_0| (H.5 lines 2851-2868; K.5 display " ++
      "lines 5455-5469); assembly: J.6 4319+, L.1 5482+, L.2 5891+, I.2 3233+.",
    "COMPARISON AT THE EVALUATION POINT (PROVED, exact constants): formal frozen term " ++
      "<= 7/32 (termCnl_faithful_le_7_32) < Y = L/64 (termCnl_faithful_lt_Y); source " ++
      "budget per threshold fibre X*2^(-c0*eta*eps*L) with c0*eta*eps = 17/2^34 <= 1/2 " ++
      "(sourceH1_exponent_le_half), so source >= 2^(L/2) > Y " ++
      "(Y_lt_sourceH1CnlBudgetPerFibre) > 7/32 >= frozen (termCnl_frozen_lt_sourceH1); " ++
      "exponent freeze quantified by auditFrozenExponent_gt_source (c0*eta*eps*L < " ++
      "c0*eta*X).",
    "VERDICT: the formalized faithful term is a SMALLER FROZEN VALUE - |I_j| frozen to " ++
      "the single Kraft cylinder 2^(-M) instead of the threshold interval c_I*L, the " ++
      "shell-Chernoff exponent frozen at Y := X instead of the active floor, and no " ++
      "stage factor - NOT the source's budget at the evaluation stage.  The emptiness " ++
      "demand (the razor) is a transcription artifact: the source ledger admits ~ " ++
      "2^((1-c*eps)*L)*64/L surviving class-1 starts at the contradiction stage and " ++
      "never demands |fibre_1| = 0.",
    "CORRECTION (PROVED): correctedCnlData keeps the genuine family and re-scales the " ++
      "shell/interval normalization to SATURATE the consumed per-class budget cap: " ++
      "termCnl(corrected) = cStar*xi/6*X = (31/1536)*X exactly (termCnl_corrected_eq), " ++
      "manuscript_bound holds with equality; correctedCapacityPhases changes ONLY the " ++
      "cnl slot (five rfl term transports); frozen <= corrected " ++
      "(termCnl_frozen_le_corrected) and Y < corrected (Y_lt_termCnl_corrected, the " ++
      "de-razoring).",
    "RE-BASED LEDGER BRIDGE (PROVED): CorrectedP9CtxPinnedLedgerResidual carries the " ++
      "five ledger bounds over the corrected phases + class-6 vacancy; toStatement " ++
      "reaches Erdos260Statement through RoutedHighExcessChargeDataOldRes (oldResMass = " ++
      "0) -> HighExcessChargeData -> GlobalAssemblyActualInputs -> " ++
      "erdos260_final_actual; ofPinnedRoutingZero: the OLD frozen residual implies the " ++
      "corrected one; ofGenuineCaps: hTRT/hOldRes closed generically (seedHTRT, " ++
      "genuineChargeRoute_routed6_zero), leaving classes 0/3 plus the class-1 count-cap " ++
      "absorption.",
    "SURVIVOR CLOSURES ENABLED (PROVED): r = 0 shells (ALL L <= 15420) close OUTRIGHT - " ++
      "correctedHCnl_of_r_eq_zero / correctedHCnl_of_L_le / correctedHCnl_v3_of_r_eq_zero " ++
      "via the wave cap |fibre_1| <= 1 (class1Fibre_card_le_one_of_r_eq_zero) and Y < " ++
      "(31/1536)*X; the wave-14 per-pair cycle-density caps b_4*ceil(W/c) close under " ++
      "the numeric absorption gate cap*Y <= (31/1536)*X (correctedHCnl_of_cycleDensity, " ++
      "correctedHCnl_of_card_cap).",
    "HONEST RESIDUAL: the corrected term is the MAXIMAL capacity the in-tree X-unit " ++
      "calibration admits (floor cPr*X = X/2, total budget 31/256*X); it does NOT " ++
      "reproduce the source's r*X*|I_0| ~ L^2*X scale (re-basing the floor spine is out " ++
      "of additive scope and unnecessary for the proved closures).  Deep shells (L > " ++
      "15420) whose proved count caps exceed (31/24)*X/L remain open on the class-1 " ++
      "axis - now under an honest capacity instead of a sub-excess frozen one.  Nothing " ++
      "here closes the global P9 residual.",
    "SOURCE-PATCH RECOMMENDATION: none for the source text (its H.1/K.4 calibration is " ++
      "consistent); the patch target is the formal frozen choice cnlShellFactorOfShell / " ++
      "cnlIjOfShell (CNLScalarBudgetCore.lean) - read the exponent at the active floor Y " ++
      "and |I_j| at the (2.0) threshold-interval scale, which inside the in-tree X-unit " ++
      "ledger is exactly the correctedCnlData re-scaling." ]

theorem ledgerCalibrationAuditStatus_nonempty :
    ledgerCalibrationAuditStatus ≠ [] := by
  simp [ledgerCalibrationAuditStatus]

#print axioms auditFrozenShellFactor
#print axioms auditFrozenIj
#print axioms auditFrozenFamily
#print axioms auditFrozenTiling
#print axioms auditFrozenExponent_gt_source
#print axioms auditRazor
#print axioms sourceH1CnlBudgetPerFibre
#print axioms sourceH1_exponent_le_half
#print axioms Y_lt_sourceH1CnlBudgetPerFibre
#print axioms termCnl_frozen_lt_sourceH1
#print axioms correctedCnlShare_eq
#print axioms cleanCNLKraftSum_c_zero
#print axioms correctedCnlData
#print axioms correctedCapacityPhases
#print axioms termCnl_corrected_eq
#print axioms termCnl_frozen_le_corrected
#print axioms Y_lt_termCnl_corrected
#print axioms correctedHCnl_of_card_cap
#print axioms correctedHCnl_of_r_eq_zero
#print axioms correctedHCnl_of_L_le
#print axioms correctedHCnl_of_cycleDensity
#print axioms CorrectedP9CtxPinnedLedgerResidual.routingZero
#print axioms CorrectedP9CtxPinnedLedgerResidual.toActualInputs
#print axioms CorrectedP9CtxPinnedLedgerResidual.toStatement
#print axioms CorrectedP9CtxPinnedLedgerResidual.ofPinnedRoutingZero
#print axioms CorrectedP9CtxPinnedLedgerResidual.ofGenuineCaps
#print axioms erdos260_of_correctedP9Ledger
#print axioms erdos260_of_pinnedRoutingZero_via_corrected
#print axioms correctedHCnl_v3_of_r_eq_zero
#print axioms ledgerCalibrationAuditStatus_nonempty

end

end Erdos260
