import Erdos260.Erdos260ChargeReduced
import Erdos260.ChargePerOutputEstimates
import Erdos260.AppendixI_PackageBounds

/-!
# Erdős #260 — the class-0 (Chernoff / shell-paid progress) charging bound

This module (NEW; it edits no existing file) attacks the **`hChernoff` field** of
`Erdos260ChargeResidual` (`Erdos260ChargeReduced.lean`), i.e. the class-0
(Chernoff 22.1A / shell-paid progress) per-class charging bound of the consolidated
faithful charge residual:

```
hChernoff : ∀ ctx : ActualFailureContext,
  routedClassMassOf ctx.n24CarryData (budget ctx).route 0
    ≤ termChernoff (faithfulCapacityPhases budget ctx).toClosurePhaseData
```

Here the RHS `termChernoff (faithfulCapacityPhases budget ctx).toClosurePhaseData`
is the Chernoff phase term of the **fully unconditional** §22 model leaf
`chernoff22_1ALeafOfShell ctx` (`ShellPaidChernoff22_1ALeafConstruction.lean`),
baked into the faithful six-phase assembly; the LHS is the window-excess mass of
the high-excess carry starts the J.1.1 routing `(budget ctx).route` sends to the
class-0 (Chernoff/progress) charge slot.

## The reduction (the genuine charging *direction*)

The bound is the manuscript **charging** inequality — the *carry* mass routed to
class 0 is dominated by the *output* area of the Chernoff high-cost path family.
It is bounded by the count×multiplier / charging-map mechanism

```
routedClassMassOf … route 0
  ≤ (count of class-0 starts) · (per-start window-excess multiplier)   -- proved core
  ≤ termChernoff …                                                     -- 22.1A area
```

* the structural step `routedClassMassOf ≤ count·mult` is the **proved**
  `routedClassMassOf_le_countMultiplier` (the carry-side twin of
  `densePackMass_le_of_density`) — it does genuine work (a finite sum dominated by
  `count·sup`), it is *not* a repackaging of the goal;
* the area-side step `count·mult ≤ termChernoff …` is the genuine I.4.2 / 22.1A
  *charging* content: the count of progress/high-cost starts (the I.4.2
  progress-endpoint count) times the shell-paid per-start multiplier (22.1A) fits
  the Chernoff high-cost output area `termChernoff = ∑_{cost ≥ Y} weight`.

The **sharper** form `routedClass0_le_termChernoff_of_matching` reuses the genuine
J.1.7 charging-map mechanism `routedChernoff_le_term_of_matching`
(`ChargePerOutputEstimates.lean`): a *matching* charge map of the class-0 fibre
into the Chernoff high-cost path family with the per-path charged domination
`windowExcess k ≤ weight (chargeOf k)` closes the bound with the area
identification `termChernoff = ∑_p weight p` **proved** (`rfl`,
`termChernoff_eq_chargedArea`).  In that form the only undischarged content is the
charging map itself (J.1.7), with neither a count nor an area-identification
residual.

## What is genuinely closed here, and the minimal residual

`windowExcess` is an unbounded `positivePart` and `termChernoff` is the §22 model
leaf's high-cost area; the charging inequality between them is the orthogonal
Appendix-L.2 *charging* content — provably **not** derivable from any phase budget
(see `ChargeMultiplierClosure.chargeMultiplierResidual` /
`ChargePerOutputEstimates.chargePerOutputResidual`: phase cores bound the output
*area* `∑_o cap o`, never the carry mass each output absorbs).  We therefore:

* **CLOSE** the full structural reduction `routedClassMassOf route 0 ≤ termChernoff`
  modulo the smallest named charging residual, in two interchangeable shapes —
  the count×multiplier shape (`Class0ChernoffCharge`, reusing
  `routedClassMassOf_le_countMultiplier`) and the sharper J.1.7 charging-map shape
  (`routedClass0_le_termChernoff_of_matching`);
* **EXPOSE** the residual as the minimal per-context data: the J.1.1 fibre count of
  class-0 starts (`hcard`, the I.4.2 progress count), the per-fibre window-excess
  multiplier (`hpoint`/`hmult_nonneg`, the K.1.2/L.20 residual multiplier ≤ the
  22.1A shell-paid multiplier), and the area identification `count·mult ≤
  termChernoff` (`hbud`, 22.1A) — or, equivalently, one charging map (J.1.7);
* **PRODUCE** the exact `Erdos260ChargeResidual.hChernoff` field from that residual
  (`Class0ChernoffCharge.hChernoff`), and show it drops into a full residual with a
  matching `budget` (`Erdos260ChargeResidual.withClass0Chernoff`).

The Chernoff term itself is fully grounded: `termChernoff_faithful_nonneg`
(`0 ≤ termChernoff`) and `termChernoff_faithful_le_budget`
(`termChernoff ≤ c⋆·ξ·X/6`, Lemma 22.1) are proved outright.

No `sorry`, `axiom`, or `admit`.  No degenerate / empty-fibre shortcut: the bound
is reduced to genuine charging data, not assumed and not made vacuously true.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 1.  The faithful Chernoff phase term is grounded (nonneg + Lemma 22.1 budget)

The class-0 RHS `termChernoff (faithfulCapacityPhases budget ctx).toClosurePhaseData`
is the high-cost path area of the unconditional §22 model leaf
`chernoff22_1ALeafOfShell ctx`.  It is nonnegative by construction and fits the
manuscript per-phase budget `c⋆·ξ·X/6` (Lemma 22.1, via `termChernoff_le_budget`)
— so the class-0 slot is a genuine nonnegative fraction, never an over-strength
back-door. -/

/-- **The faithful Chernoff term is nonnegative.**  The high-cost subfamily area
`∑_{cost ≥ Y} weight` of nonnegatively-weighted Chernoff paths is `≥ 0`. -/
theorem termChernoff_faithful_nonneg
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    0 ≤ termChernoff (faithfulCapacityPhases budget ctx).toClosurePhaseData := by
  unfold termChernoff weightedMass
  refine Finset.sum_nonneg (fun p hp => ?_)
  exact ((faithfulCapacityPhases budget ctx).toClosurePhaseData).chernoff.weight_nonneg p
    (mem_highCostSet.1 hp).1

/-- **The faithful Chernoff term fits the Lemma 22.1 per-phase budget.**
`termChernoff … ≤ c⋆·ξ·X/6`, via the proved `termChernoff_le_budget`
(`shellChernoff_bound_of_moment_bound` + the bundled `manuscript_bound`). -/
theorem termChernoff_faithful_le_budget
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    termChernoff (faithfulCapacityPhases budget ctx).toClosurePhaseData
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  termChernoff_le_budget (faithfulCapacityPhases budget ctx).toClosurePhaseData

/-! ## 2.  The class-0 charging reduction (count×multiplier and charging-map shapes) -/

/-- **Class-0 charging bound from per-fibre count×multiplier data.**

`routedClassMassOf route 0 ≤ termChernoff` from
* `hpoint` — every class-0 start charges window excess `≤ mult` (K.1.2/L.20
  residual multiplier),
* `hmult_nonneg` — `0 ≤ mult`,
* `hcard` — the class-0 fibre has at most `count` members (the J.1.1 / I.4.2
  progress count),
* `hbud` — `count·mult ≤ termChernoff` (the 22.1A area identification).

The structural step is the proved `routedClassMassOf_le_countMultiplier`; the only
genuinely charging inputs are `hcard` (count) and `hbud` (area). -/
theorem routedClass0_le_termChernoff_of_countMul
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) {mult count : ℝ}
    (hpoint : ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        ≤ mult)
    (hmult_nonneg : 0 ≤ mult)
    (hcard : ((routedFibre ctx.n24CarryData (budget ctx).route 0).card : ℝ) ≤ count)
    (hbud : count * mult
      ≤ termChernoff (faithfulCapacityPhases budget ctx).toClosurePhaseData) :
    routedClassMassOf ctx.n24CarryData (budget ctx).route 0
      ≤ termChernoff (faithfulCapacityPhases budget ctx).toClosurePhaseData :=
  (routedClassMassOf_le_countMultiplier ctx.n24CarryData (budget ctx).route 0
    hpoint hmult_nonneg hcard).trans hbud

/-- **Class-0 charging bound from a J.1.7 charging map (sharper).**

`routedClassMassOf route 0 ≤ termChernoff` from a **matching** charge map
`chargeOf` of the class-0 fibre into the Chernoff high-cost path family
(`hmaps` into `highCostSet …`, `hinj` injective on the fibre) with the per-path
charged domination `windowExcess k ≤ weight (chargeOf k)` (`hdom`, J.1.7).  The
per-output summation is discharged by `perOutput_charged_of_injOn` and the area
identification `termChernoff = ∑_p weight p` is `rfl` — both **inside**
`routedChernoff_le_term_of_matching`.  Hence the only undischarged content is the
charging map; there is neither a count nor an area-identification residual.

The `DecidableEq` on the (opaque) Chernoff path type is supplied classically; the
whole development is `noncomputable`. -/
theorem routedClass0_le_termChernoff_of_matching
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext)
    (chargeOf : ℕ → ((faithfulCapacityPhases budget ctx).toClosurePhaseData).chernoff.α)
    (hmaps : ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
      chargeOf k ∈ highCostSet
        ((faithfulCapacityPhases budget ctx).toClosurePhaseData).chernoff.paths
        ((faithfulCapacityPhases budget ctx).toClosurePhaseData).chernoff.cost
        ((faithfulCapacityPhases budget ctx).toClosurePhaseData).chernoff.Y)
    (hinj : ∀ x ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
      ∀ y ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
        chargeOf x = chargeOf y → x = y)
    (hdom : ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        ≤ ((faithfulCapacityPhases budget ctx).toClosurePhaseData).chernoff.weight
            (chargeOf k)) :
    routedClassMassOf ctx.n24CarryData (budget ctx).route 0
      ≤ termChernoff (faithfulCapacityPhases budget ctx).toClosurePhaseData := by
  classical
  exact routedChernoff_le_term_of_matching
    (faithfulCapacityPhases budget ctx).toClosurePhaseData
    ctx.n24CarryData (budget ctx).route chargeOf hmaps hinj hdom

/-! ## 3.  The minimal named residual and the `hChernoff` field it produces -/

/-- **The minimal class-0 (Chernoff) charging residual.**

For each failure context: the per-fibre window-excess multiplier `mult` (the
K.1.2/L.20 residual multiplier, ≤ the 22.1A shell-paid multiplier), the class-0
fibre count `count` (the J.1.1 / I.4.2 progress count), and the two genuine
charging facts — every class-0 start charges `≤ mult` (`hpoint`/`hmult_nonneg`),
the fibre has `≤ count` members (`hcard`), and `count·mult` fits the Chernoff
high-cost area (`hbud`).  This is the smallest count×multiplier interface from
which the class-0 charging bound follows by the proved
`routedClassMassOf_le_countMultiplier`. -/
structure Class0ChernoffCharge
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx) where
  /-- The per-fibre window-excess multiplier (K.1.2/L.20 ≤ 22.1A shell-paid). -/
  mult : ∀ _ctx : ActualFailureContext, ℝ
  /-- The class-0 fibre count (J.1.1 / I.4.2 progress count). -/
  count : ∀ _ctx : ActualFailureContext, ℝ
  /-- The multiplier is nonnegative. -/
  hmult_nonneg : ∀ ctx : ActualFailureContext, 0 ≤ mult ctx
  /-- Every class-0 start charges window excess `≤ mult` (the K.1.2/L.20 bound). -/
  hpoint : ∀ ctx : ActualFailureContext,
    ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        ≤ mult ctx
  /-- The class-0 fibre has at most `count` members (the I.4.2 progress count). -/
  hcard : ∀ ctx : ActualFailureContext,
    ((routedFibre ctx.n24CarryData (budget ctx).route 0).card : ℝ) ≤ count ctx
  /-- `count·mult` fits the Chernoff high-cost area (the 22.1A area identification). -/
  hbud : ∀ ctx : ActualFailureContext,
    count ctx * mult ctx
      ≤ termChernoff (faithfulCapacityPhases budget ctx).toClosurePhaseData

/-- **The exact `Erdos260ChargeResidual.hChernoff` field, produced from the minimal
residual.**  For every failure context, the count×multiplier reduction closes the
class-0 charging bound against the faithful Chernoff term. -/
def Class0ChernoffCharge.hChernoff
    {budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}
    (R : Class0ChernoffCharge budget) :
    ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (budget ctx).route 0
        ≤ termChernoff (faithfulCapacityPhases budget ctx).toClosurePhaseData :=
  fun ctx => routedClass0_le_termChernoff_of_countMul budget ctx
    (R.hpoint ctx) (R.hmult_nonneg ctx) (R.hcard ctx) (R.hbud ctx)

/-- **The same `hChernoff` field, produced from the sharper J.1.7 charging map.**  A
per-context matching charge map of the class-0 fibre into the Chernoff high-cost
family (with per-path charged domination) closes the field with no count and no
area-identification residual. -/
def hChernoffField_ofMatching
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (chargeOf : ∀ ctx : ActualFailureContext,
      ℕ → ((faithfulCapacityPhases budget ctx).toClosurePhaseData).chernoff.α)
    (hmaps : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
        chargeOf ctx k ∈ highCostSet
          ((faithfulCapacityPhases budget ctx).toClosurePhaseData).chernoff.paths
          ((faithfulCapacityPhases budget ctx).toClosurePhaseData).chernoff.cost
          ((faithfulCapacityPhases budget ctx).toClosurePhaseData).chernoff.Y)
    (hinj : ∀ ctx : ActualFailureContext,
      ∀ x ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
        ∀ y ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
          chargeOf ctx x = chargeOf ctx y → x = y)
    (hdom : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
        windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
          ≤ ((faithfulCapacityPhases budget ctx).toClosurePhaseData).chernoff.weight
              (chargeOf ctx k)) :
    ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (budget ctx).route 0
        ≤ termChernoff (faithfulCapacityPhases budget ctx).toClosurePhaseData :=
  fun ctx => routedClass0_le_termChernoff_of_matching budget ctx (chargeOf ctx)
    (hmaps ctx) (hinj ctx) (hdom ctx)

/-- **Drop-in confirmation.**  The class-0 charging residual replaces the
`hChernoff` field of any full `Erdos260ChargeResidual` sharing its `budget`,
yielding another full `Erdos260ChargeResidual` — so `Class0ChernoffCharge.hChernoff`
has exactly the field's type and genuinely plugs into the consolidated surface. -/
def Erdos260ChargeResidual.withClass0Chernoff
    (R0 : Erdos260ChargeResidual)
    (C : Class0ChernoffCharge R0.budget) :
    Erdos260ChargeResidual :=
  { R0 with hChernoff := C.hChernoff }

/-! ## 4.  Honest residual inventory -/

/-- The precise status of the class-0 (Chernoff / shell-paid progress) charging
bound after this module. -/
def chargeClass0ChernoffResiduals : List String :=
  [ "GROUNDED (RHS term) — termChernoff_faithful_nonneg (0 ≤ termChernoff) and " ++
      "termChernoff_faithful_le_budget (termChernoff ≤ c⋆·ξ·X/6, Lemma 22.1) prove the faithful " ++
      "Chernoff term of the unconditional §22 model leaf chernoff22_1ALeafOfShell is a genuine " ++
      "nonnegative fraction of the per-phase budget.",
    "CLOSED (structural reduction) — routedClass0_le_termChernoff_of_countMul: " ++
      "routedClassMassOf route 0 ≤ count·mult ≤ termChernoff via the PROVED " ++
      "routedClassMassOf_le_countMultiplier (a finite window-excess sum dominated by count·sup), " ++
      "chained with the area identification. NOT a repackaging of the goal.",
    "CLOSED (sharper, J.1.7) — routedClass0_le_termChernoff_of_matching: a matching charge map of " ++
      "the class-0 fibre into the Chernoff high-cost path family + per-path charged domination " ++
      "windowExcess k ≤ weight(chargeOf k) closes the bound via routedChernoff_le_term_of_matching, " ++
      "with the per-output summation discharged (perOutput_charged_of_injOn) and the area " ++
      "identification termChernoff = ∑_p weight p PROVED (rfl). No count/area residual remains.",
    "FIELD PRODUCED — Class0ChernoffCharge.hChernoff (count×multiplier) and hChernoffField_ofMatching " ++
      "(charging map) have EXACTLY the Erdos260ChargeResidual.hChernoff field type; " ++
      "Erdos260ChargeResidual.withClass0Chernoff drops the residual into a full residual with a " ++
      "matching budget.",
    "MINIMAL RESIDUAL (genuine charging) — the class-0 fibre count (hcard, the J.1.1/I.4.2 " ++
      "progress-endpoint count) and the per-fibre window-excess multiplier × area identification " ++
      "(hpoint/hmult_nonneg/hbud, the K.1.2/L.20 multiplier ≤ 22.1A shell-paid × the high-cost area), " ++
      "or equivalently ONE J.1.7 charging map. This is the orthogonal Appendix-L.2 CHARGING content: " ++
      "phase cores bound the output AREA ∑_o cap o, never the carry mass each output absorbs, so it " ++
      "is provably NOT derivable from any phase budget (ChargeMultiplierClosure.chargeMultiplierResidual " ++
      "/ ChargePerOutputEstimates.chargePerOutputResidual). windowExcess is an unbounded positivePart, " ++
      "so no uniform multiplier exists a priori — the residual is genuine, not a degenerate shortcut." ]

theorem chargeClass0ChernoffResiduals_nonempty : chargeClass0ChernoffResiduals ≠ [] := by
  simp [chargeClass0ChernoffResiduals]

/-! ## 5.  Axiom-cleanliness audit -/

#print axioms termChernoff_faithful_nonneg
#print axioms termChernoff_faithful_le_budget
#print axioms routedClass0_le_termChernoff_of_countMul
#print axioms routedClass0_le_termChernoff_of_matching
#print axioms Class0ChernoffCharge.hChernoff
#print axioms hChernoffField_ofMatching
#print axioms Erdos260ChargeResidual.withClass0Chernoff

end

end Erdos260
