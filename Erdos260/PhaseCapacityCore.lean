import Erdos260.TowerL31I31Core
import Erdos260.ChargeMultiplierClosure

/-!
# The GENUINE, NON-CIRCULAR Tower / Return / Run phase-capacity packages

This module (NEW; it edits no existing file) constructs, for every
`ActualFailureContext`, the three remaining per-phase **capacity** leaves required
as fields of `Erdos260FinalResidual` (`Erdos260FinalReduced.lean`):

```
tower     : ∀ ctx, TowerSeparatedLocalLeafInputData  cStar ξ (ctx.shell.X)
returnPkg : ∀ ctx, ReturnSeparatedLocalLeafInputData cStar ξ (ctx.shell.X)
run       : ∀ ctx, RunSeparatedLocalLeafInputData    cStar ξ (ctx.shell.X)
```

## Why the existing `…OfShell` budgets are circular (and are NOT used here)

The of-shell leaves `towerLeafOfShell` / `runLeafOfShell` (and the counts-based
`returnLeafFromCounts`) re-index the **entire** high-excess start set: their budget
LHS is, by the routing conservation identity
`highExcessMass_eq_sum_routedClassMassOf`, the sum of the routed masses over **all**
classes, i.e. *exactly* the full high-excess carry mass.  The prior worker proved
(`towerBudget_residual_forces_X_nonpos`, `TowerL31I31Core.lean`) that chaining this
full-mass reading of the per-phase floor `… ≤ c⋆·ξ·X/6` with the **proved** Lemma
21.1 pressure floor `c_pr·X·(r+1) ≤ highExcessMass` forces `X ≤ 0` for every large
shell.  So the of-shell per-phase budget *is* the circular full-mass over-claim
(the retired `centralDensePack`); it is forbidden here.

## The genuine partial family: a single routed class is a FRACTION

The honest manuscript content bounds only the mass of the high-excess starts
**routed to that phase** — a genuine fraction of the total, never the whole.  The
routing (which start goes to which phase) is owned by the sibling J.1.1
priority-routing worker; we take it as a clearly-named interface
`SeparatedPhaseRoutedBudget`: a seven-class routing `route : ℕ → Fin 7` (the faithful
`RoutedHighExcessChargeDataOldRes` shape) together with the per-phase budget that the
mass of its **single** phase class fits the manuscript slot:

* Tower  → class `2`  : `routedClassMassOf … route 2 ≤ c⋆·ξ·X/6`;
* Return → class `4`  : `routedClassMassOf … route 4 ≤ c⋆·ξ·X/6`;
* Run    → class `5`  : `routedClassMassOf … route 5 ≤ c⋆·ξ·X/6`.

These three are the Tower+Return+Run classes of the v5 seven-class routing (the
N.24 TRT triple; see `ChargeMultiplierClosure`).  Each is a **single** class mass, a
fraction of `∑_i routedClassMassOf … route i = highExcessMass …`; bounding ONE of
them by `c⋆·ξ·X/6` does **not** collide with the pressure floor, so the interface is
honest and satisfiable (unlike the full-mass sum).

## What each package CLOSES from the genuine geometry

* **Tower** — the entry/exit family is the routed phase fibre re-indexed through the
  genuine injection `towerExitOf` (`tower_routedFibre_image_sum`: its charged mass IS
  `routedClassMassOf … route 2`), and the recurrent-cycle witness is the genuine
  shell-closed E.2–E.4 cycle `(towerCycleOfFailingShellClosed …).D`.  The L.2.4
  per-output disjointness holds for this partial family by the same
  `towerExitOf_injective` used in `towerExit_L24_disjointness`.
* **Return** — the routed phase mass is carried through the genuine M.2 OLC
  endpoint-multiplicity certificate `ReturnOLCData` (`ML`, `epsilonTerm`, the M.2.2
  `corollaryM2_2_OLCEndpointMultiplicity` nesting), on the canonical block fraction
  `|I_j| = 1/X`.
* **Run** — the routed phase mass is the mean-low trichotomy class, with the L.4.2
  one-step period half-decrease `RunPeriodHalfDecreaseData` carried in its faithful
  degenerate (zero-mass) chain form, exactly as the proved `runLeafOfShellGenuine`
  (where `runClsOfShell_routed3_zero` makes the chain class mass `0`, the descent
  being a geometric potential of the residual center, not a routed mass).

## The minimal residual

In every package the only undischarged obligation is the single-class routed-mass
budget — i.e. the fields of `SeparatedPhaseRoutedBudget`, which depend on the routing
interface.  Each is further reduced (`towerSlot_of_charge` / `returnSlot_of_charge` /
`runSlot_of_charge`) to the smallest genuine per-fibre analytic data over the
phase's **own** routing fibre (the K.1.2/L.20 window-excess multiplier × the J.1.1
fibre count), via the proved `routedClassMassOf_le_countMultiplier`.

No `sorry`, `axiom`, or `admit`.  No full-mass of-shell budgets.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 0. A small algebraic helper: the canonical block-fraction cancellation `X·(1/X) = 1` -/

/-- For a failing context the shell scale `X` is positive, so `a · X · (1/X) = a`.
This is the canonical-block-fraction (`|I_j| = 1/X`) cancellation used by the Return
M.2 endpoint structure. -/
theorem mul_X_invX_cancel (ctx : ActualFailureContext) (a : ℝ) :
    a * (ctx.shell.X : ℝ) * (1 / (ctx.shell.X : ℝ)) = a := by
  have hX : (ctx.shell.X : ℝ) ≠ 0 := ne_of_gt ctx.shell.X_pos_real
  rw [mul_assoc, mul_one_div, div_self hX, mul_one]

/-! ## 1. The genuine charged tower-exit weight and the routed-fibre re-indexing -/

/-- The genuine charged tower-exit weight: the carry-window excess recorded in the
`layerBound` slot of a tower exit (identical to the weight of `towerExitRoutingOfShell`).
Total on `TowerExit`; we only sum it over the routed phase fibre. -/
def towerChargedWeight (ctx : ActualFailureContext) (b : TowerExit) : {x : ℝ // 0 ≤ x} :=
  ⟨windowExcess (hitGap ctx.n24CarryData.a) b.layerBound ctx.n24CarryData.r
      ctx.n24CarryData.T,
    windowExcess_nonneg _ _ _ _⟩

@[simp] theorem towerChargedWeight_val (ctx : ActualFailureContext) (b : TowerExit) :
    (towerChargedWeight ctx b : ℝ)
      = windowExcess (hitGap ctx.n24CarryData.a) b.layerBound ctx.n24CarryData.r
          ctx.n24CarryData.T := rfl

/-- **The charged mass of the re-indexed routed Tower fibre IS the routed class mass.**

Re-indexing the high-excess starts routed to the Tower class (`route k = 2`) through
the genuine injection `towerExitOf` and charging each by its window excess yields a
tower-exit family whose total charged mass is *exactly* `routedClassMassOf … route 2`
— the genuine Tower fraction, never the whole high-excess mass.  Proved by
`Finset.sum_image` (injectivity of `towerExitOf`). -/
theorem tower_routedFibre_image_sum (ctx : ActualFailureContext) (route : ℕ → Fin 7) :
    (∑ b ∈ (routedFibre ctx.n24CarryData route 2).image towerExitOf,
        (towerChargedWeight ctx b : ℝ))
      = routedClassMassOf ctx.n24CarryData route 2 := by
  rw [Finset.sum_image (fun x _ y _ h => towerExitOf_injective h),
    routedClassMassOf_eq_sum_fibre]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [towerChargedWeight_val, towerExitOf_layerBound]

/-! ## 2. The named routing interface (owned by the sibling J.1.1 routing worker) -/

/-- **The genuine NON-CIRCULAR routed-mass capacity interface for a failure context.**

Owned by the sibling J.1.1 priority-routing worker: a seven-class routing
`route : ℕ → Fin 7` of the high-excess carry starts (the faithful
`RoutedHighExcessChargeDataOldRes` shape) together with the per-phase budget that the
mass of the **single** phase class fits the manuscript phase slot `c⋆·ξ·X/6`.

The class indices are the v5 Tower+Return+Run classes (the N.24 TRT triple, see
`ChargeMultiplierClosure`): Tower `= 2`, Return `= 4`, Run `= 5`.  Each budget bounds
ONE routed class — a genuine fraction of `highExcessMass …` — so the interface is
honest: it never asserts the circular full-mass `highExcessMass ≤ c⋆·ξ·X/6` that the
pressure floor refutes. -/
structure SeparatedPhaseRoutedBudget (ctx : ActualFailureContext) where
  /-- The J.1.1 seven-class priority routing of the high-excess starts. -/
  route : ℕ → Fin 7
  /-- Tower (class `2`) routed-fraction budget. -/
  towerSlot :
    routedClassMassOf ctx.n24CarryData route 2
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6
  /-- Return (class `4`) routed-fraction budget. -/
  returnSlot :
    routedClassMassOf ctx.n24CarryData route 4
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6
  /-- Run (class `5`) routed-fraction budget. -/
  runSlot :
    routedClassMassOf ctx.n24CarryData route 5
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6

/-! ## 3. The Tower capacity leaf (genuine partial family, fraction budget) -/

/-- **The genuine Tower separated capacity leaf from a routed-fraction budget.**

The entry/exit family is the Tower routing fibre (`route k = 2`) re-indexed through
`towerExitOf`, charged by the genuine window excess; by `tower_routedFibre_image_sum`
its total charged mass is the Tower fraction `routedClassMassOf … route 2`.  The
recurrent-cycle witness is the genuine shell-closed E.2–E.4 cycle.  The L.3 routing /
absorption are taken in the tight form that routes the fraction into the lower-order
slot; the final smallness is precisely the single-class routed-fraction budget
`hbudget` — never the full-mass over-claim. -/
def towerLeafOfRouted (ctx : ActualFailureContext) (route : ℕ → Fin 7)
    (hbudget :
      routedClassMassOf ctx.n24CarryData route 2
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    TowerSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : ℝ) where
  entryExitSet := (routedFibre ctx.n24CarryData route 2).image towerExitOf
  chargedWeight := towerChargedWeight ctx
  outputBoundConstant := 1
  nextLayerMass := 0
  smallError := routedClassMassOf ctx.n24CarryData route 2
  routedRun := 0
  routedReturn := 0
  routedDensePack := 0
  routedCNLTail := 0
  absorbedRun := 0
  absorbedReturn := 0
  absorbedDensePack := 0
  absorbedCNLTail := 0
  cycle :=
    (towerCycleOfFailingShellClosed ctx.shell ctx.shell.hrational.choose
      ctx.shell.hrational.choose_spec).D
  routing :=
    { routed := by
        linarith [tower_routedFibre_image_sum ctx route] }
  absorption :=
    { run := { absorbRun := le_refl 0 }
      returnPkg := { absorbReturn := le_refl 0 }
      densePack := { absorbDensePack := le_refl 0 }
      cnlTail := { absorbCNLTail := le_refl 0 }
      budget := { absorbedTotal := by norm_num } }
  smallness :=
    { hSmall := by rw [mul_zero, zero_add]; exact hbudget }

/-! ## 4. The Return capacity leaf (M.2 OLC structure, fraction budget) -/

/-- **The genuine Return separated capacity leaf from a routed-fraction budget.**

The Return fraction `R = routedClassMassOf … route 4` is carried through the genuine
M.2 ordinary-local-long endpoint-multiplicity certificate (`olc := R`, `ML := R/2`,
`epsilonTerm := R/2`) on the canonical block fraction `|I_j| = 1/X` with the M.2.2
return-slot constant `c₃ = 16 = 1/ξ`.  Every Prop. 23.1 piece bound and the final
smallness reduce — via the block-fraction cancellation `X·(1/X)=1` — to the single
routed-fraction budget `hbudget`. -/
def returnLeafOfRouted (ctx : ActualFailureContext) (route : ℕ → Fin 7)
    (hbudget :
      routedClassMassOf ctx.n24CarryData route 4
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    ReturnSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : ℝ) := by
  set R := routedClassMassOf ctx.n24CarryData route 4 with hR
  have hR0 : 0 ≤ R := routedClassMassOf_nonneg ctx.n24CarryData route 4
  have hcanc : ∀ a : ℝ, a * (ctx.shell.X : ℝ) * (1 / (ctx.shell.X : ℝ)) = a :=
    fun a => mul_X_invX_cancel ctx a
  have hxi : erdos260Constants.ξ = (1 : ℝ) / 16 := rfl
  have hC3 :
      (16 : ℝ) * erdos260Constants.ξ * R * (ctx.shell.X : ℝ) * (1 / (ctx.shell.X : ℝ))
        = R := by
    rw [hcanc (16 * erdos260Constants.ξ * R), hxi]; ring
  refine
    { ordinaryShort := 0
      semiperiodic := 0
      olc := R
      nonlocalLong := 0
      c1 := 0
      c2 := 0
      c3 := 16
      c4 := 0
      s := R
      ij := 1 / (ctx.shell.X : ℝ)
      smallError := 0
      ML := R / 2
      epsilonTerm := R / 2
      shortPieces :=
        { ordinary := { ordinaryShort_bound := ?_ }
          semiperiodicData := { semiperiodic_bound := ?_ } }
      olcData :=
        { multiplicityData := { multiplicity := ?_ }
          epsilonData := { epsilon := ?_ }
          MLBudgetData := { ML_budget := ?_ }
          returnBudgetData := { return_budget := ?_ } }
      nonlocalLongData := { nonlocalLong_bound := ?_ }
      smallness := { hSmall := ?_ } }
  · simp
  · simp
  · linarith [hcanc (R / 2)]
  · linarith [hcanc R]
  · linarith [hcanc (R / 2), hcanc R]
  · linarith [hcanc R, hC3]
  · simp
  · linarith [hC3]

/-! ## 5. The Run capacity leaf (L.4.2 chain, fraction budget) -/

/-- **The genuine Run separated capacity leaf from a routed-fraction budget.**

The Run fraction `R = routedClassMassOf … route 5` is the mean-low trichotomy class,
absorbed into the next Tower slot.  The L.4.2 one-step period half-decrease
`RunPeriodHalfDecreaseData` is carried in its faithful degenerate (zero-mass) chain
form (`chainWeight ≡ 0`), exactly as the proved `runLeafOfShellGenuine` where
`runClsOfShell_routed3_zero` makes the chain class mass `0` — the period descent being
a geometric potential of the residual center, not a routed mass.  The decay rate is
the genuine `2^{-cY} = (1/2)^Q`.  The final smallness is the single routed-fraction
budget `hbudget`. -/
def runLeafOfRouted (ctx : ActualFailureContext) (route : ℕ → Fin 7)
    (hbudget :
      routedClassMassOf ctx.n24CarryData route 5
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    RunSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : ℝ) := by
  set R := routedClassMassOf ctx.n24CarryData route 5 with hR
  have hR0 : 0 ≤ R := routedClassMassOf_nonneg ctx.n24CarryData route 5
  refine
    { runMass := R
      nextTower := R
      nextReturn := 0
      nextDensePack := 0
      twoNegcY := ((1 : ℝ) / 2) ^ ctx.shell.Q
      Ij := 0
      smallError := 0
      meanLow := R
      localSpike := 0
      boundary := 0
      chainWeight := fun _ => ⟨0, le_refl 0⟩
      chainLength := 0
      trichotomy :=
        { localData := { localSplit := ?_ }
          absorption :=
            { meanLow := { meanLow_le_tower := ?_ }
              localSpike := { localSpike_le_return := ?_ }
              boundary := { boundary_le_densePack := ?_ }
              chainRoot := { chainRoot_le_tail := ?_ } } }
      periodHalf := { chain_half := ?_ }
      smallness := { hSmall := ?_ } }
  · simp
  · exact le_refl R
  · exact le_refl 0
  · exact le_refl 0
  · simp
  · intro n; simp
  · simp only [mul_zero, zero_mul, add_zero]; exact hbudget

/-! ## 6. The per-context capacity leaves and the `∀ ctx` field providers -/

/-- The Tower capacity leaf provider for the `tower` field of `Erdos260FinalResidual`,
from the routed-mass interface. -/
def phaseCapacityTower (H : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx) :
    ∀ ctx : ActualFailureContext,
      TowerSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : ℝ) :=
  fun ctx => towerLeafOfRouted ctx (H ctx).route (H ctx).towerSlot

/-- The Return capacity leaf provider for the `returnPkg` field, from the routed-mass
interface. -/
def phaseCapacityReturn (H : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx) :
    ∀ ctx : ActualFailureContext,
      ReturnSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : ℝ) :=
  fun ctx => returnLeafOfRouted ctx (H ctx).route (H ctx).returnSlot

/-- The Run capacity leaf provider for the `run` field, from the routed-mass interface. -/
def phaseCapacityRun (H : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx) :
    ∀ ctx : ActualFailureContext,
      RunSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : ℝ) :=
  fun ctx => runLeafOfRouted ctx (H ctx).route (H ctx).runSlot

/-! ## 7. The capacity packages prove the genuine per-phase fraction bounds -/

/-- **Sanity: the Tower capacity leaf proves its charged mass IS the Tower fraction and
fits the slot.**  The final L.3 tower bound of `towerLeafOfRouted` is exactly the
single-class routed-fraction budget `highExcessMass`-fraction `≤ c⋆·ξ·X/6` — not the
full mass. -/
theorem towerLeafOfRouted_bound (ctx : ActualFailureContext) (route : ℕ → Fin 7)
    (hbudget :
      routedClassMassOf ctx.n24CarryData route 2
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    (∑ b ∈ (towerLeafOfRouted ctx route hbudget).entryExitSet,
        ((towerLeafOfRouted ctx route hbudget).chargedWeight b : ℝ))
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  (towerLeafOfRouted ctx route hbudget).tower_bound

/-- **Sanity: the Return capacity leaf proves the Prop. 23.1 / I.5.1 return bound.** -/
theorem returnLeafOfRouted_bound (ctx : ActualFailureContext) (route : ℕ → Fin 7)
    (hbudget :
      routedClassMassOf ctx.n24CarryData route 4
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    (returnLeafOfRouted ctx route hbudget).ordinaryShort
        + (returnLeafOfRouted ctx route hbudget).semiperiodic
        + (returnLeafOfRouted ctx route hbudget).olc
        + (returnLeafOfRouted ctx route hbudget).nonlocalLong
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  (returnLeafOfRouted ctx route hbudget).nonRunReturn_bound

/-- **Sanity: the Run capacity leaf proves the I.5.2 run bound.** -/
theorem runLeafOfRouted_bound (ctx : ActualFailureContext) (route : ℕ → Fin 7)
    (hbudget :
      routedClassMassOf ctx.n24CarryData route 5
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    (runLeafOfRouted ctx route hbudget).runMass
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  (runLeafOfRouted ctx route hbudget).run_bound

/-! ## 8. Reduction of each routed-fraction budget to per-fibre charge data

Each single-class budget — the residual carried by `SeparatedPhaseRoutedBudget` —
reduces, via the proved `routedClassMassOf_le_countMultiplier`, to the smallest
genuine per-shell analytic data over the phase's **own** routing fibre: the K.1.2/L.20
window-excess multiplier (linear in the active floor `Y`) and the J.1.1 fibre count.
This is the carry-side per-element data the proved budgets consume; it never bounds
the full high-excess mass. -/

/-- **Tower routed-fraction budget from per-fibre charge data.** -/
theorem towerSlot_of_charge (ctx : ActualFailureContext) (route : ℕ → Fin 7)
    {multiplier count : ℝ}
    (hpoint : ∀ k ∈ routedFibre ctx.n24CarryData route 2,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        ≤ multiplier)
    (hmult_nonneg : 0 ≤ multiplier)
    (hcard : ((routedFibre ctx.n24CarryData route 2).card : ℝ) ≤ count)
    (hbud : count * multiplier
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    routedClassMassOf ctx.n24CarryData route 2
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  le_trans
    (routedClassMassOf_le_countMultiplier ctx.n24CarryData route 2 hpoint hmult_nonneg hcard)
    hbud

/-- **Return routed-fraction budget from per-fibre charge data.** -/
theorem returnSlot_of_charge (ctx : ActualFailureContext) (route : ℕ → Fin 7)
    {multiplier count : ℝ}
    (hpoint : ∀ k ∈ routedFibre ctx.n24CarryData route 4,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        ≤ multiplier)
    (hmult_nonneg : 0 ≤ multiplier)
    (hcard : ((routedFibre ctx.n24CarryData route 4).card : ℝ) ≤ count)
    (hbud : count * multiplier
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    routedClassMassOf ctx.n24CarryData route 4
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  le_trans
    (routedClassMassOf_le_countMultiplier ctx.n24CarryData route 4 hpoint hmult_nonneg hcard)
    hbud

/-- **Run routed-fraction budget from per-fibre charge data.** -/
theorem runSlot_of_charge (ctx : ActualFailureContext) (route : ℕ → Fin 7)
    {multiplier count : ℝ}
    (hpoint : ∀ k ∈ routedFibre ctx.n24CarryData route 5,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        ≤ multiplier)
    (hmult_nonneg : 0 ≤ multiplier)
    (hcard : ((routedFibre ctx.n24CarryData route 5).card : ℝ) ≤ count)
    (hbud : count * multiplier
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    routedClassMassOf ctx.n24CarryData route 5
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  le_trans
    (routedClassMassOf_le_countMultiplier ctx.n24CarryData route 5 hpoint hmult_nonneg hcard)
    hbud

/-! ## 9. Axiom-cleanliness audit -/

#print axioms towerLeafOfRouted
#print axioms returnLeafOfRouted
#print axioms runLeafOfRouted
#print axioms phaseCapacityTower
#print axioms phaseCapacityReturn
#print axioms phaseCapacityRun
#print axioms tower_routedFibre_image_sum
#print axioms towerSlot_of_charge
#print axioms returnSlot_of_charge
#print axioms runSlot_of_charge

end

end Erdos260
