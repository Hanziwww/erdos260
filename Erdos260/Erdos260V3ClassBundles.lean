import Erdos260.Erdos260UnconditionalSeedClosureV3
import Erdos260.ChernoffCNLChargeInjectionCore
import Erdos260.DensePackK11SeedClosure
import Erdos260.DensePackFirstStopOwnerCore
import Erdos260.DensePackLandsShiftCore

/-!
# Wiring the deep per-class reductions into the V3 final-theorem consumer surface

This module (NEW; it edits no existing file) closes the integration gap between the wave-9..24
per-class *minimal residual* reductions and the structure `Erdos260MinimalResidualV3`, which is what
the final theorem (`erdos260_of_minimalResidualV3`) actually consumes.

Until now the per-class reductions targeted the older surfaces (`Erdos260SeedResidual`,
`Erdos260ChargeResidual`), so no instance of `Erdos260MinimalResidualV3` had ever been assembled from
the minimal residuals.  Here we build exactly that:

```
erdos260MinimalResidualV3_ofClassData :  (the five OWNED minimal class residuals)
                                       → (the Return per-slice charge, supplied by the sibling worker)
                                       → Erdos260MinimalResidualV3
```

and the resulting endpoint `erdos260_of_classData : … → Erdos260Statement`.

For each of the five charge classes this worker owns, the V3 field is **not** re-stated but produced
from a strictly smaller manuscript residual, reusing the already-proved deep machinery:

* **Chernoff (class 0)** — the four V3 fields `chernoffChargeOf/chernoffMaps/chernoffInj/chernoffDom`
  are produced from a single `Class0ChernoffInjection (v3Budget …)`: the J.1.7 charge map into the
  §22.1A high-cost family, with the per-path area domination `chernoffDom` **derived** from the
  active-window gap geometry (`Class0ChernoffInjection.hdom`, via the proved
  `windowExcess_le_cap_chargeOf_on_routedFibre`), never assumed.
* **clean-CNL (class 1)** — `cnlG/cnlMem/cnlInj/cnlCharge` are produced from a single
  `Class1CNLInjection (v3Budget …)`: the J.1.1 charge map into the surviving clean-CNL family, with
  the per-codeword Kraft domination `cnlCharge` **derived** (`Class1CNLInjection.hcharge`).
* **DensePack (class 3)** — `densePackSupport` is produced from the bare K.1.1 endpoint-disjoint count
  `|genuineDensePackStarts| ≤ |densePackMarkers|` via `DensePackCoareaSupport.ofCardLe` (the genuine
  non-identity order-rank owner, not a singleton stand-in); `densePackG0 := densePackDyadicG0`
  (`= L+B+1`, the *proved* dyadic-scale gap ceiling) and `densePackGap` is **derived** from the
  active-window containment via the proved `hitGap_le_densePackDyadicG0_of_window`; only `densePackScale`
  (the K.1.2 active-floor calibration) is carried.
* **Tower (class 2)** and **Run (class 5)** are the budget-defining slots; they are taken here as the
  already-reduced families `Class2ActiveFloorCount` / `RunClass5StageChain` (see the sibling Tower/Run
  closure modules for their further reduction to the SDR / §26 run-area cover).

No `sorry`, `axiom`, `admit`, or `native_decide`.  No degenerate / empty / full-mass / zero-fraction
shortcut: every produced field is over the genuine first-obstruction route `genuineChargeRoute` and
its real per-class fibre.
-/

namespace Erdos260

open Finset

noncomputable section

set_option linter.unusedVariables false

/-! ## 1.  The V3 minimal residual, assembled from the per-class minimal residuals -/

/-- **`Erdos260MinimalResidualV3`, built from the five owned per-class minimal residuals + the Return
per-slice charge.**

The budget-defining slots are the reduced Tower / Run families (`towerCount`, `runChain`) and the
Return per-slice charge (`returnCharge`, supplied by the sibling worker).  Over the resulting
`v3Budget`, the Chernoff and clean-CNL charge *injections* produce all eight matched-charge fields
(the dominations `chernoffDom` / `cnlCharge` are the derived `hdom` / `hcharge`), and the DensePack
fields are produced from the bare K.1.1 count + active-window containment + the K.1.2 calibration. -/
def erdos260MinimalResidualV3_ofClassData
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runChain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (chernoff : Class0ChernoffInjection (v3Budget towerCount runChain returnCharge))
    (cnl : Class1CNLInjection (v3Budget towerCount runChain returnCharge))
    (densePackCount : ∀ ctx : ActualFailureContext,
      (genuineDensePackStarts ctx).card
        ≤ (densePackMarkers (v3Budget towerCount runChain returnCharge) ctx).card)
    (windowReach : ActualFailureContext → ℕ)
    (hReach : ∀ ctx : ActualFailureContext,
      windowReach ctx + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hContain : ∀ ctx : ActualFailureContext, ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + windowReach ctx)
    (hScale : ∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ) - ctx.n24CarryData.T ≤ 1) :
    Erdos260MinimalResidualV3 where
  towerCount := towerCount
  runChain := runChain
  returnCharge := returnCharge
  chernoffChargeOf := chernoff.chargeOf
  chernoffMaps := chernoff.hmaps
  chernoffInj := chernoff.hinj
  chernoffDom := chernoff.hdom
  cnlG := cnl.g
  cnlMem := cnl.hmem
  cnlInj := cnl.hinj
  cnlCharge := cnl.hcharge
  densePackSupport := fun ctx =>
    DensePackCoareaSupport.ofCardLe (v3Budget towerCount runChain returnCharge) ctx
      (densePackCount ctx)
  densePackG0 := densePackDyadicG0
  densePackGap :=
    densePackGap_ofContainment (v3Budget towerCount runChain returnCharge)
      (v3Budget_route towerCount runChain returnCharge) windowReach hReach hContain
  densePackScale := hScale

/-- **Erdős #260 from the five owned per-class minimal residuals + the Return per-slice charge.**

Composes `erdos260MinimalResidualV3_ofClassData` with the V3 endpoint `erdos260_of_minimalResidualV3`.
The five owned classes (Tower active-floor count, Run period-descent chain, Chernoff §22.1A matched
area charge, clean-CNL matched Kraft charge, DensePack K.1.1 coarea support) are reduced to their
minimal manuscript residuals; the Return slot is the sibling worker's per-slice charge. -/
theorem erdos260_of_classData
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runChain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (chernoff : Class0ChernoffInjection (v3Budget towerCount runChain returnCharge))
    (cnl : Class1CNLInjection (v3Budget towerCount runChain returnCharge))
    (densePackCount : ∀ ctx : ActualFailureContext,
      (genuineDensePackStarts ctx).card
        ≤ (densePackMarkers (v3Budget towerCount runChain returnCharge) ctx).card)
    (windowReach : ActualFailureContext → ℕ)
    (hReach : ∀ ctx : ActualFailureContext,
      windowReach ctx + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hContain : ∀ ctx : ActualFailureContext, ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + windowReach ctx)
    (hScale : ∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ) - ctx.n24CarryData.T ≤ 1) :
    Erdos260Statement :=
  erdos260_of_minimalResidualV3
    (erdos260MinimalResidualV3_ofClassData towerCount runChain returnCharge chernoff cnl
      densePackCount windowReach hReach hContain hScale)

/-! ## 2.  The DensePack count, reduced to the smallest K.1.4 endpoint-landing residual -/

/-- **The K.1.1 endpoint-disjoint count, from the smaller `landsShift` family.**

`densePackLandsShift budget ctx` (each densePack tower-exit start's terminal endpoint `k + r` is a
dense marker) is a *single geometric membership fact* — strictly smaller than the count.  The endpoint
map `· + r` injects `genuineDensePackStarts` into `densePackMarkers` (`densePackStarts_card_le_of_landsShift`,
a genuine non-identity injection for `r > 0`), giving the count for free. -/
theorem densePackCount_ofLandsShift
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (hlands : ∀ ctx : ActualFailureContext, densePackLandsShift budget ctx) :
    ∀ ctx : ActualFailureContext,
      (genuineDensePackStarts ctx).card ≤ (densePackMarkers budget ctx).card :=
  fun ctx => densePackStarts_card_le_of_landsShift budget ctx (hlands ctx)

/-- **Erdős #260 from the owned class residuals, with DensePack reduced to the `landsShift` landing.**

Identical to `erdos260_of_classData` but the DensePack count input is replaced by the strictly
smaller K.1.4 endpoint-landing residual `landsShift`. -/
theorem erdos260_of_classData_landsShift
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runChain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (chernoff : Class0ChernoffInjection (v3Budget towerCount runChain returnCharge))
    (cnl : Class1CNLInjection (v3Budget towerCount runChain returnCharge))
    (hlands : ∀ ctx : ActualFailureContext,
      densePackLandsShift (v3Budget towerCount runChain returnCharge) ctx)
    (windowReach : ActualFailureContext → ℕ)
    (hReach : ∀ ctx : ActualFailureContext,
      windowReach ctx + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hContain : ∀ ctx : ActualFailureContext, ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + windowReach ctx)
    (hScale : ∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ) - ctx.n24CarryData.T ≤ 1) :
    Erdos260Statement :=
  erdos260_of_classData towerCount runChain returnCharge chernoff cnl
    (densePackCount_ofLandsShift (v3Budget towerCount runChain returnCharge) hlands)
    windowReach hReach hContain hScale

/-! ## 3.  The DensePack count, reduced to the budget-INDEPENDENT K.1.1 hit-density -/

/-- **The K.1.1 endpoint-disjoint count, from the bare hit-density `densePackEndpointDensity`.**

`densePackEndpointDensity ctx` (`⌊ρ_D·L⌋ ≤ |supportWindow (k + r)|` at each densePack endpoint) is the
smallest DensePack residual: a single coarea hit-density inequality that **depends only on `ctx`, not
on the routing `budget`** (the marker set is budget-independent, `densePackMarkers_eq_actualPoints`).
It forces `landsShift` (`densePackLandsShift_of_density`), hence the count. -/
theorem densePackCount_ofEndpointDensity
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (hdens : ∀ ctx : ActualFailureContext, densePackEndpointDensity ctx) :
    ∀ ctx : ActualFailureContext,
      (genuineDensePackStarts ctx).card ≤ (densePackMarkers budget ctx).card :=
  fun ctx => densePackStarts_card_le_of_landsShift budget ctx
    (densePackLandsShift_of_density budget ctx (hdens ctx))

/-- **Erdős #260 from the owned class residuals, with DensePack reduced to the bare K.1.1 hit-density.**

Identical to `erdos260_of_classData` but the DensePack count input is the strictly smaller,
budget-independent K.1.1 hit-density `densePackEndpointDensity` (the genuine §K.1 coarea landing at the
descent endpoints). -/
theorem erdos260_of_classData_endpointDensity
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runChain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (chernoff : Class0ChernoffInjection (v3Budget towerCount runChain returnCharge))
    (cnl : Class1CNLInjection (v3Budget towerCount runChain returnCharge))
    (hdens : ∀ ctx : ActualFailureContext, densePackEndpointDensity ctx)
    (windowReach : ActualFailureContext → ℕ)
    (hReach : ∀ ctx : ActualFailureContext,
      windowReach ctx + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hContain : ∀ ctx : ActualFailureContext, ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + windowReach ctx)
    (hScale : ∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ) - ctx.n24CarryData.T ≤ 1) :
    Erdos260Statement :=
  erdos260_of_classData towerCount runChain returnCharge chernoff cnl
    (densePackCount_ofEndpointDensity (v3Budget towerCount runChain returnCharge) hdens)
    windowReach hReach hContain hScale

/-! ## 4.  Axiom-cleanliness audit -/

#print axioms erdos260MinimalResidualV3_ofClassData
#print axioms erdos260_of_classData
#print axioms densePackCount_ofLandsShift
#print axioms erdos260_of_classData_landsShift
#print axioms densePackCount_ofEndpointDensity
#print axioms erdos260_of_classData_endpointDensity

end

end Erdos260
