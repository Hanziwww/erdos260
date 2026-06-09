import Erdos260.Erdos260V3ClassBundles
import Erdos260.TowerSDRCore
import Erdos260.TowerK13PackingExistenceCore
import Erdos260.TowerI41PackingCore

/-!
# Reducing the Tower (class-2) V3 field to the index-space SDR

This module (NEW; it edits no existing file) reduces the Tower V3 residual field
`towerCount : ∀ ctx, Class2ActiveFloorCount ctx` (the I.4.1 active-floor count `(★)`) to the
**index-space SDR** `Class2IndexSDR` — the manuscript K.1.3 maximal-disjoint selection of hit-index
blocks of size `≥ ρ_D·L` landing in the shell support.

The reduction composes the already-proved Tower cores (none of them rhoDQ / Return modules):

```
Class2IndexSDR --toShellSDR--> Class2ShellSDR --ofShellSDR--> Class2OwnershipPacking
              --ofOwnershipPacking--> Class2AreaPacking --ofAreaPacking--> Class2ActiveFloorCount
```

`Class2IndexSDR` itself reduces further, via the already-proved `Class2IndexSDR.ofWindowsHall`
(`SDRSelectionCore`) / `Class2IndexSDR.ofSemiperiodicDensity` (`SDRDensityCore`), to the genuine
manuscript frontier residual: the Hall **marginal condition** `∀ S ⊆ fibre₂, m·#S ≤ #(⋃ W)` plus the
per-block density floor `ρ_D·L ≤ m` (the no-large-run semiperiodic-window density).  That marginal
condition is the irreducible class-2 input (the §I.4 / K.2 semiperiodic-window existence).

No `sorry`, `axiom`, `admit`, or `native_decide`.  No degenerate / empty / full-mass shortcut: the
SDR is over the genuine class-2 fibre `routedFibre … (genuineChargeRoute ctx) 2`.
-/

namespace Erdos260

open Finset

noncomputable section

set_option linter.unusedVariables false

/-! ## 1.  The Tower V3 field from the index-space SDR -/

/-- **The Tower V3 field `Class2ActiveFloorCount`, from the index-space SDR family.**

For every failure context, the index-space SDR `Class2IndexSDR ctx` (disjoint hit-index blocks of
card `≥ ρ_D·L` landing in the shell, over the genuine class-2 fibre) is transported through the proved
Tower chain (`toShellSDR` → `Class2OwnershipPacking.ofShellSDR` → `Class2AreaPacking.ofOwnershipPacking`
→ `Class2ActiveFloorCount.ofAreaPacking`) to the active-floor count `(★)`.  This is the corrected,
deep-shell-satisfiable Tower residual (carrying the active-order `1/s ≍ 1/(κL)` factor), so the I.4.1
slot `routedClassMassOf … 2 ≤ ξ·X/6` holds with no dense-marker blow-up. -/
def towerCount_ofIndexSDR (S : ∀ ctx : ActualFailureContext, Class2IndexSDR ctx) :
    ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx :=
  fun ctx =>
    Class2ActiveFloorCount.ofAreaPacking
      (Class2AreaPacking.ofOwnershipPacking
        (Class2OwnershipPacking.ofShellSDR (S ctx).toShellSDR))

/-! ## 2.  End-to-end with Tower reduced to the SDR and DensePack to the landing -/

/-- **Erdős #260 with Tower reduced to the index-space SDR and DensePack to the K.1.4 landing.**

Composes `towerCount_ofIndexSDR` (Tower ⟸ `Class2IndexSDR`) with `erdos260_of_classData_landsShift`
(DensePack ⟸ `landsShift`).  The five owned classes are then carried by: the Tower index-SDR, the Run
period-descent chain, the Chernoff §22.1A charge injection, the clean-CNL Kraft charge injection, and
the DensePack endpoint landing; the Return slot is the sibling worker's per-slice charge. -/
theorem erdos260_of_towerSDR_landsShift
    (towerSDR : ∀ ctx : ActualFailureContext, Class2IndexSDR ctx)
    (runChain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (chernoff : Class0ChernoffInjection
      (v3Budget (towerCount_ofIndexSDR towerSDR) runChain returnCharge))
    (cnl : Class1CNLInjection
      (v3Budget (towerCount_ofIndexSDR towerSDR) runChain returnCharge))
    (hlands : ∀ ctx : ActualFailureContext,
      densePackLandsShift (v3Budget (towerCount_ofIndexSDR towerSDR) runChain returnCharge) ctx)
    (windowReach : ActualFailureContext → ℕ)
    (hReach : ∀ ctx : ActualFailureContext,
      windowReach ctx + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hContain : ∀ ctx : ActualFailureContext, ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + windowReach ctx)
    (hScale : ∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ) - ctx.n24CarryData.T ≤ 1) :
    Erdos260Statement :=
  erdos260_of_classData_landsShift (towerCount_ofIndexSDR towerSDR) runChain returnCharge
    chernoff cnl hlands windowReach hReach hContain hScale

/-! ## 3.  Axiom-cleanliness audit -/

#print axioms towerCount_ofIndexSDR
#print axioms erdos260_of_towerSDR_landsShift

end

end Erdos260
