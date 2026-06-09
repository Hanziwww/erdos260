import Erdos260.ReturnRunFamily
import Erdos260.UnconditionalTheorem

/-!
# Prop. I.5.1/M.2/J.4/L.6 Return local leaf, inhabited from a genuine failing dyadic shell

This file makes the Return separated local leaf **unconditional in the shell**: it builds the
manuscript-shaped `ReturnClosedI51M2J4L6PackageInputData` for an `ActualFailureContext` by wiring the
three non-OLC return masses to the *actual* routed high-excess carry masses
`routedClassMassOf ctx.n24CarryData cls i` of the failing shell, never the forbidden
`returnFamilyCoreTrivial` all-zero witness.

## What is closed unconditionally (from the shell)

* The three non-OLC return contributions (ordinary-short, semiperiodic-short, nonlocal-long) are the
  genuine routed carry masses `routedClassMassOf ctx.n24CarryData cls 0/1/2`.
* The M.2.1 crossing/nesting counting (`OLCEndpointMultiplicity.card_le`) and the I.5.1 OLC bound
  `olc ≤ M_L·X·|I_j|` are reused as proved theorems; the OLC piece mass is the genuine endpoint count
  `|olcGeom.endpoints|`, not a free scalar.
* The four-piece Prop. 23.1 assembly to `ReturnClosedI51M2J4L6PackageInputData`
  (`ReturnFamilyCore.toPackage`) and the Prop. I.5.1 budget (`termReturn_bound`).

## Residual cores exposed as explicit named hypotheses (NOT closed here)

* `cls : ℕ → Fin 3` — the routing of carry starts into the three non-OLC return sub-pieces.
* `olcGeom : OLCEndpointMultiplicity ℕ ℕ` — the **M.2.1 OLC endpoint crossing/nesting geometry on
  the actual shell return geometry**, whose `nesting_multiplicity` field is the genuine M.2.1
  primitive (`card(endpoints.filter (baseAnchor · = b)) ≤ M_L` per base point).
* `olc_route` — the **I.5.1** anchor routing `|baseSet| ≤ X·|I_j|`.
* `olc_ML_budget` — the **J.4/K.2.5** envelope budget `M_L·X·|I_j| ≤ s·X·|I_j|/2` (the `M_L = o(s)`
  regime).
* `ordinaryShort_bound`/`semiperiodic_bound`/`nonlocalLong_bound` — the **L.2.2** non-OLC counts
  (synchronizing sets / short-return envelope / return-length normalization) bounding the routed
  carry masses.
* `olc_return_budget`, `hsXij`, `hSmall` — the M.2/Prop. 23.1 routing, the scale nonnegativity, and
  the K.4 numerical smallness.

No `sorry`, `axiom`, or `admit`.  No empty/trivial witnesses.
-/

namespace Erdos260

open Finset

noncomputable section

/-- **The Return four-piece family core of a failing shell.**

The three non-OLC return masses are the genuine routed high-excess carry masses; the OLC piece is
the genuine endpoint count of the supplied M.2.1 geometry.  The only inputs are the named
irreducible cores: the M.2.1 nesting geometry `olcGeom`, the I.5.1/J.4 routing budgets, the three
L.2.2 counts, and the K.4 numerical smallness. -/
def returnFamilyCoreOfShell (ctx : ActualFailureContext) (cls : ℕ → Fin 3)
    (olcGeom : OLCEndpointMultiplicity ℕ ℕ)
    (c1 c2 c3 c4 s ij smallError : ℝ)
    (olc_route : (olcGeom.baseSet.card : ℝ) ≤ (ctx.shell.X : ℝ) * ij)
    (olc_ML_budget :
      (olcGeom.multiplicityBound : ℝ) * (ctx.shell.X : ℝ) * ij
        ≤ s * (ctx.shell.X : ℝ) * ij / 2)
    (olc_return_budget :
      s * (ctx.shell.X : ℝ) * ij
        ≤ c3 * erdos260Constants.ξ * s * (ctx.shell.X : ℝ) * ij + smallError / 4)
    (hsXij : 0 ≤ s * (ctx.shell.X : ℝ) * ij)
    (ordinaryShort_bound :
      routedClassMassOf ctx.n24CarryData cls 0
        ≤ c1 * erdos260Constants.ξ * s * (ctx.shell.X : ℝ) * ij + smallError / 4)
    (semiperiodic_bound :
      routedClassMassOf ctx.n24CarryData cls 1
        ≤ c2 * erdos260Constants.ξ * s * (ctx.shell.X : ℝ) * ij + smallError / 4)
    (nonlocalLong_bound :
      routedClassMassOf ctx.n24CarryData cls 2
        ≤ c4 * erdos260Constants.ξ * s * (ctx.shell.X : ℝ) * ij + smallError / 4)
    (hSmall :
      (c1 + c2 + c3 + c4) * erdos260Constants.ξ * s * (ctx.shell.X : ℝ) * ij + smallError
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    ReturnFamilyCore erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : ℝ) ℕ ℕ where
  ordinaryShort := routedClassMassOf ctx.n24CarryData cls 0
  semiperiodic := routedClassMassOf ctx.n24CarryData cls 1
  nonlocalLong := routedClassMassOf ctx.n24CarryData cls 2
  c1 := c1
  c2 := c2
  c3 := c3
  c4 := c4
  s := s
  ij := ij
  smallError := smallError
  olcGeom := olcGeom
  olc_route := olc_route
  olc_ML_budget := olc_ML_budget
  olc_return_budget := olc_return_budget
  hsXij := hsXij
  ordinaryShort_bound := ordinaryShort_bound
  semiperiodic_bound := semiperiodic_bound
  nonlocalLong_bound := nonlocalLong_bound
  hSmall := hSmall

/-- **The Return separated local leaf package of a failing shell (manuscript shape).**

`ReturnClosedI51M2J4L6PackageInputData` at the pinned constants and the shell scale, assembled
through `ReturnFamilyCore.toPackage` from the of-shell return family.  This feeds
`ActualFailureContext.leafPhases`/`leafPhasesRunPackage`. -/
def returnLeafOfShell (ctx : ActualFailureContext) (cls : ℕ → Fin 3)
    (olcGeom : OLCEndpointMultiplicity ℕ ℕ)
    (c1 c2 c3 c4 s ij smallError : ℝ)
    (olc_route : (olcGeom.baseSet.card : ℝ) ≤ (ctx.shell.X : ℝ) * ij)
    (olc_ML_budget :
      (olcGeom.multiplicityBound : ℝ) * (ctx.shell.X : ℝ) * ij
        ≤ s * (ctx.shell.X : ℝ) * ij / 2)
    (olc_return_budget :
      s * (ctx.shell.X : ℝ) * ij
        ≤ c3 * erdos260Constants.ξ * s * (ctx.shell.X : ℝ) * ij + smallError / 4)
    (hsXij : 0 ≤ s * (ctx.shell.X : ℝ) * ij)
    (ordinaryShort_bound :
      routedClassMassOf ctx.n24CarryData cls 0
        ≤ c1 * erdos260Constants.ξ * s * (ctx.shell.X : ℝ) * ij + smallError / 4)
    (semiperiodic_bound :
      routedClassMassOf ctx.n24CarryData cls 1
        ≤ c2 * erdos260Constants.ξ * s * (ctx.shell.X : ℝ) * ij + smallError / 4)
    (nonlocalLong_bound :
      routedClassMassOf ctx.n24CarryData cls 2
        ≤ c4 * erdos260Constants.ξ * s * (ctx.shell.X : ℝ) * ij + smallError / 4)
    (hSmall :
      (c1 + c2 + c3 + c4) * erdos260Constants.ξ * s * (ctx.shell.X : ℝ) * ij + smallError
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    ReturnClosedI51M2J4L6PackageInputData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : ℝ) :=
  (returnFamilyCoreOfShell ctx cls olcGeom c1 c2 c3 c4 s ij smallError olc_route olc_ML_budget
    olc_return_budget hsXij ordinaryShort_bound semiperiodic_bound nonlocalLong_bound
    hSmall).toPackage

/-- **The four-piece non-run return mass of the of-shell family meets the I.5.1 budget.**

Sanity bound: the genuine non-run return mass — the three routed carry masses plus the genuine OLC
endpoint count — fits the return slot `cStar·ξ·X/6`. -/
theorem returnLeafOfShell_termReturn_bound (ctx : ActualFailureContext) (cls : ℕ → Fin 3)
    (olcGeom : OLCEndpointMultiplicity ℕ ℕ)
    (c1 c2 c3 c4 s ij smallError : ℝ)
    (olc_route : (olcGeom.baseSet.card : ℝ) ≤ (ctx.shell.X : ℝ) * ij)
    (olc_ML_budget :
      (olcGeom.multiplicityBound : ℝ) * (ctx.shell.X : ℝ) * ij
        ≤ s * (ctx.shell.X : ℝ) * ij / 2)
    (olc_return_budget :
      s * (ctx.shell.X : ℝ) * ij
        ≤ c3 * erdos260Constants.ξ * s * (ctx.shell.X : ℝ) * ij + smallError / 4)
    (hsXij : 0 ≤ s * (ctx.shell.X : ℝ) * ij)
    (ordinaryShort_bound :
      routedClassMassOf ctx.n24CarryData cls 0
        ≤ c1 * erdos260Constants.ξ * s * (ctx.shell.X : ℝ) * ij + smallError / 4)
    (semiperiodic_bound :
      routedClassMassOf ctx.n24CarryData cls 1
        ≤ c2 * erdos260Constants.ξ * s * (ctx.shell.X : ℝ) * ij + smallError / 4)
    (nonlocalLong_bound :
      routedClassMassOf ctx.n24CarryData cls 2
        ≤ c4 * erdos260Constants.ξ * s * (ctx.shell.X : ℝ) * ij + smallError / 4)
    (hSmall :
      (c1 + c2 + c3 + c4) * erdos260Constants.ξ * s * (ctx.shell.X : ℝ) * ij + smallError
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    routedClassMassOf ctx.n24CarryData cls 0 + routedClassMassOf ctx.n24CarryData cls 1
        + (olcGeom.endpoints.card : ℝ) + routedClassMassOf ctx.n24CarryData cls 2
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  (returnFamilyCoreOfShell ctx cls olcGeom c1 c2 c3 c4 s ij smallError olc_route olc_ML_budget
    olc_return_budget hsXij ordinaryShort_bound semiperiodic_bound nonlocalLong_bound
    hSmall).termReturn_bound

/-- **Per-element charge domination of a routed non-OLC return mass** (the generic per-output charge
mechanism, `routedClassMassOf_le_countMultiplier`, of which `charge_perOutput_by_matching` is the
matching-map form): if every high-excess start routed to the non-OLC sub-piece `i` charges at most
`multiplier` and the class fibre has at most `count` elements, the routed return mass is
`≤ count·multiplier`.  This is how the L.2.2 non-OLC count hypotheses are discharged from the
synchronizing-set / short-return-envelope / return-length per-element data. -/
theorem returnRoutedClassMass_le_countMultiplier (ctx : ActualFailureContext) (cls : ℕ → Fin 3)
    (i : Fin 3) {multiplier count : ℝ}
    (hpoint : ∀ k ∈ routedFibre ctx.n24CarryData cls i,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        ≤ multiplier)
    (hmult_nonneg : 0 ≤ multiplier)
    (hcard : ((routedFibre ctx.n24CarryData cls i).card : ℝ) ≤ count) :
    routedClassMassOf ctx.n24CarryData cls i ≤ count * multiplier :=
  routedClassMassOf_le_countMultiplier ctx.n24CarryData cls i hpoint hmult_nonneg hcard

end

end Erdos260
