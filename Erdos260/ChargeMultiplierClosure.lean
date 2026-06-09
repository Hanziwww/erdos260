import Mathlib
import Erdos260.CarryRouting
import Erdos260.GeomMarkerCoverage
import Erdos260.TRTChargeBound
import Erdos260.AppendixI_PackageBounds
import Erdos260.DensePackChargeBound
import Erdos260.OldResCountFromCarry
import Erdos260.UnconditionalAssembly

/-!
# Per-class charge multipliers — connecting the routing fibres to the proved phase budgets

The deepest residual atom of the v5 reduction (`UnconditionalAssembly.charge`) bundles a
`CarryPriorityRoutingCharge`: the genuinely-constructed J.1.1 first-obstruction routing
together with **five per-class mass multipliers**

```
hChernoff : routedClassMassOf carryData route 0 ≤ termChernoff   (class 0)
hCnl      : routedClassMassOf carryData route 1 ≤ termCnl        (class 1)
hDensePack: routedClassMassOf carryData route 3 ≤ termDensePack  (class 3)
hTRT      : routedClassMassOf route 2 + route 4 + route 5 ≤ termTower+termReturn+termRun
hOldRes   : routedClassMassOf carryData route 6 ≤ oldResMass     (class 6)
```

each routing one of the seven v5 charge classes' carry **window-excess mass** into its phase
term.  This file isolates exactly what is — and is **not** — derivable about these multipliers
from the **already-proved per-phase budgets**
(`Erdos260.AppendixI_PackageBounds.term*_le_budget`, `Erdos260.TRTChargeBound`,
`Erdos260.DensePackChargeBound`, `Erdos260.OldResCountFromCarry`).

## The honest structural fact

A per-class multiplier `routedClassMassOf carryData route i ≤ termX phases` and the proved
budget `termX phases ≤ cStar·ξ·X/6` point in **the same direction with respect to `termX`** but
they are **orthogonal facts**:

* the **proved budget** bounds the phase *term* `termX` (built from the phase-factory data) from
  above by the numeric floor `cStar·ξ·X/6`;
* the **multiplier** bounds the routed carry *mass* `routedClassMassOf` (the sum of window
  excesses over the class-`i` fibre, pure carry data) from above by the phase term.

The proved budgets **cannot** supply a multiplier: there is no unconditional relation between the
carry window-excess mass of a routing fibre and an independent phase-factory term.  That relation
is exactly the manuscript's J.1.1 / N.24 / I.9 *charging* (Appendix L.2 / N.3.3 family/transcript
dynamics) — the deep content the routing was built to isolate.

What the budgets **do** give, and what this file genuinely proves, is the **composition**: each
per-class multiplier, chained with its proved budget, collapses the per-class obligation to the
*numeric* per-phase floor.  And the multipliers themselves are reduced to their finest manuscript
granularity — the **count×multiplier** mechanism (the proved
`ChargeBridgeReduction.densePackMass_le_of_density` core, applied to the routing fibre) and the
**Lemma N.3.1 same-threshold compression** (the proved `TerminalOutputData.compression`).

## What is genuinely proved here (axiom-clean)

* `routedClassMassOf_le_countMultiplier` — the **count×multiplier reduction of any routed class
  mass**: if every high-excess start in the class-`i` fibre has window excess `≤ mult` and the
  fibre has `≤ count` members, then `routedClassMassOf ≤ count·mult`.  This is the carry-side twin
  of `densePackMass_le_of_density`, reused verbatim.
* `routed{Chernoff,Cnl,Tower,DensePack,Return,Run}_le_budget`,
  `routedTRT_le_budget` — the **budget chaining**: a per-class multiplier, composed with the
  PROVED `term*_le_budget`, yields the numeric per-phase floor `cStar·ξ·X/6` (resp. `/2` jointly).
* `highExcessMass_le_budget_add_oldRes_of_multipliers` — assembling the five multipliers and the
  PROVED `ClosurePhaseMass_le_budget` into the augmented bridge at the numeric floor.
* `routedTRT_le_packageTerms_fin7` — the **joint TRT multiplier** for the `Fin 7` routing via the
  PROVED Lemma N.3.1 compression (the `Fin 7` analog of `TRTChargeBound.routedTRT_le_packageTerms`).
* `CarryPriorityRoutingCharge.ofGeom` — assembling the charge atom from the **geometric routing**
  `G.toRouting config` (whose coverage primitive is `pkg_exposes`) plus the five multipliers, so
  the routing's only coverage input is the single geometric primitive.
* `CarryPriorityRoutingCharge.ofGeomFibre` — the **fully reduced** constructor: the five
  multipliers are themselves derived from per-fibre count×multiplier data (classes 0,1,3,6) and
  the N.3.1 compression data (classes 2,4,5), so the charge atom is reduced to `pkg_exposes` plus
  the genuinely per-shell count/pointwise/routing data the proved cores consume.
* `ShellRoutedChargeAtom.ofRoutingCharge` — wrapping a constructed `CarryPriorityRoutingCharge`
  with the L.6.5 old-residual smallness into the actual `charge` atom shape.
* `oldResMass_le_of_carryFailure'` — the OldRes proved budget (`oldRes_le_of_carryFailure`)
  re-exposed as the density-small bound on the class-6 mass.

## Honest verdict (see the residual inventory at the bottom)

**No per-class multiplier is CLOSED** (none follows from a proved budget): each is *reduced* to
per-fibre count×multiplier / compression data, with the proved budgets supplying only the
term→floor step.  **`pkg_exposes` is genuinely IRREDUCIBLE**: it is the geometric primitive that a
PKG verdict exposes a real charge class; the scan's exhaustiveness only ever supplies the
CleanCNL catch-all (`j11Scan_catchall_only`), and `pkg_exposes` is realized — but not derived —
by concrete witnesses (`denseObstructionGeometry`).

No `sorry`, `axiom`, or `admit`.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 1.  The count×multiplier reduction of a routed class mass

`routedClassMassOf carryData route i` is, by definition, the sum of the window excess over the
class-`i` routing fibre.  The proved generic count×multiplier core
`ChargeBridgeReduction.densePackMass_le_of_density` therefore applies **verbatim** to the routing
fibre: if every member's window excess is bounded by a per-fibre multiplier (the K.1.2/L.20
residual multiplier, *linear in the active floor `Y`*) and the fibre count is bounded, the routed
class mass is bounded by `count · multiplier`.  This is the carry-side twin of the DensePack /
old-residual mass estimates, now applied to the J.1.1 routing itself. -/

/-- The class-`i` fibre of a routing: the high-excess starts the routing assigns to class `i`. -/
def routedFibre {shell : FailingDyadicShell} {cPr : ℝ} {ι : Type*} [DecidableEq ι]
    (carryData : CarryDataFromFailure shell cPr) (route : Nat → ι) (i : ι) : Finset ℕ :=
  (highExcessStarts carryData.starts (hitGap carryData.a)
      carryData.r carryData.T carryData.Y).filter (fun k => route k = i)

/-- The routed class mass is the window-excess sum over the class fibre (definitional). -/
theorem routedClassMassOf_eq_sum_fibre {shell : FailingDyadicShell} {cPr : ℝ}
    {ι : Type*} [DecidableEq ι]
    (carryData : CarryDataFromFailure shell cPr) (route : Nat → ι) (i : ι) :
    routedClassMassOf carryData route i
      = ∑ k ∈ routedFibre carryData route i,
          windowExcess (hitGap carryData.a) k carryData.r carryData.T := rfl

/-- **Count×multiplier reduction of a routed class mass (faithful — reuses
`densePackMass_le_of_density`).**

If every high-excess start `k` in the class-`i` fibre has window excess
`≤ multiplier` (the per-fibre residual multiplier, K.1.2/L.20: linear in the active floor `Y`),
and the fibre has at most `count` members (the J.1.1 fibre population), then the routed class mass
obeys `routedClassMassOf ≤ count · multiplier`.

This is the carry-side analog of the manuscript count×multiplier mass mechanism
(`densePackMass_le_of_density`, `oldRes_le_of_density`).  It reduces the per-class multiplier
`routedClassMassOf ≤ termX` to the per-fibre pointwise bound `hpoint`, the fibre count `hcard`,
and the identification `count · multiplier ≤ termX` — the genuinely per-shell data the proved
budgets consume.  It does **not** close the multiplier. -/
theorem routedClassMassOf_le_countMultiplier {shell : FailingDyadicShell} {cPr : ℝ}
    {ι : Type*} [DecidableEq ι]
    (carryData : CarryDataFromFailure shell cPr) (route : Nat → ι) (i : ι)
    {multiplier count : ℝ}
    (hpoint : ∀ k ∈ routedFibre carryData route i,
      windowExcess (hitGap carryData.a) k carryData.r carryData.T ≤ multiplier)
    (hmult_nonneg : 0 ≤ multiplier)
    (hcard : ((routedFibre carryData route i).card : ℝ) ≤ count) :
    routedClassMassOf carryData route i ≤ count * multiplier := by
  rw [routedClassMassOf_eq_sum_fibre]
  exact densePackMass_le_of_density
    (D₀ := routedFibre carryData route i)
    (fiberMass := fun k => windowExcess (hitGap carryData.a) k carryData.r carryData.T)
    (multiplier := multiplier) (markerCount := count) hpoint hmult_nonneg hcard

/-! ## 2.  Budget chaining: each per-class multiplier collapses to the numeric phase floor

These lemmas demonstrate the genuine *use* of the proved per-phase budgets
(`Erdos260.AppendixI_PackageBounds.term*_le_budget`): a per-class multiplier
`routedClassMassOf ≤ termX`, composed with the proved `termX ≤ cStar·ξ·X/6`, yields the numeric
per-phase floor.  The multiplier `hMult` is the genuine residual input; the budget is reused. -/

variable {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}

/-- **Class 0 (Chernoff) → numeric floor.**  The Chernoff multiplier, chained with the proved
Lemma 22.1 budget `termChernoff_le_budget`. -/
theorem routedChernoff_le_budget
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr) (route : Nat → Fin 7)
    (hMult : routedClassMassOf carryData route 0 ≤ termChernoff phases.toClosurePhaseData) :
    routedClassMassOf carryData route 0 ≤ cStar * ξ * (shell.X : ℝ) / 6 :=
  hMult.trans (termChernoff_le_budget phases.toClosurePhaseData)

/-- **Class 1 (clean-CNL) → numeric floor.**  The CNL multiplier, chained with the proved
Theorem G.6 budget `termCnl_le_budget`. -/
theorem routedCnl_le_budget
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr) (route : Nat → Fin 7)
    (hMult : routedClassMassOf carryData route 1 ≤ termCnl phases.toClosurePhaseData) :
    routedClassMassOf carryData route 1 ≤ cStar * ξ * (shell.X : ℝ) / 6 :=
  hMult.trans (termCnl_le_budget phases.toClosurePhaseData shell.X_pos_real.le)

/-- **Class 3 (DensePack) → numeric floor.**  The DensePack multiplier, chained with the proved
Lemma I.4.1 + K.1.3 budget `termDensePack_le_budget`. -/
theorem routedDensePack_le_budget
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr) (route : Nat → Fin 7)
    (hMult : routedClassMassOf carryData route 3 ≤ termDensePack phases.toClosurePhaseData) :
    routedClassMassOf carryData route 3 ≤ cStar * ξ * (shell.X : ℝ) / 6 :=
  hMult.trans (termDensePack_le_budget phases.toClosurePhaseData)

/-- **Class 2 (Tower) → numeric floor (individual budget).**  Provided for completeness: the
per-class Tower budget `termTower_le_budget` is proved, even though Tower/Return/Run are bounded
*jointly* in the v5 charge bridge (`routedTRT_le_budget`). -/
theorem routedTower_le_budget
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr) (route : Nat → Fin 7)
    (hMult : routedClassMassOf carryData route 2 ≤ termTower phases.toClosurePhaseData) :
    routedClassMassOf carryData route 2 ≤ cStar * ξ * (shell.X : ℝ) / 6 :=
  hMult.trans (termTower_le_budget phases.toClosurePhaseData)

/-- **Class 4 (Return) → numeric floor (individual budget).** -/
theorem routedReturn_le_budget
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr) (route : Nat → Fin 7)
    (hMult : routedClassMassOf carryData route 4 ≤ termReturn phases.toClosurePhaseData) :
    routedClassMassOf carryData route 4 ≤ cStar * ξ * (shell.X : ℝ) / 6 :=
  hMult.trans (termReturn_le_budget phases.toClosurePhaseData)

/-- **Class 5 (Run) → numeric floor (individual budget).** -/
theorem routedRun_le_budget
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr) (route : Nat → Fin 7)
    (hMult : routedClassMassOf carryData route 5 ≤ termRun phases.toClosurePhaseData) :
    routedClassMassOf carryData route 5 ≤ cStar * ξ * (shell.X : ℝ) / 6 :=
  hMult.trans (termRun_le_budget phases.toClosurePhaseData)

/-- **Classes 2+4+5 (joint TRT) → numeric floor.**  The joint Tower+Return+Run multiplier, chained
with the proved TRT budget `termTRT_toClosurePhaseData_le_half_budget` (`= 3·(cStar·ξ·X/6)`). -/
theorem routedTRT_le_budget
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr) (route : Nat → Fin 7)
    (hMult : routedClassMassOf carryData route 2 + routedClassMassOf carryData route 4
        + routedClassMassOf carryData route 5
      ≤ termTower phases.toClosurePhaseData + termReturn phases.toClosurePhaseData
        + termRun phases.toClosurePhaseData) :
    routedClassMassOf carryData route 2 + routedClassMassOf carryData route 4
        + routedClassMassOf carryData route 5
      ≤ cStar * ξ * (shell.X : ℝ) / 2 :=
  hMult.trans (termTRT_toClosurePhaseData_le_half_budget phases)

/-! ### Assembling the augmented bridge at the numeric floor

Given the five multipliers (the genuine residual), the proved `ClosurePhaseMass_le_budget`
collapses the augmented bridge `highExcessMass ≤ ClosurePhaseMass + oldResMass` to the numeric
floor `highExcessMass ≤ cStar·ξ·X + oldResMass`. -/

/-- **Augmented bridge at the numeric floor, from the five multipliers.**

Bundles the five per-class multipliers into a `RoutedHighExcessChargeDataOldRes`, applies its
proved augmented-bridge summation, then the proved `ClosurePhaseMass_le_budget`.  The five
multipliers are the genuine residual; the summation and budget are reused. -/
theorem highExcessMass_le_budget_add_oldRes_of_multipliers
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr) (route : Nat → Fin 7) (oldResMass : ℝ)
    (hChernoff : routedClassMassOf carryData route 0 ≤ termChernoff phases.toClosurePhaseData)
    (hCnl : routedClassMassOf carryData route 1 ≤ termCnl phases.toClosurePhaseData)
    (hDensePack : routedClassMassOf carryData route 3 ≤ termDensePack phases.toClosurePhaseData)
    (hTRT : routedClassMassOf carryData route 2 + routedClassMassOf carryData route 4
        + routedClassMassOf carryData route 5
      ≤ termTower phases.toClosurePhaseData + termReturn phases.toClosurePhaseData
        + termRun phases.toClosurePhaseData)
    (hOldRes : routedClassMassOf carryData route 6 ≤ oldResMass) :
    highExcessMass (highExcessStarts carryData.starts (hitGap carryData.a)
        carryData.r carryData.T carryData.Y)
        (hitGap carryData.a) carryData.r carryData.T
      ≤ cStar * ξ * (shell.X : ℝ) + oldResMass := by
  have hbridge :
      highExcessMass (highExcessStarts carryData.starts (hitGap carryData.a)
          carryData.r carryData.T carryData.Y)
          (hitGap carryData.a) carryData.r carryData.T
        ≤ ClosurePhaseMass phases.toClosurePhaseData + oldResMass :=
    RoutedHighExcessChargeDataOldRes.highExcess_le_phaseMass_add_oldRes
      { route := route
        hChernoff := hChernoff
        hCnl := hCnl
        hDensePack := hDensePack
        hTRT := hTRT
        hOldRes := hOldRes }
  have hbudget : ClosurePhaseMass phases.toClosurePhaseData ≤ cStar * ξ * (shell.X : ℝ) :=
    ClosurePhaseMass_le_budget phases.toClosurePhaseData shell.X_pos_real.le
  linarith

/-! ## 3.  The joint TRT multiplier via the proved Lemma N.3.1 compression (`Fin 7`)

The `Fin 7` analog of `TRTChargeBound.routedTRT_le_packageTerms`: the joint Tower+Return+Run carry
mass is dominated by the three package terms, with the **proved** Lemma N.3.1 `C_Q`-to-one
compression `comp.compression` reused as the central step.  Reduces the joint multiplier to the
two faithful inputs `hRouteToOutput` (J.1.2 / N.1.0 charging onto the same-threshold output
family) and `hAbsorb` (N.3.3 / N.24 absorption). -/

/-- **Joint TRT multiplier for the `Fin 7` routing (reuses the proved N.3.1 compression).** -/
theorem routedTRT_le_packageTerms_fin7
    {β σ : Type*} [DecidableEq σ]
    (comp : AppendixN.TerminalOutputData β σ)
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (route : Nat → Fin 7)
    (hRouteToOutput :
      routedClassMassOf carryData route 2 + routedClassMassOf carryData route 4
          + routedClassMassOf carryData route 5
        ≤ ∑ b ∈ comp.branches, comp.wtO b)
    (hAbsorb :
      comp.CQ * (comp.YO * ∑ ζ ∈ comp.ground, comp.fibreMass ζ)
        ≤ termTower phases.toClosurePhaseData + termReturn phases.toClosurePhaseData
            + termRun phases.toClosurePhaseData) :
    routedClassMassOf carryData route 2 + routedClassMassOf carryData route 4
        + routedClassMassOf carryData route 5
      ≤ termTower phases.toClosurePhaseData + termReturn phases.toClosurePhaseData
          + termRun phases.toClosurePhaseData :=
  joint_le_of_compression_absorbed hRouteToOutput comp.compression hAbsorb

/-! ## 4.  Assembling the charge atom on the geometric routing (coverage = `pkg_exposes`)

The charge atom's routing is an abstract `CarryPriorityRouting`.  Building it as the **geometric**
routing `G.toRouting config` of a `CNLObstructionGeometry` makes its single coverage primitive be
`pkg_exposes` (`Erdos260.GeomMarkerCoverage`: `pkg_marked ⟺ pkg_exposes`).  The two constructors
below assemble the charge atom from this geometric routing: `ofGeom` takes the five multipliers
directly; `ofGeomFibre` derives them from the per-fibre count×multiplier / N.3.1 compression data
the proved cores consume. -/

/-- **Charge atom from the geometric routing + the five multipliers.**

The routing is `G.toRouting config` (coverage primitive = `pkg_exposes`); the five multipliers are
the genuine residual dynamical inputs. -/
def CarryPriorityRoutingCharge.ofGeom
    {oldResMass : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (G : CNLObstructionGeometry) (config : Nat → LiftState)
    (hChernoff :
      routedClassMassOf carryData (G.toRouting config).classify 0
        ≤ termChernoff phases.toClosurePhaseData)
    (hCnl :
      routedClassMassOf carryData (G.toRouting config).classify 1
        ≤ termCnl phases.toClosurePhaseData)
    (hDensePack :
      routedClassMassOf carryData (G.toRouting config).classify 3
        ≤ termDensePack phases.toClosurePhaseData)
    (hTRT :
      routedClassMassOf carryData (G.toRouting config).classify 2
          + routedClassMassOf carryData (G.toRouting config).classify 4
          + routedClassMassOf carryData (G.toRouting config).classify 5
        ≤ termTower phases.toClosurePhaseData + termReturn phases.toClosurePhaseData
            + termRun phases.toClosurePhaseData)
    (hOldRes :
      routedClassMassOf carryData (G.toRouting config).classify 6 ≤ oldResMass) :
    CarryPriorityRoutingCharge phases carryData oldResMass where
  routing := G.toRouting config
  hChernoff := hChernoff
  hCnl := hCnl
  hDensePack := hDensePack
  hTRT := hTRT
  hOldRes := hOldRes

/-- **Fully reduced charge atom from per-fibre count×multiplier + N.3.1 compression data.**

The headline reduction.  The routing is the geometric `G.toRouting config` (coverage primitive =
`pkg_exposes`).  Each separable multiplier (classes 0,1,3,6) is **derived** from per-fibre
count×multiplier data — a per-fibre window-excess bound (`hpoint*`, the K.1.2/L.20 residual
multiplier linear in `Y`), the fibre count (`hcard*`), and the identification
`count·mult ≤ termX` (`hbud*`) — via the proved `routedClassMassOf_le_countMultiplier`.  The joint
TRT multiplier (classes 2,4,5) is **derived** from the routing/absorption inputs via the proved
N.3.1 compression (`routedTRT_le_packageTerms_fin7`).

So the charge atom is reduced to `pkg_exposes` (inside `G`) plus the genuinely per-shell
count/pointwise/identification/routing data — exactly the data the proved budgets and compression
cores consume.  No multiplier is closed; each is exposed at its finest manuscript granularity. -/
def CarryPriorityRoutingCharge.ofGeomFibre
    {oldResMass : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (G : CNLObstructionGeometry) (config : Nat → LiftState)
    -- class 0 (Chernoff) count×multiplier data
    {multChernoff countChernoff : ℝ}
    (hpoint0 : ∀ k ∈ routedFibre carryData (G.toRouting config).classify 0,
        windowExcess (hitGap carryData.a) k carryData.r carryData.T ≤ multChernoff)
    (hnn0 : 0 ≤ multChernoff)
    (hcard0 : ((routedFibre carryData (G.toRouting config).classify 0).card : ℝ) ≤ countChernoff)
    (hbud0 : countChernoff * multChernoff ≤ termChernoff phases.toClosurePhaseData)
    -- class 1 (clean-CNL) count×multiplier data
    {multCnl countCnl : ℝ}
    (hpoint1 : ∀ k ∈ routedFibre carryData (G.toRouting config).classify 1,
        windowExcess (hitGap carryData.a) k carryData.r carryData.T ≤ multCnl)
    (hnn1 : 0 ≤ multCnl)
    (hcard1 : ((routedFibre carryData (G.toRouting config).classify 1).card : ℝ) ≤ countCnl)
    (hbud1 : countCnl * multCnl ≤ termCnl phases.toClosurePhaseData)
    -- class 3 (DensePack) count×multiplier data
    {multDP countDP : ℝ}
    (hpoint3 : ∀ k ∈ routedFibre carryData (G.toRouting config).classify 3,
        windowExcess (hitGap carryData.a) k carryData.r carryData.T ≤ multDP)
    (hnn3 : 0 ≤ multDP)
    (hcard3 : ((routedFibre carryData (G.toRouting config).classify 3).card : ℝ) ≤ countDP)
    (hbud3 : countDP * multDP ≤ termDensePack phases.toClosurePhaseData)
    -- classes 2+4+5 (joint TRT) via the proved N.3.1 compression
    {β σ : Type*} [DecidableEq σ]
    (comp : AppendixN.TerminalOutputData β σ)
    (hRouteToOutput :
      routedClassMassOf carryData (G.toRouting config).classify 2
          + routedClassMassOf carryData (G.toRouting config).classify 4
          + routedClassMassOf carryData (G.toRouting config).classify 5
        ≤ ∑ b ∈ comp.branches, comp.wtO b)
    (hAbsorb :
      comp.CQ * (comp.YO * ∑ ζ ∈ comp.ground, comp.fibreMass ζ)
        ≤ termTower phases.toClosurePhaseData + termReturn phases.toClosurePhaseData
            + termRun phases.toClosurePhaseData)
    -- class 6 (old-residual) count×multiplier data
    {multOR countOR : ℝ}
    (hpoint6 : ∀ k ∈ routedFibre carryData (G.toRouting config).classify 6,
        windowExcess (hitGap carryData.a) k carryData.r carryData.T ≤ multOR)
    (hnn6 : 0 ≤ multOR)
    (hcard6 : ((routedFibre carryData (G.toRouting config).classify 6).card : ℝ) ≤ countOR)
    (hbud6 : countOR * multOR ≤ oldResMass) :
    CarryPriorityRoutingCharge phases carryData oldResMass :=
  CarryPriorityRoutingCharge.ofGeom phases carryData G config
    ((routedClassMassOf_le_countMultiplier carryData (G.toRouting config).classify 0
        hpoint0 hnn0 hcard0).trans hbud0)
    ((routedClassMassOf_le_countMultiplier carryData (G.toRouting config).classify 1
        hpoint1 hnn1 hcard1).trans hbud1)
    ((routedClassMassOf_le_countMultiplier carryData (G.toRouting config).classify 3
        hpoint3 hnn3 hcard3).trans hbud3)
    (routedTRT_le_packageTerms_fin7 comp phases carryData (G.toRouting config).classify
        hRouteToOutput hAbsorb)
    ((routedClassMassOf_le_countMultiplier carryData (G.toRouting config).classify 6
        hpoint6 hnn6 hcard6).trans hbud6)

/-! ## 5.  Wrapping into the actual `charge` atom + the OldRes proved budget -/

/-- **Wrap a constructed routing charge into the `ShellRoutedChargeAtom`.**

The actual `charge` atom of `Erdos260MinimalAtoms` is a `ShellRoutedChargeAtom`: a
`CarryPriorityRoutingCharge` plus the L.6.5 old-residual smallness `oldResMass ≤ cQ·cStarSmall·X`.
This assembles it from any constructed routing charge (e.g. `ofGeom` / `ofGeomFibre`) and the
smallness bound. -/
def ShellRoutedChargeAtom.ofRoutingCharge
    {shell : FailingDyadicShell}
    {phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)}
    {carryData : CarryDataFromFailure shell erdos260Constants.cPr}
    {cQ cStarSmall oldResMass : ℝ}
    (rc : CarryPriorityRoutingCharge phases carryData oldResMass)
    (hsmall : oldResMass ≤ cQ * cStarSmall * (shell.X : ℝ)) :
    ShellRoutedChargeAtom phases carryData cQ cStarSmall where
  oldResMass := oldResMass
  routingCharge := rc
  oldRes_le := hsmall

/-- **OldRes proved budget (Lemma L.6.5) re-exposed as the class-6 branch-mass smallness.**

`Erdos260.OldResCountFromCarry.oldRes_le_of_carryFailure` derives, from the carry failure data,
the density-sensitive bound on the branch-level old-residual mass `OldRes = ∑_{k∈K} oldResAt k`:
the failure-bounded endpoint count `|K| ≤ c₀·X + collar` (eq. L.22) times the per-index
multiplier×support `(Cres·Y)·(Csupp·Ij)` (eqs. L.20/L.21).  This is the genuine OldRes "budget"
backing the `oldResMass` smallness; the per-index primitives `hpoint`/`hbound_nonneg` and the
window-subset `hKsub` remain the faithful analytic inputs. -/
theorem oldResMass_le_of_carryFailure'
    {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr) (cW : Nat)
    {K : Finset ℕ} {oldResAt : ℕ → ℝ} {Cres Y Csupp Ij : ℝ}
    (hKsub : K ⊆ windowHitIndices carryData.a (shell.X - cW) (2 * shell.X + cW))
    (hpoint : ∀ k ∈ K, oldResAt k ≤ (Cres * Y) * (Csupp * Ij))
    (hbound_nonneg : 0 ≤ (Cres * Y) * (Csupp * Ij)) :
    (∑ k ∈ K, oldResAt k)
      ≤ shell.c0 * (shell.X : ℝ) * ((Cres * Y) * (Csupp * Ij))
        + (2 * (cW : ℝ) + 1) * ((Cres * Y) * (Csupp * Ij)) :=
  oldRes_le_of_carryFailure carryData cW hKsub hpoint hbound_nonneg

/-! ## 6.  `pkg_exposes` — the irreducible geometric primitive

The routing of the charge atom (built geometrically as `G.toRouting config`) reduces its coverage
to the single primitive `pkg_exposes` (`Erdos260.GeomMarkerCoverage`, where `pkg_marked ⟺
pkg_exposes`).  We record precisely why `pkg_exposes` is **irreducible**, and that it is
**inhabitable** (so the residual is consistent, not vacuous). -/

/-- **Exhaustiveness is not coverage (irreducibility witness).**

The J.1.1 scan's exhaustiveness only ever supplies the deliberately-last CleanCNL catch-all
(class `1`): on the profile carrying *only* class `1`, the scan returns `1`, never a package class.
So `pkg_exposes` — that a PKG verdict exposes a **genuine** charge class — cannot be derived from
the scan's exhaustiveness/single-valuedness.  This is `j11Scan_catchall_only`, re-exposed as the
precise statement of why coverage is a separate primitive. -/
theorem pkg_exposes_not_from_exhaustiveness :
    j11Scan ({1} : Finset (Fin 7)) = some 1 :=
  j11Scan_catchall_only

/-- **`pkg_exposes` is inhabitable (consistency of the residual).**

There exists a concrete obstruction geometry whose `pkg_exposes` holds — `denseObstructionGeometry`
exposes the DensePack class `3` on every package exit.  So the irreducible primitive is *realized*
by a witness, hence consistent and non-vacuous; it is the universal statement about the *real*
carry/CNL geometry of a failing shell that remains the deep K/L/N input. -/
theorem pkg_exposes_inhabited :
    ∃ G : CNLObstructionGeometry,
      ∀ s : LiftState, canonicalCNLSelector (G.cnlOf s) = some CNLClass.pkg →
        ∃ c : Fin 7, G.geomDetect c s = true :=
  ⟨denseObstructionGeometry, denseObstructionGeometry.pkg_exposes⟩

/-! ## 7.  Honest residual inventory -/

/-- The honest status of the per-class multipliers and `pkg_exposes` after this file. -/
def chargeMultiplierResidual : List String :=
  [ "Classes 0/1/3 (Chernoff/CNL/DensePack), 6 (OldRes): each per-class multiplier " ++
      "routedClassMassOf ≤ termX is REDUCED (NOT closed) to per-fibre count×multiplier data via " ++
      "the proved core `densePackMass_le_of_density` (`routedClassMassOf_le_countMultiplier`): a " ++
      "per-fibre window-excess bound (K.1.2/L.20, linear in Y), a fibre count, and the " ++
      "identification count·mult ≤ termX. The proved budgets `term*_le_budget` then collapse " ++
      "termX to the numeric floor cStar·ξ·X/6 (`routed*_le_budget`).",
    "Classes 2+4+5 (Tower/Return/Run): the joint multiplier is REDUCED (NOT closed) via the " ++
      "proved Lemma N.3.1 compression `TerminalOutputData.compression` " ++
      "(`routedTRT_le_packageTerms_fin7`) to the routing input `hRouteToOutput` (J.1.2/N.1.0) " ++
      "and the absorption `hAbsorb` (N.3.3/N.24); the proved TRT budget then gives cStar·ξ·X/2.",
    "NOT DERIVABLE FROM A PROVED BUDGET: no per-class multiplier follows from a proved phase " ++
      "budget. The budgets bound the phase TERM termX ≤ floor; the multiplier bounds the routed " ++
      "carry MASS ≤ termX — the orthogonal J.1.1/N.24/I.9 charging direction. They compose " ++
      "(routedClassMassOf ≤ termX ≤ floor) but the budgets cannot supply the first step.",
    "pkg_exposes: IRREDUCIBLE. The scan's exhaustiveness supplies only the CleanCNL catch-all " ++
      "(`pkg_exposes_not_from_exhaustiveness`: j11Scan {1} = some 1). pkg_exposes — that a PKG " ++
      "verdict exposes a genuine charge class — is the smallest deep K/L/N geometric primitive; " ++
      "it is inhabitable (`pkg_exposes_inhabited`, denseObstructionGeometry) hence consistent, " ++
      "but not derivable. It is the routing's single coverage residual (pkg_marked ⟺ pkg_exposes)." ]

theorem chargeMultiplierResidual_nonempty : chargeMultiplierResidual ≠ [] := by
  simp [chargeMultiplierResidual]

end

end Erdos260
