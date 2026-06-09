import Erdos260.TowerFamily
import Erdos260.UnconditionalTheorem

/-!
# L.3/I.3 Tower local leaf, inhabited from a genuine failing dyadic shell

This file makes the Tower separated local leaf **unconditional in the shell**: it builds the
manuscript-shaped `TowerClosedL31I31PackageInputData` for an `ActualFailureContext` from

* the **shell-closed E.2–E.4 recurrent cycle** `towerCycleOfFailingShellClosed` (its `.D` carry-fibre
  cycle is derived from the failing shell with no extra hypothesis), and
* a **genuine charged tower-exit family** obtained by re-indexing the *actual* high-excess carry
  starts of the shell through `towerExitOf : ℕ ↪ TowerExit`, with the per-branch charged weight equal
  to the genuine carry-window excess.

It never uses the forbidden empty `emptyTowerFamilyInput`/`emptyRouting` witnesses: the routed
tower-exit masses are *definitionally* the routed carry masses
(`towerExitRoutingOfShell_routedMass`): `routedMass c = routedClassMassOf ctx.n24CarryData cls c`.

## What is closed unconditionally (from the shell)

* The E.2–E.4 cycle witness (`cycle := (towerCycleOfFailingShellClosed …).D`).
* The L.3.1 routed-exit partition (proved in `TowerFamily`) carried on the actual carry fibre.
* The routed-output absorption (taken tight: `C_T = 1`, each routed mass absorbing into itself).
* The per-class routed-mass identity to `routedClassMassOf`.

## Residual cores exposed as explicit named hypotheses (NOT closed here)

* `cls : ℕ → TowerExitClass` — the **L.3.1 single-valued first-obstruction classifier** routing each
  high-excess carry start to its tower-exit destination (Run / non-run Return / DensePack / clean CNL
  tail / lower-order remainder), with Lemma L.2.4 disjointness.
* `hBudget` — the **I.3.1 numerical budget** that the total routed carry mass over the five L.3.1
  destinations meets the tower slot `cStar·ξ·X/6` (needs I.4.1 dense-packing + M.2.2 + the K.4
  `c_* ≪ ρ_D κ ξ` hierarchy at large `X`).

No `sorry`, `axiom`, or `admit`.  No empty/trivial witnesses.
-/

namespace Erdos260

open Finset

noncomputable section

/-- The canonical injection of a carry start `k` into a charged tower exit, recording `k` in the
`layerBound` slot (the base source/target vertices are fixed). -/
def towerExitOf (k : ℕ) : TowerExit where
  source := ⟨0, 0, none⟩
  target := ⟨0, 0, none⟩
  layerBound := k

@[simp] theorem towerExitOf_layerBound (k : ℕ) : (towerExitOf k).layerBound = k := rfl

theorem towerExitOf_injective : Function.Injective towerExitOf := by
  intro x y hxy
  simpa [towerExitOf] using congrArg TowerExit.layerBound hxy

/-- **The L.3.1 routed tower-exit family of a failing shell.**

The entry/exit set is the image of the shell's actual high-excess carry starts under `towerExitOf`;
the charged weight is the genuine carry-window excess; and the destination of each exit is the
L.3.1 classifier `cls` applied to the recorded carry start. -/
def towerExitRoutingOfShell (ctx : ActualFailureContext) (cls : ℕ → TowerExitClass) :
    TowerExitRouting where
  entryExitSet :=
    (highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
      ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y).image towerExitOf
  weight := fun b =>
    ⟨windowExcess (hitGap ctx.n24CarryData.a) b.layerBound ctx.n24CarryData.r ctx.n24CarryData.T,
      windowExcess_nonneg _ _ _ _⟩
  route := fun b => cls b.layerBound

@[simp] theorem towerExitRoutingOfShell_entryExitSet
    (ctx : ActualFailureContext) (cls : ℕ → TowerExitClass) :
    (towerExitRoutingOfShell ctx cls).entryExitSet
      = (highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
          ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y).image towerExitOf := rfl

@[simp] theorem towerExitRoutingOfShell_route
    (ctx : ActualFailureContext) (cls : ℕ → TowerExitClass) (b : TowerExit) :
    (towerExitRoutingOfShell ctx cls).route b = cls b.layerBound := rfl

@[simp] theorem towerExitRoutingOfShell_weight_val
    (ctx : ActualFailureContext) (cls : ℕ → TowerExitClass) (b : TowerExit) :
    ((towerExitRoutingOfShell ctx cls).weight b : ℝ)
      = windowExcess (hitGap ctx.n24CarryData.a) b.layerBound ctx.n24CarryData.r
          ctx.n24CarryData.T := rfl

/-- **Each routed tower-exit mass IS the routed carry mass** (genuine, not a free scalar):
the fibrewise charged tower-exit mass landing in class `c` equals the high-excess carry mass routed
to `c` by the L.3.1 classifier. -/
theorem towerExitRoutingOfShell_routedMass
    (ctx : ActualFailureContext) (cls : ℕ → TowerExitClass) (c : TowerExitClass) :
    (towerExitRoutingOfShell ctx cls).routedMass c
      = routedClassMassOf ctx.n24CarryData cls c := by
  classical
  have hinj : ∀ x ∈ (highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
        ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y),
      ∀ y ∈ (highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
        ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y),
      towerExitOf x = towerExitOf y → x = y :=
    fun x _ y _ hxy => towerExitOf_injective hxy
  rw [TowerExitRouting.routedMass]
  simp only [towerExitRoutingOfShell_entryExitSet, towerExitRoutingOfShell_route,
    towerExitRoutingOfShell_weight_val]
  rw [Finset.sum_filter, Finset.sum_image hinj]
  simp only [towerExitOf_layerBound]
  rw [← Finset.sum_filter]
  rfl

/-- **The Tower family input of a failing shell.**

The cycle witness is the shell-closed E.2–E.4 recurrent cycle; the routing is the genuine carry
re-indexing above; the absorption is taken tight (`C_T = 1`, each next-layer mass equal to its
routed mass).  The only residual input is `hBudget`, the I.3.1 numerical budget on the total routed
carry mass. -/
def towerFamilyInputOfShell (ctx : ActualFailureContext) (cls : ℕ → TowerExitClass)
    (hBudget :
      routedClassMassOf ctx.n24CarryData cls TowerExitClass.run
          + routedClassMassOf ctx.n24CarryData cls TowerExitClass.returnPkg
          + routedClassMassOf ctx.n24CarryData cls TowerExitClass.densePack
          + routedClassMassOf ctx.n24CarryData cls TowerExitClass.cnlTail
          + routedClassMassOf ctx.n24CarryData cls TowerExitClass.other
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    TowerFamilyInput erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : ℝ) where
  cycle :=
    (towerCycleOfFailingShellClosed ctx.shell ctx.shell.hrational.choose
      ctx.shell.hrational.choose_spec).D
  routing := towerExitRoutingOfShell ctx cls
  outputBoundConstant := 1
  outputBoundConstant_nonneg := zero_le_one
  nextLayerMass :=
    routedClassMassOf ctx.n24CarryData cls TowerExitClass.run
      + routedClassMassOf ctx.n24CarryData cls TowerExitClass.returnPkg
      + routedClassMassOf ctx.n24CarryData cls TowerExitClass.densePack
      + routedClassMassOf ctx.n24CarryData cls TowerExitClass.cnlTail
  massRun := routedClassMassOf ctx.n24CarryData cls TowerExitClass.run
  massReturn := routedClassMassOf ctx.n24CarryData cls TowerExitClass.returnPkg
  massDensePack := routedClassMassOf ctx.n24CarryData cls TowerExitClass.densePack
  massCNL := routedClassMassOf ctx.n24CarryData cls TowerExitClass.cnlTail
  absorbRun := by
    rw [one_mul]
    exact le_of_eq (towerExitRoutingOfShell_routedMass ctx cls TowerExitClass.run)
  absorbReturn := by
    rw [one_mul]
    exact le_of_eq (towerExitRoutingOfShell_routedMass ctx cls TowerExitClass.returnPkg)
  absorbDensePack := by
    rw [one_mul]
    exact le_of_eq (towerExitRoutingOfShell_routedMass ctx cls TowerExitClass.densePack)
  absorbCNL := by
    rw [one_mul]
    exact le_of_eq (towerExitRoutingOfShell_routedMass ctx cls TowerExitClass.cnlTail)
  massSum := le_refl _
  hSmall := by
    rw [one_mul,
      show (towerExitRoutingOfShell ctx cls).smallError
          = routedClassMassOf ctx.n24CarryData cls TowerExitClass.other from
        towerExitRoutingOfShell_routedMass ctx cls TowerExitClass.other]
    linarith [hBudget]

/-- **The Tower separated local leaf package of a failing shell (manuscript shape).**

`TowerClosedL31I31PackageInputData` at the pinned constants and the shell scale, assembled through
`TowerFamilyInput.toClosedPackage` from the of-shell tower family. -/
def towerLeafOfShell (ctx : ActualFailureContext) (cls : ℕ → TowerExitClass)
    (hBudget :
      routedClassMassOf ctx.n24CarryData cls TowerExitClass.run
          + routedClassMassOf ctx.n24CarryData cls TowerExitClass.returnPkg
          + routedClassMassOf ctx.n24CarryData cls TowerExitClass.densePack
          + routedClassMassOf ctx.n24CarryData cls TowerExitClass.cnlTail
          + routedClassMassOf ctx.n24CarryData cls TowerExitClass.other
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    TowerClosedL31I31PackageInputData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : ℝ) :=
  (towerFamilyInputOfShell ctx cls hBudget).toClosedPackage

/-- **The total charged tower-exit mass of the of-shell family meets the I.3.1 budget.**  Sanity
bound: the genuine tower charged mass — the high-excess carry mass routed by the L.3.1 classifier —
fits the tower slot `cStar·ξ·X/6`. -/
theorem towerLeafOfShell_tower_bound (ctx : ActualFailureContext) (cls : ℕ → TowerExitClass)
    (hBudget :
      routedClassMassOf ctx.n24CarryData cls TowerExitClass.run
          + routedClassMassOf ctx.n24CarryData cls TowerExitClass.returnPkg
          + routedClassMassOf ctx.n24CarryData cls TowerExitClass.densePack
          + routedClassMassOf ctx.n24CarryData cls TowerExitClass.cnlTail
          + routedClassMassOf ctx.n24CarryData cls TowerExitClass.other
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    (∑ b ∈ (towerExitRoutingOfShell ctx cls).entryExitSet,
        ((towerExitRoutingOfShell ctx cls).weight b : ℝ))
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  (towerFamilyInputOfShell ctx cls hBudget).tower_bound

/-- **Per-element charge domination of a routed tower-exit mass** (the generic per-output charge
mechanism, `routedClassMassOf_le_countMultiplier`, of which `charge_perOutput_by_matching` is the
matching-map form): if every high-excess start routed to the L.3.1 destination `c` charges at most
`multiplier` and the class fibre has at most `count` elements, the routed tower-exit mass is
`≤ count·multiplier`.  This is how the I.3.1 budget hypothesis is discharged from the J/K analytic
per-element data (Lemma L.2.4 disjointness `Σ_{Θ=O} wt ≤ C_Q·wt(O)`). -/
theorem towerRoutedClassMass_le_countMultiplier (ctx : ActualFailureContext)
    (cls : ℕ → TowerExitClass) (c : TowerExitClass) {multiplier count : ℝ}
    (hpoint : ∀ k ∈ routedFibre ctx.n24CarryData cls c,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        ≤ multiplier)
    (hmult_nonneg : 0 ≤ multiplier)
    (hcard : ((routedFibre ctx.n24CarryData cls c).card : ℝ) ≤ count) :
    routedClassMassOf ctx.n24CarryData cls c ≤ count * multiplier :=
  routedClassMassOf_le_countMultiplier ctx.n24CarryData cls c hpoint hmult_nonneg hcard

end

end Erdos260
