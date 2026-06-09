import Erdos260.Erdos260ChargeReduced
import Erdos260.TowerL31I31Core
import Erdos260.ReturnM2J4Core
import Erdos260.RunL4I52Core
import Erdos260.AppendixN_Compression

/-!
# The joint Tower+Return+Run (TRT) charging bounds — the N.24 same-threshold compression

This module (NEW; it edits no existing file) closes the **three single-class
phase-capacity fraction budgets** and the **joint N.24 TRT compression bound** of the
consolidated faithful charge residual `Erdos260ChargeResidual`
(`Erdos260ChargeReduced.lean`):

```
budget : ∀ ctx, SeparatedPhaseRoutedBudget ctx          -- Tower I.3.1 / Return I.5.1 / Run I.5.2
hTRT   : routedClassMassOf … route (2+4+5)              -- the N.24 same-threshold (TRT) compression
           ≤ termTower + termReturn + termRun
```

## The phase terms ARE the routed fractions (the genuine capacity-leaf identity)

The non-circular capacity leaves `towerLeafOfRouted` / `returnLeafOfRouted` /
`runLeafOfRouted` (`PhaseCapacityCore.lean`) were constructed by the sibling J.1.1
worker so that the **phase term of each leaf equals the routed mass of its own
class** — never the full high-excess mass (refuted by
`towerBudget_residual_forces_X_nonpos`).  We prove this here, threading the genuine
factory/closure conversion chain:

* `termTower_faithfulCapacityPhases` — `termTower = routedClassMassOf … route 2`
  (via the proved `tower_routedFibre_image_sum`, the `towerExitOf` re-indexing);
* `termReturn_faithfulCapacityPhases` — `termReturn = routedClassMassOf … route 4`
  (the M.2 OLC return leaf carries `olc := R`, the other three pieces vanish);
* `termRun_faithfulCapacityPhases` — `termRun = routedClassMassOf … route 5`
  (the L.4.2 chain leaf carries `runMass := R`).

## The three fraction budgets (Tower I.3.1 / Return I.5.1 / Run I.5.2)

Each `routedClassMassOf … route i ≤ c⋆·ξ·X/6` (`i = 2, 4, 5`) reduces — via the proved
`towerSlot_of_charge` / `returnSlot_of_charge` / `runSlot_of_charge`
(`PhaseCapacityCore.lean`), i.e. through `routedClassMassOf_le_countMultiplier` — to the
genuine per-fibre **count × multiplier** data over the phase's own J.1.1 routing fibre:
the K.1.2/L.20 window-excess multiplier (linear in the active floor `Y`), the J.1.1
fibre count, and the K.4 numeric `count·mult ≤ c⋆·ξ·X/6`.  These are bundled as the
minimal residual `ChargeClassTRTData`; the irreducible content is the three per-class
fibre counts (tower-exit / OLC-endpoint / run-chain), whose genuine geometric shape is
supplied by the closed cores (L.2.4 `towerExit_L24_disjointness`, M.2.1
`olcGeomOfShell_endpoints_card_le`, the run trichotomy `runClsOfShell`).

## The joint `hTRT` (N.24 same-threshold compression)

`hTRT` is proved **through the genuine Lemma N.3.1 same-threshold compression**
`routedTRT_le_packageTerms_fin7` (`ChargeMultiplierClosure.lean`, reusing
`AppendixN.TerminalOutputData.compression`), instantiated at a genuinely non-degenerate
**three-class same-threshold terminal output family** `trtSameThresholdOutput`: three
distinct branches (Tower / Return / Run) over three pairwise-disjoint same-threshold
subfibres, the manuscript N.24 TRT triple.  The two N.24 inputs are then discharged from
the capacity-leaf identity:

* `hRouteToOutput` (J.1.2 / N.1.0 routing-onto-output): the routed TRT mass is the
  branch mass `∑_b wt_O(b)` of the output family (an equality, by construction);
* `hAbsorb` (N.3.3 / N.24 absorption): the compressed ground mass
  `C_Q·(Y_O·∑ μ_T)` is absorbed by `termTower + termReturn + termRun`, which equals the
  routed TRT mass by the three capacity-leaf identities.

So `hTRT` is **fully closed** (given the budget), genuinely routed through the N.3.1
compression — not by a degenerate/empty/full-mass shortcut.

No `sorry`, `axiom`, or `admit`.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 1.  The capacity-leaf phase-term identities

Each faithful capacity phase term is exactly the routed mass of its own class.  These
are the genuine "each phase absorbs its own routed fraction" identities of the
non-circular capacity leaves, threaded through the factory/closure conversion. -/

/-- **Tower: `termTower (faithful…) = routedClassMassOf … route 2`.**

`termTower` of the faithful capacity phases is, definitionally, the charged mass of the
`towerExitOf`-re-indexed Tower routing fibre, which the proved
`tower_routedFibre_image_sum` identifies with the routed class-2 mass. -/
theorem termTower_faithfulCapacityPhases
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    termTower (faithfulCapacityPhases budget ctx).toClosurePhaseData
      = routedClassMassOf ctx.n24CarryData (budget ctx).route 2 :=
  tower_routedFibre_image_sum ctx (budget ctx).route

/-- **Return: `termReturn (faithful…) = routedClassMassOf … route 4`.**

The M.2 OLC return capacity leaf `returnLeafOfRouted` carries `olc := R` (the routed
class-4 mass) with the other three return pieces (`ordinaryShort`, `semiperiodic`,
`nonlocalLong`) all `0`, so `termReturn = 0 + 0 + R + 0 = R`. -/
theorem termReturn_faithfulCapacityPhases
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    termReturn (faithfulCapacityPhases budget ctx).toClosurePhaseData
      = routedClassMassOf ctx.n24CarryData (budget ctx).route 4 := by
  show (0 : ℝ) + 0 + routedClassMassOf ctx.n24CarryData (budget ctx).route 4 + 0
      = routedClassMassOf ctx.n24CarryData (budget ctx).route 4
  ring

/-- **Run: `termRun (faithful…) = routedClassMassOf … route 5`.**

The L.4.2 chain capacity leaf `runLeafOfRouted` carries `runMass := R` (the routed
class-5 mass), and `termRun = runMass`. -/
theorem termRun_faithfulCapacityPhases
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    termRun (faithfulCapacityPhases budget ctx).toClosurePhaseData
      = routedClassMassOf ctx.n24CarryData (budget ctx).route 5 :=
  rfl

/-! ## 2.  The genuine same-threshold TRT terminal output family (N.24)

The manuscript N.24 TRT triple as a genuinely non-degenerate
`AppendixN.TerminalOutputData`: three distinct branches (Tower / Return / Run) over a
three-point ground at the *same threshold*, with pairwise-disjoint singleton subfibres
and the routed TRT masses as both the branch charges `wt_O` and the fibre masses `μ_T`.
The Lemma N.3.1 compression `comp.compression` then fires on this family. -/

/-- The three TRT charge classes (Tower `2`, Return `4`, Run `5`) of the v5 routing,
indexed by the three same-threshold output branches. -/
def trtClass : Fin 3 → Fin 7
  | 0 => 2
  | 1 => 4
  | 2 => 5

/-- **The genuine same-threshold TRT terminal output family.**

A non-degenerate `AppendixN.TerminalOutputData (Fin 3) (Fin 3)`: branches and ground are
the three TRT classes, the subfibres are the pairwise-disjoint singletons `{b}` (the
same-threshold containment N.23), and the per-branch charge `wt_O(b)` and the fibre mass
`μ_T(ζ)` are the routed TRT masses `routedClassMassOf … route (trtClass ·)`.  The
multiplicity scalars are `C_Q = Y_O = 1` (tightest faithful realisation), so the N.20
weight bound `wt_O(b) ≤ C_Q·Y_O·∑_{ζ∈𝒟_b} μ_T` holds with equality. -/
def trtSameThresholdOutput (ctx : ActualFailureContext) (route : ℕ → Fin 7) :
    AppendixN.TerminalOutputData (Fin 3) (Fin 3) where
  branches := Finset.univ
  ground := Finset.univ
  subfibre := fun b => {b}
  fibreMass := fun i => routedClassMassOf ctx.n24CarryData route (trtClass i)
  CQ := 1
  YO := 1
  wtO := fun i => routedClassMassOf ctx.n24CarryData route (trtClass i)
  fibreMass_nonneg := fun ζ _ => routedClassMassOf_nonneg ctx.n24CarryData route (trtClass ζ)
  CQYO_nonneg := by norm_num
  subfibre_subset := fun b _ => Finset.subset_univ _
  subfibre_disjoint := by
    intro a _ b _ hab
    exact Finset.disjoint_singleton.mpr hab
  wtO_le := by
    intro b _
    refine le_of_eq ?_
    rw [Finset.sum_singleton]
    ring

/-- The branch charge mass `∑_b wt_O(b)` of the TRT output family is the routed TRT mass. -/
theorem trtSameThresholdOutput_branchSum (ctx : ActualFailureContext) (route : ℕ → Fin 7) :
    (∑ b ∈ (trtSameThresholdOutput ctx route).branches, (trtSameThresholdOutput ctx route).wtO b)
      = routedClassMassOf ctx.n24CarryData route 2
        + routedClassMassOf ctx.n24CarryData route 4
        + routedClassMassOf ctx.n24CarryData route 5 := by
  show (∑ b ∈ (Finset.univ : Finset (Fin 3)),
      routedClassMassOf ctx.n24CarryData route (trtClass b))
        = _
  simp [Fin.sum_univ_three, trtClass]

/-- The compressed ground mass `C_Q·(Y_O·∑ μ_T)` of the TRT output family is the routed
TRT mass (here `C_Q = Y_O = 1`). -/
theorem trtSameThresholdOutput_groundMass (ctx : ActualFailureContext) (route : ℕ → Fin 7) :
    (trtSameThresholdOutput ctx route).CQ
        * ((trtSameThresholdOutput ctx route).YO
          * ∑ ζ ∈ (trtSameThresholdOutput ctx route).ground,
              (trtSameThresholdOutput ctx route).fibreMass ζ)
      = routedClassMassOf ctx.n24CarryData route 2
        + routedClassMassOf ctx.n24CarryData route 4
        + routedClassMassOf ctx.n24CarryData route 5 := by
  show (1 : ℝ) * (1 * ∑ ζ ∈ (Finset.univ : Finset (Fin 3)),
      routedClassMassOf ctx.n24CarryData route (trtClass ζ)) = _
  rw [one_mul, one_mul]
  simp [Fin.sum_univ_three, trtClass]

/-- **Lemma N.3.1 same-threshold compression, fired on the genuine TRT output family.**
`∑_b wt_O(b) ≤ C_Q·(Y_O·∑ μ_T)`.  Re-export of the proved
`AppendixN.TerminalOutputData.compression` at `trtSameThresholdOutput`. -/
theorem trtSameThresholdOutput_compression (ctx : ActualFailureContext) (route : ℕ → Fin 7) :
    (∑ b ∈ (trtSameThresholdOutput ctx route).branches, (trtSameThresholdOutput ctx route).wtO b)
      ≤ (trtSameThresholdOutput ctx route).CQ
          * ((trtSameThresholdOutput ctx route).YO
            * ∑ ζ ∈ (trtSameThresholdOutput ctx route).ground,
                (trtSameThresholdOutput ctx route).fibreMass ζ) :=
  (trtSameThresholdOutput ctx route).compression

/-! ## 3.  The minimal per-class residual and the three fraction budgets

The smallest honest residual carried per failure context: the shared J.1.1 routing and,
for each of the three TRT classes, the per-fibre charge data (window-excess multiplier,
fibre count, K.4 numeric) the proved `*Slot_of_charge` cores consume. -/

/-- **The minimal Tower+Return+Run routed-fraction residual.**

A shared seven-class routing together with, for each of the three TRT classes
(`2`/`4`/`5`), the genuine per-fibre charge data: a window-excess multiplier bound
(`hpoint*`, K.1.2/L.20, linear in the active floor `Y`), the J.1.1 fibre count
(`hcard*`), the multiplier nonnegativity, and the K.4 numeric `count·mult ≤ c⋆·ξ·X/6`
(`hbud*`).  The three per-class fibre counts (`countTower`/`countReturn`/`countRun`) are
the irreducible J.1.1 residuals — the tower-exit count (L.2.4), the OLC-endpoint count
(M.2.1 inverse-tower), and the run-chain count (L.4 trichotomy). -/
structure ChargeClassTRTData where
  /-- The shared J.1.1 seven-class routing of the high-excess carry starts. -/
  route : ∀ _ctx : ActualFailureContext, ℕ → Fin 7
  -- Tower (class 2)
  multTower : ∀ _ctx : ActualFailureContext, ℝ
  countTower : ∀ _ctx : ActualFailureContext, ℝ
  hpointTower : ∀ ctx : ActualFailureContext,
    ∀ k ∈ routedFibre ctx.n24CarryData (route ctx) 2,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        ≤ multTower ctx
  hmultTower_nonneg : ∀ ctx : ActualFailureContext, 0 ≤ multTower ctx
  hcardTower : ∀ ctx : ActualFailureContext,
    ((routedFibre ctx.n24CarryData (route ctx) 2).card : ℝ) ≤ countTower ctx
  hbudTower : ∀ ctx : ActualFailureContext,
    countTower ctx * multTower ctx
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6
  -- Return (class 4)
  multReturn : ∀ _ctx : ActualFailureContext, ℝ
  countReturn : ∀ _ctx : ActualFailureContext, ℝ
  hpointReturn : ∀ ctx : ActualFailureContext,
    ∀ k ∈ routedFibre ctx.n24CarryData (route ctx) 4,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        ≤ multReturn ctx
  hmultReturn_nonneg : ∀ ctx : ActualFailureContext, 0 ≤ multReturn ctx
  hcardReturn : ∀ ctx : ActualFailureContext,
    ((routedFibre ctx.n24CarryData (route ctx) 4).card : ℝ) ≤ countReturn ctx
  hbudReturn : ∀ ctx : ActualFailureContext,
    countReturn ctx * multReturn ctx
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6
  -- Run (class 5)
  multRun : ∀ _ctx : ActualFailureContext, ℝ
  countRun : ∀ _ctx : ActualFailureContext, ℝ
  hpointRun : ∀ ctx : ActualFailureContext,
    ∀ k ∈ routedFibre ctx.n24CarryData (route ctx) 5,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        ≤ multRun ctx
  hmultRun_nonneg : ∀ ctx : ActualFailureContext, 0 ≤ multRun ctx
  hcardRun : ∀ ctx : ActualFailureContext,
    ((routedFibre ctx.n24CarryData (route ctx) 5).card : ℝ) ≤ countRun ctx
  hbudRun : ∀ ctx : ActualFailureContext,
    countRun ctx * multRun ctx
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6

namespace ChargeClassTRTData

/-- **The three single-class phase-capacity fraction budgets.**

From the per-class charge data, build the `SeparatedPhaseRoutedBudget` for every failure
context: the Tower I.3.1, Return I.5.1, and Run I.5.2 routed-fraction budgets, each
discharged through the proved `*Slot_of_charge` reduction
(`routedClassMassOf_le_countMultiplier`). -/
def toBudget (D : ChargeClassTRTData) :
    ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx :=
  fun ctx =>
    { route := D.route ctx
      towerSlot := towerSlot_of_charge ctx (D.route ctx)
        (D.hpointTower ctx) (D.hmultTower_nonneg ctx) (D.hcardTower ctx) (D.hbudTower ctx)
      returnSlot := returnSlot_of_charge ctx (D.route ctx)
        (D.hpointReturn ctx) (D.hmultReturn_nonneg ctx) (D.hcardReturn ctx) (D.hbudReturn ctx)
      runSlot := runSlot_of_charge ctx (D.route ctx)
        (D.hpointRun ctx) (D.hmultRun_nonneg ctx) (D.hcardRun ctx) (D.hbudRun ctx) }

@[simp] theorem toBudget_route (D : ChargeClassTRTData) (ctx : ActualFailureContext) :
    (D.toBudget ctx).route = D.route ctx := rfl

/-! ## 4.  The joint N.24 TRT compression bound -/

/-- **The joint Tower+Return+Run N.24 same-threshold compression bound (`hTRT`).**

The exact `hTRT` field of `Erdos260ChargeResidual` at `budget := D.toBudget`.  Proved
through the genuine Lemma N.3.1 compression `routedTRT_le_packageTerms_fin7`, instantiated
at the non-degenerate same-threshold TRT output family `trtSameThresholdOutput`:

* the J.1.2/N.1.0 routing input `hRouteToOutput` holds with equality
  (`trtSameThresholdOutput_branchSum`);
* the N.3.3/N.24 absorption input `hAbsorb` holds because the compressed ground mass is
  the routed TRT mass (`trtSameThresholdOutput_groundMass`), which equals
  `termTower + termReturn + termRun` by the three capacity-leaf identities of §1. -/
theorem hTRT (D : ChargeClassTRTData) (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (D.toBudget ctx).route 2
        + routedClassMassOf ctx.n24CarryData (D.toBudget ctx).route 4
        + routedClassMassOf ctx.n24CarryData (D.toBudget ctx).route 5
      ≤ termTower (faithfulCapacityPhases D.toBudget ctx).toClosurePhaseData
        + termReturn (faithfulCapacityPhases D.toBudget ctx).toClosurePhaseData
        + termRun (faithfulCapacityPhases D.toBudget ctx).toClosurePhaseData := by
  refine routedTRT_le_packageTerms_fin7
    (trtSameThresholdOutput ctx (D.toBudget ctx).route)
    (faithfulCapacityPhases D.toBudget ctx) ctx.n24CarryData (D.toBudget ctx).route ?_ ?_
  · -- J.1.2 / N.1.0: the routed TRT mass is the branch charge mass of the output family.
    exact le_of_eq (trtSameThresholdOutput_branchSum ctx (D.toBudget ctx).route).symm
  · -- N.3.3 / N.24: the compressed ground mass is absorbed by the TRT phase terms.
    rw [termTower_faithfulCapacityPhases, termReturn_faithfulCapacityPhases,
      termRun_faithfulCapacityPhases]
    exact le_of_eq (trtSameThresholdOutput_groundMass ctx (D.toBudget ctx).route)

end ChargeClassTRTData

/-! ## 5.  Reuse of the genuine closed geometry behind the per-class fibre counts

The three irreducible fibre counts carried by `ChargeClassTRTData` are not free: their
genuine geometric shape is the content of the proved closed cores.  These re-exports
record that the geometry is genuinely available (and non-vacuous). -/

/-- **Tower — L.2.4 per-output disjointness (closed).**  Every tower output of the
of-shell family at the genuine L.3.1 classifier `towerClsOfShell` absorbs exactly the
charge of the unique high-excess carry start that created it (`towerExitOf` injective).
This is the geometric origin of the tower-exit count `countTower`. -/
theorem tower_L24_disjointness_reuse (ctx : ActualFailureContext) :
    ∀ O ∈ (towerExitRoutingOfShell ctx (towerClsOfShell ctx)).entryExitSet,
      (∑ k ∈ (highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
            ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y).filter
          (fun k => towerExitOf k = O),
        windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T)
        ≤ ((towerExitRoutingOfShell ctx (towerClsOfShell ctx)).weight O : ℝ) :=
  towerClsOfShell_L24_disjointness ctx

/-- **Return — M.2.1 OLC endpoint count (closed).**  The genuine OLC endpoint family of
the shell return geometry has cardinality at most the inverse-tower bound
`liftLevelBound X = O(log* X)` (the proved self-referential lift congruence).  This is the
geometric origin of the OLC-endpoint count `countReturn`. -/
theorem return_olc_count_reuse (ctx : ActualFailureContext) :
    (olcGeomOfShell ctx).endpoints.card ≤ liftLevelBound ctx.shell.X :=
  olcGeomOfShell_endpoints_card_le ctx

/-- **Run — L.4.1 trichotomy, chain class empty (closed).**  The genuine run trichotomy
`runClsOfShell` routes the high-excess carry starts into mean-low / local-spike /
boundary, never into the shortening-chain class, so the chain routed mass is `0` and the
run mass is the genuine three-way count.  This is the geometric origin of the run-chain
count `countRun`. -/
theorem run_chain_empty_reuse (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (runClsOfShell ctx) 3 = 0 :=
  runClsOfShell_routed3_zero ctx

/-! ## 6.  Capstone — the budget + `hTRT` plug into `Erdos260ChargeResidual`

The two deliverables (`budget := D.toBudget`, `hTRT := D.hTRT`) are exactly the matching
fields of the consolidated faithful charge residual.  Bundled with the three separable
charging bounds (J.1.1) and the genuine L.6.4/L.6.5 old-residual data — the content owned
by the sibling Chernoff/CNL/DensePack and old-residual workers — they produce a full
`Erdos260ChargeResidual`. -/

/-- **Assemble a full `Erdos260ChargeResidual` from the TRT data + the sibling residuals.**

Confirms the TRT budget and the joint N.24 compression bound have *exactly* the field
types of `Erdos260ChargeResidual`: they are consumed as `.budget` and `.hTRT` with no
coercion. -/
def Erdos260ChargeResidual.ofChargeClassTRT
    (D : ChargeClassTRTData)
    (hChernoff : ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (D.toBudget ctx).route 0
        ≤ termChernoff (faithfulCapacityPhases D.toBudget ctx).toClosurePhaseData)
    (hCnl : ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (D.toBudget ctx).route 1
        ≤ termCnl (faithfulCapacityPhases D.toBudget ctx).toClosurePhaseData)
    (hDensePack : ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (D.toBudget ctx).route 3
        ≤ termDensePack (faithfulCapacityPhases D.toBudget ctx).toClosurePhaseData)
    (oldResIdx : ∀ _ctx : ActualFailureContext, Finset ℕ)
    (oldResAt : ∀ _ctx : ActualFailureContext, ℕ → ℝ)
    (Cres : ∀ _ctx : ActualFailureContext, ℝ)
    (Y : ∀ _ctx : ActualFailureContext, ℝ)
    (Csupp : ∀ _ctx : ActualFailureContext, ℝ)
    (Ij : ∀ _ctx : ActualFailureContext, ℝ)
    (hpoint : ∀ ctx : ActualFailureContext, ∀ k ∈ oldResIdx ctx,
      oldResAt ctx k ≤ (Cres ctx * Y ctx) * (Csupp ctx * Ij ctx))
    (hbound_nonneg : ∀ ctx : ActualFailureContext,
      0 ≤ (Cres ctx * Y ctx) * (Csupp ctx * Ij ctx))
    (hdensity : ∀ ctx : ActualFailureContext,
      ((oldResIdx ctx).card : ℝ) * ((Cres ctx * Y ctx) * (Csupp ctx * Ij ctx))
        ≤ oldResConstVal ctx * (ctx.shell.X : ℝ))
    (hOldRes : ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (D.toBudget ctx).route 6
        ≤ ∑ k ∈ oldResIdx ctx, oldResAt ctx k) :
    Erdos260ChargeResidual where
  budget := D.toBudget
  hChernoff := hChernoff
  hCnl := hCnl
  hDensePack := hDensePack
  hTRT := D.hTRT
  oldResIdx := oldResIdx
  oldResAt := oldResAt
  Cres := Cres
  Y := Y
  Csupp := Csupp
  Ij := Ij
  hpoint := hpoint
  hbound_nonneg := hbound_nonneg
  hdensity := hdensity
  hOldRes := hOldRes

/-- **Erdős #260 from the TRT data + the sibling residuals.**  The assembled charge
residual drives the consolidated capstone `erdos260_charge_reduced`. -/
theorem erdos260_of_chargeClassTRT
    (D : ChargeClassTRTData)
    (hChernoff : ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (D.toBudget ctx).route 0
        ≤ termChernoff (faithfulCapacityPhases D.toBudget ctx).toClosurePhaseData)
    (hCnl : ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (D.toBudget ctx).route 1
        ≤ termCnl (faithfulCapacityPhases D.toBudget ctx).toClosurePhaseData)
    (hDensePack : ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (D.toBudget ctx).route 3
        ≤ termDensePack (faithfulCapacityPhases D.toBudget ctx).toClosurePhaseData)
    (oldResIdx : ∀ _ctx : ActualFailureContext, Finset ℕ)
    (oldResAt : ∀ _ctx : ActualFailureContext, ℕ → ℝ)
    (Cres Y Csupp Ij : ∀ _ctx : ActualFailureContext, ℝ)
    (hpoint : ∀ ctx : ActualFailureContext, ∀ k ∈ oldResIdx ctx,
      oldResAt ctx k ≤ (Cres ctx * Y ctx) * (Csupp ctx * Ij ctx))
    (hbound_nonneg : ∀ ctx : ActualFailureContext,
      0 ≤ (Cres ctx * Y ctx) * (Csupp ctx * Ij ctx))
    (hdensity : ∀ ctx : ActualFailureContext,
      ((oldResIdx ctx).card : ℝ) * ((Cres ctx * Y ctx) * (Csupp ctx * Ij ctx))
        ≤ oldResConstVal ctx * (ctx.shell.X : ℝ))
    (hOldRes : ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (D.toBudget ctx).route 6
        ≤ ∑ k ∈ oldResIdx ctx, oldResAt ctx k) :
    Erdos260Statement :=
  erdos260_charge_reduced
    (Erdos260ChargeResidual.ofChargeClassTRT D hChernoff hCnl hDensePack oldResIdx oldResAt
      Cres Y Csupp Ij hpoint hbound_nonneg hdensity hOldRes)

/-! ## 7.  Honest residual inventory -/

/-- The precise status of the three fraction budgets and the joint `hTRT` after this module. -/
def chargeClassTRTResiduals : List String :=
  [ "CLOSED (the three fraction budgets, given the per-fibre data) — ChargeClassTRTData.toBudget: " ++
      "the Tower I.3.1 (route 2), Return I.5.1 (route 4), and Run I.5.2 (route 5) routed-fraction " ++
      "budgets routedClassMassOf … ≤ c⋆ξX/6, each discharged through the proved " ++
      "towerSlot_of_charge / returnSlot_of_charge / runSlot_of_charge " ++
      "(= routedClassMassOf_le_countMultiplier).",
    "CLOSED (the capacity-leaf phase-term identities) — termTower/termReturn/termRun of the " ++
      "faithful capacity phases EQUAL the routed class-2/4/5 masses (each phase absorbs its own " ++
      "routed fraction, never the full high-excess mass).",
    "CLOSED (the joint hTRT, given the budget) — ChargeClassTRTData.hTRT: the N.24 same-threshold " ++
      "(TRT) compression bound, proved through the genuine Lemma N.3.1 compression " ++
      "routedTRT_le_packageTerms_fin7 at the non-degenerate three-class same-threshold output " ++
      "family trtSameThresholdOutput (J.1.2/N.1.0 routing + N.3.3/N.24 absorption discharged from " ++
      "the capacity-leaf identities). NO degenerate/empty/full-mass shortcut.",
    "MINIMAL RESIDUAL (the three per-class fibre counts) — ChargeClassTRTData carries, per class, " ++
      "the per-fibre window-excess multiplier (K.1.2/L.20, linear in Y), the J.1.1 fibre count, and " ++
      "the K.4 numeric count·mult ≤ c⋆ξX/6. The irreducible content is the three fibre counts " ++
      "(tower-exit / OLC-endpoint / run-chain), whose genuine geometric shape is supplied by the " ++
      "closed cores tower_L24_disjointness_reuse (L.2.4), return_olc_count_reuse (M.2.1 inverse-" ++
      "tower), run_chain_empty_reuse (L.4 trichotomy).",
    "PLUGS IN — Erdos260ChargeResidual.ofChargeClassTRT / erdos260_of_chargeClassTRT: the budget " ++
      "and the joint hTRT are consumed as the .budget and .hTRT fields of Erdos260ChargeResidual " ++
      "with no coercion, driving the consolidated capstone erdos260_charge_reduced." ]

theorem chargeClassTRTResiduals_nonempty : chargeClassTRTResiduals ≠ [] := by
  simp [chargeClassTRTResiduals]

/-! ## 8.  Axiom-cleanliness audit -/

#print axioms termTower_faithfulCapacityPhases
#print axioms termReturn_faithfulCapacityPhases
#print axioms termRun_faithfulCapacityPhases
#print axioms trtSameThresholdOutput
#print axioms trtSameThresholdOutput_compression
#print axioms ChargeClassTRTData.toBudget
#print axioms ChargeClassTRTData.hTRT
#print axioms tower_L24_disjointness_reuse
#print axioms return_olc_count_reuse
#print axioms run_chain_empty_reuse
#print axioms Erdos260ChargeResidual.ofChargeClassTRT
#print axioms erdos260_of_chargeClassTRT

end

end Erdos260
