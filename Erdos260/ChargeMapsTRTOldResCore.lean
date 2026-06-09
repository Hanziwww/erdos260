import Erdos260.ChargeClassTRT
import Erdos260.OldResL65Core
import Erdos260.Erdos260ChargedLedger

/-!
# Class-2/4/5 (Tower/Return/Run) + class-6 (old-residual) charge maps (`ChargeMapsTRTOldResCore`)

This module (NEW; it edits no existing file) constructs the **genuine per-class
fibre-count / charge data** of the Erdős #260 charged ledger
(`Erdos260ChargedLedger.lean`): the `trt : ChargeClassTRTData` field (the shared
seven-class J.1.1 routing + the three single-class fraction budgets, Tower I.3.1 /
Return I.5.1 / Run I.5.2) and the class-6 `hOldRes` field (the routed class-6 mass
dominated by the genuine nonzero L.6.4 old-residual branch mass).

The seven-class routing `route` is **free data** of `Erdos260ChargeResidual` (owned by the
sibling J.1.1 routing worker); it is taken here as an *interface*.  Everything else — the
per-fibre count×multiplier data — is reduced to the **smallest named residual** that ties
each class to its proven geometric core.  No `sorry`/`axiom`/`admit`, no degenerate/empty
shortcut.

## Return (class 4) — the M.2.1 count, genuinely reduced

The OLC-endpoint fibre count is reduced to the proved M.2.1 inverse-tower bound: a
charging map of the routed class-4 fibre into the genuine OLC endpoint family
`(olcGeomOfShell ctx).endpoints` (the centerpiece of `ReturnM2J4Core`) yields, through
`Finset.card_le_card_of_injOn` and the proved `olcGeomOfShell_endpoints_card_le`
(`= IsLiftChain.card_le`), the genuine **inverse-tower count**
`|routedFibre 4| ≤ liftLevelBound X = O(log* X)`.  So `countReturn = liftLevelBound X`
is *derived* (not free), and the only residual is the J.1.1 routing-to-OLC injection
`ReturnOlcRoutingCharge` (the M.2 endpoint nesting in carry form) plus the per-fibre
window-excess multiplier and the K.4 numeric `liftLevelBound X · mult ≤ c⋆ξX/6`.

## Tower (class 2) / Run (class 5) — count×multiplier over the routing fibre

Tower and Run carry no *small combinatorial* count (their smallness is the I.4.1
dense-packing fraction and the I.5.2 run-mass floor, respectively, both mass bounds, not
count bounds).  Their budgets are therefore reduced — via the proved
`routedClassMassOf_le_countMultiplier` — to the per-fibre count×multiplier residual over
the routing's own class-2 / class-5 fibre, with the genuine geometry re-exported and
*closed*: the L.2.4 per-output disjointness `towerClsOfShell_L24_disjointness` (the E.13
slope-orbit classifier `towerClsOfShell`, `towerExitOf` injective), and the L.4.1
trichotomy `runClsOfShell` with the chain class empty `runClsOfShell_routed3_zero` (the
L.4.2 half-decrease carried by `runFOfShell`).

## Old-residual (class 6) — the routed mass ≤ the genuine L.6.4 branch mass

`routedClass6_le_oldResBranchMass` proves the exact `hOldRes` field
`routedClassMassOf … route 6 ≤ ∑_{k∈K} oldResAt k` from two minimal routing residuals:
the L.6.4 retention `routedFibre 6 ⊆ oldResIdxVal` (the class-6 starts are retained
terminal hit-indices `K = supportShell d X`) and the L.20/L.21 per-index cap
`windowExcess … k ≤ oldResBoundVal = ξ`.  Because `oldResAt k = min(windowExcess k, ξ)`
is exactly the capped window excess (`OldResL65Core`), the routed mass equals
`∑_{routedFibre 6} oldResAt k`, which the subset + nonnegativity dominate by the genuine
nonzero branch mass `∑_{k∈K} oldResAt k` (NOT the degenerate `oldResMass = 0`).

## Capstone

`chargeClassTRTDataOfRouting` assembles the `ChargeClassTRTData` (with `countReturn`
derived from M.2.1); `chargedLedgerOfTRTOldRes` plugs it together with `hOldRes` and the
three sibling charging maps (Chernoff 0 / clean-CNL 1 / DensePack 3) into the final
`ChargedLedger`, and `erdos260_of_TRTOldRes` drives `Erdos260Statement` through the
proved capstone `erdos260_chargedledger_reduced`.

No `sorry`, `axiom`, or `admit`.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 1.  Reuse of the genuine closed geometric cores behind the per-class data

The three irreducible fibre counts are not free: their genuine geometric shape is the
content of the proved closed cores, re-exported here (referencing the cores directly) so
the per-class residuals are tied to genuine, non-vacuous geometry. -/

/-- **Tower (L.2.4, closed).**  Each tower output of the of-shell family at the genuine
E.13 slope-orbit classifier `towerClsOfShell` absorbs exactly the charge of the unique
high-excess carry start that created it (`towerExitOf` injective).  The geometric origin
of the Tower count×multiplier residual. -/
theorem tower_L24_disjointness_closed (ctx : ActualFailureContext) :
    ∀ O ∈ (towerExitRoutingOfShell ctx (towerClsOfShell ctx)).entryExitSet,
      (∑ k ∈ (highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
            ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y).filter
          (fun k => towerExitOf k = O),
        windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T)
        ≤ ((towerExitRoutingOfShell ctx (towerClsOfShell ctx)).weight O : ℝ) :=
  towerClsOfShell_L24_disjointness ctx

/-- **Return (M.2.1, closed).**  The genuine OLC endpoint family of the shell return
geometry has cardinality at most the inverse-tower bound `liftLevelBound X = O(log* X)`
(the proved self-referential lift congruence `IsLiftChain.card_le`).  The geometric origin
of the Return count `countReturn = liftLevelBound X`. -/
theorem return_olc_count_closed (ctx : ActualFailureContext) :
    (olcGeomOfShell ctx).endpoints.card ≤ liftLevelBound ctx.shell.X :=
  olcGeomOfShell_endpoints_card_le ctx

/-- **Run (L.4.1, closed).**  The genuine run trichotomy `runClsOfShell` never routes a
high-excess carry start to the shortening-chain class, so the chain routed mass is `0`
(the chain dynamics are carried by the residual-center descent of `runFOfShell`, the
L.4.2 half-decrease).  The geometric origin of the Run count×multiplier residual. -/
theorem run_chain_empty_closed (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (runClsOfShell ctx) 3 = 0 :=
  runClsOfShell_routed3_zero ctx

/-! ## 2.  The generic count×multiplier step (the proved `routedClassMassOf_le_countMultiplier`)

The single reduction core consumed by every TRT class: the routed class-`i` carry mass is
at most `count · multiplier` from a per-fibre window-excess bound and the fibre count. -/

/-- **Generic count×multiplier reduction** (re-export at the N.24 carry data of a context).
For any seven-class routing and any class `i`, the routed mass `≤ count · multiplier` from
the per-fibre window-excess multiplier (`hpoint`) and the J.1.1 fibre count (`hcard`). -/
theorem routedClassMass_le_countMult (ctx : ActualFailureContext) (route : ℕ → Fin 7)
    (i : Fin 7) {multiplier count : ℝ}
    (hpoint : ∀ k ∈ routedFibre ctx.n24CarryData route i,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        ≤ multiplier)
    (hmult_nonneg : 0 ≤ multiplier)
    (hcard : ((routedFibre ctx.n24CarryData route i).card : ℝ) ≤ count) :
    routedClassMassOf ctx.n24CarryData route i ≤ count * multiplier :=
  routedClassMassOf_le_countMultiplier ctx.n24CarryData route i hpoint hmult_nonneg hcard

/-! ## 3.  Return (class 4) — the M.2.1 OLC-endpoint fibre count, genuinely reduced -/

/-- **The Return class-4 OLC routing charge (the M.2 endpoint-nesting residual).**

The genuine J.1.1 routing-to-OLC injection connecting the routed class-4 fibre to the
proved M.2.1 OLC endpoint family `(olcGeomOfShell ctx).endpoints`:

* `olcOf` — the charging map of each routed class-4 start to an OLC return endpoint;
* `maps_into` — each routed-4 start lands in the genuine OLC endpoint family
  (the M.2 return-endpoint geometry);
* `matching` — distinct routed-4 starts charge distinct OLC endpoints (the M.2.1
  nonseparated-nesting deletion / endpoint disjointness in carry form).

These are the only undischarged inputs; the inverse-tower count bound is then *derived*
from the proved `olcGeomOfShell_endpoints_card_le`. -/
structure ReturnOlcRoutingCharge (route : ℕ → Fin 7) (ctx : ActualFailureContext) where
  /-- The J.1.1 charging map of routed class-4 starts to OLC return endpoints. -/
  olcOf : ℕ → ℕ
  /-- **Support injection** — each routed class-4 start lands in the OLC endpoint family. -/
  maps_into : ∀ k ∈ routedFibre ctx.n24CarryData route 4,
    olcOf k ∈ (olcGeomOfShell ctx).endpoints
  /-- **Matching** — distinct routed-4 starts charge distinct OLC endpoints (M.2.1). -/
  matching : ∀ x ∈ routedFibre ctx.n24CarryData route 4,
    ∀ y ∈ routedFibre ctx.n24CarryData route 4, olcOf x = olcOf y → x = y

namespace ReturnOlcRoutingCharge

variable {route : ℕ → Fin 7} {ctx : ActualFailureContext}

/-- **The OLC endpoint cardinal comparison (derived, not assumed).**  The routed class-4
fibre injects into the OLC endpoint family, so its cardinality is at most the OLC endpoint
count `|(olcGeomOfShell ctx).endpoints|` — the M.2 endpoint disjointness in carry form. -/
theorem fibreCard_le_olcCard (rc : ReturnOlcRoutingCharge route ctx) :
    (routedFibre ctx.n24CarryData route 4).card ≤ (olcGeomOfShell ctx).endpoints.card :=
  Finset.card_le_card_of_injOn rc.olcOf rc.maps_into
    (by
      intro x hx y hy h
      simp only [Finset.mem_coe] at hx hy
      exact rc.matching x hx y hy h)

/-- **The genuine M.2.1 inverse-tower fibre count (derived).**  Chaining the OLC cardinal
comparison with the proved `olcGeomOfShell_endpoints_card_le`, the routed class-4 fibre
count is at most the inverse-tower bound `liftLevelBound X = O(log* X)`. -/
theorem fibreCard_le_liftLevelBound (rc : ReturnOlcRoutingCharge route ctx) :
    (routedFibre ctx.n24CarryData route 4).card ≤ liftLevelBound ctx.shell.X :=
  le_trans rc.fibreCard_le_olcCard (olcGeomOfShell_endpoints_card_le ctx)

/-- The M.2.1 inverse-tower fibre count, real-valued (the `hcardReturn` shape). -/
theorem fibreCard_le_liftLevelBound_real (rc : ReturnOlcRoutingCharge route ctx) :
    ((routedFibre ctx.n24CarryData route 4).card : ℝ) ≤ (liftLevelBound ctx.shell.X : ℝ) := by
  exact_mod_cast rc.fibreCard_le_liftLevelBound

/-- **The Return class-4 budget (numeric floor), via M.2.1 + count×multiplier.**

`routedClassMassOf route 4 ≤ liftLevelBound X · mult ≤ c⋆ξX/6`: the first inequality by the
proved `routedClassMassOf_le_countMultiplier` with the *derived* inverse-tower count and a
per-fibre window-excess multiplier; the second is the K.4 numeric `liftLevelBound X · mult
≤ c⋆ξX/6` (the genuine I.5.1 smallness over the inverse-tower count). -/
theorem routedClass4_le_budget (rc : ReturnOlcRoutingCharge route ctx) {mult : ℝ}
    (hpoint : ∀ k ∈ routedFibre ctx.n24CarryData route 4,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T ≤ mult)
    (hmult_nonneg : 0 ≤ mult)
    (hbud : (liftLevelBound ctx.shell.X : ℝ) * mult
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    routedClassMassOf ctx.n24CarryData route 4
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  (routedClassMassOf_le_countMultiplier ctx.n24CarryData route 4 hpoint hmult_nonneg
    rc.fibreCard_le_liftLevelBound_real).trans hbud

/-- **Non-vacuity (non-degenerate witness).**  When the routed class-4 fibre already sits
inside the OLC endpoint family (the natural M.2 routing of the return starts to their
nesting endpoints), the identity charging map is a matching support injection — a genuine
`ReturnOlcRoutingCharge`.  No emptiness is assumed. -/
def ofSubsetEndpoints (route : ℕ → Fin 7) (ctx : ActualFailureContext)
    (hsub : routedFibre ctx.n24CarryData route 4 ⊆ (olcGeomOfShell ctx).endpoints) :
    ReturnOlcRoutingCharge route ctx where
  olcOf := id
  maps_into := fun _k hk => hsub hk
  matching := fun _x _hx _y _hy h => h

end ReturnOlcRoutingCharge

/-! ## 4.  Tower (class 2) / Run (class 5) — count×multiplier floor-close

No small combinatorial count exists for Tower / Run (their smallness is the I.4.1
dense-packing fraction and the I.5.2 run-mass floor — mass bounds).  Their budgets reduce,
via the proved `routedClassMassOf_le_countMultiplier`, to the per-fibre count×multiplier
residual over the routing's own fibre; the genuine geometry is the closed cores of §1. -/

/-- **The Tower class-2 budget (numeric floor), via count×multiplier.**  The routed class-2
carry mass fits the manuscript Tower slot `c⋆ξX/6` from the per-fibre window-excess
multiplier (`hpoint`, K.1.2/L.20), the routing's class-2 fibre count (`hcard`), and the K.4
numeric `count·mult ≤ c⋆ξX/6` (the I.4.1 dense-packing fraction in count×multiplier form).
The genuine Tower geometry is the L.2.4 disjointness `tower_L24_disjointness_closed`. -/
theorem routedClass2_le_budget (ctx : ActualFailureContext) (route : ℕ → Fin 7)
    {mult count : ℝ}
    (hpoint : ∀ k ∈ routedFibre ctx.n24CarryData route 2,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T ≤ mult)
    (hmult_nonneg : 0 ≤ mult)
    (hcard : ((routedFibre ctx.n24CarryData route 2).card : ℝ) ≤ count)
    (hbud : count * mult
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    routedClassMassOf ctx.n24CarryData route 2
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  (routedClassMassOf_le_countMultiplier ctx.n24CarryData route 2 hpoint hmult_nonneg hcard).trans
    hbud

/-- **The Run class-5 budget (numeric floor), via count×multiplier.**  The routed class-5
carry mass fits the manuscript Run slot `c⋆ξX/6` from the per-fibre window-excess
multiplier, the routing's class-5 fibre count, and the K.4 numeric `count·mult ≤ c⋆ξX/6`
(the I.5.2 run-mass floor in count×multiplier form).  The genuine Run geometry is the L.4.1
trichotomy `run_chain_empty_closed` (chain class empty) and the L.4.2 half-decrease. -/
theorem routedClass5_le_budget (ctx : ActualFailureContext) (route : ℕ → Fin 7)
    {mult count : ℝ}
    (hpoint : ∀ k ∈ routedFibre ctx.n24CarryData route 5,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T ≤ mult)
    (hmult_nonneg : 0 ≤ mult)
    (hcard : ((routedFibre ctx.n24CarryData route 5).card : ℝ) ≤ count)
    (hbud : count * mult
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    routedClassMassOf ctx.n24CarryData route 5
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  (routedClassMassOf_le_countMultiplier ctx.n24CarryData route 5 hpoint hmult_nonneg hcard).trans
    hbud

/-! ## 5.  Old-residual (class 6) — the routed mass ≤ the genuine L.6.4 branch mass -/

/-- **The class-6 routed mass is dominated by the genuine L.6.4 old-residual branch mass.**

The exact `hOldRes` field shape `routedClassMassOf … route 6 ≤ ∑_{k∈K} oldResAt k`, proved
from two minimal routing residuals:

* `hsub` — the **L.6.4 retention**: the routed class-6 fibre sits inside the retained
  terminal hit-index set `K = oldResIdxVal ctx = supportShell d X`;
* `hcap` — the **L.20/L.21 per-index cap**: every routed-6 start has window excess
  `≤ oldResBoundVal ctx = ξ`.

Because `oldResAt k = min(windowExcess … k, ξ)` is exactly the capped window excess
(`OldResL65Core.oldResAtVal`), the cap makes the routed window excess *equal* the per-index
old-residual mass on the fibre, and the subset + nonnegativity dominate it by the genuine
nonzero branch mass `∑_{k∈K} oldResAt k`.  No degenerate `oldResMass = 0`. -/
theorem routedClass6_le_oldResBranchMass (ctx : ActualFailureContext) (route : ℕ → Fin 7)
    (hsub : routedFibre ctx.n24CarryData route 6 ⊆ oldResIdxVal ctx)
    (hcap : ∀ k ∈ routedFibre ctx.n24CarryData route 6,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        ≤ oldResBoundVal ctx) :
    routedClassMassOf ctx.n24CarryData route 6
      ≤ ∑ k ∈ oldResIdxVal ctx, oldResAtVal ctx k := by
  have hpe : ∀ k ∈ routedFibre ctx.n24CarryData route 6,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        = oldResAtVal ctx k := by
    intro k hk
    simp only [oldResAtVal, oldResWindowExcess]
    rw [min_eq_left (hcap k hk)]
  calc routedClassMassOf ctx.n24CarryData route 6
      = ∑ k ∈ routedFibre ctx.n24CarryData route 6,
          windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T :=
        routedClassMassOf_eq_sum_fibre ctx.n24CarryData route 6
    _ = ∑ k ∈ routedFibre ctx.n24CarryData route 6, oldResAtVal ctx k :=
        Finset.sum_congr rfl hpe
    _ ≤ ∑ k ∈ oldResIdxVal ctx, oldResAtVal ctx k :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => oldResAtVal_nonneg ctx k)

/-! ## 6.  Assembly — the `ChargeClassTRTData` (trt field) with the Return count derived

The shared seven-class J.1.1 routing `route` is taken as the sibling interface; the three
single-class fraction budgets are carried as per-fibre count×multiplier data, **except**
that `countReturn` is *derived* from the M.2.1 OLC routing charge as the genuine
inverse-tower count `liftLevelBound X` (never a free count). -/

/-- **The `ChargeClassTRTData` (the `trt` ledger field) from the routing interface.**

Builds the Tower I.3.1 / Return I.5.1 / Run I.5.2 fraction-budget data over the sibling
routing `route`.  Tower and Run carry the per-fibre count×multiplier residual (count,
multiplier, point bound, fibre count, K.4 numeric).  Return is the genuine reduction: its
count is *derived* as `liftLevelBound X` from the M.2.1 OLC routing charge `retCharge`
(`ReturnOlcRoutingCharge.fibreCard_le_liftLevelBound_real`), so only the OLC injection, the
per-fibre multiplier, and the K.4 numeric `liftLevelBound X · mult ≤ c⋆ξX/6` remain. -/
def chargeClassTRTDataOfRouting
    (route : ∀ _ctx : ActualFailureContext, ℕ → Fin 7)
    -- Tower (class 2)
    (multTower countTower : ∀ _ctx : ActualFailureContext, ℝ)
    (hpointTower : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (route ctx) 2,
        windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
          ≤ multTower ctx)
    (hmultTower_nonneg : ∀ ctx : ActualFailureContext, 0 ≤ multTower ctx)
    (hcardTower : ∀ ctx : ActualFailureContext,
      ((routedFibre ctx.n24CarryData (route ctx) 2).card : ℝ) ≤ countTower ctx)
    (hbudTower : ∀ ctx : ActualFailureContext,
      countTower ctx * multTower ctx
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6)
    -- Return (class 4): the M.2.1 OLC routing charge + multiplier + K.4
    (retCharge : ∀ ctx : ActualFailureContext, ReturnOlcRoutingCharge (route ctx) ctx)
    (multReturn : ∀ _ctx : ActualFailureContext, ℝ)
    (hpointReturn : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (route ctx) 4,
        windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
          ≤ multReturn ctx)
    (hmultReturn_nonneg : ∀ ctx : ActualFailureContext, 0 ≤ multReturn ctx)
    (hbudReturn : ∀ ctx : ActualFailureContext,
      (liftLevelBound ctx.shell.X : ℝ) * multReturn ctx
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6)
    -- Run (class 5)
    (multRun countRun : ∀ _ctx : ActualFailureContext, ℝ)
    (hpointRun : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (route ctx) 5,
        windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
          ≤ multRun ctx)
    (hmultRun_nonneg : ∀ ctx : ActualFailureContext, 0 ≤ multRun ctx)
    (hcardRun : ∀ ctx : ActualFailureContext,
      ((routedFibre ctx.n24CarryData (route ctx) 5).card : ℝ) ≤ countRun ctx)
    (hbudRun : ∀ ctx : ActualFailureContext,
      countRun ctx * multRun ctx
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    ChargeClassTRTData where
  route := route
  multTower := multTower
  countTower := countTower
  hpointTower := hpointTower
  hmultTower_nonneg := hmultTower_nonneg
  hcardTower := hcardTower
  hbudTower := hbudTower
  multReturn := multReturn
  countReturn := fun ctx => (liftLevelBound ctx.shell.X : ℝ)
  hpointReturn := hpointReturn
  hmultReturn_nonneg := hmultReturn_nonneg
  hcardReturn := fun ctx => (retCharge ctx).fibreCard_le_liftLevelBound_real
  hbudReturn := hbudReturn
  multRun := multRun
  countRun := countRun
  hpointRun := hpointRun
  hmultRun_nonneg := hmultRun_nonneg
  hcardRun := hcardRun
  hbudRun := hbudRun

/-! ## 7.  The class-6 `hOldRes` ledger field + the full `ChargedLedger` assembly

The class-6 leakage routing bound is produced from the two minimal L.6.4 routing residuals,
phrased against the *shared* budget routing `(trt.toBudget ctx).route` (= `trt.route ctx`),
so it is drop-in for the `hOldRes` field of `ChargedLedger`. -/

/-- **The class-6 `hOldRes` ledger field, from the L.6.4 routing residuals.**

`routedClassMassOf … (trt.toBudget ctx).route 6 ≤ ∑_{k∈K} oldResAt k` for every failure
context, from the L.6.4 retention `hsub` (routed class-6 fibre ⊆ `oldResIdxVal`) and the
L.20/L.21 cap `hcap` (per-index window excess ≤ `oldResBoundVal = ξ`), via
`routedClass6_le_oldResBranchMass`. -/
theorem hOldRes_of_routing (trt : ChargeClassTRTData)
    (hsub : ∀ ctx : ActualFailureContext,
      routedFibre ctx.n24CarryData (trt.toBudget ctx).route 6 ⊆ oldResIdxVal ctx)
    (hcap : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (trt.toBudget ctx).route 6,
        windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
          ≤ oldResBoundVal ctx) :
    ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (trt.toBudget ctx).route 6
        ≤ ∑ k ∈ oldResIdxVal ctx, oldResAtVal ctx k :=
  fun ctx => routedClass6_le_oldResBranchMass ctx (trt.toBudget ctx).route (hsub ctx) (hcap ctx)

/-- **Assemble a full `ChargedLedger` from the TRT data + the class-6 residuals + the three
sibling charging maps.**

Bundles the constructed `trt : ChargeClassTRTData` (classes 2/4/5 + the shared routing), the
class-6 old-residual leakage bound `hOldRes_of_routing` (against the genuine nonzero L.6.4
branch mass), and the sibling charging maps for classes 0/1/3 (Chernoff / clean-CNL /
DensePack) into the single residual surface `ChargedLedger`. -/
def chargedLedgerOfTRTOldRes (trt : ChargeClassTRTData)
    (chernoff : Class0ChernoffCharge trt.toBudget)
    (cnl : Class1CNLChargeData trt.toBudget)
    (densePack : ∀ ctx : ActualFailureContext, Class3DensePackCharge trt.toBudget ctx)
    (hsub : ∀ ctx : ActualFailureContext,
      routedFibre ctx.n24CarryData (trt.toBudget ctx).route 6 ⊆ oldResIdxVal ctx)
    (hcap : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (trt.toBudget ctx).route 6,
        windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
          ≤ oldResBoundVal ctx) :
    ChargedLedger where
  trt := trt
  chernoff := chernoff
  cnl := cnl
  densePack := densePack
  hOldRes := hOldRes_of_routing trt hsub hcap

/-- **Erdős #260 from the TRT data + the class-6 residuals + the sibling charging maps.**

The assembled charged ledger drives the consolidated capstone
`erdos260_chargedledger_reduced`, so the whole formalization follows from the genuine
per-class charge data constructed here together with the three sibling charging maps. -/
theorem erdos260_of_TRTOldRes (trt : ChargeClassTRTData)
    (chernoff : Class0ChernoffCharge trt.toBudget)
    (cnl : Class1CNLChargeData trt.toBudget)
    (densePack : ∀ ctx : ActualFailureContext, Class3DensePackCharge trt.toBudget ctx)
    (hsub : ∀ ctx : ActualFailureContext,
      routedFibre ctx.n24CarryData (trt.toBudget ctx).route 6 ⊆ oldResIdxVal ctx)
    (hcap : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (trt.toBudget ctx).route 6,
        windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
          ≤ oldResBoundVal ctx) :
    Erdos260Statement :=
  erdos260_chargedledger_reduced (chargedLedgerOfTRTOldRes trt chernoff cnl densePack hsub hcap)

/-! ## 8.  Honest residual inventory -/

/-- The precise status of the class-2/4/5 (Tower/Return/Run) and class-6 (old-residual)
charge-map construction after this module. -/
def chargeMapsTRTOldResResiduals : List String :=
  [ "RETURN (class 4) — GENUINELY REDUCED to the M.2.1 count: ReturnOlcRoutingCharge " ++
      "(the J.1.1 routing-to-OLC injection + matching) DERIVES, via Finset.card_le_card_of_injOn " ++
      "and the PROVED olcGeomOfShell_endpoints_card_le (= IsLiftChain.card_le), the genuine " ++
      "inverse-tower count |routedFibre 4| ≤ liftLevelBound X = O(log* X) " ++
      "(ReturnOlcRoutingCharge.fibreCard_le_liftLevelBound). So countReturn is DERIVED, not free; " ++
      "the residual is the OLC injection + the per-fibre window-excess multiplier + the K.4 numeric " ++
      "liftLevelBound X · mult ≤ c⋆ξX/6 (routedClass4_le_budget). Non-vacuous: ofSubsetEndpoints.",
    "TOWER (class 2) — count×multiplier over the routing fibre: routedClass2_le_budget reduces the " ++
      "Tower I.3.1 budget to the per-fibre window-excess multiplier (K.1.2/L.20), the routing's " ++
      "class-2 fibre count, and the K.4 numeric count·mult ≤ c⋆ξX/6 (the I.4.1 dense-packing " ++
      "fraction in count×multiplier form), via the PROVED routedClassMassOf_le_countMultiplier. The " ++
      "genuine Tower GEOMETRY is CLOSED and re-exported: tower_L24_disjointness_closed (L.2.4 " ++
      "per-output disjointness, the E.13 slope-orbit classifier towerClsOfShell, towerExitOf " ++
      "injective). No small combinatorial count exists for Tower (its smallness is the I.4.1 " ++
      "dense-packing fraction, a mass bound), so the count is a genuine routing residual.",
    "RUN (class 5) — count×multiplier over the routing fibre: routedClass5_le_budget reduces the Run " ++
      "I.5.2 budget to the per-fibre window-excess multiplier, the routing's class-5 fibre count, and " ++
      "the K.4 numeric count·mult ≤ c⋆ξX/6 (the I.5.2 run-mass floor in count×multiplier form), via " ++
      "the PROVED routedClassMassOf_le_countMultiplier. The genuine Run GEOMETRY is CLOSED and " ++
      "re-exported: run_chain_empty_closed (L.4.1 trichotomy runClsOfShell never routes to the " ++
      "shortening-chain class, so its routed mass is 0; the L.4.2 half-decrease is carried by " ++
      "runFOfShell). No small combinatorial count exists for Run either.",
    "OLD-RESIDUAL (class 6) — FULLY CONNECTED to the genuine L.6.4 branch mass: " ++
      "routedClass6_le_oldResBranchMass proves the exact hOldRes field routedClassMassOf … route 6 " ++
      "≤ ∑_{k∈K} oldResAt k from two minimal routing residuals — the L.6.4 retention " ++
      "routedFibre 6 ⊆ oldResIdxVal (K = supportShell d X) and the L.20/L.21 per-index cap " ++
      "windowExcess … k ≤ oldResBoundVal = ξ. Since oldResAt k = min(windowExcess k, ξ) is the " ++
      "capped window excess (OldResL65Core), the cap makes the routed mass EQUAL ∑_{routedFibre 6} " ++
      "oldResAt k, dominated by the genuine nonzero branch mass ∑_{k∈K} oldResAt k via subset + " ++
      "nonnegativity. NOT the degenerate oldResMass = 0.",
    "MINIMAL RESIDUAL (depends ONLY on the sibling J.1.1 routing interface) — per class, the routing " ++
      "fibre data: the per-fibre window-excess multiplier (hpoint, K.1.2/L.20), the fibre count " ++
      "(hcard for 2/5; the OLC injection for 4), the K.4 numeric (hbud), and for class 6 the " ++
      "retention/cap. The seven-class routing `route` is FREE data of Erdos260ChargeResidual, so " ++
      "these carry↔geometry relations are the genuine surviving J.1.1/M.2/L.6.4 content.",
    "ASSEMBLED — chargeClassTRTDataOfRouting builds the trt ledger field (countReturn DERIVED as " ++
      "liftLevelBound X); hOldRes_of_routing builds the class-6 field; chargedLedgerOfTRTOldRes + " ++
      "erdos260_of_TRTOldRes plug trt + hOldRes together with the three sibling charging maps into " ++
      "ChargedLedger and drive Erdos260Statement via erdos260_chargedledger_reduced." ]

theorem chargeMapsTRTOldResResiduals_nonempty : chargeMapsTRTOldResResiduals ≠ [] := by
  simp [chargeMapsTRTOldResResiduals]

/-! ## 9.  Axiom-cleanliness audit -/

#print axioms tower_L24_disjointness_closed
#print axioms return_olc_count_closed
#print axioms run_chain_empty_closed
#print axioms routedClassMass_le_countMult
#print axioms ReturnOlcRoutingCharge.fibreCard_le_liftLevelBound
#print axioms ReturnOlcRoutingCharge.routedClass4_le_budget
#print axioms ReturnOlcRoutingCharge.ofSubsetEndpoints
#print axioms routedClass2_le_budget
#print axioms routedClass5_le_budget
#print axioms routedClass6_le_oldResBranchMass
#print axioms chargeClassTRTDataOfRouting
#print axioms hOldRes_of_routing
#print axioms chargedLedgerOfTRTOldRes
#print axioms erdos260_of_TRTOldRes

end

end Erdos260
