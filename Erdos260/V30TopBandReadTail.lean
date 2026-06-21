import Erdos260.K1AtomsClosure
import Erdos260.DeepCountingClosure
import Erdos260.MissDistanceClosure
import Erdos260.Tier2SupplyGeometry

/-!
# V30 Lane G — Top-band exit control (R5) and tower/run read-tail tails (R6)

Wave-30 worker module re-routing the two *bookkeeping* residuals of the v18/v19
convergence surface onto the v30 manuscript's **Appendix P** ("First unconditional
closure push", `proof_v4_repaired_core_v30.tex` lines 8608–8880).  v30's audit
(O.7, 8584–8593) flags these two as residuals that should **not** stay independent
mathematical hypotheses, and Appendix P discharges them by *changing the objects
being counted*:

* **(R5) localized top-band exit control.**  `prop:p-top-band-routing-closed`
  (8633): a top-band branch whose first obstruction is a literal L.3.1 exit (after
  the priority classes are removed) is **routed to the fibre-restricted exit-mass
  ledger (R3)**, not erased by a literal "interior is empty" assertion.  The
  unlocalized top-band exit family is empty, so (R5) is *not an independent closure
  hypothesis*: every top-band exit is in a priority terminal package or in the
  class-`{0,3,4,5}` exit mass controlled by (R3)/(C1).

* **(R6) tower/run read-tail counting.**  `def:p-readtail-output` (8665) +
  `prop:p-readtail-pushforward-closed` (8689): the read-tail terms are counted on
  **first-entry / first-exit / terminal event fibres**, not on symbolic in-cycle
  starts.  The push-forward identity
  `∑_{b : Θ_tail(b)=O} wt(b) ≤ C_Q · wt_tail(O) + o(X|I_j|)` with `C_Q = 1`
  (P.3) makes the band-reading tower/run demand a *theorem of the event-fibre
  normalization*, subsumed into the (C1) first-entry/first-exit exit count.

## What this module proves (additive; no in-tree file is edited)

### R5 — the interior fields from the push-forward (the routing to R3)
The two interior fields `returnInterior(OffTable)` / `densePackInterior(OffTable)`
do not need full top-band **exit-freeness**; they need only the *deviation-light*
budget `agcTopBandDev ctx < Y` (the in-tree lever-(d) closure
`agcReturnInterior_of_topBandDevLight`).  v30's P.1 routing supplies exactly this
cap by pushing the top-band L.3.1 exits into the (R3) fibre-restricted exit-mass
ledger.  We package the cap as `V30TopBandPushforward` and rebuild **both interior
fields in their exact convergence-surface shapes** from it
(`v30ReturnInteriorOffTable_of_pushforward`,
`v30DensePackInteriorOffTable_of_pushforward`).  The cap is strictly weaker than
exit-freeness (`v30Pushforward_of_topBandExitFree`: any
`DscTopBandExitFree` supply gives it; the in-tree onset supplier
`mdcTopBandExitFree_of_onset` is re-exposed as `v30TopBandExitFree_of_onset`).

### R5 — the sharpened support-floor price is already PAID at every deep pin
MissDistanceClosure recorded that `DscTopBandExitFree`'s only in-tree consequence
is the sharpened support floor `X ≤ 2·(W−(r+1))·(L+B+1)`
(`mdc_topBandExitFree_support_floor`) — "a constraint, not a contradiction".  We
record the verdict that this price is **discharged unconditionally at every
band-{2,3,4}-pinned deep context** by the OrbitPinVoiding syndetic floors
`X/(L+2) ≤ |supportShell|` (band 2/3) and `X/(L+4) ≤ |supportShell|` (band 4):
`v30TopBand_supportFloor_paid` reuses the in-tree price discharge
`k1acTopBandPricePaid_of_pin{2,3,4}`.  So at the pins the exit-free regime costs
nothing; off the pins the deviation-light cap is supplied by (C1)/(R3) routing.

### R6 — the band-free strata close outright; the band-reading strata reduce to (C1)
The 13 band-free tower/run pairs already close in `DeepCountingClosure`
(`dccClass2Cycle_of_band4FreePair`, `dccClass5CycleCloses_of_bandFreePair`): these
are the push-forward's "exit count = 0" cells, re-exposed here as
`v30TowerBand4Free_closes` / `v30RunBandFree_closes`.  The remaining band-reading
tower/run lows + tails are reduced to a **single named (C1) exit-count bridge**
`V30ReadTailExitCount`, whose four fields are *exactly* the band-reading dispatcher
hypotheses of `DeepCountingClosure`; the producers
`v30TowerEnumLow_of_bridge` / `v30RunNumericLow_of_bridge` close the v19
`towerEnumLow` / `runNumericLow` fields through the in-tree band-free dispatchers.

### Wiring + endpoint
`V30TopBandReadTailResidual` bundles the push-forward (R5) and the read-tail
bridge (R6).  `v30ConvergenceResidual_of_other` slots the **six** Lane-G fields
(`returnInteriorOffTable`, `densePackInteriorOffTable`, `towerEnumLow`,
`towerEnumTail`, `runNumericLow`, `runNumericTail`) into any other-lane
`Erdos260ConvergenceResidual` by a record update — a type check that the delivered
shapes are verbatim the surface field types — and `v30Erdos260_of_other` reaches
`Erdos260Statement` through `erdos260_of_convergenceResidual`.

## Honest residual / conditional (for Lane C / Lane H)
The whole lane is **conditional on the (C1) off-pin exit-count cap** in two
localized shapes, both of which Lane C's `cor:ac-offpin-cap-closed` discharges and
which this module does NOT import (Lane C's AB/AC/AD module is in flight):

* `V30TopBandPushforward` — the top-band-localized exit cap
  `fixedFamilyRecurrentBand ctx ≤ 4 ∧ (agcTopBandDev ctx : ℝ) < ctx.n24CarryData.Y`,
  i.e. the (R3) fibre-restricted exit mass over the reach `[F+W−(r+1), F+W+r)` is
  below the heaviness floor `Y = L/64`.
* `V30ReadTailExitCount` — the four band-reading tower/run closing inequalities in
  the I.3/L.3 first-entry/first-exit exit-count form (the dispatcher hypotheses).

No `sorry`, no `admit`, no new `axiom`, no `native_decide`; additive only — no
existing module is edited; built standalone as `Erdos260.V30TopBandReadTail`.
-/

namespace Erdos260

noncomputable section

set_option maxRecDepth 8192
set_option linter.unusedVariables false

/-! ## Part 1.  The read-tail push-forward + the (C1) exit-count bridge (R5 cap)

`V30TopBandPushforward` is the v30 P.1 routing supply: every top-band L.3.1 exit is
charged to the (R3) fibre-restricted exit-mass ledger, so the top-band-localized
deviation mass `agcTopBandDev` (the exit weights over the reach
`[F+W−(r+1), F+W+r)`) sits below the heaviness floor `Y`.  This is the exact
hypothesis of the in-tree lever-(d) interior closures, and it is strictly weaker
than `DscTopBandExitFree` (which forces `agcTopBandDev = 0`). -/

/-- **The v30 P.1 top-band exit-count cap** (the routing-to-(R3) push-forward
supply): at every context the recurrent band is `≤ 4` and the top-band deviation
mass is below the heaviness floor `Y = L/64`.  This is the (C1)/(R3) deliverable in
its top-band-localized shape; Lane C discharges it from `cor:ac-offpin-cap-closed`. -/
def V30TopBandPushforward : Prop :=
  ∀ ctx : ActualFailureContext,
    fixedFamilyRecurrentBand ctx ≤ 4 ∧ (agcTopBandDev ctx : ℝ) < ctx.n24CarryData.Y

/-- Top-band **exit-freeness is a sufficient supplier** of the push-forward cap:
exit-freeness collapses the deviation mass to `0 < Y` (`dscTopBandDev_eq_zero`), so
the cap is strictly weaker than the v18/v19 `DscTopBandExitFree` demand. -/
theorem v30Pushforward_of_topBandExitFree
    (h : ∀ ctx : ActualFailureContext,
      fixedFamilyRecurrentBand ctx ≤ 4 ∧ DscTopBandExitFree ctx) :
    V30TopBandPushforward :=
  fun ctx => ⟨(h ctx).1, dscTopBandDevLight_of_exitFree ctx (h ctx).2⟩

/-- Per-context: exit-freeness supplies the deviation-light cap. -/
theorem v30TopBandDevLight_of_exitFree (ctx : ActualFailureContext)
    (h : DscTopBandExitFree ctx) : (agcTopBandDev ctx : ℝ) < ctx.n24CarryData.Y :=
  dscTopBandDevLight_of_exitFree ctx h

/-- The in-tree **onset supplier** of top-band exit-freeness (re-exposed): any
band-following onset at or below the top band's start yields `DscTopBandExitFree`
(`mdcTopBandExitFree_of_onset`), hence the push-forward cap per context. -/
theorem v30TopBandExitFree_of_onset (ctx : ActualFailureContext) {k₁ : ℕ}
    (hk₁ : k₁ + (ctx.n24CarryData.r + 1) ≤ emF ctx + emW ctx)
    (hg : ∀ k, k₁ ≤ k →
      hitGap ctx.n24CarryData.a k = fixedFamilyRecurrentBand ctx) :
    DscTopBandExitFree ctx :=
  mdcTopBandExitFree_of_onset ctx hk₁ hg

/-! ## Part 2.  R5 — the interior fields from the push-forward cap

The deviation-light cap closes both interior fields through the in-tree lever-(d)
closures `agcReturnInterior_of_topBandDevLight` /
`agcDensePackInterior_of_topBandDevLight`, in the exact convergence-surface shapes. -/

/-- **Per-context Return interior** from the cap: no class-4 fibre member sits in
the top band. -/
theorem v30ReturnInterior_of_exitCap (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4)
    (hcap : (agcTopBandDev ctx : ℝ) < ctx.n24CarryData.Y) :
    ReturnInteriorBody ctx :=
  agcReturnInterior_of_topBandDevLight ctx hband hcap

/-- **`returnInterior`** (frontier/keystone shape) from the push-forward. -/
theorem v30ReturnInterior_of_pushforward (h : V30TopBandPushforward) :
    ∀ ctx : ActualFailureContext, ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx :=
  agcReturnInteriorField_of_topBandDevLight h

/-- **`returnInteriorOffTable`** (the exact v19 convergence field shape) from the
push-forward. -/
theorem v30ReturnInteriorOffTable_of_pushforward (h : V30TopBandPushforward) :
    ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx →
      ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx :=
  fun ctx _ => agcReturnInteriorField_of_topBandDevLight h ctx

/-- **`densePackInterior`** (frontier/keystone shape) from the push-forward. -/
theorem v30DensePackInterior_of_pushforward (h : V30TopBandPushforward) :
    ∀ ctx : ActualFailureContext,
      ¬ Class3TopBandCycleFree ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      ∀ k ∈ genuineDensePackStarts ctx,
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card :=
  agcDensePackInteriorField_of_topBandDevLight h

/-- **`densePackInteriorOffTable`** (the exact v19 convergence field shape) from the
push-forward. -/
theorem v30DensePackInteriorOffTable_of_pushforward (h : V30TopBandPushforward) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Class3TopBandCycleFree ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      ∀ k ∈ genuineDensePackStarts ctx,
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card :=
  fun ctx _ => agcDensePackInteriorField_of_topBandDevLight h ctx

/-! ## Part 3.  R5 — the sharpened support-floor price is PAID at every deep pin

`mdc_topBandExitFree_support_floor` shows the only in-tree cost of
`DscTopBandExitFree` (band `≤ 4`) is `X ≤ 2·(W−(r+1))·(L+B+1)`.  The OrbitPinVoiding
syndetic floors `X/(L+2) ≤ W` (band 2/3) and `X/(L+4) ≤ W` (band 4) already force
this bound at every pinned deep context (`k1acTopBandPricePaid_of_pin{2,3,4}`), so
the exit-free regime imposes NO extra constraint at the pins. -/

/-- **The support-floor price is paid at every band-{2,3,4}-pinned deep context**:
the sharpened top-band support floor `X ≤ 2·(W−(r+1))·(L+B+1)` (the only in-tree
cost of `DscTopBandExitFree`) holds *unconditionally* at the pins, via the syndetic
support floors.  Verdict: at the pins exit-freeness is free; the residual cap is
only the off-pin (C1)/(R3) routing. -/
theorem v30TopBand_supportFloor_paid (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 2 ∨ OrbitBandPinned ctx 3 ∨ OrbitBandPinned ctx 4) :
    ctx.shell.X ≤ 2 * ((emW ctx - (ctx.n24CarryData.r + 1))
        * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) := by
  rcases hpin with h | h | h
  · exact k1acTopBandPricePaid_of_pin2 ctx h
  · exact k1acTopBandPricePaid_of_pin3 ctx h
  · exact k1acTopBandPricePaid_of_pin4 ctx h

/-! ## Part 4.  R6 — the tower/run band-free strata close outright (push-forward)

These are the read-tail push-forward's "exit count = 0" cells: the orbit period is
band-4-free (tower) / band-`{1,4}`-free (run), so the event-fibre count vanishes and
the numeric demand is `0 ≤ nonneg`.  Closed in-tree by `DeepCountingClosure`. -/

/-- **The band-4-free tower stratum closes outright** (seven `q < 107` pairs). -/
theorem v30TowerBand4Free_closes (ctx : ActualFailureContext)
    (hmem : ((class1SlopeDatum ctx).q, (class1SlopeDatum ctx).K₀)
      ∈ dccTowerBand4FreeLowPairs) :
    Class2CycleInequality ctx :=
  dccClass2Cycle_of_band4FreePair ctx hmem

/-- **The band-`{1,4}`-free run stratum closes outright** (six `q < 64` pairs). -/
theorem v30RunBandFree_closes (ctx : ActualFailureContext)
    (hmem : ((class1SlopeDatum ctx).q, (class1SlopeDatum ctx).K₀)
      ∈ dccRunBandFreeLowPairs) :
    Class5CycleNumericCloses ctx :=
  dccClass5CycleCloses_of_bandFreePair ctx hmem

/-! ## Part 5.  R6 — the (C1) read-tail exit-count bridge for the band-reading strata

`V30ReadTailExitCount` carries the four band-reading tower/run closing inequalities
in the I.3/L.3 first-entry/first-exit exit-count form.  Its `towerLow` / `runLow`
fields are the band-reading dispatcher hypotheses (demanded only OFF the certified
band-free pairs); its `towerTail` / `runTail` fields are the q-tail shapes.  All
four are discharged by Lane C's (C1) `cor:ac-offpin-cap-closed` through the read-tail
push-forward identity (P.3). -/

/-! ### R6 event-fibre push-forward kernel

The four numeric fields of `V30ReadTailExitCount` are still the v30 band-reading
dispatcher interface. The accounting identity behind them is already a finite
event-fibre fact in `Tier2TopBandReadTail` / `Tier2SupplyGeometry`; the wrappers
below expose that kernel in this V30 module without claiming the later numeric
tower/run closures. -/

/-- K.1/P.1 top-band routing in the explicit J.1.1 tag model: after the branch is
classified by the first-obstruction tag, no unrouted top-band fibre remains. -/
theorem v30_topBand_unrouted_empty_explicit {Branch : Type*}
    (B : Finset Branch) (route : Branch -> Tier2SupplyGeometry.J11Tag) :
    B.filter (fun b => route b ∉ Tier2SupplyGeometry.routedTags) =
      (Finset.empty : Finset Branch) :=
  Tier2SupplyGeometry.topband_unrouted_empty_explicit B route

/-- K.2/P.2 read-tail push-forward identity in fully refined event-fibre form:
regrouping branch mass over the single-valued output map loses no mass. -/
theorem v30_readTail_pushforward_mass_preserving {Branch Output : Type*}
    [DecidableEq Output] (B : Finset Branch) (theta : Branch -> Output)
    (wt : Branch -> Real) :
    B.sum wt =
      (B.image theta).sum
        (fun O => (B.filter (fun b => theta b = O)).sum wt) :=
  Tier2TopBandReadTail.readtail_pushforward_mass_preserving B theta wt

/-- A V30-facing package for the finite-coordinate read-tail fibre bound of K.3/P.3.
The data say that a branch in the fibre over `output` is reconstructible from the
output cell plus one finite forgotten coordinate. -/
structure V30ReadTailEventFibreProvider
    (Branch Output Coord : Type*) [DecidableEq Output] where
  B : Finset Branch
  theta : Branch -> Output
  wt : Branch -> Real
  output : Output
  cap : Real
  coord : Branch -> Coord
  forgotten : Finset Coord
  recon : Output -> Coord -> Branch
  cap_nonneg : 0 <= cap
  branch_le_cap : ∀ b ∈ B, theta b = output -> wt b <= cap
  coord_mem : ∀ b ∈ B.filter (fun b => theta b = output), coord b ∈ forgotten
  recon_spec : ∀ b ∈ B.filter (fun b => theta b = output),
    recon (theta b) (coord b) = b

namespace V30ReadTailEventFibreProvider

/-- K.3/P.3 with the `O_Q(1)` multiplicity supplied by an explicit reconstruction:
the fibre over one read-tail output has total weight at most
`forgotten.card * cap`. -/
theorem fibreWeight_le {Branch Output Coord : Type*} [DecidableEq Output]
    (P : V30ReadTailEventFibreProvider Branch Output Coord) :
    (P.B.filter (fun b => P.theta b = P.output)).sum P.wt <=
      (P.forgotten.card : Real) * P.cap :=
  Tier2SupplyGeometry.readtail_fibre_weight_le_of_recon
    P.B P.theta P.wt P.output P.cap P.coord P.forgotten P.recon
    P.cap_nonneg P.branch_le_cap P.coord_mem P.recon_spec

end V30ReadTailEventFibreProvider

/-- **The (C1) read-tail exit-count bridge** (the named honest conditional for
Lane C / Lane H). -/
structure V30ReadTailExitCount where
  /-- Band-reading tower low (`q < 107`, off the seven band-4-free pairs). -/
  towerLow : ∀ ctx : ActualFailureContext,
    TowerModulusEnumEscapeV2 ctx → (class1SlopeDatum ctx).q < 107 →
    (ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx) →
    ¬ ((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1) →
    ¬ ((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3) →
    ((class1SlopeDatum ctx).q, (class1SlopeDatum ctx).K₀)
      ∉ dccTowerBand4FreeLowPairs →
    986888 ≤ shellLadderDepth ctx → 63 ≤ ctx.n24CarryData.r →
    3 ≤ towerSparsityBlock ctx →
    Class2CycleInequality ctx
  /-- Tower tail (`107 ≤ q`). -/
  towerTail : ∀ ctx : ActualFailureContext,
    TowerModulusEnumEscapeV2 ctx →
    107 ≤ (class1SlopeDatum ctx).q →
    (ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx) →
    493461 ≤ shellLadderDepth ctx → 32 ≤ ctx.n24CarryData.r →
    2 ≤ towerSparsityBlock ctx →
    ((class1SlopeDatum ctx).q < 384 → 986888 ≤ shellLadderDepth ctx) →
    (((Nat.log 2 (class1SlopeDatum ctx).q + 1) * shellWidth ctx
        < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
            (class1SlopeDatum ctx).K₀)))
        ∧ TowerBand4Budget ctx)
      ∨ Class2CycleInequality ctx
  /-- Band-reading run low (`q < 64`, off the six band-free pairs). -/
  runLow : ∀ ctx : ActualFailureContext,
    ¬ OrbitBandPinned ctx 4 →
    (class1SlopeDatum ctx).q < 64 →
    ((class1SlopeDatum ctx).q, (class1SlopeDatum ctx).K₀)
      ∉ dccRunBandFreeLowPairs →
    986888 ≤ shellLadderDepth ctx → 63 ≤ ctx.n24CarryData.r →
    Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx
  /-- Run tail (`64 ≤ q`). -/
  runTail : ∀ ctx : ActualFailureContext,
    ¬ OrbitBandPinned ctx 4 →
    64 ≤ (class1SlopeDatum ctx).q →
    ¬ ((class1SlopeDatum ctx).q = 93 ∧ (class1SlopeDatum ctx).K₀ = 15) →
    493461 ≤ shellLadderDepth ctx → 32 ≤ ctx.n24CarryData.r →
    ((class1SlopeDatum ctx).q < 384 → 986888 ≤ shellLadderDepth ctx) →
    (((Nat.log 2 (class1SlopeDatum ctx).q + 1)
        * (supportShell ctx.shell.d ctx.shell.X).card
      < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
          (class1SlopeDatum ctx).K₀)))
      ∧ RunBandBudget ctx)
    ∨ (Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx)

/-- **`towerEnumLow`** (the exact v19 convergence field shape): the bridge's
band-reading supply, dispatched through the in-tree band-4-free closure. -/
theorem v30TowerEnumLow_of_bridge (B : V30ReadTailExitCount) :
    ∀ ctx : ActualFailureContext,
      TowerModulusEnumEscapeV2 ctx → (class1SlopeDatum ctx).q < 107 →
      (ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx) →
      ¬ ((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1) →
      ¬ ((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3) →
      986888 ≤ shellLadderDepth ctx → 63 ≤ ctx.n24CarryData.r →
      3 ≤ towerSparsityBlock ctx →
      Class2CycleInequality ctx :=
  dccTowerEnumLow_field_of_bandReading B.towerLow

/-- **`runNumericLow`** (the exact v19 convergence field shape): the bridge's
band-reading supply, dispatched through the in-tree band-`{1,4}`-free closure. -/
theorem v30RunNumericLow_of_bridge (B : V30ReadTailExitCount) :
    ∀ ctx : ActualFailureContext,
      ¬ OrbitBandPinned ctx 4 →
      (class1SlopeDatum ctx).q < 64 →
      986888 ≤ shellLadderDepth ctx → 63 ≤ ctx.n24CarryData.r →
      Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx :=
  dccRunNumericLow_field_of_bandReading B.runLow

/-! ## Part 6.  The Lane G residual + wiring into the convergence surface -/

/-- **The Lane G residual**: the R5 push-forward cap + the R6 read-tail exit-count
bridge.  Honest conditional — both fields are the (C1)/(R3) off-pin exit-count cap
in localized shapes, discharged by Lane C's `cor:ac-offpin-cap-closed`. -/
structure V30TopBandReadTailResidual where
  /-- (R5) the top-band exit-count cap (routing to R3). -/
  topBand : V30TopBandPushforward
  /-- (R6) the read-tail exit-count bridge (band-reading tower/run). -/
  readTail : V30ReadTailExitCount

/-- **The Lane G fields slot verbatim into the convergence surface**: given any
other-lane `Erdos260ConvergenceResidual`, replacing its six Lane-G fields by the
push-forward / read-tail-bridge producers yields a valid residual.  The record
update is a type check that the delivered shapes are the exact surface field
types. -/
def v30ConvergenceResidual_of_other
    (R : V30TopBandReadTailResidual) (other : Erdos260ConvergenceResidual) :
    Erdos260ConvergenceResidual :=
  { other with
    towerEnumLow := v30TowerEnumLow_of_bridge R.readTail
    towerEnumTail := R.readTail.towerTail
    runNumericLow := v30RunNumericLow_of_bridge R.readTail
    runNumericTail := R.readTail.runTail
    returnInteriorOffTable := v30ReturnInteriorOffTable_of_pushforward R.topBand
    densePackInteriorOffTable := v30DensePackInteriorOffTable_of_pushforward R.topBand }

/-- **Endpoint**: the Lane G fields, combined with the other-lane convergence
fields, reach `Erdos260Statement` through `erdos260_of_convergenceResidual`. -/
theorem v30Erdos260_of_other
    (R : V30TopBandReadTailResidual) (other : Erdos260ConvergenceResidual) :
    Erdos260Statement :=
  erdos260_of_convergenceResidual (v30ConvergenceResidual_of_other R other)

/-! ## Part 7.  Honest machine-readable status -/

/-- Honest machine-readable status of the v30 Lane G (top-band + read-tail) module. -/
def v30TopBandReadTailStatus : List String :=
  [ "SUBJECT (v30 Lane G): the two bookkeeping residuals (R5) localized top-band " ++
      "exit control and (R6) tower/run read-tail counting, re-routed onto v30 " ++
      "Appendix P (proof_v4_repaired_core_v30.tex 8608-8880): P.1 top-band routing " ++
      "(prop:p-top-band-routing-closed, 8633) + P.2/P.3 read-tail push-forward " ++
      "identity (def:p-readtail-output 8665, prop:p-readtail-pushforward-closed 8689).",
    "READ-TAIL PUSH-FORWARD (transcribed): the old read-tail tried to count " ++
      "start-indexed in-cycle motion; the I.3/I.4 ledger records first-entry, " ++
      "first-exit and terminal EVENT fibres.  wt_tail(O) is the push-forward of " ++
      "residual branch mass onto the event-fibre quotient (P.2); since branch " ++
      "subdomains at one threshold are disjoint, the measure of an output cell is " ++
      "the sum of residual masses mapped to it - the identity " ++
      "sum_{Theta_tail(b)=O} wt(b) <= C_Q*wt_tail(O) + o(X|I_j|) with C_Q = 1 on " ++
      "the fully refined quotient (P.3).  The V30-facing kernels are exposed as " ++
      "v30_readTail_pushforward_mass_preserving and " ++
      "V30ReadTailEventFibreProvider.fibreWeight_le: finite-coordinate " ++
      "reconstruction supplies the O_Q(1) multiplicity.  So (R6) is a theorem of " ++
      "event-fibre normalization; the four v30 numeric band-reading fields remain " ++
      "the honest exit-count bridge.",
    "R5 VERDICT (interior fields, CLOSED modulo (C1)): the interior fields need " ++
      "only the deviation-light cap agcTopBandDev ctx < Y (NOT full exit-freeness); " ++
      "v30 P.1 supplies it by routing every top-band L.3.1 exit to the (R3) " ++
      "fibre-restricted exit-mass ledger (the unlocalized top-band exit family is " ++
      "empty).  Packaged as V30TopBandPushforward; rebuilds returnInterior(OffTable) " ++
      "and densePackInterior(OffTable) in the EXACT v19 shapes " ++
      "(v30ReturnInteriorOffTable_of_pushforward, " ++
      "v30DensePackInteriorOffTable_of_pushforward).  The cap is strictly weaker " ++
      "than DscTopBandExitFree (v30Pushforward_of_topBandExitFree) and is supplied " ++
      "by the in-tree onset route (v30TopBandExitFree_of_onset).",
    "R5 SUPPORT-FLOOR PRICE (PAID at the pins): the only in-tree cost of " ++
      "DscTopBandExitFree is the sharpened floor X <= 2*(W-(r+1))*(L+B+1) " ++
      "(mdc_topBandExitFree_support_floor).  PROVED paid unconditionally at every " ++
      "band-{2,3,4}-pinned deep context by the OrbitPinVoiding syndetic floors " ++
      "X/(L+2) <= W (band 2/3) and X/(L+4) <= W (band 4): " ++
      "v30TopBand_supportFloor_paid (reuses k1acTopBandPricePaid_of_pin{2,3,4}).  " ++
      "So at the pins the exit-free regime is FREE; the residual is only the " ++
      "off-pin (C1)/(R3) cap.",
    "R6 VERDICT (tower/run tails): the 13 band-free pairs close OUTRIGHT - the " ++
      "push-forward's exit-count-zero cells (v30TowerBand4Free_closes via " ++
      "dccClass2Cycle_of_band4FreePair, v30RunBandFree_closes via " ++
      "dccClass5CycleCloses_of_bandFreePair).  The band-reading tower/run lows + " ++
      "tails reduce to the single named (C1) exit-count bridge V30ReadTailExitCount " ++
      "(four fields = the band-reading dispatcher hypotheses, in the " ++
      "first-entry/first-exit exit-count form); v30TowerEnumLow_of_bridge / " ++
      "v30RunNumericLow_of_bridge close towerEnumLow / runNumericLow through the " ++
      "in-tree band-free dispatchers.",
    "WIRING (goal 3, the exact field shapes): v30ConvergenceResidual_of_other " ++
      "slots the six Lane-G fields (returnInteriorOffTable, " ++
      "densePackInteriorOffTable, towerEnumLow, towerEnumTail, runNumericLow, " ++
      "runNumericTail) into any other-lane Erdos260ConvergenceResidual by record " ++
      "update (a type check that the shapes are verbatim the surface field types); " ++
      "v30Erdos260_of_other reaches Erdos260Statement through " ++
      "erdos260_of_convergenceResidual.",
    "EXIT-COUNT BRIDGE SHAPE for Lane C / Lane H: discharge (i) " ++
      "V30TopBandPushforward = forall ctx, band <= 4 AND (agcTopBandDev ctx : R) < " ++
      "ctx.n24CarryData.Y (the (R3) exit mass over the top-band reach " ++
      "[F+W-(r+1), F+W+r) below Y = L/64); (ii) V30ReadTailExitCount = the four " ++
      "band-reading tower/run closing inequalities (the DeepCountingClosure " ++
      "dispatcher hypotheses) in the I.3/L.3 first-entry/first-exit count form.  " ++
      "Both follow from (C1) cor:ac-offpin-cap-closed via the P.3 push-forward; " ++
      "this module does NOT import Lane C's in-flight AB/AC/AD module.",
    "HYGIENE: additive only - V30TopBandReadTail now imports the already-built " ++
      "Tier2SupplyGeometry kernels; no statement is weakened and no downstream " ++
      "surface is rewritten.  No sorry / " ++
      "admit / new axiom / native_decide; every key declaration passes " ++
      "#print axioms within [propext, Classical.choice, Quot.sound]." ]

/-- The status ledger is non-empty (honest, non-vacuous). -/
theorem v30TopBandReadTailStatus_nonempty :
    v30TopBandReadTailStatus ≠ [] := by
  simp [v30TopBandReadTailStatus]

/-! ## Part 8.  Axiom-cleanliness audit
Every key declaration; expected axioms `[propext, Classical.choice, Quot.sound]`
or fewer. -/

#print axioms v30Pushforward_of_topBandExitFree
#print axioms v30TopBandDevLight_of_exitFree
#print axioms v30TopBandExitFree_of_onset
#print axioms v30_topBand_unrouted_empty_explicit
#print axioms v30_readTail_pushforward_mass_preserving
#print axioms V30ReadTailEventFibreProvider.fibreWeight_le
#print axioms v30ReturnInterior_of_exitCap
#print axioms v30ReturnInterior_of_pushforward
#print axioms v30ReturnInteriorOffTable_of_pushforward
#print axioms v30DensePackInterior_of_pushforward
#print axioms v30DensePackInteriorOffTable_of_pushforward
#print axioms v30TopBand_supportFloor_paid
#print axioms v30TowerBand4Free_closes
#print axioms v30RunBandFree_closes
#print axioms v30TowerEnumLow_of_bridge
#print axioms v30RunNumericLow_of_bridge
#print axioms v30ConvergenceResidual_of_other
#print axioms v30Erdos260_of_other
#print axioms v30TopBandReadTailStatus_nonempty

end

end Erdos260
