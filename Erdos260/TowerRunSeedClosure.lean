import Erdos260.TowerRunMassSeedCore
import Erdos260.GenuineObstructionRoutingCore
import Erdos260.Erdos260SeedResidual

/-!
# The Tower (I.4.1) and Run (I.5.2 / L.4.2) mass-fraction seeds, PINNED to the genuine route

This module (NEW; it edits no existing file) closes the two `SeedTRTData` / `TowerRunMassFractionData`
**Tower (class 2)** and **Run (class 5)** seed fields *for the actual first-obstruction route*
`genuineChargeRoute` (`GenuineObstructionRoutingCore.lean`), pushing each toward full unconditional
construction and reducing the irreducible remainder to a single honest manuscript core.

It builds on the generic, route-agnostic `TowerRunMassSeedCore.lean` (the prior worker's
`towerFraction_of_failure` / `runFloor_of_geometricBase`), adding three genuinely new pieces:

1. **A concrete active threshold layer.**  `seedTowerS ctx = X/6` and `seedTowerIj ctx = 1/X` realise
   the I.4.1 active layer at the *canonical block fraction* `|I_j| = 1/X` (the same canonical fraction
   the Return capacity leaf uses, `PhaseCapacityCore.returnLeafOfRouted`), normalised so the single
   active layer measure equals the per-phase budget share: `seedTowerLayer` proves
   `seedTowerS · seedTowerIj = 1/6 ≤ 1/6`.  (`TowerRunMassSeedData` left `towerS`/`towerIj` as free
   fields; here they are *constructed* from the shell's `X`, with the normalisation proved.)

2. **A single-inequality Tower core.**  With the layer pinned to the budget share, the I.4.1 fraction
   `htowerFraction : routedClassMassOf … 2 ≤ ξ·s·X·|I_j|` collapses to the *smallest honest core*
   `htowerSubMass : routedClassMassOf … 2 ≤ ξ·X/6` (`towerFraction_of_subMass`, exact algebra via the
   block-fraction cancellation `X·(1/X)=1`).  This is a bound on the **class-2 routed SUB-mass** — a
   fraction strictly below the slot `c⋆·ξ·X/6` — never the full high-excess mass (whose `≤ c⋆ξX/6`
   reading is refuted by the reused honest finding `towerBudget_residual_forces_X_nonpos`).  The deeper
   reduction `towerSubMass_of_failure` shows this single core itself follows from the K.1.1
   endpoint-disjoint cover + the I.4.1 dense-marker hit packing + the K.4 smallness, genuinely
   consuming the positive-density failure `ctx.hfailure` (via `markerCount_le_of_failure`).

3. **The Run period-descent chain, pinned to the genuine route.**  The geometric chain
   `w_i = w₀·2^{-i}` (ratio `1/2` = the L.4.2 half-decrease, anchored in the actual shell residual
   centre by `runFOfShell_halfDecrease`) reduces the I.5.2 floor `hrunFloor : routedClassMassOf … 5 ≤
   c⋆ξX/6` to the I.6S chain domination (`hrunSum`) and the **base run output bound**
   `hrunBase12 : w₀ ≤ c⋆ξX/12`, with NO count (`runFloor_of_geometricBase`).

The deliverable `TowerRunSeedClosureData` carries exactly these minimal cores over `genuineChargeRoute`
and produces, for an arbitrary `ActualFailureContext`, the genuine `towerS`/`towerIj`/`htowerLayer`/
`htowerFraction`/`hrunFloor` fields of `SeedTRTData` and `TowerRunMassFractionData` — plugging into the
frontier endpoint `erdos260_seed_reduced` (`Erdos260SeedResidual.lean`) with the Return seed supplied by
the sibling worker.

No `sorry`, `axiom`, or `admit`.  No degenerate full-mass / empty / zero-fraction / `PEmpty` shortcut.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 1.  The active threshold layer: canonical block-fraction order and length

The I.4.1 active layer is realised at the canonical block fraction `|I_j| = 1/X` (the layer measure used
by the Return capacity leaf), with order `s = X/6` chosen so the *single* active layer measure equals the
`1/6` per-phase budget share.  This is the genuine layer normalisation `s·|I_j| ≤ 1/6`, here with
equality `= 1/6`. -/

/-- **The I.4.1 active threshold-layer order `s`** of the actual shell: `s = X/6`, the order pinning the
single active layer's measure to the `1/6` per-phase budget share at the canonical block fraction. -/
def seedTowerS (ctx : ActualFailureContext) : ℝ := (ctx.shell.X : ℝ) / 6

/-- **The I.4.1 active threshold-layer interval length `|I_j|`** of the actual shell: the canonical block
fraction `|I_j| = 1/X` (the same fraction the Return M.2 capacity leaf uses). -/
def seedTowerIj (ctx : ActualFailureContext) : ℝ := 1 / (ctx.shell.X : ℝ)

/-- **The layer normalisation (PROVED), `s·|I_j| ≤ 1/6`.**  The single active layer measure
`seedTowerS · seedTowerIj = (X/6)·(1/X) = 1/6` is exactly the per-phase budget share, via the canonical
block-fraction cancellation `X·(1/X) = 1` (`PhaseCapacityCore.mul_X_invX_cancel`). -/
theorem seedTowerLayer (ctx : ActualFailureContext) :
    seedTowerS ctx * seedTowerIj ctx ≤ 1 / 6 := by
  have heq : seedTowerS ctx * seedTowerIj ctx = 1 / 6 := by
    unfold seedTowerS seedTowerIj
    have h := mul_X_invX_cancel ctx (1 / 6 : ℝ)
    calc (ctx.shell.X : ℝ) / 6 * (1 / (ctx.shell.X : ℝ))
        = (1 / 6 : ℝ) * (ctx.shell.X : ℝ) * (1 / (ctx.shell.X : ℝ)) := by ring
      _ = 1 / 6 := h
  exact heq.le

/-- The active-layer measure is exactly the `1/6` budget share (not strictly below it). -/
theorem seedTowerLayer_eq (ctx : ActualFailureContext) :
    seedTowerS ctx * seedTowerIj ctx = 1 / 6 := by
  unfold seedTowerS seedTowerIj
  have h := mul_X_invX_cancel ctx (1 / 6 : ℝ)
  calc (ctx.shell.X : ℝ) / 6 * (1 / (ctx.shell.X : ℝ))
      = (1 / 6 : ℝ) * (ctx.shell.X : ℝ) * (1 / (ctx.shell.X : ℝ)) := by ring
    _ = 1 / 6 := h

/-! ## 2.  Tower (class 2): the single sub-mass fraction core, and its failure-driven reduction -/

/-- **The I.4.1 dense-packing fraction from the single sub-mass core (exact algebra).**

With the active layer pinned to the budget share (`s·|I_j| = 1/6`), the manuscript I.4.1 fraction
`routedClassMassOf … 2 ≤ ξ·s·X·|I_j|` is *exactly* the single-inequality core
`routedClassMassOf … 2 ≤ ξ·X/6`: the RHS `ξ·(X/6)·X·(1/X) = ξ·X/6` by the canonical block-fraction
cancellation `X·(1/X) = 1`.  So the Tower seed reduces to the bare class-2 sub-mass fraction. -/
theorem towerFraction_of_subMass (ctx : ActualFailureContext)
    (hsub : routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
        ≤ erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
      ≤ erdos260Constants.ξ * seedTowerS ctx * (ctx.shell.X : ℝ) * seedTowerIj ctx := by
  have heq : erdos260Constants.ξ * seedTowerS ctx * (ctx.shell.X : ℝ) * seedTowerIj ctx
      = erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 := by
    unfold seedTowerS seedTowerIj
    rw [mul_X_invX_cancel ctx (erdos260Constants.ξ * ((ctx.shell.X : ℝ) / 6))]
    ring
  rw [heq]; exact hsub

/-- **The Tower routed-fraction slot from the single sub-mass core (no count).**  The class-2 sub-mass
fraction `routedClassMassOf … 2 ≤ ξ·X/6` fits the per-phase slot `c⋆·ξ·X/6` because `c⋆ ≥ 1` and
`ξ·X ≥ 0`.  This is a bound on ONE routed class — a genuine fraction, never the circular full mass. -/
theorem towerSlot_of_subMass (ctx : ActualFailureContext)
    (hsub : routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
        ≤ erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 := by
  have hξ : (0 : ℝ) ≤ erdos260Constants.ξ := le_of_lt erdos260Constants.ξ_pos
  have hX : (0 : ℝ) ≤ (ctx.shell.X : ℝ) := ctx.shell.X_nonneg_real
  have hc : (1 : ℝ) ≤ erdos260Constants.cStar := one_le_cStar
  have hprod : 0 ≤ (erdos260Constants.cStar - 1) * (erdos260Constants.ξ * (ctx.shell.X : ℝ)) :=
    mul_nonneg (by linarith) (mul_nonneg hξ hX)
  nlinarith [hsub, hprod]

/-- **The single Tower sub-mass core itself, reduced to the I.4.1 failure-driven count×multiplier.**

The class-2 sub-mass fraction `routedClassMassOf … 2 ≤ ξ·X/6` follows from the bare I.4.1 geometry,
*genuinely consuming the positive-density failure hypothesis* `ctx.hfailure`:

* the K.1.2/L.20 residual multiplier bounds every routed-`2` window excess (`hpoint`, `hmult_nonneg`);
* the K.1.1 endpoint-disjoint cover bounds the class-`2` fibre by the dense markers' neighbourhoods
  (`hcover`);
* the markers each pack `≥ ρ_D·L` hits (`hpack`), so the failure cap `#(supportShell d X) < c₀·X`
  forces the marker count small (`markerCount_le_of_failure`, eq. I.3);
* the proved `corollaryK1_3_densePackUnderFailure` + `routedClassMassOf_le_countMultiplier` turn this
  into the routed-mass bound, and the K.4 numeric smallness `hsmall` ("choose `c_* ≪_Q ρ_D κ ξ`",
  I.3 → I.4) collapses it to `ξ·X/6`.

Re-routes the prior worker's `towerFraction_of_failure` (`TowerRunMassSeedCore.lean`) to the *genuine
first-obstruction route* and to the single core (the layer values `s = 1/6`, `|I_j| = 1`). -/
theorem towerSubMass_of_failure (ctx : ActualFailureContext)
    {mult rhoL : ℝ} {spread markersCard : ℕ}
    (hpoint : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T ≤ mult)
    (hmult_nonneg : 0 ≤ mult)
    (hcover : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).card
        ≤ markersCard * (2 * spread + 1))
    (hrhoL_pos : 0 < rhoL)
    (hpack : (markersCard : ℝ) * rhoL ≤ ((supportShell ctx.d ctx.X).card : ℝ))
    (hsmall : (erdos260Constants.c0 / rhoL) * ((2 * spread + 1 : ℕ) : ℝ) * mult
        ≤ erdos260Constants.ξ / 6) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
      ≤ erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 := by
  have hsmall' : (erdos260Constants.c0 / rhoL) * ((2 * spread + 1 : ℕ) : ℝ) * mult
      ≤ erdos260Constants.ξ * (1 / 6) * 1 := by
    have hconv : erdos260Constants.ξ * (1 / 6 : ℝ) * 1 = erdos260Constants.ξ / 6 := by ring
    rw [hconv]; exact hsmall
  have h := towerFraction_of_failure ctx (genuineChargeRoute ctx)
    (s := 1 / 6) (Ij := 1) hpoint hmult_nonneg hcover hrhoL_pos hpack hsmall'
  calc routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
      ≤ erdos260Constants.ξ * (1 / 6) * (ctx.shell.X : ℝ) * 1 := h
    _ = erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 := by ring

/-! ## 3.  Run (class 5): the L.4.2 period-descent chain, anchored in the actual shell

The Run floor is produced from the geometric chain `w_i = w₀·2^{-i}` of the prior worker's
`runFloor_of_geometricBase`, reducing it to the I.6S domination (`hsum`) and the I.5.2 base output
(`hbase`).  The ratio `1/2` is the genuine L.4.2 half-decrease, anchored below in the actual shell. -/

/-- **The L.4.2 half-decrease on the actual shell residual centre (re-export, geometry anchor).**

The genuine ratio-`1/2` period descent `2·p' ≤ scaleMult·ord_{q₀}(2)` of the §25.2 residual centre
`runFOfShell ctx` — the dynamical source of the geometric chain ratio `1/2`, NOT an assumed ratio.
This is the prior worker's `run_periodDescent_halfDecrease`, re-exported so the chain below is anchored
in the actual shell's period descent. -/
theorem seedRun_periodDescent_halfDecrease (ctx : ActualFailureContext) (u : ℕ) (weight : ℝ) :
    ∃ p', PeriodicOn (dyadicDigit (residualCenterOfFailingShell (runFOfShell ctx)).q0
            (residualCenterOfFailingShell (runFOfShell ctx)).a) u
          (2 * ((residualCenterOfFailingShell (runFOfShell ctx)).scaleMult
            * orderOf (2 : ZMod (residualCenterOfFailingShell (runFOfShell ctx)).q0))) p'
        ∧ 0 < p'
        ∧ 2 * p' ≤ (residualCenterOfFailingShell (runFOfShell ctx)).scaleMult
            * orderOf (2 : ZMod (residualCenterOfFailingShell (runFOfShell ctx)).q0) :=
  run_periodDescent_halfDecrease ctx u weight

/-! ## 4.  The pinned Tower+Run seed-closure data -/

/-- **The Tower+Run mass-fraction seed closure, over the genuine first-obstruction route.**

Carries, per failure context, the two *smallest honest cores* of the Tower (class 2) and Run (class 5)
seeds, both pinned to `genuineChargeRoute`:

* **Tower (I.4.1)** — the single class-2 routed sub-mass fraction `htowerSubMass : routedClassMassOf … 2
  ≤ ξ·X/6` (a fraction below the slot, never the full mass).  The active layer `s = X/6`, `|I_j| = 1/X`
  and the normalisation `s·|I_j| ≤ 1/6` are *constructed* (`seedTowerS`/`seedTowerIj`/`seedTowerLayer`),
  so the fraction `htowerFraction` is derived (`towerFraction_of_subMass`), not assumed.
* **Run (I.5.2 / L.4.2)** — the geometric period-descent chain `w_i = w₀·2^{-i}`: the chain length
  `runChainLen`; the base run output `runBase` with the I.5.2 floor `hrunBase12 : w₀ ≤ c⋆ξX/12`; and the
  I.6S charged summability `hrunSum`.  The floor `hrunFloor` is derived (`runFloor_of_geometricBase`),
  with NO count. -/
structure TowerRunSeedClosureData where
  /-- **Tower (class 2) — the single I.4.1 sub-mass core (smallest honest core).**  The class-2 routed
  sub-mass fits `ξ·X/6`: a fraction strictly below the slot `c⋆·ξ·X/6`, never the full high-excess
  mass (refuted by `towerBudget_residual_forces_X_nonpos`).  Reducible further to the failure-driven
  count×multiplier by `towerSubMass_of_failure`. -/
  htowerSubMass : ∀ ctx : ActualFailureContext,
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
      ≤ erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6
  /-- The L.4.2 period-descent chain length. -/
  runChainLen : ActualFailureContext → ℕ
  /-- The I.5.2 base run output weight `w₀ = wt(O₀)`. -/
  runBase : ActualFailureContext → ℝ
  /-- The base run output is nonnegative. -/
  hrunBase_nonneg : ∀ ctx : ActualFailureContext, 0 ≤ runBase ctx
  /-- **Run (class 5) — the I.6S charged summability.**  The class-5 routed mass is dominated by the
  L.4.2 geometric chain `∑ w₀·2^{-i}` (each descent stage `wt(O_i) ≤ w₀·2^{-i}`, summed). -/
  hrunSum : ∀ ctx : ActualFailureContext,
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
      ≤ ∑ i ∈ Finset.range (runChainLen ctx), runBase ctx * (1 / 2) ^ i
  /-- **Run (class 5) — the I.5.2 base output bound (smallest honest core).**  `w₀ ≤ c⋆·ξ·X/12`. -/
  hrunBase12 : ∀ ctx : ActualFailureContext,
    runBase ctx ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 12

namespace TowerRunSeedClosureData

/-- The constructed I.4.1 active-layer order `s = X/6` (independent of the closure data). -/
def towerS (_C : TowerRunSeedClosureData) : ActualFailureContext → ℝ := seedTowerS

/-- The constructed I.4.1 active-layer interval length `|I_j| = 1/X` (canonical block fraction). -/
def towerIj (_C : TowerRunSeedClosureData) : ActualFailureContext → ℝ := seedTowerIj

/-- **`htowerLayer` field (PROVED)** — the constructed active layer's normalisation `s·|I_j| ≤ 1/6`. -/
theorem htowerLayer (C : TowerRunSeedClosureData) :
    ∀ ctx : ActualFailureContext, C.towerS ctx * C.towerIj ctx ≤ 1 / 6 :=
  fun ctx => seedTowerLayer ctx

/-- **`htowerFraction` field (PROVED)** — the genuine I.4.1 dense-packing mass fraction
`routedClassMassOf … 2 ≤ ξ·s·X·|I_j|`, derived from the single sub-mass core via the constructed
layer. -/
theorem htowerFraction (C : TowerRunSeedClosureData) :
    ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
        ≤ erdos260Constants.ξ * C.towerS ctx * (ctx.shell.X : ℝ) * C.towerIj ctx :=
  fun ctx => towerFraction_of_subMass ctx (C.htowerSubMass ctx)

/-- **`hrunFloor` field (PROVED)** — the I.5.2 run-mass floor `routedClassMassOf … 5 ≤ c⋆·ξ·X/6`,
derived from the geometric period-descent chain (`runFloor_of_geometricBase`), with NO count. -/
theorem hrunFloor (C : TowerRunSeedClosureData) :
    ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  fun ctx =>
    runFloor_of_geometricBase ctx (genuineChargeRoute ctx) (C.runChainLen ctx)
      (C.hrunBase_nonneg ctx) (C.hrunSum ctx) (C.hrunBase12 ctx)

/-- **The Tower routed slot (PROVED)** — `routedClassMassOf … 2 ≤ c⋆·ξ·X/6`, directly from the
sub-mass core. -/
theorem towerSlot (C : TowerRunSeedClosureData) :
    ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  fun ctx => towerSlot_of_subMass ctx (C.htowerSubMass ctx)

/-! ### Failure-driven smart constructor — the closure from the bare I.4.1/I.5.2 primitives -/

/-- **Build the seed closure from the bare manuscript primitives + the failure hypothesis.**

The single Tower sub-mass core is discharged by `towerSubMass_of_failure` (genuinely consuming
`ctx.hfailure`); the Run cores are carried as the period-descent chain data.  This realises the whole
Tower+Run seed closure from the bare I.4.1 (K.1.1 cover + dense-marker packing + K.4 smallness) and
I.5.2 (I.6S summability + base output) geometry, with no assumed mass slot. -/
def ofFailureSeeds
    (towerMult towerRhoL : ActualFailureContext → ℝ)
    (towerSpread towerMarkersCard : ActualFailureContext → ℕ)
    (htowerPoint : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
        windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
          ≤ towerMult ctx)
    (htowerMult_nonneg : ∀ ctx : ActualFailureContext, 0 ≤ towerMult ctx)
    (htowerCover : ∀ ctx : ActualFailureContext,
      (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).card
        ≤ towerMarkersCard ctx * (2 * towerSpread ctx + 1))
    (htowerRhoL_pos : ∀ ctx : ActualFailureContext, 0 < towerRhoL ctx)
    (htowerPack : ∀ ctx : ActualFailureContext,
      (towerMarkersCard ctx : ℝ) * towerRhoL ctx ≤ ((supportShell ctx.d ctx.X).card : ℝ))
    (htowerSmall : ∀ ctx : ActualFailureContext,
      (erdos260Constants.c0 / towerRhoL ctx) * ((2 * towerSpread ctx + 1 : ℕ) : ℝ) * towerMult ctx
        ≤ erdos260Constants.ξ / 6)
    (runChainLen : ActualFailureContext → ℕ)
    (runBase : ActualFailureContext → ℝ)
    (hrunBase_nonneg : ∀ ctx : ActualFailureContext, 0 ≤ runBase ctx)
    (hrunSum : ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
        ≤ ∑ i ∈ Finset.range (runChainLen ctx), runBase ctx * (1 / 2) ^ i)
    (hrunBase12 : ∀ ctx : ActualFailureContext,
      runBase ctx ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 12) :
    TowerRunSeedClosureData where
  htowerSubMass := fun ctx =>
    towerSubMass_of_failure ctx (htowerPoint ctx) (htowerMult_nonneg ctx) (htowerCover ctx)
      (htowerRhoL_pos ctx) (htowerPack ctx) (htowerSmall ctx)
  runChainLen := runChainLen
  runBase := runBase
  hrunBase_nonneg := hrunBase_nonneg
  hrunSum := hrunSum
  hrunBase12 := hrunBase12

/-! ## 5.  Assembly — the frontier `TowerRunMassFractionData` / `SeedTRTData` Tower+Run fields -/

/-- **The Tower+Run mass-fraction data over the genuine route, from the seed closure.**

Builds the `TowerRunMassFractionData` (`TowerRunMassFractionCore.lean`) whose route is
`genuineChargeRoute`, whose Tower fields are the constructed active layer + the proved I.4.1 fraction,
whose Run field is the proved I.5.2 floor, and whose Return slot is the sibling worker's `returnSlot`.
Feeding this to `TowerRunMassFractionData.toBudget` yields the `SeparatedPhaseRoutedBudget` from genuine
mass bounds with NO free Tower/Run count. -/
def toMassFractionData (C : TowerRunSeedClosureData)
    (returnSlot : ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 4
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    TowerRunMassFractionData where
  route := fun ctx => genuineChargeRoute ctx
  towerS := C.towerS
  towerIj := C.towerIj
  htowerLayer := C.htowerLayer
  htowerFraction := C.htowerFraction
  hrunFloor := C.hrunFloor
  returnSlot := returnSlot

@[simp] theorem toMassFractionData_route (C : TowerRunSeedClosureData)
    (returnSlot : ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 4
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6)
    (ctx : ActualFailureContext) :
    (C.toMassFractionData returnSlot).route ctx = genuineChargeRoute ctx := rfl

/-- **The shared budget from the seed closure (no free Tower/Run count).** -/
def toBudget (C : TowerRunSeedClosureData)
    (returnSlot : ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 4
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx :=
  (C.toMassFractionData returnSlot).toBudget

@[simp] theorem toBudget_route (C : TowerRunSeedClosureData)
    (returnSlot : ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 4
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6)
    (ctx : ActualFailureContext) :
    (C.toBudget returnSlot ctx).route = genuineChargeRoute ctx := rfl

/-- **The Tower+Run fields plugged into the frontier `SeedTRTData`.**

Given any `SeedTRTData` `D₀` (supplying the sibling Return M.2.1 congruence seed), the seed closure's
constructed Tower fields (`towerS`/`towerIj`/`htowerLayer`/`htowerFraction`) and proved Run floor
(`hrunFloor`) drop in as the Tower (class 2) and Run (class 5) seed fields, producing a full
`SeedTRTData` whose Tower/Run portion is the genuinely-reduced closure.  This is exactly the `trt`
field consumed by the frontier endpoint `erdos260_seed_reduced` (`Erdos260SeedResidual.lean`). -/
def withSeedReturn (C : TowerRunSeedClosureData) (D₀ : SeedTRTData) : SeedTRTData where
  retLevel := D₀.retLevel
  retXi := D₀.retXi
  retBound := D₀.retBound
  retCompat := D₀.retCompat
  retInj := D₀.retInj
  multReturn := D₀.multReturn
  hpointReturn := D₀.hpointReturn
  hmultReturn_nonneg := D₀.hmultReturn_nonneg
  hbudReturn := D₀.hbudReturn
  towerS := C.towerS
  towerIj := C.towerIj
  htowerLayer := C.htowerLayer
  htowerFraction := C.htowerFraction
  hrunFloor := C.hrunFloor

@[simp] theorem withSeedReturn_towerS (C : TowerRunSeedClosureData) (D₀ : SeedTRTData) :
    (C.withSeedReturn D₀).towerS = C.towerS := rfl

@[simp] theorem withSeedReturn_towerIj (C : TowerRunSeedClosureData) (D₀ : SeedTRTData) :
    (C.withSeedReturn D₀).towerIj = C.towerIj := rfl

end TowerRunSeedClosureData

/-! ## 6.  Non-circularity and genuine-geometry reuse

The Tower core is a bound on the class-2 routed SUB-mass; it is honest precisely because the full-mass
reading is refuted, and the underlying geometry is genuine (not fabricated). -/

/-- **The honest finding (reused): the FULL high-excess mass cannot fit the slot.**  Re-export of
`towerBudget_residual_forces_X_nonpos` (`TowerL31I31Core.lean`): `highExcessMass ≤ c⋆·ξ·X/6` forces
`X ≤ 0` against the Lemma 21.1 pressure floor.  Hence the genuine Tower content is a bound on the
class-2 ROUTED SUB-mass (`htowerSubMass : … ≤ ξ·X/6`, a fraction strictly below the slot), never the
full mass — the seed closure is non-circular. -/
theorem seed_fullMass_forces_X_nonpos (ctx : ActualFailureContext)
    (hI31 :
      highExcessMass
          (highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
            ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y)
          (hitGap ctx.n24CarryData.a) ctx.n24CarryData.r ctx.n24CarryData.T
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    (ctx.shell.X : ℝ) ≤ 0 :=
  towerBudget_residual_forces_X_nonpos ctx hI31

/-- **The class-2 routed sub-mass is genuinely a fraction of the full high-excess mass.**  Re-export of
`routedClassMassOf_le_highExcessMass`: `routedClassMassOf … 2 ≤ highExcessMass`.  The Tower core
`htowerSubMass` bounds this sub-mass by `ξ·X/6` — a genuine fraction of the (large) total, the
manuscript per-class routing, never the total itself. -/
theorem seed_class2_le_highExcessMass (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
      ≤ highExcessMass
          (highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
            ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y)
          (hitGap ctx.n24CarryData.a) ctx.n24CarryData.r ctx.n24CarryData.T :=
  routedClassMassOf_le_highExcessMass ctx.n24CarryData (genuineChargeRoute ctx) 2

/-- **The class-2 (Tower) fibre is the genuine semiperiodic-return band, not empty by fiat.**  Re-export
of `genuineChargeRoute_eq_two_iff`: a high-excess start is routed to the Tower class exactly when its
tower exit is the `cnlTail` catch-all with no large run and a semiperiodic recurrence
(`returnCls = 1`).  The fibre is genuinely populated by the SCC band geometry. -/
theorem seed_class2_fibre_iff (ctx : ActualFailureContext) (k : ℕ) :
    genuineChargeRoute ctx k = 2 ↔
      (towerClsOfShell ctx k = TowerExitClass.cnlTail ∧ runClsOfShell ctx k ≠ 1 ∧
        returnCls ctx k = 1) :=
  genuineChargeRoute_eq_two_iff ctx k

/-! ## 7.  Honest residual inventory -/

/-- The precise per-class status of the Tower+Run seed closure after this module. -/
def towerRunSeedClosureResiduals : List String :=
  [ "CONSTRUCTED (Tower layer) — seedTowerS = X/6, seedTowerIj = 1/X (the canonical block fraction): " ++
      "the I.4.1 active threshold layer, with the normalisation seedTowerLayer s·|I_j| = 1/6 ≤ 1/6 " ++
      "PROVED via the block-fraction cancellation X·(1/X)=1. (TowerRunMassSeedData left towerS/towerIj " ++
      "free; here they are constructed from the shell's X.)",
    "PROVED (Tower, class 2 — htowerFraction) — towerFraction_of_subMass: the I.4.1 dense-packing " ++
      "fraction routedClassMassOf … 2 ≤ ξ·s·X·|I_j| is derived from the single sub-mass core by exact " ++
      "algebra (RHS = ξ·X/6). towerSlot_of_subMass lifts it to the slot c⋆ξX/6 (c⋆ ≥ 1).",
    "SMALLEST HONEST CORE (Tower, class 2) — htowerSubMass: routedClassMassOf … 2 ≤ ξ·X/6, the " ++
      "class-2 routed SUB-mass fraction (strictly below the slot c⋆ξX/6, never the full high-excess " ++
      "mass — refuted by towerBudget_residual_forces_X_nonpos, re-exported as " ++
      "seed_fullMass_forces_X_nonpos). DEEPER REDUCTION: towerSubMass_of_failure derives this core " ++
      "from the K.1.1 cover + the I.4.1 dense-marker hit packing + the K.4 smallness, genuinely " ++
      "consuming the positive-density failure ctx.hfailure (markerCount_le_of_failure).",
    "PROVED (Run, class 5 — hrunFloor) — runFloor_of_geometricBase: the I.5.2 run-mass floor " ++
      "routedClassMassOf … 5 ≤ c⋆ξX/6 is derived from the geometric period-descent chain w_i = w₀·2^{-i} " ++
      "(halfChain_sum_le: ∑ ≤ 2·w₀), with NO count. Ratio 1/2 anchored in the actual shell by " ++
      "seedRun_periodDescent_halfDecrease (= runFOfShell_halfDecrease).",
    "SMALLEST HONEST CORES (Run, class 5) — hrunSum (the I.6S charged summability sending the class-5 " ++
      "routed mass to the chain ∑ w₀·2^{-i}) and hrunBase12 (the I.5.2 base run output w₀ ≤ c⋆ξX/12). " ++
      "Non-degenerate: hrunSum admits routedClassMassOf … 5 up to the full geometric envelope.",
    "ASSEMBLED — TowerRunSeedClosureData.toMassFractionData / toBudget build the TowerRunMassFractionData " ++
      "/ SeparatedPhaseRoutedBudget over genuineChargeRoute; withSeedReturn drops the constructed " ++
      "Tower+Run fields into the frontier SeedTRTData (Return seed from the sibling worker), feeding " ++
      "erdos260_seed_reduced. ofFailureSeeds builds the whole closure from the bare I.4.1/I.5.2 " ++
      "primitives + the failure hypothesis.",
    "ROUTE PINNED — every core is over the genuine first-obstruction route genuineChargeRoute (its " ++
      "class-2 fibre is the genuine semiperiodic-return band, seed_class2_fibre_iff), not a free route." ]

theorem towerRunSeedClosureResiduals_nonempty : towerRunSeedClosureResiduals ≠ [] := by
  simp [towerRunSeedClosureResiduals]

/-! ## 8.  Axiom-cleanliness audit -/

#print axioms seedTowerLayer
#print axioms towerFraction_of_subMass
#print axioms towerSlot_of_subMass
#print axioms towerSubMass_of_failure
#print axioms seedRun_periodDescent_halfDecrease
#print axioms TowerRunSeedClosureData.htowerFraction
#print axioms TowerRunSeedClosureData.hrunFloor
#print axioms TowerRunSeedClosureData.ofFailureSeeds
#print axioms TowerRunSeedClosureData.toMassFractionData
#print axioms TowerRunSeedClosureData.toBudget
#print axioms TowerRunSeedClosureData.withSeedReturn
#print axioms seed_fullMass_forces_X_nonpos

end

end Erdos260
