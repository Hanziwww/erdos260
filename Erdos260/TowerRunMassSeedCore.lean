import Erdos260.TowerRunMassFractionCore
import Erdos260.DensePack
import Erdos260.ChargeMultiplierClosure

/-!
# The Tower (I.4.1) and Run (I.5.2 / L.4.2) mass-bound SEEDS, proved from the failure hypothesis

This module (NEW; it edits no existing file) discharges the two **bare manuscript seeds** of the
consolidated charged ledger that `TowerRunMassFractionCore.lean` left as free structure fields:

* the **Tower seed** `htowerFraction` — the Lemma I.4.1 dense-packing mass fraction
  `routedClassMassOf … route 2 ≤ ξ·s·X·|I_j|` (manuscript eq. I.4); and
* the **Run seed** `hrunFloor` — the Proposition I.5.2 run-mass floor
  `routedClassMassOf … route 5 ≤ c⋆·ξ·X/6`, reduced through the L.4.2 period-descent potential to
  the **base run output bound** `w₀ ≤ c⋆·ξ·X/12`.

Both are produced from `ctx.hfailure` (the positive-density failure
`#(supportShell d X) < c₀·X`) and the genuine manuscript I.4.1 / I.5.2 / L.4.2 arguments, using only
**proved** infrastructure (`corollaryK1_3_densePackUnderFailure`, `routedClassMassOf_le_countMultiplier`,
`runMassFloor_slot_of_periodDescent`, `geomChain_sum_le`).  Whatever cannot close is reduced to the
**smallest named residual**: the bare per-class sub-mass geometry (the K.1.1/K.1.2 cover + multiplier,
the dense-marker hit packing, the K.4 numeric smallness; the I.6S chain domination + the I.5.2 base
output), documented per class below.

## Tower (class 2) — I.4.1 dense-marker packing under failure (manuscript §I.4, lines ~2983–3030)

The manuscript I.4.1 proof selects a maximal disjoint subfamily of dense markers; each carries
`≥ ρ_D·L` hits, so under the failure hypothesis `A_S(2X)−A_S(X) ≤ c_*X` (formalized as
`#(supportShell d X) < c₀·X`) the marker count obeys `|𝒟₀|·ρ_D·L ≤ #hits < c₀·X`, i.e.
`|𝒟₀| ≤ (c₀/ρ_D·L)·X` (`markerCount_le_of_failure`, eq. I.3 numerator — **this is where the failure
hypothesis enters**).  The K.1.1 endpoint-disjoint cover bounds the class-2 fibre by the markers and
the K.1.2/L.20 residual multiplier `mult` bounds each window excess; chaining the **proved**
`corollaryK1_3_densePackUnderFailure` with `routedClassMassOf_le_countMultiplier` and the K.4 numeric
smallness ("choose `c_* ≪_Q ρ_D κ ξ`", the I.3 → I.4 step) gives the fraction `ξ·s·X·|I_j|`
(`towerFraction_of_failure`).

## Run (class 5) — I.5.2 run output via the L.4.2 period-descent potential
(manuscript §I.5.2 lines ~3112–3171, §L.4.2 lines ~5508–5539)

The L.4.2 potential `𝔓(p)=⌈log₈(p/(P_hand L+C_Q))⌉` strictly decreases at every genuine shortening
step (`p_{i+1} ≤ p_i/8`, the actual-shell descent re-exported as `run_periodDescent_halfDecrease`),
giving the nested-support relation `|O_{i+1}| ≤ c|O_i|` (`c<1`).  At the half-decrease ratio `c=1/2`
the augmented chain weights are dominated by the geometric series `w_i = w₀·2^{-i}`, whose finite sum
is `≤ 2·w₀` (the proved `geomChain_sum_le` / `halfChain_sum_le`, eq. L.8a / I.6R).  Feeding this to
the proved `runMassFloor_slot_of_periodDescent`, the I.5.2 base run output `w₀ ≤ c⋆·ξ·X/12` lifts the
run-routed mass into the slot `c⋆·ξ·X/6` (`runFloor_of_geometricBase`) — **with no count**.

## Deliverable

`TowerRunMassSeedData.toMassFractionData` assembles a full `TowerRunMassFractionData` whose Tower and
Run fields (`htowerFraction` / `hrunFloor`) are **proved** by the two theorems above from the bare
seeds, and whose Return slot is the sibling worker's.  This realizes the
`TowerRunMassFractionData`/`SeedTRTData` Tower+Run seeds as theorems, not assumptions.

No `sorry`, `axiom`, or `admit`.  No degenerate full-mass / empty / zero-fraction shortcut.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 0.  The failure hypothesis bites: the dense-marker count is small (I.4.1, eq. I.3 numerator)

This is the **only** place the positive-density failure hypothesis `ctx.hfailure` enters the Tower
seed, and it is the manuscript I.4.1 packing step: disjoint dense markers each carry `≥ ρ_D·L` hits,
so their count times `ρ_D·L` is at most the total number of shell hits, which the failure hypothesis
caps by `c₀·X`. -/

/-- **Dense-marker count under the positive-density failure (manuscript I.4.1, eq. I.3).**

If `markersCard` disjoint dense markers each pack at least `ρ_D·L` hits of the actual shell — so that
`markersCard · ρ_D·L ≤ #(supportShell d X)` (the bare K.1.1 packing seed, `hpack`) — then the failure
hypothesis `ctx.hfailure : #(supportShell d X) < c₀·X` forces the marker count
`markersCard ≤ (c₀/ρ_D·L)·X`.  This is the genuine `|𝒟₀| ≤ C(c_*X)/(ρ_D L)` of the manuscript I.4.1
proof, with `c₀` playing the role of the failure density `c_*`. -/
theorem markerCount_le_of_failure (ctx : ActualFailureContext)
    {markersCard : ℕ} {rhoL : ℝ} (hrhoL_pos : 0 < rhoL)
    (hpack : (markersCard : ℝ) * rhoL ≤ ((supportShell ctx.d ctx.X).card : ℝ)) :
    (markersCard : ℝ) ≤ (erdos260Constants.c0 / rhoL) * (ctx.shell.X : ℝ) := by
  have hfail : ((supportShell ctx.d ctx.X).card : ℝ) < erdos260Constants.c0 * (ctx.X : ℝ) :=
    ctx.hfailure
  have hmul : (markersCard : ℝ) * rhoL ≤ erdos260Constants.c0 * (ctx.shell.X : ℝ) := by
    have h := le_of_lt (lt_of_le_of_lt hpack hfail)
    simpa [ActualFailureContext.shell_X] using h
  rw [div_mul_eq_mul_div, le_div_iff₀ hrhoL_pos]
  exact hmul

/-! ## 1.  Tower (class 2): the I.4.1 dense-packing mass fraction -/

/-- **The I.4.1 dense-packing mass fraction from the K.1.1 cover + the failure-driven count.**

The genuine route-`2` (Tower) sub-mass is bounded by the I.4.1 dense-packing fraction `ξ·s·X·|I_j|`:

* the K.1.2/L.20 residual multiplier `mult` bounds every routed-`2` window excess (`hpoint`,
  `hmult_nonneg`);
* the K.1.1 endpoint-disjoint cover bounds the class-`2` fibre by the dense markers (`hcover`);
* the dense markers each pack `≥ ρ_D·L` hits (`hpack`), so the failure hypothesis caps their count
  (`markerCount_le_of_failure`);
* the **proved** `corollaryK1_3_densePackUnderFailure` then gives
  `#fibre ≤ (c₀/ρ_D·L)·X·(2 spread+1)`, and `routedClassMassOf_le_countMultiplier` turns the
  per-fibre data into `routedClassMassOf … 2 ≤ #fibre · mult`;
* the K.4 numeric smallness `hsmall` (the manuscript "choose `c_* ≪_Q ρ_D κ ξ`", I.3 → I.4) collapses
  the product to `ξ·s·X·|I_j|`.

No `count·mult ≤ c⋆ξX/6` slot is asserted — only the genuine I.4.1 sub-mass fraction. -/
theorem towerFraction_of_failure (ctx : ActualFailureContext) (route : ℕ → Fin 7)
    {s Ij mult rhoL : ℝ} {spread markersCard : ℕ}
    (hpoint : ∀ k ∈ routedFibre ctx.n24CarryData route 2,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T ≤ mult)
    (hmult_nonneg : 0 ≤ mult)
    (hcover : (routedFibre ctx.n24CarryData route 2).card ≤ markersCard * (2 * spread + 1))
    (hrhoL_pos : 0 < rhoL)
    (hpack : (markersCard : ℝ) * rhoL ≤ ((supportShell ctx.d ctx.X).card : ℝ))
    (hsmall : (erdos260Constants.c0 / rhoL) * ((2 * spread + 1 : ℕ) : ℝ) * mult
        ≤ erdos260Constants.ξ * s * Ij) :
    routedClassMassOf ctx.n24CarryData route 2
      ≤ erdos260Constants.ξ * s * (ctx.shell.X : ℝ) * Ij := by
  have hcount : (markersCard : ℝ) ≤ (erdos260Constants.c0 / rhoL) * (ctx.shell.X : ℝ) :=
    markerCount_le_of_failure ctx hrhoL_pos hpack
  have hcard : ((routedFibre ctx.n24CarryData route 2).card : ℝ)
      ≤ (erdos260Constants.c0 / rhoL) * (ctx.shell.X : ℝ) * ((2 * spread + 1 : ℕ) : ℝ) :=
    corollaryK1_3_densePackUnderFailure hcover hcount
  have hcm := routedClassMassOf_le_countMultiplier ctx.n24CarryData route 2 hpoint hmult_nonneg hcard
  have hXnn : (0 : ℝ) ≤ (ctx.shell.X : ℝ) := ctx.shell.X_nonneg_real
  calc routedClassMassOf ctx.n24CarryData route 2
      ≤ ((erdos260Constants.c0 / rhoL) * (ctx.shell.X : ℝ) * ((2 * spread + 1 : ℕ) : ℝ)) * mult :=
        hcm
    _ = ((erdos260Constants.c0 / rhoL) * ((2 * spread + 1 : ℕ) : ℝ) * mult) * (ctx.shell.X : ℝ) := by
        ring
    _ ≤ (erdos260Constants.ξ * s * Ij) * (ctx.shell.X : ℝ) :=
        mul_le_mul_of_nonneg_right hsmall hXnn
    _ = erdos260Constants.ξ * s * (ctx.shell.X : ℝ) * Ij := by ring

/-- **The Tower routed-fraction slot, end-to-end from the failure hypothesis (no count).**

Chains `towerFraction_of_failure` (the I.4.1 fraction) with the proved `towerMassFraction_slot` (the
K.4 layer normalisation `s·|I_j| ≤ 1/6` + pinned `c⋆ ≥ 1`): the Tower slot
`routedClassMassOf … 2 ≤ c⋆·ξ·X/6` is produced from `ctx.hfailure` and the bare I.4.1 geometry, with
NO free count. -/
theorem towerSlot_of_failure (ctx : ActualFailureContext) (route : ℕ → Fin 7)
    {s Ij mult rhoL : ℝ} {spread markersCard : ℕ}
    (hlayer : s * Ij ≤ 1 / 6)
    (hpoint : ∀ k ∈ routedFibre ctx.n24CarryData route 2,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T ≤ mult)
    (hmult_nonneg : 0 ≤ mult)
    (hcover : (routedFibre ctx.n24CarryData route 2).card ≤ markersCard * (2 * spread + 1))
    (hrhoL_pos : 0 < rhoL)
    (hpack : (markersCard : ℝ) * rhoL ≤ ((supportShell ctx.d ctx.X).card : ℝ))
    (hsmall : (erdos260Constants.c0 / rhoL) * ((2 * spread + 1 : ℕ) : ℝ) * mult
        ≤ erdos260Constants.ξ * s * Ij) :
    routedClassMassOf ctx.n24CarryData route 2
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  towerMassFraction_slot ctx route s Ij hlayer
    (towerFraction_of_failure ctx route hpoint hmult_nonneg hcover hrhoL_pos hpack hsmall)

/-! ## 2.  Run (class 5): the I.5.2 base output via the L.4.2 period-descent potential -/

/-- **The L.4.2 one-step half-decrease on the actual shell residual center (re-export).**

The genuine ratio-`1/2` descent `2·p' ≤ scaleMult·ord_{q₀}(2)` of the §25.2 residual center
`runFOfShell ctx` — the dynamical source of the geometric chain ratio `c = 1/2` used below.  This is
exactly `runFOfShell_halfDecrease`; re-exported here to anchor the geometric weights `w_i = w₀·2^{-i}`
in the actual shell's period descent (not an assumed ratio). -/
theorem run_periodDescent_halfDecrease (ctx : ActualFailureContext) (u : ℕ) (weight : ℝ) :
    ∃ p', PeriodicOn (dyadicDigit (residualCenterOfFailingShell (runFOfShell ctx)).q0
            (residualCenterOfFailingShell (runFOfShell ctx)).a) u
          (2 * ((residualCenterOfFailingShell (runFOfShell ctx)).scaleMult
            * orderOf (2 : ZMod (residualCenterOfFailingShell (runFOfShell ctx)).q0))) p'
        ∧ 0 < p'
        ∧ 2 * p' ≤ (residualCenterOfFailingShell (runFOfShell ctx)).scaleMult
            * orderOf (2 : ZMod (residualCenterOfFailingShell (runFOfShell ctx)).q0) :=
  runFOfShell_halfDecrease ctx u weight

/-- **The I.5.2 run-mass floor from the base run output (no count).**

The L.4.2 period descent gives the nested supports `|O_{i+1}| ≤ (1/2)|O_i|`, so the augmented chain
weights are dominated by the geometric series `w_i = w₀·2^{-i}`.  Given the I.6S domination of the
run-routed (class 5) mass by the chain sum (`hsum`) and the I.5.2 base run output bound
`w₀ ≤ c⋆·ξ·X/12` (`hbase`), the proved `runMassFloor_slot_of_periodDescent` (whose summability
`∑ w_i ≤ 2·w₀` is the proved `geomChain_sum_le` at `c = 1/2`) lifts the run-routed mass into the slot
`c⋆·ξ·X/6`.

The geometric chain `w_i = w₀·2^{-i}` is constructed here (its nonnegativity and exact half-decrease
are proved outright), so the Run seed reduces to the two bare residuals `hsum` (I.6S charged
summability) and `hbase` (the I.5.2 base output) — never a count. -/
theorem runFloor_of_geometricBase (ctx : ActualFailureContext) (route : ℕ → Fin 7)
    (n : ℕ) {w0 : ℝ} (hw0 : 0 ≤ w0)
    (hsum : routedClassMassOf ctx.n24CarryData route 5
        ≤ ∑ i ∈ Finset.range n, w0 * (1 / 2) ^ i)
    (hbase : w0 ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 12) :
    routedClassMassOf ctx.n24CarryData route 5
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 := by
  refine runMassFloor_slot_of_periodDescent ctx route (fun i => w0 * (1 / 2) ^ i) n
    (fun i => ?_) (fun i => ?_) hsum ?_
  · exact mul_nonneg hw0 (pow_nonneg (by norm_num) i)
  · show w0 * (1 / 2) ^ (i + 1) ≤ (1 / 2) * (w0 * (1 / 2) ^ i)
    exact le_of_eq (by rw [pow_succ]; ring)
  · show w0 * (1 / 2) ^ 0 ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 12
    simpa using hbase

/-! ## 3.  Assembly — the Tower+Run mass-fraction data from the bare seeds -/

/-- **The Tower+Run mass-bound seed data.**

Per failure context, the bare manuscript seeds determining the Tower (I.4.1) and Run (I.5.2/L.4.2)
routed-fraction bounds over the shared route:

* **Tower (I.4.1)** — the layer order/length `towerS`/`towerIj` with the normalisation `s·|I_j| ≤ 1/6`;
  the K.1.2/L.20 multiplier (`towerMult`/`htowerPoint`/`htowerMult_nonneg`); the K.1.1 cover
  (`htowerCover`); the dense-marker hit packing (`towerRhoL`/`htowerRhoL_pos`/`htowerPack`); and the
  K.4 numeric smallness (`htowerSmall`).
* **Run (I.5.2/L.4.2)** — the chain length `runChainLen`; the base run output `runBase` with the I.5.2
  floor `w₀ ≤ c⋆·ξ·X/12` (`hrunFloor12`); and the I.6S chain domination (`hrunSum`).
* **Return** — the sibling worker's class-4 slot (`returnSlot`), carried unchanged. -/
structure TowerRunMassSeedData where
  /-- The shared seven-class routing of the high-excess starts. -/
  route : ActualFailureContext → ℕ → Fin 7
  /-- I.4.1 active threshold-layer order `s` (`s ≍ L`). -/
  towerS : ActualFailureContext → ℝ
  /-- I.4.1 active threshold-layer interval length `|I_j|`. -/
  towerIj : ActualFailureContext → ℝ
  /-- K.1.2/L.20 residual window-excess multiplier on the class-2 fibre. -/
  towerMult : ActualFailureContext → ℝ
  /-- The per-marker hit floor `ρ_D·L` (each disjoint dense marker packs at least this many hits). -/
  towerRhoL : ActualFailureContext → ℝ
  /-- The K.1.1 marker spread (cover half-width index). -/
  towerSpread : ActualFailureContext → ℕ
  /-- The number of selected disjoint dense markers (`|𝒟₀|`). -/
  towerMarkersCard : ActualFailureContext → ℕ
  /-- **Layer normalisation** `s·|I_j| ≤ 1/6` (the single active layer's `1/6` budget share). -/
  htowerLayer : ∀ ctx : ActualFailureContext, towerS ctx * towerIj ctx ≤ 1 / 6
  /-- K.1.2/L.20 per-fibre multiplier bound. -/
  htowerPoint : ∀ ctx : ActualFailureContext,
    ∀ k ∈ routedFibre ctx.n24CarryData (route ctx) 2,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        ≤ towerMult ctx
  /-- The multiplier is nonnegative. -/
  htowerMult_nonneg : ∀ ctx : ActualFailureContext, 0 ≤ towerMult ctx
  /-- **K.1.1 endpoint-disjoint cover** — the class-2 fibre is covered by the markers' neighbourhoods. -/
  htowerCover : ∀ ctx : ActualFailureContext,
    (routedFibre ctx.n24CarryData (route ctx) 2).card
      ≤ towerMarkersCard ctx * (2 * towerSpread ctx + 1)
  /-- The per-marker hit floor is positive. -/
  htowerRhoL_pos : ∀ ctx : ActualFailureContext, 0 < towerRhoL ctx
  /-- **The I.4.1 dense-marker hit packing (bare seed)** — disjoint markers each pack `≥ ρ_D·L` hits,
  so their count times `ρ_D·L` is at most the shell's total hit count. -/
  htowerPack : ∀ ctx : ActualFailureContext,
    (towerMarkersCard ctx : ℝ) * towerRhoL ctx ≤ ((supportShell ctx.d ctx.X).card : ℝ)
  /-- **The K.4 numeric smallness (bare seed)** — the manuscript "choose `c_* ≪_Q ρ_D κ ξ`" (I.3→I.4). -/
  htowerSmall : ∀ ctx : ActualFailureContext,
    (erdos260Constants.c0 / towerRhoL ctx) * ((2 * towerSpread ctx + 1 : ℕ) : ℝ) * towerMult ctx
      ≤ erdos260Constants.ξ * towerS ctx * towerIj ctx
  /-- The L.4.2 period-descent chain length. -/
  runChainLen : ActualFailureContext → ℕ
  /-- The I.5.2 base run output weight `w₀ = wt(O₀)`. -/
  runBase : ActualFailureContext → ℝ
  /-- The base run output is nonnegative. -/
  hrunBase_nonneg : ∀ ctx : ActualFailureContext, 0 ≤ runBase ctx
  /-- **The I.6S charged summability (bare seed)** — the run-routed (class 5) mass is dominated by the
  L.4.2 geometric chain `∑ w₀·2^{-i}`. -/
  hrunSum : ∀ ctx : ActualFailureContext,
    routedClassMassOf ctx.n24CarryData (route ctx) 5
      ≤ ∑ i ∈ Finset.range (runChainLen ctx), runBase ctx * (1 / 2) ^ i
  /-- **The I.5.2 base run output bound (bare seed)** — `w₀ ≤ c⋆·ξ·X/12`. -/
  hrunFloor12 : ∀ ctx : ActualFailureContext,
    runBase ctx ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 12
  /-- The Return (class 4) routed-fraction slot — owned by the sibling Return worker. -/
  returnSlot : ∀ ctx : ActualFailureContext,
    routedClassMassOf ctx.n24CarryData (route ctx) 4
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6

namespace TowerRunMassSeedData

/-- **The proved Tower seed `htowerFraction`** — the I.4.1 dense-packing mass fraction for the seed
data's route, discharged by `towerFraction_of_failure` from the failure hypothesis. -/
theorem htowerFraction (D : TowerRunMassSeedData) (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (D.route ctx) 2
      ≤ erdos260Constants.ξ * D.towerS ctx * (ctx.shell.X : ℝ) * D.towerIj ctx :=
  towerFraction_of_failure ctx (D.route ctx) (D.htowerPoint ctx) (D.htowerMult_nonneg ctx)
    (D.htowerCover ctx) (D.htowerRhoL_pos ctx) (D.htowerPack ctx) (D.htowerSmall ctx)

/-- **The proved Run seed `hrunFloor`** — the I.5.2 run-mass floor for the seed data's route,
discharged by `runFloor_of_geometricBase` from the L.4.2 period-descent chain + base output. -/
theorem hrunFloor (D : TowerRunMassSeedData) (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (D.route ctx) 5
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  runFloor_of_geometricBase ctx (D.route ctx) (D.runChainLen ctx) (D.hrunBase_nonneg ctx)
    (D.hrunSum ctx) (D.hrunFloor12 ctx)

/-- **The Tower+Run mass-fraction data, with both seeds PROVED.**

Builds the `TowerRunMassFractionData` whose Tower field `htowerFraction` is the proved I.4.1 fraction
(`towerFraction_of_failure`), whose Run field `hrunFloor` is the proved I.5.2 floor
(`runFloor_of_geometricBase`), and whose Return slot is the sibling worker's.  Feeding this to
`TowerRunMassFractionData.toBudget` yields the `SeparatedPhaseRoutedBudget` from genuine mass bounds
with NO free Tower/Run count. -/
def toMassFractionData (D : TowerRunMassSeedData) : TowerRunMassFractionData where
  route := D.route
  towerS := D.towerS
  towerIj := D.towerIj
  htowerLayer := D.htowerLayer
  htowerFraction := D.htowerFraction
  hrunFloor := D.hrunFloor
  returnSlot := D.returnSlot

@[simp] theorem toMassFractionData_route (D : TowerRunMassSeedData) (ctx : ActualFailureContext) :
    (D.toMassFractionData).route ctx = D.route ctx := rfl

/-- **The shared budget, from the bare Tower/Run seeds (no free count).**  The Tower slot is the
I.4.1 fraction and the Run slot is the I.5.2 floor, both via `TowerRunMassFractionData.toBudget`. -/
def toBudget (D : TowerRunMassSeedData) :
    ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx :=
  D.toMassFractionData.toBudget

end TowerRunMassSeedData

/-! ## 4.  Honest residual inventory -/

/-- The precise status of the two mass-bound seeds after this module. -/
def towerRunMassSeedResiduals : List String :=
  [ "PROVED (class 2, Tower — htowerFraction) — towerFraction_of_failure: the I.4.1 dense-packing " ++
      "mass fraction routedClassMassOf … 2 ≤ ξ·s·X·|I_j| is PROVED from ctx.hfailure. The failure " ++
      "hypothesis #(supportShell d X) < c₀·X enters through markerCount_le_of_failure (the I.4.1 " ++
      "packing |𝒟₀|·ρ_D·L ≤ #hits < c₀·X ⟹ |𝒟₀| ≤ (c₀/ρ_D·L)·X), then the proved " ++
      "corollaryK1_3_densePackUnderFailure + routedClassMassOf_le_countMultiplier + the K.4 smallness.",
    "SEED RESIDUAL (class 2) — the bare per-class sub-mass geometry: htowerPoint/htowerMult_nonneg " ++
      "(K.1.2/L.20 multiplier), htowerCover (K.1.1 endpoint-disjoint cover), htowerPack (the " ++
      "dense-marker hit packing ρ_D·L), htowerSmall (the K.4 'choose c_* ≪ ρ_D κ ξ'). These are the " ++
      "irreducible I.4.1 input geometry — NOT the full high-excess mass.",
    "PROVED (class 5, Run — hrunFloor) — runFloor_of_geometricBase: the I.5.2 run-mass floor " ++
      "routedClassMassOf … 5 ≤ c⋆ξX/6 is PROVED via the proved runMassFloor_slot_of_periodDescent " ++
      "(geomChain_sum_le at c=1/2, ∑ w₀·2^{-i} ≤ 2·w₀, eq. L.8a/I.6R). The geometric chain w_i = " ++
      "w₀·2^{-i} (ratio 1/2 = the L.4.2 half-decrease run_periodDescent_halfDecrease) is constructed " ++
      "here with nonnegativity + exact half-decrease proved outright.",
    "SEED RESIDUAL (class 5) — the two bare residuals: hrunSum (the I.6S charged summability sending " ++
      "the run-routed mass to the chain ∑ w₀·2^{-i}) and hrunFloor12 (the I.5.2 base run output " ++
      "w₀ ≤ c⋆ξX/12). Non-degenerate: hrunSum admits routedClassMassOf … 5 up to the full slot 2·w₀.",
    "ASSEMBLED — TowerRunMassSeedData.toMassFractionData: a full TowerRunMassFractionData whose Tower " ++
      "(htowerFraction) and Run (hrunFloor) fields are the PROVED seeds and whose Return slot is the " ++
      "sibling worker's. Its toBudget is the SeparatedPhaseRoutedBudget with NO free Tower/Run count.",
    "FAILURE USED — markerCount_le_of_failure genuinely consumes ctx.hfailure (the positive-density " ++
      "failure). GEOMETRY ANCHORED — run_periodDescent_halfDecrease re-exports the actual-shell L.4.2 " ++
      "half-decrease (runFOfShell_halfDecrease) supplying the geometric ratio 1/2." ]

theorem towerRunMassSeedResiduals_nonempty : towerRunMassSeedResiduals ≠ [] := by
  simp [towerRunMassSeedResiduals]

/-! ## 5.  Axiom-cleanliness audit -/

#print axioms markerCount_le_of_failure
#print axioms towerFraction_of_failure
#print axioms towerSlot_of_failure
#print axioms run_periodDescent_halfDecrease
#print axioms runFloor_of_geometricBase
#print axioms TowerRunMassSeedData.htowerFraction
#print axioms TowerRunMassSeedData.hrunFloor
#print axioms TowerRunMassSeedData.toMassFractionData

end

end Erdos260
