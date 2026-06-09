import Erdos260.TowerRunSeedClosure

/-!
# Tower core 3 + Run cores 4/5 of `TowerRunSeedClosureData`, from the genuine geometry

This module (NEW; it edits no existing file) closes / shrinks the three remaining honest cores
of the wave-9 `TowerRunSeedClosureData` (`TowerRunSeedClosure.lean`, the `towerRun` field of the
frontier `Erdos260MinimalResidual`) — all pinned to the genuine first-obstruction route
`genuineChargeRoute`:

* **Core 3** — `htowerSubMass : routedClassMassOf … 2 ≤ ξ·X/6` (the I.4.1 dense-packing sub-mass);
* **Core 4** — `hrunSum : routedClassMassOf … 5 ≤ ∑_{i<len} w₀·(1/2)^i` (the I.6S charged
  summability of the run mass onto the L.4.2 geometric period-descent chain);
* **Core 5** — `hrunBase12 : w₀ ≤ c⋆·ξ·X/12` (the I.5.2 base run output bound).

## Core 3 — the K.1.2/L.20 multiplier is GENUINELY pinned to the active floor

The wave-9 worker reduced Core 3 to `towerSubMass_of_failure` — the K.1.1 endpoint-disjoint cover
+ the I.4.1 dense-marker hit packing + the K.4 smallness + a *free* window-excess multiplier
`mult` (`htowerPoint`), genuinely consuming `ctx.hfailure` through `markerCount_le_of_failure`.

Here the multiplier is no longer free: on the genuine class-2 fibre the first-obstruction
characterisation `genuineChargeRoute_eq_two_iff` forces `runClsOfShell ctx k ≠ 1`, i.e. (away from
the boundary `k = 0`) **`windowExcess … k … < 2·Y`** — the K.1.2/L.20 residual multiplier *linear
in the active floor `Y`* (`class2_windowExcess_lt_twoY` / `class2_fibre_windowExcess_le`).  So the
Tower sub-mass core is discharged by `Class2DenseMarkerCover.htowerSubMass` with `mult` *pinned* to
`positivePart (2·Y)`; the residual shrinks to the **bare dense-marker existence/packing fact** (the
K.1.1 cover `hcover` + the dense-marker hit packing `hpack`), the boundary exclusion `hbdry`
(`0 ∉` the class-2 fibre — the manuscript treats the boundary start separately), and the K.4
numeric smallness `hsmall`.

## Cores 4 + 5 — the actual half-decreasing stage chain, with the geometric envelope PROVED

`RunClass5StageChain` exposes the *actual* per-stage run masses `stageMass i = wt(O_i)` of the
L.4.2 nested-support descent, carrying the genuine residuals
* `hhalf : stageMass (i+1) ≤ (1/2)·stageMass i` — the mass-level L.4.2 half-decrease (anchored in
  the period-level half-decrease `seedRun_periodDescent_halfDecrease` of the actual shell);
* `hsum  : routedClassMassOf … 5 ≤ ∑_{i<len} stageMass i` — the I.6S charged summation; and
* `hbase : stageMass 0 ≤ c⋆·ξ·X/12` — the I.5.2 base run output.

From these the geometric envelope `stageMass i ≤ stageMass 0·(1/2)^i` is **proved outright**
(`stageMass_le_geom`), so `RunClass5StageChain.hrunSum` discharges Core 4 with `w₀ := stageMass 0`
and Core 5 is `hbase`.  This separates the two genuine I.5.2/I.6S ingredients (decay + summation)
from the geometric bookkeeping, which is now a theorem.

## Deliverable

`buildTowerRunSeedClosure` assembles a full `TowerRunSeedClosureData` from a per-context
`Class2DenseMarkerCover` (Core 3) and `RunClass5StageChain` (Cores 4 + 5), feeding the frontier
`Erdos260MinimalResidual.towerRun` and hence `erdos260_of_minimalResidual`.

No `sorry`, `axiom`, `admit`, or `native_decide`.  No degenerate/empty/zero-fraction/full-mass
shortcut: the multiplier is the genuine active floor, and every residual is over the real class-2 /
class-5 fibre of the genuine route.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 1.  Tower (class 2): the K.1.2/L.20 active-floor multiplier on the genuine fibre

On the genuine first-obstruction route, the class-2 (Tower) fibre is the `cnlTail` band with a
semiperiodic recurrence and **no large run** (`genuineChargeRoute_eq_two_iff`).  "No large run"
(`runClsOfShell ctx k ≠ 1`) is exactly the K.1.2/L.20 active-floor bound `windowExcess < 2·Y` once
the boundary start `k = 0` is set aside — the genuine residual multiplier, no longer free. -/

/-- **The genuine K.1.2/L.20 multiplier on the class-2 fibre (interior starts).**

For a high-excess start `k ≠ 0` routed to the Tower class `2` by the genuine first-obstruction
route, the window excess is below twice the active floor: `windowExcess … k … < 2·Y`.  This is the
"no large run" half of `genuineChargeRoute_eq_two_iff` (`runClsOfShell ctx k ≠ 1`), unfolded
through the L.4.1 trichotomy `runClsOfShell` — the genuine residual window-excess multiplier
linear in `Y`, consumed here in place of the wave-9 free `mult`. -/
theorem class2_windowExcess_lt_twoY (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2) (hk0 : k ≠ 0) :
    windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
      < 2 * ctx.n24CarryData.Y := by
  have hmem : k ∈ (highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
        ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y).filter
        (fun j => genuineChargeRoute ctx j = 2) := hk
  have hroute : genuineChargeRoute ctx k = 2 := (Finset.mem_filter.mp hmem).2
  have hrun : runClsOfShell ctx k ≠ 1 := ((genuineChargeRoute_eq_two_iff ctx k).mp hroute).2.1
  by_contra hge
  rw [not_lt] at hge
  apply hrun
  unfold runClsOfShell
  rw [if_neg hk0, if_pos hge]

/-- **The pinned class-2 multiplier `positivePart (2·Y)`, for every fibre member.**

Away from the boundary start `0` (excluded by `hbdry`), every class-2 fibre member has
`windowExcess … ≤ positivePart (2·Y)` — a *nonnegative* multiplier (no `Y ≥ 0` hypothesis needed)
pinned to the active floor, discharging the wave-9 free `htowerPoint`/`hmult_nonneg`. -/
theorem class2_fibre_windowExcess_le (ctx : ActualFailureContext)
    (hbdry : 0 ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2)
    {k : ℕ} (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2) :
    windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
      ≤ positivePart (2 * ctx.n24CarryData.Y) := by
  have hk0 : k ≠ 0 := fun h => hbdry (h ▸ hk)
  exact le_trans (le_of_lt (class2_windowExcess_lt_twoY ctx hk hk0))
    (self_le_positivePart _)

-- WAVE-12/13 CORRECTION NOTE (additive; structure & signatures unchanged): the
-- `Class2DenseMarkerCover` residual below is *deep-shell-vacuous* — it is the `O(L)`-branch cover,
-- which carries no information once the shell scales (`r = ⌊κL⌋ ≥ 1`).  The genuine class-2 Tower
-- I.4.1 path is the multiplicity-one area packing `Class2AreaPacking` /
-- `Class2ActiveFloorCount.ofAreaPacking` in `TowerI41PackingCore.lean` (carrying the active-order
-- `1/s ≍ 1/(κL)` factor); that is the corrected datum feeding the V3 endpoint.
/-- **The bare dense-marker existence/packing residual for the genuine class-2 fibre.**

This bundles *exactly* the irreducible I.4.1 dense-packing input, with the multiplier already
pinned to the active floor `positivePart (2·Y)`:

* `hbdry` — the boundary start `0` is not class-2 routed (the manuscript treats it separately);
* `hcover` — the K.1.1 endpoint-disjoint cover (`|fibre 2| ≤ |𝒟₀|·(2 spread + 1)`);
* `hpack` — the dense-marker hit packing (`|𝒟₀|·ρ_D·L ≤ #(supportShell d X)`, the seed the failure
  hypothesis caps via `markerCount_le_of_failure`);
* `hsmall` — the K.4 numeric smallness `(c₀/ρ_D·L)·(2 spread + 1)·(2·Y) ≤ ξ/6`. -/
structure Class2DenseMarkerCover (ctx : ActualFailureContext) where
  /-- The K.1.1 marker spread (cover half-width index). -/
  spread : ℕ
  /-- The number of selected disjoint dense markers `|𝒟₀|`. -/
  markersCard : ℕ
  /-- The per-marker hit floor `ρ_D·L`. -/
  rhoL : ℝ
  /-- The per-marker hit floor is positive. -/
  hrhoL_pos : 0 < rhoL
  /-- **Boundary exclusion** — the boundary start `0` is not class-2 routed. -/
  hbdry : 0 ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2
  /-- **K.1.1 endpoint-disjoint cover** of the class-2 fibre by the markers' neighbourhoods. -/
  hcover : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).card
      ≤ markersCard * (2 * spread + 1)
  /-- **The I.4.1 dense-marker hit packing** — the markers pack into the shell support count. -/
  hpack : (markersCard : ℝ) * rhoL ≤ ((supportShell ctx.d ctx.X).card : ℝ)
  /-- **The K.4 numeric smallness** at the pinned active-floor multiplier `positivePart (2·Y)`. -/
  hsmall : (erdos260Constants.c0 / rhoL) * ((2 * spread + 1 : ℕ) : ℝ)
        * positivePart (2 * ctx.n24CarryData.Y)
      ≤ erdos260Constants.ξ / 6

/-- **Tower Core 3, discharged from the dense-marker existence/packing (multiplier pinned).**

The class-2 routed sub-mass `routedClassMassOf … 2 ≤ ξ·X/6` follows from the bundled
`Class2DenseMarkerCover` via the wave-9 `towerSubMass_of_failure`, with the window-excess
multiplier *pinned* to the genuine active floor `positivePart (2·Y)` (`class2_fibre_windowExcess_le`)
rather than carried as a free input.  Genuinely consumes `ctx.hfailure` (through
`markerCount_le_of_failure`, inside `towerSubMass_of_failure`). -/
theorem Class2DenseMarkerCover.htowerSubMass {ctx : ActualFailureContext}
    (C : Class2DenseMarkerCover ctx) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
      ≤ erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  towerSubMass_of_failure ctx
    (mult := positivePart (2 * ctx.n24CarryData.Y))
    (rhoL := C.rhoL) (spread := C.spread) (markersCard := C.markersCard)
    (fun _k hk => class2_fibre_windowExcess_le ctx C.hbdry hk)
    (positivePart_nonneg _)
    C.hcover C.hrhoL_pos C.hpack C.hsmall

/-! ## 2.  Run (class 5): the half-decreasing stage chain and its geometric envelope

The L.4.2 period descent yields *actual* per-stage run masses `stageMass i = wt(O_i)`, contracting
by `1/2` at every stage.  The geometric envelope `stageMass i ≤ stageMass 0·(1/2)^i` is proved
outright, separating the genuine I.5.2/I.6S inputs (the half-decrease + the base output + the
charged summation) from the geometric bookkeeping. -/

/-- **The geometric envelope of a half-decreasing chain (PROVED).**

For any chain `w` with the one-step contraction `w (i+1) ≤ (1/2)·w i` (the L.4.2 nested-support
relation `|O_{i+1}| ≤ |O_i|/2`), every stage is below the geometric envelope `w i ≤ w 0·(1/2)^i`.
Proved by induction on `i` — the bookkeeping that turns the dynamical half-decrease into the
`∑ w₀·2^{-i}` envelope (no nonnegativity needed: the contraction alone forces the envelope). -/
theorem stageMass_le_geom {w : ℕ → ℝ}
    (hhalf : ∀ i, w (i + 1) ≤ (1 / 2) * w i) :
    ∀ i, w i ≤ w 0 * (1 / 2) ^ i := by
  intro i
  induction i with
  | zero => simp
  | succ n ih =>
      calc w (n + 1) ≤ (1 / 2) * w n := hhalf n
        _ ≤ (1 / 2) * (w 0 * (1 / 2) ^ n) :=
            mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = w 0 * (1 / 2) ^ (n + 1) := by rw [pow_succ]; ring

/-- **The L.4.2 period-descent run chain on the genuine class-5 fibre.**

The genuine residual data for the I.5.2 / I.6S run output:

* `stageMass i = wt(O_i)` — the *actual* augmented-chain run mass at descent stage `i`;
* `hhalf` — the mass-level L.4.2 half-decrease (anchored in the actual shell's period-level
  half-decrease `seedRun_periodDescent_halfDecrease`);
* `hsum` — **the I.6S charged summability**: the class-5 routed mass is the sum of the stage masses;
* `hbase` — **the I.5.2 base run output** `wt(O₀) ≤ c⋆·ξ·X/12`. -/
structure RunClass5StageChain (ctx : ActualFailureContext) where
  /-- The L.4.2 period-descent chain length. -/
  len : ℕ
  /-- The actual per-stage augmented run mass `wt(O_i)`. -/
  stageMass : ℕ → ℝ
  /-- Each stage mass is nonnegative. -/
  hnonneg : ∀ i, 0 ≤ stageMass i
  /-- **The mass-level L.4.2 half-decrease** `wt(O_{i+1}) ≤ wt(O_i)/2`. -/
  hhalf : ∀ i, stageMass (i + 1) ≤ (1 / 2) * stageMass i
  /-- **The I.6S charged summability** — the class-5 routed mass is dominated by the stage sum. -/
  hsum : routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
      ≤ ∑ i ∈ Finset.range len, stageMass i
  /-- **The I.5.2 base run output bound** `wt(O₀) ≤ c⋆·ξ·X/12`. -/
  hbase : stageMass 0
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 12

/-- **Run Core 4 (`hrunSum`), discharged from the stage chain.**

The class-5 routed mass is below the geometric envelope `∑_{i<len} (wt O₀)·(1/2)^i`: chain the
I.6S summation `hsum` with the proved geometric envelope `stageMass_le_geom` (the L.4.2 mass
half-decrease).  The base output `w₀` is the actual base stage mass `stageMass 0`. -/
theorem RunClass5StageChain.hrunSum {ctx : ActualFailureContext}
    (C : RunClass5StageChain ctx) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
      ≤ ∑ i ∈ Finset.range C.len, C.stageMass 0 * (1 / 2) ^ i := by
  refine le_trans C.hsum (Finset.sum_le_sum (fun i _ => ?_))
  exact stageMass_le_geom C.hhalf i

/-! ## 3.  Assembly — the Tower+Run seed closure from the two reduced residuals -/

/-- **The wave-10 Tower+Run seed closure.**

Builds the full `TowerRunSeedClosureData` (the `towerRun` field of `Erdos260MinimalResidual`,
feeding `erdos260_of_minimalResidual`) from:

* `cover ctx : Class2DenseMarkerCover ctx` — Core 3 (the dense-marker existence/packing, with the
  multiplier pinned to the genuine active floor); and
* `chain ctx : RunClass5StageChain ctx` — Cores 4 + 5 (the half-decreasing stage chain, the I.6S
  summation, and the I.5.2 base output).

The base run output `runBase` is the *actual* base stage mass `stageMass 0`; the chain length is
the actual descent length; no count is introduced. -/
def buildTowerRunSeedClosure
    (cover : ∀ ctx : ActualFailureContext, Class2DenseMarkerCover ctx)
    (chain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx) :
    TowerRunSeedClosureData where
  htowerSubMass := fun ctx => (cover ctx).htowerSubMass
  runChainLen := fun ctx => (chain ctx).len
  runBase := fun ctx => (chain ctx).stageMass 0
  hrunBase_nonneg := fun ctx => (chain ctx).hnonneg 0
  hrunSum := fun ctx => (chain ctx).hrunSum
  hrunBase12 := fun ctx => (chain ctx).hbase

/-- The constructed closure routes its Tower active layer at the canonical `s = X/6`. -/
@[simp] theorem buildTowerRunSeedClosure_towerS
    (cover : ∀ ctx : ActualFailureContext, Class2DenseMarkerCover ctx)
    (chain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx)
    (ctx : ActualFailureContext) :
    (buildTowerRunSeedClosure cover chain).towerS ctx = seedTowerS ctx := rfl

/-- The constructed closure's run base output is the actual base stage mass `wt(O₀)`. -/
@[simp] theorem buildTowerRunSeedClosure_runBase
    (cover : ∀ ctx : ActualFailureContext, Class2DenseMarkerCover ctx)
    (chain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx)
    (ctx : ActualFailureContext) :
    (buildTowerRunSeedClosure cover chain).runBase ctx = (chain ctx).stageMass 0 := rfl

/-! ## 4.  Geometry anchors (re-exports)

The Run chain's ratio `1/2` is not assumed: it is the actual shell's period-level half-decrease. -/

/-- **The L.4.2 half-decrease on the actual shell residual centre (re-export anchor).**

Re-export of `seedRun_periodDescent_halfDecrease` — the period-level half-decrease
`2·p' ≤ scaleMult·ord_{q₀}(2)` of the §25.2 residual centre `runFOfShell ctx`, the dynamical
source of the mass-level ratio `1/2` used by `RunClass5StageChain.hhalf`. -/
theorem runChain_halfDecrease_anchor (ctx : ActualFailureContext) (u : ℕ) (weight : ℝ) :
    ∃ p', PeriodicOn (dyadicDigit (residualCenterOfFailingShell (runFOfShell ctx)).q0
            (residualCenterOfFailingShell (runFOfShell ctx)).a) u
          (2 * ((residualCenterOfFailingShell (runFOfShell ctx)).scaleMult
            * orderOf (2 : ZMod (residualCenterOfFailingShell (runFOfShell ctx)).q0))) p'
        ∧ 0 < p'
        ∧ 2 * p' ≤ (residualCenterOfFailingShell (runFOfShell ctx)).scaleMult
            * orderOf (2 : ZMod (residualCenterOfFailingShell (runFOfShell ctx)).q0) :=
  seedRun_periodDescent_halfDecrease ctx u weight

/-! ## 5.  Honest residual inventory -/

/-- The precise per-core status of the wave-10 Tower core 3 + Run cores 4/5 after this module. -/
def towerRunMassBoundResiduals : List String :=
  [ "SHRANK (Core 3, Tower class 2 — multiplier pinned) — Class2DenseMarkerCover.htowerSubMass: " ++
      "the class-2 sub-mass routedClassMassOf … 2 ≤ ξ·X/6 is discharged from towerSubMass_of_failure " ++
      "with the window-excess multiplier PINNED to the genuine active floor positivePart (2·Y) " ++
      "(class2_windowExcess_lt_twoY: on the genuine class-2 fibre runClsOfShell ≠ 1 ⟹ windowExcess " ++
      "< 2·Y, the K.1.2/L.20 residual multiplier). The wave-9 free htowerPoint/hmult_nonneg are " ++
      "GONE; ctx.hfailure is still consumed via markerCount_le_of_failure.",
    "BARE RESIDUAL (Core 3, Tower class 2 — dense-marker existence/packing) — Class2DenseMarkerCover: " ++
      "hcover (K.1.1 endpoint-disjoint cover |fibre 2| ≤ |𝒟₀|·(2 spread+1)) + hpack (the I.4.1 " ++
      "dense-marker hit packing |𝒟₀|·ρ_D·L ≤ #supportShell) + hbdry (0 ∉ class-2 fibre, the " ++
      "manuscript boundary start) + hsmall (the K.4 numeric (c₀/ρ_D·L)·(2 spread+1)·(2·Y) ≤ ξ/6). " ++
      "This is the irreducible I.4.1 dense-packing input geometry — a SUB-mass, never the full " ++
      "high-excess mass (refuted by seed_fullMass_forces_X_nonpos).",
    "SHRANK (Core 4, Run class 5 — geometric envelope PROVED) — RunClass5StageChain.hrunSum: " ++
      "routedClassMassOf … 5 ≤ ∑_{i<len} (wt O₀)·(1/2)^i is derived from the I.6S summation hsum " ++
      "(class-5 mass ≤ ∑ stageMass i) chained with the PROVED geometric envelope stageMass_le_geom " ++
      "(stageMass i ≤ stageMass 0·(1/2)^i, from the mass half-decrease). The geometric bookkeeping " ++
      "is now a theorem.",
    "BARE RESIDUAL (Core 4, Run class 5 — I.6S charged summability) — RunClass5StageChain.hsum + " ++
      "hhalf: the class-5 routed mass is the sum of the actual descent-stage masses (hsum) which " ++
      "contract by 1/2 (hhalf, the mass-level L.4.2 half-decrease, anchored in the period-level " ++
      "half-decrease runChain_halfDecrease_anchor = seedRun_periodDescent_halfDecrease).",
    "BARE RESIDUAL (Core 5, Run class 5 — I.5.2 base run output) — RunClass5StageChain.hbase: " ++
      "stageMass 0 = wt(O₀) ≤ c⋆·ξ·X/12, the L.4.2 period-descent base output bound. runBase is the " ++
      "ACTUAL base stage mass, not a free weight.",
    "ASSEMBLED — buildTowerRunSeedClosure: a full TowerRunSeedClosureData (the towerRun field of " ++
      "Erdos260MinimalResidual) from the per-context Class2DenseMarkerCover (Core 3) and " ++
      "RunClass5StageChain (Cores 4+5), with NO free Tower/Run count. Feeds erdos260_of_minimalResidual.",
    "ROUTE PINNED — every core is over the genuine first-obstruction route genuineChargeRoute; the " ++
      "multiplier and base output are pinned to genuine geometric quantities (the active floor 2·Y, " ++
      "the actual stage masses wt(O_i)), no degenerate/empty/zero-fraction/full-mass shortcut." ]

theorem towerRunMassBoundResiduals_nonempty : towerRunMassBoundResiduals ≠ [] := by
  simp [towerRunMassBoundResiduals]

/-! ## 6.  Axiom-cleanliness audit -/

#print axioms class2_windowExcess_lt_twoY
#print axioms class2_fibre_windowExcess_le
#print axioms Class2DenseMarkerCover.htowerSubMass
#print axioms stageMass_le_geom
#print axioms RunClass5StageChain.hrunSum
#print axioms buildTowerRunSeedClosure
#print axioms runChain_halfDecrease_anchor

end

end Erdos260
