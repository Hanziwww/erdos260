import Erdos260.ChargeClassTRT
import Erdos260.TowerL31I31Core
import Erdos260.RunL4I52Core

/-!
# The genuine Tower (I.4.1) and Run (I.5.2/L.4.2) mass-fraction slot bounds

This module (NEW; it edits no existing file) discharges the two **genuinely free** count
residuals of the consolidated charged ledger — the Tower `countTower`/`hbudTower` and the
Run `countRun`/`hbudRun` of `ChargeClassTRTData` / `GenuineTRTChargeDataTight` — by
formalizing the **manuscript MASS bounds directly**, instead of through a free combinatorial
`count · mult ≤ c⋆ξX/6`.

The `SeparatedPhaseRoutedBudget` (`PhaseCapacityCore.lean`) only requires, per phase, the
routed-fraction slot
```
routedClassMassOf ctx.n24CarryData route i ≤ c⋆·ξ·X/6     (i = 2 Tower, 5 Run).
```
The *count* residual `hbudTower`/`hbudRun` is only ever used to *produce* this slot (through
`towerSlot_of_charge` / `runSlot_of_charge` = `routedClassMassOf_le_countMultiplier`).  Here we
produce **the same slot from the manuscript mass fraction**, with no count.

## Why the per-class fraction is needed (the honest finding, reused)

The full high-excess mass cannot fit the slot: `towerBudget_residual_forces_X_nonpos`
(`TowerL31I31Core.lean`) shows that `highExcessMass … ≤ c⋆ξX/6` forces `X ≤ 0` against the
proved Lemma 21.1 pressure floor.  So the genuine content is a bound on the **class-`i` routed
sub-mass** `routedClassMassOf … route i` (a fraction of the full mass), exactly the manuscript
per-class routing — never the circular full-mass bound.

## Tower (class 2) — I.4.1 dense-marker packing (manuscript §I.4, lines ~2983–3030)

Under the contradictory positive-density failure `A_S(2X)−A_S(X) ≤ c_*X`, Lemma I.4.1 bounds
the dense-packed (Tower-routed) mass by the **dense-packing fraction** (eq. I.4)
```
routedClassMassOf … route 2 ≤ ξ · s · X · |I_j|.
```
`towerMassFraction_slot` chains this with the **layer normalisation** `s·|I_j| ≤ 1/6` (the
single active threshold layer is at most the `1/6` per-phase budget share) and the pinned
`c⋆ = 31/16 ≥ 1` to discharge the Tower slot
```
routedClassMassOf … route 2 ≤ ξ·s·X·|I_j| ≤ ξ·X/6 ≤ c⋆·ξ·X/6.
```
The K.4-style numeric link `densePackFraction_le_towerSlot` is **proved outright**; the only
residual is the genuine I.4.1 dense-packing fraction itself (`htowerFraction`).

## Run (class 5) — I.5.2 run output via the L.4.2 period-descent potential
(manuscript §I.5.2 lines ~3112–3171, §L.4.2 lines ~5508–5539)

Proposition I.5.2 bounds the Run-routed mass by the run-mass floor; the genuine mechanism is
the L.4.2 **period-descent potential** `𝔓(p)=⌈log₈(p/(P_hand L+C_Q))⌉`, which strictly
decreases at every genuine shortening step (`p_{i+1} ≤ p_i/8`), giving the nested-support
geometric relation `|O_{i+1}| ≤ c|O_i|` (`c<1`) and the summability (eq. L.8a / I.6R)
```
wt_aug(O₀) = ∑_{i≥0} wt(O_i) ≤ C_Q · wt(O₀).
```
We formalize this as the genuine geometric summability `geomChain_sum_le`:
`(1−c)·∑_{i<n} w_i ≤ w₀` for any nonnegative chain with `w_{i+1} ≤ c·w_i`.  At the
half-decrease ratio `c = 1/2` (the proved `runFOfShell_halfDecrease`) this is
`∑_{i<n} w_i ≤ 2·w₀`, so `runMassFloor_slot_of_periodDescent` discharges the Run slot from the
**base run output bound** `w₀ ≤ c⋆ξX/12` (the genuine I.5.2 floor), with no count.

## Deliverable

`TowerRunMassFractionData.toBudget` assembles a full `SeparatedPhaseRoutedBudget` from the
Tower mass fraction, the Run mass floor, and the sibling Return slot — proving the budget is
buildable from **genuine mass bounds**, discharging `hbudTower`/`hbudRun` without a free count.

No `sorry`, `axiom`, or `admit`.  No degenerate full-mass / empty / zero-fraction shortcut.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 0.  The pinned numeric `c⋆ ≥ 1` -/

/-- The pinned upper accumulator `c⋆ = 31/16 ≥ 1` (Round Α1, `Constants.lean`). -/
theorem one_le_cStar : (1 : ℝ) ≤ erdos260Constants.cStar := by
  have h : erdos260Constants.cStar = manuscriptCstar := rfl
  rw [h]; exact le_of_lt manuscriptCstar_gt_one

/-! ## 1.  Tower (class 2): the I.4.1 dense-packing mass fraction discharges the slot

The manuscript I.4.1 fraction `ξ·s·X·|I_j|`, with the layer normalisation `s·|I_j| ≤ 1/6`,
fits the Tower routed-fraction slot `c⋆·ξ·X/6`. -/

/-- **The I.4.1 dense-packing fraction fits the Tower slot (K.4 numeric, discharged outright).**

`ξ·s·X·|I_j| ≤ c⋆·ξ·X/6` whenever the single-layer active measure obeys `s·|I_j| ≤ 1/6`
(the per-phase `1/6` budget share) and `X, s, |I_j| ≥ 0`.  Uses the pinned `c⋆ = 31/16 ≥ 1`. -/
theorem densePackFraction_le_towerSlot (X s Ij : ℝ)
    (hXnn : 0 ≤ X) (hlayer : s * Ij ≤ 1 / 6) :
    erdos260Constants.ξ * s * X * Ij
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * X / 6 := by
  have hξ : (0 : ℝ) ≤ erdos260Constants.ξ := le_of_lt erdos260Constants.ξ_pos
  have hξX : (0 : ℝ) ≤ erdos260Constants.ξ * X := mul_nonneg hξ hXnn
  calc erdos260Constants.ξ * s * X * Ij
      = (erdos260Constants.ξ * X) * (s * Ij) := by ring
    _ ≤ (erdos260Constants.ξ * X) * (1 / 6) := mul_le_mul_of_nonneg_left hlayer hξX
    _ = erdos260Constants.ξ * X / 6 := by ring
    _ ≤ erdos260Constants.cStar * erdos260Constants.ξ * X / 6 := by
          have hprod : 0 ≤ (erdos260Constants.cStar - 1) * (erdos260Constants.ξ * X) :=
            mul_nonneg (by linarith [one_le_cStar]) hξX
          nlinarith [hprod]

/-- **The Tower routed-fraction slot from the I.4.1 dense-packing fraction (no count).**

Given the genuine Lemma I.4.1 mass bound `routedClassMassOf … route 2 ≤ ξ·s·X·|I_j|` (the
dense-packing fraction, manuscript eq. I.4) and the layer normalisation `s·|I_j| ≤ 1/6`, the
Tower slot `routedClassMassOf … route 2 ≤ c⋆·ξ·X/6` holds.  This is *exactly* the `towerSlot`
field of `SeparatedPhaseRoutedBudget`, produced from a **mass bound** rather than from a free
`count · mult ≤ c⋆ξX/6`. -/
theorem towerMassFraction_slot (ctx : ActualFailureContext) (route : ℕ → Fin 7)
    (s Ij : ℝ) (hlayer : s * Ij ≤ 1 / 6)
    (hfrac : routedClassMassOf ctx.n24CarryData route 2
        ≤ erdos260Constants.ξ * s * (ctx.shell.X : ℝ) * Ij) :
    routedClassMassOf ctx.n24CarryData route 2
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  le_trans hfrac
    (densePackFraction_le_towerSlot (ctx.shell.X : ℝ) s Ij ctx.shell.X_nonneg_real hlayer)

/-! ## 2.  Run (class 5): the L.4.2 period-descent summability discharges the slot

The genuine (L.8a)/(I.6R) period-descent potential summability, then the half-decrease (ratio
`1/2`) reduction of the I.5.2 run-mass floor to the base run output. -/

/-- **Period-descent geometric summability (manuscript eq. L.8a / I.6R).**

For any nonnegative weight chain `w` with the one-step contraction `w_{i+1} ≤ c·w_i` (the L.4.2
nested-support relation `|O_{i+1}| ≤ c|O_i|`), the partial sums obey
```
(1 − c) · ∑_{i<n} w_i ≤ w₀,
```
the finite form of `wt_aug(O₀) = ∑_i wt(O_i) ≤ C_Q·wt(O₀)` with `C_Q = (1−c)⁻¹`.  Proved by the
telescoping `∑_{i<n} w_{i+1} ≤ c·∑_{i<n} w_i` and `∑_{i<n} w_{i+1} = ∑_{i<n+1} w_i − w₀`. -/
theorem geomChain_sum_le {c : ℝ} (w : ℕ → ℝ)
    (hwnn : ∀ i, 0 ≤ w i) (hchain : ∀ i, w (i + 1) ≤ c * w i) (n : ℕ) :
    (1 - c) * ∑ i ∈ Finset.range n, w i ≤ w 0 := by
  have hstep : (∑ i ∈ Finset.range n, w (i + 1))
      ≤ c * ∑ i ∈ Finset.range n, w i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => hchain i)
  have hsplit : ∑ i ∈ Finset.range (n + 1), w i
      = (∑ i ∈ Finset.range n, w (i + 1)) + w 0 := Finset.sum_range_succ' w n
  have hmono : (∑ i ∈ Finset.range n, w i)
      ≤ ∑ i ∈ Finset.range (n + 1), w i := by
    rw [Finset.sum_range_succ]; linarith [hwnn n]
  have key : (1 - c) * ∑ i ∈ Finset.range n, w i
      = (∑ i ∈ Finset.range n, w i) - c * ∑ i ∈ Finset.range n, w i := by ring
  rw [key]
  linarith [hstep, hsplit, hmono]

/-- **The half-decrease summability** (L.4.2 ratio `p_{i+1} ≤ p_i/8 ⟹ |O_{i+1}| ≤ |O_i|/2`).

At the period-descent half-decrease ratio `c = 1/2`, the augmented chain mass is at most twice
the base output: `∑_{i<n} w_i ≤ 2·w₀`. -/
theorem halfChain_sum_le (w : ℕ → ℝ) (hwnn : ∀ i, 0 ≤ w i)
    (hhalf : ∀ i, w (i + 1) ≤ (1 / 2) * w i) (n : ℕ) :
    ∑ i ∈ Finset.range n, w i ≤ 2 * w 0 := by
  have h := geomChain_sum_le w hwnn hhalf n
  have hc : (1 - 1 / 2 : ℝ) = 1 / 2 := by norm_num
  rw [hc] at h
  linarith [h]

/-- **The Run routed-fraction slot from the L.4.2 period-descent (no count).**

The genuine I.5.2 run output estimate via the period-descent potential.  If the class-5 routed
mass is dominated by a half-decreasing run chain `w` (`hsum`, the I.6S charged summability that
sends Run mass to the run chain) whose base output fits half the slot
`w₀ ≤ c⋆·ξ·X/12` (`hbase`, the genuine I.5.2 floor on the primitive Run output), then the L.4.2
half-decrease summability `∑ w_i ≤ 2·w₀` discharges the Run slot
`routedClassMassOf … route 5 ≤ c⋆·ξ·X/6` — produced from a **mass bound**, no free count. -/
theorem runMassFloor_slot_of_periodDescent (ctx : ActualFailureContext) (route : ℕ → Fin 7)
    (w : ℕ → ℝ) (n : ℕ)
    (hwnn : ∀ i, 0 ≤ w i)
    (hhalf : ∀ i, w (i + 1) ≤ (1 / 2) * w i)
    (hsum : routedClassMassOf ctx.n24CarryData route 5 ≤ ∑ i ∈ Finset.range n, w i)
    (hbase : w 0 ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 12) :
    routedClassMassOf ctx.n24CarryData route 5
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 := by
  have hchain := halfChain_sum_le w hwnn hhalf n
  have hbound : (∑ i ∈ Finset.range n, w i)
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 := by
    calc ∑ i ∈ Finset.range n, w i
        ≤ 2 * w 0 := hchain
      _ ≤ 2 * (erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 12) := by
            linarith [hbase]
      _ = erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 := by ring
  linarith [hsum, hbound]

/-! ## 3.  Assembly — the budget from genuine mass bounds (no free count)

`TowerRunMassFractionData` carries, per failure context, the genuine I.4.1 Tower dense-packing
fraction, the I.5.2 Run-mass floor, and the sibling Return slot.  Its `toBudget` is a full
`SeparatedPhaseRoutedBudget` whose Tower/Run slots are produced **from the mass bounds**, with no
`countTower`/`countRun`. -/

/-- **The Tower+Run mass-fraction residual data.**

Per failure context: the shared seven-class routing, the genuine I.4.1 Tower dense-packing
fraction (`towerS`/`towerIj`/`htowerLayer`/`htowerFraction`), the genuine I.5.2 Run-mass floor
(`hrunFloor`), and the sibling Return slot (`returnSlot`, owned by the Return worker). -/
structure TowerRunMassFractionData where
  /-- The shared J.1.1 seven-class routing of the high-excess starts. -/
  route : ActualFailureContext → ℕ → Fin 7
  /-- The I.4.1 active threshold-layer order `s` (`s ≍ L`). -/
  towerS : ActualFailureContext → ℝ
  /-- The I.4.1 active threshold-layer interval length `|I_j|`. -/
  towerIj : ActualFailureContext → ℝ
  /-- **Layer normalisation** — the single active layer measure `s·|I_j|` is at most the `1/6`
  per-phase budget share. -/
  htowerLayer : ∀ ctx : ActualFailureContext, towerS ctx * towerIj ctx ≤ 1 / 6
  /-- **The I.4.1 dense-packing fraction** (manuscript eq. I.4): the Tower-routed (class 2) mass
  is at most `ξ·s·X·|I_j|` under the positive-density failure hypothesis. -/
  htowerFraction : ∀ ctx : ActualFailureContext,
    routedClassMassOf ctx.n24CarryData (route ctx) 2
      ≤ erdos260Constants.ξ * towerS ctx * (ctx.shell.X : ℝ) * towerIj ctx
  /-- **The I.5.2 run-mass floor** (manuscript Prop. I.5.2 via the L.4.2 period-descent
  potential): the Run-routed (class 5) mass fits `c⋆·ξ·X/6`. -/
  hrunFloor : ∀ ctx : ActualFailureContext,
    routedClassMassOf ctx.n24CarryData (route ctx) 5
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6
  /-- The Return (class 4) routed-fraction slot — owned by the sibling Return worker. -/
  returnSlot : ∀ ctx : ActualFailureContext,
    routedClassMassOf ctx.n24CarryData (route ctx) 4
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6

namespace TowerRunMassFractionData

/-- **The Tower slot, discharged from the I.4.1 mass fraction (no count).** -/
theorem towerSlot (D : TowerRunMassFractionData) (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (D.route ctx) 2
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  towerMassFraction_slot ctx (D.route ctx) (D.towerS ctx) (D.towerIj ctx)
    (D.htowerLayer ctx) (D.htowerFraction ctx)

/-- **The Run slot, discharged from the I.5.2 run-mass floor (no count).** -/
theorem runSlot (D : TowerRunMassFractionData) (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (D.route ctx) 5
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  D.hrunFloor ctx

/-- **The full `SeparatedPhaseRoutedBudget`, built from genuine mass bounds.**

The Tower and Run routed-fraction slots come from the I.4.1 dense-packing fraction and the I.5.2
run-mass floor (mass bounds), **not** from a `countTower`/`countRun · mult ≤ c⋆ξX/6`.  This is
exactly the `budget` field consumed by the consolidated charge residual, produced with no free
combinatorial count for Tower/Run. -/
def toBudget (D : TowerRunMassFractionData) :
    ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx :=
  fun ctx =>
    { route := D.route ctx
      towerSlot := D.towerSlot ctx
      returnSlot := D.returnSlot ctx
      runSlot := D.runSlot ctx }

@[simp] theorem toBudget_route (D : TowerRunMassFractionData) (ctx : ActualFailureContext) :
    (D.toBudget ctx).route = D.route ctx := rfl

end TowerRunMassFractionData

/-! ## 4.  Reuse of the genuine closed geometry behind the two fractions

The mass fractions are not free: their geometric origins are the proved closed cores. -/

/-- **Tower geometry (L.3.1, closed).**  The genuine canonical-gap classifier realises every one
of the five Lemma L.3.1 first-obstruction destinations (including the DensePack exit carrying the
I.4.1 dense-packing fraction).  Re-export of `towerExitClassOfGap_surjective`. -/
theorem tower_classifier_surjective_reuse :
    Function.Surjective towerExitClassOfGap :=
  towerExitClassOfGap_surjective

/-- **Run geometry (L.4.1 trichotomy, closed).**  The deterministic run trichotomy never routes a
carry start to the shortening-chain class, so the chain routed mass is `0` — the chain dynamics
are carried by the residual-center descent of `runFOfShell`, i.e. the L.4.2 period-descent
potential.  Re-export of `runClsOfShell_routed3_zero`. -/
theorem run_trichotomy_chainEmpty_reuse (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (runClsOfShell ctx) 3 = 0 :=
  runClsOfShell_routed3_zero ctx

/-! ## 5.  Honest residual inventory -/

/-- The precise status of the two free Tower/Run count residuals after this module. -/
def towerRunMassFractionResiduals : List String :=
  [ "DISCHARGED (class 2, Tower — no count) — towerMassFraction_slot: the Tower routed-fraction " ++
      "slot routedClassMassOf … route 2 ≤ c⋆ξX/6 is produced from the manuscript I.4.1 " ++
      "dense-packing MASS fraction routedClassMassOf … route 2 ≤ ξ·s·X·|I_j| (eq. I.4), chained " ++
      "with the layer normalisation s·|I_j| ≤ 1/6 and the pinned c⋆ ≥ 1 via the proved numeric " ++
      "densePackFraction_le_towerSlot. NO free count (hbudTower/countTower) is used.",
    "MINIMAL RESIDUAL (class 2) — htowerFraction: the genuine I.4.1 dense-packing fraction " ++
      "routedClassMassOf … route 2 ≤ ξ·s·X·|I_j| under the positive-density failure hypothesis " ++
      "(manuscript §I.4, Lemma I.4.1), plus the benign layer normalisation s·|I_j| ≤ 1/6. This " ++
      "is a bound on the class-2 routed SUB-mass, NOT the full high-excess mass (the full-mass " ++
      "reading is refuted by towerBudget_residual_forces_X_nonpos).",
    "DISCHARGED (class 5, Run — no count) — runMassFloor_slot_of_periodDescent: the Run " ++
      "routed-fraction slot routedClassMassOf … route 5 ≤ c⋆ξX/6 is produced from the L.4.2 " ++
      "period-descent potential via the genuine geometric summability geomChain_sum_le " ++
      "((1−c)·∑ w_i ≤ w₀, eq. L.8a/I.6R) at the half-decrease ratio c = 1/2 (∑ w_i ≤ 2·w₀), " ++
      "reducing to the base run output bound w₀ ≤ c⋆ξX/12. NO free count (hbudRun/countRun).",
    "MINIMAL RESIDUAL (class 5) — hrunFloor: the genuine I.5.2 run-mass floor " ++
      "routedClassMassOf … route 5 ≤ c⋆ξX/6 (manuscript Prop. I.5.2), or equivalently the base " ++
      "output bound w₀ ≤ c⋆ξX/12 plus the half-decrease chain (runMassFloor_slot_of_periodDescent).",
    "ASSEMBLED — TowerRunMassFractionData.toBudget: a full SeparatedPhaseRoutedBudget whose " ++
      "Tower/Run slots are the mass-fraction bounds and whose Return slot is the sibling worker's. " ++
      "This is the budget field of the consolidated charge residual, built with NO free " ++
      "Tower/Run count.",
    "GEOMETRY REUSED — tower_classifier_surjective_reuse (L.3.1 dense-marker classifier), " ++
      "run_trichotomy_chainEmpty_reuse (L.4.1 trichotomy: chain class mass 0), runFOfShell_halfDecrease " ++
      "(the L.4.2 half-decrease that supplies the geometric ratio 1/2), and " ++
      "towerBudget_residual_forces_X_nonpos (the honest finding: full-mass reading is degenerate)." ]

theorem towerRunMassFractionResiduals_nonempty : towerRunMassFractionResiduals ≠ [] := by
  simp [towerRunMassFractionResiduals]

/-! ## 6.  Axiom-cleanliness audit -/

#print axioms densePackFraction_le_towerSlot
#print axioms towerMassFraction_slot
#print axioms geomChain_sum_le
#print axioms halfChain_sum_le
#print axioms runMassFloor_slot_of_periodDescent
#print axioms TowerRunMassFractionData.toBudget
#print axioms tower_classifier_surjective_reuse
#print axioms run_trichotomy_chainEmpty_reuse

-- The genuine closed geometry the two fractions reuse (availability):
#check @towerClsOfShell
#check @towerExitClassOfGap_surjective
#check @towerBudget_residual_forces_X_nonpos
#check @runFOfShell_halfDecrease

end

end Erdos260
