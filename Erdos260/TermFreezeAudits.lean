import Erdos260.Erdos260CorrectedLedgerCapstone
import Erdos260.ChernoffProgressCountCore
import Erdos260.DensePackCorrectedClosure
import Erdos260.RunClass5BoundaryClosure
import Erdos260.ScaleFloorPush
import Erdos260.FloorPushV2

/-!
# Term freeze audits: the Chernoff / DensePack / Run capacity terms of the P9 ledger
# (`TermFreezeAudits`)

This module (NEW; it edits no existing file) extends the wave-16 calibration audit
(`LedgerCalibrationAudit.lean`, which settled the class-1 `termCnl` freeze) to the THREE
remaining per-class capacity terms of the faithful P9 ledger — `termChernoff` (class 0),
`termDensePack` (class 3), `termRun` (class 5) — following the same playbook:
provenance-trace the consumed frozen value, compare it against the source budget at the
evaluation stage, construct the corrected term saturating the in-tree per-class budget cap
`c⋆·ξ·X/6 = (31/1536)·X`, and deliver the fully-corrected ledger bridge plus every closure
the corrected caps enable.

## The three freeze verdicts (all pins proved below)

* **Class 0 (Chernoff).**  The consumed faithful term is the SHELL-INDEPENDENT constant
  `chernoffModelArea = ∑_{σ∈{0,1}²} 2^{−cost σ} ∈ [1, 4]` (`termChernoff_faithful_eq`,
  `ChernoffProgressCountCore.lean`): the §22.1A area budget `C_Q·X·|I_j|·2^{−cY}`
  (tex H.1 lines 2725–2740; the same `ξ·s·X·|I_j|` per-class growth of H.2', lines
  2755–2768) was frozen to the FOUR-PATH model leaf `modelPaths = {0,1}²` with `Y := 0`
  and NO `X·|I_j|` scaling at all.  Since every routed class-0 start carries window excess
  `≥ Y = L/64 ≥ 15421/64 > 4`, the frozen class-0 ledger bound IS class-0 fibre emptiness
  (`tfaClass0Razor` below) — the same razor artifact as the class-1 lane, and exactly the
  per-pair emptiness demand that the corrected capstone's unified `class0Fibre` field
  makes at the 19 survivor pairs (`OffFibreMissClosure.lean`).
* **Class 3 (DensePack).**  The consumed faithful term is the raw marker COUNT
  `|proofV4DensePackActualPoints ctx.shell|` (`termDensePack_faithful_eq`,
  `DensePackCorrectedClosure.lean`) — each K.1 marker absorbs ONE unit while each routed
  class-3 start carries excess up to `(r+1)(L+B+1) − (2L+1) ≥ 31·L` (proved floor below);
  the source charges the class by the stage-growing `ξ·s·X·|I_j|` budget (H.2'/H.3', K.1.2
  multiplier linear in the active floor), never by a unit-per-marker count.
* **Class 5 (Run).**  The consumed faithful term is the routed class-5 mass ITSELF:
  `termRun (faithfulCapacityPhases …) = routedClassMassOf … route 5` (`rfl`,
  `termRun_faithfulCapacityPhases`, `ChargeClassTRT.lean`) — a CIRCULAR freeze: the
  capacity was frozen to the demand, so the ledger's TRT row carries no run content and
  the entire run constraint lives in the budget's `runSlot` hypothesis.  The corrected
  term replaces it by the genuine non-circular capacity `(31/1536)·X`.

## The corrected six-phase assembly (`correctedAllPhases`)

ALL SIX phase slots saturated at the per-class cap (the class-1 slot reuses the audit's
`correctedCnlData`): `termChernoff = termCnl = termTower = termReturn = termRun
= (31/1536)·X` exactly, and `termDensePack = ⌊31·X/1536⌋` (the term is an ℕ count; the
floor is the maximal admissible value, within `1` of the cap —
`termDensePack_correctedAll_saturates`).  The consumption arithmetic SURVIVES with all six
terms at their caps: total phase mass `≤ c⋆·ξ·X = (31/256)·X` (the generic
`ClosurePhaseMass_le_budget` still applies — every `manuscript_bound`/`hSmall` field holds
with equality) and `(31/256)·X < X/2 = c_pr·X` (`tfaCorrectedTotal_lt_floor`), so the
pressure-floor contradiction is intact: `1/2 > 31/256`.  Each class can take its full cap
INDEPENDENTLY.

## The fully-corrected ledger bridge

`FullyCorrectedP9LedgerResidual` = the five per-context ledger bounds over
`correctedAllPhases` + class-6 vacancy, with the complete bridge `toStatement` to
`Erdos260Statement` through `RoutedHighExcessChargeDataOldRes` (`oldResMass = 0`) and
`erdos260_final_actual`.  `ofPinnedRoutingZero`: the OLD frozen pinned residual implies
the fully-corrected one (all six frozen terms are dominated by the corrected ones —
`tfa*_frozen_le_correctedAll`); `ofGenuineCaps`: over any genuine-routed budget the
residual needs ONLY the three count-cap absorption gates (classes 0/1/3) — the TRT row
closes from the budget slots themselves and class 6 from the genuine route's vacancy.

## Closures and honest L-regime accounting per lane (all proved below)

* **Class 0**: mass₀ ≤ |fibre₀|·runDyadicMult (the proved window cap); at every survivor
  pair |fibre₀| ≤ ⌈W/c⌉ (`ofcClass0Fibre_card_le_of_survivor`, gate-free), so the ℕ gate
  `1536·⌈W/c⌉·(r+1)(L+B+1) ≤ 31·X` closes the corrected class-0 ledger bound — absorption
  instead of the emptiness razor (`tfaCorrectedHChernoff_of_survivor`).  HONEST: the gate
  cannot be discharged from the in-tree failure cap `W < (17/2²⁴)·X` alone — the
  worst-case count `(17/2²⁴)·X/18` times the multiplier floor `31·L` exceeds the cap
  `(31/1536)·X` at EVERY actual context (`tfaClass0Gate_not_from_failureCap`; the
  W-cap-only sufficient regime needs `L ≲ 642·c ≤ 11556`, against the unconditional floor
  `L ≥ 493461`).  At the 19 survivor pairs the proved regime is `q ≤ 45 < 2²⁰`, hence
  `L ≥ 986876` and `r ≥ 63` (the wave-10 small-`q` floors apply at ALL nineteen pairs —
  NOT only generic wave-8 `L ≥ 493461`); the spaced-singleton regime `W ≤ c` is VACUOUS
  there (`r ≥ 63` forces `W ≥ 64 > 18 ≥ c`).  The gate is a genuine narrow-support
  condition (roughly `W ≲ c·X/(50·mult)`), conditional per context.
* **Class 3**: mass₃ ≤ |fibre₃|·runDyadicMult with the generic width cap |fibre₃| ≤ W;
  the ℕ gate `W·(r+1)(L+B+1) ≤ 31·X/1536` closes the corrected class-3 bound
  (`tfaCorrectedHDensePack_of_widthGate`) — same narrow-support regime, same honest
  obstruction from the failure cap.
* **Class 5**: the wave-16 band-4 split is decisive.  On band-4-pinned contexts the
  corrected run bound is FALSE (`tfaBand4_correctedRun_false`: the relocated pressure
  floor `(511/1024)·X·(r+1)` exceeds `(31/1536)·X` at every scale) — indeed NO
  genuine-routed budget exists there at all (`tfaBand4_no_genuine_budget`: the `runSlot`
  itself fails), so the lane MUST route band-4 data through L.3/M.5 (the wave-16
  `runBand4Void` reading is forced, now against the corrected term as well).  On
  band-4-free contexts the corrected run bound is the conditional count×multiplier gate
  `|fibre₅|·runDyadicMult ≤ (31/1536)·X` (`tfaCorrectedHRun_of_gate`).

## What stays open (honest)

The three absorption gates are PER-CONTEXT numeric conditions on the actual support width
`W`; no in-tree cap discharges them (proved impossible from the failure cap alone), and no
per-pair width pins exist for the 19 survivors.  The corrected surface replaces emptiness
demands by absorption demands — strictly weaker (`tfaClass0Absorption_of_fibreEmpty`,
`ofPinnedRoutingZero`) — but does not close the global P9 residual.  Nothing here touches
the pressure-floor spine; additive only.

No `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Part 0.  Shared constants and arithmetic helpers -/

/-- The pinned product `c⋆·ξ = (31/16)·(1/16) = 31/256` (Constants.lean, round Α1). -/
theorem tfaCstarXi_eq :
    erdos260Constants.cStar * erdos260Constants.ξ = (31 : ℝ) / 256 := by
  rw [show erdos260Constants.cStar = manuscriptCstar from rfl,
    show erdos260Constants.ξ = manuscriptXi from rfl]
  exact manuscriptCstar_mul_xi_eq_31_256

/-- The saturated per-class capacity value `c⋆·ξ·X/6 = (31/1536)·X` is nonnegative. -/
theorem tfaShareTerm_nonneg (ctx : ActualFailureContext) :
    (0 : ℝ) ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 := by
  have h := correctedCnlShare_num_nonneg
  have hX : (0 : ℝ) ≤ (ctx.shell.X : ℝ) := Nat.cast_nonneg _
  have hm := mul_nonneg h hX
  linarith

/-- The canonical ℕ window multiplier `(r+1)·(L+B+1)` (the dyadic gap ceiling times the
window length — the ℕ skeleton of `runDyadicMult`). -/
def tfaNatMult (ctx : ActualFailureContext) : ℕ :=
  (ctx.n24CarryData.r + 1) * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)

/-- The matched window-excess ceiling is dominated by its ℕ skeleton:
`runDyadicMult = max 0 ((r+1)(L+B+1) − T) ≤ (r+1)(L+B+1)` (the threshold `T = 2L+1 ≥ 0`). -/
theorem tfaRunDyadicMult_le_natMult (ctx : ActualFailureContext) :
    runDyadicMult ctx ≤ ((tfaNatMult ctx : ℕ) : ℝ) := by
  have hT : (0 : ℝ) ≤ ctx.n24CarryData.T := by
    rw [cnlMulti_n24_T_eq]
    positivity
  unfold runDyadicMult
  apply max_le
  · exact Nat.cast_nonneg _
  · rw [show runDyadicG0 ctx = shellLadderDepth ctx + carryB ctx.shell.Q + 1 from rfl]
    unfold tfaNatMult
    push_cast
    linarith

/-- **The proved multiplier floor `runDyadicMult ≥ 31·L`** (from the wave-8 unconditional
`r ≥ 32`): each routed start can carry up to `(r+1)(L+B+1) − (2L+1) ≥ 33(L+B+1) − (2L+1)
≥ 31L` window excess — the quantitative reason the per-element charge is NOT `O(1)`. -/
theorem tfaRunDyadicMult_ge_31L (ctx : ActualFailureContext) :
    31 * ((shellLadderDepth ctx : ℕ) : ℝ) ≤ runDyadicMult ctx := by
  have hr := n24_r_ge_thirtytwo ctx
  have hrR : (32 : ℝ) ≤ (ctx.n24CarryData.r : ℝ) := by exact_mod_cast hr
  have hB : (0 : ℝ) ≤ (carryB ctx.shell.Q : ℝ) := Nat.cast_nonneg _
  have hL : (0 : ℝ) ≤ ((shellLadderDepth ctx : ℕ) : ℝ) := Nat.cast_nonneg _
  unfold runDyadicMult
  refine le_trans ?_ (le_max_right _ _)
  have hG : (runDyadicG0 ctx : ℝ)
      = ((shellLadderDepth ctx : ℕ) : ℝ) + (carryB ctx.shell.Q : ℝ) + 1 := by
    rw [show runDyadicG0 ctx = shellLadderDepth ctx + carryB ctx.shell.Q + 1 from rfl]
    push_cast
    ring
  rw [hG, cnlMulti_n24_T_eq]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (ctx.n24CarryData.r : ℝ) + 1 - 33)
    (by linarith : (0 : ℝ) ≤ ((shellLadderDepth ctx : ℕ) : ℝ)
      + (carryB ctx.shell.Q : ℝ) + 1)]

/-- **The generic count×multiplier ceiling for ANY routed class**: every fibre member is a
carry-window start, so its excess obeys the proved ungated ceiling
`n24_windowExcess_le_runDyadicMult`; summing, `mass_i ≤ |fibre_i|·runDyadicMult`. -/
theorem tfaMass_le_card_mul_mult (ctx : ActualFailureContext)
    (route : ℕ → Fin 7) (i : Fin 7) :
    routedClassMassOf ctx.n24CarryData route i
      ≤ ((routedFibre ctx.n24CarryData route i).card : ℝ) * runDyadicMult ctx := by
  refine routedClassMassOf_le_countMultiplier ctx.n24CarryData route i ?_
    (runDyadicMult_nonneg ctx) le_rfl
  intro k hk
  have hstart : k ∈ ctx.n24CarryData.starts :=
    (mem_highExcessStarts.mp (Finset.mem_filter.mp hk).1).1
  rw [cnlMulti_starts_eq_window, Finset.mem_Ico] at hstart
  exact n24_windowExcess_le_runDyadicMult ctx hstart.2

/-- **The generic fibre width cap**: every routed fibre sits inside the carry start
window, so `|fibre_i| ≤ W = |supportShell d X|`. -/
theorem tfaFibre_card_le_width (ctx : ActualFailureContext)
    (route : ℕ → Fin 7) (i : Fin 7) :
    (routedFibre ctx.n24CarryData route i).card
      ≤ (supportShell ctx.shell.d ctx.shell.X).card := by
  have hsub : routedFibre ctx.n24CarryData route i ⊆ ctx.n24CarryData.starts := by
    intro k hk
    exact (mem_highExcessStarts.mp (Finset.mem_filter.mp hk).1).1
  have hcard := Finset.card_le_card hsub
  rwa [scc_starts_card ctx] at hcard

/-! ## Part 1.  Provenance pins of the three FROZEN terms

All evaluations are in-tree theorems, re-derived or re-exported here for the audit's axiom
block.  Manuscript counterparts: the per-class H.1 ledger terms `X·|I_j|·2^{−cY}` (tex
lines 2725–2740) with the per-class budgets `ξ·s·X·|I_j|` GROWING in the stage `s`
(H.2' lines 2755–2768, H.3' lines 2786–2795), evaluated at the contradiction stage
`s = r = ⌊κL⌋`, `Y = εL` (H.4' lines 2838–2848; K.4 items 4–5, lines 5386–5400). -/

/-- **Pin C1 (frozen Chernoff value).**  The consumed faithful class-0 term is the
shell-independent constant `chernoffModelArea` — re-export of `termChernoff_faithful_eq`:
the §22.1A area budget was frozen to the four-path model leaf `{0,1}²` at `Y := 0`. -/
theorem tfaChernoffFrozenValue
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    termChernoff (faithfulCapacityPhases budget ctx).toClosurePhaseData
      = chernoffModelArea :=
  termChernoff_faithful_eq budget ctx

/-- **Pin C2 (frozen Chernoff bounds).**  `1 ≤ termChernoff(frozen) ≤ 4` — an `O(1)`
constant against a shell-scaling LHS. -/
theorem tfaChernoffFrozenBounds
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    1 ≤ termChernoff (faithfulCapacityPhases budget ctx).toClosurePhaseData ∧
      termChernoff (faithfulCapacityPhases budget ctx).toClosurePhaseData ≤ 4 :=
  ⟨one_le_termChernoff_faithful budget ctx, termChernoff_faithful_le_four budget ctx⟩

/-- **Pin C3 (the class-0 razor).**  Over the frozen term the per-context class-0 ledger
bound is EQUIVALENT to outright class-0 fibre emptiness: any fibre member carries excess
`≥ Y = L/64 ≥ 15421/64 > 4 ≥ termChernoff(frozen)`.  This is the very emptiness demand the
corrected capstone's `class0Fibre` field makes at the 19 survivor pairs — a transcription
razor of the same genre as the class-1 one (`class1Ledger_iff_fibre_empty`). -/
theorem tfaClass0Razor
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    (routedClassMassOf ctx.n24CarryData (budget ctx).route 0
        ≤ termChernoff (faithfulCapacityPhases budget ctx).toClosurePhaseData)
      ↔ routedFibre ctx.n24CarryData (budget ctx).route 0 = ∅ := by
  constructor
  · intro hle
    by_contra hne
    obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hY := Y_le_windowExcess_of_mem_routedFibre ctx.n24CarryData (budget ctx).route 0 hk
    have hmass : windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
          ctx.n24CarryData.T
        ≤ routedClassMassOf ctx.n24CarryData (budget ctx).route 0 := by
      rw [routedClassMassOf_eq_sum_fibre]
      exact Finset.single_le_sum
        (fun j _ => windowExcess_nonneg (hitGap ctx.n24CarryData.a) j ctx.n24CarryData.r
          ctx.n24CarryData.T) hk
    have h4 := termChernoff_faithful_le_four budget ctx
    have hL : (15421 : ℝ) ≤ ((shellLadderDepth ctx : ℕ) : ℝ) := by
      exact_mod_cast shellLadderDepth_ge_15421 ctx
    rw [n24CarryData_Y_eq_div] at hY
    linarith
  · intro hempty
    rw [routedClassMassOf_eq_sum_fibre, hempty, Finset.sum_empty]
    have h1 := one_le_termChernoff_faithful budget ctx
    linarith

/-- **Pin D1 (frozen DensePack value).**  The consumed faithful class-3 term is the raw
marker count `|proofV4DensePackActualPoints ctx.shell|` — re-export of
`termDensePack_faithful_eq`: a unit-per-marker count, not an `X·|I_j|`-scaled mass. -/
theorem tfaDensePackFrozenValue
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    termDensePack (faithfulCapacityPhases budget ctx).toClosurePhaseData
      = ((proofV4DensePackActualPoints ctx.shell).card : ℝ) :=
  termDensePack_faithful_eq budget ctx

/-- **Pin R1 (the circular Run freeze).**  The consumed faithful class-5 term IS the
routed class-5 mass — re-export of the `rfl`-level `termRun_faithfulCapacityPhases`: the
capacity was frozen to the demand, so the faithful TRT ledger row carries no independent
run content (the run constraint lives entirely in the budget's `runSlot` hypothesis). -/
theorem tfaRunFrozenCircular
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    termRun (faithfulCapacityPhases budget ctx).toClosurePhaseData
      = routedClassMassOf ctx.n24CarryData (budget ctx).route 5 :=
  termRun_faithfulCapacityPhases budget ctx

/-! ## Part 2.  The source budget at the evaluation point

The like-for-like source object is the (H.1) per-class term per unit threshold length,
`X·2^{−c·Y}` at `Y = εL` — the SAME shape for every charged class (the per-class budgets
of H.2'/H.3' are all `ξ·s·X·|I_j|`).  The audit module already formalized it as
`sourceH1CnlBudgetPerFibre` and proved `Y < source` (`Y_lt_sourceH1CnlBudgetPerFibre`);
we reuse it verbatim for the class-0 comparison. -/

/-- **The class-0 comparison, concluded**: the frozen Chernoff term sits strictly BELOW
the source budget at the evaluation point — indeed below one single start's excess `Y`,
which itself sits below the source budget:
`termChernoff(frozen) ≤ 4 < Y = L/64 < X·2^{−c·εL}`. -/
theorem tfaChernoff_frozen_lt_sourceH1
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    termChernoff (faithfulCapacityPhases budget ctx).toClosurePhaseData
      < sourceH1CnlBudgetPerFibre ctx := by
  have h4 := termChernoff_faithful_le_four budget ctx
  have hsrc := Y_lt_sourceH1CnlBudgetPerFibre ctx
  have hL : (15421 : ℝ) ≤ ((shellLadderDepth ctx : ℕ) : ℝ) := by
    exact_mod_cast shellLadderDepth_ge_15421 ctx
  rw [n24CarryData_Y_eq_div] at hsrc
  linarith

/-- **The class-0 frozen term is below ONE routed start's excess** — the razor inequality
in its quantitative form: `termChernoff(frozen) ≤ 4 < L/64 ≤ windowExcess(k)` for every
class-0 routed `k`. -/
theorem tfaChernoff_frozen_lt_singleExcess
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0) :
    termChernoff (faithfulCapacityPhases budget ctx).toClosurePhaseData
      < windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T := by
  have hY := Y_le_windowExcess_of_mem_routedFibre ctx.n24CarryData (budget ctx).route 0 hk
  have h4 := termChernoff_faithful_le_four budget ctx
  have hL : (15421 : ℝ) ≤ ((shellLadderDepth ctx : ℕ) : ℝ) := by
    exact_mod_cast shellLadderDepth_ge_15421 ctx
  rw [n24CarryData_Y_eq_div] at hY
  linarith

/-! ## Part 3.  The corrected per-phase data, all six slots saturated

Each datum keeps the structural fields demanded by its factory record and re-scales the
scalar normalization so the realized term SATURATES the consumed per-class budget cap
`c⋆·ξ·X/6` exactly (the class-3 term is an ℕ count, so it takes the floor
`⌊31·X/1536⌋` — within `1` of the cap).  Every `manuscript_bound`/`hSmall` field holds
with equality, so the corrected phases remain consumable by the global budget machinery. -/

/-- **The corrected class-0 (Chernoff) phase datum**: one path of cost `0` carrying the
full per-class share as weight; `z = 1`, so the §22 moment bookkeeping is exact and
`manuscript_bound` holds with equality. -/
def correctedChernoffData (ctx : ActualFailureContext) :
    ChernoffPathData erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : ℝ) where
  α := Unit
  paths := {Unit.unit}
  weight := fun _ => erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6
  cost := fun _ => 0
  Y := 0
  m := 0
  z := 1
  root := erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6
  A := 1
  weight_nonneg := fun _ _ => tfaShareTerm_nonneg ctx
  z_ge_one := le_rfl
  moment_bound := by
    unfold weightedMoment
    rw [Finset.sum_singleton]
  manuscript_bound := by
    norm_num

/-- **The corrected class-2 (Tower) phase datum**: one charged exit carrying the full
per-class share; `hSummable`/`hSmall` hold with equality. -/
def correctedTowerData (ctx : ActualFailureContext) :
    TowerTransientFactoryData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : ℝ) where
  entryExitSet := {towerExitOf 0}
  chargedWeight := fun _ =>
    erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6
  chargedWeight_nonneg := fun _ _ => tfaShareTerm_nonneg ctx
  outputBoundConstant := erdos260Constants.cStar * erdos260Constants.ξ
    * (ctx.shell.X : ℝ) / 6
  nextLayerMass := 1
  smallError := 0
  hSummable := by
    rw [Finset.sum_singleton]
    norm_num
  hSmall := by norm_num

/-- **The corrected class-3 (DensePack) phase datum**: `⌊31·X/1536⌋` markers at spread
`0`, density constant `cStarSmall = c⋆·ξ/6`; `hsmall` holds with equality. -/
def correctedDensePackData (ctx : ActualFailureContext) :
    DensePackFactoryData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : ℝ) where
  densePackPoints := Finset.range (31 * ctx.shell.X / 1536)
  markersCard := 31 * ctx.shell.X / 1536
  spread := 0
  cStarSmall := erdos260Constants.cStar * erdos260Constants.ξ / 6
  hcover := by
    rw [Finset.card_range]
    omega
  hcount := by
    rw [tfaCstarXi_eq]
    have hdiv : 31 * ctx.shell.X / 1536 * 1536 ≤ 31 * ctx.shell.X :=
      Nat.div_mul_le_self _ _
    have hcast : ((31 * ctx.shell.X / 1536 : ℕ) : ℝ) * 1536
        ≤ 31 * (ctx.shell.X : ℝ) := by exact_mod_cast hdiv
    linarith
  hsmall := le_of_eq (by push_cast; ring)

/-- **The corrected class-4 (Return) phase datum**: the OLC slot carries the full
per-class share (`c₃ = c⋆/6`, `s = ij = 1`); all four envelope bounds and `hSmall` hold
with equality. -/
def correctedReturnData (ctx : ActualFailureContext) :
    ReturnFactoryData erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : ℝ) where
  ordinaryShort := 0
  semiperiodic := 0
  olc := erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6
  nonlocalLong := 0
  c1 := 0
  c2 := 0
  c3 := erdos260Constants.cStar / 6
  c4 := 0
  s := 1
  ij := 1
  smallError := 0
  hOrdinaryShort := le_of_eq (by ring)
  hSemiperiodic := le_of_eq (by ring)
  hOLC := le_of_eq (by ring)
  hNonlocalLong := le_of_eq (by ring)
  hSmall := le_of_eq (by ring)

/-- **The corrected class-5 (Run) phase datum**: `runMass` is the full per-class share,
realized through the `X·|I_j|·2^{−cY}` slot at `|I_j| = 1`, `2^{−cY} := c⋆·ξ/6`;
`trichotomy`/`hSmall` hold with equality.  This REPLACES the circular faithful freeze
`runMass := routedClassMassOf … 5` by a genuine non-circular capacity. -/
def correctedRunData (ctx : ActualFailureContext) :
    RunFactoryData erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : ℝ) where
  runMass := erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6
  nextTower := 0
  nextReturn := 0
  nextDensePack := 0
  twoNegcY := erdos260Constants.cStar * erdos260Constants.ξ / 6
  Ij := 1
  smallError := 0
  trichotomy := le_of_eq (by ring)
  hSmall := le_of_eq (by ring)

/-- **The fully-corrected six-phase assembly**: ALL SIX slots saturated at the in-tree
per-class budget cap (the class-1 slot is the audit's `correctedCnlData`).  Budget-free:
every slot is read off the context alone. -/
def correctedAllPhases (ctx : ActualFailureContext) :
    SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : ℝ) where
  chernoff := correctedChernoffData ctx
  cnl := correctedCnlData ctx
  tower := correctedTowerData ctx
  densePack := correctedDensePackData ctx
  returnPkg := correctedReturnData ctx
  run := correctedRunData ctx

/-! ### The six corrected terms, evaluated exactly -/

/-- `termChernoff(correctedAll) = c⋆·ξ·X/6 = (31/1536)·X` exactly. -/
theorem termChernoff_correctedAll_eq (ctx : ActualFailureContext) :
    termChernoff (correctedAllPhases ctx).toClosurePhaseData
      = erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 := by
  show weightedMass
      (highCostSet ({Unit.unit} : Finset Unit) (fun _ => 0) 0)
      (fun _ => erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6)
    = erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6
  unfold weightedMass highCostSet
  rw [Finset.filter_true_of_mem (fun p _ => Nat.le_refl 0), Finset.sum_singleton]

/-- `termCnl(correctedAll) = c⋆·ξ·X/6` exactly (the audit's corrected class-1 value,
re-evaluated on the fully-corrected assembly). -/
theorem termCnl_correctedAll_eq (ctx : ActualFailureContext) :
    termCnl (correctedAllPhases ctx).toClosurePhaseData
      = erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 := by
  have h0 : termCnl (correctedAllPhases ctx).toClosurePhaseData
      = cleanCNLKraftSum (selectedTransitions (liftTransitionsOfShell ctx))
          (fun t => (bndHeightNatOfShell ctx t : ℝ)) 0
        * (erdos260Constants.cStar * erdos260Constants.ξ
            / (6 * ((selectedTransitions (liftTransitionsOfShell ctx)).card : ℝ)))
        * (ctx.shell.X : ℝ) * 1 := rfl
  rw [h0, cleanCNLKraftSum_c_zero, mul_one, correctedCnl_collapse]
  ring

/-- `termTower(correctedAll) = c⋆·ξ·X/6` exactly. -/
theorem termTower_correctedAll_eq (ctx : ActualFailureContext) :
    termTower (correctedAllPhases ctx).toClosurePhaseData
      = erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 := by
  show (∑ _b ∈ ({towerExitOf 0} : Finset TowerExit),
      erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6)
    = erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6
  rw [Finset.sum_singleton]

/-- `termDensePack(correctedAll) = ⌊31·X/1536⌋` exactly (the term is an ℕ count). -/
theorem termDensePack_correctedAll_eq (ctx : ActualFailureContext) :
    termDensePack (correctedAllPhases ctx).toClosurePhaseData
      = ((31 * ctx.shell.X / 1536 : ℕ) : ℝ) := by
  show ((Finset.range (31 * ctx.shell.X / 1536)).card : ℝ)
    = ((31 * ctx.shell.X / 1536 : ℕ) : ℝ)
  rw [Finset.card_range]

/-- The corrected class-3 term saturates its cap to within one unit:
`c⋆·ξ·X/6 − 1 < termDensePack(correctedAll) ≤ c⋆·ξ·X/6`. -/
theorem termDensePack_correctedAll_saturates (ctx : ActualFailureContext) :
    erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 - 1
      < termDensePack (correctedAllPhases ctx).toClosurePhaseData ∧
    termDensePack (correctedAllPhases ctx).toClosurePhaseData
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 := by
  constructor
  · rw [termDensePack_correctedAll_eq, tfaCstarXi_eq]
    have h : 31 * ctx.shell.X < 1536 * (31 * ctx.shell.X / 1536) + 1536 := by omega
    have hcast : 31 * (ctx.shell.X : ℝ)
        < 1536 * ((31 * ctx.shell.X / 1536 : ℕ) : ℝ) + 1536 := by exact_mod_cast h
    linarith
  · exact termDensePack_le_budget (correctedAllPhases ctx).toClosurePhaseData

/-- `termReturn(correctedAll) = c⋆·ξ·X/6` exactly. -/
theorem termReturn_correctedAll_eq (ctx : ActualFailureContext) :
    termReturn (correctedAllPhases ctx).toClosurePhaseData
      = erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 := by
  show (0 : ℝ) + 0
      + erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 + 0
    = erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6
  ring

/-- `termRun(correctedAll) = c⋆·ξ·X/6` exactly (`rfl`). -/
theorem termRun_correctedAll_eq (ctx : ActualFailureContext) :
    termRun (correctedAllPhases ctx).toClosurePhaseData
      = erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 := rfl

/-! ### The consumption arithmetic survives with all six terms at their caps -/

/-- The fully-corrected total phase mass still fits the global budget:
`ClosurePhaseMass(correctedAll) ≤ c⋆·ξ·X = (31/256)·X` (the generic per-term budget
lemmas apply — every internal bound holds with equality). -/
theorem tfaCorrectedAll_phaseMass_le (ctx : ActualFailureContext) :
    ClosurePhaseMass (correctedAllPhases ctx).toClosurePhaseData
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) :=
  ClosurePhaseMass_le_budget (correctedAllPhases ctx).toClosurePhaseData
    (Nat.cast_nonneg _)

/-- **The contradiction margin is intact**: the saturated total `(31/256)·X` stays
strictly below the pressure floor `c_pr·X = X/2` — `1/2 > 31/256`, so each of the six
classes can take its FULL cap independently and the global contradiction survives. -/
theorem tfaCorrectedTotal_lt_floor (ctx : ActualFailureContext) :
    erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ)
      < erdos260Constants.cPr * (ctx.shell.X : ℝ) := by
  rw [tfaCstarXi_eq, show erdos260Constants.cPr = (1 / 2 : ℝ) from rfl]
  have hX : (0 : ℝ) < (ctx.shell.X : ℝ) := ctx.shell.X_pos_real
  linarith

/-! ## Part 4.  Monotone domination: every frozen term is below its corrected one -/

/-- The frozen Chernoff term is dominated by the corrected one
(`4 ≤ (31/1536)·X` for `X ≥ 2²⁸`). -/
theorem tfaChernoff_frozen_le_correctedAll
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    termChernoff (faithfulCapacityPhases budget ctx).toClosurePhaseData
      ≤ termChernoff (correctedAllPhases ctx).toClosurePhaseData := by
  have h4 := termChernoff_faithful_le_four budget ctx
  have hX := shell_X_ge_real ctx
  rw [termChernoff_correctedAll_eq, tfaCstarXi_eq]
  linarith

/-- The frozen clean-CNL term is dominated by the corrected one
(`7/32 ≤ (31/1536)·X`). -/
theorem tfaCnl_frozen_le_correctedAll
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    termCnl (faithfulCapacityPhases budget ctx).toClosurePhaseData
      ≤ termCnl (correctedAllPhases ctx).toClosurePhaseData := by
  have h7 := termCnl_faithful_le_7_32 budget ctx
  have hX := shell_X_ge_real ctx
  rw [termCnl_correctedAll_eq, tfaCstarXi_eq]
  linarith

/-- The frozen DensePack marker count is dominated by the corrected floor
(`|actualPoints| ≤ c⋆·ξ·X/6` forces `|actualPoints| ≤ ⌊31·X/1536⌋` in ℕ). -/
theorem tfaDensePack_frozen_le_correctedAll
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    termDensePack (faithfulCapacityPhases budget ctx).toClosurePhaseData
      ≤ termDensePack (correctedAllPhases ctx).toClosurePhaseData := by
  have hcap := termDensePack_le_budget (faithfulCapacityPhases budget ctx).toClosurePhaseData
  have heq : termDensePack (faithfulCapacityPhases budget ctx).toClosurePhaseData
      = (((faithfulCapacityPhases budget ctx).densePack.densePackPoints.card : ℕ) : ℝ) :=
    rfl
  rw [heq] at hcap ⊢
  rw [tfaCstarXi_eq] at hcap
  rw [termDensePack_correctedAll_eq]
  have hnat : 1536 * (faithfulCapacityPhases budget ctx).densePack.densePackPoints.card
      ≤ 31 * ctx.shell.X := by
    have hr : (1536 : ℝ)
          * (((faithfulCapacityPhases budget ctx).densePack.densePackPoints.card : ℕ) : ℝ)
        ≤ 31 * (ctx.shell.X : ℝ) := by linarith
    exact_mod_cast hr
  have hdiv : (faithfulCapacityPhases budget ctx).densePack.densePackPoints.card
      ≤ 31 * ctx.shell.X / 1536 := by omega
  exact_mod_cast hdiv

/-- The frozen Tower term is dominated by the corrected one (the routed class-2 mass fits
its own budget slot). -/
theorem tfaTower_frozen_le_correctedAll
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    termTower (faithfulCapacityPhases budget ctx).toClosurePhaseData
      ≤ termTower (correctedAllPhases ctx).toClosurePhaseData := by
  rw [termTower_faithfulCapacityPhases, termTower_correctedAll_eq]
  exact (budget ctx).towerSlot

/-- The frozen Return term is dominated by the corrected one. -/
theorem tfaReturn_frozen_le_correctedAll
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    termReturn (faithfulCapacityPhases budget ctx).toClosurePhaseData
      ≤ termReturn (correctedAllPhases ctx).toClosurePhaseData := by
  rw [termReturn_faithfulCapacityPhases, termReturn_correctedAll_eq]
  exact (budget ctx).returnSlot

/-- The frozen (circular) Run term is dominated by the corrected one. -/
theorem tfaRun_frozen_le_correctedAll
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    termRun (faithfulCapacityPhases budget ctx).toClosurePhaseData
      ≤ termRun (correctedAllPhases ctx).toClosurePhaseData := by
  rw [termRun_faithfulCapacityPhases, termRun_correctedAll_eq]
  exact (budget ctx).runSlot

/-! ### The de-razoring inequalities -/

/-- **Class-0 de-razored**: the corrected Chernoff capacity absorbs a FULL pinned excess
on every shell (`Y = L/64 < (31/1536)·X`) — in sharp contrast with the frozen razor
(`termChernoff(frozen) < windowExcess(k)` at any fibre member). -/
theorem tfaY_lt_termChernoff_correctedAll (ctx : ActualFailureContext) :
    ctx.n24CarryData.Y < termChernoff (correctedAllPhases ctx).toClosurePhaseData := by
  rw [termChernoff_correctedAll_eq, tfaCstarXi_eq, n24CarryData_Y_eq_div]
  have hXeq : ctx.shell.X = 2 ^ shellLadderDepth ctx :=
    Classical.choose_spec ctx.shell.hXdyadic
  have hL : shellLadderDepth ctx < ctx.shell.X := by
    rw [hXeq]; exact Nat.lt_two_pow_self
  have hLr : ((shellLadderDepth ctx : ℕ) : ℝ) < (ctx.shell.X : ℝ) := by exact_mod_cast hL
  have hX0 : (0 : ℝ) ≤ (ctx.shell.X : ℝ) := Nat.cast_nonneg _
  linarith

/-- **Class-5 de-razored**: `Y < termRun(correctedAll)` — the corrected run capacity is a
genuine non-circular budget absorbing a full pinned excess. -/
theorem tfaY_lt_termRun_correctedAll (ctx : ActualFailureContext) :
    ctx.n24CarryData.Y < termRun (correctedAllPhases ctx).toClosurePhaseData := by
  rw [termRun_correctedAll_eq, tfaCstarXi_eq, n24CarryData_Y_eq_div]
  have hXeq : ctx.shell.X = 2 ^ shellLadderDepth ctx :=
    Classical.choose_spec ctx.shell.hXdyadic
  have hL : shellLadderDepth ctx < ctx.shell.X := by
    rw [hXeq]; exact Nat.lt_two_pow_self
  have hLr : ((shellLadderDepth ctx : ℕ) : ℝ) < (ctx.shell.X : ℝ) := by exact_mod_cast hL
  have hX0 : (0 : ℝ) ≤ (ctx.shell.X : ℝ) := Nat.cast_nonneg _
  linarith

/-- **Class-3 de-razored**: `Y < termDensePack(correctedAll)` (via the one-unit
saturation margin: `(31/1536)·X − 1 < ⌊31·X/1536⌋` and `L/64 + 1 ≤ (31/1536)·X`). -/
theorem tfaY_lt_termDensePack_correctedAll (ctx : ActualFailureContext) :
    ctx.n24CarryData.Y < termDensePack (correctedAllPhases ctx).toClosurePhaseData := by
  have hsat := (termDensePack_correctedAll_saturates ctx).1
  rw [tfaCstarXi_eq] at hsat
  rw [n24CarryData_Y_eq_div]
  have hXeq : ctx.shell.X = 2 ^ shellLadderDepth ctx :=
    Classical.choose_spec ctx.shell.hXdyadic
  have hL : shellLadderDepth ctx < ctx.shell.X := by
    rw [hXeq]; exact Nat.lt_two_pow_self
  have hLr : ((shellLadderDepth ctx : ℕ) : ℝ) < (ctx.shell.X : ℝ) := by exact_mod_cast hL
  have hX := shell_X_ge_real ctx
  linarith

/-! ## Part 5.  The fully-corrected ledger bridge -/

/-- **The fully-corrected ctx-pinned P9 ledger residual**: the five per-context ledger
bounds over `correctedAllPhases` (ALL SIX phase terms saturated at their caps) plus
class-6 vacancy.  The class-0/1/3 capacities are the corrected shares instead of the
frozen `O(1)`/sub-excess values; the TRT capacities are the genuine non-circular caps
instead of the routed masses themselves. -/
structure FullyCorrectedP9LedgerResidual where
  /-- The shared seven-class routed budget (the class 2/4/5 capacity slots). -/
  budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx
  /-- Class 0, against the corrected Chernoff capacity `(31/1536)·X`. -/
  hChernoff : ∀ ctx : ActualFailureContext,
    routedClassMassOf ctx.n24CarryData (budget ctx).route 0
      ≤ termChernoff (correctedAllPhases ctx).toClosurePhaseData
  /-- Class 1, against the corrected clean-CNL capacity `(31/1536)·X`. -/
  hCnl : ∀ ctx : ActualFailureContext,
    routedClassMassOf ctx.n24CarryData (budget ctx).route 1
      ≤ termCnl (correctedAllPhases ctx).toClosurePhaseData
  /-- Class 3, against the corrected DensePack capacity `⌊31·X/1536⌋`. -/
  hDensePack : ∀ ctx : ActualFailureContext,
    routedClassMassOf ctx.n24CarryData (budget ctx).route 3
      ≤ termDensePack (correctedAllPhases ctx).toClosurePhaseData
  /-- Classes 2+4+5 jointly, against the corrected (saturated, non-circular) TRT caps. -/
  hTRT : ∀ ctx : ActualFailureContext,
    routedClassMassOf ctx.n24CarryData (budget ctx).route 2
        + routedClassMassOf ctx.n24CarryData (budget ctx).route 4
        + routedClassMassOf ctx.n24CarryData (budget ctx).route 5
      ≤ termTower (correctedAllPhases ctx).toClosurePhaseData
        + termReturn (correctedAllPhases ctx).toClosurePhaseData
        + termRun (correctedAllPhases ctx).toClosurePhaseData
  /-- Class 6, the old-residual class, vacant. -/
  hOldRes : ∀ ctx : ActualFailureContext,
    routedClassMassOf ctx.n24CarryData (budget ctx).route 6 ≤ 0

namespace FullyCorrectedP9LedgerResidual

/-- The per-context seven-class routed package at `oldResMass = 0` over the
fully-corrected phases. -/
def routingZero (R : FullyCorrectedP9LedgerResidual) (ctx : ActualFailureContext) :
    RoutedHighExcessChargeDataOldRes (correctedAllPhases ctx) ctx.n24CarryData 0 where
  route := (R.budget ctx).route
  hChernoff := R.hChernoff ctx
  hCnl := R.hCnl ctx
  hDensePack := R.hDensePack ctx
  hTRT := R.hTRT ctx
  hOldRes := R.hOldRes ctx

/-- The fully-corrected actual-assembly inputs. -/
def toActualInputs (R : FullyCorrectedP9LedgerResidual) :
    GlobalAssemblyActualInputs where
  carryData := fun ctx => ctx.n24CarryData
  chernoff := fun ctx => (correctedAllPhases ctx).chernoff
  cnl := fun ctx => (correctedAllPhases ctx).cnl
  densePack := fun ctx => (correctedAllPhases ctx).densePack
  tower := fun ctx => (correctedAllPhases ctx).tower
  returnPkg := fun ctx => (correctedAllPhases ctx).returnPkg
  run := fun ctx => (correctedAllPhases ctx).run
  highExcessCharge := fun ctx => by
    change HighExcessChargeData (correctedAllPhases ctx) ctx.n24CarryData
    exact (R.routingZero ctx).toHighExcessChargeData_of_oldRes_nonpos le_rfl

/-- **The fully-corrected ledger bridge**: the residual proves `Erdos260Statement`
through the polymorphic actual assembly. -/
theorem toStatement (R : FullyCorrectedP9LedgerResidual) : Erdos260Statement :=
  erdos260_final_actual R.toActualInputs

/-- **Monotone weakening**: the OLD (all-terms-frozen) routed-zero pinned residual
implies the fully-corrected residual — every frozen term is dominated by its corrected
one, so the corrected surface is never harder. -/
def ofPinnedRoutingZero (R : P9CtxPinnedRoutingZeroResidual) :
    FullyCorrectedP9LedgerResidual where
  budget := R.budget
  hChernoff := fun ctx => by
    have h := (R.routingZero ctx).hChernoff
    rw [R.route_eq ctx] at h
    exact le_trans h (tfaChernoff_frozen_le_correctedAll R.budget ctx)
  hCnl := fun ctx => by
    have h := (R.routingZero ctx).hCnl
    rw [R.route_eq ctx] at h
    exact le_trans h (tfaCnl_frozen_le_correctedAll R.budget ctx)
  hDensePack := fun ctx => by
    have h := (R.routingZero ctx).hDensePack
    rw [R.route_eq ctx] at h
    exact le_trans h (tfaDensePack_frozen_le_correctedAll R.budget ctx)
  hTRT := fun ctx => by
    rw [termTower_correctedAll_eq, termReturn_correctedAll_eq, termRun_correctedAll_eq]
    have h2 := (R.budget ctx).towerSlot
    have h4 := (R.budget ctx).returnSlot
    have h5 := (R.budget ctx).runSlot
    linarith
  hOldRes := fun ctx => by
    have h := (R.routingZero ctx).hOldRes
    rw [R.route_eq ctx] at h
    exact h

/-- **The fully-corrected residual from the three genuine-route count-cap gates**: over
any genuine-routed budget, ONLY the class-0/1/3 absorption gates are needed — the TRT row
closes from the budget slots themselves (the corrected caps EQUAL the slot caps) and
class 6 from the genuine route's vacancy. -/
def ofGenuineCaps
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (hroute : ∀ ctx : ActualFailureContext, (budget ctx).route = genuineChargeRoute ctx)
    (hcap0 : ∀ ctx : ActualFailureContext,
      ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card : ℝ)
          * runDyadicMult ctx
        ≤ termChernoff (correctedAllPhases ctx).toClosurePhaseData)
    (hcap1 : ∀ ctx : ActualFailureContext,
      ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
          * ctx.n24CarryData.Y
        ≤ termCnl (correctedAllPhases ctx).toClosurePhaseData)
    (hcap3 : ∀ ctx : ActualFailureContext,
      ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 3).card : ℝ)
          * runDyadicMult ctx
        ≤ termDensePack (correctedAllPhases ctx).toClosurePhaseData) :
    FullyCorrectedP9LedgerResidual where
  budget := budget
  hChernoff := fun ctx => by
    rw [hroute ctx]
    exact le_trans (tfaMass_le_card_mul_mult ctx (genuineChargeRoute ctx) 0) (hcap0 ctx)
  hCnl := fun ctx => by
    rw [hroute ctx, routedClassMass_one_eq_card_mul_Y]
    exact hcap1 ctx
  hDensePack := fun ctx => by
    rw [hroute ctx]
    exact le_trans (tfaMass_le_card_mul_mult ctx (genuineChargeRoute ctx) 3) (hcap3 ctx)
  hTRT := fun ctx => by
    rw [termTower_correctedAll_eq, termReturn_correctedAll_eq, termRun_correctedAll_eq]
    have h2 := (budget ctx).towerSlot
    have h4 := (budget ctx).returnSlot
    have h5 := (budget ctx).runSlot
    linarith
  hOldRes := fun ctx => by
    rw [hroute ctx]
    exact le_of_eq (genuineChargeRoute_routed6_zero ctx)

end FullyCorrectedP9LedgerResidual

/-- Final endpoint from the fully-corrected ctx-pinned P9 ledger residual. -/
theorem erdos260_of_fullyCorrectedLedger
    (R : FullyCorrectedP9LedgerResidual) : Erdos260Statement :=
  R.toStatement

/-- Sanity commutation: the old pinned routed-zero residual reaches the statement through
the fully-corrected bridge as well. -/
theorem erdos260_of_pinnedRoutingZero_via_fullyCorrected
    (R : P9CtxPinnedRoutingZeroResidual) : Erdos260Statement :=
  (FullyCorrectedP9LedgerResidual.ofPinnedRoutingZero R).toStatement

/-! ## Part 6.  Class-0 closures: the survivor absorption (THE PRIZE) -/

/-- **Generic count-cap absorption for the corrected class-0 ledger bound** (the class-0
analogue of the audit's `correctedHCnl_of_card_cap`). -/
theorem tfaCorrectedHChernoff_of_card_cap
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext)
    (hroute : (budget ctx).route = genuineChargeRoute ctx)
    (n : ℕ)
    (hcard : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card ≤ n)
    (habs : (n : ℝ) * runDyadicMult ctx
        ≤ termChernoff (correctedAllPhases ctx).toClosurePhaseData) :
    routedClassMassOf ctx.n24CarryData (budget ctx).route 0
      ≤ termChernoff (correctedAllPhases ctx).toClosurePhaseData := by
  rw [hroute]
  refine le_trans (tfaMass_le_card_mul_mult ctx (genuineChargeRoute ctx) 0)
    (le_trans ?_ habs)
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (runDyadicMult_nonneg ctx)

/-- The 19 class-0 survivor pairs all sit at `q ≤ 45 ≤ 2²⁰`. -/
theorem tfaClass0Survivor_q_le (ctx : ActualFailureContext)
    (h : Class0DatumSurvivor ctx) :
    (class1SlopeDatum ctx).q ≤ 1048576 := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    (rw [h.1]; omega)

/-- **The survivor regime floor (wave 10 applies at ALL nineteen pairs)**: every class-0
survivor context has `L ≥ 986876` — far above the generic wave-8 floor `493461`. -/
theorem tfaClass0Survivor_depth_ge (ctx : ActualFailureContext)
    (h : Class0DatumSurvivor ctx) :
    986876 ≤ shellLadderDepth ctx :=
  floorPushV2_depth_of_q_le_2pow20 ctx (tfaClass0Survivor_q_le ctx h)

/-- Every class-0 survivor context has `r ≥ 63`. -/
theorem tfaClass0Survivor_r_ge (ctx : ActualFailureContext)
    (h : Class0DatumSurvivor ctx) :
    63 ≤ ctx.n24CarryData.r :=
  floorPushV2_r_ge_63_of_q_le_2pow20 ctx (tfaClass0Survivor_q_le ctx h)

/-- The survivor periods are bounded: `class0SurvivorPeriod q ≤ 18` for every `q`. -/
theorem tfaClass0SurvivorPeriod_le_18 (q : ℕ) : class0SurvivorPeriod q ≤ 18 := by
  unfold class0SurvivorPeriod
  split_ifs <;> norm_num

/-- The survivor periods are positive: `1 ≤ class0SurvivorPeriod q`. -/
theorem tfaClass0SurvivorPeriod_pos (q : ℕ) : 1 ≤ class0SurvivorPeriod q := by
  unfold class0SurvivorPeriod
  split_ifs <;> norm_num

/-- **HONEST: the spaced-singleton regime is VACUOUS at every survivor pair** — `r ≥ 63`
forces window width `W ≥ 64 > 18 ≥ c`, so the wave `|fibre₀| ≤ 1` lever
(`ofcClass0Fibre_card_le_one_of_survivor`) never fires on an actual context. -/
theorem tfaClass0Survivor_singletonRegime_vacuous (ctx : ActualFailureContext)
    (h : Class0DatumSurvivor ctx) :
    ¬ ((supportShell ctx.shell.d ctx.shell.X).card
        ≤ class0SurvivorPeriod (class1SlopeDatum ctx).q) := by
  intro hW
  have hr := tfaClass0Survivor_r_ge ctx h
  have hw := cnlMulti_r_add_one_le_width ctx
  have hp := tfaClass0SurvivorPeriod_le_18 (class1SlopeDatum ctx).q
  omega

/-- **The survivor absorption (count-cap side)**: at any survivor pair, the gate-free
count cap `|fibre₀| ≤ ⌈W/c⌉` plus the ℕ absorption gate
`1536·⌈W/c⌉·(r+1)(L+B+1) ≤ 31·X` bound the class-0 count×multiplier product by the
corrected Chernoff capacity. -/
theorem tfaClass0SurvivorAbsorption (ctx : ActualFailureContext)
    (hsurv : Class0DatumSurvivor ctx)
    (hgate : 1536 * (((supportShell ctx.shell.d ctx.shell.X).card
            + class0SurvivorPeriod (class1SlopeDatum ctx).q - 1)
          / class0SurvivorPeriod (class1SlopeDatum ctx).q * tfaNatMult ctx)
        ≤ 31 * ctx.shell.X) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card : ℝ)
        * runDyadicMult ctx
      ≤ termChernoff (correctedAllPhases ctx).toClosurePhaseData := by
  set m := ((supportShell ctx.shell.d ctx.shell.X).card
      + class0SurvivorPeriod (class1SlopeDatum ctx).q - 1)
    / class0SurvivorPeriod (class1SlopeDatum ctx).q with hm
  have hcard : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card ≤ m :=
    ofcClass0Fibre_card_le_of_survivor ctx hsurv
  have hcardR : ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card : ℝ)
      ≤ (m : ℝ) := by exact_mod_cast hcard
  have h1 : ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card : ℝ)
        * runDyadicMult ctx
      ≤ (m : ℝ) * ((tfaNatMult ctx : ℕ) : ℝ) :=
    mul_le_mul hcardR (tfaRunDyadicMult_le_natMult ctx) (runDyadicMult_nonneg ctx)
      (Nat.cast_nonneg m)
  have h2 : (1536 : ℝ) * ((m * tfaNatMult ctx : ℕ) : ℝ) ≤ 31 * (ctx.shell.X : ℝ) := by
    exact_mod_cast hgate
  have hmn : (m : ℝ) * ((tfaNatMult ctx : ℕ) : ℝ) = ((m * tfaNatMult ctx : ℕ) : ℝ) := by
    push_cast
    ring
  rw [termChernoff_correctedAll_eq, tfaCstarXi_eq]
  linarith

/-- **THE PRIZE, conditional form**: at every one of the 19 survivor pairs the corrected
class-0 ledger bound closes from the per-pair ℕ absorption gate — NO fibre emptiness is
demanded (the frozen term demanded outright emptiness, `tfaClass0Razor`).  This is the
exact class-0 analogue of the audit's class-1 count-cap closure. -/
theorem tfaCorrectedHChernoff_of_survivor
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext)
    (hroute : (budget ctx).route = genuineChargeRoute ctx)
    (hsurv : Class0DatumSurvivor ctx)
    (hgate : 1536 * (((supportShell ctx.shell.d ctx.shell.X).card
            + class0SurvivorPeriod (class1SlopeDatum ctx).q - 1)
          / class0SurvivorPeriod (class1SlopeDatum ctx).q * tfaNatMult ctx)
        ≤ 31 * ctx.shell.X) :
    routedClassMassOf ctx.n24CarryData (budget ctx).route 0
      ≤ termChernoff (correctedAllPhases ctx).toClosurePhaseData := by
  rw [hroute]
  exact le_trans (tfaMass_le_card_mul_mult ctx (genuineChargeRoute ctx) 0)
    (tfaClass0SurvivorAbsorption ctx hsurv hgate)

/-- **The old demand implies the new one**: class-0 fibre emptiness (the wave-16
capstone's `class0Fibre` survivor conjunct) yields the absorption input for free — the
corrected surface is strictly weaker at every survivor pair. -/
theorem tfaClass0Absorption_of_fibreEmpty (ctx : ActualFailureContext)
    (h : routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0 = ∅) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card : ℝ)
        * runDyadicMult ctx
      ≤ termChernoff (correctedAllPhases ctx).toClosurePhaseData := by
  rw [h]
  simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
  rw [termChernoff_correctedAll_eq]
  exact tfaShareTerm_nonneg ctx

/-- The pointwise consumption of the corrected capstone surface: any inhabitant of
`Erdos260CorrectedResidual` supplies the survivor-pair class-0 absorption (through its
emptiness field — monotone direction only; the converse needs only the numeric gate). -/
theorem tfaSurvivorAbsorption_of_correctedResidual (R : Erdos260CorrectedResidual)
    (ctx : ActualFailureContext) (hsurv : Class0DatumSurvivor ctx) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card : ℝ)
        * runDyadicMult ctx
      ≤ termChernoff (correctedAllPhases ctx).toClosurePhaseData :=
  tfaClass0Absorption_of_fibreEmpty ctx ((R.class0Fibre ctx).1 hsurv)

/-- **HONEST L-regime accounting (class 0)**: the absorption gate can NEVER be discharged
from the in-tree failure cap `W < (17/2²⁴)·X` alone — even at the largest survivor period
`c = 18`, the worst-case count `(17/2²⁴)·X/18` times the proved multiplier floor
`runDyadicMult ≥ 31·L ≥ 31·493461` EXCEEDS the corrected capacity `(31/1536)·X` at every
actual context.  (The W-cap-only sufficient regime needs `L ≲ 642·c ≤ 11556`, against the
unconditional floor `L ≥ 493461`.)  The gate is a genuine narrow-support condition. -/
theorem tfaClass0Gate_not_from_failureCap (ctx : ActualFailureContext) :
    erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6
      < 17 / 16777216 * (ctx.shell.X : ℝ) / 18 * runDyadicMult ctx := by
  have hmult := tfaRunDyadicMult_ge_31L ctx
  have hL : (493461 : ℝ) ≤ ((shellLadderDepth ctx : ℕ) : ℝ) := by
    exact_mod_cast shellLadderDepth_ge_493461 ctx
  have hX : (0 : ℝ) < (ctx.shell.X : ℝ) := ctx.shell.X_pos_real
  have h15 : (15297291 : ℝ) ≤ runDyadicMult ctx := by linarith
  have hc : (0 : ℝ) ≤ 17 / 16777216 * (ctx.shell.X : ℝ) / 18 := by positivity
  have h1 : 17 / 16777216 * (ctx.shell.X : ℝ) / 18 * 15297291
      ≤ 17 / 16777216 * (ctx.shell.X : ℝ) / 18 * runDyadicMult ctx :=
    mul_le_mul_of_nonneg_left h15 hc
  rw [tfaCstarXi_eq]
  nlinarith [h1, hX]

/-! ## Part 7.  Class-3 closures: the corrected DensePack absorption -/

/-- **Generic count-cap absorption for the corrected class-3 ledger bound.** -/
theorem tfaCorrectedHDensePack_of_card_cap
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext)
    (hroute : (budget ctx).route = genuineChargeRoute ctx)
    (n : ℕ)
    (hcard : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 3).card ≤ n)
    (habs : (n : ℝ) * runDyadicMult ctx
        ≤ termDensePack (correctedAllPhases ctx).toClosurePhaseData) :
    routedClassMassOf ctx.n24CarryData (budget ctx).route 3
      ≤ termDensePack (correctedAllPhases ctx).toClosurePhaseData := by
  rw [hroute]
  refine le_trans (tfaMass_le_card_mul_mult ctx (genuineChargeRoute ctx) 3)
    (le_trans ?_ habs)
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (runDyadicMult_nonneg ctx)

/-- **The corrected class-3 closure from the ℕ width gate**
`W·(r+1)(L+B+1) ≤ ⌊31·X/1536⌋`: the generic width cap `|fibre₃| ≤ W` plus the multiplier
skeleton bound absorb the routed class-3 mass into the corrected DensePack capacity —
compare the faithful demand, the amortized Nat-cover against the marker count
`|proofV4DensePackActualPoints|` (`amortizedCover_iff_nat_of_r_ge_one`), which charged
each marker ONE unit. -/
theorem tfaCorrectedHDensePack_of_widthGate
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext)
    (hroute : (budget ctx).route = genuineChargeRoute ctx)
    (hgate : (supportShell ctx.shell.d ctx.shell.X).card * tfaNatMult ctx
        ≤ 31 * ctx.shell.X / 1536) :
    routedClassMassOf ctx.n24CarryData (budget ctx).route 3
      ≤ termDensePack (correctedAllPhases ctx).toClosurePhaseData := by
  apply tfaCorrectedHDensePack_of_card_cap budget ctx hroute
    ((supportShell ctx.shell.d ctx.shell.X).card)
    (tfaFibre_card_le_width ctx (genuineChargeRoute ctx) 3)
  rw [termDensePack_correctedAll_eq]
  have h1 : ((supportShell ctx.shell.d ctx.shell.X).card : ℝ) * runDyadicMult ctx
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card : ℝ) * ((tfaNatMult ctx : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left (tfaRunDyadicMult_le_natMult ctx) (Nat.cast_nonneg _)
  have h2 : (((supportShell ctx.shell.d ctx.shell.X).card * tfaNatMult ctx : ℕ) : ℝ)
      ≤ ((31 * ctx.shell.X / 1536 : ℕ) : ℝ) := by exact_mod_cast hgate
  have hcast : ((supportShell ctx.shell.d ctx.shell.X).card : ℝ)
        * ((tfaNatMult ctx : ℕ) : ℝ)
      = (((supportShell ctx.shell.d ctx.shell.X).card * tfaNatMult ctx : ℕ) : ℝ) := by
    push_cast
    ring
  linarith

/-! ## Part 8.  Class-5 closures: the corrected Run term against the band-4 split -/

/-- **The corrected class-5 closure from the count×multiplier gate** (the band-4-free
conjunct's demand measured against the corrected term): on the genuine route,
`|fibre₅|·runDyadicMult ≤ (31/1536)·X` closes the corrected run ledger row. -/
theorem tfaCorrectedHRun_of_gate
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext)
    (hroute : (budget ctx).route = genuineChargeRoute ctx)
    (hgate : ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card : ℝ)
          * runDyadicMult ctx
        ≤ termRun (correctedAllPhases ctx).toClosurePhaseData) :
    routedClassMassOf ctx.n24CarryData (budget ctx).route 5
      ≤ termRun (correctedAllPhases ctx).toClosurePhaseData := by
  rw [hroute]
  exact le_trans (em_class5Mass_le_card_mul ctx) hgate

/-- **The band-4 collision (the corrected run bound is FALSE there)**: at every
band-4-pinned context the relocated pressure floor `(511/1024)·X·(r+1)` already exceeds
the corrected capacity `(31/1536)·X`, so the corrected class-5 ledger row CANNOT hold on
the genuine route — the wave-16 voiding reading (`runBand4Void`) is forced against the
corrected term exactly as it was against the Section 26 numeric. -/
theorem tfaBand4_correctedRun_false (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 4) :
    ¬ (routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
        ≤ termRun (correctedAllPhases ctx).toClosurePhaseData) := by
  intro hle
  have h1 : 511 / 512 * ((1 / 2 : ℝ) * (ctx.shell.X : ℝ) * ((ctx.n24CarryData.r : ℝ) + 1))
      ≤ routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5 :=
    band4_pressure_in_class5 ctx hpin
  rw [termRun_correctedAll_eq, tfaCstarXi_eq] at hle
  have hX : (0 : ℝ) < (ctx.shell.X : ℝ) := ctx.shell.X_pos_real
  have hr : (0 : ℝ) ≤ (ctx.n24CarryData.r : ℝ) := Nat.cast_nonneg _
  nlinarith [h1, hle, hX, hr, mul_nonneg hX.le hr]

/-- The band-4 collision in gate form: at band-4-pinned contexts even the
count×multiplier ABSORPTION gate is false (the demand-side floor
`(511/1024)·X·(r+1) ≤ |fibre₅|·runDyadicMult` overwhelms the corrected capacity). -/
theorem tfaBand4_correctedRunGate_false (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 4) :
    ¬ (((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card : ℝ)
          * runDyadicMult ctx
        ≤ termRun (correctedAllPhases ctx).toClosurePhaseData) := by
  intro hgate
  have h1 := band4_class5_demand_floor ctx hpin
  rw [termRun_correctedAll_eq, tfaCstarXi_eq] at hgate
  have hX : (0 : ℝ) < (ctx.shell.X : ℝ) := ctx.shell.X_pos_real
  have hr : (0 : ℝ) ≤ (ctx.n24CarryData.r : ℝ) := Nat.cast_nonneg _
  nlinarith [h1, hgate, hX, hr, mul_nonneg hX.le hr]

/-- **Sharper still: at band-4-pinned contexts NO genuine-routed budget exists at all** —
the budget's own `runSlot` (`routedClassMassOf … 5 ≤ c⋆·ξ·X/6`) is already false there.
The band-4 data must be routed outside the Section 26 run lane (L.3/M.5), as the
manuscript does. -/
theorem tfaBand4_no_genuine_budget (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 4)
    (b : SeparatedPhaseRoutedBudget ctx)
    (hroute : b.route = genuineChargeRoute ctx) :
    False := by
  have hslot := b.runSlot
  rw [hroute] at hslot
  have h1 : 511 / 512 * ((1 / 2 : ℝ) * (ctx.shell.X : ℝ) * ((ctx.n24CarryData.r : ℝ) + 1))
      ≤ routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5 :=
    band4_pressure_in_class5 ctx hpin
  rw [tfaCstarXi_eq] at hslot
  have hX : (0 : ℝ) < (ctx.shell.X : ℝ) := ctx.shell.X_pos_real
  have hr : (0 : ℝ) ≤ (ctx.n24CarryData.r : ℝ) := Nat.cast_nonneg _
  nlinarith [h1, hslot, hX, hr, mul_nonneg hX.le hr]

/-! ## Part 9.  Honest status inventory and the audit block -/

/-- Machine-readable, honest status of the three term-freeze audits. -/
def termFreezeAuditsStatus : List String :=
  [ "OBJECTS: the class-0/3/5 capacity terms of the P9 ledger (termChernoff / " ++
      "termDensePack / termRun over faithfulCapacityPhases), consumed by toStatement " ++
      "through RoutedHighExcessChargeDataOldRes.highExcess_le_phaseMass_add_oldRes " ++
      "against the cPr*X = X/2 floor and the cStar*xi*X/6 per-phase caps - the same " ++
      "consumption point as the wave-16 class-1 audit (LedgerCalibrationAudit).",
    "FREEZE VERDICT, CLASS 0 (PROVED): termChernoff(faithful) = chernoffModelArea in " ++
      "[1,4], SHELL-INDEPENDENT (tfaChernoffFrozenValue/Bounds, re-exports of " ++
      "termChernoff_faithful_eq) - the source 22.1A/H.1 area budget C_Q*X*|I_j|*2^(-cY) " ++
      "(tex lines 2725-2740; per-class budgets xi*s*X*|I_j| growing in the stage, H.2' " ++
      "lines 2755-2768) frozen to the FOUR-PATH model leaf {0,1}^2 at Y := 0 with no " ++
      "X*|I_j| scaling.  Since every routed class-0 start carries excess >= Y = L/64 >= " ++
      "15421/64 > 4, the frozen class-0 ledger bound IS fibre emptiness (tfaClass0Razor) " ++
      "- the demand the corrected capstone's class0Fibre field makes at the 19 survivor " ++
      "pairs; frozen < one single excess < source budget at the evaluation point " ++
      "(tfaChernoff_frozen_lt_singleExcess, tfaChernoff_frozen_lt_sourceH1).",
    "FREEZE VERDICT, CLASS 3 (PROVED): termDensePack(faithful) = " ++
      "|proofV4DensePackActualPoints| (tfaDensePackFrozenValue, re-export) - a raw " ++
      "marker COUNT charging each K.1 marker ONE unit, while each routed class-3 start " ++
      "carries up to runDyadicMult >= 31*L excess (tfaRunDyadicMult_ge_31L, from the " ++
      "wave-8 r >= 32); the source charges the class by the stage-growing " ++
      "xi*s*X*|I_j| budget (H.2'/H.3', K.1.2 multiplier linear in the active floor), " ++
      "never unit-per-marker.  The freeze is in the per-element calibration, not the " ++
      "count magnitude (the count fits the cap, termDensePack_le_budget).",
    "FREEZE VERDICT, CLASS 5 (PROVED, rfl): termRun(faithful) = routedClassMassOf " ++
      "(budget).route 5 (tfaRunFrozenCircular, re-export of " ++
      "termRun_faithfulCapacityPhases) - a CIRCULAR freeze: the capacity equals the " ++
      "demand, the faithful TRT ledger row carries no independent run content, and the " ++
      "whole run constraint lives in the budget's runSlot HYPOTHESIS.",
    "CORRECTED TERMS (PROVED, all evaluated exactly): correctedAllPhases saturates ALL " ++
      "SIX slots at the in-tree per-class cap - termChernoff = termCnl = termTower = " ++
      "termReturn = termRun = cStar*xi*X/6 = (31/1536)*X exactly " ++
      "(term*_correctedAll_eq), termDensePack = floor(31*X/1536) (Nat count; within 1 " ++
      "of the cap, termDensePack_correctedAll_saturates); every manuscript_bound/hSmall " ++
      "field holds with equality.  THE SUM CHECK: all six caps total cStar*xi*X = " ++
      "(31/256)*X < X/2 = cPr*X (tfaCorrectedAll_phaseMass_le, " ++
      "tfaCorrectedTotal_lt_floor: 1/2 > 31/256) - each class takes its full cap " ++
      "INDEPENDENTLY and the pressure-floor contradiction survives.",
    "FULLY-CORRECTED LEDGER BRIDGE (PROVED): FullyCorrectedP9LedgerResidual carries the " ++
      "five ledger bounds over correctedAllPhases + class-6 vacancy; toStatement " ++
      "reaches Erdos260Statement through RoutedHighExcessChargeDataOldRes (oldResMass = " ++
      "0) -> erdos260_final_actual.  ofPinnedRoutingZero: the OLD frozen residual " ++
      "implies the fully-corrected one (all six tfa*_frozen_le_correctedAll dominations " ++
      "- never harder).  ofGenuineCaps: over any genuine-routed budget ONLY the three " ++
      "class-0/1/3 count-cap absorption gates are needed - the TRT row closes from the " ++
      "budget slots themselves (corrected caps EQUAL slot caps) and class 6 from " ++
      "genuineChargeRoute_routed6_zero.  De-razoring: Y < corrected term on all three " ++
      "audited lanes (tfaY_lt_term*_correctedAll).",
    "CLASS-0 CLOSURES (THE PRIZE, conditional - PROVED): mass0 <= |fibre0|*runDyadicMult " ++
      "(tfaMass_le_card_mul_mult, the proved ungated window ceiling); at every survivor " ++
      "pair |fibre0| <= ceil(W/c) (ofcClass0Fibre_card_le_of_survivor, gate-free), so " ++
      "the Nat gate 1536*ceil(W/c)*(r+1)(L+B+1) <= 31*X closes the corrected class-0 " ++
      "ledger bound (tfaCorrectedHChernoff_of_survivor) - ABSORPTION instead of the " ++
      "emptiness razor, exactly as the class-1 lane was de-razored.  Old demand => new " ++
      "demand: emptiness yields the absorption for free " ++
      "(tfaClass0Absorption_of_fibreEmpty, tfaSurvivorAbsorption_of_correctedResidual).",
    "CLASS-0 HONEST L-REGIME: the gate is NOT dischargeable from the in-tree failure " ++
      "cap W < (17/2^24)*X alone - the worst-case count (17/2^24)*X/18 times the proved " ++
      "multiplier floor 31*L (>= 31*493461) EXCEEDS (31/1536)*X at EVERY actual context " ++
      "(tfaClass0Gate_not_from_failureCap; the W-cap-only sufficient regime needs L <= " ++
      "~642*c <= 11556 vs the unconditional floor L >= 493461 - empty).  At the 19 " ++
      "survivor pairs the proved regime is q <= 45 < 2^20, hence L >= 986876 and r >= " ++
      "63 (tfaClass0Survivor_depth_ge/_r_ge - the wave-10 small-q floors apply at ALL " ++
      "nineteen pairs, NOT just the generic wave-8 L >= 493461); the spaced-singleton " ++
      "lever W <= c is VACUOUS there (r >= 63 forces W >= 64 > 18 >= c, " ++
      "tfaClass0Survivor_singletonRegime_vacuous).  The gate is a genuine narrow-support " ++
      "condition (roughly W <= ~c*X/(50*runDyadicMult)) - conditional per context; no " ++
      "survivor pair closes unconditionally.",
    "CLASS-3 CLOSURES (conditional - PROVED): mass3 <= |fibre3|*runDyadicMult with the " ++
      "generic width cap |fibre3| <= W (tfaFibre_card_le_width); the Nat width gate " ++
      "W*(r+1)(L+B+1) <= floor(31*X/1536) closes the corrected class-3 bound " ++
      "(tfaCorrectedHDensePack_of_widthGate, generic form _of_card_cap).  Same honest " ++
      "narrow-support regime as class 0 (the failure cap alone cannot discharge it); " ++
      "the corrected demand replaces the faithful unit-per-marker Nat-cover " ++
      "(amortizedCover_iff_nat_of_r_ge_one) by a capacity 31X/1536 >> any in-window " ++
      "marker count.",
    "CLASS-5 CLOSURES (the band-4 split is decisive - PROVED): on band-4-pinned " ++
      "contexts the corrected run bound is FALSE (tfaBand4_correctedRun_false: the " ++
      "relocated pressure floor (511/1024)*X*(r+1) > (31/1536)*X at every scale, every " ++
      "r >= 0), the absorption gate is FALSE (tfaBand4_correctedRunGate_false), and " ++
      "indeed NO genuine-routed budget exists at all (tfaBand4_no_genuine_budget: the " ++
      "runSlot itself fails) - the wave-16 voiding reading (runBand4Void; route band-4 " ++
      "data through L.3/M.5) is FORCED against the corrected term exactly as against " ++
      "the Section 26 numeric.  On band-4-free contexts the corrected run row is the " ++
      "conditional count*multiplier gate (tfaCorrectedHRun_of_gate via " ++
      "em_class5Mass_le_card_mul).",
    "WHAT STAYS OPEN (honest): the three absorption gates are per-context numeric " ++
      "conditions on the ACTUAL support width W - no in-tree cap discharges them " ++
      "(proved impossible from the failure cap alone) and no per-pair width pins exist " ++
      "for the 19 survivors; the class-1 gate (24*n*L <= 31*X, " ++
      "correctedAbsorption_of_nat_gate) remains conditional likewise; band-4-pinned " ++
      "contexts are excluded from the genuine-routed surface entirely (their lane is " ++
      "the voiding demand).  Nothing here closes the global P9 residual; the " ++
      "fully-corrected surface is the faithful re-calibration of all six lanes plus " ++
      "its proved partial closures.  r = 0 / L <= 15420 relief is VACUOUS everywhere " ++
      "(n24_r_pos, shellLadderDepth_ge_15421) - recorded, not used.",
    "PATCH TARGETS (formal side only; the source H.1/H.2'/K.4 calibration is " ++
      "consistent): chernoff22_1ALeafOfShell (the four-path Y := 0 model leaf - read " ++
      "the genuine area envelope at the active floor), the K.1 unit-per-marker charge " ++
      "behind termDensePack_faithful_eq, and runLeafOfRouted's runMass := routed mass " ++
      "(the circular slot) - all three are, inside the in-tree X-unit ledger, exactly " ++
      "the correctedAllPhases re-scaling constructed here." ]

theorem termFreezeAuditsStatus_nonempty : termFreezeAuditsStatus ≠ [] := by
  simp [termFreezeAuditsStatus]

/-! ### Axiom audit -/

#print axioms tfaCstarXi_eq
#print axioms tfaShareTerm_nonneg
#print axioms tfaRunDyadicMult_le_natMult
#print axioms tfaRunDyadicMult_ge_31L
#print axioms tfaMass_le_card_mul_mult
#print axioms tfaFibre_card_le_width
#print axioms tfaChernoffFrozenValue
#print axioms tfaChernoffFrozenBounds
#print axioms tfaClass0Razor
#print axioms tfaDensePackFrozenValue
#print axioms tfaRunFrozenCircular
#print axioms tfaChernoff_frozen_lt_sourceH1
#print axioms tfaChernoff_frozen_lt_singleExcess
#print axioms correctedChernoffData
#print axioms correctedTowerData
#print axioms correctedDensePackData
#print axioms correctedReturnData
#print axioms correctedRunData
#print axioms correctedAllPhases
#print axioms termChernoff_correctedAll_eq
#print axioms termCnl_correctedAll_eq
#print axioms termTower_correctedAll_eq
#print axioms termDensePack_correctedAll_eq
#print axioms termDensePack_correctedAll_saturates
#print axioms termReturn_correctedAll_eq
#print axioms termRun_correctedAll_eq
#print axioms tfaCorrectedAll_phaseMass_le
#print axioms tfaCorrectedTotal_lt_floor
#print axioms tfaChernoff_frozen_le_correctedAll
#print axioms tfaCnl_frozen_le_correctedAll
#print axioms tfaDensePack_frozen_le_correctedAll
#print axioms tfaTower_frozen_le_correctedAll
#print axioms tfaReturn_frozen_le_correctedAll
#print axioms tfaRun_frozen_le_correctedAll
#print axioms tfaY_lt_termChernoff_correctedAll
#print axioms tfaY_lt_termRun_correctedAll
#print axioms tfaY_lt_termDensePack_correctedAll
#print axioms FullyCorrectedP9LedgerResidual.routingZero
#print axioms FullyCorrectedP9LedgerResidual.toActualInputs
#print axioms FullyCorrectedP9LedgerResidual.toStatement
#print axioms FullyCorrectedP9LedgerResidual.ofPinnedRoutingZero
#print axioms FullyCorrectedP9LedgerResidual.ofGenuineCaps
#print axioms erdos260_of_fullyCorrectedLedger
#print axioms erdos260_of_pinnedRoutingZero_via_fullyCorrected
#print axioms tfaCorrectedHChernoff_of_card_cap
#print axioms tfaClass0Survivor_q_le
#print axioms tfaClass0Survivor_depth_ge
#print axioms tfaClass0Survivor_r_ge
#print axioms tfaClass0SurvivorPeriod_le_18
#print axioms tfaClass0SurvivorPeriod_pos
#print axioms tfaClass0Survivor_singletonRegime_vacuous
#print axioms tfaClass0SurvivorAbsorption
#print axioms tfaCorrectedHChernoff_of_survivor
#print axioms tfaClass0Absorption_of_fibreEmpty
#print axioms tfaSurvivorAbsorption_of_correctedResidual
#print axioms tfaClass0Gate_not_from_failureCap
#print axioms tfaCorrectedHDensePack_of_card_cap
#print axioms tfaCorrectedHDensePack_of_widthGate
#print axioms tfaCorrectedHRun_of_gate
#print axioms tfaBand4_correctedRun_false
#print axioms tfaBand4_correctedRunGate_false
#print axioms tfaBand4_no_genuine_budget
#print axioms termFreezeAuditsStatus_nonempty

end

end Erdos260
