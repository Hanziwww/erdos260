import Erdos260.SCCPersistence
import Erdos260.RunNumericSettlement

/-!
# Exit-mass transcription at the fixed families (`ExitMassTranscription`)

This module (NEW; it edits no existing file) transcribes the manuscript's exit-MASS
machinery — L.3.1 (tower transient-excursion alternative), M.5.1 (low transient tower
exits), I.3/I.3.1 (tower first-entry/first-exit mass `Tower^{fe/ex} <= Run + Return +
DensePack + VarDrop + CNL-tail + OldRes`) — into the word language at the five fixed
data, and tests whether the exit-mass bounds force `FixedFamilyShellPersistence`.

## Dictionary

At a fixed datum the recurrent band is `g = fixedFamilyRecurrentBand ctx ∈ {2,3,4}`
(`fixedFamilyRecurrentBand_bounds`).  An **exit** (the L.3.1 first-exit of the refined
simple cycle, read on the word) is an index `j` with `hitGap a j ≠ g`; an **excursion**
is a maximal block of consecutive exits.  The reach range `emReach = Ico F (F+W+r)`
covers every gap index touched by some carry-window start (`F = firstIndexAbove X`,
`W = |supportShell|`).  The exit MASS is `emExitMass = Σ_{exits in reach} hitGap` —
the total word length spent deviating from the band AP.

## Part 1 — where the heavy mass lives (the brief's KEY QUESTION, settled)

`em_windowExcess_le_devWindow` (PROVED): the window excess of EVERY start is at most the
exit content of its window — band gaps contribute `(r+1)·g ≤ 4(κL+1) < 2L+1 = T`, below
the threshold, so the entire excess is carried by the deviating gaps.  The heavy mass
LIVES ON THE EXITS.  Combining with the proved Lemma 21.1 pressure floor and the
`(r+1)`-fold window covering (`em_devWindow_sum_le`):

* `fixedFamily_exitMass_lower` (PROVED): **`X ≤ 2·emExitMass`** — at every fixed-family
  hit the word spends at least HALF the dyadic scale deviating.  (The brief conjectured
  `≥ X/256`; the exact constant is `X/2`.)

## Part 2 — the giant-gap escape is BLOCKED; exits are MANY; the dichotomy

`SCCPersistence` recorded the honest limit "(b) an exit COUNT bound cannot void: a single
giant gap pays the floor".  The carry rigidity REVERSES this: every gap in reach is
`≤ L+B+1` (`n24_hitGap_le_reach`, the wave of `pow_two_le_oddpart_of_zero_gap`), so

* `fixedFamily_exitCount_lower` (PROVED): `X ≤ 2·#exits·(L+B+1)` — the word makes
  `≥ X/(2(L+B+1))` exits; deviations occur at positive index density, COFINALLY in the
  window range.  Consequently the named SCC atom is quantitatively REFUTED upward:
  `fixedFamilyWindowExitBound_floor` / `fixedFamilyWindowExitBound_refuted` —
  `FixedFamilyWindowExitBound ctx E` forces `X ≤ 2(E+r)(L+B+1)`, so EVERY subexponential
  exit-count bound is false at every fixed-family hit.  The manuscript's
  transient-excursion alternative can never terminate in an eventually-band state here.
* The dichotomy (`fixedFamily_exit_dichotomy`, PROVED): the band-dominated horn is
  IMPOSSIBLE — `4194304·emBandMass < 17X + 16777216·r` (band gaps cover `< ~2^-17` of
  the shell span, `em_bandMass_le_of_band` + the failure cap) while exits cover `≥ X/2`.
  The deviation-dominated horn forces the LONG-GAP STRUCTURE: `fixedFamily_support_floor`
  `X ≤ 2(W+r)(L+B+1)` — a support-count LOWER bound `W ≥ X/(2(L+B+1)) − r` against
  `hfailure`'s upper cap `W < c₀X`, giving the depth relation
  `fixedFamily_depth_relation` (`2^24·X < 34(L+B+1)X + 2^25(L+B+1)r`, i.e.
  `L+B+1 > ~2^24/34`; numerically subsumed by the wave-8 scale floor but an INDEPENDENT,
  mass-driven mechanism).  Hit planting on band stretches: `em_bandRun_positions`.
  HONEST: the long-gap scenario (word ≈ alternating `~(L+B+1)`-gaps and single hits,
  every window heavy) survives all mass/count accounting here — at deep scales
  `X/(2(L+B+1)) < c₀X`, consistent with `hfailure`; persistence is NOT yet forced.

## Part 3 — the `runNumeric` verdict: OVER-TRANSCRIPTION FOUND (PROVED refutation)

The long-gap structure makes (up to `1/512`) the whole pressure floor sit in class 5
(`band4_pressure_in_class5`), and the proved ungated ceiling gives
`mass₅ ≤ #fibre₅·runDyadicMult` (`em_class5Mass_le_card_mul`).  Hence the demand-side
floor `band4_class5_demand_floor`: `(511/1024)·X·(r+1) ≤ #fibre₅·runDyadicMult`.  The
formalized capstone field `runNumeric` (`Erdos260CycleResidual.runNumeric` =
`RunNumericIneq ctx`) budgets this by `(c⋆ξ/12)·W < (c⋆ξ/12)·c₀·X ≈ 10⁻⁸·X` — a factor
`~5·10⁷·(r+1)` too small:

* `band4_pinned_not_runNumericIneq` (PROVED): at EVERY band-4-pinned context (the fixed
  data `(15,1)`, `(15,2)`, `(105,7)`), `RunNumericIneq ctx` is FALSE — at every scale.
* Even the `X`-scaled budget variant dies: `band4_deep_not_runNumericXBudget` — for
  `r ≥ 20000` (i.e. `L ≳ 3.1·10⁸`) the inequality `c₀·#fibre₅·runDyadicMult ≤ (c⋆ξ/12)·X`
  is also refuted.  NO per-start × worst-case-multiplier charging survives the band-4
  pressure relocation; the faithful Section 26 / L.4 run lane charges first-entry/
  first-exit branches per OUTPUT (I.3: "clean deterministic motion inside the simple
  cycle is not charged as tower area"), not every class-5 window start.
* Consequences (PROVED, additive wiring): supplying the field VOIDS the band-4 families
  (`runNumericIneq_voids_towerFP15_1/_15_2/_105_7`,
  `runNumericSettlementHyp_voids_towerFamilies`), and under `RunNumericSettlementHyp`
  the five-family surface collapses to the two non-tower data `(3,1)`, `(21,3)`
  (`fixedFamilyHit_reduces_of_settlement`).  The honest decomposition
  `runNumericField_iff_band4Void_split`: the field ⟺ (band-4 orbit-pin voiding) ∧ (the
  field on band-4-free contexts).  The first conjunct is exactly (the orbit-pinned form
  of) the deep open axis — the manuscript does NOT demand it in Section 26; it routes it
  through the tower lane.  **The corrected surface is the second conjunct**: demand
  `RunNumericIneq` only at `¬OrbitBandPinned ctx 4` contexts, and route the band-4 data
  to the L.3/M.5 tower-exit machinery (the `FixedFamilyShellPersistence` axis).

Manuscript patch note: the v3-faithful `runNumeric` transcription underbudgets the run
lane by charging `c₀·#fibre₅·max 0((r+1)(L+B+1)−T)` against `(c⋆ξ/12)·|supportShell|`;
at the band-4 fixed data the PROVED floor `mass₅ ≥ (511/1024)X(r+1)` exceeds ANY budget
of shape `C·X` once `r+1 > C·1024·2^24/(511·17)`, and exceeds the support-count budget at
EVERY scale.  L.4.1/L.5 charge runs per output weight; the per-start form is strictly
stronger than the manuscript and must be weakened as above.

No `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Part 0.  The exit/band dictionary on the reach range -/

/-- The first in-shell hit index `F = firstIndexAbove X`. -/
def emF (ctx : ActualFailureContext) : ℕ :=
  ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X

/-- The shell support count `W = |supportShell d X|`. -/
def emW (ctx : ActualFailureContext) : ℕ :=
  (supportShell ctx.shell.d ctx.shell.X).card

/-- The reach range `Ico F (F+W+r)` — every gap index touched by some carry-window
start's descent window (the exact range of the proved gap ceiling
`n24_hitGap_le_reach`). -/
def emReach (ctx : ActualFailureContext) : Finset ℕ :=
  Finset.Ico (emF ctx) (emF ctx + emW ctx + ctx.n24CarryData.r)

/-- The exit weight of an index: its hit gap if it DEVIATES from the recurrent band
(an L.3.1 exit), `0` if it follows the band. -/
def emExitWeight (ctx : ActualFailureContext) (j : ℕ) : ℕ :=
  if hitGap ctx.n24CarryData.a j = fixedFamilyRecurrentBand ctx then 0
  else hitGap ctx.n24CarryData.a j

/-- The exit content of the descent window at start `k`: the total deviating gap length
among its `r+1` gaps. -/
def emDevWindow (ctx : ActualFailureContext) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (ctx.n24CarryData.r + 1), emExitWeight ctx (k + i)

/-- **The exit mass**: the total word length spent deviating from the band AP across the
reach range — the word-level shadow of the I.3 first-exit mass. -/
def emExitMass (ctx : ActualFailureContext) : ℕ :=
  ∑ j ∈ emReach ctx, emExitWeight ctx j

/-- The exit set: the deviating indices of the reach range. -/
def emExitSet (ctx : ActualFailureContext) : Finset ℕ :=
  (emReach ctx).filter
    (fun j => ¬(hitGap ctx.n24CarryData.a j = fixedFamilyRecurrentBand ctx))

/-- The band set: the persistent (band-following) indices of the reach range. -/
def emBandSet (ctx : ActualFailureContext) : Finset ℕ :=
  (emReach ctx).filter
    (fun j => hitGap ctx.n24CarryData.a j = fixedFamilyRecurrentBand ctx)

/-- The band mass: the total word length spent following the band. -/
def emBandMass (ctx : ActualFailureContext) : ℕ :=
  ∑ j ∈ emBandSet ctx, hitGap ctx.n24CarryData.a j

/-- The exit mass is the gap sum over the exit set. -/
theorem emExitMass_eq_sum_exitSet (ctx : ActualFailureContext) :
    emExitMass ctx = ∑ j ∈ emExitSet ctx, hitGap ctx.n24CarryData.a j := by
  unfold emExitMass emExitSet
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro j _
  unfold emExitWeight
  rw [ite_not]

/-- The exit weight never exceeds the gap. -/
theorem emExitWeight_le_hitGap (ctx : ActualFailureContext) (j : ℕ) :
    emExitWeight ctx j ≤ hitGap ctx.n24CarryData.a j := by
  unfold emExitWeight
  by_cases h : hitGap ctx.n24CarryData.a j = fixedFamilyRecurrentBand ctx
  · rw [if_pos h]; omega
  · rw [if_neg h]

/-- Every gap is at most its exit weight plus the band (equality on band indices,
slack `band` on exits). -/
theorem em_hitGap_le_weight_add_band (ctx : ActualFailureContext) (j : ℕ) :
    hitGap ctx.n24CarryData.a j ≤ emExitWeight ctx j + fixedFamilyRecurrentBand ctx := by
  unfold emExitWeight
  by_cases h : hitGap ctx.n24CarryData.a j = fixedFamilyRecurrentBand ctx
  · rw [if_pos h]; omega
  · rw [if_neg h]; omega

/-- **The per-gap rigidity ceiling on the reach range** (the giant-gap blocker): every
gap of the reach range is `≤ L + B + 1` — the carry-rigidity zero-run bound
`n24_hitGap_le_reach`, restated on `emReach`. -/
theorem em_hitGap_le_of_reach (ctx : ActualFailureContext) {j : ℕ}
    (hj : j ∈ emReach ctx) :
    hitGap ctx.n24CarryData.a j
      ≤ shellLadderDepth ctx + carryB ctx.shell.Q + 1 := by
  refine n24_hitGap_le_reach ctx ?_
  unfold emReach emF emW at hj
  rw [Finset.mem_Ico] at hj
  exact hj.2

/-- The reach range has exactly `W + r` indices. -/
theorem em_reach_card (ctx : ActualFailureContext) :
    (emReach ctx).card = emW ctx + ctx.n24CarryData.r := by
  unfold emReach
  rw [Nat.card_Ico]
  omega

/-! ## Part 1.  Where the heavy mass lives: on the exits

The KEY QUESTION of the brief.  Band gaps in a window contribute at most
`(r+1)·band ≤ 4(κL+1) < 2L+1 = T` — below the threshold — so every window's excess is
carried entirely by its DEVIATING gaps. -/

/-- The window gap sum splits below exit content plus the full-band ceiling. -/
theorem em_gapWindow_le (ctx : ActualFailureContext) (k : ℕ) :
    gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
      ≤ emDevWindow ctx k + (ctx.n24CarryData.r + 1) * fixedFamilyRecurrentBand ctx := by
  unfold gapWindow emDevWindow
  calc ∑ i ∈ Finset.range (ctx.n24CarryData.r + 1), hitGap ctx.n24CarryData.a (k + i)
      ≤ ∑ i ∈ Finset.range (ctx.n24CarryData.r + 1),
          (emExitWeight ctx (k + i) + fixedFamilyRecurrentBand ctx) :=
        Finset.sum_le_sum (fun i _ => em_hitGap_le_weight_add_band ctx (k + i))
    _ = (∑ i ∈ Finset.range (ctx.n24CarryData.r + 1), emExitWeight ctx (k + i))
          + (ctx.n24CarryData.r + 1) * fixedFamilyRecurrentBand ctx := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- The full-band window sum sits below the threshold: `(r+1)·band ≤ T = 2L+1`
(for any band `≤ 4`, since `r ≤ κL` with `κ = 17/2^18` and `L ≥ 28`). -/
theorem em_band_mul_le_T (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4) :
    ((ctx.n24CarryData.r : ℝ) + 1) * ((fixedFamilyRecurrentBand ctx : ℕ) : ℝ)
      ≤ ctx.n24CarryData.T := by
  rw [cnlMulti_n24_T_eq]
  have hr := scc_r_le_kappaL ctx
  rw [towerKappa_eq] at hr
  have hL28 : (28 : ℝ) ≤ ((shellLadderDepth ctx : ℕ) : ℝ) := by
    exact_mod_cast shellLadderDepth_ge ctx
  have hb4 : ((fixedFamilyRecurrentBand ctx : ℕ) : ℝ) ≤ 4 := by exact_mod_cast hband
  have hrnn : (0 : ℝ) ≤ (ctx.n24CarryData.r : ℝ) := Nat.cast_nonneg _
  have hmul : ((ctx.n24CarryData.r : ℝ) + 1) * ((fixedFamilyRecurrentBand ctx : ℕ) : ℝ)
      ≤ ((ctx.n24CarryData.r : ℝ) + 1) * 4 :=
    mul_le_mul_of_nonneg_left hb4 (by linarith)
  linarith

/-- **THE KEY-QUESTION ANSWER (PROVED)**: the window excess of EVERY start is at most the
exit content of its window — the heavy mass lives ON the deviating gaps; band-following
stretches contribute nothing to the pressure. -/
theorem em_windowExcess_le_devWindow (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4) (k : ℕ) :
    windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
      ≤ (emDevWindow ctx k : ℝ) := by
  have hgw := em_gapWindow_le ctx k
  have hgwR : ((gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r : ℕ) : ℝ)
      ≤ (emDevWindow ctx k : ℝ)
        + ((ctx.n24CarryData.r : ℝ) + 1) * ((fixedFamilyRecurrentBand ctx : ℕ) : ℝ) := by
    exact_mod_cast hgw
  have hT := em_band_mul_le_T ctx hband
  unfold windowExcess positivePart
  apply max_le
  · linarith
  · exact Nat.cast_nonneg _

/-- **The `(r+1)`-fold window covering**: summing the exit content over all window starts
counts each deviating gap at most `r+1` times. -/
theorem em_devWindow_sum_le (ctx : ActualFailureContext) :
    ∑ k ∈ ctx.n24CarryData.starts, emDevWindow ctx k
      ≤ (ctx.n24CarryData.r + 1) * emExitMass ctx := by
  unfold emDevWindow
  rw [Finset.sum_comm]
  calc ∑ i ∈ Finset.range (ctx.n24CarryData.r + 1),
        ∑ k ∈ ctx.n24CarryData.starts, emExitWeight ctx (k + i)
      ≤ ∑ _i ∈ Finset.range (ctx.n24CarryData.r + 1), emExitMass ctx := by
        refine Finset.sum_le_sum ?_
        intro i hi
        rw [Finset.mem_range] at hi
        have himg : ∑ k ∈ ctx.n24CarryData.starts, emExitWeight ctx (k + i)
            = ∑ j ∈ ctx.n24CarryData.starts.image (fun k => k + i),
                emExitWeight ctx j :=
          (Finset.sum_image (fun x _ y _ h => by omega)).symm
        rw [himg]
        unfold emExitMass
        refine Finset.sum_le_sum_of_subset ?_
        intro j hj
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
        rw [cnlMulti_starts_eq_window, Finset.mem_Ico] at hk
        unfold emReach emF emW
        rw [Finset.mem_Ico]
        omega
    _ = (ctx.n24CarryData.r + 1) * emExitMass ctx := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- The proved Lemma 21.1 pressure floor relocates onto the summed exit content. -/
theorem em_pressure_le_devSum (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4) :
    erdos260Constants.cPr * (ctx.shell.X : ℝ) * ((ctx.n24CarryData.r : ℝ) + 1)
      ≤ ((∑ k ∈ ctx.n24CarryData.starts, emDevWindow ctx k : ℕ) : ℝ) := by
  refine le_trans ctx.n24CarryData.highExcessMass_lower ?_
  unfold highExcessMass
  calc ∑ k ∈ highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
        ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y,
        windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
      ≤ ∑ k ∈ highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
          ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y,
          (emDevWindow ctx k : ℝ) :=
        Finset.sum_le_sum (fun k _ => em_windowExcess_le_devWindow ctx hband k)
    _ ≤ ∑ k ∈ ctx.n24CarryData.starts, (emDevWindow ctx k : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (highExcessStarts_subset _ _ _ _ _)
          (fun i _ _ => Nat.cast_nonneg _)
    _ = ((∑ k ∈ ctx.n24CarryData.starts, emDevWindow ctx k : ℕ) : ℝ) :=
        (Nat.cast_sum _ _).symm

/-- **THE EXIT-MASS FLOOR (core form)**: any band `≤ 4` forces `X ≤ 2·emExitMass` — the
word spends at least half the dyadic scale deviating from the band AP. -/
theorem em_exitMass_lower_of_band (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4) :
    ctx.shell.X ≤ 2 * emExitMass ctx := by
  -- cPr = 1/2 definitionally; retype to avoid the dependent rewrite
  have h1 : (1 / 2 : ℝ) * (ctx.shell.X : ℝ) * ((ctx.n24CarryData.r : ℝ) + 1)
      ≤ ((∑ k ∈ ctx.n24CarryData.starts, emDevWindow ctx k : ℕ) : ℝ) :=
    em_pressure_le_devSum ctx hband
  have h2 : ((∑ k ∈ ctx.n24CarryData.starts, emDevWindow ctx k : ℕ) : ℝ)
      ≤ (((ctx.n24CarryData.r + 1) * emExitMass ctx : ℕ) : ℝ) :=
    Nat.cast_le.mpr (em_devWindow_sum_le ctx)
  rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h2
  have hr1 : (0 : ℝ) < (ctx.n24CarryData.r : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) ctx.n24CarryData.r
    linarith
  have hchain : 1 / 2 * (ctx.shell.X : ℝ) * ((ctx.n24CarryData.r : ℝ) + 1)
      ≤ ((ctx.n24CarryData.r : ℝ) + 1) * (emExitMass ctx : ℝ) := le_trans h1 h2
  have hX2 : (ctx.shell.X : ℝ) ≤ 2 * (emExitMass ctx : ℝ) := by
    by_contra hcon
    push Not at hcon
    have hm := mul_lt_mul_of_pos_left hcon hr1
    linarith
  exact_mod_cast hX2

/-- **THE DEVIATION-MASS THEOREM (headline)**: at every fixed-family hit,
`X ≤ 2·emExitMass` — the manuscript's exit mass is at least `X/2`. -/
theorem fixedFamily_exitMass_lower (ctx : ActualFailureContext)
    (hhit : FixedFamilyHit ctx) :
    ctx.shell.X ≤ 2 * emExitMass ctx :=
  em_exitMass_lower_of_band ctx (fixedFamilyRecurrentBand_bounds ctx hhit).2

/-! ## Part 2.  Many exits, the band-stretch bounds, and the dichotomy -/

/-- The exit mass is capped by count × the rigidity gap ceiling. -/
theorem em_exitMass_le_count_mul (ctx : ActualFailureContext) :
    emExitMass ctx
      ≤ (emExitSet ctx).card * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) := by
  rw [emExitMass_eq_sum_exitSet]
  calc ∑ j ∈ emExitSet ctx, hitGap ctx.n24CarryData.a j
      ≤ ∑ _j ∈ emExitSet ctx, (shellLadderDepth ctx + carryB ctx.shell.Q + 1) := by
        refine Finset.sum_le_sum ?_
        intro j hj
        exact em_hitGap_le_of_reach ctx (Finset.mem_filter.mp hj).1
    _ = (emExitSet ctx).card * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) := by
        rw [Finset.sum_const, smul_eq_mul]

/-- **THE EXIT-COUNT FLOOR (headline)**: at every fixed-family hit,
`X ≤ 2·#exits·(L+B+1)` — at least `X/(2(L+B+1))` exits; deviations are COFINAL in the
window range.  The SCC honest limit "(b) one giant gap pays the floor" is REVERSED:
the rigidity ceiling `hitGap ≤ L+B+1` blocks all giant gaps. -/
theorem fixedFamily_exitCount_lower (ctx : ActualFailureContext)
    (hhit : FixedFamilyHit ctx) :
    ctx.shell.X
      ≤ 2 * ((emExitSet ctx).card * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) :=
  le_trans (fixedFamily_exitMass_lower ctx hhit)
    (Nat.mul_le_mul le_rfl (em_exitMass_le_count_mul ctx))

/-- An in-window exit-count bound caps the reach exit count by `E + r`. -/
theorem em_exitSet_card_le_of_windowExitBound (ctx : ActualFailureContext) {E : ℕ}
    (hE : FixedFamilyWindowExitBound ctx E) :
    (emExitSet ctx).card ≤ E + ctx.n24CarryData.r := by
  unfold FixedFamilyWindowExitBound at hE
  unfold emExitSet emReach emF emW
  set F := ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X with hF
  set W := (supportShell ctx.shell.d ctx.shell.X).card with hW
  set A := (Finset.Ico F (F + W)).filter
    (fun k => hitGap ctx.n24CarryData.a k ≠ fixedFamilyRecurrentBand ctx) with hA
  set B := Finset.Ico (F + W) (F + W + ctx.n24CarryData.r) with hB
  have hsub : (Finset.Ico F (F + W + ctx.n24CarryData.r)).filter
      (fun j => ¬(hitGap ctx.n24CarryData.a j = fixedFamilyRecurrentBand ctx))
      ⊆ A ∪ B := by
    intro j hj
    have hj' := Finset.mem_filter.mp hj
    have hjr := Finset.mem_Ico.mp hj'.1
    rcases Nat.lt_or_ge j (F + W) with hlt | hge
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hjr.1, hlt⟩, hj'.2⟩)
    · exact Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨hge, hjr.2⟩)
  have hBcard : B.card = ctx.n24CarryData.r := by
    rw [hB, Nat.card_Ico]
    omega
  calc ((Finset.Ico F (F + W + ctx.n24CarryData.r)).filter
        (fun j => ¬(hitGap ctx.n24CarryData.a j = fixedFamilyRecurrentBand ctx))).card
      ≤ (A ∪ B).card := Finset.card_le_card hsub
    _ ≤ A.card + B.card := Finset.card_union_le _ _
    _ ≤ E + ctx.n24CarryData.r := by omega

/-- **THE WINDOW-EXIT-BOUND FLOOR**: the named SCC atom `FixedFamilyWindowExitBound ctx E`
forces `X ≤ 2(E+r)(L+B+1)` — the formalizable shadow of the I.3 exit accounting now
carries a quantitative PRICE. -/
theorem fixedFamilyWindowExitBound_floor (ctx : ActualFailureContext)
    (hhit : FixedFamilyHit ctx) {E : ℕ} (hE : FixedFamilyWindowExitBound ctx E) :
    ctx.shell.X
      ≤ 2 * ((E + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) := by
  have h1 := fixedFamily_exitCount_lower ctx hhit
  have h2 := em_exitSet_card_le_of_windowExitBound ctx hE
  calc ctx.shell.X
      ≤ 2 * ((emExitSet ctx).card
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) := h1
    _ ≤ 2 * ((E + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) :=
        Nat.mul_le_mul le_rfl (Nat.mul_le_mul h2 le_rfl)

/-- **Sub-pigeonhole exit bounds are REFUTED at every fixed-family hit**: any
`E < X/(2(L+B+1)) − r` is impossible — in particular every `L`-polynomial bound at
`X = 2^L`.  The manuscript's transient-excursion alternative cannot stabilize. -/
theorem fixedFamilyWindowExitBound_refuted (ctx : ActualFailureContext)
    (hhit : FixedFamilyHit ctx) {E : ℕ}
    (hsmall : 2 * ((E + ctx.n24CarryData.r)
        * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) < ctx.shell.X) :
    ¬ FixedFamilyWindowExitBound ctx E := fun hE =>
  absurd (fixedFamilyWindowExitBound_floor ctx hhit hE) (by omega)

/-- **The band-stretch hit-planting bound**: a finite band run plants hits in an exact
arithmetic progression of step `band` — `a (k₀+m) = a k₀ + m·band` for `m ≤ len`. -/
theorem em_bandRun_positions (ctx : ActualFailureContext) {k₀ len : ℕ}
    (hrun : ∀ i, i < len →
      hitGap ctx.n24CarryData.a (k₀ + i) = fixedFamilyRecurrentBand ctx) :
    ∀ m, m ≤ len →
      ctx.n24CarryData.a (k₀ + m)
        = ctx.n24CarryData.a k₀ + m * fixedFamilyRecurrentBand ctx := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
      intro hm
      have hstep := hitGap_position_step ctx.n24CarryData.carry.hits.strict (k₀ + m)
      rw [show k₀ + (m + 1) = k₀ + m + 1 from by omega, hstep, ih (by omega),
        hrun m (by omega)]
      ring

/-- The band mass is tiny: at most `4·(W+r)` — band stretches plant a hit per index,
so their total length is count-capped. -/
theorem em_bandMass_le_of_band (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4) :
    emBandMass ctx ≤ 4 * (emW ctx + ctx.n24CarryData.r) := by
  unfold emBandMass emBandSet
  calc ∑ j ∈ (emReach ctx).filter
        (fun j => hitGap ctx.n24CarryData.a j = fixedFamilyRecurrentBand ctx),
        hitGap ctx.n24CarryData.a j
      ≤ ∑ _j ∈ (emReach ctx).filter
          (fun j => hitGap ctx.n24CarryData.a j = fixedFamilyRecurrentBand ctx), 4 := by
        refine Finset.sum_le_sum ?_
        intro j hj
        have h := (Finset.mem_filter.mp hj).2
        omega
    _ = ((emReach ctx).filter
          (fun j => hitGap ctx.n24CarryData.a j = fixedFamilyRecurrentBand ctx)).card
            * 4 := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (emW ctx + ctx.n24CarryData.r) * 4 := by
        have hc := Finset.card_filter_le (emReach ctx)
          (fun j => hitGap ctx.n24CarryData.a j = fixedFamilyRecurrentBand ctx)
        rw [em_reach_card] at hc
        exact Nat.mul_le_mul hc le_rfl
    _ = 4 * (emW ctx + ctx.n24CarryData.r) := Nat.mul_comm _ _

/-- The failure cap in strict `ℕ` form: `2^24·W < 17·X`. -/
theorem em_supportShell_strict (ctx : ActualFailureContext) :
    16777216 * emW ctx < 17 * ctx.shell.X := by
  have h := scc_supportShell_lt ctx
  have h2 : (16777216 : ℝ) * ((supportShell ctx.shell.d ctx.shell.X).card : ℝ)
      < 17 * (ctx.shell.X : ℝ) := by linarith
  unfold emW
  exact_mod_cast h2

/-- **The band-dominated horn is VOID**: `2^22·emBandMass < 17·X + 2^24·r` — band
stretches cover under `~2^-17` of the shell scale; the exits cover `≥ 1/2`. -/
theorem fixedFamily_bandMass_lt (ctx : ActualFailureContext)
    (hhit : FixedFamilyHit ctx) :
    4194304 * emBandMass ctx < 17 * ctx.shell.X + 16777216 * ctx.n24CarryData.r := by
  have h1 := em_bandMass_le_of_band ctx (fixedFamilyRecurrentBand_bounds ctx hhit).2
  have h2 := em_supportShell_strict ctx
  have h3 : 4194304 * emBandMass ctx
      ≤ 4194304 * (4 * (emW ctx + ctx.n24CarryData.r)) :=
    Nat.mul_le_mul le_rfl h1
  omega

/-- The exit mass is capped by the full reach span ceiling. -/
theorem em_exitMass_le_reach_span (ctx : ActualFailureContext) :
    emExitMass ctx
      ≤ (emW ctx + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) := by
  unfold emExitMass
  calc ∑ j ∈ emReach ctx, emExitWeight ctx j
      ≤ ∑ _j ∈ emReach ctx, (shellLadderDepth ctx + carryB ctx.shell.Q + 1) := by
        refine Finset.sum_le_sum ?_
        intro j hj
        exact le_trans (emExitWeight_le_hitGap ctx j) (em_hitGap_le_of_reach ctx hj)
    _ = (emReach ctx).card * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ = (emW ctx + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) := by
        rw [em_reach_card]

/-- **The forced LONG-GAP STRUCTURE**: `X ≤ 2(W+r)(L+B+1)` — a support-count LOWER bound
`W ≥ X/(2(L+B+1)) − r` against `hfailure`'s upper cap; the word is exactly
long-gap-sparse (mean in-reach gap `≥ (L+B+1)/...`, each gap `≤ L+B+1`). -/
theorem fixedFamily_support_floor (ctx : ActualFailureContext)
    (hhit : FixedFamilyHit ctx) :
    ctx.shell.X
      ≤ 2 * ((emW ctx + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) :=
  le_trans (fixedFamily_exitMass_lower ctx hhit)
    (Nat.mul_le_mul le_rfl (em_exitMass_le_reach_span ctx))

/-- **The depth relation** (independent, mass-driven; numerically subsumed by the wave-8
scale floor): `2^24·X < 34(L+B+1)X + 2^25(L+B+1)r` — i.e. `L+B+1 ≳ 2^24/34` at every
fixed-family hit, from the exit-mass floor alone. -/
theorem fixedFamily_depth_relation (ctx : ActualFailureContext)
    (hhit : FixedFamilyHit ctx) :
    16777216 * ctx.shell.X
      < 34 * ((shellLadderDepth ctx + carryB ctx.shell.Q + 1) * ctx.shell.X)
        + 33554432 * ((shellLadderDepth ctx + carryB ctx.shell.Q + 1)
            * ctx.n24CarryData.r) := by
  have h1 := fixedFamily_support_floor ctx hhit
  have h2 := em_supportShell_strict ctx
  have h1R : (ctx.shell.X : ℝ)
      ≤ 2 * (((emW ctx : ℝ) + (ctx.n24CarryData.r : ℝ))
          * ((shellLadderDepth ctx : ℝ) + (carryB ctx.shell.Q : ℝ) + 1)) := by
    exact_mod_cast h1
  have h2R : (16777216 : ℝ) * (emW ctx : ℝ) < 17 * (ctx.shell.X : ℝ) := by
    exact_mod_cast h2
  have hL28 : (28 : ℝ) ≤ (shellLadderDepth ctx : ℝ) := by
    exact_mod_cast shellLadderDepth_ge ctx
  have hBnn : (0 : ℝ) ≤ (carryB ctx.shell.Q : ℝ) := Nat.cast_nonneg _
  have hG : (0 : ℝ)
      < 2 * ((shellLadderDepth ctx : ℝ) + (carryB ctx.shell.Q : ℝ) + 1) := by
    linarith
  have h5 := mul_lt_mul_of_pos_right h2R hG
  have hrnn : (0 : ℝ) ≤ (ctx.n24CarryData.r : ℝ) := Nat.cast_nonneg _
  have key : (16777216 : ℝ) * (ctx.shell.X : ℝ)
      < 34 * (((shellLadderDepth ctx : ℝ) + (carryB ctx.shell.Q : ℝ) + 1)
            * (ctx.shell.X : ℝ))
        + 33554432 * (((shellLadderDepth ctx : ℝ) + (carryB ctx.shell.Q : ℝ) + 1)
            * (ctx.n24CarryData.r : ℝ)) := by
    nlinarith [h1R, h5, hrnn, Nat.cast_nonneg (α := ℝ) (emW ctx)]
  exact_mod_cast key

/-- **THE DICHOTOMY THEOREM (packaged)**: at every fixed-family hit the
deviation-dominated horn is FORCED — exits carry `≥ X/2`, band stretches carry
`< (17X + 2^24·r)/2^22`, and the support count is squeezed from below
(`W ≥ X/(2(L+B+1)) − r`): the word has the long-gap structure. -/
theorem fixedFamily_exit_dichotomy (ctx : ActualFailureContext)
    (hhit : FixedFamilyHit ctx) :
    ctx.shell.X ≤ 2 * emExitMass ctx
    ∧ 4194304 * emBandMass ctx < 17 * ctx.shell.X + 16777216 * ctx.n24CarryData.r
    ∧ ctx.shell.X
        ≤ 2 * ((emW ctx + ctx.n24CarryData.r)
            * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) :=
  ⟨fixedFamily_exitMass_lower ctx hhit,
   fixedFamily_bandMass_lt ctx hhit,
   fixedFamily_support_floor ctx hhit⟩

/-! ### The span identity (the exact band/exit split of the traversed positions) -/

/-- Telescoping: positions accumulate the gaps. -/
theorem em_position_telescope (ctx : ActualFailureContext) (s n : ℕ) :
    ctx.n24CarryData.a (s + n)
      = ctx.n24CarryData.a s
        + ∑ i ∈ Finset.range n, hitGap ctx.n24CarryData.a (s + i) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep := hitGap_position_step ctx.n24CarryData.carry.hits.strict (s + n)
      rw [Finset.sum_range_succ, show s + (n + 1) = s + n + 1 from by omega, hstep, ih]
      omega

/-- The reach gap sum in range form. -/
theorem em_reach_sum_eq (ctx : ActualFailureContext) :
    ∑ j ∈ emReach ctx, hitGap ctx.n24CarryData.a j
      = ∑ i ∈ Finset.range (emW ctx + ctx.n24CarryData.r),
          hitGap ctx.n24CarryData.a (emF ctx + i) := by
  unfold emReach
  rw [Finset.sum_Ico_eq_sum_range,
    show emF ctx + emW ctx + ctx.n24CarryData.r - emF ctx
      = emW ctx + ctx.n24CarryData.r from by omega]

/-- **The span identity**: the position swept across the reach range splits exactly into
band mass plus exit mass — `a(F+W+r) = a(F) + emBandMass + emExitMass`. -/
theorem em_span_eq (ctx : ActualFailureContext) :
    ctx.n24CarryData.a (emF ctx + (emW ctx + ctx.n24CarryData.r))
      = ctx.n24CarryData.a (emF ctx) + (emBandMass ctx + emExitMass ctx) := by
  rw [em_position_telescope ctx (emF ctx) (emW ctx + ctx.n24CarryData.r)]
  congr 1
  rw [← em_reach_sum_eq ctx, emExitMass_eq_sum_exitSet]
  unfold emBandMass emBandSet emExitSet
  exact (Finset.sum_filter_add_sum_filter_not (emReach ctx)
    (fun j => hitGap ctx.n24CarryData.a j = fixedFamilyRecurrentBand ctx)
    (hitGap ctx.n24CarryData.a)).symm

/-! ## Part 3.  The `runNumeric` verdict: the formalized field is REFUTED at the
band-4 data — over-transcription found -/

/-- A band-4 orbit pin fixes the recurrent band: `fixedFamilyRecurrentBand = 4`. -/
theorem em_band_eq_four_of_pinned (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 4) : fixedFamilyRecurrentBand ctx = 4 := by
  unfold fixedFamilyRecurrentBand
  exact hpin 1 le_rfl

/-- The exit-mass floor under the band-4 orbit pin alone. -/
theorem orbitBand4_exitMass_lower (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 4) :
    ctx.shell.X ≤ 2 * emExitMass ctx :=
  em_exitMass_lower_of_band ctx (le_of_eq (em_band_eq_four_of_pinned ctx hpin))

/-- The long-gap support floor under the band-4 orbit pin alone. -/
theorem orbitBand4_support_floor (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 4) :
    ctx.shell.X
      ≤ 2 * ((emW ctx + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) :=
  le_trans (orbitBand4_exitMass_lower ctx hpin)
    (Nat.mul_le_mul le_rfl (em_exitMass_le_reach_span ctx))

/-- The class-5 routed mass is count × multiplier bounded — the demand side of the
Section 26 inequality, via the proved ungated ceiling
`n24_windowExcess_le_runDyadicMult`. -/
theorem em_class5Mass_le_card_mul (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
      ≤ ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card : ℝ)
          * runDyadicMult ctx := by
  rw [routedClassMassOf_eq_sum_fibre]
  calc ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5,
        windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
      ≤ ∑ _k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5,
          runDyadicMult ctx := by
        refine Finset.sum_le_sum ?_
        intro k hk
        have hstart : k ∈ ctx.n24CarryData.starts :=
          (mem_highExcessStarts.mp (Finset.mem_filter.mp hk).1).1
        rw [cnlMulti_starts_eq_window, Finset.mem_Ico] at hstart
        exact n24_windowExcess_le_runDyadicMult ctx hstart.2
    _ = ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card : ℝ)
          * runDyadicMult ctx := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- **The demand-side floor at band-4 data**: `(511/1024)·X·(r+1) ≤ #fibre₅·runDyadicMult`
— any budget for the count × multiplier product must beat HALF the relocated pressure
floor.  This is what every `runNumeric`-shaped budget must absorb. -/
theorem band4_class5_demand_floor (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 4) :
    511 / 512 * ((1 / 2 : ℝ) * (ctx.shell.X : ℝ) * ((ctx.n24CarryData.r : ℝ) + 1))
      ≤ ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card : ℝ)
          * runDyadicMult ctx := by
  -- cPr = 1/2 definitionally; retype to avoid the dependent rewrite
  have h1 : 511 / 512 * ((1 / 2 : ℝ) * (ctx.shell.X : ℝ) * ((ctx.n24CarryData.r : ℝ) + 1))
      ≤ routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5 :=
    band4_pressure_in_class5 ctx hpin
  exact le_trans h1 (em_class5Mass_le_card_mul ctx)

/-- **THE OVER-TRANSCRIPTION VERDICT (headline)**: at EVERY band-4-pinned context the
formalized capstone field `runNumeric` (= `RunNumericIneq ctx`, with budget
`(c⋆ξ/12)·|supportShell| < (c⋆ξ/12)·c₀·X ≈ 10⁻⁸·X`) is FALSE — the relocated pressure
floor `(511/1024)·X·(r+1)` overwhelms it at every scale, for every `r ≥ 0`. -/
theorem band4_pinned_not_runNumericIneq (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 4) : ¬ RunNumericIneq ctx := by
  intro hnum
  unfold RunNumericIneq at hnum
  rw [← ActualFailureContext.shell_d ctx, ← ActualFailureContext.shell_X ctx,
    show erdos260Constants.c0 = manuscriptKappa / 64 from rfl, towerKappa_eq,
    show erdos260Constants.cStar = (31 / 16 : ℝ) from rfl,
    show erdos260Constants.ξ = (1 / 16 : ℝ) from rfl] at hnum
  -- cPr = 1/2 definitionally; retype to avoid the dependent rewrite
  have h1 : 511 / 512 * ((1 / 2 : ℝ) * (ctx.shell.X : ℝ) * ((ctx.n24CarryData.r : ℝ) + 1))
      ≤ routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5 :=
    band4_pressure_in_class5 ctx hpin
  have h2 := em_class5Mass_le_card_mul ctx
  have hW := scc_supportShell_lt ctx
  have hX := ctx.shell.X_pos_real
  have hr0 : (0 : ℝ) ≤ (ctx.n24CarryData.r : ℝ) := Nat.cast_nonneg _
  have hc0nn : (0 : ℝ) ≤ 17 / 262144 / 64 := by norm_num
  have h1' := mul_le_mul_of_nonneg_left h1 hc0nn
  have h2' := mul_le_mul_of_nonneg_left h2 hc0nn
  nlinarith [h1', h2', hnum, hW, hX, mul_nonneg hX.le hr0]

/-- The contrapositive: the `runNumeric` field at a context excludes the band-4 orbit
pin — supplying the field IS (at least) the band-4 fixed-point voiding. -/
theorem runNumericIneq_not_band4 (ctx : ActualFailureContext)
    (hnum : RunNumericIneq ctx) : ¬ OrbitBandPinned ctx 4 :=
  fun hpin => band4_pinned_not_runNumericIneq ctx hpin hnum

/-- The `runNumeric` field voids the `(15,1)` tower family. -/
theorem runNumericIneq_voids_towerFP15_1 (ctx : ActualFailureContext)
    (hnum : RunNumericIneq ctx) :
    ¬((class1SlopeDatum ctx).q = 15 ∧ (class1SlopeDatum ctx).K₀ = 1) :=
  fun h => runNumericIneq_not_band4 ctx hnum (orbitBandPinned_15_1 ctx h)

/-- The `runNumeric` field voids the `(15,2)` tower family. -/
theorem runNumericIneq_voids_towerFP15_2 (ctx : ActualFailureContext)
    (hnum : RunNumericIneq ctx) :
    ¬((class1SlopeDatum ctx).q = 15 ∧ (class1SlopeDatum ctx).K₀ = 2) :=
  fun h => runNumericIneq_not_band4 ctx hnum (orbitBandPinned_15_2 ctx h)

/-- The `runNumeric` field voids the `(105,7)` tower family. -/
theorem runNumericIneq_voids_towerFP105_7 (ctx : ActualFailureContext)
    (hnum : RunNumericIneq ctx) :
    ¬((class1SlopeDatum ctx).q = 105 ∧ (class1SlopeDatum ctx).K₀ = 7) :=
  fun h => runNumericIneq_not_band4 ctx hnum (orbitBandPinned_105_7 ctx h)

/-- The run-lane settlement hypothesis (the sharpest in-tree residual feeding the
`runNumeric` field) excludes the band-4 orbit pin at every context. -/
theorem runNumericSettlementHyp_not_band4 (h : RunNumericSettlementHyp)
    (ctx : ActualFailureContext) : ¬ OrbitBandPinned ctx 4 := by
  intro hpin
  rcases Nat.eq_zero_or_pos ctx.n24CarryData.r with hr | hr
  · exact band4_pinned_not_runNumericIneq ctx hpin (runNumericIneq_of_r_eq_zero ctx hr)
  · exact band4_pinned_not_runNumericIneq ctx hpin
      (runNumericIneq_of_cycleNumericCloses ctx (h ctx hr))

/-- The settlement hypothesis voids all three band-4 tower families. -/
theorem runNumericSettlementHyp_voids_towerFamilies (h : RunNumericSettlementHyp)
    (ctx : ActualFailureContext) :
    ¬((class1SlopeDatum ctx).q = 15 ∧ (class1SlopeDatum ctx).K₀ = 1)
    ∧ ¬((class1SlopeDatum ctx).q = 15 ∧ (class1SlopeDatum ctx).K₀ = 2)
    ∧ ¬((class1SlopeDatum ctx).q = 105 ∧ (class1SlopeDatum ctx).K₀ = 7) :=
  ⟨fun hq => runNumericSettlementHyp_not_band4 h ctx (orbitBandPinned_15_1 ctx hq),
   fun hq => runNumericSettlementHyp_not_band4 h ctx (orbitBandPinned_15_2 ctx hq),
   fun hq => runNumericSettlementHyp_not_band4 h ctx (orbitBandPinned_105_7 ctx hq)⟩

/-- **The five-family surface collapses under the run-lane settlement**: any
fixed-family hit must be one of the two non-tower data `(3,1)` or `(21,3)`. -/
theorem fixedFamilyHit_reduces_of_settlement (h : RunNumericSettlementHyp)
    (ctx : ActualFailureContext) (hhit : FixedFamilyHit ctx) :
    ((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1)
    ∨ ((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3) := by
  rcases hhit with h1 | h2 | h3 | h4 | h5
  · exact Or.inl h1
  · exact Or.inr h2
  · exact absurd (orbitBandPinned_15_1 ctx h3)
      (runNumericSettlementHyp_not_band4 h ctx)
  · exact absurd (orbitBandPinned_15_2 ctx h4)
      (runNumericSettlementHyp_not_band4 h ctx)
  · exact absurd (orbitBandPinned_105_7 ctx h5)
      (runNumericSettlementHyp_not_band4 h ctx)

/-- **THE CORRECTED SURFACE (the L.4-faithful split)**: the full `runNumeric` field is
EXACTLY (band-4 orbit-pin voiding) ∧ (the field on band-4-free contexts).  The first
conjunct does not belong to Section 26 — the manuscript routes the band-4 recurrent
data through the L.3/M.5 tower-exit lane; the honest run-lane residual is the second
conjunct alone. -/
theorem runNumericField_iff_band4Void_split :
    (∀ ctx : ActualFailureContext, RunNumericIneq ctx)
      ↔ ((∀ ctx : ActualFailureContext, ¬ OrbitBandPinned ctx 4)
          ∧ (∀ ctx : ActualFailureContext,
              ¬ OrbitBandPinned ctx 4 → RunNumericIneq ctx)) := by
  constructor
  · intro h
    exact ⟨fun ctx => runNumericIneq_not_band4 ctx (h ctx), fun ctx _ => h ctx⟩
  · rintro ⟨hvoid, hoff⟩ ctx
    exact hoff ctx (hvoid ctx)

/-- The `X`-scaled budget variant of the Section 26 inequality (the budget the
manuscript's area ledger would plausibly supply, `(c⋆ξ/12)·X` instead of the
formalized `(c⋆ξ/12)·|supportShell|`). -/
def RunNumericXBudgetIneq (ctx : ActualFailureContext) : Prop :=
  erdos260Constants.c0
      * ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card : ℝ)
      * runDyadicMult ctx
    ≤ (erdos260Constants.cStar * erdos260Constants.ξ / 12) * (ctx.X : ℝ)

/-- **Even the `X`-scaled budget dies at ultra-deep band-4 contexts**: for
`r ≥ 20000` (i.e. `L ≳ 3.1·10⁸`, since `r = ⌊κL⌋`, `κ = 17/2^18`) the relocated floor
`(511/1024)·X·(r+1)` exceeds `(c⋆ξ/(12·c₀))·X ≈ 9959·X`.  NO per-start ×
worst-case-multiplier charging survives the band-4 data; the faithful fix must charge
per EXIT (I.3: cycle interiors are not charged), not per window start. -/
theorem band4_deep_not_runNumericXBudget (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 4) (hdeep : 20000 ≤ ctx.n24CarryData.r) :
    ¬ RunNumericXBudgetIneq ctx := by
  intro hnum
  unfold RunNumericXBudgetIneq at hnum
  rw [← ActualFailureContext.shell_X ctx,
    show erdos260Constants.c0 = manuscriptKappa / 64 from rfl, towerKappa_eq,
    show erdos260Constants.cStar = (31 / 16 : ℝ) from rfl,
    show erdos260Constants.ξ = (1 / 16 : ℝ) from rfl] at hnum
  -- cPr = 1/2 definitionally; retype to avoid the dependent rewrite
  have h1 : 511 / 512 * ((1 / 2 : ℝ) * (ctx.shell.X : ℝ) * ((ctx.n24CarryData.r : ℝ) + 1))
      ≤ routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5 :=
    band4_pressure_in_class5 ctx hpin
  have h2 := em_class5Mass_le_card_mul ctx
  have hX := ctx.shell.X_pos_real
  have hrR : (20000 : ℝ) ≤ (ctx.n24CarryData.r : ℝ) := by exact_mod_cast hdeep
  have hc0nn : (0 : ℝ) ≤ 17 / 262144 / 64 := by norm_num
  have h1' := mul_le_mul_of_nonneg_left h1 hc0nn
  have h2' := mul_le_mul_of_nonneg_left h2 hc0nn
  have hXr : (ctx.shell.X : ℝ) * 20000 ≤ (ctx.shell.X : ℝ) * (ctx.n24CarryData.r : ℝ) :=
    mul_le_mul_of_nonneg_left hrR hX.le
  nlinarith [h1', h2', hnum, hX, hXr]

/-! ## Part 4.  Honest machine-readable status -/

/-- The precise status of the exit-mass transcription pass. -/
def exitMassTranscriptionStatus : List String :=
  [ "MANUSCRIPT TRANSCRIPTION (read fully): L.3.1 routes every transient excursion " ++
      "from a refined recurrent tower SCC to Run/Return/DensePack/Progress/Endpoint/" ++
      "CNL-tail with charged summability; M.5.1 makes clean low transient exits CNL " ++
      "leaves (cost ~X*|Ij|*2^-cY); I.3.1 bounds Tower^{fe/ex} by the package outputs " ++
      "+ VarDrop + CNL tail + OldRes, charging ONLY first-entry/first-exit branches - " ++
      "'clean deterministic motion inside the simple cycle is not charged'.  In the " ++
      "word language at a band-g fixed datum: an exit is a hit gap != g; an excursion " ++
      "is a maximal exit block; the exit MASS is the deviating gap length emExitMass " ++
      "over the reach range Ico F (F+W+r).",
    "KEY QUESTION SETTLED (PROVED, em_windowExcess_le_devWindow): the heavy mass " ++
      "lives ON the exits - band gaps contribute (r+1)*g <= 4(kappaL+1) < 2L+1 = T " ++
      "per window (em_band_mul_le_T), so EVERY window's excess is carried by its " ++
      "deviating gaps.  With the proved Lemma 21.1 floor and the (r+1)-fold covering " ++
      "(em_devWindow_sum_le): fixedFamily_exitMass_lower - X <= 2*emExitMass at every " ++
      "fixed-family hit.  The brief's guess was X/256; the exact constant is X/2.",
    "GIANT-GAP ESCAPE BLOCKED (PROVED): SCCPersistence's honest limit (b) - 'one " ++
      "giant gap pays the floor, so exit COUNTS prove nothing' - is REVERSED by the " ++
      "carry rigidity: every reach gap is <= L+B+1 (n24_hitGap_le_reach), so " ++
      "fixedFamily_exitCount_lower: X <= 2*#exits*(L+B+1) - at least X/(2(L+B+1)) " ++
      "exits, deviations COFINAL in the window range.  The named SCC atom now has a " ++
      "price: fixedFamilyWindowExitBound_floor (X <= 2(E+r)(L+B+1)) and " ++
      "fixedFamilyWindowExitBound_refuted - every subexponential exit-count bound is " ++
      "FALSE at every fixed-family hit.  The L.3 alternative can never stabilize to " ++
      "an eventually-band state at the fixed data; exit-mass accounting alone still " ++
      "does NOT force FixedFamilyShellPersistence (the onset never materializes).",
    "DICHOTOMY (PROVED, fixedFamily_exit_dichotomy): band-domination is IMPOSSIBLE - " ++
      "4194304*emBandMass < 17X + 2^24*r (em_bandMass_le_of_band: band stretches " ++
      "plant a hit per index, count-capped by W+r < c0*X + r) while exits carry >= " ++
      "X/2.  The forced long-gap structure: fixedFamily_support_floor X <= " ++
      "2(W+r)(L+B+1) - a support-count LOWER bound against hfailure's cap, giving " ++
      "fixedFamily_depth_relation 2^24*X < 34(L+B+1)X + 2^25(L+B+1)r (L+B+1 > " ++
      "~2^24/34; an independent mass-driven floor, numerically subsumed by wave 8's " ++
      "X > 2^493460).  Span split: em_span_eq a(F+W+r) = a(F) + bandMass + exitMass; " ++
      "AP planting on band runs: em_bandRun_positions.  HONEST: at deep scales " ++
      "X/(2(L+B+1)) < c0*X, so the long-gap word (every window heavy, ~X/(2L) hits) " ++
      "is CONSISTENT with all mass/count accounting here - persistence is not forced " ++
      "by this route; the orbit/word gap remains.",
    "RUNNUMERIC VERDICT - OVER-TRANSCRIPTION FOUND (PROVED, " ++
      "band4_pinned_not_runNumericIneq): at EVERY band-4-pinned ctx (the fixed data " ++
      "(15,1)/(15,2)/(105,7)) the formalized capstone field runNumeric " ++
      "(RunNumericIneq: c0*#fibre5*runDyadicMult <= (cStar*xi/12)*W) is FALSE at " ++
      "every scale: band4_pressure_in_class5 + the proved ungated ceiling " ++
      "(em_class5Mass_le_card_mul via n24_windowExcess_le_runDyadicMult) give the " ++
      "demand floor (511/1024)*X*(r+1) <= #fibre5*runDyadicMult " ++
      "(band4_class5_demand_floor), while the budget is < (cStar*xi/12)*c0*X ~ " ++
      "10^-8*X.  Even the X-scaled budget (cStar*xi/12)*X dies at r >= 20000, i.e. " ++
      "L >~ 3.1*10^8 (band4_deep_not_runNumericXBudget): NO per-start*worst-" ++
      "multiplier charging survives; the manuscript (I.3/L.4.1/L.5) charges " ++
      "first-entry/first-exit branches per OUTPUT weight, never every class-5 " ++
      "window start.  This is the run-lane sibling of the documented TowerL31I31Core " ++
      "finding (full-mass I.3.1 budget forces X <= 0).",
    "CONSEQUENCES WIRED (PROVED, additive): runNumericIneq_voids_towerFP15_1/_15_2/" ++
      "_105_7 and runNumericSettlementHyp_voids_towerFamilies - supplying the " ++
      "formalized run lane VOIDS the three band-4 fixed families outright; " ++
      "fixedFamilyHit_reduces_of_settlement collapses the five-family surface to " ++
      "(3,1) and (21,3) under RunNumericSettlementHyp.  No free lunch, made exact: " ++
      "runNumericField_iff_band4Void_split - the field IS (band-4 orbit-pin " ++
      "voiding) AND (the field on band-4-free ctx).  The CORRECTED L.4-faithful " ++
      "surface is the second conjunct alone; the band-4 voiding belongs to the " ++
      "tower lane (the FixedFamilyShellPersistence axis), not to Section 26.",
    "MANUSCRIPT PATCH NOTE: the v3-faithful runNumeric transcription demands " ++
      "c0*#fibre5*max0((r+1)(L+B+1)-T) <= (cStar*xi/12)*|supportShell| - at the " ++
      "band-4 data the PROVED relocated floor makes the left side >= " ++
      "c0*(511/1024)*X*(r+1), exceeding the support-count budget at EVERY scale and " ++
      "any C*X budget once r+1 > C*1024*2^24/(511*17).  Patch: restrict the Section " ++
      "26 numeric to contexts whose slope orbit is NOT band-4 pinned (equivalently: " ++
      "charge the run lane per L.4.1-trichotomy output, with cycle interiors " ++
      "uncharged per I.3), and route the band-4 recurrent data to the L.3/M.5 " ++
      "transient-exit machinery.",
    "WHAT REMAINS (the deep axis, unchanged but sharpened): supplying " ++
      "FixedFamilyShellPersistence at the deep fixed data is NOT achieved by " ++
      "exit-mass accounting - the long-gap scenario satisfies every proved bound.  " ++
      "But the burden moved: the run-lane residual (RunNumericSettlementHyp / " ++
      "Class5CycleNumericCloses on r >= 1) now PROVABLY contains the band-4 " ++
      "voiding, so any honest supply of it must come through the tower lane first.  " ++
      "The two non-tower data (3,1)/(21,3) are untouched by the run-lane verdict " ++
      "(their pressure sits in classes 4/3)." ]

/-- The status list is non-empty. -/
theorem exitMassTranscriptionStatus_nonempty : exitMassTranscriptionStatus ≠ [] := by
  simp [exitMassTranscriptionStatus]

/-! ## Part 5.  Axiom-cleanliness audit
Every key declaration; expected axioms `[propext, Classical.choice, Quot.sound]` or
fewer. -/

#print axioms emExitMass_eq_sum_exitSet
#print axioms em_hitGap_le_of_reach
#print axioms em_reach_card
#print axioms em_gapWindow_le
#print axioms em_band_mul_le_T
#print axioms em_windowExcess_le_devWindow
#print axioms em_devWindow_sum_le
#print axioms em_pressure_le_devSum
#print axioms em_exitMass_lower_of_band
#print axioms fixedFamily_exitMass_lower
#print axioms em_exitMass_le_count_mul
#print axioms fixedFamily_exitCount_lower
#print axioms em_exitSet_card_le_of_windowExitBound
#print axioms fixedFamilyWindowExitBound_floor
#print axioms fixedFamilyWindowExitBound_refuted
#print axioms em_bandRun_positions
#print axioms em_bandMass_le_of_band
#print axioms em_supportShell_strict
#print axioms fixedFamily_bandMass_lt
#print axioms em_exitMass_le_reach_span
#print axioms fixedFamily_support_floor
#print axioms fixedFamily_depth_relation
#print axioms fixedFamily_exit_dichotomy
#print axioms em_position_telescope
#print axioms em_span_eq
#print axioms em_band_eq_four_of_pinned
#print axioms orbitBand4_exitMass_lower
#print axioms orbitBand4_support_floor
#print axioms em_class5Mass_le_card_mul
#print axioms band4_class5_demand_floor
#print axioms band4_pinned_not_runNumericIneq
#print axioms runNumericIneq_not_band4
#print axioms runNumericIneq_voids_towerFP15_1
#print axioms runNumericIneq_voids_towerFP15_2
#print axioms runNumericIneq_voids_towerFP105_7
#print axioms runNumericSettlementHyp_not_band4
#print axioms runNumericSettlementHyp_voids_towerFamilies
#print axioms fixedFamilyHit_reduces_of_settlement
#print axioms runNumericField_iff_band4Void_split
#print axioms band4_deep_not_runNumericXBudget
#print axioms exitMassTranscriptionStatus_nonempty

end

end Erdos260
