import Erdos260.Erdos260CorrectedLedgerCapstone
import Erdos260.FloorPushV2
import Erdos260.ReturnFixedPointClosure
import Erdos260.DensePackFixedPointClosure

/-!
# The endgame at the two surviving fixed data (`FixedDataEndgame`)

This module (NEW; it edits no existing file) runs the wave-16 exit-mass template against
the surviving capstone fields at the two non-tower fixed data `(3,1)` (return, band-2
pinned) and `(21,3)` (densepack, band-3 pinned), hunting over-transcriptions #5/#6.

## The `(3,1)` probe — over-transcription #5 FOUND (PROVED refutation)

At every band-2-pinned context the WHOLE pressure floor sits in class 4
(`band2_pressure_in_class4`), so the class-4 fibre is LARGE: the generic count floor
`fde_highExcess_card_floor` (`X ≤ 2·#HE·(L+B+1)`, from the Lemma 21.1 floor + the
ungated per-start ceiling `n24_windowExcess_le_runDyadicMult`) transfers to the fibre
(`band2_class4_card_floor`) because the band-2 pin routes EVERY start to class 4.
Against this, ALL THREE live disjuncts of `ReturnGatesBodyUngated` are FALSE
(`band2_pinned_not_returnGatesBodyUngated`):

* full-span gate `64·(a(F+W+r)−a(F)) < 2(129L+64)`: the span identity `em_span_eq` plus
  the exit-mass floor `X ≤ 2·emExitMass` force `64·span ≥ 32X ≥ 10240·L² ≫ 258L+128`;
* sub-span gate `64·(a(F+W−1)−a(F)) < 129L+64`: the tail `[F+W−1, F+W+r)` carries at
  most `(r+1)(L+B+1) ≤ 4L²`, so the sub-span still holds `≥ 32X − 256L² ≫ 129L+64`;
* cycle-count gate: under the band-2 pin EVERY cycle residue reads band 2, so
  `b₂ = c` and the gate forces `W ≤ t·c ≤ r+1` — against `W ≥ X/(2(L+B+1)) − r`.

The guards do not save the field: the pin refutes `ReturnB2FreeDatum` and
`ReturnB2OneSpacedDatum` (their closures would prove the refuted body), and the numeric
reach hypothesis holds at EVERY context (`fde_returnGates_numeric_guard`).  Hence
`band2_pinned_not_returnGatesInstance`: the `returnGates` field instance is
unsatisfiable at every band-2-pinned context — supplying the field IS (at least) the
band-2 orbit-pin voiding.  The corrected split mirrors the wave-16 run-lane split:
`returnGatesField_iff_band2Void_split` — the field ⟺ (band-2 voiding) ∧ (the field on
band-2-free contexts).  Consumers: `returnGatesField_voids_3_1`; the population bound
`Class4FibreSmall` (`#fibre₄ ≤ r+1`) that the gates feed is refuted directly at the pin
(`band2_pinned_not_class4Small`).

`returnInterior` does NOT refute: at the pin the fibre is the FULL high-excess set, and
the K.1 interior demand is exactly a POSITION constraint — `band2_returnInterior_iff_`
`topBand_light`: the body ⟺ every start in the top band `[F+W−r−1, F+W)` is LIGHT
(`windowExcess < Y`).  The pressure floor forces `≥ X/(2(L+B+1))` heavy starts among
`W < c₀X` — the heavy mass can sit low; the word's choice survives all proved
accounting.  The exact remaining demand is extracted:
`band2_pinned_returnInterior_demand`.

## The `(21,3)` probe — over-transcription #6 FOUND (PROVED refutation)

Under the band-3 pin every start routes to class 3 and `genuineDensePackStarts` IS the
full high-excess set (`band3_genuineStarts_eq`), so `#gdps ≥ X/(2(L+B+1))`.  The
Nat-cover field `ungatedCoverNat` demands
`#gdps·((r+1)(L+B+1) − (2L+1)) ≤ #proofV4DensePackActualPoints`; with `r ≥ 16` the
per-start slack is `≥ 15L`, so the LHS is `≥ 15X/4`, while the RHS is structurally
capped by its ambient window: `≤ 3X + (L+B+2)`.  `15X/4 > 3X + 2L` at every scale
(`X ≥ 320L²`) — the cover is FALSE at every band-3-pinned context
(`band3_pinned_not_coverNat`).  The guards hold at the pin (`¬Class3CycleBand3Free`,
`¬DensePackDatumClosed`, `¬Class3TopBandCycleFree` are all theorems there), so the
field instance is unsatisfiable on the pinned-wide class (pin ∧ the field's own modulus
window `q = 5 ∨ 13 ≤ q`): `band3PinnedWide_not_coverInstance`.  Corrected split:
`densePackCoverField_iff_band3Void_split`; consumer `densePackCoverField_voids_21_3`.

The density field does NOT refute by counting (at `L ≥ 15421` the incidence count
`#gdps·(L/8) ≤ W·(L+B+2)` is consistent), but it carries an extreme extracted demand:
the windows `[k+r, k+r+L+B+1]` live in INDEX-derived positions while support sits in
`(X, 2X]`, so even ONE nonempty window forces `X < F+W+r+(L+B+1)`
(`band3_density_forces_subshell`) and hence `F > (1 − 17/2²⁴)·X − (r+L+B+1)`
(`band3_density_F_floor`): the word must have hits at almost ALL indices below the
shell.  Not refutable here (ones may sit above `X/2²⁰` keeping the value tiny) —
recorded as the exact demand.  The interior field mirrors the return lane:
`band3_densePackInterior_iff_topBand_light`, demand extraction
`band3_pinned_densePackInterior_demand` — satisfiable, genuine.

## The synthesis — the two-data endgame

* `FixedDataEndgameVoiding` (THE NAMED FINAL ATOM): no context realizes `(3,1)` or
  `(21,3)`.  Supplied BY the corrected surface's own fields
  (`fixedDataEndgameVoiding_of_fields`); with the surface's `runBand4Void` this voids
  ALL FIVE fixed families (`fixedFamilyHit_void_of_endgame`).
* Consequently EVERY inhabitant of the wave-16 corrected surface already voids the
  five fixed families outright (`correctedResidual_not_fixedFamilyHit`), supplies the
  deep voiding (`correctedResidual_deepFixedFamilyVoid`), and VACUOUSLY supplies the
  shell-persistence axis (`correctedResidual_deepShellPersistence`) — the
  `FixedFamilyShellPersistence` axis is ABSORBED by the corrected surface: its own
  return/densepack/run fields contain the three voidings.  The no-free-lunch is now
  exact and two-data-shaped.
* The atom's PROVED constraints, packaged: the value pin (`twoData_shellValueDyadic`
  — the weighted value is `1/2^t` at both data; `Q = 2^t` resp. `3·2^t`,
  `twoData_oddpartQ_pin`), the pushed scale floor `X > 2^986893`
  (`twoData_scale_floor`), and the long-gap profile (`twoData_longGap_profile`:
  `X ≤ 2·emExitMass`, `X ≤ 2(W+r)(L+B+1)`, `X ≤ 2·#HE·(L+B+1)`).
* The carry top/bottom-half structure explored in the brief (hits need the carry in
  the top half of its envelope, long gaps need it small) is CONSISTENT in both
  regimes — no cheap kill; recorded honestly in the status, in line with the
  `HitToHitCarry` verdict that no in-tree atom constrains exit mass or carry
  magnitude at the surviving data.

No `sorry`, no `admit`, no new `axiom`, no `native_decide`; additive only.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Part 0.  Scale and parameter helpers -/

/-- Dyadic domination: `320·(n+28)² ≤ 2^(n+28)` — the quadratic-vs-exponential engine
behind every span/count refutation below. -/
theorem fde_pow_dom : ∀ n : ℕ, 320 * ((n + 28) * (n + 28)) ≤ 2 ^ (n + 28) := by
  intro n
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hsq : (n + 1 + 28) * (n + 1 + 28) ≤ 2 * ((n + 28) * (n + 28)) := by
        nlinarith
      calc 320 * ((n + 1 + 28) * (n + 1 + 28))
          ≤ 320 * (2 * ((n + 28) * (n + 28))) := Nat.mul_le_mul le_rfl hsq
        _ = 2 * (320 * ((n + 28) * (n + 28))) := by ring
        _ ≤ 2 * 2 ^ (n + 28) := Nat.mul_le_mul le_rfl ih
        _ = 2 ^ (n + 1 + 28) := by
            rw [show n + 1 + 28 = (n + 28) + 1 from by omega, pow_succ]
            ring

/-- **The square floor**: `320·L² ≤ X` at every actual failure context (from `X = 2^L`
and `L ≥ 28`). -/
theorem fde_X_ge_squares (ctx : ActualFailureContext) :
    320 * (shellLadderDepth ctx * shellLadderDepth ctx) ≤ ctx.shell.X := by
  have hL := shellLadderDepth_ge ctx
  have hX := scc_X_pow ctx
  obtain ⟨n, hn⟩ : ∃ n, shellLadderDepth ctx = n + 28 :=
    ⟨shellLadderDepth ctx - 28, by omega⟩
  rw [hX, hn]
  exact fde_pow_dom n

/-- The carry-largeness gate, retyped onto `shellLadderDepth` (the raw field speaks
`Classical.choose ctx.shell.hXdyadic` — definitionally the same): `B + 25 ≤ L`. -/
theorem fde_carryB_le (ctx : ActualFailureContext) :
    carryB ctx.shell.Q + 25 ≤ shellLadderDepth ctx := ctx.shell_carryLarge

/-- The descent order is below the depth: `r ≤ L` (from `r = ⌊κL⌋`, `κ = 17/2¹⁸ < 1`). -/
theorem fde_r_le_L (ctx : ActualFailureContext) :
    ctx.n24CarryData.r ≤ shellLadderDepth ctx := by
  have hr := scc_r_le_kappaL ctx
  rw [towerKappa_eq] at hr
  have hL0 : (0 : ℝ) ≤ ((shellLadderDepth ctx : ℕ) : ℝ) := Nat.cast_nonneg _
  have hrL : (ctx.n24CarryData.r : ℝ) ≤ ((shellLadderDepth ctx : ℕ) : ℝ) := by
    linarith
  exact_mod_cast hrL

/-- The class-4 routed mass is count × multiplier bounded (the class-4 sibling of
`em_class5Mass_le_card_mul`, via the proved ungated ceiling). -/
theorem fde_class4Mass_le_card_mul (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 4
      ≤ ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4).card : ℝ)
          * runDyadicMult ctx := by
  rw [routedClassMassOf_eq_sum_fibre]
  calc ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4,
        windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
      ≤ ∑ _k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4,
          runDyadicMult ctx := by
        refine Finset.sum_le_sum ?_
        intro k hk
        have hstart : k ∈ ctx.n24CarryData.starts :=
          (mem_highExcessStarts.mp (Finset.mem_filter.mp hk).1).1
        rw [cnlMulti_starts_eq_window, Finset.mem_Ico] at hstart
        exact n24_windowExcess_le_runDyadicMult ctx hstart.2
    _ = ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4).card : ℝ)
          * runDyadicMult ctx := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- The class-3 routed mass is count × multiplier bounded (the class-3 sibling). -/
theorem fde_class3Mass_le_card_mul (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 3
      ≤ ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 3).card : ℝ)
          * runDyadicMult ctx := by
  rw [routedClassMassOf_eq_sum_fibre]
  calc ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 3,
        windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
      ≤ ∑ _k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 3,
          runDyadicMult ctx := by
        refine Finset.sum_le_sum ?_
        intro k hk
        have hstart : k ∈ ctx.n24CarryData.starts :=
          (mem_highExcessStarts.mp (Finset.mem_filter.mp hk).1).1
        rw [cnlMulti_starts_eq_window, Finset.mem_Ico] at hstart
        exact n24_windowExcess_le_runDyadicMult ctx hstart.2
    _ = ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 3).card : ℝ)
          * runDyadicMult ctx := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- **THE GENERIC HIGH-EXCESS COUNT FLOOR** (unconditional — no orbit pin needed):
`X ≤ 2·#HE·(L+B+1)`.  The Lemma 21.1 floor lives on the high-excess set, every member
is per-start capped by `runDyadicMult ≤ (r+1)(L+B+1)`, and the `(r+1)` factors cancel.
This is the sharpened support floor: not just `W` but the HEAVY count is `≥ X/(2(L+B+1))`. -/
theorem fde_highExcess_card_floor (ctx : ActualFailureContext) :
    ctx.shell.X
      ≤ 2 * ((highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
            ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y).card
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) := by
  -- cPr = 1/2 definitionally; retype to avoid the dependent rewrite
  have h1 : (1 / 2 : ℝ) * (ctx.shell.X : ℝ) * ((ctx.n24CarryData.r : ℝ) + 1)
      ≤ ∑ k ∈ highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
          ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y,
          windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
            ctx.n24CarryData.T :=
    ctx.n24CarryData.highExcessMass_lower
  have h2 : (∑ k ∈ highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
          ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y,
          windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
            ctx.n24CarryData.T)
      ≤ ((highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
            ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y).card : ℝ)
          * runDyadicMult ctx := by
    calc ∑ k ∈ highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
          ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y,
          windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
            ctx.n24CarryData.T
        ≤ ∑ _k ∈ highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
            ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y,
            runDyadicMult ctx := by
          refine Finset.sum_le_sum ?_
          intro k hk
          have hks := (mem_highExcessStarts.mp hk).1
          rw [cnlMulti_starts_eq_window, Finset.mem_Ico] at hks
          exact n24_windowExcess_le_runDyadicMult ctx hks.2
      _ = ((highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
            ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y).card : ℝ)
            * runDyadicMult ctx := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hT0 : (0 : ℝ) ≤ ctx.n24CarryData.T := by
    rw [cnlMulti_n24_T_eq]
    positivity
  have h3 : runDyadicMult ctx
      ≤ ((ctx.n24CarryData.r : ℝ) + 1)
          * ((shellLadderDepth ctx + carryB ctx.shell.Q + 1 : ℕ) : ℝ) := by
    unfold runDyadicMult
    rw [show runDyadicG0 ctx = shellLadderDepth ctx + carryB ctx.shell.Q + 1 from rfl]
    apply max_le
    · positivity
    · linarith
  have hcard0 : (0 : ℝ)
      ≤ ((highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
            ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y).card : ℝ) :=
    Nat.cast_nonneg _
  have hchain : (1 / 2 : ℝ) * (ctx.shell.X : ℝ) * ((ctx.n24CarryData.r : ℝ) + 1)
      ≤ ((highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
            ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y).card : ℝ)
          * (((ctx.n24CarryData.r : ℝ) + 1)
            * ((shellLadderDepth ctx + carryB ctx.shell.Q + 1 : ℕ) : ℝ)) :=
    le_trans h1 (le_trans h2 (mul_le_mul_of_nonneg_left h3 hcard0))
  have hr1 : (0 : ℝ) < (ctx.n24CarryData.r : ℝ) + 1 := by positivity
  have hreal : (ctx.shell.X : ℝ)
      ≤ 2 * (((highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
            ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y).card : ℝ)
          * ((shellLadderDepth ctx + carryB ctx.shell.Q + 1 : ℕ) : ℝ)) := by
    by_contra hcon
    push Not at hcon
    have hm := mul_lt_mul_of_pos_right hcon hr1
    nlinarith [hchain, hm]
  have hcast : (ctx.shell.X : ℝ)
      ≤ ((2 * ((highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
            ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y).card
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) : ℕ) : ℝ) := by
    push_cast
    push_cast at hreal
    linarith
  exact_mod_cast hcast

/-- The high-excess set is nonempty at every actual failure context. -/
theorem fde_highExcess_card_pos (ctx : ActualFailureContext) :
    1 ≤ (highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
        ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y).card := by
  have hfloor := fde_highExcess_card_floor ctx
  have hX := scc_X_ge ctx
  rcases Nat.eq_zero_or_pos (highExcessStarts ctx.n24CarryData.starts
      (hitGap ctx.n24CarryData.a) ctx.n24CarryData.r ctx.n24CarryData.T
      ctx.n24CarryData.Y).card with h0 | h1
  · rw [h0] at hfloor
    simp only [Nat.zero_mul, Nat.mul_zero] at hfloor
    omega
  · exact h1

/-- The shell support is nonempty: `1 ≤ W`. -/
theorem fde_supportShell_card_pos (ctx : ActualFailureContext) :
    1 ≤ (supportShell ctx.shell.d ctx.shell.X).card := by
  have h1 := fde_highExcess_card_pos ctx
  have h2 : (highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
        ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y).card
      ≤ (supportShell ctx.shell.d ctx.shell.X).card := by
    rw [← scc_starts_card ctx]
    exact Finset.card_le_card (highExcessStarts_subset _ _ _ _ _)
  omega

/-- The first in-shell hit index is positive: `1 ≤ F`. -/
theorem fde_firstIndex_pos (ctx : ActualFailureContext) :
    1 ≤ ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X := by
  have h0 := zero_notMem_n24Starts ctx
  rw [cnlMulti_starts_eq_window, Finset.mem_Ico] at h0
  have hW := fde_supportShell_card_pos ctx
  omega

/-- The support floor in the gate's exact shape: `X ≤ 2(W+r)(L+B+1)`. -/
theorem fde_W_floor (ctx : ActualFailureContext) :
    ctx.shell.X
      ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) := by
  have h1 := fde_highExcess_card_floor ctx
  have h2 : (highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
        ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y).card
      ≤ (supportShell ctx.shell.d ctx.shell.X).card := by
    rw [← scc_starts_card ctx]
    exact Finset.card_le_card (highExcessStarts_subset _ _ _ _ _)
  refine le_trans h1 (Nat.mul_le_mul le_rfl (Nat.mul_le_mul ?_ le_rfl))
  omega

/-- **The reach numeric guard of the `returnGates` field holds at EVERY context** —
`2(129L+64) ≤ 64(W+r)(L+B+1)` (the `returnGatesBody_of_reach_numeric` escape branch
never fires; the field's demand is always live). -/
theorem fde_returnGates_numeric_guard (ctx : ActualFailureContext) :
    2 * (129 * shellLadderDepth ctx + 64)
      ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) := by
  have hfloor := fde_W_floor ctx
  have hXsq := fde_X_ge_squares ctx
  have hL28 := shellLadderDepth_ge ctx
  have hLP : shellLadderDepth ctx ≤ shellLadderDepth ctx * shellLadderDepth ctx :=
    Nat.le_mul_of_pos_left _ (by omega)
  generalize hQ : ((supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r)
      * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) = Qv at hfloor ⊢
  generalize hP : shellLadderDepth ctx * shellLadderDepth ctx = P at hXsq hLP
  omega

/-! ## Part 1.  The `(3,1)` probe: the band-2 pin and the class-4 floor -/

/-- A band-2 orbit pin fixes the recurrent band: `fixedFamilyRecurrentBand = 2`. -/
theorem band2_recurrentBand_eq (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 2) : fixedFamilyRecurrentBand ctx = 2 := by
  unfold fixedFamilyRecurrentBand
  exact hpin 1 le_rfl

/-- Under the band-2 pin the class-4 fibre IS the full high-excess set. -/
theorem band2_fibre4_eq_highExcess (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 2) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4
      = highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
          ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y := by
  apply Finset.Subset.antisymm
  · intro k hk
    exact ((mem_routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4 k).mp hk).1
  · intro k hk
    exact (mem_routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4 k).mpr
      ⟨hk, scc_route_of_pinned2 ctx hpin
        (scc_starts_pos ctx (mem_highExcessStarts.mp hk).1)⟩

/-- **The class-4 count floor at the band-2 pin**: `X ≤ 2·#fibre₄·(L+B+1)` — the fibre
is forced LARGE (`≥ X/(2(L+B+1))` members). -/
theorem band2_class4_card_floor (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 2) :
    ctx.shell.X
      ≤ 2 * ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4).card
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) := by
  rw [band2_fibre4_eq_highExcess ctx hpin]
  exact fde_highExcess_card_floor ctx

/-- **The class-4 demand floor** (the mirror of `band4_class5_demand_floor`): at every
band-2-pinned context `(1/2)·X·(r+1) ≤ #fibre₄·runDyadicMult` — the FULL pressure floor
against the count × multiplier product. -/
theorem band2_class4_demand_floor (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 2) :
    (1 / 2 : ℝ) * (ctx.shell.X : ℝ) * ((ctx.n24CarryData.r : ℝ) + 1)
      ≤ ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4).card : ℝ)
          * runDyadicMult ctx := by
  -- cPr = 1/2 definitionally; retype to avoid the dependent rewrite
  have h1 : (1 / 2 : ℝ) * (ctx.shell.X : ℝ) * ((ctx.n24CarryData.r : ℝ) + 1)
      ≤ routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 4 :=
    band2_pressure_in_class4 ctx hpin
  exact le_trans h1 (fde_class4Mass_le_card_mul ctx)

/-- **The population bound `Class4FibreSmall` is REFUTED at every band-2-pinned
context**: `#fibre₄ ≤ r+1` contradicts the forced floor `#fibre₄ ≥ X/(2(L+B+1))`.
(The bound is exactly what `class4FibreSmall_of_gates` extracts from the gates field.) -/
theorem band2_pinned_not_class4Small (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 2)
    (hsmall : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4).card
        ≤ ctx.n24CarryData.r + 1) : False := by
  have hfloor := band2_class4_card_floor ctx hpin
  have hrL := fde_r_le_L ctx
  have hBL := fde_carryB_le ctx
  have hL28 := shellLadderDepth_ge ctx
  have hprod : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4).card
      * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)
      ≤ (2 * shellLadderDepth ctx) * (2 * shellLadderDepth ctx) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hX8 : ctx.shell.X
      ≤ 2 * (4 * (shellLadderDepth ctx * shellLadderDepth ctx)) := by
    calc ctx.shell.X
        ≤ 2 * ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4).card
            * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) := hfloor
      _ ≤ 2 * ((2 * shellLadderDepth ctx) * (2 * shellLadderDepth ctx)) :=
          Nat.mul_le_mul le_rfl hprod
      _ = 2 * (4 * (shellLadderDepth ctx * shellLadderDepth ctx)) := by ring
  have hXsq := fde_X_ge_squares ctx
  have hLP : shellLadderDepth ctx ≤ shellLadderDepth ctx * shellLadderDepth ctx :=
    Nat.le_mul_of_pos_left _ (by omega)
  generalize hP : shellLadderDepth ctx * shellLadderDepth ctx = P at hX8 hXsq hLP
  omega

/-! ## Part 2.  The `(3,1)` probe: ALL THREE live `returnGates` disjuncts are FALSE -/

/-- **OVER-TRANSCRIPTION #5, the core refutation**: at every band-2-pinned context the
gate-free Return body `ReturnGatesBodyUngated` is FALSE — the full-span and sub-span
gates die against the exit-mass floor `X ≤ 2·emExitMass` (the span carries `≥ X/2`
while the gates demand `≲ 4L`), and the cycle-count gate dies because the pinned cycle
reads band 2 EVERYWHERE (`b₂ = c`), forcing `W ≤ r+1` against `W ≥ X/(2(L+B+1)) − r`. -/
theorem band2_pinned_not_returnGatesBodyUngated (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 2) : ¬ ReturnGatesBodyUngated ctx := by
  have hb2 := band2_recurrentBand_eq ctx hpin
  have hband : fixedFamilyRecurrentBand ctx ≤ 4 := by omega
  have hEM : ctx.shell.X ≤ 2 * emExitMass ctx := em_exitMass_lower_of_band ctx hband
  have hXsq := fde_X_ge_squares ctx
  have hL28 := shellLadderDepth_ge ctx
  have hLP : shellLadderDepth ctx ≤ shellLadderDepth ctx * shellLadderDepth ctx :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hW1 := fde_supportShell_card_pos ctx
  have hspan2 : ctx.n24CarryData.a
      (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
        + (supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r)
      = ctx.n24CarryData.a (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X)
        + (emBandMass ctx + emExitMass ctx) := by
    have h := em_span_eq ctx
    rw [show emF ctx + (emW ctx + ctx.n24CarryData.r)
        = ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + (supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r from by
      unfold emF emW
      omega] at h
    exact h
  intro hbody
  rcases hbody with h1 | h2 | h3
  · -- full-span gate
    generalize hP : shellLadderDepth ctx * shellLadderDepth ctx = P at hXsq hLP
    omega
  · -- sub-span gate
    have htel := em_position_telescope ctx
      (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
        + (supportShell ctx.shell.d ctx.shell.X).card - 1) (ctx.n24CarryData.r + 1)
    rw [show ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
        + (supportShell ctx.shell.d ctx.shell.X).card - 1 + (ctx.n24CarryData.r + 1)
        = ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + (supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r from by
      omega] at htel
    have htail0 : (∑ i ∈ Finset.range (ctx.n24CarryData.r + 1),
          hitGap ctx.n24CarryData.a
            (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card - 1 + i))
        ≤ (ctx.n24CarryData.r + 1)
            * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) := by
      calc (∑ i ∈ Finset.range (ctx.n24CarryData.r + 1),
            hitGap ctx.n24CarryData.a
              (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
                + (supportShell ctx.shell.d ctx.shell.X).card - 1 + i))
          ≤ ∑ _i ∈ Finset.range (ctx.n24CarryData.r + 1),
              (shellLadderDepth ctx + carryB ctx.shell.Q + 1) := by
            refine Finset.sum_le_sum ?_
            intro i hi
            rw [Finset.mem_range] at hi
            refine n24_hitGap_le_reach ctx ?_
            omega
        _ = (ctx.n24CarryData.r + 1)
              * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) := by
            rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    have hRG : (ctx.n24CarryData.r + 1)
        * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)
        ≤ 4 * (shellLadderDepth ctx * shellLadderDepth ctx) := by
      have ha : ctx.n24CarryData.r + 1 ≤ 2 * shellLadderDepth ctx := by
        have := fde_r_le_L ctx
        omega
      have hb : shellLadderDepth ctx + carryB ctx.shell.Q + 1
          ≤ 2 * shellLadderDepth ctx := by
        have := fde_carryB_le ctx
        omega
      calc (ctx.n24CarryData.r + 1) * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)
          ≤ (2 * shellLadderDepth ctx) * (2 * shellLadderDepth ctx) :=
            Nat.mul_le_mul ha hb
        _ = 4 * (shellLadderDepth ctx * shellLadderDepth ctx) := by ring
    have htail4 := le_trans htail0 hRG
    have hmono : ctx.n24CarryData.a
        (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X)
        ≤ ctx.n24CarryData.a
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card - 1) :=
      ctx.n24CarryData.carry.hits.strict.monotone (by omega)
    generalize hP : shellLadderDepth ctx * shellLadderDepth ctx = P at hXsq hLP htail4
    omega
  · -- cycle-count gate
    obtain ⟨c, t, hc, hper, hWtc, htb⟩ := h3
    have hfilt : ((Finset.Icc 1 c).filter (fun j =>
        canonGap (class1SlopeDatum ctx).q
          (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) = 2))
        = Finset.Icc 1 c :=
      Finset.filter_true_of_mem (fun j hj => hpin j (Finset.mem_Icc.mp hj).1)
    rw [hfilt, Nat.card_Icc, Nat.add_sub_cancel] at htb
    have hWr1 : (supportShell ctx.shell.d ctx.shell.X).card ≤ ctx.n24CarryData.r + 1 :=
      le_trans hWtc htb
    have hfloor := fde_W_floor ctx
    have hrL := fde_r_le_L ctx
    have hBL := fde_carryB_le ctx
    have hprod : ((supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r)
        * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)
        ≤ (2 * shellLadderDepth ctx + 1) * (2 * shellLadderDepth ctx) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hX8 : ctx.shell.X
        ≤ 2 * (4 * (shellLadderDepth ctx * shellLadderDepth ctx)
            + 2 * shellLadderDepth ctx) := by
      calc ctx.shell.X
          ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r)
              * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) := hfloor
        _ ≤ 2 * ((2 * shellLadderDepth ctx + 1) * (2 * shellLadderDepth ctx)) :=
            Nat.mul_le_mul le_rfl hprod
        _ = 2 * (4 * (shellLadderDepth ctx * shellLadderDepth ctx)
              + 2 * shellLadderDepth ctx) := by ring
    generalize hP : shellLadderDepth ctx * shellLadderDepth ctx = P at hX8 hXsq hLP
    omega

/-- The full 4-way `ReturnGatesBody` is FALSE at every band-2-pinned context. -/
theorem band2_pinned_not_returnGatesBody (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 2) : ¬ ReturnGatesBody ctx := fun h =>
  band2_pinned_not_returnGatesBodyUngated ctx hpin
    ((returnGatesBody_iff_ungated ctx).mp h)

/-- The band-2 pin refutes `ReturnB2FreeDatum` (its closure would prove the refuted
body) — the first guard of the `returnGates` field HOLDS at every pinned context. -/
theorem band2_pinned_not_b2Free (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 2) : ¬ ReturnB2FreeDatum ctx := fun h =>
  band2_pinned_not_returnGatesBody ctx hpin (returnCtxAllFour_of_b2FreeDatum ctx h).1

/-- The band-2 pin refutes `ReturnB2OneSpacedDatum` — the second guard HOLDS. -/
theorem band2_pinned_not_b2OneSpaced (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 2) : ¬ ReturnB2OneSpacedDatum ctx := fun h =>
  band2_pinned_not_returnGatesBody ctx hpin
    (returnGatesZeroCard_of_b2OneSpacedDatum ctx h).1

/-- **THE `(3,1)` GATES VERDICT**: the `returnGates` field instance is UNSATISFIABLE at
every band-2-pinned context — all guards hold there and the conclusion is false. -/
theorem band2_pinned_not_returnGatesInstance (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 2)
    (hfield : ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
      2 * (129 * shellLadderDepth ctx + 64)
        ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r)
            * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
      ReturnGatesBodyUngated ctx) : False :=
  band2_pinned_not_returnGatesBodyUngated ctx hpin
    (hfield (band2_pinned_not_b2Free ctx hpin) (band2_pinned_not_b2OneSpaced ctx hpin)
      (fde_returnGates_numeric_guard ctx))

/-- The Return gates field of the corrected/anchored surfaces, as a named `Prop`
(verbatim the `returnGates` field of `Erdos260CorrectedResidual`). -/
def ReturnGatesField : Prop :=
  ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    2 * (129 * shellLadderDepth ctx + 64)
      ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
    ReturnGatesBodyUngated ctx

/-- **THE CORRECTED SPLIT (the Return-lane sibling of
`runNumericField_iff_band4Void_split`)**: the `returnGates` field is EXACTLY (band-2
orbit-pin voiding) ∧ (the field on band-2-free contexts).  The voiding conjunct is the
orbit-pinned deep axis at `(3,1)`; the manuscript's I.5/M.2.2 budget never charges the
recurrent band-2 data through these count gates. -/
theorem returnGatesField_iff_band2Void_split :
    ReturnGatesField
      ↔ ((∀ ctx : ActualFailureContext, ¬ OrbitBandPinned ctx 2)
          ∧ (∀ ctx : ActualFailureContext, ¬ OrbitBandPinned ctx 2 →
              ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
              2 * (129 * shellLadderDepth ctx + 64)
                ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card
                      + ctx.n24CarryData.r)
                    * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
              ReturnGatesBodyUngated ctx)) := by
  constructor
  · intro h
    exact ⟨fun ctx hpin => band2_pinned_not_returnGatesInstance ctx hpin (h ctx),
      fun ctx _ => h ctx⟩
  · rintro ⟨hvoid, hoff⟩ ctx
    exact hoff ctx (hvoid ctx)

/-- **Supplying the `returnGates` field VOIDS the `(3,1)` family** — over-transcription
#5 as a consumer: the field charges what the manuscript budgets through the L.3/M.5
recurrent lane. -/
theorem returnGatesField_voids_3_1 (h : ReturnGatesField)
    (ctx : ActualFailureContext) :
    ¬ ((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1) := fun hd =>
  band2_pinned_not_returnGatesInstance ctx (orbitBandPinned_3_1 ctx hd) (h ctx)

/-! ## Part 3.  The `(3,1)` probe: `returnInterior` SURVIVES — the exact demand -/

/-- **The `returnInterior` probe verdict (SATISFIABLE — the exact remaining demand)**:
at every band-2-pinned context the K.1 interior body is EQUIVALENT to "every start in
the top band `[F+W−r−1, F+W)` is LIGHT (`windowExcess < Y`)" — a pure position
constraint on where the word places its heavy windows.  The pressure floor forces
`≥ X/(2(L+B+1))` heavy starts but not WHERE they sit; words placing the heavy mass low
satisfy the demand, so no refutation is possible by mass/count accounting. -/
theorem band2_returnInterior_iff_topBand_light (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 2) :
    ReturnInteriorBody ctx
      ↔ ∀ k ∈ ctx.n24CarryData.starts,
          ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card
            ≤ k + ctx.n24CarryData.r + 1 →
          windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
              ctx.n24CarryData.T
            < ctx.n24CarryData.Y := by
  constructor
  · intro hbody k hk htop
    by_contra hge
    push Not at hge
    have hkHE : k ∈ highExcessStarts ctx.n24CarryData.starts
        (hitGap ctx.n24CarryData.a) ctx.n24CarryData.r ctx.n24CarryData.T
        ctx.n24CarryData.Y :=
      mem_highExcessStarts.mpr ⟨hk, hge⟩
    have hk4 : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4 :=
      (mem_routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4 k).mpr
        ⟨hkHE, scc_route_of_pinned2 ctx hpin (scc_starts_pos ctx hk)⟩
    have hlt := hbody k hk4
    omega
  · intro hlight k hk
    have hmem := (mem_routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4 k).mp hk
    have hks := (mem_highExcessStarts.mp hmem.1).1
    have hY := (mem_highExcessStarts.mp hmem.1).2
    by_contra hcon
    push Not at hcon
    have := hlight k hks hcon
    linarith

/-- The exact demand extracted from the surface's `returnInterior` field at a
band-2-pinned context: the top `r+1` starts must all be light. -/
theorem band2_pinned_returnInterior_demand (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 2)
    (hfield : ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx) :
    ∀ k ∈ ctx.n24CarryData.starts,
      ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + (supportShell ctx.shell.d ctx.shell.X).card
        ≤ k + ctx.n24CarryData.r + 1 →
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        < ctx.n24CarryData.Y :=
  (band2_returnInterior_iff_topBand_light ctx hpin).mp
    (hfield (band2_pinned_not_b2Free ctx hpin))

/-! ## Part 4.  The `(21,3)` probe: the band-3 pin and the class-3 floor -/

/-- Under the band-3 pin the genuine densepack start set IS the full high-excess set. -/
theorem band3_genuineStarts_eq (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 3) :
    genuineDensePackStarts ctx
      = highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
          ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y := by
  apply Finset.Subset.antisymm
  · intro k hk
    exact ((mem_genuineDensePackStarts ctx k).mp hk).1
  · intro k hk
    exact (mem_genuineDensePackStarts ctx k).mpr
      ⟨hk, scc_towerCls_of_pinned3 ctx hpin
        (scc_starts_pos ctx (mem_highExcessStarts.mp hk).1)⟩

/-- Under the band-3 pin the class-3 fibre IS the full high-excess set. -/
theorem band3_fibre3_eq_highExcess (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 3) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 3
      = highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
          ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y := by
  apply Finset.Subset.antisymm
  · intro k hk
    exact ((mem_routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 3 k).mp hk).1
  · intro k hk
    exact (mem_routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 3 k).mpr
      ⟨hk, scc_route_of_pinned3 ctx hpin
        (scc_starts_pos ctx (mem_highExcessStarts.mp hk).1)⟩

/-- **The genuine-start count floor at the band-3 pin**: `X ≤ 2·#gdps·(L+B+1)`. -/
theorem band3_genuineStarts_card_floor (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 3) :
    ctx.shell.X
      ≤ 2 * ((genuineDensePackStarts ctx).card
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) := by
  rw [band3_genuineStarts_eq ctx hpin]
  exact fde_highExcess_card_floor ctx

/-- The class-3 count floor at the band-3 pin: `X ≤ 2·#fibre₃·(L+B+1)`. -/
theorem band3_class3_card_floor (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 3) :
    ctx.shell.X
      ≤ 2 * ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 3).card
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) := by
  rw [band3_fibre3_eq_highExcess ctx hpin]
  exact fde_highExcess_card_floor ctx

/-- **The class-3 demand floor** (the densepack mirror of `band4_class5_demand_floor`):
`(1/2)·X·(r+1) ≤ #fibre₃·runDyadicMult` at every band-3-pinned context. -/
theorem band3_class3_demand_floor (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 3) :
    (1 / 2 : ℝ) * (ctx.shell.X : ℝ) * ((ctx.n24CarryData.r : ℝ) + 1)
      ≤ ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 3).card : ℝ)
          * runDyadicMult ctx := by
  -- cPr = 1/2 definitionally; retype to avoid the dependent rewrite
  have h1 : (1 / 2 : ℝ) * (ctx.shell.X : ℝ) * ((ctx.n24CarryData.r : ℝ) + 1)
      ≤ routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 3 :=
    band3_pressure_in_class3 ctx hpin
  exact le_trans h1 (fde_class3Mass_le_card_mul ctx)

/-- The band-3 pin refutes `Class3CycleBand3Free` — the cycle reads band 3 at `j = 1`. -/
theorem band3_pinned_not_cycleBand3Free (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 3) : ¬ Class3CycleBand3Free ctx := by
  rintro ⟨c, hc, hper, hband⟩
  exact hband 1 le_rfl hc (hpin 1 le_rfl)

/-- The band-3 pin refutes `DensePackDatumClosed` (closed data have band-3-free
cycles). -/
theorem band3_pinned_not_datumClosed (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 3) : ¬ DensePackDatumClosed ctx := fun h =>
  band3_pinned_not_cycleBand3Free ctx hpin (class3CycleBand3Free_of_datumClosed ctx h)

/-- The band-3 pin refutes `Class3TopBandCycleFree` — the top-band start `F+W−1`
witnesses a band-3 cycle reading. -/
theorem band3_pinned_not_topBandCycleFree (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 3) : ¬ Class3TopBandCycleFree ctx := by
  rintro ⟨c, hc, hper, htop⟩
  have hF := fde_firstIndex_pos ctx
  have hW := fde_supportShell_card_pos ctx
  have hk := htop (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
      + (supportShell ctx.shell.d ctx.shell.X).card - 1)
    (by omega) (by omega) (by omega)
  exact hk (hpin (1 + (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
      + (supportShell ctx.shell.d ctx.shell.X).card - 1 - 1) % c) (by omega))

/-! ## Part 5.  The `(21,3)` probe: the Nat-cover field is FALSE — over-transcription
#6 -/

/-- **OVER-TRANSCRIPTION #6, the core refutation**: at every band-3-pinned context the
K.1.2 Nat-cover inequality is FALSE — with `r ≥ 16` the per-start slack
`(r+1)(L+B+1) − (2L+1) ≥ 15L`, so the demand side is
`≥ 15L·#gdps ≥ 15X/4`, while the actual-point set is structurally capped by its
ambient window at `3X + (L+B+2)`.  At `X ≥ 320L²` the cover cannot hold. -/
theorem band3_pinned_not_coverNat (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 3) :
    ¬ ((genuineDensePackStarts ctx).card
        * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
            - (2 * shellLadderDepth ctx + 1))
      ≤ (proofV4DensePackActualPoints ctx.shell).card) := by
  intro hcover
  rw [show densePackDyadicG0 ctx
      = shellLadderDepth ctx + carryB ctx.shell.Q + 1 from rfl] at hcover
  have hr16 := n24_r_ge_sixteen ctx
  have hB1 : 1 ≤ carryB ctx.shell.Q := by unfold carryB; omega
  have hL28 := shellLadderDepth_ge ctx
  have hslack : 15 * shellLadderDepth ctx
      ≤ (ctx.n24CarryData.r + 1) * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)
        - (2 * shellLadderDepth ctx + 1) := by
    have h17 : 17 * (shellLadderDepth ctx + 2)
        ≤ (ctx.n24CarryData.r + 1)
            * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    generalize hQ : (ctx.n24CarryData.r + 1)
        * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) = Qv at h17 ⊢
    omega
  have hLHS : (genuineDensePackStarts ctx).card * (15 * shellLadderDepth ctx)
      ≤ (genuineDensePackStarts ctx).card
          * ((ctx.n24CarryData.r + 1)
              * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)
            - (2 * shellLadderDepth ctx + 1)) :=
    Nat.mul_le_mul le_rfl hslack
  have hRHS : (proofV4DensePackActualPoints ctx.shell).card
      ≤ 3 * ctx.shell.X + (shellLadderDepth ctx + carryB ctx.shell.Q + 1) + 1 := by
    have hsub : (proofV4DensePackActualPoints ctx.shell).card
        ≤ (Finset.Icc 0 (3 * ctx.shell.X + proofV4DensePackSpread ctx.shell)).card :=
      Finset.card_filter_le _ _
    rw [Nat.card_Icc] at hsub
    rw [show proofV4DensePackSpread ctx.shell
        = shellLadderDepth ctx + carryB ctx.shell.Q + 1 from rfl] at hsub
    omega
  have hfloor := band3_genuineStarts_card_floor ctx hpin
  have hGL : shellLadderDepth ctx + carryB ctx.shell.Q + 1
      ≤ 2 * shellLadderDepth ctx := by
    have := fde_carryB_le ctx
    omega
  have hX4 : ctx.shell.X
      ≤ 4 * ((genuineDensePackStarts ctx).card * shellLadderDepth ctx) := by
    calc ctx.shell.X
        ≤ 2 * ((genuineDensePackStarts ctx).card
            * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) := hfloor
      _ ≤ 2 * ((genuineDensePackStarts ctx).card * (2 * shellLadderDepth ctx)) :=
          Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hGL)
      _ = 4 * ((genuineDensePackStarts ctx).card * shellLadderDepth ctx) := by ring
  have hchain : (genuineDensePackStarts ctx).card * (15 * shellLadderDepth ctx)
      ≤ 3 * ctx.shell.X + (shellLadderDepth ctx + carryB ctx.shell.Q + 1) + 1 :=
    le_trans hLHS (le_trans hcover hRHS)
  have h15 : 15 * ((genuineDensePackStarts ctx).card * shellLadderDepth ctx)
      = (genuineDensePackStarts ctx).card * (15 * shellLadderDepth ctx) := by ring
  have hXsq := fde_X_ge_squares ctx
  have hLP : shellLadderDepth ctx ≤ shellLadderDepth ctx * shellLadderDepth ctx :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hBL := fde_carryB_le ctx
  generalize hNL : (genuineDensePackStarts ctx).card * shellLadderDepth ctx = NL
    at hX4 h15
  generalize hP : shellLadderDepth ctx * shellLadderDepth ctx = P at hXsq hLP
  rw [← h15] at hchain
  omega

/-- The densepack Nat-cover field of the collapsed surfaces, as a named `Prop`
(verbatim the `ungatedCoverNat` field of `DensePackUngatedClosureResidual`). -/
def DensePackCoverField : Prop :=
  ∀ ctx : ActualFailureContext,
    ¬ Class3CycleBand3Free ctx →
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
    ¬ DensePackDatumClosed ctx →
    (genuineDensePackStarts ctx).card
        * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
            - (2 * shellLadderDepth ctx + 1))
      ≤ (proofV4DensePackActualPoints ctx.shell).card

/-- The band-3 pin together with the cover field's own modulus window — the exact
class of contexts where the cover field fires and is refuted. -/
def Band3PinnedWide (ctx : ActualFailureContext) : Prop :=
  OrbitBandPinned ctx 3
    ∧ ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q)

/-- **THE `(21,3)` COVER VERDICT**: the `ungatedCoverNat` field instance is
UNSATISFIABLE at every wide band-3-pinned context — the guards are theorems at the pin
and the cover conclusion is false. -/
theorem band3PinnedWide_not_coverInstance (ctx : ActualFailureContext)
    (h : Band3PinnedWide ctx)
    (hinst : ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      (genuineDensePackStarts ctx).card
          * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
              - (2 * shellLadderDepth ctx + 1))
        ≤ (proofV4DensePackActualPoints ctx.shell).card) : False :=
  band3_pinned_not_coverNat ctx h.1
    (hinst (band3_pinned_not_cycleBand3Free ctx h.1) h.2
      (band3_pinned_not_datumClosed ctx h.1))

/-- **THE CORRECTED SPLIT (the densepack sibling)**: the Nat-cover field is EXACTLY
(wide band-3 orbit-pin voiding) ∧ (the field on the band-3-free contexts).  The
voiding conjunct is the orbit-pinned deep axis at `(21,3)`. -/
theorem densePackCoverField_iff_band3Void_split :
    DensePackCoverField
      ↔ ((∀ ctx : ActualFailureContext, ¬ Band3PinnedWide ctx)
          ∧ (∀ ctx : ActualFailureContext, ¬ Band3PinnedWide ctx →
              ¬ Class3CycleBand3Free ctx →
              ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
              ¬ DensePackDatumClosed ctx →
              (genuineDensePackStarts ctx).card
                  * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
                      - (2 * shellLadderDepth ctx + 1))
                ≤ (proofV4DensePackActualPoints ctx.shell).card)) := by
  constructor
  · intro h
    exact ⟨fun ctx hwide => band3PinnedWide_not_coverInstance ctx hwide (h ctx),
      fun ctx _ => h ctx⟩
  · rintro ⟨hvoid, hoff⟩ ctx
    exact hoff ctx (hvoid ctx)

/-- **Supplying the densepack Nat-cover field VOIDS the `(21,3)` family** —
over-transcription #6 as a consumer. -/
theorem densePackCoverField_voids_21_3 (h : DensePackCoverField)
    (ctx : ActualFailureContext) :
    ¬ ((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3) := fun hd =>
  band3PinnedWide_not_coverInstance ctx
    ⟨orbitBandPinned_21_3 ctx hd, Or.inr (by rw [hd.1]; norm_num)⟩ (h ctx)

/-! ## Part 6.  The `(21,3)` probe: density and interior — the exact demands -/

/-- **The density probe extraction**: at a band-3-pinned context the K.1.1 endpoint
density field forces the index range to REACH the shell — `X < F + W + r + (L+B+1)`.
(The support windows live at index-derived positions `[k+r, k+r+L+B+1]` while support
sits in `(X, 2X]`; with `minHits ≥ 1` even one window must be nonempty.) -/
theorem band3_density_forces_subshell (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 3) (hdens : densePackEndpointDensity ctx) :
    ctx.shell.X
      < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + (supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r
          + (shellLadderDepth ctx + carryB ctx.shell.Q + 1) := by
  have heq := band3_genuineStarts_eq ctx hpin
  have hpos : 0 < (genuineDensePackStarts ctx).card := by
    rw [heq]
    exact fde_highExcess_card_pos ctx
  obtain ⟨k, hk⟩ := Finset.card_pos.mp hpos
  have hdk := hdens k hk
  have hmin : 0 < proofV4DensePackMinHits ctx.shell :=
    proofV4DensePackMinHits_pos_of_carryLarge ctx.shell_carryLarge
  have hwin : 0 < (proofV4DensePackSupportWindow ctx.shell
      (k + ctx.n24CarryData.r)).card := by omega
  obtain ⟨n, hn⟩ := Finset.card_pos.mp hwin
  have hn' := Finset.mem_filter.mp hn
  have hXn : ctx.shell.X < n :=
    ((mem_supportShell ctx.shell.d ctx.shell.X n).mp hn'.1).1
  have hnub := hn'.2.2
  rw [show proofV4DensePackSpread ctx.shell
      = shellLadderDepth ctx + carryB ctx.shell.Q + 1 from rfl] at hnub
  have hkW : k < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
      + (supportShell ctx.shell.d ctx.shell.X).card := by
    have hkHE : k ∈ highExcessStarts ctx.n24CarryData.starts
        (hitGap ctx.n24CarryData.a) ctx.n24CarryData.r ctx.n24CarryData.T
        ctx.n24CarryData.Y := by
      rw [heq] at hk
      exact hk
    have hks := (mem_highExcessStarts.mp hkHE).1
    rw [cnlMulti_starts_eq_window, Finset.mem_Ico] at hks
    exact hks.2
  omega

/-- **The density `F`-floor**: with the failure cap `2²⁴·W < 17·X` the density field
forces `F > (1 − 17/2²⁴)·X − (r+L+B+1)` — the word must carry hits at essentially ALL
indices below the shell.  Not refuted here (the ones may sit above `X/2²⁰`, keeping the
weighted value small) — the exact extracted demand. -/
theorem band3_density_F_floor (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 3) (hdens : densePackEndpointDensity ctx) :
    16777199 * ctx.shell.X
      < 16777216 * (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + ctx.n24CarryData.r + shellLadderDepth ctx + carryB ctx.shell.Q + 1) := by
  have h1 := band3_density_forces_subshell ctx hpin hdens
  have h2 : 16777216 * (supportShell ctx.shell.d ctx.shell.X).card
      < 17 * ctx.shell.X := em_supportShell_strict ctx
  omega

/-- **The densepack-interior probe verdict (SATISFIABLE — the exact remaining
demand)**: at a band-3-pinned context the `ungatedInterior` body is EQUIVALENT to
"every top-band start is light" — the same position constraint as the Return lane. -/
theorem band3_densePackInterior_iff_topBand_light (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 3) :
    (∀ k ∈ genuineDensePackStarts ctx,
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card)
      ↔ ∀ k ∈ ctx.n24CarryData.starts,
          ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card
            ≤ k + ctx.n24CarryData.r + 1 →
          windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
              ctx.n24CarryData.T
            < ctx.n24CarryData.Y := by
  constructor
  · intro hbody k hk htop
    by_contra hge
    push Not at hge
    have hkHE : k ∈ highExcessStarts ctx.n24CarryData.starts
        (hitGap ctx.n24CarryData.a) ctx.n24CarryData.r ctx.n24CarryData.T
        ctx.n24CarryData.Y :=
      mem_highExcessStarts.mpr ⟨hk, hge⟩
    have hkg : k ∈ genuineDensePackStarts ctx :=
      (mem_genuineDensePackStarts ctx k).mpr
        ⟨hkHE, scc_towerCls_of_pinned3 ctx hpin (scc_starts_pos ctx hk)⟩
    have hlt := hbody k hkg
    omega
  · intro hlight k hk
    have hmem := (mem_genuineDensePackStarts ctx k).mp hk
    have hks := (mem_highExcessStarts.mp hmem.1).1
    have hY := (mem_highExcessStarts.mp hmem.1).2
    by_contra hcon
    push Not at hcon
    have := hlight k hks hcon
    linarith

/-- The exact demand extracted from the surface's `ungatedInterior` field at a
band-3-pinned context inside the field's modulus window. -/
theorem band3_pinned_densePackInterior_demand (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 3)
    (hq : (class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q)
    (hfield : ¬ Class3TopBandCycleFree ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      ∀ k ∈ genuineDensePackStarts ctx,
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card) :
    ∀ k ∈ ctx.n24CarryData.starts,
      ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + (supportShell ctx.shell.d ctx.shell.X).card
        ≤ k + ctx.n24CarryData.r + 1 →
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        < ctx.n24CarryData.Y :=
  (band3_densePackInterior_iff_topBand_light ctx hpin).mp
    (hfield (band3_pinned_not_topBandCycleFree ctx hpin) hq
      (band3_pinned_not_datumClosed ctx hpin))

/-! ## Part 7.  The synthesis: the two-data endgame -/

/-- **THE NAMED FINAL ATOM**: no actual failure context realizes the `(3,1)` or the
`(21,3)` datum — the exact remaining content of the fixed-family axis after the two
probes (the band-4 trio is already carried by the surface's `runBand4Void`). -/
def FixedDataEndgameVoiding : Prop :=
  ∀ ctx : ActualFailureContext,
    ¬ ((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1)
    ∧ ¬ ((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3)

/-- The two surviving capstone fields supply the final atom — the no-free-lunch, made
exact at the two data. -/
theorem fixedDataEndgameVoiding_of_fields (hg : ReturnGatesField)
    (hc : DensePackCoverField) : FixedDataEndgameVoiding := fun ctx =>
  ⟨returnGatesField_voids_3_1 hg ctx, densePackCoverField_voids_21_3 hc ctx⟩

/-- The final atom plus the band-4 voiding void ALL FIVE fixed families at every
scale. -/
theorem fixedFamilyHit_void_of_endgame (h2 : FixedDataEndgameVoiding)
    (hb4 : ∀ ctx : ActualFailureContext, ¬ OrbitBandPinned ctx 4)
    (ctx : ActualFailureContext) : ¬ FixedFamilyHit ctx := by
  rintro (hd | hd | hd | hd | hd)
  · exact (h2 ctx).1 hd
  · exact (h2 ctx).2 hd
  · exact hb4 ctx (orbitBandPinned_15_1 ctx hd)
  · exact hb4 ctx (orbitBandPinned_15_2 ctx hd)
  · exact hb4 ctx (orbitBandPinned_105_7 ctx hd)

/-- The wave-16 corrected surface supplies the final atom THROUGH ITS OWN FIELDS
(`returnGates` + `densePackUngated.ungatedCoverNat`). -/
theorem correctedResidual_fixedDataVoiding (R : Erdos260CorrectedResidual) :
    FixedDataEndgameVoiding :=
  fixedDataEndgameVoiding_of_fields R.returnGates R.densePackUngated.ungatedCoverNat

/-- **EVERY inhabitant of the corrected surface voids all five fixed families
outright** — the Return lane carries `(3,1)`, the densepack lane carries `(21,3)`, and
`runBand4Void` carries the band-4 trio. -/
theorem correctedResidual_not_fixedFamilyHit (R : Erdos260CorrectedResidual)
    (ctx : ActualFailureContext) : ¬ FixedFamilyHit ctx :=
  fixedFamilyHit_void_of_endgame (correctedResidual_fixedDataVoiding R)
    R.runBand4Void ctx

/-- The corrected surface supplies the deep family voiding. -/
theorem correctedResidual_deepFixedFamilyVoid (R : Erdos260CorrectedResidual) :
    DeepFixedFamilyVoid := fun ctx _ =>
  correctedResidual_not_fixedFamilyHit R ctx

/-- **The `FixedFamilyShellPersistence` axis is ABSORBED by the corrected surface**:
its fields void every fixed-family hit, so the deep shell-persistence supply holds
vacuously.  The open axis has moved INTO the surface's own voiding conjuncts. -/
theorem correctedResidual_deepShellPersistence (R : Erdos260CorrectedResidual) :
    DeepFixedFamilyShellPersistence := fun ctx _ hhit =>
  absurd hhit (correctedResidual_not_fixedFamilyHit R ctx)

/-! ## Part 8.  The final atom's proved constraints (the attack record) -/

/-- **The value pin at the two data**: the Erdős weighted value is EXACTLY the dyadic
reciprocal `1/2^t` (with `Q = 2^t` at `(3,1)` and `Q = 3·2^t` at `(21,3)`). -/
theorem twoData_shellValueDyadic (ctx : ActualFailureContext)
    (hd : ((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1)
        ∨ ((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3)) :
    ShellValueDyadic ctx := by
  rcases hd with ⟨hq, hK⟩ | ⟨hq, hK⟩
  · obtain ⟨t, _, hval⟩ := return_datum_value_eq ctx hq hK
    exact ⟨t, hval⟩
  · obtain ⟨t, _, hval⟩ := densePack_datum_value_eq ctx hq hK
    exact ⟨t, hval⟩

/-- **The pushed pinned-value scale floor at the two data**: `X > 2^986893` (through
the wave-10 dyadic-value voiding). -/
theorem twoData_scale_floor (ctx : ActualFailureContext)
    (hd : ((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1)
        ∨ ((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3)) :
    2 ^ 986893 < ctx.X :=
  shellValueDyadic_scale_lower_pushV2 ctx (twoData_shellValueDyadic ctx hd)

/-- The odd part of `Q` at the two data: `1` at `(3,1)`, `3` at `(21,3)`. -/
theorem twoData_oddpartQ_pin (ctx : ActualFailureContext)
    (hd : ((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1)
        ∨ ((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3)) :
    ordCompl[2] ctx.shell.Q = 1 ∨ ordCompl[2] ctx.shell.Q = 3 := by
  rcases hd with ⟨hq, hK⟩ | ⟨hq, hK⟩
  · exact Or.inl (return_datum_Q_oddPart ctx hq hK)
  · exact Or.inr (densePack_datum_Q_oddPart ctx hq hK)

/-- **The long-gap profile at the two data**: deviations carry `≥ X/2`
(`X ≤ 2·emExitMass`), the support obeys `X ≤ 2(W+r)(L+B+1)`, and even the HEAVY count
obeys `X ≤ 2·#HE·(L+B+1)` — the word is exactly long-gap-sparse with cofinal heavy
windows. -/
theorem twoData_longGap_profile (ctx : ActualFailureContext)
    (hd : ((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1)
        ∨ ((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3)) :
    ctx.shell.X ≤ 2 * emExitMass ctx
    ∧ ctx.shell.X
        ≤ 2 * ((emW ctx + ctx.n24CarryData.r)
            * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
    ∧ ctx.shell.X
        ≤ 2 * ((highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
              ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y).card
            * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) := by
  have hband : fixedFamilyRecurrentBand ctx ≤ 4 := by
    rcases hd with ⟨hq, hK⟩ | ⟨hq, hK⟩
    · have hpin := orbitBandPinned_3_1 ctx ⟨hq, hK⟩
      have hb : fixedFamilyRecurrentBand ctx = 2 := by
        unfold fixedFamilyRecurrentBand
        exact hpin 1 le_rfl
      omega
    · have hpin := orbitBandPinned_21_3 ctx ⟨hq, hK⟩
      have hb : fixedFamilyRecurrentBand ctx = 3 := by
        unfold fixedFamilyRecurrentBand
        exact hpin 1 le_rfl
      omega
  refine ⟨em_exitMass_lower_of_band ctx hband, ?_, fde_highExcess_card_floor ctx⟩
  exact le_trans (em_exitMass_lower_of_band ctx hband)
    (Nat.mul_le_mul le_rfl (em_exitMass_le_reach_span ctx))

/-! ## Part 9.  Honest machine-readable status -/

/-- The precise status of the fixed-data endgame pass. -/
def fixedDataEndgameStatus : List String :=
  [ "(3,1) PROBE - OVER-TRANSCRIPTION #5 FOUND (PROVED, " ++
      "band2_pinned_not_returnGatesBodyUngated): at EVERY band-2-pinned ctx all " ++
      "three live disjuncts of ReturnGatesBodyUngated are FALSE.  Full-span gate: " ++
      "em_span_eq + the exit-mass floor X <= 2*emExitMass give 64*span >= 32X >= " ++
      "10240*L^2 (fde_X_ge_squares: X = 2^L >= 320L^2) >> 2(129L+64).  Sub-span " ++
      "gate: the tail [F+W-1, F+W+r) carries <= (r+1)(L+B+1) <= 4L^2 " ++
      "(n24_hitGap_le_reach + r <= L + B+25 <= L), so 64*subspan >= 32X - 256L^2 " ++
      ">> 129L+64.  Cycle-count gate: the pin makes EVERY cycle residue read band " ++
      "2, so b2 = c and W <= t*c <= r+1 - against the support floor X <= " ++
      "2(W+r)(L+B+1) (W >= X/(4L) >> r+1).  The guards do NOT save the field: the " ++
      "pin refutes ReturnB2FreeDatum and ReturnB2OneSpacedDatum (their closures " ++
      "prove the refuted body - band2_pinned_not_b2Free/_b2OneSpaced) and the " ++
      "reach numeric guard is a THEOREM at every ctx " ++
      "(fde_returnGates_numeric_guard; the returnGatesBody_of_reach_numeric " ++
      "escape branch never fires anywhere).",
    "(3,1) PRESSURE MECHANISM (PROVED): band2_pressure_in_class4 relocates the " ++
      "WHOLE Lemma 21.1 floor into class 4; the fibre is the FULL high-excess set " ++
      "(band2_fibre4_eq_highExcess) and the generic count floor " ++
      "fde_highExcess_card_floor (X <= 2*#HE*(L+B+1), unconditional - the " ++
      "sharpened support floor on the HEAVY count) transfers: " ++
      "band2_class4_card_floor (#fibre4 >= X/(2(L+B+1))) and the demand floor " ++
      "band2_class4_demand_floor ((1/2)X(r+1) <= #fibre4*runDyadicMult - the " ++
      "exact mirror of band4_class5_demand_floor).  Consequence: the population " ++
      "bound Class4FibreSmall (#fibre4 <= r+1) that class4FibreSmall_of_gates " ++
      "extracts from the gates is refuted directly (band2_pinned_not_class4Small).",
    "(3,1) CORRECTED SPLIT (PROVED): returnGatesField_iff_band2Void_split - the " ++
      "returnGates field (verbatim the Erdos260CorrectedResidual field) IS " ++
      "(band-2 orbit-pin voiding) AND (the field on band-2-free ctx) - the exact " ++
      "Return-lane sibling of runNumericField_iff_band4Void_split.  Supplying the " ++
      "field VOIDS (3,1): returnGatesField_voids_3_1.  The manuscript's I.5/M.2.2 " ++
      "budget routes the recurrent band-2 data through L.3/M.5, not through the " ++
      "wave-3 count gates; the corrected surface should demand the gates only at " ++
      "NOT OrbitBandPinned ctx 2 contexts.",
    "(3,1) returnInterior - SATISFIABLE, genuine demand (PROVED equivalence " ++
      "band2_returnInterior_iff_topBand_light): at the pin the K.1 interior body " ++
      "is EXACTLY 'every start in the top band [F+W-r-1, F+W) is light " ++
      "(windowExcess < Y)' - a position constraint.  The pressure forces >= " ++
      "X/(2(L+B+1)) heavy starts among W < c0*X but NOT where they sit; words " ++
      "placing the heavy mass low satisfy it - no mass/count refutation exists " ++
      "(the heavy fraction ~2^24/(34L) < 1 at L > 2^24/34).  Exact demand " ++
      "extracted: band2_pinned_returnInterior_demand.",
    "(21,3) PROBE - OVER-TRANSCRIPTION #6 FOUND (PROVED, " ++
      "band3_pinned_not_coverNat): at EVERY band-3-pinned ctx the K.1.2 Nat-cover " ++
      "ungatedCoverNat is FALSE.  band3_pressure_in_class3 + " ++
      "band3_genuineStarts_eq (gdps = the FULL high-excess set under the pin) " ++
      "give #gdps >= X/(2(L+B+1)) (band3_genuineStarts_card_floor); with r >= 16 " ++
      "(n24_r_ge_sixteen) the per-start slack (r+1)*(L+B+1) - (2L+1) >= 15L, so " ++
      "LHS >= 15L*#gdps >= (15/4)X, while #proofV4DensePackActualPoints <= " ++
      "3X + (L+B+2) (ambient-window cap).  (15/4)X > 3X + 2L at X >= 320L^2: " ++
      "FALSE at every scale.  termDensePack itself is NOT even reached - the " ++
      "cover's own Nat shape dies structurally; the frozen-faithful capacity " ++
      "audit (wave-16 target list item 4) is MOOT on this lane at the pin.  " ++
      "Guards are theorems at the pin: band3_pinned_not_cycleBand3Free / " ++
      "_not_datumClosed / _not_topBandCycleFree.",
    "(21,3) CORRECTED SPLIT (PROVED): densePackCoverField_iff_band3Void_split - " ++
      "the cover field IS (wide band-3 voiding: OrbitBandPinned ctx 3 AND the " ++
      "field's own modulus window q = 5 or 13 <= q) AND (the field on the " ++
      "complement).  Supplying it VOIDS (21,3): densePackCoverField_voids_21_3.  " ++
      "The q-window guard is honest: a band-3 pin outside the window never fires " ++
      "the field, so the voiding conjunct is exactly Band3PinnedWide.",
    "(21,3) density - SATISFIABLE but with an EXTREME extracted demand (PROVED " ++
      "band3_density_forces_subshell / band3_density_F_floor): the K.1.1 windows " ++
      "[k+r, k+r+L+B+1] live at INDEX-derived positions while support sits in " ++
      "(X, 2X], so even one nonempty window forces X < F + W + r + (L+B+1), " ++
      "hence 16777199*X < 2^24*(F + r + L + B + 1): the word must have hits at " ++
      "essentially ALL indices below the shell (F > (1 - 2^-20)X).  NOT refuted: " ++
      "the sub-shell ones may sit above X/2^20 keeping the weighted value tiny - " ++
      "no contradiction with the value pin 1/2^t.  Counting cannot refute either " ++
      "(at L >= 15421 the incidence bound #gdps*(L/8) <= W*(L+B+2) is " ++
      "consistent).  Interior: same verdict as Return - " ++
      "band3_densePackInterior_iff_topBand_light, demand " ++
      "band3_pinned_densePackInterior_demand.",
    "SYNTHESIS (PROVED): FixedDataEndgameVoiding (THE NAMED FINAL ATOM - no ctx " ++
      "realizes (3,1) or (21,3)) is supplied BY the surviving fields " ++
      "(fixedDataEndgameVoiding_of_fields); with runBand4Void all FIVE families " ++
      "void (fixedFamilyHit_void_of_endgame).  Hence EVERY inhabitant of the " ++
      "wave-16 corrected surface voids the five fixed families outright " ++
      "(correctedResidual_not_fixedFamilyHit), supplies DeepFixedFamilyVoid " ++
      "(correctedResidual_deepFixedFamilyVoid), and VACUOUSLY supplies " ++
      "DeepFixedFamilyShellPersistence (correctedResidual_deepShellPersistence): " ++
      "the FixedFamilyShellPersistence axis is ABSORBED - the no-free-lunch now " ++
      "sits at exactly TWO data inside the surface's own returnGates/" ++
      "ungatedCoverNat fields plus the named runBand4Void.  (Consequently the " ++
      "anchored surface too was always this strong: its returnGates field was " ++
      "never suppliable without voiding (3,1).)",
    "THE FINAL ATOM'S PROVED CONSTRAINTS (the attack record): value pin - " ++
      "ShellValueDyadic at both data (twoData_shellValueDyadic; Q = 2^t at (3,1), " ++
      "Q = 3*2^t at (21,3), twoData_oddpartQ_pin); scale floor X > 2^986893 " ++
      "(twoData_scale_floor via the wave-10 pushed dyadic lever); long-gap " ++
      "profile (twoData_longGap_profile: X <= 2*emExitMass, X <= 2(W+r)(L+B+1), " ++
      "X <= 2*#HE*(L+B+1) - heavy windows cofinal at density >= 1/(2(L+B+1))).  " ++
      "CARRY STRUCTURE (recorded honestly, not formalized): the hit-positivity " ++
      "R_{N'} = 2^g R_N - Q N' >= 0 needs R_N >= Q N'/2^g and the envelope " ++
      "R_N <= Q(N+2) caps the carry BEFORE a length-g gap at ~Q(2N+2g+2)/2^g - " ++
      "hits need a charged carry, long gaps need a drained one, and BOTH regimes " ++
      "are satisfiable at every checked scale; consistent with the HitToHitCarry " ++
      "verdict that no in-tree atom constrains exit mass or carry magnitude at " ++
      "the surviving data.  No cheap kill.",
    "WHAT REMAINS (sharpest known form): supply the two voiding conjuncts - " ++
      "(a) no band-2 orbit pin (kills (3,1)); (b) no wide band-3 orbit pin " ++
      "(kills (21,3)); (c) no band-4 orbit pin (the wave-16 runBand4Void) - " ++
      "all three are orbit-pinned forms of the deep open axis, each now carrying " ++
      "the full constraint package above (value 1/2^t, X > 2^986893, long-gap " ++
      "word, pressure relocated into a single >= X/(2(L+B+1))-large class).  The " ++
      "honest Section-26/K.1-faithful surface demands the count fields only on " ++
      "pin-free contexts (the second conjuncts of the two splits).",
    "HYGIENE: additive only - ONE new module, no existing file edited, root " ++
      "import untouched; no sorry / admit / new axiom / native_decide; every key " ++
      "declaration passes #print axioms within [propext, Classical.choice, " ++
      "Quot.sound]." ]

/-- The status list is non-empty. -/
theorem fixedDataEndgameStatus_nonempty : fixedDataEndgameStatus ≠ [] := by
  simp [fixedDataEndgameStatus]

/-! ## Part 10.  Axiom-cleanliness audit
Every key declaration; expected axioms `[propext, Classical.choice, Quot.sound]` or
fewer. -/

#print axioms fde_pow_dom
#print axioms fde_X_ge_squares
#print axioms fde_carryB_le
#print axioms fde_r_le_L
#print axioms fde_class4Mass_le_card_mul
#print axioms fde_class3Mass_le_card_mul
#print axioms fde_highExcess_card_floor
#print axioms fde_highExcess_card_pos
#print axioms fde_supportShell_card_pos
#print axioms fde_firstIndex_pos
#print axioms fde_W_floor
#print axioms fde_returnGates_numeric_guard
#print axioms band2_recurrentBand_eq
#print axioms band2_fibre4_eq_highExcess
#print axioms band2_class4_card_floor
#print axioms band2_class4_demand_floor
#print axioms band2_pinned_not_class4Small
#print axioms band2_pinned_not_returnGatesBodyUngated
#print axioms band2_pinned_not_returnGatesBody
#print axioms band2_pinned_not_b2Free
#print axioms band2_pinned_not_b2OneSpaced
#print axioms band2_pinned_not_returnGatesInstance
#print axioms returnGatesField_iff_band2Void_split
#print axioms returnGatesField_voids_3_1
#print axioms band2_returnInterior_iff_topBand_light
#print axioms band2_pinned_returnInterior_demand
#print axioms band3_genuineStarts_eq
#print axioms band3_fibre3_eq_highExcess
#print axioms band3_genuineStarts_card_floor
#print axioms band3_class3_card_floor
#print axioms band3_class3_demand_floor
#print axioms band3_pinned_not_cycleBand3Free
#print axioms band3_pinned_not_datumClosed
#print axioms band3_pinned_not_topBandCycleFree
#print axioms band3_pinned_not_coverNat
#print axioms band3PinnedWide_not_coverInstance
#print axioms densePackCoverField_iff_band3Void_split
#print axioms densePackCoverField_voids_21_3
#print axioms band3_density_forces_subshell
#print axioms band3_density_F_floor
#print axioms band3_densePackInterior_iff_topBand_light
#print axioms band3_pinned_densePackInterior_demand
#print axioms fixedDataEndgameVoiding_of_fields
#print axioms fixedFamilyHit_void_of_endgame
#print axioms correctedResidual_fixedDataVoiding
#print axioms correctedResidual_not_fixedFamilyHit
#print axioms correctedResidual_deepFixedFamilyVoid
#print axioms correctedResidual_deepShellPersistence
#print axioms twoData_shellValueDyadic
#print axioms twoData_scale_floor
#print axioms twoData_oddpartQ_pin
#print axioms twoData_longGap_profile
#print axioms fixedDataEndgameStatus_nonempty

end

end Erdos260
