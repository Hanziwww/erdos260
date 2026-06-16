import Erdos260.Erdos260CorrectedLedgerCapstone
import Erdos260.FloorPushV2

/-!
# The class-1 survivor regime enumeration (`SurvivorRegimeEnumeration`)

The mechanical wave-16 follow-up: per-pair certified data for the COMPLETE current
class-1 survivor list - the 23 wave-14 pairs of `q <= 99` (the `CNLClass1PairClosure`
open data, with the wave-5 obstructed moduli `25/29/37/41/47/49` included) PLUS the
87 `FiniteTailsSweep` survivors of `101 <= q < 200` (`finiteTailsSweepClass1SurvivorPairs`)
- 110 pairs in this build.  For each pair this module certifies:

1. **The orbit period from index 1** (`sreCert_<q>_<K0>`, new for the 87 sweep pairs;
   the 23 wave-14 pairs reuse the public in-tree count lemmas
   `class1Fibre_card_le_of_datum_*`): kernel-checked `slopeOrbit_step_eval` chains,
   the return collision `K_(1+c) = K_1`, and the certified band-4 residue SET of one
   period (every `canonGap = 4` reading lands in the listed residues - the count `b4`).
2. **The per-pair count cap** `|fibre_1| <= b4 * ceil(W/c)`
   (`sreClass1Count_of_datum_*` via `class1Fibre_card_le_cycleDensity`).
3. **The regime closure** `sreClass1Absorption_of_datum_<q>_<K0>`: at the datum, the
   single scale hypothesis `L <= T(q,K0)` with `T = floor(15*2^24*c/(408*b4))`
   closes the corrected class-1 absorption
   `card(fibre_1)*Y <= (cStar*xi/6)*X = (31/1536)*X` - EXACTLY the
   `Erdos260CorrectedResidual.class1CapAbsorption` field shape of the wave-16
   capstone at this `ctx` (the `r >= 1` guard is not even needed).  The engine is
   the budget-free remake of `correctedAbsorption_of_cycleDensity_regime`: main
   regime `408*b4*L <= 15*2^24*c` discharged by `L <= T` + numerals; the slack
   `24*b4*c*L <= 16*X` discharged FREE from the wave-8 floor `X > 2^493460`
   (`sreSlackBound`: the slack budget is below `2^48` at every pair).
4. **The aggregate dispatcher** `sreClass1Absorption_of_mem` over the machine-readable
   threshold table `sreClass1ThresholdTable` (q, K0, c, b4, T), and the capstone
   field wrapper `sreClass1CapAbsorption_field_of_mem`.

## The honest threshold tabulation (deep shells stay OPEN)

The gate closes ONLY the regime `L <= T`; `L` is unbounded, so at every pair the
deep-shell residual `L > T` STAYS OPEN on the absorption axis - no unconditional
closure of the capstone field is claimed.  Three categories (proved floors:
generic wave-8 `L >= 493461` = `sreDepth_ge_493461`; and the FloorPushV2 q-side
value pin `3*oddpart(Q) <= q` at EVERY ctx, so `q < 384 = 3*2^7` forces
`L >= 986888` = `sreDepth_ge_986888_of_q_lt_384` - every survivor pair has
`q <= 199 < 384`, hence carries the 986888 floor, NOT merely the generic one):

* NEVER-FIRES (`T < 493461`): 0 pairs - the gate regime is below even the
  generic floor.
* SUB-PIN (`493461 <= T < 986888`): 1 pair(s) - the gate fires against the
  generic floor alone but the regime `[493461, T]` is VACUOUS on actual contexts
  (`sreClass1Gate_vacuous_below_pin`): the q-side pin floor empties it.  Honest:
  the per-pair theorem is still emitted; it closes nothing on genuine shells.
* LIVE (`T >= 986888`): 109 pairs - the regime `[986888, T]` is genuinely closed;
  `L > T` is the honest per-pair deep-shell residual.

## Class 0 (the 19 `OffFibreMissClosure` survivor pairs - parametric forms)

Periods and deep-slot data are already certified in-tree
(`ofcCert_*` / `offFibreMissResidualTable`); this module REUSES the public count cap
`ofcClass0Fibre_card_le_of_survivor` (`|fibre_0| <= ceil(W/c)`) and delivers the
count*excess forms PARAMETRICALLY, ready for the sibling freeze-audit lane's
corrected `termChernoff` gate (NOT imported - it may not exist yet):
`sreClass0Mass_le_of_survivor` / `sreClass0Mass_le_of_datum_<q>_<K0>`:
`sum_(k in fibre_0) f k <= ceil(W/c) * E` for ANY per-member excess cap `E`, and the
bare product form `sreClass0CountExcess_le_of_survivor`.  No class-0 gate is claimed
here; the corrected-termChernoff inequality is the sibling's deliverable.

No `sorry`, no `admit`, no new `axiom`, no `native_decide` (`decide` only on small
closed numeric / Finset-literal goals); additive only - no existing module is edited,
NOT root-wired (built standalone as `Erdos260.SurvivorRegimeEnumeration`).
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-! ## Part 0.  The budget-free gate engines -/

/-- **The field-shaped corrected absorption gate**: any proved class-1 count cap `n`
with the `ℕ` gate `24*n*L ≤ 31*X` closes the corrected class-1 capacity bound in
the EXACT `Erdos260CorrectedResidual.class1CapAbsorption` field shape - no budget
argument (the capstone's `correctedAbsorption_of_nat_gate` concludes against
`termCnl (correctedCapacityPhases budget ctx)`; this version targets the
budget-free constant via `correctedCnlShare_eq`). -/
theorem sreAbsorption_of_nat_gate (ctx : ActualFailureContext) (n : ℕ)
    (hcard : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card ≤ n)
    (hgate : 24 * (n * shellLadderDepth ctx) ≤ 31 * ctx.shell.X) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  rw [correctedCnlShare_eq, n24CarryData_Y_eq_div]
  have hcardR : ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
      ≤ (n : ℝ) := by exact_mod_cast hcard
  have hgateR : (24 : ℝ) * ((n : ℝ) * ((shellLadderDepth ctx : ℕ) : ℝ))
      ≤ 31 * ((ctx.shell.X : ℕ) : ℝ) := by exact_mod_cast hgate
  have hL0 : (0 : ℝ) ≤ ((shellLadderDepth ctx : ℕ) : ℝ) := Nat.cast_nonneg _
  have h1 : ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * (((shellLadderDepth ctx : ℕ) : ℝ) / 64)
      ≤ (n : ℝ) * (((shellLadderDepth ctx : ℕ) : ℝ) / 64) := by
    apply mul_le_mul_of_nonneg_right hcardR
    positivity
  linarith

/-- **The period-block collapse, pure `ℕ` form** (the arithmetic core of the capstone's
`correctedAbsorption_of_cycleDensity_regime`, freed of the context): the failure cap
`2^24*W ≤ 17*X`, the main regime `408*b4*L ≤ 15*2^24*c`, and the scale slack
`24*b4*c*L ≤ 16*X` give the gate for the cycle-density count `b4*ceil(W/c)`. -/
private theorem sreNatGate_of_regime {b4 c W L X : ℕ} (hc : 1 ≤ c)
    (hW16 : 16777216 * W ≤ 17 * X)
    (hmain : 408 * (b4 * L) ≤ 251658240 * c)
    (hslack : 24 * (b4 * (c * L)) ≤ 16 * X) :
    24 * (b4 * ((W + c - 1) / c) * L) ≤ 31 * X := by
  have hdiv : (W + c - 1) / c * c ≤ W + c - 1 := Nat.div_mul_le_self _ _
  have hcc : c * (b4 * ((W + c - 1) / c)) ≤ b4 * (W + c) := by
    calc c * (b4 * ((W + c - 1) / c))
        = b4 * ((W + c - 1) / c * c) := by ring
      _ ≤ b4 * (W + c - 1) := Nat.mul_le_mul le_rfl hdiv
      _ ≤ b4 * (W + c) := Nat.mul_le_mul le_rfl (by omega)
  have hXc : X ≤ c * X := Nat.le_mul_of_pos_left X hc
  have key : 16777216 * c * (24 * (b4 * ((W + c - 1) / c) * L))
      ≤ 16777216 * c * (31 * X) := by
    calc 16777216 * c * (24 * (b4 * ((W + c - 1) / c) * L))
        = 24 * L * 16777216 * (c * (b4 * ((W + c - 1) / c))) := by ring
      _ ≤ 24 * L * 16777216 * (b4 * (W + c)) := Nat.mul_le_mul le_rfl hcc
      _ = 24 * (L * b4) * (16777216 * W) + 16777216 * (24 * (b4 * (c * L))) := by
          ring
      _ ≤ 24 * (L * b4) * (17 * X) + 16777216 * (16 * X) :=
          Nat.add_le_add (Nat.mul_le_mul le_rfl hW16) (Nat.mul_le_mul le_rfl hslack)
      _ = 408 * (b4 * L) * X + 268435456 * X := by ring
      _ ≤ 251658240 * c * X + 268435456 * (c * X) :=
          Nat.add_le_add (Nat.mul_le_mul hmain le_rfl)
            (Nat.mul_le_mul le_rfl hXc)
      _ = 16777216 * c * (31 * X) := by ring
  have hpos : 0 < 16777216 * c := by positivity
  exact Nat.le_of_mul_le_mul_left key hpos

/-- **The slack discharger**: anything below `2^48` is below `16*X` on every actual
failure shell - the wave-8 floor `2^493460 < X` (`scaleFloorPush_scale_lower`) makes
the per-pair scale slack `24*b4*c*L ≤ 16*X` FREE under `L ≤ T` (every per-pair
slack budget `24*b4*c*T` is below `2^48`). -/
private theorem sreSlackBound (ctx : ActualFailureContext) {N : ℕ}
    (hN : N ≤ 2 ^ 48) : N ≤ 16 * ctx.shell.X :=
  calc N ≤ 2 ^ 48 := hN
    _ ≤ 2 ^ 493460 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    _ ≤ ctx.X := le_of_lt (scaleFloorPush_scale_lower ctx)
    _ = ctx.shell.X := (ActualFailureContext.shell_X ctx).symm
    _ ≤ 16 * ctx.shell.X := Nat.le_mul_of_pos_left _ (by norm_num)

/-- Re-export: the generic wave-8 depth floor `L ≥ 493461` at every actual failure
context (`shellLadderDepth_ge_493461`). -/
theorem sreDepth_ge_493461 (ctx : ActualFailureContext) :
    493461 ≤ shellLadderDepth ctx :=
  shellLadderDepth_ge_493461 ctx

/-- **The q-side value-pin depth floor at every survivor pair**: `3*oddpart(Q) ≤ q`
holds at EVERY ctx (`floorPushV2_three_oddpartQ_le_q`), so `q < 384 = 3*2^7` forces
`L ≥ 986888` (`floorPushV2_void_of_q_lt` at `b = 7`).  Every class-1 survivor pair
has `q ≤ 199 < 384` - their contexts carry THIS floor, not merely the generic
`493461`. -/
theorem sreDepth_ge_986888_of_q_lt_384 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q < 384) : 986888 ≤ shellLadderDepth ctx := by
  by_contra hcon
  push Not at hcon
  have hXeq : ctx.shell.X = 2 ^ shellLadderDepth ctx :=
    Classical.choose_spec ctx.shell.hXdyadic
  refine floorPushV2_void_of_q_lt ctx (b := 7) (by norm_num)
    (lt_of_lt_of_le hq (by norm_num)) ?_
  have hX' : ctx.X = 2 ^ shellLadderDepth ctx := by
    rw [← ActualFailureContext.shell_X ctx]
    exact hXeq
  rw [hX']
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **The sub-pin vacuity verdict (honest)**: a gate threshold `T < 986888` at a pair
with `q < 384` fires on NO actual context - the regime `[493461, T]` visible to the
generic floor is emptied by the q-side pin floor.  (At this build's tables the unique
such pair is `(105, 7)`, the band-4 fixed point, `c = 1`, `T = 616809`.) -/
theorem sreClass1Gate_vacuous_below_pin (ctx : ActualFailureContext)
    {qv Tv : ℕ} (hq : (class1SlopeDatum ctx).q = qv) (hqlt : qv < 384)
    (hT : Tv < 986888) (hL : shellLadderDepth ctx ≤ Tv) : False := by
  have h := sreDepth_ge_986888_of_q_lt_384 ctx (by omega)
  omega

/-! ## Part 1.  The 87 sweep-pair certificates: orbit period + band-4 residue set

Each `sreCert_<q>_<K0>` certifies the return collision at index `1 + c` and that
every band-4 reading of one period lands in the listed residue set; the count cap
follows through `class1Fibre_card_le_cycleDensity` + `band4_cycle_card_le_of_subset`.
(The 23 wave-14 pairs are NOT re-certified - their public in-tree count lemmas
`class1Fibre_card_le_of_datum_*` are consumed directly in Part 2.) -/

/-- `(101,50)`: period `50`, cycle `[99, 97, 93, 85, 69, 37, 47, 87, 73, 45, 79, 57, 13, 3, 91, 81, 61, 21, 67, 33, 31, 23, 83, 65, 29, 15, 19, 51, 1, 27, 7, 11, 75, 49, 95, 89, 77, 53, 5, 59, 17, 35, 39, 55, 9, 43, 71, 41, 63, 25]`, bands `[1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 3, 3, 1, 7, 2, 4, 4, 1, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 4, 2, 1, 2, 1, 3]` - band-4 residue set `{31, 32, 45}` (values `7, 11, 9`), `b4 = 3`. -/
private theorem sreCert_101_50 :
    slopeOrbit 101 50 (1 + 50) = slopeOrbit 101 50 1
      ∧ ∀ j, 1 ≤ j → j ≤ 50 →
          canonGap 101 (slopeOrbit 101 50 j) = 4 → j ∈ ({31, 32, 45} : Finset ℕ) := by
  have e0 : slopeOrbit 101 50 0 = 50 := rfl
  have e1 : slopeOrbit 101 50 1 = 99 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 101 50 2 = 97 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 101 50 3 = 93 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 101 50 4 = 85 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 101 50 5 = 69 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 101 50 6 = 37 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 101 50 7 = 47 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 101 50 8 = 87 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 101 50 9 = 73 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 101 50 10 = 45 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 101 50 11 = 79 :=
    slopeOrbit_step_eval 10 1 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 101 50 12 = 57 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 101 50 13 = 13 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 101 50 14 = 3 :=
    slopeOrbit_step_eval 13 2 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 101 50 15 = 91 :=
    slopeOrbit_step_eval 14 5 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 101 50 16 = 81 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 101 50 17 = 61 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 101 50 18 = 21 :=
    slopeOrbit_step_eval 17 0 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 101 50 19 = 67 :=
    slopeOrbit_step_eval 18 2 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 101 50 20 = 33 :=
    slopeOrbit_step_eval 19 0 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 101 50 21 = 31 :=
    slopeOrbit_step_eval 20 1 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 101 50 22 = 23 :=
    slopeOrbit_step_eval 21 1 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 101 50 23 = 83 :=
    slopeOrbit_step_eval 22 2 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 101 50 24 = 65 :=
    slopeOrbit_step_eval 23 0 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 101 50 25 = 29 :=
    slopeOrbit_step_eval 24 0 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 101 50 26 = 15 :=
    slopeOrbit_step_eval 25 1 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 101 50 27 = 19 :=
    slopeOrbit_step_eval 26 2 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 101 50 28 = 51 :=
    slopeOrbit_step_eval 27 2 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 101 50 29 = 1 :=
    slopeOrbit_step_eval 28 0 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 101 50 30 = 27 :=
    slopeOrbit_step_eval 29 6 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : slopeOrbit 101 50 31 = 7 :=
    slopeOrbit_step_eval 30 1 e30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e32 : slopeOrbit 101 50 32 = 11 :=
    slopeOrbit_step_eval 31 3 e31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e33 : slopeOrbit 101 50 33 = 75 :=
    slopeOrbit_step_eval 32 3 e32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e34 : slopeOrbit 101 50 34 = 49 :=
    slopeOrbit_step_eval 33 0 e33 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e35 : slopeOrbit 101 50 35 = 95 :=
    slopeOrbit_step_eval 34 1 e34 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e36 : slopeOrbit 101 50 36 = 89 :=
    slopeOrbit_step_eval 35 0 e35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e37 : slopeOrbit 101 50 37 = 77 :=
    slopeOrbit_step_eval 36 0 e36 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e38 : slopeOrbit 101 50 38 = 53 :=
    slopeOrbit_step_eval 37 0 e37 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e39 : slopeOrbit 101 50 39 = 5 :=
    slopeOrbit_step_eval 38 0 e38 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e40 : slopeOrbit 101 50 40 = 59 :=
    slopeOrbit_step_eval 39 4 e39 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e41 : slopeOrbit 101 50 41 = 17 :=
    slopeOrbit_step_eval 40 0 e40 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e42 : slopeOrbit 101 50 42 = 35 :=
    slopeOrbit_step_eval 41 2 e41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e43 : slopeOrbit 101 50 43 = 39 :=
    slopeOrbit_step_eval 42 1 e42 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e44 : slopeOrbit 101 50 44 = 55 :=
    slopeOrbit_step_eval 43 1 e43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e45 : slopeOrbit 101 50 45 = 9 :=
    slopeOrbit_step_eval 44 0 e44 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e46 : slopeOrbit 101 50 46 = 43 :=
    slopeOrbit_step_eval 45 3 e45 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e47 : slopeOrbit 101 50 47 = 71 :=
    slopeOrbit_step_eval 46 1 e46 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e48 : slopeOrbit 101 50 48 = 41 :=
    slopeOrbit_step_eval 47 0 e47 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e49 : slopeOrbit 101 50 49 = 63 :=
    slopeOrbit_step_eval 48 1 e48 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e50 : slopeOrbit 101 50 50 = 25 :=
    slopeOrbit_step_eval 49 0 e49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e51 : slopeOrbit 101 50 51 = 99 :=
    slopeOrbit_step_eval 50 2 e50 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 101 50 51 = slopeOrbit 101 50 1
    rw [e51, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e26] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e27] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e28] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e29] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e30] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · decide
    · rw [e33] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e34] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e35] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e36] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e37] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e38] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e39] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e40] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e41] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e42] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e43] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e44] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e46] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e47] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e48] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e49] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e50] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))

/-- `(101,50)`: the certified class-1 count cap `|fibre_1| <= 3 * ceil(W/50)`. -/
theorem sreClass1Count_of_datum_101_50 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 101) (hK : (class1SlopeDatum ctx).K₀ = 50) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 3 * (((supportShell ctx.shell.d ctx.shell.X).card + 50 - 1) / 50) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 50)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_101_50.1
  have hcount : (class1Band4CycleBand ctx 50).card ≤ 3 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_101_50.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 50).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 50 - 1) / 50) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 3 * (((supportShell ctx.shell.d ctx.shell.X).card + 50 - 1) / 50) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(103,51)`: period `28`, cycle `[101, 99, 95, 87, 71, 39, 53, 3, 89, 75, 47, 85, 67, 31, 21, 65, 27, 5, 57, 11, 73, 43, 69, 35, 37, 45, 77, 51]`, bands `[1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 2, 3, 1, 2, 5, 1, 4, 1, 2, 1, 2, 2, 2, 1, 2]` - band-4 residue set `{20}` (values `11`), `b4 = 1`. -/
private theorem sreCert_103_51 :
    slopeOrbit 103 51 (1 + 28) = slopeOrbit 103 51 1
      ∧ ∀ j, 1 ≤ j → j ≤ 28 →
          canonGap 103 (slopeOrbit 103 51 j) = 4 → j ∈ ({20} : Finset ℕ) := by
  have e0 : slopeOrbit 103 51 0 = 51 := rfl
  have e1 : slopeOrbit 103 51 1 = 101 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 103 51 2 = 99 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 103 51 3 = 95 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 103 51 4 = 87 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 103 51 5 = 71 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 103 51 6 = 39 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 103 51 7 = 53 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 103 51 8 = 3 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 103 51 9 = 89 :=
    slopeOrbit_step_eval 8 5 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 103 51 10 = 75 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 103 51 11 = 47 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 103 51 12 = 85 :=
    slopeOrbit_step_eval 11 1 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 103 51 13 = 67 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 103 51 14 = 31 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 103 51 15 = 21 :=
    slopeOrbit_step_eval 14 1 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 103 51 16 = 65 :=
    slopeOrbit_step_eval 15 2 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 103 51 17 = 27 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 103 51 18 = 5 :=
    slopeOrbit_step_eval 17 1 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 103 51 19 = 57 :=
    slopeOrbit_step_eval 18 4 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 103 51 20 = 11 :=
    slopeOrbit_step_eval 19 0 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 103 51 21 = 73 :=
    slopeOrbit_step_eval 20 3 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 103 51 22 = 43 :=
    slopeOrbit_step_eval 21 0 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 103 51 23 = 69 :=
    slopeOrbit_step_eval 22 1 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 103 51 24 = 35 :=
    slopeOrbit_step_eval 23 0 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 103 51 25 = 37 :=
    slopeOrbit_step_eval 24 1 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 103 51 26 = 45 :=
    slopeOrbit_step_eval 25 1 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 103 51 27 = 77 :=
    slopeOrbit_step_eval 26 1 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 103 51 28 = 51 :=
    slopeOrbit_step_eval 27 0 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 103 51 29 = 101 :=
    slopeOrbit_step_eval 28 1 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 103 51 29 = slopeOrbit 103 51 1
    rw [e29, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e26] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e27] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e28] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))

/-- `(103,51)`: the certified class-1 count cap `|fibre_1| <= 1 * ceil(W/28)`. -/
theorem sreClass1Count_of_datum_103_51 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 103) (hK : (class1SlopeDatum ctx).K₀ = 51) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 28 - 1) / 28) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 28)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_103_51.1
  have hcount : (class1Band4CycleBand ctx 28).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_103_51.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 28).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 28 - 1) / 28) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 28 - 1) / 28) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(105,7)`: period `1`, cycle `[7]`, bands `[4]` - band-4 residue set `{1}` (values `7`), `b4 = 1`. -/
private theorem sreCert_105_7 :
    slopeOrbit 105 7 (1 + 1) = slopeOrbit 105 7 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 →
          canonGap 105 (slopeOrbit 105 7 j) = 4 → j ∈ ({1} : Finset ℕ) := by
  have e0 : slopeOrbit 105 7 0 = 7 := rfl
  have e1 : slopeOrbit 105 7 1 = 7 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 105 7 2 = 7 :=
    slopeOrbit_step_eval 1 3 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 105 7 2 = slopeOrbit 105 7 1
    rw [e2, e1]
  · intro j h1 h2 hband
    interval_cases j
    · decide

/-- `(105,7)`: the certified class-1 count cap `|fibre_1| <= 1 * ceil(W/1)`. -/
theorem sreClass1Count_of_datum_105_7 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 105) (hK : (class1SlopeDatum ctx).K₀ = 7) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 1 - 1) / 1) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 1)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_105_7.1
  have hcount : (class1Band4CycleBand ctx 1).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_105_7.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 1).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 1 - 1) / 1) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 1 - 1) / 1) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(105,52)`: period `8`, cycle `[103, 101, 97, 89, 73, 41, 59, 13]`, bands `[1, 1, 1, 1, 1, 2, 1, 4]` - band-4 residue set `{8}` (values `13`), `b4 = 1`. -/
private theorem sreCert_105_52 :
    slopeOrbit 105 52 (1 + 8) = slopeOrbit 105 52 1
      ∧ ∀ j, 1 ≤ j → j ≤ 8 →
          canonGap 105 (slopeOrbit 105 52 j) = 4 → j ∈ ({8} : Finset ℕ) := by
  have e0 : slopeOrbit 105 52 0 = 52 := rfl
  have e1 : slopeOrbit 105 52 1 = 103 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 105 52 2 = 101 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 105 52 3 = 97 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 105 52 4 = 89 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 105 52 5 = 73 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 105 52 6 = 41 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 105 52 7 = 59 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 105 52 8 = 13 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 105 52 9 = 103 :=
    slopeOrbit_step_eval 8 3 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 105 52 9 = slopeOrbit 105 52 1
    rw [e9, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide

/-- `(105,52)`: the certified class-1 count cap `|fibre_1| <= 1 * ceil(W/8)`. -/
theorem sreClass1Count_of_datum_105_52 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 105) (hK : (class1SlopeDatum ctx).K₀ = 52) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 8 - 1) / 8) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 8)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_105_52.1
  have hcount : (class1Band4CycleBand ctx 8).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_105_52.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 8).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 8 - 1) / 8) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 8 - 1) / 8) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(107,53)`: period `53`, cycle `[105, 103, 99, 91, 75, 43, 65, 23, 77, 47, 81, 55, 3, 85, 63, 19, 45, 73, 39, 49, 89, 71, 35, 33, 25, 93, 79, 51, 97, 87, 67, 27, 1, 21, 61, 15, 13, 101, 95, 83, 59, 11, 69, 31, 17, 29, 9, 37, 41, 57, 7, 5, 53]`, bands `[1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 1, 2, 7, 3, 1, 3, 4, 1, 1, 1, 1, 4, 1, 2, 3, 2, 4, 2, 2, 1, 4, 5, 2]` - band-4 residue set `{37, 42, 47, 51}` (values `13, 11, 9, 7`), `b4 = 4`. -/
private theorem sreCert_107_53 :
    slopeOrbit 107 53 (1 + 53) = slopeOrbit 107 53 1
      ∧ ∀ j, 1 ≤ j → j ≤ 53 →
          canonGap 107 (slopeOrbit 107 53 j) = 4 → j ∈ ({37, 42, 47, 51} : Finset ℕ) := by
  have e0 : slopeOrbit 107 53 0 = 53 := rfl
  have e1 : slopeOrbit 107 53 1 = 105 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 107 53 2 = 103 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 107 53 3 = 99 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 107 53 4 = 91 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 107 53 5 = 75 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 107 53 6 = 43 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 107 53 7 = 65 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 107 53 8 = 23 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 107 53 9 = 77 :=
    slopeOrbit_step_eval 8 2 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 107 53 10 = 47 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 107 53 11 = 81 :=
    slopeOrbit_step_eval 10 1 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 107 53 12 = 55 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 107 53 13 = 3 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 107 53 14 = 85 :=
    slopeOrbit_step_eval 13 5 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 107 53 15 = 63 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 107 53 16 = 19 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 107 53 17 = 45 :=
    slopeOrbit_step_eval 16 2 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 107 53 18 = 73 :=
    slopeOrbit_step_eval 17 1 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 107 53 19 = 39 :=
    slopeOrbit_step_eval 18 0 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 107 53 20 = 49 :=
    slopeOrbit_step_eval 19 1 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 107 53 21 = 89 :=
    slopeOrbit_step_eval 20 1 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 107 53 22 = 71 :=
    slopeOrbit_step_eval 21 0 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 107 53 23 = 35 :=
    slopeOrbit_step_eval 22 0 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 107 53 24 = 33 :=
    slopeOrbit_step_eval 23 1 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 107 53 25 = 25 :=
    slopeOrbit_step_eval 24 1 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 107 53 26 = 93 :=
    slopeOrbit_step_eval 25 2 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 107 53 27 = 79 :=
    slopeOrbit_step_eval 26 0 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 107 53 28 = 51 :=
    slopeOrbit_step_eval 27 0 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 107 53 29 = 97 :=
    slopeOrbit_step_eval 28 1 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 107 53 30 = 87 :=
    slopeOrbit_step_eval 29 0 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : slopeOrbit 107 53 31 = 67 :=
    slopeOrbit_step_eval 30 0 e30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e32 : slopeOrbit 107 53 32 = 27 :=
    slopeOrbit_step_eval 31 0 e31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e33 : slopeOrbit 107 53 33 = 1 :=
    slopeOrbit_step_eval 32 1 e32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e34 : slopeOrbit 107 53 34 = 21 :=
    slopeOrbit_step_eval 33 6 e33 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e35 : slopeOrbit 107 53 35 = 61 :=
    slopeOrbit_step_eval 34 2 e34 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e36 : slopeOrbit 107 53 36 = 15 :=
    slopeOrbit_step_eval 35 0 e35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e37 : slopeOrbit 107 53 37 = 13 :=
    slopeOrbit_step_eval 36 2 e36 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e38 : slopeOrbit 107 53 38 = 101 :=
    slopeOrbit_step_eval 37 3 e37 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e39 : slopeOrbit 107 53 39 = 95 :=
    slopeOrbit_step_eval 38 0 e38 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e40 : slopeOrbit 107 53 40 = 83 :=
    slopeOrbit_step_eval 39 0 e39 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e41 : slopeOrbit 107 53 41 = 59 :=
    slopeOrbit_step_eval 40 0 e40 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e42 : slopeOrbit 107 53 42 = 11 :=
    slopeOrbit_step_eval 41 0 e41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e43 : slopeOrbit 107 53 43 = 69 :=
    slopeOrbit_step_eval 42 3 e42 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e44 : slopeOrbit 107 53 44 = 31 :=
    slopeOrbit_step_eval 43 0 e43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e45 : slopeOrbit 107 53 45 = 17 :=
    slopeOrbit_step_eval 44 1 e44 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e46 : slopeOrbit 107 53 46 = 29 :=
    slopeOrbit_step_eval 45 2 e45 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e47 : slopeOrbit 107 53 47 = 9 :=
    slopeOrbit_step_eval 46 1 e46 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e48 : slopeOrbit 107 53 48 = 37 :=
    slopeOrbit_step_eval 47 3 e47 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e49 : slopeOrbit 107 53 49 = 41 :=
    slopeOrbit_step_eval 48 1 e48 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e50 : slopeOrbit 107 53 50 = 57 :=
    slopeOrbit_step_eval 49 1 e49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e51 : slopeOrbit 107 53 51 = 7 :=
    slopeOrbit_step_eval 50 0 e50 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e52 : slopeOrbit 107 53 52 = 5 :=
    slopeOrbit_step_eval 51 3 e51 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e53 : slopeOrbit 107 53 53 = 53 :=
    slopeOrbit_step_eval 52 4 e52 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e54 : slopeOrbit 107 53 54 = 105 :=
    slopeOrbit_step_eval 53 1 e53 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 107 53 54 = slopeOrbit 107 53 1
    rw [e54, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e26] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e27] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e28] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e29] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e30] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e31] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e32] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e33] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e34] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e35] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e36] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e38] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e39] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e40] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e41] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e43] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e44] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e45] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e46] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e48] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e49] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e50] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e52] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e53] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))

/-- `(107,53)`: the certified class-1 count cap `|fibre_1| <= 4 * ceil(W/53)`. -/
theorem sreClass1Count_of_datum_107_53 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 107) (hK : (class1SlopeDatum ctx).K₀ = 53) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 4 * (((supportShell ctx.shell.d ctx.shell.X).card + 53 - 1) / 53) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 53)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_107_53.1
  have hcount : (class1Band4CycleBand ctx 53).card ≤ 4 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_107_53.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 53).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 53 - 1) / 53) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 4 * (((supportShell ctx.shell.d ctx.shell.X).card + 53 - 1) / 53) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(111,1)`: period `14`, cycle `[17, 25, 89, 67, 23, 73, 35, 29, 5, 49, 85, 59, 7, 1]`, bands `[3, 3, 1, 1, 3, 1, 2, 2, 5, 2, 1, 1, 4, 7]` - band-4 residue set `{13}` (values `7`), `b4 = 1`. -/
private theorem sreCert_111_1 :
    slopeOrbit 111 1 (1 + 14) = slopeOrbit 111 1 1
      ∧ ∀ j, 1 ≤ j → j ≤ 14 →
          canonGap 111 (slopeOrbit 111 1 j) = 4 → j ∈ ({13} : Finset ℕ) := by
  have e0 : slopeOrbit 111 1 0 = 1 := rfl
  have e1 : slopeOrbit 111 1 1 = 17 :=
    slopeOrbit_step_eval 0 6 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 111 1 2 = 25 :=
    slopeOrbit_step_eval 1 2 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 111 1 3 = 89 :=
    slopeOrbit_step_eval 2 2 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 111 1 4 = 67 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 111 1 5 = 23 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 111 1 6 = 73 :=
    slopeOrbit_step_eval 5 2 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 111 1 7 = 35 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 111 1 8 = 29 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 111 1 9 = 5 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 111 1 10 = 49 :=
    slopeOrbit_step_eval 9 4 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 111 1 11 = 85 :=
    slopeOrbit_step_eval 10 1 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 111 1 12 = 59 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 111 1 13 = 7 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 111 1 14 = 1 :=
    slopeOrbit_step_eval 13 3 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 111 1 15 = 17 :=
    slopeOrbit_step_eval 14 6 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 111 1 15 = slopeOrbit 111 1 1
    rw [e15, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(111,1)`: the certified class-1 count cap `|fibre_1| <= 1 * ceil(W/14)`. -/
theorem sreClass1Count_of_datum_111_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 111) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 14 - 1) / 14) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 14)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_111_1.1
  have hcount : (class1Band4CycleBand ctx 14).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_111_1.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 14).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 14 - 1) / 14) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 14 - 1) / 14) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(111,18)`: period `18`, cycle `[33, 21, 57, 3, 81, 51, 93, 75, 39, 45, 69, 27, 105, 99, 87, 63, 15, 9]`, bands `[2, 3, 1, 6, 1, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 3, 4]` - band-4 residue set `{18}` (values `9`), `b4 = 1`. -/
private theorem sreCert_111_18 :
    slopeOrbit 111 18 (1 + 18) = slopeOrbit 111 18 1
      ∧ ∀ j, 1 ≤ j → j ≤ 18 →
          canonGap 111 (slopeOrbit 111 18 j) = 4 → j ∈ ({18} : Finset ℕ) := by
  have e0 : slopeOrbit 111 18 0 = 18 := rfl
  have e1 : slopeOrbit 111 18 1 = 33 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 111 18 2 = 21 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 111 18 3 = 57 :=
    slopeOrbit_step_eval 2 2 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 111 18 4 = 3 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 111 18 5 = 81 :=
    slopeOrbit_step_eval 4 5 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 111 18 6 = 51 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 111 18 7 = 93 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 111 18 8 = 75 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 111 18 9 = 39 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 111 18 10 = 45 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 111 18 11 = 69 :=
    slopeOrbit_step_eval 10 1 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 111 18 12 = 27 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 111 18 13 = 105 :=
    slopeOrbit_step_eval 12 2 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 111 18 14 = 99 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 111 18 15 = 87 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 111 18 16 = 63 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 111 18 17 = 15 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 111 18 18 = 9 :=
    slopeOrbit_step_eval 17 2 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 111 18 19 = 33 :=
    slopeOrbit_step_eval 18 3 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 111 18 19 = slopeOrbit 111 18 1
    rw [e19, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide

/-- `(111,18)`: the certified class-1 count cap `|fibre_1| <= 1 * ceil(W/18)`. -/
theorem sreClass1Count_of_datum_111_18 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 111) (hK : (class1SlopeDatum ctx).K₀ = 18) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 18 - 1) / 18) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 18)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_111_18.1
  have hcount : (class1Band4CycleBand ctx 18).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_111_18.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 18).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 18 - 1) / 18) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 18 - 1) / 18) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(111,55)`: period `22`, cycle `[109, 107, 103, 95, 79, 47, 77, 43, 61, 11, 65, 19, 41, 53, 101, 91, 71, 31, 13, 97, 83, 55]`, bands `[1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2]` - band-4 residue set `{10, 19}` (values `11, 13`), `b4 = 2`. -/
private theorem sreCert_111_55 :
    slopeOrbit 111 55 (1 + 22) = slopeOrbit 111 55 1
      ∧ ∀ j, 1 ≤ j → j ≤ 22 →
          canonGap 111 (slopeOrbit 111 55 j) = 4 → j ∈ ({10, 19} : Finset ℕ) := by
  have e0 : slopeOrbit 111 55 0 = 55 := rfl
  have e1 : slopeOrbit 111 55 1 = 109 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 111 55 2 = 107 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 111 55 3 = 103 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 111 55 4 = 95 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 111 55 5 = 79 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 111 55 6 = 47 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 111 55 7 = 77 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 111 55 8 = 43 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 111 55 9 = 61 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 111 55 10 = 11 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 111 55 11 = 65 :=
    slopeOrbit_step_eval 10 3 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 111 55 12 = 19 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 111 55 13 = 41 :=
    slopeOrbit_step_eval 12 2 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 111 55 14 = 53 :=
    slopeOrbit_step_eval 13 1 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 111 55 15 = 101 :=
    slopeOrbit_step_eval 14 1 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 111 55 16 = 91 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 111 55 17 = 71 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 111 55 18 = 31 :=
    slopeOrbit_step_eval 17 0 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 111 55 19 = 13 :=
    slopeOrbit_step_eval 18 1 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 111 55 20 = 97 :=
    slopeOrbit_step_eval 19 3 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 111 55 21 = 83 :=
    slopeOrbit_step_eval 20 0 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 111 55 22 = 55 :=
    slopeOrbit_step_eval 21 0 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 111 55 23 = 109 :=
    slopeOrbit_step_eval 22 1 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 111 55 23 = slopeOrbit 111 55 1
    rw [e23, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))

/-- `(111,55)`: the certified class-1 count cap `|fibre_1| <= 2 * ceil(W/22)`. -/
theorem sreClass1Count_of_datum_111_55 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 111) (hK : (class1SlopeDatum ctx).K₀ = 55) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 22 - 1) / 22) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 22)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_111_55.1
  have hcount : (class1Band4CycleBand ctx 22).card ≤ 2 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_111_55.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 22).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 22 - 1) / 22) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 22 - 1) / 22) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(115,2)`: period `19`, cycle `[13, 93, 71, 27, 101, 87, 59, 3, 77, 39, 41, 49, 81, 47, 73, 31, 9, 29, 1]`, bands `[4, 1, 1, 3, 1, 1, 1, 6, 1, 2, 2, 2, 1, 2, 1, 2, 4, 2, 7]` - band-4 residue set `{1, 17}` (values `13, 9`), `b4 = 2`. -/
private theorem sreCert_115_2 :
    slopeOrbit 115 2 (1 + 19) = slopeOrbit 115 2 1
      ∧ ∀ j, 1 ≤ j → j ≤ 19 →
          canonGap 115 (slopeOrbit 115 2 j) = 4 → j ∈ ({1, 17} : Finset ℕ) := by
  have e0 : slopeOrbit 115 2 0 = 2 := rfl
  have e1 : slopeOrbit 115 2 1 = 13 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 115 2 2 = 93 :=
    slopeOrbit_step_eval 1 3 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 115 2 3 = 71 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 115 2 4 = 27 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 115 2 5 = 101 :=
    slopeOrbit_step_eval 4 2 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 115 2 6 = 87 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 115 2 7 = 59 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 115 2 8 = 3 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 115 2 9 = 77 :=
    slopeOrbit_step_eval 8 5 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 115 2 10 = 39 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 115 2 11 = 41 :=
    slopeOrbit_step_eval 10 1 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 115 2 12 = 49 :=
    slopeOrbit_step_eval 11 1 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 115 2 13 = 81 :=
    slopeOrbit_step_eval 12 1 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 115 2 14 = 47 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 115 2 15 = 73 :=
    slopeOrbit_step_eval 14 1 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 115 2 16 = 31 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 115 2 17 = 9 :=
    slopeOrbit_step_eval 16 1 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 115 2 18 = 29 :=
    slopeOrbit_step_eval 17 3 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 115 2 19 = 1 :=
    slopeOrbit_step_eval 18 1 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 115 2 20 = 13 :=
    slopeOrbit_step_eval 19 6 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 115 2 20 = slopeOrbit 115 2 1
    rw [e20, e1]
  · intro j h1 h2 hband
    interval_cases j
    · decide
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(115,2)`: the certified class-1 count cap `|fibre_1| <= 2 * ceil(W/19)`. -/
theorem sreClass1Count_of_datum_115_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 115) (hK : (class1SlopeDatum ctx).K₀ = 2) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 19 - 1) / 19) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 19)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_115_2.1
  have hcount : (class1Band4CycleBand ctx 19).card ≤ 2 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_115_2.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 19).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 19 - 1) / 19) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 19 - 1) / 19) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(115,11)`: period `25`, cycle `[61, 7, 109, 103, 91, 67, 19, 37, 33, 17, 21, 53, 97, 79, 43, 57, 113, 111, 107, 99, 83, 51, 89, 63, 11]`, bands `[1, 5, 1, 1, 1, 1, 3, 2, 2, 3, 3, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4]` - band-4 residue set `{25}` (values `11`), `b4 = 1`. -/
private theorem sreCert_115_11 :
    slopeOrbit 115 11 (1 + 25) = slopeOrbit 115 11 1
      ∧ ∀ j, 1 ≤ j → j ≤ 25 →
          canonGap 115 (slopeOrbit 115 11 j) = 4 → j ∈ ({25} : Finset ℕ) := by
  have e0 : slopeOrbit 115 11 0 = 11 := rfl
  have e1 : slopeOrbit 115 11 1 = 61 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 115 11 2 = 7 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 115 11 3 = 109 :=
    slopeOrbit_step_eval 2 4 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 115 11 4 = 103 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 115 11 5 = 91 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 115 11 6 = 67 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 115 11 7 = 19 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 115 11 8 = 37 :=
    slopeOrbit_step_eval 7 2 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 115 11 9 = 33 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 115 11 10 = 17 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 115 11 11 = 21 :=
    slopeOrbit_step_eval 10 2 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 115 11 12 = 53 :=
    slopeOrbit_step_eval 11 2 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 115 11 13 = 97 :=
    slopeOrbit_step_eval 12 1 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 115 11 14 = 79 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 115 11 15 = 43 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 115 11 16 = 57 :=
    slopeOrbit_step_eval 15 1 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 115 11 17 = 113 :=
    slopeOrbit_step_eval 16 1 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 115 11 18 = 111 :=
    slopeOrbit_step_eval 17 0 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 115 11 19 = 107 :=
    slopeOrbit_step_eval 18 0 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 115 11 20 = 99 :=
    slopeOrbit_step_eval 19 0 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 115 11 21 = 83 :=
    slopeOrbit_step_eval 20 0 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 115 11 22 = 51 :=
    slopeOrbit_step_eval 21 0 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 115 11 23 = 89 :=
    slopeOrbit_step_eval 22 1 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 115 11 24 = 63 :=
    slopeOrbit_step_eval 23 0 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 115 11 25 = 11 :=
    slopeOrbit_step_eval 24 0 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 115 11 26 = 61 :=
    slopeOrbit_step_eval 25 3 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 115 11 26 = slopeOrbit 115 11 1
    rw [e26, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide

/-- `(115,11)`: the certified class-1 count cap `|fibre_1| <= 1 * ceil(W/25)`. -/
theorem sreClass1Count_of_datum_115_11 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 115) (hK : (class1SlopeDatum ctx).K₀ = 11) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 25 - 1) / 25) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 25)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_115_11.1
  have hcount : (class1Band4CycleBand ctx 25).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_115_11.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 25).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 25 - 1) / 25) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 25 - 1) / 25) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(115,57)`: period `25`, cycle `[113, 111, 107, 99, 83, 51, 89, 63, 11, 61, 7, 109, 103, 91, 67, 19, 37, 33, 17, 21, 53, 97, 79, 43, 57]`, bands `[1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 3, 2, 2, 3, 3, 2, 1, 1, 2, 2]` - band-4 residue set `{9}` (values `11`), `b4 = 1`. -/
private theorem sreCert_115_57 :
    slopeOrbit 115 57 (1 + 25) = slopeOrbit 115 57 1
      ∧ ∀ j, 1 ≤ j → j ≤ 25 →
          canonGap 115 (slopeOrbit 115 57 j) = 4 → j ∈ ({9} : Finset ℕ) := by
  have e0 : slopeOrbit 115 57 0 = 57 := rfl
  have e1 : slopeOrbit 115 57 1 = 113 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 115 57 2 = 111 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 115 57 3 = 107 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 115 57 4 = 99 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 115 57 5 = 83 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 115 57 6 = 51 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 115 57 7 = 89 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 115 57 8 = 63 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 115 57 9 = 11 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 115 57 10 = 61 :=
    slopeOrbit_step_eval 9 3 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 115 57 11 = 7 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 115 57 12 = 109 :=
    slopeOrbit_step_eval 11 4 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 115 57 13 = 103 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 115 57 14 = 91 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 115 57 15 = 67 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 115 57 16 = 19 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 115 57 17 = 37 :=
    slopeOrbit_step_eval 16 2 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 115 57 18 = 33 :=
    slopeOrbit_step_eval 17 1 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 115 57 19 = 17 :=
    slopeOrbit_step_eval 18 1 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 115 57 20 = 21 :=
    slopeOrbit_step_eval 19 2 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 115 57 21 = 53 :=
    slopeOrbit_step_eval 20 2 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 115 57 22 = 97 :=
    slopeOrbit_step_eval 21 1 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 115 57 23 = 79 :=
    slopeOrbit_step_eval 22 0 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 115 57 24 = 43 :=
    slopeOrbit_step_eval 23 0 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 115 57 25 = 57 :=
    slopeOrbit_step_eval 24 1 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 115 57 26 = 113 :=
    slopeOrbit_step_eval 25 1 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 115 57 26 = slopeOrbit 115 57 1
    rw [e26, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))

/-- `(115,57)`: the certified class-1 count cap `|fibre_1| <= 1 * ceil(W/25)`. -/
theorem sreClass1Count_of_datum_115_57 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 115) (hK : (class1SlopeDatum ctx).K₀ = 57) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 25 - 1) / 25) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 25)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_115_57.1
  have hcount : (class1Band4CycleBand ctx 25).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_115_57.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 25).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 25 - 1) / 25) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 25 - 1) / 25) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(117,1)`: period `3`, cycle `[11, 59, 1]`, bands `[4, 1, 7]` - band-4 residue set `{1}` (values `11`), `b4 = 1`. -/
private theorem sreCert_117_1 :
    slopeOrbit 117 1 (1 + 3) = slopeOrbit 117 1 1
      ∧ ∀ j, 1 ≤ j → j ≤ 3 →
          canonGap 117 (slopeOrbit 117 1 j) = 4 → j ∈ ({1} : Finset ℕ) := by
  have e0 : slopeOrbit 117 1 0 = 1 := rfl
  have e1 : slopeOrbit 117 1 1 = 11 :=
    slopeOrbit_step_eval 0 6 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 117 1 2 = 59 :=
    slopeOrbit_step_eval 1 3 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 117 1 3 = 1 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 117 1 4 = 11 :=
    slopeOrbit_step_eval 3 6 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 117 1 4 = slopeOrbit 117 1 1
    rw [e4, e1]
  · intro j h1 h2 hband
    interval_cases j
    · decide
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(117,1)`: the certified class-1 count cap `|fibre_1| <= 1 * ceil(W/3)`. -/
theorem sreClass1Count_of_datum_117_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 117) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 3 - 1) / 3) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 3)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_117_1.1
  have hcount : (class1Band4CycleBand ctx 3).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_117_1.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 3).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 3 - 1) / 3) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 3 - 1) / 3) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(117,4)`: period `3`, cycle `[11, 59, 1]`, bands `[4, 1, 7]` - band-4 residue set `{1}` (values `11`), `b4 = 1`. -/
private theorem sreCert_117_4 :
    slopeOrbit 117 4 (1 + 3) = slopeOrbit 117 4 1
      ∧ ∀ j, 1 ≤ j → j ≤ 3 →
          canonGap 117 (slopeOrbit 117 4 j) = 4 → j ∈ ({1} : Finset ℕ) := by
  have e0 : slopeOrbit 117 4 0 = 4 := rfl
  have e1 : slopeOrbit 117 4 1 = 11 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 117 4 2 = 59 :=
    slopeOrbit_step_eval 1 3 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 117 4 3 = 1 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 117 4 4 = 11 :=
    slopeOrbit_step_eval 3 6 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 117 4 4 = slopeOrbit 117 4 1
    rw [e4, e1]
  · intro j h1 h2 hband
    interval_cases j
    · decide
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(117,4)`: the certified class-1 count cap `|fibre_1| <= 1 * ceil(W/3)`. -/
theorem sreClass1Count_of_datum_117_4 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 117) (hK : (class1SlopeDatum ctx).K₀ = 4) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 3 - 1) / 3) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 3)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_117_4.1
  have hcount : (class1Band4CycleBand ctx 3).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_117_4.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 3).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 3 - 1) / 3) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 3 - 1) / 3) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(119,8)`: period `9`, cycle `[9, 25, 81, 43, 53, 93, 67, 15, 1]`, bands `[4, 3, 1, 2, 2, 1, 1, 3, 7]` - band-4 residue set `{1}` (values `9`), `b4 = 1`. -/
private theorem sreCert_119_8 :
    slopeOrbit 119 8 (1 + 9) = slopeOrbit 119 8 1
      ∧ ∀ j, 1 ≤ j → j ≤ 9 →
          canonGap 119 (slopeOrbit 119 8 j) = 4 → j ∈ ({1} : Finset ℕ) := by
  have e0 : slopeOrbit 119 8 0 = 8 := rfl
  have e1 : slopeOrbit 119 8 1 = 9 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 119 8 2 = 25 :=
    slopeOrbit_step_eval 1 3 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 119 8 3 = 81 :=
    slopeOrbit_step_eval 2 2 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 119 8 4 = 43 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 119 8 5 = 53 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 119 8 6 = 93 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 119 8 7 = 67 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 119 8 8 = 15 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 119 8 9 = 1 :=
    slopeOrbit_step_eval 8 2 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 119 8 10 = 9 :=
    slopeOrbit_step_eval 9 6 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 119 8 10 = slopeOrbit 119 8 1
    rw [e10, e1]
  · intro j h1 h2 hband
    interval_cases j
    · decide
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(119,8)`: the certified class-1 count cap `|fibre_1| <= 1 * ceil(W/9)`. -/
theorem sreClass1Count_of_datum_119_8 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 119) (hK : (class1SlopeDatum ctx).K₀ = 8) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 9 - 1) / 9) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 9)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_119_8.1
  have hcount : (class1Band4CycleBand ctx 9).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_119_8.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 9).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 9 - 1) / 9) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 9 - 1) / 9) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(119,59)`: period `15`, cycle `[117, 115, 111, 103, 87, 55, 101, 83, 47, 69, 19, 33, 13, 89, 59]`, bands `[1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2]` - band-4 residue set `{13}` (values `13`), `b4 = 1`. -/
private theorem sreCert_119_59 :
    slopeOrbit 119 59 (1 + 15) = slopeOrbit 119 59 1
      ∧ ∀ j, 1 ≤ j → j ≤ 15 →
          canonGap 119 (slopeOrbit 119 59 j) = 4 → j ∈ ({13} : Finset ℕ) := by
  have e0 : slopeOrbit 119 59 0 = 59 := rfl
  have e1 : slopeOrbit 119 59 1 = 117 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 119 59 2 = 115 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 119 59 3 = 111 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 119 59 4 = 103 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 119 59 5 = 87 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 119 59 6 = 55 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 119 59 7 = 101 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 119 59 8 = 83 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 119 59 9 = 47 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 119 59 10 = 69 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 119 59 11 = 19 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 119 59 12 = 33 :=
    slopeOrbit_step_eval 11 2 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 119 59 13 = 13 :=
    slopeOrbit_step_eval 12 1 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 119 59 14 = 89 :=
    slopeOrbit_step_eval 13 3 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 119 59 15 = 59 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 119 59 16 = 117 :=
    slopeOrbit_step_eval 15 1 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 119 59 16 = slopeOrbit 119 59 1
    rw [e16, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))

/-- `(119,59)`: the certified class-1 count cap `|fibre_1| <= 1 * ceil(W/15)`. -/
theorem sreClass1Count_of_datum_119_59 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 119) (hK : (class1SlopeDatum ctx).K₀ = 59) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 15 - 1) / 15) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 15)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_119_59.1
  have hcount : (class1Band4CycleBand ctx 15).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_119_59.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 15).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 15 - 1) / 15) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 15 - 1) / 15) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(121,5)`: period `55`, cycle `[39, 35, 19, 31, 3, 71, 21, 47, 67, 13, 87, 53, 91, 61, 1, 7, 103, 85, 49, 75, 29, 111, 101, 81, 41, 43, 51, 83, 45, 59, 115, 109, 97, 73, 25, 79, 37, 27, 95, 69, 17, 15, 119, 117, 113, 105, 89, 57, 107, 93, 65, 9, 23, 63, 5]`, bands `[2, 2, 3, 2, 6, 1, 3, 2, 1, 4, 1, 2, 1, 1, 7, 5, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 5]` - band-4 residue set `{10, 42, 52}` (values `13, 15, 9`), `b4 = 3`. -/
private theorem sreCert_121_5 :
    slopeOrbit 121 5 (1 + 55) = slopeOrbit 121 5 1
      ∧ ∀ j, 1 ≤ j → j ≤ 55 →
          canonGap 121 (slopeOrbit 121 5 j) = 4 → j ∈ ({10, 42, 52} : Finset ℕ) := by
  have e0 : slopeOrbit 121 5 0 = 5 := rfl
  have e1 : slopeOrbit 121 5 1 = 39 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 121 5 2 = 35 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 121 5 3 = 19 :=
    slopeOrbit_step_eval 2 1 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 121 5 4 = 31 :=
    slopeOrbit_step_eval 3 2 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 121 5 5 = 3 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 121 5 6 = 71 :=
    slopeOrbit_step_eval 5 5 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 121 5 7 = 21 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 121 5 8 = 47 :=
    slopeOrbit_step_eval 7 2 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 121 5 9 = 67 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 121 5 10 = 13 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 121 5 11 = 87 :=
    slopeOrbit_step_eval 10 3 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 121 5 12 = 53 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 121 5 13 = 91 :=
    slopeOrbit_step_eval 12 1 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 121 5 14 = 61 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 121 5 15 = 1 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 121 5 16 = 7 :=
    slopeOrbit_step_eval 15 6 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 121 5 17 = 103 :=
    slopeOrbit_step_eval 16 4 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 121 5 18 = 85 :=
    slopeOrbit_step_eval 17 0 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 121 5 19 = 49 :=
    slopeOrbit_step_eval 18 0 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 121 5 20 = 75 :=
    slopeOrbit_step_eval 19 1 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 121 5 21 = 29 :=
    slopeOrbit_step_eval 20 0 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 121 5 22 = 111 :=
    slopeOrbit_step_eval 21 2 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 121 5 23 = 101 :=
    slopeOrbit_step_eval 22 0 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 121 5 24 = 81 :=
    slopeOrbit_step_eval 23 0 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 121 5 25 = 41 :=
    slopeOrbit_step_eval 24 0 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 121 5 26 = 43 :=
    slopeOrbit_step_eval 25 1 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 121 5 27 = 51 :=
    slopeOrbit_step_eval 26 1 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 121 5 28 = 83 :=
    slopeOrbit_step_eval 27 1 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 121 5 29 = 45 :=
    slopeOrbit_step_eval 28 0 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 121 5 30 = 59 :=
    slopeOrbit_step_eval 29 1 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : slopeOrbit 121 5 31 = 115 :=
    slopeOrbit_step_eval 30 1 e30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e32 : slopeOrbit 121 5 32 = 109 :=
    slopeOrbit_step_eval 31 0 e31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e33 : slopeOrbit 121 5 33 = 97 :=
    slopeOrbit_step_eval 32 0 e32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e34 : slopeOrbit 121 5 34 = 73 :=
    slopeOrbit_step_eval 33 0 e33 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e35 : slopeOrbit 121 5 35 = 25 :=
    slopeOrbit_step_eval 34 0 e34 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e36 : slopeOrbit 121 5 36 = 79 :=
    slopeOrbit_step_eval 35 2 e35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e37 : slopeOrbit 121 5 37 = 37 :=
    slopeOrbit_step_eval 36 0 e36 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e38 : slopeOrbit 121 5 38 = 27 :=
    slopeOrbit_step_eval 37 1 e37 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e39 : slopeOrbit 121 5 39 = 95 :=
    slopeOrbit_step_eval 38 2 e38 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e40 : slopeOrbit 121 5 40 = 69 :=
    slopeOrbit_step_eval 39 0 e39 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e41 : slopeOrbit 121 5 41 = 17 :=
    slopeOrbit_step_eval 40 0 e40 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e42 : slopeOrbit 121 5 42 = 15 :=
    slopeOrbit_step_eval 41 2 e41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e43 : slopeOrbit 121 5 43 = 119 :=
    slopeOrbit_step_eval 42 3 e42 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e44 : slopeOrbit 121 5 44 = 117 :=
    slopeOrbit_step_eval 43 0 e43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e45 : slopeOrbit 121 5 45 = 113 :=
    slopeOrbit_step_eval 44 0 e44 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e46 : slopeOrbit 121 5 46 = 105 :=
    slopeOrbit_step_eval 45 0 e45 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e47 : slopeOrbit 121 5 47 = 89 :=
    slopeOrbit_step_eval 46 0 e46 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e48 : slopeOrbit 121 5 48 = 57 :=
    slopeOrbit_step_eval 47 0 e47 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e49 : slopeOrbit 121 5 49 = 107 :=
    slopeOrbit_step_eval 48 1 e48 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e50 : slopeOrbit 121 5 50 = 93 :=
    slopeOrbit_step_eval 49 0 e49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e51 : slopeOrbit 121 5 51 = 65 :=
    slopeOrbit_step_eval 50 0 e50 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e52 : slopeOrbit 121 5 52 = 9 :=
    slopeOrbit_step_eval 51 0 e51 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e53 : slopeOrbit 121 5 53 = 23 :=
    slopeOrbit_step_eval 52 3 e52 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e54 : slopeOrbit 121 5 54 = 63 :=
    slopeOrbit_step_eval 53 2 e53 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e55 : slopeOrbit 121 5 55 = 5 :=
    slopeOrbit_step_eval 54 0 e54 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e56 : slopeOrbit 121 5 56 = 39 :=
    slopeOrbit_step_eval 55 4 e55 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 121 5 56 = slopeOrbit 121 5 1
    rw [e56, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e26] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e27] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e28] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e29] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e30] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e31] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e32] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e33] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e34] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e35] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e36] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e37] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e38] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e39] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e40] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e41] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e43] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e44] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e45] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e46] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e47] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e48] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e49] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e50] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e51] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e53] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e54] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e55] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(121,5)`: the certified class-1 count cap `|fibre_1| <= 3 * ceil(W/55)`. -/
theorem sreClass1Count_of_datum_121_5 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 121) (hK : (class1SlopeDatum ctx).K₀ = 5) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 3 * (((supportShell ctx.shell.d ctx.shell.X).card + 55 - 1) / 55) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 55)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_121_5.1
  have hcount : (class1Band4CycleBand ctx 55).card ≤ 3 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_121_5.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 55).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 55 - 1) / 55) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 3 * (((supportShell ctx.shell.d ctx.shell.X).card + 55 - 1) / 55) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(121,60)`: period `55`, cycle `[119, 117, 113, 105, 89, 57, 107, 93, 65, 9, 23, 63, 5, 39, 35, 19, 31, 3, 71, 21, 47, 67, 13, 87, 53, 91, 61, 1, 7, 103, 85, 49, 75, 29, 111, 101, 81, 41, 43, 51, 83, 45, 59, 115, 109, 97, 73, 25, 79, 37, 27, 95, 69, 17, 15]`, bands `[1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 5, 2, 2, 3, 2, 6, 1, 3, 2, 1, 4, 1, 2, 1, 1, 7, 5, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 4]` - band-4 residue set `{10, 23, 55}` (values `9, 13, 15`), `b4 = 3`. -/
private theorem sreCert_121_60 :
    slopeOrbit 121 60 (1 + 55) = slopeOrbit 121 60 1
      ∧ ∀ j, 1 ≤ j → j ≤ 55 →
          canonGap 121 (slopeOrbit 121 60 j) = 4 → j ∈ ({10, 23, 55} : Finset ℕ) := by
  have e0 : slopeOrbit 121 60 0 = 60 := rfl
  have e1 : slopeOrbit 121 60 1 = 119 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 121 60 2 = 117 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 121 60 3 = 113 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 121 60 4 = 105 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 121 60 5 = 89 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 121 60 6 = 57 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 121 60 7 = 107 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 121 60 8 = 93 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 121 60 9 = 65 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 121 60 10 = 9 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 121 60 11 = 23 :=
    slopeOrbit_step_eval 10 3 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 121 60 12 = 63 :=
    slopeOrbit_step_eval 11 2 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 121 60 13 = 5 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 121 60 14 = 39 :=
    slopeOrbit_step_eval 13 4 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 121 60 15 = 35 :=
    slopeOrbit_step_eval 14 1 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 121 60 16 = 19 :=
    slopeOrbit_step_eval 15 1 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 121 60 17 = 31 :=
    slopeOrbit_step_eval 16 2 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 121 60 18 = 3 :=
    slopeOrbit_step_eval 17 1 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 121 60 19 = 71 :=
    slopeOrbit_step_eval 18 5 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 121 60 20 = 21 :=
    slopeOrbit_step_eval 19 0 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 121 60 21 = 47 :=
    slopeOrbit_step_eval 20 2 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 121 60 22 = 67 :=
    slopeOrbit_step_eval 21 1 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 121 60 23 = 13 :=
    slopeOrbit_step_eval 22 0 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 121 60 24 = 87 :=
    slopeOrbit_step_eval 23 3 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 121 60 25 = 53 :=
    slopeOrbit_step_eval 24 0 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 121 60 26 = 91 :=
    slopeOrbit_step_eval 25 1 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 121 60 27 = 61 :=
    slopeOrbit_step_eval 26 0 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 121 60 28 = 1 :=
    slopeOrbit_step_eval 27 0 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 121 60 29 = 7 :=
    slopeOrbit_step_eval 28 6 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 121 60 30 = 103 :=
    slopeOrbit_step_eval 29 4 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : slopeOrbit 121 60 31 = 85 :=
    slopeOrbit_step_eval 30 0 e30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e32 : slopeOrbit 121 60 32 = 49 :=
    slopeOrbit_step_eval 31 0 e31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e33 : slopeOrbit 121 60 33 = 75 :=
    slopeOrbit_step_eval 32 1 e32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e34 : slopeOrbit 121 60 34 = 29 :=
    slopeOrbit_step_eval 33 0 e33 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e35 : slopeOrbit 121 60 35 = 111 :=
    slopeOrbit_step_eval 34 2 e34 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e36 : slopeOrbit 121 60 36 = 101 :=
    slopeOrbit_step_eval 35 0 e35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e37 : slopeOrbit 121 60 37 = 81 :=
    slopeOrbit_step_eval 36 0 e36 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e38 : slopeOrbit 121 60 38 = 41 :=
    slopeOrbit_step_eval 37 0 e37 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e39 : slopeOrbit 121 60 39 = 43 :=
    slopeOrbit_step_eval 38 1 e38 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e40 : slopeOrbit 121 60 40 = 51 :=
    slopeOrbit_step_eval 39 1 e39 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e41 : slopeOrbit 121 60 41 = 83 :=
    slopeOrbit_step_eval 40 1 e40 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e42 : slopeOrbit 121 60 42 = 45 :=
    slopeOrbit_step_eval 41 0 e41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e43 : slopeOrbit 121 60 43 = 59 :=
    slopeOrbit_step_eval 42 1 e42 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e44 : slopeOrbit 121 60 44 = 115 :=
    slopeOrbit_step_eval 43 1 e43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e45 : slopeOrbit 121 60 45 = 109 :=
    slopeOrbit_step_eval 44 0 e44 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e46 : slopeOrbit 121 60 46 = 97 :=
    slopeOrbit_step_eval 45 0 e45 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e47 : slopeOrbit 121 60 47 = 73 :=
    slopeOrbit_step_eval 46 0 e46 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e48 : slopeOrbit 121 60 48 = 25 :=
    slopeOrbit_step_eval 47 0 e47 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e49 : slopeOrbit 121 60 49 = 79 :=
    slopeOrbit_step_eval 48 2 e48 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e50 : slopeOrbit 121 60 50 = 37 :=
    slopeOrbit_step_eval 49 0 e49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e51 : slopeOrbit 121 60 51 = 27 :=
    slopeOrbit_step_eval 50 1 e50 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e52 : slopeOrbit 121 60 52 = 95 :=
    slopeOrbit_step_eval 51 2 e51 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e53 : slopeOrbit 121 60 53 = 69 :=
    slopeOrbit_step_eval 52 0 e52 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e54 : slopeOrbit 121 60 54 = 17 :=
    slopeOrbit_step_eval 53 0 e53 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e55 : slopeOrbit 121 60 55 = 15 :=
    slopeOrbit_step_eval 54 2 e54 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e56 : slopeOrbit 121 60 56 = 119 :=
    slopeOrbit_step_eval 55 3 e55 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 121 60 56 = slopeOrbit 121 60 1
    rw [e56, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e26] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e27] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e28] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e29] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e30] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e31] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e32] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e33] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e34] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e35] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e36] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e37] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e38] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e39] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e40] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e41] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e42] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e43] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e44] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e45] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e46] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e47] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e48] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e49] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e50] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e51] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e52] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e53] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e54] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide

/-- `(121,60)`: the certified class-1 count cap `|fibre_1| <= 3 * ceil(W/55)`. -/
theorem sreClass1Count_of_datum_121_60 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 121) (hK : (class1SlopeDatum ctx).K₀ = 60) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 3 * (((supportShell ctx.shell.d ctx.shell.X).card + 55 - 1) / 55) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 55)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_121_60.1
  have hcount : (class1Band4CycleBand ctx 55).card ≤ 3 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_121_60.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 55).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 55 - 1) / 55) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 3 * (((supportShell ctx.shell.d ctx.shell.X).card + 55 - 1) / 55) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(125,2)`: period `50`, cycle `[3, 67, 9, 19, 27, 91, 57, 103, 81, 37, 23, 59, 111, 97, 69, 13, 83, 41, 39, 31, 123, 121, 117, 109, 93, 61, 119, 113, 101, 77, 29, 107, 89, 53, 87, 49, 71, 17, 11, 51, 79, 33, 7, 99, 73, 21, 43, 47, 63, 1]`, bands `[6, 1, 4, 3, 3, 1, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 2, 5, 1, 1, 3, 2, 2, 1, 7]` - band-4 residue set `{3, 16, 39}` (values `9, 13, 11`), `b4 = 3`. -/
private theorem sreCert_125_2 :
    slopeOrbit 125 2 (1 + 50) = slopeOrbit 125 2 1
      ∧ ∀ j, 1 ≤ j → j ≤ 50 →
          canonGap 125 (slopeOrbit 125 2 j) = 4 → j ∈ ({3, 16, 39} : Finset ℕ) := by
  have e0 : slopeOrbit 125 2 0 = 2 := rfl
  have e1 : slopeOrbit 125 2 1 = 3 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 125 2 2 = 67 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 125 2 3 = 9 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 125 2 4 = 19 :=
    slopeOrbit_step_eval 3 3 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 125 2 5 = 27 :=
    slopeOrbit_step_eval 4 2 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 125 2 6 = 91 :=
    slopeOrbit_step_eval 5 2 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 125 2 7 = 57 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 125 2 8 = 103 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 125 2 9 = 81 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 125 2 10 = 37 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 125 2 11 = 23 :=
    slopeOrbit_step_eval 10 1 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 125 2 12 = 59 :=
    slopeOrbit_step_eval 11 2 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 125 2 13 = 111 :=
    slopeOrbit_step_eval 12 1 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 125 2 14 = 97 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 125 2 15 = 69 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 125 2 16 = 13 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 125 2 17 = 83 :=
    slopeOrbit_step_eval 16 3 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 125 2 18 = 41 :=
    slopeOrbit_step_eval 17 0 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 125 2 19 = 39 :=
    slopeOrbit_step_eval 18 1 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 125 2 20 = 31 :=
    slopeOrbit_step_eval 19 1 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 125 2 21 = 123 :=
    slopeOrbit_step_eval 20 2 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 125 2 22 = 121 :=
    slopeOrbit_step_eval 21 0 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 125 2 23 = 117 :=
    slopeOrbit_step_eval 22 0 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 125 2 24 = 109 :=
    slopeOrbit_step_eval 23 0 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 125 2 25 = 93 :=
    slopeOrbit_step_eval 24 0 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 125 2 26 = 61 :=
    slopeOrbit_step_eval 25 0 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 125 2 27 = 119 :=
    slopeOrbit_step_eval 26 1 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 125 2 28 = 113 :=
    slopeOrbit_step_eval 27 0 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 125 2 29 = 101 :=
    slopeOrbit_step_eval 28 0 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 125 2 30 = 77 :=
    slopeOrbit_step_eval 29 0 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : slopeOrbit 125 2 31 = 29 :=
    slopeOrbit_step_eval 30 0 e30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e32 : slopeOrbit 125 2 32 = 107 :=
    slopeOrbit_step_eval 31 2 e31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e33 : slopeOrbit 125 2 33 = 89 :=
    slopeOrbit_step_eval 32 0 e32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e34 : slopeOrbit 125 2 34 = 53 :=
    slopeOrbit_step_eval 33 0 e33 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e35 : slopeOrbit 125 2 35 = 87 :=
    slopeOrbit_step_eval 34 1 e34 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e36 : slopeOrbit 125 2 36 = 49 :=
    slopeOrbit_step_eval 35 0 e35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e37 : slopeOrbit 125 2 37 = 71 :=
    slopeOrbit_step_eval 36 1 e36 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e38 : slopeOrbit 125 2 38 = 17 :=
    slopeOrbit_step_eval 37 0 e37 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e39 : slopeOrbit 125 2 39 = 11 :=
    slopeOrbit_step_eval 38 2 e38 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e40 : slopeOrbit 125 2 40 = 51 :=
    slopeOrbit_step_eval 39 3 e39 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e41 : slopeOrbit 125 2 41 = 79 :=
    slopeOrbit_step_eval 40 1 e40 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e42 : slopeOrbit 125 2 42 = 33 :=
    slopeOrbit_step_eval 41 0 e41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e43 : slopeOrbit 125 2 43 = 7 :=
    slopeOrbit_step_eval 42 1 e42 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e44 : slopeOrbit 125 2 44 = 99 :=
    slopeOrbit_step_eval 43 4 e43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e45 : slopeOrbit 125 2 45 = 73 :=
    slopeOrbit_step_eval 44 0 e44 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e46 : slopeOrbit 125 2 46 = 21 :=
    slopeOrbit_step_eval 45 0 e45 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e47 : slopeOrbit 125 2 47 = 43 :=
    slopeOrbit_step_eval 46 2 e46 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e48 : slopeOrbit 125 2 48 = 47 :=
    slopeOrbit_step_eval 47 1 e47 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e49 : slopeOrbit 125 2 49 = 63 :=
    slopeOrbit_step_eval 48 1 e48 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e50 : slopeOrbit 125 2 50 = 1 :=
    slopeOrbit_step_eval 49 0 e49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e51 : slopeOrbit 125 2 51 = 3 :=
    slopeOrbit_step_eval 50 6 e50 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 125 2 51 = slopeOrbit 125 2 1
    rw [e51, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e26] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e27] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e28] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e29] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e30] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e31] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e32] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e33] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e34] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e35] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e36] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e37] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e38] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e40] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e41] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e42] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e43] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e44] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e45] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e46] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e47] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e48] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e49] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e50] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(125,2)`: the certified class-1 count cap `|fibre_1| <= 3 * ceil(W/50)`. -/
theorem sreClass1Count_of_datum_125_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 125) (hK : (class1SlopeDatum ctx).K₀ = 2) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 3 * (((supportShell ctx.shell.d ctx.shell.X).card + 50 - 1) / 50) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 50)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_125_2.1
  have hcount : (class1Band4CycleBand ctx 50).card ≤ 3 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_125_2.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 50).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 50 - 1) / 50) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 3 * (((supportShell ctx.shell.d ctx.shell.X).card + 50 - 1) / 50) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(125,12)`: period `50`, cycle `[67, 9, 19, 27, 91, 57, 103, 81, 37, 23, 59, 111, 97, 69, 13, 83, 41, 39, 31, 123, 121, 117, 109, 93, 61, 119, 113, 101, 77, 29, 107, 89, 53, 87, 49, 71, 17, 11, 51, 79, 33, 7, 99, 73, 21, 43, 47, 63, 1, 3]`, bands `[1, 4, 3, 3, 1, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 2, 5, 1, 1, 3, 2, 2, 1, 7, 6]` - band-4 residue set `{2, 15, 38}` (values `9, 13, 11`), `b4 = 3`. -/
private theorem sreCert_125_12 :
    slopeOrbit 125 12 (1 + 50) = slopeOrbit 125 12 1
      ∧ ∀ j, 1 ≤ j → j ≤ 50 →
          canonGap 125 (slopeOrbit 125 12 j) = 4 → j ∈ ({2, 15, 38} : Finset ℕ) := by
  have e0 : slopeOrbit 125 12 0 = 12 := rfl
  have e1 : slopeOrbit 125 12 1 = 67 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 125 12 2 = 9 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 125 12 3 = 19 :=
    slopeOrbit_step_eval 2 3 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 125 12 4 = 27 :=
    slopeOrbit_step_eval 3 2 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 125 12 5 = 91 :=
    slopeOrbit_step_eval 4 2 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 125 12 6 = 57 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 125 12 7 = 103 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 125 12 8 = 81 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 125 12 9 = 37 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 125 12 10 = 23 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 125 12 11 = 59 :=
    slopeOrbit_step_eval 10 2 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 125 12 12 = 111 :=
    slopeOrbit_step_eval 11 1 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 125 12 13 = 97 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 125 12 14 = 69 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 125 12 15 = 13 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 125 12 16 = 83 :=
    slopeOrbit_step_eval 15 3 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 125 12 17 = 41 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 125 12 18 = 39 :=
    slopeOrbit_step_eval 17 1 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 125 12 19 = 31 :=
    slopeOrbit_step_eval 18 1 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 125 12 20 = 123 :=
    slopeOrbit_step_eval 19 2 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 125 12 21 = 121 :=
    slopeOrbit_step_eval 20 0 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 125 12 22 = 117 :=
    slopeOrbit_step_eval 21 0 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 125 12 23 = 109 :=
    slopeOrbit_step_eval 22 0 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 125 12 24 = 93 :=
    slopeOrbit_step_eval 23 0 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 125 12 25 = 61 :=
    slopeOrbit_step_eval 24 0 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 125 12 26 = 119 :=
    slopeOrbit_step_eval 25 1 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 125 12 27 = 113 :=
    slopeOrbit_step_eval 26 0 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 125 12 28 = 101 :=
    slopeOrbit_step_eval 27 0 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 125 12 29 = 77 :=
    slopeOrbit_step_eval 28 0 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 125 12 30 = 29 :=
    slopeOrbit_step_eval 29 0 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : slopeOrbit 125 12 31 = 107 :=
    slopeOrbit_step_eval 30 2 e30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e32 : slopeOrbit 125 12 32 = 89 :=
    slopeOrbit_step_eval 31 0 e31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e33 : slopeOrbit 125 12 33 = 53 :=
    slopeOrbit_step_eval 32 0 e32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e34 : slopeOrbit 125 12 34 = 87 :=
    slopeOrbit_step_eval 33 1 e33 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e35 : slopeOrbit 125 12 35 = 49 :=
    slopeOrbit_step_eval 34 0 e34 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e36 : slopeOrbit 125 12 36 = 71 :=
    slopeOrbit_step_eval 35 1 e35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e37 : slopeOrbit 125 12 37 = 17 :=
    slopeOrbit_step_eval 36 0 e36 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e38 : slopeOrbit 125 12 38 = 11 :=
    slopeOrbit_step_eval 37 2 e37 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e39 : slopeOrbit 125 12 39 = 51 :=
    slopeOrbit_step_eval 38 3 e38 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e40 : slopeOrbit 125 12 40 = 79 :=
    slopeOrbit_step_eval 39 1 e39 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e41 : slopeOrbit 125 12 41 = 33 :=
    slopeOrbit_step_eval 40 0 e40 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e42 : slopeOrbit 125 12 42 = 7 :=
    slopeOrbit_step_eval 41 1 e41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e43 : slopeOrbit 125 12 43 = 99 :=
    slopeOrbit_step_eval 42 4 e42 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e44 : slopeOrbit 125 12 44 = 73 :=
    slopeOrbit_step_eval 43 0 e43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e45 : slopeOrbit 125 12 45 = 21 :=
    slopeOrbit_step_eval 44 0 e44 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e46 : slopeOrbit 125 12 46 = 43 :=
    slopeOrbit_step_eval 45 2 e45 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e47 : slopeOrbit 125 12 47 = 47 :=
    slopeOrbit_step_eval 46 1 e46 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e48 : slopeOrbit 125 12 48 = 63 :=
    slopeOrbit_step_eval 47 1 e47 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e49 : slopeOrbit 125 12 49 = 1 :=
    slopeOrbit_step_eval 48 0 e48 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e50 : slopeOrbit 125 12 50 = 3 :=
    slopeOrbit_step_eval 49 6 e49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e51 : slopeOrbit 125 12 51 = 67 :=
    slopeOrbit_step_eval 50 5 e50 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 125 12 51 = slopeOrbit 125 12 1
    rw [e51, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e26] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e27] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e28] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e29] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e30] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e31] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e32] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e33] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e34] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e35] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e36] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e37] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e39] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e40] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e41] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e42] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e43] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e44] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e45] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e46] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e47] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e48] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e49] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e50] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(125,12)`: the certified class-1 count cap `|fibre_1| <= 3 * ceil(W/50)`. -/
theorem sreClass1Count_of_datum_125_12 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 125) (hK : (class1SlopeDatum ctx).K₀ = 12) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 3 * (((supportShell ctx.shell.d ctx.shell.X).card + 50 - 1) / 50) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 50)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_125_12.1
  have hcount : (class1Band4CycleBand ctx 50).card ≤ 3 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_125_12.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 50).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 50 - 1) / 50) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 3 * (((supportShell ctx.shell.d ctx.shell.X).card + 50 - 1) / 50) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(125,62)`: period `50`, cycle `[123, 121, 117, 109, 93, 61, 119, 113, 101, 77, 29, 107, 89, 53, 87, 49, 71, 17, 11, 51, 79, 33, 7, 99, 73, 21, 43, 47, 63, 1, 3, 67, 9, 19, 27, 91, 57, 103, 81, 37, 23, 59, 111, 97, 69, 13, 83, 41, 39, 31]`, bands `[1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 2, 5, 1, 1, 3, 2, 2, 1, 7, 6, 1, 4, 3, 3, 1, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 2, 2, 3]` - band-4 residue set `{19, 33, 46}` (values `11, 9, 13`), `b4 = 3`. -/
private theorem sreCert_125_62 :
    slopeOrbit 125 62 (1 + 50) = slopeOrbit 125 62 1
      ∧ ∀ j, 1 ≤ j → j ≤ 50 →
          canonGap 125 (slopeOrbit 125 62 j) = 4 → j ∈ ({19, 33, 46} : Finset ℕ) := by
  have e0 : slopeOrbit 125 62 0 = 62 := rfl
  have e1 : slopeOrbit 125 62 1 = 123 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 125 62 2 = 121 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 125 62 3 = 117 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 125 62 4 = 109 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 125 62 5 = 93 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 125 62 6 = 61 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 125 62 7 = 119 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 125 62 8 = 113 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 125 62 9 = 101 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 125 62 10 = 77 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 125 62 11 = 29 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 125 62 12 = 107 :=
    slopeOrbit_step_eval 11 2 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 125 62 13 = 89 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 125 62 14 = 53 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 125 62 15 = 87 :=
    slopeOrbit_step_eval 14 1 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 125 62 16 = 49 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 125 62 17 = 71 :=
    slopeOrbit_step_eval 16 1 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 125 62 18 = 17 :=
    slopeOrbit_step_eval 17 0 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 125 62 19 = 11 :=
    slopeOrbit_step_eval 18 2 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 125 62 20 = 51 :=
    slopeOrbit_step_eval 19 3 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 125 62 21 = 79 :=
    slopeOrbit_step_eval 20 1 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 125 62 22 = 33 :=
    slopeOrbit_step_eval 21 0 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 125 62 23 = 7 :=
    slopeOrbit_step_eval 22 1 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 125 62 24 = 99 :=
    slopeOrbit_step_eval 23 4 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 125 62 25 = 73 :=
    slopeOrbit_step_eval 24 0 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 125 62 26 = 21 :=
    slopeOrbit_step_eval 25 0 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 125 62 27 = 43 :=
    slopeOrbit_step_eval 26 2 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 125 62 28 = 47 :=
    slopeOrbit_step_eval 27 1 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 125 62 29 = 63 :=
    slopeOrbit_step_eval 28 1 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 125 62 30 = 1 :=
    slopeOrbit_step_eval 29 0 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : slopeOrbit 125 62 31 = 3 :=
    slopeOrbit_step_eval 30 6 e30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e32 : slopeOrbit 125 62 32 = 67 :=
    slopeOrbit_step_eval 31 5 e31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e33 : slopeOrbit 125 62 33 = 9 :=
    slopeOrbit_step_eval 32 0 e32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e34 : slopeOrbit 125 62 34 = 19 :=
    slopeOrbit_step_eval 33 3 e33 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e35 : slopeOrbit 125 62 35 = 27 :=
    slopeOrbit_step_eval 34 2 e34 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e36 : slopeOrbit 125 62 36 = 91 :=
    slopeOrbit_step_eval 35 2 e35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e37 : slopeOrbit 125 62 37 = 57 :=
    slopeOrbit_step_eval 36 0 e36 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e38 : slopeOrbit 125 62 38 = 103 :=
    slopeOrbit_step_eval 37 1 e37 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e39 : slopeOrbit 125 62 39 = 81 :=
    slopeOrbit_step_eval 38 0 e38 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e40 : slopeOrbit 125 62 40 = 37 :=
    slopeOrbit_step_eval 39 0 e39 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e41 : slopeOrbit 125 62 41 = 23 :=
    slopeOrbit_step_eval 40 1 e40 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e42 : slopeOrbit 125 62 42 = 59 :=
    slopeOrbit_step_eval 41 2 e41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e43 : slopeOrbit 125 62 43 = 111 :=
    slopeOrbit_step_eval 42 1 e42 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e44 : slopeOrbit 125 62 44 = 97 :=
    slopeOrbit_step_eval 43 0 e43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e45 : slopeOrbit 125 62 45 = 69 :=
    slopeOrbit_step_eval 44 0 e44 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e46 : slopeOrbit 125 62 46 = 13 :=
    slopeOrbit_step_eval 45 0 e45 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e47 : slopeOrbit 125 62 47 = 83 :=
    slopeOrbit_step_eval 46 3 e46 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e48 : slopeOrbit 125 62 48 = 41 :=
    slopeOrbit_step_eval 47 0 e47 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e49 : slopeOrbit 125 62 49 = 39 :=
    slopeOrbit_step_eval 48 1 e48 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e50 : slopeOrbit 125 62 50 = 31 :=
    slopeOrbit_step_eval 49 1 e49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e51 : slopeOrbit 125 62 51 = 123 :=
    slopeOrbit_step_eval 50 2 e50 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 125 62 51 = slopeOrbit 125 62 1
    rw [e51, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e26] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e27] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e28] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e29] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e30] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e31] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e32] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e34] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e35] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e36] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e37] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e38] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e39] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e40] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e41] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e42] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e43] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e44] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e45] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e47] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e48] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e49] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e50] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))

/-- `(125,62)`: the certified class-1 count cap `|fibre_1| <= 3 * ceil(W/50)`. -/
theorem sreClass1Count_of_datum_125_62 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 125) (hK : (class1SlopeDatum ctx).K₀ = 62) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 3 * (((supportShell ctx.shell.d ctx.shell.X).card + 50 - 1) / 50) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 50)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_125_62.1
  have hcount : (class1Band4CycleBand ctx 50).card ≤ 3 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_125_62.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 50).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 50 - 1) / 50) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 3 * (((supportShell ctx.shell.d ctx.shell.X).card + 50 - 1) / 50) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(131,65)`: period `65`, cycle `[129, 127, 123, 115, 99, 67, 3, 61, 113, 95, 59, 105, 79, 27, 85, 39, 25, 69, 7, 93, 55, 89, 47, 57, 97, 63, 121, 111, 91, 51, 73, 15, 109, 87, 43, 41, 33, 1, 125, 119, 107, 83, 35, 9, 13, 77, 23, 53, 81, 31, 117, 103, 75, 19, 21, 37, 17, 5, 29, 101, 71, 11, 45, 49, 65]`, bands `[1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 5, 1, 2, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 8, 1, 1, 1, 1, 2, 4, 4, 1, 3, 2, 1, 3, 1, 1, 1, 3, 3, 2, 3, 5, 3, 1, 1, 4, 2, 2, 2]` - band-4 residue set `{32, 44, 45, 62}` (values `15, 9, 13, 11`), `b4 = 4`. -/
private theorem sreCert_131_65 :
    slopeOrbit 131 65 (1 + 65) = slopeOrbit 131 65 1
      ∧ ∀ j, 1 ≤ j → j ≤ 65 →
          canonGap 131 (slopeOrbit 131 65 j) = 4 → j ∈ ({32, 44, 45, 62} : Finset ℕ) := by
  have e0 : slopeOrbit 131 65 0 = 65 := rfl
  have e1 : slopeOrbit 131 65 1 = 129 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 131 65 2 = 127 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 131 65 3 = 123 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 131 65 4 = 115 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 131 65 5 = 99 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 131 65 6 = 67 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 131 65 7 = 3 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 131 65 8 = 61 :=
    slopeOrbit_step_eval 7 5 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 131 65 9 = 113 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 131 65 10 = 95 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 131 65 11 = 59 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 131 65 12 = 105 :=
    slopeOrbit_step_eval 11 1 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 131 65 13 = 79 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 131 65 14 = 27 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 131 65 15 = 85 :=
    slopeOrbit_step_eval 14 2 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 131 65 16 = 39 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 131 65 17 = 25 :=
    slopeOrbit_step_eval 16 1 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 131 65 18 = 69 :=
    slopeOrbit_step_eval 17 2 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 131 65 19 = 7 :=
    slopeOrbit_step_eval 18 0 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 131 65 20 = 93 :=
    slopeOrbit_step_eval 19 4 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 131 65 21 = 55 :=
    slopeOrbit_step_eval 20 0 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 131 65 22 = 89 :=
    slopeOrbit_step_eval 21 1 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 131 65 23 = 47 :=
    slopeOrbit_step_eval 22 0 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 131 65 24 = 57 :=
    slopeOrbit_step_eval 23 1 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 131 65 25 = 97 :=
    slopeOrbit_step_eval 24 1 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 131 65 26 = 63 :=
    slopeOrbit_step_eval 25 0 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 131 65 27 = 121 :=
    slopeOrbit_step_eval 26 1 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 131 65 28 = 111 :=
    slopeOrbit_step_eval 27 0 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 131 65 29 = 91 :=
    slopeOrbit_step_eval 28 0 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 131 65 30 = 51 :=
    slopeOrbit_step_eval 29 0 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : slopeOrbit 131 65 31 = 73 :=
    slopeOrbit_step_eval 30 1 e30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e32 : slopeOrbit 131 65 32 = 15 :=
    slopeOrbit_step_eval 31 0 e31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e33 : slopeOrbit 131 65 33 = 109 :=
    slopeOrbit_step_eval 32 3 e32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e34 : slopeOrbit 131 65 34 = 87 :=
    slopeOrbit_step_eval 33 0 e33 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e35 : slopeOrbit 131 65 35 = 43 :=
    slopeOrbit_step_eval 34 0 e34 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e36 : slopeOrbit 131 65 36 = 41 :=
    slopeOrbit_step_eval 35 1 e35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e37 : slopeOrbit 131 65 37 = 33 :=
    slopeOrbit_step_eval 36 1 e36 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e38 : slopeOrbit 131 65 38 = 1 :=
    slopeOrbit_step_eval 37 1 e37 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e39 : slopeOrbit 131 65 39 = 125 :=
    slopeOrbit_step_eval 38 7 e38 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e40 : slopeOrbit 131 65 40 = 119 :=
    slopeOrbit_step_eval 39 0 e39 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e41 : slopeOrbit 131 65 41 = 107 :=
    slopeOrbit_step_eval 40 0 e40 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e42 : slopeOrbit 131 65 42 = 83 :=
    slopeOrbit_step_eval 41 0 e41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e43 : slopeOrbit 131 65 43 = 35 :=
    slopeOrbit_step_eval 42 0 e42 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e44 : slopeOrbit 131 65 44 = 9 :=
    slopeOrbit_step_eval 43 1 e43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e45 : slopeOrbit 131 65 45 = 13 :=
    slopeOrbit_step_eval 44 3 e44 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e46 : slopeOrbit 131 65 46 = 77 :=
    slopeOrbit_step_eval 45 3 e45 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e47 : slopeOrbit 131 65 47 = 23 :=
    slopeOrbit_step_eval 46 0 e46 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e48 : slopeOrbit 131 65 48 = 53 :=
    slopeOrbit_step_eval 47 2 e47 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e49 : slopeOrbit 131 65 49 = 81 :=
    slopeOrbit_step_eval 48 1 e48 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e50 : slopeOrbit 131 65 50 = 31 :=
    slopeOrbit_step_eval 49 0 e49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e51 : slopeOrbit 131 65 51 = 117 :=
    slopeOrbit_step_eval 50 2 e50 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e52 : slopeOrbit 131 65 52 = 103 :=
    slopeOrbit_step_eval 51 0 e51 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e53 : slopeOrbit 131 65 53 = 75 :=
    slopeOrbit_step_eval 52 0 e52 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e54 : slopeOrbit 131 65 54 = 19 :=
    slopeOrbit_step_eval 53 0 e53 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e55 : slopeOrbit 131 65 55 = 21 :=
    slopeOrbit_step_eval 54 2 e54 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e56 : slopeOrbit 131 65 56 = 37 :=
    slopeOrbit_step_eval 55 2 e55 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e57 : slopeOrbit 131 65 57 = 17 :=
    slopeOrbit_step_eval 56 1 e56 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e58 : slopeOrbit 131 65 58 = 5 :=
    slopeOrbit_step_eval 57 2 e57 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e59 : slopeOrbit 131 65 59 = 29 :=
    slopeOrbit_step_eval 58 4 e58 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e60 : slopeOrbit 131 65 60 = 101 :=
    slopeOrbit_step_eval 59 2 e59 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e61 : slopeOrbit 131 65 61 = 71 :=
    slopeOrbit_step_eval 60 0 e60 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e62 : slopeOrbit 131 65 62 = 11 :=
    slopeOrbit_step_eval 61 0 e61 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e63 : slopeOrbit 131 65 63 = 45 :=
    slopeOrbit_step_eval 62 3 e62 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e64 : slopeOrbit 131 65 64 = 49 :=
    slopeOrbit_step_eval 63 1 e63 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e65 : slopeOrbit 131 65 65 = 65 :=
    slopeOrbit_step_eval 64 1 e64 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e66 : slopeOrbit 131 65 66 = 129 :=
    slopeOrbit_step_eval 65 1 e65 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 131 65 66 = slopeOrbit 131 65 1
    rw [e66, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e26] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e27] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e28] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e29] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e30] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e31] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e33] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e34] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e35] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e36] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e37] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e38] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e39] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e40] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e41] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e42] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e43] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · decide
    · rw [e46] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e47] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e48] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e49] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e50] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e51] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e52] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e53] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e54] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e55] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e56] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e57] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e58] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e59] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e60] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e61] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e63] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e64] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e65] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))

/-- `(131,65)`: the certified class-1 count cap `|fibre_1| <= 4 * ceil(W/65)`. -/
theorem sreClass1Count_of_datum_131_65 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 131) (hK : (class1SlopeDatum ctx).K₀ = 65) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 4 * (((supportShell ctx.shell.d ctx.shell.X).card + 65 - 1) / 65) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 65)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_131_65.1
  have hcount : (class1Band4CycleBand ctx 65).card ≤ 4 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_131_65.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 65).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 65 - 1) / 65) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 4 * (((supportShell ctx.shell.d ctx.shell.X).card + 65 - 1) / 65) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(133,3)`: period `7`, cycle `[59, 103, 73, 13, 75, 17, 3]`, bands `[2, 1, 1, 4, 1, 3, 6]` - band-4 residue set `{4}` (values `13`), `b4 = 1`. -/
private theorem sreCert_133_3 :
    slopeOrbit 133 3 (1 + 7) = slopeOrbit 133 3 1
      ∧ ∀ j, 1 ≤ j → j ≤ 7 →
          canonGap 133 (slopeOrbit 133 3 j) = 4 → j ∈ ({4} : Finset ℕ) := by
  have e0 : slopeOrbit 133 3 0 = 3 := rfl
  have e1 : slopeOrbit 133 3 1 = 59 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 133 3 2 = 103 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 133 3 3 = 73 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 133 3 4 = 13 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 133 3 5 = 75 :=
    slopeOrbit_step_eval 4 3 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 133 3 6 = 17 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 133 3 7 = 3 :=
    slopeOrbit_step_eval 6 2 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 133 3 8 = 59 :=
    slopeOrbit_step_eval 7 5 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 133 3 8 = slopeOrbit 133 3 1
    rw [e8, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(133,3)`: the certified class-1 count cap `|fibre_1| <= 1 * ceil(W/7)`. -/
theorem sreClass1Count_of_datum_133_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 133) (hK : (class1SlopeDatum ctx).K₀ = 3) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 7 - 1) / 7) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 7)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_133_3.1
  have hcount : (class1Band4CycleBand ctx 7).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_133_3.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 7).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 7 - 1) / 7) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 7 - 1) / 7) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(133,9)`: period `7`, cycle `[11, 43, 39, 23, 51, 71, 9]`, bands `[4, 2, 2, 3, 2, 1, 4]` - band-4 residue set `{1, 7}` (values `11, 9`), `b4 = 2`. -/
private theorem sreCert_133_9 :
    slopeOrbit 133 9 (1 + 7) = slopeOrbit 133 9 1
      ∧ ∀ j, 1 ≤ j → j ≤ 7 →
          canonGap 133 (slopeOrbit 133 9 j) = 4 → j ∈ ({1, 7} : Finset ℕ) := by
  have e0 : slopeOrbit 133 9 0 = 9 := rfl
  have e1 : slopeOrbit 133 9 1 = 11 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 133 9 2 = 43 :=
    slopeOrbit_step_eval 1 3 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 133 9 3 = 39 :=
    slopeOrbit_step_eval 2 1 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 133 9 4 = 23 :=
    slopeOrbit_step_eval 3 1 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 133 9 5 = 51 :=
    slopeOrbit_step_eval 4 2 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 133 9 6 = 71 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 133 9 7 = 9 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 133 9 8 = 11 :=
    slopeOrbit_step_eval 7 3 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 133 9 8 = slopeOrbit 133 9 1
    rw [e8, e1]
  · intro j h1 h2 hband
    interval_cases j
    · decide
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide

/-- `(133,9)`: the certified class-1 count cap `|fibre_1| <= 2 * ceil(W/7)`. -/
theorem sreClass1Count_of_datum_133_9 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 133) (hK : (class1SlopeDatum ctx).K₀ = 9) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 7 - 1) / 7) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 7)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_133_9.1
  have hcount : (class1Band4CycleBand ctx 7).card ≤ 2 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_133_9.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 7).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 7 - 1) / 7) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 7 - 1) / 7) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(135,7)`: period `19`, cycle `[89, 43, 37, 13, 73, 11, 41, 29, 97, 59, 101, 67, 133, 131, 127, 119, 103, 71, 7]`, bands `[1, 2, 2, 4, 1, 4, 2, 3, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 5]` - band-4 residue set `{4, 6}` (values `13, 11`), `b4 = 2`. -/
private theorem sreCert_135_7 :
    slopeOrbit 135 7 (1 + 19) = slopeOrbit 135 7 1
      ∧ ∀ j, 1 ≤ j → j ≤ 19 →
          canonGap 135 (slopeOrbit 135 7 j) = 4 → j ∈ ({4, 6} : Finset ℕ) := by
  have e0 : slopeOrbit 135 7 0 = 7 := rfl
  have e1 : slopeOrbit 135 7 1 = 89 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 135 7 2 = 43 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 135 7 3 = 37 :=
    slopeOrbit_step_eval 2 1 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 135 7 4 = 13 :=
    slopeOrbit_step_eval 3 1 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 135 7 5 = 73 :=
    slopeOrbit_step_eval 4 3 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 135 7 6 = 11 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 135 7 7 = 41 :=
    slopeOrbit_step_eval 6 3 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 135 7 8 = 29 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 135 7 9 = 97 :=
    slopeOrbit_step_eval 8 2 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 135 7 10 = 59 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 135 7 11 = 101 :=
    slopeOrbit_step_eval 10 1 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 135 7 12 = 67 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 135 7 13 = 133 :=
    slopeOrbit_step_eval 12 1 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 135 7 14 = 131 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 135 7 15 = 127 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 135 7 16 = 119 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 135 7 17 = 103 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 135 7 18 = 71 :=
    slopeOrbit_step_eval 17 0 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 135 7 19 = 7 :=
    slopeOrbit_step_eval 18 0 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 135 7 20 = 89 :=
    slopeOrbit_step_eval 19 4 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 135 7 20 = slopeOrbit 135 7 1
    rw [e20, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(135,7)`: the certified class-1 count cap `|fibre_1| <= 2 * ceil(W/19)`. -/
theorem sreClass1Count_of_datum_135_7 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 135) (hK : (class1SlopeDatum ctx).K₀ = 7) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 19 - 1) / 19) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 19)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_135_7.1
  have hcount : (class1Band4CycleBand ctx 19).card ≤ 2 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_135_7.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 19).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 19 - 1) / 19) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 19 - 1) / 19) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(135,13)`: period `19`, cycle `[73, 11, 41, 29, 97, 59, 101, 67, 133, 131, 127, 119, 103, 71, 7, 89, 43, 37, 13]`, bands `[1, 4, 2, 3, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 4]` - band-4 residue set `{2, 19}` (values `11, 13`), `b4 = 2`. -/
private theorem sreCert_135_13 :
    slopeOrbit 135 13 (1 + 19) = slopeOrbit 135 13 1
      ∧ ∀ j, 1 ≤ j → j ≤ 19 →
          canonGap 135 (slopeOrbit 135 13 j) = 4 → j ∈ ({2, 19} : Finset ℕ) := by
  have e0 : slopeOrbit 135 13 0 = 13 := rfl
  have e1 : slopeOrbit 135 13 1 = 73 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 135 13 2 = 11 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 135 13 3 = 41 :=
    slopeOrbit_step_eval 2 3 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 135 13 4 = 29 :=
    slopeOrbit_step_eval 3 1 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 135 13 5 = 97 :=
    slopeOrbit_step_eval 4 2 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 135 13 6 = 59 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 135 13 7 = 101 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 135 13 8 = 67 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 135 13 9 = 133 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 135 13 10 = 131 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 135 13 11 = 127 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 135 13 12 = 119 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 135 13 13 = 103 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 135 13 14 = 71 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 135 13 15 = 7 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 135 13 16 = 89 :=
    slopeOrbit_step_eval 15 4 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 135 13 17 = 43 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 135 13 18 = 37 :=
    slopeOrbit_step_eval 17 1 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 135 13 19 = 13 :=
    slopeOrbit_step_eval 18 1 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 135 13 20 = 73 :=
    slopeOrbit_step_eval 19 3 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 135 13 20 = slopeOrbit 135 13 1
    rw [e20, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide

/-- `(135,13)`: the certified class-1 count cap `|fibre_1| <= 2 * ceil(W/19)`. -/
theorem sreClass1Count_of_datum_135_13 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 135) (hK : (class1SlopeDatum ctx).K₀ = 13) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 19 - 1) / 19) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 19)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_135_13.1
  have hcount : (class1Band4CycleBand ctx 19).card ≤ 2 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_135_13.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 19).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 19 - 1) / 19) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 19 - 1) / 19) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(135,22)`: period `19`, cycle `[41, 29, 97, 59, 101, 67, 133, 131, 127, 119, 103, 71, 7, 89, 43, 37, 13, 73, 11]`, bands `[2, 3, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 4, 1, 4]` - band-4 residue set `{17, 19}` (values `13, 11`), `b4 = 2`. -/
private theorem sreCert_135_22 :
    slopeOrbit 135 22 (1 + 19) = slopeOrbit 135 22 1
      ∧ ∀ j, 1 ≤ j → j ≤ 19 →
          canonGap 135 (slopeOrbit 135 22 j) = 4 → j ∈ ({17, 19} : Finset ℕ) := by
  have e0 : slopeOrbit 135 22 0 = 22 := rfl
  have e1 : slopeOrbit 135 22 1 = 41 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 135 22 2 = 29 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 135 22 3 = 97 :=
    slopeOrbit_step_eval 2 2 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 135 22 4 = 59 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 135 22 5 = 101 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 135 22 6 = 67 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 135 22 7 = 133 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 135 22 8 = 131 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 135 22 9 = 127 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 135 22 10 = 119 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 135 22 11 = 103 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 135 22 12 = 71 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 135 22 13 = 7 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 135 22 14 = 89 :=
    slopeOrbit_step_eval 13 4 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 135 22 15 = 43 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 135 22 16 = 37 :=
    slopeOrbit_step_eval 15 1 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 135 22 17 = 13 :=
    slopeOrbit_step_eval 16 1 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 135 22 18 = 73 :=
    slopeOrbit_step_eval 17 3 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 135 22 19 = 11 :=
    slopeOrbit_step_eval 18 0 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 135 22 20 = 41 :=
    slopeOrbit_step_eval 19 3 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 135 22 20 = slopeOrbit 135 22 1
    rw [e20, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide

/-- `(135,22)`: the certified class-1 count cap `|fibre_1| <= 2 * ceil(W/19)`. -/
theorem sreClass1Count_of_datum_135_22 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 135) (hK : (class1SlopeDatum ctx).K₀ = 22) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 19 - 1) / 19) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 19)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_135_22.1
  have hcount : (class1Band4CycleBand ctx 19).card ≤ 2 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_135_22.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 19).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 19 - 1) / 19) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 19 - 1) / 19) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(135,67)`: period `19`, cycle `[133, 131, 127, 119, 103, 71, 7, 89, 43, 37, 13, 73, 11, 41, 29, 97, 59, 101, 67]`, bands `[1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 4, 1, 4, 2, 3, 1, 2, 1, 2]` - band-4 residue set `{11, 13}` (values `13, 11`), `b4 = 2`. -/
private theorem sreCert_135_67 :
    slopeOrbit 135 67 (1 + 19) = slopeOrbit 135 67 1
      ∧ ∀ j, 1 ≤ j → j ≤ 19 →
          canonGap 135 (slopeOrbit 135 67 j) = 4 → j ∈ ({11, 13} : Finset ℕ) := by
  have e0 : slopeOrbit 135 67 0 = 67 := rfl
  have e1 : slopeOrbit 135 67 1 = 133 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 135 67 2 = 131 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 135 67 3 = 127 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 135 67 4 = 119 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 135 67 5 = 103 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 135 67 6 = 71 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 135 67 7 = 7 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 135 67 8 = 89 :=
    slopeOrbit_step_eval 7 4 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 135 67 9 = 43 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 135 67 10 = 37 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 135 67 11 = 13 :=
    slopeOrbit_step_eval 10 1 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 135 67 12 = 73 :=
    slopeOrbit_step_eval 11 3 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 135 67 13 = 11 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 135 67 14 = 41 :=
    slopeOrbit_step_eval 13 3 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 135 67 15 = 29 :=
    slopeOrbit_step_eval 14 1 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 135 67 16 = 97 :=
    slopeOrbit_step_eval 15 2 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 135 67 17 = 59 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 135 67 18 = 101 :=
    slopeOrbit_step_eval 17 1 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 135 67 19 = 67 :=
    slopeOrbit_step_eval 18 0 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 135 67 20 = 133 :=
    slopeOrbit_step_eval 19 1 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 135 67 20 = slopeOrbit 135 67 1
    rw [e20, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))

/-- `(135,67)`: the certified class-1 count cap `|fibre_1| <= 2 * ceil(W/19)`. -/
theorem sreClass1Count_of_datum_135_67 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 135) (hK : (class1SlopeDatum ctx).K₀ = 67) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 19 - 1) / 19) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 19)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_135_67.1
  have hcount : (class1Band4CycleBand ctx 19).card ≤ 2 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_135_67.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 19).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 19 - 1) / 19) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 19 - 1) / 19) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(137,68)`: period `34`, cycle `[135, 133, 129, 121, 105, 73, 9, 7, 87, 37, 11, 39, 19, 15, 103, 69, 1, 119, 101, 65, 123, 109, 81, 25, 63, 115, 93, 49, 59, 99, 61, 107, 77, 17]`, bands `[1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 4, 2, 3, 4, 1, 1, 8, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4]` - band-4 residue set `{7, 11, 14, 34}` (values `9, 11, 15, 17`), `b4 = 4`. -/
private theorem sreCert_137_68 :
    slopeOrbit 137 68 (1 + 34) = slopeOrbit 137 68 1
      ∧ ∀ j, 1 ≤ j → j ≤ 34 →
          canonGap 137 (slopeOrbit 137 68 j) = 4 → j ∈ ({7, 11, 14, 34} : Finset ℕ) := by
  have e0 : slopeOrbit 137 68 0 = 68 := rfl
  have e1 : slopeOrbit 137 68 1 = 135 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 137 68 2 = 133 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 137 68 3 = 129 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 137 68 4 = 121 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 137 68 5 = 105 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 137 68 6 = 73 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 137 68 7 = 9 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 137 68 8 = 7 :=
    slopeOrbit_step_eval 7 3 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 137 68 9 = 87 :=
    slopeOrbit_step_eval 8 4 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 137 68 10 = 37 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 137 68 11 = 11 :=
    slopeOrbit_step_eval 10 1 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 137 68 12 = 39 :=
    slopeOrbit_step_eval 11 3 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 137 68 13 = 19 :=
    slopeOrbit_step_eval 12 1 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 137 68 14 = 15 :=
    slopeOrbit_step_eval 13 2 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 137 68 15 = 103 :=
    slopeOrbit_step_eval 14 3 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 137 68 16 = 69 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 137 68 17 = 1 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 137 68 18 = 119 :=
    slopeOrbit_step_eval 17 7 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 137 68 19 = 101 :=
    slopeOrbit_step_eval 18 0 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 137 68 20 = 65 :=
    slopeOrbit_step_eval 19 0 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 137 68 21 = 123 :=
    slopeOrbit_step_eval 20 1 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 137 68 22 = 109 :=
    slopeOrbit_step_eval 21 0 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 137 68 23 = 81 :=
    slopeOrbit_step_eval 22 0 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 137 68 24 = 25 :=
    slopeOrbit_step_eval 23 0 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 137 68 25 = 63 :=
    slopeOrbit_step_eval 24 2 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 137 68 26 = 115 :=
    slopeOrbit_step_eval 25 1 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 137 68 27 = 93 :=
    slopeOrbit_step_eval 26 0 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 137 68 28 = 49 :=
    slopeOrbit_step_eval 27 0 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 137 68 29 = 59 :=
    slopeOrbit_step_eval 28 1 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 137 68 30 = 99 :=
    slopeOrbit_step_eval 29 1 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : slopeOrbit 137 68 31 = 61 :=
    slopeOrbit_step_eval 30 0 e30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e32 : slopeOrbit 137 68 32 = 107 :=
    slopeOrbit_step_eval 31 1 e31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e33 : slopeOrbit 137 68 33 = 77 :=
    slopeOrbit_step_eval 32 0 e32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e34 : slopeOrbit 137 68 34 = 17 :=
    slopeOrbit_step_eval 33 0 e33 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e35 : slopeOrbit 137 68 35 = 135 :=
    slopeOrbit_step_eval 34 3 e34 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 137 68 35 = slopeOrbit 137 68 1
    rw [e35, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e26] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e27] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e28] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e29] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e30] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e31] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e32] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e33] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide

/-- `(137,68)`: the certified class-1 count cap `|fibre_1| <= 4 * ceil(W/34)`. -/
theorem sreClass1Count_of_datum_137_68 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 137) (hK : (class1SlopeDatum ctx).K₀ = 68) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 4 * (((supportShell ctx.shell.d ctx.shell.X).card + 34 - 1) / 34) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 34)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_137_68.1
  have hcount : (class1Band4CycleBand ctx 34).card ≤ 4 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_137_68.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 34).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 34 - 1) / 34) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 4 * (((supportShell ctx.shell.d ctx.shell.X).card + 34 - 1) / 34) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(139,69)`: period `69`, cycle `[137, 135, 131, 123, 107, 75, 11, 37, 9, 5, 21, 29, 93, 47, 49, 57, 89, 39, 17, 133, 127, 115, 91, 43, 33, 125, 111, 83, 27, 77, 15, 101, 63, 113, 87, 35, 1, 117, 95, 51, 65, 121, 103, 67, 129, 119, 99, 59, 97, 55, 81, 23, 45, 41, 25, 61, 105, 71, 3, 53, 73, 7, 85, 31, 109, 79, 19, 13, 69]`, bands `[1, 1, 1, 1, 1, 1, 4, 2, 4, 5, 3, 3, 1, 2, 2, 2, 1, 2, 4, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 8, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 2, 1, 1, 6, 2, 1, 5, 1, 3, 1, 1, 3, 4, 2]` - band-4 residue set `{7, 9, 19, 31, 68}` (values `11, 9, 17, 15, 13`), `b4 = 5`. -/
private theorem sreCert_139_69 :
    slopeOrbit 139 69 (1 + 69) = slopeOrbit 139 69 1
      ∧ ∀ j, 1 ≤ j → j ≤ 69 →
          canonGap 139 (slopeOrbit 139 69 j) = 4 → j ∈ ({7, 9, 19, 31, 68} : Finset ℕ) := by
  have e0 : slopeOrbit 139 69 0 = 69 := rfl
  have e1 : slopeOrbit 139 69 1 = 137 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 139 69 2 = 135 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 139 69 3 = 131 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 139 69 4 = 123 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 139 69 5 = 107 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 139 69 6 = 75 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 139 69 7 = 11 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 139 69 8 = 37 :=
    slopeOrbit_step_eval 7 3 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 139 69 9 = 9 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 139 69 10 = 5 :=
    slopeOrbit_step_eval 9 3 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 139 69 11 = 21 :=
    slopeOrbit_step_eval 10 4 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 139 69 12 = 29 :=
    slopeOrbit_step_eval 11 2 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 139 69 13 = 93 :=
    slopeOrbit_step_eval 12 2 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 139 69 14 = 47 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 139 69 15 = 49 :=
    slopeOrbit_step_eval 14 1 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 139 69 16 = 57 :=
    slopeOrbit_step_eval 15 1 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 139 69 17 = 89 :=
    slopeOrbit_step_eval 16 1 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 139 69 18 = 39 :=
    slopeOrbit_step_eval 17 0 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 139 69 19 = 17 :=
    slopeOrbit_step_eval 18 1 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 139 69 20 = 133 :=
    slopeOrbit_step_eval 19 3 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 139 69 21 = 127 :=
    slopeOrbit_step_eval 20 0 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 139 69 22 = 115 :=
    slopeOrbit_step_eval 21 0 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 139 69 23 = 91 :=
    slopeOrbit_step_eval 22 0 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 139 69 24 = 43 :=
    slopeOrbit_step_eval 23 0 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 139 69 25 = 33 :=
    slopeOrbit_step_eval 24 1 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 139 69 26 = 125 :=
    slopeOrbit_step_eval 25 2 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 139 69 27 = 111 :=
    slopeOrbit_step_eval 26 0 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 139 69 28 = 83 :=
    slopeOrbit_step_eval 27 0 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 139 69 29 = 27 :=
    slopeOrbit_step_eval 28 0 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 139 69 30 = 77 :=
    slopeOrbit_step_eval 29 2 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : slopeOrbit 139 69 31 = 15 :=
    slopeOrbit_step_eval 30 0 e30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e32 : slopeOrbit 139 69 32 = 101 :=
    slopeOrbit_step_eval 31 3 e31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e33 : slopeOrbit 139 69 33 = 63 :=
    slopeOrbit_step_eval 32 0 e32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e34 : slopeOrbit 139 69 34 = 113 :=
    slopeOrbit_step_eval 33 1 e33 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e35 : slopeOrbit 139 69 35 = 87 :=
    slopeOrbit_step_eval 34 0 e34 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e36 : slopeOrbit 139 69 36 = 35 :=
    slopeOrbit_step_eval 35 0 e35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e37 : slopeOrbit 139 69 37 = 1 :=
    slopeOrbit_step_eval 36 1 e36 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e38 : slopeOrbit 139 69 38 = 117 :=
    slopeOrbit_step_eval 37 7 e37 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e39 : slopeOrbit 139 69 39 = 95 :=
    slopeOrbit_step_eval 38 0 e38 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e40 : slopeOrbit 139 69 40 = 51 :=
    slopeOrbit_step_eval 39 0 e39 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e41 : slopeOrbit 139 69 41 = 65 :=
    slopeOrbit_step_eval 40 1 e40 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e42 : slopeOrbit 139 69 42 = 121 :=
    slopeOrbit_step_eval 41 1 e41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e43 : slopeOrbit 139 69 43 = 103 :=
    slopeOrbit_step_eval 42 0 e42 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e44 : slopeOrbit 139 69 44 = 67 :=
    slopeOrbit_step_eval 43 0 e43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e45 : slopeOrbit 139 69 45 = 129 :=
    slopeOrbit_step_eval 44 1 e44 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e46 : slopeOrbit 139 69 46 = 119 :=
    slopeOrbit_step_eval 45 0 e45 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e47 : slopeOrbit 139 69 47 = 99 :=
    slopeOrbit_step_eval 46 0 e46 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e48 : slopeOrbit 139 69 48 = 59 :=
    slopeOrbit_step_eval 47 0 e47 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e49 : slopeOrbit 139 69 49 = 97 :=
    slopeOrbit_step_eval 48 1 e48 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e50 : slopeOrbit 139 69 50 = 55 :=
    slopeOrbit_step_eval 49 0 e49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e51 : slopeOrbit 139 69 51 = 81 :=
    slopeOrbit_step_eval 50 1 e50 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e52 : slopeOrbit 139 69 52 = 23 :=
    slopeOrbit_step_eval 51 0 e51 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e53 : slopeOrbit 139 69 53 = 45 :=
    slopeOrbit_step_eval 52 2 e52 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e54 : slopeOrbit 139 69 54 = 41 :=
    slopeOrbit_step_eval 53 1 e53 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e55 : slopeOrbit 139 69 55 = 25 :=
    slopeOrbit_step_eval 54 1 e54 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e56 : slopeOrbit 139 69 56 = 61 :=
    slopeOrbit_step_eval 55 2 e55 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e57 : slopeOrbit 139 69 57 = 105 :=
    slopeOrbit_step_eval 56 1 e56 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e58 : slopeOrbit 139 69 58 = 71 :=
    slopeOrbit_step_eval 57 0 e57 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e59 : slopeOrbit 139 69 59 = 3 :=
    slopeOrbit_step_eval 58 0 e58 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e60 : slopeOrbit 139 69 60 = 53 :=
    slopeOrbit_step_eval 59 5 e59 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e61 : slopeOrbit 139 69 61 = 73 :=
    slopeOrbit_step_eval 60 1 e60 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e62 : slopeOrbit 139 69 62 = 7 :=
    slopeOrbit_step_eval 61 0 e61 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e63 : slopeOrbit 139 69 63 = 85 :=
    slopeOrbit_step_eval 62 4 e62 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e64 : slopeOrbit 139 69 64 = 31 :=
    slopeOrbit_step_eval 63 0 e63 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e65 : slopeOrbit 139 69 65 = 109 :=
    slopeOrbit_step_eval 64 2 e64 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e66 : slopeOrbit 139 69 66 = 79 :=
    slopeOrbit_step_eval 65 0 e65 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e67 : slopeOrbit 139 69 67 = 19 :=
    slopeOrbit_step_eval 66 0 e66 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e68 : slopeOrbit 139 69 68 = 13 :=
    slopeOrbit_step_eval 67 2 e67 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e69 : slopeOrbit 139 69 69 = 69 :=
    slopeOrbit_step_eval 68 3 e68 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e70 : slopeOrbit 139 69 70 = 137 :=
    slopeOrbit_step_eval 69 1 e69 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 139 69 70 = slopeOrbit 139 69 1
    rw [e70, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e26] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e27] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e28] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e29] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e30] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e32] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e33] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e34] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e35] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e36] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e37] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e38] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e39] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e40] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e41] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e42] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e43] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e44] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e45] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e46] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e47] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e48] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e49] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e50] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e51] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e52] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e53] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e54] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e55] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e56] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e57] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e58] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e59] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e60] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e61] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e62] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e63] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e64] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e65] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e66] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e67] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e69] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))

/-- `(139,69)`: the certified class-1 count cap `|fibre_1| <= 5 * ceil(W/69)`. -/
theorem sreClass1Count_of_datum_139_69 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 139) (hK : (class1SlopeDatum ctx).K₀ = 69) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 5 * (((supportShell ctx.shell.d ctx.shell.X).card + 69 - 1) / 69) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 69)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_139_69.1
  have hcount : (class1Band4CycleBand ctx 69).card ≤ 5 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_139_69.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 69).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 69 - 1) / 69) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 5 * (((supportShell ctx.shell.d ctx.shell.X).card + 69 - 1) / 69) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(141,1)`: period `23`, cycle `[115, 89, 37, 7, 83, 25, 59, 95, 49, 55, 79, 17, 131, 121, 101, 61, 103, 65, 119, 97, 53, 71, 1]`, bands `[1, 1, 2, 5, 1, 3, 2, 1, 2, 2, 1, 4, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 8]` - band-4 residue set `{12}` (values `17`), `b4 = 1`. -/
private theorem sreCert_141_1 :
    slopeOrbit 141 1 (1 + 23) = slopeOrbit 141 1 1
      ∧ ∀ j, 1 ≤ j → j ≤ 23 →
          canonGap 141 (slopeOrbit 141 1 j) = 4 → j ∈ ({12} : Finset ℕ) := by
  have e0 : slopeOrbit 141 1 0 = 1 := rfl
  have e1 : slopeOrbit 141 1 1 = 115 :=
    slopeOrbit_step_eval 0 7 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 141 1 2 = 89 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 141 1 3 = 37 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 141 1 4 = 7 :=
    slopeOrbit_step_eval 3 1 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 141 1 5 = 83 :=
    slopeOrbit_step_eval 4 4 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 141 1 6 = 25 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 141 1 7 = 59 :=
    slopeOrbit_step_eval 6 2 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 141 1 8 = 95 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 141 1 9 = 49 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 141 1 10 = 55 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 141 1 11 = 79 :=
    slopeOrbit_step_eval 10 1 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 141 1 12 = 17 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 141 1 13 = 131 :=
    slopeOrbit_step_eval 12 3 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 141 1 14 = 121 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 141 1 15 = 101 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 141 1 16 = 61 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 141 1 17 = 103 :=
    slopeOrbit_step_eval 16 1 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 141 1 18 = 65 :=
    slopeOrbit_step_eval 17 0 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 141 1 19 = 119 :=
    slopeOrbit_step_eval 18 1 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 141 1 20 = 97 :=
    slopeOrbit_step_eval 19 0 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 141 1 21 = 53 :=
    slopeOrbit_step_eval 20 0 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 141 1 22 = 71 :=
    slopeOrbit_step_eval 21 1 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 141 1 23 = 1 :=
    slopeOrbit_step_eval 22 0 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 141 1 24 = 115 :=
    slopeOrbit_step_eval 23 7 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 141 1 24 = slopeOrbit 141 1 1
    rw [e24, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(141,1)`: the certified class-1 count cap `|fibre_1| <= 1 * ceil(W/23)`. -/
theorem sreClass1Count_of_datum_141_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 141) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 23 - 1) / 23) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 23)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_141_1.1
  have hcount : (class1Band4CycleBand ctx 23).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_141_1.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 23).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 23 - 1) / 23) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 23 - 1) / 23) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(141,23)`: period `23`, cycle `[43, 31, 107, 73, 5, 19, 11, 35, 139, 137, 133, 125, 109, 77, 13, 67, 127, 113, 85, 29, 91, 41, 23]`, bands `[2, 3, 1, 1, 5, 3, 4, 3, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 3]` - band-4 residue set `{7, 15}` (values `11, 13`), `b4 = 2`. -/
private theorem sreCert_141_23 :
    slopeOrbit 141 23 (1 + 23) = slopeOrbit 141 23 1
      ∧ ∀ j, 1 ≤ j → j ≤ 23 →
          canonGap 141 (slopeOrbit 141 23 j) = 4 → j ∈ ({7, 15} : Finset ℕ) := by
  have e0 : slopeOrbit 141 23 0 = 23 := rfl
  have e1 : slopeOrbit 141 23 1 = 43 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 141 23 2 = 31 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 141 23 3 = 107 :=
    slopeOrbit_step_eval 2 2 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 141 23 4 = 73 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 141 23 5 = 5 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 141 23 6 = 19 :=
    slopeOrbit_step_eval 5 4 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 141 23 7 = 11 :=
    slopeOrbit_step_eval 6 2 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 141 23 8 = 35 :=
    slopeOrbit_step_eval 7 3 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 141 23 9 = 139 :=
    slopeOrbit_step_eval 8 2 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 141 23 10 = 137 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 141 23 11 = 133 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 141 23 12 = 125 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 141 23 13 = 109 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 141 23 14 = 77 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 141 23 15 = 13 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 141 23 16 = 67 :=
    slopeOrbit_step_eval 15 3 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 141 23 17 = 127 :=
    slopeOrbit_step_eval 16 1 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 141 23 18 = 113 :=
    slopeOrbit_step_eval 17 0 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 141 23 19 = 85 :=
    slopeOrbit_step_eval 18 0 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 141 23 20 = 29 :=
    slopeOrbit_step_eval 19 0 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 141 23 21 = 91 :=
    slopeOrbit_step_eval 20 2 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 141 23 22 = 41 :=
    slopeOrbit_step_eval 21 0 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 141 23 23 = 23 :=
    slopeOrbit_step_eval 22 1 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 141 23 24 = 43 :=
    slopeOrbit_step_eval 23 2 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 141 23 24 = slopeOrbit 141 23 1
    rw [e24, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))

/-- `(141,23)`: the certified class-1 count cap `|fibre_1| <= 2 * ceil(W/23)`. -/
theorem sreClass1Count_of_datum_141_23 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 141) (hK : (class1SlopeDatum ctx).K₀ = 23) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 23 - 1) / 23) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 23)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_141_23.1
  have hcount : (class1Band4CycleBand ctx 23).card ≤ 2 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_141_23.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 23).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 23 - 1) / 23) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 23 - 1) / 23) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(141,70)`: period `23`, cycle `[139, 137, 133, 125, 109, 77, 13, 67, 127, 113, 85, 29, 91, 41, 23, 43, 31, 107, 73, 5, 19, 11, 35]`, bands `[1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 5, 3, 4, 3]` - band-4 residue set `{7, 22}` (values `13, 11`), `b4 = 2`. -/
private theorem sreCert_141_70 :
    slopeOrbit 141 70 (1 + 23) = slopeOrbit 141 70 1
      ∧ ∀ j, 1 ≤ j → j ≤ 23 →
          canonGap 141 (slopeOrbit 141 70 j) = 4 → j ∈ ({7, 22} : Finset ℕ) := by
  have e0 : slopeOrbit 141 70 0 = 70 := rfl
  have e1 : slopeOrbit 141 70 1 = 139 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 141 70 2 = 137 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 141 70 3 = 133 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 141 70 4 = 125 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 141 70 5 = 109 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 141 70 6 = 77 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 141 70 7 = 13 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 141 70 8 = 67 :=
    slopeOrbit_step_eval 7 3 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 141 70 9 = 127 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 141 70 10 = 113 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 141 70 11 = 85 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 141 70 12 = 29 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 141 70 13 = 91 :=
    slopeOrbit_step_eval 12 2 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 141 70 14 = 41 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 141 70 15 = 23 :=
    slopeOrbit_step_eval 14 1 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 141 70 16 = 43 :=
    slopeOrbit_step_eval 15 2 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 141 70 17 = 31 :=
    slopeOrbit_step_eval 16 1 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 141 70 18 = 107 :=
    slopeOrbit_step_eval 17 2 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 141 70 19 = 73 :=
    slopeOrbit_step_eval 18 0 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 141 70 20 = 5 :=
    slopeOrbit_step_eval 19 0 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 141 70 21 = 19 :=
    slopeOrbit_step_eval 20 4 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 141 70 22 = 11 :=
    slopeOrbit_step_eval 21 2 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 141 70 23 = 35 :=
    slopeOrbit_step_eval 22 3 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 141 70 24 = 139 :=
    slopeOrbit_step_eval 23 2 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 141 70 24 = slopeOrbit 141 70 1
    rw [e24, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))

/-- `(141,70)`: the certified class-1 count cap `|fibre_1| <= 2 * ceil(W/23)`. -/
theorem sreClass1Count_of_datum_141_70 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 141) (hK : (class1SlopeDatum ctx).K₀ = 70) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 23 - 1) / 23) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 23)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_141_70.1
  have hcount : (class1Band4CycleBand ctx 23).card ≤ 2 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_141_70.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 23).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 23 - 1) / 23) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 23 - 1) / 23) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(143,5)`: period `35`, cycle `[17, 129, 115, 87, 31, 105, 67, 125, 107, 71, 141, 139, 135, 127, 111, 79, 15, 97, 51, 61, 101, 59, 93, 43, 29, 89, 35, 137, 131, 119, 95, 47, 45, 37, 5]`, bands `[4, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 3, 1, 3, 1, 1, 1, 1, 2, 2, 2, 5]` - band-4 residue set `{1, 17}` (values `17, 15`), `b4 = 2`. -/
private theorem sreCert_143_5 :
    slopeOrbit 143 5 (1 + 35) = slopeOrbit 143 5 1
      ∧ ∀ j, 1 ≤ j → j ≤ 35 →
          canonGap 143 (slopeOrbit 143 5 j) = 4 → j ∈ ({1, 17} : Finset ℕ) := by
  have e0 : slopeOrbit 143 5 0 = 5 := rfl
  have e1 : slopeOrbit 143 5 1 = 17 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 143 5 2 = 129 :=
    slopeOrbit_step_eval 1 3 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 143 5 3 = 115 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 143 5 4 = 87 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 143 5 5 = 31 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 143 5 6 = 105 :=
    slopeOrbit_step_eval 5 2 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 143 5 7 = 67 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 143 5 8 = 125 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 143 5 9 = 107 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 143 5 10 = 71 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 143 5 11 = 141 :=
    slopeOrbit_step_eval 10 1 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 143 5 12 = 139 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 143 5 13 = 135 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 143 5 14 = 127 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 143 5 15 = 111 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 143 5 16 = 79 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 143 5 17 = 15 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 143 5 18 = 97 :=
    slopeOrbit_step_eval 17 3 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 143 5 19 = 51 :=
    slopeOrbit_step_eval 18 0 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 143 5 20 = 61 :=
    slopeOrbit_step_eval 19 1 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 143 5 21 = 101 :=
    slopeOrbit_step_eval 20 1 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 143 5 22 = 59 :=
    slopeOrbit_step_eval 21 0 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 143 5 23 = 93 :=
    slopeOrbit_step_eval 22 1 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 143 5 24 = 43 :=
    slopeOrbit_step_eval 23 0 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 143 5 25 = 29 :=
    slopeOrbit_step_eval 24 1 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 143 5 26 = 89 :=
    slopeOrbit_step_eval 25 2 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 143 5 27 = 35 :=
    slopeOrbit_step_eval 26 0 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 143 5 28 = 137 :=
    slopeOrbit_step_eval 27 2 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 143 5 29 = 131 :=
    slopeOrbit_step_eval 28 0 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 143 5 30 = 119 :=
    slopeOrbit_step_eval 29 0 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : slopeOrbit 143 5 31 = 95 :=
    slopeOrbit_step_eval 30 0 e30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e32 : slopeOrbit 143 5 32 = 47 :=
    slopeOrbit_step_eval 31 0 e31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e33 : slopeOrbit 143 5 33 = 45 :=
    slopeOrbit_step_eval 32 1 e32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e34 : slopeOrbit 143 5 34 = 37 :=
    slopeOrbit_step_eval 33 1 e33 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e35 : slopeOrbit 143 5 35 = 5 :=
    slopeOrbit_step_eval 34 1 e34 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e36 : slopeOrbit 143 5 36 = 17 :=
    slopeOrbit_step_eval 35 4 e35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 143 5 36 = slopeOrbit 143 5 1
    rw [e36, e1]
  · intro j h1 h2 hband
    interval_cases j
    · decide
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e26] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e27] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e28] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e29] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e30] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e31] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e32] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e33] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e34] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e35] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(143,5)`: the certified class-1 count cap `|fibre_1| <= 2 * ceil(W/35)`. -/
theorem sreClass1Count_of_datum_143_5 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 143) (hK : (class1SlopeDatum ctx).K₀ = 5) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 35 - 1) / 35) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 35)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_143_5.1
  have hcount : (class1Band4CycleBand ctx 35).card ≤ 2 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_143_5.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 35).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 35 - 1) / 35) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 35 - 1) / 35) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(143,6)`: period `25`, cycle `[49, 53, 69, 133, 123, 103, 63, 109, 75, 7, 81, 19, 9, 1, 113, 83, 23, 41, 21, 25, 57, 85, 27, 73, 3]`, bands `[2, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 4, 8, 1, 1, 3, 2, 3, 3, 2, 1, 3, 1, 6]` - band-4 residue set `{13}` (values `9`), `b4 = 1`. -/
private theorem sreCert_143_6 :
    slopeOrbit 143 6 (1 + 25) = slopeOrbit 143 6 1
      ∧ ∀ j, 1 ≤ j → j ≤ 25 →
          canonGap 143 (slopeOrbit 143 6 j) = 4 → j ∈ ({13} : Finset ℕ) := by
  have e0 : slopeOrbit 143 6 0 = 6 := rfl
  have e1 : slopeOrbit 143 6 1 = 49 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 143 6 2 = 53 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 143 6 3 = 69 :=
    slopeOrbit_step_eval 2 1 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 143 6 4 = 133 :=
    slopeOrbit_step_eval 3 1 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 143 6 5 = 123 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 143 6 6 = 103 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 143 6 7 = 63 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 143 6 8 = 109 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 143 6 9 = 75 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 143 6 10 = 7 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 143 6 11 = 81 :=
    slopeOrbit_step_eval 10 4 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 143 6 12 = 19 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 143 6 13 = 9 :=
    slopeOrbit_step_eval 12 2 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 143 6 14 = 1 :=
    slopeOrbit_step_eval 13 3 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 143 6 15 = 113 :=
    slopeOrbit_step_eval 14 7 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 143 6 16 = 83 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 143 6 17 = 23 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 143 6 18 = 41 :=
    slopeOrbit_step_eval 17 2 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 143 6 19 = 21 :=
    slopeOrbit_step_eval 18 1 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 143 6 20 = 25 :=
    slopeOrbit_step_eval 19 2 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 143 6 21 = 57 :=
    slopeOrbit_step_eval 20 2 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 143 6 22 = 85 :=
    slopeOrbit_step_eval 21 1 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 143 6 23 = 27 :=
    slopeOrbit_step_eval 22 0 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 143 6 24 = 73 :=
    slopeOrbit_step_eval 23 2 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 143 6 25 = 3 :=
    slopeOrbit_step_eval 24 0 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 143 6 26 = 49 :=
    slopeOrbit_step_eval 25 5 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 143 6 26 = slopeOrbit 143 6 1
    rw [e26, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(143,6)`: the certified class-1 count cap `|fibre_1| <= 1 * ceil(W/25)`. -/
theorem sreClass1Count_of_datum_143_6 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 143) (hK : (class1SlopeDatum ctx).K₀ = 6) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 25 - 1) / 25) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 25)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_143_6.1
  have hcount : (class1Band4CycleBand ctx 25).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_143_6.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 25).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 25 - 1) / 25) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 25 - 1) / 25) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(143,71)`: period `35`, cycle `[141, 139, 135, 127, 111, 79, 15, 97, 51, 61, 101, 59, 93, 43, 29, 89, 35, 137, 131, 119, 95, 47, 45, 37, 5, 17, 129, 115, 87, 31, 105, 67, 125, 107, 71]`, bands `[1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 3, 1, 3, 1, 1, 1, 1, 2, 2, 2, 5, 4, 1, 1, 1, 3, 1, 2, 1, 1, 2]` - band-4 residue set `{7, 26}` (values `15, 17`), `b4 = 2`. -/
private theorem sreCert_143_71 :
    slopeOrbit 143 71 (1 + 35) = slopeOrbit 143 71 1
      ∧ ∀ j, 1 ≤ j → j ≤ 35 →
          canonGap 143 (slopeOrbit 143 71 j) = 4 → j ∈ ({7, 26} : Finset ℕ) := by
  have e0 : slopeOrbit 143 71 0 = 71 := rfl
  have e1 : slopeOrbit 143 71 1 = 141 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 143 71 2 = 139 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 143 71 3 = 135 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 143 71 4 = 127 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 143 71 5 = 111 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 143 71 6 = 79 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 143 71 7 = 15 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 143 71 8 = 97 :=
    slopeOrbit_step_eval 7 3 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 143 71 9 = 51 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 143 71 10 = 61 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 143 71 11 = 101 :=
    slopeOrbit_step_eval 10 1 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 143 71 12 = 59 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 143 71 13 = 93 :=
    slopeOrbit_step_eval 12 1 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 143 71 14 = 43 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 143 71 15 = 29 :=
    slopeOrbit_step_eval 14 1 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 143 71 16 = 89 :=
    slopeOrbit_step_eval 15 2 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 143 71 17 = 35 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 143 71 18 = 137 :=
    slopeOrbit_step_eval 17 2 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 143 71 19 = 131 :=
    slopeOrbit_step_eval 18 0 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 143 71 20 = 119 :=
    slopeOrbit_step_eval 19 0 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 143 71 21 = 95 :=
    slopeOrbit_step_eval 20 0 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 143 71 22 = 47 :=
    slopeOrbit_step_eval 21 0 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 143 71 23 = 45 :=
    slopeOrbit_step_eval 22 1 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 143 71 24 = 37 :=
    slopeOrbit_step_eval 23 1 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 143 71 25 = 5 :=
    slopeOrbit_step_eval 24 1 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 143 71 26 = 17 :=
    slopeOrbit_step_eval 25 4 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 143 71 27 = 129 :=
    slopeOrbit_step_eval 26 3 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 143 71 28 = 115 :=
    slopeOrbit_step_eval 27 0 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 143 71 29 = 87 :=
    slopeOrbit_step_eval 28 0 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 143 71 30 = 31 :=
    slopeOrbit_step_eval 29 0 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : slopeOrbit 143 71 31 = 105 :=
    slopeOrbit_step_eval 30 2 e30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e32 : slopeOrbit 143 71 32 = 67 :=
    slopeOrbit_step_eval 31 0 e31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e33 : slopeOrbit 143 71 33 = 125 :=
    slopeOrbit_step_eval 32 1 e32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e34 : slopeOrbit 143 71 34 = 107 :=
    slopeOrbit_step_eval 33 0 e33 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e35 : slopeOrbit 143 71 35 = 71 :=
    slopeOrbit_step_eval 34 0 e34 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e36 : slopeOrbit 143 71 36 = 141 :=
    slopeOrbit_step_eval 35 1 e35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 143 71 36 = slopeOrbit 143 71 1
    rw [e36, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · decide
    · rw [e27] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e28] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e29] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e30] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e31] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e32] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e33] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e34] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e35] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))

/-- `(143,71)`: the certified class-1 count cap `|fibre_1| <= 2 * ceil(W/35)`. -/
theorem sreClass1Count_of_datum_143_71 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 143) (hK : (class1SlopeDatum ctx).K₀ = 71) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 35 - 1) / 35) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 35)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_143_71.1
  have hcount : (class1Band4CycleBand ctx 35).card ≤ 2 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_143_71.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 35).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 35 - 1) / 35) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 35 - 1) / 35) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(145,2)`: period `14`, cycle `[111, 77, 9, 143, 141, 137, 129, 113, 81, 17, 127, 109, 73, 1]`, bands `[1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 8]` - band-4 residue set `{10}` (values `17`), `b4 = 1`. -/
private theorem sreCert_145_2 :
    slopeOrbit 145 2 (1 + 14) = slopeOrbit 145 2 1
      ∧ ∀ j, 1 ≤ j → j ≤ 14 →
          canonGap 145 (slopeOrbit 145 2 j) = 4 → j ∈ ({10} : Finset ℕ) := by
  have e0 : slopeOrbit 145 2 0 = 2 := rfl
  have e1 : slopeOrbit 145 2 1 = 111 :=
    slopeOrbit_step_eval 0 6 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 145 2 2 = 77 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 145 2 3 = 9 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 145 2 4 = 143 :=
    slopeOrbit_step_eval 3 4 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 145 2 5 = 141 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 145 2 6 = 137 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 145 2 7 = 129 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 145 2 8 = 113 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 145 2 9 = 81 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 145 2 10 = 17 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 145 2 11 = 127 :=
    slopeOrbit_step_eval 10 3 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 145 2 12 = 109 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 145 2 13 = 73 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 145 2 14 = 1 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 145 2 15 = 111 :=
    slopeOrbit_step_eval 14 7 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 145 2 15 = slopeOrbit 145 2 1
    rw [e15, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(145,2)`: the certified class-1 count cap `|fibre_1| <= 1 * ceil(W/14)`. -/
theorem sreClass1Count_of_datum_145_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 145) (hK : (class1SlopeDatum ctx).K₀ = 2) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 14 - 1) / 14) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 14)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_145_2.1
  have hcount : (class1Band4CycleBand ctx 14).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_145_2.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 14).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 14 - 1) / 14) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 14 - 1) / 14) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(145,14)`: period `14`, cycle `[79, 13, 63, 107, 69, 131, 117, 89, 33, 119, 93, 41, 19, 7]`, bands `[1, 4, 2, 1, 2, 1, 1, 1, 3, 1, 1, 2, 3, 5]` - band-4 residue set `{2}` (values `13`), `b4 = 1`. -/
private theorem sreCert_145_14 :
    slopeOrbit 145 14 (1 + 14) = slopeOrbit 145 14 1
      ∧ ∀ j, 1 ≤ j → j ≤ 14 →
          canonGap 145 (slopeOrbit 145 14 j) = 4 → j ∈ ({2} : Finset ℕ) := by
  have e0 : slopeOrbit 145 14 0 = 14 := rfl
  have e1 : slopeOrbit 145 14 1 = 79 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 145 14 2 = 13 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 145 14 3 = 63 :=
    slopeOrbit_step_eval 2 3 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 145 14 4 = 107 :=
    slopeOrbit_step_eval 3 1 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 145 14 5 = 69 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 145 14 6 = 131 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 145 14 7 = 117 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 145 14 8 = 89 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 145 14 9 = 33 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 145 14 10 = 119 :=
    slopeOrbit_step_eval 9 2 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 145 14 11 = 93 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 145 14 12 = 41 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 145 14 13 = 19 :=
    slopeOrbit_step_eval 12 1 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 145 14 14 = 7 :=
    slopeOrbit_step_eval 13 2 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 145 14 15 = 79 :=
    slopeOrbit_step_eval 14 4 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 145 14 15 = slopeOrbit 145 14 1
    rw [e15, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(145,14)`: the certified class-1 count cap `|fibre_1| <= 1 * ceil(W/14)`. -/
theorem sreClass1Count_of_datum_145_14 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 145) (hK : (class1SlopeDatum ctx).K₀ = 14) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 14 - 1) / 14) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 14)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_145_14.1
  have hcount : (class1Band4CycleBand ctx 14).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_145_14.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 14).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 14 - 1) / 14) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 14 - 1) / 14) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(145,72)`: period `14`, cycle `[143, 141, 137, 129, 113, 81, 17, 127, 109, 73, 1, 111, 77, 9]`, bands `[1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 8, 1, 1, 5]` - band-4 residue set `{7}` (values `17`), `b4 = 1`. -/
private theorem sreCert_145_72 :
    slopeOrbit 145 72 (1 + 14) = slopeOrbit 145 72 1
      ∧ ∀ j, 1 ≤ j → j ≤ 14 →
          canonGap 145 (slopeOrbit 145 72 j) = 4 → j ∈ ({7} : Finset ℕ) := by
  have e0 : slopeOrbit 145 72 0 = 72 := rfl
  have e1 : slopeOrbit 145 72 1 = 143 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 145 72 2 = 141 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 145 72 3 = 137 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 145 72 4 = 129 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 145 72 5 = 113 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 145 72 6 = 81 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 145 72 7 = 17 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 145 72 8 = 127 :=
    slopeOrbit_step_eval 7 3 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 145 72 9 = 109 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 145 72 10 = 73 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 145 72 11 = 1 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 145 72 12 = 111 :=
    slopeOrbit_step_eval 11 7 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 145 72 13 = 77 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 145 72 14 = 9 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 145 72 15 = 143 :=
    slopeOrbit_step_eval 14 4 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 145 72 15 = slopeOrbit 145 72 1
    rw [e15, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(145,72)`: the certified class-1 count cap `|fibre_1| <= 1 * ceil(W/14)`. -/
theorem sreClass1Count_of_datum_145_72 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 145) (hK : (class1SlopeDatum ctx).K₀ = 72) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 14 - 1) / 14) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 14)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_145_72.1
  have hcount : (class1Band4CycleBand ctx 14).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_145_72.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 14).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 14 - 1) / 14) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 14 - 1) / 14) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(147,1)`: period `20`, cycle `[109, 71, 137, 127, 107, 67, 121, 95, 43, 25, 53, 65, 113, 79, 11, 29, 85, 23, 37, 1]`, bands `[1, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 3, 1, 3, 2, 8]` - band-4 residue set `{15}` (values `11`), `b4 = 1`. -/
private theorem sreCert_147_1 :
    slopeOrbit 147 1 (1 + 20) = slopeOrbit 147 1 1
      ∧ ∀ j, 1 ≤ j → j ≤ 20 →
          canonGap 147 (slopeOrbit 147 1 j) = 4 → j ∈ ({15} : Finset ℕ) := by
  have e0 : slopeOrbit 147 1 0 = 1 := rfl
  have e1 : slopeOrbit 147 1 1 = 109 :=
    slopeOrbit_step_eval 0 7 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 147 1 2 = 71 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 147 1 3 = 137 :=
    slopeOrbit_step_eval 2 1 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 147 1 4 = 127 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 147 1 5 = 107 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 147 1 6 = 67 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 147 1 7 = 121 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 147 1 8 = 95 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 147 1 9 = 43 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 147 1 10 = 25 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 147 1 11 = 53 :=
    slopeOrbit_step_eval 10 2 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 147 1 12 = 65 :=
    slopeOrbit_step_eval 11 1 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 147 1 13 = 113 :=
    slopeOrbit_step_eval 12 1 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 147 1 14 = 79 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 147 1 15 = 11 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 147 1 16 = 29 :=
    slopeOrbit_step_eval 15 3 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 147 1 17 = 85 :=
    slopeOrbit_step_eval 16 2 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 147 1 18 = 23 :=
    slopeOrbit_step_eval 17 0 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 147 1 19 = 37 :=
    slopeOrbit_step_eval 18 2 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 147 1 20 = 1 :=
    slopeOrbit_step_eval 19 1 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 147 1 21 = 109 :=
    slopeOrbit_step_eval 20 7 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 147 1 21 = slopeOrbit 147 1 1
    rw [e21, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(147,1)`: the certified class-1 count cap `|fibre_1| <= 1 * ceil(W/20)`. -/
theorem sreClass1Count_of_datum_147_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 147) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 20 - 1) / 20) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 20)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_147_1.1
  have hcount : (class1Band4CycleBand ctx 20).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_147_1.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 20).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 20 - 1) / 20) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 20 - 1) / 20) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(147,10)`: period `22`, cycle `[13, 61, 97, 47, 41, 17, 125, 103, 59, 89, 31, 101, 55, 73, 145, 143, 139, 131, 115, 83, 19, 5]`, bands `[4, 2, 1, 2, 2, 4, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5]` - band-4 residue set `{1, 6}` (values `13, 17`), `b4 = 2`. -/
private theorem sreCert_147_10 :
    slopeOrbit 147 10 (1 + 22) = slopeOrbit 147 10 1
      ∧ ∀ j, 1 ≤ j → j ≤ 22 →
          canonGap 147 (slopeOrbit 147 10 j) = 4 → j ∈ ({1, 6} : Finset ℕ) := by
  have e0 : slopeOrbit 147 10 0 = 10 := rfl
  have e1 : slopeOrbit 147 10 1 = 13 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 147 10 2 = 61 :=
    slopeOrbit_step_eval 1 3 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 147 10 3 = 97 :=
    slopeOrbit_step_eval 2 1 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 147 10 4 = 47 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 147 10 5 = 41 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 147 10 6 = 17 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 147 10 7 = 125 :=
    slopeOrbit_step_eval 6 3 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 147 10 8 = 103 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 147 10 9 = 59 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 147 10 10 = 89 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 147 10 11 = 31 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 147 10 12 = 101 :=
    slopeOrbit_step_eval 11 2 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 147 10 13 = 55 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 147 10 14 = 73 :=
    slopeOrbit_step_eval 13 1 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 147 10 15 = 145 :=
    slopeOrbit_step_eval 14 1 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 147 10 16 = 143 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 147 10 17 = 139 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 147 10 18 = 131 :=
    slopeOrbit_step_eval 17 0 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 147 10 19 = 115 :=
    slopeOrbit_step_eval 18 0 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 147 10 20 = 83 :=
    slopeOrbit_step_eval 19 0 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 147 10 21 = 19 :=
    slopeOrbit_step_eval 20 0 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 147 10 22 = 5 :=
    slopeOrbit_step_eval 21 2 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 147 10 23 = 13 :=
    slopeOrbit_step_eval 22 4 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 147 10 23 = slopeOrbit 147 10 1
    rw [e23, e1]
  · intro j h1 h2 hband
    interval_cases j
    · decide
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(147,10)`: the certified class-1 count cap `|fibre_1| <= 2 * ceil(W/22)`. -/
theorem sreClass1Count_of_datum_147_10 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 147) (hK : (class1SlopeDatum ctx).K₀ = 10) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 22 - 1) / 22) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 22)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_147_10.1
  have hcount : (class1Band4CycleBand ctx 22).card ≤ 2 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_147_10.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 22).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 22 - 1) / 22) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 22 - 1) / 22) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(147,73)`: period `22`, cycle `[145, 143, 139, 131, 115, 83, 19, 5, 13, 61, 97, 47, 41, 17, 125, 103, 59, 89, 31, 101, 55, 73]`, bands `[1, 1, 1, 1, 1, 1, 3, 5, 4, 2, 1, 2, 2, 4, 1, 1, 2, 1, 3, 1, 2, 2]` - band-4 residue set `{9, 14}` (values `13, 17`), `b4 = 2`. -/
private theorem sreCert_147_73 :
    slopeOrbit 147 73 (1 + 22) = slopeOrbit 147 73 1
      ∧ ∀ j, 1 ≤ j → j ≤ 22 →
          canonGap 147 (slopeOrbit 147 73 j) = 4 → j ∈ ({9, 14} : Finset ℕ) := by
  have e0 : slopeOrbit 147 73 0 = 73 := rfl
  have e1 : slopeOrbit 147 73 1 = 145 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 147 73 2 = 143 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 147 73 3 = 139 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 147 73 4 = 131 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 147 73 5 = 115 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 147 73 6 = 83 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 147 73 7 = 19 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 147 73 8 = 5 :=
    slopeOrbit_step_eval 7 2 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 147 73 9 = 13 :=
    slopeOrbit_step_eval 8 4 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 147 73 10 = 61 :=
    slopeOrbit_step_eval 9 3 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 147 73 11 = 97 :=
    slopeOrbit_step_eval 10 1 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 147 73 12 = 47 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 147 73 13 = 41 :=
    slopeOrbit_step_eval 12 1 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 147 73 14 = 17 :=
    slopeOrbit_step_eval 13 1 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 147 73 15 = 125 :=
    slopeOrbit_step_eval 14 3 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 147 73 16 = 103 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 147 73 17 = 59 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 147 73 18 = 89 :=
    slopeOrbit_step_eval 17 1 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 147 73 19 = 31 :=
    slopeOrbit_step_eval 18 0 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 147 73 20 = 101 :=
    slopeOrbit_step_eval 19 2 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 147 73 21 = 55 :=
    slopeOrbit_step_eval 20 0 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 147 73 22 = 73 :=
    slopeOrbit_step_eval 21 1 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 147 73 23 = 145 :=
    slopeOrbit_step_eval 22 1 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 147 73 23 = slopeOrbit 147 73 1
    rw [e23, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · decide
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))

/-- `(147,73)`: the certified class-1 count cap `|fibre_1| <= 2 * ceil(W/22)`. -/
theorem sreClass1Count_of_datum_147_73 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 147) (hK : (class1SlopeDatum ctx).K₀ = 73) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 22 - 1) / 22) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 22)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_147_73.1
  have hcount : (class1Band4CycleBand ctx 22).card ≤ 2 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_147_73.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 22).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 22 - 1) / 22) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 22 - 1) / 22) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(149,74)`: period `74`, cycle `[147, 145, 141, 133, 117, 85, 21, 19, 3, 43, 23, 35, 131, 113, 77, 5, 11, 27, 67, 119, 89, 29, 83, 17, 123, 97, 45, 31, 99, 49, 47, 39, 7, 75, 1, 107, 65, 111, 73, 143, 137, 125, 101, 53, 63, 103, 57, 79, 9, 139, 129, 109, 69, 127, 105, 61, 95, 41, 15, 91, 33, 115, 81, 13, 59, 87, 25, 51, 55, 71, 135, 121, 93, 37]`, bands `[1, 1, 1, 1, 1, 1, 3, 3, 6, 2, 3, 3, 1, 1, 1, 5, 4, 3, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 2, 2, 2, 5, 1, 8, 1, 2, 1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 4, 2, 1, 3, 2, 2, 2, 1, 1, 1, 3]` - band-4 residue set `{17, 24, 59, 64}` (values `11, 17, 15, 13`), `b4 = 4`. -/
private theorem sreCert_149_74 :
    slopeOrbit 149 74 (1 + 74) = slopeOrbit 149 74 1
      ∧ ∀ j, 1 ≤ j → j ≤ 74 →
          canonGap 149 (slopeOrbit 149 74 j) = 4 → j ∈ ({17, 24, 59, 64} : Finset ℕ) := by
  have e0 : slopeOrbit 149 74 0 = 74 := rfl
  have e1 : slopeOrbit 149 74 1 = 147 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 149 74 2 = 145 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 149 74 3 = 141 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 149 74 4 = 133 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 149 74 5 = 117 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 149 74 6 = 85 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 149 74 7 = 21 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 149 74 8 = 19 :=
    slopeOrbit_step_eval 7 2 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 149 74 9 = 3 :=
    slopeOrbit_step_eval 8 2 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 149 74 10 = 43 :=
    slopeOrbit_step_eval 9 5 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 149 74 11 = 23 :=
    slopeOrbit_step_eval 10 1 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 149 74 12 = 35 :=
    slopeOrbit_step_eval 11 2 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 149 74 13 = 131 :=
    slopeOrbit_step_eval 12 2 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 149 74 14 = 113 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 149 74 15 = 77 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 149 74 16 = 5 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 149 74 17 = 11 :=
    slopeOrbit_step_eval 16 4 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 149 74 18 = 27 :=
    slopeOrbit_step_eval 17 3 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 149 74 19 = 67 :=
    slopeOrbit_step_eval 18 2 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 149 74 20 = 119 :=
    slopeOrbit_step_eval 19 1 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 149 74 21 = 89 :=
    slopeOrbit_step_eval 20 0 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 149 74 22 = 29 :=
    slopeOrbit_step_eval 21 0 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 149 74 23 = 83 :=
    slopeOrbit_step_eval 22 2 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 149 74 24 = 17 :=
    slopeOrbit_step_eval 23 0 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 149 74 25 = 123 :=
    slopeOrbit_step_eval 24 3 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 149 74 26 = 97 :=
    slopeOrbit_step_eval 25 0 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 149 74 27 = 45 :=
    slopeOrbit_step_eval 26 0 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 149 74 28 = 31 :=
    slopeOrbit_step_eval 27 1 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 149 74 29 = 99 :=
    slopeOrbit_step_eval 28 2 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 149 74 30 = 49 :=
    slopeOrbit_step_eval 29 0 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : slopeOrbit 149 74 31 = 47 :=
    slopeOrbit_step_eval 30 1 e30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e32 : slopeOrbit 149 74 32 = 39 :=
    slopeOrbit_step_eval 31 1 e31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e33 : slopeOrbit 149 74 33 = 7 :=
    slopeOrbit_step_eval 32 1 e32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e34 : slopeOrbit 149 74 34 = 75 :=
    slopeOrbit_step_eval 33 4 e33 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e35 : slopeOrbit 149 74 35 = 1 :=
    slopeOrbit_step_eval 34 0 e34 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e36 : slopeOrbit 149 74 36 = 107 :=
    slopeOrbit_step_eval 35 7 e35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e37 : slopeOrbit 149 74 37 = 65 :=
    slopeOrbit_step_eval 36 0 e36 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e38 : slopeOrbit 149 74 38 = 111 :=
    slopeOrbit_step_eval 37 1 e37 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e39 : slopeOrbit 149 74 39 = 73 :=
    slopeOrbit_step_eval 38 0 e38 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e40 : slopeOrbit 149 74 40 = 143 :=
    slopeOrbit_step_eval 39 1 e39 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e41 : slopeOrbit 149 74 41 = 137 :=
    slopeOrbit_step_eval 40 0 e40 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e42 : slopeOrbit 149 74 42 = 125 :=
    slopeOrbit_step_eval 41 0 e41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e43 : slopeOrbit 149 74 43 = 101 :=
    slopeOrbit_step_eval 42 0 e42 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e44 : slopeOrbit 149 74 44 = 53 :=
    slopeOrbit_step_eval 43 0 e43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e45 : slopeOrbit 149 74 45 = 63 :=
    slopeOrbit_step_eval 44 1 e44 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e46 : slopeOrbit 149 74 46 = 103 :=
    slopeOrbit_step_eval 45 1 e45 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e47 : slopeOrbit 149 74 47 = 57 :=
    slopeOrbit_step_eval 46 0 e46 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e48 : slopeOrbit 149 74 48 = 79 :=
    slopeOrbit_step_eval 47 1 e47 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e49 : slopeOrbit 149 74 49 = 9 :=
    slopeOrbit_step_eval 48 0 e48 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e50 : slopeOrbit 149 74 50 = 139 :=
    slopeOrbit_step_eval 49 4 e49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e51 : slopeOrbit 149 74 51 = 129 :=
    slopeOrbit_step_eval 50 0 e50 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e52 : slopeOrbit 149 74 52 = 109 :=
    slopeOrbit_step_eval 51 0 e51 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e53 : slopeOrbit 149 74 53 = 69 :=
    slopeOrbit_step_eval 52 0 e52 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e54 : slopeOrbit 149 74 54 = 127 :=
    slopeOrbit_step_eval 53 1 e53 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e55 : slopeOrbit 149 74 55 = 105 :=
    slopeOrbit_step_eval 54 0 e54 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e56 : slopeOrbit 149 74 56 = 61 :=
    slopeOrbit_step_eval 55 0 e55 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e57 : slopeOrbit 149 74 57 = 95 :=
    slopeOrbit_step_eval 56 1 e56 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e58 : slopeOrbit 149 74 58 = 41 :=
    slopeOrbit_step_eval 57 0 e57 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e59 : slopeOrbit 149 74 59 = 15 :=
    slopeOrbit_step_eval 58 1 e58 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e60 : slopeOrbit 149 74 60 = 91 :=
    slopeOrbit_step_eval 59 3 e59 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e61 : slopeOrbit 149 74 61 = 33 :=
    slopeOrbit_step_eval 60 0 e60 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e62 : slopeOrbit 149 74 62 = 115 :=
    slopeOrbit_step_eval 61 2 e61 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e63 : slopeOrbit 149 74 63 = 81 :=
    slopeOrbit_step_eval 62 0 e62 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e64 : slopeOrbit 149 74 64 = 13 :=
    slopeOrbit_step_eval 63 0 e63 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e65 : slopeOrbit 149 74 65 = 59 :=
    slopeOrbit_step_eval 64 3 e64 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e66 : slopeOrbit 149 74 66 = 87 :=
    slopeOrbit_step_eval 65 1 e65 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e67 : slopeOrbit 149 74 67 = 25 :=
    slopeOrbit_step_eval 66 0 e66 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e68 : slopeOrbit 149 74 68 = 51 :=
    slopeOrbit_step_eval 67 2 e67 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e69 : slopeOrbit 149 74 69 = 55 :=
    slopeOrbit_step_eval 68 1 e68 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e70 : slopeOrbit 149 74 70 = 71 :=
    slopeOrbit_step_eval 69 1 e69 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e71 : slopeOrbit 149 74 71 = 135 :=
    slopeOrbit_step_eval 70 1 e70 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e72 : slopeOrbit 149 74 72 = 121 :=
    slopeOrbit_step_eval 71 0 e71 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e73 : slopeOrbit 149 74 73 = 93 :=
    slopeOrbit_step_eval 72 0 e72 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e74 : slopeOrbit 149 74 74 = 37 :=
    slopeOrbit_step_eval 73 0 e73 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e75 : slopeOrbit 149 74 75 = 147 :=
    slopeOrbit_step_eval 74 2 e74 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 149 74 75 = slopeOrbit 149 74 1
    rw [e75, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · decide
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e26] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e27] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e28] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e29] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e30] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e31] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e32] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e33] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e34] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e35] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e36] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e37] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e38] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e39] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e40] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e41] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e42] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e43] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e44] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e45] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e46] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e47] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e48] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e49] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e50] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e51] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e52] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e53] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e54] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e55] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e56] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e57] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e58] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e60] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e61] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e62] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e63] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e65] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e66] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e67] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e68] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e69] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e70] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e71] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e72] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e73] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e74] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))

/-- `(149,74)`: the certified class-1 count cap `|fibre_1| <= 4 * ceil(W/74)`. -/
theorem sreClass1Count_of_datum_149_74 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 149) (hK : (class1SlopeDatum ctx).K₀ = 74) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 4 * (((supportShell ctx.shell.d ctx.shell.X).card + 74 - 1) / 74) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 74)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_149_74.1
  have hcount : (class1Band4CycleBand ctx 74).card ≤ 4 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_149_74.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 74).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 74 - 1) / 74) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 4 * (((supportShell ctx.shell.d ctx.shell.X).card + 74 - 1) / 74) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(153,1)`: period `10`, cycle `[103, 53, 59, 83, 13, 55, 67, 115, 77, 1]`, bands `[1, 2, 2, 1, 4, 2, 2, 1, 1, 8]` - band-4 residue set `{5}` (values `13`), `b4 = 1`. -/
private theorem sreCert_153_1 :
    slopeOrbit 153 1 (1 + 10) = slopeOrbit 153 1 1
      ∧ ∀ j, 1 ≤ j → j ≤ 10 →
          canonGap 153 (slopeOrbit 153 1 j) = 4 → j ∈ ({5} : Finset ℕ) := by
  have e0 : slopeOrbit 153 1 0 = 1 := rfl
  have e1 : slopeOrbit 153 1 1 = 103 :=
    slopeOrbit_step_eval 0 7 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 153 1 2 = 53 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 153 1 3 = 59 :=
    slopeOrbit_step_eval 2 1 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 153 1 4 = 83 :=
    slopeOrbit_step_eval 3 1 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 153 1 5 = 13 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 153 1 6 = 55 :=
    slopeOrbit_step_eval 5 3 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 153 1 7 = 67 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 153 1 8 = 115 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 153 1 9 = 77 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 153 1 10 = 1 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 153 1 11 = 103 :=
    slopeOrbit_step_eval 10 7 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 153 1 11 = slopeOrbit 153 1 1
    rw [e11, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(153,1)`: the certified class-1 count cap `|fibre_1| <= 1 * ceil(W/10)`. -/
theorem sreClass1Count_of_datum_153_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 153) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 10 - 1) / 10) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 10)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_153_1.1
  have hcount : (class1Band4CycleBand ctx 10).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_153_1.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 10).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 10 - 1) / 10) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 10 - 1) / 10) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(153,4)`: period `10`, cycle `[103, 53, 59, 83, 13, 55, 67, 115, 77, 1]`, bands `[1, 2, 2, 1, 4, 2, 2, 1, 1, 8]` - band-4 residue set `{5}` (values `13`), `b4 = 1`. -/
private theorem sreCert_153_4 :
    slopeOrbit 153 4 (1 + 10) = slopeOrbit 153 4 1
      ∧ ∀ j, 1 ≤ j → j ≤ 10 →
          canonGap 153 (slopeOrbit 153 4 j) = 4 → j ∈ ({5} : Finset ℕ) := by
  have e0 : slopeOrbit 153 4 0 = 4 := rfl
  have e1 : slopeOrbit 153 4 1 = 103 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 153 4 2 = 53 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 153 4 3 = 59 :=
    slopeOrbit_step_eval 2 1 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 153 4 4 = 83 :=
    slopeOrbit_step_eval 3 1 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 153 4 5 = 13 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 153 4 6 = 55 :=
    slopeOrbit_step_eval 5 3 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 153 4 7 = 67 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 153 4 8 = 115 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 153 4 9 = 77 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 153 4 10 = 1 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 153 4 11 = 103 :=
    slopeOrbit_step_eval 10 7 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 153 4 11 = slopeOrbit 153 4 1
    rw [e11, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(153,4)`: the certified class-1 count cap `|fibre_1| <= 1 * ceil(W/10)`. -/
theorem sreClass1Count_of_datum_153_4 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 153) (hK : (class1SlopeDatum ctx).K₀ = 4) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 10 - 1) / 10) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 10)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_153_4.1
  have hcount : (class1Band4CycleBand ctx 10).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_153_4.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 10).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 10 - 1) / 10) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 10 - 1) / 10) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(153,8)`: period `10`, cycle `[103, 53, 59, 83, 13, 55, 67, 115, 77, 1]`, bands `[1, 2, 2, 1, 4, 2, 2, 1, 1, 8]` - band-4 residue set `{5}` (values `13`), `b4 = 1`. -/
private theorem sreCert_153_8 :
    slopeOrbit 153 8 (1 + 10) = slopeOrbit 153 8 1
      ∧ ∀ j, 1 ≤ j → j ≤ 10 →
          canonGap 153 (slopeOrbit 153 8 j) = 4 → j ∈ ({5} : Finset ℕ) := by
  have e0 : slopeOrbit 153 8 0 = 8 := rfl
  have e1 : slopeOrbit 153 8 1 = 103 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 153 8 2 = 53 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 153 8 3 = 59 :=
    slopeOrbit_step_eval 2 1 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 153 8 4 = 83 :=
    slopeOrbit_step_eval 3 1 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 153 8 5 = 13 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 153 8 6 = 55 :=
    slopeOrbit_step_eval 5 3 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 153 8 7 = 67 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 153 8 8 = 115 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 153 8 9 = 77 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 153 8 10 = 1 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 153 8 11 = 103 :=
    slopeOrbit_step_eval 10 7 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 153 8 11 = slopeOrbit 153 8 1
    rw [e11, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(153,8)`: the certified class-1 count cap `|fibre_1| <= 1 * ceil(W/10)`. -/
theorem sreClass1Count_of_datum_153_8 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 153) (hK : (class1SlopeDatum ctx).K₀ = 8) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 10 - 1) / 10) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 10)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_153_8.1
  have hcount : (class1Band4CycleBand ctx 10).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_153_8.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 10).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 10 - 1) / 10) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 10 - 1) / 10) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(153,25)`: period `14`, cycle `[47, 35, 127, 101, 49, 43, 19, 151, 149, 145, 137, 121, 89, 25]`, bands `[2, 3, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 1, 3]` - band-4 residue set `{7}` (values `19`), `b4 = 1`. -/
private theorem sreCert_153_25 :
    slopeOrbit 153 25 (1 + 14) = slopeOrbit 153 25 1
      ∧ ∀ j, 1 ≤ j → j ≤ 14 →
          canonGap 153 (slopeOrbit 153 25 j) = 4 → j ∈ ({7} : Finset ℕ) := by
  have e0 : slopeOrbit 153 25 0 = 25 := rfl
  have e1 : slopeOrbit 153 25 1 = 47 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 153 25 2 = 35 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 153 25 3 = 127 :=
    slopeOrbit_step_eval 2 2 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 153 25 4 = 101 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 153 25 5 = 49 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 153 25 6 = 43 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 153 25 7 = 19 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 153 25 8 = 151 :=
    slopeOrbit_step_eval 7 3 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 153 25 9 = 149 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 153 25 10 = 145 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 153 25 11 = 137 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 153 25 12 = 121 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 153 25 13 = 89 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 153 25 14 = 25 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 153 25 15 = 47 :=
    slopeOrbit_step_eval 14 2 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 153 25 15 = slopeOrbit 153 25 1
    rw [e15, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))

/-- `(153,25)`: the certified class-1 count cap `|fibre_1| <= 1 * ceil(W/14)`. -/
theorem sreClass1Count_of_datum_153_25 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 153) (hK : (class1SlopeDatum ctx).K₀ = 25) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 14 - 1) / 14) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 14)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_153_25.1
  have hcount : (class1Band4CycleBand ctx 14).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_153_25.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 14).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 14 - 1) / 14) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 14 - 1) / 14) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(153,76)`: period `14`, cycle `[151, 149, 145, 137, 121, 89, 25, 47, 35, 127, 101, 49, 43, 19]`, bands `[1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 4]` - band-4 residue set `{14}` (values `19`), `b4 = 1`. -/
private theorem sreCert_153_76 :
    slopeOrbit 153 76 (1 + 14) = slopeOrbit 153 76 1
      ∧ ∀ j, 1 ≤ j → j ≤ 14 →
          canonGap 153 (slopeOrbit 153 76 j) = 4 → j ∈ ({14} : Finset ℕ) := by
  have e0 : slopeOrbit 153 76 0 = 76 := rfl
  have e1 : slopeOrbit 153 76 1 = 151 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 153 76 2 = 149 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 153 76 3 = 145 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 153 76 4 = 137 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 153 76 5 = 121 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 153 76 6 = 89 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 153 76 7 = 25 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 153 76 8 = 47 :=
    slopeOrbit_step_eval 7 2 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 153 76 9 = 35 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 153 76 10 = 127 :=
    slopeOrbit_step_eval 9 2 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 153 76 11 = 101 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 153 76 12 = 49 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 153 76 13 = 43 :=
    slopeOrbit_step_eval 12 1 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 153 76 14 = 19 :=
    slopeOrbit_step_eval 13 1 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 153 76 15 = 151 :=
    slopeOrbit_step_eval 14 3 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 153 76 15 = slopeOrbit 153 76 1
    rw [e15, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide

/-- `(153,76)`: the certified class-1 count cap `|fibre_1| <= 1 * ceil(W/14)`. -/
theorem sreClass1Count_of_datum_153_76 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 153) (hK : (class1SlopeDatum ctx).K₀ = 76) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 14 - 1) / 14) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 14)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_153_76.1
  have hcount : (class1Band4CycleBand ctx 14).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_153_76.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 14).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 14 - 1) / 14) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 14 - 1) / 14) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(155,15)`: period `2`, cycle `[85, 15]`, bands `[1, 4]` - band-4 residue set `{2}` (values `15`), `b4 = 1`. -/
private theorem sreCert_155_15 :
    slopeOrbit 155 15 (1 + 2) = slopeOrbit 155 15 1
      ∧ ∀ j, 1 ≤ j → j ≤ 2 →
          canonGap 155 (slopeOrbit 155 15 j) = 4 → j ∈ ({2} : Finset ℕ) := by
  have e0 : slopeOrbit 155 15 0 = 15 := rfl
  have e1 : slopeOrbit 155 15 1 = 85 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 155 15 2 = 15 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 155 15 3 = 85 :=
    slopeOrbit_step_eval 2 3 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 155 15 3 = slopeOrbit 155 15 1
    rw [e3, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide

/-- `(155,15)`: the certified class-1 count cap `|fibre_1| <= 1 * ceil(W/2)`. -/
theorem sreClass1Count_of_datum_155_15 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 155) (hK : (class1SlopeDatum ctx).K₀ = 15) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 2 - 1) / 2) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 2)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_155_15.1
  have hcount : (class1Band4CycleBand ctx 2).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_155_15.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 2).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 2 - 1) / 2) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 2 - 1) / 2) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(159,1)`: period `21`, cycle `[97, 35, 121, 83, 7, 65, 101, 43, 13, 49, 37, 137, 115, 71, 125, 91, 23, 25, 41, 5, 1]`, bands `[1, 3, 1, 1, 5, 2, 1, 2, 4, 2, 3, 1, 1, 2, 1, 1, 3, 3, 2, 5, 8]` - band-4 residue set `{9}` (values `13`), `b4 = 1`. -/
private theorem sreCert_159_1 :
    slopeOrbit 159 1 (1 + 21) = slopeOrbit 159 1 1
      ∧ ∀ j, 1 ≤ j → j ≤ 21 →
          canonGap 159 (slopeOrbit 159 1 j) = 4 → j ∈ ({9} : Finset ℕ) := by
  have e0 : slopeOrbit 159 1 0 = 1 := rfl
  have e1 : slopeOrbit 159 1 1 = 97 :=
    slopeOrbit_step_eval 0 7 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 159 1 2 = 35 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 159 1 3 = 121 :=
    slopeOrbit_step_eval 2 2 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 159 1 4 = 83 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 159 1 5 = 7 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 159 1 6 = 65 :=
    slopeOrbit_step_eval 5 4 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 159 1 7 = 101 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 159 1 8 = 43 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 159 1 9 = 13 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 159 1 10 = 49 :=
    slopeOrbit_step_eval 9 3 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 159 1 11 = 37 :=
    slopeOrbit_step_eval 10 1 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 159 1 12 = 137 :=
    slopeOrbit_step_eval 11 2 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 159 1 13 = 115 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 159 1 14 = 71 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 159 1 15 = 125 :=
    slopeOrbit_step_eval 14 1 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 159 1 16 = 91 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 159 1 17 = 23 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 159 1 18 = 25 :=
    slopeOrbit_step_eval 17 2 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 159 1 19 = 41 :=
    slopeOrbit_step_eval 18 2 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 159 1 20 = 5 :=
    slopeOrbit_step_eval 19 1 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 159 1 21 = 1 :=
    slopeOrbit_step_eval 20 4 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 159 1 22 = 97 :=
    slopeOrbit_step_eval 21 7 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 159 1 22 = slopeOrbit 159 1 1
    rw [e22, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(159,1)`: the certified class-1 count cap `|fibre_1| <= 1 * ceil(W/21)`. -/
theorem sreClass1Count_of_datum_159_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 159) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 21 - 1) / 21) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 21)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_159_1.1
  have hcount : (class1Band4CycleBand ctx 21).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_159_1.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 21).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 21 - 1) / 21) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 21 - 1) / 21) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(159,26)`: period `21`, cycle `[49, 37, 137, 115, 71, 125, 91, 23, 25, 41, 5, 1, 97, 35, 121, 83, 7, 65, 101, 43, 13]`, bands `[2, 3, 1, 1, 2, 1, 1, 3, 3, 2, 5, 8, 1, 3, 1, 1, 5, 2, 1, 2, 4]` - band-4 residue set `{21}` (values `13`), `b4 = 1`. -/
private theorem sreCert_159_26 :
    slopeOrbit 159 26 (1 + 21) = slopeOrbit 159 26 1
      ∧ ∀ j, 1 ≤ j → j ≤ 21 →
          canonGap 159 (slopeOrbit 159 26 j) = 4 → j ∈ ({21} : Finset ℕ) := by
  have e0 : slopeOrbit 159 26 0 = 26 := rfl
  have e1 : slopeOrbit 159 26 1 = 49 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 159 26 2 = 37 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 159 26 3 = 137 :=
    slopeOrbit_step_eval 2 2 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 159 26 4 = 115 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 159 26 5 = 71 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 159 26 6 = 125 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 159 26 7 = 91 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 159 26 8 = 23 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 159 26 9 = 25 :=
    slopeOrbit_step_eval 8 2 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 159 26 10 = 41 :=
    slopeOrbit_step_eval 9 2 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 159 26 11 = 5 :=
    slopeOrbit_step_eval 10 1 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 159 26 12 = 1 :=
    slopeOrbit_step_eval 11 4 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 159 26 13 = 97 :=
    slopeOrbit_step_eval 12 7 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 159 26 14 = 35 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 159 26 15 = 121 :=
    slopeOrbit_step_eval 14 2 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 159 26 16 = 83 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 159 26 17 = 7 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 159 26 18 = 65 :=
    slopeOrbit_step_eval 17 4 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 159 26 19 = 101 :=
    slopeOrbit_step_eval 18 1 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 159 26 20 = 43 :=
    slopeOrbit_step_eval 19 0 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 159 26 21 = 13 :=
    slopeOrbit_step_eval 20 1 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 159 26 22 = 49 :=
    slopeOrbit_step_eval 21 3 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 159 26 22 = slopeOrbit 159 26 1
    rw [e22, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide

/-- `(159,26)`: the certified class-1 count cap `|fibre_1| <= 1 * ceil(W/21)`. -/
theorem sreClass1Count_of_datum_159_26 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 159) (hK : (class1SlopeDatum ctx).K₀ = 26) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 21 - 1) / 21) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 21)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_159_26.1
  have hcount : (class1Band4CycleBand ctx 21).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_159_26.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 21).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 21 - 1) / 21) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 21 - 1) / 21) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(159,79)`: period `31`, cycle `[157, 155, 151, 143, 127, 95, 31, 89, 19, 145, 131, 103, 47, 29, 73, 133, 107, 55, 61, 85, 11, 17, 113, 67, 109, 59, 77, 149, 139, 119, 79]`, bands `[1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 1, 2, 2, 1, 1, 1, 2]` - band-4 residue set `{9, 21, 22}` (values `19, 11, 17`), `b4 = 3`. -/
private theorem sreCert_159_79 :
    slopeOrbit 159 79 (1 + 31) = slopeOrbit 159 79 1
      ∧ ∀ j, 1 ≤ j → j ≤ 31 →
          canonGap 159 (slopeOrbit 159 79 j) = 4 → j ∈ ({9, 21, 22} : Finset ℕ) := by
  have e0 : slopeOrbit 159 79 0 = 79 := rfl
  have e1 : slopeOrbit 159 79 1 = 157 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 159 79 2 = 155 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 159 79 3 = 151 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 159 79 4 = 143 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 159 79 5 = 127 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 159 79 6 = 95 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 159 79 7 = 31 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 159 79 8 = 89 :=
    slopeOrbit_step_eval 7 2 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 159 79 9 = 19 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 159 79 10 = 145 :=
    slopeOrbit_step_eval 9 3 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 159 79 11 = 131 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 159 79 12 = 103 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 159 79 13 = 47 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 159 79 14 = 29 :=
    slopeOrbit_step_eval 13 1 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 159 79 15 = 73 :=
    slopeOrbit_step_eval 14 2 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 159 79 16 = 133 :=
    slopeOrbit_step_eval 15 1 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 159 79 17 = 107 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 159 79 18 = 55 :=
    slopeOrbit_step_eval 17 0 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 159 79 19 = 61 :=
    slopeOrbit_step_eval 18 1 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 159 79 20 = 85 :=
    slopeOrbit_step_eval 19 1 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 159 79 21 = 11 :=
    slopeOrbit_step_eval 20 0 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 159 79 22 = 17 :=
    slopeOrbit_step_eval 21 3 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 159 79 23 = 113 :=
    slopeOrbit_step_eval 22 3 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 159 79 24 = 67 :=
    slopeOrbit_step_eval 23 0 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 159 79 25 = 109 :=
    slopeOrbit_step_eval 24 1 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 159 79 26 = 59 :=
    slopeOrbit_step_eval 25 0 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 159 79 27 = 77 :=
    slopeOrbit_step_eval 26 1 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 159 79 28 = 149 :=
    slopeOrbit_step_eval 27 1 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 159 79 29 = 139 :=
    slopeOrbit_step_eval 28 0 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 159 79 30 = 119 :=
    slopeOrbit_step_eval 29 0 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : slopeOrbit 159 79 31 = 79 :=
    slopeOrbit_step_eval 30 0 e30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e32 : slopeOrbit 159 79 32 = 157 :=
    slopeOrbit_step_eval 31 1 e31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 159 79 32 = slopeOrbit 159 79 1
    rw [e32, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · decide
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e26] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e27] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e28] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e29] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e30] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e31] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))

/-- `(159,79)`: the certified class-1 count cap `|fibre_1| <= 3 * ceil(W/31)`. -/
theorem sreClass1Count_of_datum_159_79 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 159) (hK : (class1SlopeDatum ctx).K₀ = 79) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 3 * (((supportShell ctx.shell.d ctx.shell.X).card + 31 - 1) / 31) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 31)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_159_79.1
  have hcount : (class1Band4CycleBand ctx 31).card ≤ 3 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_159_79.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 31).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 31 - 1) / 31) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 3 * (((supportShell ctx.shell.d ctx.shell.X).card + 31 - 1) / 31) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(161,3)`: period `15`, cycle `[31, 87, 13, 47, 27, 55, 59, 75, 139, 117, 73, 131, 101, 41, 3]`, bands `[3, 1, 4, 2, 3, 2, 2, 2, 1, 1, 2, 1, 1, 2, 6]` - band-4 residue set `{3}` (values `13`), `b4 = 1`. -/
private theorem sreCert_161_3 :
    slopeOrbit 161 3 (1 + 15) = slopeOrbit 161 3 1
      ∧ ∀ j, 1 ≤ j → j ≤ 15 →
          canonGap 161 (slopeOrbit 161 3 j) = 4 → j ∈ ({3} : Finset ℕ) := by
  have e0 : slopeOrbit 161 3 0 = 3 := rfl
  have e1 : slopeOrbit 161 3 1 = 31 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 161 3 2 = 87 :=
    slopeOrbit_step_eval 1 2 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 161 3 3 = 13 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 161 3 4 = 47 :=
    slopeOrbit_step_eval 3 3 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 161 3 5 = 27 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 161 3 6 = 55 :=
    slopeOrbit_step_eval 5 2 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 161 3 7 = 59 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 161 3 8 = 75 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 161 3 9 = 139 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 161 3 10 = 117 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 161 3 11 = 73 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 161 3 12 = 131 :=
    slopeOrbit_step_eval 11 1 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 161 3 13 = 101 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 161 3 14 = 41 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 161 3 15 = 3 :=
    slopeOrbit_step_eval 14 1 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 161 3 16 = 31 :=
    slopeOrbit_step_eval 15 5 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 161 3 16 = slopeOrbit 161 3 1
    rw [e16, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(161,3)`: the certified class-1 count cap `|fibre_1| <= 1 * ceil(W/15)`. -/
theorem sreClass1Count_of_datum_161_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 161) (hK : (class1SlopeDatum ctx).K₀ = 3) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 15 - 1) / 15) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 15)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_161_3.1
  have hcount : (class1Band4CycleBand ctx 15).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_161_3.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 15).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 15 - 1) / 15) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 15 - 1) / 15) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(161,11)`: period `18`, cycle `[15, 79, 155, 149, 137, 113, 65, 99, 37, 135, 109, 57, 67, 107, 53, 51, 43, 11]`, bands `[4, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 2, 2, 2, 4]` - band-4 residue set `{1, 18}` (values `15, 11`), `b4 = 2`. -/
private theorem sreCert_161_11 :
    slopeOrbit 161 11 (1 + 18) = slopeOrbit 161 11 1
      ∧ ∀ j, 1 ≤ j → j ≤ 18 →
          canonGap 161 (slopeOrbit 161 11 j) = 4 → j ∈ ({1, 18} : Finset ℕ) := by
  have e0 : slopeOrbit 161 11 0 = 11 := rfl
  have e1 : slopeOrbit 161 11 1 = 15 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 161 11 2 = 79 :=
    slopeOrbit_step_eval 1 3 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 161 11 3 = 155 :=
    slopeOrbit_step_eval 2 1 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 161 11 4 = 149 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 161 11 5 = 137 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 161 11 6 = 113 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 161 11 7 = 65 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 161 11 8 = 99 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 161 11 9 = 37 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 161 11 10 = 135 :=
    slopeOrbit_step_eval 9 2 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 161 11 11 = 109 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 161 11 12 = 57 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 161 11 13 = 67 :=
    slopeOrbit_step_eval 12 1 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 161 11 14 = 107 :=
    slopeOrbit_step_eval 13 1 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 161 11 15 = 53 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 161 11 16 = 51 :=
    slopeOrbit_step_eval 15 1 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 161 11 17 = 43 :=
    slopeOrbit_step_eval 16 1 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 161 11 18 = 11 :=
    slopeOrbit_step_eval 17 1 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 161 11 19 = 15 :=
    slopeOrbit_step_eval 18 3 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 161 11 19 = slopeOrbit 161 11 1
    rw [e19, e1]
  · intro j h1 h2 hband
    interval_cases j
    · decide
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide

/-- `(161,11)`: the certified class-1 count cap `|fibre_1| <= 2 * ceil(W/18)`. -/
theorem sreClass1Count_of_datum_161_11 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 161) (hK : (class1SlopeDatum ctx).K₀ = 11) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 18 - 1) / 18) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 18)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_161_11.1
  have hcount : (class1Band4CycleBand ctx 18).card ≤ 2 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_161_11.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 18).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 18 - 1) / 18) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 18 - 1) / 18) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(161,80)`: period `18`, cycle `[159, 157, 153, 145, 129, 97, 33, 103, 45, 19, 143, 125, 89, 17, 111, 61, 83, 5]`, bands `[1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 4, 1, 2, 1, 6]` - band-4 residue set `{10, 14}` (values `19, 17`), `b4 = 2`. -/
private theorem sreCert_161_80 :
    slopeOrbit 161 80 (1 + 18) = slopeOrbit 161 80 1
      ∧ ∀ j, 1 ≤ j → j ≤ 18 →
          canonGap 161 (slopeOrbit 161 80 j) = 4 → j ∈ ({10, 14} : Finset ℕ) := by
  have e0 : slopeOrbit 161 80 0 = 80 := rfl
  have e1 : slopeOrbit 161 80 1 = 159 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 161 80 2 = 157 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 161 80 3 = 153 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 161 80 4 = 145 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 161 80 5 = 129 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 161 80 6 = 97 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 161 80 7 = 33 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 161 80 8 = 103 :=
    slopeOrbit_step_eval 7 2 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 161 80 9 = 45 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 161 80 10 = 19 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 161 80 11 = 143 :=
    slopeOrbit_step_eval 10 3 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 161 80 12 = 125 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 161 80 13 = 89 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 161 80 14 = 17 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 161 80 15 = 111 :=
    slopeOrbit_step_eval 14 3 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 161 80 16 = 61 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 161 80 17 = 83 :=
    slopeOrbit_step_eval 16 1 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 161 80 18 = 5 :=
    slopeOrbit_step_eval 17 0 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 161 80 19 = 159 :=
    slopeOrbit_step_eval 18 5 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 161 80 19 = slopeOrbit 161 80 1
    rw [e19, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(161,80)`: the certified class-1 count cap `|fibre_1| <= 2 * ceil(W/18)`. -/
theorem sreClass1Count_of_datum_161_80 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 161) (hK : (class1SlopeDatum ctx).K₀ = 80) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 18 - 1) / 18) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 18)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_161_80.1
  have hcount : (class1Band4CycleBand ctx 18).card ≤ 2 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_161_80.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 18).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 18 - 1) / 18) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 18 - 1) / 18) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(163,81)`: period `81`, cycle `[161, 159, 155, 147, 131, 99, 35, 117, 71, 121, 79, 153, 143, 123, 83, 3, 29, 69, 113, 63, 89, 15, 77, 145, 127, 91, 19, 141, 119, 75, 137, 111, 59, 73, 129, 95, 27, 53, 49, 33, 101, 39, 149, 135, 107, 51, 41, 1, 93, 23, 21, 5, 157, 151, 139, 115, 67, 105, 47, 25, 37, 133, 103, 43, 9, 125, 87, 11, 13, 45, 17, 109, 55, 57, 65, 97, 31, 85, 7, 61, 81]`, bands `[1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 1, 4, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 1, 2, 2, 8, 1, 3, 3, 6, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 5, 1, 1, 4, 4, 2, 4, 1, 2, 2, 2, 1, 3, 1, 5, 2, 2]` - band-4 residue set `{22, 27, 68, 69, 71}` (values `15, 19, 11, 13, 17`), `b4 = 5`. -/
private theorem sreCert_163_81 :
    slopeOrbit 163 81 (1 + 81) = slopeOrbit 163 81 1
      ∧ ∀ j, 1 ≤ j → j ≤ 81 →
          canonGap 163 (slopeOrbit 163 81 j) = 4 → j ∈ ({22, 27, 68, 69, 71} : Finset ℕ) := by
  have e0 : slopeOrbit 163 81 0 = 81 := rfl
  have e1 : slopeOrbit 163 81 1 = 161 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 163 81 2 = 159 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 163 81 3 = 155 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 163 81 4 = 147 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 163 81 5 = 131 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 163 81 6 = 99 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 163 81 7 = 35 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 163 81 8 = 117 :=
    slopeOrbit_step_eval 7 2 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 163 81 9 = 71 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 163 81 10 = 121 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 163 81 11 = 79 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 163 81 12 = 153 :=
    slopeOrbit_step_eval 11 1 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 163 81 13 = 143 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 163 81 14 = 123 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 163 81 15 = 83 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 163 81 16 = 3 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 163 81 17 = 29 :=
    slopeOrbit_step_eval 16 5 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 163 81 18 = 69 :=
    slopeOrbit_step_eval 17 2 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 163 81 19 = 113 :=
    slopeOrbit_step_eval 18 1 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 163 81 20 = 63 :=
    slopeOrbit_step_eval 19 0 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 163 81 21 = 89 :=
    slopeOrbit_step_eval 20 1 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 163 81 22 = 15 :=
    slopeOrbit_step_eval 21 0 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 163 81 23 = 77 :=
    slopeOrbit_step_eval 22 3 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 163 81 24 = 145 :=
    slopeOrbit_step_eval 23 1 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 163 81 25 = 127 :=
    slopeOrbit_step_eval 24 0 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 163 81 26 = 91 :=
    slopeOrbit_step_eval 25 0 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 163 81 27 = 19 :=
    slopeOrbit_step_eval 26 0 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 163 81 28 = 141 :=
    slopeOrbit_step_eval 27 3 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 163 81 29 = 119 :=
    slopeOrbit_step_eval 28 0 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 163 81 30 = 75 :=
    slopeOrbit_step_eval 29 0 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : slopeOrbit 163 81 31 = 137 :=
    slopeOrbit_step_eval 30 1 e30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e32 : slopeOrbit 163 81 32 = 111 :=
    slopeOrbit_step_eval 31 0 e31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e33 : slopeOrbit 163 81 33 = 59 :=
    slopeOrbit_step_eval 32 0 e32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e34 : slopeOrbit 163 81 34 = 73 :=
    slopeOrbit_step_eval 33 1 e33 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e35 : slopeOrbit 163 81 35 = 129 :=
    slopeOrbit_step_eval 34 1 e34 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e36 : slopeOrbit 163 81 36 = 95 :=
    slopeOrbit_step_eval 35 0 e35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e37 : slopeOrbit 163 81 37 = 27 :=
    slopeOrbit_step_eval 36 0 e36 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e38 : slopeOrbit 163 81 38 = 53 :=
    slopeOrbit_step_eval 37 2 e37 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e39 : slopeOrbit 163 81 39 = 49 :=
    slopeOrbit_step_eval 38 1 e38 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e40 : slopeOrbit 163 81 40 = 33 :=
    slopeOrbit_step_eval 39 1 e39 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e41 : slopeOrbit 163 81 41 = 101 :=
    slopeOrbit_step_eval 40 2 e40 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e42 : slopeOrbit 163 81 42 = 39 :=
    slopeOrbit_step_eval 41 0 e41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e43 : slopeOrbit 163 81 43 = 149 :=
    slopeOrbit_step_eval 42 2 e42 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e44 : slopeOrbit 163 81 44 = 135 :=
    slopeOrbit_step_eval 43 0 e43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e45 : slopeOrbit 163 81 45 = 107 :=
    slopeOrbit_step_eval 44 0 e44 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e46 : slopeOrbit 163 81 46 = 51 :=
    slopeOrbit_step_eval 45 0 e45 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e47 : slopeOrbit 163 81 47 = 41 :=
    slopeOrbit_step_eval 46 1 e46 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e48 : slopeOrbit 163 81 48 = 1 :=
    slopeOrbit_step_eval 47 1 e47 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e49 : slopeOrbit 163 81 49 = 93 :=
    slopeOrbit_step_eval 48 7 e48 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e50 : slopeOrbit 163 81 50 = 23 :=
    slopeOrbit_step_eval 49 0 e49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e51 : slopeOrbit 163 81 51 = 21 :=
    slopeOrbit_step_eval 50 2 e50 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e52 : slopeOrbit 163 81 52 = 5 :=
    slopeOrbit_step_eval 51 2 e51 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e53 : slopeOrbit 163 81 53 = 157 :=
    slopeOrbit_step_eval 52 5 e52 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e54 : slopeOrbit 163 81 54 = 151 :=
    slopeOrbit_step_eval 53 0 e53 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e55 : slopeOrbit 163 81 55 = 139 :=
    slopeOrbit_step_eval 54 0 e54 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e56 : slopeOrbit 163 81 56 = 115 :=
    slopeOrbit_step_eval 55 0 e55 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e57 : slopeOrbit 163 81 57 = 67 :=
    slopeOrbit_step_eval 56 0 e56 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e58 : slopeOrbit 163 81 58 = 105 :=
    slopeOrbit_step_eval 57 1 e57 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e59 : slopeOrbit 163 81 59 = 47 :=
    slopeOrbit_step_eval 58 0 e58 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e60 : slopeOrbit 163 81 60 = 25 :=
    slopeOrbit_step_eval 59 1 e59 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e61 : slopeOrbit 163 81 61 = 37 :=
    slopeOrbit_step_eval 60 2 e60 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e62 : slopeOrbit 163 81 62 = 133 :=
    slopeOrbit_step_eval 61 2 e61 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e63 : slopeOrbit 163 81 63 = 103 :=
    slopeOrbit_step_eval 62 0 e62 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e64 : slopeOrbit 163 81 64 = 43 :=
    slopeOrbit_step_eval 63 0 e63 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e65 : slopeOrbit 163 81 65 = 9 :=
    slopeOrbit_step_eval 64 1 e64 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e66 : slopeOrbit 163 81 66 = 125 :=
    slopeOrbit_step_eval 65 4 e65 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e67 : slopeOrbit 163 81 67 = 87 :=
    slopeOrbit_step_eval 66 0 e66 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e68 : slopeOrbit 163 81 68 = 11 :=
    slopeOrbit_step_eval 67 0 e67 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e69 : slopeOrbit 163 81 69 = 13 :=
    slopeOrbit_step_eval 68 3 e68 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e70 : slopeOrbit 163 81 70 = 45 :=
    slopeOrbit_step_eval 69 3 e69 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e71 : slopeOrbit 163 81 71 = 17 :=
    slopeOrbit_step_eval 70 1 e70 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e72 : slopeOrbit 163 81 72 = 109 :=
    slopeOrbit_step_eval 71 3 e71 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e73 : slopeOrbit 163 81 73 = 55 :=
    slopeOrbit_step_eval 72 0 e72 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e74 : slopeOrbit 163 81 74 = 57 :=
    slopeOrbit_step_eval 73 1 e73 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e75 : slopeOrbit 163 81 75 = 65 :=
    slopeOrbit_step_eval 74 1 e74 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e76 : slopeOrbit 163 81 76 = 97 :=
    slopeOrbit_step_eval 75 1 e75 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e77 : slopeOrbit 163 81 77 = 31 :=
    slopeOrbit_step_eval 76 0 e76 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e78 : slopeOrbit 163 81 78 = 85 :=
    slopeOrbit_step_eval 77 2 e77 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e79 : slopeOrbit 163 81 79 = 7 :=
    slopeOrbit_step_eval 78 0 e78 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e80 : slopeOrbit 163 81 80 = 61 :=
    slopeOrbit_step_eval 79 4 e79 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e81 : slopeOrbit 163 81 81 = 81 :=
    slopeOrbit_step_eval 80 1 e80 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e82 : slopeOrbit 163 81 82 = 161 :=
    slopeOrbit_step_eval 81 1 e81 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 163 81 82 = slopeOrbit 163 81 1
    rw [e82, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e26] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e28] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e29] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e30] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e31] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e32] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e33] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e34] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e35] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e36] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e37] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e38] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e39] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e40] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e41] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e42] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e43] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e44] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e45] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e46] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e47] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e48] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e49] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e50] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e51] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e52] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e53] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e54] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e55] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e56] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e57] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e58] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e59] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e60] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e61] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e62] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e63] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e64] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e65] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e66] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e67] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · decide
    · rw [e70] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e72] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e73] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e74] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e75] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e76] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e77] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e78] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e79] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e80] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e81] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))

/-- `(163,81)`: the certified class-1 count cap `|fibre_1| <= 5 * ceil(W/81)`. -/
theorem sreClass1Count_of_datum_163_81 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 163) (hK : (class1SlopeDatum ctx).K₀ = 81) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 5 * (((supportShell ctx.shell.d ctx.shell.X).card + 81 - 1) / 81) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 81)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_163_81.1
  have hcount : (class1Band4CycleBand ctx 81).card ≤ 5 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_163_81.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 81).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 81 - 1) / 81) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 5 * (((supportShell ctx.shell.d ctx.shell.X).card + 81 - 1) / 81) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(165,1)`: period `7`, cycle `[91, 17, 107, 49, 31, 83, 1]`, bands `[1, 4, 1, 2, 3, 1, 8]` - band-4 residue set `{2}` (values `17`), `b4 = 1`. -/
private theorem sreCert_165_1 :
    slopeOrbit 165 1 (1 + 7) = slopeOrbit 165 1 1
      ∧ ∀ j, 1 ≤ j → j ≤ 7 →
          canonGap 165 (slopeOrbit 165 1 j) = 4 → j ∈ ({2} : Finset ℕ) := by
  have e0 : slopeOrbit 165 1 0 = 1 := rfl
  have e1 : slopeOrbit 165 1 1 = 91 :=
    slopeOrbit_step_eval 0 7 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 165 1 2 = 17 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 165 1 3 = 107 :=
    slopeOrbit_step_eval 2 3 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 165 1 4 = 49 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 165 1 5 = 31 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 165 1 6 = 83 :=
    slopeOrbit_step_eval 5 2 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 165 1 7 = 1 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 165 1 8 = 91 :=
    slopeOrbit_step_eval 7 7 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 165 1 8 = slopeOrbit 165 1 1
    rw [e8, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(165,1)`: the certified class-1 count cap `|fibre_1| <= 1 * ceil(W/7)`. -/
theorem sreClass1Count_of_datum_165_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 165) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 7 - 1) / 7) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 7)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_165_1.1
  have hcount : (class1Band4CycleBand ctx 7).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_165_1.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 7).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 7 - 1) / 7) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 7 - 1) / 7) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(165,2)`: period `7`, cycle `[91, 17, 107, 49, 31, 83, 1]`, bands `[1, 4, 1, 2, 3, 1, 8]` - band-4 residue set `{2}` (values `17`), `b4 = 1`. -/
private theorem sreCert_165_2 :
    slopeOrbit 165 2 (1 + 7) = slopeOrbit 165 2 1
      ∧ ∀ j, 1 ≤ j → j ≤ 7 →
          canonGap 165 (slopeOrbit 165 2 j) = 4 → j ∈ ({2} : Finset ℕ) := by
  have e0 : slopeOrbit 165 2 0 = 2 := rfl
  have e1 : slopeOrbit 165 2 1 = 91 :=
    slopeOrbit_step_eval 0 6 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 165 2 2 = 17 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 165 2 3 = 107 :=
    slopeOrbit_step_eval 2 3 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 165 2 4 = 49 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 165 2 5 = 31 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 165 2 6 = 83 :=
    slopeOrbit_step_eval 5 2 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 165 2 7 = 1 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 165 2 8 = 91 :=
    slopeOrbit_step_eval 7 7 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 165 2 8 = slopeOrbit 165 2 1
    rw [e8, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(165,2)`: the certified class-1 count cap `|fibre_1| <= 1 * ceil(W/7)`. -/
theorem sreClass1Count_of_datum_165_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 165) (hK : (class1SlopeDatum ctx).K₀ = 2) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 7 - 1) / 7) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 7)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_165_2.1
  have hcount : (class1Band4CycleBand ctx 7).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_165_2.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 7).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 7 - 1) / 7) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 7 - 1) / 7) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(165,7)`: period `9`, cycle `[59, 71, 119, 73, 127, 89, 13, 43, 7]`, bands `[2, 2, 1, 2, 1, 1, 4, 2, 5]` - band-4 residue set `{7}` (values `13`), `b4 = 1`. -/
private theorem sreCert_165_7 :
    slopeOrbit 165 7 (1 + 9) = slopeOrbit 165 7 1
      ∧ ∀ j, 1 ≤ j → j ≤ 9 →
          canonGap 165 (slopeOrbit 165 7 j) = 4 → j ∈ ({7} : Finset ℕ) := by
  have e0 : slopeOrbit 165 7 0 = 7 := rfl
  have e1 : slopeOrbit 165 7 1 = 59 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 165 7 2 = 71 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 165 7 3 = 119 :=
    slopeOrbit_step_eval 2 1 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 165 7 4 = 73 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 165 7 5 = 127 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 165 7 6 = 89 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 165 7 7 = 13 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 165 7 8 = 43 :=
    slopeOrbit_step_eval 7 3 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 165 7 9 = 7 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 165 7 10 = 59 :=
    slopeOrbit_step_eval 9 4 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 165 7 10 = slopeOrbit 165 7 1
    rw [e10, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(165,7)`: the certified class-1 count cap `|fibre_1| <= 1 * ceil(W/9)`. -/
theorem sreClass1Count_of_datum_165_7 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 165) (hK : (class1SlopeDatum ctx).K₀ = 7) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 9 - 1) / 9) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 9)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_165_7.1
  have hcount : (class1Band4CycleBand ctx 9).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_165_7.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 9).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 9 - 1) / 9) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 9 - 1) / 9) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(165,16)`: period `7`, cycle `[91, 17, 107, 49, 31, 83, 1]`, bands `[1, 4, 1, 2, 3, 1, 8]` - band-4 residue set `{2}` (values `17`), `b4 = 1`. -/
private theorem sreCert_165_16 :
    slopeOrbit 165 16 (1 + 7) = slopeOrbit 165 16 1
      ∧ ∀ j, 1 ≤ j → j ≤ 7 →
          canonGap 165 (slopeOrbit 165 16 j) = 4 → j ∈ ({2} : Finset ℕ) := by
  have e0 : slopeOrbit 165 16 0 = 16 := rfl
  have e1 : slopeOrbit 165 16 1 = 91 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 165 16 2 = 17 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 165 16 3 = 107 :=
    slopeOrbit_step_eval 2 3 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 165 16 4 = 49 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 165 16 5 = 31 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 165 16 6 = 83 :=
    slopeOrbit_step_eval 5 2 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 165 16 7 = 1 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 165 16 8 = 91 :=
    slopeOrbit_step_eval 7 7 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 165 16 8 = slopeOrbit 165 16 1
    rw [e8, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(165,16)`: the certified class-1 count cap `|fibre_1| <= 1 * ceil(W/7)`. -/
theorem sreClass1Count_of_datum_165_16 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 165) (hK : (class1SlopeDatum ctx).K₀ = 16) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 7 - 1) / 7) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 7)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_165_16.1
  have hcount : (class1Band4CycleBand ctx 7).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_165_16.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 7).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 7 - 1) / 7) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 7 - 1) / 7) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(167,83)`: period `47`, cycle `[165, 163, 159, 151, 135, 103, 39, 145, 123, 79, 149, 131, 95, 23, 17, 105, 43, 5, 153, 139, 111, 55, 53, 45, 13, 41, 161, 155, 143, 119, 71, 117, 67, 101, 35, 113, 59, 69, 109, 51, 37, 129, 91, 15, 73, 125, 83]`, bands `[1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 6, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 1, 2, 3, 1, 1, 4, 2, 1, 2]` - band-4 residue set `{15, 25, 44}` (values `17, 13, 15`), `b4 = 3`. -/
private theorem sreCert_167_83 :
    slopeOrbit 167 83 (1 + 47) = slopeOrbit 167 83 1
      ∧ ∀ j, 1 ≤ j → j ≤ 47 →
          canonGap 167 (slopeOrbit 167 83 j) = 4 → j ∈ ({15, 25, 44} : Finset ℕ) := by
  have e0 : slopeOrbit 167 83 0 = 83 := rfl
  have e1 : slopeOrbit 167 83 1 = 165 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 167 83 2 = 163 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 167 83 3 = 159 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 167 83 4 = 151 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 167 83 5 = 135 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 167 83 6 = 103 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 167 83 7 = 39 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 167 83 8 = 145 :=
    slopeOrbit_step_eval 7 2 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 167 83 9 = 123 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 167 83 10 = 79 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 167 83 11 = 149 :=
    slopeOrbit_step_eval 10 1 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 167 83 12 = 131 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 167 83 13 = 95 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 167 83 14 = 23 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 167 83 15 = 17 :=
    slopeOrbit_step_eval 14 2 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 167 83 16 = 105 :=
    slopeOrbit_step_eval 15 3 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 167 83 17 = 43 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 167 83 18 = 5 :=
    slopeOrbit_step_eval 17 1 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 167 83 19 = 153 :=
    slopeOrbit_step_eval 18 5 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 167 83 20 = 139 :=
    slopeOrbit_step_eval 19 0 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 167 83 21 = 111 :=
    slopeOrbit_step_eval 20 0 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 167 83 22 = 55 :=
    slopeOrbit_step_eval 21 0 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 167 83 23 = 53 :=
    slopeOrbit_step_eval 22 1 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 167 83 24 = 45 :=
    slopeOrbit_step_eval 23 1 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 167 83 25 = 13 :=
    slopeOrbit_step_eval 24 1 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 167 83 26 = 41 :=
    slopeOrbit_step_eval 25 3 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 167 83 27 = 161 :=
    slopeOrbit_step_eval 26 2 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 167 83 28 = 155 :=
    slopeOrbit_step_eval 27 0 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 167 83 29 = 143 :=
    slopeOrbit_step_eval 28 0 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 167 83 30 = 119 :=
    slopeOrbit_step_eval 29 0 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : slopeOrbit 167 83 31 = 71 :=
    slopeOrbit_step_eval 30 0 e30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e32 : slopeOrbit 167 83 32 = 117 :=
    slopeOrbit_step_eval 31 1 e31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e33 : slopeOrbit 167 83 33 = 67 :=
    slopeOrbit_step_eval 32 0 e32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e34 : slopeOrbit 167 83 34 = 101 :=
    slopeOrbit_step_eval 33 1 e33 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e35 : slopeOrbit 167 83 35 = 35 :=
    slopeOrbit_step_eval 34 0 e34 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e36 : slopeOrbit 167 83 36 = 113 :=
    slopeOrbit_step_eval 35 2 e35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e37 : slopeOrbit 167 83 37 = 59 :=
    slopeOrbit_step_eval 36 0 e36 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e38 : slopeOrbit 167 83 38 = 69 :=
    slopeOrbit_step_eval 37 1 e37 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e39 : slopeOrbit 167 83 39 = 109 :=
    slopeOrbit_step_eval 38 1 e38 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e40 : slopeOrbit 167 83 40 = 51 :=
    slopeOrbit_step_eval 39 0 e39 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e41 : slopeOrbit 167 83 41 = 37 :=
    slopeOrbit_step_eval 40 1 e40 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e42 : slopeOrbit 167 83 42 = 129 :=
    slopeOrbit_step_eval 41 2 e41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e43 : slopeOrbit 167 83 43 = 91 :=
    slopeOrbit_step_eval 42 0 e42 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e44 : slopeOrbit 167 83 44 = 15 :=
    slopeOrbit_step_eval 43 0 e43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e45 : slopeOrbit 167 83 45 = 73 :=
    slopeOrbit_step_eval 44 3 e44 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e46 : slopeOrbit 167 83 46 = 125 :=
    slopeOrbit_step_eval 45 1 e45 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e47 : slopeOrbit 167 83 47 = 83 :=
    slopeOrbit_step_eval 46 0 e46 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e48 : slopeOrbit 167 83 48 = 165 :=
    slopeOrbit_step_eval 47 1 e47 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 167 83 48 = slopeOrbit 167 83 1
    rw [e48, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e26] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e27] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e28] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e29] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e30] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e31] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e32] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e33] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e34] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e35] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e36] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e37] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e38] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e39] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e40] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e41] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e42] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e43] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e45] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e46] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e47] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))

/-- `(167,83)`: the certified class-1 count cap `|fibre_1| <= 3 * ceil(W/47)`. -/
theorem sreClass1Count_of_datum_167_83 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 167) (hK : (class1SlopeDatum ctx).K₀ = 83) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 3 * (((supportShell ctx.shell.d ctx.shell.X).card + 47 - 1) / 47) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 47)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_167_83.1
  have hcount : (class1Band4CycleBand ctx 47).card ≤ 3 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_167_83.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 47).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 47 - 1) / 47) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 3 * (((supportShell ctx.shell.d ctx.shell.X).card + 47 - 1) / 47) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(169,6)`: period `78`, cycle `[23, 15, 71, 115, 61, 75, 131, 93, 17, 103, 37, 127, 85, 1, 87, 5, 151, 133, 97, 25, 31, 79, 147, 125, 81, 155, 141, 113, 57, 59, 67, 99, 29, 63, 83, 163, 157, 145, 121, 73, 123, 77, 139, 109, 49, 27, 47, 19, 135, 101, 33, 95, 21, 167, 165, 161, 153, 137, 105, 41, 159, 149, 129, 89, 9, 119, 69, 107, 45, 11, 7, 55, 51, 35, 111, 53, 43, 3]`, bands `[3, 4, 2, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 8, 1, 6, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 1, 2, 4, 5, 2, 2, 3, 1, 2, 2, 6]` - band-4 residue set `{2, 9, 48, 53, 70}` (values `15, 17, 19, 21, 11`), `b4 = 5`. -/
private theorem sreCert_169_6 :
    slopeOrbit 169 6 (1 + 78) = slopeOrbit 169 6 1
      ∧ ∀ j, 1 ≤ j → j ≤ 78 →
          canonGap 169 (slopeOrbit 169 6 j) = 4 → j ∈ ({2, 9, 48, 53, 70} : Finset ℕ) := by
  have e0 : slopeOrbit 169 6 0 = 6 := rfl
  have e1 : slopeOrbit 169 6 1 = 23 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 169 6 2 = 15 :=
    slopeOrbit_step_eval 1 2 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 169 6 3 = 71 :=
    slopeOrbit_step_eval 2 3 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 169 6 4 = 115 :=
    slopeOrbit_step_eval 3 1 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 169 6 5 = 61 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 169 6 6 = 75 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 169 6 7 = 131 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 169 6 8 = 93 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 169 6 9 = 17 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 169 6 10 = 103 :=
    slopeOrbit_step_eval 9 3 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 169 6 11 = 37 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 169 6 12 = 127 :=
    slopeOrbit_step_eval 11 2 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 169 6 13 = 85 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 169 6 14 = 1 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 169 6 15 = 87 :=
    slopeOrbit_step_eval 14 7 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 169 6 16 = 5 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 169 6 17 = 151 :=
    slopeOrbit_step_eval 16 5 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 169 6 18 = 133 :=
    slopeOrbit_step_eval 17 0 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 169 6 19 = 97 :=
    slopeOrbit_step_eval 18 0 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 169 6 20 = 25 :=
    slopeOrbit_step_eval 19 0 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 169 6 21 = 31 :=
    slopeOrbit_step_eval 20 2 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 169 6 22 = 79 :=
    slopeOrbit_step_eval 21 2 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 169 6 23 = 147 :=
    slopeOrbit_step_eval 22 1 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 169 6 24 = 125 :=
    slopeOrbit_step_eval 23 0 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 169 6 25 = 81 :=
    slopeOrbit_step_eval 24 0 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 169 6 26 = 155 :=
    slopeOrbit_step_eval 25 1 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 169 6 27 = 141 :=
    slopeOrbit_step_eval 26 0 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 169 6 28 = 113 :=
    slopeOrbit_step_eval 27 0 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 169 6 29 = 57 :=
    slopeOrbit_step_eval 28 0 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 169 6 30 = 59 :=
    slopeOrbit_step_eval 29 1 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : slopeOrbit 169 6 31 = 67 :=
    slopeOrbit_step_eval 30 1 e30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e32 : slopeOrbit 169 6 32 = 99 :=
    slopeOrbit_step_eval 31 1 e31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e33 : slopeOrbit 169 6 33 = 29 :=
    slopeOrbit_step_eval 32 0 e32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e34 : slopeOrbit 169 6 34 = 63 :=
    slopeOrbit_step_eval 33 2 e33 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e35 : slopeOrbit 169 6 35 = 83 :=
    slopeOrbit_step_eval 34 1 e34 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e36 : slopeOrbit 169 6 36 = 163 :=
    slopeOrbit_step_eval 35 1 e35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e37 : slopeOrbit 169 6 37 = 157 :=
    slopeOrbit_step_eval 36 0 e36 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e38 : slopeOrbit 169 6 38 = 145 :=
    slopeOrbit_step_eval 37 0 e37 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e39 : slopeOrbit 169 6 39 = 121 :=
    slopeOrbit_step_eval 38 0 e38 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e40 : slopeOrbit 169 6 40 = 73 :=
    slopeOrbit_step_eval 39 0 e39 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e41 : slopeOrbit 169 6 41 = 123 :=
    slopeOrbit_step_eval 40 1 e40 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e42 : slopeOrbit 169 6 42 = 77 :=
    slopeOrbit_step_eval 41 0 e41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e43 : slopeOrbit 169 6 43 = 139 :=
    slopeOrbit_step_eval 42 1 e42 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e44 : slopeOrbit 169 6 44 = 109 :=
    slopeOrbit_step_eval 43 0 e43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e45 : slopeOrbit 169 6 45 = 49 :=
    slopeOrbit_step_eval 44 0 e44 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e46 : slopeOrbit 169 6 46 = 27 :=
    slopeOrbit_step_eval 45 1 e45 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e47 : slopeOrbit 169 6 47 = 47 :=
    slopeOrbit_step_eval 46 2 e46 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e48 : slopeOrbit 169 6 48 = 19 :=
    slopeOrbit_step_eval 47 1 e47 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e49 : slopeOrbit 169 6 49 = 135 :=
    slopeOrbit_step_eval 48 3 e48 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e50 : slopeOrbit 169 6 50 = 101 :=
    slopeOrbit_step_eval 49 0 e49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e51 : slopeOrbit 169 6 51 = 33 :=
    slopeOrbit_step_eval 50 0 e50 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e52 : slopeOrbit 169 6 52 = 95 :=
    slopeOrbit_step_eval 51 2 e51 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e53 : slopeOrbit 169 6 53 = 21 :=
    slopeOrbit_step_eval 52 0 e52 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e54 : slopeOrbit 169 6 54 = 167 :=
    slopeOrbit_step_eval 53 3 e53 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e55 : slopeOrbit 169 6 55 = 165 :=
    slopeOrbit_step_eval 54 0 e54 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e56 : slopeOrbit 169 6 56 = 161 :=
    slopeOrbit_step_eval 55 0 e55 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e57 : slopeOrbit 169 6 57 = 153 :=
    slopeOrbit_step_eval 56 0 e56 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e58 : slopeOrbit 169 6 58 = 137 :=
    slopeOrbit_step_eval 57 0 e57 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e59 : slopeOrbit 169 6 59 = 105 :=
    slopeOrbit_step_eval 58 0 e58 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e60 : slopeOrbit 169 6 60 = 41 :=
    slopeOrbit_step_eval 59 0 e59 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e61 : slopeOrbit 169 6 61 = 159 :=
    slopeOrbit_step_eval 60 2 e60 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e62 : slopeOrbit 169 6 62 = 149 :=
    slopeOrbit_step_eval 61 0 e61 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e63 : slopeOrbit 169 6 63 = 129 :=
    slopeOrbit_step_eval 62 0 e62 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e64 : slopeOrbit 169 6 64 = 89 :=
    slopeOrbit_step_eval 63 0 e63 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e65 : slopeOrbit 169 6 65 = 9 :=
    slopeOrbit_step_eval 64 0 e64 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e66 : slopeOrbit 169 6 66 = 119 :=
    slopeOrbit_step_eval 65 4 e65 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e67 : slopeOrbit 169 6 67 = 69 :=
    slopeOrbit_step_eval 66 0 e66 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e68 : slopeOrbit 169 6 68 = 107 :=
    slopeOrbit_step_eval 67 1 e67 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e69 : slopeOrbit 169 6 69 = 45 :=
    slopeOrbit_step_eval 68 0 e68 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e70 : slopeOrbit 169 6 70 = 11 :=
    slopeOrbit_step_eval 69 1 e69 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e71 : slopeOrbit 169 6 71 = 7 :=
    slopeOrbit_step_eval 70 3 e70 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e72 : slopeOrbit 169 6 72 = 55 :=
    slopeOrbit_step_eval 71 4 e71 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e73 : slopeOrbit 169 6 73 = 51 :=
    slopeOrbit_step_eval 72 1 e72 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e74 : slopeOrbit 169 6 74 = 35 :=
    slopeOrbit_step_eval 73 1 e73 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e75 : slopeOrbit 169 6 75 = 111 :=
    slopeOrbit_step_eval 74 2 e74 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e76 : slopeOrbit 169 6 76 = 53 :=
    slopeOrbit_step_eval 75 0 e75 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e77 : slopeOrbit 169 6 77 = 43 :=
    slopeOrbit_step_eval 76 1 e76 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e78 : slopeOrbit 169 6 78 = 3 :=
    slopeOrbit_step_eval 77 1 e77 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e79 : slopeOrbit 169 6 79 = 23 :=
    slopeOrbit_step_eval 78 5 e78 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 169 6 79 = slopeOrbit 169 6 1
    rw [e79, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e26] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e27] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e28] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e29] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e30] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e31] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e32] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e33] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e34] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e35] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e36] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e37] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e38] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e39] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e40] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e41] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e42] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e43] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e44] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e45] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e46] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e47] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e49] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e50] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e51] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e52] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e54] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e55] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e56] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e57] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e58] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e59] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e60] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e61] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e62] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e63] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e64] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e65] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e66] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e67] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e68] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e69] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e71] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e72] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e73] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e74] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e75] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e76] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e77] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e78] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(169,6)`: the certified class-1 count cap `|fibre_1| <= 5 * ceil(W/78)`. -/
theorem sreClass1Count_of_datum_169_6 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 169) (hK : (class1SlopeDatum ctx).K₀ = 6) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 5 * (((supportShell ctx.shell.d ctx.shell.X).card + 78 - 1) / 78) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 78)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_169_6.1
  have hcount : (class1Band4CycleBand ctx 78).card ≤ 5 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_169_6.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 78).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 78 - 1) / 78) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 5 * (((supportShell ctx.shell.d ctx.shell.X).card + 78 - 1) / 78) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(169,84)`: period `78`, cycle `[167, 165, 161, 153, 137, 105, 41, 159, 149, 129, 89, 9, 119, 69, 107, 45, 11, 7, 55, 51, 35, 111, 53, 43, 3, 23, 15, 71, 115, 61, 75, 131, 93, 17, 103, 37, 127, 85, 1, 87, 5, 151, 133, 97, 25, 31, 79, 147, 125, 81, 155, 141, 113, 57, 59, 67, 99, 29, 63, 83, 163, 157, 145, 121, 73, 123, 77, 139, 109, 49, 27, 47, 19, 135, 101, 33, 95, 21]`, bands `[1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 1, 2, 4, 5, 2, 2, 3, 1, 2, 2, 6, 3, 4, 2, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 8, 1, 6, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 1, 4]` - band-4 residue set `{17, 27, 34, 73, 78}` (values `11, 15, 17, 19, 21`), `b4 = 5`. -/
private theorem sreCert_169_84 :
    slopeOrbit 169 84 (1 + 78) = slopeOrbit 169 84 1
      ∧ ∀ j, 1 ≤ j → j ≤ 78 →
          canonGap 169 (slopeOrbit 169 84 j) = 4 → j ∈ ({17, 27, 34, 73, 78} : Finset ℕ) := by
  have e0 : slopeOrbit 169 84 0 = 84 := rfl
  have e1 : slopeOrbit 169 84 1 = 167 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 169 84 2 = 165 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 169 84 3 = 161 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 169 84 4 = 153 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 169 84 5 = 137 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 169 84 6 = 105 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 169 84 7 = 41 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 169 84 8 = 159 :=
    slopeOrbit_step_eval 7 2 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 169 84 9 = 149 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 169 84 10 = 129 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 169 84 11 = 89 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 169 84 12 = 9 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 169 84 13 = 119 :=
    slopeOrbit_step_eval 12 4 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 169 84 14 = 69 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 169 84 15 = 107 :=
    slopeOrbit_step_eval 14 1 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 169 84 16 = 45 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 169 84 17 = 11 :=
    slopeOrbit_step_eval 16 1 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 169 84 18 = 7 :=
    slopeOrbit_step_eval 17 3 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 169 84 19 = 55 :=
    slopeOrbit_step_eval 18 4 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 169 84 20 = 51 :=
    slopeOrbit_step_eval 19 1 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 169 84 21 = 35 :=
    slopeOrbit_step_eval 20 1 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 169 84 22 = 111 :=
    slopeOrbit_step_eval 21 2 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 169 84 23 = 53 :=
    slopeOrbit_step_eval 22 0 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 169 84 24 = 43 :=
    slopeOrbit_step_eval 23 1 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 169 84 25 = 3 :=
    slopeOrbit_step_eval 24 1 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 169 84 26 = 23 :=
    slopeOrbit_step_eval 25 5 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 169 84 27 = 15 :=
    slopeOrbit_step_eval 26 2 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 169 84 28 = 71 :=
    slopeOrbit_step_eval 27 3 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 169 84 29 = 115 :=
    slopeOrbit_step_eval 28 1 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 169 84 30 = 61 :=
    slopeOrbit_step_eval 29 0 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : slopeOrbit 169 84 31 = 75 :=
    slopeOrbit_step_eval 30 1 e30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e32 : slopeOrbit 169 84 32 = 131 :=
    slopeOrbit_step_eval 31 1 e31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e33 : slopeOrbit 169 84 33 = 93 :=
    slopeOrbit_step_eval 32 0 e32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e34 : slopeOrbit 169 84 34 = 17 :=
    slopeOrbit_step_eval 33 0 e33 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e35 : slopeOrbit 169 84 35 = 103 :=
    slopeOrbit_step_eval 34 3 e34 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e36 : slopeOrbit 169 84 36 = 37 :=
    slopeOrbit_step_eval 35 0 e35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e37 : slopeOrbit 169 84 37 = 127 :=
    slopeOrbit_step_eval 36 2 e36 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e38 : slopeOrbit 169 84 38 = 85 :=
    slopeOrbit_step_eval 37 0 e37 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e39 : slopeOrbit 169 84 39 = 1 :=
    slopeOrbit_step_eval 38 0 e38 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e40 : slopeOrbit 169 84 40 = 87 :=
    slopeOrbit_step_eval 39 7 e39 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e41 : slopeOrbit 169 84 41 = 5 :=
    slopeOrbit_step_eval 40 0 e40 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e42 : slopeOrbit 169 84 42 = 151 :=
    slopeOrbit_step_eval 41 5 e41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e43 : slopeOrbit 169 84 43 = 133 :=
    slopeOrbit_step_eval 42 0 e42 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e44 : slopeOrbit 169 84 44 = 97 :=
    slopeOrbit_step_eval 43 0 e43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e45 : slopeOrbit 169 84 45 = 25 :=
    slopeOrbit_step_eval 44 0 e44 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e46 : slopeOrbit 169 84 46 = 31 :=
    slopeOrbit_step_eval 45 2 e45 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e47 : slopeOrbit 169 84 47 = 79 :=
    slopeOrbit_step_eval 46 2 e46 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e48 : slopeOrbit 169 84 48 = 147 :=
    slopeOrbit_step_eval 47 1 e47 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e49 : slopeOrbit 169 84 49 = 125 :=
    slopeOrbit_step_eval 48 0 e48 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e50 : slopeOrbit 169 84 50 = 81 :=
    slopeOrbit_step_eval 49 0 e49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e51 : slopeOrbit 169 84 51 = 155 :=
    slopeOrbit_step_eval 50 1 e50 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e52 : slopeOrbit 169 84 52 = 141 :=
    slopeOrbit_step_eval 51 0 e51 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e53 : slopeOrbit 169 84 53 = 113 :=
    slopeOrbit_step_eval 52 0 e52 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e54 : slopeOrbit 169 84 54 = 57 :=
    slopeOrbit_step_eval 53 0 e53 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e55 : slopeOrbit 169 84 55 = 59 :=
    slopeOrbit_step_eval 54 1 e54 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e56 : slopeOrbit 169 84 56 = 67 :=
    slopeOrbit_step_eval 55 1 e55 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e57 : slopeOrbit 169 84 57 = 99 :=
    slopeOrbit_step_eval 56 1 e56 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e58 : slopeOrbit 169 84 58 = 29 :=
    slopeOrbit_step_eval 57 0 e57 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e59 : slopeOrbit 169 84 59 = 63 :=
    slopeOrbit_step_eval 58 2 e58 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e60 : slopeOrbit 169 84 60 = 83 :=
    slopeOrbit_step_eval 59 1 e59 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e61 : slopeOrbit 169 84 61 = 163 :=
    slopeOrbit_step_eval 60 1 e60 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e62 : slopeOrbit 169 84 62 = 157 :=
    slopeOrbit_step_eval 61 0 e61 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e63 : slopeOrbit 169 84 63 = 145 :=
    slopeOrbit_step_eval 62 0 e62 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e64 : slopeOrbit 169 84 64 = 121 :=
    slopeOrbit_step_eval 63 0 e63 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e65 : slopeOrbit 169 84 65 = 73 :=
    slopeOrbit_step_eval 64 0 e64 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e66 : slopeOrbit 169 84 66 = 123 :=
    slopeOrbit_step_eval 65 1 e65 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e67 : slopeOrbit 169 84 67 = 77 :=
    slopeOrbit_step_eval 66 0 e66 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e68 : slopeOrbit 169 84 68 = 139 :=
    slopeOrbit_step_eval 67 1 e67 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e69 : slopeOrbit 169 84 69 = 109 :=
    slopeOrbit_step_eval 68 0 e68 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e70 : slopeOrbit 169 84 70 = 49 :=
    slopeOrbit_step_eval 69 0 e69 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e71 : slopeOrbit 169 84 71 = 27 :=
    slopeOrbit_step_eval 70 1 e70 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e72 : slopeOrbit 169 84 72 = 47 :=
    slopeOrbit_step_eval 71 2 e71 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e73 : slopeOrbit 169 84 73 = 19 :=
    slopeOrbit_step_eval 72 1 e72 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e74 : slopeOrbit 169 84 74 = 135 :=
    slopeOrbit_step_eval 73 3 e73 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e75 : slopeOrbit 169 84 75 = 101 :=
    slopeOrbit_step_eval 74 0 e74 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e76 : slopeOrbit 169 84 76 = 33 :=
    slopeOrbit_step_eval 75 0 e75 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e77 : slopeOrbit 169 84 77 = 95 :=
    slopeOrbit_step_eval 76 2 e76 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e78 : slopeOrbit 169 84 78 = 21 :=
    slopeOrbit_step_eval 77 0 e77 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e79 : slopeOrbit 169 84 79 = 167 :=
    slopeOrbit_step_eval 78 3 e78 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 169 84 79 = slopeOrbit 169 84 1
    rw [e79, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e26] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e28] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e29] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e30] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e31] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e32] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e33] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e35] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e36] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e37] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e38] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e39] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e40] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e41] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e42] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e43] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e44] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e45] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e46] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e47] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e48] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e49] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e50] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e51] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e52] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e53] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e54] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e55] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e56] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e57] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e58] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e59] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e60] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e61] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e62] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e63] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e64] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e65] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e66] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e67] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e68] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e69] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e70] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e71] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e72] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e74] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e75] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e76] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e77] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide

/-- `(169,84)`: the certified class-1 count cap `|fibre_1| <= 5 * ceil(W/78)`. -/
theorem sreClass1Count_of_datum_169_84 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 169) (hK : (class1SlopeDatum ctx).K₀ = 84) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 5 * (((supportShell ctx.shell.d ctx.shell.X).card + 78 - 1) / 78) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 78)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_169_84.1
  have hcount : (class1Band4CycleBand ctx 78).card ≤ 5 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_169_84.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 78).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 78 - 1) / 78) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 5 * (((supportShell ctx.shell.d ctx.shell.X).card + 78 - 1) / 78) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(173,86)`: period `86`, cycle `[171, 169, 165, 157, 141, 109, 45, 7, 51, 31, 75, 127, 81, 151, 129, 85, 167, 161, 149, 125, 77, 135, 97, 21, 163, 153, 133, 93, 13, 35, 107, 41, 155, 137, 101, 29, 59, 63, 79, 143, 113, 53, 39, 139, 105, 37, 123, 73, 119, 65, 87, 1, 83, 159, 145, 117, 61, 71, 111, 49, 23, 11, 3, 19, 131, 89, 5, 147, 121, 69, 103, 33, 91, 9, 115, 57, 55, 47, 15, 67, 95, 17, 99, 25, 27, 43]`, bands `[1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 2, 1, 8, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 6, 4, 1, 1, 6, 1, 1, 2, 1, 3, 1, 5, 1, 2, 2, 2, 4, 2, 1, 4, 1, 3, 3, 3]` - band-4 residue set `{24, 29, 62, 64, 79, 82}` (values `21, 13, 11, 19, 15, 17`), `b4 = 6`. -/
private theorem sreCert_173_86 :
    slopeOrbit 173 86 (1 + 86) = slopeOrbit 173 86 1
      ∧ ∀ j, 1 ≤ j → j ≤ 86 →
          canonGap 173 (slopeOrbit 173 86 j) = 4 → j ∈ ({24, 29, 62, 64, 79, 82} : Finset ℕ) := by
  have e0 : slopeOrbit 173 86 0 = 86 := rfl
  have e1 : slopeOrbit 173 86 1 = 171 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 173 86 2 = 169 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 173 86 3 = 165 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 173 86 4 = 157 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 173 86 5 = 141 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 173 86 6 = 109 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 173 86 7 = 45 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 173 86 8 = 7 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 173 86 9 = 51 :=
    slopeOrbit_step_eval 8 4 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 173 86 10 = 31 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 173 86 11 = 75 :=
    slopeOrbit_step_eval 10 2 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 173 86 12 = 127 :=
    slopeOrbit_step_eval 11 1 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 173 86 13 = 81 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 173 86 14 = 151 :=
    slopeOrbit_step_eval 13 1 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 173 86 15 = 129 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 173 86 16 = 85 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 173 86 17 = 167 :=
    slopeOrbit_step_eval 16 1 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 173 86 18 = 161 :=
    slopeOrbit_step_eval 17 0 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 173 86 19 = 149 :=
    slopeOrbit_step_eval 18 0 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 173 86 20 = 125 :=
    slopeOrbit_step_eval 19 0 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 173 86 21 = 77 :=
    slopeOrbit_step_eval 20 0 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 173 86 22 = 135 :=
    slopeOrbit_step_eval 21 1 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 173 86 23 = 97 :=
    slopeOrbit_step_eval 22 0 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 173 86 24 = 21 :=
    slopeOrbit_step_eval 23 0 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 173 86 25 = 163 :=
    slopeOrbit_step_eval 24 3 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 173 86 26 = 153 :=
    slopeOrbit_step_eval 25 0 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 173 86 27 = 133 :=
    slopeOrbit_step_eval 26 0 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 173 86 28 = 93 :=
    slopeOrbit_step_eval 27 0 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 173 86 29 = 13 :=
    slopeOrbit_step_eval 28 0 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 173 86 30 = 35 :=
    slopeOrbit_step_eval 29 3 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : slopeOrbit 173 86 31 = 107 :=
    slopeOrbit_step_eval 30 2 e30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e32 : slopeOrbit 173 86 32 = 41 :=
    slopeOrbit_step_eval 31 0 e31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e33 : slopeOrbit 173 86 33 = 155 :=
    slopeOrbit_step_eval 32 2 e32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e34 : slopeOrbit 173 86 34 = 137 :=
    slopeOrbit_step_eval 33 0 e33 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e35 : slopeOrbit 173 86 35 = 101 :=
    slopeOrbit_step_eval 34 0 e34 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e36 : slopeOrbit 173 86 36 = 29 :=
    slopeOrbit_step_eval 35 0 e35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e37 : slopeOrbit 173 86 37 = 59 :=
    slopeOrbit_step_eval 36 2 e36 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e38 : slopeOrbit 173 86 38 = 63 :=
    slopeOrbit_step_eval 37 1 e37 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e39 : slopeOrbit 173 86 39 = 79 :=
    slopeOrbit_step_eval 38 1 e38 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e40 : slopeOrbit 173 86 40 = 143 :=
    slopeOrbit_step_eval 39 1 e39 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e41 : slopeOrbit 173 86 41 = 113 :=
    slopeOrbit_step_eval 40 0 e40 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e42 : slopeOrbit 173 86 42 = 53 :=
    slopeOrbit_step_eval 41 0 e41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e43 : slopeOrbit 173 86 43 = 39 :=
    slopeOrbit_step_eval 42 1 e42 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e44 : slopeOrbit 173 86 44 = 139 :=
    slopeOrbit_step_eval 43 2 e43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e45 : slopeOrbit 173 86 45 = 105 :=
    slopeOrbit_step_eval 44 0 e44 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e46 : slopeOrbit 173 86 46 = 37 :=
    slopeOrbit_step_eval 45 0 e45 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e47 : slopeOrbit 173 86 47 = 123 :=
    slopeOrbit_step_eval 46 2 e46 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e48 : slopeOrbit 173 86 48 = 73 :=
    slopeOrbit_step_eval 47 0 e47 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e49 : slopeOrbit 173 86 49 = 119 :=
    slopeOrbit_step_eval 48 1 e48 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e50 : slopeOrbit 173 86 50 = 65 :=
    slopeOrbit_step_eval 49 0 e49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e51 : slopeOrbit 173 86 51 = 87 :=
    slopeOrbit_step_eval 50 1 e50 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e52 : slopeOrbit 173 86 52 = 1 :=
    slopeOrbit_step_eval 51 0 e51 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e53 : slopeOrbit 173 86 53 = 83 :=
    slopeOrbit_step_eval 52 7 e52 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e54 : slopeOrbit 173 86 54 = 159 :=
    slopeOrbit_step_eval 53 1 e53 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e55 : slopeOrbit 173 86 55 = 145 :=
    slopeOrbit_step_eval 54 0 e54 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e56 : slopeOrbit 173 86 56 = 117 :=
    slopeOrbit_step_eval 55 0 e55 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e57 : slopeOrbit 173 86 57 = 61 :=
    slopeOrbit_step_eval 56 0 e56 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e58 : slopeOrbit 173 86 58 = 71 :=
    slopeOrbit_step_eval 57 1 e57 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e59 : slopeOrbit 173 86 59 = 111 :=
    slopeOrbit_step_eval 58 1 e58 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e60 : slopeOrbit 173 86 60 = 49 :=
    slopeOrbit_step_eval 59 0 e59 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e61 : slopeOrbit 173 86 61 = 23 :=
    slopeOrbit_step_eval 60 1 e60 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e62 : slopeOrbit 173 86 62 = 11 :=
    slopeOrbit_step_eval 61 2 e61 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e63 : slopeOrbit 173 86 63 = 3 :=
    slopeOrbit_step_eval 62 3 e62 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e64 : slopeOrbit 173 86 64 = 19 :=
    slopeOrbit_step_eval 63 5 e63 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e65 : slopeOrbit 173 86 65 = 131 :=
    slopeOrbit_step_eval 64 3 e64 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e66 : slopeOrbit 173 86 66 = 89 :=
    slopeOrbit_step_eval 65 0 e65 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e67 : slopeOrbit 173 86 67 = 5 :=
    slopeOrbit_step_eval 66 0 e66 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e68 : slopeOrbit 173 86 68 = 147 :=
    slopeOrbit_step_eval 67 5 e67 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e69 : slopeOrbit 173 86 69 = 121 :=
    slopeOrbit_step_eval 68 0 e68 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e70 : slopeOrbit 173 86 70 = 69 :=
    slopeOrbit_step_eval 69 0 e69 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e71 : slopeOrbit 173 86 71 = 103 :=
    slopeOrbit_step_eval 70 1 e70 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e72 : slopeOrbit 173 86 72 = 33 :=
    slopeOrbit_step_eval 71 0 e71 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e73 : slopeOrbit 173 86 73 = 91 :=
    slopeOrbit_step_eval 72 2 e72 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e74 : slopeOrbit 173 86 74 = 9 :=
    slopeOrbit_step_eval 73 0 e73 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e75 : slopeOrbit 173 86 75 = 115 :=
    slopeOrbit_step_eval 74 4 e74 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e76 : slopeOrbit 173 86 76 = 57 :=
    slopeOrbit_step_eval 75 0 e75 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e77 : slopeOrbit 173 86 77 = 55 :=
    slopeOrbit_step_eval 76 1 e76 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e78 : slopeOrbit 173 86 78 = 47 :=
    slopeOrbit_step_eval 77 1 e77 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e79 : slopeOrbit 173 86 79 = 15 :=
    slopeOrbit_step_eval 78 1 e78 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e80 : slopeOrbit 173 86 80 = 67 :=
    slopeOrbit_step_eval 79 3 e79 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e81 : slopeOrbit 173 86 81 = 95 :=
    slopeOrbit_step_eval 80 1 e80 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e82 : slopeOrbit 173 86 82 = 17 :=
    slopeOrbit_step_eval 81 0 e81 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e83 : slopeOrbit 173 86 83 = 99 :=
    slopeOrbit_step_eval 82 3 e82 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e84 : slopeOrbit 173 86 84 = 25 :=
    slopeOrbit_step_eval 83 0 e83 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e85 : slopeOrbit 173 86 85 = 27 :=
    slopeOrbit_step_eval 84 2 e84 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e86 : slopeOrbit 173 86 86 = 43 :=
    slopeOrbit_step_eval 85 2 e85 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e87 : slopeOrbit 173 86 87 = 171 :=
    slopeOrbit_step_eval 86 2 e86 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 173 86 87 = slopeOrbit 173 86 1
    rw [e87, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e26] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e27] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e28] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e30] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e31] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e32] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e33] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e34] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e35] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e36] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e37] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e38] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e39] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e40] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e41] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e42] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e43] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e44] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e45] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e46] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e47] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e48] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e49] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e50] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e51] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e52] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e53] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e54] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e55] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e56] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e57] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e58] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e59] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e60] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e61] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e63] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · decide
    · rw [e65] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e66] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e67] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e68] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e69] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e70] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e71] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e72] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e73] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e74] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e75] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e76] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e77] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e78] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e80] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e81] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e83] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e84] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e85] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e86] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))

/-- `(173,86)`: the certified class-1 count cap `|fibre_1| <= 6 * ceil(W/86)`. -/
theorem sreClass1Count_of_datum_173_86 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 173) (hK : (class1SlopeDatum ctx).K₀ = 86) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 6 * (((supportShell ctx.shell.d ctx.shell.X).card + 86 - 1) / 86) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 86)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_173_86.1
  have hcount : (class1Band4CycleBand ctx 86).card ≤ 6 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_173_86.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 86).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 86 - 1) / 86) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 6 * (((supportShell ctx.shell.d ctx.shell.X).card + 86 - 1) / 86) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(175,2)`: period `29`, cycle `[81, 149, 123, 71, 109, 43, 169, 163, 151, 127, 79, 141, 107, 39, 137, 99, 23, 9, 113, 51, 29, 57, 53, 37, 121, 67, 93, 11, 1]`, bands `[2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 3, 2, 2, 3, 1, 2, 1, 4, 8]` - band-4 residue set `{28}` (values `11`), `b4 = 1`. -/
private theorem sreCert_175_2 :
    slopeOrbit 175 2 (1 + 29) = slopeOrbit 175 2 1
      ∧ ∀ j, 1 ≤ j → j ≤ 29 →
          canonGap 175 (slopeOrbit 175 2 j) = 4 → j ∈ ({28} : Finset ℕ) := by
  have e0 : slopeOrbit 175 2 0 = 2 := rfl
  have e1 : slopeOrbit 175 2 1 = 81 :=
    slopeOrbit_step_eval 0 6 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 175 2 2 = 149 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 175 2 3 = 123 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 175 2 4 = 71 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 175 2 5 = 109 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 175 2 6 = 43 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 175 2 7 = 169 :=
    slopeOrbit_step_eval 6 2 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 175 2 8 = 163 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 175 2 9 = 151 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 175 2 10 = 127 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 175 2 11 = 79 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 175 2 12 = 141 :=
    slopeOrbit_step_eval 11 1 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 175 2 13 = 107 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 175 2 14 = 39 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 175 2 15 = 137 :=
    slopeOrbit_step_eval 14 2 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 175 2 16 = 99 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 175 2 17 = 23 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 175 2 18 = 9 :=
    slopeOrbit_step_eval 17 2 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 175 2 19 = 113 :=
    slopeOrbit_step_eval 18 4 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 175 2 20 = 51 :=
    slopeOrbit_step_eval 19 0 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 175 2 21 = 29 :=
    slopeOrbit_step_eval 20 1 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 175 2 22 = 57 :=
    slopeOrbit_step_eval 21 2 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 175 2 23 = 53 :=
    slopeOrbit_step_eval 22 1 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 175 2 24 = 37 :=
    slopeOrbit_step_eval 23 1 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 175 2 25 = 121 :=
    slopeOrbit_step_eval 24 2 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 175 2 26 = 67 :=
    slopeOrbit_step_eval 25 0 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 175 2 27 = 93 :=
    slopeOrbit_step_eval 26 1 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 175 2 28 = 11 :=
    slopeOrbit_step_eval 27 0 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 175 2 29 = 1 :=
    slopeOrbit_step_eval 28 3 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 175 2 30 = 81 :=
    slopeOrbit_step_eval 29 7 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 175 2 30 = slopeOrbit 175 2 1
    rw [e30, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e26] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e27] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e29] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(175,2)`: the certified class-1 count cap `|fibre_1| <= 1 * ceil(W/29)`. -/
theorem sreClass1Count_of_datum_175_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 175) (hK : (class1SlopeDatum ctx).K₀ = 2) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 29 - 1) / 29) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 29)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_175_2.1
  have hcount : (class1Band4CycleBand ctx 29).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_175_2.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 29).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 29 - 1) / 29) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 29 - 1) / 29) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(175,3)`: period `31`, cycle `[17, 97, 19, 129, 83, 157, 139, 103, 31, 73, 117, 59, 61, 69, 101, 27, 41, 153, 131, 87, 173, 171, 167, 159, 143, 111, 47, 13, 33, 89, 3]`, bands `[4, 1, 4, 1, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 3, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 6]` - band-4 residue set `{1, 3, 28}` (values `17, 19, 13`), `b4 = 3`. -/
private theorem sreCert_175_3 :
    slopeOrbit 175 3 (1 + 31) = slopeOrbit 175 3 1
      ∧ ∀ j, 1 ≤ j → j ≤ 31 →
          canonGap 175 (slopeOrbit 175 3 j) = 4 → j ∈ ({1, 3, 28} : Finset ℕ) := by
  have e0 : slopeOrbit 175 3 0 = 3 := rfl
  have e1 : slopeOrbit 175 3 1 = 17 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 175 3 2 = 97 :=
    slopeOrbit_step_eval 1 3 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 175 3 3 = 19 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 175 3 4 = 129 :=
    slopeOrbit_step_eval 3 3 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 175 3 5 = 83 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 175 3 6 = 157 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 175 3 7 = 139 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 175 3 8 = 103 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 175 3 9 = 31 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 175 3 10 = 73 :=
    slopeOrbit_step_eval 9 2 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 175 3 11 = 117 :=
    slopeOrbit_step_eval 10 1 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 175 3 12 = 59 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 175 3 13 = 61 :=
    slopeOrbit_step_eval 12 1 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 175 3 14 = 69 :=
    slopeOrbit_step_eval 13 1 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 175 3 15 = 101 :=
    slopeOrbit_step_eval 14 1 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 175 3 16 = 27 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 175 3 17 = 41 :=
    slopeOrbit_step_eval 16 2 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 175 3 18 = 153 :=
    slopeOrbit_step_eval 17 2 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 175 3 19 = 131 :=
    slopeOrbit_step_eval 18 0 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 175 3 20 = 87 :=
    slopeOrbit_step_eval 19 0 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 175 3 21 = 173 :=
    slopeOrbit_step_eval 20 1 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 175 3 22 = 171 :=
    slopeOrbit_step_eval 21 0 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 175 3 23 = 167 :=
    slopeOrbit_step_eval 22 0 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 175 3 24 = 159 :=
    slopeOrbit_step_eval 23 0 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 175 3 25 = 143 :=
    slopeOrbit_step_eval 24 0 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 175 3 26 = 111 :=
    slopeOrbit_step_eval 25 0 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 175 3 27 = 47 :=
    slopeOrbit_step_eval 26 0 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 175 3 28 = 13 :=
    slopeOrbit_step_eval 27 1 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 175 3 29 = 33 :=
    slopeOrbit_step_eval 28 3 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 175 3 30 = 89 :=
    slopeOrbit_step_eval 29 2 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : slopeOrbit 175 3 31 = 3 :=
    slopeOrbit_step_eval 30 0 e30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e32 : slopeOrbit 175 3 32 = 17 :=
    slopeOrbit_step_eval 31 5 e31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 175 3 32 = slopeOrbit 175 3 1
    rw [e32, e1]
  · intro j h1 h2 hband
    interval_cases j
    · decide
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e26] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e27] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e29] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e30] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e31] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(175,3)`: the certified class-1 count cap `|fibre_1| <= 3 * ceil(W/31)`. -/
theorem sreClass1Count_of_datum_175_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 175) (hK : (class1SlopeDatum ctx).K₀ = 3) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 3 * (((supportShell ctx.shell.d ctx.shell.X).card + 31 - 1) / 31) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 31)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_175_3.1
  have hcount : (class1Band4CycleBand ctx 31).card ≤ 3 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_175_3.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 31).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 31 - 1) / 31) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 3 * (((supportShell ctx.shell.d ctx.shell.X).card + 31 - 1) / 31) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(175,12)`: period `31`, cycle `[17, 97, 19, 129, 83, 157, 139, 103, 31, 73, 117, 59, 61, 69, 101, 27, 41, 153, 131, 87, 173, 171, 167, 159, 143, 111, 47, 13, 33, 89, 3]`, bands `[4, 1, 4, 1, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 3, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 6]` - band-4 residue set `{1, 3, 28}` (values `17, 19, 13`), `b4 = 3`. -/
private theorem sreCert_175_12 :
    slopeOrbit 175 12 (1 + 31) = slopeOrbit 175 12 1
      ∧ ∀ j, 1 ≤ j → j ≤ 31 →
          canonGap 175 (slopeOrbit 175 12 j) = 4 → j ∈ ({1, 3, 28} : Finset ℕ) := by
  have e0 : slopeOrbit 175 12 0 = 12 := rfl
  have e1 : slopeOrbit 175 12 1 = 17 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 175 12 2 = 97 :=
    slopeOrbit_step_eval 1 3 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 175 12 3 = 19 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 175 12 4 = 129 :=
    slopeOrbit_step_eval 3 3 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 175 12 5 = 83 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 175 12 6 = 157 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 175 12 7 = 139 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 175 12 8 = 103 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 175 12 9 = 31 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 175 12 10 = 73 :=
    slopeOrbit_step_eval 9 2 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 175 12 11 = 117 :=
    slopeOrbit_step_eval 10 1 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 175 12 12 = 59 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 175 12 13 = 61 :=
    slopeOrbit_step_eval 12 1 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 175 12 14 = 69 :=
    slopeOrbit_step_eval 13 1 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 175 12 15 = 101 :=
    slopeOrbit_step_eval 14 1 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 175 12 16 = 27 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 175 12 17 = 41 :=
    slopeOrbit_step_eval 16 2 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 175 12 18 = 153 :=
    slopeOrbit_step_eval 17 2 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 175 12 19 = 131 :=
    slopeOrbit_step_eval 18 0 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 175 12 20 = 87 :=
    slopeOrbit_step_eval 19 0 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 175 12 21 = 173 :=
    slopeOrbit_step_eval 20 1 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 175 12 22 = 171 :=
    slopeOrbit_step_eval 21 0 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 175 12 23 = 167 :=
    slopeOrbit_step_eval 22 0 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 175 12 24 = 159 :=
    slopeOrbit_step_eval 23 0 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 175 12 25 = 143 :=
    slopeOrbit_step_eval 24 0 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 175 12 26 = 111 :=
    slopeOrbit_step_eval 25 0 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 175 12 27 = 47 :=
    slopeOrbit_step_eval 26 0 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 175 12 28 = 13 :=
    slopeOrbit_step_eval 27 1 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 175 12 29 = 33 :=
    slopeOrbit_step_eval 28 3 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 175 12 30 = 89 :=
    slopeOrbit_step_eval 29 2 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : slopeOrbit 175 12 31 = 3 :=
    slopeOrbit_step_eval 30 0 e30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e32 : slopeOrbit 175 12 32 = 17 :=
    slopeOrbit_step_eval 31 5 e31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 175 12 32 = slopeOrbit 175 12 1
    rw [e32, e1]
  · intro j h1 h2 hband
    interval_cases j
    · decide
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e26] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e27] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e29] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e30] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e31] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(175,12)`: the certified class-1 count cap `|fibre_1| <= 3 * ceil(W/31)`. -/
theorem sreClass1Count_of_datum_175_12 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 175) (hK : (class1SlopeDatum ctx).K₀ = 12) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 3 * (((supportShell ctx.shell.d ctx.shell.X).card + 31 - 1) / 31) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 31)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_175_12.1
  have hcount : (class1Band4CycleBand ctx 31).card ≤ 3 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_175_12.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 31).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 31 - 1) / 31) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 3 * (((supportShell ctx.shell.d ctx.shell.X).card + 31 - 1) / 31) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(175,17)`: period `31`, cycle `[97, 19, 129, 83, 157, 139, 103, 31, 73, 117, 59, 61, 69, 101, 27, 41, 153, 131, 87, 173, 171, 167, 159, 143, 111, 47, 13, 33, 89, 3, 17]`, bands `[1, 4, 1, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 3, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 6, 4]` - band-4 residue set `{2, 27, 31}` (values `19, 13, 17`), `b4 = 3`. -/
private theorem sreCert_175_17 :
    slopeOrbit 175 17 (1 + 31) = slopeOrbit 175 17 1
      ∧ ∀ j, 1 ≤ j → j ≤ 31 →
          canonGap 175 (slopeOrbit 175 17 j) = 4 → j ∈ ({2, 27, 31} : Finset ℕ) := by
  have e0 : slopeOrbit 175 17 0 = 17 := rfl
  have e1 : slopeOrbit 175 17 1 = 97 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 175 17 2 = 19 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 175 17 3 = 129 :=
    slopeOrbit_step_eval 2 3 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 175 17 4 = 83 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 175 17 5 = 157 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 175 17 6 = 139 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 175 17 7 = 103 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 175 17 8 = 31 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 175 17 9 = 73 :=
    slopeOrbit_step_eval 8 2 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 175 17 10 = 117 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 175 17 11 = 59 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 175 17 12 = 61 :=
    slopeOrbit_step_eval 11 1 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 175 17 13 = 69 :=
    slopeOrbit_step_eval 12 1 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 175 17 14 = 101 :=
    slopeOrbit_step_eval 13 1 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 175 17 15 = 27 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 175 17 16 = 41 :=
    slopeOrbit_step_eval 15 2 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 175 17 17 = 153 :=
    slopeOrbit_step_eval 16 2 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 175 17 18 = 131 :=
    slopeOrbit_step_eval 17 0 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 175 17 19 = 87 :=
    slopeOrbit_step_eval 18 0 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 175 17 20 = 173 :=
    slopeOrbit_step_eval 19 1 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 175 17 21 = 171 :=
    slopeOrbit_step_eval 20 0 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 175 17 22 = 167 :=
    slopeOrbit_step_eval 21 0 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 175 17 23 = 159 :=
    slopeOrbit_step_eval 22 0 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 175 17 24 = 143 :=
    slopeOrbit_step_eval 23 0 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 175 17 25 = 111 :=
    slopeOrbit_step_eval 24 0 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 175 17 26 = 47 :=
    slopeOrbit_step_eval 25 0 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 175 17 27 = 13 :=
    slopeOrbit_step_eval 26 1 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 175 17 28 = 33 :=
    slopeOrbit_step_eval 27 3 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 175 17 29 = 89 :=
    slopeOrbit_step_eval 28 2 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 175 17 30 = 3 :=
    slopeOrbit_step_eval 29 0 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : slopeOrbit 175 17 31 = 17 :=
    slopeOrbit_step_eval 30 5 e30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e32 : slopeOrbit 175 17 32 = 97 :=
    slopeOrbit_step_eval 31 3 e31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 175 17 32 = slopeOrbit 175 17 1
    rw [e32, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e26] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e28] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e29] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e30] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · decide

/-- `(175,17)`: the certified class-1 count cap `|fibre_1| <= 3 * ceil(W/31)`. -/
theorem sreClass1Count_of_datum_175_17 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 175) (hK : (class1SlopeDatum ctx).K₀ = 17) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 3 * (((supportShell ctx.shell.d ctx.shell.X).card + 31 - 1) / 31) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 31)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_175_17.1
  have hcount : (class1Band4CycleBand ctx 31).card ≤ 3 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_175_17.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 31).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 31 - 1) / 31) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 3 * (((supportShell ctx.shell.d ctx.shell.X).card + 31 - 1) / 31) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(175,87)`: period `31`, cycle `[173, 171, 167, 159, 143, 111, 47, 13, 33, 89, 3, 17, 97, 19, 129, 83, 157, 139, 103, 31, 73, 117, 59, 61, 69, 101, 27, 41, 153, 131, 87]`, bands `[1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 6, 4, 1, 4, 1, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 3, 1, 1, 2]` - band-4 residue set `{8, 12, 14}` (values `13, 17, 19`), `b4 = 3`. -/
private theorem sreCert_175_87 :
    slopeOrbit 175 87 (1 + 31) = slopeOrbit 175 87 1
      ∧ ∀ j, 1 ≤ j → j ≤ 31 →
          canonGap 175 (slopeOrbit 175 87 j) = 4 → j ∈ ({8, 12, 14} : Finset ℕ) := by
  have e0 : slopeOrbit 175 87 0 = 87 := rfl
  have e1 : slopeOrbit 175 87 1 = 173 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 175 87 2 = 171 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 175 87 3 = 167 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 175 87 4 = 159 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 175 87 5 = 143 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 175 87 6 = 111 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 175 87 7 = 47 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 175 87 8 = 13 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 175 87 9 = 33 :=
    slopeOrbit_step_eval 8 3 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 175 87 10 = 89 :=
    slopeOrbit_step_eval 9 2 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 175 87 11 = 3 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 175 87 12 = 17 :=
    slopeOrbit_step_eval 11 5 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 175 87 13 = 97 :=
    slopeOrbit_step_eval 12 3 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 175 87 14 = 19 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 175 87 15 = 129 :=
    slopeOrbit_step_eval 14 3 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 175 87 16 = 83 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 175 87 17 = 157 :=
    slopeOrbit_step_eval 16 1 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 175 87 18 = 139 :=
    slopeOrbit_step_eval 17 0 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 175 87 19 = 103 :=
    slopeOrbit_step_eval 18 0 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 175 87 20 = 31 :=
    slopeOrbit_step_eval 19 0 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 175 87 21 = 73 :=
    slopeOrbit_step_eval 20 2 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 175 87 22 = 117 :=
    slopeOrbit_step_eval 21 1 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 175 87 23 = 59 :=
    slopeOrbit_step_eval 22 0 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 175 87 24 = 61 :=
    slopeOrbit_step_eval 23 1 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 175 87 25 = 69 :=
    slopeOrbit_step_eval 24 1 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 175 87 26 = 101 :=
    slopeOrbit_step_eval 25 1 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 175 87 27 = 27 :=
    slopeOrbit_step_eval 26 0 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 175 87 28 = 41 :=
    slopeOrbit_step_eval 27 2 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 175 87 29 = 153 :=
    slopeOrbit_step_eval 28 2 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 175 87 30 = 131 :=
    slopeOrbit_step_eval 29 0 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : slopeOrbit 175 87 31 = 87 :=
    slopeOrbit_step_eval 30 0 e30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e32 : slopeOrbit 175 87 32 = 173 :=
    slopeOrbit_step_eval 31 1 e31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 175 87 32 = slopeOrbit 175 87 1
    rw [e32, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · decide
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e26] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e27] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e28] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e29] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e30] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e31] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))

/-- `(175,87)`: the certified class-1 count cap `|fibre_1| <= 3 * ceil(W/31)`. -/
theorem sreClass1Count_of_datum_175_87 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 175) (hK : (class1SlopeDatum ctx).K₀ = 87) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 3 * (((supportShell ctx.shell.d ctx.shell.X).card + 31 - 1) / 31) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 31)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_175_87.1
  have hcount : (class1Band4CycleBand ctx 31).card ≤ 3 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_175_87.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 31).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 31 - 1) / 31) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 3 * (((supportShell ctx.shell.d ctx.shell.X).card + 31 - 1) / 31) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(177,1)`: period `29`, cycle `[79, 139, 101, 25, 23, 7, 47, 11, 175, 173, 169, 161, 145, 113, 49, 19, 127, 77, 131, 85, 163, 149, 121, 65, 83, 155, 133, 89, 1]`, bands `[2, 1, 1, 3, 3, 5, 2, 5, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8]` - band-4 residue set `{16}` (values `19`), `b4 = 1`. -/
private theorem sreCert_177_1 :
    slopeOrbit 177 1 (1 + 29) = slopeOrbit 177 1 1
      ∧ ∀ j, 1 ≤ j → j ≤ 29 →
          canonGap 177 (slopeOrbit 177 1 j) = 4 → j ∈ ({16} : Finset ℕ) := by
  have e0 : slopeOrbit 177 1 0 = 1 := rfl
  have e1 : slopeOrbit 177 1 1 = 79 :=
    slopeOrbit_step_eval 0 7 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 177 1 2 = 139 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 177 1 3 = 101 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 177 1 4 = 25 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 177 1 5 = 23 :=
    slopeOrbit_step_eval 4 2 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 177 1 6 = 7 :=
    slopeOrbit_step_eval 5 2 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 177 1 7 = 47 :=
    slopeOrbit_step_eval 6 4 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 177 1 8 = 11 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 177 1 9 = 175 :=
    slopeOrbit_step_eval 8 4 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 177 1 10 = 173 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 177 1 11 = 169 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 177 1 12 = 161 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 177 1 13 = 145 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 177 1 14 = 113 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 177 1 15 = 49 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 177 1 16 = 19 :=
    slopeOrbit_step_eval 15 1 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 177 1 17 = 127 :=
    slopeOrbit_step_eval 16 3 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 177 1 18 = 77 :=
    slopeOrbit_step_eval 17 0 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 177 1 19 = 131 :=
    slopeOrbit_step_eval 18 1 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 177 1 20 = 85 :=
    slopeOrbit_step_eval 19 0 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 177 1 21 = 163 :=
    slopeOrbit_step_eval 20 1 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 177 1 22 = 149 :=
    slopeOrbit_step_eval 21 0 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 177 1 23 = 121 :=
    slopeOrbit_step_eval 22 0 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 177 1 24 = 65 :=
    slopeOrbit_step_eval 23 0 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 177 1 25 = 83 :=
    slopeOrbit_step_eval 24 1 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 177 1 26 = 155 :=
    slopeOrbit_step_eval 25 1 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 177 1 27 = 133 :=
    slopeOrbit_step_eval 26 0 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 177 1 28 = 89 :=
    slopeOrbit_step_eval 27 0 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 177 1 29 = 1 :=
    slopeOrbit_step_eval 28 0 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 177 1 30 = 79 :=
    slopeOrbit_step_eval 29 7 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 177 1 30 = slopeOrbit 177 1 1
    rw [e30, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e26] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e27] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e28] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e29] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(177,1)`: the certified class-1 count cap `|fibre_1| <= 1 * ceil(W/29)`. -/
theorem sreClass1Count_of_datum_177_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 177) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 29 - 1) / 29) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 29)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_177_1.1
  have hcount : (class1Band4CycleBand ctx 29).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_177_1.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 29).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 29 - 1) / 29) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 29 - 1) / 29) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(177,29)`: period `29`, cycle `[55, 43, 167, 157, 137, 97, 17, 95, 13, 31, 71, 107, 37, 119, 61, 67, 91, 5, 143, 109, 41, 151, 125, 73, 115, 53, 35, 103, 29]`, bands `[2, 3, 1, 1, 1, 1, 4, 1, 4, 3, 2, 1, 3, 1, 2, 2, 1, 6, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 3]` - band-4 residue set `{7, 9}` (values `17, 13`), `b4 = 2`. -/
private theorem sreCert_177_29 :
    slopeOrbit 177 29 (1 + 29) = slopeOrbit 177 29 1
      ∧ ∀ j, 1 ≤ j → j ≤ 29 →
          canonGap 177 (slopeOrbit 177 29 j) = 4 → j ∈ ({7, 9} : Finset ℕ) := by
  have e0 : slopeOrbit 177 29 0 = 29 := rfl
  have e1 : slopeOrbit 177 29 1 = 55 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 177 29 2 = 43 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 177 29 3 = 167 :=
    slopeOrbit_step_eval 2 2 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 177 29 4 = 157 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 177 29 5 = 137 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 177 29 6 = 97 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 177 29 7 = 17 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 177 29 8 = 95 :=
    slopeOrbit_step_eval 7 3 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 177 29 9 = 13 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 177 29 10 = 31 :=
    slopeOrbit_step_eval 9 3 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 177 29 11 = 71 :=
    slopeOrbit_step_eval 10 2 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 177 29 12 = 107 :=
    slopeOrbit_step_eval 11 1 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 177 29 13 = 37 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 177 29 14 = 119 :=
    slopeOrbit_step_eval 13 2 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 177 29 15 = 61 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 177 29 16 = 67 :=
    slopeOrbit_step_eval 15 1 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 177 29 17 = 91 :=
    slopeOrbit_step_eval 16 1 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 177 29 18 = 5 :=
    slopeOrbit_step_eval 17 0 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 177 29 19 = 143 :=
    slopeOrbit_step_eval 18 5 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 177 29 20 = 109 :=
    slopeOrbit_step_eval 19 0 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 177 29 21 = 41 :=
    slopeOrbit_step_eval 20 0 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 177 29 22 = 151 :=
    slopeOrbit_step_eval 21 2 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 177 29 23 = 125 :=
    slopeOrbit_step_eval 22 0 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 177 29 24 = 73 :=
    slopeOrbit_step_eval 23 0 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 177 29 25 = 115 :=
    slopeOrbit_step_eval 24 1 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 177 29 26 = 53 :=
    slopeOrbit_step_eval 25 0 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 177 29 27 = 35 :=
    slopeOrbit_step_eval 26 1 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 177 29 28 = 103 :=
    slopeOrbit_step_eval 27 2 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 177 29 29 = 29 :=
    slopeOrbit_step_eval 28 0 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 177 29 30 = 55 :=
    slopeOrbit_step_eval 29 2 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 177 29 30 = slopeOrbit 177 29 1
    rw [e30, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e26] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e27] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e28] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e29] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))

/-- `(177,29)`: the certified class-1 count cap `|fibre_1| <= 2 * ceil(W/29)`. -/
theorem sreClass1Count_of_datum_177_29 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 177) (hK : (class1SlopeDatum ctx).K₀ = 29) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 29 - 1) / 29) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 29)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_177_29.1
  have hcount : (class1Band4CycleBand ctx 29).card ≤ 2 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_177_29.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 29).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 29 - 1) / 29) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 29 - 1) / 29) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(177,88)`: period `29`, cycle `[175, 173, 169, 161, 145, 113, 49, 19, 127, 77, 131, 85, 163, 149, 121, 65, 83, 155, 133, 89, 1, 79, 139, 101, 25, 23, 7, 47, 11]`, bands `[1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 2, 1, 1, 3, 3, 5, 2, 5]` - band-4 residue set `{8}` (values `19`), `b4 = 1`. -/
private theorem sreCert_177_88 :
    slopeOrbit 177 88 (1 + 29) = slopeOrbit 177 88 1
      ∧ ∀ j, 1 ≤ j → j ≤ 29 →
          canonGap 177 (slopeOrbit 177 88 j) = 4 → j ∈ ({8} : Finset ℕ) := by
  have e0 : slopeOrbit 177 88 0 = 88 := rfl
  have e1 : slopeOrbit 177 88 1 = 175 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 177 88 2 = 173 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 177 88 3 = 169 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 177 88 4 = 161 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 177 88 5 = 145 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 177 88 6 = 113 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 177 88 7 = 49 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 177 88 8 = 19 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 177 88 9 = 127 :=
    slopeOrbit_step_eval 8 3 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 177 88 10 = 77 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 177 88 11 = 131 :=
    slopeOrbit_step_eval 10 1 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 177 88 12 = 85 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 177 88 13 = 163 :=
    slopeOrbit_step_eval 12 1 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 177 88 14 = 149 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 177 88 15 = 121 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 177 88 16 = 65 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 177 88 17 = 83 :=
    slopeOrbit_step_eval 16 1 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 177 88 18 = 155 :=
    slopeOrbit_step_eval 17 1 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 177 88 19 = 133 :=
    slopeOrbit_step_eval 18 0 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 177 88 20 = 89 :=
    slopeOrbit_step_eval 19 0 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 177 88 21 = 1 :=
    slopeOrbit_step_eval 20 0 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 177 88 22 = 79 :=
    slopeOrbit_step_eval 21 7 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 177 88 23 = 139 :=
    slopeOrbit_step_eval 22 1 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 177 88 24 = 101 :=
    slopeOrbit_step_eval 23 0 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 177 88 25 = 25 :=
    slopeOrbit_step_eval 24 0 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 177 88 26 = 23 :=
    slopeOrbit_step_eval 25 2 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 177 88 27 = 7 :=
    slopeOrbit_step_eval 26 2 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 177 88 28 = 47 :=
    slopeOrbit_step_eval 27 4 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 177 88 29 = 11 :=
    slopeOrbit_step_eval 28 1 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 177 88 30 = 175 :=
    slopeOrbit_step_eval 29 4 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 177 88 30 = slopeOrbit 177 88 1
    rw [e30, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e26] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e27] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e28] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e29] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(177,88)`: the certified class-1 count cap `|fibre_1| <= 1 * ceil(W/29)`. -/
theorem sreClass1Count_of_datum_177_88 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 177) (hK : (class1SlopeDatum ctx).K₀ = 88) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 29 - 1) / 29) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 29)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_177_88.1
  have hcount : (class1Band4CycleBand ctx 29).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_177_88.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 29).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 29 - 1) / 29) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 29 - 1) / 29) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(179,89)`: period `89`, cycle `[177, 175, 171, 163, 147, 115, 51, 25, 21, 157, 135, 91, 3, 13, 29, 53, 33, 85, 161, 143, 107, 35, 101, 23, 5, 141, 103, 27, 37, 117, 55, 41, 149, 119, 59, 57, 49, 17, 93, 7, 45, 1, 77, 129, 79, 137, 95, 11, 173, 167, 155, 131, 83, 153, 127, 75, 121, 63, 73, 113, 47, 9, 109, 39, 133, 87, 169, 159, 139, 99, 19, 125, 71, 105, 31, 69, 97, 15, 61, 65, 81, 145, 111, 43, 165, 151, 123, 67, 89]`, bands `[1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 6, 4, 3, 2, 3, 2, 1, 1, 1, 3, 1, 3, 6, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 2, 2, 4, 1, 5, 2, 8, 2, 1, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 3, 1, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 4, 2, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2]` - band-4 residue set `{9, 14, 38, 71, 78}` (values `21, 13, 17, 19, 15`), `b4 = 5`. -/
private theorem sreCert_179_89 :
    slopeOrbit 179 89 (1 + 89) = slopeOrbit 179 89 1
      ∧ ∀ j, 1 ≤ j → j ≤ 89 →
          canonGap 179 (slopeOrbit 179 89 j) = 4 → j ∈ ({9, 14, 38, 71, 78} : Finset ℕ) := by
  have e0 : slopeOrbit 179 89 0 = 89 := rfl
  have e1 : slopeOrbit 179 89 1 = 177 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 179 89 2 = 175 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 179 89 3 = 171 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 179 89 4 = 163 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 179 89 5 = 147 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 179 89 6 = 115 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 179 89 7 = 51 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 179 89 8 = 25 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 179 89 9 = 21 :=
    slopeOrbit_step_eval 8 2 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 179 89 10 = 157 :=
    slopeOrbit_step_eval 9 3 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 179 89 11 = 135 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 179 89 12 = 91 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 179 89 13 = 3 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 179 89 14 = 13 :=
    slopeOrbit_step_eval 13 5 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 179 89 15 = 29 :=
    slopeOrbit_step_eval 14 3 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 179 89 16 = 53 :=
    slopeOrbit_step_eval 15 2 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 179 89 17 = 33 :=
    slopeOrbit_step_eval 16 1 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 179 89 18 = 85 :=
    slopeOrbit_step_eval 17 2 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 179 89 19 = 161 :=
    slopeOrbit_step_eval 18 1 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 179 89 20 = 143 :=
    slopeOrbit_step_eval 19 0 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 179 89 21 = 107 :=
    slopeOrbit_step_eval 20 0 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 179 89 22 = 35 :=
    slopeOrbit_step_eval 21 0 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 179 89 23 = 101 :=
    slopeOrbit_step_eval 22 2 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 179 89 24 = 23 :=
    slopeOrbit_step_eval 23 0 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 179 89 25 = 5 :=
    slopeOrbit_step_eval 24 2 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 179 89 26 = 141 :=
    slopeOrbit_step_eval 25 5 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 179 89 27 = 103 :=
    slopeOrbit_step_eval 26 0 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 179 89 28 = 27 :=
    slopeOrbit_step_eval 27 0 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 179 89 29 = 37 :=
    slopeOrbit_step_eval 28 2 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 179 89 30 = 117 :=
    slopeOrbit_step_eval 29 2 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : slopeOrbit 179 89 31 = 55 :=
    slopeOrbit_step_eval 30 0 e30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e32 : slopeOrbit 179 89 32 = 41 :=
    slopeOrbit_step_eval 31 1 e31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e33 : slopeOrbit 179 89 33 = 149 :=
    slopeOrbit_step_eval 32 2 e32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e34 : slopeOrbit 179 89 34 = 119 :=
    slopeOrbit_step_eval 33 0 e33 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e35 : slopeOrbit 179 89 35 = 59 :=
    slopeOrbit_step_eval 34 0 e34 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e36 : slopeOrbit 179 89 36 = 57 :=
    slopeOrbit_step_eval 35 1 e35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e37 : slopeOrbit 179 89 37 = 49 :=
    slopeOrbit_step_eval 36 1 e36 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e38 : slopeOrbit 179 89 38 = 17 :=
    slopeOrbit_step_eval 37 1 e37 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e39 : slopeOrbit 179 89 39 = 93 :=
    slopeOrbit_step_eval 38 3 e38 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e40 : slopeOrbit 179 89 40 = 7 :=
    slopeOrbit_step_eval 39 0 e39 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e41 : slopeOrbit 179 89 41 = 45 :=
    slopeOrbit_step_eval 40 4 e40 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e42 : slopeOrbit 179 89 42 = 1 :=
    slopeOrbit_step_eval 41 1 e41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e43 : slopeOrbit 179 89 43 = 77 :=
    slopeOrbit_step_eval 42 7 e42 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e44 : slopeOrbit 179 89 44 = 129 :=
    slopeOrbit_step_eval 43 1 e43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e45 : slopeOrbit 179 89 45 = 79 :=
    slopeOrbit_step_eval 44 0 e44 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e46 : slopeOrbit 179 89 46 = 137 :=
    slopeOrbit_step_eval 45 1 e45 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e47 : slopeOrbit 179 89 47 = 95 :=
    slopeOrbit_step_eval 46 0 e46 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e48 : slopeOrbit 179 89 48 = 11 :=
    slopeOrbit_step_eval 47 0 e47 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e49 : slopeOrbit 179 89 49 = 173 :=
    slopeOrbit_step_eval 48 4 e48 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e50 : slopeOrbit 179 89 50 = 167 :=
    slopeOrbit_step_eval 49 0 e49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e51 : slopeOrbit 179 89 51 = 155 :=
    slopeOrbit_step_eval 50 0 e50 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e52 : slopeOrbit 179 89 52 = 131 :=
    slopeOrbit_step_eval 51 0 e51 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e53 : slopeOrbit 179 89 53 = 83 :=
    slopeOrbit_step_eval 52 0 e52 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e54 : slopeOrbit 179 89 54 = 153 :=
    slopeOrbit_step_eval 53 1 e53 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e55 : slopeOrbit 179 89 55 = 127 :=
    slopeOrbit_step_eval 54 0 e54 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e56 : slopeOrbit 179 89 56 = 75 :=
    slopeOrbit_step_eval 55 0 e55 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e57 : slopeOrbit 179 89 57 = 121 :=
    slopeOrbit_step_eval 56 1 e56 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e58 : slopeOrbit 179 89 58 = 63 :=
    slopeOrbit_step_eval 57 0 e57 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e59 : slopeOrbit 179 89 59 = 73 :=
    slopeOrbit_step_eval 58 1 e58 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e60 : slopeOrbit 179 89 60 = 113 :=
    slopeOrbit_step_eval 59 1 e59 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e61 : slopeOrbit 179 89 61 = 47 :=
    slopeOrbit_step_eval 60 0 e60 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e62 : slopeOrbit 179 89 62 = 9 :=
    slopeOrbit_step_eval 61 1 e61 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e63 : slopeOrbit 179 89 63 = 109 :=
    slopeOrbit_step_eval 62 4 e62 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e64 : slopeOrbit 179 89 64 = 39 :=
    slopeOrbit_step_eval 63 0 e63 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e65 : slopeOrbit 179 89 65 = 133 :=
    slopeOrbit_step_eval 64 2 e64 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e66 : slopeOrbit 179 89 66 = 87 :=
    slopeOrbit_step_eval 65 0 e65 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e67 : slopeOrbit 179 89 67 = 169 :=
    slopeOrbit_step_eval 66 1 e66 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e68 : slopeOrbit 179 89 68 = 159 :=
    slopeOrbit_step_eval 67 0 e67 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e69 : slopeOrbit 179 89 69 = 139 :=
    slopeOrbit_step_eval 68 0 e68 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e70 : slopeOrbit 179 89 70 = 99 :=
    slopeOrbit_step_eval 69 0 e69 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e71 : slopeOrbit 179 89 71 = 19 :=
    slopeOrbit_step_eval 70 0 e70 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e72 : slopeOrbit 179 89 72 = 125 :=
    slopeOrbit_step_eval 71 3 e71 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e73 : slopeOrbit 179 89 73 = 71 :=
    slopeOrbit_step_eval 72 0 e72 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e74 : slopeOrbit 179 89 74 = 105 :=
    slopeOrbit_step_eval 73 1 e73 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e75 : slopeOrbit 179 89 75 = 31 :=
    slopeOrbit_step_eval 74 0 e74 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e76 : slopeOrbit 179 89 76 = 69 :=
    slopeOrbit_step_eval 75 2 e75 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e77 : slopeOrbit 179 89 77 = 97 :=
    slopeOrbit_step_eval 76 1 e76 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e78 : slopeOrbit 179 89 78 = 15 :=
    slopeOrbit_step_eval 77 0 e77 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e79 : slopeOrbit 179 89 79 = 61 :=
    slopeOrbit_step_eval 78 3 e78 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e80 : slopeOrbit 179 89 80 = 65 :=
    slopeOrbit_step_eval 79 1 e79 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e81 : slopeOrbit 179 89 81 = 81 :=
    slopeOrbit_step_eval 80 1 e80 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e82 : slopeOrbit 179 89 82 = 145 :=
    slopeOrbit_step_eval 81 1 e81 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e83 : slopeOrbit 179 89 83 = 111 :=
    slopeOrbit_step_eval 82 0 e82 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e84 : slopeOrbit 179 89 84 = 43 :=
    slopeOrbit_step_eval 83 0 e83 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e85 : slopeOrbit 179 89 85 = 165 :=
    slopeOrbit_step_eval 84 2 e84 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e86 : slopeOrbit 179 89 86 = 151 :=
    slopeOrbit_step_eval 85 0 e85 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e87 : slopeOrbit 179 89 87 = 123 :=
    slopeOrbit_step_eval 86 0 e86 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e88 : slopeOrbit 179 89 88 = 67 :=
    slopeOrbit_step_eval 87 0 e87 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e89 : slopeOrbit 179 89 89 = 89 :=
    slopeOrbit_step_eval 88 1 e88 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e90 : slopeOrbit 179 89 90 = 177 :=
    slopeOrbit_step_eval 89 1 e89 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 179 89 90 = slopeOrbit 179 89 1
    rw [e90, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · decide
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e26] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e27] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e28] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e29] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e30] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e31] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e32] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e33] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e34] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e35] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e36] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e37] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e39] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e40] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e41] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e42] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e43] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e44] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e45] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e46] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e47] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e48] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e49] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e50] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e51] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e52] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e53] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e54] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e55] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e56] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e57] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e58] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e59] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e60] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e61] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e62] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e63] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e64] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e65] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e66] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e67] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e68] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e69] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e70] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e72] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e73] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e74] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e75] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e76] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e77] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e79] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e80] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e81] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e82] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e83] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e84] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e85] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e86] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e87] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e88] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e89] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))

/-- `(179,89)`: the certified class-1 count cap `|fibre_1| <= 5 * ceil(W/89)`. -/
theorem sreClass1Count_of_datum_179_89 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 179) (hK : (class1SlopeDatum ctx).K₀ = 89) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 5 * (((supportShell ctx.shell.d ctx.shell.X).card + 89 - 1) / 89) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 89)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_179_89.1
  have hcount : (class1Band4CycleBand ctx 89).card ≤ 5 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_179_89.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 89).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 89 - 1) / 89) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 5 * (((supportShell ctx.shell.d ctx.shell.X).card + 89 - 1) / 89) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(181,90)`: period `90`, cycle `[179, 177, 173, 165, 149, 117, 53, 31, 67, 87, 167, 153, 125, 69, 95, 9, 107, 33, 83, 151, 121, 61, 63, 71, 103, 25, 19, 123, 65, 79, 135, 89, 175, 169, 157, 133, 85, 159, 137, 93, 5, 139, 97, 13, 27, 35, 99, 17, 91, 1, 75, 119, 57, 47, 7, 43, 163, 145, 109, 37, 115, 49, 15, 59, 55, 39, 131, 81, 143, 105, 29, 51, 23, 3, 11, 171, 161, 141, 101, 21, 155, 129, 77, 127, 73, 111, 41, 147, 113, 45]`, bands `[1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 2, 2, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 4, 3, 3, 1, 4, 1, 8, 2, 1, 2, 2, 5, 3, 1, 1, 1, 3, 1, 2, 4, 2, 2, 3, 1, 2, 1, 1, 3, 2, 3, 6, 5, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3]` - band-4 residue set `{27, 44, 48, 63, 80}` (values `19, 13, 17, 15, 21`), `b4 = 5`. -/
private theorem sreCert_181_90 :
    slopeOrbit 181 90 (1 + 90) = slopeOrbit 181 90 1
      ∧ ∀ j, 1 ≤ j → j ≤ 90 →
          canonGap 181 (slopeOrbit 181 90 j) = 4 → j ∈ ({27, 44, 48, 63, 80} : Finset ℕ) := by
  have e0 : slopeOrbit 181 90 0 = 90 := rfl
  have e1 : slopeOrbit 181 90 1 = 179 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 181 90 2 = 177 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 181 90 3 = 173 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 181 90 4 = 165 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 181 90 5 = 149 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 181 90 6 = 117 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 181 90 7 = 53 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 181 90 8 = 31 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 181 90 9 = 67 :=
    slopeOrbit_step_eval 8 2 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 181 90 10 = 87 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 181 90 11 = 167 :=
    slopeOrbit_step_eval 10 1 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 181 90 12 = 153 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 181 90 13 = 125 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 181 90 14 = 69 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 181 90 15 = 95 :=
    slopeOrbit_step_eval 14 1 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 181 90 16 = 9 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 181 90 17 = 107 :=
    slopeOrbit_step_eval 16 4 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 181 90 18 = 33 :=
    slopeOrbit_step_eval 17 0 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 181 90 19 = 83 :=
    slopeOrbit_step_eval 18 2 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 181 90 20 = 151 :=
    slopeOrbit_step_eval 19 1 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 181 90 21 = 121 :=
    slopeOrbit_step_eval 20 0 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 181 90 22 = 61 :=
    slopeOrbit_step_eval 21 0 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 181 90 23 = 63 :=
    slopeOrbit_step_eval 22 1 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 181 90 24 = 71 :=
    slopeOrbit_step_eval 23 1 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 181 90 25 = 103 :=
    slopeOrbit_step_eval 24 1 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 181 90 26 = 25 :=
    slopeOrbit_step_eval 25 0 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 181 90 27 = 19 :=
    slopeOrbit_step_eval 26 2 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 181 90 28 = 123 :=
    slopeOrbit_step_eval 27 3 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 181 90 29 = 65 :=
    slopeOrbit_step_eval 28 0 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 181 90 30 = 79 :=
    slopeOrbit_step_eval 29 1 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : slopeOrbit 181 90 31 = 135 :=
    slopeOrbit_step_eval 30 1 e30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e32 : slopeOrbit 181 90 32 = 89 :=
    slopeOrbit_step_eval 31 0 e31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e33 : slopeOrbit 181 90 33 = 175 :=
    slopeOrbit_step_eval 32 1 e32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e34 : slopeOrbit 181 90 34 = 169 :=
    slopeOrbit_step_eval 33 0 e33 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e35 : slopeOrbit 181 90 35 = 157 :=
    slopeOrbit_step_eval 34 0 e34 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e36 : slopeOrbit 181 90 36 = 133 :=
    slopeOrbit_step_eval 35 0 e35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e37 : slopeOrbit 181 90 37 = 85 :=
    slopeOrbit_step_eval 36 0 e36 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e38 : slopeOrbit 181 90 38 = 159 :=
    slopeOrbit_step_eval 37 1 e37 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e39 : slopeOrbit 181 90 39 = 137 :=
    slopeOrbit_step_eval 38 0 e38 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e40 : slopeOrbit 181 90 40 = 93 :=
    slopeOrbit_step_eval 39 0 e39 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e41 : slopeOrbit 181 90 41 = 5 :=
    slopeOrbit_step_eval 40 0 e40 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e42 : slopeOrbit 181 90 42 = 139 :=
    slopeOrbit_step_eval 41 5 e41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e43 : slopeOrbit 181 90 43 = 97 :=
    slopeOrbit_step_eval 42 0 e42 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e44 : slopeOrbit 181 90 44 = 13 :=
    slopeOrbit_step_eval 43 0 e43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e45 : slopeOrbit 181 90 45 = 27 :=
    slopeOrbit_step_eval 44 3 e44 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e46 : slopeOrbit 181 90 46 = 35 :=
    slopeOrbit_step_eval 45 2 e45 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e47 : slopeOrbit 181 90 47 = 99 :=
    slopeOrbit_step_eval 46 2 e46 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e48 : slopeOrbit 181 90 48 = 17 :=
    slopeOrbit_step_eval 47 0 e47 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e49 : slopeOrbit 181 90 49 = 91 :=
    slopeOrbit_step_eval 48 3 e48 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e50 : slopeOrbit 181 90 50 = 1 :=
    slopeOrbit_step_eval 49 0 e49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e51 : slopeOrbit 181 90 51 = 75 :=
    slopeOrbit_step_eval 50 7 e50 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e52 : slopeOrbit 181 90 52 = 119 :=
    slopeOrbit_step_eval 51 1 e51 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e53 : slopeOrbit 181 90 53 = 57 :=
    slopeOrbit_step_eval 52 0 e52 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e54 : slopeOrbit 181 90 54 = 47 :=
    slopeOrbit_step_eval 53 1 e53 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e55 : slopeOrbit 181 90 55 = 7 :=
    slopeOrbit_step_eval 54 1 e54 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e56 : slopeOrbit 181 90 56 = 43 :=
    slopeOrbit_step_eval 55 4 e55 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e57 : slopeOrbit 181 90 57 = 163 :=
    slopeOrbit_step_eval 56 2 e56 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e58 : slopeOrbit 181 90 58 = 145 :=
    slopeOrbit_step_eval 57 0 e57 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e59 : slopeOrbit 181 90 59 = 109 :=
    slopeOrbit_step_eval 58 0 e58 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e60 : slopeOrbit 181 90 60 = 37 :=
    slopeOrbit_step_eval 59 0 e59 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e61 : slopeOrbit 181 90 61 = 115 :=
    slopeOrbit_step_eval 60 2 e60 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e62 : slopeOrbit 181 90 62 = 49 :=
    slopeOrbit_step_eval 61 0 e61 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e63 : slopeOrbit 181 90 63 = 15 :=
    slopeOrbit_step_eval 62 1 e62 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e64 : slopeOrbit 181 90 64 = 59 :=
    slopeOrbit_step_eval 63 3 e63 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e65 : slopeOrbit 181 90 65 = 55 :=
    slopeOrbit_step_eval 64 1 e64 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e66 : slopeOrbit 181 90 66 = 39 :=
    slopeOrbit_step_eval 65 1 e65 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e67 : slopeOrbit 181 90 67 = 131 :=
    slopeOrbit_step_eval 66 2 e66 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e68 : slopeOrbit 181 90 68 = 81 :=
    slopeOrbit_step_eval 67 0 e67 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e69 : slopeOrbit 181 90 69 = 143 :=
    slopeOrbit_step_eval 68 1 e68 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e70 : slopeOrbit 181 90 70 = 105 :=
    slopeOrbit_step_eval 69 0 e69 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e71 : slopeOrbit 181 90 71 = 29 :=
    slopeOrbit_step_eval 70 0 e70 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e72 : slopeOrbit 181 90 72 = 51 :=
    slopeOrbit_step_eval 71 2 e71 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e73 : slopeOrbit 181 90 73 = 23 :=
    slopeOrbit_step_eval 72 1 e72 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e74 : slopeOrbit 181 90 74 = 3 :=
    slopeOrbit_step_eval 73 2 e73 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e75 : slopeOrbit 181 90 75 = 11 :=
    slopeOrbit_step_eval 74 5 e74 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e76 : slopeOrbit 181 90 76 = 171 :=
    slopeOrbit_step_eval 75 4 e75 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e77 : slopeOrbit 181 90 77 = 161 :=
    slopeOrbit_step_eval 76 0 e76 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e78 : slopeOrbit 181 90 78 = 141 :=
    slopeOrbit_step_eval 77 0 e77 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e79 : slopeOrbit 181 90 79 = 101 :=
    slopeOrbit_step_eval 78 0 e78 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e80 : slopeOrbit 181 90 80 = 21 :=
    slopeOrbit_step_eval 79 0 e79 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e81 : slopeOrbit 181 90 81 = 155 :=
    slopeOrbit_step_eval 80 3 e80 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e82 : slopeOrbit 181 90 82 = 129 :=
    slopeOrbit_step_eval 81 0 e81 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e83 : slopeOrbit 181 90 83 = 77 :=
    slopeOrbit_step_eval 82 0 e82 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e84 : slopeOrbit 181 90 84 = 127 :=
    slopeOrbit_step_eval 83 1 e83 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e85 : slopeOrbit 181 90 85 = 73 :=
    slopeOrbit_step_eval 84 0 e84 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e86 : slopeOrbit 181 90 86 = 111 :=
    slopeOrbit_step_eval 85 1 e85 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e87 : slopeOrbit 181 90 87 = 41 :=
    slopeOrbit_step_eval 86 0 e86 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e88 : slopeOrbit 181 90 88 = 147 :=
    slopeOrbit_step_eval 87 2 e87 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e89 : slopeOrbit 181 90 89 = 113 :=
    slopeOrbit_step_eval 88 0 e88 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e90 : slopeOrbit 181 90 90 = 45 :=
    slopeOrbit_step_eval 89 0 e89 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e91 : slopeOrbit 181 90 91 = 179 :=
    slopeOrbit_step_eval 90 2 e90 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 181 90 91 = slopeOrbit 181 90 1
    rw [e91, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e26] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e28] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e29] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e30] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e31] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e32] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e33] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e34] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e35] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e36] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e37] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e38] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e39] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e40] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e41] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e42] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e43] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e45] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e46] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e47] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e49] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e50] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e51] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e52] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e53] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e54] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e55] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e56] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e57] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e58] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e59] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e60] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e61] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e62] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e64] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e65] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e66] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e67] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e68] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e69] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e70] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e71] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e72] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e73] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e74] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e75] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e76] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e77] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e78] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e79] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e81] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e82] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e83] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e84] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e85] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e86] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e87] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e88] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e89] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e90] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))

/-- `(181,90)`: the certified class-1 count cap `|fibre_1| <= 5 * ceil(W/90)`. -/
theorem sreClass1Count_of_datum_181_90 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 181) (hK : (class1SlopeDatum ctx).K₀ = 90) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 5 * (((supportShell ctx.shell.d ctx.shell.X).card + 90 - 1) / 90) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 90)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_181_90.1
  have hcount : (class1Band4CycleBand ctx 90).card ≤ 5 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_181_90.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 90).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 90 - 1) / 90) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 5 * (((supportShell ctx.shell.d ctx.shell.X).card + 90 - 1) / 90) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(183,1)`: period `26`, cycle `[73, 109, 35, 97, 11, 169, 155, 127, 71, 101, 19, 121, 59, 53, 29, 49, 13, 25, 17, 89, 173, 163, 143, 103, 23, 1]`, bands `[2, 1, 3, 1, 5, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 2, 4, 3, 4, 2, 1, 1, 1, 1, 3, 8]` - band-4 residue set `{11, 17, 19}` (values `19, 13, 17`), `b4 = 3`. -/
private theorem sreCert_183_1 :
    slopeOrbit 183 1 (1 + 26) = slopeOrbit 183 1 1
      ∧ ∀ j, 1 ≤ j → j ≤ 26 →
          canonGap 183 (slopeOrbit 183 1 j) = 4 → j ∈ ({11, 17, 19} : Finset ℕ) := by
  have e0 : slopeOrbit 183 1 0 = 1 := rfl
  have e1 : slopeOrbit 183 1 1 = 73 :=
    slopeOrbit_step_eval 0 7 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 183 1 2 = 109 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 183 1 3 = 35 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 183 1 4 = 97 :=
    slopeOrbit_step_eval 3 2 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 183 1 5 = 11 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 183 1 6 = 169 :=
    slopeOrbit_step_eval 5 4 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 183 1 7 = 155 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 183 1 8 = 127 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 183 1 9 = 71 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 183 1 10 = 101 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 183 1 11 = 19 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 183 1 12 = 121 :=
    slopeOrbit_step_eval 11 3 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 183 1 13 = 59 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 183 1 14 = 53 :=
    slopeOrbit_step_eval 13 1 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 183 1 15 = 29 :=
    slopeOrbit_step_eval 14 1 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 183 1 16 = 49 :=
    slopeOrbit_step_eval 15 2 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 183 1 17 = 13 :=
    slopeOrbit_step_eval 16 1 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 183 1 18 = 25 :=
    slopeOrbit_step_eval 17 3 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 183 1 19 = 17 :=
    slopeOrbit_step_eval 18 2 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 183 1 20 = 89 :=
    slopeOrbit_step_eval 19 3 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 183 1 21 = 173 :=
    slopeOrbit_step_eval 20 1 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 183 1 22 = 163 :=
    slopeOrbit_step_eval 21 0 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 183 1 23 = 143 :=
    slopeOrbit_step_eval 22 0 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 183 1 24 = 103 :=
    slopeOrbit_step_eval 23 0 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 183 1 25 = 23 :=
    slopeOrbit_step_eval 24 0 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 183 1 26 = 1 :=
    slopeOrbit_step_eval 25 2 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 183 1 27 = 73 :=
    slopeOrbit_step_eval 26 7 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 183 1 27 = slopeOrbit 183 1 1
    rw [e27, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e26] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(183,1)`: the certified class-1 count cap `|fibre_1| <= 3 * ceil(W/26)`. -/
theorem sreClass1Count_of_datum_183_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 183) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 3 * (((supportShell ctx.shell.d ctx.shell.X).card + 26 - 1) / 26) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 26)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_183_1.1
  have hcount : (class1Band4CycleBand ctx 26).card ≤ 3 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_183_1.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 26).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 26 - 1) / 26) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 3 * (((supportShell ctx.shell.d ctx.shell.X).card + 26 - 1) / 26) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(183,30)`: period `30`, cycle `[57, 45, 177, 171, 159, 135, 87, 165, 147, 111, 39, 129, 75, 117, 51, 21, 153, 123, 63, 69, 93, 3, 9, 105, 27, 33, 81, 141, 99, 15]`, bands `[2, 3, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 2, 2, 1, 6, 5, 1, 3, 3, 2, 1, 1, 4]` - band-4 residue set `{16, 30}` (values `21, 15`), `b4 = 2`. -/
private theorem sreCert_183_30 :
    slopeOrbit 183 30 (1 + 30) = slopeOrbit 183 30 1
      ∧ ∀ j, 1 ≤ j → j ≤ 30 →
          canonGap 183 (slopeOrbit 183 30 j) = 4 → j ∈ ({16, 30} : Finset ℕ) := by
  have e0 : slopeOrbit 183 30 0 = 30 := rfl
  have e1 : slopeOrbit 183 30 1 = 57 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 183 30 2 = 45 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 183 30 3 = 177 :=
    slopeOrbit_step_eval 2 2 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 183 30 4 = 171 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 183 30 5 = 159 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 183 30 6 = 135 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 183 30 7 = 87 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 183 30 8 = 165 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 183 30 9 = 147 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 183 30 10 = 111 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 183 30 11 = 39 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 183 30 12 = 129 :=
    slopeOrbit_step_eval 11 2 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 183 30 13 = 75 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 183 30 14 = 117 :=
    slopeOrbit_step_eval 13 1 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 183 30 15 = 51 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 183 30 16 = 21 :=
    slopeOrbit_step_eval 15 1 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 183 30 17 = 153 :=
    slopeOrbit_step_eval 16 3 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 183 30 18 = 123 :=
    slopeOrbit_step_eval 17 0 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 183 30 19 = 63 :=
    slopeOrbit_step_eval 18 0 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 183 30 20 = 69 :=
    slopeOrbit_step_eval 19 1 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 183 30 21 = 93 :=
    slopeOrbit_step_eval 20 1 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 183 30 22 = 3 :=
    slopeOrbit_step_eval 21 0 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 183 30 23 = 9 :=
    slopeOrbit_step_eval 22 5 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 183 30 24 = 105 :=
    slopeOrbit_step_eval 23 4 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 183 30 25 = 27 :=
    slopeOrbit_step_eval 24 0 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 183 30 26 = 33 :=
    slopeOrbit_step_eval 25 2 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 183 30 27 = 81 :=
    slopeOrbit_step_eval 26 2 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 183 30 28 = 141 :=
    slopeOrbit_step_eval 27 1 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 183 30 29 = 99 :=
    slopeOrbit_step_eval 28 0 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 183 30 30 = 15 :=
    slopeOrbit_step_eval 29 0 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : slopeOrbit 183 30 31 = 57 :=
    slopeOrbit_step_eval 30 3 e30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 183 30 31 = slopeOrbit 183 30 1
    rw [e31, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e26] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e27] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e28] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e29] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide

/-- `(183,30)`: the certified class-1 count cap `|fibre_1| <= 2 * ceil(W/30)`. -/
theorem sreClass1Count_of_datum_183_30 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 183) (hK : (class1SlopeDatum ctx).K₀ = 30) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 30 - 1) / 30) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 30)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_183_30.1
  have hcount : (class1Band4CycleBand ctx 30).card ≤ 2 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_183_30.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 30).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 30 - 1) / 30) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 30 - 1) / 30) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(185,2)`: period `18`, cycle `[71, 99, 13, 23, 183, 181, 177, 169, 153, 121, 57, 43, 159, 133, 81, 139, 93, 1]`, bands `[2, 1, 4, 4, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 8]` - band-4 residue set `{3, 4}` (values `13, 23`), `b4 = 2`. -/
private theorem sreCert_185_2 :
    slopeOrbit 185 2 (1 + 18) = slopeOrbit 185 2 1
      ∧ ∀ j, 1 ≤ j → j ≤ 18 →
          canonGap 185 (slopeOrbit 185 2 j) = 4 → j ∈ ({3, 4} : Finset ℕ) := by
  have e0 : slopeOrbit 185 2 0 = 2 := rfl
  have e1 : slopeOrbit 185 2 1 = 71 :=
    slopeOrbit_step_eval 0 6 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 185 2 2 = 99 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 185 2 3 = 13 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 185 2 4 = 23 :=
    slopeOrbit_step_eval 3 3 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 185 2 5 = 183 :=
    slopeOrbit_step_eval 4 3 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 185 2 6 = 181 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 185 2 7 = 177 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 185 2 8 = 169 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 185 2 9 = 153 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 185 2 10 = 121 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 185 2 11 = 57 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 185 2 12 = 43 :=
    slopeOrbit_step_eval 11 1 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 185 2 13 = 159 :=
    slopeOrbit_step_eval 12 2 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 185 2 14 = 133 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 185 2 15 = 81 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 185 2 16 = 139 :=
    slopeOrbit_step_eval 15 1 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 185 2 17 = 93 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 185 2 18 = 1 :=
    slopeOrbit_step_eval 17 0 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 185 2 19 = 71 :=
    slopeOrbit_step_eval 18 7 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 185 2 19 = slopeOrbit 185 2 1
    rw [e19, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · decide
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(185,2)`: the certified class-1 count cap `|fibre_1| <= 2 * ceil(W/18)`. -/
theorem sreClass1Count_of_datum_185_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 185) (hK : (class1SlopeDatum ctx).K₀ = 2) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 18 - 1) / 18) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 18)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_185_2.1
  have hcount : (class1Band4CycleBand ctx 18).card ≤ 2 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_185_2.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 18).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 18 - 1) / 18) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 18 - 1) / 18) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(185,18)`: period `18`, cycle `[103, 21, 151, 117, 49, 11, 167, 149, 113, 41, 143, 101, 17, 87, 163, 141, 97, 9]`, bands `[1, 4, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 5]` - band-4 residue set `{2, 13}` (values `21, 17`), `b4 = 2`. -/
private theorem sreCert_185_18 :
    slopeOrbit 185 18 (1 + 18) = slopeOrbit 185 18 1
      ∧ ∀ j, 1 ≤ j → j ≤ 18 →
          canonGap 185 (slopeOrbit 185 18 j) = 4 → j ∈ ({2, 13} : Finset ℕ) := by
  have e0 : slopeOrbit 185 18 0 = 18 := rfl
  have e1 : slopeOrbit 185 18 1 = 103 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 185 18 2 = 21 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 185 18 3 = 151 :=
    slopeOrbit_step_eval 2 3 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 185 18 4 = 117 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 185 18 5 = 49 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 185 18 6 = 11 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 185 18 7 = 167 :=
    slopeOrbit_step_eval 6 4 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 185 18 8 = 149 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 185 18 9 = 113 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 185 18 10 = 41 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 185 18 11 = 143 :=
    slopeOrbit_step_eval 10 2 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 185 18 12 = 101 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 185 18 13 = 17 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 185 18 14 = 87 :=
    slopeOrbit_step_eval 13 3 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 185 18 15 = 163 :=
    slopeOrbit_step_eval 14 1 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 185 18 16 = 141 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 185 18 17 = 97 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 185 18 18 = 9 :=
    slopeOrbit_step_eval 17 0 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 185 18 19 = 103 :=
    slopeOrbit_step_eval 18 4 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 185 18 19 = slopeOrbit 185 18 1
    rw [e19, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(185,18)`: the certified class-1 count cap `|fibre_1| <= 2 * ceil(W/18)`. -/
theorem sreClass1Count_of_datum_185_18 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 185) (hK : (class1SlopeDatum ctx).K₀ = 18) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 18 - 1) / 18) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 18)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_185_18.1
  have hcount : (class1Band4CycleBand ctx 18).card ≤ 2 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_185_18.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 18).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 18 - 1) / 18) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 18 - 1) / 18) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(185,92)`: period `18`, cycle `[183, 181, 177, 169, 153, 121, 57, 43, 159, 133, 81, 139, 93, 1, 71, 99, 13, 23]`, bands `[1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 8, 2, 1, 4, 4]` - band-4 residue set `{17, 18}` (values `13, 23`), `b4 = 2`. -/
private theorem sreCert_185_92 :
    slopeOrbit 185 92 (1 + 18) = slopeOrbit 185 92 1
      ∧ ∀ j, 1 ≤ j → j ≤ 18 →
          canonGap 185 (slopeOrbit 185 92 j) = 4 → j ∈ ({17, 18} : Finset ℕ) := by
  have e0 : slopeOrbit 185 92 0 = 92 := rfl
  have e1 : slopeOrbit 185 92 1 = 183 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 185 92 2 = 181 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 185 92 3 = 177 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 185 92 4 = 169 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 185 92 5 = 153 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 185 92 6 = 121 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 185 92 7 = 57 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 185 92 8 = 43 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 185 92 9 = 159 :=
    slopeOrbit_step_eval 8 2 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 185 92 10 = 133 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 185 92 11 = 81 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 185 92 12 = 139 :=
    slopeOrbit_step_eval 11 1 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 185 92 13 = 93 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 185 92 14 = 1 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 185 92 15 = 71 :=
    slopeOrbit_step_eval 14 7 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 185 92 16 = 99 :=
    slopeOrbit_step_eval 15 1 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 185 92 17 = 13 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 185 92 18 = 23 :=
    slopeOrbit_step_eval 17 3 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 185 92 19 = 183 :=
    slopeOrbit_step_eval 18 3 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 185 92 19 = slopeOrbit 185 92 1
    rw [e19, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · decide

/-- `(185,92)`: the certified class-1 count cap `|fibre_1| <= 2 * ceil(W/18)`. -/
theorem sreClass1Count_of_datum_185_92 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 185) (hK : (class1SlopeDatum ctx).K₀ = 92) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 18 - 1) / 18) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 18)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_185_92.1
  have hcount : (class1Band4CycleBand ctx 18).card ≤ 2 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_185_92.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 18).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 18 - 1) / 18) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 18 - 1) / 18) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(187,8)`: period `21`, cycle `[69, 89, 169, 151, 115, 43, 157, 127, 67, 81, 137, 87, 161, 135, 83, 145, 103, 19, 117, 47, 1]`, bands `[2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 4, 1, 2, 8]` - band-4 residue set `{18}` (values `19`), `b4 = 1`. -/
private theorem sreCert_187_8 :
    slopeOrbit 187 8 (1 + 21) = slopeOrbit 187 8 1
      ∧ ∀ j, 1 ≤ j → j ≤ 21 →
          canonGap 187 (slopeOrbit 187 8 j) = 4 → j ∈ ({18} : Finset ℕ) := by
  have e0 : slopeOrbit 187 8 0 = 8 := rfl
  have e1 : slopeOrbit 187 8 1 = 69 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 187 8 2 = 89 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 187 8 3 = 169 :=
    slopeOrbit_step_eval 2 1 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 187 8 4 = 151 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 187 8 5 = 115 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 187 8 6 = 43 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 187 8 7 = 157 :=
    slopeOrbit_step_eval 6 2 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 187 8 8 = 127 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 187 8 9 = 67 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 187 8 10 = 81 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 187 8 11 = 137 :=
    slopeOrbit_step_eval 10 1 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 187 8 12 = 87 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 187 8 13 = 161 :=
    slopeOrbit_step_eval 12 1 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 187 8 14 = 135 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 187 8 15 = 83 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 187 8 16 = 145 :=
    slopeOrbit_step_eval 15 1 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 187 8 17 = 103 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 187 8 18 = 19 :=
    slopeOrbit_step_eval 17 0 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 187 8 19 = 117 :=
    slopeOrbit_step_eval 18 3 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 187 8 20 = 47 :=
    slopeOrbit_step_eval 19 0 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 187 8 21 = 1 :=
    slopeOrbit_step_eval 20 1 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 187 8 22 = 69 :=
    slopeOrbit_step_eval 21 7 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 187 8 22 = slopeOrbit 187 8 1
    rw [e22, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(187,8)`: the certified class-1 count cap `|fibre_1| <= 1 * ceil(W/21)`. -/
theorem sreClass1Count_of_datum_187_8 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 187) (hK : (class1SlopeDatum ctx).K₀ = 8) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 21 - 1) / 21) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 21)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_187_8.1
  have hcount : (class1Band4CycleBand ctx 21).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_187_8.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 21).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 21 - 1) / 21) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 21 - 1) / 21) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(187,93)`: period `19`, cycle `[185, 183, 179, 171, 155, 123, 59, 49, 9, 101, 15, 53, 25, 13, 21, 149, 111, 35, 93]`, bands `[1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 4, 2, 3, 4, 4, 1, 1, 3, 2]` - band-4 residue set `{11, 14, 15}` (values `15, 13, 21`), `b4 = 3`. -/
private theorem sreCert_187_93 :
    slopeOrbit 187 93 (1 + 19) = slopeOrbit 187 93 1
      ∧ ∀ j, 1 ≤ j → j ≤ 19 →
          canonGap 187 (slopeOrbit 187 93 j) = 4 → j ∈ ({11, 14, 15} : Finset ℕ) := by
  have e0 : slopeOrbit 187 93 0 = 93 := rfl
  have e1 : slopeOrbit 187 93 1 = 185 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 187 93 2 = 183 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 187 93 3 = 179 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 187 93 4 = 171 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 187 93 5 = 155 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 187 93 6 = 123 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 187 93 7 = 59 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 187 93 8 = 49 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 187 93 9 = 9 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 187 93 10 = 101 :=
    slopeOrbit_step_eval 9 4 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 187 93 11 = 15 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 187 93 12 = 53 :=
    slopeOrbit_step_eval 11 3 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 187 93 13 = 25 :=
    slopeOrbit_step_eval 12 1 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 187 93 14 = 13 :=
    slopeOrbit_step_eval 13 2 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 187 93 15 = 21 :=
    slopeOrbit_step_eval 14 3 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 187 93 16 = 149 :=
    slopeOrbit_step_eval 15 3 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 187 93 17 = 111 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 187 93 18 = 35 :=
    slopeOrbit_step_eval 17 0 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 187 93 19 = 93 :=
    slopeOrbit_step_eval 18 2 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 187 93 20 = 185 :=
    slopeOrbit_step_eval 19 1 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 187 93 20 = slopeOrbit 187 93 1
    rw [e20, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · decide
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))

/-- `(187,93)`: the certified class-1 count cap `|fibre_1| <= 3 * ceil(W/19)`. -/
theorem sreClass1Count_of_datum_187_93 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 187) (hK : (class1SlopeDatum ctx).K₀ = 93) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 3 * (((supportShell ctx.shell.d ctx.shell.X).card + 19 - 1) / 19) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 19)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_187_93.1
  have hcount : (class1Band4CycleBand ctx 19).card ≤ 3 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_187_93.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 19).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 19 - 1) / 19) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 3 * (((supportShell ctx.shell.d ctx.shell.X).card + 19 - 1) / 19) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(189,10)`: period `8`, cycle `[131, 73, 103, 17, 83, 143, 97, 5]`, bands `[1, 2, 1, 4, 2, 1, 1, 6]` - band-4 residue set `{4}` (values `17`), `b4 = 1`. -/
private theorem sreCert_189_10 :
    slopeOrbit 189 10 (1 + 8) = slopeOrbit 189 10 1
      ∧ ∀ j, 1 ≤ j → j ≤ 8 →
          canonGap 189 (slopeOrbit 189 10 j) = 4 → j ∈ ({4} : Finset ℕ) := by
  have e0 : slopeOrbit 189 10 0 = 10 := rfl
  have e1 : slopeOrbit 189 10 1 = 131 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 189 10 2 = 73 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 189 10 3 = 103 :=
    slopeOrbit_step_eval 2 1 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 189 10 4 = 17 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 189 10 5 = 83 :=
    slopeOrbit_step_eval 4 3 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 189 10 6 = 143 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 189 10 7 = 97 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 189 10 8 = 5 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 189 10 9 = 131 :=
    slopeOrbit_step_eval 8 5 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 189 10 9 = slopeOrbit 189 10 1
    rw [e9, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(189,10)`: the certified class-1 count cap `|fibre_1| <= 1 * ceil(W/8)`. -/
theorem sreClass1Count_of_datum_189_10 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 189) (hK : (class1SlopeDatum ctx).K₀ = 10) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 8 - 1) / 8) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 8)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_189_10.1
  have hcount : (class1Band4CycleBand ctx 8).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_189_10.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 8).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 8 - 1) / 8) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 8 - 1) / 8) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(189,13)`: period `9`, cycle `[19, 115, 41, 139, 89, 167, 145, 101, 13]`, bands `[4, 1, 3, 1, 2, 1, 1, 1, 4]` - band-4 residue set `{1, 9}` (values `19, 13`), `b4 = 2`. -/
private theorem sreCert_189_13 :
    slopeOrbit 189 13 (1 + 9) = slopeOrbit 189 13 1
      ∧ ∀ j, 1 ≤ j → j ≤ 9 →
          canonGap 189 (slopeOrbit 189 13 j) = 4 → j ∈ ({1, 9} : Finset ℕ) := by
  have e0 : slopeOrbit 189 13 0 = 13 := rfl
  have e1 : slopeOrbit 189 13 1 = 19 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 189 13 2 = 115 :=
    slopeOrbit_step_eval 1 3 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 189 13 3 = 41 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 189 13 4 = 139 :=
    slopeOrbit_step_eval 3 2 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 189 13 5 = 89 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 189 13 6 = 167 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 189 13 7 = 145 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 189 13 8 = 101 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 189 13 9 = 13 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 189 13 10 = 19 :=
    slopeOrbit_step_eval 9 3 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 189 13 10 = slopeOrbit 189 13 1
    rw [e10, e1]
  · intro j h1 h2 hband
    interval_cases j
    · decide
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide

/-- `(189,13)`: the certified class-1 count cap `|fibre_1| <= 2 * ceil(W/9)`. -/
theorem sreClass1Count_of_datum_189_13 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 189) (hK : (class1SlopeDatum ctx).K₀ = 13) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 9 - 1) / 9) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 9)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_189_13.1
  have hcount : (class1Band4CycleBand ctx 9).card ≤ 2 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_189_13.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 9).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 9 - 1) / 9) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 9 - 1) / 9) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(191,95)`: period `54`, cycle `[189, 187, 183, 175, 159, 127, 63, 61, 53, 21, 145, 99, 7, 33, 73, 101, 11, 161, 131, 71, 93, 181, 171, 151, 111, 31, 57, 37, 105, 19, 113, 35, 89, 165, 139, 87, 157, 123, 55, 29, 41, 137, 83, 141, 91, 173, 155, 119, 47, 185, 179, 167, 143, 95]`, bands `[1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 5, 3, 2, 1, 5, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 3, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2]` - band-4 residue set `{10, 30}` (values `21, 19`), `b4 = 2`. -/
private theorem sreCert_191_95 :
    slopeOrbit 191 95 (1 + 54) = slopeOrbit 191 95 1
      ∧ ∀ j, 1 ≤ j → j ≤ 54 →
          canonGap 191 (slopeOrbit 191 95 j) = 4 → j ∈ ({10, 30} : Finset ℕ) := by
  have e0 : slopeOrbit 191 95 0 = 95 := rfl
  have e1 : slopeOrbit 191 95 1 = 189 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 191 95 2 = 187 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 191 95 3 = 183 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 191 95 4 = 175 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 191 95 5 = 159 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 191 95 6 = 127 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 191 95 7 = 63 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 191 95 8 = 61 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 191 95 9 = 53 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 191 95 10 = 21 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 191 95 11 = 145 :=
    slopeOrbit_step_eval 10 3 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 191 95 12 = 99 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 191 95 13 = 7 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 191 95 14 = 33 :=
    slopeOrbit_step_eval 13 4 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 191 95 15 = 73 :=
    slopeOrbit_step_eval 14 2 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 191 95 16 = 101 :=
    slopeOrbit_step_eval 15 1 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 191 95 17 = 11 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 191 95 18 = 161 :=
    slopeOrbit_step_eval 17 4 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 191 95 19 = 131 :=
    slopeOrbit_step_eval 18 0 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 191 95 20 = 71 :=
    slopeOrbit_step_eval 19 0 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 191 95 21 = 93 :=
    slopeOrbit_step_eval 20 1 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 191 95 22 = 181 :=
    slopeOrbit_step_eval 21 1 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 191 95 23 = 171 :=
    slopeOrbit_step_eval 22 0 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 191 95 24 = 151 :=
    slopeOrbit_step_eval 23 0 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 191 95 25 = 111 :=
    slopeOrbit_step_eval 24 0 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 191 95 26 = 31 :=
    slopeOrbit_step_eval 25 0 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 191 95 27 = 57 :=
    slopeOrbit_step_eval 26 2 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 191 95 28 = 37 :=
    slopeOrbit_step_eval 27 1 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 191 95 29 = 105 :=
    slopeOrbit_step_eval 28 2 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 191 95 30 = 19 :=
    slopeOrbit_step_eval 29 0 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : slopeOrbit 191 95 31 = 113 :=
    slopeOrbit_step_eval 30 3 e30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e32 : slopeOrbit 191 95 32 = 35 :=
    slopeOrbit_step_eval 31 0 e31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e33 : slopeOrbit 191 95 33 = 89 :=
    slopeOrbit_step_eval 32 2 e32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e34 : slopeOrbit 191 95 34 = 165 :=
    slopeOrbit_step_eval 33 1 e33 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e35 : slopeOrbit 191 95 35 = 139 :=
    slopeOrbit_step_eval 34 0 e34 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e36 : slopeOrbit 191 95 36 = 87 :=
    slopeOrbit_step_eval 35 0 e35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e37 : slopeOrbit 191 95 37 = 157 :=
    slopeOrbit_step_eval 36 1 e36 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e38 : slopeOrbit 191 95 38 = 123 :=
    slopeOrbit_step_eval 37 0 e37 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e39 : slopeOrbit 191 95 39 = 55 :=
    slopeOrbit_step_eval 38 0 e38 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e40 : slopeOrbit 191 95 40 = 29 :=
    slopeOrbit_step_eval 39 1 e39 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e41 : slopeOrbit 191 95 41 = 41 :=
    slopeOrbit_step_eval 40 2 e40 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e42 : slopeOrbit 191 95 42 = 137 :=
    slopeOrbit_step_eval 41 2 e41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e43 : slopeOrbit 191 95 43 = 83 :=
    slopeOrbit_step_eval 42 0 e42 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e44 : slopeOrbit 191 95 44 = 141 :=
    slopeOrbit_step_eval 43 1 e43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e45 : slopeOrbit 191 95 45 = 91 :=
    slopeOrbit_step_eval 44 0 e44 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e46 : slopeOrbit 191 95 46 = 173 :=
    slopeOrbit_step_eval 45 1 e45 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e47 : slopeOrbit 191 95 47 = 155 :=
    slopeOrbit_step_eval 46 0 e46 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e48 : slopeOrbit 191 95 48 = 119 :=
    slopeOrbit_step_eval 47 0 e47 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e49 : slopeOrbit 191 95 49 = 47 :=
    slopeOrbit_step_eval 48 0 e48 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e50 : slopeOrbit 191 95 50 = 185 :=
    slopeOrbit_step_eval 49 2 e49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e51 : slopeOrbit 191 95 51 = 179 :=
    slopeOrbit_step_eval 50 0 e50 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e52 : slopeOrbit 191 95 52 = 167 :=
    slopeOrbit_step_eval 51 0 e51 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e53 : slopeOrbit 191 95 53 = 143 :=
    slopeOrbit_step_eval 52 0 e52 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e54 : slopeOrbit 191 95 54 = 95 :=
    slopeOrbit_step_eval 53 0 e53 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e55 : slopeOrbit 191 95 55 = 189 :=
    slopeOrbit_step_eval 54 1 e54 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 191 95 55 = slopeOrbit 191 95 1
    rw [e55, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e26] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e27] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e28] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e29] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e31] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e32] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e33] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e34] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e35] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e36] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e37] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e38] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e39] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e40] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e41] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e42] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e43] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e44] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e45] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e46] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e47] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e48] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e49] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e50] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e51] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e52] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e53] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e54] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))

/-- `(191,95)`: the certified class-1 count cap `|fibre_1| <= 2 * ceil(W/54)`. -/
theorem sreClass1Count_of_datum_191_95 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 191) (hK : (class1SlopeDatum ctx).K₀ = 95) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 54 - 1) / 54) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 54)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_191_95.1
  have hcount : (class1Band4CycleBand ctx 54).card ≤ 2 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_191_95.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 54).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 54 - 1) / 54) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 54 - 1) / 54) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(193,96)`: period `48`, cycle `[191, 189, 185, 177, 161, 129, 65, 67, 75, 107, 21, 143, 93, 179, 165, 137, 81, 131, 69, 83, 139, 85, 147, 101, 9, 95, 187, 181, 169, 145, 97, 1, 63, 59, 43, 151, 109, 25, 7, 31, 55, 27, 23, 175, 157, 121, 49, 3]`, bands `[1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 8, 2, 2, 3, 1, 1, 3, 5, 3, 2, 3, 4, 1, 1, 1, 2, 7]` - band-4 residue set `{11, 43}` (values `21, 23`), `b4 = 2`. -/
private theorem sreCert_193_96 :
    slopeOrbit 193 96 (1 + 48) = slopeOrbit 193 96 1
      ∧ ∀ j, 1 ≤ j → j ≤ 48 →
          canonGap 193 (slopeOrbit 193 96 j) = 4 → j ∈ ({11, 43} : Finset ℕ) := by
  have e0 : slopeOrbit 193 96 0 = 96 := rfl
  have e1 : slopeOrbit 193 96 1 = 191 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 193 96 2 = 189 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 193 96 3 = 185 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 193 96 4 = 177 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 193 96 5 = 161 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 193 96 6 = 129 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 193 96 7 = 65 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 193 96 8 = 67 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 193 96 9 = 75 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 193 96 10 = 107 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 193 96 11 = 21 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 193 96 12 = 143 :=
    slopeOrbit_step_eval 11 3 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 193 96 13 = 93 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 193 96 14 = 179 :=
    slopeOrbit_step_eval 13 1 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 193 96 15 = 165 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 193 96 16 = 137 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 193 96 17 = 81 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 193 96 18 = 131 :=
    slopeOrbit_step_eval 17 1 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 193 96 19 = 69 :=
    slopeOrbit_step_eval 18 0 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 193 96 20 = 83 :=
    slopeOrbit_step_eval 19 1 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 193 96 21 = 139 :=
    slopeOrbit_step_eval 20 1 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 193 96 22 = 85 :=
    slopeOrbit_step_eval 21 0 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 193 96 23 = 147 :=
    slopeOrbit_step_eval 22 1 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 193 96 24 = 101 :=
    slopeOrbit_step_eval 23 0 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 193 96 25 = 9 :=
    slopeOrbit_step_eval 24 0 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 193 96 26 = 95 :=
    slopeOrbit_step_eval 25 4 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 193 96 27 = 187 :=
    slopeOrbit_step_eval 26 1 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 193 96 28 = 181 :=
    slopeOrbit_step_eval 27 0 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 193 96 29 = 169 :=
    slopeOrbit_step_eval 28 0 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 193 96 30 = 145 :=
    slopeOrbit_step_eval 29 0 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : slopeOrbit 193 96 31 = 97 :=
    slopeOrbit_step_eval 30 0 e30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e32 : slopeOrbit 193 96 32 = 1 :=
    slopeOrbit_step_eval 31 0 e31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e33 : slopeOrbit 193 96 33 = 63 :=
    slopeOrbit_step_eval 32 7 e32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e34 : slopeOrbit 193 96 34 = 59 :=
    slopeOrbit_step_eval 33 1 e33 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e35 : slopeOrbit 193 96 35 = 43 :=
    slopeOrbit_step_eval 34 1 e34 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e36 : slopeOrbit 193 96 36 = 151 :=
    slopeOrbit_step_eval 35 2 e35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e37 : slopeOrbit 193 96 37 = 109 :=
    slopeOrbit_step_eval 36 0 e36 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e38 : slopeOrbit 193 96 38 = 25 :=
    slopeOrbit_step_eval 37 0 e37 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e39 : slopeOrbit 193 96 39 = 7 :=
    slopeOrbit_step_eval 38 2 e38 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e40 : slopeOrbit 193 96 40 = 31 :=
    slopeOrbit_step_eval 39 4 e39 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e41 : slopeOrbit 193 96 41 = 55 :=
    slopeOrbit_step_eval 40 2 e40 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e42 : slopeOrbit 193 96 42 = 27 :=
    slopeOrbit_step_eval 41 1 e41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e43 : slopeOrbit 193 96 43 = 23 :=
    slopeOrbit_step_eval 42 2 e42 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e44 : slopeOrbit 193 96 44 = 175 :=
    slopeOrbit_step_eval 43 3 e43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e45 : slopeOrbit 193 96 45 = 157 :=
    slopeOrbit_step_eval 44 0 e44 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e46 : slopeOrbit 193 96 46 = 121 :=
    slopeOrbit_step_eval 45 0 e45 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e47 : slopeOrbit 193 96 47 = 49 :=
    slopeOrbit_step_eval 46 0 e46 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e48 : slopeOrbit 193 96 48 = 3 :=
    slopeOrbit_step_eval 47 1 e47 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e49 : slopeOrbit 193 96 49 = 191 :=
    slopeOrbit_step_eval 48 6 e48 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 193 96 49 = slopeOrbit 193 96 1
    rw [e49, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e26] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e27] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e28] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e29] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e30] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e31] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e32] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e33] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e34] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e35] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e36] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e37] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e38] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e39] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e40] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e41] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e42] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e44] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e45] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e46] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e47] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e48] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(193,96)`: the certified class-1 count cap `|fibre_1| <= 2 * ceil(W/48)`. -/
theorem sreClass1Count_of_datum_193_96 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 193) (hK : (class1SlopeDatum ctx).K₀ = 96) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 48 - 1) / 48) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 48)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_193_96.1
  have hcount : (class1Band4CycleBand ctx 48).card ≤ 2 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_193_96.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 48).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 48 - 1) / 48) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 48 - 1) / 48) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(195,19)`: period `6`, cycle `[109, 23, 173, 151, 107, 19]`, bands `[1, 4, 1, 1, 1, 4]` - band-4 residue set `{2, 6}` (values `23, 19`), `b4 = 2`. -/
private theorem sreCert_195_19 :
    slopeOrbit 195 19 (1 + 6) = slopeOrbit 195 19 1
      ∧ ∀ j, 1 ≤ j → j ≤ 6 →
          canonGap 195 (slopeOrbit 195 19 j) = 4 → j ∈ ({2, 6} : Finset ℕ) := by
  have e0 : slopeOrbit 195 19 0 = 19 := rfl
  have e1 : slopeOrbit 195 19 1 = 109 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 195 19 2 = 23 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 195 19 3 = 173 :=
    slopeOrbit_step_eval 2 3 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 195 19 4 = 151 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 195 19 5 = 107 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 195 19 6 = 19 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 195 19 7 = 109 :=
    slopeOrbit_step_eval 6 3 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 195 19 7 = slopeOrbit 195 19 1
    rw [e7, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide

/-- `(195,19)`: the certified class-1 count cap `|fibre_1| <= 2 * ceil(W/6)`. -/
theorem sreClass1Count_of_datum_195_19 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 195) (hK : (class1SlopeDatum ctx).K₀ = 19) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 6 - 1) / 6) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 6)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_195_19.1
  have hcount : (class1Band4CycleBand ctx 6).card ≤ 2 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_195_19.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 6).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 6 - 1) / 6) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 6 - 1) / 6) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(197,98)`: period `98`, cycle `[195, 193, 189, 181, 165, 133, 69, 79, 119, 41, 131, 65, 63, 55, 23, 171, 145, 93, 175, 153, 109, 21, 139, 81, 127, 57, 31, 51, 7, 27, 19, 107, 17, 75, 103, 9, 91, 167, 137, 77, 111, 25, 3, 187, 177, 157, 117, 37, 99, 1, 59, 39, 115, 33, 67, 71, 87, 151, 105, 13, 11, 155, 113, 29, 35, 83, 135, 73, 95, 183, 169, 141, 85, 143, 89, 159, 121, 45, 163, 129, 61, 47, 179, 161, 125, 53, 15, 43, 147, 97, 191, 185, 173, 149, 101, 5, 123, 49]`, bands `[1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 4, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 5, 3, 4, 1, 4, 2, 1, 5, 2, 1, 1, 2, 1, 3, 7, 1, 1, 1, 1, 3, 1, 8, 2, 3, 1, 3, 2, 2, 2, 1, 1, 4, 5, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 1, 1, 6, 1, 3]` - band-4 residue set `{15, 22, 31, 33, 60, 87}` (values `23, 21, 19, 17, 13, 15`), `b4 = 6`. -/
private theorem sreCert_197_98 :
    slopeOrbit 197 98 (1 + 98) = slopeOrbit 197 98 1
      ∧ ∀ j, 1 ≤ j → j ≤ 98 →
          canonGap 197 (slopeOrbit 197 98 j) = 4 → j ∈ ({15, 22, 31, 33, 60, 87} : Finset ℕ) := by
  have e0 : slopeOrbit 197 98 0 = 98 := rfl
  have e1 : slopeOrbit 197 98 1 = 195 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 197 98 2 = 193 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 197 98 3 = 189 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 197 98 4 = 181 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 197 98 5 = 165 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 197 98 6 = 133 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 197 98 7 = 69 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 197 98 8 = 79 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 197 98 9 = 119 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 197 98 10 = 41 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 197 98 11 = 131 :=
    slopeOrbit_step_eval 10 2 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 197 98 12 = 65 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 197 98 13 = 63 :=
    slopeOrbit_step_eval 12 1 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 197 98 14 = 55 :=
    slopeOrbit_step_eval 13 1 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 197 98 15 = 23 :=
    slopeOrbit_step_eval 14 1 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 197 98 16 = 171 :=
    slopeOrbit_step_eval 15 3 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 197 98 17 = 145 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 197 98 18 = 93 :=
    slopeOrbit_step_eval 17 0 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 197 98 19 = 175 :=
    slopeOrbit_step_eval 18 1 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 197 98 20 = 153 :=
    slopeOrbit_step_eval 19 0 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 197 98 21 = 109 :=
    slopeOrbit_step_eval 20 0 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 197 98 22 = 21 :=
    slopeOrbit_step_eval 21 0 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 197 98 23 = 139 :=
    slopeOrbit_step_eval 22 3 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 197 98 24 = 81 :=
    slopeOrbit_step_eval 23 0 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 197 98 25 = 127 :=
    slopeOrbit_step_eval 24 1 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 197 98 26 = 57 :=
    slopeOrbit_step_eval 25 0 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 197 98 27 = 31 :=
    slopeOrbit_step_eval 26 1 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 197 98 28 = 51 :=
    slopeOrbit_step_eval 27 2 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 197 98 29 = 7 :=
    slopeOrbit_step_eval 28 1 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 197 98 30 = 27 :=
    slopeOrbit_step_eval 29 4 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : slopeOrbit 197 98 31 = 19 :=
    slopeOrbit_step_eval 30 2 e30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e32 : slopeOrbit 197 98 32 = 107 :=
    slopeOrbit_step_eval 31 3 e31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e33 : slopeOrbit 197 98 33 = 17 :=
    slopeOrbit_step_eval 32 0 e32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e34 : slopeOrbit 197 98 34 = 75 :=
    slopeOrbit_step_eval 33 3 e33 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e35 : slopeOrbit 197 98 35 = 103 :=
    slopeOrbit_step_eval 34 1 e34 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e36 : slopeOrbit 197 98 36 = 9 :=
    slopeOrbit_step_eval 35 0 e35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e37 : slopeOrbit 197 98 37 = 91 :=
    slopeOrbit_step_eval 36 4 e36 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e38 : slopeOrbit 197 98 38 = 167 :=
    slopeOrbit_step_eval 37 1 e37 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e39 : slopeOrbit 197 98 39 = 137 :=
    slopeOrbit_step_eval 38 0 e38 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e40 : slopeOrbit 197 98 40 = 77 :=
    slopeOrbit_step_eval 39 0 e39 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e41 : slopeOrbit 197 98 41 = 111 :=
    slopeOrbit_step_eval 40 1 e40 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e42 : slopeOrbit 197 98 42 = 25 :=
    slopeOrbit_step_eval 41 0 e41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e43 : slopeOrbit 197 98 43 = 3 :=
    slopeOrbit_step_eval 42 2 e42 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e44 : slopeOrbit 197 98 44 = 187 :=
    slopeOrbit_step_eval 43 6 e43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e45 : slopeOrbit 197 98 45 = 177 :=
    slopeOrbit_step_eval 44 0 e44 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e46 : slopeOrbit 197 98 46 = 157 :=
    slopeOrbit_step_eval 45 0 e45 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e47 : slopeOrbit 197 98 47 = 117 :=
    slopeOrbit_step_eval 46 0 e46 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e48 : slopeOrbit 197 98 48 = 37 :=
    slopeOrbit_step_eval 47 0 e47 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e49 : slopeOrbit 197 98 49 = 99 :=
    slopeOrbit_step_eval 48 2 e48 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e50 : slopeOrbit 197 98 50 = 1 :=
    slopeOrbit_step_eval 49 0 e49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e51 : slopeOrbit 197 98 51 = 59 :=
    slopeOrbit_step_eval 50 7 e50 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e52 : slopeOrbit 197 98 52 = 39 :=
    slopeOrbit_step_eval 51 1 e51 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e53 : slopeOrbit 197 98 53 = 115 :=
    slopeOrbit_step_eval 52 2 e52 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e54 : slopeOrbit 197 98 54 = 33 :=
    slopeOrbit_step_eval 53 0 e53 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e55 : slopeOrbit 197 98 55 = 67 :=
    slopeOrbit_step_eval 54 2 e54 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e56 : slopeOrbit 197 98 56 = 71 :=
    slopeOrbit_step_eval 55 1 e55 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e57 : slopeOrbit 197 98 57 = 87 :=
    slopeOrbit_step_eval 56 1 e56 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e58 : slopeOrbit 197 98 58 = 151 :=
    slopeOrbit_step_eval 57 1 e57 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e59 : slopeOrbit 197 98 59 = 105 :=
    slopeOrbit_step_eval 58 0 e58 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e60 : slopeOrbit 197 98 60 = 13 :=
    slopeOrbit_step_eval 59 0 e59 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e61 : slopeOrbit 197 98 61 = 11 :=
    slopeOrbit_step_eval 60 3 e60 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e62 : slopeOrbit 197 98 62 = 155 :=
    slopeOrbit_step_eval 61 4 e61 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e63 : slopeOrbit 197 98 63 = 113 :=
    slopeOrbit_step_eval 62 0 e62 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e64 : slopeOrbit 197 98 64 = 29 :=
    slopeOrbit_step_eval 63 0 e63 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e65 : slopeOrbit 197 98 65 = 35 :=
    slopeOrbit_step_eval 64 2 e64 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e66 : slopeOrbit 197 98 66 = 83 :=
    slopeOrbit_step_eval 65 2 e65 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e67 : slopeOrbit 197 98 67 = 135 :=
    slopeOrbit_step_eval 66 1 e66 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e68 : slopeOrbit 197 98 68 = 73 :=
    slopeOrbit_step_eval 67 0 e67 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e69 : slopeOrbit 197 98 69 = 95 :=
    slopeOrbit_step_eval 68 1 e68 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e70 : slopeOrbit 197 98 70 = 183 :=
    slopeOrbit_step_eval 69 1 e69 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e71 : slopeOrbit 197 98 71 = 169 :=
    slopeOrbit_step_eval 70 0 e70 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e72 : slopeOrbit 197 98 72 = 141 :=
    slopeOrbit_step_eval 71 0 e71 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e73 : slopeOrbit 197 98 73 = 85 :=
    slopeOrbit_step_eval 72 0 e72 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e74 : slopeOrbit 197 98 74 = 143 :=
    slopeOrbit_step_eval 73 1 e73 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e75 : slopeOrbit 197 98 75 = 89 :=
    slopeOrbit_step_eval 74 0 e74 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e76 : slopeOrbit 197 98 76 = 159 :=
    slopeOrbit_step_eval 75 1 e75 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e77 : slopeOrbit 197 98 77 = 121 :=
    slopeOrbit_step_eval 76 0 e76 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e78 : slopeOrbit 197 98 78 = 45 :=
    slopeOrbit_step_eval 77 0 e77 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e79 : slopeOrbit 197 98 79 = 163 :=
    slopeOrbit_step_eval 78 2 e78 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e80 : slopeOrbit 197 98 80 = 129 :=
    slopeOrbit_step_eval 79 0 e79 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e81 : slopeOrbit 197 98 81 = 61 :=
    slopeOrbit_step_eval 80 0 e80 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e82 : slopeOrbit 197 98 82 = 47 :=
    slopeOrbit_step_eval 81 1 e81 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e83 : slopeOrbit 197 98 83 = 179 :=
    slopeOrbit_step_eval 82 2 e82 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e84 : slopeOrbit 197 98 84 = 161 :=
    slopeOrbit_step_eval 83 0 e83 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e85 : slopeOrbit 197 98 85 = 125 :=
    slopeOrbit_step_eval 84 0 e84 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e86 : slopeOrbit 197 98 86 = 53 :=
    slopeOrbit_step_eval 85 0 e85 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e87 : slopeOrbit 197 98 87 = 15 :=
    slopeOrbit_step_eval 86 1 e86 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e88 : slopeOrbit 197 98 88 = 43 :=
    slopeOrbit_step_eval 87 3 e87 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e89 : slopeOrbit 197 98 89 = 147 :=
    slopeOrbit_step_eval 88 2 e88 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e90 : slopeOrbit 197 98 90 = 97 :=
    slopeOrbit_step_eval 89 0 e89 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e91 : slopeOrbit 197 98 91 = 191 :=
    slopeOrbit_step_eval 90 1 e90 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e92 : slopeOrbit 197 98 92 = 185 :=
    slopeOrbit_step_eval 91 0 e91 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e93 : slopeOrbit 197 98 93 = 173 :=
    slopeOrbit_step_eval 92 0 e92 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e94 : slopeOrbit 197 98 94 = 149 :=
    slopeOrbit_step_eval 93 0 e93 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e95 : slopeOrbit 197 98 95 = 101 :=
    slopeOrbit_step_eval 94 0 e94 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e96 : slopeOrbit 197 98 96 = 5 :=
    slopeOrbit_step_eval 95 0 e95 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e97 : slopeOrbit 197 98 97 = 123 :=
    slopeOrbit_step_eval 96 5 e96 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e98 : slopeOrbit 197 98 98 = 49 :=
    slopeOrbit_step_eval 97 0 e97 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e99 : slopeOrbit 197 98 99 = 195 :=
    slopeOrbit_step_eval 98 2 e98 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 197 98 99 = slopeOrbit 197 98 1
    rw [e99, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e26] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e27] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e28] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e29] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e30] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e32] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e34] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e35] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e36] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e37] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e38] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e39] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e40] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e41] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e42] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e43] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e44] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e45] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e46] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e47] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e48] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e49] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e50] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e51] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e52] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e53] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e54] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e55] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e56] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e57] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e58] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e59] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e61] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e62] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e63] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e64] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e65] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e66] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e67] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e68] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e69] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e70] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e71] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e72] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e73] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e74] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e75] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e76] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e77] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e78] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e79] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e80] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e81] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e82] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e83] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e84] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e85] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e86] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e88] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e89] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e90] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e91] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e92] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e93] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e94] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e95] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e96] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e97] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e98] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))

/-- `(197,98)`: the certified class-1 count cap `|fibre_1| <= 6 * ceil(W/98)`. -/
theorem sreClass1Count_of_datum_197_98 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 197) (hK : (class1SlopeDatum ctx).K₀ = 98) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 6 * (((supportShell ctx.shell.d ctx.shell.X).card + 98 - 1) / 98) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 98)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_197_98.1
  have hcount : (class1Band4CycleBand ctx 98).card ≤ 6 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_197_98.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 98).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 98 - 1) / 98) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 6 * (((supportShell ctx.shell.d ctx.shell.X).card + 98 - 1) / 98) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(199,99)`: period `54`, cycle `[197, 195, 191, 183, 167, 135, 71, 85, 141, 83, 133, 67, 69, 77, 109, 19, 105, 11, 153, 107, 15, 41, 129, 59, 37, 97, 189, 179, 159, 119, 39, 113, 27, 17, 73, 93, 173, 147, 95, 181, 163, 127, 55, 21, 137, 75, 101, 3, 185, 171, 143, 87, 149, 99]`, bands `[1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 4, 1, 5, 1, 1, 4, 3, 1, 2, 3, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 1, 7, 1, 1, 1, 2, 1, 2]` - band-4 residue set `{16, 21, 34, 44}` (values `19, 15, 17, 21`), `b4 = 4`. -/
private theorem sreCert_199_99 :
    slopeOrbit 199 99 (1 + 54) = slopeOrbit 199 99 1
      ∧ ∀ j, 1 ≤ j → j ≤ 54 →
          canonGap 199 (slopeOrbit 199 99 j) = 4 → j ∈ ({16, 21, 34, 44} : Finset ℕ) := by
  have e0 : slopeOrbit 199 99 0 = 99 := rfl
  have e1 : slopeOrbit 199 99 1 = 197 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 199 99 2 = 195 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 199 99 3 = 191 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 199 99 4 = 183 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 199 99 5 = 167 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 199 99 6 = 135 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 199 99 7 = 71 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 199 99 8 = 85 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 199 99 9 = 141 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 199 99 10 = 83 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 199 99 11 = 133 :=
    slopeOrbit_step_eval 10 1 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 199 99 12 = 67 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 199 99 13 = 69 :=
    slopeOrbit_step_eval 12 1 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 199 99 14 = 77 :=
    slopeOrbit_step_eval 13 1 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 199 99 15 = 109 :=
    slopeOrbit_step_eval 14 1 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 199 99 16 = 19 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 199 99 17 = 105 :=
    slopeOrbit_step_eval 16 3 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 199 99 18 = 11 :=
    slopeOrbit_step_eval 17 0 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 199 99 19 = 153 :=
    slopeOrbit_step_eval 18 4 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 199 99 20 = 107 :=
    slopeOrbit_step_eval 19 0 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 199 99 21 = 15 :=
    slopeOrbit_step_eval 20 0 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 199 99 22 = 41 :=
    slopeOrbit_step_eval 21 3 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 199 99 23 = 129 :=
    slopeOrbit_step_eval 22 2 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 199 99 24 = 59 :=
    slopeOrbit_step_eval 23 0 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 199 99 25 = 37 :=
    slopeOrbit_step_eval 24 1 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 199 99 26 = 97 :=
    slopeOrbit_step_eval 25 2 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 199 99 27 = 189 :=
    slopeOrbit_step_eval 26 1 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 199 99 28 = 179 :=
    slopeOrbit_step_eval 27 0 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 199 99 29 = 159 :=
    slopeOrbit_step_eval 28 0 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 199 99 30 = 119 :=
    slopeOrbit_step_eval 29 0 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : slopeOrbit 199 99 31 = 39 :=
    slopeOrbit_step_eval 30 0 e30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e32 : slopeOrbit 199 99 32 = 113 :=
    slopeOrbit_step_eval 31 2 e31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e33 : slopeOrbit 199 99 33 = 27 :=
    slopeOrbit_step_eval 32 0 e32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e34 : slopeOrbit 199 99 34 = 17 :=
    slopeOrbit_step_eval 33 2 e33 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e35 : slopeOrbit 199 99 35 = 73 :=
    slopeOrbit_step_eval 34 3 e34 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e36 : slopeOrbit 199 99 36 = 93 :=
    slopeOrbit_step_eval 35 1 e35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e37 : slopeOrbit 199 99 37 = 173 :=
    slopeOrbit_step_eval 36 1 e36 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e38 : slopeOrbit 199 99 38 = 147 :=
    slopeOrbit_step_eval 37 0 e37 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e39 : slopeOrbit 199 99 39 = 95 :=
    slopeOrbit_step_eval 38 0 e38 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e40 : slopeOrbit 199 99 40 = 181 :=
    slopeOrbit_step_eval 39 1 e39 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e41 : slopeOrbit 199 99 41 = 163 :=
    slopeOrbit_step_eval 40 0 e40 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e42 : slopeOrbit 199 99 42 = 127 :=
    slopeOrbit_step_eval 41 0 e41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e43 : slopeOrbit 199 99 43 = 55 :=
    slopeOrbit_step_eval 42 0 e42 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e44 : slopeOrbit 199 99 44 = 21 :=
    slopeOrbit_step_eval 43 1 e43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e45 : slopeOrbit 199 99 45 = 137 :=
    slopeOrbit_step_eval 44 3 e44 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e46 : slopeOrbit 199 99 46 = 75 :=
    slopeOrbit_step_eval 45 0 e45 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e47 : slopeOrbit 199 99 47 = 101 :=
    slopeOrbit_step_eval 46 1 e46 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e48 : slopeOrbit 199 99 48 = 3 :=
    slopeOrbit_step_eval 47 0 e47 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e49 : slopeOrbit 199 99 49 = 185 :=
    slopeOrbit_step_eval 48 6 e48 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e50 : slopeOrbit 199 99 50 = 171 :=
    slopeOrbit_step_eval 49 0 e49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e51 : slopeOrbit 199 99 51 = 143 :=
    slopeOrbit_step_eval 50 0 e50 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e52 : slopeOrbit 199 99 52 = 87 :=
    slopeOrbit_step_eval 51 0 e51 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e53 : slopeOrbit 199 99 53 = 149 :=
    slopeOrbit_step_eval 52 1 e52 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e54 : slopeOrbit 199 99 54 = 99 :=
    slopeOrbit_step_eval 53 0 e53 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e55 : slopeOrbit 199 99 55 = 197 :=
    slopeOrbit_step_eval 54 1 e54 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 199 99 55 = slopeOrbit 199 99 1
    rw [e55, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e26] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e27] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e28] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e29] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e30] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e31] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e32] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e33] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e35] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e36] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e37] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e38] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e39] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e40] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e41] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e42] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e43] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e45] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e46] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e47] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e48] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e49] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e50] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e51] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e52] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e53] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e54] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))

/-- `(199,99)`: the certified class-1 count cap `|fibre_1| <= 4 * ceil(W/54)`. -/
theorem sreClass1Count_of_datum_199_99 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 199) (hK : (class1SlopeDatum ctx).K₀ = 99) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 4 * (((supportShell ctx.shell.d ctx.shell.X).card + 54 - 1) / 54) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 54)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return sreCert_199_99.1
  have hcount : (class1Band4CycleBand ctx 54).card ≤ 4 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset sreCert_199_99.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 54).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 54 - 1) / 54) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 4 * (((supportShell ctx.shell.d ctx.shell.X).card + 54 - 1) / 54) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-! ## Part 2.  The 110 per-pair regime closures

`sreClass1Absorption_of_datum_<q>_<K0>`: at the datum, `L ≤ T(q,K0)` closes the
corrected class-1 absorption in the capstone field shape (for EVERY `r` - the field's
`1 ≤ r` guard is not needed).  HONEST: `L > T` stays open at every pair. -/

/-- `(25,2)` (`c = 10`, `b4 = 1`): threshold `T = 6168094` - LIVE: closes the regime `[986888, 6168094]`; `L > 6168094` stays open. -/
theorem sreClass1Absorption_of_datum_25_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 25) (hK : (class1SlopeDatum ctx).K₀ = 2)
    (hL : shellLadderDepth ctx ≤ 6168094) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 10 - 1) / 10) := by
    rw [one_mul]
    exact class1Fibre_card_le_of_datum_25_2 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 10 - 1) / 10)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 10) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(25,12)` (`c = 10`, `b4 = 1`): threshold `T = 6168094` - LIVE: closes the regime `[986888, 6168094]`; `L > 6168094` stays open. -/
theorem sreClass1Absorption_of_datum_25_12 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 25) (hK : (class1SlopeDatum ctx).K₀ = 12)
    (hL : shellLadderDepth ctx ≤ 6168094) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 10 - 1) / 10) := by
    rw [one_mul]
    exact class1Fibre_card_le_of_datum_25_12 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 10 - 1) / 10)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 10) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(29,14)` (`c = 14`, `b4 = 1`): threshold `T = 8635331` - LIVE: closes the regime `[986888, 8635331]`; `L > 8635331` stays open. -/
theorem sreClass1Absorption_of_datum_29_14 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 29) (hK : (class1SlopeDatum ctx).K₀ = 14)
    (hL : shellLadderDepth ctx ≤ 8635331) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 14 - 1) / 14) := by
    rw [one_mul]
    exact class1Fibre_card_le_of_datum_29_14 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 14 - 1) / 14)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 14) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(35,3)` (`c = 7`, `b4 = 1`): threshold `T = 4317665` - LIVE: closes the regime `[986888, 4317665]`; `L > 4317665` stays open. -/
theorem sreClass1Absorption_of_datum_35_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 35) (hK : (class1SlopeDatum ctx).K₀ = 3)
    (hL : shellLadderDepth ctx ≤ 4317665) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 7 - 1) / 7) := by
    rw [one_mul]
    exact class1Fibre_card_le_of_datum_35_3 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 7 - 1) / 7)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 7) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(35,17)` (`c = 7`, `b4 = 1`): threshold `T = 4317665` - LIVE: closes the regime `[986888, 4317665]`; `L > 4317665` stays open. -/
theorem sreClass1Absorption_of_datum_35_17 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 35) (hK : (class1SlopeDatum ctx).K₀ = 17)
    (hL : shellLadderDepth ctx ≤ 4317665) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 7 - 1) / 7) := by
    rw [one_mul]
    exact class1Fibre_card_le_of_datum_35_17 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 7 - 1) / 7)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 7) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(37,18)` (`c = 18`, `b4 = 1`): threshold `T = 11102569` - LIVE: closes the regime `[986888, 11102569]`; `L > 11102569` stays open. -/
theorem sreClass1Absorption_of_datum_37_18 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 37) (hK : (class1SlopeDatum ctx).K₀ = 18)
    (hL : shellLadderDepth ctx ≤ 11102569) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 18 - 1) / 18) := by
    rw [one_mul]
    exact class1Fibre_card_le_of_datum_37_18 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 18 - 1) / 18)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 18) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(39,6)` (`c = 6`, `b4 = 1`): threshold `T = 3700856` - LIVE: closes the regime `[986888, 3700856]`; `L > 3700856` stays open. -/
theorem sreClass1Absorption_of_datum_39_6 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 39) (hK : (class1SlopeDatum ctx).K₀ = 6)
    (hL : shellLadderDepth ctx ≤ 3700856) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 6 - 1) / 6) := by
    rw [one_mul]
    exact class1Fibre_card_le_of_datum_39_6 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 6 - 1) / 6)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 6) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(41,20)` (`c = 10`, `b4 = 1`): threshold `T = 6168094` - LIVE: closes the regime `[986888, 6168094]`; `L > 6168094` stays open. -/
theorem sreClass1Absorption_of_datum_41_20 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 41) (hK : (class1SlopeDatum ctx).K₀ = 20)
    (hL : shellLadderDepth ctx ≤ 6168094) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 10 - 1) / 10) := by
    rw [one_mul]
    exact class1Fibre_card_le_of_datum_41_20 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 10 - 1) / 10)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 10) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(47,23)` (`c = 14`, `b4 = 1`): threshold `T = 8635331` - LIVE: closes the regime `[986888, 8635331]`; `L > 8635331` stays open. -/
theorem sreClass1Absorption_of_datum_47_23 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 47) (hK : (class1SlopeDatum ctx).K₀ = 23)
    (hL : shellLadderDepth ctx ≤ 8635331) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 14 - 1) / 14) := by
    rw [one_mul]
    exact class1Fibre_card_le_of_datum_47_23 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 14 - 1) / 14)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 14) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(49,3)` (`c = 11`, `b4 = 1`): threshold `T = 6784903` - LIVE: closes the regime `[986888, 6784903]`; `L > 6784903` stays open. -/
theorem sreClass1Absorption_of_datum_49_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 49) (hK : (class1SlopeDatum ctx).K₀ = 3)
    (hL : shellLadderDepth ctx ≤ 6784903) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 11 - 1) / 11) := by
    rw [one_mul]
    exact class1Fibre_card_le_of_datum_49_3 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 11 - 1) / 11)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 11) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(49,24)` (`c = 11`, `b4 = 1`): threshold `T = 6784903` - LIVE: closes the regime `[986888, 6784903]`; `L > 6784903` stays open. -/
theorem sreClass1Absorption_of_datum_49_24 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 49) (hK : (class1SlopeDatum ctx).K₀ = 24)
    (hL : shellLadderDepth ctx ≤ 6784903) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 11 - 1) / 11) := by
    rw [one_mul]
    exact class1Fibre_card_le_of_datum_49_24 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 11 - 1) / 11)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 11) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(55,5)` (`c = 5`, `b4 = 1`): threshold `T = 3084047` - LIVE: closes the regime `[986888, 3084047]`; `L > 3084047` stays open. -/
theorem sreClass1Absorption_of_datum_55_5 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 55) (hK : (class1SlopeDatum ctx).K₀ = 5)
    (hL : shellLadderDepth ctx ≤ 3084047) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 5 - 1) / 5) := by
    rw [one_mul]
    exact class1Fibre_card_le_of_datum_55_5 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 5 - 1) / 5)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 5) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(57,1)` (`c = 9`, `b4 = 1`): threshold `T = 5551284` - LIVE: closes the regime `[986888, 5551284]`; `L > 5551284` stays open. -/
theorem sreClass1Absorption_of_datum_57_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 57) (hK : (class1SlopeDatum ctx).K₀ = 1)
    (hL : shellLadderDepth ctx ≤ 5551284) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 9 - 1) / 9) := by
    rw [one_mul]
    exact class1Fibre_card_le_of_datum_57_1 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 9 - 1) / 9)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 9) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(57,28)` (`c = 9`, `b4 = 1`): threshold `T = 5551284` - LIVE: closes the regime `[986888, 5551284]`; `L > 5551284` stays open. -/
theorem sreClass1Absorption_of_datum_57_28 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 57) (hK : (class1SlopeDatum ctx).K₀ = 28)
    (hL : shellLadderDepth ctx ≤ 5551284) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 9 - 1) / 9) := by
    rw [one_mul]
    exact class1Fibre_card_le_of_datum_57_28 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 9 - 1) / 9)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 9) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(63,10)` (`c = 2`, `b4 = 1`): threshold `T = 1233618` - LIVE: closes the regime `[986888, 1233618]`; `L > 1233618` stays open. -/
theorem sreClass1Absorption_of_datum_63_10 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) (hK : (class1SlopeDatum ctx).K₀ = 10)
    (hL : shellLadderDepth ctx ≤ 1233618) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 2 - 1) / 2) := by
    rw [one_mul]
    exact class1Fibre_card_le_of_datum_63_10 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 2 - 1) / 2)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 2) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(69,11)` (`c = 11`, `b4 = 2`): threshold `T = 3392451` - LIVE: closes the regime `[986888, 3392451]`; `L > 3392451` stays open. -/
theorem sreClass1Absorption_of_datum_69_11 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 69) (hK : (class1SlopeDatum ctx).K₀ = 11)
    (hL : shellLadderDepth ctx ≤ 3392451) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 11 - 1) / 11) :=
    class1Fibre_card_le_of_datum_69_11 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (2 * (((supportShell ctx.shell.d ctx.shell.X).card + 11 - 1) / 11)) hcard ?_
  refine sreNatGate_of_regime (b4 := 2) (c := 11) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(69,34)` (`c = 11`, `b4 = 2`): threshold `T = 3392451` - LIVE: closes the regime `[986888, 3392451]`; `L > 3392451` stays open. -/
theorem sreClass1Absorption_of_datum_69_34 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 69) (hK : (class1SlopeDatum ctx).K₀ = 34)
    (hL : shellLadderDepth ctx ≤ 3392451) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 11 - 1) / 11) :=
    class1Fibre_card_le_of_datum_69_34 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (2 * (((supportShell ctx.shell.d ctx.shell.X).card + 11 - 1) / 11)) hcard ?_
  refine sreNatGate_of_regime (b4 := 2) (c := 11) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(75,7)` (`c = 11`, `b4 = 1`): threshold `T = 6784903` - LIVE: closes the regime `[986888, 6784903]`; `L > 6784903` stays open. -/
theorem sreClass1Absorption_of_datum_75_7 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 75) (hK : (class1SlopeDatum ctx).K₀ = 7)
    (hL : shellLadderDepth ctx ≤ 6784903) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 11 - 1) / 11) := by
    rw [one_mul]
    exact class1Fibre_card_le_of_datum_75_7 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 11 - 1) / 11)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 11) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(75,12)` (`c = 10`, `b4 = 1`): threshold `T = 6168094` - LIVE: closes the regime `[986888, 6168094]`; `L > 6168094` stays open. -/
theorem sreClass1Absorption_of_datum_75_12 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 75) (hK : (class1SlopeDatum ctx).K₀ = 12)
    (hL : shellLadderDepth ctx ≤ 6168094) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 10 - 1) / 10) := by
    rw [one_mul]
    exact class1Fibre_card_le_of_datum_75_12 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 10 - 1) / 10)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 10) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(75,37)` (`c = 11`, `b4 = 1`): threshold `T = 6784903` - LIVE: closes the regime `[986888, 6784903]`; `L > 6784903` stays open. -/
theorem sreClass1Absorption_of_datum_75_37 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 75) (hK : (class1SlopeDatum ctx).K₀ = 37)
    (hL : shellLadderDepth ctx ≤ 6784903) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 11 - 1) / 11) := by
    rw [one_mul]
    exact class1Fibre_card_le_of_datum_75_37 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 11 - 1) / 11)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 11) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(87,1)` (`c = 11`, `b4 = 1`): threshold `T = 6784903` - LIVE: closes the regime `[986888, 6784903]`; `L > 6784903` stays open. -/
theorem sreClass1Absorption_of_datum_87_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 87) (hK : (class1SlopeDatum ctx).K₀ = 1)
    (hL : shellLadderDepth ctx ≤ 6784903) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 11 - 1) / 11) := by
    rw [one_mul]
    exact class1Fibre_card_le_of_datum_87_1 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 11 - 1) / 11)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 11) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(87,14)` (`c = 11`, `b4 = 1`): threshold `T = 6784903` - LIVE: closes the regime `[986888, 6784903]`; `L > 6784903` stays open. -/
theorem sreClass1Absorption_of_datum_87_14 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 87) (hK : (class1SlopeDatum ctx).K₀ = 14)
    (hL : shellLadderDepth ctx ≤ 6784903) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 11 - 1) / 11) := by
    rw [one_mul]
    exact class1Fibre_card_le_of_datum_87_14 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 11 - 1) / 11)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 11) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(99,5)` (`c = 15`, `b4 = 1`): threshold `T = 9252141` - LIVE: closes the regime `[986888, 9252141]`; `L > 9252141` stays open. -/
theorem sreClass1Absorption_of_datum_99_5 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 99) (hK : (class1SlopeDatum ctx).K₀ = 5)
    (hL : shellLadderDepth ctx ≤ 9252141) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 15 - 1) / 15) := by
    rw [one_mul]
    exact class1Fibre_card_le_of_datum_99_5 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 15 - 1) / 15)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 15) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(101,50)` (`c = 50`, `b4 = 3`): threshold `T = 10280156` - LIVE: closes the regime `[986888, 10280156]`; `L > 10280156` stays open. -/
theorem sreClass1Absorption_of_datum_101_50 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 101) (hK : (class1SlopeDatum ctx).K₀ = 50)
    (hL : shellLadderDepth ctx ≤ 10280156) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_101_50 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (3 * (((supportShell ctx.shell.d ctx.shell.X).card + 50 - 1) / 50)) hcard ?_
  refine sreNatGate_of_regime (b4 := 3) (c := 50) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(103,51)` (`c = 28`, `b4 = 1`): threshold `T = 17270663` - LIVE: closes the regime `[986888, 17270663]`; `L > 17270663` stays open. -/
theorem sreClass1Absorption_of_datum_103_51 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 103) (hK : (class1SlopeDatum ctx).K₀ = 51)
    (hL : shellLadderDepth ctx ≤ 17270663) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_103_51 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 28 - 1) / 28)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 28) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(105,7)` (`c = 1`, `b4 = 1`): threshold `T = 616809` - SUB-PIN: `T < 986888` - vacuous on actual contexts (`sreClass1Gate_vacuous_below_pin`). -/
theorem sreClass1Absorption_of_datum_105_7 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 105) (hK : (class1SlopeDatum ctx).K₀ = 7)
    (hL : shellLadderDepth ctx ≤ 616809) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_105_7 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 1 - 1) / 1)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 1) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(105,52)` (`c = 8`, `b4 = 1`): threshold `T = 4934475` - LIVE: closes the regime `[986888, 4934475]`; `L > 4934475` stays open. -/
theorem sreClass1Absorption_of_datum_105_52 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 105) (hK : (class1SlopeDatum ctx).K₀ = 52)
    (hL : shellLadderDepth ctx ≤ 4934475) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_105_52 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 8 - 1) / 8)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 8) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(107,53)` (`c = 53`, `b4 = 4`): threshold `T = 8172724` - LIVE: closes the regime `[986888, 8172724]`; `L > 8172724` stays open. -/
theorem sreClass1Absorption_of_datum_107_53 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 107) (hK : (class1SlopeDatum ctx).K₀ = 53)
    (hL : shellLadderDepth ctx ≤ 8172724) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_107_53 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (4 * (((supportShell ctx.shell.d ctx.shell.X).card + 53 - 1) / 53)) hcard ?_
  refine sreNatGate_of_regime (b4 := 4) (c := 53) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(111,1)` (`c = 14`, `b4 = 1`): threshold `T = 8635331` - LIVE: closes the regime `[986888, 8635331]`; `L > 8635331` stays open. -/
theorem sreClass1Absorption_of_datum_111_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 111) (hK : (class1SlopeDatum ctx).K₀ = 1)
    (hL : shellLadderDepth ctx ≤ 8635331) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_111_1 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 14 - 1) / 14)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 14) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(111,18)` (`c = 18`, `b4 = 1`): threshold `T = 11102569` - LIVE: closes the regime `[986888, 11102569]`; `L > 11102569` stays open. -/
theorem sreClass1Absorption_of_datum_111_18 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 111) (hK : (class1SlopeDatum ctx).K₀ = 18)
    (hL : shellLadderDepth ctx ≤ 11102569) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_111_18 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 18 - 1) / 18)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 18) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(111,55)` (`c = 22`, `b4 = 2`): threshold `T = 6784903` - LIVE: closes the regime `[986888, 6784903]`; `L > 6784903` stays open. -/
theorem sreClass1Absorption_of_datum_111_55 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 111) (hK : (class1SlopeDatum ctx).K₀ = 55)
    (hL : shellLadderDepth ctx ≤ 6784903) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_111_55 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (2 * (((supportShell ctx.shell.d ctx.shell.X).card + 22 - 1) / 22)) hcard ?_
  refine sreNatGate_of_regime (b4 := 2) (c := 22) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(115,2)` (`c = 19`, `b4 = 2`): threshold `T = 5859689` - LIVE: closes the regime `[986888, 5859689]`; `L > 5859689` stays open. -/
theorem sreClass1Absorption_of_datum_115_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 115) (hK : (class1SlopeDatum ctx).K₀ = 2)
    (hL : shellLadderDepth ctx ≤ 5859689) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_115_2 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (2 * (((supportShell ctx.shell.d ctx.shell.X).card + 19 - 1) / 19)) hcard ?_
  refine sreNatGate_of_regime (b4 := 2) (c := 19) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(115,11)` (`c = 25`, `b4 = 1`): threshold `T = 15420235` - LIVE: closes the regime `[986888, 15420235]`; `L > 15420235` stays open. -/
theorem sreClass1Absorption_of_datum_115_11 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 115) (hK : (class1SlopeDatum ctx).K₀ = 11)
    (hL : shellLadderDepth ctx ≤ 15420235) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_115_11 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 25 - 1) / 25)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 25) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(115,57)` (`c = 25`, `b4 = 1`): threshold `T = 15420235` - LIVE: closes the regime `[986888, 15420235]`; `L > 15420235` stays open. -/
theorem sreClass1Absorption_of_datum_115_57 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 115) (hK : (class1SlopeDatum ctx).K₀ = 57)
    (hL : shellLadderDepth ctx ≤ 15420235) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_115_57 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 25 - 1) / 25)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 25) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(117,1)` (`c = 3`, `b4 = 1`): threshold `T = 1850428` - LIVE: closes the regime `[986888, 1850428]`; `L > 1850428` stays open. -/
theorem sreClass1Absorption_of_datum_117_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 117) (hK : (class1SlopeDatum ctx).K₀ = 1)
    (hL : shellLadderDepth ctx ≤ 1850428) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_117_1 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 3 - 1) / 3)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 3) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(117,4)` (`c = 3`, `b4 = 1`): threshold `T = 1850428` - LIVE: closes the regime `[986888, 1850428]`; `L > 1850428` stays open. -/
theorem sreClass1Absorption_of_datum_117_4 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 117) (hK : (class1SlopeDatum ctx).K₀ = 4)
    (hL : shellLadderDepth ctx ≤ 1850428) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_117_4 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 3 - 1) / 3)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 3) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(119,8)` (`c = 9`, `b4 = 1`): threshold `T = 5551284` - LIVE: closes the regime `[986888, 5551284]`; `L > 5551284` stays open. -/
theorem sreClass1Absorption_of_datum_119_8 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 119) (hK : (class1SlopeDatum ctx).K₀ = 8)
    (hL : shellLadderDepth ctx ≤ 5551284) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_119_8 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 9 - 1) / 9)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 9) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(119,59)` (`c = 15`, `b4 = 1`): threshold `T = 9252141` - LIVE: closes the regime `[986888, 9252141]`; `L > 9252141` stays open. -/
theorem sreClass1Absorption_of_datum_119_59 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 119) (hK : (class1SlopeDatum ctx).K₀ = 59)
    (hL : shellLadderDepth ctx ≤ 9252141) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_119_59 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 15 - 1) / 15)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 15) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(121,5)` (`c = 55`, `b4 = 3`): threshold `T = 11308172` - LIVE: closes the regime `[986888, 11308172]`; `L > 11308172` stays open. -/
theorem sreClass1Absorption_of_datum_121_5 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 121) (hK : (class1SlopeDatum ctx).K₀ = 5)
    (hL : shellLadderDepth ctx ≤ 11308172) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_121_5 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (3 * (((supportShell ctx.shell.d ctx.shell.X).card + 55 - 1) / 55)) hcard ?_
  refine sreNatGate_of_regime (b4 := 3) (c := 55) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(121,60)` (`c = 55`, `b4 = 3`): threshold `T = 11308172` - LIVE: closes the regime `[986888, 11308172]`; `L > 11308172` stays open. -/
theorem sreClass1Absorption_of_datum_121_60 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 121) (hK : (class1SlopeDatum ctx).K₀ = 60)
    (hL : shellLadderDepth ctx ≤ 11308172) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_121_60 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (3 * (((supportShell ctx.shell.d ctx.shell.X).card + 55 - 1) / 55)) hcard ?_
  refine sreNatGate_of_regime (b4 := 3) (c := 55) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(125,2)` (`c = 50`, `b4 = 3`): threshold `T = 10280156` - LIVE: closes the regime `[986888, 10280156]`; `L > 10280156` stays open. -/
theorem sreClass1Absorption_of_datum_125_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 125) (hK : (class1SlopeDatum ctx).K₀ = 2)
    (hL : shellLadderDepth ctx ≤ 10280156) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_125_2 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (3 * (((supportShell ctx.shell.d ctx.shell.X).card + 50 - 1) / 50)) hcard ?_
  refine sreNatGate_of_regime (b4 := 3) (c := 50) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(125,12)` (`c = 50`, `b4 = 3`): threshold `T = 10280156` - LIVE: closes the regime `[986888, 10280156]`; `L > 10280156` stays open. -/
theorem sreClass1Absorption_of_datum_125_12 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 125) (hK : (class1SlopeDatum ctx).K₀ = 12)
    (hL : shellLadderDepth ctx ≤ 10280156) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_125_12 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (3 * (((supportShell ctx.shell.d ctx.shell.X).card + 50 - 1) / 50)) hcard ?_
  refine sreNatGate_of_regime (b4 := 3) (c := 50) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(125,62)` (`c = 50`, `b4 = 3`): threshold `T = 10280156` - LIVE: closes the regime `[986888, 10280156]`; `L > 10280156` stays open. -/
theorem sreClass1Absorption_of_datum_125_62 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 125) (hK : (class1SlopeDatum ctx).K₀ = 62)
    (hL : shellLadderDepth ctx ≤ 10280156) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_125_62 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (3 * (((supportShell ctx.shell.d ctx.shell.X).card + 50 - 1) / 50)) hcard ?_
  refine sreNatGate_of_regime (b4 := 3) (c := 50) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(131,65)` (`c = 65`, `b4 = 4`): threshold `T = 10023152` - LIVE: closes the regime `[986888, 10023152]`; `L > 10023152` stays open. -/
theorem sreClass1Absorption_of_datum_131_65 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 131) (hK : (class1SlopeDatum ctx).K₀ = 65)
    (hL : shellLadderDepth ctx ≤ 10023152) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_131_65 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (4 * (((supportShell ctx.shell.d ctx.shell.X).card + 65 - 1) / 65)) hcard ?_
  refine sreNatGate_of_regime (b4 := 4) (c := 65) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(133,3)` (`c = 7`, `b4 = 1`): threshold `T = 4317665` - LIVE: closes the regime `[986888, 4317665]`; `L > 4317665` stays open. -/
theorem sreClass1Absorption_of_datum_133_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 133) (hK : (class1SlopeDatum ctx).K₀ = 3)
    (hL : shellLadderDepth ctx ≤ 4317665) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_133_3 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 7 - 1) / 7)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 7) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(133,9)` (`c = 7`, `b4 = 2`): threshold `T = 2158832` - LIVE: closes the regime `[986888, 2158832]`; `L > 2158832` stays open. -/
theorem sreClass1Absorption_of_datum_133_9 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 133) (hK : (class1SlopeDatum ctx).K₀ = 9)
    (hL : shellLadderDepth ctx ≤ 2158832) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_133_9 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (2 * (((supportShell ctx.shell.d ctx.shell.X).card + 7 - 1) / 7)) hcard ?_
  refine sreNatGate_of_regime (b4 := 2) (c := 7) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(135,7)` (`c = 19`, `b4 = 2`): threshold `T = 5859689` - LIVE: closes the regime `[986888, 5859689]`; `L > 5859689` stays open. -/
theorem sreClass1Absorption_of_datum_135_7 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 135) (hK : (class1SlopeDatum ctx).K₀ = 7)
    (hL : shellLadderDepth ctx ≤ 5859689) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_135_7 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (2 * (((supportShell ctx.shell.d ctx.shell.X).card + 19 - 1) / 19)) hcard ?_
  refine sreNatGate_of_regime (b4 := 2) (c := 19) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(135,13)` (`c = 19`, `b4 = 2`): threshold `T = 5859689` - LIVE: closes the regime `[986888, 5859689]`; `L > 5859689` stays open. -/
theorem sreClass1Absorption_of_datum_135_13 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 135) (hK : (class1SlopeDatum ctx).K₀ = 13)
    (hL : shellLadderDepth ctx ≤ 5859689) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_135_13 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (2 * (((supportShell ctx.shell.d ctx.shell.X).card + 19 - 1) / 19)) hcard ?_
  refine sreNatGate_of_regime (b4 := 2) (c := 19) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(135,22)` (`c = 19`, `b4 = 2`): threshold `T = 5859689` - LIVE: closes the regime `[986888, 5859689]`; `L > 5859689` stays open. -/
theorem sreClass1Absorption_of_datum_135_22 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 135) (hK : (class1SlopeDatum ctx).K₀ = 22)
    (hL : shellLadderDepth ctx ≤ 5859689) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_135_22 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (2 * (((supportShell ctx.shell.d ctx.shell.X).card + 19 - 1) / 19)) hcard ?_
  refine sreNatGate_of_regime (b4 := 2) (c := 19) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(135,67)` (`c = 19`, `b4 = 2`): threshold `T = 5859689` - LIVE: closes the regime `[986888, 5859689]`; `L > 5859689` stays open. -/
theorem sreClass1Absorption_of_datum_135_67 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 135) (hK : (class1SlopeDatum ctx).K₀ = 67)
    (hL : shellLadderDepth ctx ≤ 5859689) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_135_67 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (2 * (((supportShell ctx.shell.d ctx.shell.X).card + 19 - 1) / 19)) hcard ?_
  refine sreNatGate_of_regime (b4 := 2) (c := 19) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(137,68)` (`c = 34`, `b4 = 4`): threshold `T = 5242880` - LIVE: closes the regime `[986888, 5242880]`; `L > 5242880` stays open. -/
theorem sreClass1Absorption_of_datum_137_68 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 137) (hK : (class1SlopeDatum ctx).K₀ = 68)
    (hL : shellLadderDepth ctx ≤ 5242880) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_137_68 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (4 * (((supportShell ctx.shell.d ctx.shell.X).card + 34 - 1) / 34)) hcard ?_
  refine sreNatGate_of_regime (b4 := 4) (c := 34) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(139,69)` (`c = 69`, `b4 = 5`): threshold `T = 8511969` - LIVE: closes the regime `[986888, 8511969]`; `L > 8511969` stays open. -/
theorem sreClass1Absorption_of_datum_139_69 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 139) (hK : (class1SlopeDatum ctx).K₀ = 69)
    (hL : shellLadderDepth ctx ≤ 8511969) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_139_69 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (5 * (((supportShell ctx.shell.d ctx.shell.X).card + 69 - 1) / 69)) hcard ?_
  refine sreNatGate_of_regime (b4 := 5) (c := 69) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(141,1)` (`c = 23`, `b4 = 1`): threshold `T = 14186616` - LIVE: closes the regime `[986888, 14186616]`; `L > 14186616` stays open. -/
theorem sreClass1Absorption_of_datum_141_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 141) (hK : (class1SlopeDatum ctx).K₀ = 1)
    (hL : shellLadderDepth ctx ≤ 14186616) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_141_1 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 23 - 1) / 23)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 23) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(141,23)` (`c = 23`, `b4 = 2`): threshold `T = 7093308` - LIVE: closes the regime `[986888, 7093308]`; `L > 7093308` stays open. -/
theorem sreClass1Absorption_of_datum_141_23 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 141) (hK : (class1SlopeDatum ctx).K₀ = 23)
    (hL : shellLadderDepth ctx ≤ 7093308) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_141_23 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (2 * (((supportShell ctx.shell.d ctx.shell.X).card + 23 - 1) / 23)) hcard ?_
  refine sreNatGate_of_regime (b4 := 2) (c := 23) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(141,70)` (`c = 23`, `b4 = 2`): threshold `T = 7093308` - LIVE: closes the regime `[986888, 7093308]`; `L > 7093308` stays open. -/
theorem sreClass1Absorption_of_datum_141_70 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 141) (hK : (class1SlopeDatum ctx).K₀ = 70)
    (hL : shellLadderDepth ctx ≤ 7093308) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_141_70 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (2 * (((supportShell ctx.shell.d ctx.shell.X).card + 23 - 1) / 23)) hcard ?_
  refine sreNatGate_of_regime (b4 := 2) (c := 23) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(143,5)` (`c = 35`, `b4 = 2`): threshold `T = 10794164` - LIVE: closes the regime `[986888, 10794164]`; `L > 10794164` stays open. -/
theorem sreClass1Absorption_of_datum_143_5 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 143) (hK : (class1SlopeDatum ctx).K₀ = 5)
    (hL : shellLadderDepth ctx ≤ 10794164) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_143_5 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (2 * (((supportShell ctx.shell.d ctx.shell.X).card + 35 - 1) / 35)) hcard ?_
  refine sreNatGate_of_regime (b4 := 2) (c := 35) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(143,6)` (`c = 25`, `b4 = 1`): threshold `T = 15420235` - LIVE: closes the regime `[986888, 15420235]`; `L > 15420235` stays open. -/
theorem sreClass1Absorption_of_datum_143_6 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 143) (hK : (class1SlopeDatum ctx).K₀ = 6)
    (hL : shellLadderDepth ctx ≤ 15420235) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_143_6 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 25 - 1) / 25)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 25) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(143,71)` (`c = 35`, `b4 = 2`): threshold `T = 10794164` - LIVE: closes the regime `[986888, 10794164]`; `L > 10794164` stays open. -/
theorem sreClass1Absorption_of_datum_143_71 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 143) (hK : (class1SlopeDatum ctx).K₀ = 71)
    (hL : shellLadderDepth ctx ≤ 10794164) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_143_71 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (2 * (((supportShell ctx.shell.d ctx.shell.X).card + 35 - 1) / 35)) hcard ?_
  refine sreNatGate_of_regime (b4 := 2) (c := 35) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(145,2)` (`c = 14`, `b4 = 1`): threshold `T = 8635331` - LIVE: closes the regime `[986888, 8635331]`; `L > 8635331` stays open. -/
theorem sreClass1Absorption_of_datum_145_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 145) (hK : (class1SlopeDatum ctx).K₀ = 2)
    (hL : shellLadderDepth ctx ≤ 8635331) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_145_2 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 14 - 1) / 14)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 14) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(145,14)` (`c = 14`, `b4 = 1`): threshold `T = 8635331` - LIVE: closes the regime `[986888, 8635331]`; `L > 8635331` stays open. -/
theorem sreClass1Absorption_of_datum_145_14 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 145) (hK : (class1SlopeDatum ctx).K₀ = 14)
    (hL : shellLadderDepth ctx ≤ 8635331) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_145_14 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 14 - 1) / 14)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 14) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(145,72)` (`c = 14`, `b4 = 1`): threshold `T = 8635331` - LIVE: closes the regime `[986888, 8635331]`; `L > 8635331` stays open. -/
theorem sreClass1Absorption_of_datum_145_72 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 145) (hK : (class1SlopeDatum ctx).K₀ = 72)
    (hL : shellLadderDepth ctx ≤ 8635331) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_145_72 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 14 - 1) / 14)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 14) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(147,1)` (`c = 20`, `b4 = 1`): threshold `T = 12336188` - LIVE: closes the regime `[986888, 12336188]`; `L > 12336188` stays open. -/
theorem sreClass1Absorption_of_datum_147_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 147) (hK : (class1SlopeDatum ctx).K₀ = 1)
    (hL : shellLadderDepth ctx ≤ 12336188) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_147_1 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 20 - 1) / 20)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 20) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(147,10)` (`c = 22`, `b4 = 2`): threshold `T = 6784903` - LIVE: closes the regime `[986888, 6784903]`; `L > 6784903` stays open. -/
theorem sreClass1Absorption_of_datum_147_10 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 147) (hK : (class1SlopeDatum ctx).K₀ = 10)
    (hL : shellLadderDepth ctx ≤ 6784903) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_147_10 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (2 * (((supportShell ctx.shell.d ctx.shell.X).card + 22 - 1) / 22)) hcard ?_
  refine sreNatGate_of_regime (b4 := 2) (c := 22) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(147,73)` (`c = 22`, `b4 = 2`): threshold `T = 6784903` - LIVE: closes the regime `[986888, 6784903]`; `L > 6784903` stays open. -/
theorem sreClass1Absorption_of_datum_147_73 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 147) (hK : (class1SlopeDatum ctx).K₀ = 73)
    (hL : shellLadderDepth ctx ≤ 6784903) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_147_73 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (2 * (((supportShell ctx.shell.d ctx.shell.X).card + 22 - 1) / 22)) hcard ?_
  refine sreNatGate_of_regime (b4 := 2) (c := 22) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(149,74)` (`c = 74`, `b4 = 4`): threshold `T = 11410974` - LIVE: closes the regime `[986888, 11410974]`; `L > 11410974` stays open. -/
theorem sreClass1Absorption_of_datum_149_74 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 149) (hK : (class1SlopeDatum ctx).K₀ = 74)
    (hL : shellLadderDepth ctx ≤ 11410974) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_149_74 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (4 * (((supportShell ctx.shell.d ctx.shell.X).card + 74 - 1) / 74)) hcard ?_
  refine sreNatGate_of_regime (b4 := 4) (c := 74) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(153,1)` (`c = 10`, `b4 = 1`): threshold `T = 6168094` - LIVE: closes the regime `[986888, 6168094]`; `L > 6168094` stays open. -/
theorem sreClass1Absorption_of_datum_153_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 153) (hK : (class1SlopeDatum ctx).K₀ = 1)
    (hL : shellLadderDepth ctx ≤ 6168094) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_153_1 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 10 - 1) / 10)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 10) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(153,4)` (`c = 10`, `b4 = 1`): threshold `T = 6168094` - LIVE: closes the regime `[986888, 6168094]`; `L > 6168094` stays open. -/
theorem sreClass1Absorption_of_datum_153_4 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 153) (hK : (class1SlopeDatum ctx).K₀ = 4)
    (hL : shellLadderDepth ctx ≤ 6168094) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_153_4 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 10 - 1) / 10)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 10) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(153,8)` (`c = 10`, `b4 = 1`): threshold `T = 6168094` - LIVE: closes the regime `[986888, 6168094]`; `L > 6168094` stays open. -/
theorem sreClass1Absorption_of_datum_153_8 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 153) (hK : (class1SlopeDatum ctx).K₀ = 8)
    (hL : shellLadderDepth ctx ≤ 6168094) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_153_8 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 10 - 1) / 10)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 10) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(153,25)` (`c = 14`, `b4 = 1`): threshold `T = 8635331` - LIVE: closes the regime `[986888, 8635331]`; `L > 8635331` stays open. -/
theorem sreClass1Absorption_of_datum_153_25 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 153) (hK : (class1SlopeDatum ctx).K₀ = 25)
    (hL : shellLadderDepth ctx ≤ 8635331) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_153_25 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 14 - 1) / 14)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 14) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(153,76)` (`c = 14`, `b4 = 1`): threshold `T = 8635331` - LIVE: closes the regime `[986888, 8635331]`; `L > 8635331` stays open. -/
theorem sreClass1Absorption_of_datum_153_76 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 153) (hK : (class1SlopeDatum ctx).K₀ = 76)
    (hL : shellLadderDepth ctx ≤ 8635331) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_153_76 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 14 - 1) / 14)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 14) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(155,15)` (`c = 2`, `b4 = 1`): threshold `T = 1233618` - LIVE: closes the regime `[986888, 1233618]`; `L > 1233618` stays open. -/
theorem sreClass1Absorption_of_datum_155_15 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 155) (hK : (class1SlopeDatum ctx).K₀ = 15)
    (hL : shellLadderDepth ctx ≤ 1233618) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_155_15 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 2 - 1) / 2)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 2) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(159,1)` (`c = 21`, `b4 = 1`): threshold `T = 12952997` - LIVE: closes the regime `[986888, 12952997]`; `L > 12952997` stays open. -/
theorem sreClass1Absorption_of_datum_159_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 159) (hK : (class1SlopeDatum ctx).K₀ = 1)
    (hL : shellLadderDepth ctx ≤ 12952997) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_159_1 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 21 - 1) / 21)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 21) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(159,26)` (`c = 21`, `b4 = 1`): threshold `T = 12952997` - LIVE: closes the regime `[986888, 12952997]`; `L > 12952997` stays open. -/
theorem sreClass1Absorption_of_datum_159_26 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 159) (hK : (class1SlopeDatum ctx).K₀ = 26)
    (hL : shellLadderDepth ctx ≤ 12952997) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_159_26 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 21 - 1) / 21)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 21) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(159,79)` (`c = 31`, `b4 = 3`): threshold `T = 6373697` - LIVE: closes the regime `[986888, 6373697]`; `L > 6373697` stays open. -/
theorem sreClass1Absorption_of_datum_159_79 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 159) (hK : (class1SlopeDatum ctx).K₀ = 79)
    (hL : shellLadderDepth ctx ≤ 6373697) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_159_79 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (3 * (((supportShell ctx.shell.d ctx.shell.X).card + 31 - 1) / 31)) hcard ?_
  refine sreNatGate_of_regime (b4 := 3) (c := 31) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(161,3)` (`c = 15`, `b4 = 1`): threshold `T = 9252141` - LIVE: closes the regime `[986888, 9252141]`; `L > 9252141` stays open. -/
theorem sreClass1Absorption_of_datum_161_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 161) (hK : (class1SlopeDatum ctx).K₀ = 3)
    (hL : shellLadderDepth ctx ≤ 9252141) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_161_3 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 15 - 1) / 15)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 15) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(161,11)` (`c = 18`, `b4 = 2`): threshold `T = 5551284` - LIVE: closes the regime `[986888, 5551284]`; `L > 5551284` stays open. -/
theorem sreClass1Absorption_of_datum_161_11 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 161) (hK : (class1SlopeDatum ctx).K₀ = 11)
    (hL : shellLadderDepth ctx ≤ 5551284) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_161_11 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (2 * (((supportShell ctx.shell.d ctx.shell.X).card + 18 - 1) / 18)) hcard ?_
  refine sreNatGate_of_regime (b4 := 2) (c := 18) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(161,80)` (`c = 18`, `b4 = 2`): threshold `T = 5551284` - LIVE: closes the regime `[986888, 5551284]`; `L > 5551284` stays open. -/
theorem sreClass1Absorption_of_datum_161_80 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 161) (hK : (class1SlopeDatum ctx).K₀ = 80)
    (hL : shellLadderDepth ctx ≤ 5551284) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_161_80 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (2 * (((supportShell ctx.shell.d ctx.shell.X).card + 18 - 1) / 18)) hcard ?_
  refine sreNatGate_of_regime (b4 := 2) (c := 18) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(163,81)` (`c = 81`, `b4 = 5`): threshold `T = 9992312` - LIVE: closes the regime `[986888, 9992312]`; `L > 9992312` stays open. -/
theorem sreClass1Absorption_of_datum_163_81 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 163) (hK : (class1SlopeDatum ctx).K₀ = 81)
    (hL : shellLadderDepth ctx ≤ 9992312) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_163_81 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (5 * (((supportShell ctx.shell.d ctx.shell.X).card + 81 - 1) / 81)) hcard ?_
  refine sreNatGate_of_regime (b4 := 5) (c := 81) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(165,1)` (`c = 7`, `b4 = 1`): threshold `T = 4317665` - LIVE: closes the regime `[986888, 4317665]`; `L > 4317665` stays open. -/
theorem sreClass1Absorption_of_datum_165_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 165) (hK : (class1SlopeDatum ctx).K₀ = 1)
    (hL : shellLadderDepth ctx ≤ 4317665) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_165_1 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 7 - 1) / 7)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 7) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(165,2)` (`c = 7`, `b4 = 1`): threshold `T = 4317665` - LIVE: closes the regime `[986888, 4317665]`; `L > 4317665` stays open. -/
theorem sreClass1Absorption_of_datum_165_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 165) (hK : (class1SlopeDatum ctx).K₀ = 2)
    (hL : shellLadderDepth ctx ≤ 4317665) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_165_2 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 7 - 1) / 7)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 7) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(165,7)` (`c = 9`, `b4 = 1`): threshold `T = 5551284` - LIVE: closes the regime `[986888, 5551284]`; `L > 5551284` stays open. -/
theorem sreClass1Absorption_of_datum_165_7 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 165) (hK : (class1SlopeDatum ctx).K₀ = 7)
    (hL : shellLadderDepth ctx ≤ 5551284) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_165_7 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 9 - 1) / 9)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 9) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(165,16)` (`c = 7`, `b4 = 1`): threshold `T = 4317665` - LIVE: closes the regime `[986888, 4317665]`; `L > 4317665` stays open. -/
theorem sreClass1Absorption_of_datum_165_16 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 165) (hK : (class1SlopeDatum ctx).K₀ = 16)
    (hL : shellLadderDepth ctx ≤ 4317665) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_165_16 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 7 - 1) / 7)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 7) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(167,83)` (`c = 47`, `b4 = 3`): threshold `T = 9663347` - LIVE: closes the regime `[986888, 9663347]`; `L > 9663347` stays open. -/
theorem sreClass1Absorption_of_datum_167_83 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 167) (hK : (class1SlopeDatum ctx).K₀ = 83)
    (hL : shellLadderDepth ctx ≤ 9663347) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_167_83 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (3 * (((supportShell ctx.shell.d ctx.shell.X).card + 47 - 1) / 47)) hcard ?_
  refine sreNatGate_of_regime (b4 := 3) (c := 47) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(169,6)` (`c = 78`, `b4 = 5`): threshold `T = 9622226` - LIVE: closes the regime `[986888, 9622226]`; `L > 9622226` stays open. -/
theorem sreClass1Absorption_of_datum_169_6 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 169) (hK : (class1SlopeDatum ctx).K₀ = 6)
    (hL : shellLadderDepth ctx ≤ 9622226) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_169_6 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (5 * (((supportShell ctx.shell.d ctx.shell.X).card + 78 - 1) / 78)) hcard ?_
  refine sreNatGate_of_regime (b4 := 5) (c := 78) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(169,84)` (`c = 78`, `b4 = 5`): threshold `T = 9622226` - LIVE: closes the regime `[986888, 9622226]`; `L > 9622226` stays open. -/
theorem sreClass1Absorption_of_datum_169_84 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 169) (hK : (class1SlopeDatum ctx).K₀ = 84)
    (hL : shellLadderDepth ctx ≤ 9622226) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_169_84 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (5 * (((supportShell ctx.shell.d ctx.shell.X).card + 78 - 1) / 78)) hcard ?_
  refine sreNatGate_of_regime (b4 := 5) (c := 78) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(173,86)` (`c = 86`, `b4 = 6`): threshold `T = 8840934` - LIVE: closes the regime `[986888, 8840934]`; `L > 8840934` stays open. -/
theorem sreClass1Absorption_of_datum_173_86 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 173) (hK : (class1SlopeDatum ctx).K₀ = 86)
    (hL : shellLadderDepth ctx ≤ 8840934) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_173_86 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (6 * (((supportShell ctx.shell.d ctx.shell.X).card + 86 - 1) / 86)) hcard ?_
  refine sreNatGate_of_regime (b4 := 6) (c := 86) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(175,2)` (`c = 29`, `b4 = 1`): threshold `T = 17887472` - LIVE: closes the regime `[986888, 17887472]`; `L > 17887472` stays open. -/
theorem sreClass1Absorption_of_datum_175_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 175) (hK : (class1SlopeDatum ctx).K₀ = 2)
    (hL : shellLadderDepth ctx ≤ 17887472) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_175_2 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 29 - 1) / 29)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 29) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(175,3)` (`c = 31`, `b4 = 3`): threshold `T = 6373697` - LIVE: closes the regime `[986888, 6373697]`; `L > 6373697` stays open. -/
theorem sreClass1Absorption_of_datum_175_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 175) (hK : (class1SlopeDatum ctx).K₀ = 3)
    (hL : shellLadderDepth ctx ≤ 6373697) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_175_3 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (3 * (((supportShell ctx.shell.d ctx.shell.X).card + 31 - 1) / 31)) hcard ?_
  refine sreNatGate_of_regime (b4 := 3) (c := 31) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(175,12)` (`c = 31`, `b4 = 3`): threshold `T = 6373697` - LIVE: closes the regime `[986888, 6373697]`; `L > 6373697` stays open. -/
theorem sreClass1Absorption_of_datum_175_12 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 175) (hK : (class1SlopeDatum ctx).K₀ = 12)
    (hL : shellLadderDepth ctx ≤ 6373697) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_175_12 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (3 * (((supportShell ctx.shell.d ctx.shell.X).card + 31 - 1) / 31)) hcard ?_
  refine sreNatGate_of_regime (b4 := 3) (c := 31) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(175,17)` (`c = 31`, `b4 = 3`): threshold `T = 6373697` - LIVE: closes the regime `[986888, 6373697]`; `L > 6373697` stays open. -/
theorem sreClass1Absorption_of_datum_175_17 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 175) (hK : (class1SlopeDatum ctx).K₀ = 17)
    (hL : shellLadderDepth ctx ≤ 6373697) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_175_17 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (3 * (((supportShell ctx.shell.d ctx.shell.X).card + 31 - 1) / 31)) hcard ?_
  refine sreNatGate_of_regime (b4 := 3) (c := 31) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(175,87)` (`c = 31`, `b4 = 3`): threshold `T = 6373697` - LIVE: closes the regime `[986888, 6373697]`; `L > 6373697` stays open. -/
theorem sreClass1Absorption_of_datum_175_87 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 175) (hK : (class1SlopeDatum ctx).K₀ = 87)
    (hL : shellLadderDepth ctx ≤ 6373697) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_175_87 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (3 * (((supportShell ctx.shell.d ctx.shell.X).card + 31 - 1) / 31)) hcard ?_
  refine sreNatGate_of_regime (b4 := 3) (c := 31) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(177,1)` (`c = 29`, `b4 = 1`): threshold `T = 17887472` - LIVE: closes the regime `[986888, 17887472]`; `L > 17887472` stays open. -/
theorem sreClass1Absorption_of_datum_177_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 177) (hK : (class1SlopeDatum ctx).K₀ = 1)
    (hL : shellLadderDepth ctx ≤ 17887472) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_177_1 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 29 - 1) / 29)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 29) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(177,29)` (`c = 29`, `b4 = 2`): threshold `T = 8943736` - LIVE: closes the regime `[986888, 8943736]`; `L > 8943736` stays open. -/
theorem sreClass1Absorption_of_datum_177_29 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 177) (hK : (class1SlopeDatum ctx).K₀ = 29)
    (hL : shellLadderDepth ctx ≤ 8943736) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_177_29 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (2 * (((supportShell ctx.shell.d ctx.shell.X).card + 29 - 1) / 29)) hcard ?_
  refine sreNatGate_of_regime (b4 := 2) (c := 29) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(177,88)` (`c = 29`, `b4 = 1`): threshold `T = 17887472` - LIVE: closes the regime `[986888, 17887472]`; `L > 17887472` stays open. -/
theorem sreClass1Absorption_of_datum_177_88 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 177) (hK : (class1SlopeDatum ctx).K₀ = 88)
    (hL : shellLadderDepth ctx ≤ 17887472) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_177_88 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 29 - 1) / 29)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 29) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(179,89)` (`c = 89`, `b4 = 5`): threshold `T = 10979207` - LIVE: closes the regime `[986888, 10979207]`; `L > 10979207` stays open. -/
theorem sreClass1Absorption_of_datum_179_89 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 179) (hK : (class1SlopeDatum ctx).K₀ = 89)
    (hL : shellLadderDepth ctx ≤ 10979207) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_179_89 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (5 * (((supportShell ctx.shell.d ctx.shell.X).card + 89 - 1) / 89)) hcard ?_
  refine sreNatGate_of_regime (b4 := 5) (c := 89) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(181,90)` (`c = 90`, `b4 = 5`): threshold `T = 11102569` - LIVE: closes the regime `[986888, 11102569]`; `L > 11102569` stays open. -/
theorem sreClass1Absorption_of_datum_181_90 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 181) (hK : (class1SlopeDatum ctx).K₀ = 90)
    (hL : shellLadderDepth ctx ≤ 11102569) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_181_90 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (5 * (((supportShell ctx.shell.d ctx.shell.X).card + 90 - 1) / 90)) hcard ?_
  refine sreNatGate_of_regime (b4 := 5) (c := 90) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(183,1)` (`c = 26`, `b4 = 3`): threshold `T = 5345681` - LIVE: closes the regime `[986888, 5345681]`; `L > 5345681` stays open. -/
theorem sreClass1Absorption_of_datum_183_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 183) (hK : (class1SlopeDatum ctx).K₀ = 1)
    (hL : shellLadderDepth ctx ≤ 5345681) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_183_1 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (3 * (((supportShell ctx.shell.d ctx.shell.X).card + 26 - 1) / 26)) hcard ?_
  refine sreNatGate_of_regime (b4 := 3) (c := 26) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(183,30)` (`c = 30`, `b4 = 2`): threshold `T = 9252141` - LIVE: closes the regime `[986888, 9252141]`; `L > 9252141` stays open. -/
theorem sreClass1Absorption_of_datum_183_30 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 183) (hK : (class1SlopeDatum ctx).K₀ = 30)
    (hL : shellLadderDepth ctx ≤ 9252141) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_183_30 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (2 * (((supportShell ctx.shell.d ctx.shell.X).card + 30 - 1) / 30)) hcard ?_
  refine sreNatGate_of_regime (b4 := 2) (c := 30) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(185,2)` (`c = 18`, `b4 = 2`): threshold `T = 5551284` - LIVE: closes the regime `[986888, 5551284]`; `L > 5551284` stays open. -/
theorem sreClass1Absorption_of_datum_185_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 185) (hK : (class1SlopeDatum ctx).K₀ = 2)
    (hL : shellLadderDepth ctx ≤ 5551284) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_185_2 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (2 * (((supportShell ctx.shell.d ctx.shell.X).card + 18 - 1) / 18)) hcard ?_
  refine sreNatGate_of_regime (b4 := 2) (c := 18) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(185,18)` (`c = 18`, `b4 = 2`): threshold `T = 5551284` - LIVE: closes the regime `[986888, 5551284]`; `L > 5551284` stays open. -/
theorem sreClass1Absorption_of_datum_185_18 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 185) (hK : (class1SlopeDatum ctx).K₀ = 18)
    (hL : shellLadderDepth ctx ≤ 5551284) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_185_18 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (2 * (((supportShell ctx.shell.d ctx.shell.X).card + 18 - 1) / 18)) hcard ?_
  refine sreNatGate_of_regime (b4 := 2) (c := 18) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(185,92)` (`c = 18`, `b4 = 2`): threshold `T = 5551284` - LIVE: closes the regime `[986888, 5551284]`; `L > 5551284` stays open. -/
theorem sreClass1Absorption_of_datum_185_92 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 185) (hK : (class1SlopeDatum ctx).K₀ = 92)
    (hL : shellLadderDepth ctx ≤ 5551284) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_185_92 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (2 * (((supportShell ctx.shell.d ctx.shell.X).card + 18 - 1) / 18)) hcard ?_
  refine sreNatGate_of_regime (b4 := 2) (c := 18) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(187,8)` (`c = 21`, `b4 = 1`): threshold `T = 12952997` - LIVE: closes the regime `[986888, 12952997]`; `L > 12952997` stays open. -/
theorem sreClass1Absorption_of_datum_187_8 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 187) (hK : (class1SlopeDatum ctx).K₀ = 8)
    (hL : shellLadderDepth ctx ≤ 12952997) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_187_8 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 21 - 1) / 21)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 21) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(187,93)` (`c = 19`, `b4 = 3`): threshold `T = 3906459` - LIVE: closes the regime `[986888, 3906459]`; `L > 3906459` stays open. -/
theorem sreClass1Absorption_of_datum_187_93 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 187) (hK : (class1SlopeDatum ctx).K₀ = 93)
    (hL : shellLadderDepth ctx ≤ 3906459) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_187_93 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (3 * (((supportShell ctx.shell.d ctx.shell.X).card + 19 - 1) / 19)) hcard ?_
  refine sreNatGate_of_regime (b4 := 3) (c := 19) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(189,10)` (`c = 8`, `b4 = 1`): threshold `T = 4934475` - LIVE: closes the regime `[986888, 4934475]`; `L > 4934475` stays open. -/
theorem sreClass1Absorption_of_datum_189_10 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 189) (hK : (class1SlopeDatum ctx).K₀ = 10)
    (hL : shellLadderDepth ctx ≤ 4934475) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_189_10 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (1 * (((supportShell ctx.shell.d ctx.shell.X).card + 8 - 1) / 8)) hcard ?_
  refine sreNatGate_of_regime (b4 := 1) (c := 8) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(189,13)` (`c = 9`, `b4 = 2`): threshold `T = 2775642` - LIVE: closes the regime `[986888, 2775642]`; `L > 2775642` stays open. -/
theorem sreClass1Absorption_of_datum_189_13 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 189) (hK : (class1SlopeDatum ctx).K₀ = 13)
    (hL : shellLadderDepth ctx ≤ 2775642) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_189_13 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (2 * (((supportShell ctx.shell.d ctx.shell.X).card + 9 - 1) / 9)) hcard ?_
  refine sreNatGate_of_regime (b4 := 2) (c := 9) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(191,95)` (`c = 54`, `b4 = 2`): threshold `T = 16653854` - LIVE: closes the regime `[986888, 16653854]`; `L > 16653854` stays open. -/
theorem sreClass1Absorption_of_datum_191_95 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 191) (hK : (class1SlopeDatum ctx).K₀ = 95)
    (hL : shellLadderDepth ctx ≤ 16653854) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_191_95 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (2 * (((supportShell ctx.shell.d ctx.shell.X).card + 54 - 1) / 54)) hcard ?_
  refine sreNatGate_of_regime (b4 := 2) (c := 54) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(193,96)` (`c = 48`, `b4 = 2`): threshold `T = 14803425` - LIVE: closes the regime `[986888, 14803425]`; `L > 14803425` stays open. -/
theorem sreClass1Absorption_of_datum_193_96 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 193) (hK : (class1SlopeDatum ctx).K₀ = 96)
    (hL : shellLadderDepth ctx ≤ 14803425) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_193_96 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (2 * (((supportShell ctx.shell.d ctx.shell.X).card + 48 - 1) / 48)) hcard ?_
  refine sreNatGate_of_regime (b4 := 2) (c := 48) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(195,19)` (`c = 6`, `b4 = 2`): threshold `T = 1850428` - LIVE: closes the regime `[986888, 1850428]`; `L > 1850428` stays open. -/
theorem sreClass1Absorption_of_datum_195_19 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 195) (hK : (class1SlopeDatum ctx).K₀ = 19)
    (hL : shellLadderDepth ctx ≤ 1850428) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_195_19 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (2 * (((supportShell ctx.shell.d ctx.shell.X).card + 6 - 1) / 6)) hcard ?_
  refine sreNatGate_of_regime (b4 := 2) (c := 6) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(197,98)` (`c = 98`, `b4 = 6`): threshold `T = 10074553` - LIVE: closes the regime `[986888, 10074553]`; `L > 10074553` stays open. -/
theorem sreClass1Absorption_of_datum_197_98 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 197) (hK : (class1SlopeDatum ctx).K₀ = 98)
    (hL : shellLadderDepth ctx ≤ 10074553) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_197_98 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (6 * (((supportShell ctx.shell.d ctx.shell.X).card + 98 - 1) / 98)) hcard ?_
  refine sreNatGate_of_regime (b4 := 6) (c := 98) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-- `(199,99)` (`c = 54`, `b4 = 4`): threshold `T = 8326927` - LIVE: closes the regime `[986888, 8326927]`; `L > 8326927` stays open. -/
theorem sreClass1Absorption_of_datum_199_99 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 199) (hK : (class1SlopeDatum ctx).K₀ = 99)
    (hL : shellLadderDepth ctx ≤ 8326927) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcard := sreClass1Count_of_datum_199_99 ctx hq hK
  refine sreAbsorption_of_nat_gate ctx
    (4 * (((supportShell ctx.shell.d ctx.shell.X).card + 54 - 1) / 54)) hcard ?_
  refine sreNatGate_of_regime (b4 := 4) (c := 54) (by norm_num)
    (le_of_lt (em_supportShell_strict ctx)) ?_ ?_
  · exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)) (by norm_num)
  · exact sreSlackBound ctx
      (le_trans
        (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hL)))
        (by norm_num))

/-! ## Part 3.  The master lists, the threshold table, and the dispatcher -/

/-- The 23 wave-14 class-1 survivor pairs of `q <= 99` (the `CNLClass1PairClosure`
open data - the wave-5 obstructed moduli `25/29/37/41/47/49` plus the in-modulus
leftovers). -/
def sreWave14Pairs : List (ℕ × ℕ) := [ (25, 2), (25, 12), (29, 14), (35, 3), (35, 17), (37, 18),
   (39, 6), (41, 20), (47, 23), (49, 3), (49, 24), (55, 5), (57, 1), (57, 28), (63, 10), (69, 11),
   (69, 34), (75, 7), (75, 12), (75, 37), (87, 1), (87, 14), (99, 5)]

/-- **The complete current class-1 survivor master list** (110 pairs): the 23 wave-14
pairs plus the 87 sweep survivors of `101 <= q < 200`. -/
def sreClass1SurvivorMasterList : List (ℕ × ℕ) :=
  sreWave14Pairs ++ finiteTailsSweepClass1SurvivorPairs

theorem sreClass1SurvivorMasterList_length :
    sreClass1SurvivorMasterList.length = 110 := rfl

/-- **The machine-readable threshold table** `(q, K0, c, b4, T)`:
`c` = certified orbit period from index 1, `b4` = certified band-4 residue count,
`T = floor(15*2^24*c/(408*b4))` = the sharp regime threshold of the corrected gate
`408*b4*L ≤ 15*2^24*c`. -/
def sreClass1ThresholdTable : List (ℕ × ℕ × ℕ × ℕ × ℕ) := [ (25, 2, 10, 1, 6168094),
   (25, 12, 10, 1, 6168094), (29, 14, 14, 1, 8635331), (35, 3, 7, 1, 4317665),
   (35, 17, 7, 1, 4317665), (37, 18, 18, 1, 11102569), (39, 6, 6, 1, 3700856),
   (41, 20, 10, 1, 6168094), (47, 23, 14, 1, 8635331), (49, 3, 11, 1, 6784903),
   (49, 24, 11, 1, 6784903), (55, 5, 5, 1, 3084047), (57, 1, 9, 1, 5551284),
   (57, 28, 9, 1, 5551284), (63, 10, 2, 1, 1233618), (69, 11, 11, 2, 3392451),
   (69, 34, 11, 2, 3392451), (75, 7, 11, 1, 6784903), (75, 12, 10, 1, 6168094),
   (75, 37, 11, 1, 6784903), (87, 1, 11, 1, 6784903), (87, 14, 11, 1, 6784903),
   (99, 5, 15, 1, 9252141), (101, 50, 50, 3, 10280156), (103, 51, 28, 1, 17270663),
   (105, 7, 1, 1, 616809), (105, 52, 8, 1, 4934475), (107, 53, 53, 4, 8172724),
   (111, 1, 14, 1, 8635331), (111, 18, 18, 1, 11102569), (111, 55, 22, 2, 6784903),
   (115, 2, 19, 2, 5859689), (115, 11, 25, 1, 15420235), (115, 57, 25, 1, 15420235),
   (117, 1, 3, 1, 1850428), (117, 4, 3, 1, 1850428), (119, 8, 9, 1, 5551284),
   (119, 59, 15, 1, 9252141), (121, 5, 55, 3, 11308172), (121, 60, 55, 3, 11308172),
   (125, 2, 50, 3, 10280156), (125, 12, 50, 3, 10280156), (125, 62, 50, 3, 10280156),
   (131, 65, 65, 4, 10023152), (133, 3, 7, 1, 4317665), (133, 9, 7, 2, 2158832),
   (135, 7, 19, 2, 5859689), (135, 13, 19, 2, 5859689), (135, 22, 19, 2, 5859689),
   (135, 67, 19, 2, 5859689), (137, 68, 34, 4, 5242880), (139, 69, 69, 5, 8511969),
   (141, 1, 23, 1, 14186616), (141, 23, 23, 2, 7093308), (141, 70, 23, 2, 7093308),
   (143, 5, 35, 2, 10794164), (143, 6, 25, 1, 15420235), (143, 71, 35, 2, 10794164),
   (145, 2, 14, 1, 8635331), (145, 14, 14, 1, 8635331), (145, 72, 14, 1, 8635331),
   (147, 1, 20, 1, 12336188), (147, 10, 22, 2, 6784903), (147, 73, 22, 2, 6784903),
   (149, 74, 74, 4, 11410974), (153, 1, 10, 1, 6168094), (153, 4, 10, 1, 6168094),
   (153, 8, 10, 1, 6168094), (153, 25, 14, 1, 8635331), (153, 76, 14, 1, 8635331),
   (155, 15, 2, 1, 1233618), (159, 1, 21, 1, 12952997), (159, 26, 21, 1, 12952997),
   (159, 79, 31, 3, 6373697), (161, 3, 15, 1, 9252141), (161, 11, 18, 2, 5551284),
   (161, 80, 18, 2, 5551284), (163, 81, 81, 5, 9992312), (165, 1, 7, 1, 4317665),
   (165, 2, 7, 1, 4317665), (165, 7, 9, 1, 5551284), (165, 16, 7, 1, 4317665),
   (167, 83, 47, 3, 9663347), (169, 6, 78, 5, 9622226), (169, 84, 78, 5, 9622226),
   (173, 86, 86, 6, 8840934), (175, 2, 29, 1, 17887472), (175, 3, 31, 3, 6373697),
   (175, 12, 31, 3, 6373697), (175, 17, 31, 3, 6373697), (175, 87, 31, 3, 6373697),
   (177, 1, 29, 1, 17887472), (177, 29, 29, 2, 8943736), (177, 88, 29, 1, 17887472),
   (179, 89, 89, 5, 10979207), (181, 90, 90, 5, 11102569), (183, 1, 26, 3, 5345681),
   (183, 30, 30, 2, 9252141), (185, 2, 18, 2, 5551284), (185, 18, 18, 2, 5551284),
   (185, 92, 18, 2, 5551284), (187, 8, 21, 1, 12952997), (187, 93, 19, 3, 3906459),
   (189, 10, 8, 1, 4934475), (189, 13, 9, 2, 2775642), (191, 95, 54, 2, 16653854),
   (193, 96, 48, 2, 14803425), (195, 19, 6, 2, 1850428), (197, 98, 98, 6, 10074553),
   (199, 99, 54, 4, 8326927)]

theorem sreClass1ThresholdTable_length :
    sreClass1ThresholdTable.length = 110 := rfl

/-- **Coverage**: the threshold table enumerates EXACTLY the master survivor list,
in order - every pair on the master lists carries a certificate row. -/
theorem sreClass1ThresholdTable_covers_master :
    sreClass1ThresholdTable.map (fun e => (e.1, e.2.1))
      = sreClass1SurvivorMasterList := rfl

/-- Category 1 (honest): thresholds below even the generic floor `493461` - the gate
NEVER fires.  Empty at this build (every pair has `T ≥ 616809`). -/
def sreClass1NeverFirePairs : List (ℕ × ℕ) := []

/-- Category 2 (honest): `493461 ≤ T < 986888` - fires against the generic floor
alone, but VACUOUS on actual contexts by the q-side pin floor
(`sreClass1Gate_vacuous_below_pin`). -/
def sreClass1SubPinPairs : List (ℕ × ℕ) := [(105, 7)]

/-- Category 3: `T ≥ 986888` - the regime `[986888, T]` is genuinely closed;
`L > T` is the honest per-pair deep-shell residual. -/
def sreClass1LiveRegimePairs : List (ℕ × ℕ) := [ (25, 2), (25, 12), (29, 14), (35, 3), (35, 17),
   (37, 18), (39, 6), (41, 20), (47, 23), (49, 3), (49, 24), (55, 5), (57, 1), (57, 28), (63, 10),
   (69, 11), (69, 34), (75, 7), (75, 12), (75, 37), (87, 1), (87, 14), (99, 5), (101, 50),
   (103, 51), (105, 52), (107, 53), (111, 1), (111, 18), (111, 55), (115, 2), (115, 11),
   (115, 57), (117, 1), (117, 4), (119, 8), (119, 59), (121, 5), (121, 60), (125, 2), (125, 12),
   (125, 62), (131, 65), (133, 3), (133, 9), (135, 7), (135, 13), (135, 22), (135, 67), (137, 68),
   (139, 69), (141, 1), (141, 23), (141, 70), (143, 5), (143, 6), (143, 71), (145, 2), (145, 14),
   (145, 72), (147, 1), (147, 10), (147, 73), (149, 74), (153, 1), (153, 4), (153, 8), (153, 25),
   (153, 76), (155, 15), (159, 1), (159, 26), (159, 79), (161, 3), (161, 11), (161, 80),
   (163, 81), (165, 1), (165, 2), (165, 7), (165, 16), (167, 83), (169, 6), (169, 84), (173, 86),
   (175, 2), (175, 3), (175, 12), (175, 17), (175, 87), (177, 1), (177, 29), (177, 88), (179, 89),
   (181, 90), (183, 1), (183, 30), (185, 2), (185, 18), (185, 92), (187, 8), (187, 93), (189, 10),
   (189, 13), (191, 95), (193, 96), (195, 19), (197, 98), (199, 99)]

theorem sreClass1Categories_count :
    sreClass1NeverFirePairs.length = 0
      ∧ sreClass1SubPinPairs.length = 1
      ∧ sreClass1LiveRegimePairs.length = 109 :=
  ⟨rfl, rfl, rfl⟩

/-- **THE AGGREGATE DISPATCHER**: at any context whose datum row `(q, K0, c, b4, T)`
sits in the threshold table, the scale regime `L ≤ T` closes the corrected class-1
absorption (the capstone field shape). -/
theorem sreClass1Absorption_of_mem (ctx : ActualFailureContext)
    {qv Kv cv bv Tv : ℕ}
    (hmem : (qv, Kv, cv, bv, Tv) ∈ sreClass1ThresholdTable)
    (hq : (class1SlopeDatum ctx).q = qv) (hK : (class1SlopeDatum ctx).K₀ = Kv)
    (hL : shellLadderDepth ctx ≤ Tv) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  simp only [sreClass1ThresholdTable, List.mem_cons, List.not_mem_nil,
    or_false, Prod.mk.injEq] at hmem
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_25_2 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_25_12 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_29_14 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_35_3 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_35_17 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_37_18 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_39_6 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_41_20 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_47_23 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_49_3 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_49_24 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_55_5 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_57_1 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_57_28 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_63_10 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_69_11 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_69_34 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_75_7 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_75_12 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_75_37 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_87_1 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_87_14 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_99_5 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_101_50 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_103_51 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_105_7 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_105_52 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_107_53 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_111_1 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_111_18 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_111_55 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_115_2 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_115_11 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_115_57 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_117_1 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_117_4 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_119_8 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_119_59 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_121_5 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_121_60 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_125_2 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_125_12 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_125_62 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_131_65 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_133_3 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_133_9 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_135_7 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_135_13 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_135_22 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_135_67 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_137_68 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_139_69 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_141_1 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_141_23 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_141_70 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_143_5 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_143_6 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_143_71 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_145_2 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_145_14 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_145_72 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_147_1 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_147_10 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_147_73 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_149_74 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_153_1 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_153_4 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_153_8 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_153_25 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_153_76 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_155_15 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_159_1 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_159_26 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_159_79 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_161_3 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_161_11 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_161_80 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_163_81 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_165_1 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_165_2 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_165_7 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_165_16 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_167_83 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_169_6 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_169_84 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_173_86 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_175_2 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_175_3 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_175_12 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_175_17 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_175_87 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_177_1 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_177_29 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_177_88 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_179_89 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_181_90 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_183_1 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_183_30 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_185_2 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_185_18 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_185_92 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_187_8 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_187_93 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_189_10 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_189_13 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_191_95 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_193_96 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_195_19 ctx hq hK hL
  rcases hmem with ⟨rfl, rfl, rfl, rfl, rfl⟩ | hmem
  · exact sreClass1Absorption_of_datum_197_98 ctx hq hK hL
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hmem
  exact sreClass1Absorption_of_datum_199_99 ctx hq hK hL

/-- **The capstone field wrapper**: the EXACT `Erdos260CorrectedResidual.
class1CapAbsorption` shape at `ctx` (`1 ≤ r → absorption`) from the table gate -
the `r` guard is discharged for free (the gate closes every `r`). -/
theorem sreClass1CapAbsorption_field_of_mem (ctx : ActualFailureContext)
    {qv Kv cv bv Tv : ℕ}
    (hmem : (qv, Kv, cv, bv, Tv) ∈ sreClass1ThresholdTable)
    (hq : (class1SlopeDatum ctx).q = qv) (hK : (class1SlopeDatum ctx).K₀ = Kv)
    (hL : shellLadderDepth ctx ≤ Tv) :
    1 ≤ ctx.n24CarryData.r →
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) :=
  fun _ => sreClass1Absorption_of_mem ctx hmem hq hK hL

/-! ## Part 4.  Class 0: the parametric count*excess forms at the 19 survivor pairs

The periods/deep-slot data are certified in `OffFibreMissClosure` (`ofcCert_*`,
`offFibreMissResidualTable`); the public count cap is
`ofcClass0Fibre_card_le_of_survivor : |fibre_0| ≤ ceil(W/c)`.  The forms below are
PARAMETRIC in the per-member excess cap `E` - ready for the sibling freeze-audit
lane's corrected `termChernoff` gate (NOT imported here). -/

/-- **The parametric class-0 mass cap, survivor-generic**: for ANY per-member excess
cap `E`, the class-0 fibre mass is at most `ceil(W/c) * E`. -/
theorem sreClass0Mass_le_of_survivor (ctx : ActualFailureContext)
    (h : Class0DatumSurvivor ctx) (f : ℕ → ℝ) (E : ℝ) (hE : 0 ≤ E)
    (hf : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k ≤ E) :
    ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k
      ≤ ((((supportShell ctx.shell.d ctx.shell.X).card
            + class0SurvivorPeriod (class1SlopeDatum ctx).q - 1)
          / class0SurvivorPeriod (class1SlopeDatum ctx).q : ℕ) : ℝ) * E := by
  have hcard := ofcClass0Fibre_card_le_of_survivor ctx h
  have hsum := Finset.sum_le_card_nsmul
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0) f E hf
  rw [nsmul_eq_mul] at hsum
  calc ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k
      ≤ ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card : ℝ) * E :=
        hsum
    _ ≤ ((((supportShell ctx.shell.d ctx.shell.X).card
            + class0SurvivorPeriod (class1SlopeDatum ctx).q - 1)
          / class0SurvivorPeriod (class1SlopeDatum ctx).q : ℕ) : ℝ) * E :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hE

/-- The bare product form: `count * E ≤ ceil(W/c) * E` for any nonneg excess cap. -/
theorem sreClass0CountExcess_le_of_survivor (ctx : ActualFailureContext)
    (h : Class0DatumSurvivor ctx) (E : ℝ) (hE : 0 ≤ E) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card : ℝ) * E
      ≤ ((((supportShell ctx.shell.d ctx.shell.X).card
            + class0SurvivorPeriod (class1SlopeDatum ctx).q - 1)
          / class0SurvivorPeriod (class1SlopeDatum ctx).q : ℕ) : ℝ) * E :=
  mul_le_mul_of_nonneg_right
    (by exact_mod_cast ofcClass0Fibre_card_le_of_survivor ctx h) hE

/-- `(17,8)` (period `4`, deep residue `0`): `|fibre_0| ≤ ceil(W/4)`. -/
theorem sreClass0Count_le_of_datum_17_8 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 17) (hK : (class1SlopeDatum ctx).K₀ = 8) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card + 4 - 1) / 4 := by
  have h := ofcClass0Fibre_card_le_of_survivor ctx
    (Or.inl ⟨hq, hK⟩)
  rw [hq, show class0SurvivorPeriod 17 = 4 from by
    norm_num [class0SurvivorPeriod]] at h
  exact h

/-- `(17,8)`: the parametric mass cap `mass_0 ≤ ceil(W/4) * E` - ready for the
sibling's corrected-termChernoff excess cap. -/
theorem sreClass0Mass_le_of_datum_17_8 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 17) (hK : (class1SlopeDatum ctx).K₀ = 8)
    (f : ℕ → ℝ) (E : ℝ) (hE : 0 ≤ E)
    (hf : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k ≤ E) :
    ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k
      ≤ ((((supportShell ctx.shell.d ctx.shell.X).card + 4 - 1) / 4 : ℕ) : ℝ)
        * E := by
  have hcard := sreClass0Count_le_of_datum_17_8 ctx hq hK
  have hsum := Finset.sum_le_card_nsmul
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0) f E hf
  rw [nsmul_eq_mul] at hsum
  calc ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k
      ≤ ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card : ℝ) * E :=
        hsum
    _ ≤ ((((supportShell ctx.shell.d ctx.shell.X).card + 4 - 1) / 4 : ℕ) : ℝ)
        * E :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hE

/-- `(19,9)` (period `9`, deep residue `6`): `|fibre_0| ≤ ceil(W/9)`. -/
theorem sreClass0Count_le_of_datum_19_9 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 19) (hK : (class1SlopeDatum ctx).K₀ = 9) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card + 9 - 1) / 9 := by
  have h := ofcClass0Fibre_card_le_of_survivor ctx
    (Or.inr (Or.inl ⟨hq, hK⟩))
  rw [hq, show class0SurvivorPeriod 19 = 9 from by
    norm_num [class0SurvivorPeriod]] at h
  exact h

/-- `(19,9)`: the parametric mass cap `mass_0 ≤ ceil(W/9) * E` - ready for the
sibling's corrected-termChernoff excess cap. -/
theorem sreClass0Mass_le_of_datum_19_9 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 19) (hK : (class1SlopeDatum ctx).K₀ = 9)
    (f : ℕ → ℝ) (E : ℝ) (hE : 0 ≤ E)
    (hf : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k ≤ E) :
    ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k
      ≤ ((((supportShell ctx.shell.d ctx.shell.X).card + 9 - 1) / 9 : ℕ) : ℝ)
        * E := by
  have hcard := sreClass0Count_le_of_datum_19_9 ctx hq hK
  have hsum := Finset.sum_le_card_nsmul
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0) f E hf
  rw [nsmul_eq_mul] at hsum
  calc ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k
      ≤ ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card : ℝ) * E :=
        hsum
    _ ≤ ((((supportShell ctx.shell.d ctx.shell.X).card + 9 - 1) / 9 : ℕ) : ℝ)
        * E :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hE

/-- `(21,1)` (period `2`, deep residue `0`): `|fibre_0| ≤ ceil(W/2)`. -/
theorem sreClass0Count_le_of_datum_21_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 21) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card + 2 - 1) / 2 := by
  have h := ofcClass0Fibre_card_le_of_survivor ctx
    (Or.inr (Or.inr (Or.inl ⟨hq, hK⟩)))
  rw [hq, show class0SurvivorPeriod 21 = 2 from by
    norm_num [class0SurvivorPeriod]] at h
  exact h

/-- `(21,1)`: the parametric mass cap `mass_0 ≤ ceil(W/2) * E` - ready for the
sibling's corrected-termChernoff excess cap. -/
theorem sreClass0Mass_le_of_datum_21_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 21) (hK : (class1SlopeDatum ctx).K₀ = 1)
    (f : ℕ → ℝ) (E : ℝ) (hE : 0 ≤ E)
    (hf : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k ≤ E) :
    ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k
      ≤ ((((supportShell ctx.shell.d ctx.shell.X).card + 2 - 1) / 2 : ℕ) : ℝ)
        * E := by
  have hcard := sreClass0Count_le_of_datum_21_1 ctx hq hK
  have hsum := Finset.sum_le_card_nsmul
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0) f E hf
  rw [nsmul_eq_mul] at hsum
  calc ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k
      ≤ ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card : ℝ) * E :=
        hsum
    _ ≤ ((((supportShell ctx.shell.d ctx.shell.X).card + 2 - 1) / 2 : ℕ) : ℝ)
        * E :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hE

/-- `(25,2)` (period `10`, deep residue `0`): `|fibre_0| ≤ ceil(W/10)`. -/
theorem sreClass0Count_le_of_datum_25_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 25) (hK : (class1SlopeDatum ctx).K₀ = 2) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card + 10 - 1) / 10 := by
  have h := ofcClass0Fibre_card_le_of_survivor ctx
    (Or.inr (Or.inr (Or.inr (Or.inl ⟨hq, hK⟩))))
  rw [hq, show class0SurvivorPeriod 25 = 10 from by
    norm_num [class0SurvivorPeriod]] at h
  exact h

/-- `(25,2)`: the parametric mass cap `mass_0 ≤ ceil(W/10) * E` - ready for the
sibling's corrected-termChernoff excess cap. -/
theorem sreClass0Mass_le_of_datum_25_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 25) (hK : (class1SlopeDatum ctx).K₀ = 2)
    (f : ℕ → ℝ) (E : ℝ) (hE : 0 ≤ E)
    (hf : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k ≤ E) :
    ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k
      ≤ ((((supportShell ctx.shell.d ctx.shell.X).card + 10 - 1) / 10 : ℕ) : ℝ)
        * E := by
  have hcard := sreClass0Count_le_of_datum_25_2 ctx hq hK
  have hsum := Finset.sum_le_card_nsmul
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0) f E hf
  rw [nsmul_eq_mul] at hsum
  calc ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k
      ≤ ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card : ℝ) * E :=
        hsum
    _ ≤ ((((supportShell ctx.shell.d ctx.shell.X).card + 10 - 1) / 10 : ℕ) : ℝ)
        * E :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hE

/-- `(25,12)` (period `10`, deep residue `8`): `|fibre_0| ≤ ceil(W/10)`. -/
theorem sreClass0Count_le_of_datum_25_12 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 25) (hK : (class1SlopeDatum ctx).K₀ = 12) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card + 10 - 1) / 10 := by
  have h := ofcClass0Fibre_card_le_of_survivor ctx
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hq, hK⟩)))))
  rw [hq, show class0SurvivorPeriod 25 = 10 from by
    norm_num [class0SurvivorPeriod]] at h
  exact h

/-- `(25,12)`: the parametric mass cap `mass_0 ≤ ceil(W/10) * E` - ready for the
sibling's corrected-termChernoff excess cap. -/
theorem sreClass0Mass_le_of_datum_25_12 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 25) (hK : (class1SlopeDatum ctx).K₀ = 12)
    (f : ℕ → ℝ) (E : ℝ) (hE : 0 ≤ E)
    (hf : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k ≤ E) :
    ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k
      ≤ ((((supportShell ctx.shell.d ctx.shell.X).card + 10 - 1) / 10 : ℕ) : ℝ)
        * E := by
  have hcard := sreClass0Count_le_of_datum_25_12 ctx hq hK
  have hsum := Finset.sum_le_card_nsmul
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0) f E hf
  rw [nsmul_eq_mul] at hsum
  calc ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k
      ≤ ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card : ℝ) * E :=
        hsum
    _ ≤ ((((supportShell ctx.shell.d ctx.shell.X).card + 10 - 1) / 10 : ℕ) : ℝ)
        * E :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hE

/-- `(27,1)` (period `9`, deep residue `0`): `|fibre_0| ≤ ceil(W/9)`. -/
theorem sreClass0Count_le_of_datum_27_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 27) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card + 9 - 1) / 9 := by
  have h := ofcClass0Fibre_card_le_of_survivor ctx
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hq, hK⟩))))))
  rw [hq, show class0SurvivorPeriod 27 = 9 from by
    norm_num [class0SurvivorPeriod]] at h
  exact h

/-- `(27,1)`: the parametric mass cap `mass_0 ≤ ceil(W/9) * E` - ready for the
sibling's corrected-termChernoff excess cap. -/
theorem sreClass0Mass_le_of_datum_27_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 27) (hK : (class1SlopeDatum ctx).K₀ = 1)
    (f : ℕ → ℝ) (E : ℝ) (hE : 0 ≤ E)
    (hf : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k ≤ E) :
    ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k
      ≤ ((((supportShell ctx.shell.d ctx.shell.X).card + 9 - 1) / 9 : ℕ) : ℝ)
        * E := by
  have hcard := sreClass0Count_le_of_datum_27_1 ctx hq hK
  have hsum := Finset.sum_le_card_nsmul
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0) f E hf
  rw [nsmul_eq_mul] at hsum
  calc ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k
      ≤ ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card : ℝ) * E :=
        hsum
    _ ≤ ((((supportShell ctx.shell.d ctx.shell.X).card + 9 - 1) / 9 : ℕ) : ℝ)
        * E :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hE

/-- `(27,4)` (period `9`, deep residue `0`): `|fibre_0| ≤ ceil(W/9)`. -/
theorem sreClass0Count_le_of_datum_27_4 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 27) (hK : (class1SlopeDatum ctx).K₀ = 4) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card + 9 - 1) / 9 := by
  have h := ofcClass0Fibre_card_le_of_survivor ctx
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hq, hK⟩)))))))
  rw [hq, show class0SurvivorPeriod 27 = 9 from by
    norm_num [class0SurvivorPeriod]] at h
  exact h

/-- `(27,4)`: the parametric mass cap `mass_0 ≤ ceil(W/9) * E` - ready for the
sibling's corrected-termChernoff excess cap. -/
theorem sreClass0Mass_le_of_datum_27_4 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 27) (hK : (class1SlopeDatum ctx).K₀ = 4)
    (f : ℕ → ℝ) (E : ℝ) (hE : 0 ≤ E)
    (hf : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k ≤ E) :
    ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k
      ≤ ((((supportShell ctx.shell.d ctx.shell.X).card + 9 - 1) / 9 : ℕ) : ℝ)
        * E := by
  have hcard := sreClass0Count_le_of_datum_27_4 ctx hq hK
  have hsum := Finset.sum_le_card_nsmul
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0) f E hf
  rw [nsmul_eq_mul] at hsum
  calc ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k
      ≤ ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card : ℝ) * E :=
        hsum
    _ ≤ ((((supportShell ctx.shell.d ctx.shell.X).card + 9 - 1) / 9 : ℕ) : ℝ)
        * E :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hE

/-- `(27,13)` (period `9`, deep residue `7`): `|fibre_0| ≤ ceil(W/9)`. -/
theorem sreClass0Count_le_of_datum_27_13 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 27) (hK : (class1SlopeDatum ctx).K₀ = 13) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card + 9 - 1) / 9 := by
  have h := ofcClass0Fibre_card_le_of_survivor ctx
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hq, hK⟩))))))))
  rw [hq, show class0SurvivorPeriod 27 = 9 from by
    norm_num [class0SurvivorPeriod]] at h
  exact h

/-- `(27,13)`: the parametric mass cap `mass_0 ≤ ceil(W/9) * E` - ready for the
sibling's corrected-termChernoff excess cap. -/
theorem sreClass0Mass_le_of_datum_27_13 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 27) (hK : (class1SlopeDatum ctx).K₀ = 13)
    (f : ℕ → ℝ) (E : ℝ) (hE : 0 ≤ E)
    (hf : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k ≤ E) :
    ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k
      ≤ ((((supportShell ctx.shell.d ctx.shell.X).card + 9 - 1) / 9 : ℕ) : ℝ)
        * E := by
  have hcard := sreClass0Count_le_of_datum_27_13 ctx hq hK
  have hsum := Finset.sum_le_card_nsmul
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0) f E hf
  rw [nsmul_eq_mul] at hsum
  calc ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k
      ≤ ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card : ℝ) * E :=
        hsum
    _ ≤ ((((supportShell ctx.shell.d ctx.shell.X).card + 9 - 1) / 9 : ℕ) : ℝ)
        * E :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hE

/-- `(29,14)` (period `14`, deep residue `10`): `|fibre_0| ≤ ceil(W/14)`. -/
theorem sreClass0Count_le_of_datum_29_14 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 29) (hK : (class1SlopeDatum ctx).K₀ = 14) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card + 14 - 1) / 14 := by
  have h := ofcClass0Fibre_card_le_of_survivor ctx
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hq, hK⟩)))))))))
  rw [hq, show class0SurvivorPeriod 29 = 14 from by
    norm_num [class0SurvivorPeriod]] at h
  exact h

/-- `(29,14)`: the parametric mass cap `mass_0 ≤ ceil(W/14) * E` - ready for the
sibling's corrected-termChernoff excess cap. -/
theorem sreClass0Mass_le_of_datum_29_14 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 29) (hK : (class1SlopeDatum ctx).K₀ = 14)
    (f : ℕ → ℝ) (E : ℝ) (hE : 0 ≤ E)
    (hf : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k ≤ E) :
    ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k
      ≤ ((((supportShell ctx.shell.d ctx.shell.X).card + 14 - 1) / 14 : ℕ) : ℝ)
        * E := by
  have hcard := sreClass0Count_le_of_datum_29_14 ctx hq hK
  have hsum := Finset.sum_le_card_nsmul
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0) f E hf
  rw [nsmul_eq_mul] at hsum
  calc ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k
      ≤ ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card : ℝ) * E :=
        hsum
    _ ≤ ((((supportShell ctx.shell.d ctx.shell.X).card + 14 - 1) / 14 : ℕ) : ℝ)
        * E :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hE

/-- `(33,1)` (period `5`, deep residue `0`): `|fibre_0| ≤ ceil(W/5)`. -/
theorem sreClass0Count_le_of_datum_33_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 33) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card + 5 - 1) / 5 := by
  have h := ofcClass0Fibre_card_le_of_survivor ctx
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hq, hK⟩))))))))))
  rw [hq, show class0SurvivorPeriod 33 = 5 from by
    norm_num [class0SurvivorPeriod]] at h
  exact h

/-- `(33,1)`: the parametric mass cap `mass_0 ≤ ceil(W/5) * E` - ready for the
sibling's corrected-termChernoff excess cap. -/
theorem sreClass0Mass_le_of_datum_33_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 33) (hK : (class1SlopeDatum ctx).K₀ = 1)
    (f : ℕ → ℝ) (E : ℝ) (hE : 0 ≤ E)
    (hf : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k ≤ E) :
    ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k
      ≤ ((((supportShell ctx.shell.d ctx.shell.X).card + 5 - 1) / 5 : ℕ) : ℝ)
        * E := by
  have hcard := sreClass0Count_le_of_datum_33_1 ctx hq hK
  have hsum := Finset.sum_le_card_nsmul
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0) f E hf
  rw [nsmul_eq_mul] at hsum
  calc ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k
      ≤ ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card : ℝ) * E :=
        hsum
    _ ≤ ((((supportShell ctx.shell.d ctx.shell.X).card + 5 - 1) / 5 : ℕ) : ℝ)
        * E :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hE

/-- `(33,16)` (period `5`, deep residue `0`): `|fibre_0| ≤ ceil(W/5)`. -/
theorem sreClass0Count_le_of_datum_33_16 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 33) (hK : (class1SlopeDatum ctx).K₀ = 16) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card + 5 - 1) / 5 := by
  have h := ofcClass0Fibre_card_le_of_survivor ctx
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hq, hK⟩)))))))))))
  rw [hq, show class0SurvivorPeriod 33 = 5 from by
    norm_num [class0SurvivorPeriod]] at h
  exact h

/-- `(33,16)`: the parametric mass cap `mass_0 ≤ ceil(W/5) * E` - ready for the
sibling's corrected-termChernoff excess cap. -/
theorem sreClass0Mass_le_of_datum_33_16 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 33) (hK : (class1SlopeDatum ctx).K₀ = 16)
    (f : ℕ → ℝ) (E : ℝ) (hE : 0 ≤ E)
    (hf : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k ≤ E) :
    ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k
      ≤ ((((supportShell ctx.shell.d ctx.shell.X).card + 5 - 1) / 5 : ℕ) : ℝ)
        * E := by
  have hcard := sreClass0Count_le_of_datum_33_16 ctx hq hK
  have hsum := Finset.sum_le_card_nsmul
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0) f E hf
  rw [nsmul_eq_mul] at hsum
  calc ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k
      ≤ ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card : ℝ) * E :=
        hsum
    _ ≤ ((((supportShell ctx.shell.d ctx.shell.X).card + 5 - 1) / 5 : ℕ) : ℝ)
        * E :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hE

/-- `(35,2)` (period `5`, deep residue `0`): `|fibre_0| ≤ ceil(W/5)`. -/
theorem sreClass0Count_le_of_datum_35_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 35) (hK : (class1SlopeDatum ctx).K₀ = 2) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card + 5 - 1) / 5 := by
  have h := ofcClass0Fibre_card_le_of_survivor ctx
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hq, hK⟩))))))))))))
  rw [hq, show class0SurvivorPeriod 35 = 5 from by
    norm_num [class0SurvivorPeriod]] at h
  exact h

/-- `(35,2)`: the parametric mass cap `mass_0 ≤ ceil(W/5) * E` - ready for the
sibling's corrected-termChernoff excess cap. -/
theorem sreClass0Mass_le_of_datum_35_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 35) (hK : (class1SlopeDatum ctx).K₀ = 2)
    (f : ℕ → ℝ) (E : ℝ) (hE : 0 ≤ E)
    (hf : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k ≤ E) :
    ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k
      ≤ ((((supportShell ctx.shell.d ctx.shell.X).card + 5 - 1) / 5 : ℕ) : ℝ)
        * E := by
  have hcard := sreClass0Count_le_of_datum_35_2 ctx hq hK
  have hsum := Finset.sum_le_card_nsmul
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0) f E hf
  rw [nsmul_eq_mul] at hsum
  calc ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k
      ≤ ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card : ℝ) * E :=
        hsum
    _ ≤ ((((supportShell ctx.shell.d ctx.shell.X).card + 5 - 1) / 5 : ℕ) : ℝ)
        * E :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hE

/-- `(37,18)` (period `18`, deep residue `10`): `|fibre_0| ≤ ceil(W/18)`. -/
theorem sreClass0Count_le_of_datum_37_18 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 37) (hK : (class1SlopeDatum ctx).K₀ = 18) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card + 18 - 1) / 18 := by
  have h := ofcClass0Fibre_card_le_of_survivor ctx
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hq, hK⟩)))))))))))))
  rw [hq, show class0SurvivorPeriod 37 = 18 from by
    norm_num [class0SurvivorPeriod]] at h
  exact h

/-- `(37,18)`: the parametric mass cap `mass_0 ≤ ceil(W/18) * E` - ready for the
sibling's corrected-termChernoff excess cap. -/
theorem sreClass0Mass_le_of_datum_37_18 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 37) (hK : (class1SlopeDatum ctx).K₀ = 18)
    (f : ℕ → ℝ) (E : ℝ) (hE : 0 ≤ E)
    (hf : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k ≤ E) :
    ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k
      ≤ ((((supportShell ctx.shell.d ctx.shell.X).card + 18 - 1) / 18 : ℕ) : ℝ)
        * E := by
  have hcard := sreClass0Count_le_of_datum_37_18 ctx hq hK
  have hsum := Finset.sum_le_card_nsmul
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0) f E hf
  rw [nsmul_eq_mul] at hsum
  calc ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k
      ≤ ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card : ℝ) * E :=
        hsum
    _ ≤ ((((supportShell ctx.shell.d ctx.shell.X).card + 18 - 1) / 18 : ℕ) : ℝ)
        * E :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hE

/-- `(39,1)` (period `4`, deep residue `0`): `|fibre_0| ≤ ceil(W/4)`. -/
theorem sreClass0Count_le_of_datum_39_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 39) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card + 4 - 1) / 4 := by
  have h := ofcClass0Fibre_card_le_of_survivor ctx
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hq, hK⟩))))))))))))))
  rw [hq, show class0SurvivorPeriod 39 = 4 from by
    norm_num [class0SurvivorPeriod]] at h
  exact h

/-- `(39,1)`: the parametric mass cap `mass_0 ≤ ceil(W/4) * E` - ready for the
sibling's corrected-termChernoff excess cap. -/
theorem sreClass0Mass_le_of_datum_39_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 39) (hK : (class1SlopeDatum ctx).K₀ = 1)
    (f : ℕ → ℝ) (E : ℝ) (hE : 0 ≤ E)
    (hf : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k ≤ E) :
    ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k
      ≤ ((((supportShell ctx.shell.d ctx.shell.X).card + 4 - 1) / 4 : ℕ) : ℝ)
        * E := by
  have hcard := sreClass0Count_le_of_datum_39_1 ctx hq hK
  have hsum := Finset.sum_le_card_nsmul
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0) f E hf
  rw [nsmul_eq_mul] at hsum
  calc ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k
      ≤ ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card : ℝ) * E :=
        hsum
    _ ≤ ((((supportShell ctx.shell.d ctx.shell.X).card + 4 - 1) / 4 : ℕ) : ℝ)
        * E :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hE

/-- `(41,20)` (period `10`, deep residue `8`): `|fibre_0| ≤ ceil(W/10)`. -/
theorem sreClass0Count_le_of_datum_41_20 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 41) (hK : (class1SlopeDatum ctx).K₀ = 20) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card + 10 - 1) / 10 := by
  have h := ofcClass0Fibre_card_le_of_survivor ctx
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hq, hK⟩)))))))))))))))
  rw [hq, show class0SurvivorPeriod 41 = 10 from by
    norm_num [class0SurvivorPeriod]] at h
  exact h

/-- `(41,20)`: the parametric mass cap `mass_0 ≤ ceil(W/10) * E` - ready for the
sibling's corrected-termChernoff excess cap. -/
theorem sreClass0Mass_le_of_datum_41_20 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 41) (hK : (class1SlopeDatum ctx).K₀ = 20)
    (f : ℕ → ℝ) (E : ℝ) (hE : 0 ≤ E)
    (hf : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k ≤ E) :
    ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k
      ≤ ((((supportShell ctx.shell.d ctx.shell.X).card + 10 - 1) / 10 : ℕ) : ℝ)
        * E := by
  have hcard := sreClass0Count_le_of_datum_41_20 ctx hq hK
  have hsum := Finset.sum_le_card_nsmul
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0) f E hf
  rw [nsmul_eq_mul] at hsum
  calc ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k
      ≤ ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card : ℝ) * E :=
        hsum
    _ ≤ ((((supportShell ctx.shell.d ctx.shell.X).card + 10 - 1) / 10 : ℕ) : ℝ)
        * E :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hE

/-- `(43,21)` (period `7`, deep residue `6`): `|fibre_0| ≤ ceil(W/7)`. -/
theorem sreClass0Count_le_of_datum_43_21 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 43) (hK : (class1SlopeDatum ctx).K₀ = 21) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card + 7 - 1) / 7 := by
  have h := ofcClass0Fibre_card_le_of_survivor ctx
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hq, hK⟩))))))))))))))))
  rw [hq, show class0SurvivorPeriod 43 = 7 from by
    norm_num [class0SurvivorPeriod]] at h
  exact h

/-- `(43,21)`: the parametric mass cap `mass_0 ≤ ceil(W/7) * E` - ready for the
sibling's corrected-termChernoff excess cap. -/
theorem sreClass0Mass_le_of_datum_43_21 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 43) (hK : (class1SlopeDatum ctx).K₀ = 21)
    (f : ℕ → ℝ) (E : ℝ) (hE : 0 ≤ E)
    (hf : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k ≤ E) :
    ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k
      ≤ ((((supportShell ctx.shell.d ctx.shell.X).card + 7 - 1) / 7 : ℕ) : ℝ)
        * E := by
  have hcard := sreClass0Count_le_of_datum_43_21 ctx hq hK
  have hsum := Finset.sum_le_card_nsmul
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0) f E hf
  rw [nsmul_eq_mul] at hsum
  calc ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k
      ≤ ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card : ℝ) * E :=
        hsum
    _ ≤ ((((supportShell ctx.shell.d ctx.shell.X).card + 7 - 1) / 7 : ℕ) : ℝ)
        * E :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hE

/-- `(45,1)` (period `5`, deep residue `0`): `|fibre_0| ≤ ceil(W/5)`. -/
theorem sreClass0Count_le_of_datum_45_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 45) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card + 5 - 1) / 5 := by
  have h := ofcClass0Fibre_card_le_of_survivor ctx
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hq, hK⟩)))))))))))))))))
  rw [hq, show class0SurvivorPeriod 45 = 5 from by
    norm_num [class0SurvivorPeriod]] at h
  exact h

/-- `(45,1)`: the parametric mass cap `mass_0 ≤ ceil(W/5) * E` - ready for the
sibling's corrected-termChernoff excess cap. -/
theorem sreClass0Mass_le_of_datum_45_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 45) (hK : (class1SlopeDatum ctx).K₀ = 1)
    (f : ℕ → ℝ) (E : ℝ) (hE : 0 ≤ E)
    (hf : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k ≤ E) :
    ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k
      ≤ ((((supportShell ctx.shell.d ctx.shell.X).card + 5 - 1) / 5 : ℕ) : ℝ)
        * E := by
  have hcard := sreClass0Count_le_of_datum_45_1 ctx hq hK
  have hsum := Finset.sum_le_card_nsmul
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0) f E hf
  rw [nsmul_eq_mul] at hsum
  calc ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k
      ≤ ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card : ℝ) * E :=
        hsum
    _ ≤ ((((supportShell ctx.shell.d ctx.shell.X).card + 5 - 1) / 5 : ℕ) : ℝ)
        * E :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hE

/-- `(45,2)` (period `5`, deep residue `0`): `|fibre_0| ≤ ceil(W/5)`. -/
theorem sreClass0Count_le_of_datum_45_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 45) (hK : (class1SlopeDatum ctx).K₀ = 2) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card + 5 - 1) / 5 := by
  have h := ofcClass0Fibre_card_le_of_survivor ctx
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hq, hK⟩))))))))))))))))))
  rw [hq, show class0SurvivorPeriod 45 = 5 from by
    norm_num [class0SurvivorPeriod]] at h
  exact h

/-- `(45,2)`: the parametric mass cap `mass_0 ≤ ceil(W/5) * E` - ready for the
sibling's corrected-termChernoff excess cap. -/
theorem sreClass0Mass_le_of_datum_45_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 45) (hK : (class1SlopeDatum ctx).K₀ = 2)
    (f : ℕ → ℝ) (E : ℝ) (hE : 0 ≤ E)
    (hf : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k ≤ E) :
    ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k
      ≤ ((((supportShell ctx.shell.d ctx.shell.X).card + 5 - 1) / 5 : ℕ) : ℝ)
        * E := by
  have hcard := sreClass0Count_le_of_datum_45_2 ctx hq hK
  have hsum := Finset.sum_le_card_nsmul
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0) f E hf
  rw [nsmul_eq_mul] at hsum
  calc ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k
      ≤ ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card : ℝ) * E :=
        hsum
    _ ≤ ((((supportShell ctx.shell.d ctx.shell.X).card + 5 - 1) / 5 : ℕ) : ℝ)
        * E :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hE

/-- `(45,4)` (period `5`, deep residue `0`): `|fibre_0| ≤ ceil(W/5)`. -/
theorem sreClass0Count_le_of_datum_45_4 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 45) (hK : (class1SlopeDatum ctx).K₀ = 4) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card + 5 - 1) / 5 := by
  have h := ofcClass0Fibre_card_le_of_survivor ctx
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hq, hK⟩))))))))))))))))))
  rw [hq, show class0SurvivorPeriod 45 = 5 from by
    norm_num [class0SurvivorPeriod]] at h
  exact h

/-- `(45,4)`: the parametric mass cap `mass_0 ≤ ceil(W/5) * E` - ready for the
sibling's corrected-termChernoff excess cap. -/
theorem sreClass0Mass_le_of_datum_45_4 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 45) (hK : (class1SlopeDatum ctx).K₀ = 4)
    (f : ℕ → ℝ) (E : ℝ) (hE : 0 ≤ E)
    (hf : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k ≤ E) :
    ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k
      ≤ ((((supportShell ctx.shell.d ctx.shell.X).card + 5 - 1) / 5 : ℕ) : ℝ)
        * E := by
  have hcard := sreClass0Count_le_of_datum_45_4 ctx hq hK
  have hsum := Finset.sum_le_card_nsmul
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0) f E hf
  rw [nsmul_eq_mul] at hsum
  calc ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, f k
      ≤ ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card : ℝ) * E :=
        hsum
    _ ≤ ((((supportShell ctx.shell.d ctx.shell.X).card + 5 - 1) / 5 : ℕ) : ℝ)
        * E :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hE

/-! ## Part 5.  Machine-readable status (honest) -/

/-- Honest machine-readable status of the survivor regime enumeration. -/
def survivorRegimeEnumerationStatus : List String :=
  [ "SUBJECT (wave-16 follow-up): per-pair certified data for the COMPLETE current class-1 " ++
      "survivor list - 110 pairs = 23 wave-14 pairs of q <= 99 (CNLClass1PairClosure open data, " ++
      "wave-5 obstructed moduli included) + 87 FiniteTailsSweep survivors of 101 <= q < 200 " ++
      "(finiteTailsSweepClass1SurvivorPairs) - enabling the corrected-ledger regime gate of " ++
      "Erdos260CorrectedLedgerCapstone.",
    "CERTIFICATES (goal 1, PROVED): the 87 sweep pairs get NEW kernel-checked certificates " ++
      "sreCert_<q>_<K0> (slopeOrbit_step_eval chains; orbit period from index 1 via the return " ++
      "collision; the certified band-4 residue set of one period) and count caps " ++
      "sreClass1Count_of_datum_* : |fibre_1| <= b4*ceil(W/c) (class1Fibre_card_le_cycleDensity " ++
      "+ band4_cycle_card_le_of_subset).  The 23 wave-14 pairs REUSE the public in-tree count " ++
      "lemmas class1Fibre_card_le_of_datum_* (b4 = 1 at 21 pairs, b4 = 2 at the two q = 69 " ++
      "pairs) - no re-certification.",
    "REGIME GATE (goal 2, PROVED): sreClass1Absorption_of_datum_<q>_<K0> - at the datum, L <= " ++
      "T = floor(15*2^24*c/(408*b4)) closes card(fibre_1)*Y <= (cStar*xi/6)*X = (31/1536)*X, " ++
      "the EXACT Erdos260CorrectedResidual.class1CapAbsorption field shape at ctx (every r; the " ++
      "field's 1 <= r guard is free).  Engine: sreAbsorption_of_nat_gate (the budget-free " ++
      "remake of correctedAbsorption_of_nat_gate via correctedCnlShare_eq) + " ++
      "sreNatGate_of_regime (the capstone's period-block collapse, pure Nat) + sreSlackBound " ++
      "(slack 24*b4*c*L <= 16*X FREE under L <= T from the wave-8 floor 2^493460 < X: every " ++
      "per-pair slack budget is < 2^48).",
    "DISPATCHER + TABLE (goal 3): sreClass1ThresholdTable lists (q, K0, c, b4, T) for all 110 " ++
      "pairs (length lemma; in the full build the coverage lemma " ++
      "sreClass1ThresholdTable_covers_master proves the table enumerates EXACTLY sreWave14Pairs " ++
      "++ finiteTailsSweepClass1SurvivorPairs); sreClass1Absorption_of_mem dispatches any table " ++
      "row; sreClass1CapAbsorption_field_of_mem emits the literal capstone field shape.",
    "THE HONEST THRESHOLD VERDICT: the gate closes ONLY L <= T; L is unbounded, so the " ++
      "deep-shell residual L > T stays OPEN at every pair - no unconditional field closure is " ++
      "claimed.  Proved floors: generic L >= 493461 (sreDepth_ge_493461); and the FloorPushV2 " ++
      "q-side value pin (3*oddpart(Q) <= q at EVERY ctx) gives L >= 986888 at q < 384 = 3*2^7 " ++
      "(sreDepth_ge_986888_of_q_lt_384) - EVERY survivor pair has q <= 199 < 384, so all " ++
      "survivor contexts carry the 986888 floor (the brief's 'only generic L >= 493461' " ++
      "undersells the in-tree state: the q-side pin needs no per-pair value representation).  " ++
      "Categories: NEVER-FIRES (T < 493461): 0 pairs; SUB-PIN (493461 <= T < 986888, fires only " ++
      "in the regime emptied by the pin floor - sreClass1Gate_vacuous_below_pin): 1 pair(s) - " ++
      "(105,7), the band-4 fixed point, c = 1, T = 616809; LIVE (T >= 986888, regime [986888, " ++
      "T] genuinely closed): 109 pairs.  Threshold extremes at this build: min LIVE T = 1233618 " ++
      "((63,10) and (155,15), c = 2); max T = 17887472 ((175,2)/(177,1)/(177,88), c = 29, b4 = " ++
      "1).",
    "CLASS 0 (goal 4, PARAMETRIC - 19 pairs): periods/deep-slot data REUSED from " ++
      "OffFibreMissClosure (ofcCert_*, offFibreMissResidualTable, count cap " ++
      "ofcClass0Fibre_card_le_of_survivor).  Delivered: sreClass0Count_le_of_datum_* (|fibre_0| " ++
      "<= ceil(W/c) with explicit numerals), sreClass0Mass_le_of_datum_* and the generic " ++
      "sreClass0Mass_le_of_survivor / sreClass0CountExcess_le_of_survivor: sum_(k in fibre_0) f " ++
      "k <= ceil(W/c)*E for ANY per-member excess cap E - the count*excess <= bound forms ready " ++
      "for the sibling freeze-audit lane's corrected termChernoff gate.  The sibling's module " ++
      "is NOT imported (it may not exist yet); no class-0 gate inequality is claimed here.",
    "WIRING (goal 5, additive only): nothing in the corrected capstone is edited; the " ++
      "per-pair closures and the field wrapper PRODUCE the class1CapAbsorption field shape " ++
      "consumable at any ctx whose datum sits in the table and whose depth sits in the regime.  " ++
      "What they do NOT produce (honest): the field's full forall-ctx closure - deep shells (L " ++
      "> T per pair), un-enumerated 200 <= q, and every non-survivor datum route remain with " ++
      "the capstone's other lanes.",
    "HYGIENE: additive only - no existing module edited, NOT root-wired (built standalone as " ++
      "Erdos260.SurvivorRegimeEnumeration); no sorry / admit / new axiom / native_decide " ++
      "(decide only on small closed numeric and Finset-literal goals); all #print axioms in " ++
      "[propext, Classical.choice, Quot.sound] or fewer." ]

/-- The status ledger is non-empty (honest, non-vacuous). -/
theorem survivorRegimeEnumerationStatus_nonempty :
    survivorRegimeEnumerationStatus ≠ [] := by
  simp [survivorRegimeEnumerationStatus]

/-! ## Part 6.  Axiom-cleanliness audit -/

#print axioms sreAbsorption_of_nat_gate
#print axioms sreDepth_ge_493461
#print axioms sreDepth_ge_986888_of_q_lt_384
#print axioms sreClass1Gate_vacuous_below_pin
#print axioms sreClass1Count_of_datum_101_50
#print axioms sreClass1Count_of_datum_103_51
#print axioms sreClass1Count_of_datum_105_7
#print axioms sreClass1Count_of_datum_105_52
#print axioms sreClass1Count_of_datum_107_53
#print axioms sreClass1Count_of_datum_111_1
#print axioms sreClass1Count_of_datum_111_18
#print axioms sreClass1Count_of_datum_111_55
#print axioms sreClass1Count_of_datum_115_2
#print axioms sreClass1Count_of_datum_115_11
#print axioms sreClass1Count_of_datum_115_57
#print axioms sreClass1Count_of_datum_117_1
#print axioms sreClass1Count_of_datum_117_4
#print axioms sreClass1Count_of_datum_119_8
#print axioms sreClass1Count_of_datum_119_59
#print axioms sreClass1Count_of_datum_121_5
#print axioms sreClass1Count_of_datum_121_60
#print axioms sreClass1Count_of_datum_125_2
#print axioms sreClass1Count_of_datum_125_12
#print axioms sreClass1Count_of_datum_125_62
#print axioms sreClass1Count_of_datum_131_65
#print axioms sreClass1Count_of_datum_133_3
#print axioms sreClass1Count_of_datum_133_9
#print axioms sreClass1Count_of_datum_135_7
#print axioms sreClass1Count_of_datum_135_13
#print axioms sreClass1Count_of_datum_135_22
#print axioms sreClass1Count_of_datum_135_67
#print axioms sreClass1Count_of_datum_137_68
#print axioms sreClass1Count_of_datum_139_69
#print axioms sreClass1Count_of_datum_141_1
#print axioms sreClass1Count_of_datum_141_23
#print axioms sreClass1Count_of_datum_141_70
#print axioms sreClass1Count_of_datum_143_5
#print axioms sreClass1Count_of_datum_143_6
#print axioms sreClass1Count_of_datum_143_71
#print axioms sreClass1Count_of_datum_145_2
#print axioms sreClass1Count_of_datum_145_14
#print axioms sreClass1Count_of_datum_145_72
#print axioms sreClass1Count_of_datum_147_1
#print axioms sreClass1Count_of_datum_147_10
#print axioms sreClass1Count_of_datum_147_73
#print axioms sreClass1Count_of_datum_149_74
#print axioms sreClass1Count_of_datum_153_1
#print axioms sreClass1Count_of_datum_153_4
#print axioms sreClass1Count_of_datum_153_8
#print axioms sreClass1Count_of_datum_153_25
#print axioms sreClass1Count_of_datum_153_76
#print axioms sreClass1Count_of_datum_155_15
#print axioms sreClass1Count_of_datum_159_1
#print axioms sreClass1Count_of_datum_159_26
#print axioms sreClass1Count_of_datum_159_79
#print axioms sreClass1Count_of_datum_161_3
#print axioms sreClass1Count_of_datum_161_11
#print axioms sreClass1Count_of_datum_161_80
#print axioms sreClass1Count_of_datum_163_81
#print axioms sreClass1Count_of_datum_165_1
#print axioms sreClass1Count_of_datum_165_2
#print axioms sreClass1Count_of_datum_165_7
#print axioms sreClass1Count_of_datum_165_16
#print axioms sreClass1Count_of_datum_167_83
#print axioms sreClass1Count_of_datum_169_6
#print axioms sreClass1Count_of_datum_169_84
#print axioms sreClass1Count_of_datum_173_86
#print axioms sreClass1Count_of_datum_175_2
#print axioms sreClass1Count_of_datum_175_3
#print axioms sreClass1Count_of_datum_175_12
#print axioms sreClass1Count_of_datum_175_17
#print axioms sreClass1Count_of_datum_175_87
#print axioms sreClass1Count_of_datum_177_1
#print axioms sreClass1Count_of_datum_177_29
#print axioms sreClass1Count_of_datum_177_88
#print axioms sreClass1Count_of_datum_179_89
#print axioms sreClass1Count_of_datum_181_90
#print axioms sreClass1Count_of_datum_183_1
#print axioms sreClass1Count_of_datum_183_30
#print axioms sreClass1Count_of_datum_185_2
#print axioms sreClass1Count_of_datum_185_18
#print axioms sreClass1Count_of_datum_185_92
#print axioms sreClass1Count_of_datum_187_8
#print axioms sreClass1Count_of_datum_187_93
#print axioms sreClass1Count_of_datum_189_10
#print axioms sreClass1Count_of_datum_189_13
#print axioms sreClass1Count_of_datum_191_95
#print axioms sreClass1Count_of_datum_193_96
#print axioms sreClass1Count_of_datum_195_19
#print axioms sreClass1Count_of_datum_197_98
#print axioms sreClass1Count_of_datum_199_99
#print axioms sreClass1Absorption_of_datum_25_2
#print axioms sreClass1Absorption_of_datum_25_12
#print axioms sreClass1Absorption_of_datum_29_14
#print axioms sreClass1Absorption_of_datum_35_3
#print axioms sreClass1Absorption_of_datum_35_17
#print axioms sreClass1Absorption_of_datum_37_18
#print axioms sreClass1Absorption_of_datum_39_6
#print axioms sreClass1Absorption_of_datum_41_20
#print axioms sreClass1Absorption_of_datum_47_23
#print axioms sreClass1Absorption_of_datum_49_3
#print axioms sreClass1Absorption_of_datum_49_24
#print axioms sreClass1Absorption_of_datum_55_5
#print axioms sreClass1Absorption_of_datum_57_1
#print axioms sreClass1Absorption_of_datum_57_28
#print axioms sreClass1Absorption_of_datum_63_10
#print axioms sreClass1Absorption_of_datum_69_11
#print axioms sreClass1Absorption_of_datum_69_34
#print axioms sreClass1Absorption_of_datum_75_7
#print axioms sreClass1Absorption_of_datum_75_12
#print axioms sreClass1Absorption_of_datum_75_37
#print axioms sreClass1Absorption_of_datum_87_1
#print axioms sreClass1Absorption_of_datum_87_14
#print axioms sreClass1Absorption_of_datum_99_5
#print axioms sreClass1Absorption_of_datum_101_50
#print axioms sreClass1Absorption_of_datum_103_51
#print axioms sreClass1Absorption_of_datum_105_7
#print axioms sreClass1Absorption_of_datum_105_52
#print axioms sreClass1Absorption_of_datum_107_53
#print axioms sreClass1Absorption_of_datum_111_1
#print axioms sreClass1Absorption_of_datum_111_18
#print axioms sreClass1Absorption_of_datum_111_55
#print axioms sreClass1Absorption_of_datum_115_2
#print axioms sreClass1Absorption_of_datum_115_11
#print axioms sreClass1Absorption_of_datum_115_57
#print axioms sreClass1Absorption_of_datum_117_1
#print axioms sreClass1Absorption_of_datum_117_4
#print axioms sreClass1Absorption_of_datum_119_8
#print axioms sreClass1Absorption_of_datum_119_59
#print axioms sreClass1Absorption_of_datum_121_5
#print axioms sreClass1Absorption_of_datum_121_60
#print axioms sreClass1Absorption_of_datum_125_2
#print axioms sreClass1Absorption_of_datum_125_12
#print axioms sreClass1Absorption_of_datum_125_62
#print axioms sreClass1Absorption_of_datum_131_65
#print axioms sreClass1Absorption_of_datum_133_3
#print axioms sreClass1Absorption_of_datum_133_9
#print axioms sreClass1Absorption_of_datum_135_7
#print axioms sreClass1Absorption_of_datum_135_13
#print axioms sreClass1Absorption_of_datum_135_22
#print axioms sreClass1Absorption_of_datum_135_67
#print axioms sreClass1Absorption_of_datum_137_68
#print axioms sreClass1Absorption_of_datum_139_69
#print axioms sreClass1Absorption_of_datum_141_1
#print axioms sreClass1Absorption_of_datum_141_23
#print axioms sreClass1Absorption_of_datum_141_70
#print axioms sreClass1Absorption_of_datum_143_5
#print axioms sreClass1Absorption_of_datum_143_6
#print axioms sreClass1Absorption_of_datum_143_71
#print axioms sreClass1Absorption_of_datum_145_2
#print axioms sreClass1Absorption_of_datum_145_14
#print axioms sreClass1Absorption_of_datum_145_72
#print axioms sreClass1Absorption_of_datum_147_1
#print axioms sreClass1Absorption_of_datum_147_10
#print axioms sreClass1Absorption_of_datum_147_73
#print axioms sreClass1Absorption_of_datum_149_74
#print axioms sreClass1Absorption_of_datum_153_1
#print axioms sreClass1Absorption_of_datum_153_4
#print axioms sreClass1Absorption_of_datum_153_8
#print axioms sreClass1Absorption_of_datum_153_25
#print axioms sreClass1Absorption_of_datum_153_76
#print axioms sreClass1Absorption_of_datum_155_15
#print axioms sreClass1Absorption_of_datum_159_1
#print axioms sreClass1Absorption_of_datum_159_26
#print axioms sreClass1Absorption_of_datum_159_79
#print axioms sreClass1Absorption_of_datum_161_3
#print axioms sreClass1Absorption_of_datum_161_11
#print axioms sreClass1Absorption_of_datum_161_80
#print axioms sreClass1Absorption_of_datum_163_81
#print axioms sreClass1Absorption_of_datum_165_1
#print axioms sreClass1Absorption_of_datum_165_2
#print axioms sreClass1Absorption_of_datum_165_7
#print axioms sreClass1Absorption_of_datum_165_16
#print axioms sreClass1Absorption_of_datum_167_83
#print axioms sreClass1Absorption_of_datum_169_6
#print axioms sreClass1Absorption_of_datum_169_84
#print axioms sreClass1Absorption_of_datum_173_86
#print axioms sreClass1Absorption_of_datum_175_2
#print axioms sreClass1Absorption_of_datum_175_3
#print axioms sreClass1Absorption_of_datum_175_12
#print axioms sreClass1Absorption_of_datum_175_17
#print axioms sreClass1Absorption_of_datum_175_87
#print axioms sreClass1Absorption_of_datum_177_1
#print axioms sreClass1Absorption_of_datum_177_29
#print axioms sreClass1Absorption_of_datum_177_88
#print axioms sreClass1Absorption_of_datum_179_89
#print axioms sreClass1Absorption_of_datum_181_90
#print axioms sreClass1Absorption_of_datum_183_1
#print axioms sreClass1Absorption_of_datum_183_30
#print axioms sreClass1Absorption_of_datum_185_2
#print axioms sreClass1Absorption_of_datum_185_18
#print axioms sreClass1Absorption_of_datum_185_92
#print axioms sreClass1Absorption_of_datum_187_8
#print axioms sreClass1Absorption_of_datum_187_93
#print axioms sreClass1Absorption_of_datum_189_10
#print axioms sreClass1Absorption_of_datum_189_13
#print axioms sreClass1Absorption_of_datum_191_95
#print axioms sreClass1Absorption_of_datum_193_96
#print axioms sreClass1Absorption_of_datum_195_19
#print axioms sreClass1Absorption_of_datum_197_98
#print axioms sreClass1Absorption_of_datum_199_99
#print axioms sreClass1ThresholdTable_length
#print axioms sreClass1Categories_count
#print axioms sreClass1SurvivorMasterList_length
#print axioms sreClass1ThresholdTable_covers_master
#print axioms sreClass1Absorption_of_mem
#print axioms sreClass1CapAbsorption_field_of_mem
#print axioms sreClass0Mass_le_of_survivor
#print axioms sreClass0CountExcess_le_of_survivor
#print axioms sreClass0Count_le_of_datum_17_8
#print axioms sreClass0Mass_le_of_datum_17_8
#print axioms sreClass0Count_le_of_datum_19_9
#print axioms sreClass0Mass_le_of_datum_19_9
#print axioms sreClass0Count_le_of_datum_21_1
#print axioms sreClass0Mass_le_of_datum_21_1
#print axioms sreClass0Count_le_of_datum_25_2
#print axioms sreClass0Mass_le_of_datum_25_2
#print axioms sreClass0Count_le_of_datum_25_12
#print axioms sreClass0Mass_le_of_datum_25_12
#print axioms sreClass0Count_le_of_datum_27_1
#print axioms sreClass0Mass_le_of_datum_27_1
#print axioms sreClass0Count_le_of_datum_27_4
#print axioms sreClass0Mass_le_of_datum_27_4
#print axioms sreClass0Count_le_of_datum_27_13
#print axioms sreClass0Mass_le_of_datum_27_13
#print axioms sreClass0Count_le_of_datum_29_14
#print axioms sreClass0Mass_le_of_datum_29_14
#print axioms sreClass0Count_le_of_datum_33_1
#print axioms sreClass0Mass_le_of_datum_33_1
#print axioms sreClass0Count_le_of_datum_33_16
#print axioms sreClass0Mass_le_of_datum_33_16
#print axioms sreClass0Count_le_of_datum_35_2
#print axioms sreClass0Mass_le_of_datum_35_2
#print axioms sreClass0Count_le_of_datum_37_18
#print axioms sreClass0Mass_le_of_datum_37_18
#print axioms sreClass0Count_le_of_datum_39_1
#print axioms sreClass0Mass_le_of_datum_39_1
#print axioms sreClass0Count_le_of_datum_41_20
#print axioms sreClass0Mass_le_of_datum_41_20
#print axioms sreClass0Count_le_of_datum_43_21
#print axioms sreClass0Mass_le_of_datum_43_21
#print axioms sreClass0Count_le_of_datum_45_1
#print axioms sreClass0Mass_le_of_datum_45_1
#print axioms sreClass0Count_le_of_datum_45_2
#print axioms sreClass0Mass_le_of_datum_45_2
#print axioms sreClass0Count_le_of_datum_45_4
#print axioms sreClass0Mass_le_of_datum_45_4
#print axioms survivorRegimeEnumerationStatus_nonempty

end

end Erdos260
