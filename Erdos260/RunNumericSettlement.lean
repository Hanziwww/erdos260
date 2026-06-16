import Erdos260.RunClass5BoundaryClosure

/-!
# Erdős 260 — per-regime settlement of the Run / class-5 capstone field `runNumeric`

The `runNumeric` field of `Erdos260CycleResidual`
(`lean/Erdos260/Erdos260CycleCapstone.lean`) is, for every `ctx`, the single Section 26
linear inequality at the canonical multiplier `runDyadicMult ctx`:

`c0 · #fibre₅(ctx) · runDyadicMult ctx ≤ (c⋆·ξ/12) · #supportShell(ctx)`,

where `#fibre₅(ctx) = (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card` and
`#supportShell(ctx) = (supportShell ctx.d ctx.X).card`.  This module records exactly which
shell regimes settle this inequality from already-proved bounds, and isolates the genuine
residual.

## What this module establishes

`RunNumericIneq ctx` names that inequality.  We show:

1. **`r = 0` regime — UNCONDITIONAL** (`runNumericIneq_of_r_eq_zero`).  Note: at `r = 0`
   the multiplier `runDyadicMult ctx = max 0 (1·(L+B+1) − T)` is NOT identically `0` (it is
   positive whenever `L+B+1 > T`), so the inequality does NOT follow from a multiplier
   collapse.  It follows because the class-5 fibre is PROVABLY EMPTY at `r = 0`
   (`class5Fibre_empty_of_r_eq_zero`): `#fibre₅ = 0` makes the left side `0 ≤ nonneg`.  The
   same emptiness route closes every `L ≤ 15420` shell (`runNumericIneq_of_L_le`) and every
   K.1-gated shell (`runNumericIneq_of_gate_ceiling`).

2. **`r ≥ 1` regime — finite per-context cycle checks.**  A period avoiding the canonical
   gap bands `1` and `4` empties the fibre (`runNumericIneq_of_cycle_band_free`); its
   fixed-point form (`runNumericIneq_of_orbit_fixed`) and the explicit modulus family
   `(q, K₀) = (21, 3)` (`runNumericIneq_of_q21_K3`) are closed outright.  The cycle-density
   count bound `#fibre₅ ≤ #class5CycleBand · ⌈W/c⌉` reduces the inequality to the
   per-`(q, K₀, L)` scalar numeric (`runNumericIneq_of_cycleDensity_numeric`); on a
   band-`{1,4}`-free period that count is `0`, so the arithmetic works out trivially.

3. **The sharpest sufficient per-context condition** is `Class5CycleNumericCloses ctx`: some
   orbit period `c` whose cycle-density count, scaled by `c0·runDyadicMult`, fits under the
   support budget.  `runNumericIneq_of_cycleNumericCloses` bridges it to `RunNumericIneq`.
   Because `r = 0` is unconditional, the WHOLE field needs this condition only on `r ≥ 1`
   shells: `RunNumericSettlementHyp` packages exactly that, and `runNumericField_settled` /
   `runSplitBoundary_settled` discharge the full `runNumeric` field (and the capstone
   `RunClass5SplitBoundary` surface) from it.

Honest residual: on `r ≥ 1` shells with a NONEMPTY fibre and no band-`{1,4}`-free period,
`Class5CycleNumericCloses` is NOT derivable from the formalized content — the failure
hypothesis bounds `#supportShell` only from ABOVE, giving no lower bound against
`#fibre₅ · runDyadicMult`.  This is the manuscript's irreducible Section 26 positive-density
input, carried here by one scalar inequality per `r ≥ 1` context.

Everything is composed from existing public lemmas of `RunClass5BoundaryClosure`; nothing is
re-proved.
-/

namespace Erdos260

noncomputable section

/-- **The Run / class-5 capstone inequality at a single context** — verbatim the
`runNumeric` field of `Erdos260CycleResidual` (and the `hcount` hypothesis of
`runSplitOfNumericAt`). -/
def RunNumericIneq (ctx : ActualFailureContext) : Prop :=
  erdos260Constants.c0
      * ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card : ℝ)
      * runDyadicMult ctx
    ≤ (erdos260Constants.cStar * erdos260Constants.ξ / 12)
      * ((supportShell ctx.d ctx.X).card : ℝ)

/-- **Core bridge — an empty class-5 fibre settles the inequality.**  The left side
collapses to `c0 · 0 · runDyadicMult = 0`, dominated by the nonnegative right side. -/
theorem runNumericIneq_of_class5Fibre_empty (ctx : ActualFailureContext)
    (h : routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5 = ∅) :
    RunNumericIneq ctx := by
  refine class5_numeric_of_card_le ctx (N := 0) ?_ ?_
  · exact le_of_eq (Finset.card_eq_zero.mpr h)
  · have hrhs : (0 : ℝ) ≤ (erdos260Constants.cStar * erdos260Constants.ξ / 12)
        * ((supportShell ctx.d ctx.X).card : ℝ) :=
      mul_nonneg
        (div_nonneg
          (mul_nonneg erdos260Constants.cStar_pos.le erdos260Constants.ξ_pos.le)
          (by norm_num))
        (Nat.cast_nonneg _)
    simpa using hrhs

/-! ## 1.  The `r = 0` regime and its emptiness siblings (UNCONDITIONAL) -/

/-- **`r = 0` shells — UNCONDITIONAL.**  The class-5 fibre is empty
(`class5Fibre_empty_of_r_eq_zero`); the multiplier need not vanish. -/
theorem runNumericIneq_of_r_eq_zero (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0) : RunNumericIneq ctx :=
  runNumericIneq_of_class5Fibre_empty ctx (class5Fibre_empty_of_r_eq_zero ctx hr)

/-- **`L ≤ 15420` shells — UNCONDITIONAL** (these are exactly the `r = 0` shells, explicit
numeral form). -/
theorem runNumericIneq_of_L_le (ctx : ActualFailureContext)
    (hL : shellLadderDepth ctx ≤ 15420) : RunNumericIneq ctx :=
  runNumericIneq_of_class5Fibre_empty ctx (class5Fibre_empty_of_L_le ctx hL)

/-- **K.1-gated shells — UNCONDITIONAL given the gate.**  Under
`64(r+1)(L+B+1) < 129L+64` the fibre is empty (`class5Fibre_empty_of_gate_ceiling`). -/
theorem runNumericIneq_of_gate_ceiling (ctx : ActualFailureContext)
    (hnum : 64 * ((ctx.n24CarryData.r + 1)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
        < 129 * shellLadderDepth ctx + 64) :
    RunNumericIneq ctx :=
  runNumericIneq_of_class5Fibre_empty ctx (class5Fibre_empty_of_gate_ceiling ctx hnum)

/-! ## 2.  The `r ≥ 1` regime — finite per-context cycle checks -/

/-- **Band-`{1,4}`-free cycle check.**  A period `c` whose canonical gaps avoid bands `1`
and `4` empties the fibre (`class5Fibre_empty_of_cycle_band_free`); the cycle-density count
is then `0`, so the inequality is immediate.  A finite per-context readout. -/
theorem runNumericIneq_of_cycle_band_free (ctx : ActualFailureContext) {c : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hband : ∀ j, 1 ≤ j → j ≤ c →
      canonGap (class1SlopeDatum ctx).q
          (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) ≠ 1
        ∧ canonGap (class1SlopeDatum ctx).q
            (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) ≠ 4) :
    RunNumericIneq ctx :=
  runNumericIneq_of_class5Fibre_empty ctx
    (class5Fibre_empty_of_cycle_band_free ctx hc hper hband)

/-- **Fixed-point form** of the band-`{1,4}`-free check (`class5Fibre_empty_of_orbit_fixed`):
the orbit stalls at index `1` off bands `1` and `4`. -/
theorem runNumericIneq_of_orbit_fixed (ctx : ActualFailureContext)
    (hfix : slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 2
      = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 1)
    (h1 : canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 1) ≠ 1)
    (h4 : canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 1) ≠ 4) :
    RunNumericIneq ctx :=
  runNumericIneq_of_class5Fibre_empty ctx
    (class5Fibre_empty_of_orbit_fixed ctx hfix h1 h4)

/-- **Explicit modulus family `(q, K₀) = (21, 3)` — closed outright**
(`class5Fibre_empty_of_q21_K3`): the orbit is the fixed point `3` with `canonGap 21 3 = 3`,
which lies in neither band. -/
theorem runNumericIneq_of_q21_K3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 21) (hK : (class1SlopeDatum ctx).K₀ = 3) :
    RunNumericIneq ctx :=
  runNumericIneq_of_class5Fibre_empty ctx (class5Fibre_empty_of_q21_K3 ctx hq hK)

/-- **The cycle-density count route.**  Given a period `c` and the Section 26 numeric at the
PROVED cycle-density count bound `#class5CycleBand · ⌈W/c⌉` (rather than the raw fibre
count), the inequality follows by count monotonicity (`class5_numeric_of_card_le` on
`class5Fibre_card_le_cycleDensity`). -/
theorem runNumericIneq_of_cycleDensity_numeric (ctx : ActualFailureContext) {c : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hnum : erdos260Constants.c0
        * (((class5CycleBand ctx c).card
            * (((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c) : ℕ) : ℝ)
        * runDyadicMult ctx
      ≤ (erdos260Constants.cStar * erdos260Constants.ξ / 12)
        * ((supportShell ctx.d ctx.X).card : ℝ)) :
    RunNumericIneq ctx :=
  class5_numeric_of_card_le ctx (class5Fibre_card_le_cycleDensity ctx hc hper) hnum

/-! ## 3.  The sharpest sufficient per-context condition and the full settlement -/

/-- **The sharpest sufficient per-context condition** bridged through proved bounds: some
orbit period `c` whose cycle-density count, scaled by `c0 · runDyadicMult`, fits under the
support budget `(c⋆ξ/12)·#supportShell`.  A band-`{1,4}`-free period makes the count `0`, so
this condition SUBSUMES every emptiness closure of §2; on a nonempty fibre it is exactly the
per-`(q, K₀, L)` scalar numeric. -/
def Class5CycleNumericCloses (ctx : ActualFailureContext) : Prop :=
  ∃ c : ℕ, 1 ≤ c
    ∧ (∀ m, 1 ≤ m →
        slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
          = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    ∧ erdos260Constants.c0
        * (((class5CycleBand ctx c).card
            * (((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c) : ℕ) : ℝ)
        * runDyadicMult ctx
      ≤ (erdos260Constants.cStar * erdos260Constants.ξ / 12)
        * ((supportShell ctx.d ctx.X).card : ℝ)

/-- `Class5CycleNumericCloses ctx` implies the capstone inequality at `ctx`. -/
theorem runNumericIneq_of_cycleNumericCloses (ctx : ActualFailureContext)
    (h : Class5CycleNumericCloses ctx) : RunNumericIneq ctx := by
  obtain ⟨c, hc, hper, hnum⟩ := h
  exact runNumericIneq_of_cycleDensity_numeric ctx hc hper hnum

/-- **The settlement hypothesis** — the sharpest residual after the unconditional `r = 0`
closure: the per-context cycle-density numeric `Class5CycleNumericCloses` is needed ONLY on
`r ≥ 1` shells. -/
def RunNumericSettlementHyp : Prop :=
  ∀ ctx : ActualFailureContext, 1 ≤ ctx.n24CarryData.r → Class5CycleNumericCloses ctx

/-- **The full `runNumeric` field, settled.**  `r = 0` is discharged unconditionally; the
`r ≥ 1` shells are discharged from `RunNumericSettlementHyp`.  The output is verbatim the
`runNumeric` field type of `Erdos260CycleResidual`. -/
theorem runNumericField_settled (h : RunNumericSettlementHyp) :
    ∀ ctx : ActualFailureContext,
      erdos260Constants.c0
          * ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card : ℝ)
          * runDyadicMult ctx
        ≤ (erdos260Constants.cStar * erdos260Constants.ξ / 12)
          * ((supportShell ctx.d ctx.X).card : ℝ) := by
  intro ctx
  rcases Nat.eq_zero_or_pos ctx.n24CarryData.r with hr | hr
  · exact runNumericIneq_of_r_eq_zero ctx hr
  · exact runNumericIneq_of_cycleNumericCloses ctx (h ctx hr)

/-- **The capstone `RunClass5SplitBoundary` surface, settled** — the exact object consumed
by `runSplitOfNumeric` inside `Erdos260CycleResidual.toSharp`. -/
def runSplitBoundary_settled (h : RunNumericSettlementHyp) :
    ∀ ctx : ActualFailureContext, RunClass5SplitBoundary ctx :=
  runSplitOfNumeric (runNumericField_settled h)

/-- Per-context bridge to the capstone surface from a band-`{1,4}`-free period. -/
def runSplitBoundary_of_cycle_band_free (ctx : ActualFailureContext) {c : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hband : ∀ j, 1 ≤ j → j ≤ c →
      canonGap (class1SlopeDatum ctx).q
          (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) ≠ 1
        ∧ canonGap (class1SlopeDatum ctx).q
            (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) ≠ 4) :
    RunClass5SplitBoundary ctx :=
  runSplitOfNumericAt ctx (runNumericIneq_of_cycle_band_free ctx hc hper hband)

/-- Per-context bridge to the capstone surface for the `(q, K₀) = (21, 3)` family. -/
def runSplitBoundary_of_q21_K3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 21) (hK : (class1SlopeDatum ctx).K₀ = 3) :
    RunClass5SplitBoundary ctx :=
  runSplitOfNumericAt ctx (runNumericIneq_of_q21_K3 ctx hq hK)

/-! ## 4.  Honest status -/

/-- Machine-readable status of the Run / class-5 numeric settlement. -/
def runNumericSettlementStatus : List String :=
  [ "FIELD: Erdos260CycleResidual.runNumeric = forall ctx, c0 * #fibre5(ctx) * " ++
      "runDyadicMult ctx <= (cStar*xi/12) * #supportShell(ctx), named RunNumericIneq ctx.",
    "CORE BRIDGE: runNumericIneq_of_class5Fibre_empty - an EMPTY class-5 fibre forces the " ++
      "left side to c0 * 0 * runDyadicMult = 0 <= nonneg (via class5_numeric_of_card_le at " ++
      "N = 0). All emptiness closures below route through it.",
    "REGIME r = 0 (UNCONDITIONAL): runNumericIneq_of_r_eq_zero. FINDING - runDyadicMult ctx " ++
      "= max 0 (1*(L+B+1) - T) is NOT identically 0 at r = 0 (positive when L+B+1 > T), so " ++
      "the closure is NOT a multiplier collapse; it is the PROVED fibre emptiness " ++
      "class5Fibre_empty_of_r_eq_zero (card = 0). Same route: runNumericIneq_of_L_le " ++
      "(L <= 15420) and runNumericIneq_of_gate_ceiling (any K.1-gated shell).",
    "REGIME r >= 1 (FINITE PER-CONTEXT CYCLE CHECKS): runNumericIneq_of_cycle_band_free - a " ++
      "period avoiding canonical-gap bands 1 and 4 empties the fibre (cycle-density count = " ++
      "0, arithmetic trivial); fixed-point form runNumericIneq_of_orbit_fixed; explicit " ++
      "modulus family (q,K0) = (21,3) closed outright by runNumericIneq_of_q21_K3.",
    "COUNT ROUTE: runNumericIneq_of_cycleDensity_numeric - the proved bound " ++
      "#fibre5 <= #class5CycleBand * ceil(W/c) reduces the inequality to the per-(q,K0,L) " ++
      "scalar numeric (class5_numeric_of_card_le on class5Fibre_card_le_cycleDensity).",
    "SHARPEST SUFFICIENT PER-CONTEXT CONDITION: Class5CycleNumericCloses ctx (some period c " ++
      "with the cycle-density count scaled by c0*runDyadicMult fitting under the support " ++
      "budget). It subsumes every band-{1,4}-free emptiness closure (count 0). Bridge: " ++
      "runNumericIneq_of_cycleNumericCloses.",
    "FULL SETTLEMENT: RunNumericSettlementHyp := forall ctx, 1 <= r -> " ++
      "Class5CycleNumericCloses ctx. runNumericField_settled : RunNumericSettlementHyp -> " ++
      "(the runNumeric field verbatim); runSplitBoundary_settled : RunNumericSettlementHyp " ++
      "-> forall ctx, RunClass5SplitBoundary ctx (the object runSplitOfNumeric consumes in " ++
      "Erdos260CycleResidual.toSharp). r = 0 needs NO hypothesis.",
    "HONEST RESIDUAL (r >= 1, nonempty fibre, no band-{1,4}-free period): " ++
      "Class5CycleNumericCloses is NOT derivable from proved bounds - the failure " ++
      "hypothesis bounds #supportShell only from ABOVE (< c0*X), giving no lower bound " ++
      "against #fibre5 * runDyadicMult, where runDyadicMult >= Y = L/64 > 0 cannot " ++
      "collapse. This is the manuscript's irreducible Section 26 positive-density input, " ++
      "now carried by ONE scalar inequality per r >= 1 context.",
    "NO new axioms / no sorry / no native_decide; composed entirely from existing public " ++
      "lemmas of RunClass5BoundaryClosure." ]

theorem runNumericSettlementStatus_nonempty : runNumericSettlementStatus ≠ [] := by
  simp [runNumericSettlementStatus]

/-! ## 5.  Axiom audit -/

#print axioms RunNumericIneq
#print axioms runNumericIneq_of_class5Fibre_empty
#print axioms runNumericIneq_of_r_eq_zero
#print axioms runNumericIneq_of_L_le
#print axioms runNumericIneq_of_gate_ceiling
#print axioms runNumericIneq_of_cycle_band_free
#print axioms runNumericIneq_of_orbit_fixed
#print axioms runNumericIneq_of_q21_K3
#print axioms runNumericIneq_of_cycleDensity_numeric
#print axioms Class5CycleNumericCloses
#print axioms runNumericIneq_of_cycleNumericCloses
#print axioms RunNumericSettlementHyp
#print axioms runNumericField_settled
#print axioms runSplitBoundary_settled
#print axioms runSplitBoundary_of_cycle_band_free
#print axioms runSplitBoundary_of_q21_K3
#print axioms runNumericSettlementStatus_nonempty

end

end Erdos260
