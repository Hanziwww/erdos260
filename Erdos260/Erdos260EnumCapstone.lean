import Erdos260.Erdos260DatumCapstone
import Erdos260.DyadicValueLever
import Erdos260.TowerModulusEnumeration
import Erdos260.ChernoffClass0SurvivorClosure
import Erdos260.CNLClass1PairClosure
import Erdos260.RunCycleNumericClosure
import Erdos260.ReturnSpanGateClosure
import Erdos260.DensePackGatedClosure

/-!
# Erdős 260 — the wave-5 enumeration capstone

This module consolidates the 2026-06-10 wave-5 full-datum-enumeration effort.  It
defines `Erdos260EnumResidual`, the strictly weaker successor of
`Erdos260DatumResidual`, and proves the new final endpoint

`erdos260_of_enumResidual : Erdos260EnumResidual → Erdos260Statement`

by composing ONLY existing public bridges of the wave-5 modules into the wave-3
capstone `erdos260_of_cycleResidual`.  Nothing is re-proved here.

The wave-5 lever: the divisor pin `(2K₀ + 1) ∣ q` confines the orbit datum of the
actual failing shell to explicit finite pair lists per lane (the window enumerations
on odd `q` below the per-lane horizon), and per-pair certified orbit periods, band
residues and counts shrink — or close outright — every enumerated pair.

The per-atom surfaces consumed:

1. **Tower / class 2** (`TowerModulusEnumeration`) — `TowerModulusEnumerationResidual`:
   the cycle inequality demanded only on the wave-4 counted families and fixed pairs,
   the enumerated `25 ≤ q ≤ 103` data ABOVE their per-pair thresholds (band-4-free
   data are gone entirely; ten whole moduli closed), and the un-enumerated odd moduli
   `107 ≤ q`; consumed through `towerSplit_of_modulusEnumeration`, which rebuilds the
   capstone `towerSplit` field VERBATIM.
2. **Run / class 5** (`RunCycleNumericClosure`) — `RunCycleNumericSettlementHyp`: per
   `r ≥ 1` context EITHER the split-budget two-scalar condition
   `Class5BandHeavyNumericCloses` (band-1 cycle count + heavy sliding-window mass) OR
   the original full numeric `Class5CycleNumericCloses`; consumed through
   `runCycleNumericField_settled`, which rebuilds the `runNumeric` field VERBATIM.
3. **Return / class 4** (`ReturnSpanGateClosure`) — the four Return fields at the
   `ReturnSpanGateResidual` shapes: `returnGates` demanded only off the fifteen
   band-2-free pairs, off the six spaced `b₂ = 1` regimes AND only where the
   two-window numeric criterion fails; `returnZero` (small-carry regime) demanded
   only off the band-2-free pairs and the spaced regimes (the large-carry regime
   stays closed by `returnZero_of_carryVal2_large`); `returnMaxClean` /
   `returnInterior` demanded only off the band-2-free pairs.  Consumed by the same
   per-ctx case splits as `ReturnSpanGateResidual.toDatum`
   (`returnCtxAllFour_of_b2FreeDatum`, `returnGatesZeroCard_of_b2OneSpacedDatum`,
   `returnGatesBody_of_reach_numeric`).  DEDUPE NOTE: the import is possible because
   the former name collision with `RunCycleNumericClosure` was resolved — the Return
   module's low-window enumeration is now `returnSG_datum_low_window_pairs`.
4. **Chernoff / class 0** (`ChernoffClass0SurvivorClosure`) — the successor split of
   `class0Cycle_of_survivor_residue_split`: ONE congruence miss per survivor pair
   (`Class0SurvivorResidueMiss` — the windowed check on the nineteen survivors is
   EQUIVALENT to it), the windowed check on `48 ≤ q < 96` only where the cycle
   provably meets `{1, 3, 5}` (`Class0CycleMeetsShallow`; avoiding cycles close
   free), and the windowed check on `96 ≤ q`; it produces the `class0Cycle` field
   VERBATIM.
5. **CNL / class 1** (`CNLClass1PairClosure`) — `Class1PairResidual`: the wave-4
   `r = 0`/deep split, each field additionally relieved of the gcd-window-miss shells
   and (on `r = 0`) the top-residue-miss shells — all twenty-three open pairs carry
   certified band-4 congruences (the `q = 69` pairs carry two residues); consumed
   through `class1DeepResidual_of_pairResidual` into the existing wave-3 chain.
6. **DensePack / class 3** (`DensePackGatedClosure`) —
   `DensePackGatedClosureResidual`: the wave-4 datum-split fields, each additionally
   guarded by `¬ DensePackDatumClosed` (`q = 15` closed as a whole modulus, `(21, 1)`
   closed; band-3 defeats settled for every enumerated `q ∈ {5, 13, 15, 21}`);
   consumed through `DensePackGatedClosureResidual.toDatumSplit` followed by
   `DensePackDatumSplitResidual.toCycleSplit`, landing EXACTLY in the capstone
   `densePackCycle` field type.

ALTERNATIVE ROUTES (recorded, not consumed): `erdos260_of_returnSpanGateResidual`
(the wave-5 Return surface over the wave-4 shapes of the other five atoms — now
subsumed by this endpoint, which carries all six wave-5 surfaces at once),
`erdos260_of_gatedClosure` (class-3 slot at wave 5 over the six wave-4 sharp fields),
and the conditional lever route `erdos260_of_dyadicValueLever` over
`Erdos260DyadicLeverResidual`, which additionally assumes the single Prop
`DyadicValueLever` (no failing shell has `Q = K₀·2^t`) and in exchange is relieved of
the three exactly-dyadic families `(3,1)`, `(21,3)`, `(105,7)`.

Dependency order mirrors `Erdos260DatumCapstone`: tower / run / return fields first,
then the class-0/class-1/class-3 fields; all fields are mutually independent.
-/

namespace Erdos260

noncomputable section

/-- **The wave-5 enumeration residual.**  Each field is the sharpest wave-5 surface of
its atom — the post-enumeration tower escape surface, the two-scalar run successor,
the span-gate Return successor (the four Return fields at the
`ReturnSpanGateResidual` shapes: demanded only off the closed band-2-free pairs,
spaced `b₂ = 1` regimes and the two-window numeric regime), the survivor congruence
misses with the shallow-meeting mid band, the pair-closure class-1 split, and the
datum-gated class-3 fields.  All fields are mutually independent. -/
structure Erdos260EnumResidual where
  /-- Tower / class 2 (post-enumeration escape surface only): the finite cycle
  inequality demanded only on the wave-4 counted families and fixed pairs, the
  enumerated `25 ≤ q ≤ 103` data above their per-pair thresholds, and the
  un-enumerated odd moduli `107 ≤ q`. -/
  towerEnum : TowerModulusEnumerationResidual
  /-- Run / class 5 (`r ≥ 1` only, two-scalar successor): per deep context, the
  split-budget condition (band-1 cycle count + heavy sliding-window mass) OR the
  original full cycle-density numeric. -/
  runNumeric : RunCycleNumericSettlementHyp
  /-- Return / class 4 (count gates, span-gate successor): the 4-way gate disjunction
  demanded only off the fifteen band-2-free pairs, off the six spaced `b₂ = 1`
  regimes, AND only where the two-window numeric criterion fails. -/
  returnGates : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    2 * (129 * shellLadderDepth ctx + 64)
      ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
    ReturnGatesBody ctx
  /-- Return / class 4 (digit Z, small-carry regime, span-gate successor): the
  all-pairs zero-run demanded only off the closed data and regimes, and only on
  contexts where some routed class-4 start has `2 ^ carryVal2 < K`; the
  complementary large-carry regime is closed by the proved
  `returnZero_of_carryVal2_large`. -/
  returnZero : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    (∃ k ∈ olcFibre ctx,
      2 ^ carryVal2 ctx k < (supportShell ctx.shell.d ctx.shell.X).card) →
    ReturnZeroBody ctx
  /-- Return / class 4 (digit, reduced clean step, span-gate successor): `d(k+1) = 0`
  at per-slice MAXIMA, demanded only off the band-2-free pairs. -/
  returnMaxClean : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ReturnMaxCleanBody ctx
  /-- Return / class 4 (digit, K.1 boundary, span-gate successor): descent windows
  stay strictly inside the shell window, demanded only off the band-2-free pairs. -/
  returnInterior : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx
  /-- Chernoff / class 0 (survivor shells, congruence form): ONE congruence miss
  `k % c ≠ ρ` per floor-realizing window start on each of the nineteen
  `Class0DatumSurvivor` pairs — equivalent to (and strictly leaner than) the full
  windowed check demanded by wave 4. -/
  class0Survivor : ∀ ctx : ActualFailureContext, Class0DatumSurvivor ctx →
    Class0SurvivorResidueMiss ctx
  /-- Chernoff / class 0 (mid band `48 ≤ q < 96`): the windowed check demanded only
  where the cycle provably meets the shallow values `{1, 3, 5}` — avoiding cycles
  close free. -/
  class0Mid : ∀ ctx : ActualFailureContext, 48 ≤ (class1SlopeDatum ctx).q →
    (class1SlopeDatum ctx).q < 96 → Class0CycleMeetsShallow ctx →
    Class0WindowCycleCheck ctx
  /-- Chernoff / class 0 (large moduli): the windowed finite cycle check on `96 ≤ q`
  shells (the enumeration is not extended past 96). -/
  class0Big : ∀ ctx : ActualFailureContext, 96 ≤ (class1SlopeDatum ctx).q →
    Class0WindowCycleCheck ctx
  /-- CNL / class 1 (pair residual): the wave-4 `r = 0`/deep split, additionally
  relieved of the gcd-window-miss shells and the top-residue-miss shells (all
  twenty-three open pairs carry certified band-4 congruences). -/
  class1Pair : Class1PairResidual
  /-- DensePack / class 3 (gated closure): the wave-4 datum-split fields, each
  additionally guarded by `¬ DensePackDatumClosed` (`q = 15` and `(21, 1)` closed). -/
  densePackGated : DensePackGatedClosureResidual

namespace Erdos260EnumResidual

/-- **The bridge into the wave-3 capstone**: every field of `Erdos260CycleResidual` is
rebuilt from the wave-5 surfaces through existing public bridges — nothing is re-proved.

* Tower — `towerSplit_of_modulusEnumeration` (enumeration dispatcher, field verbatim);
* Run — `runCycleNumericField_settled` (`r = 0` discharged unconditionally, `r ≥ 1` by
  either disjunct, field verbatim);
* Return count / digit Z / clean step / interior — the per-ctx case splits of
  `ReturnSpanGateResidual.toDatum`: band-2-free pairs through
  `returnCtxAllFour_of_b2FreeDatum`, spaced `b₂ = 1` regimes through
  `returnGatesZeroCard_of_b2OneSpacedDatum`, the two-window numeric regime through
  `returnGatesBody_of_reach_numeric`, the rest from the residual fields; on digit Z
  the large-carry regime is additionally closed by `returnZero_of_carryVal2_large`
  (exactly as `Erdos260DatumResidual.toCycle`);
* class 0 — `class0Cycle_of_survivor_residue_split` (congruence misses on survivors +
  shallow-meeting mid band + `96 ≤ q`, field verbatim);
* class 1 — `class1DeepResidual_of_pairResidual` (gcd-window and top-residue misses
  filled in);
* class 3 — `DensePackGatedClosureResidual.toDatumSplit` then
  `DensePackDatumSplitResidual.toCycleSplit` (closed data discharged). -/
def toCycle (R : Erdos260EnumResidual) : Erdos260CycleResidual where
  towerSplit := towerSplit_of_modulusEnumeration R.towerEnum
  runNumeric := runCycleNumericField_settled R.runNumeric
  returnGates := fun ctx => by
    by_cases hfree : ReturnB2FreeDatum ctx
    · exact (returnCtxAllFour_of_b2FreeDatum ctx hfree).1
    · by_cases hone : ReturnB2OneSpacedDatum ctx
      · exact (returnGatesZeroCard_of_b2OneSpacedDatum ctx hone).1
      · by_cases hnum : 64 * (((supportShell ctx.shell.d ctx.shell.X).card
              + ctx.n24CarryData.r)
            * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
            < 2 * (129 * shellLadderDepth ctx + 64)
        · exact returnGatesBody_of_reach_numeric ctx hnum
        · exact R.returnGates ctx hfree hone (not_lt.mp hnum)
  returnZero := fun ctx => by
    by_cases hfree : ReturnB2FreeDatum ctx
    · exact (returnCtxAllFour_of_b2FreeDatum ctx hfree).2.1
    · by_cases hone : ReturnB2OneSpacedDatum ctx
      · exact (returnGatesZeroCard_of_b2OneSpacedDatum ctx hone).2.1
      · by_cases hex : ∃ k ∈ olcFibre ctx,
            2 ^ carryVal2 ctx k < (supportShell ctx.shell.d ctx.shell.X).card
        · exact R.returnZero ctx hfree hone hex
        · refine returnZero_of_carryVal2_large ctx fun k hk => ?_
          by_contra hlt
          exact hex ⟨k, hk, not_le.mp hlt⟩
  returnMaxClean := fun ctx => by
    by_cases hfree : ReturnB2FreeDatum ctx
    · exact (returnCtxAllFour_of_b2FreeDatum ctx hfree).2.2.1
    · exact R.returnMaxClean ctx hfree
  returnInterior := fun ctx => by
    by_cases hfree : ReturnB2FreeDatum ctx
    · exact (returnCtxAllFour_of_b2FreeDatum ctx hfree).2.2.2
    · exact R.returnInterior ctx hfree
  class0Cycle := class0Cycle_of_survivor_residue_split R.class0Survivor R.class0Mid
    R.class0Big
  class1Deep := class1DeepResidual_of_pairResidual R.class1Pair
  densePackCycle := R.densePackGated.toDatumSplit.toCycleSplit

/-- The final statement from the enumeration residual, through the wave-3 cycle
capstone, the wave-2 sharp capstone and the wave-1 six-atom capstone. -/
theorem toStatement (R : Erdos260EnumResidual) : Erdos260Statement :=
  erdos260_of_cycleResidual R.toCycle

end Erdos260EnumResidual

/-- **The wave-5 final endpoint.**  `Erdos260Statement` from the per-atom wave-5
enumeration surfaces (all six atoms, Return included via the span-gate successor
shapes), composed through the wave-3 cycle capstone with no re-proving and no
over-strong scalar anywhere on the route. -/
theorem erdos260_of_enumResidual (R : Erdos260EnumResidual) : Erdos260Statement :=
  R.toStatement

/-- **The weakening witness**: the wave-4 datum residual provides the wave-5
enumeration residual outright — every new field demands no more than its wave-4
counterpart (tower via `towerModulusEnumerationResidual_of_fixedPointResidual`, run
via `runCycleNumericSettlementHyp_of_settlement`, Return by dropping the new
span-gate hypotheses, class 0 via
`class0_survivor_residueMiss_of_windowCycleCheck` and the `48 ≤ q` field, class 1
via `class1PairResidual_of_datumResidual`, class 3 via
`DensePackDatumSplitResidual.toGatedClosure`). -/
def erdos260EnumResidual_of_datumResidual (R : Erdos260DatumResidual) :
    Erdos260EnumResidual where
  towerEnum := towerModulusEnumerationResidual_of_fixedPointResidual R.towerFixed
  runNumeric := runCycleNumericSettlementHyp_of_settlement R.runNumeric
  returnGates := fun ctx _ _ _ => R.returnGates ctx
  returnZero := fun ctx _ _ hex => R.returnZero ctx hex
  returnMaxClean := fun ctx _ => R.returnMaxClean ctx
  returnInterior := fun ctx _ => R.returnInterior ctx
  class0Survivor := fun ctx hsv =>
    class0_survivor_residueMiss_of_windowCycleCheck ctx hsv (R.class0Survivor ctx hsv)
  class0Mid := fun ctx h48 _ _ => R.class0Big ctx h48
  class0Big := fun ctx h96 => R.class0Big ctx (by omega)
  class1Pair := class1PairResidual_of_datumResidual R.class1Datum
  densePackGated := R.densePackDatum.toGatedClosure

/-- Machine-readable status of the wave-5 enumeration capstone. -/
def erdos260EnumCapstoneStatus : List String :=
  [ "FINAL ENDPOINT (wave 5): erdos260_of_enumResidual (R : Erdos260EnumResidual) : " ++
      "Erdos260Statement, composed through toCycle into erdos260_of_cycleResidual " ++
      "(wave 3), the wave-2 sharp capstone and the wave-1 six-atom capstone; only " ++
      "existing public bridges are consumed, nothing re-proved.  Weakening witness " ++
      "erdos260EnumResidual_of_datumResidual : Erdos260DatumResidual -> " ++
      "Erdos260EnumResidual - the new endpoint demands no more than wave 4.",
    "THE WAVE-5 LEVER: the divisor pin (2K0+1) | q confines the orbit datum to " ++
      "explicit finite pair lists per lane (window enumerations on odd q below the " ++
      "per-lane horizon), and per-pair certified orbit periods, band residues and " ++
      "counts shrink - or close outright - every enumerated pair.",
    "ALL SIX ATOMS CARRY THEIR WAVE-5 SURFACE (tower, run, RETURN, class 0, " ++
      "class 1, densepack).  DEDUPE COMPLETED (NEW): the former top-level name " ++
      "collision between ReturnSpanGateClosure and RunCycleNumericClosure on " ++
      "datum_low_window_pairs (run form: 3 <= q < 16; return form: q < 17) was " ++
      "resolved by renaming the Return module's copy to " ++
      "returnSG_datum_low_window_pairs; both modules now coexist in one Lean " ++
      "environment and this endpoint consumes the wave-5 Return surface directly " ++
      "(no wave-4 fallback).",
    "ATOM Tower/class 2 (WEAKENED to the post-enumeration escape surface): " ++
      "TowerModulusEnumerationResidual - forty pin enumerations close every odd " ++
      "modulus 25 <= q <= 103: 46 band-4-free data closed by fibre emptiness " ++
      "(TEN whole moduli {27,31,33,43,45,51,65,85,91,93} fully closed), 44 counted " ++
      "data closed up to explicit per-pair sparsity thresholds, and the one hard " ++
      "pair (63,10) (band-4 density 1/2 on its 2-cycle) stays demanded; consumed " ++
      "via towerSplit_of_modulusEnumeration (capstone towerSplit field verbatim); " ++
      "weakening witness towerModulusEnumerationResidual_of_fixedPointResidual.",
    "ATOM Run/class 5 (WEAKENED to the two-scalar successor): " ++
      "RunCycleNumericSettlementHyp - per r >= 1 ctx, Class5BandHeavyNumericCloses " ++
      "(band-1 cycle count + heavy sliding-window mass, splitting the Section 26 " ++
      "budget cStar*xi/12 = cStar*xi/24 + cStar*xi/24) OR the original full " ++
      "Class5CycleNumericCloses; the odd q < 64 datum enumeration carries EXACTLY " ++
      "60 pairs, 6 closed outright ((3,1),(21,3),(51,1),(51,8),(63,1),(63,4)), 54 " ++
      "with certified per-pair period/band-1-count thresholds; consumed via " ++
      "runCycleNumericField_settled (runNumeric field verbatim); weakening witness " ++
      "runCycleNumericSettlementHyp_of_settlement.",
    "ATOM Return/class 4 (WEAKENED to the span-gate successor): the four fields at " ++
      "the ReturnSpanGateResidual shapes - returnGates (4-way gate disjunction) " ++
      "demanded only off the FIFTEEN band-2-free pairs " ++
      "(returnCtxAllFour_of_b2FreeDatum), off the SIX spaced b2 = 1 regimes " ++
      "(returnGatesZeroCard_of_b2OneSpacedDatum) AND only where the two-window " ++
      "numeric criterion fails (returnGatesBody_of_reach_numeric closes it where " ++
      "it holds); returnZero (small-carry regime only; the large-carry regime " ++
      "stays closed by returnZero_of_carryVal2_large inside toCycle) demanded " ++
      "only off the closed data and regimes; returnMaxClean (per-slice maxima) " ++
      "and returnInterior (K.1 interior) demanded only off the band-2-free " ++
      "pairs.  Consumed by the per-ctx case splits of " ++
      "ReturnSpanGateResidual.toDatum, inlined in toCycle.",
    "ATOM Chernoff/class 0 (WEAKENED to congruence misses + shallow-meeting mid " ++
      "band): one congruence miss k % c != rho per floor-realizing start on each of " ++
      "the NINETEEN Class0DatumSurvivor pairs (Class0SurvivorResidueMiss, " ++
      "EQUIVALENT to the wave-4 windowed check there - all nineteen residue-shrunk " ++
      "exactly, none closed; seventeen new per-pair exploits + two wave-4 " ++
      "flagships), the windowed check on 48 <= q < 96 only where the cycle " ++
      "provably meets {1,3,5} (Class0CycleMeetsShallow; avoiding cycles close " ++
      "free), and the windowed check on 96 <= q; consumed via " ++
      "class0Cycle_of_survivor_residue_split (class0Cycle field verbatim); " ++
      "weakening witness class0_survivorResidueMiss_hypothesis_of_datum_split.",
    "ATOM CNL/class 1 (WEAKENED by the pair closures): Class1PairResidual - the " ++
      "wave-4 r = 0/deep split additionally relieved of the gcd-window-miss shells " ++
      "(class1Fibre_empty_of_gcd_window_miss) and, on r = 0, the top-residue-miss " ++
      "shells (class1Fibre_top_notMem_of_pairTopMiss); ALL twenty-three open pairs " ++
      "carry certified band-4 congruences (the q = 69 pairs carry two residues " ++
      "each) plus per-pair count bounds and rigidity; consumed via " ++
      "class1DeepResidual_of_pairResidual into the wave-3 chain; weakening witness " ++
      "class1PairResidual_of_datumResidual.",
    "ATOM DensePack/class 3 (WEAKENED by the datum gate): " ++
      "DensePackGatedClosureResidual - every wave-4 datum-split field additionally " ++
      "guarded by not DensePackDatumClosed: the whole modulus q = 15 (all three " ++
      "pins (15,1),(15,2),(15,7)) and the datum (21,1) are closed outright; " ++
      "band-3 defeats are settled for every enumerated q in {5,13,15,21} " ++
      "((5,2),(13,6),(21,10) certified genuine, (21,3) the wave-4 defeat); " ++
      "consumed via DensePackGatedClosureResidual.toDatumSplit then " ++
      "DensePackDatumSplitResidual.toCycleSplit (lands exactly in the capstone " ++
      "densePackCycle field type; equivalence nonempty_gatedClosure_iff_datumSplit).",
    "ALTERNATIVE ROUTES (recorded, not consumed): " ++
      "erdos260_of_returnSpanGateResidual : ReturnSpanGateResidual -> " ++
      "Erdos260Statement (Return slot at wave 5, all other atoms at wave 4 - now " ++
      "subsumed by this endpoint) and " ++
      "erdos260_of_gatedClosure (class-3 slot at wave 5 over the six wave-4 sharp " ++
      "fields); and THE LEVER ROUTE erdos260_of_dyadicValueLever : " ++
      "Erdos260DyadicLeverResidual -> Erdos260Statement, which additionally " ++
      "assumes the single Prop DyadicValueLever (no failing shell has Q = K0*2^t) " ++
      "and in exchange is relieved of the three exactly-dyadic families (3,1), " ++
      "(21,3), (105,7); the dyadic settlement: the model does NOT pin Q's parity " ++
      "(value data alone cannot void the families - proved witness), value = K0/Q " ++
      "exactly, q = oddpart(Q)*(2K0+1), 2^27*Q < X.",
    "THE HARD CORES AFTER WAVE 5: the three exactly-dyadic families (3,1) Q=2^t, " ++
      "(21,3) Q=3*2^t, (105,7) Q=7*2^t (each value exactly 1/2^t); the non-dyadic " ++
      "tower pairs (15,1) Q=5*2^t value 1/(5*2^t) and (15,2) Q=3*2^t value " ++
      "2/(3*2^t); the tower hard pair (63,10); the per-pair digit-side leftovers " ++
      "(one congruence class each on the nineteen class-0 survivors and the " ++
      "twenty-three class-1 pairs); and the un-enumerated tails (q >= 64 run/" ++
      "return/densepack, q >= 96 class 0, q >= 101 class 1, q >= 107 tower).",
    "ROOT OBSTRUCTION (unchanged): no formalized bridge ties the digit-side " ++
      "gap-window pins (hitGap) to the orbit-side band pins (canonGap) beyond the " ++
      "shared index k; the per-atom open cores are exactly the surfaces above on " ++
      "the surviving datum pairs and un-enumerated moduli.  We do NOT claim " ++
      "unconditional closure of any atom.",
    "CLOSED INSIDE the composition (unchanged from waves 1-4): carry floor, " ++
      "faithful phases, mass nonnegativity, the class-6 old-residual vacancy, the " ++
      "joint TRT ledger bound, the Kraft sum, and the hne/hcard counts." ]

theorem erdos260EnumCapstoneStatus_nonempty : erdos260EnumCapstoneStatus ≠ [] := by
  simp [erdos260EnumCapstoneStatus]

#print axioms Erdos260EnumResidual.toCycle
#print axioms Erdos260EnumResidual.toStatement
#print axioms erdos260_of_enumResidual
#print axioms erdos260EnumResidual_of_datumResidual
#print axioms erdos260EnumCapstoneStatus_nonempty

end

end Erdos260
