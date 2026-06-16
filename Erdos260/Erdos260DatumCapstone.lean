import Erdos260.Erdos260CycleCapstone
import Erdos260.TowerFixedPointClosure
import Erdos260.RunNumericSettlement
import Erdos260.ReturnFixedPointClosure
import Erdos260.ChernoffClass0DatumClosure
import Erdos260.CNLClass1DatumClosure
import Erdos260.DensePackFixedPointClosure

/-!
# Erdős 260 — the wave-4 datum capstone

This module consolidates the 2026-06-10 wave-4 datum-lever effort.  It defines
`Erdos260DatumResidual`, the strictly weaker successor of `Erdos260CycleResidual`,
and proves the new final endpoint

`erdos260_of_datumResidual : Erdos260DatumResidual → Erdos260Statement`

by composing ONLY existing public bridges of the six wave-4 modules into the wave-3
capstone `erdos260_of_cycleResidual`.  Nothing is re-proved here.

The wave-4 lever: the orbit datum `(q, K₀)` of the actual failing shell is pinned by
`K₀ = |P|` and the divisor pin `(2K₀ + 1) ∣ q`, so each band's constant-cycle
(fixed-point) family collapses to explicit finite pairs via base-step + divisor-pin +
coprimality (template `band3_fixedHit_pins`, transplanted to bands 2 and 4).

The per-atom surfaces consumed:

1. **Tower / class 2** (`TowerFixedPointClosure`) — `TowerFixedPointResidual`: the
   cycle inequality demanded ONLY on the escape surface `TowerEscape` (strictly
   smaller than the wave-3 `Class2CycleDensityResidual`, witnessed by
   `towerFixedPointResidual_of_cycleDensity`); consumed through
   `towerSplit_of_fixedPointResidual`, which rebuilds the `towerSplit` field VERBATIM.
2. **Run / class 5** (`RunNumericSettlement`) — `RunNumericSettlementHyp`: one
   `Class5CycleNumericCloses` witness per `r ≥ 1` context only (`r = 0`, `L ≤ 15420`,
   gated, band-`{1,4}`-free-cycle and `(21,3)` shells are closed unconditionally via
   fibre emptiness); consumed through `runNumericField_settled`, which rebuilds the
   `runNumeric` field VERBATIM.
3. **Return / class 4** (`ReturnFixedPointClosure`) — PARTIAL: the wave-3 field
   shapes are kept for `returnGates` / `returnMaxClean` / `returnInterior` (carried
   verbatim; the band-2 fixed-point analysis pins the surviving family `(3, 1)` but
   does not replace those fields wholesale), while `returnZero` is WEAKENED to the
   small-carry regime: it is demanded only on contexts where some routed class-4
   start has `2 ^ carryVal2 < K`; the complementary large-carry regime is closed by
   the proved `returnZero_of_carryVal2_large`.  The extra gate-4 entry
   `class4FibreSmall_of_cycleCount` (per-`(q, K₀)` band-2 cycle-count form via
   `band2CycleCount`) is available but adds no new gate shape.
4. **Chernoff / class 0** (`ChernoffClass0DatumClosure`) — the two hypotheses of
   `class0Cycle_of_datum_split`: windowed checks ONLY on the nineteen
   `Class0DatumSurvivor` shells and on `48 ≤ q` shells (the wave-3 surface needed
   them on EVERY `q ≥ 17` shell); it produces the `class0Cycle` field VERBATIM.
5. **CNL / class 1** (`CNLClass1DatumClosure`) — `Class1DatumResidual`: the wave-3
   `r = 0`/deep split, each field relieved of the eighteen band-4-free `(q, K₀)`
   data (`¬ Class1DatumClosed`); consumed through `class1DeepResidual_of_datumResidual`
   into the existing wave-3 chain.
6. **DensePack / class 3** (`DensePackFixedPointClosure`) —
   `DensePackDatumSplitResidual`: the wave-3 cycle-split fields, each additionally
   guarded by the surviving-modulus window `q = 5 ∨ 13 ≤ q` (`q = 7` VOIDED at the
   datum); consumed through `DensePackDatumSplitResidual.toCycleSplit`, which lands
   EXACTLY in the capstone `densePackCycle` field type.

Dependency order mirrors `Erdos260CycleCapstone`: tower / run / return fields first,
then the class-0/class-1/class-3 fields; all fields are mutually independent.
-/

namespace Erdos260

noncomputable section

/-- **The wave-4 datum residual.**  Each field is the sharpest wave-4 surface of its
atom — per-datum finite cycle checks on the survivor pairs only, the escape-surface
cycle inequality, the `r ≥ 1` run numeric, and the small-carry digit regime; the
return count/clean-step/interior fields are carried verbatim from wave 3 (recorded
honestly).  All fields are mutually independent. -/
structure Erdos260DatumResidual where
  /-- Tower / class 2 (escape surface only): the finite cycle inequality demanded
  only on deep shells whose datum configuration escapes every wave-4 closure
  (`q = 9` with `m₀ ≥ 3`, `q = 11` with `m₀ ≥ 5`, `q = 13` with `m₀ ≥ 6`, the fixed
  pairs `(15, K₀ ≤ 2)`, `q = 105` on `K₀ = 7` or `m₀ ≥ 8`, and the un-enumerated
  odd moduli `25 ≤ q ≠ 105`). -/
  towerFixed : TowerFixedPointResidual
  /-- Run / class 5 (`r ≥ 1` only): one `Class5CycleNumericCloses` witness per deep
  context — `r = 0` shells need NO hypothesis (proved fibre emptiness). -/
  runNumeric : RunNumericSettlementHyp
  /-- Return / class 4 (count gates, carried verbatim from wave 3): per ctx, the K.1
  gap-ceiling gate OR the two-window span gate OR the in-window span gate OR a band-2
  cycle-count bound `t·b₂ ≤ r + 1` (the gate-4 entry is dischargeable per-`(q, K₀)`
  via `band2CycleCount`; at the surviving fixed pair `(3, 1)` it is vacuous since
  `b₂ = c`). -/
  returnGates : ∀ ctx : ActualFailureContext,
    64 * ((ctx.n24CarryData.r + 1)
        * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
      < 129 * shellLadderDepth ctx + 64
    ∨ 64 * (ctx.n24CarryData.a
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r)
        - ctx.n24CarryData.a
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X))
      < 2 * (129 * shellLadderDepth ctx + 64)
    ∨ 64 * (ctx.n24CarryData.a
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card - 1)
        - ctx.n24CarryData.a
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X))
      < 129 * shellLadderDepth ctx + 64
    ∨ ∃ c t : ℕ, 1 ≤ c
        ∧ (∀ m, 1 ≤ m →
            slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
              = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
        ∧ (supportShell ctx.shell.d ctx.shell.X).card ≤ t * c
        ∧ t * ((Finset.Icc 1 c).filter (fun j =>
            canonGap (class1SlopeDatum ctx).q
              (slopeOrbit (class1SlopeDatum ctx).q
                (class1SlopeDatum ctx).K₀ j) = 2)).card
            ≤ ctx.n24CarryData.r + 1
  /-- Return / class 4 (digit, Z — WEAKENED to the small-carry regime): the all-pairs
  zero-run between same-slice starts of the self-referential key is demanded only on
  contexts where some routed class-4 start has `2 ^ carryVal2 < K`; the complementary
  large-carry regime (`K ≤ 2 ^ carryVal2` at every start) is closed by the proved
  `returnZero_of_carryVal2_large`. -/
  returnZero : ∀ ctx : ActualFailureContext,
    (∃ k ∈ olcFibre ctx,
      2 ^ carryVal2 ctx k < (supportShell ctx.shell.d ctx.shell.X).card) →
    ∀ y ∈ (olcFibre ctx).image (returnSelfRefKey ctx),
      ∀ x ∈ olcSlice ctx (returnSelfRefKey ctx) y,
        ∀ z ∈ olcSlice ctx (returnSelfRefKey ctx) y,
          x < z → ∀ j, x < j → j ≤ z → ctx.d j = 0
  /-- Return / class 4 (digit, reduced clean step — carried verbatim from wave 3):
  `d(k+1) = 0` at per-slice MAXIMA only. -/
  returnMaxClean : ∀ ctx : ActualFailureContext, ∀ k ∈ olcFibre ctx,
    (∀ z ∈ olcFibre ctx, returnSelfRefKey ctx z = returnSelfRefKey ctx k → z ≤ k) →
    ctx.d (k + 1) = 0
  /-- Return / class 4 (digit, K.1 boundary — carried verbatim from wave 3): descent
  windows stay strictly inside the shell window (at the surviving `(3, 1)` family
  every orbit residue reads band 2, so the interior top-band cycle check cannot fire
  there). -/
  returnInterior : ∀ ctx : ActualFailureContext,
    ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4,
      k + ctx.n24CarryData.r + 1
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card
  /-- Chernoff / class 0 (survivor shells only): the windowed finite cycle check on
  the nineteen `Class0DatumSurvivor` pairs — every other `q < 48` datum is closed
  outright (twelve per-pair cycle certificates + the extended avoid-1 window + the
  divisor-pin enumerations). -/
  class0Survivor : ∀ ctx : ActualFailureContext, Class0DatumSurvivor ctx →
    Class0WindowCycleCheck ctx
  /-- Chernoff / class 0 (large moduli): the windowed finite cycle check on `48 ≤ q`
  shells (the datum enumeration is not extended past 48). -/
  class0Big : ∀ ctx : ActualFailureContext, 48 ≤ (class1SlopeDatum ctx).q →
    Class0WindowCycleCheck ctx
  /-- CNL / class 1 (datum residual): the wave-3 `r = 0`/deep split relieved of the
  eighteen unconditionally closed band-4-free `(q, K₀)` data. -/
  class1Datum : Class1DatumResidual
  /-- DensePack / class 3 (datum split): the wave-3 cycle-split fields additionally
  guarded by the surviving-modulus window `q = 5 ∨ 13 ≤ q` (`q = 7` voided at the
  datum, unique band-3 fixed survivor `(21, 3)`). -/
  densePackDatum : DensePackDatumSplitResidual

namespace Erdos260DatumResidual

/-- **The bridge into the wave-3 capstone**: every field of `Erdos260CycleResidual` is
rebuilt from the wave-4 surfaces through existing public bridges — nothing is re-proved.

* Tower — `towerSplit_of_fixedPointResidual` (escape-surface residual, field verbatim);
* Run — `runNumericField_settled` (`r = 0` discharged unconditionally, field verbatim);
* Return count — `returnGates` carried verbatim (wave-3 shape);
* Return digit Z — per-ctx case split on the carry-valuation regime: the large-carry
  regime is closed by `returnZero_of_carryVal2_large`, the small-carry regime is the
  residual hypothesis;
* Return digit clean step / interior — carried verbatim (wave-3 shapes);
* class 0 — `class0Cycle_of_datum_split` (windowed checks only on survivors + `48 ≤ q`);
* class 1 — `class1DeepResidual_of_datumResidual` (band-4-free data filled in);
* class 3 — `DensePackDatumSplitResidual.toCycleSplit` (closed moduli discharged). -/
def toCycle (R : Erdos260DatumResidual) : Erdos260CycleResidual where
  towerSplit := towerSplit_of_fixedPointResidual R.towerFixed
  runNumeric := runNumericField_settled R.runNumeric
  returnGates := R.returnGates
  returnZero := fun ctx => by
    by_cases hex : ∃ k ∈ olcFibre ctx,
        2 ^ carryVal2 ctx k < (supportShell ctx.shell.d ctx.shell.X).card
    · exact R.returnZero ctx hex
    · refine returnZero_of_carryVal2_large ctx fun k hk => ?_
      by_contra hlt
      exact hex ⟨k, hk, not_le.mp hlt⟩
  returnMaxClean := R.returnMaxClean
  returnInterior := R.returnInterior
  class0Cycle := class0Cycle_of_datum_split R.class0Survivor R.class0Big
  class1Deep := class1DeepResidual_of_datumResidual R.class1Datum
  densePackCycle := R.densePackDatum.toCycleSplit

/-- The final statement from the datum residual, through the wave-3 cycle capstone,
the wave-2 sharp capstone and the wave-1 six-atom capstone. -/
theorem toStatement (R : Erdos260DatumResidual) : Erdos260Statement :=
  erdos260_of_cycleResidual R.toCycle

end Erdos260DatumResidual

/-- **The wave-4 final endpoint.**  `Erdos260Statement` from the per-atom wave-4 datum
surfaces, composed through the wave-3 cycle capstone with no re-proving and no
over-strong scalar anywhere on the route. -/
theorem erdos260_of_datumResidual (R : Erdos260DatumResidual) : Erdos260Statement :=
  R.toStatement

/-- Machine-readable status of the wave-4 datum capstone. -/
def erdos260DatumCapstoneStatus : List String :=
  [ "FINAL ENDPOINT (wave 4): erdos260_of_datumResidual (R : Erdos260DatumResidual) : " ++
      "Erdos260Statement, composed through toCycle into erdos260_of_cycleResidual " ++
      "(wave 3), the wave-2 sharp capstone and the wave-1 six-atom capstone; only " ++
      "existing public bridges are consumed, nothing re-proved.",
    "THE WAVE-4 LEVER: the orbit datum (q, K0) is pinned by K0 = |P| and the divisor " ++
      "pin (2K0+1) | q, so each band's constant-cycle (fixed-point) family collapses " ++
      "to explicit finite pairs via base-step + divisor-pin + coprimality (template " ++
      "band3_fixedHit_pins, transplanted to bands 2 and 4).",
    "FIVE ATOMS CARRY THEIR WAVE-4 SURFACE (tower, run, class 0, class 1, densepack); " ++
      "the RETURN atom is PARTIAL: returnGates/returnMaxClean/returnInterior are " ++
      "carried VERBATIM from wave 3 (the band-2 fixed-point module pins the surviving " ++
      "family but does not replace those fields wholesale), and returnZero is " ++
      "WEAKENED to the small-carry regime only.",
    "ATOM Tower/class 2 (WEAKENED to the escape surface): TowerFixedPointResidual " ++
      "demands the cycle inequality only on TowerEscape configurations (q = 9 with " ++
      "m0 >= 3, q = 11 with m0 >= 5, q = 13 with m0 >= 6, the fixed pairs (15, K0 <= 2), " ++
      "q = 105 on K0 = 7 or m0 >= 8, un-enumerated odd moduli 25 <= q != 105); a " ++
      "band-4-full period forces (q, K0) in {(15,1), (15,2), (105,7)} (three pairs, " ++
      "not two - the even-K0 tail (15,2) survives) with oddpart(Q) in {5, 3, 7} " ++
      "respectively; consumed via towerSplit_of_fixedPointResidual (field verbatim); " ++
      "weakening witness towerFixedPointResidual_of_cycleDensity.",
    "ATOM Run/class 5 (WEAKENED to r >= 1): RunNumericSettlementHyp - one " ++
      "Class5CycleNumericCloses witness per deep context; r = 0, L <= 15420, gated, " ++
      "band-{1,4}-free-cycle and (21,3) shells are closed unconditionally via fibre " ++
      "emptiness (NOTE: runDyadicMult is NOT zero at r = 0; the closure is the proved " ++
      "emptiness class5Fibre_empty_of_r_eq_zero, not a multiplier collapse); consumed " ++
      "via runNumericField_settled (field verbatim).",
    "ATOM Return/class 4 (PARTIAL): returnZero is demanded only on contexts with some " ++
      "routed class-4 start at 2^carryVal2 < K - the complementary regime is the " ++
      "proved returnZero_of_carryVal2_large (via " ++
      "returnSelfRef_sliceModulus_lt_width_of_pair, same-slice pairs force " ++
      "2^carryVal2 < K); returnGates keeps the wave-3 4-gate shape with the gate-4 " ++
      "band-2 cycle-count entry dischargeable per-(q,K0) (band2CycleCount, " ++
      "class4FibreSmall_of_cycleCount); the band-2 fixed-point confinement pins the " ++
      "UNIQUE datum survivor (q, K0) = (3, 1), where Q = 2^t and the weighted value " ++
      "is EXACTLY 1/2^t (return_datum_Q_eq, return_datum_value_eq); at (3,1) b2 = c, " ++
      "so the cycle-count gate is vacuous there - exactly the honest wave-3 " ++
      "obstruction relocated to (3,1).",
    "ATOM Chernoff/class 0 (WEAKENED to survivors + 48 <= q): windowed checks only on " ++
      "the NINETEEN Class0DatumSurvivor pairs (all with deep value 1 on-cycle; twelve " ++
      "per-pair closures and the avoid-1 window extended to q < 48 close every other " ++
      "q < 48 datum) and on 48 <= q shells; consumed via class0Cycle_of_datum_split " ++
      "(field verbatim); the wave-3 surface needed the windowed check on EVERY " ++
      "q >= 17 shell.",
    "ATOM CNL/class 1 (WEAKENED by 18 closures): Class1DatumResidual - the r = 0 / " ++
      "deep split relieved of the EIGHTEEN unconditionally closed band-4-free (q,K0) " ++
      "data across moduli {35,39,55,57,63,69,75,87,99}; honest finding: NO whole open " ++
      "modulus in 25..99 closes (every such q keeps at least one band-4 K0); consumed " ++
      "via class1DeepResidual_of_datumResidual into the wave-3 chain; weakening " ++
      "witness class1DatumResidual_of_deepResidual.",
    "ATOM DensePack/class 3 (WEAKENED by the modulus window): " ++
      "DensePackDatumSplitResidual - every field additionally guarded by q = 5 or " ++
      "13 <= q; the q = 7 fixed family is VOIDED at the datum (class3_q7_orbit_ne_one) " ++
      "and the unique band-3 fixed survivor is (21, 3), where Q = 3*2^t and the " ++
      "weighted value is EXACTLY 1/2^t (densePack_datum_Q_eq, " ++
      "densePack_datum_value_eq); consumed via DensePackDatumSplitResidual.toCycleSplit " ++
      "(lands exactly in the capstone densePackCycle field type; equivalence " ++
      "nonempty_datumSplit_iff_cycleSplit).",
    "THE WAVE-5 FLAG: two independent lanes (band 2 at (3,1), band 3 at (21,3)) pin " ++
      "their surviving fixed families to EXACTLY-DYADIC weighted values 1/2^t, and " ++
      "band 4's three survivors carry oddpart(Q) pins {5, 3, 7}; a single formalized " ++
      "digit-side fact incompatible with exactly-dyadic values on a failing shell " ++
      "would void the band-2 and band-3 fixed families wholesale and constrain band 4 " ++
      "via the oddpart pins - the recommended next target.",
    "ROOT OBSTRUCTION (unchanged): no formalized bridge ties the digit-side gap-window " ++
      "pins (hitGap) to the orbit-side band pins (canonGap) beyond the shared index k; " ++
      "the per-atom open cores are exactly the surfaces above on the surviving datum " ++
      "pairs and un-enumerated moduli.  We do NOT claim unconditional closure of any " ++
      "atom.",
    "CLOSED INSIDE the composition (unchanged from waves 1-3): carry floor, faithful " ++
      "phases, mass nonnegativity, the class-6 old-residual vacancy, the joint TRT " ++
      "ledger bound, the Kraft sum, and the hne/hcard counts." ]

theorem erdos260DatumCapstoneStatus_nonempty : erdos260DatumCapstoneStatus ≠ [] := by
  simp [erdos260DatumCapstoneStatus]

#print axioms Erdos260DatumResidual.toCycle
#print axioms Erdos260DatumResidual.toStatement
#print axioms erdos260_of_datumResidual
#print axioms erdos260DatumCapstoneStatus_nonempty

end

end Erdos260
