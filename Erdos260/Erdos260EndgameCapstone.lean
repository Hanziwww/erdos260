import Erdos260.FixedDataEndgame
import Erdos260.TermFreezeAudits
import Erdos260.SurvivorRegimeEnumeration

/-!
# The wave-17 endgame capstone: `Erdos260EndgameResidual`

The wave-16 corrected surface (`Erdos260CorrectedResidual`,
`Erdos260CorrectedLedgerCapstone`) REBASED on the three wave-17 lanes:

* **`FixedDataEndgame`** — over-transcriptions #5/#6: the `returnGates` field IS
  (band-2 orbit-pin voiding) ∧ (the field on band-2-free contexts)
  (`returnGatesField_iff_band2Void_split`), and the densepack Nat-cover field IS
  (wide band-3 voiding) ∧ (the cover on the complement)
  (`densePackCoverField_iff_band3Void_split`).  The corrected surface should demand
  the count gates only at pin-free contexts; the voiding conjuncts become NAMED
  fields, exactly as `runBand4Void` did in wave 16.
* **`TermFreezeAudits`** — all six ledger phases corrected (`correctedAllPhases`,
  total `(31/256)·X < X/2`); the `FullyCorrectedP9LedgerResidual` bridge reaches
  `Erdos260Statement` from the corrected per-class rows; the class-0 emptiness
  demand is DE-RAZORED to count-cap absorption
  (`tfaCorrectedHChernoff_of_survivor` / `tfaClass0SurvivorAbsorption`).
* **`SurvivorRegimeEnumeration`** — all 110 class-1 survivor pairs carry certified
  periods, band-4 counts and thresholds `T = ⌊15·2²⁴·c/(408·b4)⌋`; the dispatcher
  `sreClass1CapAbsorption_field_of_mem` closes the class-1 absorption at every
  table pair in the regime `L ≤ T`, so the surface field is demanded only at
  `L > T` or off-table data.

## The surface (14 fields)

Tower: `towerEnumLow` / `towerEnumTail` (verbatim wave 16).  Run:
`runBand4Void` + `runNumericLow` / `runNumericTail` on band-4-free contexts
(verbatim wave-16 split).  Return: `returnBand2Void` (NEW: no band-2 orbit pin) +
`returnGatesFree` (the gates demanded ONLY on band-2-free contexts — the second
conjunct of the wave-17 split) + `returnInterior` (verbatim).  DensePack:
`densePackBand3Void` (NEW: no wide band-3 pin) + `densePackCoverFree` (the
Nat-cover only on the complement) + `densePackDensity` / `densePackInterior`
(verbatim ungated fields).  Class 0: `class0Absorption` — the count-cap
ABSORPTION at the 19 survivor pairs REPLACES the emptiness razor (the mid-band and
big-order lanes stay in their wave-16 emptiness form, where emptiness IS the
windowed check).  Class 1: `class1CapAbsorption` demanded only at `1 ≤ r` AND
(off-table datum or `L > T`) — the 110 table pairs in regime are FREE via the
`SurvivorRegimeEnumeration` dispatcher.

## The endpoint

`erdos260_of_endgameResidual` routes through the FULLY-corrected ledger
(`FullyCorrectedP9LedgerResidual.toStatement`): the wave-16 tower/run/return walks
rebuild the genuine-routed budget, the class-0/1 rows close from the absorption
fields (+ the in-tree non-survivor closures + the 110-pair dispatcher), the class-3
row closes from the rebuilt cover residual through the frozen→corrected domination
(`tfaDensePack_frozen_le_correctedAll`), and the TRT row from the budget slots.

## The three-voidings synthesis

`endgame_threeVoidings_deepFixedFamilyVoid`: the residual's three orbit-pin voiding
fields ALONE (bands 2 / 3-wide / 4) imply `DeepFixedFamilyVoid` — no count field is
consumed; the `FixedFamilyShellPersistence` axis stays absorbed
(`endgameResidual_deepShellPersistence`).
-/

namespace Erdos260

noncomputable section

/-! ## Part 1.  The wave-17 endgame surface -/

/-- **The wave-17 endgame capstone surface.**  The wave-16 corrected surface rebased on
the wave-17 results: the Return and DensePack count fields are split into named
orbit-pin voidings plus pin-free count demands (over-transcriptions #5/#6), the class-0
emptiness razor is replaced by count-cap absorption at the survivor pairs, and the
class-1 absorption is relieved at all 110 certified table pairs in the regime
`L ≤ T`.  14 fields. -/
structure Erdos260EndgameResidual where
  /-- Tower / class 2 - enumerated part (`q < 107`); verbatim wave-16 field (relieved
  at the band-pinned fixed data `(3,1)` and `(21,3)`). -/
  towerEnumLow : ∀ ctx : ActualFailureContext,
    TowerModulusEnumEscapeV2 ctx → (class1SlopeDatum ctx).q < 107 →
    (ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx) →
    ¬ ((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1) →
    ¬ ((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3) →
    Class2CycleInequality ctx
  /-- Tower / class 2 - tail (`107 ≤ q`); verbatim wave-16 field. -/
  towerEnumTail : ∀ ctx : ActualFailureContext,
    TowerModulusEnumEscapeV2 ctx →
    107 ≤ (class1SlopeDatum ctx).q →
    (ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx) →
    (((Nat.log 2 (class1SlopeDatum ctx).q + 1) * shellWidth ctx
        < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
            (class1SlopeDatum ctx).K₀)))
        ∧ TowerBand4Budget ctx)
      ∨ Class2CycleInequality ctx
  /-- **The band-4 orbit-pin voiding** (wave 16; the first of the THREE voiding
  conjuncts).  At band-4 pins even the corrected run capacity is refuted
  (`tfaBand4_no_genuine_budget`): the voiding reading is forced against the corrected
  term exactly as against the Section 26 numeric. -/
  runBand4Void : ∀ ctx : ActualFailureContext, ¬ OrbitBandPinned ctx 4
  /-- Run / class 5 - enumerated part (`q < 64`), restricted to band-4-free contexts
  (verbatim wave-16 split conjunct). -/
  runNumericLow : ∀ ctx : ActualFailureContext,
    ¬ OrbitBandPinned ctx 4 →
    (class1SlopeDatum ctx).q < 64 →
    Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx
  /-- Run / class 5 - tail (`64 ≤ q`), restricted to band-4-free contexts; relieved of
  `(93,15)`; verbatim wave-16 split conjunct. -/
  runNumericTail : ∀ ctx : ActualFailureContext,
    ¬ OrbitBandPinned ctx 4 →
    64 ≤ (class1SlopeDatum ctx).q →
    ¬ ((class1SlopeDatum ctx).q = 93 ∧ (class1SlopeDatum ctx).K₀ = 15) →
    ((Nat.log 2 (class1SlopeDatum ctx).q + 1)
        * (supportShell ctx.shell.d ctx.shell.X).card
      < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
          (class1SlopeDatum ctx).K₀)))
      ∧ RunBandBudget ctx
    ∨ Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx
  /-- **The band-2 orbit-pin voiding** (NEW; over-transcription #5, the Return-lane
  sibling of `runBand4Void`): no context pins the slope orbit at band 2.  The wave-16
  `returnGates` field PROVABLY contained this conjunct
  (`returnGatesField_iff_band2Void_split`); the manuscript routes the recurrent band-2
  data through L.3/M.5, not the wave-3 count gates. -/
  returnBand2Void : ∀ ctx : ActualFailureContext, ¬ OrbitBandPinned ctx 2
  /-- Return / class 4 count gates, demanded ONLY on band-2-free contexts (the honest
  I.5/M.2.2 content — the second conjunct of `returnGatesField_iff_band2Void_split`). -/
  returnGatesFree : ∀ ctx : ActualFailureContext, ¬ OrbitBandPinned ctx 2 →
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    2 * (129 * shellLadderDepth ctx + 64)
      ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card
            + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
    ReturnGatesBodyUngated ctx
  /-- Return / class 4 K.1 interior - verbatim wave-16 field (at band-2 pins this is
  exactly the top-band-light position demand,
  `band2_returnInterior_iff_topBand_light`). -/
  returnInterior : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx
  /-- **The wide band-3 orbit-pin voiding** (NEW; over-transcription #6, the densepack
  sibling): no context carries a band-3 pin inside the cover field's own modulus
  window (`Band3PinnedWide` = pin ∧ (`q = 5 ∨ 13 ≤ q`)).  The wave-16
  `ungatedCoverNat` field PROVABLY contained this conjunct
  (`densePackCoverField_iff_band3Void_split`). -/
  densePackBand3Void : ∀ ctx : ActualFailureContext, ¬ Band3PinnedWide ctx
  /-- DensePack / class 3 corrected K.1.2 Nat-cover, demanded ONLY on the wide
  band-3-free complement (the second conjunct of
  `densePackCoverField_iff_band3Void_split`). -/
  densePackCoverFree : ∀ ctx : ActualFailureContext, ¬ Band3PinnedWide ctx →
    ¬ Class3CycleBand3Free ctx →
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
    ¬ DensePackDatumClosed ctx →
    (genuineDensePackStarts ctx).card
        * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
            - (2 * shellLadderDepth ctx + 1))
      ≤ (proofV4DensePackActualPoints ctx.shell).card
  /-- DensePack / class 3 K.1.1 coarea hit-density - verbatim ungated field (at band-3
  pins this forces the extreme sub-shell profile, `band3_density_forces_subshell`). -/
  densePackDensity : ∀ ctx : ActualFailureContext,
    ¬ Class3CycleBand3Free ctx →
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
    ¬ DensePackDatumClosed ctx →
    densePackEndpointDensity ctx
  /-- DensePack / class 3 K.1 active-window interior - verbatim ungated field (at
  band-3 pins this is the top-band-light demand,
  `band3_densePackInterior_iff_topBand_light`). -/
  densePackInterior : ∀ ctx : ActualFailureContext,
    ¬ Class3TopBandCycleFree ctx →
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
    ¬ DensePackDatumClosed ctx →
    ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r + 1
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card
  /-- **The de-razored class-0 field** (the wave-17 replacement of the wave-16
  emptiness field): at the 19 survivor pairs only count-cap ABSORPTION
  `card(fibre₀)·runDyadicMult ≤ (c⋆ξ/6)·X` is demanded (strictly weaker than
  emptiness — `tfaClass0Absorption_of_fibreEmpty`; suppliable from the per-pair ℕ gate
  `1536·⌈W/c⌉·(r+1)(L+B+1) ≤ 31·X`, `tfaClass0SurvivorAbsorption`).  The mid-band and
  big-order lanes keep their wave-16 emptiness form (there emptiness IS the windowed
  check, `ofcClass0Fibre_empty_iff_windowCycleCheck` — no razor was found on those
  lanes). -/
  class0Absorption : ∀ ctx : ActualFailureContext,
    (Class0DatumSurvivor ctx →
      ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card : ℝ)
          * runDyadicMult ctx
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ)) ∧
    (48 ≤ (class1SlopeDatum ctx).q → (class1SlopeDatum ctx).q < 96 →
      Class0CycleMeetsShallow ctx →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0 = ∅) ∧
    (96 ≤ (class1SlopeDatum ctx).q →
      (∃ C, ((Nat.log 2 (class1SlopeDatum ctx).q + 1) * C
            < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
                (class1SlopeDatum ctx).K₀)))
          ∧ ∃ c, C < c ∧ c ≤ (class1SlopeDatum ctx).q
              ∧ (∀ m, 1 ≤ m →
                  slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
                    = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
              ∧ ∀ k ∈ ctx.n24CarryData.starts,
                  129 * shellLadderDepth ctx + 64
                      ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
                  (class1SlopeDatum ctx).q
                    < 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀
                        (cycleRep c k))
      ∨ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0 = ∅)
  /-- **The regime-folded class-1 absorption field** (the wave-17 relief): the wave-16
  count-cap absorption, now demanded ONLY when no `SurvivorRegimeEnumeration` table row
  `(q, K₀, c, b4, T)` covers the context in regime (`L ≤ T`) — at all 110 certified
  table pairs in regime the dispatcher `sreClass1CapAbsorption_field_of_mem` supplies
  the bound FREE.  The `r = 0` shells (all `L ≤ 15420`) stay relieved free. -/
  class1CapAbsorption : ∀ ctx : ActualFailureContext,
    1 ≤ ctx.n24CarryData.r →
    (¬ ∃ cv bv Tv : ℕ,
      ((class1SlopeDatum ctx).q, (class1SlopeDatum ctx).K₀, cv, bv, Tv)
          ∈ sreClass1ThresholdTable
        ∧ shellLadderDepth ctx ≤ Tv) →
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ)

namespace Erdos260EndgameResidual

/-! ### The two over-transcription splits, reassembled -/

/-- The split fields rebuild the FULL wave-16 `returnGates` field (the mpr direction of
over-transcription #5). -/
theorem returnGatesField (R : Erdos260EndgameResidual) : ReturnGatesField :=
  returnGatesField_iff_band2Void_split.mpr ⟨R.returnBand2Void, R.returnGatesFree⟩

/-- The split fields rebuild the FULL wave-16 densepack Nat-cover field (the mpr
direction of over-transcription #6). -/
theorem densePackCoverField (R : Erdos260EndgameResidual) : DensePackCoverField :=
  densePackCoverField_iff_band3Void_split.mpr ⟨R.densePackBand3Void, R.densePackCoverFree⟩

/-- The collapsed densepack residual, rebuilt from the four wave-17 densepack fields. -/
def densePackUngated (R : Erdos260EndgameResidual) : DensePackUngatedClosureResidual where
  ungatedDensity := R.densePackDensity
  ungatedInterior := R.densePackInterior
  ungatedCoverNat := R.densePackCoverField

/-! ### The tower lane (verbatim wave-16 walk) -/

/-- Tower lane — the wave-5 enumeration residual (the wave-16 walk verbatim). -/
def towerEnum (R : Erdos260EndgameResidual) : TowerModulusEnumerationResidual := by
  intro ctx _hdeep hesc
  have hescV2 : TowerModulusEnumEscapeV2 ctx :=
    (towerModulusEnumEscape_iff_v2 ctx).mp hesc
  have haper : ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx := fun hu7 hwp =>
    thirdsLever_windowPeriodic_void_of_oddpartQ_le_seven ctx hu7 hwp
  rcases Nat.lt_or_ge (class1SlopeDatum ctx).q 107 with hlt | hge
  · by_cases h31 : (class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1
    · exact anchoredCapstone_class2Ineq_of_datum_3_1 ctx h31.1 h31.2
    · by_cases h213 : (class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3
      · exact anchoredCapstone_class2Ineq_of_datum_21_3 ctx h213.1 h213.2
      · exact R.towerEnumLow ctx hescV2 hlt haper h31 h213
  · cases R.towerEnumTail ctx hescV2 hge haper with
    | inl ho => exact towerTail_of_order_gt ctx ho.1 ho.2
    | inr hineq => exact hineq

/-- The V3 tower count of the budget (verbatim walk). -/
def towerCountV3 (R : Erdos260EndgameResidual) :
    ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx :=
  p9V3TowerCount_ofShallowDeep
    (towerDeepResidual_ofCountBound (towerCountBound_of_modulusEnumeration R.towerEnum))

/-! ### The run lane (verbatim wave-16 split walk) -/

/-- Run lane — the wave-5 settlement hypothesis: the band-4-free conjunct fields with
their guards discharged by the voiding field (the wave-16 walk verbatim). -/
def runNumeric (R : Erdos260EndgameResidual) : RunCycleNumericSettlementHyp := by
  intro ctx _hr
  have hnp : ¬ OrbitBandPinned ctx 4 := R.runBand4Void ctx
  rcases Nat.lt_or_ge (class1SlopeDatum ctx).q 64 with hlt | hge
  · exact R.runNumericLow ctx hnp hlt
  · by_cases h93 : (class1SlopeDatum ctx).q = 93 ∧ (class1SlopeDatum ctx).K₀ = 15
    · exact Or.inr (ftRunCloses_of_datum_93_15 ctx h93.1 h93.2)
    · cases R.runNumericTail ctx hnp hge h93 with
      | inl ho => exact Or.inr (runTail_of_order_gt ctx ho.1 ho.2)
      | inr hrun => exact hrun

/-- The Run max-core family of the budget (verbatim walk). -/
def runCore (R : Erdos260EndgameResidual) :
    ∀ ctx : ActualFailureContext, RunClass5LeafSupportMaxCoreResidual ctx :=
  fun ctx => (runSplitOfNumeric (runCycleNumericField_settled R.runNumeric) ctx).toCore

/-- The V3 run chain of the budget (verbatim walk). -/
def runChain (R : Erdos260EndgameResidual) :
    ∀ ctx : ActualFailureContext, RunClass5StageChain ctx :=
  p9V3RunChainOfResidual (runClass5LeafResidual_ofSupportMaxCoreResidual R.runCore)

/-! ### The Return lane (the wave-16 walk through the reassembled gates field) -/

/-- The wave-3 4-way gate disjunction from the reassembled gates field (verbatim
wave-16 walk, with the field rebuilt through the over-transcription #5 split). -/
def returnGatesCycle (R : Erdos260EndgameResidual) :
    ∀ ctx : ActualFailureContext, ReturnGatesBody ctx := fun ctx => by
  by_cases hfree : ReturnB2FreeDatum ctx
  · exact (returnCtxAllFour_of_b2FreeDatum ctx hfree).1
  · by_cases hone : ReturnB2OneSpacedDatum ctx
    · exact (returnGatesZeroCard_of_b2OneSpacedDatum ctx hone).1
    · by_cases hnum : 64 * (((supportShell ctx.shell.d ctx.shell.X).card
            + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
          < 2 * (129 * shellLadderDepth ctx + 64)
      · exact returnGatesBody_of_reach_numeric ctx hnum
      · exact (returnGatesBody_iff_ungated ctx).mpr
          (R.returnGatesField ctx hfree hone (not_lt.mp hnum))

/-- The class-4 population bound `|olcFibre| ≤ r + 1` from the gates. -/
theorem fibreSmall (R : Erdos260EndgameResidual) : Class4FibreSmall :=
  class4FibreSmall_of_gates R.returnGatesCycle

/-- The per-ctx K.1 interior (verbatim walk). -/
def interiorAt (R : Erdos260EndgameResidual) (ctx : ActualFailureContext) :
    ReturnInteriorBody ctx := by
  by_cases hfree : ReturnB2FreeDatum ctx
  · exact (returnCtxAllFour_of_b2FreeDatum ctx hfree).2.2.2
  · exact R.returnInterior ctx hfree

/-- The Return slot — the wave-15a unconditional charge from the counts alone. -/
def returnCharge (R : Erdos260EndgameResidual) :
    ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx :=
  fun ctx => Class4ReturnPerSliceCharge.ofCountsOnly ctx (R.interiorAt ctx) (R.fibreSmall ctx)

/-! ### The genuine-routed budget -/

/-- **The endgame budget** — `v3Budget` over the genuine route, rebuilt from the
wave-17 fields (identical in shape to the wave-16 corrected budget). -/
def budget (R : Erdos260EndgameResidual) :
    ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx :=
  v3Budget R.towerCountV3 R.runChain R.returnCharge

/-! ### The class-0 row: absorption at survivors, in-tree closure elsewhere -/

/-- **The corrected class-0 count-cap at EVERY context**: at the 19 survivor pairs from
the absorption field directly (the de-razored demand); at non-survivor `q < 48` from
the in-tree closure (`class0Pinned_of_datum_not_survivor`); on `48 ≤ q` from the
mid-band/big-order emptiness lanes through the wave-5 band split
(`class0WindowCycleCheck_of_band5_split`). -/
theorem hcap0 (R : Erdos260EndgameResidual) (ctx : ActualFailureContext) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card : ℝ)
        * runDyadicMult ctx
      ≤ termChernoff (correctedAllPhases ctx).toClosurePhaseData := by
  rcases Nat.lt_or_ge (class1SlopeDatum ctx).q 48 with h48 | h48
  · by_cases hs : Class0DatumSurvivor ctx
    · have h := (R.class0Absorption ctx).1 hs
      rw [termChernoff_correctedAll_eq, ← div_mul_eq_mul_div]
      exact h
    · have hpin := class0Pinned_of_datum_not_survivor ctx h48 hs
      have hcheck := (class0Pinned_iff_windowCycleCheck ctx).mp hpin
      exact tfaClass0Absorption_of_fibreEmpty ctx
        ((ofcClass0Fibre_empty_iff_windowCycleCheck ctx).mpr hcheck)
  · have hcheck : Class0WindowCycleCheck ctx := by
      refine class0WindowCycleCheck_of_band5_split ctx ?_ ?_ h48
      · intro h48' h96 hmeet
        exact (ofcClass0Fibre_empty_iff_windowCycleCheck ctx).mp
          ((R.class0Absorption ctx).2.1 h48' h96 hmeet)
      · intro h96
        cases (R.class0Absorption ctx).2.2 h96 with
        | inl hcert =>
            obtain ⟨C, horder, hcheck'⟩ := hcert
            exact class0Tail_of_order_gt ctx C horder hcheck'
        | inr hempty => exact (ofcClass0Fibre_empty_iff_windowCycleCheck ctx).mp hempty
    exact tfaClass0Absorption_of_fibreEmpty ctx
      ((ofcClass0Fibre_empty_iff_windowCycleCheck ctx).mpr hcheck)

/-! ### The class-1 row: the 110-pair dispatcher + the regime-folded field -/

/-- **The corrected class-1 count-cap at EVERY context**: `r = 0` shells close FREE;
contexts covered by a `SurvivorRegimeEnumeration` table row in regime (`L ≤ T`) close
through the aggregate dispatcher (`sreClass1Absorption_of_mem`); everything else from
the regime-folded surface field. -/
theorem hcap1 (R : Erdos260EndgameResidual) (ctx : ActualFailureContext) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ termCnl (correctedAllPhases ctx).toClosurePhaseData := by
  rw [termCnl_correctedAll_eq, ← div_mul_eq_mul_div]
  rcases Nat.eq_zero_or_pos ctx.n24CarryData.r with hr0 | hr1
  · have hcard : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card ≤ 1 :=
      class1Fibre_card_le_one_of_r_eq_zero ctx hr0
    have hcardR : ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        ≤ 1 := by exact_mod_cast hcard
    have hY0 : (0 : ℝ) ≤ ctx.n24CarryData.Y := le_of_lt (n24CarryData_Y_pos ctx)
    have hYlt : ctx.n24CarryData.Y
        < erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
      have h := Y_lt_termCnl_corrected R.budget ctx
      rwa [termCnl_corrected_eq R.budget ctx] at h
    calc ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
          * ctx.n24CarryData.Y
        ≤ 1 * ctx.n24CarryData.Y := mul_le_mul_of_nonneg_right hcardR hY0
      _ = ctx.n24CarryData.Y := one_mul _
      _ ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) :=
          le_of_lt hYlt
  · by_cases hreg : ∃ cv bv Tv : ℕ,
        ((class1SlopeDatum ctx).q, (class1SlopeDatum ctx).K₀, cv, bv, Tv)
            ∈ sreClass1ThresholdTable
          ∧ shellLadderDepth ctx ≤ Tv
    · obtain ⟨cv, bv, Tv, hmem, hL⟩ := hreg
      exact sreClass1Absorption_of_mem ctx hmem rfl rfl hL
    · exact R.class1CapAbsorption ctx hr1 hreg

/-! ### The class-3 row: the rebuilt cover residual through the domination -/

/-- The corrected DensePack residue at the endgame budget (the wave-16 walk over the
rebuilt collapsed residual). -/
def densePackCorrected (R : Erdos260EndgameResidual) :
    DensePackCorrectedResidue R.budget :=
  (R.densePackUngated.toGatedClosure.toDatumSplit.toCycleSplit.toRegimeSplit R.budget).toCorrected

/-- **The corrected class-3 ledger row at EVERY context**: the rebuilt cover residual
closes the frozen (marker-count) row, and the frozen term is dominated by the
fully-corrected one (`tfaDensePack_frozen_le_correctedAll`). -/
theorem hDensePackAll (R : Erdos260EndgameResidual) (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (R.budget ctx).route 3
      ≤ termDensePack (correctedAllPhases ctx).toClosurePhaseData :=
  le_trans (R.densePackCorrected.hDensePackField (fun _ => rfl) ctx)
    (tfaDensePack_frozen_le_correctedAll R.budget ctx)

/-! ### The fully-corrected ledger assembly and the endpoint -/

/-- **The fully-corrected ctx-pinned P9 ledger from the wave-17 surface**: classes
0/1 from the absorption rows above, class 3 through the frozen→corrected domination,
the TRT row from the budget slots themselves (the corrected caps EQUAL the slot caps),
and class 6 from the genuine route's vacancy. -/
def toFullyCorrectedLedger (R : Erdos260EndgameResidual) :
    FullyCorrectedP9LedgerResidual where
  budget := R.budget
  hChernoff := fun ctx => by
    show routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 0
        ≤ termChernoff (correctedAllPhases ctx).toClosurePhaseData
    exact le_trans (tfaMass_le_card_mul_mult ctx (genuineChargeRoute ctx) 0) (R.hcap0 ctx)
  hCnl := fun ctx => by
    show routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 1
        ≤ termCnl (correctedAllPhases ctx).toClosurePhaseData
    rw [routedClassMass_one_eq_card_mul_Y]
    exact R.hcap1 ctx
  hDensePack := fun ctx => R.hDensePackAll ctx
  hTRT := fun ctx => by
    rw [termTower_correctedAll_eq, termReturn_correctedAll_eq, termRun_correctedAll_eq]
    have h2 := (R.budget ctx).towerSlot
    have h4 := (R.budget ctx).returnSlot
    have h5 := (R.budget ctx).runSlot
    linarith
  hOldRes := fun ctx => by
    show routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 6 ≤ 0
    exact le_of_eq (genuineChargeRoute_routed6_zero ctx)

/-- The final statement from the wave-17 surface, through the fully-corrected ledger
bridge.  Composition only. -/
theorem toStatement (R : Erdos260EndgameResidual) : Erdos260Statement :=
  R.toFullyCorrectedLedger.toStatement

end Erdos260EndgameResidual

/-- **THE WAVE-17 ENDPOINT**: `Erdos260Statement` from the folded 14-field surface —
the Return/DensePack count gates demanded only on orbit-pin-free contexts (the
over-transcription #5/#6 splits), the class-0 emptiness razor replaced by survivor
count-cap absorption, the class-1 absorption relieved at all 110 certified table pairs
in regime, all routed through the FULLY-corrected six-phase ledger
(`FullyCorrectedP9LedgerResidual`).  Public bridges only. -/
theorem erdos260_of_endgameResidual (R : Erdos260EndgameResidual) :
    Erdos260Statement :=
  R.toStatement

/-! ## Part 2.  The weakening witness: wave 16 → wave 17 (never harder) -/

/-- **The weakening witness**: every wave-16 corrected-surface inhabitant yields a
wave-17 endgame inhabitant.  Tower/run/return-interior/densepack-density/interior
transport verbatim; the four split conjuncts are EXTRACTED from the wave-16 count
fields (the mp directions of the two over-transcription splits); survivor emptiness
yields the class-0 absorption for free (`tfaClass0Absorption_of_fibreEmpty`); the
class-1 field drops its new regime guard.  One direction only; NO converse is
claimed (the converse direction is exactly the wave-17 relief). -/
def endgameResidual_of_correctedResidual (R : Erdos260CorrectedResidual) :
    Erdos260EndgameResidual where
  towerEnumLow := R.towerEnumLow
  towerEnumTail := R.towerEnumTail
  runBand4Void := R.runBand4Void
  runNumericLow := R.runNumericLow
  runNumericTail := R.runNumericTail
  returnBand2Void := (returnGatesField_iff_band2Void_split.mp R.returnGates).1
  returnGatesFree := (returnGatesField_iff_band2Void_split.mp R.returnGates).2
  returnInterior := R.returnInterior
  densePackBand3Void :=
    (densePackCoverField_iff_band3Void_split.mp R.densePackUngated.ungatedCoverNat).1
  densePackCoverFree :=
    (densePackCoverField_iff_band3Void_split.mp R.densePackUngated.ungatedCoverNat).2
  densePackDensity := R.densePackUngated.ungatedDensity
  densePackInterior := R.densePackUngated.ungatedInterior
  class0Absorption := fun ctx =>
    ⟨fun hsurv => by
        have h := tfaClass0Absorption_of_fibreEmpty ctx ((R.class0Fibre ctx).1 hsurv)
        rw [termChernoff_correctedAll_eq] at h
        rw [div_mul_eq_mul_div]
        exact h,
      (R.class0Fibre ctx).2.1, (R.class0Fibre ctx).2.2⟩
  class1CapAbsorption := fun ctx hr _ => R.class1CapAbsorption ctx hr

/-- Nonempty transport from the wave-16 corrected surface (one direction — honest). -/
theorem nonempty_endgameResidual_of_correctedResidual
    (h : Nonempty Erdos260CorrectedResidual) :
    Nonempty Erdos260EndgameResidual :=
  h.elim fun R => ⟨endgameResidual_of_correctedResidual R⟩

/-- Sanity commutation: the wave-16 surface reaches the statement through the wave-17
endgame route as well. -/
theorem erdos260_of_correctedResidual_via_endgame (R : Erdos260CorrectedResidual) :
    Erdos260Statement :=
  (endgameResidual_of_correctedResidual R).toStatement

/-! ## Part 3.  The three-voidings synthesis: the fixed-family axis from the
voiding fields ALONE -/

/-- **The three orbit-pin voidings void every fixed-family hit at every context** — no
count field is consumed: `(3,1)` pins band 2 (`orbitBandPinned_3_1`), `(21,3)` pins
band 3 inside the cover window (`orbitBandPinned_21_3`, `q = 21 ≥ 13`), and the band-4
trio pins band 4. -/
theorem endgame_threeVoidings_fixedFamilyVoid
    (h2 : ∀ ctx : ActualFailureContext, ¬ OrbitBandPinned ctx 2)
    (h3 : ∀ ctx : ActualFailureContext, ¬ Band3PinnedWide ctx)
    (h4 : ∀ ctx : ActualFailureContext, ¬ OrbitBandPinned ctx 4)
    (ctx : ActualFailureContext) : ¬ FixedFamilyHit ctx := by
  rintro (hd | hd | hd | hd | hd)
  · exact h2 ctx (orbitBandPinned_3_1 ctx hd)
  · exact h3 ctx ⟨orbitBandPinned_21_3 ctx hd, Or.inr (by rw [hd.1]; norm_num)⟩
  · exact h4 ctx (orbitBandPinned_15_1 ctx hd)
  · exact h4 ctx (orbitBandPinned_15_2 ctx hd)
  · exact h4 ctx (orbitBandPinned_105_7 ctx hd)

/-- **THE THREE-VOIDINGS SYNTHESIS**: the residual's three orbit-pin voiding fields
imply the deep fixed-family voiding — the whole `FixedFamilyShellPersistence` axis is
carried by `returnBand2Void` + `densePackBand3Void` + `runBand4Void` alone (sharper
than the wave-17 lane-1 consumption, which routed through the full count fields). -/
theorem endgame_threeVoidings_deepFixedFamilyVoid
    (h2 : ∀ ctx : ActualFailureContext, ¬ OrbitBandPinned ctx 2)
    (h3 : ∀ ctx : ActualFailureContext, ¬ Band3PinnedWide ctx)
    (h4 : ∀ ctx : ActualFailureContext, ¬ OrbitBandPinned ctx 4) :
    DeepFixedFamilyVoid :=
  fun ctx _ => endgame_threeVoidings_fixedFamilyVoid h2 h3 h4 ctx

/-- Every endgame inhabitant voids all five fixed families outright. -/
theorem endgameResidual_not_fixedFamilyHit (R : Erdos260EndgameResidual)
    (ctx : ActualFailureContext) : ¬ FixedFamilyHit ctx :=
  endgame_threeVoidings_fixedFamilyVoid
    R.returnBand2Void R.densePackBand3Void R.runBand4Void ctx

/-- The endgame surface supplies the deep family voiding (through the voiding fields
alone). -/
theorem endgameResidual_deepFixedFamilyVoid (R : Erdos260EndgameResidual) :
    DeepFixedFamilyVoid := fun ctx _ =>
  endgameResidual_not_fixedFamilyHit R ctx

/-- The `FixedFamilyShellPersistence` axis stays ABSORBED on the wave-17 surface: the
deep shell-persistence supply holds vacuously from the three voiding fields. -/
theorem endgameResidual_deepShellPersistence (R : Erdos260EndgameResidual) :
    DeepFixedFamilyShellPersistence := fun ctx _ hhit =>
  absurd hhit (endgameResidual_not_fixedFamilyHit R ctx)

/-! ## Part 4.  Run-lane consumers of the corrected term (wave-17 lane 2) -/

/-- The corrected run ledger row closes from the count×multiplier gate over the
endgame budget (`tfaCorrectedHRun_of_gate` consumed at the wave-17 surface; the row is
NOT needed for `toStatement` — the TRT row closes from the budget slots — but the gate
form is the honest band-4-free demand shape). -/
theorem endgameResidual_runRow_of_gate (R : Erdos260EndgameResidual)
    (ctx : ActualFailureContext)
    (hgate : ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card : ℝ)
          * runDyadicMult ctx
        ≤ termRun (correctedAllPhases ctx).toClosurePhaseData) :
    routedClassMassOf ctx.n24CarryData (R.budget ctx).route 5
      ≤ termRun (correctedAllPhases ctx).toClosurePhaseData :=
  tfaCorrectedHRun_of_gate R.budget ctx rfl hgate

/-- **The band-4 voiding is FORCED by the endgame surface's own budget**
(`tfaBand4_no_genuine_budget`): at any band-4-pinned context the genuine-routed budget
rebuilt from the wave-17 fields cannot exist — the corrected reading (route band-4
data through L.3/M.5) is not optional. -/
theorem endgameResidual_band4_forced (R : Erdos260EndgameResidual)
    (ctx : ActualFailureContext) (hpin : OrbitBandPinned ctx 4) : False :=
  tfaBand4_no_genuine_budget ctx hpin (R.budget ctx) rfl

/-! ## Part 5.  Honest machine-readable status -/

/-- Machine-readable, honest status of the wave-17 endgame capstone. -/
def erdos260EndgameCapstoneStatus : List String :=
  [ "SURFACE (14 fields): Erdos260EndgameResidual = the wave-16 corrected surface " ++
      "rebased on the three wave-17 lanes.  NEW vs wave 16: returnBand2Void + " ++
      "densePackBand3Void join runBand4Void as NAMED orbit-pin voiding fields " ++
      "(over-transcriptions #5/#6 - the wave-16 returnGates/ungatedCoverNat fields " ++
      "provably CONTAINED these conjuncts); the count gates are now demanded only " ++
      "on pin-free contexts (returnGatesFree / densePackCoverFree = the second " ++
      "conjuncts of the two splits); class0Absorption replaces the survivor " ++
      "emptiness razor by count-cap absorption; class1CapAbsorption is demanded " ++
      "only at off-table data or L > T (the 110 certified pairs in regime are FREE).",
    "ENDPOINT (PROVED): erdos260_of_endgameResidual : Erdos260EndgameResidual -> " ++
      "Erdos260Statement, through FullyCorrectedP9LedgerResidual.toStatement - the " ++
      "FIRST endpoint consuming the fully-corrected six-phase ledger " ++
      "(correctedAllPhases, all six caps (31/1536)*X, total (31/256)*X < X/2).  " ++
      "Class 0: survivor absorption field + in-tree non-survivor closure " ++
      "(class0Pinned_of_datum_not_survivor) + the wave-16 mid/big lanes through " ++
      "class0WindowCycleCheck_of_band5_split.  Class 1: r = 0 free, table pairs in " ++
      "regime free (sreClass1Absorption_of_mem dispatcher over all 110 rows), the " ++
      "field only elsewhere.  Class 3: the rebuilt cover residual through " ++
      "tfaDensePack_frozen_le_correctedAll.  TRT: the budget slots themselves.  " ++
      "Class 6: genuineChargeRoute_routed6_zero.",
    "FIELDS CHEAPER THAN WAVE 16 (all proved, endgameResidual_of_correctedResidual " ++
      "= the formal weakening witness): (a) returnGates -> returnBand2Void + " ++
      "returnGatesFree (equal total strength by the split iff, but the voiding is " ++
      "now NAMED and the count gate fires only on band-2-free ctx); (b) " ++
      "ungatedCoverNat -> densePackBand3Void + densePackCoverFree (same, band 3 " ++
      "wide); (c) class0Fibre survivor lane: emptiness -> absorption " ++
      "(STRICTLY weaker - tfaClass0Absorption_of_fibreEmpty gives the old->new " ++
      "direction; the converse needs only the numeric gate " ++
      "1536*ceil(W/c)*(r+1)(L+B+1) <= 31*X, tfaClass0SurvivorAbsorption); (d) " ++
      "class1CapAbsorption: now guarded by the 110-pair regime dispatcher " ++
      "(STRICTLY weaker - every table pair with L <= T is relieved outright).  " ++
      "UNCHANGED: towerEnumLow/Tail, runBand4Void + runNumericLow/Tail, " ++
      "returnInterior, densePackDensity/Interior, class0 mid/big lanes.",
    "FOLDS SKIPPED (honest): returnInterior is kept at the wave-16 shape rather " ++
      "than the band-2 top-band-light demand form " ++
      "(band2_returnInterior_iff_topBand_light) - the equivalence holds only AT " ++
      "the pin, and the surface now carries returnBand2Void, so the pinned form " ++
      "would be vacuous on the surface's own contexts; same for densePackInterior " ++
      "vs band3_densePackInterior_iff_topBand_light.  The class-0 mid/big lanes " ++
      "keep emptiness language: no razor was found there (emptiness IS the " ++
      "windowed check, ofcClass0Fibre_empty_iff_windowCycleCheck) and no " ++
      "absorption-only closure exists in-tree.",
    "THREE-VOIDINGS SYNTHESIS (PROVED): endgame_threeVoidings_deepFixedFamilyVoid " ++
      "- the three voiding FIELDS alone (bands 2/3-wide/4) imply " ++
      "DeepFixedFamilyVoid; endgameResidual_deepShellPersistence keeps the " ++
      "FixedFamilyShellPersistence axis ABSORBED.  Sharper than wave-17 lane 1 " ++
      "(correctedResidual_not_fixedFamilyHit), which consumed the full count " ++
      "fields: here the count gates contribute NOTHING to the fixed-family axis - " ++
      "the axis sits entirely in the three voiding conjuncts.",
    "RUN LANE (lane-2 consumption): endgameResidual_runRow_of_gate consumes " ++
      "tfaCorrectedHRun_of_gate over the endgame budget (the honest band-4-free " ++
      "gate shape; not needed for toStatement - the TRT row closes from the " ++
      "slots).  endgameResidual_band4_forced re-derives the band-4 voiding from " ++
      "the surface's own budget via tfaBand4_no_genuine_budget: the voiding " ++
      "reading is forced, not chosen.",
    "WHAT REMAINS OPEN AFTER WAVE 17 (the honest core): (a) the THREE orbit-pin " ++
      "voidings - returnBand2Void (kills (3,1)), densePackBand3Void (kills " ++
      "(21,3)), runBand4Void (kills the band-4 trio) - each carrying the proved " ++
      "constraint package: value pin ShellValueDyadic (1/2^t), scale floor X > " ++
      "2^986893, long-gap profile (twoData_* / band4 analogues); (b) the pin-free " ++
      "count gates returnGatesFree / densePackCoverFree + returnInterior / " ++
      "densePackDensity / densePackInterior; (c) the class-0 absorption gates at " ++
      "the 19 survivor pairs (genuine narrow-support conditions, W <= " ++
      "~c*X/(50*runDyadicMult); L >= 986876, r >= 63 there) and the mid/big " ++
      "emptiness lanes; (d) the class-1 deep-shell residual L > T at each of the " ++
      "110 pairs (T in [1233618, 17887472] at the live pairs) plus off-table data " ++
      "(200 <= q tails); (e) towerEnumLow/Tail and runNumericLow/Tail (the " ++
      "enumerated/tail tower and run lanes).",
    "HYGIENE: additive only - ONE new module; no sorry / admit / new axiom / " ++
      "native_decide; every key declaration passes #print axioms within [propext, " ++
      "Classical.choice, Quot.sound]." ]

/-- The status ledger is non-empty (honest, non-vacuous). -/
theorem erdos260EndgameCapstoneStatus_nonempty :
    erdos260EndgameCapstoneStatus ≠ [] := by
  simp [erdos260EndgameCapstoneStatus]

/-! ## Part 6.  Axiom-cleanliness audit
Every key declaration; expected axioms `[propext, Classical.choice, Quot.sound]` or
fewer. -/

#print axioms Erdos260EndgameResidual.returnGatesField
#print axioms Erdos260EndgameResidual.densePackCoverField
#print axioms Erdos260EndgameResidual.densePackUngated
#print axioms Erdos260EndgameResidual.towerEnum
#print axioms Erdos260EndgameResidual.towerCountV3
#print axioms Erdos260EndgameResidual.runNumeric
#print axioms Erdos260EndgameResidual.runCore
#print axioms Erdos260EndgameResidual.runChain
#print axioms Erdos260EndgameResidual.returnGatesCycle
#print axioms Erdos260EndgameResidual.fibreSmall
#print axioms Erdos260EndgameResidual.interiorAt
#print axioms Erdos260EndgameResidual.returnCharge
#print axioms Erdos260EndgameResidual.budget
#print axioms Erdos260EndgameResidual.hcap0
#print axioms Erdos260EndgameResidual.hcap1
#print axioms Erdos260EndgameResidual.densePackCorrected
#print axioms Erdos260EndgameResidual.hDensePackAll
#print axioms Erdos260EndgameResidual.toFullyCorrectedLedger
#print axioms Erdos260EndgameResidual.toStatement
#print axioms erdos260_of_endgameResidual
#print axioms endgameResidual_of_correctedResidual
#print axioms nonempty_endgameResidual_of_correctedResidual
#print axioms erdos260_of_correctedResidual_via_endgame
#print axioms endgame_threeVoidings_fixedFamilyVoid
#print axioms endgame_threeVoidings_deepFixedFamilyVoid
#print axioms endgameResidual_not_fixedFamilyHit
#print axioms endgameResidual_deepFixedFamilyVoid
#print axioms endgameResidual_deepShellPersistence
#print axioms endgameResidual_runRow_of_gate
#print axioms endgameResidual_band4_forced
#print axioms erdos260EndgameCapstoneStatus_nonempty

end

end Erdos260
