import Erdos260.AnchoredKeyCount
import Erdos260.FiniteTailsSweep
import Erdos260.SCCPersistence
import Erdos260.Erdos260OnsetCapstone

/-!
# The anchored capstone — the wave-15 fold (`Erdos260AnchoredCapstone`)

This module (NEW; it edits no existing file) folds the wave-15 deliverables —
`AnchoredKeyCount` (the junction collapse: the Return lane CLOSED unconditionally),
`FiniteTailsSweep` (the fourteen b2-heavy joint conflicts, the class-1 sweep to `q < 200`,
the run/densepack band sweeps), and `SCCPersistence` (the pressure relocation, the second
bootstrap-free voiding, the widened shell-persistence supply atom) — into a single successor
surface above `Erdos260AnchoredCountResidual`.

## The fold verdict (honest — read this first)

* **The base is the Return-closed surface**: `AnchoredKeyCount` proved
  `erdos260_of_anchoredCount : Erdos260AnchoredCountResidual → Erdos260Statement` with the
  `returnDirtyEnvelope` field DELETED — the Return lane is carried by `returnGates` +
  `returnInterior` alone.  This module's surface keeps that skeleton (12 fields) and folds
  the other two wave-15 modules onto four of the fields.
* **What genuinely folds (four lanes weakened)**:
  1. *Tower*: `towerEnumLow` is RELIEVED at the two band-pinned fixed data `(3,1)` and
     `(21,3)` — there `Class2CycleInequality` is FREE (the orbit is constant at a non-band-4
     fixed point, so the period-1 cycle has band-4 count 0:
     `anchoredCapstone_class2Ineq_of_datum_3_1` / `_21_3`, from `SCCPersistence`'s pin data).
  2. *Run*: `runNumericTail` is RELIEVED of `(93,15)` — the unique mid-band run closure of
     the sweep (`ftRunCloses_of_datum_93_15`).
  3. *Class 0*: the survivor field DECOMPOSES along the wave-14 b2 cross/heavy split — at
     the FOURTEEN b2-heavy pairs only the OFF-FIBRE residue miss is demanded
     (`ftClass0ResidueMiss_of_offFibre`: the on-fibre part is free by the fourteen proved
     joint-congruence conflicts); at the five crossed pairs the verbatim miss remains.
  4. *Class 1*: the deep threshold moves `101 → 200` — the low field is relieved of the
     eight closed moduli (`ftClass1ClosedModuli200`) and the 49 band-4-free pairs
     (`FtClass1Band4FreeDatum`), and gains the FREE guards `1 ≤ r` and the aperiodicity
     lever; the tail field keeps the verbatim disjunction shape at `200 ≤ q`.
* **What did NOT fold (honest)**:
  * *DensePack*: the nineteen band-3-free closures compose as GUARD DISCHARGE, not as a
    field change — `DensePackUngatedClosureResidual`'s fields carry `¬ Class3CycleBand3Free`
    as their first guard, which FAILS at the nineteen pairs
    (`anchoredCapstone_class3Band3Free_of_band3FreeDatum`); the field stays verbatim.  The
    `ftDensePackStartsEmpty_split_at_128` dispatcher is an ALTERNATIVE route shape
    (emptiness demands), incomparable to the structured residual — recorded, not folded.
  * *Tower tail*: at the five fixed data the `towerEnumTail` demand NEVER fires
    (`q ≤ 105 < 107` — vacuous by threshold), and the pressure relocation does NOT relieve
    the genuine `107 ≤ q` tail: under the band-4 pin classes 0/3/4/6 are empty but class 2
    remains populated (the `cnlTail` branch routes by window excess), and the relocation
    starves class-2 MASS (`scc_class12_deficit`) while `Class2CycleInequality` is a COUNT
    bound — mass starvation supplies no count bound.  The class-2 escape demand at the
    three band-4 fixed data `(15,1) (15,2) (105,7)` (where `TowerModulusEnumEscapeV2` fires
    by enumeration) REMAINS in `towerEnumLow` — the brief's hoped-for vacuity is REVERSED
    into relief at the band-2/3 data only.
  * *SCC*: no capstone field is a fixed-family demand, so the shell-persistence atom and
    the pressure voidings enter as named conditional routes (re-exported below), not as
    field changes.

## DIRECTION OF STRENGTH (honest)

`Erdos260ReturnChargeResidual → Erdos260AnchoredCountResidual` (field deletion, wave 15a)
`→ Erdos260AnchoredResidual` (`anchoredResidual_of_anchoredCount`, this module) — each step
one-directional downward; NO converse is claimed (the relieved guards cannot be
un-relieved; the off-fibre restriction and the moved thresholds demand strictly less).
The endpoint `erdos260_of_anchoredResidual` replays the public per-lane ledger walk of
`AnchoredKeyCount` with the four folded lanes dispatched through the sweep closures.

No `sorry`, no `admit`, no new `axiom`, no `native_decide`; additive only — no existing
module is edited (the root import file gains one line; the three wave-15 modules enter the
root closure through this module's imports).
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 1.  The SCC fold lemmas: the cycle inequality is free at the band-2/3 pins -/

/-- **`(3,1)` closes the class-2 cycle inequality outright**: the orbit is constant at the
band-2 fixed point `1` (`slopeOrbit_three_one_const`), so the period-1 cycle has band-4
count `0` and the count bound is `0 ≤ W`. -/
theorem anchoredCapstone_class2Ineq_of_datum_3_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 3) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    Class2CycleInequality ctx := by
  have hcount : towerBand4CycleCount 3 1 1 = 0 := by
    unfold towerBand4CycleCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hj1 : j = 1 := by omega
    subst hj1
    rw [slopeOrbit_three_one_const 1, fixedCycleGap_3_1]
    norm_num
  refine ⟨1, le_rfl, ?_, ?_⟩
  · intro m _
    rw [hq, hK, slopeOrbit_three_one_const (m + 1), slopeOrbit_three_one_const m]
  · rw [hq, hK, hcount]
    simp

/-- **`(21,3)` closes the class-2 cycle inequality outright**: the orbit is constant at the
band-3 fixed point `3` (`slopeOrbit_twentyone_three_const`), so the period-1 cycle has
band-4 count `0`. -/
theorem anchoredCapstone_class2Ineq_of_datum_21_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 21) (hK : (class1SlopeDatum ctx).K₀ = 3) :
    Class2CycleInequality ctx := by
  have hcount : towerBand4CycleCount 21 3 1 = 0 := by
    unfold towerBand4CycleCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hj1 : j = 1 := by omega
    subst hj1
    rw [slopeOrbit_twentyone_three_const 1, fixedCycleGap_21_3]
    norm_num
  refine ⟨1, le_rfl, ?_, ?_⟩
  · intro m _
    rw [hq, hK, slopeOrbit_twentyone_three_const (m + 1), slopeOrbit_twentyone_three_const m]
  · rw [hq, hK, hcount]
    simp

/-! ## Part 2.  The densepack guard discharge (recorded, not folded) -/

/-- **The nineteen swept pairs discharge the densepack residual's first guard**: at every
`FtDensePackBand3FreeDatum` pair the cycle check `Class3CycleBand3Free` HOLDS, so the
`DensePackUngatedClosureResidual` fields (guarded on its negation) demand nothing there —
exactly the closures the capstone's class-3 walk already applies. -/
theorem anchoredCapstone_class3Band3Free_of_band3FreeDatum (ctx : ActualFailureContext)
    (h : FtDensePackBand3FreeDatum ctx) : Class3CycleBand3Free ctx := by
  rcases h with ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩
  · exact ftClass3Band3Free_of_datum_65_2 ctx hq hK
  · exact ftClass3Band3Free_of_datum_65_6 ctx hq hK
  · exact ftClass3Band3Free_of_datum_65_32 ctx hq hK
  · exact ftClass3Band3Free_of_datum_73_36 ctx hq hK
  · exact ftClass3Band3Free_of_datum_75_12 ctx hq hK
  · exact ftClass3Band3Free_of_datum_85_2 ctx hq hK
  · exact ftClass3Band3Free_of_datum_85_8 ctx hq hK
  · exact ftClass3Band3Free_of_datum_89_44 ctx hq hK
  · exact ftClass3Band3Free_of_datum_91_3 ctx hq hK
  · exact ftClass3Band3Free_of_datum_91_6 ctx hq hK
  · exact ftClass3Band3Free_of_datum_93_1 ctx hq hK
  · exact ftClass3Band3Free_of_datum_97_48 ctx hq hK
  · exact ftClass3Band3Free_of_datum_105_3 ctx hq hK
  · exact ftClass3Band3Free_of_datum_105_7 ctx hq hK
  · exact ftClass3Band3Free_of_datum_105_10 ctx hq hK
  · exact ftClass3Band3Free_of_datum_105_52 ctx hq hK
  · exact ftClass3Band3Free_of_datum_117_1 ctx hq hK
  · exact ftClass3Band3Free_of_datum_117_4 ctx hq hK
  · exact ftClass3Band3Free_of_datum_127_63 ctx hq hK

/-! ## Part 3.  The heavy-conflict record at the capstone guard -/

/-- **The composed heavy conflict**: inside the capstone fields' first Return guard
(`¬ ReturnB2FreeDatum`), every class-0 survivor context puts EVERY class-4 fibre member off
the class-0 bad residue — the wave-14 reach lemma composed with the fourteen wave-15
joint-congruence conflicts. -/
theorem anchoredCapstone_heavyConflict_of_survivor (ctx : ActualFailureContext)
    (hsurv : Class0DatumSurvivor ctx) (hnb2 : ¬ ReturnB2FreeDatum ctx) :
    ∀ k ∈ olcFibre ctx,
      k % class0SurvivorPeriod (class1SlopeDatum ctx).q
        ≠ class0SurvivorDeepResidue (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ :=
  ftHeavyConflict_dispatch ctx (class0Survivor_heavy_of_not_b2Free ctx hsurv hnb2)

/-- Re-export (the exact decomposition): on a b2-heavy survivor pair the class-0 residue
miss IS its off-fibre restriction. -/
theorem anchoredCapstone_class0ResidueMiss_iff_offFibre (ctx : ActualFailureContext)
    (h : Class0SurvivorB2HeavyRest ctx) :
    Class0SurvivorResidueMiss ctx
      ↔ ∀ k ∈ ctx.n24CarryData.starts,
          129 * shellLadderDepth ctx + 64
              ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
          k ∉ olcFibre ctx →
          k % class0SurvivorPeriod (class1SlopeDatum ctx).q
            ≠ class0SurvivorDeepResidue (class1SlopeDatum ctx).q
                (class1SlopeDatum ctx).K₀ :=
  ftClass0ResidueMiss_iff_offFibre ctx h

/-! ## Part 4.  The successor surface (`Erdos260AnchoredResidual`)

`Erdos260AnchoredCountResidual` with four lanes folded: `towerEnumLow` relieved at
`(3,1)/(21,3)`, `runNumericTail` relieved of `(93,15)`, `class0Survivor` decomposed along
the cross/heavy split (off-fibre demand only at the fourteen heavy pairs), and the class-1
deep threshold moved `101 → 200` with the swept closures relieved.  12 fields. -/

/-- **The wave-15 anchored capstone surface**: the Return-closed 12-field skeleton of
`Erdos260AnchoredCountResidual` with the tower/run/class-0/class-1 lanes weakened by the
wave-15 sweeps and pins.  12 fields; `returnDirtyEnvelope` remains DELETED. -/
structure Erdos260AnchoredResidual where
  /-- Tower / class 2 - enumerated part (`q < 107`), RELIEVED at the band-pinned fixed data
  `(3,1)` and `(21,3)` (the cycle inequality is free there). -/
  towerEnumLow : ∀ ctx : ActualFailureContext,
    TowerModulusEnumEscapeV2 ctx → (class1SlopeDatum ctx).q < 107 →
    (ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx) →
    ¬ ((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1) →
    ¬ ((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3) →
    Class2CycleInequality ctx
  /-- Tower / class 2 - tail (`107 ≤ q`), with the free aperiodicity guard; verbatim field
  (the relocation supplies no count bound — honest). -/
  towerEnumTail : ∀ ctx : ActualFailureContext,
    TowerModulusEnumEscapeV2 ctx →
    107 ≤ (class1SlopeDatum ctx).q →
    (ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx) →
    (((Nat.log 2 (class1SlopeDatum ctx).q + 1) * shellWidth ctx
        < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
            (class1SlopeDatum ctx).K₀)))
        ∧ TowerBand4Budget ctx)
      ∨ Class2CycleInequality ctx
  /-- Run / class 5 - enumerated part (`q < 64`); verbatim field. -/
  runNumericLow : ∀ ctx : ActualFailureContext,
    (class1SlopeDatum ctx).q < 64 →
    Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx
  /-- Run / class 5 - tail (`64 ≤ q`), RELIEVED of the unique swept closure `(93,15)`. -/
  runNumericTail : ∀ ctx : ActualFailureContext,
    64 ≤ (class1SlopeDatum ctx).q →
    ¬ ((class1SlopeDatum ctx).q = 93 ∧ (class1SlopeDatum ctx).K₀ = 15) →
    ((Nat.log 2 (class1SlopeDatum ctx).q + 1)
        * (supportShell ctx.shell.d ctx.shell.X).card
      < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
          (class1SlopeDatum ctx).K₀)))
      ∧ RunBandBudget ctx
    ∨ Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx
  /-- Return / class 4 count gates - verbatim field (with `returnInterior` it carries the
  WHOLE Return lane — the wave-15a junction collapse). -/
  returnGates : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    2 * (129 * shellLadderDepth ctx + 64)
      ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
    ReturnGatesBodyUngated ctx
  /-- Return / class 4 K.1 interior - verbatim field. -/
  returnInterior : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx
  /-- Chernoff / class 0 survivors - DECOMPOSED along the b2 cross/heavy split: the
  verbatim residue miss at the five crossed pairs; at the FOURTEEN b2-heavy pairs only the
  OFF-FIBRE restriction (the on-fibre part is free by the proved joint conflicts). -/
  class0Survivor : ∀ ctx : ActualFailureContext, Class0DatumSurvivor ctx →
    (Class0SurvivorB2FreeCross ctx → Class0SurvivorResidueMiss ctx) ∧
    (Class0SurvivorB2HeavyRest ctx →
      ∀ k ∈ ctx.n24CarryData.starts,
        129 * shellLadderDepth ctx + 64
            ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
        k ∉ olcFibre ctx →
        k % class0SurvivorPeriod (class1SlopeDatum ctx).q
          ≠ class0SurvivorDeepResidue (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀)
  /-- Chernoff / class 0 mid band - verbatim field. -/
  class0Mid : ∀ ctx : ActualFailureContext, 48 ≤ (class1SlopeDatum ctx).q →
    (class1SlopeDatum ctx).q < 96 → Class0CycleMeetsShallow ctx →
    Class0WindowCycleCheck ctx
  /-- Chernoff / class 0 large moduli (`96 ≤ q`) - verbatim field. -/
  class0BigOrder : ∀ ctx : ActualFailureContext, 96 ≤ (class1SlopeDatum ctx).q →
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
    ∨ Class0WindowCycleCheck ctx
  /-- CNL / class 1 - deep part pushed to `q < 200`, RELIEVED of the eight closed moduli
  and the 49 band-4-free pairs, with the FREE guards `1 ≤ r` and the aperiodicity lever. -/
  class1DeepLow : ∀ ctx : ActualFailureContext,
    1 ≤ ctx.n24CarryData.r →
    64 ∣ shellLadderDepth ctx →
    9 ≤ (class1SlopeDatum ctx).q →
    ((class1SlopeDatum ctx).q ≤ 15 ∨ 25 ≤ (class1SlopeDatum ctx).q) →
    (class1SlopeDatum ctx).q ∉ class1ClosedModuli →
    ¬ Class1DatumClosed ctx →
    ¬ Class1GcdWindowMiss ctx →
    (class1SlopeDatum ctx).q ∉ ftClass1ClosedModuli200 →
    ¬ FtClass1Band4FreeDatum ctx →
    (class1SlopeDatum ctx).q < 200 →
    (ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx) →
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅
  /-- CNL / class 1 - tail (`200 ≤ q`); the verbatim disjunction shape at the moved
  threshold, with the free `1 ≤ r` guard. -/
  class1DeepTail : ∀ ctx : ActualFailureContext,
    1 ≤ ctx.n24CarryData.r →
    200 ≤ (class1SlopeDatum ctx).q →
    Class1Band4FreePeriod ctx
    ∨ (64 ∣ shellLadderDepth ctx →
        9 ≤ (class1SlopeDatum ctx).q →
        ((class1SlopeDatum ctx).q ≤ 15 ∨ 25 ≤ (class1SlopeDatum ctx).q) →
        (class1SlopeDatum ctx).q ∉ class1ClosedModuli →
        ¬ Class1DatumClosed ctx →
        ¬ Class1GcdWindowMiss ctx →
        routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅)
  /-- DensePack / class 3 - verbatim field (the nineteen swept closures discharge its first
  guard at their pairs; no field change is available — honest). -/
  densePackUngated : DensePackUngatedClosureResidual

namespace Erdos260AnchoredResidual

/-- Tower lane — the wave-5 enumeration residual: the anchored-count walk with the two
band-pinned fixed data dispatched through the free cycle inequalities. -/
def towerEnum (R : Erdos260AnchoredResidual) : TowerModulusEnumerationResidual := by
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

/-- Run lane — the wave-5 settlement hypothesis: the anchored-count walk with `(93,15)`
dispatched through the swept closure. -/
def runNumeric (R : Erdos260AnchoredResidual) : RunCycleNumericSettlementHyp := by
  intro ctx _hr
  rcases Nat.lt_or_ge (class1SlopeDatum ctx).q 64 with hlt | hge
  · exact R.runNumericLow ctx hlt
  · by_cases h93 : (class1SlopeDatum ctx).q = 93 ∧ (class1SlopeDatum ctx).K₀ = 15
    · exact Or.inr (ftRunCloses_of_datum_93_15 ctx h93.1 h93.2)
    · cases R.runNumericTail ctx hge h93 with
      | inl ho => exact Or.inr (runTail_of_order_gt ctx ho.1 ho.2)
      | inr hrun => exact hrun

/-- **The rebuilt verbatim survivor field**: residue miss at every survivor — the crossed
pairs from the surface's cross part, the heavy pairs from the off-fibre part through the
fourteen proved conflicts. -/
theorem class0SurvivorMiss (R : Erdos260AnchoredResidual) :
    ∀ ctx : ActualFailureContext, Class0DatumSurvivor ctx →
      Class0SurvivorResidueMiss ctx := fun ctx hsurv => by
  rcases class0Survivor_b2_split ctx hsurv with hcross | hheavy
  · exact (R.class0Survivor ctx hsurv).1 hcross
  · exact ftClass0ResidueMiss_of_offFibre ctx hheavy
      ((R.class0Survivor ctx hsurv).2 hheavy)

/-- Class-0 lane — the wave-3 windowed cycle check (the anchored-count walk over the
rebuilt survivor field). -/
def class0Cycle (R : Erdos260AnchoredResidual) :
    ∀ ctx : ActualFailureContext, Class0WindowCycleCheck ctx :=
  class0Cycle_of_survivor_residue_split R.class0SurvivorMiss R.class0Mid
    (fun ctx h96 => by
      cases R.class0BigOrder ctx h96 with
      | inl hcert =>
          obtain ⟨C, horder, hcheck⟩ := hcert
          exact class0Tail_of_order_gt ctx C horder hcheck
      | inr hwin => exact hwin)

/-- Class-1 lane — the wave-3 deep residual: the anchored-count walk with the swept
moduli/pairs dispatched and the threshold at `200`. -/
def class1Deep (R : Erdos260AnchoredResidual) : Class1DeepResidual :=
  class1DeepResidual_of_pairResidual (class1PairResidual_of_deepOnly
    (fun ctx hr hdvd h9 hwin hcl hdc hgcd => by
      have haper : ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx := fun hu7 hwp =>
        thirdsLever_windowPeriodic_void_of_oddpartQ_le_seven ctx hu7 hwp
      by_cases hext : (class1SlopeDatum ctx).q ∈ ftClass1ClosedModuli200
      · exact ftClass1Fibre_empty_of_mem_extended ctx hext
      by_cases hA : FtClass1Band4FreeDatum ctx
      · exact ftClass1Fibre_empty_of_band4FreeDatum ctx hA
      rcases Nat.lt_or_ge (class1SlopeDatum ctx).q 200 with hlt | hge
      · exact R.class1DeepLow ctx hr hdvd h9 hwin hcl hdc hgcd hext hA hlt haper
      · cases R.class1DeepTail ctx hr hge with
        | inl hfree => exact class1Tail_of_band4FreePeriod ctx hfree
        | inr hdeep => exact hdeep hdvd h9 hwin hcl hdc hgcd))

/-- The wave-3 4-way gate disjunction from the surface gates field (verbatim walk). -/
def returnGatesCycle (R : Erdos260AnchoredResidual) :
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
          (R.returnGates ctx hfree hone (not_lt.mp hnum))

/-- The class-4 population bound `|olcFibre| ≤ r + 1` from the gates. -/
theorem fibreSmall (R : Erdos260AnchoredResidual) : Class4FibreSmall :=
  class4FibreSmall_of_gates R.returnGatesCycle

/-- The per-ctx K.1 interior (verbatim walk). -/
def interiorAt (R : Erdos260AnchoredResidual) (ctx : ActualFailureContext) :
    ReturnInteriorBody ctx := by
  by_cases hfree : ReturnB2FreeDatum ctx
  · exact (returnCtxAllFour_of_b2FreeDatum ctx hfree).2.2.2
  · exact R.returnInterior ctx hfree

/-- The Return slot with the Return lane CLOSED — the wave-15a unconditional charge from
the counts alone. -/
def returnCharge (R : Erdos260AnchoredResidual) :
    ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx :=
  fun ctx => Class4ReturnPerSliceCharge.ofCountsOnly ctx (R.interiorAt ctx) (R.fibreSmall ctx)

/-- The Return capacity floor from the kept fields alone (the record). -/
theorem returnFloor (R : Erdos260AnchoredResidual) (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 4
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  (R.returnCharge ctx).returnFloor

/-- The V3 tower count of the budget (verbatim walk). -/
def towerCountV3 (R : Erdos260AnchoredResidual) :
    ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx :=
  p9V3TowerCount_ofShallowDeep
    (towerDeepResidual_ofCountBound (towerCountBound_of_modulusEnumeration R.towerEnum))

/-- The Run max-core family of the budget (verbatim walk). -/
def runCore (R : Erdos260AnchoredResidual) :
    ∀ ctx : ActualFailureContext, RunClass5LeafSupportMaxCoreResidual ctx :=
  fun ctx => (runSplitOfNumeric (runCycleNumericField_settled R.runNumeric) ctx).toCore

/-- The V3 run chain of the budget (verbatim walk). -/
def runChain (R : Erdos260AnchoredResidual) :
    ∀ ctx : ActualFailureContext, RunClass5StageChain ctx :=
  p9V3RunChainOfResidual (runClass5LeafResidual_ofSupportMaxCoreResidual R.runCore)

/-- **The anchored budget** — `v3Budget` with the Return slot carried by the unconditional
charge. -/
def budget (R : Erdos260AnchoredResidual) :
    ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx :=
  v3Budget R.towerCountV3 R.runChain R.returnCharge

/-- Class-0 routed emptiness at the anchored budget (budget-generic bridge). -/
theorem class0Empty (R : Erdos260AnchoredResidual) : Class0FibreEmpty R.budget :=
  class0FibreEmpty_of_genuineRoute_pinned R.budget (fun _ => rfl)
    (class0Pinned_field_iff_windowCycleCheck.mpr R.class0Cycle)

/-- Class-1 routed emptiness at the anchored budget (charge-family-generic bridge). -/
theorem class1Empty (R : Erdos260AnchoredResidual) : Class1FibreEmpty R.budget :=
  class1FibreEmpty_of_pinned_arithmetic_sharp R.towerCountV3 R.runChain R.returnCharge
    (class1Pinned_of_deepResidual R.class1Deep)

/-- The corrected DensePack residue at the anchored budget (budget-generic walk). -/
def densePackCorrected (R : Erdos260AnchoredResidual) :
    DensePackCorrectedResidue R.budget :=
  (R.densePackUngated.toGatedClosure.toDatumSplit.toCycleSplit.toRegimeSplit R.budget).toCorrected

/-- **The ctx-pinned P9 ledger from the wave-15 surface** — exactly the anchored-count
walk over the folded fields. -/
def toLedger (R : Erdos260AnchoredResidual) : P9CtxPinnedLedgerResidual where
  budget := R.budget
  hChernoff :=
    (ChernoffGenuineAreaKraftSmallResidual.ofClass0FibreEmpty R.budget
      R.class0Empty).hChernoffField
  hCnl := (hCnlField_iff_class1FibreEmpty R.budget).mpr R.class1Empty
  hDensePack := R.densePackCorrected.hDensePackField (fun _ => rfl)
  hTRT := seedHTRT R.budget
  hOldRes := fun ctx => by
    show routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 6
        ≤ ∑ k ∈ oldResIdxVal ctx, oldResAtVal ctx k
    rw [genuineChargeRoute_routed6_zero ctx]
    exact oldResL65_branchMass_nonneg ctx

/-- The final statement from the wave-15 surface.  Composition only. -/
theorem toStatement (R : Erdos260AnchoredResidual) : Erdos260Statement :=
  R.toLedger.toStatement

end Erdos260AnchoredResidual

/-- **THE WAVE-15 ENDPOINT**: `Erdos260Statement` from the folded 12-field surface — the
Return lane closed (wave 15a), the tower lane relieved at the band-pinned fixed data, the
run lane relieved of `(93,15)`, the class-0 survivor demand reduced to its off-fibre part
at the fourteen heavy pairs, and the class-1 deep threshold at `200`.  Public bridges
only. -/
theorem erdos260_of_anchoredResidual (R : Erdos260AnchoredResidual) :
    Erdos260Statement :=
  R.toStatement

/-! ## Part 5.  Witnesses and honest direction accounting -/

/-- **The weakening witness**: the anchored-count surface yields the wave-15 surface — the
relieved guards are dropped, the decomposed survivor field restricts, and the moved class-1
thresholds are re-dispatched through the OLD fields.  One direction only; NO converse is
claimed. -/
def anchoredResidual_of_anchoredCount (R : Erdos260AnchoredCountResidual) :
    Erdos260AnchoredResidual where
  towerEnumLow := fun ctx hesc hlt haper _ _ => R.towerEnumLow ctx hesc hlt haper
  towerEnumTail := R.towerEnumTail
  runNumericLow := R.runNumericLow
  runNumericTail := fun ctx hge _ => R.runNumericTail ctx hge
  returnGates := R.returnGates
  returnInterior := R.returnInterior
  class0Survivor := fun ctx hsurv =>
    ⟨fun _ => R.class0Survivor ctx hsurv,
     fun _ k hk hfl _ => R.class0Survivor ctx hsurv k hk hfl⟩
  class0Mid := R.class0Mid
  class0BigOrder := R.class0BigOrder
  class1DeepLow := fun ctx _hr hdvd h9 hwin hcl hdc hgcd _hext _hA _hlt haper => by
    rcases Nat.lt_or_ge (class1SlopeDatum ctx).q 101 with h101 | h101
    · exact R.class1DeepLow ctx hdvd h9 hwin hcl hdc hgcd h101 haper
    · cases R.class1DeepTail ctx h101 with
      | inl hfree => exact class1Tail_of_band4FreePeriod ctx hfree
      | inr hdeep => exact hdeep hdvd h9 hwin hcl hdc hgcd
  class1DeepTail := fun ctx _hr hge =>
    R.class1DeepTail ctx (le_trans (by norm_num) hge)
  densePackUngated := R.densePackUngated

/-- Nonempty transport from the anchored-count surface (one direction — honest). -/
theorem nonempty_anchoredResidual_of_anchoredCount
    (h : Nonempty Erdos260AnchoredCountResidual) :
    Nonempty Erdos260AnchoredResidual :=
  h.elim fun R => ⟨anchoredResidual_of_anchoredCount R⟩

/-- Nonempty transport from the canonical charge surface (two one-directional steps). -/
theorem nonempty_anchoredResidual_of_returnCharge
    (h : Nonempty Erdos260ReturnChargeResidual) :
    Nonempty Erdos260AnchoredResidual :=
  h.elim fun R =>
    ⟨anchoredResidual_of_anchoredCount (anchoredCountResidual_of_returnChargeResidual R)⟩

/-! ## Part 6.  The conditional routes (re-exported under capstone-local names)

The SCC persistence routes are NEW in wave 15; the onset / covering-families /
carry-linear / zero-field routes are carried forward from wave 14.  None is claimed
unconditional. -/

/-- Route A (the pressure relocation — the wave-15 verdict): at every fixed-family hit the
pressure floor sits in class 4 / class 3 / (up to `1/512`) class 5 — NEVER in class 2. -/
theorem anchoredCapstone_pressure_relocation (ctx : ActualFailureContext)
    (hhit : FixedFamilyHit ctx) :
    erdos260Constants.cPr * (ctx.shell.X : ℝ) * ((ctx.n24CarryData.r : ℝ) + 1)
        ≤ routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 4
      ∨ erdos260Constants.cPr * (ctx.shell.X : ℝ) * ((ctx.n24CarryData.r : ℝ) + 1)
          ≤ routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 3
      ∨ 511 / 512 * (erdos260Constants.cPr * (ctx.shell.X : ℝ)
            * ((ctx.n24CarryData.r : ℝ) + 1))
          ≤ routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5 :=
  fixedFamilyHit_pressure_relocation ctx hhit

/-- Route A's voiding (the SECOND, bootstrap-free voiding of the clean continuation): per
context, at EVERY scale. -/
theorem anchoredCapstone_cleanContinuation_pressure_void (ctx : ActualFailureContext)
    (hhit : FixedFamilyHit ctx) (hcc : FixedFamilyCleanContinuation ctx) : False :=
  fixedFamilyCleanContinuation_pressure_void ctx hhit hcc

/-- Route A's carry-linear corollary: the carry linearity is pressure-void at every
fixed-family hit. -/
theorem anchoredCapstone_carryLinear_pressure_void (ctx : ActualFailureContext)
    (hhit : FixedFamilyHit ctx) (hcl : FixedFamilyCarryLinear ctx) : False :=
  fixedFamilyCarryLinear_pressure_void ctx hhit hcl

/-- Route B (the widened supply atom): shell persistence is VOID at every scale by raw
support counting. -/
theorem anchoredCapstone_shellPersistence_void (ctx : ActualFailureContext)
    (hhit : FixedFamilyHit ctx) (hp : FixedFamilyShellPersistence ctx) : False :=
  fixedFamilyShellPersistence_void ctx hhit hp

/-- Route B's consumer: ALL FIVE fixed families void at every scale under the deep
shell-persistence supply. -/
theorem anchoredCapstone_fixedFamilyHit_void_of_shellPersistence
    (h : DeepFixedFamilyShellPersistence) (ctx : ActualFailureContext) :
    ¬ FixedFamilyHit ctx :=
  fixedFamilyHit_void_of_shellPersistence h ctx

/-- Route B's no-free-lunch record: the deep shell persistence IS the deep voiding. -/
theorem anchoredCapstone_shellPersistence_iff_void :
    DeepFixedFamilyShellPersistence ↔ DeepFixedFamilyVoid :=
  deepFixedFamilyShellPersistence_iff_void

/-- Route B's strength record: the deep shell persistence has exactly the strength of the
deep carry linearity. -/
theorem anchoredCapstone_shellPersistence_iff_carryLinear :
    DeepFixedFamilyShellPersistence ↔ DeepFixedFamilyCarryLinear :=
  deepFixedFamilyShellPersistence_iff_carryLinear

/-- Route B's supply drop: the clean continuation supplies the deep shell persistence (the
onset window widens `(0, X]` to `(0, 2X − X/512]`). -/
theorem anchoredCapstone_shellPersistence_of_cleanContinuation
    (h : DeepFixedFamilyCleanContinuation) : DeepFixedFamilyShellPersistence :=
  deepFixedFamilyShellPersistence_of_cleanContinuation h

/-- Route B's tower consumer: the tower capstone field bridge under the shell
persistence. -/
theorem anchoredCapstone_towerFixedPointResidual_of_shellPersistence
    (h : DeepFixedFamilyShellPersistence) (hres : TowerLeverResidual) :
    TowerFixedPointResidual :=
  towerFixedPointResidual_of_shellPersistence h hres

/-- Route C (the carry-linear chain, carried forward): EQUIVALENT to the clean
continuation. -/
theorem anchoredCapstone_cleanContinuation_iff_carryLinear :
    DeepFixedFamilyCleanContinuation ↔ DeepFixedFamilyCarryLinear :=
  deepFixedFamilyCleanContinuation_iff_carryLinear

/-- Route C's strength record: the deep carry linearity equals the deep family voiding. -/
theorem anchoredCapstone_carryLinear_iff_void :
    DeepFixedFamilyCarryLinear ↔ DeepFixedFamilyVoid :=
  deepFixedFamilyCarryLinear_iff_void

/-- Route C's bootstrap form: the deep carry linearity equals the deep window-periodicity
supply. -/
theorem anchoredCapstone_carryLinear_iff_windowPeriodicity :
    DeepFixedFamilyCarryLinear ↔ DeepFixedFamilyWindowPeriodicity :=
  deepFixedFamilyCarryLinear_iff_windowPeriodicity

/-- Route D (consumer 1, covering families, carried forward): onset-capped families
covering every deep context fire the full multi-scale sibling supply and the wave-6
chain. -/
theorem anchoredCapstone_erdos260_of_coveringFamilies
    (h : ∀ ctx : ActualFailureContext, 2 ^ 493443 < ctx.X →
      ∃ fam : ObligationScaleFamily,
        fam.onset ≤ 493443 ∧ ctx.d = fam.d ∧ ctx.Q ≤ 2 ^ max fam.onset 5)
    (surfaces : DyadicValueLever → Erdos260DyadicLeverResidual) :
    Erdos260Statement :=
  erdos260_of_coveringFamilies h surfaces

/-- Route E (the wave-14 onset entry, carried forward; SUPERSEDED as a need — the Return
lane its gate fed is now closed — but still a valid conditional entry). -/
theorem anchoredCapstone_erdos260_of_onsetResidual (R : Erdos260OnsetResidual) :
    Erdos260Statement :=
  erdos260_of_onsetResidual R

/-- Route F (the graded zero entry, carried forward). -/
theorem anchoredCapstone_erdos260_of_windowOnesZeroField (R : Erdos260WindowOnesResidual)
    (h : ReturnWindowOnesZeroField) : Erdos260Statement :=
  erdos260_of_windowOnesZeroField R h

/-! ## Part 7.  Machine-readable status (honest) -/

/-- Honest machine-readable status of the anchored capstone (the wave-15 fold). -/
def erdos260AnchoredCapstoneStatus : List String :=
  [ "SURFACES (ordered by strength - honest): Erdos260ReturnChargeResidual " ++
      "(Erdos260ChargeCapstone, 13 fields) -> Erdos260AnchoredCountResidual " ++
      "(AnchoredKeyCount, 12 fields, returnDirtyEnvelope DELETED - the Return lane " ++
      "CLOSED unconditionally at the charge junction) -> Erdos260AnchoredResidual " ++
      "(this module, 12 fields) - each step one-directional downward " ++
      "(anchoredCountResidual_of_returnChargeResidual, anchoredResidual_of_" ++
      "anchoredCount); NO converse claimed.  Endpoint erdos260_of_anchoredResidual " ++
      "replays the public per-lane ledger walk with the folded lanes dispatched " ++
      "through the wave-15 sweep closures.",
    "THE RETURN LANE IS CLOSED (wave 15a, carried verbatim): the per-slice charge is " ++
      "key-generic, the maximally refined anchored key k -> k makes every slice a " ++
      "singleton, and returnGates supplies the population bound |olcFibre| <= r + 1 - " ++
      "Class4ReturnPerSliceCharge.ofCountsOnly needs NO envelope, NO digit, NO " ++
      "key-injectivity, NO dirty-slice field.  The returnZero/envelope lineage of " ++
      "waves 1-14 is RETIRED.  Honest: this is transcription-granularity - the " ++
      "manuscript's M.2.1 count is faithfully transcribed AND bypassed, because the " ++
      "formal class-4 fibre is already gated to <= r + 1 members.",
    "WHAT FOLDED (the four weakened lanes): (1) towerEnumLow relieved at (3,1) and " ++
      "(21,3) - Class2CycleInequality is FREE at the band-2/3 pinned fixed points " ++
      "(anchoredCapstone_class2Ineq_of_datum_3_1/_21_3: constant orbit, period-1 " ++
      "cycle, band-4 count 0); (2) runNumericTail relieved of (93,15) " ++
      "(ftRunCloses_of_datum_93_15 - the unique band-{1,4}-free closure on odd " ++
      "64 <= q < 128); (3) class0Survivor decomposed along the b2 cross/heavy split: " ++
      "verbatim residue miss at the five crossed pairs, OFF-FIBRE restriction only at " ++
      "the FOURTEEN heavy pairs (ftClass0ResidueMiss_of_offFibre; the on-fibre part " ++
      "is free by ftHeavyConflict_dispatch); (4) class1DeepLow/Tail moved 101 -> 200, " ++
      "relieved of the eight closed moduli ftClass1ClosedModuli200 = {109, 113, 123, " ++
      "127, 129, 151, 157, 171} and the 49 band-4-free pairs (FtClass1Band4FreeDatum), " ++
      "with the free guards 1 <= r and the aperiodicity lever added.",
    "WHAT DID NOT FOLD (honest): (a) densepack - the nineteen band-3-free closures " ++
      "compose as GUARD DISCHARGE (anchoredCapstone_class3Band3Free_of_band3FreeDatum " ++
      "fails the residual's first guard at the pairs); the field stays verbatim; " ++
      "ftDensePackStartsEmpty_split_at_128 is an ALTERNATIVE route shape (emptiness " ++
      "demands), incomparable to the structured residual; (b) towerEnumTail - at the " ++
      "five fixed data the demand NEVER fires (q <= 105 < 107), and the relocation " ++
      "supplies no count bound for the genuine 107 <= q tail (class-2 stays populated " ++
      "under the band-4 pin; scc_class12_deficit starves MASS, Class2CycleInequality " ++
      "is a COUNT bound); the class-2 escape demand at (15,1) (15,2) (105,7) REMAINS " ++
      "in towerEnumLow - the brief's hoped-for vacuity REVERSED into relief at the " ++
      "band-2/3 data only; (c) the run/densepack 128-split mid-band hypotheses are " ++
      "STRONGER than the surface's order-escape tails - dispatchers recorded, not " ++
      "folded.",
    "THE PRESSURE RELOCATION (PROVED, wave 15, re-exported): at every fixed-family " ++
      "hit the Lemma 21.1 floor sits in class 4 at (3,1), class 3 at (21,3), and (up " ++
      "to 1/512) class 5 at the band-4 data - NEVER in class 2 " ++
      "(anchoredCapstone_pressure_relocation; classes 1+2 absorb < 1/512 of the " ++
      "floor).  The SECOND bootstrap-free voiding: the clean continuation and the " ++
      "carry linearity contradict the pressure floor per context at EVERY scale " ++
      "(anchoredCapstone_cleanContinuation_pressure_void / _carryLinear_pressure_" ++
      "void).  The widened supply atom FixedFamilyShellPersistence (onset anywhere " ++
      "with 512*a(k1) <= 1023*X) is VOID by raw support counting " ++
      "(anchoredCapstone_shellPersistence_void); its deep form has EXACTLY the " ++
      "strength of the deep voiding / carry linearity (no free lunch).",
    "THE TAIL-SWEEP MASTER LISTS (recorded in FiniteTailsSweep): heavy conflicts " ++
      "finiteTailsSweepHeavyConflictPairs (14); class-1 closed " ++
      "finiteTailsSweepClass1ClosedModuli (8) + finiteTailsSweepClass1ClosedPairs " ++
      "(49), surviving finiteTailsSweepClass1SurvivorPairs (87); run closed (93,15) " ++
      "only - band-1 saturated - surviving finiteTailsSweepRunSurvivorPairs (79); " ++
      "densepack closed finiteTailsSweepDensePackClosedPairs (19), surviving " ++
      "finiteTailsSweepDensePackSurvivorPairs (61).  The exceptional-cofactor cross " ++
      "among the 87 class-1 survivors is EXACTLY (105,7) and (155,15) " ++
      "(ftSurvivor_105_7_exceptional / ftSurvivor_155_15_exceptional).",
    "ROUTES RE-EXPORTED (conditional, none claimed unconditional): A. the pressure " ++
      "relocation + the second voiding; B. shell persistence (void per hit; deep form " ++
      "iff void iff carry linearity; consumer anchoredCapstone_fixedFamilyHit_void_" ++
      "of_shellPersistence; tower consumer anchoredCapstone_towerFixedPointResidual_" ++
      "of_shellPersistence); C. the carry-linear chain (iff clean continuation, iff " ++
      "void, iff window periodicity); D. covering families " ++
      "(anchoredCapstone_erdos260_of_coveringFamilies - consumer 1, genuinely open: " ++
      "pinned words force onset > 493443); E. the wave-14 onset entry " ++
      "(anchoredCapstone_erdos260_of_onsetResidual - SUPERSEDED as a need: the " ++
      "Return consumer its gate fed is GONE, kept as a valid conditional entry); " ++
      "F. the graded zero entry (anchoredCapstone_erdos260_of_windowOnesZeroField).",
    "WHAT REMAINS OPEN (the honest post-wave-15 set, sharpest form): (1) " ++
      "FixedFamilyShellPersistence at the five fixed data - the weakest known " ++
      "fixed-family form (everything else on that axis proved equivalent or " ++
      "stronger); (2) the onset FUNCTION bound - consumer 1 (covering families) " ++
      "ONLY now, since the Return consumer is gone; (3) the finite survivor lists - " ++
      "87 class-1 pairs (101 <= q < 200) + the 23 wave-5 pairs (q <= 99) + 79 run " ++
      "pairs + 61 densepack pairs + the off-fibre class-0 residue misses at the 19 " ++
      "survivor pairs; (4) the remaining non-Return per-survivor windowed checks and " ++
      "the modulus tails (towerEnumLow at the three band-4 fixed data, towerEnumTail, " ++
      "runNumericTail, class0Mid/BigOrder, class1DeepTail at 200 <= q).",
    "HYGIENE: additive only - no existing module edited (the root import file gains " ++
      "one line; SCCPersistence, AnchoredKeyCount, FiniteTailsSweep and the wave-14 " ++
      "chain enter the root through this module's imports); no sorry / admit / new " ++
      "axiom / native_decide; all #print axioms in [propext, Classical.choice, " ++
      "Quot.sound] or fewer." ]

theorem erdos260AnchoredCapstoneStatus_nonempty :
    erdos260AnchoredCapstoneStatus ≠ [] := by
  simp [erdos260AnchoredCapstoneStatus]

/-! ## Part 8.  Axiom-cleanliness audit -/

#print axioms anchoredCapstone_class2Ineq_of_datum_3_1
#print axioms anchoredCapstone_class2Ineq_of_datum_21_3
#print axioms anchoredCapstone_class3Band3Free_of_band3FreeDatum
#print axioms anchoredCapstone_heavyConflict_of_survivor
#print axioms anchoredCapstone_class0ResidueMiss_iff_offFibre
#print axioms Erdos260AnchoredResidual.towerEnum
#print axioms Erdos260AnchoredResidual.runNumeric
#print axioms Erdos260AnchoredResidual.class0SurvivorMiss
#print axioms Erdos260AnchoredResidual.class0Cycle
#print axioms Erdos260AnchoredResidual.class1Deep
#print axioms Erdos260AnchoredResidual.returnCharge
#print axioms Erdos260AnchoredResidual.returnFloor
#print axioms Erdos260AnchoredResidual.budget
#print axioms Erdos260AnchoredResidual.toLedger
#print axioms Erdos260AnchoredResidual.toStatement
#print axioms erdos260_of_anchoredResidual
#print axioms anchoredResidual_of_anchoredCount
#print axioms nonempty_anchoredResidual_of_anchoredCount
#print axioms nonempty_anchoredResidual_of_returnCharge
#print axioms anchoredCapstone_pressure_relocation
#print axioms anchoredCapstone_cleanContinuation_pressure_void
#print axioms anchoredCapstone_carryLinear_pressure_void
#print axioms anchoredCapstone_shellPersistence_void
#print axioms anchoredCapstone_fixedFamilyHit_void_of_shellPersistence
#print axioms anchoredCapstone_shellPersistence_iff_void
#print axioms anchoredCapstone_shellPersistence_iff_carryLinear
#print axioms anchoredCapstone_shellPersistence_of_cleanContinuation
#print axioms anchoredCapstone_towerFixedPointResidual_of_shellPersistence
#print axioms anchoredCapstone_cleanContinuation_iff_carryLinear
#print axioms anchoredCapstone_carryLinear_iff_void
#print axioms anchoredCapstone_carryLinear_iff_windowPeriodicity
#print axioms anchoredCapstone_erdos260_of_coveringFamilies
#print axioms anchoredCapstone_erdos260_of_onsetResidual
#print axioms anchoredCapstone_erdos260_of_windowOnesZeroField
#print axioms erdos260AnchoredCapstoneStatus_nonempty

end

end Erdos260
