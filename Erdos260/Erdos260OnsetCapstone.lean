import Erdos260.SparsityOnsetQuantification
import Erdos260.HitToHitCarry
import Erdos260.SurvivorKeyCount

/-!
# The onset capstone — the wave-14 fold (`Erdos260OnsetCapstone`)

This module (NEW; it edits no existing file) folds the wave-14 deliverables —
`SparsityOnsetQuantification` (the producing-side scale family and the consumer-2 onset
gate), `HitToHitCarry` (the E.11/E.14 hit-carry settlement), and `SurvivorKeyCount` (the
b2-free survivor harvest and the window-ones grading) — into the capstone chain above
`Erdos260WindowOnesCapstone`.

## The fold verdict (honest — read this first)

* **The survivor harvest composes as GUARD DISCHARGE, not as a new guard**: the charge
  capstone's envelope field (`ReturnDirtyEnvelopeField`) and the wave-13 entry field
  (`ReturnWindowOnesField`) ALREADY carry `¬ ReturnB2FreeDatum ctx` as their first verbatim
  guard, so the fifteen per-datum Return-lane closures
  (`returnLane_free_of_datumB2Free` + instances) and the crossed survivors
  (`returnLane_free_of_class0Cross`, `jointFree_of_class1Cross`) are exactly the closures
  the chain's endpoint already uses on the guard-failing contexts.  NO successor surface
  with a NOT-b2-free guard is needed — the guard is already in the field shape.  The new
  formal record is the REACH lemma `class0Survivor_heavy_of_not_b2Free`: inside the field's
  first guard, a class-0 survivor can only be one of the FOURTEEN b2-heavy remainder pairs.
* **What genuinely folds is consumer 2's onset supply**: `ReturnWindowOnesOnsetSupply`
  (the explicit sparsity-onset gate under the verbatim wave-13 guards) discharges the
  window-ones atom field (`returnWindowOnesField_of_onsetSupply`), so the successor surface
  `Erdos260OnsetResidual` below replaces `returnWindowOnesAtom` by the onset supply —
  13 fields, 12 verbatim.  Endpoint: `erdos260_of_onsetResidual`.
* **Entry-only content (recorded, not folded)**: the graded zero field
  (`ReturnWindowOnesZeroField` — a DIFFERENT strengthening of the same atom, neither
  implying nor implied by the onset supply; its endpoint
  `erdos260_of_windowOnesZeroField` is re-exported); the covering-families route
  (consumer 1; re-exported — pinned words force the onset above the cap, so the route is
  genuinely open); the carry-linear chain (EQUIVALENT to the clean continuation, hence to
  the deep voiding — by the no-free-lunch records it cannot enter as a weaker field, only
  as the named conditional route, re-exported); the lcm slice bounds at the unique-band-2
  parity pairs (conditional counting records, kept in `SurvivorKeyCount`).

## DIRECTION OF STRENGTH (honest)

`ReturnWindowOnesOnsetSupply → ReturnWindowOnesField` is ONE-directional (the gate is a
sufficient arithmetic certificate; the atom carries no ε-sparsity content from which a gate
could be rebuilt).  Hence `Erdos260OnsetResidual` is a SUFFICIENT ENTRY above the wave-13
entry surface, which itself sits one-directionally above the canonical
`Erdos260ReturnChargeResidual` — the canonical WEAKEST capstone surface remains the charge
surface; nothing here supersedes it.  The flat successor surface IS nonempty-equivalent to
the structured consumer-2 surface `Erdos260SparsityOnsetResidual`
(`nonempty_onsetResidual_iff_sparsityOnset` — mutual constructors, no strength gap).

No `sorry`, no `admit`, no new `axiom`, no `native_decide`; additive only — no existing
module is edited (the root import file gains one line; the three wave-14 modules enter the
root closure through this module's imports).
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 1.  The fold verdict at the survivor harvest (guard discharge, formalized) -/

/-- **The field-reach lemma at class-0 survivors**: inside the capstone fields' first
verbatim guard (`¬ ReturnB2FreeDatum ctx`), every class-0 survivor is one of the FOURTEEN
b2-heavy remainder pairs — the five crossed pairs `(17,8) (21,1) (33,1) (33,16) (41,20)`
never reach the field (their Return lane closes outright). -/
theorem class0Survivor_heavy_of_not_b2Free (ctx : ActualFailureContext)
    (hsurv : Class0DatumSurvivor ctx) (hnb2 : ¬ ReturnB2FreeDatum ctx) :
    Class0SurvivorB2HeavyRest ctx := by
  rcases class0Survivor_b2_split ctx hsurv with hcross | hheavy
  · exact absurd (returnB2FreeDatum_of_class0Cross ctx hcross) hnb2
  · exact hheavy

/-- Re-export (the aggregate guard discharge): every band-2-free datum frees the WHOLE
Return lane — gates, zero, maxClean, interior, and the envelope at once. -/
theorem onsetCapstone_returnLane_free_of_datumB2Free (ctx : ActualFailureContext)
    (h : ReturnB2FreeDatum ctx) : ReturnLaneFree ctx :=
  returnLane_free_of_datumB2Free ctx h

/-- Re-export (the class-0 cross): at the five crossed survivor pairs the whole Return lane
is free — the joint demand drops to the non-Return fields. -/
theorem onsetCapstone_returnLane_free_of_class0Cross (ctx : ActualFailureContext)
    (h : Class0SurvivorB2FreeCross ctx) : ReturnLaneFree ctx :=
  returnLane_free_of_class0Cross ctx h

/-- Re-export (the class-1 cross): at `(63,1) (63,3) (63,4)` the Return lane is free AND
the class-1 routed fibre is empty — two lanes settle at once. -/
theorem onsetCapstone_jointFree_of_class1Cross (ctx : ActualFailureContext)
    (h : Class1ClosedB2FreeCross ctx) :
    ReturnLaneFree ctx
      ∧ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  jointFree_of_class1Cross ctx h

/-! ## Part 2.  The successor surface (`Erdos260OnsetResidual`)

The wave-13 entry surface with the window-ones atom field replaced by consumer 2's named
onset supply — the only wave-14 deliverable that composes as a FIELD EXCHANGE through a
public discharge lemma (`returnWindowOnesField_of_onsetSupply`).  13 fields, 12 verbatim
wave-12/13 shapes. -/

/-- **The onset successor surface**: `Erdos260WindowOnesResidual` with
`returnWindowOnesAtom : ReturnWindowOnesField` REPLACED by
`returnWindowOnesOnset : ReturnWindowOnesOnsetSupply` (the explicit sparsity-onset gate
under the same verbatim guards — STRONGER demanded content; the gate implies the atom, no
converse).  The other 12 fields verbatim. -/
structure Erdos260OnsetResidual where
  /-- Tower / class 2 - enumerated part (`q < 107`), with the free aperiodicity guard. -/
  towerEnumLow : ∀ ctx : ActualFailureContext,
    TowerModulusEnumEscapeV2 ctx → (class1SlopeDatum ctx).q < 107 →
    (ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx) →
    Class2CycleInequality ctx
  /-- Tower / class 2 - tail (`107 ≤ q`), with the free aperiodicity guard. -/
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
  /-- Run / class 5 - tail (`64 ≤ q`); verbatim field. -/
  runNumericTail : ∀ ctx : ActualFailureContext,
    64 ≤ (class1SlopeDatum ctx).q →
    ((Nat.log 2 (class1SlopeDatum ctx).q + 1)
        * (supportShell ctx.shell.d ctx.shell.X).card
      < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
          (class1SlopeDatum ctx).K₀)))
      ∧ RunBandBudget ctx
    ∨ Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx
  /-- Return / class 4 count gates - verbatim field (the `hnumeric` supplier of the
  per-slice charge, through `class4FibreSmall_of_gates`). -/
  returnGates : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    2 * (129 * shellLadderDepth ctx + 64)
      ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
    ReturnGatesBodyUngated ctx
  /-- Return / class 4 digit Z, BOTH parities - **the onset-supply entry form**: some
  `(ε, L0)` clears the explicit sparsity-onset gate `WindowOnesOnsetGate` under the
  VERBATIM guards of the wave-13 entry field.  STRONGER demanded content than
  `returnWindowOnesAtom` (the gate implies the atom via
  `returnWindowOnesBound_of_onsetGate`; no converse) - the quantified-residual exchange of
  this surface. -/
  returnWindowOnesOnset : ReturnWindowOnesOnsetSupply
  /-- Return / class 4 K.1 interior - verbatim field (the `class4Interior` supplier of the
  per-slice charge). -/
  returnInterior : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx
  /-- Chernoff / class 0 survivors - verbatim field. -/
  class0Survivor : ∀ ctx : ActualFailureContext, Class0DatumSurvivor ctx →
    Class0SurvivorResidueMiss ctx
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
  /-- CNL / class 1 - enumerated deep part (`q < 101`), with the free aperiodicity guard. -/
  class1DeepLow : ∀ ctx : ActualFailureContext,
    64 ∣ shellLadderDepth ctx →
    9 ≤ (class1SlopeDatum ctx).q →
    ((class1SlopeDatum ctx).q ≤ 15 ∨ 25 ≤ (class1SlopeDatum ctx).q) →
    (class1SlopeDatum ctx).q ∉ class1ClosedModuli →
    ¬ Class1DatumClosed ctx →
    ¬ Class1GcdWindowMiss ctx →
    (class1SlopeDatum ctx).q < 101 →
    (ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx) →
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅
  /-- CNL / class 1 - tail (`101 ≤ q`); verbatim field. -/
  class1DeepTail : ∀ ctx : ActualFailureContext,
    101 ≤ (class1SlopeDatum ctx).q →
    Class1Band4FreePeriod ctx
    ∨ (64 ∣ shellLadderDepth ctx →
        9 ≤ (class1SlopeDatum ctx).q →
        ((class1SlopeDatum ctx).q ≤ 15 ∨ 25 ≤ (class1SlopeDatum ctx).q) →
        (class1SlopeDatum ctx).q ∉ class1ClosedModuli →
        ¬ Class1DatumClosed ctx →
        ¬ Class1GcdWindowMiss ctx →
        routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅)
  /-- DensePack / class 3 - verbatim field. -/
  densePackUngated : DensePackUngatedClosureResidual

namespace Erdos260OnsetResidual

/-- **The implication record (the direction that holds)**: the onset surface rebuilds the
wave-13 entry surface — the atom field from the onset supply
(`returnWindowOnesField_of_onsetSupply`), the other 12 fields verbatim.  NO CONVERSE IS
CLAIMED (the atom carries no ε-sparsity certificate; see the module header). -/
def toWindowOnes (R : Erdos260OnsetResidual) : Erdos260WindowOnesResidual where
  towerEnumLow := R.towerEnumLow
  towerEnumTail := R.towerEnumTail
  runNumericLow := R.runNumericLow
  runNumericTail := R.runNumericTail
  returnGates := R.returnGates
  returnWindowOnesAtom := returnWindowOnesField_of_onsetSupply R.returnWindowOnesOnset
  returnInterior := R.returnInterior
  class0Survivor := R.class0Survivor
  class0Mid := R.class0Mid
  class0BigOrder := R.class0BigOrder
  class1DeepLow := R.class1DeepLow
  class1DeepTail := R.class1DeepTail
  densePackUngated := R.densePackUngated

/-- The onset surface rebuilds the canonical charge surface (two one-directional steps). -/
def toReturnCharge (R : Erdos260OnsetResidual) : Erdos260ReturnChargeResidual :=
  R.toWindowOnes.toReturnCharge

/-- The flat onset surface rebuilds the structured consumer-2 surface of
`SparsityOnsetQuantification` (one half of the nonempty equivalence). -/
def toSparsityOnset (R : Erdos260OnsetResidual) : Erdos260SparsityOnsetResidual where
  onsetSupply := R.returnWindowOnesOnset
  surfaces := fun hF =>
    { towerEnumLow := R.towerEnumLow
      towerEnumTail := R.towerEnumTail
      runNumericLow := R.runNumericLow
      runNumericTail := R.runNumericTail
      returnGates := R.returnGates
      returnWindowOnesAtom := hF
      returnInterior := R.returnInterior
      class0Survivor := R.class0Survivor
      class0Mid := R.class0Mid
      class0BigOrder := R.class0BigOrder
      class1DeepLow := R.class1DeepLow
      class1DeepTail := R.class1DeepTail
      densePackUngated := R.densePackUngated }

/-- The final statement from the onset surface, through the wave-13 entry endpoint and the
canonical charge endpoint.  Composition only; nothing re-proved. -/
theorem toStatement (R : Erdos260OnsetResidual) : Erdos260Statement :=
  R.toWindowOnes.toStatement

end Erdos260OnsetResidual

/-- **THE WAVE-14 ENDPOINT**: `Erdos260Statement` from the onset successor surface — the
Return window-ones atom fired by the explicit sparsity-onset gate (`WindowOnesOnsetGate`,
the doubly-small demand `2^L0·(1+ε) + 2ε·(F+W) + 1 ≤ liftLevelBound X` with
`liftLevelBound` the INVERSE TOWER `log*`), routed through `erdos260_of_windowOnesResidual`
and `erdos260_of_returnChargeResidual`.  Public bridges only. -/
theorem erdos260_of_onsetResidual (R : Erdos260OnsetResidual) : Erdos260Statement :=
  R.toStatement

/-- The structured consumer-2 surface rebuilds the flat onset surface (the other half of
the nonempty equivalence): apply the stored surface function to the discharged atom and
keep the onset supply. -/
def onsetResidual_of_sparsityOnsetResidual (S : Erdos260SparsityOnsetResidual) :
    Erdos260OnsetResidual :=
  let W := S.surfaces (returnWindowOnesField_of_onsetSupply S.onsetSupply)
  { towerEnumLow := W.towerEnumLow
    towerEnumTail := W.towerEnumTail
    runNumericLow := W.runNumericLow
    runNumericTail := W.runNumericTail
    returnGates := W.returnGates
    returnWindowOnesOnset := S.onsetSupply
    returnInterior := W.returnInterior
    class0Survivor := W.class0Survivor
    class0Mid := W.class0Mid
    class0BigOrder := W.class0BigOrder
    class1DeepLow := W.class1DeepLow
    class1DeepTail := W.class1DeepTail
    densePackUngated := W.densePackUngated }

/-- The implication record, onset surface → entry surface (one direction only — honest). -/
def windowOnesResidual_of_onsetResidual (R : Erdos260OnsetResidual) :
    Erdos260WindowOnesResidual :=
  R.toWindowOnes

/-- Nonempty transport, onset → entry (one direction only — honest). -/
theorem nonempty_windowOnesResidual_of_onset
    (h : Nonempty Erdos260OnsetResidual) : Nonempty Erdos260WindowOnesResidual :=
  h.elim fun R => ⟨R.toWindowOnes⟩

/-- Nonempty transport, onset → canonical charge (one direction only — honest). -/
theorem nonempty_returnChargeResidual_of_onset
    (h : Nonempty Erdos260OnsetResidual) : Nonempty Erdos260ReturnChargeResidual :=
  h.elim fun R => ⟨R.toReturnCharge⟩

/-- **The presentation equivalence (no strength gap)**: the flat onset surface and the
structured consumer-2 surface are nonempty-equivalent — mutual constructors; the wave-14
successor surface is exactly `SparsityOnsetQuantification`'s residual in flat form. -/
theorem nonempty_onsetResidual_iff_sparsityOnset :
    Nonempty Erdos260OnsetResidual ↔ Nonempty Erdos260SparsityOnsetResidual :=
  ⟨fun h => h.elim fun R => ⟨R.toSparsityOnset⟩,
   fun h => h.elim fun S => ⟨onsetResidual_of_sparsityOnsetResidual S⟩⟩

/-! ## Part 3.  The conditional routes (re-exported under capstone-local names)

Four named conditional routes reach `Erdos260Statement` after wave 14; none is claimed
unconditional, and the honest obstructions are recorded in the status. -/

/-- Route 1 (consumer 2, THE NEW SUCCESSOR ROUTE): the structured sparsity-onset residual
endpoint of `SparsityOnsetQuantification` — equivalent to `erdos260_of_onsetResidual`. -/
theorem onsetCapstone_erdos260_of_sparsityOnsetResidual
    (R : Erdos260SparsityOnsetResidual) : Erdos260Statement :=
  erdos260_of_sparsityOnsetResidual R

/-- Route 2 (consumer 1, covering families): onset-capped families covering every deep
context fire the full multi-scale sibling supply and the wave-6 chain. -/
theorem onsetCapstone_erdos260_of_coveringFamilies
    (h : ∀ ctx : ActualFailureContext, 2 ^ 493443 < ctx.X →
      ∃ fam : ObligationScaleFamily,
        fam.onset ≤ 493443 ∧ ctx.d = fam.d ∧ ctx.Q ≤ 2 ^ max fam.onset 5)
    (surfaces : DyadicValueLever → Erdos260DyadicLeverResidual) :
    Erdos260Statement :=
  erdos260_of_coveringFamilies h surfaces

/-- Route 2's supply form: covering families discharge `MultiScaleSiblingSupply`. -/
theorem onsetCapstone_multiScaleSiblingSupply_of_coveringFamilies
    (h : ∀ ctx : ActualFailureContext, 2 ^ 493443 < ctx.X →
      ∃ fam : ObligationScaleFamily,
        fam.onset ≤ 493443 ∧ ctx.d = fam.d ∧ ctx.Q ≤ 2 ^ max fam.onset 5) :
    MultiScaleSiblingSupply :=
  multiScaleSiblingSupply_of_coveringFamilies h

/-- Route 3 (the carry-linear chain): the E.14 band-pinned hit-carry linearity residual is
EQUIVALENT to the clean continuation — the no-free-lunch verdict on this axis. -/
theorem onsetCapstone_cleanContinuation_iff_carryLinear :
    DeepFixedFamilyCleanContinuation ↔ DeepFixedFamilyCarryLinear :=
  deepFixedFamilyCleanContinuation_iff_carryLinear

/-- Route 3's strength record: the deep carry linearity equals the deep family voiding. -/
theorem onsetCapstone_carryLinear_iff_void :
    DeepFixedFamilyCarryLinear ↔ DeepFixedFamilyVoid :=
  deepFixedFamilyCarryLinear_iff_void

/-- Route 3's bootstrap form: the deep carry linearity equals the deep window-periodicity
supply. -/
theorem onsetCapstone_carryLinear_iff_windowPeriodicity :
    DeepFixedFamilyCarryLinear ↔ DeepFixedFamilyWindowPeriodicity :=
  deepFixedFamilyCarryLinear_iff_windowPeriodicity

/-- Route 3's consumer: under the deep carry linearity ALL FIVE fixed families are void at
EVERY scale. -/
theorem onsetCapstone_fixedFamilyVoid_of_carryLinear (h : DeepFixedFamilyCarryLinear)
    (ctx : ActualFailureContext) : ¬ FixedFamilyHit ctx :=
  fixedFamilyHit_void_of_carryLinear h ctx

/-- Route 4 (the graded zero entry): the window-ones ZERO field (no raw ones in the window,
under the verbatim guards) fires the wave-13 entry surface with the atom upgraded. -/
theorem onsetCapstone_erdos260_of_windowOnesZeroField (R : Erdos260WindowOnesResidual)
    (h : ReturnWindowOnesZeroField) : Erdos260Statement :=
  erdos260_of_windowOnesZeroField R h

/-! ## Part 4.  The producing-side surface (re-exported)

The reusable wave-14 finding: a SECOND `ActualFailureContext` over the same word exists at
EVERY sufficiently large scale — the obligation layer alone cannot supply it, the producing
side does. -/

/-- Re-export (the reusable producing-side surface): a genuine `ActualFailureContext` at
EVERY scale `2 ^ L` with `L ≥ fam.scaleFloor`, over the family word. -/
def onsetCapstone_ctxAt (fam : ObligationScaleFamily) (L : ℕ)
    (hL : fam.scaleFloor ≤ L) : ActualFailureContext :=
  fam.ctxAt L hL

/-- Re-export (the two-context transport): over one family word, failure contexts exist at
ANY two scales beyond the floor. -/
theorem onsetCapstone_twoContext_transport (fam : ObligationScaleFamily) {L L' : ℕ}
    (hL : fam.scaleFloor ≤ L) (hL' : fam.scaleFloor ≤ L') :
    ∃ ctx ctx' : ActualFailureContext,
      ctx.d = fam.d ∧ ctx'.d = fam.d ∧ ctx.Q = fam.Q ∧ ctx'.Q = fam.Q ∧
        ctx.X = 2 ^ L ∧ ctx'.X = 2 ^ L' :=
  fam.twoContext_transport hL hL'

/-- Re-export (the deep onset finding, the honest flip on route 2): a PINNED family word
forces the onset ABOVE the cap `493443` — the pin and an onset-capped tail cannot coexist,
so consumer 1 is genuinely open. -/
theorem onsetCapstone_onset_above_cap_of_pinned (fam : ObligationScaleFamily)
    {u t : ℕ} {P : ℤ} (hu7 : u ≤ 7) (hupos : 0 < u)
    (heta : realWeightedValue (natBinaryAsReal fam.d)
      = (P : ℝ) / ((u * 2 ^ t : ℕ) : ℝ))
    (ht : t ≤ 2 ^ max fam.onset 5) : 493443 < fam.onset :=
  fam.onset_above_cap_of_pinned hu7 hupos heta ht

/-! ## Part 5.  Machine-readable status (honest) -/

/-- Honest machine-readable status of the onset capstone (the wave-14 fold). -/
def erdos260OnsetCapstoneStatus : List String :=
  [ "SURFACES (three live, ordered by strength - honest): " ++
      "Erdos260ReturnChargeResidual (Erdos260ChargeCapstone, 13 fields) remains THE " ++
      "CANONICAL WEAKEST capstone surface; Erdos260WindowOnesResidual " ++
      "(Erdos260WindowOnesCapstone, 13 fields) is the wave-13 sufficient entry; " ++
      "Erdos260OnsetResidual (this module, 13 fields, 12 verbatim) is the wave-14 " ++
      "successor entry - the window-ones atom field replaced by " ++
      "returnWindowOnesOnset : ReturnWindowOnesOnsetSupply (the explicit sparsity-onset " ++
      "gate WindowOnesOnsetGate under the verbatim guards).  Endpoint " ++
      "erdos260_of_onsetResidual via returnWindowOnesField_of_onsetSupply -> " ++
      "erdos260_of_windowOnesResidual -> erdos260_of_returnChargeResidual.  Directions " ++
      "one-way down the chain (onset -> windowOnes -> charge); the flat onset surface is " ++
      "nonempty-EQUIVALENT to SparsityOnsetQuantification's structured " ++
      "Erdos260SparsityOnsetResidual (nonempty_onsetResidual_iff_sparsityOnset, mutual " ++
      "constructors).",
    "THE FOLD VERDICT ON THE SURVIVOR HARVEST (honest): the charge/windowOnes fields " ++
      "ALREADY guard on NOT ReturnB2FreeDatum (first verbatim guard since wave 12), so " ++
      "the fifteen b2-free Return-lane closures (returnLane_free_of_datumB2Free + " ++
      "per-datum instances) and the crossed survivors " ++
      "(returnLane_free_of_class0Cross at (17,8) (21,1) (33,1) (33,16) (41,20); " ++
      "jointFree_of_class1Cross at (63,1) (63,3) (63,4)) compose as GUARD DISCHARGE - " ++
      "exactly the closures the charge endpoint already applies on guard-failing " ++
      "contexts.  NO new successor guard is needed; the new formal record is the reach " ++
      "lemma class0Survivor_heavy_of_not_b2Free: inside the field's guard a class-0 " ++
      "survivor is one of the FOURTEEN b2-heavy remainder pairs (19,9) (25,2) (25,12) " ++
      "(27,1) (27,4) (27,13) (29,14) (35,2) (37,18) (39,1) (43,21) (45,1) (45,2) (45,4).  " ++
      "The lcm slice bounds at the unique-band-2 parity pairs (sliceCard_le_of_band2_" ++
      "unique et al.) remain conditional counting records in SurvivorKeyCount - they do " ++
      "NOT close the envelope (W ~ c0*X vs liftLevelBound X), so nothing to fold there.",
    "THE CONSUMER-2 GATE IS DOUBLY SMALL (the wave-13 correction): the demanded envelope " ++
      "liftLevelBound X is the INVERSE TOWER log* X (ReturnM2J4Core) - the wave-13 TODO " ++
      "text read the gate as L + 1; liftLevelBound X <= L + 1 is only an UPPER bound and " ++
      "the true gate is log*-small, so the onset function must satisfy f(eps) <= " ++
      "log2(log* X - 1) - 2 with eps ~ (log* X)/(F+W) (windowOnesOnsetGate_of_explicit).  " ++
      "All-scales c0-sparsity CANNOT reach it (the provable count is X-linear).",
    "THE FOUR CONDITIONAL ROUTES RE-EXPORTED: (1) the onset successor route " ++
      "(erdos260_of_onsetResidual / onsetCapstone_erdos260_of_sparsityOnsetResidual); " ++
      "(2) covering families (onsetCapstone_erdos260_of_coveringFamilies + supply form) " ++
      "- genuinely open: pinned words force onset > 493443 " ++
      "(onsetCapstone_onset_above_cap_of_pinned), so only non-pinned words could comply; " ++
      "(3) the carry-linear chain (onsetCapstone_cleanContinuation_iff_carryLinear, " ++
      "onsetCapstone_carryLinear_iff_void, onsetCapstone_carryLinear_iff_" ++
      "windowPeriodicity, onsetCapstone_fixedFamilyVoid_of_carryLinear) - EQUIVALENT to " ++
      "the clean continuation and to the deep voiding, so it enters as a named route, " ++
      "never as a weaker field; the open question is what forces band-pinned linearity " ++
      "(the manuscript's SCC persistence, I.3.1) - no in-tree tower atom constrains the " ++
      "integer-carry magnitude; (4) the graded zero entry " ++
      "(onsetCapstone_erdos260_of_windowOnesZeroField) - the zero field and the onset " ++
      "supply are INDEPENDENT strengthenings of the same atom: neither implies the " ++
      "other, no relation is claimed between them.",
    "THE PRODUCING-SIDE SURFACE (re-exported, settled): ObligationScaleFamily.ctxAt " ++
      "(onsetCapstone_ctxAt) builds a genuine ActualFailureContext at EVERY scale 2^L " ++
      "with L >= scaleFloor = max(onset, log2(threshold) + 1) over the family word - " ++
      "the threshold question is SETTLED (manuscriptLargeThresholdOf_eq: the threshold " ++
      "is fPST(d) + 2^(log2(4Q)+26), checkable-small modulo the opaque fPST, and NOT " ++
      "the binding constraint - the failure supply is the uncontrolled sparsity onset).  " ++
      "Two-context transport re-exported (onsetCapstone_twoContext_transport).",
    "WHAT REMAINS OPEN (the honest current set after wave 14): (1) the onset FUNCTION " ++
      "bound - BOTH consumers reduce to onset bounds the formalized structure cannot " ++
      "place (consumer 1 needs c0-onset <= 493443, refuted on pinned words; consumer 2 " ++
      "needs f(eps) ~ log2(log* X), doubly small) - genuinely deep; (2) SCC persistence " ++
      "=> carry linearity at the five fixed data (DeepFixedFamilyCarryLinear, " ++
      "equivalent to the voiding - no waypoint); (3) ReturnWindowOnesBound at the 14 " ++
      "b2-heavy class-0 survivors and the parity pairs (the lcm counts do not fit under " ++
      "liftLevelBound generically); (4) the per-pair aperiodic tails and the modulus " ++
      "tails (towerEnumTail / runNumericTail / class0BigOrder / class1DeepTail " ++
      "verbatim).  Plus the unchanged non-Return lanes and the returnGates/" ++
      "returnInterior count-and-boundary fields.",
    "HYGIENE: additive only - no existing module edited (the root import file gains one " ++
      "line; SparsityOnsetQuantification, HitToHitCarry, SurvivorKeyCount and their " ++
      "closures enter the root through this module's imports); no sorry / admit / new " ++
      "axiom / native_decide; all #print axioms in [propext, Classical.choice, " ++
      "Quot.sound] or fewer." ]

theorem erdos260OnsetCapstoneStatus_nonempty : erdos260OnsetCapstoneStatus ≠ [] := by
  simp [erdos260OnsetCapstoneStatus]

/-! ## Part 6.  Axiom-cleanliness audit -/

#print axioms class0Survivor_heavy_of_not_b2Free
#print axioms onsetCapstone_returnLane_free_of_datumB2Free
#print axioms onsetCapstone_returnLane_free_of_class0Cross
#print axioms onsetCapstone_jointFree_of_class1Cross
#print axioms Erdos260OnsetResidual.toWindowOnes
#print axioms Erdos260OnsetResidual.toReturnCharge
#print axioms Erdos260OnsetResidual.toSparsityOnset
#print axioms Erdos260OnsetResidual.toStatement
#print axioms erdos260_of_onsetResidual
#print axioms onsetResidual_of_sparsityOnsetResidual
#print axioms windowOnesResidual_of_onsetResidual
#print axioms nonempty_windowOnesResidual_of_onset
#print axioms nonempty_returnChargeResidual_of_onset
#print axioms nonempty_onsetResidual_iff_sparsityOnset
#print axioms onsetCapstone_erdos260_of_sparsityOnsetResidual
#print axioms onsetCapstone_erdos260_of_coveringFamilies
#print axioms onsetCapstone_multiScaleSiblingSupply_of_coveringFamilies
#print axioms onsetCapstone_cleanContinuation_iff_carryLinear
#print axioms onsetCapstone_carryLinear_iff_void
#print axioms onsetCapstone_carryLinear_iff_windowPeriodicity
#print axioms onsetCapstone_fixedFamilyVoid_of_carryLinear
#print axioms onsetCapstone_erdos260_of_windowOnesZeroField
#print axioms onsetCapstone_ctxAt
#print axioms onsetCapstone_twoContext_transport
#print axioms onsetCapstone_onset_above_cap_of_pinned
#print axioms erdos260OnsetCapstoneStatus_nonempty

end

end Erdos260
