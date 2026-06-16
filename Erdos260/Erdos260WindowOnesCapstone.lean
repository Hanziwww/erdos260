import Erdos260.Erdos260ChargeCapstone
import Erdos260.DirtySliceEnvelope
import Erdos260.FixedFamilyPeriodicity

/-!
# The window-ones capstone — the sufficient ENTRY surface above the charge capstone
(`Erdos260WindowOnesCapstone`)

This module (NEW; it edits no existing file) performs the wave-13 fold: the dirty-envelope
reduction of `DirtySliceEnvelope` enters the capstone chain as a SUFFICIENT-ENTRY surface
`Erdos260WindowOnesResidual` sitting ABOVE the canonical charge surface
`Erdos260ReturnChargeResidual` (`Erdos260ChargeCapstone`), and the fixed-family settlement of
`FixedFamilyPeriodicity` is wired into the build and re-exported into the status record.

## DIRECTION OF STRENGTH (read this first — honest)

`ReturnWindowOnesBound ctx` (the `DirtySliceEnvelope` atom:
`|returnWindowOnes ctx| + 1 <= liftLevelBound X`, pure sub-shell raw-support counting — no
slice, key, or carry content) IMPLIES the full dirty-slice envelope `SliceDirtyEnvelope ctx`
(`sliceDirtyEnvelope_of_windowOnesBound`) — indeed the (M.1) envelope on ALL slices of the
self-referential key, not only the dirty ones.  The window-ones surface therefore demands
STRICTLY MORE than the envelope surface, not less:

* `Erdos260ReturnChargeResidual` (the charge capstone) remains **THE CANONICAL WEAKEST**
  capstone surface — nothing in this module supersedes it;
* `Erdos260WindowOnesResidual` (this module) is **THE SUFFICIENT ENTRY** — the sharpest named
  atom from which the whole chain currently fires, mirroring how the run lane enters through
  `runSplitOfNumeric` (a sufficient numeric settlement, not a weakest form).

NO WEAKENING IS CLAIMED.  The implication record is ONE-directional:
`returnChargeResidual_of_windowOnesResidual : Erdos260WindowOnesResidual →
Erdos260ReturnChargeResidual`.  No converse is provided, and none should be derivable inside
the present interface: the envelope bounds the SLICE CARDINALITIES of the self-referential
key, while the window-ones atom bounds the RAW window support — an envelope provider (e.g.
any key-injectivity provider, which forces singleton slices outright via
`sliceDirtyEnvelope_of_keyInjOn`) constrains the raw window ones not at all.

## What the module delivers

* `ReturnWindowOnesField` — the window-ones atom under the VERBATIM guards of the charge
  capstone's `ReturnDirtyEnvelopeField` (band-2-free datum, spaced `b2 = 1` datum, the
  small-carry regime, index-window separation; NO parity hypothesis).  The guard placement is
  complementary by construction: window-cleanliness makes the atom free
  (`returnWindowOnesBound_of_indexWindowClean`), matching the `¬ ReturnIndexWindowClean`
  gate.
* `returnDirtyEnvelopeField_of_windowOnesField` — the parity-free field-level discharge of
  the envelope field from the atom.  CHECKED: this composition did NOT exist in tree —
  `DirtySliceEnvelope` ships only the Q-odd-target discharge
  (`dirtyEnvelopeQOddField_of_windowOnesBound`); here it is composed from the public lemmas
  (`sliceDirtyEnvelope_of_windowOnesBound` under the guards), and the Q-odd named target of
  the case-split rebase follows through the charge capstone's own
  `dirtyEnvelopeQOddField_of_envelopeField`.
* `Erdos260WindowOnesResidual` — the charge surface with `returnDirtyEnvelope` replaced by
  `returnWindowOnesAtom : ReturnWindowOnesField`; 13 fields, 12 verbatim.
* `erdos260_of_windowOnesResidual` — THE ENTRY ENDPOINT (`Erdos260Statement` from the entry
  surface), composing PUBLIC bridges only: the field discharge above, then the canonical
  charge endpoint `erdos260_of_returnChargeResidual`.  Nothing is re-proved.
* `returnChargeResidual_of_windowOnesResidual` +
  `nonempty_returnChargeResidual_of_windowOnes` — the one-directional implication record.
* The fixed-family settlement re-exports (`FixedFamilyPeriodicity`): the conditional voiding
  chain (`fixedFamilyHit_void_of_cleanContinuation`), the DEAD zero-run bridge
  (`actual_zeroRun_void` / `carry_tracks_hzero_void` — the wave-2..5 conditional hit/orbit
  bridge hypothesis is EMPTY at every actual context), and the no-free-lunch equivalences
  (`deepFixedFamilyCleanContinuation_iff_void`).

No `sorry`, no `admit`, no new `axiom`, no `native_decide`; additive only — no existing
module is edited (the root import file gains one line).
-/

namespace Erdos260

noncomputable section

/-! ## Part 1.  The window-ones entry field (the atom under the verbatim envelope guards) -/

/-- **The window-ones entry field**: under the VERBATIM guards of the charge capstone's
`ReturnDirtyEnvelopeField` (band-2-free datum, spaced `b2 = 1` datum, the small-carry regime,
index-window separation — NO parity hypothesis), the raw window ones fit under the
inverse-tower envelope (`ReturnWindowOnesBound ctx`:
`|returnWindowOnes ctx| + 1 <= liftLevelBound X`).  Pure sub-shell raw-support counting — no
slice, key, or carry content.  STRONGER in demanded content than the envelope field it
discharges (see the module header); the guards are complementary
(`returnWindowOnesBound_of_indexWindowClean` makes the atom free on window-clean
contexts). -/
def ReturnWindowOnesField : Prop :=
  ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    (∃ k ∈ olcFibre ctx,
      2 ^ carryVal2 ctx k < (supportShell ctx.shell.d ctx.shell.X).card) →
    ¬ ReturnIndexWindowClean ctx →
    ReturnWindowOnesBound ctx

/-- An unguarded atom supply yields the guarded entry field (the guards are simply
absorbed). -/
theorem returnWindowOnesField_of_forall
    (h : ∀ ctx : ActualFailureContext, ReturnWindowOnesBound ctx) :
    ReturnWindowOnesField :=
  fun ctx _hA _hB _hC _hD => h ctx

/-- A guarded support-form supply (`LowScaleSupportBound`, the
`supportCount d (F + W) + 1 <= liftLevelBound X` form) yields the entry field through the
public atom implication `returnWindowOnesBound_of_lowScaleSupport`. -/
theorem returnWindowOnesField_of_lowScaleSupport
    (h : ∀ ctx : ActualFailureContext,
      ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
      (∃ k ∈ olcFibre ctx,
        2 ^ carryVal2 ctx k < (supportShell ctx.shell.d ctx.shell.X).card) →
      ¬ ReturnIndexWindowClean ctx →
      LowScaleSupportBound ctx) :
    ReturnWindowOnesField :=
  fun ctx hA hB hC hD =>
    returnWindowOnesBound_of_lowScaleSupport ctx (h ctx hA hB hC hD)

/-- **The parity-free field-level discharge** (the composition that did not exist in tree):
the window-ones entry field discharges the charge capstone's WHOLE parity-free envelope field
`ReturnDirtyEnvelopeField`, guard for guard, through the public reduction
`sliceDirtyEnvelope_of_windowOnesBound`.  THE DIRECTION IS STRENGTHENING: the atom implies
the envelope; no converse is claimed. -/
theorem returnDirtyEnvelopeField_of_windowOnesField
    (h : ReturnWindowOnesField) : ReturnDirtyEnvelopeField :=
  fun ctx hA hB hC hD => sliceDirtyEnvelope_of_windowOnesBound ctx (h ctx hA hB hC hD)

/-- The named Q-odd weaker target of the case-split rebase
(`ReturnDirtyEnvelopeQOddField`) discharges from the entry field, through the charge
capstone's parity absorption `dirtyEnvelopeQOddField_of_envelopeField`. -/
theorem dirtyEnvelopeQOddField_of_windowOnesField
    (h : ReturnWindowOnesField) : ReturnDirtyEnvelopeQOddField :=
  dirtyEnvelopeQOddField_of_envelopeField (returnDirtyEnvelopeField_of_windowOnesField h)

/-! ## Part 2.  The entry surface

The charge capstone surface with the (canonical, weakest) envelope field replaced by the
(stronger, sharpest-atom) window-ones entry field; the other 12 fields VERBATIM wave-12/13
shapes.  This surface is the SUFFICIENT ENTRY, not a successor: `Erdos260ReturnChargeResidual`
remains the canonical weakest capstone surface. -/

/-- **The window-ones entry surface**: `Erdos260ReturnChargeResidual` with the parity-free
envelope field `returnDirtyEnvelope` REPLACED by the window-ones entry field
`returnWindowOnesAtom : ReturnWindowOnesField` (same guards, STRONGER demanded content — the
atom implies the envelope, not conversely).  13 fields, 12 verbatim.  Mirrors how the run
lane enters through `runSplitOfNumeric`: a sufficient entry above the canonical surface. -/
structure Erdos260WindowOnesResidual where
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
  /-- Return / class 4 count gates - verbatim field (now ALSO the `hnumeric` supplier of the
  per-slice charge, through `class4FibreSmall_of_gates`). -/
  returnGates : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    2 * (129 * shellLadderDepth ctx + 64)
      ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
    ReturnGatesBodyUngated ctx
  /-- Return / class 4 digit Z, BOTH parities - **the window-ones entry form**: the raw
  window ones fit under the inverse-tower envelope (`ReturnWindowOnesBound`), under the
  VERBATIM guards of the canonical envelope field.  STRONGER demanded content than
  `returnDirtyEnvelope` (the atom implies the envelope; no converse) - the sufficient-entry
  exchange of this surface. -/
  returnWindowOnesAtom : ReturnWindowOnesField
  /-- Return / class 4 K.1 interior - verbatim field (now ALSO the `class4Interior` supplier
  of the per-slice charge). -/
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

namespace Erdos260WindowOnesResidual

/-- **The implication record (the direction that holds)**: the entry surface rebuilds the
canonical charge surface — the envelope field from the window-ones field
(`returnDirtyEnvelopeField_of_windowOnesField`), the other 12 fields verbatim.  NO CONVERSE
IS CLAIMED (the envelope carries no raw-support content; see the module header). -/
def toReturnCharge (R : Erdos260WindowOnesResidual) : Erdos260ReturnChargeResidual where
  towerEnumLow := R.towerEnumLow
  towerEnumTail := R.towerEnumTail
  runNumericLow := R.runNumericLow
  runNumericTail := R.runNumericTail
  returnGates := R.returnGates
  returnDirtyEnvelope := returnDirtyEnvelopeField_of_windowOnesField R.returnWindowOnesAtom
  returnInterior := R.returnInterior
  class0Survivor := R.class0Survivor
  class0Mid := R.class0Mid
  class0BigOrder := R.class0BigOrder
  class1DeepLow := R.class1DeepLow
  class1DeepTail := R.class1DeepTail
  densePackUngated := R.densePackUngated

/-- The final statement from the entry surface, through the canonical charge endpoint.
Composition only; nothing re-proved. -/
theorem toStatement (R : Erdos260WindowOnesResidual) : Erdos260Statement :=
  R.toReturnCharge.toStatement

end Erdos260WindowOnesResidual

/-- **THE ENTRY ENDPOINT**: `Erdos260Statement` from the window-ones entry surface — the
Return lane fired by the sub-shell support atom `ReturnWindowOnesBound` alone (under the
verbatim guards), routed through the canonical charge endpoint
`erdos260_of_returnChargeResidual`.  Public bridges only. -/
theorem erdos260_of_windowOnesResidual (R : Erdos260WindowOnesResidual) :
    Erdos260Statement :=
  R.toStatement

/-! ## Part 3.  The implication record (one-directional — honest)

The window-ones surface IMPLIES the charge surface; the charge surface remains the canonical
weakest.  No witness in the other direction exists or is claimed: an envelope provider does
not bound the raw window support (key-injectivity providers force singleton slices while
leaving `returnWindowOnes` entirely unconstrained). -/

/-- The top-level implication record: entry surface → canonical surface. -/
def returnChargeResidual_of_windowOnesResidual (R : Erdos260WindowOnesResidual) :
    Erdos260ReturnChargeResidual :=
  R.toReturnCharge

/-- Nonempty transport, entry → canonical (one direction only — honest). -/
theorem nonempty_returnChargeResidual_of_windowOnes
    (h : Nonempty Erdos260WindowOnesResidual) : Nonempty Erdos260ReturnChargeResidual :=
  h.elim fun R => ⟨R.toReturnCharge⟩

/-! ## Part 4.  The fixed-family settlement re-exports (`FixedFamilyPeriodicity`)

The wave-13 fixed-family module is wired into the root through this import; its
erdos260-relevant conditional routes are re-exported here under capstone-local names, and the
dead-bridge / no-free-lunch records are listed in the status and audited below. -/

/-- Re-export: under the E.6/E.7 clean continuation (`DeepFixedFamilyCleanContinuation`) ALL
FIVE fixed families `(3,1), (21,3), (15,1), (15,2), (105,7)` are void at EVERY actual
context (deep scales by the section-24 floor, shallow scales by the wave-6/8 rigidity). -/
theorem windowOnesCapstone_fixedFamilyVoid_route
    (h : DeepFixedFamilyCleanContinuation) (ctx : ActualFailureContext) :
    ¬ FixedFamilyHit ctx :=
  fixedFamilyHit_void_of_cleanContinuation h ctx

/-- Re-export (no free lunch): the clean-continuation supply Prop is EQUIVALENT to the
voiding it feeds — it is the exact manuscript-language form of the residual, not a cheaper
waypoint. -/
theorem windowOnesCapstone_cleanContinuation_iff_void :
    DeepFixedFamilyCleanContinuation ↔ DeepFixedFamilyVoid :=
  deepFixedFamilyCleanContinuation_iff_void

/-- Re-export (no free lunch): the two supply Props (clean continuation / window
periodicity) have identical strength. -/
theorem windowOnesCapstone_cleanContinuation_iff_windowPeriodicity :
    DeepFixedFamilyCleanContinuation ↔ DeepFixedFamilyWindowPeriodicity :=
  deepFixedFamilyCleanContinuation_iff_windowPeriodicity

/-! ## Part 5.  Machine-readable status (honest) -/

/-- Honest machine-readable status of the window-ones capstone (the wave-13 fold). -/
def erdos260WindowOnesCapstoneStatus : List String :=
  [ "SURFACES (two, both kept - honest): Erdos260ReturnChargeResidual " ++
      "(Erdos260ChargeCapstone, 13 fields, the parity-free envelope field) is THE CANONICAL " ++
      "WEAKEST capstone surface; Erdos260WindowOnesResidual (this module, 13 fields, 12 " ++
      "verbatim) is THE SUFFICIENT ENTRY - the envelope field replaced by " ++
      "returnWindowOnesAtom : ReturnWindowOnesField, the DirtySliceEnvelope atom " ++
      "ReturnWindowOnesBound (|returnWindowOnes| + 1 <= liftLevelBound X, pure sub-shell " ++
      "raw-support counting, no slice/key/carry content) under the VERBATIM envelope-field " ++
      "guards, parity-free.  Mirrors the runSplitOfNumeric entry pattern.",
    "DIRECTION OF STRENGTH (honest - this is NOT a weakening): ReturnWindowOnesBound " ++
      "IMPLIES SliceDirtyEnvelope on ALL slices (sliceDirtyEnvelope_of_windowOnesBound, via " ++
      "the gap-one count sliceCard_le_windowOnes_succ), so the entry surface demands " ++
      "STRICTLY MORE than the canonical surface.  Implication record one-directional: " ++
      "returnChargeResidual_of_windowOnesResidual / " ++
      "nonempty_returnChargeResidual_of_windowOnes.  NO CONVERSE is provided or claimed: " ++
      "the envelope bounds slice cardinalities while the atom bounds raw window support - " ++
      "an envelope provider (e.g. key injectivity, which forces singleton slices via " ++
      "sliceDirtyEnvelope_of_keyInjOn) leaves returnWindowOnes unconstrained.  No formal " ++
      "independence proof is claimed either (that would need a model construction).",
    "ENTRY ENDPOINT: erdos260_of_windowOnesResidual (R : Erdos260WindowOnesResidual) : " ++
      "Erdos260Statement - public bridges only: returnDirtyEnvelopeField_of_windowOnesField " ++
      "(the parity-free field discharge, composed here - CHECKED: it did not exist in tree; " ++
      "DirtySliceEnvelope ships only the Q-odd-target form " ++
      "dirtyEnvelopeQOddField_of_windowOnesBound) -> toReturnCharge -> " ++
      "erdos260_of_returnChargeResidual (the canonical charge endpoint, junction-spliced " ++
      "ctx-pinned P9 ledger).  Q-odd named target also discharged: " ++
      "dirtyEnvelopeQOddField_of_windowOnesField via the charge capstone's " ++
      "dirtyEnvelopeQOddField_of_envelopeField.  Guard complementarity: window-cleanliness " ++
      "makes the atom free (returnWindowOnesBound_of_indexWindowClean), matching the " ++
      "not-ReturnIndexWindowClean gate; support-form entry " ++
      "returnWindowOnesField_of_lowScaleSupport (LowScaleSupportBound implies the atom).",
    "THE ATOM AND ITS CONVERGENCE: ReturnWindowOnesBound is strictly about sub-shell raw " ++
      "support at the low scale F + W (lowScaleCeiling); it demands supportCount(F+W) <= L " ++
      "in the support form (lowScaleSupportBound_forces_le_depth), pinned EXACTLY to the " ++
      "carry-rigidity floor L if the ceiling reaches X " ++
      "(lowScaleSupportBound_tight_of_ceiling_ge).  This CONVERGES with the wave-12 " ++
      "multi-scale onset gap (MultiScaleRigidity: the sparsity-onset bound <= 493443 from " ++
      "the hlarge/startThreshold data): both lanes demand control of raw support BELOW the " ++
      "failing shell scale - the project's deepest single open point, now reachable from " ++
      "TWO independent lanes (the Return window-ones lane and the multi-scale sibling " ++
      "lane).",
    "FIXED-FAMILY SETTLEMENT RE-EXPORTS (FixedFamilyPeriodicity, wired into the root " ++
      "through this module's import): (a) the conditional voiding chain - " ++
      "windowPeriodic_of_cleanContinuation -> " ++
      "deepFixedFamilyWindowPeriodicity_of_cleanContinuation -> " ++
      "fixedFamilyHit_void_of_cleanContinuation (ALL FIVE families void at every scale; " ++
      "re-export windowOnesCapstone_fixedFamilyVoid_route) + per-family voidings + the " ++
      "collapsed surfaces towerEscapeLever_of_cleanContinuation / " ++
      "towerFixedPointResidual_of_cleanContinuation; (b) THE DEAD ZERO-RUN BRIDGE - the " ++
      "wave-2..5 conditional hit/orbit bridge hypothesis is EMPTY at every actual context: " ++
      "eventuallyZero_of_gapOrbit_zeroRun (the canonical-gap intervals tile the ray, so the " ++
      "zero-run forces termination), actual_zeroRun_void / carry_tracks_hzero_void / " ++
      "classOneDatum_zeroRun_void (refuted against ctx.hnonterm); (c) THE NO-FREE-LUNCH " ++
      "EQUIVALENCES - deepFixedFamilyCleanContinuation_iff_void (re-export " ++
      "windowOnesCapstone_cleanContinuation_iff_void), " ++
      "deepFixedFamilyWindowPeriodicity_iff_void, " ++
      "deepFixedFamilyCleanContinuation_iff_windowPeriodicity (the supply equals the " ++
      "voiding); (d) the proved word side - hitSequence_AP_of_const_gaps / " ++
      "digit_periodic_of_const_gaps (constant hit gaps force exact periodicity) and the " ++
      "orbit APs at all five data (gapOrbit_three_one .. gapOrbit_oneOhFive_seven).",
    "WHAT REMAINS OPEN (the sharpest set after wave 13): (1) ReturnWindowOnesBound / the " ++
      "sparsity-onset bound - ONE support-side atom, TWO consumers (this entry endpoint and " ++
      "the multi-scale sibling route); (2) the E.6 hit-to-hit carry analysis at the five " ++
      "fixed data (FixedFamilyCleanContinuation: R_{a(k+1)} = 2^{hitGap} R_{a k} - Q*a(k+1) " ++
      "forcing the next gap to the canonical band while the recurrence persists - the full " ++
      "Appendix-E machinery, no in-tree lemma performs it); (3) key-injectivity counting at " ++
      "the enumerated survivors (ReturnKeyInjectiveField remains the sharpest Q-odd " ++
      "returnZero form on the predecessor surfaces); (4) the per-pair aperiodic tails and " ++
      "the modulus tails (towerEnumTail / runNumericTail / class0BigOrder / class1DeepTail " ++
      "verbatim).  Plus the unchanged non-Return lanes and the returnGates/returnInterior " ++
      "count-and-boundary fields.",
    "HYGIENE: additive only - no existing module edited (the root import file gains one " ++
      "line; DirtySliceEnvelope and FixedFamilyPeriodicity enter the root closure through " ++
      "this module's imports); no sorry / admit / new axiom / native_decide; all " ++
      "#print axioms in [propext, Classical.choice, Quot.sound] or fewer." ]

theorem erdos260WindowOnesCapstoneStatus_nonempty :
    erdos260WindowOnesCapstoneStatus ≠ [] := by
  simp [erdos260WindowOnesCapstoneStatus]

/-! ## Part 6.  Axiom-cleanliness audit -/

#print axioms ReturnWindowOnesField
#print axioms returnWindowOnesField_of_forall
#print axioms returnWindowOnesField_of_lowScaleSupport
#print axioms returnDirtyEnvelopeField_of_windowOnesField
#print axioms dirtyEnvelopeQOddField_of_windowOnesField
#print axioms Erdos260WindowOnesResidual.toReturnCharge
#print axioms Erdos260WindowOnesResidual.toStatement
#print axioms erdos260_of_windowOnesResidual
#print axioms returnChargeResidual_of_windowOnesResidual
#print axioms nonempty_returnChargeResidual_of_windowOnes
#print axioms windowOnesCapstone_fixedFamilyVoid_route
#print axioms windowOnesCapstone_cleanContinuation_iff_void
#print axioms windowOnesCapstone_cleanContinuation_iff_windowPeriodicity
#print axioms erdos260_of_returnChargeResidual
#print axioms sliceDirtyEnvelope_of_windowOnesBound
#print axioms sliceCard_le_windowOnes_succ
#print axioms returnWindowOnesBound_of_indexWindowClean
#print axioms eventuallyZero_of_gapOrbit_zeroRun
#print axioms actual_zeroRun_void
#print axioms carry_tracks_hzero_void
#print axioms classOneDatum_zeroRun_void
#print axioms fixedFamilyHit_void_of_cleanContinuation
#print axioms deepFixedFamilyWindowPeriodicity_iff_void
#print axioms deepFixedFamilyCleanContinuation_iff_void
#print axioms deepFixedFamilyCleanContinuation_iff_windowPeriodicity
#print axioms erdos260WindowOnesCapstoneStatus_nonempty

end

end Erdos260
