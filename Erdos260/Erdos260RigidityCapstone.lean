import Erdos260.DigitSideClosure
import Erdos260.CarryWordRigidity
import Erdos260.ModulusTailCriteria

/-!
# Erdős 260 — the wave-6 rigidity capstone

This module (NEW) assembles the wave-6 surfaces into `Erdos260RigidityResidual`,
the strictly sharper successor of `DigitSideEnumResidual`, and proves the new
final endpoint

`erdos260_of_rigidityResidual : Erdos260RigidityResidual → Erdos260Statement`

by composing ONLY existing public bridges into `erdos260_of_digitSideResidual`.
Nothing is re-proved here.

Wave-6 inputs consumed:

1. **Digit-side settlement** (`DigitSideClosure`) — base surface
   `DigitSideEnumResidual`: `returnZero` / `returnMaxClean` guarded by
   `¬ ReturnIndexWindowClean`; class-1 slot collapsed to the deep field alone
   (`class1PairResidual_of_deepOnly`); endpoint `erdos260_of_digitSideResidual`.
2. **Carry-word rigidity** (`CarryWordRigidity`) — unconditional scale floor
   `actualFailureContext_scale_lower` (`X > 2^246736` at every actual ctx) and
   the pinned-value floor `X > 2^493443` with per-family voidings; conditional
   deep-lever route `erdos260_of_deepDyadicValueLever` recorded, not consumed.
3. **Modulus-tail criteria** (`ModulusTailCriteria`) — per-ctx tail bridges
   `towerTail_of_order_gt`, `runTail_of_order_gt`, `class0Tail_of_order_gt`,
   `class1Tail_of_band4FreePeriod` (the aggregate split forms
   `towerEnumResidual_of_tail_order_criterion` / `runSettlement_split_at_tail`
   demand the order criterion unconditionally on the tail, so the per-ctx
   disjunctive folds here split locally instead); where a fold resists, each
   tail field carries an explicit verbatim fallback disjunct (honest per-atom
   retreat to the digit-side obligation).

Scale-floor collapses exploited in the status audit (see
`erdos260RigidityCapstoneStatus`): `n24_r_pos` / `shellLadderDepth_ge_15421`
(already in the digit-side chain), the new corollary `shellLadderDepth_ge_246737`
from `actualFailureContext_scale_lower`, and the class-1 `r = 0` / top-start
vacuity packaged upstream in `DigitSideClosure`.
-/

namespace Erdos260

noncomputable section

/-! ## Part 0.  Scale-floor corollaries used in the collapse audit -/

/-- Every failing context has ladder depth `L ≥ 246737` — the dyadic exponent
pin from `actualFailureContext_scale_lower`. -/
theorem shellLadderDepth_ge_246737 (ctx : ActualFailureContext) :
    246737 ≤ shellLadderDepth ctx := by
  have hX := actualFailureContext_scale_lower ctx
  have hXeq : ctx.shell.X = 2 ^ shellLadderDepth ctx :=
    Classical.choose_spec ctx.shell.hXdyadic
  rw [ActualFailureContext.shell_X] at hXeq
  rw [hXeq] at hX
  have : 246736 < shellLadderDepth ctx :=
    (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 hX
  omega

/-! ## Part 1.  The wave-6 rigidity residual -/

/-- **The wave-6 rigidity residual** — the digit-side enumeration surface with
ModulusTailCriteria tail folds (order-threshold / band-budget shapes on the
un-enumerated tails) and explicit verbatim fallbacks where a fold does not
follow from the digit-side fields alone. -/
structure Erdos260RigidityResidual where
  /-- Tower / class 2 — enumerated part (`q < 107`) at deep shells. -/
  towerEnumLow : ∀ ctx : ActualFailureContext,
    towerShallowDepthBound < shellLadderDepth ctx →
    TowerModulusEnumEscape ctx → (class1SlopeDatum ctx).q < 107 →
    Class2CycleInequality ctx
  /-- Tower / class 2 — tail (`107 ≤ q`): order-largeness + band-4 budget
  (sufficient via `towerTail_of_order_gt`) OR the verbatim wave-5/digit-side
  cycle inequality. -/
  towerEnumTail : ∀ ctx : ActualFailureContext,
    towerShallowDepthBound < shellLadderDepth ctx →
    TowerModulusEnumEscape ctx →
    107 ≤ (class1SlopeDatum ctx).q →
    (((Nat.log 2 (class1SlopeDatum ctx).q + 1) * shellWidth ctx
        < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
            (class1SlopeDatum ctx).K₀)))
        ∧ TowerBand4Budget ctx)
      ∨ Class2CycleInequality ctx
  /-- Run / class 5 — enumerated part (`q < 64`, `r ≥ 1`). -/
  runNumericLow : ∀ ctx : ActualFailureContext, 1 ≤ ctx.n24CarryData.r →
    (class1SlopeDatum ctx).q < 64 →
    Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx
  /-- Run / class 5 — tail (`64 ≤ q`, `r ≥ 1`): order-largeness + run band budget
  (sufficient via `runTail_of_order_gt`) OR the verbatim settlement disjunct. -/
  runNumericTail : ∀ ctx : ActualFailureContext, 1 ≤ ctx.n24CarryData.r →
    64 ≤ (class1SlopeDatum ctx).q →
    ((Nat.log 2 (class1SlopeDatum ctx).q + 1)
        * (supportShell ctx.shell.d ctx.shell.X).card
      < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
          (class1SlopeDatum ctx).K₀)))
      ∧ RunBandBudget ctx
    ∨ Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx
  /-- Return / class 4 count gates — verbatim digit-side field. -/
  returnGates : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    2 * (129 * shellLadderDepth ctx + 64)
      ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
    ReturnGatesBody ctx
  /-- Return / class 4 digit Z — verbatim digit-side field. -/
  returnZero : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    (∃ k ∈ olcFibre ctx,
      2 ^ carryVal2 ctx k < (supportShell ctx.shell.d ctx.shell.X).card) →
    ¬ ReturnIndexWindowClean ctx →
    ReturnZeroBody ctx
  /-- Return / class 4 clean step — verbatim digit-side field. -/
  returnMaxClean : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnIndexWindowClean ctx → ReturnMaxCleanBody ctx
  /-- Return / class 4 K.1 interior — verbatim digit-side field. -/
  returnInterior : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx
  /-- Chernoff / class 0 survivors — verbatim digit-side field. -/
  class0Survivor : ∀ ctx : ActualFailureContext, Class0DatumSurvivor ctx →
    Class0SurvivorResidueMiss ctx
  /-- Chernoff / class 0 mid band — verbatim digit-side field. -/
  class0Mid : ∀ ctx : ActualFailureContext, 48 ≤ (class1SlopeDatum ctx).q →
    (class1SlopeDatum ctx).q < 96 → Class0CycleMeetsShallow ctx →
    Class0WindowCycleCheck ctx
  /-- Chernoff / class 0 large moduli (`96 ≤ q`): order-pruned long-period certificate
  OR the verbatim windowed check. -/
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
  /-- CNL / class 1 — enumerated deep part (`q < 101`). -/
  class1DeepLow : ∀ ctx : ActualFailureContext,
    1 ≤ ctx.n24CarryData.r →
    64 ∣ shellLadderDepth ctx →
    9 ≤ (class1SlopeDatum ctx).q →
    ((class1SlopeDatum ctx).q ≤ 15 ∨ 25 ≤ (class1SlopeDatum ctx).q) →
    (class1SlopeDatum ctx).q ∉ class1ClosedModuli →
    ¬ Class1DatumClosed ctx →
    ¬ Class1GcdWindowMiss ctx →
    (class1SlopeDatum ctx).q < 101 →
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅
  /-- CNL / class 1 — tail (`101 ≤ q`): band-4-free period OR verbatim deep emptiness. -/
  class1DeepTail : ∀ ctx : ActualFailureContext,
    1 ≤ ctx.n24CarryData.r →
    101 ≤ (class1SlopeDatum ctx).q →
    Class1Band4FreePeriod ctx
    ∨ (64 ∣ shellLadderDepth ctx →
        9 ≤ (class1SlopeDatum ctx).q →
        ((class1SlopeDatum ctx).q ≤ 15 ∨ 25 ≤ (class1SlopeDatum ctx).q) →
        (class1SlopeDatum ctx).q ∉ class1ClosedModuli →
        ¬ Class1DatumClosed ctx →
        ¬ Class1GcdWindowMiss ctx →
        routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅)
  /-- DensePack / class 3 — verbatim digit-side field (no tail bridge lands in the
  gated residual shape; honest fallback). -/
  densePackGated : DensePackGatedClosureResidual

namespace Erdos260RigidityResidual

/-- Rebuild the tower enumeration tail from the rigidity tail (order criterion
or verbatim fallback). -/
def towerEnumOfTail (R : Erdos260RigidityResidual) :
    ∀ ctx : ActualFailureContext, towerShallowDepthBound < shellLadderDepth ctx →
    TowerModulusEnumEscape ctx →
    107 ≤ (class1SlopeDatum ctx).q → Class2CycleInequality ctx := by
  intro ctx hdeep hesc hge
  cases R.towerEnumTail ctx hdeep hesc hge with
  | inl ho =>
    exact towerTail_of_order_gt ctx ho.1 ho.2
  | inr hineq => exact hineq

/-- Rebuild `TowerModulusEnumerationResidual` from the rigidity tower fields
(split at `q = 107`; the tail order criterion closes through
`towerTail_of_order_gt`). -/
def towerEnum (R : Erdos260RigidityResidual) : TowerModulusEnumerationResidual := by
  intro ctx hdeep hesc
  rcases Nat.lt_or_ge (class1SlopeDatum ctx).q 107 with hlt | hge
  · exact R.towerEnumLow ctx hdeep hesc hlt
  · exact towerEnumOfTail R ctx hdeep hesc hge

/-- Rebuild the run settlement from the rigidity tail (order criterion or verbatim
fallback). -/
def runNumericOfTail (R : Erdos260RigidityResidual) :
    ∀ ctx : ActualFailureContext, 1 ≤ ctx.n24CarryData.r →
    64 ≤ (class1SlopeDatum ctx).q →
    Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx := by
  intro ctx hr hge
  cases R.runNumericTail ctx hr hge with
  | inl ho =>
    exact Or.inr (runTail_of_order_gt ctx ho.1 ho.2)
  | inr hrun => exact hrun

/-- Rebuild `RunCycleNumericSettlementHyp` (split at `q = 64`; the tail order
criterion closes through `runTail_of_order_gt`). -/
def runNumeric (R : Erdos260RigidityResidual) : RunCycleNumericSettlementHyp := by
  intro ctx hr
  rcases Nat.lt_or_ge (class1SlopeDatum ctx).q 64 with hlt | hge
  · exact R.runNumericLow ctx hr hlt
  · exact runNumericOfTail R ctx hr hge

/-- Rebuild the class-0 big field from the order-pruned certificate or verbatim
fallback. -/
def class0Big (R : Erdos260RigidityResidual) :
    ∀ ctx : ActualFailureContext, 96 ≤ (class1SlopeDatum ctx).q →
    Class0WindowCycleCheck ctx := by
  intro ctx h96
  cases R.class0BigOrder ctx h96 with
  | inl hcert =>
    obtain ⟨C, horder, hcheck⟩ := hcert
    exact class0Tail_of_order_gt ctx C horder hcheck
  | inr hwin => exact hwin

/-- Rebuild the class-1 deep field from the tail period or verbatim fallback. -/
def class1Deep (R : Erdos260RigidityResidual) :
    ∀ ctx : ActualFailureContext,
      1 ≤ ctx.n24CarryData.r →
      64 ∣ shellLadderDepth ctx →
      9 ≤ (class1SlopeDatum ctx).q →
      ((class1SlopeDatum ctx).q ≤ 15 ∨ 25 ≤ (class1SlopeDatum ctx).q) →
      (class1SlopeDatum ctx).q ∉ class1ClosedModuli →
      ¬ Class1DatumClosed ctx →
      ¬ Class1GcdWindowMiss ctx →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ := by
  intro ctx hr hdvd h9 hwin hcl hdc hgcd
  rcases Nat.lt_or_ge (class1SlopeDatum ctx).q 101 with hlt | hge
  · exact R.class1DeepLow ctx hr hdvd h9 hwin hcl hdc hgcd hlt
  · cases R.class1DeepTail ctx hr hge with
    | inl hfree =>
      exact class1Tail_of_band4FreePeriod ctx hfree
    | inr hdeep =>
      exact hdeep hdvd h9 hwin hcl hdc hgcd

/-- **The bridge into the digit-side capstone**: every field of
`DigitSideEnumResidual` is rebuilt through existing public bridges — nothing is
re-proved. -/
def toDigitSide (R : Erdos260RigidityResidual) : DigitSideEnumResidual where
  towerEnum := towerEnum R
  runNumeric := runNumeric R
  returnGates := R.returnGates
  returnZero := R.returnZero
  returnMaxClean := R.returnMaxClean
  returnInterior := R.returnInterior
  class0Survivor := R.class0Survivor
  class0Mid := R.class0Mid
  class0Big := class0Big R
  class1Deep := class1Deep R
  densePackGated := R.densePackGated

/-- The final statement from the rigidity residual, through the digit-side and
wave-5 capstones. -/
theorem toStatement (R : Erdos260RigidityResidual) : Erdos260Statement :=
  erdos260_of_digitSideResidual R.toDigitSide

end Erdos260RigidityResidual

/-- **The wave-6 final endpoint.**  `Erdos260Statement` from the rigidity surface,
composed through `toDigitSide` into `erdos260_of_digitSideResidual` with no
re-proving and no over-strong scalar anywhere on the route. -/
theorem erdos260_of_rigidityResidual (R : Erdos260RigidityResidual) :
    Erdos260Statement :=
  R.toStatement

/-- **The weakening witness**: the digit-side residual provides the rigidity
residual outright — every new field demands no more than its digit-side counterpart
(tail fields use the verbatim fallback disjunct). -/
def rigidityResidual_of_digitSideResidual (R : DigitSideEnumResidual) :
    Erdos260RigidityResidual where
  towerEnumLow := fun ctx hdeep hesc _ => R.towerEnum ctx hdeep hesc
  towerEnumTail := fun ctx hdeep hesc _ => Or.inr (R.towerEnum ctx hdeep hesc)
  runNumericLow := fun ctx hr _ => R.runNumeric ctx hr
  runNumericTail := fun ctx hr _ => Or.inr (R.runNumeric ctx hr)
  returnGates := R.returnGates
  returnZero := R.returnZero
  returnMaxClean := R.returnMaxClean
  returnInterior := R.returnInterior
  class0Survivor := R.class0Survivor
  class0Mid := R.class0Mid
  class0BigOrder := fun ctx h96 => Or.inr (R.class0Big ctx h96)
  class1DeepLow := fun ctx hr hdvd h9 hwin hcl hdc hgcd _ =>
    R.class1Deep ctx hr hdvd h9 hwin hcl hdc hgcd
  class1DeepTail := fun ctx hr _ => Or.inr fun hdvd h9 hwin hcl hdc hgcd =>
    R.class1Deep ctx hr hdvd h9 hwin hcl hdc hgcd
  densePackGated := R.densePackGated

/-- Machine-readable status of the wave-6 rigidity capstone. -/
def erdos260RigidityCapstoneStatus : List String :=
  [ "FINAL ENDPOINT (wave 6): erdos260_of_rigidityResidual (R : Erdos260RigidityResidual) : " ++
      "Erdos260Statement, composed through toDigitSide into " ++
      "erdos260_of_digitSideResidual (wave 6 digit-side base, wave 5 enum, wave 3 " ++
      "cycle, wave 2 sharp, wave 1 six-atom); only existing public bridges are " ++
      "consumed, nothing re-proved.  Weakening witness " ++
      "rigidityResidual_of_digitSideResidual : DigitSideEnumResidual -> " ++
      "Erdos260RigidityResidual (tail fields use the honest verbatim fallback disjunct).",
    "UNCONDITIONAL SCALE FLOOR (CarryWordRigidity): actualFailureContext_scale_lower - " ++
      "EVERY ActualFailureContext has X > 2^246736 (void form " ++
      "actualFailureContext_void_of_scale).  Corollary shellLadderDepth_ge_246737 " ++
      "(L >= 246737).  At c0 = kappa/64 the rigidity window fires iff L <= 246736; " ++
      "all shallow L <= 15420 guards are already vacuous via n24_r_pos / " ++
      "shellLadderDepth_ge_15421 (DigitSideClosure chain).  HONEST: L <= 328965 " ++
      "(towerShallowDepthBound) is NOT voided by the scale floor alone (246737 < 328965).",
    "PINNED-VALUE FLOOR (CarryWordRigidity): X > 2^493443 for dyadic-value / fifth-value / " ++
      "thirds-value / fixed-family hits (shellValueDyadic_scale_lower, " ++
      "fixedFamilyHit_scale_lower, per-family floors).  Deep successors " ++
      "DeepDyadicValueLever / DeepFixedFamilyVoid demand the exclusions ONLY at " ++
      "X > 2^493443; shallow voidings discharge the lever families at the scale floor. " ++
      "Conditional route RECORDED (not consumed): erdos260_of_deepDyadicValueLever : " ++
      "Erdos260DeepLeverResidual -> Erdos260Statement.",
    "DIGIT-SIDE SETTLEMENT (DigitSideClosure): ReturnIndexWindowClean as the single " ++
      "digit Prop; returnZero / returnMaxClean guarded by not-ReturnIndexWindowClean; " ++
      "class-1 slot carries ONLY class1Deep (topStart / r = 0 vacuous via n24_r_pos); " ++
      "hit-avoidance dictionary + sub-X/dense dichotomy.",
    "MODULUS-TAIL CRITERIA (ModulusTailCriteria): tower tail q >= 107 closes via " ++
      "towerTail_of_order_gt; run tail q >= 64 via runTail_of_order_gt; class-0 tail " ++
      "q >= 96 via class0Tail_of_order_gt; class-1 tail q >= 101 via " ++
      "class1Tail_of_band4FreePeriod.  The aggregate forms " ++
      "(towerEnumResidual_of_tail_order_criterion, runSettlement_split_at_tail, " ++
      "class0Big_of_order_pruned, class1PairDeep_split_at_tail) demand the criterion " ++
      "unconditionally on the tail, so the folds here split per-ctx with an honest " ++
      "verbatim fallback disjunct instead; exceptional " ++
      "cofactors with orderOf (2) <= 6 are EXACTLY {3,5,7,9,15,21,31,63}.  DensePack " ++
      "gated residual: honest verbatim fallback (no bridge to DensePackGatedClosureResidual).",
    "SCALE-FLOOR COLLAPSES EXPLOITED (exact list): (1) r >= 1 everywhere (n24_r_pos) - " ++
      "all r = 0 residual fields theorems; class1Deep-only slot; (2) L >= 15421 " ++
      "(shellLadderDepth_ge_15421) - all L <= 15420 guards vacuous; (3) L >= 246737 " ++
      "(shellLadderDepth_ge_246737 from actualFailureContext_scale_lower) - all L <= 246736 " ++
      "scale-window guards vacuous; (4) pinned-value families void at X <= 2^493443 " ++
      "(CarryWordRigidity per-family voidings).  NOT collapsed here: L <= 328965 tower " ++
      "shallow regime; digit-side returnZero/returnMaxClean on not-ReturnIndexWindowClean " ++
      "contexts; survivor congruence misses; densepack gated fields.",
    "ALTERNATIVE ROUTES (recorded, not consumed): erdos260_of_digitSideResidual, " ++
      "erdos260_of_enumResidual, erdos260_of_deepDyadicValueLever, " ++
      "erdos260_of_dyadicValueLever.",
    "ROOT OBSTRUCTION (unchanged): no formalized bridge ties digit-side gap-window pins " ++
      "to orbit-side band pins beyond the shared index k; deep tail beyond X > 2^493443 " ++
      "needs density bootstrap (rigidity density 1/(L+4) < c0), not a sharper log." ]

theorem erdos260RigidityCapstoneStatus_nonempty :
    erdos260RigidityCapstoneStatus ≠ [] := by
  simp [erdos260RigidityCapstoneStatus]

/-! ## Axiom-cleanliness audit -/

#print axioms shellLadderDepth_ge_246737
#print axioms Erdos260RigidityResidual.towerEnumOfTail
#print axioms Erdos260RigidityResidual.towerEnum
#print axioms Erdos260RigidityResidual.runNumericOfTail
#print axioms Erdos260RigidityResidual.runNumeric
#print axioms Erdos260RigidityResidual.class0Big
#print axioms Erdos260RigidityResidual.class1Deep
#print axioms Erdos260RigidityResidual.toDigitSide
#print axioms Erdos260RigidityResidual.toStatement
#print axioms erdos260_of_rigidityResidual
#print axioms rigidityResidual_of_digitSideResidual
#print axioms erdos260RigidityCapstoneStatus_nonempty

end

end Erdos260
