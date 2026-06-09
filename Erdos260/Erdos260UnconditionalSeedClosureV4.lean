import Erdos260.Erdos260UnconditionalSeedClosureV3
import Erdos260.RhoDQFrontierDischargeCore
import Erdos260.DescentDepthNoLargeRunCore
import Erdos260.SliceM31AnchoredReturnCore

/-!
# Erdos #260 -- wave-23/24 integration capstone (`SeedClosureV4`)

This module is an honest global wiring capstone over the already-compiled V3 endpoint.

The V3 endpoint remains the final theorem consumer: it carries the six broad matched-charge
class bundles required by `erdos260_of_minimalResidualV3`. The wave-23/24 cores proved sharper
frontier facts, but those names were not recorded at the global consumed surface. V4 fixes that
integration gap without pretending that the sharper facts derive all six V3 class bundles.

The V4 residual therefore:

* stores an explicit `Erdos260MinimalResidualV3`, used for the final theorem;
* records `UpperBandMatchSource ctx`, whose descent-window match, coprimality, and depth fields derive
  `UpperBandMatchData ctx`;
* records the raw M.2.1/M.3.1 anchored long-return existence on the V3 return slices, which derives
  the survivor-family residual and then discharges `CleanReturnPlacement` and `SliceCompleteReturns`;
* records the small geometric inputs needed to run `frontierDensityDischarge_rhoDQ`, making the
  Q-correct density atoms globally visible.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

namespace Erdos260

open Finset

noncomputable section

set_option linter.unusedVariables false

/-! ## 1. Upper-band data discharges the descent-window match -/

/-- Build `DescentWindowMatch` from the wave-24 upper residue-band package.

The numerator is the upper-band floor witness `upperBandCenter`. The residue bound is
`upperBandCenter_lt`; the digit agreement is `matchesCompletion_upperBandCenter`. -/
def DescentWindowMatch.ofUpperBandData {ctx : ActualFailureContext}
    (D : UpperBandMatchData ctx) : DescentWindowMatch ctx where
  a := upperBandCenter ctx
  ha := fun k hk => upperBandCenter_lt ctx (D.hband k hk)
  hmatch := fun k hk => matchesCompletion_upperBandCenter ctx (D.hband k hk)

/-- The upper-band package also gives the older named match residual. -/
def UpperBandMatchData.toDescentWindowMatch {ctx : ActualFailureContext}
    (D : UpperBandMatchData ctx) : DescentWindowMatch ctx :=
  DescentWindowMatch.ofUpperBandData D

/-! ## 2. The honest V4 residual surface -/

/-- The wave-23/24 global capstone residual.

This is intentionally not a fake replacement for `Erdos260MinimalResidualV3`: V3 remains an
explicit field. The additional fields record the sharper closures at the global surface and
provide projection lemmas below for the concrete subgoals they discharge. -/
structure Erdos260MinimalResidualV4 where
  /-- The actual final-theorem consumer surface from V3. -/
  toV3 : Erdos260MinimalResidualV3
  /-- Sharper §25.3 source data for the upper-band route: a descent-window match plus coprimality,
  small-denominator depth, and the carried density/calibration fields. -/
  upperBandSource : forall ctx : ActualFailureContext, UpperBandMatchSource ctx
  /-- Lower containment of the genuine descent windows in the shell support interval. -/
  denseWindowLo : forall ctx : ActualFailureContext,
    forall k, Membership.mem (genuineDensePackStarts ctx) k -> ctx.shell.X < k + ctx.n24CarryData.r
  /-- Upper containment of the genuine descent windows in the shell support interval. -/
  denseWindowHi : forall ctx : ActualFailureContext,
    forall k, Membership.mem (genuineDensePackStarts ctx) k ->
      (k + ctx.n24CarryData.r) + proofV4DensePackSpread ctx.shell <= 2 * ctx.shell.X
  /-- Wave-25 raw M.2.1/M.3.1 anchored long-return existence on the V3 return slices.

  This is strictly below the survivor-family packaging: the four-coordinate core containment carried
  by `AnchoredSurvivorFamily.anchored_patch` is derived from the long-return endpoint pinning and
  longness fields in `AnchoredLongReturnFamily`. -/
  anchoredLongReturnFamily : forall ctx : ActualFailureContext,
    forall y, Membership.mem ((olcFibre ctx).image (toV3.returnCharge ctx).key) y ->
      Nonempty (AnchoredLongReturnFamily ctx (toV3.returnCharge ctx).key y)

namespace Erdos260MinimalResidualV4

/-- V4 projects honestly to the V3 residual required by the existing endpoint. -/
def toMinimalResidualV3 (R : Erdos260MinimalResidualV4) : Erdos260MinimalResidualV3 :=
  R.toV3

/-- The V3 budget carried by V4. -/
def budget (R : Erdos260MinimalResidualV4) :
    forall ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx :=
  R.toV3.budget

/-- Wave-24 upper-band membership discharges the concrete `DescentWindowMatch` residual. -/
def descentWindowMatch (R : Erdos260MinimalResidualV4) (ctx : ActualFailureContext) :
    DescentWindowMatch ctx :=
  (R.upperBandSource ctx).toUpperBandMatchData.toDescentWindowMatch

/-- The sharper §25.3 source record projects to the older upper-band package. -/
def upperBand (R : Erdos260MinimalResidualV4) (ctx : ActualFailureContext) :
    UpperBandMatchData ctx :=
  (R.upperBandSource ctx).toUpperBandMatchData

/-- Coprimality of the projected upper-band floor witnesses. -/
theorem upperBandCoprime (R : Erdos260MinimalResidualV4) (ctx : ActualFailureContext) :
    forall k, Membership.mem (genuineDensePackStarts ctx) k ->
      Nat.Coprime (upperBandCenter ctx k) (canonicalCenter ctx).q0 := by
  intro k hk
  rw [upperBandCenter_eq_of_descentWindowMatch ctx (R.upperBandSource ctx).W
    (R.upperBandSource ctx).hcop (R.upperBandSource ctx).hdepth k hk]
  exact (R.upperBandSource ctx).hcop k hk

/-- The same upper-band data discharges the older semiperiodic-window match surface. -/
theorem matchedDescentWindows (R : Erdos260MinimalResidualV4) (ctx : ActualFailureContext) :
    MatchedDescentWindows ctx :=
  (R.upperBand ctx).toMatchedDescentWindows

/-- The V4 descent package already supplies the DensePack endpoint-density input:
upper-band data gives matched descent windows, and the explicit V4 support-window
containment fields feed the K.1 coarea hit-density bridge. -/
theorem densePackEndpointDensity (R : Erdos260MinimalResidualV4) (ctx : ActualFailureContext) :
    densePackEndpointDensity ctx :=
  densePackEndpointDensity_of_matchedDescentWindows ctx
    (R.denseWindowLo ctx) (R.denseWindowHi ctx) (R.matchedDescentWindows ctx)

/-- The same upper-band data discharges the section-25.1 cylinder-match residual. -/
theorem section251CylinderMatch (R : Erdos260MinimalResidualV4) (ctx : ActualFailureContext) :
    Section251CylinderMatchResidual ctx :=
  (R.upperBand ctx).toSection251

/-- The upper-band data assembles the full singular-square certificate, including the carry exclusion. -/
def singularSquareCertificate (R : Erdos260MinimalResidualV4) (ctx : ActualFailureContext) :
    SingularSquareCertificate ctx :=
  (R.upperBand ctx).toSingularSquareCertificate

/-- The raw M.2.1/M.3.1 long-return existence derives the old survivor-family residual on each V3
return slice. -/
theorem survivorFamily (R : Erdos260MinimalResidualV4) (ctx : ActualFailureContext)
    {y : Nat} (hy : Membership.mem ((olcFibre ctx).image (R.toV3.returnCharge ctx).key) y) :
    Nonempty (AnchoredSurvivorFamily ctx (R.toV3.returnCharge ctx).key y) :=
  nonempty_survivorFamily_of_anchoredLongReturnFamily (R.anchoredLongReturnFamily ctx y hy)

/-- Wave-25 anchored long-return existence discharges `CleanReturnPlacement` on each V3 return slice. -/
theorem cleanReturnPlacement (R : Erdos260MinimalResidualV4) (ctx : ActualFailureContext)
    {y : Nat} (hy : Membership.mem ((olcFibre ctx).image (R.toV3.returnCharge ctx).key) y) :
    CleanReturnPlacement ctx (R.toV3.returnCharge ctx).key y :=
  cleanReturnPlacement_of_nonempty_anchoredLongReturnFamily (R.anchoredLongReturnFamily ctx y hy)

/-- Wave-25 anchored long-return existence also discharges `SliceCompleteReturns` on each V3 return
slice. -/
theorem sliceCompleteReturns (R : Erdos260MinimalResidualV4) (ctx : ActualFailureContext)
    {y : Nat} (hy : Membership.mem ((olcFibre ctx).image (R.toV3.returnCharge ctx).key) y) :
    SliceCompleteReturns ctx (R.toV3.returnCharge ctx).key y :=
  sliceCompleteReturns_of_nonempty_anchoredLongReturnFamily (R.anchoredLongReturnFamily ctx y hy)

/-- The V4 long-return witness exposes the concrete all-pairs zero digit-run `(Z)` on the V3 return
slice. -/
theorem zeroRunAllPairs (R : Erdos260MinimalResidualV4) (ctx : ActualFailureContext)
    {y : Nat} (hy : Membership.mem ((olcFibre ctx).image (R.toV3.returnCharge ctx).key) y) :
    ∀ x ∈ olcSlice ctx (R.toV3.returnCharge ctx).key y,
      ∀ z ∈ olcSlice ctx (R.toV3.returnCharge ctx).key y, x < z →
        ∀ j, x < j → j ≤ z → ctx.d j = 0 :=
  zeroRunAllPairs_of_completeReturns ctx (R.toV3.returnCharge ctx).key y
    (R.sliceCompleteReturns ctx hy)

/-- The V4 long-return witness supplies the M.2.1 per-slice `OlcSliceData` consumed by the Return
charge, once the standard shell bound and consecutive lift-gap divisibility are provided. -/
def olcSliceData (R : Erdos260MinimalResidualV4) (ctx : ActualFailureContext)
    {y : Nat} (hy : Membership.mem ((olcFibre ctx).image (R.toV3.returnCharge ctx).key) y)
    (hbound : ∀ k ∈ olcSlice ctx (R.toV3.returnCharge ctx).key y, carryVal2 ctx k ≤ ctx.shell.X)
    (hgap : ∀ x ∈ olcSlice ctx (R.toV3.returnCharge ctx).key y,
      ∀ z ∈ olcSlice ctx (R.toV3.returnCharge ctx).key y, x < z →
        (∀ c ∈ olcSlice ctx (R.toV3.returnCharge ctx).key y, x < c → z ≤ c) →
          2 ^ carryVal2 ctx x ∣ (z - x)) :
    OlcSliceData ctx (R.toV3.returnCharge ctx).key y :=
  OlcSliceData.ofAnchoredLongReturnFamily ctx (R.toV3.returnCharge ctx).key y hbound
    (Classical.choice (R.anchoredLongReturnFamily ctx y hy)) hgap

/-- The Q-correct frontier density atoms discharged from the upper-band descent match.

This is exactly `frontierDensityDischarge_rhoDQ`, with `DescentWindowMatch` supplied by the
upper-band route and the remaining containment/coprimality fields carried explicitly by V4. -/
theorem rhoDQFrontierDensity (R : Erdos260MinimalResidualV4) (ctx : ActualFailureContext) :
    And
      (forall k, Membership.mem (genuineDensePackStarts ctx) k ->
        rhoDQ (canonicalCenter ctx).q0 * (orderOf (2 : ZMod (canonicalCenter ctx).q0) : Real)
          <= (windowWeight (dyadicDigit (canonicalCenter ctx).q0 (upperBandCenter ctx k)) 0
              (orderOf (2 : ZMod (canonicalCenter ctx).q0)) : Real))
      (And
        (forall k, Membership.mem (genuineDensePackStarts ctx) k ->
          rhoDQ (canonicalCenter ctx).q0 * ((Classical.choose ctx.shell.hXdyadic : Nat) : Real)
            <= ((proofV4DensePackSupportWindow ctx.shell (k + ctx.n24CarryData.r)).card : Real))
        (forall k, Membership.mem (genuineDensePackStarts ctx) k ->
          Nat.floor (rhoDQ (canonicalCenter ctx).q0 *
            ((Classical.choose ctx.shell.hXdyadic : Nat) : Real))
            <= (proofV4DensePackSupportWindow ctx.shell (k + ctx.n24CarryData.r)).card)) :=
  frontierDensityDischarge_rhoDQ ctx (R.descentWindowMatch ctx)
    (fun k hk => R.upperBandCoprime ctx k hk)
    (R.denseWindowLo ctx)
    (R.denseWindowHi ctx)
    (fun _ _ => (R.upperBandSource ctx).hpb)

end Erdos260MinimalResidualV4

/-! ## 3. Final theorem from V4 -/

/-- Erdos #260 from the V4 capstone residual.

This final implication is an honest projection through V3. The new wave-23/24 fields reduce the
documented subgoals above, but V4 still carries the V3 class bundles explicitly. -/
theorem erdos260_of_minimalResidualV4 (R : Erdos260MinimalResidualV4) : Erdos260Statement :=
  erdos260_of_minimalResidualV3 R.toMinimalResidualV3

/-! ## 4. Residual inventory -/

/-- The exact remaining global residual surface after the V4 capstone. -/
def erdos260UnconditionalSeedClosureV4Residuals : List String :=
  [ "V4 is an honest capstone, not a full replacement for V3: it still carries toV3 : " ++
      "Erdos260MinimalResidualV3, so the final theorem uses erdos260_of_minimalResidualV3.",
    "REDUCED (descent depth) -- upperBandSource ctx : UpperBandMatchSource ctx. Its DescentWindowMatch " ++
      "+ coprimality + q0 <= 2^(spread+1) fields derive UpperBandMatchData via " ++
      "UpperBandMatchSource.toUpperBandMatchData; the derived package then yields MatchedDescentWindows, " ++
      "Section251CylinderMatchResidual, and SingularSquareCertificate.",
    "ADDED (return placement) -- anchoredLongReturnFamily on the V3 returnCharge key. For every V3 " ++
      "return slice, Nonempty (AnchoredLongReturnFamily ctx key y) derives the old survivor-family " ++
      "residual, with M.3.1 core containment proved from endpoint pinning + longness, and then yields " ++
      "CleanReturnPlacement and SliceCompleteReturns.",
    "ADDED (Q-correct density) -- upperBandSource.hcop, denseWindowLo, denseWindowHi, and " ++
      "upperBandSource.hpb feed frontierDensityDischarge_rhoDQ, exposing the cert hdens atom, the real " ++
      "support floor, and the floored coarea endpoint floor at rhoDQ (canonicalCenter ctx).q0.",
    "REMAINING V3 SURFACE -- towerCount, runChain, returnCharge, Chernoff matched area charge, CNL " ++
      "matched Kraft charge, and DensePack coarea support are still explicit V3 fields. V4 does not fake " ++
      "a derivation of those six bundles from hband or survivor-family existence." ]

theorem erdos260UnconditionalSeedClosureV4Residuals_nonempty :
    Not (erdos260UnconditionalSeedClosureV4Residuals = []) := by
  simp [erdos260UnconditionalSeedClosureV4Residuals]

/-! ## 5. Axiom-cleanliness audit -/

#print axioms DescentWindowMatch.ofUpperBandData
#print axioms UpperBandMatchData.toDescentWindowMatch
#print axioms UpperBandMatchSource.toUpperBandMatchData
#print axioms Erdos260MinimalResidualV4.descentWindowMatch
#print axioms Erdos260MinimalResidualV4.upperBand
#print axioms Erdos260MinimalResidualV4.upperBandCoprime
#print axioms Erdos260MinimalResidualV4.matchedDescentWindows
#print axioms Erdos260MinimalResidualV4.densePackEndpointDensity
#print axioms Erdos260MinimalResidualV4.section251CylinderMatch
#print axioms Erdos260MinimalResidualV4.singularSquareCertificate
#print axioms Erdos260MinimalResidualV4.survivorFamily
#print axioms Erdos260MinimalResidualV4.cleanReturnPlacement
#print axioms Erdos260MinimalResidualV4.sliceCompleteReturns
#print axioms Erdos260MinimalResidualV4.zeroRunAllPairs
#print axioms Erdos260MinimalResidualV4.olcSliceData
#print axioms Erdos260MinimalResidualV4.rhoDQFrontierDensity
#print axioms erdos260_of_minimalResidualV4

end

end Erdos260