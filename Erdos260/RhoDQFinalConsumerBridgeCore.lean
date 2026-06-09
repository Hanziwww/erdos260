import Mathlib
import Erdos260.RhoDQFrontierDischargeCore
import Erdos260.DensePackFirstStopOwnerCore

/-!
# Wiring the Q-dependent density floor into the final consumer surface

This module is a small bridge from the already-proved `rhoDQ q0 = 1/(4 q0)` density
atoms to the *actual* reduced/final consumer shapes.

The important audit point is that the V3 reduced endpoint does not consume
`manuscriptRhoD` directly.  Its relevant fields are:

* `Class2ActiveFloorCount ctx` for Tower class 2;
* `DensePackCoareaSupport budget ctx` for DensePack class 3.

Both are rate-abstract.  The pinned `manuscriptRhoD` uses remain in precursor
density builders (`matchedWindow_of_descentMatch`, `MatchedSemiperiodicWindow.hdens`,
`DescentCylinderMatchData.hdens`, `SingularSquareCertificate.hdens`, and the
`proofV4DensePackMinHits`/`Class2IndexSDR.ofSemiperiodicDensity` path).  The bridge
below packages the Q-correct replacements for the final surface without changing
`Constants.manuscriptRhoD`.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

namespace Erdos260

open Finset

noncomputable section

set_option linter.unusedVariables false

/-! ## 1. Tower: the `rhoDQ` SDR feeds the V3 `towerCount` field -/

/-- Any class-2 index SDR, in particular one built at the Q-correct rate `rhoDQ`,
feeds the final V3 Tower consumer field `Class2ActiveFloorCount`.

This is the explicit final-surface wiring:
`Class2IndexSDR -> Class2ShellSDR -> Class2OwnershipPacking -> Class2AreaPacking
-> Class2ActiveFloorCount`. -/
def Class2IndexSDR.toActiveFloorCount {ctx : ActualFailureContext}
    (S : Class2IndexSDR ctx) : Class2ActiveFloorCount ctx :=
  Class2ActiveFloorCount.ofAreaPacking
    (Class2AreaPacking.ofOwnershipPacking
      (Class2OwnershipPacking.ofShellSDR S.toShellSDR))

/-- The routed Tower slot obtained after wiring an index SDR into the final V3
`towerCount` consumer. -/
theorem Class2IndexSDR.toActiveFloorCount_towerSlot {ctx : ActualFailureContext}
    (S : Class2IndexSDR ctx) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
      ≤ erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  S.toActiveFloorCount.htowerSubMass

/-- The final V3 `towerCount` field built from the Q-correct dyadic-match SDR at
the actual shell denominator `q0 = (canonicalCenter ctx).q0`.

All density in the construction is at `rhoDQ (canonicalCenter ctx).q0`; the
remaining hypotheses are the genuine selection/landing, scalar calibration, and
boundary data already required by the parametric SDR path. -/
def Class2ActiveFloorCount.ofActualDyadicMatchesRhoDQ
    (ctx : ActualFailureContext)
    (a : ℕ → ℕ) (hainj : Function.Injective a)
    (eps : ℝ) (Lnat : ℕ) (hLpos : 0 < Lnat)
    (hYnn : 0 ≤ ctx.n24CarryData.Y)
    (hcalibE : 2 * ctx.n24CarryData.Y ≤ 2 * eps * (Lnat : ℝ))
    (huniform :
      2 * (erdos260Constants.c0 * eps)
        ≤ erdos260Constants.ξ / 6 * rhoDQ (canonicalCenter ctx).q0)
    (hbdry : 0 ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2)
    (lo mwin lenw cen : ℕ → ℕ)
    (hcop : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
        Nat.Coprime (cen k) (canonicalCenter ctx).q0)
    (hle : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
        orderOf (2 : ZMod (canonicalCenter ctx).q0) ≤ lenw k)
    (hlenL : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
        Lnat + orderOf (2 : ZMod (canonicalCenter ctx).q0) ≤ lenw k + 1)
    (hmatch : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
        WindowMatch ctx.shell.d (dyadicDigit (canonicalCenter ctx).q0 (cen k)) (mwin k) (lenw k))
    (hlands : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
        ∀ j ∈ Finset.Ico (lo k) (lo k + windowWeight ctx.shell.d (mwin k) (lenw k)),
          a j ∈ supportShell ctx.d ctx.X)
    (hdisj : ∀ j ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
        ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2, j ≠ k →
        Disjoint (Finset.Ico (lo j) (lo j + windowWeight ctx.shell.d (mwin j) (lenw j)))
          (Finset.Ico (lo k) (lo k + windowWeight ctx.shell.d (mwin k) (lenw k)))) :
    Class2ActiveFloorCount ctx :=
  (Class2IndexSDR.ofDyadicMatchesRhoDQ ctx a hainj (canonicalCenter ctx).q0
    (runFOfShell_q0_gt_one ctx) (runFOfShell_q0_odd ctx)
    eps Lnat hLpos hYnn hcalibE huniform hbdry lo mwin lenw cen hcop
    hle hlenL hmatch hlands hdisj).toActiveFloorCount

/-! ## 2. DensePack: final coarea support plus Q-correct density atoms -/

/-- The concrete DensePack final-consumer package, parameterized by the actual
descent-window witness `W`. -/
structure RhoDQDensePackFinalConsumerDataOf
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) (W : DescentWindowMatch ctx) where
  /-- The actual final V3 DensePack consumer field. -/
  support : DensePackCoareaSupport budget ctx
  /-- The `SingularSquareCertificate.hdens` / `DescentCylinderMatchData.hdens`
  shape, recalibrated to `rhoDQ`. -/
  certHdens : ∀ k ∈ genuineDensePackStarts ctx,
      rhoDQ (canonicalCenter ctx).q0 * (orderOf (2 : ZMod (canonicalCenter ctx).q0) : ℝ)
        ≤ (windowWeight (dyadicDigit (canonicalCenter ctx).q0 (W.a k)) 0
            (orderOf (2 : ZMod (canonicalCenter ctx).q0)) : ℝ)
  /-- The real `Class2AreaPacking.hcard`-shaped support floor at `rhoDQ`. -/
  supportRealFloor : ∀ k ∈ genuineDensePackStarts ctx,
      rhoDQ (canonicalCenter ctx).q0 * ((Classical.choose ctx.shell.hXdyadic : ℕ) : ℝ)
        ≤ ((proofV4DensePackSupportWindow ctx.shell (k + ctx.n24CarryData.r)).card : ℝ)
  /-- The floored K.1.1 coarea hit-density at `rhoDQ`, replacing the pinned
  `proofV4DensePackMinHits = floor(manuscriptRhoD * L)` precursor. -/
  endpointFloor : ∀ k ∈ genuineDensePackStarts ctx,
      Nat.floor (rhoDQ (canonicalCenter ctx).q0 *
          ((Classical.choose ctx.shell.hXdyadic : ℕ) : ℝ))
        ≤ (proofV4DensePackSupportWindow ctx.shell (k + ctx.n24CarryData.r)).card

/-- Build the DensePack final-consumer package from the endpoint landing
(`DensePackCoareaSupport`) and the Q-correct descent-window density discharge.

This does not pretend that a density inequality *is* the final coarea owner map:
`hlands` supplies the final coarea support, while `frontierDensityDischarge_rhoDQ`
supplies the Q-correct precursor atoms that replace the remaining pinned
`manuscriptRhoD` density floors. -/
def rhoDQDensePackFinalConsumerDataOf
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) (W : DescentWindowMatch ctx)
    (hcop : ∀ k ∈ genuineDensePackStarts ctx, Nat.Coprime (W.a k) (canonicalCenter ctx).q0)
    (hlo : ∀ k ∈ genuineDensePackStarts ctx, ctx.shell.X < k + ctx.n24CarryData.r)
    (hhi : ∀ k ∈ genuineDensePackStarts ctx,
        (k + ctx.n24CarryData.r) + proofV4DensePackSpread ctx.shell ≤ 2 * ctx.shell.X)
    (hpb : ∀ k ∈ genuineDensePackStarts ctx,
        Classical.choose ctx.shell.hXdyadic + orderOf (2 : ZMod (canonicalCenter ctx).q0)
          ≤ proofV4DensePackSpread ctx.shell + 2)
    (hlands : densePackLandsShift budget ctx) :
    RhoDQDensePackFinalConsumerDataOf budget ctx W where
  support := (DensePackCoareaFirstStop.ofLandsShift budget ctx hlands).toCoareaSupport
  certHdens := singularSquareCertificate_hdens_rhoDQ ctx W hcop
  supportRealFloor := densePackSupportFloor_rhoDQ_of_descentWindowMatch ctx W hcop hlo hhi hpb
  endpointFloor := densePackEndpointDensity_rhoDQ_of_descentWindowMatch ctx W hcop hlo hhi hpb

/-! ## 3. Compiled audit surface -/

/-- The precise residual audit after wiring `rhoDQ` into the final consumer shapes. -/
def rhoDQFinalConsumerBridgeResiduals : List String :=
  [ "FINAL TOWER CONSUMER WIRED — Class2IndexSDR.toActiveFloorCount and " ++
      "Class2ActiveFloorCount.ofActualDyadicMatchesRhoDQ feed the Q-correct SDR at " ++
      "rhoDQ (canonicalCenter ctx).q0 into the actual V3 towerCount field " ++
      "Class2ActiveFloorCount ctx. This passes through the existing SDR/ownership/area-packing chain.",
    "FINAL DENSEPACK CONSUMER IDENTIFIED — the V3 densePackSupport field is " ++
      "DensePackCoareaSupport budget ctx, a coarea owner/marker landing datum. It is rate-free and " ++
      "does not consume manuscriptRhoD. rhoDQDensePackFinalConsumerDataOf packages that final support " ++
      "field together with the Q-correct hdens/support-floor/floored-endpoint atoms.",
    "PINNED PRECURSOR CONSUMERS REMAIN — manuscriptRhoD is still consumed in the old precursor path: " ++
      "matchedWindow_of_descentMatch (hcal), MatchedSemiperiodicWindow.hdens, " ++
      "DescentCylinderMatchData.hdens, SingularSquareCertificate.hdens, " ++
      "proofV4DensePackMinHits = floor(manuscriptRhoD * L), and " ++
      "Class2IndexSDR.ofSemiperiodicDensity / Class2AreaPacking routes that are instantiated with " ++
      "the pinned constant.",
    "Q-CORRECT REPLACEMENTS PROVED — use singularSquareCertificate_hdens_rhoDQ, " ++
      "windowWeight_ge_rhoDQ_of_descentMatch, densePackSupportFloor_rhoDQ_of_descentWindowMatch, " ++
      "densePackEndpointDensity_rhoDQ_of_descentWindowMatch, frontierDensityDischarge_rhoDQ, and " ++
      "Class2ActiveFloorCount.ofActualDyadicMatchesRhoDQ for the final-surface bridge.",
    "GLOBAL CONSTANT UNCHANGED — Constants.manuscriptRhoD remains the Q = 1 pin. The new bridge is " ++
      "explicitly Q-dependent and honest for actual q0 = (canonicalCenter ctx).q0." ]

theorem rhoDQFinalConsumerBridgeResiduals_nonempty :
    rhoDQFinalConsumerBridgeResiduals ≠ [] := by
  simp [rhoDQFinalConsumerBridgeResiduals]

/-! ## 4. Axiom-cleanliness audit -/

#print axioms Class2IndexSDR.toActiveFloorCount
#print axioms Class2ActiveFloorCount.ofActualDyadicMatchesRhoDQ
#print axioms rhoDQDensePackFinalConsumerDataOf
#print axioms rhoDQFinalConsumerBridgeResiduals_nonempty

end

end Erdos260
