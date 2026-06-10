import Erdos260.ActiveWindowContainmentCore
import Erdos260.ReturnInputUnconditional
import Erdos260.ReturnM21SliceChargeClosureCore

/-!
# Return per-slice V3 closure boundary

This module records the sharp bridge currently available for the V3 Return/Class 4
field

```
forall ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx
```

The factory-level Return atom is closed by `returnInputUnconditional`, but that atom
lives over `ctx.shell` and produces a `GenuineReturnShellInput ctx.shell`. It does
not contain the ctx-pinned slice key on `olcFibre ctx`, the per-slice
`OlcSliceData`, the active-window containment for the actual class-4 starts, or the
matched `M_L * X` numeric needed by `Class4ReturnPerSliceCharge`.

The genuine V3 bridge is therefore the anchored per-slice seed already isolated in
`ReturnM21SliceChargeClosureCore`: `ReturnClass4AnchoredSeed ctx`. It supplies the
M.3.1 anchored family, the M.2.1 carry-side slice data, active-window containment,
and numeric smallness on the same key, and it builds the V3 charge without any
all-zero or trivial witness.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

namespace Erdos260

open Finset

noncomputable section

/-- The closed factory-level Return input. This is intentionally recorded next to
the V3 bridge to make the type mismatch explicit: it is a per-shell factory input,
not a ctx-pinned per-slice charge over `olcFibre ctx`. -/
def class4ReturnFactoryInput_closed :
    forall ctx : ActualFailureContext, GenuineReturnShellInput ctx.shell :=
  returnInputUnconditional

/-! ## A narrowed anchored core surface

The full `ReturnClass4AnchoredSeed` already discharges the V3 charge once all of its
fields are available.  This smaller core records the parts that remain genuinely
ctx-pinned, while deriving the uniform active-window `windowReach/hReach/hContain`
from the same interior form used by the other matched-charge classes.
-/

/-- Uniform class-4 active-window reach: the maximal reach inside the shell window. -/
def returnWindowReach (ctx : ActualFailureContext) : ℕ :=
  densePackWindowReach ctx

/-- The class-4 reach lies inside the dyadic shell support. -/
theorem returnWindowReach_add_one_le (ctx : ActualFailureContext) :
    returnWindowReach ctx + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card := by
  simpa [returnWindowReach] using densePackWindowReach_add_one_le ctx

/-- Class-4 active-window containment from the clean interior condition. -/
theorem returnClass4Contain_ofInterior (ctx : ActualFailureContext)
    (hInterior : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4,
      k + ctx.n24CarryData.r + 1
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card) :
    ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4,
      k + ctx.n24CarryData.r
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + returnWindowReach ctx := by
  intro k hk
  have hint := hInterior k hk
  have hpos : 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card := one_le_width ctx
  show k + ctx.n24CarryData.r
      < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + densePackWindowReach ctx
  unfold densePackWindowReach
  omega

/-- The anchored Return core with active-window reach derived from class-4 interior.

Compared with `ReturnClass4AnchoredSeed`, this removes the explicit
`windowReach/hReach/hContain` fields.  The M.3.1 family also automatically gives
zero-runs and crossing-freeness on each slice; the remaining irreducible slice
inputs are the shell bound and the self-referential gap divisibility. -/
structure ReturnClass4AnchoredCore (ctx : ActualFailureContext) where
  key : ℕ → ℕ
  family : ∀ y ∈ (olcFibre ctx).image key, AnchoredLongReturnFamily ctx key y
  hbound : ∀ y ∈ (olcFibre ctx).image key,
    ∀ k ∈ olcSlice ctx key y, carryVal2 ctx k ≤ ctx.shell.X
  hgapDiv : ∀ y ∈ (olcFibre ctx).image key,
    ∀ x ∈ olcSlice ctx key y, ∀ z ∈ olcSlice ctx key y, x < z →
      (∀ c ∈ olcSlice ctx key y, x < c → z ≤ c) → 2 ^ carryVal2 ctx x ∣ (z - x)
  class4Interior : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4,
    k + ctx.n24CarryData.r + 1
      < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + (supportShell ctx.shell.d ctx.shell.X).card
  hnumeric : (((olcFibre ctx).image key).card : ℝ) * (liftLevelBound ctx.shell.X : ℝ)
      * returnDyadicMult ctx
    ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6

namespace ReturnClass4AnchoredCore

variable {ctx : ActualFailureContext}

/-- The M.3.1 anchored family gives the all-pairs clean zero-run on a slice. -/
theorem zeroRunAllPairs (S : ReturnClass4AnchoredCore ctx)
    {y : ℕ} (hy : y ∈ (olcFibre ctx).image S.key) :
    ∀ x ∈ olcSlice ctx S.key y, ∀ z ∈ olcSlice ctx S.key y, x < z →
      ∀ j, x < j → j ≤ z → ctx.d j = 0 :=
  zeroRunAllPairs_of_completeReturns ctx S.key y
    (sliceCompleteReturns_of_anchoredLongReturnFamily (S.family y hy))

/-- The M.3.1 anchored family gives carry-valuation crossing-freeness on each slice. -/
theorem carryVal2_crossingFree (S : ReturnClass4AnchoredCore ctx)
    {y : ℕ} (hy : y ∈ (olcFibre ctx).image S.key) :
    ∀ x ∈ olcSlice ctx S.key y, ∀ z ∈ olcSlice ctx S.key y, x < z →
      carryVal2 ctx x < carryVal2 ctx z :=
  fun _ hx _ hz hxz => anchoredLongReturnFamily_carry_strictMono (S.family y hy) hx hz hxz

/-- The supplied self-referential gap divisibility plus the derived zero-run gives
the carry-valuation lift congruence. -/
theorem carryVal2_congruence (S : ReturnClass4AnchoredCore ctx)
    {y : ℕ} (hy : y ∈ (olcFibre ctx).image S.key) :
    ∀ x ∈ olcSlice ctx S.key y, ∀ z ∈ olcSlice ctx S.key y, x < z →
      (∀ c ∈ olcSlice ctx S.key y, x < c → z ≤ c) →
        2 ^ carryVal2 ctx x ∣ (carryVal2 ctx z - carryVal2 ctx x) := by
  intro x hx z hz hxz hsucc
  have hzero := S.zeroRunAllPairs hy x hx z hz hxz
  have hzx : x + (z - x) = z := by omega
  have hrun : ∀ j, x < j → j ≤ x + (z - x) → ctx.d j = 0 := by
    intro j hj1 hj2
    rw [hzx] at hj2
    exact hzero j hj1 hj2
  have hdiv := S.hgapDiv y hy x hx z hz hxz hsucc
  have hcong := carryVal2_dvd_sub_of_zeroRun ctx x (z - x) hrun hdiv
  rwa [hzx] at hcong

/-- The per-slice `OlcSliceData` can be produced directly through the carry-valued
M.2.1 API once the remaining bound/divisibility inputs are supplied. -/
def toSlicesViaCarryVal2 (S : ReturnClass4AnchoredCore ctx) :
    ∀ y ∈ (olcFibre ctx).image S.key, OlcSliceData ctx S.key y :=
  fun y hy =>
    OlcSliceData.ofCarryVal2 ctx S.key y (S.hbound y hy)
      (S.carryVal2_crossingFree hy) (S.carryVal2_congruence hy)

/-- Upgrade the sharper core to the existing anchored seed. -/
def toAnchoredSeed (S : ReturnClass4AnchoredCore ctx) : ReturnClass4AnchoredSeed ctx where
  key := S.key
  family := S.family
  hbound := S.hbound
  hgapDiv := S.hgapDiv
  windowReach := returnWindowReach ctx
  hReach := returnWindowReach_add_one_le ctx
  hContain := returnClass4Contain_ofInterior ctx S.class4Interior
  hnumeric := S.hnumeric

/-- The full V3 Return/Class-4 charge from the sharper anchored core. -/
def toCharge (S : ReturnClass4AnchoredCore ctx) : Class4ReturnPerSliceCharge ctx :=
  S.toAnchoredSeed.toCharge

/-- The capacity-floor consequence of the sharper anchored core. -/
theorem returnFloor (S : ReturnClass4AnchoredCore ctx) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 4
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  S.toAnchoredSeed.returnFloor

/-- The corrected per-slice count from the sharper anchored core. -/
theorem perSliceCount (S : ReturnClass4AnchoredCore ctx) :
    (olcFibre ctx).card
      ≤ ((olcFibre ctx).image S.key).card * liftLevelBound ctx.shell.X :=
  routedFibre4_card_le_of_slices ctx S.key S.toSlicesViaCarryVal2

end ReturnClass4AnchoredCore

/-- The `returnCharge` field of V3 from a family of sharper anchored cores. -/
def returnChargeOfAnchoredCores
    (S : ∀ ctx : ActualFailureContext, ReturnClass4AnchoredCore ctx) :
    ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx :=
  fun ctx => (S ctx).toCharge

/-- The Return capacity floor from a family of sharper anchored cores. -/
theorem returnFloor_ofAnchoredCores
    (S : ∀ ctx : ActualFailureContext, ReturnClass4AnchoredCore ctx) :
    ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 4
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  fun ctx => (S ctx).returnFloor

/-- Residual surface after deriving the class-4 active window and the per-slice
crossing-free/congruence bridge from anchored M.3.1 data. -/
structure ReturnPerSliceCoreResidual where
  anchoredCore : forall ctx : ActualFailureContext, ReturnClass4AnchoredCore ctx

namespace ReturnPerSliceCoreResidual

/-- Convert the sharper residual into the older anchored-seed residual. -/
def anchoredReturn (R : ReturnPerSliceCoreResidual) :
    forall ctx : ActualFailureContext, ReturnClass4AnchoredSeed ctx :=
  fun ctx => (R.anchoredCore ctx).toAnchoredSeed

/-- Build the V3 Return/Class-4 field from the sharper core residual. -/
def returnCharge (R : ReturnPerSliceCoreResidual) :
    forall ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx :=
  returnChargeOfAnchoredCores R.anchoredCore

/-- The capacity-floor consequence of the sharper core residual. -/
theorem returnFloor (R : ReturnPerSliceCoreResidual) :
    forall ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 4
        <= erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : Real) / 6 :=
  returnFloor_ofAnchoredCores R.anchoredCore

/-- The corrected per-slice count from the sharper core residual. -/
theorem perSliceCount (R : ReturnPerSliceCoreResidual) (ctx : ActualFailureContext) :
    (olcFibre ctx).card
      <= ((olcFibre ctx).image ((R.returnCharge ctx).key)).card
          * liftLevelBound ctx.shell.X := by
  simpa [returnCharge, returnChargeOfAnchoredCores, ReturnClass4AnchoredCore.toCharge,
    ReturnClass4AnchoredSeed.toCharge, ReturnClass4AnchoredSeed.toSliceChargeSeed,
    Class4ReturnSliceChargeSeed.toCharge] using
    (R.anchoredCore ctx).perSliceCount

end ReturnPerSliceCoreResidual

/-- Sharp residual for closing the V3 Return/Class 4 per-slice field.

Each `ReturnClass4AnchoredSeed ctx` packages exactly the same key for:

* the anchored long-return family (`AnchoredLongReturnFamily`);
* the generated `OlcSliceData` slices;
* active-window containment for the actual class-4 fibre; and
* the matched `M_L * X` numeric.

This is the strongest genuine bridge currently available from the M.2.1/M.3.1
chain to `Class4ReturnPerSliceCharge`; the closed shell-factory input alone does
not supply this data. -/
structure ReturnPerSliceClosureResidual where
  anchoredReturn : forall ctx : ActualFailureContext, ReturnClass4AnchoredSeed ctx

namespace ReturnPerSliceClosureResidual

/-- Build the V3 Return/Class 4 field from the sharp anchored per-slice residual. -/
def returnCharge (R : ReturnPerSliceClosureResidual) :
    forall ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx :=
  returnChargeOfAnchoredSeeds R.anchoredReturn

/-- The requested V3-shaped field, conditional on the genuine anchored per-slice
residual rather than on the weaker factory-level shell input. -/
def class4ReturnPerSliceCharge_ofResidual
    (R : ReturnPerSliceClosureResidual) :
    forall ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx :=
  R.returnCharge

/-- The capacity-floor consequence of the anchored per-slice bridge. -/
theorem returnFloor (R : ReturnPerSliceClosureResidual) :
    forall ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 4
        <= erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : Real) / 6 :=
  returnFloor_ofAnchoredSeeds R.anchoredReturn

/-- The corrected M.2.1 per-slice count obtained from the same anchored seed. -/
theorem perSliceCount (R : ReturnPerSliceClosureResidual) (ctx : ActualFailureContext) :
    (olcFibre ctx).card
      <= ((olcFibre ctx).image ((R.returnCharge ctx).key)).card
          * liftLevelBound ctx.shell.X := by
  simpa [returnCharge, returnChargeOfAnchoredSeeds, ReturnClass4AnchoredSeed.toCharge,
    ReturnClass4AnchoredSeed.toSliceChargeSeed, Class4ReturnSliceChargeSeed.toCharge] using
    (R.anchoredReturn ctx).perSliceCount

end ReturnPerSliceClosureResidual

/-- Machine-readable audit of why the unconditional factory input does not by
itself construct the V3 per-slice Return charge. -/
def returnPerSliceClosureStatus : List String :=
  [ "CLOSED: class4ReturnFactoryInput_closed = returnInputUnconditional supplies forall ctx, GenuineReturnShellInput ctx.shell.",
    "SHRUNK: ReturnPerSliceCoreResidual derives the class-4 windowReach/hReach/hContain from class4Interior using returnWindowReach = |supportShell|-1.",
    "SHRUNK: ReturnClass4AnchoredCore derives per-slice zero-runs, crossing-freeness, and carry-valued lift congruence from AnchoredLongReturnFamily plus hgapDiv.",
    "BRIDGE: ReturnPerSliceClosureResidual.returnCharge supplies forall ctx, Class4ReturnPerSliceCharge ctx from forall ctx, ReturnClass4AnchoredSeed ctx.",
    "MISMATCH: GenuineReturnShellInput is shell-factory data; it has no key : Nat -> Nat on olcFibre ctx and no per-key OlcSliceData family.",
    "MISMATCH: the V3 charge needs hgap/hscale over ctx.n24CarryData and the actual routed class-4 fibre, plus active-window containment.",
    "MISMATCH: the V3 charge needs hnumeric, the matched (#sliceKeys) * liftLevelBound X * returnDyadicMult ctx <= cStar * xi * X / 6 smallness.",
    "NO TRIVIAL CLOSURE: the bridge uses ReturnClass4AnchoredSeed, not all-zero factory data or empty/vacuous return witnesses." ]

theorem returnPerSliceClosureStatus_nonempty :
    returnPerSliceClosureStatus != [] := by
  simp [returnPerSliceClosureStatus]

#print axioms class4ReturnFactoryInput_closed
#print axioms returnWindowReach_add_one_le
#print axioms returnClass4Contain_ofInterior
#print axioms ReturnClass4AnchoredCore.zeroRunAllPairs
#print axioms ReturnClass4AnchoredCore.carryVal2_crossingFree
#print axioms ReturnClass4AnchoredCore.carryVal2_congruence
#print axioms ReturnClass4AnchoredCore.toSlicesViaCarryVal2
#print axioms ReturnClass4AnchoredCore.toAnchoredSeed
#print axioms ReturnClass4AnchoredCore.toCharge
#print axioms ReturnClass4AnchoredCore.returnFloor
#print axioms ReturnClass4AnchoredCore.perSliceCount
#print axioms returnChargeOfAnchoredCores
#print axioms returnFloor_ofAnchoredCores
#print axioms ReturnPerSliceCoreResidual.anchoredReturn
#print axioms ReturnPerSliceCoreResidual.returnCharge
#print axioms ReturnPerSliceCoreResidual.returnFloor
#print axioms ReturnPerSliceCoreResidual.perSliceCount
#print axioms ReturnPerSliceClosureResidual.returnCharge
#print axioms ReturnPerSliceClosureResidual.class4ReturnPerSliceCharge_ofResidual
#print axioms ReturnPerSliceClosureResidual.returnFloor
#print axioms ReturnPerSliceClosureResidual.perSliceCount

end

end Erdos260
