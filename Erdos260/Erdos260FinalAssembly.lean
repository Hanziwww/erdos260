import Erdos260.DescentDepthSection253Core
import Erdos260.Erdos260V3ClassBundles
import Erdos260.Erdos260V3TowerReduction
import Erdos260.RunBaseAreaCore
import Erdos260.ReturnM21SliceChargeClosureCore
import Erdos260.ActiveWindowContainmentCore

/-!
# Final assembly scaffold and open-obligation surface (V4 seed track)

The honest unconditional endpoint is `erdos260_of_minimalResidualV4`.  Its input
`Erdos260MinimalResidualV4` *is* the open-obligation bundle: every field is a strong,
shell-faithful obligation (the matched charge must dominate the ACTUAL window excess of
the ACTUAL failing shell, `windowExcess (hitGap ctx.n24CarryData.a) k …`), so it cannot be
discharged by representative or degenerate data.  This is the track the project's
anti-synthetic-closure discipline requires.

This module records the per-class obligation surface (the shrinking gap set) and the
`ActualFailureContext.shell` bridge that lets per-shell constructions feed the per-`ctx`
fields.  As each obligation is discharged unconditionally it moves from
`erdos260V4OpenObligations` into a proved `def`, until `Erdos260MinimalResidualV4` is
constructible with no hypotheses and `theorem erdos260 : Erdos260Statement` follows.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

namespace Erdos260

noncomputable section

/-- **The ctx-to-shell bridge.**  Every `ActualFailureContext` carries its pinned failing
shell `ctx.shell`, with the constant/scale projections holding definitionally
(`ActualFailureContext.shell_cQ : ctx.shell.cQ = erdos260Constants.cQ`, `shell_c0`,
`shell_X`, `shell_Q`).  A per-shell construction `f` therefore yields a per-`ctx` term by
applying it at `ctx.shell` with the `rfl` proof `ctx.shell_cQ`; this is how shell-leaf
constructions (`*LeafFromShell`, `*UnconditionalClosure`) feed the per-`ctx` V3/V4 fields. -/
def ctxShellApply {P : FailingDyadicShell → Type _}
    (f : ∀ shell : FailingDyadicShell, shell.cQ = erdos260Constants.cQ → P shell)
    (ctx : ActualFailureContext) : P ctx.shell :=
  f ctx.shell ctx.shell_cQ

/-- The V3 residual assembled from the narrowed per-class provider surface, with DensePack
reduced to the budget-independent endpoint-density residual. -/
def erdos260MinimalResidualV3_ofClassData_endpointDensity
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runChain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (chernoff : Class0ChernoffInjection (v3Budget towerCount runChain returnCharge))
    (cnl : Class1CNLInjection (v3Budget towerCount runChain returnCharge))
    (hdens : ∀ ctx : ActualFailureContext, densePackEndpointDensity ctx)
    (windowReach : ActualFailureContext → ℕ)
    (hReach : ∀ ctx : ActualFailureContext,
      windowReach ctx + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hContain : ∀ ctx : ActualFailureContext, ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + windowReach ctx)
    (hScale : ∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ) - ctx.n24CarryData.T ≤ 1) :
    Erdos260MinimalResidualV3 :=
  erdos260MinimalResidualV3_ofClassData towerCount runChain returnCharge chernoff cnl
    (densePackCount_ofEndpointDensity (v3Budget towerCount runChain returnCharge) hdens)
    windowReach hReach hContain hScale

/-! ## Narrowed V3 provider bridges -/

/-- The V3 residual with Tower supplied by the smaller index-space SDR provider.

This composes the verified SDR-to-active-floor chain
`Class2IndexSDR -> Class2ActiveFloorCount` with the endpoint-density final assembly
surface, so the final Tower obligation can be stated as the K.1.3 index-SDR data rather
than directly as `Class2ActiveFloorCount`. -/
def erdos260MinimalResidualV3_ofTowerSDR_endpointDensity
    (towerSDR : ∀ ctx : ActualFailureContext, Class2IndexSDR ctx)
    (runChain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (chernoff : Class0ChernoffInjection
      (v3Budget (towerCount_ofIndexSDR towerSDR) runChain returnCharge))
    (cnl : Class1CNLInjection
      (v3Budget (towerCount_ofIndexSDR towerSDR) runChain returnCharge))
    (hdens : ∀ ctx : ActualFailureContext, densePackEndpointDensity ctx)
    (windowReach : ActualFailureContext → ℕ)
    (hReach : ∀ ctx : ActualFailureContext,
      windowReach ctx + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hContain : ∀ ctx : ActualFailureContext, ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + windowReach ctx)
    (hScale : ∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ) - ctx.n24CarryData.T ≤ 1) :
    Erdos260MinimalResidualV3 :=
  erdos260MinimalResidualV3_ofClassData_endpointDensity
    (towerCount_ofIndexSDR towerSDR) runChain returnCharge chernoff cnl
    hdens windowReach hReach hContain hScale

/-- The run-chain family built from the §26 base-area cover provider.  This is a
final-assembly alias for `runChainFamilyOfBaseAreaCover`, exposing the smaller Run
provider shape next to the V3/V4 endpoints. -/
def runChain_ofBaseAreaCoverProvider
    (stageOf : ActualFailureContext → ℕ → ℕ)
    (len : ActualFailureContext → ℕ)
    (hmaps : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5, stageOf ctx k < len ctx)
    (hhalf : ∀ ctx : ActualFailureContext,
      ∀ i, stageMassOf ctx (stageOf ctx) (i + 1) ≤ (1 / 2) * stageMassOf ctx (stageOf ctx) i)
    (baseArea : ∀ ctx : ActualFailureContext, RunBaseAreaCover ctx (stageOf ctx)) :
    ∀ ctx : ActualFailureContext, RunClass5StageChain ctx :=
  runChainFamilyOfBaseAreaCover stageOf len hmaps hhalf baseArea

/-- The V3 residual with Tower supplied by index-space SDR data and Run supplied by
the §26 base-area provider. -/
def erdos260MinimalResidualV3_ofTowerSDR_runBaseArea_endpointDensity
    (towerSDR : ∀ ctx : ActualFailureContext, Class2IndexSDR ctx)
    (stageOf : ActualFailureContext → ℕ → ℕ)
    (len : ActualFailureContext → ℕ)
    (hmaps : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5, stageOf ctx k < len ctx)
    (hhalf : ∀ ctx : ActualFailureContext,
      ∀ i, stageMassOf ctx (stageOf ctx) (i + 1) ≤ (1 / 2) * stageMassOf ctx (stageOf ctx) i)
    (baseArea : ∀ ctx : ActualFailureContext, RunBaseAreaCover ctx (stageOf ctx))
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (chernoff : Class0ChernoffInjection
      (v3Budget (towerCount_ofIndexSDR towerSDR)
        (runChain_ofBaseAreaCoverProvider stageOf len hmaps hhalf baseArea) returnCharge))
    (cnl : Class1CNLInjection
      (v3Budget (towerCount_ofIndexSDR towerSDR)
        (runChain_ofBaseAreaCoverProvider stageOf len hmaps hhalf baseArea) returnCharge))
    (hdens : ∀ ctx : ActualFailureContext, densePackEndpointDensity ctx)
    (windowReach : ActualFailureContext → ℕ)
    (hReach : ∀ ctx : ActualFailureContext,
      windowReach ctx + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hContain : ∀ ctx : ActualFailureContext, ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + windowReach ctx)
    (hScale : ∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ) - ctx.n24CarryData.T ≤ 1) :
    Erdos260MinimalResidualV3 :=
  erdos260MinimalResidualV3_ofTowerSDR_endpointDensity towerSDR
    (runChain_ofBaseAreaCoverProvider stageOf len hmaps hhalf baseArea) returnCharge
    chernoff cnl hdens windowReach hReach hContain hScale

/-- The V3 residual with Tower supplied by index-space SDR data, Run supplied by the
§26 base-area provider, and Return supplied by the smaller M.2.1 slice-charge seed.

`Class4ReturnSliceChargeSeed.toCharge` discharges the dyadic gap multiplier fields of
`Class4ReturnPerSliceCharge`, so this endpoint exposes only the genuine per-slice geometry,
active-window containment, and `M_L*X` numeric smallness for Return. -/
def erdos260MinimalResidualV3_ofTowerSDR_runBaseArea_returnSeeds_endpointDensity
    (towerSDR : ∀ ctx : ActualFailureContext, Class2IndexSDR ctx)
    (stageOf : ActualFailureContext → ℕ → ℕ)
    (len : ActualFailureContext → ℕ)
    (hmaps : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5, stageOf ctx k < len ctx)
    (hhalf : ∀ ctx : ActualFailureContext,
      ∀ i, stageMassOf ctx (stageOf ctx) (i + 1) ≤ (1 / 2) * stageMassOf ctx (stageOf ctx) i)
    (baseArea : ∀ ctx : ActualFailureContext, RunBaseAreaCover ctx (stageOf ctx))
    (returnSeed : ∀ ctx : ActualFailureContext, Class4ReturnSliceChargeSeed ctx)
    (chernoff : Class0ChernoffInjection
      (v3Budget (towerCount_ofIndexSDR towerSDR)
        (runChain_ofBaseAreaCoverProvider stageOf len hmaps hhalf baseArea)
        (returnChargeOfSeeds returnSeed)))
    (cnl : Class1CNLInjection
      (v3Budget (towerCount_ofIndexSDR towerSDR)
        (runChain_ofBaseAreaCoverProvider stageOf len hmaps hhalf baseArea)
        (returnChargeOfSeeds returnSeed)))
    (hdens : ∀ ctx : ActualFailureContext, densePackEndpointDensity ctx)
    (windowReach : ActualFailureContext → ℕ)
    (hReach : ∀ ctx : ActualFailureContext,
      windowReach ctx + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hContain : ∀ ctx : ActualFailureContext, ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + windowReach ctx)
    (hScale : ∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ) - ctx.n24CarryData.T ≤ 1) :
    Erdos260MinimalResidualV3 :=
  erdos260MinimalResidualV3_ofTowerSDR_runBaseArea_endpointDensity towerSDR stageOf len
    hmaps hhalf baseArea (returnChargeOfSeeds returnSeed) chernoff cnl hdens
    windowReach hReach hContain hScale

/-- Build the V4 residual from the narrowed V3 class-data surface plus the V4 descent and
return-placement fields.  This is the current sharp final assembly boundary: the broad V3
matched-charge fields are no longer separate top-level inputs here, and the §25.3 descent
input is the source record that projects to the upper-band package downstream. -/
def erdos260MinimalResidualV4_ofClassData_endpointDensity
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runChain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (chernoff : Class0ChernoffInjection (v3Budget towerCount runChain returnCharge))
    (cnl : Class1CNLInjection (v3Budget towerCount runChain returnCharge))
    (hdens : ∀ ctx : ActualFailureContext, densePackEndpointDensity ctx)
    (windowReach : ActualFailureContext → ℕ)
    (hReach : ∀ ctx : ActualFailureContext,
      windowReach ctx + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hContain : ∀ ctx : ActualFailureContext, ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + windowReach ctx)
    (hScale : ∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ) - ctx.n24CarryData.T ≤ 1)
    (upperBandSource : ∀ ctx : ActualFailureContext, UpperBandMatchSource ctx)
    (denseWindowLo : ∀ ctx : ActualFailureContext,
      ∀ k, Membership.mem (genuineDensePackStarts ctx) k → ctx.shell.X < k + ctx.n24CarryData.r)
    (denseWindowHi : ∀ ctx : ActualFailureContext,
      ∀ k, Membership.mem (genuineDensePackStarts ctx) k →
        (k + ctx.n24CarryData.r) + proofV4DensePackSpread ctx.shell ≤ 2 * ctx.shell.X)
    (anchoredLongReturnFamily : ∀ ctx : ActualFailureContext,
      ∀ y, Membership.mem ((olcFibre ctx).image (returnCharge ctx).key) y →
        Nonempty (AnchoredLongReturnFamily ctx (returnCharge ctx).key y)) :
    Erdos260MinimalResidualV4 where
  toV3 := erdos260MinimalResidualV3_ofClassData_endpointDensity
    towerCount runChain returnCharge chernoff cnl hdens windowReach hReach hContain hScale
  upperBandSource := upperBandSource
  denseWindowLo := denseWindowLo
  denseWindowHi := denseWindowHi
  anchoredLongReturnFamily := anchoredLongReturnFamily

/-- Build the V4 residual with Tower supplied by the smaller index-space SDR provider. -/
def erdos260MinimalResidualV4_ofTowerSDR_endpointDensity
    (towerSDR : ∀ ctx : ActualFailureContext, Class2IndexSDR ctx)
    (runChain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (chernoff : Class0ChernoffInjection
      (v3Budget (towerCount_ofIndexSDR towerSDR) runChain returnCharge))
    (cnl : Class1CNLInjection
      (v3Budget (towerCount_ofIndexSDR towerSDR) runChain returnCharge))
    (hdens : ∀ ctx : ActualFailureContext, densePackEndpointDensity ctx)
    (windowReach : ActualFailureContext → ℕ)
    (hReach : ∀ ctx : ActualFailureContext,
      windowReach ctx + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hContain : ∀ ctx : ActualFailureContext, ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + windowReach ctx)
    (hScale : ∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ) - ctx.n24CarryData.T ≤ 1)
    (upperBandSource : ∀ ctx : ActualFailureContext, UpperBandMatchSource ctx)
    (denseWindowLo : ∀ ctx : ActualFailureContext,
      ∀ k, Membership.mem (genuineDensePackStarts ctx) k → ctx.shell.X < k + ctx.n24CarryData.r)
    (denseWindowHi : ∀ ctx : ActualFailureContext,
      ∀ k, Membership.mem (genuineDensePackStarts ctx) k →
        (k + ctx.n24CarryData.r) + proofV4DensePackSpread ctx.shell ≤ 2 * ctx.shell.X)
    (anchoredLongReturnFamily : ∀ ctx : ActualFailureContext,
      ∀ y, Membership.mem ((olcFibre ctx).image (returnCharge ctx).key) y →
        Nonempty (AnchoredLongReturnFamily ctx (returnCharge ctx).key y)) :
    Erdos260MinimalResidualV4 :=
  erdos260MinimalResidualV4_ofClassData_endpointDensity
    (towerCount_ofIndexSDR towerSDR) runChain returnCharge chernoff cnl
    hdens windowReach hReach hContain hScale upperBandSource
    denseWindowLo denseWindowHi anchoredLongReturnFamily

/-- Build the V4 residual with Tower supplied by index-space SDR data and Run supplied by
the §26 base-area provider. -/
def erdos260MinimalResidualV4_ofTowerSDR_runBaseArea_endpointDensity
    (towerSDR : ∀ ctx : ActualFailureContext, Class2IndexSDR ctx)
    (stageOf : ActualFailureContext → ℕ → ℕ)
    (len : ActualFailureContext → ℕ)
    (hmaps : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5, stageOf ctx k < len ctx)
    (hhalf : ∀ ctx : ActualFailureContext,
      ∀ i, stageMassOf ctx (stageOf ctx) (i + 1) ≤ (1 / 2) * stageMassOf ctx (stageOf ctx) i)
    (baseArea : ∀ ctx : ActualFailureContext, RunBaseAreaCover ctx (stageOf ctx))
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (chernoff : Class0ChernoffInjection
      (v3Budget (towerCount_ofIndexSDR towerSDR)
        (runChain_ofBaseAreaCoverProvider stageOf len hmaps hhalf baseArea) returnCharge))
    (cnl : Class1CNLInjection
      (v3Budget (towerCount_ofIndexSDR towerSDR)
        (runChain_ofBaseAreaCoverProvider stageOf len hmaps hhalf baseArea) returnCharge))
    (hdens : ∀ ctx : ActualFailureContext, densePackEndpointDensity ctx)
    (windowReach : ActualFailureContext → ℕ)
    (hReach : ∀ ctx : ActualFailureContext,
      windowReach ctx + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hContain : ∀ ctx : ActualFailureContext, ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + windowReach ctx)
    (hScale : ∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ) - ctx.n24CarryData.T ≤ 1)
    (upperBandSource : ∀ ctx : ActualFailureContext, UpperBandMatchSource ctx)
    (denseWindowLo : ∀ ctx : ActualFailureContext,
      ∀ k, Membership.mem (genuineDensePackStarts ctx) k → ctx.shell.X < k + ctx.n24CarryData.r)
    (denseWindowHi : ∀ ctx : ActualFailureContext,
      ∀ k, Membership.mem (genuineDensePackStarts ctx) k →
        (k + ctx.n24CarryData.r) + proofV4DensePackSpread ctx.shell ≤ 2 * ctx.shell.X)
    (anchoredLongReturnFamily : ∀ ctx : ActualFailureContext,
      ∀ y, Membership.mem ((olcFibre ctx).image (returnCharge ctx).key) y →
        Nonempty (AnchoredLongReturnFamily ctx (returnCharge ctx).key y)) :
    Erdos260MinimalResidualV4 :=
  erdos260MinimalResidualV4_ofTowerSDR_endpointDensity towerSDR
    (runChain_ofBaseAreaCoverProvider stageOf len hmaps hhalf baseArea) returnCharge
    chernoff cnl hdens windowReach hReach hContain hScale upperBandSource
    denseWindowLo denseWindowHi anchoredLongReturnFamily

/-- Build the V4 residual at the currently sharpest connected final-assembly boundary:
Tower as index-space SDR, Run as §26 base-area data, and Return as the M.2.1
slice-charge seed. -/
def erdos260MinimalResidualV4_ofTowerSDR_runBaseArea_returnSeeds_endpointDensity
    (towerSDR : ∀ ctx : ActualFailureContext, Class2IndexSDR ctx)
    (stageOf : ActualFailureContext → ℕ → ℕ)
    (len : ActualFailureContext → ℕ)
    (hmaps : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5, stageOf ctx k < len ctx)
    (hhalf : ∀ ctx : ActualFailureContext,
      ∀ i, stageMassOf ctx (stageOf ctx) (i + 1) ≤ (1 / 2) * stageMassOf ctx (stageOf ctx) i)
    (baseArea : ∀ ctx : ActualFailureContext, RunBaseAreaCover ctx (stageOf ctx))
    (returnSeed : ∀ ctx : ActualFailureContext, Class4ReturnSliceChargeSeed ctx)
    (chernoff : Class0ChernoffInjection
      (v3Budget (towerCount_ofIndexSDR towerSDR)
        (runChain_ofBaseAreaCoverProvider stageOf len hmaps hhalf baseArea)
        (returnChargeOfSeeds returnSeed)))
    (cnl : Class1CNLInjection
      (v3Budget (towerCount_ofIndexSDR towerSDR)
        (runChain_ofBaseAreaCoverProvider stageOf len hmaps hhalf baseArea)
        (returnChargeOfSeeds returnSeed)))
    (hdens : ∀ ctx : ActualFailureContext, densePackEndpointDensity ctx)
    (windowReach : ActualFailureContext → ℕ)
    (hReach : ∀ ctx : ActualFailureContext,
      windowReach ctx + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hContain : ∀ ctx : ActualFailureContext, ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + windowReach ctx)
    (hScale : ∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ) - ctx.n24CarryData.T ≤ 1)
    (upperBandSource : ∀ ctx : ActualFailureContext, UpperBandMatchSource ctx)
    (denseWindowLo : ∀ ctx : ActualFailureContext,
      ∀ k, Membership.mem (genuineDensePackStarts ctx) k → ctx.shell.X < k + ctx.n24CarryData.r)
    (denseWindowHi : ∀ ctx : ActualFailureContext,
      ∀ k, Membership.mem (genuineDensePackStarts ctx) k →
        (k + ctx.n24CarryData.r) + proofV4DensePackSpread ctx.shell ≤ 2 * ctx.shell.X)
    (anchoredLongReturnFamily : ∀ ctx : ActualFailureContext,
      ∀ y, Membership.mem ((olcFibre ctx).image ((returnChargeOfSeeds returnSeed ctx).key)) y →
        Nonempty (AnchoredLongReturnFamily ctx ((returnChargeOfSeeds returnSeed ctx).key) y)) :
    Erdos260MinimalResidualV4 :=
  erdos260MinimalResidualV4_ofTowerSDR_runBaseArea_endpointDensity towerSDR stageOf len
    hmaps hhalf baseArea (returnChargeOfSeeds returnSeed) chernoff cnl hdens
    windowReach hReach hContain hScale upperBandSource denseWindowLo denseWindowHi
    anchoredLongReturnFamily

/-- Build the V4 residual with DensePack endpoint-density derived from the V4
upper-band package, rather than supplied as an independent final-assembly input. -/
def erdos260MinimalResidualV4_ofTowerSDR_runBaseArea_returnSeeds_descentDensity
    (towerSDR : ∀ ctx : ActualFailureContext, Class2IndexSDR ctx)
    (stageOf : ActualFailureContext → ℕ → ℕ)
    (len : ActualFailureContext → ℕ)
    (hmaps : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5, stageOf ctx k < len ctx)
    (hhalf : ∀ ctx : ActualFailureContext,
      ∀ i, stageMassOf ctx (stageOf ctx) (i + 1) ≤ (1 / 2) * stageMassOf ctx (stageOf ctx) i)
    (baseArea : ∀ ctx : ActualFailureContext, RunBaseAreaCover ctx (stageOf ctx))
    (returnSeed : ∀ ctx : ActualFailureContext, Class4ReturnSliceChargeSeed ctx)
    (upperBandSource : ∀ ctx : ActualFailureContext, UpperBandMatchSource ctx)
    (denseWindowLo : ∀ ctx : ActualFailureContext,
      ∀ k, Membership.mem (genuineDensePackStarts ctx) k → ctx.shell.X < k + ctx.n24CarryData.r)
    (denseWindowHi : ∀ ctx : ActualFailureContext,
      ∀ k, Membership.mem (genuineDensePackStarts ctx) k →
        (k + ctx.n24CarryData.r) + proofV4DensePackSpread ctx.shell ≤ 2 * ctx.shell.X)
    (chernoff : Class0ChernoffInjection
      (v3Budget (towerCount_ofIndexSDR towerSDR)
        (runChain_ofBaseAreaCoverProvider stageOf len hmaps hhalf baseArea)
        (returnChargeOfSeeds returnSeed)))
    (cnl : Class1CNLInjection
      (v3Budget (towerCount_ofIndexSDR towerSDR)
        (runChain_ofBaseAreaCoverProvider stageOf len hmaps hhalf baseArea)
        (returnChargeOfSeeds returnSeed)))
    (windowReach : ActualFailureContext → ℕ)
    (hReach : ∀ ctx : ActualFailureContext,
      windowReach ctx + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hContain : ∀ ctx : ActualFailureContext, ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + windowReach ctx)
    (hScale : ∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ) - ctx.n24CarryData.T ≤ 1)
    (anchoredLongReturnFamily : ∀ ctx : ActualFailureContext,
      ∀ y, Membership.mem ((olcFibre ctx).image ((returnChargeOfSeeds returnSeed ctx).key)) y →
        Nonempty (AnchoredLongReturnFamily ctx ((returnChargeOfSeeds returnSeed ctx).key) y)) :
    Erdos260MinimalResidualV4 :=
  erdos260MinimalResidualV4_ofTowerSDR_runBaseArea_returnSeeds_endpointDensity towerSDR
    stageOf len hmaps hhalf baseArea returnSeed chernoff cnl
    (fun ctx => densePackEndpointDensity_of_matchedDescentWindows ctx
      (denseWindowLo ctx) (denseWindowHi ctx)
      ((upperBandSource ctx).toUpperBandMatchData.toMatchedDescentWindows))
    windowReach hReach hContain hScale upperBandSource denseWindowLo denseWindowHi
    anchoredLongReturnFamily

/-- Build the V4 residual with DensePack endpoint-density derived from the V4
upper-band package and the active-window reach/containment derived from the shared
`WindowInteriorResidual`.  This leaves only the K.1.2 scalar calibration `hScale`
as the DensePack-specific active-window input. -/
def erdos260MinimalResidualV4_ofTowerSDR_runBaseArea_returnSeeds_descentDensity_windowInterior
    (towerSDR : ∀ ctx : ActualFailureContext, Class2IndexSDR ctx)
    (stageOf : ActualFailureContext → ℕ → ℕ)
    (len : ActualFailureContext → ℕ)
    (hmaps : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5, stageOf ctx k < len ctx)
    (hhalf : ∀ ctx : ActualFailureContext,
      ∀ i, stageMassOf ctx (stageOf ctx) (i + 1) ≤ (1 / 2) * stageMassOf ctx (stageOf ctx) i)
    (baseArea : ∀ ctx : ActualFailureContext, RunBaseAreaCover ctx (stageOf ctx))
    (returnSeed : ∀ ctx : ActualFailureContext, Class4ReturnSliceChargeSeed ctx)
    (upperBandSource : ∀ ctx : ActualFailureContext, UpperBandMatchSource ctx)
    (denseWindowLo : ∀ ctx : ActualFailureContext,
      ∀ k, Membership.mem (genuineDensePackStarts ctx) k → ctx.shell.X < k + ctx.n24CarryData.r)
    (denseWindowHi : ∀ ctx : ActualFailureContext,
      ∀ k, Membership.mem (genuineDensePackStarts ctx) k →
        (k + ctx.n24CarryData.r) + proofV4DensePackSpread ctx.shell ≤ 2 * ctx.shell.X)
    (chernoff : Class0ChernoffInjection
      (v3Budget (towerCount_ofIndexSDR towerSDR)
        (runChain_ofBaseAreaCoverProvider stageOf len hmaps hhalf baseArea)
        (returnChargeOfSeeds returnSeed)))
    (cnl : Class1CNLInjection
      (v3Budget (towerCount_ofIndexSDR towerSDR)
        (runChain_ofBaseAreaCoverProvider stageOf len hmaps hhalf baseArea)
        (returnChargeOfSeeds returnSeed)))
    (windowInterior : WindowInteriorResidual
      (v3Budget (towerCount_ofIndexSDR towerSDR)
        (runChain_ofBaseAreaCoverProvider stageOf len hmaps hhalf baseArea)
        (returnChargeOfSeeds returnSeed)))
    (hScale : ∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ) - ctx.n24CarryData.T ≤ 1)
    (anchoredLongReturnFamily : ∀ ctx : ActualFailureContext,
      ∀ y, Membership.mem ((olcFibre ctx).image ((returnChargeOfSeeds returnSeed ctx).key)) y →
        Nonempty (AnchoredLongReturnFamily ctx ((returnChargeOfSeeds returnSeed ctx).key) y)) :
    Erdos260MinimalResidualV4 :=
  erdos260MinimalResidualV4_ofTowerSDR_runBaseArea_returnSeeds_descentDensity towerSDR
    stageOf len hmaps hhalf baseArea returnSeed upperBandSource denseWindowLo denseWindowHi
    chernoff cnl densePackWindowReach
    (fun ctx => densePackWindowReach_add_one_le ctx)
    windowInterior.densePackContain hScale anchoredLongReturnFamily

/-- Erdos #260 from the current narrowed V4 class-data boundary. -/
theorem erdos260Statement_of_v4ClassData_endpointDensity
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runChain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (chernoff : Class0ChernoffInjection (v3Budget towerCount runChain returnCharge))
    (cnl : Class1CNLInjection (v3Budget towerCount runChain returnCharge))
    (hdens : ∀ ctx : ActualFailureContext, densePackEndpointDensity ctx)
    (windowReach : ActualFailureContext → ℕ)
    (hReach : ∀ ctx : ActualFailureContext,
      windowReach ctx + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hContain : ∀ ctx : ActualFailureContext, ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + windowReach ctx)
    (hScale : ∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ) - ctx.n24CarryData.T ≤ 1)
    (upperBandSource : ∀ ctx : ActualFailureContext, UpperBandMatchSource ctx)
    (denseWindowLo : ∀ ctx : ActualFailureContext,
      ∀ k, Membership.mem (genuineDensePackStarts ctx) k → ctx.shell.X < k + ctx.n24CarryData.r)
    (denseWindowHi : ∀ ctx : ActualFailureContext,
      ∀ k, Membership.mem (genuineDensePackStarts ctx) k →
        (k + ctx.n24CarryData.r) + proofV4DensePackSpread ctx.shell ≤ 2 * ctx.shell.X)
    (anchoredLongReturnFamily : ∀ ctx : ActualFailureContext,
      ∀ y, Membership.mem ((olcFibre ctx).image (returnCharge ctx).key) y →
        Nonempty (AnchoredLongReturnFamily ctx (returnCharge ctx).key y)) :
    Erdos260Statement :=
  erdos260_of_minimalResidualV4
    (erdos260MinimalResidualV4_ofClassData_endpointDensity
      towerCount runChain returnCharge chernoff cnl hdens windowReach hReach hContain hScale
      upperBandSource denseWindowLo denseWindowHi anchoredLongReturnFamily)

/-- Erdos #260 from the V4 endpoint-density boundary with Tower reduced to the
index-space SDR provider. -/
theorem erdos260Statement_of_v4TowerSDR_endpointDensity
    (towerSDR : ∀ ctx : ActualFailureContext, Class2IndexSDR ctx)
    (runChain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (chernoff : Class0ChernoffInjection
      (v3Budget (towerCount_ofIndexSDR towerSDR) runChain returnCharge))
    (cnl : Class1CNLInjection
      (v3Budget (towerCount_ofIndexSDR towerSDR) runChain returnCharge))
    (hdens : ∀ ctx : ActualFailureContext, densePackEndpointDensity ctx)
    (windowReach : ActualFailureContext → ℕ)
    (hReach : ∀ ctx : ActualFailureContext,
      windowReach ctx + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hContain : ∀ ctx : ActualFailureContext, ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + windowReach ctx)
    (hScale : ∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ) - ctx.n24CarryData.T ≤ 1)
    (upperBandSource : ∀ ctx : ActualFailureContext, UpperBandMatchSource ctx)
    (denseWindowLo : ∀ ctx : ActualFailureContext,
      ∀ k, Membership.mem (genuineDensePackStarts ctx) k → ctx.shell.X < k + ctx.n24CarryData.r)
    (denseWindowHi : ∀ ctx : ActualFailureContext,
      ∀ k, Membership.mem (genuineDensePackStarts ctx) k →
        (k + ctx.n24CarryData.r) + proofV4DensePackSpread ctx.shell ≤ 2 * ctx.shell.X)
    (anchoredLongReturnFamily : ∀ ctx : ActualFailureContext,
      ∀ y, Membership.mem ((olcFibre ctx).image (returnCharge ctx).key) y →
        Nonempty (AnchoredLongReturnFamily ctx (returnCharge ctx).key y)) :
    Erdos260Statement :=
  erdos260_of_minimalResidualV4
    (erdos260MinimalResidualV4_ofTowerSDR_endpointDensity towerSDR runChain returnCharge
      chernoff cnl hdens windowReach hReach hContain hScale upperBandSource
      denseWindowLo denseWindowHi anchoredLongReturnFamily)

/-- Erdos #260 from the V4 endpoint-density boundary with Tower reduced to index-space SDR
and Run reduced to the §26 base-area provider. -/
theorem erdos260Statement_of_v4TowerSDR_runBaseArea_endpointDensity
    (towerSDR : ∀ ctx : ActualFailureContext, Class2IndexSDR ctx)
    (stageOf : ActualFailureContext → ℕ → ℕ)
    (len : ActualFailureContext → ℕ)
    (hmaps : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5, stageOf ctx k < len ctx)
    (hhalf : ∀ ctx : ActualFailureContext,
      ∀ i, stageMassOf ctx (stageOf ctx) (i + 1) ≤ (1 / 2) * stageMassOf ctx (stageOf ctx) i)
    (baseArea : ∀ ctx : ActualFailureContext, RunBaseAreaCover ctx (stageOf ctx))
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (chernoff : Class0ChernoffInjection
      (v3Budget (towerCount_ofIndexSDR towerSDR)
        (runChain_ofBaseAreaCoverProvider stageOf len hmaps hhalf baseArea) returnCharge))
    (cnl : Class1CNLInjection
      (v3Budget (towerCount_ofIndexSDR towerSDR)
        (runChain_ofBaseAreaCoverProvider stageOf len hmaps hhalf baseArea) returnCharge))
    (hdens : ∀ ctx : ActualFailureContext, densePackEndpointDensity ctx)
    (windowReach : ActualFailureContext → ℕ)
    (hReach : ∀ ctx : ActualFailureContext,
      windowReach ctx + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hContain : ∀ ctx : ActualFailureContext, ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + windowReach ctx)
    (hScale : ∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ) - ctx.n24CarryData.T ≤ 1)
    (upperBandSource : ∀ ctx : ActualFailureContext, UpperBandMatchSource ctx)
    (denseWindowLo : ∀ ctx : ActualFailureContext,
      ∀ k, Membership.mem (genuineDensePackStarts ctx) k → ctx.shell.X < k + ctx.n24CarryData.r)
    (denseWindowHi : ∀ ctx : ActualFailureContext,
      ∀ k, Membership.mem (genuineDensePackStarts ctx) k →
        (k + ctx.n24CarryData.r) + proofV4DensePackSpread ctx.shell ≤ 2 * ctx.shell.X)
    (anchoredLongReturnFamily : ∀ ctx : ActualFailureContext,
      ∀ y, Membership.mem ((olcFibre ctx).image (returnCharge ctx).key) y →
        Nonempty (AnchoredLongReturnFamily ctx (returnCharge ctx).key y)) :
    Erdos260Statement :=
  erdos260_of_minimalResidualV4
    (erdos260MinimalResidualV4_ofTowerSDR_runBaseArea_endpointDensity towerSDR stageOf len
      hmaps hhalf baseArea returnCharge chernoff cnl hdens windowReach hReach hContain hScale
      upperBandSource denseWindowLo denseWindowHi anchoredLongReturnFamily)

/-- Erdos #260 from the sharp connected V4 boundary with Return reduced to the
M.2.1 slice-charge seed. -/
theorem erdos260Statement_of_v4TowerSDR_runBaseArea_returnSeeds_endpointDensity
    (towerSDR : ∀ ctx : ActualFailureContext, Class2IndexSDR ctx)
    (stageOf : ActualFailureContext → ℕ → ℕ)
    (len : ActualFailureContext → ℕ)
    (hmaps : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5, stageOf ctx k < len ctx)
    (hhalf : ∀ ctx : ActualFailureContext,
      ∀ i, stageMassOf ctx (stageOf ctx) (i + 1) ≤ (1 / 2) * stageMassOf ctx (stageOf ctx) i)
    (baseArea : ∀ ctx : ActualFailureContext, RunBaseAreaCover ctx (stageOf ctx))
    (returnSeed : ∀ ctx : ActualFailureContext, Class4ReturnSliceChargeSeed ctx)
    (chernoff : Class0ChernoffInjection
      (v3Budget (towerCount_ofIndexSDR towerSDR)
        (runChain_ofBaseAreaCoverProvider stageOf len hmaps hhalf baseArea)
        (returnChargeOfSeeds returnSeed)))
    (cnl : Class1CNLInjection
      (v3Budget (towerCount_ofIndexSDR towerSDR)
        (runChain_ofBaseAreaCoverProvider stageOf len hmaps hhalf baseArea)
        (returnChargeOfSeeds returnSeed)))
    (hdens : ∀ ctx : ActualFailureContext, densePackEndpointDensity ctx)
    (windowReach : ActualFailureContext → ℕ)
    (hReach : ∀ ctx : ActualFailureContext,
      windowReach ctx + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hContain : ∀ ctx : ActualFailureContext, ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + windowReach ctx)
    (hScale : ∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ) - ctx.n24CarryData.T ≤ 1)
    (upperBandSource : ∀ ctx : ActualFailureContext, UpperBandMatchSource ctx)
    (denseWindowLo : ∀ ctx : ActualFailureContext,
      ∀ k, Membership.mem (genuineDensePackStarts ctx) k → ctx.shell.X < k + ctx.n24CarryData.r)
    (denseWindowHi : ∀ ctx : ActualFailureContext,
      ∀ k, Membership.mem (genuineDensePackStarts ctx) k →
        (k + ctx.n24CarryData.r) + proofV4DensePackSpread ctx.shell ≤ 2 * ctx.shell.X)
    (anchoredLongReturnFamily : ∀ ctx : ActualFailureContext,
      ∀ y, Membership.mem ((olcFibre ctx).image ((returnChargeOfSeeds returnSeed ctx).key)) y →
        Nonempty (AnchoredLongReturnFamily ctx ((returnChargeOfSeeds returnSeed ctx).key) y)) :
    Erdos260Statement :=
  erdos260_of_minimalResidualV4
    (erdos260MinimalResidualV4_ofTowerSDR_runBaseArea_returnSeeds_endpointDensity towerSDR
      stageOf len hmaps hhalf baseArea returnSeed chernoff cnl hdens windowReach hReach
      hContain hScale upperBandSource denseWindowLo denseWindowHi anchoredLongReturnFamily)

/-- Erdos #260 from the sharp connected V4 boundary with DensePack endpoint density
derived from the V4 upper-band package. -/
theorem erdos260Statement_of_v4TowerSDR_runBaseArea_returnSeeds_descentDensity
    (towerSDR : ∀ ctx : ActualFailureContext, Class2IndexSDR ctx)
    (stageOf : ActualFailureContext → ℕ → ℕ)
    (len : ActualFailureContext → ℕ)
    (hmaps : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5, stageOf ctx k < len ctx)
    (hhalf : ∀ ctx : ActualFailureContext,
      ∀ i, stageMassOf ctx (stageOf ctx) (i + 1) ≤ (1 / 2) * stageMassOf ctx (stageOf ctx) i)
    (baseArea : ∀ ctx : ActualFailureContext, RunBaseAreaCover ctx (stageOf ctx))
    (returnSeed : ∀ ctx : ActualFailureContext, Class4ReturnSliceChargeSeed ctx)
    (upperBandSource : ∀ ctx : ActualFailureContext, UpperBandMatchSource ctx)
    (denseWindowLo : ∀ ctx : ActualFailureContext,
      ∀ k, Membership.mem (genuineDensePackStarts ctx) k → ctx.shell.X < k + ctx.n24CarryData.r)
    (denseWindowHi : ∀ ctx : ActualFailureContext,
      ∀ k, Membership.mem (genuineDensePackStarts ctx) k →
        (k + ctx.n24CarryData.r) + proofV4DensePackSpread ctx.shell ≤ 2 * ctx.shell.X)
    (chernoff : Class0ChernoffInjection
      (v3Budget (towerCount_ofIndexSDR towerSDR)
        (runChain_ofBaseAreaCoverProvider stageOf len hmaps hhalf baseArea)
        (returnChargeOfSeeds returnSeed)))
    (cnl : Class1CNLInjection
      (v3Budget (towerCount_ofIndexSDR towerSDR)
        (runChain_ofBaseAreaCoverProvider stageOf len hmaps hhalf baseArea)
        (returnChargeOfSeeds returnSeed)))
    (windowReach : ActualFailureContext → ℕ)
    (hReach : ∀ ctx : ActualFailureContext,
      windowReach ctx + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hContain : ∀ ctx : ActualFailureContext, ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + windowReach ctx)
    (hScale : ∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ) - ctx.n24CarryData.T ≤ 1)
    (anchoredLongReturnFamily : ∀ ctx : ActualFailureContext,
      ∀ y, Membership.mem ((olcFibre ctx).image ((returnChargeOfSeeds returnSeed ctx).key)) y →
        Nonempty (AnchoredLongReturnFamily ctx ((returnChargeOfSeeds returnSeed ctx).key) y)) :
    Erdos260Statement :=
  erdos260_of_minimalResidualV4
    (erdos260MinimalResidualV4_ofTowerSDR_runBaseArea_returnSeeds_descentDensity towerSDR
      stageOf len hmaps hhalf baseArea returnSeed upperBandSource denseWindowLo denseWindowHi
      chernoff cnl windowReach hReach hContain hScale anchoredLongReturnFamily)

/-- Erdos #260 from the sharp connected V4 boundary with both endpoint density
and active-window containment derived from existing V4/interior packages. -/
theorem erdos260Statement_of_v4TowerSDR_runBaseArea_returnSeeds_descentDensity_windowInterior
    (towerSDR : ∀ ctx : ActualFailureContext, Class2IndexSDR ctx)
    (stageOf : ActualFailureContext → ℕ → ℕ)
    (len : ActualFailureContext → ℕ)
    (hmaps : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5, stageOf ctx k < len ctx)
    (hhalf : ∀ ctx : ActualFailureContext,
      ∀ i, stageMassOf ctx (stageOf ctx) (i + 1) ≤ (1 / 2) * stageMassOf ctx (stageOf ctx) i)
    (baseArea : ∀ ctx : ActualFailureContext, RunBaseAreaCover ctx (stageOf ctx))
    (returnSeed : ∀ ctx : ActualFailureContext, Class4ReturnSliceChargeSeed ctx)
    (upperBandSource : ∀ ctx : ActualFailureContext, UpperBandMatchSource ctx)
    (denseWindowLo : ∀ ctx : ActualFailureContext,
      ∀ k, Membership.mem (genuineDensePackStarts ctx) k → ctx.shell.X < k + ctx.n24CarryData.r)
    (denseWindowHi : ∀ ctx : ActualFailureContext,
      ∀ k, Membership.mem (genuineDensePackStarts ctx) k →
        (k + ctx.n24CarryData.r) + proofV4DensePackSpread ctx.shell ≤ 2 * ctx.shell.X)
    (chernoff : Class0ChernoffInjection
      (v3Budget (towerCount_ofIndexSDR towerSDR)
        (runChain_ofBaseAreaCoverProvider stageOf len hmaps hhalf baseArea)
        (returnChargeOfSeeds returnSeed)))
    (cnl : Class1CNLInjection
      (v3Budget (towerCount_ofIndexSDR towerSDR)
        (runChain_ofBaseAreaCoverProvider stageOf len hmaps hhalf baseArea)
        (returnChargeOfSeeds returnSeed)))
    (windowInterior : WindowInteriorResidual
      (v3Budget (towerCount_ofIndexSDR towerSDR)
        (runChain_ofBaseAreaCoverProvider stageOf len hmaps hhalf baseArea)
        (returnChargeOfSeeds returnSeed)))
    (hScale : ∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ) - ctx.n24CarryData.T ≤ 1)
    (anchoredLongReturnFamily : ∀ ctx : ActualFailureContext,
      ∀ y, Membership.mem ((olcFibre ctx).image ((returnChargeOfSeeds returnSeed ctx).key)) y →
        Nonempty (AnchoredLongReturnFamily ctx ((returnChargeOfSeeds returnSeed ctx).key) y)) :
    Erdos260Statement :=
  erdos260_of_minimalResidualV4
    (erdos260MinimalResidualV4_ofTowerSDR_runBaseArea_returnSeeds_descentDensity_windowInterior
      towerSDR stageOf len hmaps hhalf baseArea returnSeed upperBandSource denseWindowLo
      denseWindowHi chernoff cnl windowInterior hScale anchoredLongReturnFamily)

/-- The remaining V4 open obligations, grouped by parallel workstream (the shrinking gap
set).  Each entry is a strong, shell-faithful `∀ ctx` field of `Erdos260MinimalResidualV4`
(or its embedded `toV3`).  When this list is empty the endpoint is unconditional. -/
def erdos260V4OpenObligations : List String :=
  [ "C0 Chernoff (class 0): Class0ChernoffInjection (v3Budget towerCount runChain returnCharge) -- the J.1.7/22.1A charge map, membership, injectivity, and area-positive cap.",
    "C1 CNL (class 1): Class1CNLInjection (v3Budget towerCount runChain returnCharge) -- the L.1.2/G.35 codeword map, membership, injectivity, and Kraft domination.",
    "C3 DensePack (class 3): windowInterior + hScale -- endpoint density derives from upperBandSource + denseWindowLo/Hi, and windowReach/hReach/hContain derive from WindowInteriorResidual.",
    "C2 Tower (class 2): towerSDR -- Class2IndexSDR, feeding Class2ActiveFloorCount through towerCount_ofIndexSDR / the SDR ownership chain.",
    "C4 Return (class 4): returnSeed -- Class4ReturnSliceChargeSeed, the M.2.1 per-slice geometry + active-window containment + M_L*X smallness; toCharge discharges Class4ReturnPerSliceCharge.",
    "C5 Run (class 5): stageOf / len / hmaps / hhalf / baseArea -- the §26 base-area provider feeding RunClass5StageChain via runChain_ofBaseAreaCoverProvider.",
    "D Sec 25.3 descent: upperBandSource / denseWindowLo / denseWindowHi -- DescentWindowMatch + coprimality + depth source for the upper residue band and Q-correct density geometry (tex Sec 8).",
    "C4' M.3.1: anchoredLongReturnFamily -- Nonempty (AnchoredLongReturnFamily) on each V3 return slice; derives survivorFamily, CleanReturnPlacement, and SliceCompleteReturns (tex Appendix M)." ]

theorem erdos260V4OpenObligations_length : erdos260V4OpenObligations.length = 8 := by
  simp [erdos260V4OpenObligations]

/-- Re-export of the honest endpoint, the Phase-3 integration target: once a
`Erdos260MinimalResidualV4` is assembled with no hypotheses, this yields `Erdos260Statement`. -/
theorem erdos260Statement_of_residualV4 (R : Erdos260MinimalResidualV4) : Erdos260Statement :=
  erdos260_of_minimalResidualV4 R

end

end Erdos260
