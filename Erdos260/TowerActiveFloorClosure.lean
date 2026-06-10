import Erdos260.TowerClass2GenuineLeaf
import Erdos260.Erdos260V3TowerReduction
import Erdos260.SDRDensityCore
import Erdos260.SDRSelectionCore

/-!
# Tower active-floor closure boundary

This module records the current honest closure boundary for the V3/P9 Tower slot

```
forall ctx : ActualFailureContext, Class2ActiveFloorCount ctx
```

The no-input provider

```
def class2ActiveFloorCount_unconditional :
  forall ctx : ActualFailureContext, Class2ActiveFloorCount ctx
```

is not available from the existing formalized data without fabricating a dense-marker
or endpoint-disjoint witness.  What is available is the sharp bridge from the current
genuine Class 2 leaf (and its equivalent SDR / packing surfaces) to the exact
`Class2ActiveFloorCount` field consumed by `P9V3RunResidual`.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

namespace Erdos260

open Finset

noncomputable section

set_option linter.unusedVariables false

/-- The current sharp Tower/Class 2 residual for the V3 active-floor field.

This is only a type alias for readability: it is the already-existing genuine leaf
from `TowerClass2GenuineLeaf.lean`, not a new assumption.  It packages the Q-correct
dyadic-match/SDR data over the genuine class-2 fibre. -/
abbrev Class2ActiveFloorClosureResidual : Type :=
  forall ctx : ActualFailureContext, Class2TowerGenuineLeaf ctx

/-- The Tower V3 field from the sharp genuine Class 2 leaf.

This is the bridge needed to fill the `P9V3RunResidual.towerCount` field once the
remaining Class 2 leaf is supplied. -/
def class2ActiveFloorCount_of_genuineLeaf
    (R : Class2ActiveFloorClosureResidual) :
    forall ctx : ActualFailureContext, Class2ActiveFloorCount ctx :=
  towerCount_of_class2GenuineLeaf R

/-- The same Tower V3 field from the index-space SDR surface.

This names the endpoint-disjoint hit-index-block route explicitly:
`Class2IndexSDR -> Class2ActiveFloorCount`. -/
def class2ActiveFloorCount_of_indexSDR
    (S : forall ctx : ActualFailureContext, Class2IndexSDR ctx) :
    forall ctx : ActualFailureContext, Class2ActiveFloorCount ctx :=
  towerCount_ofIndexSDR S

/-- The same Tower V3 field from the shell-position SDR surface. -/
def class2ActiveFloorCount_of_shellSDR
    (S : forall ctx : ActualFailureContext, Class2ShellSDR ctx) :
    forall ctx : ActualFailureContext, Class2ActiveFloorCount ctx :=
  fun ctx =>
    Class2ActiveFloorCount.ofAreaPacking
      (Class2AreaPacking.ofOwnershipPacking
        (Class2OwnershipPacking.ofShellSDR (S ctx)))

/-- The same Tower V3 field from the ownership-packing surface. -/
def class2ActiveFloorCount_of_ownershipPacking
    (P : forall ctx : ActualFailureContext, Class2OwnershipPacking ctx) :
    forall ctx : ActualFailureContext, Class2ActiveFloorCount ctx :=
  fun ctx => Class2ActiveFloorCount.ofAreaPacking
    (Class2AreaPacking.ofOwnershipPacking (P ctx))

/-- The same Tower V3 field from the area-packing surface. -/
def class2ActiveFloorCount_of_areaPacking
    (P : forall ctx : ActualFailureContext, Class2AreaPacking ctx) :
    forall ctx : ActualFailureContext, Class2ActiveFloorCount ctx :=
  fun ctx => Class2ActiveFloorCount.ofAreaPacking (P ctx)

/-! ## Narrow residual surfaces below `Class2IndexSDR` -/

/-- The Hall-marginal residual for the Class 2 index SDR, pinned to the genuine
carry hit enumeration `ctx.n24CarryData.a`.

This is the sharp selection surface of `SDRSelectionCore`: a family of hit-index
windows `W`, a nonzero block size `m` through `rhoD * L <= m`, shell landing for
the genuine enumeration, and the Hall marginal condition over the real class-2
fibre.  The endpoint-disjoint representatives are then selected by Hall rather
than supplied directly. -/
structure Class2HallIndexSDRResidual (ctx : ActualFailureContext) where
  rhoD : ℝ
  eps : ℝ
  L : ℝ
  hrhoD_pos : 0 < rhoD
  hL_pos : 0 < L
  hYnn : 0 ≤ ctx.n24CarryData.Y
  hcalib : 2 * ctx.n24CarryData.Y ≤ 2 * eps * L
  huniform : 2 * (erdos260Constants.c0 * eps) ≤ erdos260Constants.ξ / 6 * rhoD
  hbdry : 0 ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2
  W : ℕ → Finset ℕ
  m : ℕ
  hmfloor : rhoD * L ≤ (m : ℝ)
  hlands : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
    ∀ j ∈ W k, ctx.n24CarryData.a j ∈ supportShell ctx.d ctx.X
  hmarg : ∀ S ⊆ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
    m * S.card ≤ (S.biUnion W).card

/-- Convert the Hall-marginal Class 2 residual to the concrete index-space SDR. -/
def Class2HallIndexSDRResidual.toIndexSDR {ctx : ActualFailureContext}
    (R : Class2HallIndexSDRResidual ctx) : Class2IndexSDR ctx :=
  Class2IndexSDR.ofWindowsHall ctx
    ctx.n24CarryData.a ctx.n24CarryData.carry.hits.strict.injective
    R.rhoD R.eps R.L R.hrhoD_pos R.hL_pos R.hYnn R.hcalib R.huniform R.hbdry
    R.W R.m R.hmfloor R.hlands R.hmarg

/-- The global index-SDR family obtained from Hall-marginal residuals. -/
def class2IndexSDR_of_hallResidual
    (R : ∀ ctx : ActualFailureContext, Class2HallIndexSDRResidual ctx) :
    ∀ ctx : ActualFailureContext, Class2IndexSDR ctx :=
  fun ctx => (R ctx).toIndexSDR

/-- The Tower active-floor field from the Hall-marginal residual surface. -/
def class2ActiveFloorCount_of_hallResidual
    (R : ∀ ctx : ActualFailureContext, Class2HallIndexSDRResidual ctx) :
    ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx :=
  class2ActiveFloorCount_of_indexSDR (class2IndexSDR_of_hallResidual R)

/-- The routed Class 2 Tower sub-mass bound from Hall-marginal residuals. -/
theorem class2TowerSubMass_of_hallResidual
    (R : ∀ ctx : ActualFailureContext, Class2HallIndexSDRResidual ctx)
    (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
      <= erdos260Constants.ξ * (ctx.shell.X : Real) / 6 :=
  (class2ActiveFloorCount_of_hallResidual R ctx).htowerSubMass

/-- The I.3.1 Tower separated-leaf provider from Hall-marginal residuals. -/
def towerSeparatedLocalLeafProviderOfHallResidual
    (R : ∀ ctx : ActualFailureContext, Class2HallIndexSDRResidual ctx) :
    ∀ ctx : ActualFailureContext,
      TowerSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : ℝ) :=
  towerSeparatedLocalLeafProviderOfActiveFloorCount
    (class2ActiveFloorCount_of_hallResidual R)

/-- The semiperiodic-density residual for the Class 2 index SDR, pinned to the
genuine carry hit enumeration `ctx.n24CarryData.a`.

This is the density-side builder of `SDRDensityCore`: the periodic window,
period-density floor, and length calibration produce the `rhoD * L` cardinal
floor; landing and interval disjointness remain as the orthogonal K.1.3
selection data. -/
structure Class2SemiperiodicIndexSDRResidual (ctx : ActualFailureContext) where
  eps : ℝ
  Lnat : ℕ
  hLpos : 0 < Lnat
  hYnn : 0 ≤ ctx.n24CarryData.Y
  hcalibE : 2 * ctx.n24CarryData.Y ≤ 2 * eps * (Lnat : ℝ)
  huniform : 2 * (erdos260Constants.c0 * eps)
    ≤ erdos260Constants.ξ / 6 * manuscriptRhoD
  hbdry : 0 ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2
  lo : ℕ → ℕ
  mwin : ℕ → ℕ
  lenw : ℕ → ℕ
  period : ℕ → ℕ
  hp : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
    0 < period k
  hper : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
    PeriodicOn ctx.shell.d (mwin k) (lenw k) (period k)
  hdens : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
    manuscriptRhoD * (period k : ℝ)
      ≤ (windowWeight ctx.shell.d (mwin k) (period k) : ℝ)
  hlenL : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
    Lnat + period k ≤ lenw k + 1
  hlands : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
    ∀ j ∈ Finset.Ico (lo k) (lo k + windowWeight ctx.shell.d (mwin k) (lenw k)),
      ctx.n24CarryData.a j ∈ supportShell ctx.d ctx.X
  hdisj : ∀ j ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
    ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2, j ≠ k →
      Disjoint (Finset.Ico (lo j) (lo j + windowWeight ctx.shell.d (mwin j) (lenw j)))
        (Finset.Ico (lo k) (lo k + windowWeight ctx.shell.d (mwin k) (lenw k)))

/-- Convert the semiperiodic-density Class 2 residual to the concrete index-space SDR. -/
def Class2SemiperiodicIndexSDRResidual.toIndexSDR {ctx : ActualFailureContext}
    (R : Class2SemiperiodicIndexSDRResidual ctx) : Class2IndexSDR ctx :=
  Class2IndexSDR.ofSemiperiodicDensity ctx
    ctx.n24CarryData.a ctx.n24CarryData.carry.hits.strict.injective
    R.eps R.Lnat R.hLpos R.hYnn R.hcalibE R.huniform R.hbdry
    R.lo R.mwin R.lenw R.period R.hp R.hper R.hdens R.hlenL R.hlands R.hdisj

/-- The global index-SDR family obtained from semiperiodic-density residuals. -/
def class2IndexSDR_of_semiperiodicResidual
    (R : ∀ ctx : ActualFailureContext, Class2SemiperiodicIndexSDRResidual ctx) :
    ∀ ctx : ActualFailureContext, Class2IndexSDR ctx :=
  fun ctx => (R ctx).toIndexSDR

/-- The Tower active-floor field from the semiperiodic-density residual surface. -/
def class2ActiveFloorCount_of_semiperiodicResidual
    (R : ∀ ctx : ActualFailureContext, Class2SemiperiodicIndexSDRResidual ctx) :
    ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx :=
  class2ActiveFloorCount_of_indexSDR (class2IndexSDR_of_semiperiodicResidual R)

/-- The routed Class 2 Tower sub-mass bound from semiperiodic-density residuals. -/
theorem class2TowerSubMass_of_semiperiodicResidual
    (R : ∀ ctx : ActualFailureContext, Class2SemiperiodicIndexSDRResidual ctx)
    (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
      <= erdos260Constants.ξ * (ctx.shell.X : Real) / 6 :=
  (class2ActiveFloorCount_of_semiperiodicResidual R ctx).htowerSubMass

/-- The I.3.1 Tower separated-leaf provider from semiperiodic-density residuals. -/
def towerSeparatedLocalLeafProviderOfSemiperiodicResidual
    (R : ∀ ctx : ActualFailureContext, Class2SemiperiodicIndexSDRResidual ctx) :
    ∀ ctx : ActualFailureContext,
      TowerSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : ℝ) :=
  towerSeparatedLocalLeafProviderOfActiveFloorCount
    (class2ActiveFloorCount_of_semiperiodicResidual R)

/-- The routed Tower sub-mass slot obtained from the closure residual.

This sanity theorem exposes the actual inequality carried by the V3 field:
`routedClassMassOf ... 2 <= xi * X / 6`. -/
theorem class2TowerSubMass_of_genuineLeaf
    (R : Class2ActiveFloorClosureResidual)
    (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
      <= erdos260Constants.ξ * (ctx.shell.X : Real) / 6 :=
  (class2ActiveFloorCount_of_genuineLeaf R ctx).htowerSubMass

/-- The class-2 Tower slot in the exact `P9V3RunResidual.towerCount` shape. -/
def p9V3TowerCount_of_genuineLeaf
    (R : Class2ActiveFloorClosureResidual) :
    forall ctx : ActualFailureContext, Class2ActiveFloorCount ctx :=
  class2ActiveFloorCount_of_genuineLeaf R

/-- Machine-readable status for the Tower active-floor closure attempt. -/
def towerActiveFloorClosureStatus : List String :=
  [ "NOT CLOSED UNCONDITIONALLY: no no-input constructor for forall ctx, Class2ActiveFloorCount ctx is present in the current formalization.",
    "BRIDGE PROVED: class2ActiveFloorCount_of_genuineLeaf : Class2ActiveFloorClosureResidual -> forall ctx, Class2ActiveFloorCount ctx.",
    "P9 SLOT PROVED: p9V3TowerCount_of_genuineLeaf gives exactly the towerCount field shape required by P9V3RunResidual.",
    "SDR BRIDGE PROVED: class2ActiveFloorCount_of_indexSDR : (forall ctx, Class2IndexSDR ctx) -> forall ctx, Class2ActiveFloorCount ctx.",
    "PACKING BRIDGES PROVED: shell SDR, ownership packing, and area packing all feed Class2ActiveFloorCount.",
    "HALL BRIDGE PROVED: Class2HallIndexSDRResidual -> Class2IndexSDR -> Class2ActiveFloorCount, using the genuine carry enumeration and Hall marginal condition.",
    "SEMIPERIODIC BRIDGE PROVED: Class2SemiperiodicIndexSDRResidual -> Class2IndexSDR -> Class2ActiveFloorCount, using the SDRDensityCore periodic-window density mechanism.",
    "EXACT BLOCKER: prove forall ctx, Class2TowerGenuineLeaf ctx, or equivalently a genuine Class2IndexSDR / Class2HallIndexSDRResidual / endpoint-disjoint ownership packing for every ActualFailureContext.",
    "SMALLEST NAMED RESIDUALS: Hall marginal union lower bound for the real class-2 descent windows, or the semiperiodic-density window data plus landing/disjoint interval selection.",
    "NON-DEGENERACY REQUIREMENT: the missing data must provide real class-2 endpoint-disjoint windows/owned hit blocks with positive Q-correct density over routedFibre ... 2; no empty, zero-floor, fallback, or full-mass witness is acceptable." ]

theorem towerActiveFloorClosureStatus_nonempty :
    towerActiveFloorClosureStatus != [] := by
  simp [towerActiveFloorClosureStatus]

/-! ## Axiom audit -/

#print axioms class2ActiveFloorCount_of_genuineLeaf
#print axioms class2ActiveFloorCount_of_indexSDR
#print axioms class2ActiveFloorCount_of_shellSDR
#print axioms class2ActiveFloorCount_of_ownershipPacking
#print axioms class2ActiveFloorCount_of_areaPacking
#print axioms Class2HallIndexSDRResidual.toIndexSDR
#print axioms class2IndexSDR_of_hallResidual
#print axioms class2ActiveFloorCount_of_hallResidual
#print axioms class2TowerSubMass_of_hallResidual
#print axioms towerSeparatedLocalLeafProviderOfHallResidual
#print axioms Class2SemiperiodicIndexSDRResidual.toIndexSDR
#print axioms class2IndexSDR_of_semiperiodicResidual
#print axioms class2ActiveFloorCount_of_semiperiodicResidual
#print axioms class2TowerSubMass_of_semiperiodicResidual
#print axioms towerSeparatedLocalLeafProviderOfSemiperiodicResidual
#print axioms class2TowerSubMass_of_genuineLeaf
#print axioms p9V3TowerCount_of_genuineLeaf

end

end Erdos260
