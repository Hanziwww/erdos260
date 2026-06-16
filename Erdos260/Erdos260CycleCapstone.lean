import Erdos260.Erdos260SharpCapstone
import Erdos260.ChernoffClass0CycleClosure
import Erdos260.CNLClass1DeepClosure
import Erdos260.TowerCycleDensity
import Erdos260.ReturnClass4CycleClosure
import Erdos260.RunClass5BoundaryClosure
import Erdos260.DensePackClass3CycleClosure

/-!
# Erdős 260 — the wave-3 cycle capstone

This module consolidates the 2026-06-10 wave-3 cycle-machinery effort.  It defines
`Erdos260CycleResidual`, the strictly sharpened successor of `Erdos260SharpResidual`,
and proves the new final endpoint

`erdos260_of_cycleResidual : Erdos260CycleResidual → Erdos260Statement`

by composing ONLY existing public bridges of the six wave-3 modules into the wave-2
capstone `erdos260_of_sharpResidual`.  Nothing is re-proved here.  All six atoms carry
their wave-3 surface; no atom fell back to its wave-2 field.

The per-atom surfaces consumed:

1. **Tower / class 2** (`TowerCycleDensity`) — the per-deep-ctx modulus split: `q < 9`
   (closed, wave 2) OR `16 < q < 25` (closed, wave-3 parity) OR the finite cycle
   inequality `Class2CycleInequality ctx`; consumed through
   `towerCountBound_of_modulus_split` — strictly weaker than the bare cycle-density
   residual `Class2CycleDensityResidual`.
2. **Run / class 5** (`RunClass5BoundaryClosure`) — ONE Section 26 numeric per ctx at
   the canonical multiplier `runDyadicMult`; the boundary `M`/`hM` fields of
   `RunClass5SplitBoundary` are eliminated definitionally (the boundary max collapses
   under the proved ungated ceiling `n24_windowExcess_le_runDyadicMult`); consumed
   through `runSplitOfNumeric`.
3. **Return / class 4, count** (`ReturnClass4CycleClosure`) — the per-ctx 4-way gate
   disjunction: the wave-2 K.1 gap-ceiling gate OR the two-window span gate OR the
   in-window span gate OR a band-2 cycle-count bound `t·b₂ ≤ r + 1`; consumed through
   `class4FibreSmall_of_gates`.
4. **Return / class 4, digit** (`ReturnClass4CycleClosure`) — the reduced triple:
   `hzero` at the self-referential key, the clean step at per-slice MAXIMA only
   (strictly fewer positions than the wave-2 `hcleanStep`), and the K.1 interior;
   consumed through `ReturnClass4DigitResidual.ofSelfRefMaxCleanStep`.
5. **Chernoff / class 0** (`ChernoffClass0CycleClosure`) — the per-ctx windowed finite
   cycle check `Class0WindowCycleCheck`, swapped in LOSSLESSLY for the wave-2 pinned
   arithmetic via the proved equivalence `class0Pinned_field_iff_windowCycleCheck`
   (necessary AND sufficient).
6. **CNL / class 1** (`CNLClass1DeepClosure`) — `Class1DeepResidual`: on `r = 0` shells
   the single top window start, on deep shells emptiness only on the moduli surviving
   every wave-1..3 closure (ten closed moduli excluded); consumed through
   `class1Pinned_of_deepResidual` (output verbatim the wave-2 capstone field).
7. **DensePack / class 3** (`DensePackClass3CycleClosure`) — the BUDGET-FREE
   `DensePackCycleSplitResidual` (each field guarded by the failure of the matching
   proved cycle check, cover in exact `ℕ` form); consumed through
   `DensePackCycleSplitResidual.toRegimeSplit` at the canonical `sharpAtomBudget`,
   reusing the drop-in composition `erdos260SharpResidualOfCycleSplit`.

Dependency order mirrors `Erdos260SharpCapstone`: the Tower/Run/Return fields define
the canonical budget `sharpAtomBudget`; the class-3 regime split is rebuilt at that
budget inside `erdos260SharpResidualOfCycleSplit`; the class-0/class-1 fields are
budget-free.  The fields of `Erdos260CycleResidual` itself are mutually independent.
-/

namespace Erdos260

noncomputable section

/-- **The wave-3 cycle residual.**  Each field is the sharpest proven-equivalent (or
strictly weaker sufficient) wave-3 surface of its atom — per-ctx finite cycle checks,
residue pins, cycle-density counts and reduced digit data; all fields are mutually
independent (the class-3 field is budget-free). -/
structure Erdos260CycleResidual where
  /-- Tower / class 2 (split entry): per deep shell, `q < 9` OR `16 < q < 25` OR the
  finite cycle inequality `m₀ · (b₄ · ⌈K/c⌉) ≤ K` at some orbit period `c`. -/
  towerSplit : ∀ ctx : ActualFailureContext,
    towerShallowDepthBound < shellLadderDepth ctx →
    (class1SlopeDatum ctx).q < 9
    ∨ (16 < (class1SlopeDatum ctx).q ∧ (class1SlopeDatum ctx).q < 25)
    ∨ Class2CycleInequality ctx
  /-- Run / class 5 (single numeric): the Section 26 linear inequality at the canonical
  multiplier `runDyadicMult ctx` — the boundary `M`/`hM` data is eliminated by the
  proved ungated window-excess ceiling. -/
  runNumeric : ∀ ctx : ActualFailureContext,
    erdos260Constants.c0
        * ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card : ℝ)
        * runDyadicMult ctx
      ≤ (erdos260Constants.cStar * erdos260Constants.ξ / 12)
        * ((supportShell ctx.d ctx.X).card : ℝ)
  /-- Return / class 4 (count gates): per ctx, the K.1 gap-ceiling gate OR the
  two-window span gate OR the in-window span gate OR a band-2 cycle-count bound
  `t·b₂ ≤ r + 1`. -/
  returnGates : ∀ ctx : ActualFailureContext,
    64 * ((ctx.n24CarryData.r + 1)
        * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
      < 129 * shellLadderDepth ctx + 64
    ∨ 64 * (ctx.n24CarryData.a
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r)
        - ctx.n24CarryData.a
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X))
      < 2 * (129 * shellLadderDepth ctx + 64)
    ∨ 64 * (ctx.n24CarryData.a
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card - 1)
        - ctx.n24CarryData.a
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X))
      < 129 * shellLadderDepth ctx + 64
    ∨ ∃ c t : ℕ, 1 ≤ c
        ∧ (∀ m, 1 ≤ m →
            slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
              = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
        ∧ (supportShell ctx.shell.d ctx.shell.X).card ≤ t * c
        ∧ t * ((Finset.Icc 1 c).filter (fun j =>
            canonGap (class1SlopeDatum ctx).q
              (slopeOrbit (class1SlopeDatum ctx).q
                (class1SlopeDatum ctx).K₀ j) = 2)).card
            ≤ ctx.n24CarryData.r + 1
  /-- Return / class 4 (digit, Z): all-pairs zero-run between same-slice starts of the
  self-referential key (unchanged from wave 2 — already at the canonical key). -/
  returnZero : ∀ ctx : ActualFailureContext,
    ∀ y ∈ (olcFibre ctx).image (returnSelfRefKey ctx),
      ∀ x ∈ olcSlice ctx (returnSelfRefKey ctx) y,
        ∀ z ∈ olcSlice ctx (returnSelfRefKey ctx) y,
          x < z → ∀ j, x < j → j ≤ z → ctx.d j = 0
  /-- Return / class 4 (digit, reduced clean step): `d(k+1) = 0` at per-slice MAXIMA
  only — every non-maximal slice member is covered by `returnZero`. -/
  returnMaxClean : ∀ ctx : ActualFailureContext, ∀ k ∈ olcFibre ctx,
    (∀ z ∈ olcFibre ctx, returnSelfRefKey ctx z = returnSelfRefKey ctx k → z ≤ k) →
    ctx.d (k + 1) = 0
  /-- Return / class 4 (digit, K.1 boundary): descent windows stay strictly inside the
  shell window. -/
  returnInterior : ∀ ctx : ActualFailureContext,
    ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4,
      k + ctx.n24CarryData.r + 1
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card
  /-- Chernoff / class 0 (windowed finite cycle check): SOME orbit period such that
  every floor-realizing window start reads the orbit outside the deep band at its cycle
  residue — LOSSLESSLY equivalent to the wave-2 pinned arithmetic. -/
  class0Cycle : ∀ ctx : ActualFailureContext, Class0WindowCycleCheck ctx
  /-- CNL / class 1 (deep residual): the `r = 0` top-start fact plus deep-shell
  emptiness on the moduli surviving every wave-1..3 closure. -/
  class1Deep : Class1DeepResidual
  /-- DensePack / class 3 (budget-free cycle split): gated emptiness, K.1.1 density,
  K.1 interior and the exact-`ℕ` K.1.2 cover, each guarded by the FAILURE of the
  matching proved cycle check. -/
  densePackCycle : DensePackCycleSplitResidual

namespace Erdos260CycleResidual

/-- **The bridge into the wave-2 capstone**: every field of `Erdos260SharpResidual` is
rebuilt from the wave-3 surfaces through existing public bridges — nothing is re-proved.

* Tower — `towerCountBound_of_modulus_split` (per-deep-ctx split entry);
* Run — `runSplitOfNumeric` (single Section 26 numeric, `M`/`hM` eliminated);
* Return count — `class4FibreSmall_of_gates` (4-way per-ctx gate disjunction);
* Return digit — `ReturnClass4DigitResidual.ofSelfRefMaxCleanStep` (maxima reduction);
* class 0 — `class0Pinned_field_iff_windowCycleCheck.mpr` (lossless swap);
* class 1 — `class1Pinned_of_deepResidual` (output verbatim the capstone field);
* class 3 — `erdos260SharpResidualOfCycleSplit`, i.e.
  `DensePackCycleSplitResidual.toRegimeSplit` at the canonical `sharpAtomBudget`. -/
def toSharp (R : Erdos260CycleResidual) : Erdos260SharpResidual :=
  erdos260SharpResidualOfCycleSplit
    (towerCountBound_of_modulus_split R.towerSplit)
    (runSplitOfNumeric R.runNumeric)
    (class4FibreSmall_of_gates R.returnGates)
    (fun ctx => ReturnClass4DigitResidual.ofSelfRefMaxCleanStep ctx
      (R.returnZero ctx) (R.returnMaxClean ctx) (R.returnInterior ctx))
    (class0Pinned_field_iff_windowCycleCheck.mpr R.class0Cycle)
    (class1Pinned_of_deepResidual R.class1Deep)
    R.densePackCycle

/-- The final statement from the cycle residual, through the wave-2 sharp capstone and
the wave-1 six-atom capstone. -/
theorem toStatement (R : Erdos260CycleResidual) : Erdos260Statement :=
  erdos260_of_sharpResidual R.toSharp

end Erdos260CycleResidual

/-- **The wave-3 final endpoint.**  `Erdos260Statement` from the per-atom wave-3 cycle
surfaces, composed through the wave-2 sharp capstone with no re-proving and no
over-strong scalar anywhere on the route. -/
theorem erdos260_of_cycleResidual (R : Erdos260CycleResidual) : Erdos260Statement :=
  R.toStatement

/-- Machine-readable status of the wave-3 cycle capstone. -/
def erdos260CycleCapstoneStatus : List String :=
  [ "FINAL ENDPOINT (wave 3): erdos260_of_cycleResidual (R : Erdos260CycleResidual) : " ++
      "Erdos260Statement, composed through toSharp into erdos260_of_sharpResidual " ++
      "(wave 2) and the wave-1 six-atom capstone; only existing public bridges are " ++
      "consumed, nothing re-proved.",
    "ALL SIX ATOMS CARRY THEIR WAVE-3 SURFACE; NO WAVE-2 FALLBACKS.",
    "ATOM Tower/class 2 (SHARPENED, split entry): per deep ctx q < 9 (closed, wave 2) " ++
      "OR 16 < q < 25 (closed, wave-3 parity: q in {17,19,21,23}) OR the finite cycle " ++
      "inequality m0 * (b4 * ceil(K/c)) <= K at some orbit period c (at most q " ++
      "canonical-gap evaluations + one Nat comparison per ctx); consumed via " ++
      "towerCountBound_of_modulus_split - strictly weaker than the bare " ++
      "Class2CycleDensityResidual.",
    "ATOM Run/class 5 (SHARPENED, single numeric): ONE Section 26 linear inequality " ++
      "per ctx at the canonical multiplier runDyadicMult; the wave-2 M/hM boundary " ++
      "fields are eliminated definitionally (the boundary max collapses under the " ++
      "proved ungated ceiling n24_windowExcess_le_runDyadicMult); consumed via " ++
      "runSplitOfNumeric.",
    "ATOM Return/class 4 count (SHARPENED, gates): per ctx the K.1 gap-ceiling gate " ++
      "OR the two-window span gate OR the in-window span gate OR a band-2 cycle-count " ++
      "bound t*b2 <= r+1 (per-(q,K0) finite check); consumed via " ++
      "class4FibreSmall_of_gates into the capstone count field Class4FibreSmall.",
    "ATOM Return/class 4 digit (SHARPENED, maxima reduction): hzero at the " ++
      "self-referential key + the clean step at per-slice MAXIMA only (strictly fewer " ++
      "positions than the wave-2 hcleanStep; non-maximal members are covered by the " ++
      "zero-runs) + the K.1 interior; consumed via " ++
      "ReturnClass4DigitResidual.ofSelfRefMaxCleanStep.",
    "ATOM Chernoff/class 0 (SHARPENED, lossless): the per-ctx windowed finite cycle " ++
      "check Class0WindowCycleCheck (SOME period such that every floor-realizing " ++
      "window start reads the orbit outside the deep band 16K <= q at its residue), " ++
      "swapped for the wave-2 pinned arithmetic via the proved equivalence " ++
      "class0Pinned_field_iff_windowCycleCheck (necessary AND sufficient).",
    "ATOM CNL/class 1 (SHARPENED): Class1DeepResidual - on r = 0 shells (ALL " ++
      "L <= 15420) the SINGLE top window start is not class-1; on deep shells " ++
      "(r >= 1, L >= 15421) emptiness only on moduli OUTSIDE class1ClosedModuli " ++
      "{27,31,33,43,45,51,65,85,91,93} (ten cycle-closed moduli excluded), given " ++
      "64 | L, 9 <= q, the parity window; consumed via class1Pinned_of_deepResidual " ++
      "(output verbatim the wave-2 capstone field).",
    "ATOM DensePack/class 3 (SHARPENED, budget-free): DensePackCycleSplitResidual - " ++
      "gatedEmpty/ungatedDensity/ungatedInterior/ungatedCoverNat, each guarded by the " ++
      "FAILURE of the matching proved cycle check (Class3TopBandCycleFree / " ++
      "Class3CycleBand3Free), the K.1.2 cover in exact Nat form against the faithful " ++
      "marker count; equivalent to the wave-2 regime split at every budget " ++
      "(nonempty_cycleSplit_iff_regimeSplit); consumed via " ++
      "DensePackCycleSplitResidual.toRegimeSplit at sharpAtomBudget through the " ++
      "drop-in erdos260SharpResidualOfCycleSplit.",
    "PROVED OBSTRUCTION FIXED POINTS (wave 3, per class): tower - the 15 | q " ++
      "fixed-point family (a band-4-full period forces 15*K1 = q; off it b4 <= c-1); " ++
      "return - the q = 3K band-2 fixed point (deviations from q/3 quadruple; off " ++
      "3 | q every band-2 run has s <= log4(q/2)+1); densepack - the q = 7 all-ones " ++
      "band-3 fixed point (unfixed orbits enter the clean swap cycle 3 <-> 5); " ++
      "class 0 - odd small bases (every period closes at an odd base K_c = K0, so " ++
      "Odd K0 with 16*K0 <= q defeats every window-free cycle check).",
    "ROOT OBSTRUCTION (unchanged): no formalized bridge ties the digit-side gap-window " ++
      "pins (hitGap) to the orbit-side band pins (canonGap) beyond the shared index k; " ++
      "the per-atom open cores are exactly the surfaces above on the shells where the " ++
      "matching cycle checks fail.  We do NOT claim unconditional closure of any atom.",
    "CLOSED INSIDE the composition (unchanged from waves 1-2): carry floor, faithful " ++
      "phases, mass nonnegativity, the class-6 old-residual vacancy, the joint TRT " ++
      "ledger bound, the Kraft sum, and the hne/hcard counts." ]

theorem erdos260CycleCapstoneStatus_nonempty : erdos260CycleCapstoneStatus ≠ [] := by
  simp [erdos260CycleCapstoneStatus]

#print axioms Erdos260CycleResidual.toSharp
#print axioms Erdos260CycleResidual.toStatement
#print axioms erdos260_of_cycleResidual
#print axioms erdos260CycleCapstoneStatus_nonempty

end

end Erdos260
