import Erdos260.ScaleFloorPush
import Erdos260.NearPeriodicityForcing

/-!
# Erdős 260 — the wave-8 push capstone (assembly)

Wave 8 produced two green modules:

* `ScaleFloorPush` — the pushed unconditional floor `X > 2^493460` / `L ≥ 493461`
  (sharp fire `17·(2L−25) ≤ 2^24`, margin exactly 1), `r ≥ 32` everywhere, the LAST
  L-guard dead (`towerDeepGuard_unconditional`), the pinned-value floor at `2^986891`,
  and the collapsed successor surface `Erdos260ScaleFloorPushResidual` (14 fields, no
  L-guard anywhere) with endpoint `erdos260_of_scaleFloorPush`.
* `NearPeriodicityForcing` — the TailMatch bridge into `WindowPeriodic` (conditional
  endpoint `erdos260_of_dyadicTailMatch`), the digit-blindness refutation of the
  carry-residue pigeonhole route, and the two genuine unconditional digit forcings:
  the reduced-carry parity at odd positions (`digit_eq_parity_at_odd_position`) and
  the envelope band (`digit_forced_one_of_carry_high` /
  `digit_forced_zero_of_carry_low`, free band EXACTLY `Q(N+1) ≤ 2R_N ≤ Q(N+3)`).

This module is the assembly verdict on what the unconditional digit forcings do to the
scale-floor-push surface.

## The composition audit (honest)

The 14 fields of `Erdos260ScaleFloorPushResidual` split into 12 fields whose conclusions
carry NO digit values (positions, orders, masses, inequalities: `towerEnumLow/Tail`,
`runNumericLow/Tail`, `returnGates` (`ReturnGatesBodyUngated` is a position inequality),
`returnInterior` (an index bound), `class0*`, `class1Deep*`, `densePackUngated`) and the
TWO digit-valued fields `returnZero` (`ReturnZeroBody`: `d j = 0` on slice intervals
`(x, z]`) and `returnMaxClean` (`ReturnMaxCleanBody`: `d (k+1) = 0` at per-slice maxima).

1. **The envelope-low forcing COMPOSES** (the demand genuinely shrinks).  At every
   demanded zero position the conclusion is FREE whenever the carry sits strictly below
   the lower band edge (`2 R_{N} < Q·(N+1)` forces `d_{N+1} = 0`,
   `digit_forced_zero_of_carry_low`).  The banded restatements `ReturnZeroBodyBanded` /
   `ReturnMaxCleanBodyBanded` therefore demand the zero digit ONLY at positions whose
   carry sits at/above the lower band edge — and they rebuild the verbatim bodies
   through `ctx.hrational` + the forcing (`returnZeroBody_of_banded` /
   `returnMaxCleanBody_of_banded`), with per-ctx equivalences
   (`returnZeroBody_iff_banded` / `returnMaxCleanBody_iff_banded`): nothing is hidden.
2. **The parity forcing does NOT compose** (kept out, honestly).
   `digit_eq_parity_at_odd_position` is a change of VARIABLES, not a demand reduction:
   restating `d j = 0` at an odd position `j` as "`ρ_j` is even" is an obligation of
   identical strength on an equally unknown trajectory (the parity recursion consumes
   the digits it reports — non-autonomous), it covers odd positions only, and it is
   onset-limited (`t ≤ N` for `Q = u·2^t`).  No strictly-weaker field results.
3. **The envelope-high forcing is a CONSTRAINT, not a relief.**  At high-band states
   (`Q(N+3) < 2 R_N`) the next digit is forced to `1` (`digit_forced_one_of_carry_high`),
   REFUTING the demanded zero — so the digit fields secretly demand carry confinement
   `2 R_N ≤ Q(N+3)` along the slice intervals (`carry_upper_of_digit_zero`).  Recorded;
   not consumable as a weakening.
4. **The digit-blindness results touch no field** — they refute a (pigeonhole) supply
   route; they do not restate any obligation.

## The deliverable

* `Erdos260PushResidual` — the official wave-8 surface: the scale-floor-push 14 fields
  with the two digit-valued Return fields in banded form, all else verbatim.
* `erdos260_of_pushResidual : Erdos260PushResidual → Erdos260Statement` via
  `toScaleFloorPush` and `erdos260_of_scaleFloorPush` (public bridges only).
* Weakening witnesses from every predecessor surface; `Nonempty` equivalences down the
  whole lineage (wave 8 = wave 6.5/7 = wave 6 in strength on the unconditional lane).
* The conditional routes re-exported: the TailMatch route
  (`erdos260_push_tailMatch_route`) and the pushed deep-lever route
  (`erdos260_push_deepLever_route`).

Additive only: nothing upstream is touched; only existing public bridges are consumed.
No `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 1.  The banded digit bodies — the envelope-low forcing consumed -/

/-- **The banded `returnZero` body**: the zero digit on slice intervals is demanded ONLY
at positions whose carry sits at/above the lower band edge `Q·j ≤ 2·R_{j−1}`.  Below the
edge the digit is already forced to `0` unconditionally
(`digit_forced_zero_of_carry_low`), so this demands strictly less of a provider than
`ReturnZeroBody` while rebuilding it in full (`returnZeroBody_of_banded`). -/
def ReturnZeroBodyBanded (ctx : ActualFailureContext) : Prop :=
  ∀ y ∈ (olcFibre ctx).image (returnSelfRefKey ctx),
    ∀ x ∈ olcSlice ctx (returnSelfRefKey ctx) y,
      ∀ z ∈ olcSlice ctx (returnSelfRefKey ctx) y,
        x < z → ∀ j, x < j → j ≤ z →
          ∀ P : ℤ, realWeightedValue (natBinaryAsReal ctx.d) = (P : ℝ) / (ctx.Q : ℝ) →
            (ctx.Q : ℤ) * (j : ℤ) ≤ 2 * integerCarry ctx.Q P ctx.d (j - 1) →
            ctx.d j = 0

/-- **The banded `returnMaxClean` body**: the clean step at a per-slice maximum is
demanded ONLY when the carry at the maximum sits at/above the lower band edge
`Q·(k+1) ≤ 2·R_k`. -/
def ReturnMaxCleanBodyBanded (ctx : ActualFailureContext) : Prop :=
  ∀ k ∈ olcFibre ctx,
    (∀ z ∈ olcFibre ctx, returnSelfRefKey ctx z = returnSelfRefKey ctx k → z ≤ k) →
    ∀ P : ℤ, realWeightedValue (natBinaryAsReal ctx.d) = (P : ℝ) / (ctx.Q : ℝ) →
      (ctx.Q : ℤ) * ((k + 1 : ℕ) : ℤ) ≤ 2 * integerCarry ctx.Q P ctx.d k →
      ctx.d (k + 1) = 0

/-- **The reconstruction** (where the near-periodicity forcing fires): the banded body
rebuilds the verbatim `ReturnZeroBody` — at sub-band positions the zero digit is
supplied free by `digit_forced_zero_of_carry_low` through `ctx.hrational`. -/
theorem returnZeroBody_of_banded (ctx : ActualFailureContext)
    (h : ReturnZeroBodyBanded ctx) : ReturnZeroBody ctx := by
  intro y hy x hx z hz hxz j hjx hjz
  obtain ⟨P, hP⟩ := ctx.hrational
  by_cases hband : (ctx.Q : ℤ) * (j : ℤ) ≤ 2 * integerCarry ctx.Q P ctx.d (j - 1)
  · exact h y hy x hx z hz hxz j hjx hjz P hP hband
  · push Not at hband
    have hj1 : j - 1 + 1 = j := by omega
    have hlow : 2 * integerCarry ctx.Q P ctx.d (j - 1)
        < (ctx.Q : ℤ) * ((j - 1 + 1 : ℕ) : ℤ) := by
      rw [hj1]; exact hband
    have h0 := digit_forced_zero_of_carry_low ctx.hQ ctx.hd hP hlow
    rwa [hj1] at h0

/-- The verbatim body trivially yields the banded one (forget the band data). -/
theorem returnZeroBodyBanded_of_full (ctx : ActualFailureContext)
    (h : ReturnZeroBody ctx) : ReturnZeroBodyBanded ctx :=
  fun y hy x hx z hz hxz j hjx hjz _ _ _ => h y hy x hx z hz hxz j hjx hjz

/-- **Per-ctx equivalence**: the banded `returnZero` body hides no strength. -/
theorem returnZeroBody_iff_banded (ctx : ActualFailureContext) :
    ReturnZeroBody ctx ↔ ReturnZeroBodyBanded ctx :=
  ⟨returnZeroBodyBanded_of_full ctx, returnZeroBody_of_banded ctx⟩

/-- The reconstruction for the clean step at per-slice maxima. -/
theorem returnMaxCleanBody_of_banded (ctx : ActualFailureContext)
    (h : ReturnMaxCleanBodyBanded ctx) : ReturnMaxCleanBody ctx := by
  intro k hk hmax
  obtain ⟨P, hP⟩ := ctx.hrational
  by_cases hband : (ctx.Q : ℤ) * ((k + 1 : ℕ) : ℤ) ≤ 2 * integerCarry ctx.Q P ctx.d k
  · exact h k hk hmax P hP hband
  · push Not at hband
    exact digit_forced_zero_of_carry_low ctx.hQ ctx.hd hP hband

/-- The verbatim body trivially yields the banded one. -/
theorem returnMaxCleanBodyBanded_of_full (ctx : ActualFailureContext)
    (h : ReturnMaxCleanBody ctx) : ReturnMaxCleanBodyBanded ctx :=
  fun k hk hmax _ _ _ => h k hk hmax

/-- **Per-ctx equivalence**: the banded `returnMaxClean` body hides no strength. -/
theorem returnMaxCleanBody_iff_banded (ctx : ActualFailureContext) :
    ReturnMaxCleanBody ctx ↔ ReturnMaxCleanBodyBanded ctx :=
  ⟨returnMaxCleanBodyBanded_of_full ctx, returnMaxCleanBody_of_banded ctx⟩

/-! ## Part 2.  The official wave-8 surface -/

/-- **The wave-8 push residual** — the official wave-8 surface: the scale-floor-push
14 fields (`Erdos260ScaleFloorPushResidual`; no L-guard anywhere) with the TWO
digit-valued Return fields restated in envelope-banded form (the only fields the
near-periodicity module's unconditional results can shrink).  The other 12 fields are
verbatim: their conclusions carry no digit values, the parity forcing is a change of
variables (not a weakening), the high-band forcing is a constraint (not a relief), and
the digit-blindness results refute a route rather than restate an obligation. -/
structure Erdos260PushResidual where
  /-- Tower / class 2 — enumerated part (`q < 107`); verbatim wave-8 field. -/
  towerEnumLow : ∀ ctx : ActualFailureContext,
    TowerModulusEnumEscape ctx → (class1SlopeDatum ctx).q < 107 →
    Class2CycleInequality ctx
  /-- Tower / class 2 — tail (`107 ≤ q`); verbatim wave-8 field. -/
  towerEnumTail : ∀ ctx : ActualFailureContext,
    TowerModulusEnumEscape ctx →
    107 ≤ (class1SlopeDatum ctx).q →
    (((Nat.log 2 (class1SlopeDatum ctx).q + 1) * shellWidth ctx
        < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
            (class1SlopeDatum ctx).K₀)))
        ∧ TowerBand4Budget ctx)
      ∨ Class2CycleInequality ctx
  /-- Run / class 5 — enumerated part (`q < 64`); verbatim wave-8 field. -/
  runNumericLow : ∀ ctx : ActualFailureContext,
    (class1SlopeDatum ctx).q < 64 →
    Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx
  /-- Run / class 5 — tail (`64 ≤ q`); verbatim wave-8 field. -/
  runNumericTail : ∀ ctx : ActualFailureContext,
    64 ≤ (class1SlopeDatum ctx).q →
    ((Nat.log 2 (class1SlopeDatum ctx).q + 1)
        * (supportShell ctx.shell.d ctx.shell.X).card
      < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
          (class1SlopeDatum ctx).K₀)))
      ∧ RunBandBudget ctx
    ∨ Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx
  /-- Return / class 4 count gates — gate-free 3-way body; verbatim wave-8 field
  (`ReturnGatesBodyUngated` is a position inequality: no digit value to band). -/
  returnGates : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    2 * (129 * shellLadderDepth ctx + 64)
      ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
    ReturnGatesBodyUngated ctx
  /-- Return / class 4 digit Z — BANDED: the zero digit is demanded only at/above the
  lower envelope edge (`digit_forced_zero_of_carry_low` closes the rest). -/
  returnZero : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    (∃ k ∈ olcFibre ctx,
      2 ^ carryVal2 ctx k < (supportShell ctx.shell.d ctx.shell.X).card) →
    ¬ ReturnIndexWindowClean ctx →
    ReturnZeroBodyBanded ctx
  /-- Return / class 4 clean step — BANDED likewise. -/
  returnMaxClean : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnIndexWindowClean ctx →
    ReturnMaxCleanBodyBanded ctx
  /-- Return / class 4 K.1 interior — verbatim wave-8 field (an index bound; no digit
  value to band). -/
  returnInterior : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx
  /-- Chernoff / class 0 survivors — verbatim wave-8 field. -/
  class0Survivor : ∀ ctx : ActualFailureContext, Class0DatumSurvivor ctx →
    Class0SurvivorResidueMiss ctx
  /-- Chernoff / class 0 mid band — verbatim wave-8 field. -/
  class0Mid : ∀ ctx : ActualFailureContext, 48 ≤ (class1SlopeDatum ctx).q →
    (class1SlopeDatum ctx).q < 96 → Class0CycleMeetsShallow ctx →
    Class0WindowCycleCheck ctx
  /-- Chernoff / class 0 large moduli (`96 ≤ q`) — verbatim wave-8 field. -/
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
  /-- CNL / class 1 — enumerated deep part (`q < 101`); verbatim wave-8 field. -/
  class1DeepLow : ∀ ctx : ActualFailureContext,
    64 ∣ shellLadderDepth ctx →
    9 ≤ (class1SlopeDatum ctx).q →
    ((class1SlopeDatum ctx).q ≤ 15 ∨ 25 ≤ (class1SlopeDatum ctx).q) →
    (class1SlopeDatum ctx).q ∉ class1ClosedModuli →
    ¬ Class1DatumClosed ctx →
    ¬ Class1GcdWindowMiss ctx →
    (class1SlopeDatum ctx).q < 101 →
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅
  /-- CNL / class 1 — tail (`101 ≤ q`); verbatim wave-8 field. -/
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
  /-- DensePack / class 3 — the collapsed ungated residual; verbatim wave-8 field. -/
  densePackUngated : DensePackUngatedClosureResidual

namespace Erdos260PushResidual

/-- **The bridge into the scale-floor-push surface**: the two banded digit fields are
rebuilt in full by the envelope-low forcing; every other field passes verbatim. -/
def toScaleFloorPush (H : Erdos260PushResidual) : Erdos260ScaleFloorPushResidual where
  towerEnumLow := H.towerEnumLow
  towerEnumTail := H.towerEnumTail
  runNumericLow := H.runNumericLow
  runNumericTail := H.runNumericTail
  returnGates := H.returnGates
  returnZero := fun ctx h1 h2 h3 h4 =>
    returnZeroBody_of_banded ctx (H.returnZero ctx h1 h2 h3 h4)
  returnMaxClean := fun ctx h1 h2 =>
    returnMaxCleanBody_of_banded ctx (H.returnMaxClean ctx h1 h2)
  returnInterior := H.returnInterior
  class0Survivor := H.class0Survivor
  class0Mid := H.class0Mid
  class0BigOrder := H.class0BigOrder
  class1DeepLow := H.class1DeepLow
  class1DeepTail := H.class1DeepTail
  densePackUngated := H.densePackUngated

/-- The final statement from the push residual, through the scale-floor push (hence the
wave-6.5/7 floor harvest, the wave-6 rigidity capstone, and the digit-side chain). -/
theorem toStatement (H : Erdos260PushResidual) : Erdos260Statement :=
  erdos260_of_scaleFloorPush H.toScaleFloorPush

end Erdos260PushResidual

/-- **The wave-8 final endpoint.**  `Erdos260Statement` from the official wave-8
surface, with no re-proving anywhere on the route. -/
theorem erdos260_of_pushResidual (H : Erdos260PushResidual) : Erdos260Statement :=
  H.toStatement

/-! ## Part 3.  Weakening witnesses and equivalences (nothing hidden) -/

/-- Weakening witness: any scale-floor-push provider yields the push residual (the
banded fields forget their band data). -/
def pushResidual_of_scaleFloorPushResidual (R : Erdos260ScaleFloorPushResidual) :
    Erdos260PushResidual where
  towerEnumLow := R.towerEnumLow
  towerEnumTail := R.towerEnumTail
  runNumericLow := R.runNumericLow
  runNumericTail := R.runNumericTail
  returnGates := R.returnGates
  returnZero := fun ctx h1 h2 h3 h4 =>
    returnZeroBodyBanded_of_full ctx (R.returnZero ctx h1 h2 h3 h4)
  returnMaxClean := fun ctx h1 h2 =>
    returnMaxCleanBodyBanded_of_full ctx (R.returnMaxClean ctx h1 h2)
  returnInterior := R.returnInterior
  class0Survivor := R.class0Survivor
  class0Mid := R.class0Mid
  class0BigOrder := R.class0BigOrder
  class1DeepLow := R.class1DeepLow
  class1DeepTail := R.class1DeepTail
  densePackUngated := R.densePackUngated

/-- Weakening witness from the wave-6.5/7 floor-harvest surface. -/
def pushResidual_of_floorHarvestResidual (R : Erdos260FloorHarvestResidual) :
    Erdos260PushResidual :=
  pushResidual_of_scaleFloorPushResidual
    (scaleFloorPushResidual_of_floorHarvestResidual R)

/-- Weakening witness from the wave-7 bootstrap surface (a reducible alias of the
floor-harvest surface). -/
def pushResidual_of_bootstrapResidual (R : Erdos260BootstrapResidual) :
    Erdos260PushResidual :=
  pushResidual_of_floorHarvestResidual R

/-- Weakening witness from the wave-6 rigidity surface. -/
def pushResidual_of_rigidityResidual (R : Erdos260RigidityResidual) :
    Erdos260PushResidual :=
  pushResidual_of_scaleFloorPushResidual (scaleFloorPushResidual_of_rigidityResidual R)

/-- **The wave-8 surface is equivalent to the scale-floor-push surface** — the banding
hides no strength (the envelope-low forcing closes the dropped region outright). -/
theorem nonempty_pushResidual_iff_scaleFloorPush :
    Nonempty Erdos260PushResidual ↔ Nonempty Erdos260ScaleFloorPushResidual :=
  ⟨fun ⟨H⟩ => ⟨H.toScaleFloorPush⟩,
   fun ⟨R⟩ => ⟨pushResidual_of_scaleFloorPushResidual R⟩⟩

/-- Equivalence with the wave-6.5/7 floor-harvest surface. -/
theorem nonempty_pushResidual_iff_floorHarvest :
    Nonempty Erdos260PushResidual ↔ Nonempty Erdos260FloorHarvestResidual :=
  nonempty_pushResidual_iff_scaleFloorPush.trans nonempty_scaleFloorPush_iff_floorHarvest

/-- Equivalence with the wave-7 bootstrap surface. -/
theorem nonempty_pushResidual_iff_bootstrap :
    Nonempty Erdos260PushResidual ↔ Nonempty Erdos260BootstrapResidual :=
  nonempty_pushResidual_iff_floorHarvest

/-- Equivalence with the wave-6 rigidity surface: the whole unconditional lineage
(wave 6 → 6.5 → 7 → 8) is one strength class, presented ever more sharply. -/
theorem nonempty_pushResidual_iff_rigidity :
    Nonempty Erdos260PushResidual ↔ Nonempty Erdos260RigidityResidual :=
  nonempty_pushResidual_iff_floorHarvest.trans nonempty_floorHarvest_iff_rigidity

/-! ## Part 4.  The conditional routes (re-exported, PARALLEL, not merged) -/

/-- **The wave-8 tail-match conditional route** — `Erdos260Statement` from the section
25.1 all-lengths match residual `DeepDyadicTailMatch` plus the lever-shrunk wave-5
surfaces (re-export of `erdos260_of_dyadicTailMatch`).  PARALLEL to
`erdos260_of_pushResidual`: its surface is the wave-4/5 lever shape. -/
theorem erdos260_push_tailMatch_route (h : DeepDyadicTailMatch)
    (surfaces : DyadicValueLever → Erdos260DyadicLeverResidual) : Erdos260Statement :=
  erdos260_of_dyadicTailMatch h surfaces

/-- **The wave-8 pushed deep-lever conditional route** — `Erdos260Statement` from the
pushed deep dyadic-value lever (demanded only at `X > 2^986891`) plus the lever-shrunk
surfaces (re-export of `erdos260_of_deepDyadicValueLeverPush`). -/
theorem erdos260_push_deepLever_route (R : Erdos260DeepLeverPushResidual) :
    Erdos260Statement :=
  erdos260_of_deepDyadicValueLeverPush R

/-! ## Part 5.  Machine-readable status (honest) -/

/-- Honest machine-readable status of the wave-8 push capstone. -/
def erdos260PushCapstoneStatus : List String :=
  [ "MAIN ENDPOINT (wave 8): erdos260_of_pushResidual (H : Erdos260PushResidual) : " ++
      "Erdos260Statement.  Erdos260PushResidual = the scale-floor-push 14-field surface " ++
      "(no L-guard anywhere; floor X > 2^493460, L >= 493461, r >= 32 everywhere) with " ++
      "the TWO digit-valued Return fields restated in envelope-banded form.  Route: " ++
      "toScaleFloorPush -> erdos260_of_scaleFloorPush -> toFloorHarvest -> toRigidity -> " ++
      "the wave-6 digit-side chain.  Nothing re-proved; only public bridges consumed.",
    "COMPOSITION VERDICT (the honest answer): the near-periodicity module's ENVELOPE-LOW " ++
      "forcing DID compose - returnZero / returnMaxClean now demand the zero digit ONLY " ++
      "at positions whose carry sits at/above the lower band edge Q*(N+1) <= 2*R_N " ++
      "(ReturnZeroBodyBanded / ReturnMaxCleanBodyBanded); strictly-below-band positions " ++
      "are closed free by digit_forced_zero_of_carry_low through ctx.hrational " ++
      "(returnZeroBody_of_banded / returnMaxCleanBody_of_banded; per-ctx equivalences " ++
      "returnZeroBody_iff_banded / returnMaxCleanBody_iff_banded - no strength hidden).  " ++
      "What did NOT compose, and why: (a) the parity forcing " ++
      "digit_eq_parity_at_odd_position is a change of VARIABLES (digit <-> reduced-carry " ++
      "parity), not a demand reduction - the restated obligation has identical strength " ++
      "on an equally unknown trajectory, covers odd positions only, and is onset-limited " ++
      "(t <= N); no clean strictly-weaker field results.  (b) " ++
      "digit_forced_one_of_carry_high is a CONSTRAINT, not a relief: at high-band states " ++
      "the demanded zero digit is REFUTED, so the digit fields secretly demand the carry " ++
      "confinement 2*R_N <= Q*(N+3) along slice intervals (carry_upper_of_digit_zero).  " ++
      "(c) the digit-blindness results (integerCarry_mod_Q_digit_blind) touch no field - " ++
      "they refute the residue-pigeonhole supply route, they restate no obligation.  " ++
      "(d) the other 12 fields carry no digit-valued conclusions (positions, orders, " ++
      "masses, inequalities) - kept verbatim.",
    "EQUIVALENCES AND WITNESSES: nonempty_pushResidual_iff_scaleFloorPush / " ++
      "_iff_floorHarvest / _iff_bootstrap / _iff_rigidity (wave 8 = wave 7 = wave 6.5 = " ++
      "wave 6 in strength on the unconditional lane - the banding and all guard removals " ++
      "are presentation, backed by theorems); weakening witnesses " ++
      "pushResidual_of_scaleFloorPushResidual / _of_floorHarvestResidual / " ++
      "_of_bootstrapResidual / _of_rigidityResidual.",
    "CONDITIONAL ROUTES RE-EXPORTED (both PARALLEL to the unconditional surface, their " ++
      "shapes are wave-4/5): (1) the TailMatch route erdos260_push_tailMatch_route " ++
      "(h : DeepDyadicTailMatch) (surfaces : DyadicValueLever -> " ++
      "Erdos260DyadicLeverResidual) = erdos260_of_dyadicTailMatch - TailMatch (one " ++
      "centre, all depths; the section 25.1 match in all-lengths form) bridges to " ++
      "WindowPeriodic (windowPeriodic_of_tailMatch) and voids ALL pinned families " ++
      "(pinnedValue_tailMatch_void); supplying it from the in-tree (D1) residue-band " ++
      "data at a fixed centre across depths is the sharpest open frontier.  (2) the " ++
      "pushed deep-lever route erdos260_push_deepLever_route " ++
      "(R : Erdos260DeepLeverPushResidual) = erdos260_of_deepDyadicValueLeverPush - the " ++
      "dyadic-value exclusion demanded only at X > 2^986891 (the regime below is closed " ++
      "unconditionally by the pushed pinned-value floor).",
    "THE RESIDUAL SURFACE (14 fields): towerEnumLow / towerEnumTail (NO deep-shell " ++
      "guard - the last L-guard died at the pushed floor, towerDeepGuard_unconditional), " ++
      "runNumericLow / runNumericTail, returnGates (3-way ungated body), returnZero / " ++
      "returnMaxClean (BANDED digit demands, this module) / returnInterior, " ++
      "class0Survivor / class0Mid / class0BigOrder, class1DeepLow / class1DeepTail, " ++
      "densePackUngated.  All modulus-range guards (q < 107, 64 <= q, 48 <= q < 96, " ++
      "96 <= q, 101 <= q) and digit-side guards (ReturnB2FreeDatum / " ++
      "ReturnB2OneSpacedDatum / ReturnIndexWindowClean / survivor / datum / gcd) are " ++
      "floor-independent and kept verbatim.",
    "WHERE THE DIGIT FIELDS GENUINELY FIRE: not_returnIndexWindowClean_of_support_large " ++
      "- whenever Q*(F+W+2) < 2^W the index window CANNOT be clean, so the " ++
      "not-ReturnIndexWindowClean hypotheses of returnZero / returnMaxClean are " ++
      "SATISFIED there (the fields fire; the negative threshold relieves nothing, it " ++
      "certifies the demand is live).  The banded relief region (carry strictly below " ++
      "the lower envelope edge at a demanded position) is not pinned either way in-tree: " ++
      "each forced zero doubles the carry out of the low band in ~log steps, so the " ++
      "relief cannot cover whole windows - it shrinks per-position demands only.",
    "HYGIENE: additive only; no upstream module touched; no sorry / admit / new axiom / " ++
      "native_decide; all #print axioms in [propext, Classical.choice, Quot.sound]." ]

theorem erdos260PushCapstoneStatus_nonempty : erdos260PushCapstoneStatus ≠ [] := by
  simp [erdos260PushCapstoneStatus]

/-! ## Part 6.  Axiom-cleanliness audit -/

#print axioms returnZeroBody_of_banded
#print axioms returnZeroBodyBanded_of_full
#print axioms returnZeroBody_iff_banded
#print axioms returnMaxCleanBody_of_banded
#print axioms returnMaxCleanBodyBanded_of_full
#print axioms returnMaxCleanBody_iff_banded
#print axioms Erdos260PushResidual.toScaleFloorPush
#print axioms Erdos260PushResidual.toStatement
#print axioms erdos260_of_pushResidual
#print axioms pushResidual_of_scaleFloorPushResidual
#print axioms pushResidual_of_floorHarvestResidual
#print axioms pushResidual_of_bootstrapResidual
#print axioms pushResidual_of_rigidityResidual
#print axioms nonempty_pushResidual_iff_scaleFloorPush
#print axioms nonempty_pushResidual_iff_floorHarvest
#print axioms nonempty_pushResidual_iff_bootstrap
#print axioms nonempty_pushResidual_iff_rigidity
#print axioms erdos260_push_tailMatch_route
#print axioms erdos260_push_deepLever_route
#print axioms erdos260PushCapstoneStatus_nonempty

end

end Erdos260
