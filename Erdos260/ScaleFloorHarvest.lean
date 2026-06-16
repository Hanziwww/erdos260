import Erdos260.Erdos260RigidityCapstone

/-!
# Erdős 260 — the scale-floor harvest (wave 6.5)

Wave 6 proved the unconditional scale floor: every `ActualFailureContext` has
`X > 2^246736`, i.e. `L = shellLadderDepth ctx ≥ 246737`
(`shellLadderDepth_ge_246737`, `Erdos260RigidityCapstone.lean`), and `r ≥ 1`
(`n24_r_pos`).  The wave-6 synthesis only harvested the `r = 0` / `L ≤ 15420`
collapses.  This module harvests the DEEPER collapses the floor enables:

1. **The sharpened descent-order floor** `n24_r_ge_sixteen`: `r = ⌊κL⌋` with
   `κ = manuscriptKappa = 17/2^18` (`n24CarryData_r_eq_floor` / `towerKappa_eq`),
   and `⌊17·246737/262144⌋ = ⌊4194529/262144⌋ = 16`, so **`r ≥ 16` at every
   actual failure context** — the exact arithmetic the floor gives (the next
   threshold `r ≥ 17` would need `L ≥ ⌈17·262144/17⌉ = 262144 > 246737`).
2. **The K.1 gate is VOID everywhere** (`n24_K1_gate_void`, `class3Gate_void`):
   wave 6's `n24_gate_violated` proves `129L + 64 ≤ 64(r+1)(L+B+1)` at EVERY
   ctx, so the shared class-3/4/5 numeric gate `64(r+1)(L+B+1) < 129L + 64`
   never holds.  (Consistent with the wave-2 pin `not_class3Gate_of_r_ge_two`:
   `r ≥ 16 ≥ 2` already kills it; `n24_gate_violated` kills it directly.)
   Consequently the class of *gated shells* is EMPTY, so:
   * the gated-shell Return equivalences (`zResidual_iff_class4Fibre_empty`,
     `class4Interior_iff_fibre_empty`, `class3Interior_iff_densePackStarts_empty`,
     `digitResidual_iff_class4Fibre_empty`, …) are all vacuous — their gate
     hypothesis is refuted by `n24_K1_gate_void`;
   * the K.1-gate disjunct of `ReturnGatesBody` never fires —
     `ReturnGatesBodyUngated` (3-way) is EQUIVALENT
     (`returnGatesBody_iff_ungated`);
   * the `gatedEmpty` field of `DensePackGatedClosureResidual` (and of
     `DensePackDatumSplitResidual`) holds VACUOUSLY at every ctx — the
     densepack residual collapses to its three ungated components
     (`DensePackUngatedClosureResidual`, equivalence
     `nonempty_ungated_iff_gatedClosure`).
3. **The collapsed successor surface** `Erdos260FloorHarvestResidual`:
   the wave-6 `Erdos260RigidityResidual` with
   * the dead `1 ≤ r` guards dropped from `runNumericLow` / `runNumericTail` /
     `class1DeepLow` / `class1DeepTail` (they are theorems: `n24_r_pos`,
     a fortiori `n24_r_ge_sixteen`),
   * `returnGates` concluding the gate-free `ReturnGatesBodyUngated`,
   * the densepack slot at the collapsed `DensePackUngatedClosureResidual`.
   Bridge `Erdos260FloorHarvestResidual.toRigidity`, endpoint
   `erdos260_of_floorHarvest`, weakening witness
   `floorHarvestResidual_of_rigidityResidual`, equivalence
   `nonempty_floorHarvest_iff_rigidity`.

**Honestly NOT collapsed**: the tower shallow guard `towerShallowDepthBound <
L` (`L > 328965`) is NOT implied by the floor (`246737 < 328965`), so the
tower/class-2 fields keep their deep-shell guard verbatim; the modulus-range
guards (`q < 107`, `64 ≤ q`, `48 ≤ q < 96`, `96 ≤ q`, `101 ≤ q`) are
arithmetic-free of the floor and stay.

Additive only: nothing upstream is touched; only existing public lemmas are
consumed (`shellLadderDepth_ge_246737`, `n24CarryData_r_eq_floor`,
`towerKappa_eq`, `n24_gate_violated`, `n24_r_pos`,
`erdos260_of_rigidityResidual`).  No `sorry`, no `admit`, no new `axiom`, no
`native_decide`.
-/

namespace Erdos260

noncomputable section

/-! ## Part 1.  The sharpened unconditional descent-order floor: `r ≥ 16` -/

/-- **Every actual failure context has descent order `r ≥ 16`** — the exact
arithmetic of the wave-6 scale floor through the `r = ⌊κL⌋` pin:
`L ≥ 246737` (`shellLadderDepth_ge_246737`) and `κ = 17/2^18`
(`towerKappa_eq`) give `κ·L ≥ 17·246737/262144 = 4194529/262144 > 16`, so
`r = ⌊κL⌋ ≥ 16`.  (Sharp from the floor: `⌊17·246737/262144⌋ = 16`.)
Strict sharpening of `n24_r_pos` (`r ≥ 1`); unconditional counterpart of the
deep-shell `r_ge_21_of_deep` (which needs `L > 328965`). -/
theorem n24_r_ge_sixteen (ctx : ActualFailureContext) :
    16 ≤ ctx.n24CarryData.r := by
  have hL : (246737 : ℝ) ≤ (shellLadderDepth ctx : ℝ) := by
    exact_mod_cast shellLadderDepth_ge_246737 ctx
  have h16 : (16 : ℝ) ≤ manuscriptKappa * (shellLadderDepth ctx : ℝ) := by
    rw [towerKappa_eq]
    linarith
  rw [n24CarryData_r_eq_floor ctx]
  exact Nat.le_floor h16

/-! ## Part 2.  The K.1 gate is VOID at every actual failure context -/

/-- **The shared class-3/4/5 K.1 numeric gate `64(r+1)(L+B+1) < 129L + 64`
NEVER holds** — direct negation form of wave 6's `n24_gate_violated`.  This is
the single verdict that voids every gate hypothesis on the route: the
`class3Gate` guard, the class-4 gate of `zResidual_iff_class4Fibre_empty` /
`class4Interior_iff_fibre_empty` / `digitResidual_iff_class4Fibre_empty`, the
class-5 gate of `class5Fibre_window_overrun`, and the K.1-gate disjunct of
`ReturnGatesBody`.  *Gated shells do not exist.* -/
theorem n24_K1_gate_void (ctx : ActualFailureContext) :
    ¬ (64 * ((ctx.n24CarryData.r + 1)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
        < 129 * shellLadderDepth ctx + 64) :=
  not_lt.mpr (n24_gate_violated ctx)

/-- **`class3Gate` is void everywhere** (named-`Prop` form of
`n24_K1_gate_void`).  Hence every `class3Gate`-guarded field across the
DensePack surfaces holds vacuously, and every `¬ class3Gate` guard is a
theorem.  (Also derivable from the wave-2 pin `not_class3Gate_of_r_ge_two`
since `r ≥ 16 ≥ 2` by `n24_r_ge_sixteen`.) -/
theorem class3Gate_void (ctx : ActualFailureContext) : ¬ class3Gate ctx := by
  intro h
  unfold class3Gate at h
  exact n24_K1_gate_void ctx h

/-- Cross-check: the wave-2 route to the same verdict — `r ≥ 16 ≥ 2` and
`not_class3Gate_of_r_ge_two`. -/
theorem class3Gate_void_of_r_bound (ctx : ActualFailureContext) :
    ¬ class3Gate ctx :=
  not_class3Gate_of_r_ge_two ctx (le_trans (by norm_num) (n24_r_ge_sixteen ctx))

/-! ## Part 3.  Return lane: `ReturnGatesBody` loses its dead K.1-gate disjunct -/

/-- **The Return `gates` body with the dead K.1-gate disjunct removed** — the
three live disjuncts of `ReturnGatesBody` (full-span gate, sub-span gate,
orbit period-count certificate), verbatim. -/
abbrev ReturnGatesBodyUngated (ctx : ActualFailureContext) : Prop :=
  64 * (ctx.n24CarryData.a
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

/-- **The 4-way `ReturnGatesBody` is EQUIVALENT to its 3-way gate-free form**:
the K.1-gate disjunct never fires (`n24_K1_gate_void`), so it is dead weight in
both directions. -/
theorem returnGatesBody_iff_ungated (ctx : ActualFailureContext) :
    ReturnGatesBody ctx ↔ ReturnGatesBodyUngated ctx := by
  constructor
  · rintro (hgate | h | h | h)
    · exact absurd hgate (n24_K1_gate_void ctx)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))

/-! ## Part 4.  DensePack lane: the gated component is VOID — the residual
collapses to its three ungated fields -/

/-- **The `gatedEmpty` obligation of `DensePackGatedClosureResidual` (and of
`DensePackDatumSplitResidual`) is VACUOUSLY TRUE at every ctx** — its
`class3Gate` hypothesis is refuted outright.  (Stated with the full conclusion
to document the vacuity; any conclusion would do.) -/
theorem densePack_gatedEmpty_vacuous (ctx : ActualFailureContext)
    (hg : class3Gate ctx) : genuineDensePackStarts ctx = ∅ :=
  absurd hg (class3Gate_void ctx)

/-- **The collapsed densepack residual** — exactly the three UNGATED fields of
the wave-5 `DensePackGatedClosureResidual`, with the (now-theorem)
`¬ class3Gate ctx` guards dropped as well.  The gated field is gone: gated
shells do not exist (`class3Gate_void`). -/
structure DensePackUngatedClosureResidual where
  /-- Surviving-window shells with an unclosed datum whose cycle meets band 3:
  the K.1.1 coarea hit-density at the descent endpoints. -/
  ungatedDensity : ∀ ctx : ActualFailureContext,
    ¬ Class3CycleBand3Free ctx →
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
    ¬ DensePackDatumClosed ctx →
    densePackEndpointDensity ctx
  /-- Surviving-window shells with an unclosed datum whose top-band cycle
  residues meet band 3: the K.1 active-window interior containment. -/
  ungatedInterior : ∀ ctx : ActualFailureContext,
    ¬ Class3TopBandCycleFree ctx →
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
    ¬ DensePackDatumClosed ctx →
    ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r + 1
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card
  /-- Surviving-window shells with an unclosed datum whose cycle meets band 3:
  the corrected K.1.2 cover in exact `ℕ` form. -/
  ungatedCoverNat : ∀ ctx : ActualFailureContext,
    ¬ Class3CycleBand3Free ctx →
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
    ¬ DensePackDatumClosed ctx →
    (genuineDensePackStarts ctx).card
        * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
            - (2 * shellLadderDepth ctx + 1))
      ≤ (proofV4DensePackActualPoints ctx.shell).card

/-- **The collapse bridge**: the three ungated fields rebuild the FULL wave-5
gated-closure residual — `gatedEmpty` is discharged vacuously
(`class3Gate_void`), the ungated fields get their dead `¬ class3Gate` guard
for free. -/
def DensePackUngatedClosureResidual.toGatedClosure
    (R : DensePackUngatedClosureResidual) : DensePackGatedClosureResidual where
  gatedEmpty := fun ctx hg _ _ _ => absurd hg (class3Gate_void ctx)
  ungatedDensity := fun ctx _ hfree hwin hcl => R.ungatedDensity ctx hfree hwin hcl
  ungatedInterior := fun ctx _ hfree hwin hcl => R.ungatedInterior ctx hfree hwin hcl
  ungatedCoverNat := fun ctx _ hfree hwin hcl => R.ungatedCoverNat ctx hfree hwin hcl

/-- **The converse weakening**: any wave-5 gated-closure provider restricts to
the collapsed surface (the dropped `¬ class3Gate` guards are theorems). -/
def DensePackGatedClosureResidual.toUngated
    (R : DensePackGatedClosureResidual) : DensePackUngatedClosureResidual where
  ungatedDensity := fun ctx hfree hwin hcl =>
    R.ungatedDensity ctx (class3Gate_void ctx) hfree hwin hcl
  ungatedInterior := fun ctx hfree hwin hcl =>
    R.ungatedInterior ctx (class3Gate_void ctx) hfree hwin hcl
  ungatedCoverNat := fun ctx hfree hwin hcl =>
    R.ungatedCoverNat ctx (class3Gate_void ctx) hfree hwin hcl

/-- **The collapsed and gated densepack surfaces are EQUIVALENT** — the gated
component carries no content at the scale floor. -/
theorem nonempty_ungated_iff_gatedClosure :
    Nonempty DensePackUngatedClosureResidual
      ↔ Nonempty DensePackGatedClosureResidual :=
  ⟨fun ⟨R⟩ => ⟨R.toGatedClosure⟩, fun ⟨R⟩ => ⟨R.toUngated⟩⟩

/-- The collapsed surface also rebuilds the wave-4 `DensePackDatumSplitResidual`
(its gated component likewise vacuous), through the existing wave-5 bridge. -/
def DensePackUngatedClosureResidual.toDatumSplit
    (R : DensePackUngatedClosureResidual) : DensePackDatumSplitResidual :=
  R.toGatedClosure.toDatumSplit

/-! ## Part 5.  The collapsed successor surface -/

/-- **The wave-6.5 floor-harvest residual** — the wave-6
`Erdos260RigidityResidual` with every guard the scale floor kills removed:

* `runNumericLow` / `runNumericTail` / `class1DeepLow` / `class1DeepTail` lose
  the `1 ≤ r` guard (a theorem: `n24_r_pos`, a fortiori `n24_r_ge_sixteen`);
* `returnGates` concludes the gate-free 3-way `ReturnGatesBodyUngated`
  (equivalent to the 4-way body: `returnGatesBody_iff_ungated`);
* the densepack slot holds the collapsed `DensePackUngatedClosureResidual`
  (gated component void: `class3Gate_void`).

The tower deep-shell guard `towerShallowDepthBound < L` is HONESTLY kept
(`246737 < 328965`: not implied by the floor); all modulus-range guards kept
verbatim. -/
structure Erdos260FloorHarvestResidual where
  /-- Tower / class 2 — enumerated part (`q < 107`) at deep shells. -/
  towerEnumLow : ∀ ctx : ActualFailureContext,
    towerShallowDepthBound < shellLadderDepth ctx →
    TowerModulusEnumEscape ctx → (class1SlopeDatum ctx).q < 107 →
    Class2CycleInequality ctx
  /-- Tower / class 2 — tail (`107 ≤ q`): order-largeness + band-4 budget OR
  the verbatim cycle inequality. -/
  towerEnumTail : ∀ ctx : ActualFailureContext,
    towerShallowDepthBound < shellLadderDepth ctx →
    TowerModulusEnumEscape ctx →
    107 ≤ (class1SlopeDatum ctx).q →
    (((Nat.log 2 (class1SlopeDatum ctx).q + 1) * shellWidth ctx
        < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
            (class1SlopeDatum ctx).K₀)))
        ∧ TowerBand4Budget ctx)
      ∨ Class2CycleInequality ctx
  /-- Run / class 5 — enumerated part (`q < 64`); the `1 ≤ r` guard is GONE
  (`n24_r_pos`). -/
  runNumericLow : ∀ ctx : ActualFailureContext,
    (class1SlopeDatum ctx).q < 64 →
    Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx
  /-- Run / class 5 — tail (`64 ≤ q`); the `1 ≤ r` guard is GONE. -/
  runNumericTail : ∀ ctx : ActualFailureContext,
    64 ≤ (class1SlopeDatum ctx).q →
    ((Nat.log 2 (class1SlopeDatum ctx).q + 1)
        * (supportShell ctx.shell.d ctx.shell.X).card
      < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
          (class1SlopeDatum ctx).K₀)))
      ∧ RunBandBudget ctx
    ∨ Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx
  /-- Return / class 4 count gates — concluding the gate-free 3-way body. -/
  returnGates : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    2 * (129 * shellLadderDepth ctx + 64)
      ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
    ReturnGatesBodyUngated ctx
  /-- Return / class 4 digit Z — verbatim wave-6 field. -/
  returnZero : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    (∃ k ∈ olcFibre ctx,
      2 ^ carryVal2 ctx k < (supportShell ctx.shell.d ctx.shell.X).card) →
    ¬ ReturnIndexWindowClean ctx →
    ReturnZeroBody ctx
  /-- Return / class 4 clean step — verbatim wave-6 field. -/
  returnMaxClean : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnIndexWindowClean ctx → ReturnMaxCleanBody ctx
  /-- Return / class 4 K.1 interior — verbatim wave-6 field. -/
  returnInterior : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx
  /-- Chernoff / class 0 survivors — verbatim wave-6 field. -/
  class0Survivor : ∀ ctx : ActualFailureContext, Class0DatumSurvivor ctx →
    Class0SurvivorResidueMiss ctx
  /-- Chernoff / class 0 mid band — verbatim wave-6 field. -/
  class0Mid : ∀ ctx : ActualFailureContext, 48 ≤ (class1SlopeDatum ctx).q →
    (class1SlopeDatum ctx).q < 96 → Class0CycleMeetsShallow ctx →
    Class0WindowCycleCheck ctx
  /-- Chernoff / class 0 large moduli (`96 ≤ q`) — verbatim wave-6 field. -/
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
  /-- CNL / class 1 — enumerated deep part (`q < 101`); the `1 ≤ r` guard is
  GONE. -/
  class1DeepLow : ∀ ctx : ActualFailureContext,
    64 ∣ shellLadderDepth ctx →
    9 ≤ (class1SlopeDatum ctx).q →
    ((class1SlopeDatum ctx).q ≤ 15 ∨ 25 ≤ (class1SlopeDatum ctx).q) →
    (class1SlopeDatum ctx).q ∉ class1ClosedModuli →
    ¬ Class1DatumClosed ctx →
    ¬ Class1GcdWindowMiss ctx →
    (class1SlopeDatum ctx).q < 101 →
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅
  /-- CNL / class 1 — tail (`101 ≤ q`); the `1 ≤ r` guard is GONE. -/
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
  /-- DensePack / class 3 — the COLLAPSED ungated residual (gated component
  void at every ctx). -/
  densePackUngated : DensePackUngatedClosureResidual

namespace Erdos260FloorHarvestResidual

/-- **The bridge into the wave-6 rigidity surface**: dead `1 ≤ r` guards are
absorbed, the gate-free Return body upgrades to the 4-way body
(`returnGatesBody_iff_ungated`), the collapsed densepack residual rebuilds the
gated one (`toGatedClosure`).  Nothing is re-proved. -/
def toRigidity (H : Erdos260FloorHarvestResidual) : Erdos260RigidityResidual where
  towerEnumLow := H.towerEnumLow
  towerEnumTail := H.towerEnumTail
  runNumericLow := fun ctx _ hq => H.runNumericLow ctx hq
  runNumericTail := fun ctx _ hq => H.runNumericTail ctx hq
  returnGates := fun ctx h1 h2 h3 =>
    (returnGatesBody_iff_ungated ctx).mpr (H.returnGates ctx h1 h2 h3)
  returnZero := H.returnZero
  returnMaxClean := H.returnMaxClean
  returnInterior := H.returnInterior
  class0Survivor := H.class0Survivor
  class0Mid := H.class0Mid
  class0BigOrder := H.class0BigOrder
  class1DeepLow := fun ctx _ hdvd h9 hwin hcl hdc hgcd hlt =>
    H.class1DeepLow ctx hdvd h9 hwin hcl hdc hgcd hlt
  class1DeepTail := fun ctx _ hge => H.class1DeepTail ctx hge
  densePackGated := H.densePackUngated.toGatedClosure

/-- The final statement from the floor-harvest residual, through the wave-6
rigidity capstone. -/
theorem toStatement (H : Erdos260FloorHarvestResidual) : Erdos260Statement :=
  erdos260_of_rigidityResidual H.toRigidity

end Erdos260FloorHarvestResidual

/-- **The wave-6.5 final endpoint.**  `Erdos260Statement` from the collapsed
floor-harvest surface, composed through `toRigidity` into
`erdos260_of_rigidityResidual` (hence through the wave-6 `toDigitSide` chain)
with no re-proving anywhere on the route. -/
theorem erdos260_of_floorHarvest (H : Erdos260FloorHarvestResidual) :
    Erdos260Statement :=
  H.toStatement

/-- **The weakening witness**: any wave-6 rigidity provider yields the
floor-harvest residual — the dropped `1 ≤ r` guards are supplied by
`n24_r_pos`, the dead gate disjunct is stripped by
`returnGatesBody_iff_ungated`, the densepack gated residual restricts to its
ungated core.  The new presentation hides no strength. -/
def floorHarvestResidual_of_rigidityResidual (R : Erdos260RigidityResidual) :
    Erdos260FloorHarvestResidual where
  towerEnumLow := R.towerEnumLow
  towerEnumTail := R.towerEnumTail
  runNumericLow := fun ctx hq => R.runNumericLow ctx (n24_r_pos ctx) hq
  runNumericTail := fun ctx hq => R.runNumericTail ctx (n24_r_pos ctx) hq
  returnGates := fun ctx h1 h2 h3 =>
    (returnGatesBody_iff_ungated ctx).mp (R.returnGates ctx h1 h2 h3)
  returnZero := R.returnZero
  returnMaxClean := R.returnMaxClean
  returnInterior := R.returnInterior
  class0Survivor := R.class0Survivor
  class0Mid := R.class0Mid
  class0BigOrder := R.class0BigOrder
  class1DeepLow := fun ctx hdvd h9 hwin hcl hdc hgcd hlt =>
    R.class1DeepLow ctx (n24_r_pos ctx) hdvd h9 hwin hcl hdc hgcd hlt
  class1DeepTail := fun ctx hge => R.class1DeepTail ctx (n24_r_pos ctx) hge
  densePackUngated := R.densePackGated.toUngated

/-- **The two surfaces are EQUIVALENT** — the wave-6.5 residual is exactly the
wave-6 one with the floor-killed guards folded in. -/
theorem nonempty_floorHarvest_iff_rigidity :
    Nonempty Erdos260FloorHarvestResidual ↔ Nonempty Erdos260RigidityResidual :=
  ⟨fun ⟨H⟩ => ⟨H.toRigidity⟩,
   fun ⟨R⟩ => ⟨floorHarvestResidual_of_rigidityResidual R⟩⟩

/-- The floor-harvest residual directly from any digit-side provider (through
the wave-6 weakening witness). -/
def floorHarvestResidual_of_digitSideResidual (R : DigitSideEnumResidual) :
    Erdos260FloorHarvestResidual :=
  floorHarvestResidual_of_rigidityResidual
    (rigidityResidual_of_digitSideResidual R)

/-! ## Part 6.  Machine-readable status -/

/-- Machine-readable status of the wave-6.5 scale-floor harvest. -/
def scaleFloorHarvestStatus : List String :=
  [ "SHARPENED r BOUND (proved) - n24_r_ge_sixteen: EVERY ActualFailureContext has descent " ++
      "order r >= 16, from the wave-6 scale floor L >= 246737 (shellLadderDepth_ge_246737) " ++
      "through the pin r = floor(kappa*L) (n24CarryData_r_eq_floor, kappa = 17/2^18 = " ++
      "17/262144, towerKappa_eq): 17*246737 = 4194529 >= 16*262144 = 4194304.  SHARP from " ++
      "the floor: floor(4194529/262144) = 16 (r >= 17 would need L >= 262144 > 246737).  " ++
      "Strict sharpening of n24_r_pos (r >= 1); unconditional counterpart of r_ge_21_of_deep " ++
      "(which needs L > 328965).",
    "GATE VERDICT (proved) - n24_K1_gate_void / class3Gate_void (cross-check " ++
      "class3Gate_void_of_r_bound via not_class3Gate_of_r_ge_two at r >= 16 >= 2): the shared " ++
      "class-3/4/5 K.1 numeric gate 64(r+1)(L+B+1) < 129L+64 NEVER holds - wave 6's " ++
      "n24_gate_violated already proves 129L+64 <= 64(r+1)(L+B+1) at EVERY ctx, so the gate " ++
      "disjuncts/guards everywhere are dead weight.  GATED SHELLS DO NOT EXIST: the " ++
      "gated-shell equivalences zResidual_iff_class4Fibre_empty / " ++
      "class4Interior_iff_fibre_empty / digitResidual_iff_class4Fibre_empty / " ++
      "class3Interior_iff_densePackStarts_empty are all vacuous (gate hypothesis refuted).",
    "RETURN LANE COLLAPSE (proved) - ReturnGatesBodyUngated (3-way) EQUIVALENT to the 4-way " ++
      "ReturnGatesBody (returnGatesBody_iff_ungated): the K.1-gate disjunct never fires; the " ++
      "live content is the full-span gate, the sub-span gate, and the orbit period-count " ++
      "certificate.  returnZero / returnMaxClean / returnInterior carry no gate or r-guard " ++
      "and pass verbatim.",
    "DENSEPACK LANE COLLAPSE (proved) - densePack_gatedEmpty_vacuous: the gatedEmpty field " ++
      "of DensePackGatedClosureResidual (and DensePackDatumSplitResidual) holds vacuously at " ++
      "every ctx (gated needs class3Gate, but the gate is void).  Collapsed surface " ++
      "DensePackUngatedClosureResidual = the three ungated fields with their (now-theorem) " ++
      "not-class3Gate guards dropped; bridges toGatedClosure / toUngated / toDatumSplit; " ++
      "EQUIVALENCE nonempty_ungated_iff_gatedClosure.",
    "GUARDS COLLAPSED IN THE SUCCESSOR SURFACE (exact list): (1) 1 <= r dropped from " ++
      "runNumericLow, runNumericTail, class1DeepLow, class1DeepTail (theorem n24_r_pos, a " ++
      "fortiori n24_r_ge_sixteen); (2) the K.1-gate disjunct dropped from the returnGates " ++
      "conclusion (returnGatesBody_iff_ungated); (3) the gatedEmpty densepack field dropped " ++
      "and the not-class3Gate guards dropped from the three ungated densepack fields " ++
      "(class3Gate_void).  All r = 0 / L <= 15420 / L <= 246736 guards were already vacuous " ++
      "upstream (wave 6).",
    "HONESTLY NOT COLLAPSED: the tower deep-shell guard towerShallowDepthBound < L " ++
      "(L > 328965) - NOT implied by the floor (246737 < 328965), kept verbatim on " ++
      "towerEnumLow / towerEnumTail; all modulus-range guards (q < 107, 64 <= q, " ++
      "48 <= q < 96, 96 <= q, 101 <= q) and the digit-side guards " ++
      "(ReturnB2FreeDatum / ReturnIndexWindowClean / survivor / datum / gcd guards) are " ++
      "floor-independent and kept verbatim.",
    "FINAL ENDPOINT (wave 6.5): erdos260_of_floorHarvest (H : Erdos260FloorHarvestResidual) " ++
      ": Erdos260Statement, composed through toRigidity into erdos260_of_rigidityResidual " ++
      "(wave-6 toDigitSide chain); weakening witness floorHarvestResidual_of_rigidityResidual " ++
      "(also floorHarvestResidual_of_digitSideResidual), EQUIVALENCE " ++
      "nonempty_floorHarvest_iff_rigidity.  Additive only; nothing upstream touched; no " ++
      "sorry / admit / new axiom / native_decide." ]

theorem scaleFloorHarvestStatus_nonempty : scaleFloorHarvestStatus ≠ [] := by
  simp [scaleFloorHarvestStatus]

/-! ## Axiom-cleanliness audit -/

#print axioms n24_r_ge_sixteen
#print axioms n24_K1_gate_void
#print axioms class3Gate_void
#print axioms class3Gate_void_of_r_bound
#print axioms returnGatesBody_iff_ungated
#print axioms densePack_gatedEmpty_vacuous
#print axioms DensePackUngatedClosureResidual.toGatedClosure
#print axioms DensePackGatedClosureResidual.toUngated
#print axioms nonempty_ungated_iff_gatedClosure
#print axioms DensePackUngatedClosureResidual.toDatumSplit
#print axioms Erdos260FloorHarvestResidual.toRigidity
#print axioms Erdos260FloorHarvestResidual.toStatement
#print axioms erdos260_of_floorHarvest
#print axioms floorHarvestResidual_of_rigidityResidual
#print axioms nonempty_floorHarvest_iff_rigidity
#print axioms floorHarvestResidual_of_digitSideResidual
#print axioms scaleFloorHarvestStatus_nonempty

end

end Erdos260
