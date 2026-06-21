import Erdos260.Erdos260AnchoredCapstone
import Erdos260.LedgerCalibrationAudit
import Erdos260.ExitMassTranscription
import Erdos260.OffFibreMissClosure

/-!
# The corrected-ledger capstone — the wave-16 fold (`Erdos260CorrectedLedgerCapstone`)

This module (NEW; it edits no existing file) folds the wave-16 deliverables —
`LedgerCalibrationAudit` (over-transcription #4: the class-1 emptiness razor is an
artifact of the frozen `termCnl`; the corrected term `(31/1536)·X` de-razors the class-1
lane and the re-based bridge `CorrectedP9CtxPinnedLedgerResidual.toStatement` reaches
`Erdos260Statement`), `ExitMassTranscription` (over-transcription #3: `runNumeric` is
FALSE at band-4-pinned contexts; the honest Section 26 content is the band-4-free
conjunct), and `OffFibreMissClosure` (all 19 class-0 survivor demands ARE per-pair fibre
emptiness) — into a single successor surface above `Erdos260AnchoredResidual`.

## The fold verdict (honest — read this first)

* **Class 1 (THE BIG FOLD — the corrected ledger)**: the two anchored deep fields
  `class1DeepLow`/`class1DeepTail` (whose conclusion is OUTRIGHT fibre emptiness — the
  razor demand the source text never makes) are REPLACED by the single strictly weaker
  count-cap absorption field
  `class1CapAbsorption : ∀ ctx, 1 ≤ r → card(fibre₁)·Y ≤ (c⋆ξ/6)·X` — exactly the
  corrected class-1 ledger bound of `CorrectedP9CtxPinnedLedgerResidual` on the genuine
  route (`routedClassMass_one_eq_card_mul_Y` + `termCnl_corrected_eq`).  The `r = 0`
  shells (ALL `L ≤ 15420`) are relieved FREE (`class1Fibre_card_le_one_of_r_eq_zero` +
  `Y < (31/1536)·X`).  The assembly is a PARALLEL ledger walk: the class-1 lane goes
  through `CorrectedP9CtxPinnedLedgerResidual.ofGenuineCaps → toStatement`, BYPASSING
  the frozen-term consumer `P9CtxPinnedLedgerResidual` entirely; the class-0/3 caps and
  the TRT/oldRes closures are budget-generic and transport unchanged.
* **THE GATE ARITHMETIC, VERIFIED (honest — the brief's `~4.9M·c` is CORRECTED)**: on
  the genuine route the absorption gate is exactly the ℕ inequality `24·n·L ≤ 31·X`
  for any proved count cap `n` (`correctedAbsorption_of_nat_gate`).  For the wave-14
  per-pair cycle-density caps `n = b₄·⌈W/c⌉` with the failure cap `2²⁴·W < 17·X`, the
  gate closes under the L-regime hypotheses of
  `correctedAbsorption_of_cycleDensity_regime` — sharp regime
  `408·b₄·L ≲ 31·2²⁴·c`, i.e. `L ≲ 1 274 739·c/b₄` (NOT `4.9M·c`: the brief's figure
  double-counts a factor `64/1536 → 1/24`; the correct constant is
  `31·2²⁴/(24·17) = 520093696/408 ≈ 1.27·10⁶`).  Since every class-1 survivor pair
  carries band 4 ON its cycle (`b₄ ≥ 1` — that is WHY it survived the band-4-free
  sweep), the caps do NOT pass at all scales: shells with
  `L > ~1.27M·c/b₄` remain open on the absorption axis.  What genuinely folds is the
  FIELD WEAKENING (emptiness → absorption); the per-pair cap closures enter as the
  conditional regime lemmas below, not as field deletions.  No per-pair instantiation
  is attempted here: the 87 survivor pairs carry no in-tree certified periods/band-4
  counts (the sweep certified only the CLOSED pairs), and enumerating 87 orbits is out
  of additive scope — recorded honestly.
* **Run / class 5 (the L.4-faithful split — equal total strength, honest
  re-foliation)**: `runNumericField_iff_band4Void_split` proved the formalized run
  field IS (band-4 orbit-pin voiding) ∧ (the field on band-4-free contexts), and
  `band4_pinned_not_runNumericIneq` proved the first conjunct is UNAVOIDABLE (the field
  is FALSE at every band-4-pinned context).  The surface therefore splits the lane
  honestly: `runNumericLow`/`runNumericTail` keep the anchored shapes GUARDED by
  `¬ OrbitBandPinned ctx 4` (the honest Section 26 content), and the voiding is the
  separate named field `runBand4Void : ∀ ctx, ¬ OrbitBandPinned ctx 4` — the
  tower-lane-routed demand (the manuscript routes the band-4 recurrent data through
  L.3/M.5, not Section 26).  HONEST: this is a re-foliation, NOT a weakening — the old
  fields imply all three new ones (`runCycleNumericField_settled` +
  `runNumericIneq_not_band4`), and the new three rebuild the old walk verbatim; total
  strength is unchanged, but the over-transcribed conjunct is now visible and
  separately supplied.  Under the voiding the five fixed families collapse to
  `(3,1)/(21,3)` (`correctedCapstone_fixedFamilyHit_collapse`).
* **Class 0 (the unification)**: the three anchored class-0 lanes
  (`class0Survivor`/`class0Mid`/`class0BigOrder`) are UNIFIED into the single field
  `class0Fibre` speaking ONE language — per-ctx fibre emptiness
  `routedFibre … 0 = ∅` — via the modulus-free bridge
  `ofcClass0Fibre_empty_iff_windowCycleCheck` and the survivor equivalences
  (`ofcResidueMiss_iff_class0Empty_of_survivor`: at all 19 survivor pairs the
  residue-miss demand IS emptiness).  The big-order escape certificate is kept as a
  disjunct (dropping it would STRENGTHEN the demand — honest).
* **What did NOT fold**: `towerEnumLow`/`towerEnumTail`, `returnGates`/
  `returnInterior`, and `densePackUngated` are VERBATIM anchored fields (the wave-16
  modules supply no field change there); the band-4 voiding is NOT dropped — it is the
  honest unavoidable content of the old run lane, now named.

## DIRECTION OF STRENGTH (honest)

`Erdos260ReturnChargeResidual → Erdos260AnchoredCountResidual → Erdos260AnchoredResidual
→ Erdos260CorrectedResidual` (`correctedResidual_of_anchoredResidual`, this module) —
each step one-directional downward; NO converse is claimed.  The class-1 step is a
genuine weakening (emptiness → absorption); the run step is an equal-strength honest
re-foliation; the class-0 step is an equivalence in better coordinates.  The endpoint
`erdos260_of_correctedResidual` walks the corrected ledger
(`CorrectedP9CtxPinnedLedgerResidual`), not the frozen one.

No `sorry`, no `admit`, no new `axiom`, no `native_decide`; additive only — no existing
module is edited (the root import file gains one line).
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 1.  The corrected absorption gate, quantified

The class-1 routed mass on the genuine route is `card(fibre₁)·Y`
(`routedClassMass_one_eq_card_mul_Y`) and the corrected capacity is `(31/1536)·X`
(`termCnl_corrected_eq` + `correctedCnlShare_eq`), so with `Y = L/64`
(`n24CarryData_Y_eq_div`) the absorption gate for a proved count cap `n` is EXACTLY the
ℕ inequality `24·n·L ≤ 31·X`. -/

/-- **The ℕ form of the corrected absorption gate**: any proved class-1 count cap `n`
with `24·n·L ≤ 31·X` closes the corrected class-1 capacity bound (in its count-cap
form `card·Y ≤ termCnl(corrected)`). -/
theorem correctedAbsorption_of_nat_gate
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) (n : ℕ)
    (hcard : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card ≤ n)
    (hgate : 24 * (n * shellLadderDepth ctx) ≤ 31 * ctx.shell.X) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ termCnl (correctedCapacityPhases budget ctx).toClosurePhaseData := by
  rw [termCnl_corrected_eq budget ctx, correctedCnlShare_eq, n24CarryData_Y_eq_div]
  have hcardR : ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
      ≤ (n : ℝ) := by exact_mod_cast hcard
  have hgateR : (24 : ℝ) * ((n : ℝ) * ((shellLadderDepth ctx : ℕ) : ℝ))
      ≤ 31 * ((ctx.shell.X : ℕ) : ℝ) := by exact_mod_cast hgate
  have hL0 : (0 : ℝ) ≤ ((shellLadderDepth ctx : ℕ) : ℝ) := Nat.cast_nonneg _
  have h1 : ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * (((shellLadderDepth ctx : ℕ) : ℝ) / 64)
      ≤ (n : ℝ) * (((shellLadderDepth ctx : ℕ) : ℝ) / 64) := by
    apply mul_le_mul_of_nonneg_right hcardR
    positivity
  linarith

/-- **The cycle-density cap under the regime gate** (the wave-16 verified arithmetic):
with a certified orbit period `c`, the wave-14 per-pair cap `b₄·⌈W/c⌉`
(`class1Fibre_card_le_cycleDensity`) absorbs into the corrected capacity whenever the
two ℕ regime hypotheses hold — the main regime `408·b₄·L ≤ 15·2²⁴·c` (about HALF the
sharp budget `31·2²⁴·c ≈ 1.27·10⁶·c/b₄`-many `L`) and the scale-slack
`24·b₄·c·L ≤ 16·X` (negligible at `X = 2^L`).  The failure cap `2²⁴·W < 17·X` supplies
the support-count input.  HONEST: the regime is `L`-bounded — deep shells fail it. -/
theorem correctedAbsorption_of_cycleDensity_regime
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) {c : ℕ} (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hmain : 408 * ((class1Band4CycleBand ctx c).card * shellLadderDepth ctx)
        ≤ 251658240 * c)
    (hslack : 24 * ((class1Band4CycleBand ctx c).card * (c * shellLadderDepth ctx))
        ≤ 16 * ctx.shell.X) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ termCnl (correctedCapacityPhases budget ctx).toClosurePhaseData := by
  refine correctedAbsorption_of_nat_gate budget ctx
    ((class1Band4CycleBand ctx c).card
      * (((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c))
    (class1Fibre_card_le_cycleDensity ctx hc hper) ?_
  set b4 := (class1Band4CycleBand ctx c).card with hb4def
  set W := (supportShell ctx.shell.d ctx.shell.X).card with hWdef
  set L := shellLadderDepth ctx with hLdef
  set X := ctx.shell.X with hXdef
  -- the period-block collapse: c·(b₄·⌈W/c⌉) ≤ b₄·(W + c)
  have hdiv : (W + c - 1) / c * c ≤ W + c - 1 := Nat.div_mul_le_self _ _
  have hcc : c * (b4 * ((W + c - 1) / c)) ≤ b4 * (W + c) := by
    calc c * (b4 * ((W + c - 1) / c))
        = b4 * ((W + c - 1) / c * c) := by ring
      _ ≤ b4 * (W + c - 1) := Nat.mul_le_mul le_rfl hdiv
      _ ≤ b4 * (W + c) := Nat.mul_le_mul le_rfl (by omega)
  -- the failure cap: 2²⁴·W ≤ 17·X
  have hW16 : 16777216 * W ≤ 17 * X := le_of_lt (em_supportShell_strict ctx)
  have hXc : X ≤ c * X := Nat.le_mul_of_pos_left X hc
  have key : 16777216 * c * (24 * (b4 * ((W + c - 1) / c) * L))
      ≤ 16777216 * c * (31 * X) := by
    calc 16777216 * c * (24 * (b4 * ((W + c - 1) / c) * L))
        = 24 * L * 16777216 * (c * (b4 * ((W + c - 1) / c))) := by ring
      _ ≤ 24 * L * 16777216 * (b4 * (W + c)) := Nat.mul_le_mul le_rfl hcc
      _ = 24 * (L * b4) * (16777216 * W) + 16777216 * (24 * (b4 * (c * L))) := by
          ring
      _ ≤ 24 * (L * b4) * (17 * X) + 16777216 * (16 * X) :=
          Nat.add_le_add (Nat.mul_le_mul le_rfl hW16) (Nat.mul_le_mul le_rfl hslack)
      _ = 408 * (b4 * L) * X + 268435456 * X := by ring
      _ ≤ 251658240 * c * X + 268435456 * (c * X) :=
          Nat.add_le_add (Nat.mul_le_mul hmain le_rfl)
            (Nat.mul_le_mul le_rfl hXc)
      _ = 16777216 * c * (31 * X) := by ring
  have hpos : 0 < 16777216 * c := by positivity
  exact Nat.le_of_mul_le_mul_left key hpos

/-! ## Part 2.  The successor surface (`Erdos260CorrectedResidual`)

`Erdos260AnchoredResidual` with three lanes re-cut: the class-1 deep pair replaced by
the corrected-gate absorption field (strictly weaker), the run pair guarded by the
band-4-free restriction with the voiding as its own named field (equal strength,
honest), and the three class-0 lanes unified into one emptiness field (equivalent in
better coordinates).  10 fields. -/

/-- **The wave-16 corrected-ledger capstone surface.**  10 fields; the class-1 lane is
consumed by the CORRECTED P9 ledger (`CorrectedP9CtxPinnedLedgerResidual`) — the
frozen-term razor is gone from the surface. -/
structure Erdos260CorrectedResidual where
  /-- Tower / class 2 - enumerated part (`q < 107`); verbatim anchored field (relieved
  at the band-pinned fixed data `(3,1)` and `(21,3)`). -/
  towerEnumLow : ∀ ctx : ActualFailureContext,
    TowerModulusEnumEscapeV2 ctx → (class1SlopeDatum ctx).q < 107 →
    (ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx) →
    ¬ ((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1) →
    ¬ ((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3) →
    Class2CycleInequality ctx
  /-- Tower / class 2 - tail (`107 ≤ q`); verbatim anchored field. -/
  towerEnumTail : ∀ ctx : ActualFailureContext,
    TowerModulusEnumEscapeV2 ctx →
    107 ≤ (class1SlopeDatum ctx).q →
    (ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx) →
    (((Nat.log 2 (class1SlopeDatum ctx).q + 1) * shellWidth ctx
        < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
            (class1SlopeDatum ctx).K₀)))
        ∧ TowerBand4Budget ctx)
      ∨ Class2CycleInequality ctx
  /-- **The band-4 orbit-pin voiding** (NEW; the tower-lane-routed conjunct of the run
  split): no context pins the slope orbit at band 4.  PROVABLY contained in the old run
  fields (`runNumericIneq_not_band4`); the manuscript routes this data through L.3/M.5,
  not Section 26 — it is named separately so the run fields below can carry the honest
  Section 26 content only. -/
  runBand4Void : ∀ ctx : ActualFailureContext, ¬ OrbitBandPinned ctx 4
  /-- Run / class 5 - enumerated part (`q < 64`), restricted to band-4-free contexts
  (the honest Section 26 content — the corrected conjunct of
  `runNumericField_iff_band4Void_split`). -/
  runNumericLow : ∀ ctx : ActualFailureContext,
    ¬ OrbitBandPinned ctx 4 →
    (class1SlopeDatum ctx).q < 64 →
    Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx
  /-- Run / class 5 - tail (`64 ≤ q`), restricted to band-4-free contexts; relieved of
  `(93,15)` as in the anchored surface. -/
  runNumericTail : ∀ ctx : ActualFailureContext,
    ¬ OrbitBandPinned ctx 4 →
    64 ≤ (class1SlopeDatum ctx).q →
    ¬ ((class1SlopeDatum ctx).q = 93 ∧ (class1SlopeDatum ctx).K₀ = 15) →
    ((Nat.log 2 (class1SlopeDatum ctx).q + 1)
        * (supportShell ctx.shell.d ctx.shell.X).card
      < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
          (class1SlopeDatum ctx).K₀)))
      ∧ RunBandBudget ctx
    ∨ Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx
  /-- Return / class 4 count gates - verbatim anchored field. -/
  returnGates : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    2 * (129 * shellLadderDepth ctx + 64)
      ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
    ReturnGatesBodyUngated ctx
  /-- Return / class 4 K.1 interior - verbatim anchored field. -/
  returnInterior : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx
  /-- **The unified class-0 emptiness field** (the wave-16 unification): the three
  anchored lanes (survivor / mid / big-order) in ONE language — per-ctx class-0 fibre
  emptiness.  At survivors this is EXACTLY the old residue-miss/off-fibre demand
  (`ofcResidueMiss_iff_class0Empty_of_survivor`); on the mid band it is exactly the
  windowed check (`ofcClass0Fibre_empty_iff_windowCycleCheck`); the big-order escape
  certificate is KEPT as a disjunct (dropping it would strengthen the demand). -/
  class0Fibre : ∀ ctx : ActualFailureContext,
    (Class0DatumSurvivor ctx →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0 = ∅) ∧
    (48 ≤ (class1SlopeDatum ctx).q → (class1SlopeDatum ctx).q < 96 →
      Class0CycleMeetsShallow ctx →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0 = ∅) ∧
    (96 ≤ (class1SlopeDatum ctx).q →
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
      ∨ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0 = ∅)
  /-- **The corrected class-1 absorption field** (the wave-16 de-razoring): the count-cap
  absorption `card(fibre₁)·Y ≤ (c⋆ξ/6)·X = (31/1536)·X` — the CORRECTED ledger bound on
  the genuine route, strictly weaker than the anchored deep fields' outright emptiness.
  The `r = 0` shells (all `L ≤ 15420`) are relieved FREE; the gate lemmas above supply
  the proved count-cap routes. -/
  class1CapAbsorption : ∀ ctx : ActualFailureContext,
    1 ≤ ctx.n24CarryData.r →
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ)
  /-- DensePack / class 3 - verbatim anchored field. -/
  densePackUngated : DensePackUngatedClosureResidual

namespace Erdos260CorrectedResidual

/-! ### The tower lane (verbatim anchored walk) -/

/-- Tower lane — the wave-5 enumeration residual (the anchored walk verbatim). -/
def towerEnum (R : Erdos260CorrectedResidual) : TowerModulusEnumerationResidual := by
  intro ctx _hdeep hesc
  have hescV2 : TowerModulusEnumEscapeV2 ctx :=
    (towerModulusEnumEscape_iff_v2 ctx).mp hesc
  have haper : ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx := fun hu7 hwp =>
    thirdsLever_windowPeriodic_void_of_oddpartQ_le_seven ctx hu7 hwp
  rcases Nat.lt_or_ge (class1SlopeDatum ctx).q 107 with hlt | hge
  · by_cases h31 : (class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1
    · exact anchoredCapstone_class2Ineq_of_datum_3_1 ctx h31.1 h31.2
    · by_cases h213 : (class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3
      · exact anchoredCapstone_class2Ineq_of_datum_21_3 ctx h213.1 h213.2
      · exact R.towerEnumLow ctx hescV2 hlt haper h31 h213
  · cases R.towerEnumTail ctx hescV2 hge haper with
    | inl ho => exact towerTail_of_order_gt ctx ho.1 ho.2
    | inr hineq => exact hineq

/-- The V3 tower count of the budget (verbatim walk). -/
def towerCountV3 (R : Erdos260CorrectedResidual) :
    ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx :=
  p9V3TowerCount_ofShallowDeep
    (towerDeepResidual_ofCountBound (towerCountBound_of_modulusEnumeration R.towerEnum))

/-! ### The run lane (the corrected split: the voiding discharges the guards) -/

/-- Run lane — the wave-5 settlement hypothesis: the band-4-free conjunct fields with
their guards discharged by the voiding field, then the anchored dispatch verbatim. -/
def runNumeric (R : Erdos260CorrectedResidual) : RunCycleNumericSettlementHyp := by
  intro ctx _hr
  have hnp : ¬ OrbitBandPinned ctx 4 := R.runBand4Void ctx
  rcases Nat.lt_or_ge (class1SlopeDatum ctx).q 64 with hlt | hge
  · exact R.runNumericLow ctx hnp hlt
  · by_cases h93 : (class1SlopeDatum ctx).q = 93 ∧ (class1SlopeDatum ctx).K₀ = 15
    · exact Or.inr (ftRunCloses_of_datum_93_15 ctx h93.1 h93.2)
    · cases R.runNumericTail ctx hnp hge h93 with
      | inl ho => exact Or.inr (runTail_of_order_gt ctx ho.1 ho.2)
      | inr hrun => exact hrun

/-- The Run max-core family of the budget (verbatim walk). -/
def runCore (R : Erdos260CorrectedResidual) :
    ∀ ctx : ActualFailureContext, RunClass5LeafSupportMaxCoreResidual ctx :=
  fun ctx => (runSplitOfNumeric (runCycleNumericField_settled R.runNumeric) ctx).toCore

/-- The V3 run chain of the budget (verbatim walk). -/
def runChain (R : Erdos260CorrectedResidual) :
    ∀ ctx : ActualFailureContext, RunClass5StageChain ctx :=
  p9V3RunChainOfResidual (runClass5LeafResidual_ofSupportMaxCoreResidual R.runCore)

/-! ### The Return lane (verbatim anchored walk — the wave-15a closure carried) -/

/-- The wave-3 4-way gate disjunction from the surface gates field (verbatim walk). -/
def returnGatesCycle (R : Erdos260CorrectedResidual) :
    ∀ ctx : ActualFailureContext, ReturnGatesBody ctx := fun ctx => by
  by_cases hfree : ReturnB2FreeDatum ctx
  · exact (returnCtxAllFour_of_b2FreeDatum ctx hfree).1
  · by_cases hone : ReturnB2OneSpacedDatum ctx
    · exact (returnGatesZeroCard_of_b2OneSpacedDatum ctx hone).1
    · by_cases hnum : 64 * (((supportShell ctx.shell.d ctx.shell.X).card
            + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
          < 2 * (129 * shellLadderDepth ctx + 64)
      · exact returnGatesBody_of_reach_numeric ctx hnum
      · exact (returnGatesBody_iff_ungated ctx).mpr
          (R.returnGates ctx hfree hone (not_lt.mp hnum))

/-- The class-4 population bound `|olcFibre| ≤ r + 1` from the gates. -/
theorem fibreSmall (R : Erdos260CorrectedResidual) : Class4FibreSmall :=
  class4FibreSmall_of_gates R.returnGatesCycle

/-- The per-ctx K.1 interior (verbatim walk). -/
def interiorAt (R : Erdos260CorrectedResidual) (ctx : ActualFailureContext) :
    ReturnInteriorBody ctx := by
  by_cases hfree : ReturnB2FreeDatum ctx
  · exact (returnCtxAllFour_of_b2FreeDatum ctx hfree).2.2.2
  · exact R.returnInterior ctx hfree

/-- The Return slot — the wave-15a unconditional charge from the counts alone. -/
def returnCharge (R : Erdos260CorrectedResidual) :
    ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx :=
  fun ctx => Class4ReturnPerSliceCharge.ofCountsOnly ctx (R.interiorAt ctx) (R.fibreSmall ctx)

/-! ### The budget and the class-0/3 caps -/

/-- **The corrected budget** — `v3Budget` with the Return slot carried by the
unconditional charge (identical in shape to the anchored budget). -/
def budget (R : Erdos260CorrectedResidual) :
    ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx :=
  v3Budget R.towerCountV3 R.runChain R.returnCharge

/-- The class-0 windowed check at every context, from the unified emptiness field
through the wave-16 bridges (`ofcResidueMiss_iff_class0Empty_of_survivor`,
`ofcClass0Fibre_empty_iff_windowCycleCheck`) and the big-order escape. -/
def class0Cycle (R : Erdos260CorrectedResidual) :
    ∀ ctx : ActualFailureContext, Class0WindowCycleCheck ctx :=
  class0Cycle_of_survivor_residue_split
    (fun ctx hsurv =>
      (ofcResidueMiss_iff_class0Empty_of_survivor ctx hsurv).mpr
        ((R.class0Fibre ctx).1 hsurv))
    (fun ctx h48 h96 hmeet =>
      (ofcClass0Fibre_empty_iff_windowCycleCheck ctx).mp
        ((R.class0Fibre ctx).2.1 h48 h96 hmeet))
    (fun ctx h96 => by
      cases (R.class0Fibre ctx).2.2 h96 with
      | inl hcert =>
          obtain ⟨C, horder, hcheck⟩ := hcert
          exact class0Tail_of_order_gt ctx C horder hcheck
      | inr hempty => exact (ofcClass0Fibre_empty_iff_windowCycleCheck ctx).mp hempty)

/-- Class-0 routed emptiness at the corrected budget (budget-generic bridge). -/
theorem class0Empty (R : Erdos260CorrectedResidual) : Class0FibreEmpty R.budget :=
  class0FibreEmpty_of_genuineRoute_pinned R.budget (fun _ => rfl)
    (class0Pinned_field_iff_windowCycleCheck.mpr R.class0Cycle)

/-- The corrected DensePack residue at the corrected budget (budget-generic walk). -/
def densePackCorrected (R : Erdos260CorrectedResidual) :
    DensePackCorrectedResidue R.budget :=
  (R.densePackUngated.toGatedClosure.toDatumSplit.toCycleSplit.toRegimeSplit R.budget).toCorrected

/-- Direct class-3 ledger field from the corrected DensePack surface.  This names the
support-count contribution used by TeX L.1/L.3 before it is consumed by the corrected
P9 ledger. -/
theorem densePackLedgerField (R : Erdos260CorrectedResidual) :
    ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (R.budget ctx).route 3
        ≤ termDensePack (faithfulCapacityPhases R.budget ctx).toClosurePhaseData :=
  R.densePackCorrected.hDensePackField (fun _ => rfl)

/-! ### The corrected class-1 cap and the parallel ledger assembly -/

/-- **The full count-cap absorption** at every context: `r = 0` shells close FREE
(`|fibre₁| ≤ 1` and `Y < (31/1536)·X`); `r ≥ 1` shells from the surface field. -/
theorem hcapAll (R : Erdos260CorrectedResidual) (ctx : ActualFailureContext) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ termCnl (correctedCapacityPhases R.budget ctx).toClosurePhaseData := by
  rcases Nat.eq_zero_or_pos ctx.n24CarryData.r with hr0 | hr1
  · have hcard : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card ≤ 1 :=
      class1Fibre_card_le_one_of_r_eq_zero ctx hr0
    have hcardR : ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        ≤ 1 := by exact_mod_cast hcard
    have hY0 : (0 : ℝ) ≤ ctx.n24CarryData.Y := le_of_lt (n24CarryData_Y_pos ctx)
    calc ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
          * ctx.n24CarryData.Y
        ≤ 1 * ctx.n24CarryData.Y := mul_le_mul_of_nonneg_right hcardR hY0
      _ = ctx.n24CarryData.Y := one_mul _
      _ ≤ termCnl (correctedCapacityPhases R.budget ctx).toClosurePhaseData :=
          le_of_lt (Y_lt_termCnl_corrected R.budget ctx)
  · rw [termCnl_corrected_eq R.budget ctx]
    exact R.class1CapAbsorption ctx hr1

/-- **The corrected ctx-pinned P9 ledger from the wave-16 surface** — the PARALLEL
assembly: class-0 Chernoff and class-3 DensePack caps exactly as in the anchored walk
(the faithful terms are `rfl`-unchanged by the correction), `hTRT`/`hOldRes` closed
generically, and the class-1 lane carried by the count-cap absorption against the
CORRECTED capacity `(31/1536)·X`.  The frozen-term consumer
(`P9CtxPinnedLedgerResidual`) is BYPASSED. -/
def toCorrectedLedger (R : Erdos260CorrectedResidual) :
    CorrectedP9CtxPinnedLedgerResidual :=
  CorrectedP9CtxPinnedLedgerResidual.ofGenuineCaps R.budget (fun _ => rfl)
    (ChernoffGenuineAreaKraftSmallResidual.ofClass0FibreEmpty R.budget
      R.class0Empty).hChernoffField
    R.densePackLedgerField
    R.hcapAll

/-- The final statement from the wave-16 surface, through the re-based corrected
ledger bridge (`CorrectedP9CtxPinnedLedgerResidual.toStatement` →
`erdos260_final_actual`).  Composition only. -/
theorem toStatement (R : Erdos260CorrectedResidual) : Erdos260Statement :=
  R.toCorrectedLedger.toStatement

end Erdos260CorrectedResidual

/-- **THE WAVE-16 ENDPOINT**: `Erdos260Statement` from the folded 10-field surface —
the class-1 lane de-razored to the corrected count-cap absorption (consumed by the
corrected P9 ledger, bypassing the frozen-term chain), the run lane split into the
honest Section 26 conjunct plus the named band-4 voiding, and the class-0 lanes unified
into per-ctx fibre emptiness.  Public bridges only. -/
theorem erdos260_of_correctedResidual (R : Erdos260CorrectedResidual) :
    Erdos260Statement :=
  R.toStatement

/-! ## Part 3.  Witnesses and honest direction accounting -/

/-- **The weakening witness**: the wave-15 anchored surface yields the wave-16 surface.
Tower/Return/DensePack transport verbatim; the run guards are dropped (and the voiding
is DERIVED from the old run fields — `runCycleNumericField_settled` +
`runNumericIneq_not_band4`); the unified class-0 field is rebuilt through the wave-16
equivalences; the class-1 absorption follows from the old surface's derived fibre
emptiness (`card = 0`).  One direction only; NO converse is claimed. -/
def correctedResidual_of_anchoredResidual (R : Erdos260AnchoredResidual) :
    Erdos260CorrectedResidual where
  towerEnumLow := R.towerEnumLow
  towerEnumTail := R.towerEnumTail
  runBand4Void := fun ctx =>
    runNumericIneq_not_band4 ctx
      (show RunNumericIneq ctx from runCycleNumericField_settled R.runNumeric ctx)
  runNumericLow := fun ctx _ hlt => R.runNumericLow ctx hlt
  runNumericTail := fun ctx _ hge h93 => R.runNumericTail ctx hge h93
  returnGates := R.returnGates
  returnInterior := R.returnInterior
  class0Fibre := fun ctx =>
    ⟨fun hsurv => ofcAnchoredResidual_class0FibreEmpty_of_survivor R ctx hsurv,
     fun h48 h96 hmeet =>
       (ofcClass0Fibre_empty_iff_windowCycleCheck ctx).mpr
         (R.class0Mid ctx h48 h96 hmeet),
     fun h96 =>
       (R.class0BigOrder ctx h96).imp (fun h => h)
         (fun hwin => (ofcClass0Fibre_empty_iff_windowCycleCheck ctx).mpr hwin)⟩
  class1CapAbsorption := fun ctx _hr => by
    have hempty : routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
      R.class1Empty ctx
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
    exact mul_nonneg (div_nonneg correctedCnlShare_num_nonneg (by norm_num))
      (Nat.cast_nonneg _)
  densePackUngated := R.densePackUngated

/-- Nonempty transport from the anchored surface (one direction — honest). -/
theorem nonempty_correctedResidual_of_anchoredResidual
    (h : Nonempty Erdos260AnchoredResidual) :
    Nonempty Erdos260CorrectedResidual :=
  h.elim fun R => ⟨correctedResidual_of_anchoredResidual R⟩

/-- Nonempty transport from the anchored-count surface (two steps). -/
theorem nonempty_correctedResidual_of_anchoredCount
    (h : Nonempty Erdos260AnchoredCountResidual) :
    Nonempty Erdos260CorrectedResidual :=
  nonempty_correctedResidual_of_anchoredResidual
    (nonempty_anchoredResidual_of_anchoredCount h)

/-- Nonempty transport from the canonical charge surface (three steps). -/
theorem nonempty_correctedResidual_of_returnCharge
    (h : Nonempty Erdos260ReturnChargeResidual) :
    Nonempty Erdos260CorrectedResidual :=
  nonempty_correctedResidual_of_anchoredResidual
    (nonempty_anchoredResidual_of_returnCharge h)

/-! ## Part 4.  The wave-16 consumers -/

/-- **The five-family collapse at the corrected surface**: the voiding field reduces
every fixed-family hit to the two non-tower data `(3,1)` / `(21,3)` — the wave-16
sibling of `fixedFamilyHit_reduces_of_settlement`, now carried by the surface itself. -/
theorem correctedCapstone_fixedFamilyHit_collapse (R : Erdos260CorrectedResidual)
    (ctx : ActualFailureContext) (hhit : FixedFamilyHit ctx) :
    ((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1)
    ∨ ((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3) := by
  rcases hhit with h1 | h2 | h3 | h4 | h5
  · exact Or.inl h1
  · exact Or.inr h2
  · exact absurd (orbitBandPinned_15_1 ctx h3) (R.runBand4Void ctx)
  · exact absurd (orbitBandPinned_15_2 ctx h4) (R.runBand4Void ctx)
  · exact absurd (orbitBandPinned_105_7 ctx h5) (R.runBand4Void ctx)

/-- Re-export (the over-transcription verdict): the formalized run numeric is FALSE at
every band-4-pinned context — the voiding field is NOT optional. -/
theorem correctedCapstone_runNumeric_false_at_band4 (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 4) : ¬ RunNumericIneq ctx :=
  band4_pinned_not_runNumericIneq ctx hpin

/-- Re-export (the exit-mass floor): at every fixed-family hit the word spends at least
half the dyadic scale deviating from the recurrent band. -/
theorem correctedCapstone_exitMass_floor (ctx : ActualFailureContext)
    (hhit : FixedFamilyHit ctx) : ctx.shell.X ≤ 2 * emExitMass ctx :=
  fixedFamily_exitMass_lower ctx hhit

/-- Re-export (the exit-count floor): exits are cofinal at density
`≥ X/(2(L+B+1))`. -/
theorem correctedCapstone_exitCount_floor (ctx : ActualFailureContext)
    (hhit : FixedFamilyHit ctx) :
    ctx.shell.X
      ≤ 2 * ((emExitSet ctx).card * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) :=
  fixedFamily_exitCount_lower ctx hhit

/-- Re-export (the de-razoring): the corrected class-1 capacity absorbs a full pinned
excess on every shell — in sharp contrast with the frozen razor. -/
theorem correctedCapstone_Y_lt_corrected
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    ctx.n24CarryData.Y < termCnl (correctedCapacityPhases budget ctx).toClosurePhaseData :=
  Y_lt_termCnl_corrected budget ctx

/-! ## Part 5.  The conditional routes (re-exported under capstone-local names)

Carried forward from the anchored capstone; none is claimed unconditional. -/

/-- Route A (the pressure relocation): at every fixed-family hit the floor sits in
class 4 / class 3 / (up to `1/512`) class 5 — never in class 2. -/
theorem correctedCapstone_pressure_relocation (ctx : ActualFailureContext)
    (hhit : FixedFamilyHit ctx) :
    erdos260Constants.cPr * (ctx.shell.X : ℝ) * ((ctx.n24CarryData.r : ℝ) + 1)
        ≤ routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 4
      ∨ erdos260Constants.cPr * (ctx.shell.X : ℝ) * ((ctx.n24CarryData.r : ℝ) + 1)
          ≤ routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 3
      ∨ 511 / 512 * (erdos260Constants.cPr * (ctx.shell.X : ℝ)
            * ((ctx.n24CarryData.r : ℝ) + 1))
          ≤ routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5 :=
  fixedFamilyHit_pressure_relocation ctx hhit

/-- Route B (the widened supply atom): shell persistence is void at every scale. -/
theorem correctedCapstone_shellPersistence_void (ctx : ActualFailureContext)
    (hhit : FixedFamilyHit ctx) (hp : FixedFamilyShellPersistence ctx) : False :=
  fixedFamilyShellPersistence_void ctx hhit hp

/-- Route B's consumer: all five fixed families void under the deep shell-persistence
supply. -/
theorem correctedCapstone_fixedFamilyHit_void_of_shellPersistence
    (h : DeepFixedFamilyShellPersistence) (ctx : ActualFailureContext) :
    ¬ FixedFamilyHit ctx :=
  fixedFamilyHit_void_of_shellPersistence h ctx

/-- Route C (the carry-linear chain): equivalent to the clean continuation. -/
theorem correctedCapstone_cleanContinuation_iff_carryLinear :
    DeepFixedFamilyCleanContinuation ↔ DeepFixedFamilyCarryLinear :=
  deepFixedFamilyCleanContinuation_iff_carryLinear

/-- Route D (covering families, carried forward). -/
theorem correctedCapstone_erdos260_of_coveringFamilies
    (h : ∀ ctx : ActualFailureContext, 2 ^ 493443 < ctx.X →
      ∃ fam : ObligationScaleFamily,
        fam.onset ≤ 493443 ∧ ctx.d = fam.d ∧ ctx.Q ≤ 2 ^ max fam.onset 5)
    (surfaces : DyadicValueLever → Erdos260DyadicLeverResidual) :
    Erdos260Statement :=
  erdos260_of_coveringFamilies h surfaces

/-- Route E (the wave-14 onset entry, carried forward). -/
theorem correctedCapstone_erdos260_of_onsetResidual (R : Erdos260OnsetResidual) :
    Erdos260Statement :=
  erdos260_of_onsetResidual R

/-- Route F (the graded zero entry, carried forward). -/
theorem correctedCapstone_erdos260_of_windowOnesZeroField (R : Erdos260WindowOnesResidual)
    (h : ReturnWindowOnesZeroField) : Erdos260Statement :=
  erdos260_of_windowOnesZeroField R h

/-- Route G (NEW — the corrected-ledger entry itself, re-exported): any inhabitant of
the corrected P9 ledger residual closes the statement. -/
theorem correctedCapstone_erdos260_of_correctedP9Ledger
    (R : CorrectedP9CtxPinnedLedgerResidual) : Erdos260Statement :=
  erdos260_of_correctedP9Ledger R

/-! ## Part 6.  Machine-readable status (honest) -/

/-- Honest machine-readable status of the corrected-ledger capstone (the wave-16
fold). -/
def erdos260CorrectedLedgerCapstoneStatus : List String :=
  [ "SURFACES (ordered by strength - honest): Erdos260ReturnChargeResidual (13) -> " ++
      "Erdos260AnchoredCountResidual (12) -> Erdos260AnchoredResidual (12) -> " ++
      "Erdos260CorrectedResidual (this module, 10 fields) - each step one-directional " ++
      "downward (correctedResidual_of_anchoredResidual); NO converse claimed.  " ++
      "Endpoint erdos260_of_correctedResidual walks the CORRECTED P9 ledger " ++
      "(CorrectedP9CtxPinnedLedgerResidual.ofGenuineCaps -> toStatement -> " ++
      "erdos260_final_actual), BYPASSING the frozen-term consumer " ++
      "P9CtxPinnedLedgerResidual for the class-1 lane.",
    "CLASS 1 FOLDED (over-transcription #4, the BIG fold): the anchored " ++
      "class1DeepLow/Tail fields (conclusion = outright fibre emptiness, the razor " ++
      "artifact of the frozen termCnl: exponent at Y := X, |I_j| one Kraft cylinder) " ++
      "are REPLACED by class1CapAbsorption: card(fibre_1)*Y <= (cStar*xi/6)*X = " ++
      "(31/1536)*X on 1 <= r shells - the corrected ledger bound itself, strictly " ++
      "weaker than emptiness (emptiness => card = 0 => absorption; converse fails).  " ++
      "r = 0 shells (ALL L <= 15420) relieved FREE (class1Fibre_card_le_one_of_r_eq_" ++
      "zero + Y < (31/1536)*X).  The guards of the old deep fields (closed moduli, " ++
      "band-4-free pairs, gcd misses, aperiodicity) are NO LONGER NEEDED on the " ++
      "surface: the corrected consumer never demands emptiness.",
    "THE GATE ARITHMETIC VERIFIED (honest - the brief's ~4.9M*c CORRECTED): on the " ++
      "genuine route the absorption gate for a count cap n is EXACTLY 24*n*L <= 31*X " ++
      "(correctedAbsorption_of_nat_gate).  For the wave-14 cycle-density caps n = " ++
      "b4*ceil(W/c) with the failure cap 2^24*W < 17*X, the regime lemma " ++
      "correctedAbsorption_of_cycleDensity_regime closes under 408*b4*L <= 15*2^24*c " ++
      "+ slack 24*b4*c*L <= 16*X; the SHARP budget is 408*b4*L <~ 31*2^24*c, i.e. L " ++
      "<~ 1,274,739*c/b4 (the brief's 4.9M*c double-counts 64/1536 = 1/24).  Every " ++
      "class-1 survivor has b4 >= 1 (band 4 ON cycle is WHY it survived), so the " ++
      "caps do NOT pass at all scales: shells with L > ~1.27M*c/b4 stay open on the " ++
      "absorption axis.  NO per-pair instantiation: the 87 survivors carry no " ++
      "in-tree certified periods/band-4 counts (the sweep certified only CLOSED " ++
      "pairs); enumerating 87 orbits is out of additive scope - the regime lemmas " ++
      "are the honest composable deliverable.",
    "RUN FOLDED (over-transcription #3, equal-strength re-foliation - honest): " ++
      "runNumericField_iff_band4Void_split proved the formalized field IS (band-4 " ++
      "voiding) AND (the field on band-4-free ctx), and band4_pinned_not_" ++
      "runNumericIneq proved the voiding UNAVOIDABLE (the field is FALSE at every " ++
      "band-4-pinned ctx - the floor (511/1024)*X*(r+1) crushes the ~10^-8*X " ++
      "budget).  The surface now carries runBand4Void (: forall ctx, NOT " ++
      "OrbitBandPinned ctx 4 - the tower-lane-routed demand, the orbit-pinned form " ++
      "of the deep open axis) plus runNumericLow/Tail GUARDED by it (the honest " ++
      "Section 26 content).  NOT a weakening: total strength unchanged (old fields " ++
      "imply the voiding via runCycleNumericField_settled + runNumericIneq_not_" ++
      "band4); the over-transcribed conjunct is now VISIBLE and separately supplied.  " ++
      "Consumer: correctedCapstone_fixedFamilyHit_collapse - five families -> " ++
      "(3,1)/(21,3) from the surface itself.",
    "CLASS 0 UNIFIED (the wave-16 reading): the three anchored lanes " ++
      "(class0Survivor cross/heavy split, class0Mid, class0BigOrder) become ONE " ++
      "field class0Fibre in the emptiness language routedFibre ... 0 = EMPTY - via " ++
      "ofcResidueMiss_iff_class0Empty_of_survivor (all 19 survivor demands ARE " ++
      "per-pair emptiness; off-fibre = verbatim at every survivor) and the " ++
      "modulus-free ofcClass0Fibre_empty_iff_windowCycleCheck.  The big-order " ++
      "escape certificate is KEPT as a disjunct (dropping it would STRENGTHEN).  " ++
      "Equivalence in better coordinates, not a weakening - honest.",
    "WHAT DID NOT FOLD (honest): towerEnumLow/Tail, returnGates/Interior, " ++
      "densePackUngated - VERBATIM anchored fields (wave 16 supplies no field " ++
      "change there); the band-4 voiding is NOT dropped (it is the honest " ++
      "unavoidable content of the old run lane, now named); the exit-mass floors " ++
      "(X <= 2*exitMass, X <= 2*#exits*(L+B+1), the long-gap structure) are " ++
      "RECORDS re-exported (correctedCapstone_exitMass_floor/_exitCount_floor), " ++
      "not field changes - the long-gap word survives all proved accounting and " ++
      "persistence is NOT forced.",
    "ROUTES RE-EXPORTED (conditional, none claimed unconditional): A. pressure " ++
      "relocation (correctedCapstone_pressure_relocation); B. shell persistence " ++
      "void per hit + deep consumer (correctedCapstone_shellPersistence_void, " ++
      "_fixedFamilyHit_void_of_shellPersistence); C. carry-linear chain " ++
      "(_cleanContinuation_iff_carryLinear); D. covering families " ++
      "(_erdos260_of_coveringFamilies); E. the onset entry (_erdos260_of_" ++
      "onsetResidual); F. the graded zero entry (_erdos260_of_windowOnesZero" ++
      "Field); G. NEW - the corrected-ledger entry (_erdos260_of_corrected" ++
      "P9Ledger).",
    "WHAT REMAINS OPEN (the honest post-wave-16 set, sharpest form): (1) " ++
      "FixedFamilyShellPersistence - now effectively at TWO data (3,1)/(21,3) " ++
      "(the surface's voiding field collapses the band-4 three; supplying the " ++
      "voiding itself is the orbit-pinned deep axis, manuscript route L.3/M.5); " ++
      "(2) the class-1 survivors under the corrected gate - the absorption field " ++
      "at deep shells (L > ~1.27M*c/b4 per pair; r = 0 and regime-gated shells " ++
      "PROVED); (3) the class-0 per-pair emptiness instances (19 pairs, " ++
      "offFibreMissResidualTable; 8 even-spaced pairs carry the parity/val-floor " ++
      "pins); (4) the remaining freeze audits - termChernoff/termDensePack/" ++
      "termRun sit on the same CNLScalarBudgetCore-style frozen normalizations " ++
      "(named NEXT TARGET: the same audit pattern as LedgerCalibrationAudit, " ++
      "applied to ChernoffMeasureModel/AppendixK1_DensePack/AppendixL4_Run " ++
      "scalar choices); (5) towerEnumLow at the three band-4 fixed data, " ++
      "towerEnumTail, the run band-4-free conjuncts on 64 <= q survivors.",
    "HYGIENE: additive only - no existing module edited (the root import file " ++
      "gains one line; LedgerCalibrationAudit, ExitMassTranscription, " ++
      "OffFibreMissClosure enter the root closure through this module's imports); " ++
      "no sorry / admit / new axiom / native_decide; all #print axioms in " ++
      "[propext, Classical.choice, Quot.sound] or fewer." ]

theorem erdos260CorrectedLedgerCapstoneStatus_nonempty :
    erdos260CorrectedLedgerCapstoneStatus ≠ [] := by
  simp [erdos260CorrectedLedgerCapstoneStatus]

/-! ## Part 7.  Axiom-cleanliness audit -/

#print axioms correctedAbsorption_of_nat_gate
#print axioms correctedAbsorption_of_cycleDensity_regime
#print axioms Erdos260CorrectedResidual.towerEnum
#print axioms Erdos260CorrectedResidual.towerCountV3
#print axioms Erdos260CorrectedResidual.runNumeric
#print axioms Erdos260CorrectedResidual.runCore
#print axioms Erdos260CorrectedResidual.runChain
#print axioms Erdos260CorrectedResidual.returnGatesCycle
#print axioms Erdos260CorrectedResidual.fibreSmall
#print axioms Erdos260CorrectedResidual.returnCharge
#print axioms Erdos260CorrectedResidual.budget
#print axioms Erdos260CorrectedResidual.class0Cycle
#print axioms Erdos260CorrectedResidual.class0Empty
#print axioms Erdos260CorrectedResidual.densePackCorrected
#print axioms Erdos260CorrectedResidual.densePackLedgerField
#print axioms Erdos260CorrectedResidual.hcapAll
#print axioms Erdos260CorrectedResidual.toCorrectedLedger
#print axioms Erdos260CorrectedResidual.toStatement
#print axioms erdos260_of_correctedResidual
#print axioms correctedResidual_of_anchoredResidual
#print axioms nonempty_correctedResidual_of_anchoredResidual
#print axioms nonempty_correctedResidual_of_anchoredCount
#print axioms nonempty_correctedResidual_of_returnCharge
#print axioms correctedCapstone_fixedFamilyHit_collapse
#print axioms correctedCapstone_runNumeric_false_at_band4
#print axioms correctedCapstone_exitMass_floor
#print axioms correctedCapstone_exitCount_floor
#print axioms correctedCapstone_Y_lt_corrected
#print axioms correctedCapstone_pressure_relocation
#print axioms correctedCapstone_shellPersistence_void
#print axioms correctedCapstone_fixedFamilyHit_void_of_shellPersistence
#print axioms correctedCapstone_cleanContinuation_iff_carryLinear
#print axioms correctedCapstone_erdos260_of_coveringFamilies
#print axioms correctedCapstone_erdos260_of_onsetResidual
#print axioms correctedCapstone_erdos260_of_windowOnesZeroField
#print axioms correctedCapstone_erdos260_of_correctedP9Ledger
#print axioms erdos260CorrectedLedgerCapstoneStatus_nonempty

end

end Erdos260
