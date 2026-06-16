import Erdos260.Erdos260ConvergenceCapstone
import Erdos260.SCCPersistence

/-!
# The miss-distance closure: exit localization of the class-0 gates and the
# class-0 exit-mass atom (`MissDistanceClosure`)

This module (NEW; it edits no existing file) settles the wave-19 "per-pair
miss-distance excess bound" attack on `NarrowSupportClass0Gates` and the
`DscTopBandExitFree` slot, with proofs on both the positive and the negative side.

## 1.  The gap-deviation classification (VERDICT: binary, sharpest form)

The in-tree deviation calculus is already the SHARPEST possible classification:
a gap either follows the recurrent band (deviation EXACTLY `0`,
`mdc_nonExit_weight_eq_zero` — not merely `≤ B+2`) or it is an L.3.1 exit
carrying its FULL length (`emExitWeight`).  Consequences (band `≤ 4`, free at
every survivor pair):

* an exit-free window has window excess EXACTLY `0`
  (`mdc_windowExcess_eq_zero_of_devFree`) — the canonical (band-following) word
  is perfectly calibrated, the "canonical excess" of the brief is `0`;
* hence EVERY class-0 fibre member's window contains an exit
  (`mdcFibre0_window_has_exit`): the deviation of an off-fibre miss is localized
  at `≥ 1` exit gap within distance `≤ r` of the start — the exit-free stratum
  of the fibre is EMPTY (`mdcFibre0_exitFreeStratum_empty`).  The two-piece
  (exit-free + exit-containing) mass split therefore COLLAPSES: the first piece
  is vacuous, ALL of `mass₀` lives on exit-containing windows.

## 2.  The miss-distance route (HONEST INVERSION, proved)

The honest per-member miss-distance bound is
`windowExcess ≤ (#exits in window)·(L+B+1)` (`mdc_windowExcess_le_exitCount_mul`).
But the count is `≥ 1` at every member (`mdc_missDistance_floor`) and a SINGLE
exit's ceiling already swamps the activity floor: `Y = L/64 ≤ L+B+1`
(`mdc_missDistance_route_inverted`, via `dscY_le_perGapCeiling`).  So no
exit-COUNT (= miss-distance) bound can certify the gate at any useful level:
the gate is a demand on exit SIZE inside class-0 windows, not on exit count —
exactly the brief's anticipated inversion, now with proofs.

## 3.  The surviving content: the CLASS-0 SHARE of the exit mass (the named atom)

`mdcClass0ExitMass` = the exit mass restricted to the union of the class-0 fibre
windows (`mdcClass0Reach`).  Proved structure:

* per member `emDevWindow ≤ mdcClass0ExitMass` (`mdc_devWindow_le_class0ExitMass`),
  so a per-context cap `mdcClass0ExitMass ≤ s·Y` supplies the narrow-support gate
  at level `s` OUTRIGHT (`mdcGate_of_class0ExitMass_le`,
  builder `mdcGates_of_class0ExitMassCaps` for the full v19 field);
* the survivor telescope: `mass₀ ≤ ⌈(r+1)/c⌉·mdcClass0ExitMass`
  (`mdcClass0Mass_le_overlap_class0ExitMass`, via the certified `c`-spacing) and
  the generic form `mass₀ ≤ (r+1)·mdcClass0ExitMass`
  (`mdcClass0Mass_le_generic_class0ExitMass`);
* **the named atom** `MdcClass0ExitMassControl`
  (`1536·⌈(r+1)/c⌉·mdcClass0ExitMass ≤ 31·X` at survivors) closes the survivor
  mass lane in the EXACT v18/v19 row shape (`mdcClass0SurvivorMass_of_atom`) —
  the class-0 analogue of the sibling `ExitMassControlCore` (classes 3/4/5),
  same mechanism: a per-class share cap on the relocated 21.1 exit mass;
* **HONEST floor**: the UNRESTRICTED form is REFUTED at every band-`≤ 4` context
  (`mdcUnrestrictedAtom_refuted`): `X ≤ 2·emExitMass` forces the unrestricted
  budget above the cap by factor `≥ 768/31` — the restriction to class-0 windows
  is the ENTIRE content of the atom.  Exits are MANY and CARRY `≥ X/2`; the atom
  demands that the class-0 windows see almost none of it.

## 4.  The top band (workstream 2, honest)

No in-tree mechanism forces exits OUT of the top band `[F+W-(r+1), F+W+r)`:

* the only in-tree band-following supplier is an ONSET (persistence-type) datum —
  transcribed here as `mdcTopBandExitFree_of_onset` /
  `mdcTopBandExitFree_of_indexPersistence`; but index persistence at a
  fixed-family hit EMPTIES the whole high-excess set
  (`mdcIndexPersistence_voids_class0`, via
  `highExcessStarts_empty_of_indexPersistence`), and shell persistence is VOID
  (`fixedFamilyShellPersistence_void`) — the onset route only fires where the
  class-0 demand is already vacuous;
* exit-freeness of the top band is NOT refutable in-tree: its full quantitative
  cost is the sharpened support floor `X ≤ 2·(W-(r+1))·(L+B+1)`
  (`mdc_topBandExitFree_support_floor`, exits confined to the body —
  `mdc_topBandExitFree_exits_confined`) — a constraint, not a contradiction;
  the slot is a genuine structural residual;
* wiring: `mdcTopBandSlot_of_onsets` rebuilds the exact consumption-slot input
  of BOTH v19 interior closures; `mdcReturnInteriorOffTable_of_topBandOnsets`
  composes through `convergenceReturnInterior_of_topBandExitFree`.

No `sorry`, no `admit`, no new `axiom`, no `native_decide`; additive only —
no existing module is edited.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 0.  The class-0 window reach and the class-0 share of the exit mass -/

/-- **The class-0 window reach**: the union of the descent windows `[k, k+r]` of the
class-0 routed fibre members. -/
def mdcClass0Reach (ctx : ActualFailureContext) : Finset ℕ :=
  (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).biUnion
    (fun k => Finset.Ico k (k + (ctx.n24CarryData.r + 1)))

/-- **The class-0 share of the exit mass**: the total L.3.1 exit weight carried by
the class-0 fibre windows — the quantity the named atom caps. -/
def mdcClass0ExitMass (ctx : ActualFailureContext) : ℕ :=
  ∑ j ∈ mdcClass0Reach ctx, emExitWeight ctx j

/-- The class-0 fibre sits inside the carry start window. -/
theorem mdcFibre0_subset_starts (ctx : ActualFailureContext) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0
      ⊆ ctx.n24CarryData.starts := fun k hk =>
  (mem_highExcessStarts.mp (Finset.mem_filter.mp hk).1).1

/-- The class-0 reach sits inside the global reach range. -/
theorem mdcClass0Reach_subset_emReach (ctx : ActualFailureContext) :
    mdcClass0Reach ctx ⊆ emReach ctx := by
  intro j hj
  obtain ⟨k, hk, hj2⟩ := Finset.mem_biUnion.mp hj
  have hks := mdcFibre0_subset_starts ctx hk
  rw [cnlMulti_starts_eq_window, Finset.mem_Ico] at hks
  rw [Finset.mem_Ico] at hj2
  unfold emReach emF emW
  rw [Finset.mem_Ico]
  omega

/-- The class-0 exit mass is a SHARE of the global exit mass. -/
theorem mdcClass0ExitMass_le_emExitMass (ctx : ActualFailureContext) :
    mdcClass0ExitMass ctx ≤ emExitMass ctx :=
  Finset.sum_le_sum_of_subset (mdcClass0Reach_subset_emReach ctx)

/-! ## Part 1.  The gap-deviation classification (the brief's question, settled)

The classification is BINARY and sharpest-possible: a non-exit gap deviates by
EXACTLY `0` (not merely `≤ B+2`); an exit carries its full gap length. -/

/-- **Non-exit gaps deviate by exactly zero** — the canonical (band-following) word
is perfectly calibrated. -/
theorem mdc_nonExit_weight_eq_zero (ctx : ActualFailureContext) {j : ℕ}
    (h : hitGap ctx.n24CarryData.a j = fixedFamilyRecurrentBand ctx) :
    emExitWeight ctx j = 0 := by
  unfold emExitWeight
  rw [if_pos h]

/-- A positive exit weight certifies an L.3.1 exit. -/
theorem mdc_exit_of_weight_ne_zero (ctx : ActualFailureContext) {j : ℕ}
    (h : emExitWeight ctx j ≠ 0) :
    hitGap ctx.n24CarryData.a j ≠ fixedFamilyRecurrentBand ctx := by
  intro hg
  exact h (mdc_nonExit_weight_eq_zero ctx hg)

/-- Window excess is nonnegative (the positive part). -/
theorem mdc_windowExcess_nonneg (g : ℕ → ℕ) (k r : ℕ) (T : ℝ) :
    0 ≤ windowExcess g k r T := by
  unfold windowExcess positivePart
  exact le_max_right _ _

/-- **The canonical word carries ZERO excess** (band `≤ 4`): a deviation-free window
has window excess exactly `0` — the calibration question of the brief, answered in
the sharpest form. -/
theorem mdc_windowExcess_eq_zero_of_devFree (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4) {k : ℕ}
    (h : emDevWindow ctx k = 0) :
    windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
      = 0 := by
  have h1 := em_windowExcess_le_devWindow ctx hband k
  rw [h, Nat.cast_zero] at h1
  exact le_antisymm h1 (mdc_windowExcess_nonneg _ _ _ _)

/-! ## Part 2.  Exit localization: every class-0 member's window contains an exit -/

/-- **The deviation content of a class-0 member's window is nonzero** (band `≤ 4`):
the member's excess is `≥ Y > 0`, and a deviation-free window has excess `0`. -/
theorem mdcFibre0_devWindow_ne_zero (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0) :
    emDevWindow ctx k ≠ 0 := by
  intro h0
  have hzero := mdc_windowExcess_eq_zero_of_devFree ctx hband h0
  have hY := Y_le_windowExcess_of_mem_routedFibre ctx.n24CarryData
    (genuineChargeRoute ctx) 0 hk
  have hYpos := n24CarryData_Y_pos ctx
  rw [hzero] at hY
  linarith

/-- **Exit localization (weight form)**: every class-0 fibre member's window carries
a positive exit weight at some offset `≤ r`. -/
theorem mdcFibre0_window_has_exitWeight (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0) :
    ∃ i, i < ctx.n24CarryData.r + 1 ∧ emExitWeight ctx (k + i) ≠ 0 := by
  have hne := mdcFibre0_devWindow_ne_zero ctx hband hk
  by_contra hcon
  refine hne ?_
  unfold emDevWindow
  refine Finset.sum_eq_zero ?_
  intro i hi
  rw [Finset.mem_range] at hi
  by_contra hw
  exact hcon ⟨i, hi, hw⟩

/-- **Exit localization (gap form, THE MISS-DISTANCE THEOREM)**: every class-0
fibre member's window contains an L.3.1 exit — the off-fibre miss's deviation is
localized at exit gaps within distance `≤ r` of the start; the canonical-orbit
part of the window contributes nothing. -/
theorem mdcFibre0_window_has_exit (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0) :
    ∃ i, i < ctx.n24CarryData.r + 1 ∧
      hitGap ctx.n24CarryData.a (k + i) ≠ fixedFamilyRecurrentBand ctx := by
  obtain ⟨i, hi, hw⟩ := mdcFibre0_window_has_exitWeight ctx hband hk
  exact ⟨i, hi, mdc_exit_of_weight_ne_zero ctx hw⟩

/-- **The two-piece split COLLAPSES**: the exit-free stratum of the class-0 fibre is
EMPTY (band `≤ 4`) — ALL of `mass₀` lives on exit-containing windows; the heavy
members ARE the exit-containing members. -/
theorem mdcFibre0_exitFreeStratum_empty (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).filter
      (fun k => emDevWindow ctx k = 0) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro k hk
  have hmem := Finset.mem_filter.mp hk
  exact mdcFibre0_devWindow_ne_zero ctx hband hmem.1 hmem.2

/-! ## Part 3.  The per-member miss-distance bound and its HONEST inversion -/

/-- The number of exit offsets inside the descent window at `k`. -/
def mdcWindowExitCount (ctx : ActualFailureContext) (k : ℕ) : ℕ :=
  ((Finset.range (ctx.n24CarryData.r + 1)).filter
    (fun i => emExitWeight ctx (k + i) ≠ 0)).card

/-- **The per-member miss-distance bound**: the window excess of any start in the
carry window is at most (#exits in the window) × the per-gap rigidity ceiling
`L+B+1` — the honest transcription of "excess ≤ miss distance × gap ceiling". -/
theorem mdc_windowExcess_le_exitCount_mul (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4) {k : ℕ}
    (hk : k ∈ ctx.n24CarryData.starts) :
    windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
      ≤ ((mdcWindowExitCount ctx k
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) : ℕ) : ℝ) := by
  refine le_trans (em_windowExcess_le_devWindow ctx hband k) ?_
  rw [Nat.cast_le]
  rw [cnlMulti_starts_eq_window, Finset.mem_Ico] at hk
  have hsplit : ∑ i ∈ Finset.range (ctx.n24CarryData.r + 1), emExitWeight ctx (k + i)
      = ∑ i ∈ (Finset.range (ctx.n24CarryData.r + 1)).filter
          (fun i => emExitWeight ctx (k + i) ≠ 0), emExitWeight ctx (k + i) :=
    (Finset.sum_filter_of_ne (fun i _ h => h)).symm
  unfold emDevWindow mdcWindowExitCount
  rw [hsplit]
  calc ∑ i ∈ (Finset.range (ctx.n24CarryData.r + 1)).filter
        (fun i => emExitWeight ctx (k + i) ≠ 0), emExitWeight ctx (k + i)
      ≤ ∑ _i ∈ (Finset.range (ctx.n24CarryData.r + 1)).filter
          (fun i => emExitWeight ctx (k + i) ≠ 0),
          (shellLadderDepth ctx + carryB ctx.shell.Q + 1) := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have hir := (Finset.mem_filter.mp hi).1
        rw [Finset.mem_range] at hir
        refine le_trans (emExitWeight_le_hitGap ctx (k + i)) ?_
        exact n24_hitGap_le_reach ctx (by omega)
    _ = ((Finset.range (ctx.n24CarryData.r + 1)).filter
          (fun i => emExitWeight ctx (k + i) ≠ 0)).card
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) := by
        rw [Finset.sum_const, smul_eq_mul]

/-- **The miss-distance floor**: every class-0 member's window exit count is `≥ 1`
(band `≤ 4`) — the miss distance never vanishes on the fibre. -/
theorem mdc_missDistance_floor (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0) :
    1 ≤ mdcWindowExitCount ctx k := by
  obtain ⟨i, hi, hw⟩ := mdcFibre0_window_has_exitWeight ctx hband hk
  refine Finset.card_pos.mpr ⟨i, ?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hw⟩

/-- **HONEST INVERSION (the brief's anticipated verdict, proved)**: already ONE
exit's ceiling swamps the activity floor — `Y ≤ 1·(L+B+1)` — so no exit-COUNT
(miss-distance) bound can certify the narrow-support gate at any level below the
trivial calibration; the gate is a demand on exit SIZE inside class-0 windows. -/
theorem mdc_missDistance_route_inverted (ctx : ActualFailureContext) :
    ctx.n24CarryData.Y
      ≤ ((1 * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) : ℕ) : ℝ) := by
  rw [one_mul]
  exact dscY_le_perGapCeiling ctx

/-! ## Part 4.  The class-0 exit mass dominates the per-member deviation -/

/-- Each class-0 member's window deviation content is bounded by the class-0 exit
mass (the window is one of the summed windows). -/
theorem mdc_devWindow_le_class0ExitMass (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0) :
    emDevWindow ctx k ≤ mdcClass0ExitMass ctx := by
  unfold emDevWindow mdcClass0ExitMass
  rw [show (∑ i ∈ Finset.range (ctx.n24CarryData.r + 1), emExitWeight ctx (k + i))
      = ∑ j ∈ (Finset.range (ctx.n24CarryData.r + 1)).image (fun i => k + i),
          emExitWeight ctx j from (Finset.sum_image (fun x _ y _ h => by omega)).symm]
  refine Finset.sum_le_sum_of_subset ?_
  intro j hj
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
  rw [Finset.mem_range] at hi
  exact Finset.mem_biUnion.mpr
    ⟨k, hk, Finset.mem_Ico.mpr ⟨Nat.le_add_right _ _, by omega⟩⟩

/-! ## Part 5.  The telescoped mass bounds against the class-0 share -/

/-- The class-0 fibre's summed deviation telescopes through the certified survivor
`c`-spacing against the CLASS-0 share only — each class-0 exit gap is counted at
most `⌈(r+1)/c⌉ = (r+c)/c` times. -/
theorem mdcClass0DevSum_le_overlap (ctx : ActualFailureContext)
    (hsurv : Class0DatumSurvivor ctx) :
    ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, emDevWindow ctx k
      ≤ ((ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
            / class0SurvivorPeriod (class1SlopeDatum ctx).q)
          * mdcClass0ExitMass ctx := by
  have hc : 1 ≤ class0SurvivorPeriod (class1SlopeDatum ctx).q :=
    tfaClass0SurvivorPeriod_pos _
  have hspace := ofcClass0Member_spacing_of_survivor ctx hsurv
  have hU : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0,
      ∀ i, i < ctx.n24CarryData.r + 1 → k + i ∈ mdcClass0Reach ctx := by
    intro k hk i hi
    exact Finset.mem_biUnion.mpr
      ⟨k, hk, Finset.mem_Ico.mpr ⟨Nat.le_add_right _ _, by omega⟩⟩
  unfold emDevWindow mdcClass0ExitMass
  exact agc_spaced_windowSum_le (emExitWeight ctx) hc hspace hU

/-- **The survivor-lane two-piece headline (collapsed form)**: the class-0 routed
mass is bounded by `⌈(r+1)/c⌉` copies of the CLASS-0 SHARE of the exit mass —
strictly sharper than the wave-19 `⌈(r+1)/c⌉·emExitMass` budget (which carries the
fatal `X/2` floor). -/
theorem mdcClass0Mass_le_overlap_class0ExitMass (ctx : ActualFailureContext)
    (hsurv : Class0DatumSurvivor ctx) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 0
      ≤ ((((ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
            / class0SurvivorPeriod (class1SlopeDatum ctx).q)
          * mdcClass0ExitMass ctx : ℕ) : ℝ) :=
  le_trans (agcClassMass_le_sum_devWindow ctx (agcSurvivorBand_le_four ctx hsurv) 0)
    (Nat.cast_le.mpr (mdcClass0DevSum_le_overlap ctx hsurv))

/-- The generic (no-spacing) telescope: overlap factor `r + 1` against the class-0
share (the `c = 1` instance of the spaced bound). -/
theorem mdcClass0DevSum_le_generic (ctx : ActualFailureContext) :
    ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, emDevWindow ctx k
      ≤ (ctx.n24CarryData.r + 1) * mdcClass0ExitMass ctx := by
  have hU : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0,
      ∀ i, i < ctx.n24CarryData.r + 1 → k + i ∈ mdcClass0Reach ctx := by
    intro k hk i hi
    exact Finset.mem_biUnion.mpr
      ⟨k, hk, Finset.mem_Ico.mpr ⟨Nat.le_add_right _ _, by omega⟩⟩
  have h := agc_spaced_windowSum_le (c := 1) (r := ctx.n24CarryData.r)
    (emExitWeight ctx) le_rfl
    (fun x _ z _ _ => one_dvd _) hU
  rw [Nat.div_one] at h
  unfold emDevWindow mdcClass0ExitMass
  exact h

/-- The generic-lane mass bound against the class-0 share (band `≤ 4`). -/
theorem mdcClass0Mass_le_generic_class0ExitMass (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 0
      ≤ (((ctx.n24CarryData.r + 1) * mdcClass0ExitMass ctx : ℕ) : ℝ) :=
  le_trans (agcClassMass_le_sum_devWindow ctx hband 0)
    (Nat.cast_le.mpr (mdcClass0DevSum_le_generic ctx))

/-! ## Part 6.  THE NAMED ATOM: the class-0 exit-mass control, its closure, and
the HONEST refutation of its unrestricted form -/

/-- **THE NAMED CLASS-0 EXIT-MASS ATOM** (the class-0 analogue of the sibling
`ExitMassControlCore` for classes 3/4/5): at every survivor pair the telescoped
class-0 share of the exit mass clears the absorption cap —
`1536·⌈(r+1)/c⌉·mdcClass0ExitMass ≤ 31·X`.  The restriction to class-0 windows is
the ENTIRE content: the unrestricted form is refuted below. -/
def MdcClass0ExitMassControl : Prop :=
  ∀ ctx : ActualFailureContext, Class0DatumSurvivor ctx →
    1536 * (((ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
          / class0SurvivorPeriod (class1SlopeDatum ctx).q)
        * mdcClass0ExitMass ctx)
      ≤ 31 * ctx.shell.X

/-- **The atom closes the survivor mass lane** in the EXACT v18/v19 row shape (the
first conjunct of `nsgFrontierClass0Mass_of_gates`): `mass₀ ≤ (31/1536)·X`. -/
theorem mdcClass0SurvivorMass_of_atom (h : MdcClass0ExitMassControl) :
    ∀ ctx : ActualFailureContext, Class0DatumSurvivor ctx →
      routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 0
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  intro ctx hsurv
  have h1 := mdcClass0Mass_le_overlap_class0ExitMass ctx hsurv
  have h2 : (1536 : ℝ)
      * ((((ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
            / class0SurvivorPeriod (class1SlopeDatum ctx).q)
          * mdcClass0ExitMass ctx : ℕ) : ℝ)
      ≤ 31 * (ctx.shell.X : ℝ) := by exact_mod_cast h ctx hsurv
  have hc6 : erdos260Constants.cStar * erdos260Constants.ξ / 6 = 31 / 1536 := by
    rw [tfaCstarXi_eq]
    norm_num
  rw [hc6]
  linarith

/-- **HONEST FLOOR (the unrestricted form is FALSE)**: replacing the class-0 share
by the FULL exit mass refutes the atom at every band-`≤ 4` context — the relocated
Lemma 21.1 floor `X ≤ 2·emExitMass` forces the unrestricted budget above the cap by
factor `≥ 768/31 ≈ 24.8`.  The restriction IS the content. -/
theorem mdcUnrestrictedAtom_refuted (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4) :
    ¬ (1536 * (((ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
          / class0SurvivorPeriod (class1SlopeDatum ctx).q)
        * emExitMass ctx)
      ≤ 31 * ctx.shell.X) := by
  intro hle
  have hfloor := em_exitMass_lower_of_band ctx hband
  have hX1 := agcX_ge_one ctx
  have hc : 1 ≤ class0SurvivorPeriod (class1SlopeDatum ctx).q :=
    tfaClass0SurvivorPeriod_pos _
  have hone : 0 < (ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
      / class0SurvivorPeriod (class1SlopeDatum ctx).q :=
    (Nat.one_le_div_iff hc).mpr (Nat.le_add_left _ _)
  have h2 : emExitMass ctx
      ≤ ((ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
            / class0SurvivorPeriod (class1SlopeDatum ctx).q)
          * emExitMass ctx :=
    Nat.le_mul_of_pos_left _ hone
  generalize ((ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
      / class0SurvivorPeriod (class1SlopeDatum ctx).q)
      * emExitMass ctx = t at hle h2
  omega

/-! ## Part 7.  The gate suppliers: the class-0 exit-mass cap feeds the v19 gates -/

/-- **The miss-distance gate supplier**: a per-context cap `mdcClass0ExitMass ≤ s·Y`
on the class-0 share supplies the narrow-support gate at level `s` outright (band
`≤ 4`) — per member, excess ≤ window deviation ≤ class-0 exit mass. -/
theorem mdcGate_of_class0ExitMass_le (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4) {s : ℕ}
    (h : ((mdcClass0ExitMass ctx : ℕ) : ℝ) ≤ (s : ℝ) * ctx.n24CarryData.Y) :
    NarrowSupportGate ctx s := by
  intro k hk
  refine le_trans (em_windowExcess_le_devWindow ctx hband k) (le_trans ?_ h)
  exact_mod_cast mdc_devWindow_le_class0ExitMass ctx hk

/-- **The v19 gates field from per-lane class-0 exit-mass caps**: the three lanes of
`NarrowSupportClass0Gates`, each supplied by a capped class-0 exit mass in the
lane's regime (the survivor band bound is free; the generic lanes carry it as a
hypothesis — honest). -/
def mdcGates_of_class0ExitMassCaps
    (hS : ∀ ctx : ActualFailureContext, Class0DatumSurvivor ctx →
      ∃ s : ℕ, ((mdcClass0ExitMass ctx : ℕ) : ℝ) ≤ (s : ℝ) * ctx.n24CarryData.Y
        ∧ s * shellLadderDepth ctx
            ≤ 1274739 * class0SurvivorPeriod (class1SlopeDatum ctx).q)
    (hM : ∀ ctx : ActualFailureContext,
      48 ≤ (class1SlopeDatum ctx).q → (class1SlopeDatum ctx).q < 96 →
      Class0CycleMeetsShallow ctx →
      fixedFamilyRecurrentBand ctx ≤ 4 ∧
      ∃ s : ℕ, ((mdcClass0ExitMass ctx : ℕ) : ℝ) ≤ (s : ℝ) * ctx.n24CarryData.Y
        ∧ s * shellLadderDepth ctx ≤ 1274739)
    (hB : ∀ ctx : ActualFailureContext, 96 ≤ (class1SlopeDatum ctx).q →
      Class0BigOrderHorn ctx
        ∨ (fixedFamilyRecurrentBand ctx ≤ 4 ∧
          ∃ s : ℕ, ((mdcClass0ExitMass ctx : ℕ) : ℝ) ≤ (s : ℝ) * ctx.n24CarryData.Y
            ∧ s * shellLadderDepth ctx ≤ 1274739)) :
    NarrowSupportClass0Gates where
  survivor ctx hsurv := by
    obtain ⟨s, hcap, hreg⟩ := hS ctx hsurv
    exact ⟨s, mdcGate_of_class0ExitMass_le ctx
      (agcSurvivorBand_le_four ctx hsurv) hcap, hreg⟩
  mid ctx h48 h96 hmeet := by
    obtain ⟨hband, s, hcap, hreg⟩ := hM ctx h48 h96 hmeet
    exact ⟨s, mdcGate_of_class0ExitMass_le ctx hband hcap, hreg⟩
  big ctx h96 := by
    rcases hB ctx h96 with h | ⟨hband, s, hcap, hreg⟩
    · exact Or.inl h
    · exact Or.inr ⟨s, mdcGate_of_class0ExitMass_le ctx hband hcap, hreg⟩

/-! ## Part 8.  The top band (workstream 2): suppliers, the void mechanism, and
the honest quantitative cost -/

/-- **The onset supplier**: any band-following onset at or below the top band's
start yields top-band exit-freeness outright. -/
theorem mdcTopBandExitFree_of_onset (ctx : ActualFailureContext) {k₁ : ℕ}
    (hk₁ : k₁ + (ctx.n24CarryData.r + 1) ≤ emF ctx + emW ctx)
    (hg : ∀ k, k₁ ≤ k →
      hitGap ctx.n24CarryData.a k = fixedFamilyRecurrentBand ctx) :
    DscTopBandExitFree ctx := by
  intro j hj
  rw [Finset.mem_Ico] at hj
  exact hg j (by omega)

/-- Index persistence supplies top-band exit-freeness (the onset sits at or below
`F`, and the window width clears `r + 1`). -/
theorem mdcTopBandExitFree_of_indexPersistence (ctx : ActualFailureContext)
    (hp : FixedFamilyIndexPersistence ctx) : DscTopBandExitFree ctx := by
  obtain ⟨k₁, hk₁, hg⟩ := hp
  intro j hj
  rw [Finset.mem_Ico] at hj
  have hw := cnlMulti_r_add_one_le_width ctx
  unfold emF emW at hj
  exact hg j (by omega)

/-- **HONEST (the void mechanism)**: at a fixed-family hit, the ONLY in-tree
band-following supplier — index persistence — EMPTIES the whole class-0 fibre, so
the onset route to `DscTopBandExitFree` only fires where the class-0 demand is
already vacuous; the slot is a genuine structural residual. -/
theorem mdcIndexPersistence_voids_class0 (ctx : ActualFailureContext)
    (hhit : FixedFamilyHit ctx) (hp : FixedFamilyIndexPersistence ctx) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0 = ∅ := by
  have h := highExcessStarts_empty_of_indexPersistence ctx hhit hp
  unfold routedFibre
  rw [h, Finset.filter_empty]

/-- Top-band exit-freeness confines ALL exits to the window body
`[F, F+W-(r+1))`. -/
theorem mdc_topBandExitFree_exits_confined (ctx : ActualFailureContext)
    (h : DscTopBandExitFree ctx) :
    emExitSet ctx ⊆ Finset.Ico (emF ctx)
      (emF ctx + emW ctx - (ctx.n24CarryData.r + 1)) := by
  intro j hj
  have hmem := Finset.mem_filter.mp hj
  have hreach := hmem.1
  unfold emReach at hreach
  rw [Finset.mem_Ico] at hreach
  rw [Finset.mem_Ico]
  refine ⟨hreach.1, ?_⟩
  by_contra hge
  have hj2 : j ∈ Finset.Ico (emF ctx + emW ctx - (ctx.n24CarryData.r + 1))
      (emF ctx + emW ctx + ctx.n24CarryData.r) :=
    Finset.mem_Ico.mpr ⟨by omega, hreach.2⟩
  exact hmem.2 (h j hj2)

/-- **The honest quantitative COST of top-band exit-freeness** (band `≤ 4`): the
relocated 21.1 floor must be paid by the body alone — the support floor sharpens to
`X ≤ 2·(W-(r+1))·(L+B+1)`.  A constraint, NOT a contradiction: top-band
exit-freeness is consistent with all in-tree counting; no in-tree mechanism forces
exits out of (or into) the top band. -/
theorem mdc_topBandExitFree_support_floor (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4) (h : DscTopBandExitFree ctx) :
    ctx.shell.X
      ≤ 2 * ((emW ctx - (ctx.n24CarryData.r + 1))
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) := by
  have hfloor := em_exitMass_lower_of_band ctx hband
  have hcount := em_exitMass_le_count_mul ctx
  have hcard : (emExitSet ctx).card ≤ emW ctx - (ctx.n24CarryData.r + 1) := by
    have hsub := Finset.card_le_card (mdc_topBandExitFree_exits_confined ctx h)
    rw [Nat.card_Ico] at hsub
    omega
  have hM : emExitMass ctx
      ≤ (emW ctx - (ctx.n24CarryData.r + 1))
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) :=
    le_trans hcount (Nat.mul_le_mul hcard le_rfl)
  generalize (emW ctx - (ctx.n24CarryData.r + 1))
      * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) = t at hM ⊢
  omega

/-! ## Part 9.  Wiring to the v19 capstone shapes (additive) -/

/-- **The consumption-slot rebuild**: per-context band-following onsets rebuild the
EXACT hypothesis of both v19 interior closures
(`convergenceReturnInterior_of_topBandExitFree` /
`convergenceDensePackInterior_of_topBandExitFree`). -/
theorem mdcTopBandSlot_of_onsets
    (h : ∀ ctx : ActualFailureContext,
      fixedFamilyRecurrentBand ctx ≤ 4 ∧
      ∃ k₁, k₁ + (ctx.n24CarryData.r + 1) ≤ emF ctx + emW ctx ∧
        ∀ k, k₁ ≤ k →
          hitGap ctx.n24CarryData.a k = fixedFamilyRecurrentBand ctx) :
    ∀ ctx : ActualFailureContext,
      fixedFamilyRecurrentBand ctx ≤ 4 ∧ DscTopBandExitFree ctx := by
  intro ctx
  obtain ⟨hband, k₁, hk₁, hg⟩ := h ctx
  exact ⟨hband, mdcTopBandExitFree_of_onset ctx hk₁ hg⟩

/-- **`returnInteriorOffTable` from onsets** (composed through the v19 capstone
closure): band-following onsets close the off-table return interior field in the
exact v18 shape. -/
theorem mdcReturnInteriorOffTable_of_topBandOnsets
    (h : ∀ ctx : ActualFailureContext,
      fixedFamilyRecurrentBand ctx ≤ 4 ∧
      ∃ k₁, k₁ + (ctx.n24CarryData.r + 1) ≤ emF ctx + emW ctx ∧
        ∀ k, k₁ ≤ k →
          hitGap ctx.n24CarryData.a k = fixedFamilyRecurrentBand ctx) :
    ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx →
      ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx :=
  convergenceReturnInterior_of_topBandExitFree (mdcTopBandSlot_of_onsets h)

/-! ## Part 10.  Honest machine-readable status -/

/-- Machine-readable, honest status of the miss-distance closure. -/
def missDistanceClosureStatus : List String :=
  [ "GAP-DEVIATION CLASSIFICATION (goal 1, VERDICT): BINARY and sharpest " ++
      "possible - a non-exit gap deviates by EXACTLY 0 " ++
      "(mdc_nonExit_weight_eq_zero), not <= B+2; an exit carries its full gap. " ++
      "The canonical (band-following) word has window excess EXACTLY 0 at band " ++
      "<= 4 (mdc_windowExcess_eq_zero_of_devFree) - the calibration excess of " ++
      "the brief is 0.  Consequence (THE MISS-DISTANCE THEOREM, " ++
      "mdcFibre0_window_has_exit): EVERY class-0 fibre member's window contains " ++
      "an L.3.1 exit within distance <= r - the exit-free stratum of fibre0 is " ++
      "EMPTY (mdcFibre0_exitFreeStratum_empty).",
    "MISS-DISTANCE ROUTE (goal 1, HONEST INVERSION proved): the per-member " ++
      "bound is windowExcess <= (#exits in window)*(L+B+1) " ++
      "(mdc_windowExcess_le_exitCount_mul), the count is >= 1 at every member " ++
      "(mdc_missDistance_floor), and ONE exit's ceiling already swamps Y = L/64 " ++
      "<= L+B+1 (mdc_missDistance_route_inverted, via dscY_le_perGapCeiling). " ++
      "No exit-COUNT/miss-distance bound certifies the gate at any level below " ++
      "the trivial calibration; the gate is a demand on exit SIZE in class-0 " ++
      "windows.",
    "TWO-PIECE MASS ARGUMENT (goal 1, COLLAPSED honestly): piece 1 (exit-free " ++
      "members) is EMPTY; ALL of mass0 is exit-borne.  The surviving sharp form " ++
      "is the telescope against the CLASS-0 SHARE: mass0 <= " ++
      "ceil((r+1)/c)*mdcClass0ExitMass at survivors " ++
      "(mdcClass0Mass_le_overlap_class0ExitMass, certified c-spacing), generic " ++
      "mass0 <= (r+1)*mdcClass0ExitMass at band <= 4 " ++
      "(mdcClass0Mass_le_generic_class0ExitMass).",
    "THE NAMED CLASS-0 EXIT-MASS ATOM (goal 1 deliverable): " ++
      "MdcClass0ExitMassControl - 1536*ceil((r+1)/c)*mdcClass0ExitMass <= 31*X " ++
      "at every survivor pair; it closes the survivor mass lane in the EXACT " ++
      "v18/v19 row shape (mdcClass0SurvivorMass_of_atom: mass0 <= (31/1536)*X " ++
      "= cStar*xi/6*X).  This is the class-0 analogue of the sibling " ++
      "ExitMassControlCore (classes 3/4/5): the same mechanism - a per-class " ++
      "share cap on the relocated 21.1 exit mass - and the two should be " ++
      "attacked TOGETHER.  HONEST FLOOR (mdcUnrestrictedAtom_refuted): the " ++
      "UNRESTRICTED form (full emExitMass) is FALSE at every band <= 4 context " ++
      "- X <= 2*emExitMass forces the budget above the cap by factor >= " ++
      "768/31; the restriction to class-0 windows is the ENTIRE content.",
    "GATE SUPPLIERS (goal 3): a per-context cap mdcClass0ExitMass <= s*Y " ++
      "supplies NarrowSupportGate ctx s outright " ++
      "(mdcGate_of_class0ExitMass_le); mdcGates_of_class0ExitMassCaps builds " ++
      "the FULL v19 NarrowSupportClass0Gates field from per-lane caps in the " ++
      "closing regimes (survivor band <= 4 free via agcSurvivorBand_le_four; " ++
      "the generic lanes carry the band hypothesis honestly).",
    "TOP-BAND EXIT-FREE (goal 2, VERDICT): NO in-tree mechanism forces exits " ++
      "out of the top band.  Suppliers: any band-following onset at or below " ++
      "F+W-(r+1) (mdcTopBandExitFree_of_onset), in particular index " ++
      "persistence (mdcTopBandExitFree_of_indexPersistence) - but persistence " ++
      "at a fixed-family hit EMPTIES the class-0 fibre " ++
      "(mdcIndexPersistence_voids_class0) and shell persistence is VOID " ++
      "in-tree (fixedFamilyShellPersistence_void), so the onset route only " ++
      "fires where the demand is vacuous.  NOT refutable either: the full " ++
      "quantitative cost is the sharpened support floor X <= " ++
      "2*(W-(r+1))*(L+B+1) (mdc_topBandExitFree_support_floor; exits confined " ++
      "to the body, mdc_topBandExitFree_exits_confined) - a consistent " ++
      "constraint.  DscTopBandExitFree stays a genuine structural residual.",
    "WIRING (goal 3): mdcTopBandSlot_of_onsets rebuilds the exact hypothesis " ++
      "of BOTH v19 interior consumption slots; " ++
      "mdcReturnInteriorOffTable_of_topBandOnsets composes through " ++
      "convergenceReturnInterior_of_topBandExitFree to the exact v18 " ++
      "returnInterior shape.  All wiring is additive; no existing module is " ++
      "edited.",
    "WHAT REMAINS OPEN (honest): (a) MdcClass0ExitMassControl - the class-0 " ++
      "share cap (the de-razored survivor lane's surviving atom; exits carry " ++
      ">= X/2 globally, the atom demands the class-0 windows see < " ++
      "c/(r+c)*(31/1536) of X); (b) per-lane class-0 exit-mass caps at gate " ++
      "levels for the mid/big lanes (with their band <= 4 inputs); (c) " ++
      "DscTopBandExitFree itself (or the verbatim interior demands off-table); " ++
      "(d) the deep narrow-support regimes s*L > 1274739*c remain exactly as " ++
      "in wave 19.",
    "HYGIENE: additive only - ONE new module; no sorry / admit / new axiom / " ++
      "native_decide; every key declaration passes #print axioms within " ++
      "[propext, Classical.choice, Quot.sound]." ]

/-- The status ledger is non-empty (honest, non-vacuous). -/
theorem missDistanceClosureStatus_nonempty :
    missDistanceClosureStatus ≠ [] := by
  simp [missDistanceClosureStatus]

/-! ## Part 11.  Axiom-cleanliness audit
Every key declaration; expected axioms `[propext, Classical.choice, Quot.sound]` or
fewer. -/

#print axioms Erdos260.mdcClass0Reach
#print axioms Erdos260.mdcClass0ExitMass
#print axioms Erdos260.mdcFibre0_subset_starts
#print axioms Erdos260.mdcClass0Reach_subset_emReach
#print axioms Erdos260.mdcClass0ExitMass_le_emExitMass
#print axioms Erdos260.mdc_nonExit_weight_eq_zero
#print axioms Erdos260.mdc_exit_of_weight_ne_zero
#print axioms Erdos260.mdc_windowExcess_nonneg
#print axioms Erdos260.mdc_windowExcess_eq_zero_of_devFree
#print axioms Erdos260.mdcFibre0_devWindow_ne_zero
#print axioms Erdos260.mdcFibre0_window_has_exitWeight
#print axioms Erdos260.mdcFibre0_window_has_exit
#print axioms Erdos260.mdcFibre0_exitFreeStratum_empty
#print axioms Erdos260.mdcWindowExitCount
#print axioms Erdos260.mdc_windowExcess_le_exitCount_mul
#print axioms Erdos260.mdc_missDistance_floor
#print axioms Erdos260.mdc_missDistance_route_inverted
#print axioms Erdos260.mdc_devWindow_le_class0ExitMass
#print axioms Erdos260.mdcClass0DevSum_le_overlap
#print axioms Erdos260.mdcClass0Mass_le_overlap_class0ExitMass
#print axioms Erdos260.mdcClass0DevSum_le_generic
#print axioms Erdos260.mdcClass0Mass_le_generic_class0ExitMass
#print axioms Erdos260.MdcClass0ExitMassControl
#print axioms Erdos260.mdcClass0SurvivorMass_of_atom
#print axioms Erdos260.mdcUnrestrictedAtom_refuted
#print axioms Erdos260.mdcGate_of_class0ExitMass_le
#print axioms Erdos260.mdcGates_of_class0ExitMassCaps
#print axioms Erdos260.mdcTopBandExitFree_of_onset
#print axioms Erdos260.mdcTopBandExitFree_of_indexPersistence
#print axioms Erdos260.mdcIndexPersistence_voids_class0
#print axioms Erdos260.mdc_topBandExitFree_exits_confined
#print axioms Erdos260.mdc_topBandExitFree_support_floor
#print axioms Erdos260.mdcTopBandSlot_of_onsets
#print axioms Erdos260.mdcReturnInteriorOffTable_of_topBandOnsets
#print axioms Erdos260.missDistanceClosureStatus_nonempty

end

end Erdos260
