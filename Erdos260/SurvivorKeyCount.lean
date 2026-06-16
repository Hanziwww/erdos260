import Erdos260.Erdos260WindowOnesCapstone
import Erdos260.ParityResidueClosure

/-!
# Survivor key counting: the b2-free per-datum envelope closures, the survivor cross
table, and the window-ones grading (`SurvivorKeyCount`)

This module (NEW; it edits no existing file) harvests the per-survivor counting closures
now available after the wave-12 parity pass (`ParityResidueClosure`) and the wave-13 gap
dynamics (`DirtySliceEnvelope`), against the two capstone surfaces
(`Erdos260ChargeCapstone` / `Erdos260WindowOnesCapstone`).

## Goal 1 - the per-datum envelope closures (honest verdicts)

* **The fifteen band-2-free pairs CLOSE the envelope outright**: at
  `(5,2) (9,1) (9,4) (15,1) (15,2) (17,8) (21,1) (21,3) (21,10) (33,1) (33,16) (41,20)
  (63,1) (63,3) (63,4)` the class-4 fibre is EMPTY (`returnCtxAllFour_of_b2FreeDatum`), so
  `SliceDirtyEnvelope` holds vacuously - fifteen per-datum closures
  (`sliceDirtyEnvelope_of_datum_*`) plus the aggregate dispatcher
  (`sliceDirtyEnvelope_of_b2FreeDatum`), each through the public bridge
  `sliceDirtyEnvelope_of_returnZeroBody`.
* **The five unique-band-2 member-EVEN parity pairs get the honest lcm form**: at
  `(7,3)c2{2} (31,15)c4{4} (39,1)c4{2} (39,6)c6{4} (55,2)c8{2}` same-slice members share
  `carryVal2 = v`, are `2^v`-spaced (`sliceMembers_spaced` engine inside
  `returnSelfRef_slice_pair_spacing`), AND are congruent mod the period `c`
  (`olcFibre_pair_mod_eq_of_band2_unique`) - the joint congruence spaces them at
  `>= lcm(2^v, c)`, so `|slice| <= (W + lcm - 1) / lcm` (`sliceCard_le_of_band2_unique`,
  per-datum `sliceCard_le_lcm_of_datum_*`), sharpened against the wave-13 window-ones count
  to `|slice| <= min(|windowOnes| + 1, (W + lcm - 1)/lcm)`
  (`sliceCard_le_min_of_band2_unique`).  HONEST: this does NOT close the envelope outright -
  `W ~ c0 * X` grows while `liftLevelBound X <= L + 1`, so `(W + lcm - 1)/lcm <= L + 1`
  fails generically; the exact conditional form is recorded as
  `sliceDirtyEnvelope_of_band2_unique_lcm_small`.  The parity pin adds: at Q odd the val-0
  part of the fibre is EMPTY (`olcFibre_val0_empty_of_parityEvenDatum`) and every slice
  member has `carryVal2 >= 1` (`slice_member_val_pos_of_parityEvenDatum`), so `lcm >= 2`.
* `(39,19)` (residues `{6,8}`, not unique) gets NO c-spacing - only the parity transfer;
  recorded honestly in the status.  At `(7,3)`/`(31,15)` the in-tree
  `ReturnB2OneSpacedDatum` closures already give singletons on the `W <= 2` / `W <= 4`
  regimes; the lcm forms here are regime-free.

## Goal 2 - the b2-free aggregate and the cross table

`ReturnLaneFree ctx` bundles ALL FIVE Return-lane demands (gates, zero, maxClean, interior,
envelope); `returnLane_free_of_datumB2Free` + fifteen per-datum instances close it on every
band-2-free pair.  THE CROSS TABLE (formalized):

* class-0 survivors (19 pairs, `Class0DatumSurvivor`) cross the b2-free list in EXACTLY
  FIVE pairs: `(17,8) (21,1) (33,1) (33,16) (41,20)` (`Class0SurvivorB2FreeCross`,
  `class0Survivor_b2_split`) - at these the WHOLE Return lane is free
  (`returnLane_free_of_class0Cross`), so the joint demand drops to the non-Return fields;
  the other 14 survivors are NOT b2-free (`Class0SurvivorB2HeavyRest`).
* class-1 closed pairs (`Class1DatumClosed`) cross the b2-free list in `(63,1) (63,3)
  (63,4)` (`Class1ClosedB2FreeCross`) - at these the Return lane is free AND the class-1
  routed fibre is EMPTY (`jointFree_of_class1Cross`); `(33,1) (33,16)` have `q = 33` in
  `class1ClosedModuli` (`q33_mem_class1ClosedModuli`), voiding the `class1DeepLow` guard.
* class-1 `63@10` is NOT b2-free (`b2 = 1`; it is the member-ODD parity pin instead).
* bonus crosses: `(39,1)` is class-0 survivor AND class-1 closed AND member-EVEN
  parity-pinned (`datum_39_1_crossDossier`); `(35,2)` is class-0 survivor AND class-1
  closed (`datum_35_2_crossDossier`).

## Goal 3 - the window-ones consequence harvest (the grading)

`sliceCard_le_windowOnes_succ` holds for EVERY slice, so:

* **`windowOnes = 0` gives EVERYTHING**: all slices are singletons
  (`allSlices_card_le_one_of_windowOnes_zero`), the FULL key injectivity holds
  (`keyInjOn_of_windowOnes_zero`), hence `ReturnZeroBody`
  (`returnZeroBody_of_windowOnes_zero`, via the parity-free master equivalence) and the
  envelope (`sliceDirtyEnvelope_of_windowOnes_zero`).
* **`|windowOnes| + 1 <= liftLevelBound X` gives the envelope** (the in-tree
  `sliceDirtyEnvelope_of_windowOnesBound`); the atom FORCES `|windowOnes| <= L`
  (`windowOnes_le_depth_of_bound` - necessary, NOT sufficient, since `liftLevelBound X`
  may sit below `L + 1`).
* The regimes are characterized (`windowOnes_regime_trichotomy`,
  `windowOnes_regime_consequence`): zero => key injectivity; bounded => envelope; above
  the bound => NO unconditional consequence (honest).
* GRADED FIELD WIRING (additive only): `ReturnWindowOnesZeroField` (the zero atom under
  the verbatim envelope-field guards) discharges the wave-12 key field
  (`returnKeyInjectiveField_of_zeroField`), the wave-13 entry field
  (`returnWindowOnesField_of_zeroField`), the parity-free envelope field
  (`returnDirtyEnvelopeField_of_zeroField`) and the Q-odd named target
  (`dirtyEnvelopeQOddField_of_zeroField`); the surface combinator
  `windowOnesResidual_withZeroField` + endpoint `erdos260_of_windowOnesZeroField` wire it
  into the capstone chain.

No `sorry`, no `admit`, no new `axiom`, no `native_decide` (`decide` only on small closed
orbit/Finset goals); additive only - no existing module is edited.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 1.  The window-ones zero harvest (goal 3, context level)

`sliceCard_le_windowOnes_succ` bounds EVERY slice of the self-referential key by
`|windowOnes| + 1`; at `windowOnes = 0` every slice is a singleton and the FULL capstone key
injectivity follows - not merely the envelope. -/

/-- **Zero window ones make every slice a singleton** - every key value `y`, no dirtiness
hypothesis. -/
theorem allSlices_card_le_one_of_windowOnes_zero (ctx : ActualFailureContext)
    (h : (returnWindowOnes ctx).card = 0) (y : ℕ) :
    (olcSlice ctx (returnSelfRefKey ctx) y).card ≤ 1 := by
  have hb := sliceCard_le_windowOnes_succ ctx y
  omega

/-- Singleton slices give the FULL key injectivity on the class-4 fibre (the capstone
demand): two same-key members sit in one slice of cardinality `<= 1`. -/
theorem keyInjOn_of_slices_le_one (ctx : ActualFailureContext)
    (h : ∀ y, (olcSlice ctx (returnSelfRefKey ctx) y).card ≤ 1) :
    ReturnKeyInjOn ctx := by
  intro x hx z hz hkey
  exact Finset.card_le_one.mp (h (returnSelfRefKey ctx x)) x (mem_own_slice ctx hx)
    z (mem_slice_of_key_eq ctx hz hkey)

/-- **THE ZERO HARVEST (goal 3)**: no raw ones in `(F, F + W)` forces the FULL key
injectivity `ReturnKeyInjOn` - the sharpest Return demand of the whole chain, not merely
the envelope. -/
theorem keyInjOn_of_windowOnes_zero (ctx : ActualFailureContext)
    (h : (returnWindowOnes ctx).card = 0) : ReturnKeyInjOn ctx :=
  keyInjOn_of_slices_le_one ctx (allSlices_card_le_one_of_windowOnes_zero ctx h)

/-- Zero window ones give the verbatim `returnZero` body, through the parity-free master
equivalence (`returnZeroBody_iff_keyInjOn_uncond`). -/
theorem returnZeroBody_of_windowOnes_zero (ctx : ActualFailureContext)
    (h : (returnWindowOnes ctx).card = 0) : ReturnZeroBody ctx :=
  (returnZeroBody_iff_keyInjOn_uncond ctx).mpr (keyInjOn_of_windowOnes_zero ctx h)

/-- Zero window ones give the wave-13 atom for free (`1 <= liftLevelBound`). -/
theorem returnWindowOnesBound_of_zero (ctx : ActualFailureContext)
    (h : (returnWindowOnes ctx).card = 0) : ReturnWindowOnesBound ctx := by
  show (returnWindowOnes ctx).card + 1 ≤ liftLevelBound ctx.shell.X
  have h1 := one_le_liftLevelBound ctx.shell.X
  omega

/-- Zero window ones give the dirty-slice envelope (through injectivity - with room to
spare). -/
theorem sliceDirtyEnvelope_of_windowOnes_zero (ctx : ActualFailureContext)
    (h : (returnWindowOnes ctx).card = 0) : SliceDirtyEnvelope ctx :=
  sliceDirtyEnvelope_of_keyInjOn ctx (keyInjOn_of_windowOnes_zero ctx h)

/-- **Honest placement of the graded atom**: the window-ones bound FORCES
`|windowOnes| <= L` (via `liftLevelBound X <= L + 1`).  This is the necessary direction
only - `|windowOnes| <= L` is NOT sufficient, since `liftLevelBound X` may sit strictly
below `L + 1`. -/
theorem windowOnes_le_depth_of_bound (ctx : ActualFailureContext)
    (h : ReturnWindowOnesBound ctx) :
    (returnWindowOnes ctx).card ≤ shellLadderDepth ctx := by
  have h1 := returnLiftLevelBound_le ctx
  have h2 : (returnWindowOnes ctx).card + 1 ≤ liftLevelBound ctx.shell.X := h
  omega

/-- **The regime trichotomy**: every context sits in exactly one of - zero window ones /
positive but under the envelope bound / above the envelope bound. -/
theorem windowOnes_regime_trichotomy (ctx : ActualFailureContext) :
    (returnWindowOnes ctx).card = 0
      ∨ (1 ≤ (returnWindowOnes ctx).card ∧ ReturnWindowOnesBound ctx)
      ∨ liftLevelBound ctx.shell.X < (returnWindowOnes ctx).card + 1 := by
  rcases Nat.eq_zero_or_pos (returnWindowOnes ctx).card with h0 | h1
  · exact Or.inl h0
  · rcases Nat.lt_or_ge (liftLevelBound ctx.shell.X)
      ((returnWindowOnes ctx).card + 1) with hlt | hge
    · exact Or.inr (Or.inr hlt)
    · exact Or.inr (Or.inl ⟨h1, hge⟩)

/-- **The graded consequence chain (honest)**: zero gives the FULL key injectivity;
bounded gives the envelope; above the bound there is NO unconditional consequence - the
third branch returns only the defining inequality. -/
theorem windowOnes_regime_consequence (ctx : ActualFailureContext) :
    ReturnKeyInjOn ctx ∨ SliceDirtyEnvelope ctx
      ∨ liftLevelBound ctx.shell.X < (returnWindowOnes ctx).card + 1 := by
  rcases windowOnes_regime_trichotomy ctx with h | ⟨_, hb⟩ | h
  · exact Or.inl (keyInjOn_of_windowOnes_zero ctx h)
  · exact Or.inr (Or.inl (sliceDirtyEnvelope_of_windowOnesBound ctx hb))
  · exact Or.inr (Or.inr h)

/-! ## Part 2.  The joint lcm spacing at unique-band-2 data (goal 1, the honest per-datum
count)

Same-slice members share `carryVal2 = v` and are `2^v`-spaced (wave-13); at a unique-band-2
period they are also congruent mod `c` (wave-5) - so they are `lcm(2^v, c)`-spaced inside
the width-`W` window, giving `|slice| <= (W + lcm - 1) / lcm`. -/

private theorem one_le_lcm {a b : ℕ} (ha : 0 < a) (hb : 0 < b) : 1 ≤ Nat.lcm a b := by
  rcases Nat.eq_zero_or_pos (Nat.lcm a b) with h0 | hp
  · exfalso
    have hdvd : Nat.lcm a b ∣ a * b :=
      Nat.lcm_dvd (dvd_mul_right a b) (dvd_mul_left b a)
    rw [h0] at hdvd
    have hab : a * b = 0 := zero_dvd_iff.mp hdvd
    have hpos : 0 < a * b := Nat.mul_pos ha hb
    omega
  · exact hp

/-- **The joint-congruence slice count**: with a unique band-2 residue `j₀` in a period
`c`, every slice of the self-referential key containing a member `x` (of common valuation
`v = carryVal2 x`) has at most `(W + lcm(2^v, c) - 1) / lcm(2^v, c)` members - the
`2^v`-spacing and the mod-`c` congruence glue to an `lcm`-spacing inside the width-`W`
window. -/
theorem sliceCard_le_of_band2_unique (ctx : ActualFailureContext) {c j₀ : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (huniq : ∀ j, 1 ≤ j → j ≤ c →
      canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) = 2 → j = j₀)
    {y x : ℕ} (hx : x ∈ olcSlice ctx (returnSelfRefKey ctx) y) :
    (olcSlice ctx (returnSelfRefKey ctx) y).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card
          + Nat.lcm (2 ^ carryVal2 ctx x) c - 1) / Nat.lcm (2 ^ carryVal2 ctx x) c := by
  have hxf : x ∈ olcFibre ctx := mem_olcFibre_of_mem_olcSlice hx
  have hwin := olcFibre_mem_window ctx hxf
  have hW1 : 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card := by omega
  have h2v : 0 < 2 ^ carryVal2 ctx x := pow_pos (by norm_num) _
  have hm1 : 1 ≤ Nat.lcm (2 ^ carryVal2 ctx x) c := one_le_lcm h2v (by omega)
  refine spaced_finset_card_le hm1 hW1 ?_ ?_
  · intro a ha b hb hab
    have hva : carryVal2 ctx a = carryVal2 ctx x := sliceMembers_carryVal2_eq ctx ha hx
    have hkey : returnSelfRefKey ctx a = returnSelfRefKey ctx b :=
      (key_eq_of_mem_olcSlice ha).trans (key_eq_of_mem_olcSlice hb).symm
    have hsp := (returnSelfRef_slice_pair_spacing ctx hc hper huniq
      (mem_olcFibre_of_mem_olcSlice ha) (mem_olcFibre_of_mem_olcSlice hb) hkey hab).1
    rw [hva] at hsp
    exact hsp
  · intro a ha b hb hab
    exact olcFibre_pair_dist_lt_width ctx (mem_olcFibre_of_mem_olcSlice ha)
      (mem_olcFibre_of_mem_olcSlice hb)

/-- **The sharpened per-datum count**: the lcm spacing meets the wave-13 window-ones count
in a `min` - per-datum content strictly sharper than either alone. -/
theorem sliceCard_le_min_of_band2_unique (ctx : ActualFailureContext) {c j₀ : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (huniq : ∀ j, 1 ≤ j → j ≤ c →
      canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) = 2 → j = j₀)
    {y x : ℕ} (hx : x ∈ olcSlice ctx (returnSelfRefKey ctx) y) :
    (olcSlice ctx (returnSelfRefKey ctx) y).card
      ≤ min ((returnWindowOnes ctx).card + 1)
          (((supportShell ctx.shell.d ctx.shell.X).card
            + Nat.lcm (2 ^ carryVal2 ctx x) c - 1) / Nat.lcm (2 ^ carryVal2 ctx x) c) :=
  le_min (sliceCard_le_windowOnes_succ ctx y)
    (sliceCard_le_of_band2_unique ctx hc hper huniq hx)

/-- **The honest conditional envelope closure from the lcm count**: IF the per-member lcm
count fits under `liftLevelBound X`, the envelope closes.  HONEST: generically it does NOT
fit - `W ~ c0 * X` while `liftLevelBound X <= L + 1`; this records the exact inequality a
per-datum closure would need. -/
theorem sliceDirtyEnvelope_of_band2_unique_lcm_small (ctx : ActualFailureContext)
    {c j₀ : ℕ} (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (huniq : ∀ j, 1 ≤ j → j ≤ c →
      canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) = 2 → j = j₀)
    (hsmall : ∀ k ∈ olcFibre ctx,
      ((supportShell ctx.shell.d ctx.shell.X).card
          + Nat.lcm (2 ^ carryVal2 ctx k) c - 1) / Nat.lcm (2 ^ carryVal2 ctx k) c
        ≤ liftLevelBound ctx.shell.X) :
    SliceDirtyEnvelope ctx := by
  intro y hy _hdirty
  obtain ⟨x, hxf, hxy⟩ := Finset.mem_image.mp hy
  have hxs : x ∈ olcSlice ctx (returnSelfRefKey ctx) y := by
    rw [olcSlice_def]
    exact Finset.mem_filter.mpr ⟨hxf, hxy⟩
  exact le_trans (sliceCard_le_of_band2_unique ctx hc hper huniq hxs) (hsmall x hxf)

/-! ### The five unique-band-2 member-EVEN pairs (per-datum lcm instances)

Cycle certificates decided on the concrete orbits (the same data as the wave-12 parity
tables): `(7,3)` period `2` residue `{2}`; `(31,15)` period `4` residue `{4}`; `(39,1)`
period `4` residue `{2}`; `(39,6)` period `6` residue `{4}`; `(55,2)` period `8` residue
`{2}`.  `(39,19)` has residues `{6,8}` - NOT unique, no c-spacing (parity transfer only). -/

private theorem skcCycle_7_3 : slopeOrbit 7 3 (1 + 2) = slopeOrbit 7 3 1 := by decide

private theorem skcUniq_7_3 :
    ∀ j, 1 ≤ j → j ≤ 2 → canonGap 7 (slopeOrbit 7 3 j) = 2 → j = 2 := by
  intro j h1 h2
  interval_cases j <;> decide

private theorem skcCycle_31_15 : slopeOrbit 31 15 (1 + 4) = slopeOrbit 31 15 1 := by
  decide

private theorem skcUniq_31_15 :
    ∀ j, 1 ≤ j → j ≤ 4 → canonGap 31 (slopeOrbit 31 15 j) = 2 → j = 4 := by
  intro j h1 h2
  interval_cases j <;> decide

private theorem skcCycle_39_1 : slopeOrbit 39 1 (1 + 4) = slopeOrbit 39 1 1 := by decide

private theorem skcUniq_39_1 :
    ∀ j, 1 ≤ j → j ≤ 4 → canonGap 39 (slopeOrbit 39 1 j) = 2 → j = 2 := by
  intro j h1 h2
  interval_cases j <;> decide

private theorem skcCycle_39_6 : slopeOrbit 39 6 (1 + 6) = slopeOrbit 39 6 1 := by decide

private theorem skcUniq_39_6 :
    ∀ j, 1 ≤ j → j ≤ 6 → canonGap 39 (slopeOrbit 39 6 j) = 2 → j = 4 := by
  intro j h1 h2
  interval_cases j <;> decide

private theorem skcCycle_55_2 : slopeOrbit 55 2 (1 + 8) = slopeOrbit 55 2 1 := by decide

private theorem skcUniq_55_2 :
    ∀ j, 1 ≤ j → j ≤ 8 → canonGap 55 (slopeOrbit 55 2 j) = 2 → j = 2 := by
  intro j h1 h2
  interval_cases j <;> decide

/-- `(7,3)`: slices are `lcm(2^v, 2)`-spaced - `|slice| <= (W + lcm - 1)/lcm`. -/
theorem sliceCard_le_lcm_of_datum_7_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 7) (hK : (class1SlopeDatum ctx).K₀ = 3)
    {y x : ℕ} (hx : x ∈ olcSlice ctx (returnSelfRefKey ctx) y) :
    (olcSlice ctx (returnSelfRefKey ctx) y).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card
          + Nat.lcm (2 ^ carryVal2 ctx x) 2 - 1) / Nat.lcm (2 ^ carryVal2 ctx x) 2 := by
  refine sliceCard_le_of_band2_unique ctx (c := 2) (j₀ := 2) (by norm_num) ?_ ?_ hx
  · rw [hq, hK]
    exact slopeOrbit_period_of_return skcCycle_7_3
  · rw [hq, hK]
    exact skcUniq_7_3

/-- `(31,15)`: slices are `lcm(2^v, 4)`-spaced. -/
theorem sliceCard_le_lcm_of_datum_31_15 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 31) (hK : (class1SlopeDatum ctx).K₀ = 15)
    {y x : ℕ} (hx : x ∈ olcSlice ctx (returnSelfRefKey ctx) y) :
    (olcSlice ctx (returnSelfRefKey ctx) y).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card
          + Nat.lcm (2 ^ carryVal2 ctx x) 4 - 1) / Nat.lcm (2 ^ carryVal2 ctx x) 4 := by
  refine sliceCard_le_of_band2_unique ctx (c := 4) (j₀ := 4) (by norm_num) ?_ ?_ hx
  · rw [hq, hK]
    exact slopeOrbit_period_of_return skcCycle_31_15
  · rw [hq, hK]
    exact skcUniq_31_15

/-- `(39,1)`: slices are `lcm(2^v, 4)`-spaced. -/
theorem sliceCard_le_lcm_of_datum_39_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 39) (hK : (class1SlopeDatum ctx).K₀ = 1)
    {y x : ℕ} (hx : x ∈ olcSlice ctx (returnSelfRefKey ctx) y) :
    (olcSlice ctx (returnSelfRefKey ctx) y).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card
          + Nat.lcm (2 ^ carryVal2 ctx x) 4 - 1) / Nat.lcm (2 ^ carryVal2 ctx x) 4 := by
  refine sliceCard_le_of_band2_unique ctx (c := 4) (j₀ := 2) (by norm_num) ?_ ?_ hx
  · rw [hq, hK]
    exact slopeOrbit_period_of_return skcCycle_39_1
  · rw [hq, hK]
    exact skcUniq_39_1

/-- `(39,6)`: slices are `lcm(2^v, 6)`-spaced. -/
theorem sliceCard_le_lcm_of_datum_39_6 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 39) (hK : (class1SlopeDatum ctx).K₀ = 6)
    {y x : ℕ} (hx : x ∈ olcSlice ctx (returnSelfRefKey ctx) y) :
    (olcSlice ctx (returnSelfRefKey ctx) y).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card
          + Nat.lcm (2 ^ carryVal2 ctx x) 6 - 1) / Nat.lcm (2 ^ carryVal2 ctx x) 6 := by
  refine sliceCard_le_of_band2_unique ctx (c := 6) (j₀ := 4) (by norm_num) ?_ ?_ hx
  · rw [hq, hK]
    exact slopeOrbit_period_of_return skcCycle_39_6
  · rw [hq, hK]
    exact skcUniq_39_6

/-- `(55,2)`: slices are `lcm(2^v, 8)`-spaced. -/
theorem sliceCard_le_lcm_of_datum_55_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 55) (hK : (class1SlopeDatum ctx).K₀ = 2)
    {y x : ℕ} (hx : x ∈ olcSlice ctx (returnSelfRefKey ctx) y) :
    (olcSlice ctx (returnSelfRefKey ctx) y).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card
          + Nat.lcm (2 ^ carryVal2 ctx x) 8 - 1) / Nat.lcm (2 ^ carryVal2 ctx x) 8 := by
  refine sliceCard_le_of_band2_unique ctx (c := 8) (j₀ := 2) (by norm_num) ?_ ?_ hx
  · rw [hq, hK]
    exact slopeOrbit_period_of_return skcCycle_55_2
  · rw [hq, hK]
    exact skcUniq_55_2

/-! ### The parity-pin consequences at the member-EVEN data (the val-0 emptiness) -/

/-- At every member-EVEN parity-pinned datum (Q odd) the val-0 part of the class-4 fibre is
EMPTY - the per-datum "val-0 slices are empty" fact of the brief, aggregated over the six
pairs `(7,3) (31,15) (39,1) (39,6) (39,19) (55,2)`. -/
theorem olcFibre_val0_empty_of_parityEvenDatum (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) (h : ReturnB2ParityEvenDatum ctx) :
    (olcFibre ctx).filter (fun k => carryVal2 ctx k = 0) = ∅ :=
  olcFibre_val0_filter_eq_empty_of_memberEven ctx hQodd
    (olcFibre_even_of_parityEvenDatum ctx h)

/-- At every member-EVEN parity-pinned datum (Q odd) every slice member has
`carryVal2 >= 1` - so the slice spacing modulus `lcm(2^v, c)` is at least `2`. -/
theorem slice_member_val_pos_of_parityEvenDatum (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) (h : ReturnB2ParityEvenDatum ctx)
    {y k : ℕ} (hk : k ∈ olcSlice ctx (returnSelfRefKey ctx) y) :
    1 ≤ carryVal2 ctx k :=
  carryVal2_pos_of_memberEven ctx hQodd (olcFibre_even_of_parityEvenDatum ctx h) k
    (mem_olcFibre_of_mem_olcSlice hk)

/-! ## Part 3.  The fifteen band-2-free per-datum envelope closures (goal 1, closed
outright) and the Return-lane-free bundle (goal 2)

A band-2-free cycle empties the class-4 fibre, so ALL FIVE Return-lane demands hold - the
four wave-4 bodies (`returnCtxAllFour_of_b2FreeDatum`) and the envelope (vacuous on an
empty fibre, reached through the public bridge `sliceDirtyEnvelope_of_returnZeroBody`). -/

/-- **The Return-lane-free bundle**: all five Return-lane demands of the capstone surfaces
at one context - gates, zero, maxClean, interior, and the dirty-slice envelope. -/
def ReturnLaneFree (ctx : ActualFailureContext) : Prop :=
  ReturnGatesBody ctx ∧ ReturnZeroBody ctx ∧ ReturnMaxCleanBody ctx
    ∧ ReturnInteriorBody ctx ∧ SliceDirtyEnvelope ctx

/-- The four wave-4 bodies extend to the full five-field bundle (the envelope rides on the
zero body). -/
theorem returnLaneFree_of_ctxAllFour (ctx : ActualFailureContext)
    (h : ReturnCtxAllFour ctx) : ReturnLaneFree ctx :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, sliceDirtyEnvelope_of_returnZeroBody ctx h.2.1⟩

/-- **THE AGGREGATE DISPATCHER (goal 2)**: every band-2-free datum frees the WHOLE Return
lane - count gates, digit fields, interior, and the envelope at once. -/
theorem returnLane_free_of_datumB2Free (ctx : ActualFailureContext)
    (h : ReturnB2FreeDatum ctx) : ReturnLaneFree ctx :=
  returnLaneFree_of_ctxAllFour ctx (returnCtxAllFour_of_b2FreeDatum ctx h)

/-- `(5,2)` frees the Return lane. -/
theorem returnLane_free_of_datum_5_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 5) (hK : (class1SlopeDatum ctx).K₀ = 2) :
    ReturnLaneFree ctx :=
  returnLaneFree_of_ctxAllFour ctx (returnCtxAllFour_of_datum_5_2 ctx hq hK)

/-- `(9,1)` frees the Return lane. -/
theorem returnLane_free_of_datum_9_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 9) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    ReturnLaneFree ctx :=
  returnLaneFree_of_ctxAllFour ctx (returnCtxAllFour_of_datum_9_1 ctx hq hK)

/-- `(9,4)` frees the Return lane. -/
theorem returnLane_free_of_datum_9_4 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 9) (hK : (class1SlopeDatum ctx).K₀ = 4) :
    ReturnLaneFree ctx :=
  returnLaneFree_of_ctxAllFour ctx (returnCtxAllFour_of_datum_9_4 ctx hq hK)

/-- `(15,1)` frees the Return lane. -/
theorem returnLane_free_of_datum_15_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 15) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    ReturnLaneFree ctx :=
  returnLaneFree_of_ctxAllFour ctx (returnCtxAllFour_of_datum_15_1 ctx hq hK)

/-- `(15,2)` frees the Return lane. -/
theorem returnLane_free_of_datum_15_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 15) (hK : (class1SlopeDatum ctx).K₀ = 2) :
    ReturnLaneFree ctx :=
  returnLaneFree_of_ctxAllFour ctx (returnCtxAllFour_of_datum_15_2 ctx hq hK)

/-- `(17,8)` frees the Return lane. -/
theorem returnLane_free_of_datum_17_8 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 17) (hK : (class1SlopeDatum ctx).K₀ = 8) :
    ReturnLaneFree ctx :=
  returnLaneFree_of_ctxAllFour ctx (returnCtxAllFour_of_datum_17_8 ctx hq hK)

/-- `(21,1)` frees the Return lane. -/
theorem returnLane_free_of_datum_21_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 21) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    ReturnLaneFree ctx :=
  returnLaneFree_of_ctxAllFour ctx (returnCtxAllFour_of_datum_21_1 ctx hq hK)

/-- `(21,3)` frees the Return lane. -/
theorem returnLane_free_of_datum_21_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 21) (hK : (class1SlopeDatum ctx).K₀ = 3) :
    ReturnLaneFree ctx :=
  returnLaneFree_of_ctxAllFour ctx (returnCtxAllFour_of_datum_21_3 ctx hq hK)

/-- `(21,10)` frees the Return lane. -/
theorem returnLane_free_of_datum_21_10 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 21) (hK : (class1SlopeDatum ctx).K₀ = 10) :
    ReturnLaneFree ctx :=
  returnLaneFree_of_ctxAllFour ctx (returnCtxAllFour_of_datum_21_10 ctx hq hK)

/-- `(33,1)` frees the Return lane. -/
theorem returnLane_free_of_datum_33_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 33) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    ReturnLaneFree ctx :=
  returnLaneFree_of_ctxAllFour ctx (returnCtxAllFour_of_datum_33_1 ctx hq hK)

/-- `(33,16)` frees the Return lane. -/
theorem returnLane_free_of_datum_33_16 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 33) (hK : (class1SlopeDatum ctx).K₀ = 16) :
    ReturnLaneFree ctx :=
  returnLaneFree_of_ctxAllFour ctx (returnCtxAllFour_of_datum_33_16 ctx hq hK)

/-- `(41,20)` frees the Return lane. -/
theorem returnLane_free_of_datum_41_20 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 41) (hK : (class1SlopeDatum ctx).K₀ = 20) :
    ReturnLaneFree ctx :=
  returnLaneFree_of_ctxAllFour ctx (returnCtxAllFour_of_datum_41_20 ctx hq hK)

/-- `(63,1)` frees the Return lane. -/
theorem returnLane_free_of_datum_63_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    ReturnLaneFree ctx :=
  returnLaneFree_of_ctxAllFour ctx (returnCtxAllFour_of_datum_63_1 ctx hq hK)

/-- `(63,3)` frees the Return lane. -/
theorem returnLane_free_of_datum_63_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) (hK : (class1SlopeDatum ctx).K₀ = 3) :
    ReturnLaneFree ctx :=
  returnLaneFree_of_ctxAllFour ctx (returnCtxAllFour_of_datum_63_3 ctx hq hK)

/-- `(63,4)` frees the Return lane. -/
theorem returnLane_free_of_datum_63_4 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) (hK : (class1SlopeDatum ctx).K₀ = 4) :
    ReturnLaneFree ctx :=
  returnLaneFree_of_ctxAllFour ctx (returnCtxAllFour_of_datum_63_4 ctx hq hK)

/-! ### The fifteen per-datum envelope closures (goal 1) -/

/-- `(5,2)` closes the envelope outright (empty class-4 fibre). -/
theorem sliceDirtyEnvelope_of_datum_5_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 5) (hK : (class1SlopeDatum ctx).K₀ = 2) :
    SliceDirtyEnvelope ctx :=
  (returnLane_free_of_datum_5_2 ctx hq hK).2.2.2.2

/-- `(9,1)` closes the envelope outright. -/
theorem sliceDirtyEnvelope_of_datum_9_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 9) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    SliceDirtyEnvelope ctx :=
  (returnLane_free_of_datum_9_1 ctx hq hK).2.2.2.2

/-- `(9,4)` closes the envelope outright. -/
theorem sliceDirtyEnvelope_of_datum_9_4 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 9) (hK : (class1SlopeDatum ctx).K₀ = 4) :
    SliceDirtyEnvelope ctx :=
  (returnLane_free_of_datum_9_4 ctx hq hK).2.2.2.2

/-- `(15,1)` closes the envelope outright. -/
theorem sliceDirtyEnvelope_of_datum_15_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 15) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    SliceDirtyEnvelope ctx :=
  (returnLane_free_of_datum_15_1 ctx hq hK).2.2.2.2

/-- `(15,2)` closes the envelope outright. -/
theorem sliceDirtyEnvelope_of_datum_15_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 15) (hK : (class1SlopeDatum ctx).K₀ = 2) :
    SliceDirtyEnvelope ctx :=
  (returnLane_free_of_datum_15_2 ctx hq hK).2.2.2.2

/-- `(17,8)` closes the envelope outright. -/
theorem sliceDirtyEnvelope_of_datum_17_8 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 17) (hK : (class1SlopeDatum ctx).K₀ = 8) :
    SliceDirtyEnvelope ctx :=
  (returnLane_free_of_datum_17_8 ctx hq hK).2.2.2.2

/-- `(21,1)` closes the envelope outright. -/
theorem sliceDirtyEnvelope_of_datum_21_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 21) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    SliceDirtyEnvelope ctx :=
  (returnLane_free_of_datum_21_1 ctx hq hK).2.2.2.2

/-- `(21,3)` closes the envelope outright. -/
theorem sliceDirtyEnvelope_of_datum_21_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 21) (hK : (class1SlopeDatum ctx).K₀ = 3) :
    SliceDirtyEnvelope ctx :=
  (returnLane_free_of_datum_21_3 ctx hq hK).2.2.2.2

/-- `(21,10)` closes the envelope outright. -/
theorem sliceDirtyEnvelope_of_datum_21_10 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 21) (hK : (class1SlopeDatum ctx).K₀ = 10) :
    SliceDirtyEnvelope ctx :=
  (returnLane_free_of_datum_21_10 ctx hq hK).2.2.2.2

/-- `(33,1)` closes the envelope outright. -/
theorem sliceDirtyEnvelope_of_datum_33_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 33) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    SliceDirtyEnvelope ctx :=
  (returnLane_free_of_datum_33_1 ctx hq hK).2.2.2.2

/-- `(33,16)` closes the envelope outright. -/
theorem sliceDirtyEnvelope_of_datum_33_16 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 33) (hK : (class1SlopeDatum ctx).K₀ = 16) :
    SliceDirtyEnvelope ctx :=
  (returnLane_free_of_datum_33_16 ctx hq hK).2.2.2.2

/-- `(41,20)` closes the envelope outright. -/
theorem sliceDirtyEnvelope_of_datum_41_20 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 41) (hK : (class1SlopeDatum ctx).K₀ = 20) :
    SliceDirtyEnvelope ctx :=
  (returnLane_free_of_datum_41_20 ctx hq hK).2.2.2.2

/-- `(63,1)` closes the envelope outright. -/
theorem sliceDirtyEnvelope_of_datum_63_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    SliceDirtyEnvelope ctx :=
  (returnLane_free_of_datum_63_1 ctx hq hK).2.2.2.2

/-- `(63,3)` closes the envelope outright. -/
theorem sliceDirtyEnvelope_of_datum_63_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) (hK : (class1SlopeDatum ctx).K₀ = 3) :
    SliceDirtyEnvelope ctx :=
  (returnLane_free_of_datum_63_3 ctx hq hK).2.2.2.2

/-- `(63,4)` closes the envelope outright. -/
theorem sliceDirtyEnvelope_of_datum_63_4 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) (hK : (class1SlopeDatum ctx).K₀ = 4) :
    SliceDirtyEnvelope ctx :=
  (returnLane_free_of_datum_63_4 ctx hq hK).2.2.2.2

/-- **The aggregate envelope dispatcher**: every band-2-free datum closes
`SliceDirtyEnvelope` outright. -/
theorem sliceDirtyEnvelope_of_b2FreeDatum (ctx : ActualFailureContext)
    (h : ReturnB2FreeDatum ctx) : SliceDirtyEnvelope ctx :=
  (returnLane_free_of_datumB2Free ctx h).2.2.2.2

/-! ## Part 4.  The cross table (goal 2): b2-free pairs against the surviving pairs of the
other lanes

Class-0 survivors (19 pairs, `Class0DatumSurvivor`, `17 <= q < 48`) cross the b2-free list
in EXACTLY FIVE pairs; class-1 closed pairs (`Class1DatumClosed`) cross in the three
`(63, *)` pairs; `q = 33` sits in `class1ClosedModuli`. -/

/-- **The five crossed class-0 survivor pairs**: class-0 survivors whose `(q, K₀)` is
band-2-free - at these the WHOLE Return lane is free and the joint demand drops to the
non-Return fields. -/
def Class0SurvivorB2FreeCross (ctx : ActualFailureContext) : Prop :=
  ((class1SlopeDatum ctx).q = 17 ∧ (class1SlopeDatum ctx).K₀ = 8)
  ∨ ((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 1)
  ∨ ((class1SlopeDatum ctx).q = 33 ∧ (class1SlopeDatum ctx).K₀ = 1)
  ∨ ((class1SlopeDatum ctx).q = 33 ∧ (class1SlopeDatum ctx).K₀ = 16)
  ∨ ((class1SlopeDatum ctx).q = 41 ∧ (class1SlopeDatum ctx).K₀ = 20)

/-- **The fourteen non-crossed class-0 survivor pairs**: survivors that are NOT
band-2-free - at these the Return demand genuinely remains. -/
def Class0SurvivorB2HeavyRest (ctx : ActualFailureContext) : Prop :=
  ((class1SlopeDatum ctx).q = 19 ∧ (class1SlopeDatum ctx).K₀ = 9)
  ∨ ((class1SlopeDatum ctx).q = 25 ∧ (class1SlopeDatum ctx).K₀ = 2)
  ∨ ((class1SlopeDatum ctx).q = 25 ∧ (class1SlopeDatum ctx).K₀ = 12)
  ∨ ((class1SlopeDatum ctx).q = 27 ∧ (class1SlopeDatum ctx).K₀ = 1)
  ∨ ((class1SlopeDatum ctx).q = 27 ∧ (class1SlopeDatum ctx).K₀ = 4)
  ∨ ((class1SlopeDatum ctx).q = 27 ∧ (class1SlopeDatum ctx).K₀ = 13)
  ∨ ((class1SlopeDatum ctx).q = 29 ∧ (class1SlopeDatum ctx).K₀ = 14)
  ∨ ((class1SlopeDatum ctx).q = 35 ∧ (class1SlopeDatum ctx).K₀ = 2)
  ∨ ((class1SlopeDatum ctx).q = 37 ∧ (class1SlopeDatum ctx).K₀ = 18)
  ∨ ((class1SlopeDatum ctx).q = 39 ∧ (class1SlopeDatum ctx).K₀ = 1)
  ∨ ((class1SlopeDatum ctx).q = 43 ∧ (class1SlopeDatum ctx).K₀ = 21)
  ∨ ((class1SlopeDatum ctx).q = 45 ∧ (class1SlopeDatum ctx).K₀ = 1)
  ∨ ((class1SlopeDatum ctx).q = 45 ∧ (class1SlopeDatum ctx).K₀ = 2)
  ∨ ((class1SlopeDatum ctx).q = 45 ∧ (class1SlopeDatum ctx).K₀ = 4)

/-- Every crossed pair is band-2-free. -/
theorem returnB2FreeDatum_of_class0Cross (ctx : ActualFailureContext)
    (h : Class0SurvivorB2FreeCross ctx) : ReturnB2FreeDatum ctx := by
  rcases h with ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ <;>
    simp [ReturnB2FreeDatum, hq, hK]

/-- Every crossed pair is a class-0 survivor. -/
theorem class0Survivor_of_class0Cross (ctx : ActualFailureContext)
    (h : Class0SurvivorB2FreeCross ctx) : Class0DatumSurvivor ctx := by
  rcases h with ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ <;>
    simp [Class0DatumSurvivor, hq, hK]

/-- **The crossed pairs free the Return lane**: at `(17,8) (21,1) (33,1) (33,16) (41,20)`
the joint demand drops to the non-Return fields (the class-0 residue miss et al.). -/
theorem returnLane_free_of_class0Cross (ctx : ActualFailureContext)
    (h : Class0SurvivorB2FreeCross ctx) : ReturnLaneFree ctx :=
  returnLane_free_of_datumB2Free ctx (returnB2FreeDatum_of_class0Cross ctx h)

/-- **THE CROSS SPLIT**: every class-0 survivor is either one of the five b2-free crossed
pairs or one of the fourteen non-b2-free remainder pairs - the exact partition of the
survivor list along the Return lane. -/
theorem class0Survivor_b2_split (ctx : ActualFailureContext)
    (h : Class0DatumSurvivor ctx) :
    Class0SurvivorB2FreeCross ctx ∨ Class0SurvivorB2HeavyRest ctx := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact Or.inl (by simp [Class0SurvivorB2FreeCross, h.1, h.2])
  · exact Or.inr (by simp [Class0SurvivorB2HeavyRest, h.1, h.2])
  · exact Or.inl (by simp [Class0SurvivorB2FreeCross, h.1, h.2])
  · exact Or.inr (by simp [Class0SurvivorB2HeavyRest, h.1, h.2])
  · exact Or.inr (by simp [Class0SurvivorB2HeavyRest, h.1, h.2])
  · exact Or.inr (by simp [Class0SurvivorB2HeavyRest, h.1, h.2])
  · exact Or.inr (by simp [Class0SurvivorB2HeavyRest, h.1, h.2])
  · exact Or.inr (by simp [Class0SurvivorB2HeavyRest, h.1, h.2])
  · exact Or.inr (by simp [Class0SurvivorB2HeavyRest, h.1, h.2])
  · exact Or.inl (by simp [Class0SurvivorB2FreeCross, h.1, h.2])
  · exact Or.inl (by simp [Class0SurvivorB2FreeCross, h.1, h.2])
  · exact Or.inr (by simp [Class0SurvivorB2HeavyRest, h.1, h.2])
  · exact Or.inr (by simp [Class0SurvivorB2HeavyRest, h.1, h.2])
  · exact Or.inr (by simp [Class0SurvivorB2HeavyRest, h.1, h.2])
  · exact Or.inl (by simp [Class0SurvivorB2FreeCross, h.1, h.2])
  · exact Or.inr (by simp [Class0SurvivorB2HeavyRest, h.1, h.2])
  · exact Or.inr (by simp [Class0SurvivorB2HeavyRest, h.1, h.2])
  · exact Or.inr (by simp [Class0SurvivorB2HeavyRest, h.1, h.2])
  · exact Or.inr (by simp [Class0SurvivorB2HeavyRest, h.1, h.2])

/-- **The harvest at class-0 survivors**: every class-0 survivor either has a FREE Return
lane (the five crossed pairs) or is one of the fourteen named remainder pairs. -/
theorem returnLane_free_or_heavy_of_class0Survivor (ctx : ActualFailureContext)
    (h : Class0DatumSurvivor ctx) :
    ReturnLaneFree ctx ∨ Class0SurvivorB2HeavyRest ctx :=
  (class0Survivor_b2_split ctx h).imp (returnLane_free_of_class0Cross ctx) id

/-- **The three crossed class-1 pairs**: `Class1DatumClosed` pairs that are also
band-2-free - at these BOTH the Return lane is free AND the class-1 routed fibre is
empty. -/
def Class1ClosedB2FreeCross (ctx : ActualFailureContext) : Prop :=
  ((class1SlopeDatum ctx).q = 63 ∧ (class1SlopeDatum ctx).K₀ = 1)
  ∨ ((class1SlopeDatum ctx).q = 63 ∧ (class1SlopeDatum ctx).K₀ = 3)
  ∨ ((class1SlopeDatum ctx).q = 63 ∧ (class1SlopeDatum ctx).K₀ = 4)

/-- Every crossed class-1 pair is datum-closed (band-4-free). -/
theorem class1DatumClosed_of_class1Cross (ctx : ActualFailureContext)
    (h : Class1ClosedB2FreeCross ctx) : Class1DatumClosed ctx := by
  rcases h with ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ <;>
    simp [Class1DatumClosed, hq, hK]

/-- Every crossed class-1 pair is band-2-free. -/
theorem returnB2FreeDatum_of_class1Cross (ctx : ActualFailureContext)
    (h : Class1ClosedB2FreeCross ctx) : ReturnB2FreeDatum ctx := by
  rcases h with ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ <;>
    simp [ReturnB2FreeDatum, hq, hK]

/-- **The joint class-1/Return voiding**: at `(63,1) (63,3) (63,4)` the Return lane is
free AND the class-1 routed fibre is empty - two of the six lanes settle at once. -/
theorem jointFree_of_class1Cross (ctx : ActualFailureContext)
    (h : Class1ClosedB2FreeCross ctx) :
    ReturnLaneFree ctx
      ∧ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  ⟨returnLane_free_of_datumB2Free ctx (returnB2FreeDatum_of_class1Cross ctx h),
    class1Fibre_empty_of_datumClosed ctx (class1DatumClosed_of_class1Cross ctx h)⟩

/-- `33` is a closed class-1 modulus - so at the crossed pairs `(33,1) (33,16)` the
`class1DeepLow` guard `q ∉ class1ClosedModuli` fails and the class-1 deep demand is
vacuous. -/
theorem q33_mem_class1ClosedModuli : (33 : ℕ) ∈ class1ClosedModuli := by decide

/-- The guard form at a `q = 33` context. -/
theorem class1ClosedModuli_guard_of_q33 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 33) :
    (class1SlopeDatum ctx).q ∈ class1ClosedModuli := by
  rw [hq]
  exact q33_mem_class1ClosedModuli

/-- **The `(39,1)` triple cross**: class-0 survivor AND class-1 datum-closed (empty class-1
fibre) AND member-EVEN parity-pinned - the densest single datum of the cross table.  (It is
NOT band-2-free: the Return lane demand remains, now with the lcm form
`sliceCard_le_lcm_of_datum_39_1`.) -/
theorem datum_39_1_crossDossier (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 39) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    Class0DatumSurvivor ctx ∧ Class1DatumClosed ctx
      ∧ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅
      ∧ ∀ k ∈ olcFibre ctx, k % 2 = 0 := by
  have hclosed : Class1DatumClosed ctx := by simp [Class1DatumClosed, hq, hK]
  exact ⟨by simp [Class0DatumSurvivor, hq, hK], hclosed,
    class1Fibre_empty_of_datumClosed ctx hclosed,
    olcFibre_even_of_datum_39_1 ctx hq hK⟩

/-- At `(39,1)` with Q odd the val-0 fibre part is empty (the parity pin consequence). -/
theorem datum_39_1_val0_empty (ctx : ActualFailureContext) (hQodd : ctx.Q % 2 = 1)
    (hq : (class1SlopeDatum ctx).q = 39) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    (olcFibre ctx).filter (fun k => carryVal2 ctx k = 0) = ∅ :=
  olcFibre_val0_filter_eq_empty_of_memberEven ctx hQodd
    (olcFibre_even_of_datum_39_1 ctx hq hK)

/-- **The `(35,2)` double cross**: class-0 survivor AND class-1 datum-closed (empty class-1
fibre).  (NOT band-2-free; not parity-pinned.) -/
theorem datum_35_2_crossDossier (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 35) (hK : (class1SlopeDatum ctx).K₀ = 2) :
    Class0DatumSurvivor ctx ∧ Class1DatumClosed ctx
      ∧ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ := by
  have hclosed : Class1DatumClosed ctx := by simp [Class1DatumClosed, hq, hK]
  exact ⟨by simp [Class0DatumSurvivor, hq, hK], hclosed,
    class1Fibre_empty_of_datumClosed ctx hclosed⟩

/-! ## Part 5.  The graded window-ones field entries (goal 3, wired - additive only)

The zero atom under the VERBATIM envelope-field guards discharges the wave-12 key field,
the wave-13 entry field, the parity-free envelope field, and the Q-odd named target;
the surface combinator splices it into the window-ones entry surface. -/

/-- **The window-ones ZERO field**: under the verbatim guards of the charge capstone's
envelope field (band-2-free datum, spaced `b2 = 1` datum, the small-carry regime,
index-window separation; NO parity hypothesis), the window `(F, F + W)` carries NO raw
ones.  The strongest graded entry: it implies the key-injectivity field, the window-ones
entry field, and the envelope field. -/
def ReturnWindowOnesZeroField : Prop :=
  ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    (∃ k ∈ olcFibre ctx,
      2 ^ carryVal2 ctx k < (supportShell ctx.shell.d ctx.shell.X).card) →
    ¬ ReturnIndexWindowClean ctx →
    (returnWindowOnes ctx).card = 0

/-- Grade 0 => the wave-13 entry field (the atom is free at zero). -/
theorem returnWindowOnesField_of_zeroField (h : ReturnWindowOnesZeroField) :
    ReturnWindowOnesField :=
  fun ctx hA hB hC hD => returnWindowOnesBound_of_zero ctx (h ctx hA hB hC hD)

/-- **Grade 0 => the wave-12 KEY field**: zero window ones force the FULL key injectivity,
so the sharpest predecessor-surface Return demand discharges (the Q-odd hypothesis is
absorbed - the zero harvest is parity-free). -/
theorem returnKeyInjectiveField_of_zeroField (h : ReturnWindowOnesZeroField) :
    ReturnKeyInjectiveField :=
  fun ctx hA hB hC hD _hQ => keyInjOn_of_windowOnes_zero ctx (h ctx hA hB hC hD)

/-- Grade 0 => the parity-free envelope field of the charge capstone. -/
theorem returnDirtyEnvelopeField_of_zeroField (h : ReturnWindowOnesZeroField) :
    ReturnDirtyEnvelopeField :=
  returnDirtyEnvelopeField_of_windowOnesField (returnWindowOnesField_of_zeroField h)

/-- Grade 0 => the Q-odd named target of the case-split rebase. -/
theorem dirtyEnvelopeQOddField_of_zeroField (h : ReturnWindowOnesZeroField) :
    ReturnDirtyEnvelopeQOddField :=
  dirtyEnvelopeQOddField_of_windowOnesField (returnWindowOnesField_of_zeroField h)

/-- **The surface combinator**: splice the zero field into the window-ones entry surface
(the other 12 fields verbatim). -/
def windowOnesResidual_withZeroField (R : Erdos260WindowOnesResidual)
    (h : ReturnWindowOnesZeroField) : Erdos260WindowOnesResidual :=
  { R with returnWindowOnesAtom := returnWindowOnesField_of_zeroField h }

/-- **The graded endpoint**: `Erdos260Statement` from any window-ones surface provider
whose atom is upgraded to the zero field - composition only, nothing re-proved. -/
theorem erdos260_of_windowOnesZeroField (R : Erdos260WindowOnesResidual)
    (h : ReturnWindowOnesZeroField) : Erdos260Statement :=
  erdos260_of_windowOnesResidual (windowOnesResidual_withZeroField R h)

/-! ## Part 6.  Machine-readable status (honest) -/

/-- Honest machine-readable status of the survivor key-count pass. -/
def survivorKeyCountStatus : List String :=
  [ "SUBJECT: per-survivor counting closures for the capstone surfaces " ++
      "(Erdos260ChargeCapstone / Erdos260WindowOnesCapstone) - the envelope field " ++
      "returnDirtyEnvelope (SliceDirtyEnvelope under the wave-8 guards), the window-ones " ++
      "entry atom (ReturnWindowOnesBound), and the non-Return per-survivor fields " ++
      "(class0Survivor/Mid/BigOrder, class1DeepLow/Tail), using the wave-12 parity " ++
      "machinery (ParityResidueClosure) and the wave-13 gap dynamics (DirtySliceEnvelope).",
    "GOAL 1 - PER-DATUM ENVELOPE VERDICTS (honest): (a) the FIFTEEN band-2-free pairs " ++
      "(5,2) (9,1) (9,4) (15,1) (15,2) (17,8) (21,1) (21,3) (21,10) (33,1) (33,16) " ++
      "(41,20) (63,1) (63,3) (63,4) close SliceDirtyEnvelope OUTRIGHT - empty class-4 " ++
      "fibre, envelope vacuous: fifteen per-datum closures sliceDirtyEnvelope_of_datum_* " ++
      "+ dispatcher sliceDirtyEnvelope_of_b2FreeDatum (via returnCtxAllFour_of_b2FreeDatum " ++
      "-> sliceDirtyEnvelope_of_returnZeroBody).  (b) the FIVE unique-band-2 member-EVEN " ++
      "parity pairs (7,3)c2{2} (31,15)c4{4} (39,1)c4{2} (39,6)c6{4} (55,2)c8{2} get the " ++
      "honest lcm form: same-slice members share carryVal2 = v, are 2^v-spaced AND " ++
      "congruent mod c, hence lcm(2^v,c)-spaced - |slice| <= (W + lcm - 1)/lcm " ++
      "(sliceCard_le_of_band2_unique, per-datum sliceCard_le_lcm_of_datum_*), sharpened " ++
      "to min(|windowOnes| + 1, (W + lcm - 1)/lcm) (sliceCard_le_min_of_band2_unique).  " ++
      "NO outright closure there: W ~ c0*X while liftLevelBound X <= L + 1, so the lcm " ++
      "count beats the envelope only under the recorded conditional " ++
      "sliceDirtyEnvelope_of_band2_unique_lcm_small.  (c) (39,19) has residues {6,8} - " ++
      "NOT unique, no c-spacing: only the parity transfer applies.  (d) the parity pins " ++
      "add: at Q odd the val-0 fibre part is EMPTY on all six member-EVEN pairs " ++
      "(olcFibre_val0_empty_of_parityEvenDatum) and every slice member has carryVal2 >= 1 " ++
      "(slice_member_val_pos_of_parityEvenDatum), so the spacing modulus is >= 2.  " ++
      "(e) at (7,3)/(31,15) the in-tree ReturnB2OneSpacedDatum closures already give " ++
      "singletons on the W <= 2 / W <= 4 regimes; the lcm forms here are regime-free.",
    "GOAL 2 - THE B2-FREE AGGREGATE: ReturnLaneFree ctx bundles ALL FIVE Return-lane " ++
      "demands (ReturnGatesBody, ReturnZeroBody, ReturnMaxCleanBody, ReturnInteriorBody, " ++
      "SliceDirtyEnvelope); returnLane_free_of_datumB2Free closes it on every band-2-free " ++
      "datum, with fifteen per-datum instances returnLane_free_of_datum_*.  CROSS TABLE " ++
      "(formalized): class-0 survivors (19 pairs) cross the b2-free list in EXACTLY FIVE " ++
      "pairs (17,8) (21,1) (33,1) (33,16) (41,20) - Class0SurvivorB2FreeCross; " ++
      "class0Survivor_b2_split partitions every survivor into the five crossed pairs " ++
      "(Return lane FREE - returnLane_free_of_class0Cross; joint demand drops to the " ++
      "non-Return fields, e.g. Class0SurvivorResidueMiss) or the fourteen remainder pairs " ++
      "(19,9) (25,2) (25,12) (27,1) (27,4) (27,13) (29,14) (35,2) (37,18) (39,1) (43,21) " ++
      "(45,1) (45,2) (45,4) - Class0SurvivorB2HeavyRest, where the Return demand remains " ++
      "(returnLane_free_or_heavy_of_class0Survivor).  Class-1: the b2-free list crosses " ++
      "Class1DatumClosed in (63,1) (63,3) (63,4) - Class1ClosedB2FreeCross; at these BOTH " ++
      "the Return lane is free AND the class-1 routed fibre is EMPTY " ++
      "(jointFree_of_class1Cross); (33,1) (33,16) have q = 33 in class1ClosedModuli " ++
      "(q33_mem_class1ClosedModuli) so the class1DeepLow guard is void there; class-1 " ++
      "63@10 is NOT b2-free (b2 = 1; it is the member-ODD parity pin).  BONUS CROSSES: " ++
      "(39,1) is class-0 survivor AND class-1 closed AND member-EVEN parity-pinned " ++
      "(datum_39_1_crossDossier, datum_39_1_val0_empty); (35,2) is class-0 survivor AND " ++
      "class-1 closed (datum_35_2_crossDossier).",
    "GOAL 3 - THE WINDOW-ONES GRADING: sliceCard_le_windowOnes_succ holds for EVERY " ++
      "slice, so |windowOnes| = 0 forces ALL slices singleton " ++
      "(allSlices_card_le_one_of_windowOnes_zero) and hence the FULL key injectivity " ++
      "ReturnKeyInjOn (keyInjOn_of_windowOnes_zero) - EVERYTHING on the Return-zero side: " ++
      "ReturnZeroBody (returnZeroBody_of_windowOnes_zero via the parity-free master " ++
      "equivalence) and the envelope (sliceDirtyEnvelope_of_windowOnes_zero).  The graded " ++
      "chain: |windowOnes| = 0 => keyInjOn => everything; ReturnWindowOnesBound " ++
      "(|windowOnes| + 1 <= liftLevelBound X) => envelope (the in-tree " ++
      "sliceDirtyEnvelope_of_windowOnesBound); the atom FORCES |windowOnes| <= L " ++
      "(windowOnes_le_depth_of_bound - necessary only, NOT sufficient, since " ++
      "liftLevelBound X may sit below L + 1).  Regimes characterized: " ++
      "windowOnes_regime_trichotomy / windowOnes_regime_consequence - zero => key " ++
      "injectivity; bounded => envelope; above the bound => NO unconditional consequence " ++
      "(honest: the third branch returns only the defining inequality).  GRADED FIELD " ++
      "WIRING (additive): ReturnWindowOnesZeroField (zero atom under the verbatim " ++
      "envelope-field guards) => returnKeyInjectiveField_of_zeroField (the wave-12 key " ++
      "field, parity absorbed) + returnWindowOnesField_of_zeroField (the wave-13 entry " ++
      "field) + returnDirtyEnvelopeField_of_zeroField + dirtyEnvelopeQOddField_of_" ++
      "zeroField; surface combinator windowOnesResidual_withZeroField + endpoint " ++
      "erdos260_of_windowOnesZeroField.",
    "WHAT RESISTS (honest): the envelope at the fourteen non-b2-free class-0 survivor " ++
      "pairs and at all parity-pinned pairs remains conditional - the lcm count " ++
      "(W + lcm - 1)/lcm does not fit under liftLevelBound X <= L + 1 generically " ++
      "(W ~ c0*X grows, lcm <= 2^v * c is fibre-dependent), and no in-tree fact bounds " ++
      "the raw window ones at the low scale F + W (the wave-13 finding).  The zero-field " ++
      "grade is STRICTLY STRONGER than the window-ones atom (card = 0 vs card + 1 <= " ++
      "liftLevelBound) - no converse claimed anywhere; all implication records here are " ++
      "one-directional.",
    "HYGIENE: additive only - no existing module edited (this module is NOT added to the " ++
      "root import; built standalone as Erdos260.SurvivorKeyCount); no sorry / admit / " ++
      "new axiom / native_decide (decide only on small closed orbit and Finset-literal " ++
      "goals); all #print axioms in [propext, Classical.choice, Quot.sound] or fewer." ]

theorem survivorKeyCountStatus_nonempty : survivorKeyCountStatus ≠ [] := by
  simp [survivorKeyCountStatus]

/-! ## Part 7.  Axiom-cleanliness audit -/

#print axioms allSlices_card_le_one_of_windowOnes_zero
#print axioms keyInjOn_of_slices_le_one
#print axioms keyInjOn_of_windowOnes_zero
#print axioms returnZeroBody_of_windowOnes_zero
#print axioms returnWindowOnesBound_of_zero
#print axioms sliceDirtyEnvelope_of_windowOnes_zero
#print axioms windowOnes_le_depth_of_bound
#print axioms windowOnes_regime_trichotomy
#print axioms windowOnes_regime_consequence
#print axioms sliceCard_le_of_band2_unique
#print axioms sliceCard_le_min_of_band2_unique
#print axioms sliceDirtyEnvelope_of_band2_unique_lcm_small
#print axioms sliceCard_le_lcm_of_datum_7_3
#print axioms sliceCard_le_lcm_of_datum_31_15
#print axioms sliceCard_le_lcm_of_datum_39_1
#print axioms sliceCard_le_lcm_of_datum_39_6
#print axioms sliceCard_le_lcm_of_datum_55_2
#print axioms olcFibre_val0_empty_of_parityEvenDatum
#print axioms slice_member_val_pos_of_parityEvenDatum
#print axioms ReturnLaneFree
#print axioms returnLaneFree_of_ctxAllFour
#print axioms returnLane_free_of_datumB2Free
#print axioms returnLane_free_of_datum_5_2
#print axioms returnLane_free_of_datum_9_1
#print axioms returnLane_free_of_datum_9_4
#print axioms returnLane_free_of_datum_15_1
#print axioms returnLane_free_of_datum_15_2
#print axioms returnLane_free_of_datum_17_8
#print axioms returnLane_free_of_datum_21_1
#print axioms returnLane_free_of_datum_21_3
#print axioms returnLane_free_of_datum_21_10
#print axioms returnLane_free_of_datum_33_1
#print axioms returnLane_free_of_datum_33_16
#print axioms returnLane_free_of_datum_41_20
#print axioms returnLane_free_of_datum_63_1
#print axioms returnLane_free_of_datum_63_3
#print axioms returnLane_free_of_datum_63_4
#print axioms sliceDirtyEnvelope_of_datum_5_2
#print axioms sliceDirtyEnvelope_of_datum_9_1
#print axioms sliceDirtyEnvelope_of_datum_9_4
#print axioms sliceDirtyEnvelope_of_datum_15_1
#print axioms sliceDirtyEnvelope_of_datum_15_2
#print axioms sliceDirtyEnvelope_of_datum_17_8
#print axioms sliceDirtyEnvelope_of_datum_21_1
#print axioms sliceDirtyEnvelope_of_datum_21_3
#print axioms sliceDirtyEnvelope_of_datum_21_10
#print axioms sliceDirtyEnvelope_of_datum_33_1
#print axioms sliceDirtyEnvelope_of_datum_33_16
#print axioms sliceDirtyEnvelope_of_datum_41_20
#print axioms sliceDirtyEnvelope_of_datum_63_1
#print axioms sliceDirtyEnvelope_of_datum_63_3
#print axioms sliceDirtyEnvelope_of_datum_63_4
#print axioms sliceDirtyEnvelope_of_b2FreeDatum
#print axioms Class0SurvivorB2FreeCross
#print axioms Class0SurvivorB2HeavyRest
#print axioms returnB2FreeDatum_of_class0Cross
#print axioms class0Survivor_of_class0Cross
#print axioms returnLane_free_of_class0Cross
#print axioms class0Survivor_b2_split
#print axioms returnLane_free_or_heavy_of_class0Survivor
#print axioms Class1ClosedB2FreeCross
#print axioms class1DatumClosed_of_class1Cross
#print axioms returnB2FreeDatum_of_class1Cross
#print axioms jointFree_of_class1Cross
#print axioms q33_mem_class1ClosedModuli
#print axioms class1ClosedModuli_guard_of_q33
#print axioms datum_39_1_crossDossier
#print axioms datum_39_1_val0_empty
#print axioms datum_35_2_crossDossier
#print axioms ReturnWindowOnesZeroField
#print axioms returnWindowOnesField_of_zeroField
#print axioms returnKeyInjectiveField_of_zeroField
#print axioms returnDirtyEnvelopeField_of_zeroField
#print axioms dirtyEnvelopeQOddField_of_zeroField
#print axioms windowOnesResidual_withZeroField
#print axioms erdos260_of_windowOnesZeroField
#print axioms survivorKeyCountStatus_nonempty

end

end Erdos260
