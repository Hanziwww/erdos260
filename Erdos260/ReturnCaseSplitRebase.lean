import Erdos260.Erdos260KeyCapstone
import Erdos260.ReturnCompleteEnrichCore
import Erdos260.ReturnClass4Closure

/-!
# The Return (Z) case-split rebase — (Z) as a routing predicate, not a global hypothesis
(`ReturnCaseSplitRebase`)

This module (NEW; it edits no existing file) performs the transcription correction identified by
the manuscript remark *"(Z) is a routing predicate, not a global hypothesis"* (the M.2 remark of
`proof_v4_unconditional_clean_v5.tex`, after Lemma M.2.1): in M.2.1 the digit-geometry hypothesis
**(Z)** (no valuation-dropping `1`-digit between consecutive complete-return starts) enters ONLY as
the **membership predicate of the complete-return class** — slices satisfying (Z) are the
ordinary-clean returns counted by the (M.1) envelope; slices violating (Z) contain a genuine dirty
crossing datum and are routed to the dirty package (K.2, M.3–M.4, P4).  The case split is exhaustive
BY DEFINITION and (M.2) needs no digit input.  The wave-1 seed transcription instead demanded the
(Z) zero-runs on the WHOLE routed class-4 fibre (the `returnZero` field), which waves 8–12 carried
down to the current capstone field `returnKeyInjective` (`Erdos260KeyCapstone`).

## The consumption chain (goal 1, mapped end to end)

* The capstone field `returnKeyInjective : ReturnKeyInjectiveField` rebuilds the wave-11 Q-odd
  split field (`returnZeroQOddSplitField_of_keyInjective`), which with `returnZeroQEvenFloor`
  rebuilds the wave-10 `returnZeroTrajectoryFloor` (`returnZeroTrajectoryFloor_of_qOddSplit`),
  carried by the wave-10→9→8→6→5 surfaces as `ReturnZeroBody ctx` under the wave-8 guards
  (`Erdos260ValuationCapstone` → `Erdos260EnumCapstone` → `Erdos260RigidityCapstone` →
  `DigitSideClosure`).
* At the bottom, `ReturnZeroBody` is the `hzero` field of `ReturnClass4DigitResidual` /
  `ReturnSelfRefZResidual` (`ReturnClass4Closure`, `ReturnAnchoredUnconditional`); with the count
  it builds `ReturnAnchoredZResidual` → `ReturnClass4AnchoredCore` → `Class4ReturnPerSliceCharge`
  (`returnZResidualsOfDigitAndCount`, `ReturnAnchoredZResidual.toCharge`), the Return slot of the
  V3 budget (`Erdos260MinimalResidualV3.returnCharge`), delivering the Return capacity floor
  `routedClassMassOf … 4 ≤ c⋆ξX/6`.
* **The exact downstream demand**: `Class4ReturnPerSliceCharge` consumes per slice ONLY the
  M.2.1 datum `OlcSliceData` (level map, shell bound, crossing-freeness, lift-chain congruence) —
  and `OlcSliceData` is PROVED here to be inhabited **iff** the slice obeys the (M.1) envelope
  count `|slice| ≤ liftLevelBound X` (`olcSliceData_nonempty_iff_card_le`, with the new
  constructor `OlcSliceData.ofCardLe`).  The zero-runs are only ever used to MANUFACTURE that
  count; the charge construction does NOT need zero-runs on any slice, clean or dirty.
* **The dirty-slice alternative**: the in-tree dirty-package consumers
  (`DirtyLeafFibreBound` / `dirtyLeafFibreBound_card`, `faithfulFibre_le`,
  `DirtyMultiplicityClosedK25ClassicalBoundInputData`) count their own constructed crossing
  families (`dirtyFamilyOfShell`, `faithfulDirtyFamily`) for the K.2.5 envelope; NO in-tree bridge
  produces an `OlcSliceData` (or a slice-card bound) for an actual `olcSlice` from a dirty
  crossing datum.  The dirty-branch charge therefore enters here at the only honest point: the
  per-slice count itself (`SliceDirtyEnvelope`).

## The case split (goal 2, exhaustive unconditionally)

`SliceZClean` (the (Z) membership predicate on consecutive starts) versus `SliceHasDirtyDatum`
(a consecutive same-slice pair with an intervening `1`-digit, packaged as `SliceDirtyWitness` with
the K.2 data: the anchored `DirtyCrossing` whose length-1 arm is a genuine `1`-run of `ctx.d`, the
broken complete-return arm, and the strict carry deficit `R_z < 2^{z−x} R_x`).  The dichotomy
`sliceCaseSplit` is EXHAUSTIVE for every context, key and slice (near-definitional:
`¬(Z)` exhibits an intervening digit `≠ 0`, hence `= 1` by `BinaryDigits`), and exclusive
(`sliceHasDirtyDatum_iff_not_clean`).  `SliceCaseSplit ctx` is a THEOREM (`sliceCaseSplit_holds`).

## The collapse on the self-referential key (goal 3, the honest verdict)

* **The clean branch is free — at ANY parity.**  On the self-referential key
  `k ↦ (carryVal2 k, k mod 2^{carryVal2 k})` a (Z)-clean slice is a SINGLETON
  (`sliceZClean_card_le_one`, `sliceZClean_iff_card_le_one`): same-key starts share the carry
  valuation, while the zero-run lift identity `carryVal2 (x+h) = carryVal2 x + h`
  (`carryVal2_add_zeroRun`) forces the valuation to GROW across a clean gap — contradiction
  (`caseSplit_selfRefKey_zeroRun_refuted`).  This sharpens the wave-12 Q-odd collapse
  (`returnZeroBody_iff_keyInjOn_of_Q_odd`) to the PARITY-FREE master equivalence
  `returnZeroBody_iff_keyInjOn_uncond`: `ReturnZeroBody ↔ ReturnKeyInjOn` with no parity input —
  the Q-EVEN `returnZero` lane is ALSO pure counting.
* **Consequence for the case split**: at the self-referential key the (M.1)-envelope content of
  the clean branch is exactly the singleton count; ALL remaining Return-zero content lands on the
  dirty branch.  (The manuscript's multi-member clean M.1 counting lives at the anchored
  `(e,τ,P)` keys, where same-slice starts need not share `carryVal2`; the formalized fibre key is
  self-referential, which is why cleanness collapses to singletons there.)
* **The rebased demand** (`SliceDirtyEnvelope`): slices CARRYING A DIRTY DATUM obey the (M.1)
  envelope `|slice| ≤ liftLevelBound X`.  From it the FULL per-slice charge is rebuilt with no
  digit field and no clean-step field (`caseSplitSlices`,
  `Class4ReturnPerSliceCharge.ofDirtyEnvelope`, `ReturnCaseSplitChargeResidual` with
  `toCharge` / `returnFloor` / `perSliceCount`): clean slices are singletons by THEOREM, dirty
  slices by the envelope, and the charge's numeric fields never see a digit.  The dirty-branch
  charge covers EXACTLY the ledger contribution the clean-branch charge would have: both routes
  feed the same `Class4ReturnPerSliceCharge.returnFloor` on the same `routedClassMassOf … 4`.
* **What does NOT close**: `SliceDirtyEnvelope` itself.  The dichotomy makes it the WHOLE
  remaining Return-zero demand, STRICTLY WEAKER in shape than the capstone's
  `ReturnKeyInjOn` (`sliceDirtyEnvelope_of_keyInjOn`; injectivity forbids dirty slices outright,
  the envelope allows up to `liftLevelBound X` members), but it is NOT a theorem: the in-tree
  dirty-package counts bound constructed crossing families, not actual fibre slices, and the
  honest `DirtyWindowCountCore` finding shows the collapsed in-tree dirty model cannot deliver
  absolute-constant fibre counts at all.  So the Return digit lane does NOT vanish; it rebases to
  one counting demand on the (Z)-failing slices — exactly the manuscript's corrected granularity.
* **What DOES close at the surface**: demanded only on dirty-classified slices, the SINGLETON
  count is an equivalent re-presentation of the whole capstone field
  (`dirtySingletonQOddField_iff_keyInjective`, `dirtySingletonQEvenField_iff_qEvenFloor`): the
  clean branch of the demand is a THEOREM (the definitional part the manuscript flags), so the
  successor surface demands NOTHING on (Z)-clean slices — (Z) is consumed purely as the routing
  predicate.  The Q-even lane sheds its last digit-valued (trajectory) shape in the exchange.

## The successor surface (goal 4)

`Erdos260CaseSplitResidual` := the wave-12 key surface with `returnKeyInjective` replaced by
`returnDirtySingletonQOdd : ReturnDirtySingletonQOddField` and `returnZeroQEvenFloor` replaced by
`returnDirtySingletonQEven : ReturnDirtySingletonQEvenField` (both demanded only on slices carrying
a dirty datum; 14 fields verbatim).  Endpoint `erdos260_of_caseSplitResidual` through the PUBLIC
bridges only (rebuild the two key-surface fields, then `erdos260_of_keyResidual`).  Weakening
witness `caseSplitResidual_of_key` and the equivalences `nonempty_caseSplitResidual_iff_key` /
`nonempty_caseSplitResidual_iff_split`.

No `sorry`, no `admit`, no new `axiom`, no `native_decide`; additive only — no existing module is
edited.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 0.  The parity-free clean-pair collapse engine

Same-key (self-referential) starts share the carry valuation; a zero-run between them forces the
valuation to grow by the gap (`carryVal2_add_zeroRun`).  No parity input — this is the lift
identity, not the Q-odd reset law. -/

/-- **The parity-free refutation of a clean same-key pair**: a same-key pair `x < z` of the
self-referential key with a zero-run on `(x, z]` is contradictory at ANY parity of `Q` — the key
pins `carryVal2 x = carryVal2 z` while the zero-run lift identity forces
`carryVal2 z = carryVal2 x + (z − x)`. -/
theorem caseSplit_selfRefKey_zeroRun_refuted (ctx : ActualFailureContext) {x z : ℕ}
    (hkey : returnSelfRefKey ctx x = returnSelfRefKey ctx z) (hxz : x < z)
    (hrun : ∀ j, x < j → j ≤ z → ctx.d j = 0) : False := by
  have hv : carryVal2 ctx x = carryVal2 ctx z :=
    carryVal2_eq_of_returnSelfRefKey_eq ctx hkey
  have hz0 : ∀ j, x < j → j ≤ x + (z - x) → ctx.d j = 0 := by
    intro j h1 h2
    exact hrun j h1 (by omega)
  have hadd := carryVal2_add_zeroRun ctx x (z - x) hz0
  rw [show x + (z - x) = z from by omega] at hadd
  omega

/-- **The PARITY-FREE master equivalence**: `ReturnZeroBody` IS injectivity of the
self-referential key on the class-4 fibre — with no parity hypothesis.  This sharpens the wave-12
Q-odd collapse `returnZeroBody_iff_keyInjOn_of_Q_odd` (whose engine was the Q-odd reset law): the
lift identity alone refutes every clean same-key pair, so the Q-EVEN `returnZero` lane is ALSO
pure counting. -/
theorem returnZeroBody_iff_keyInjOn_uncond (ctx : ActualFailureContext) :
    ReturnZeroBody ctx ↔ ReturnKeyInjOn ctx := by
  constructor
  · intro H x hx z hz hkey
    rcases Nat.lt_trichotomy x z with hlt | heq | hgt
    · exact (caseSplit_selfRefKey_zeroRun_refuted ctx hkey hlt
        (H _ (Finset.mem_image_of_mem _ hx) x (mem_own_slice ctx hx)
          z (mem_slice_of_key_eq ctx hz hkey) hlt)).elim
    · exact heq
    · exact (caseSplit_selfRefKey_zeroRun_refuted ctx hkey.symm hgt
        (H _ (Finset.mem_image_of_mem _ hz) z (mem_own_slice ctx hz)
          x (mem_slice_of_key_eq ctx hx hkey.symm) hgt)).elim
  · intro H y hy x hx z hz hxz j hjx hjz
    have hkey : returnSelfRefKey ctx x = returnSelfRefKey ctx z :=
      (key_eq_of_mem_olcSlice hx).trans (key_eq_of_mem_olcSlice hz).symm
    have := H x (mem_olcFibre_of_mem_olcSlice hx) z (mem_olcFibre_of_mem_olcSlice hz) hkey
    omega

/-! ## Part 1.  The downstream demand, identified exactly

`Class4ReturnPerSliceCharge` consumes per slice only the M.2.1 datum `OlcSliceData`.  Here we pin
that datum to its exact counting content: `OlcSliceData ctx key y` is inhabited **iff**
`|slice| ≤ liftLevelBound X` — the (M.1) envelope.  Forward is the proved `OlcSliceData.card_le`;
backward is the new order-rank tower assignment `OlcSliceData.ofCardLe`. -/

/-- The order-rank tower level of `k` inside a finite set `S`: the `liftLevel` tower evaluated at
the number of strictly smaller members. -/
def caseSplitLevel (S : Finset ℕ) (k : ℕ) : ℕ :=
  liftLevel ((S.filter (· < k)).card)

/-- Below the inverse-tower bound the tower stays below `L` (self-contained `Nat.find` form). -/
theorem caseSplit_liftLevel_le_of_lt_bound {i L : ℕ} (h : i < liftLevelBound L) :
    liftLevel i ≤ L :=
  not_lt.mp (Nat.find_min (liftLevel_unbounded L) h)

/-- The order-rank tower level is strictly monotone on `S`. -/
theorem caseSplitLevel_lt {S : Finset ℕ} {a b : ℕ} (ha : a ∈ S) (hab : a < b) :
    caseSplitLevel S a < caseSplitLevel S b := by
  have hsub : S.filter (· < a) ⊆ S.filter (· < b) := by
    intro c hc
    rw [Finset.mem_filter] at hc ⊢
    exact ⟨hc.1, lt_trans hc.2 hab⟩
  exact liftLevel_strictMono (Finset.card_lt_card
    ((Finset.ssubset_iff_of_subset hsub).mpr
      ⟨a, Finset.mem_filter.mpr ⟨ha, hab⟩, by simp⟩))

/-- Under the envelope count `|S| ≤ liftLevelBound L`, every order-rank tower level fits below
`L`. -/
theorem caseSplitLevel_le {S : Finset ℕ} {L : ℕ} (hcard : S.card ≤ liftLevelBound L)
    {k : ℕ} (hk : k ∈ S) : caseSplitLevel S k ≤ L := by
  apply caseSplit_liftLevel_le_of_lt_bound
  apply lt_of_lt_of_le _ hcard
  exact Finset.card_lt_card
    ((Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).mpr ⟨k, hk, by simp⟩)

/-- On a consecutive pair of `S` the order-rank tower level performs exactly one tower step:
`level a + 2^(level a) ≤ level b` (in fact with equality of ranks `rank b = rank a + 1`). -/
theorem caseSplitLevel_succ_le {S : Finset ℕ} {a b : ℕ} (ha : a ∈ S) (hb : b ∈ S)
    (hab : a < b) (hsucc : ∀ c ∈ S, a < c → b ≤ c) :
    caseSplitLevel S a + 2 ^ caseSplitLevel S a ≤ caseSplitLevel S b := by
  have hins : S.filter (· < b) = insert a (S.filter (· < a)) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hcS, hcb⟩
      rcases Nat.lt_trichotomy c a with h | h | h
      · exact Or.inr ⟨hcS, h⟩
      · exact Or.inl h
      · exact absurd hcb (not_lt.mpr (hsucc c hcS h))
    · rintro (rfl | ⟨hcS, hca⟩)
      · exact ⟨ha, hab⟩
      · exact ⟨hcS, lt_trans hca hab⟩
  unfold caseSplitLevel
  rw [hins, Finset.card_insert_of_notMem (by simp), liftLevel_succ]

/-- **The per-slice M.2.1 datum from the bare envelope count (the new constructor)**: a slice
with at most `liftLevelBound X` members carries an `OlcSliceData` — the order-rank tower
assignment satisfies the shell bound, crossing-freeness, and the consecutive lift-chain step.
Together with the proved `OlcSliceData.card_le` this pins the charge's entire per-slice demand to
the (M.1) envelope count. -/
def OlcSliceData.ofCardLe (ctx : ActualFailureContext) (key : ℕ → ℕ) (y : ℕ)
    (hcard : (olcSlice ctx key y).card ≤ liftLevelBound ctx.shell.X) :
    OlcSliceData ctx key y where
  level := caseSplitLevel ((olcFibre ctx).filter (fun k => key k = y))
  hbound := fun k hk => caseSplitLevel_le hcard hk
  hcf := fun x hx z hz hxz => caseSplitLevel_lt hx hxz
  hcons := fun x hx z hz hxz hsucc => caseSplitLevel_succ_le hx hz hxz hsucc

/-- **The demand identification (goal 1, formal)**: the per-slice M.2.1 datum demanded by
`Class4ReturnPerSliceCharge` is inhabited **iff** the slice obeys the (M.1) envelope count.  The
zero-runs of the (Z) route are only ever used to manufacture this count. -/
theorem olcSliceData_nonempty_iff_card_le (ctx : ActualFailureContext) (key : ℕ → ℕ) (y : ℕ) :
    Nonempty (OlcSliceData ctx key y) ↔
      (olcSlice ctx key y).card ≤ liftLevelBound ctx.shell.X :=
  ⟨fun ⟨S⟩ => S.card_le, fun h => ⟨OlcSliceData.ofCardLe ctx key y h⟩⟩

/-! ## Part 2.  The case-split surface (goal 2)

The (Z) membership predicate per slice, the dirty crossing datum per slice, and the EXHAUSTIVE,
EXCLUSIVE dichotomy — unconditional, for every context, key, and slice. -/

/-- **The (Z) membership predicate of a slice** (the routing predicate of the manuscript M.2
remark): between consecutive slice starts every intervening digit vanishes.  This is exactly the
complete-return class membership: `SliceZClean ↔ SliceCleanReturns ↔ SliceCompleteReturns`. -/
def SliceZClean (ctx : ActualFailureContext) (key : ℕ → ℕ) (y : ℕ) : Prop :=
  ∀ x ∈ olcSlice ctx key y, ∀ z ∈ olcSlice ctx key y, x < z →
    (∀ c ∈ olcSlice ctx key y, x < c → z ≤ c) →
    ∀ j, x < j → j ≤ z → ctx.d j = 0

/-- `SliceZClean` is the wave-17 clean-return slice residual. -/
theorem sliceZClean_iff_cleanReturns (ctx : ActualFailureContext) (key : ℕ → ℕ) (y : ℕ) :
    SliceZClean ctx key y ↔ SliceCleanReturns ctx key y :=
  (sliceCleanReturns_iff_zeroRunConsecutive ctx key y).symm

/-- `SliceZClean` is the wave-18 complete-return placement: (Z)-clean slices ARE the
complete-return class (`CompleteReturnArm` on every consecutive pair). -/
theorem sliceZClean_iff_completeReturns (ctx : ActualFailureContext) (key : ℕ → ℕ) (y : ℕ) :
    SliceZClean ctx key y ↔ SliceCompleteReturns ctx key y :=
  (sliceZClean_iff_cleanReturns ctx key y).trans
    (sliceCompleteReturns_iff_sliceCleanReturns ctx key y).symm

/-- **The dirty crossing datum of a slice**: a consecutive same-slice pair `left < right` with an
intervening `1`-digit at `pos` — the valuation-dropping crossing that breaks the complete return
(manuscript K.2 / M.3–M.4 routing input). -/
structure SliceDirtyWitness (ctx : ActualFailureContext) (key : ℕ → ℕ) (y : ℕ) where
  /-- The left complete-return start. -/
  left : ℕ
  /-- The right (consecutive) complete-return start. -/
  right : ℕ
  /-- The dirty position. -/
  pos : ℕ
  /-- The left start lies on the slice. -/
  left_mem : left ∈ olcSlice ctx key y
  /-- The right start lies on the slice. -/
  right_mem : right ∈ olcSlice ctx key y
  /-- The pair is ordered. -/
  lt : left < right
  /-- The pair is consecutive on the slice. -/
  consecutive : ∀ c ∈ olcSlice ctx key y, left < c → right ≤ c
  /-- The dirty position lies strictly right of the left start. -/
  pos_gt : left < pos
  /-- The dirty position lies at or before the right start. -/
  pos_le : pos ≤ right
  /-- The digit at the dirty position is `1` — the valuation-dropping crossing datum. -/
  hit : ctx.d pos = 1

/-- A slice carries a dirty crossing datum. -/
def SliceHasDirtyDatum (ctx : ActualFailureContext) (key : ℕ → ℕ) (y : ℕ) : Prop :=
  Nonempty (SliceDirtyWitness ctx key y)

namespace SliceDirtyWitness

variable {ctx : ActualFailureContext} {key : ℕ → ℕ} {y : ℕ}

/-- **Teeth**: the dirty datum breaks the complete-return arm of its pair — the witness is a
genuine (Z)-violation, never a relabelling. -/
theorem not_completeReturnArm (W : SliceDirtyWitness ctx key y) :
    ¬ CompleteReturnArm ctx W.left W.right :=
  not_completeReturnArm_of_dirty ctx (le_of_lt W.lt) W.pos_gt W.pos_le W.hit

/-- **The valuation-dropping content, carry-exact**: the dirty datum forces the strict carry
deficit `R_right < 2^(right−left) · R_left` — the carry does NOT return to a clean doubled
state. -/
theorem carry_strict_deficit (W : SliceDirtyWitness ctx key y) :
    carryOf ctx W.right < 2 ^ (W.right - W.left) * carryOf ctx W.left :=
  dirtyBetweenStarts_strict_deficit ctx (le_of_lt W.lt) W.pos_gt W.pos_le W.hit

/-- **The K.2 crossing object of the witness** — the anchored occurrence at the dirty position,
in the exact `DirtyCrossing` shape the dirty-package families are built from
(cf. `dirtyReturnCrossing`): anchor and arm at `pos`, right-oriented, unit charge. -/
def toCrossing (W : SliceDirtyWitness ctx key y) : DirtyCrossing where
  anchor := W.pos
  periodScale := 1
  side := OrientedSide.right
  charge := 1
  arm := { start := W.pos, length := 1 }

/-- The witness crossing's arm is a GENUINE `1`-run of the actual digit word — the anchored
occurrence is real, not declarative. -/
theorem toCrossing_arm_ones (W : SliceDirtyWitness ctx key y) :
    ∀ i, W.toCrossing.arm.start ≤ i →
      i < W.toCrossing.arm.start + W.toCrossing.arm.length → ctx.d i = 1 := by
  intro i h1 h2
  have hi : i = W.pos := by
    change W.pos ≤ i at h1
    change i < W.pos + 1 at h2
    omega
  rw [hi]
  exact W.hit

end SliceDirtyWitness

/-- **THE DICHOTOMY (exhaustive, unconditional — goal 2)**: every slice of every key either
satisfies the (Z) membership predicate or carries a dirty crossing datum.  Near-definitional:
`¬(Z)` exhibits a consecutive pair and an intervening digit `≠ 0`, which `BinaryDigits` pins to
`1`. -/
theorem sliceCaseSplit (ctx : ActualFailureContext) (key : ℕ → ℕ) (y : ℕ) :
    SliceZClean ctx key y ∨ SliceHasDirtyDatum ctx key y := by
  by_cases h : SliceZClean ctx key y
  · exact Or.inl h
  · right
    unfold SliceZClean at h
    push Not at h
    obtain ⟨x, hx, z, hz, hxz, hcons, j, hjx, hjz, hdj⟩ := h
    have hj1 : ctx.d j = 1 := by
      rcases ctx.hd j with h0 | h1
      · exact absurd h0 hdj
      · exact h1
    exact ⟨⟨x, z, j, hx, hz, hxz, hcons, hjx, hjz, hj1⟩⟩

/-- **The dichotomy is exclusive**: a dirty datum is EXACTLY the failure of (Z) — the two
branches partition the slices. -/
theorem sliceHasDirtyDatum_iff_not_clean (ctx : ActualFailureContext) (key : ℕ → ℕ) (y : ℕ) :
    SliceHasDirtyDatum ctx key y ↔ ¬ SliceZClean ctx key y := by
  constructor
  · rintro ⟨W⟩ h
    have h0 := h W.left W.left_mem W.right W.right_mem W.lt W.consecutive
      W.pos W.pos_gt W.pos_le
    have h1 := W.hit
    omega
  · intro h
    rcases sliceCaseSplit ctx key y with hc | hd
    · exact absurd hc h
    · exact hd

/-- **The case-split surface Prop** at the canonical self-referential key: every routed class-4
slice is (Z)-clean or carries a dirty crossing datum. -/
def SliceCaseSplit (ctx : ActualFailureContext) : Prop :=
  ∀ y ∈ (olcFibre ctx).image (returnSelfRefKey ctx),
    SliceZClean ctx (returnSelfRefKey ctx) y ∨
      SliceHasDirtyDatum ctx (returnSelfRefKey ctx) y

/-- **The case split is a THEOREM** — exhaustive by definition, at every context, with no digit
input (the machine-checked counterpart of the manuscript M.2 remark). -/
theorem sliceCaseSplit_holds (ctx : ActualFailureContext) : SliceCaseSplit ctx :=
  fun y _ => sliceCaseSplit ctx (returnSelfRefKey ctx) y

/-! ## Part 3.  The clean branch is free on the self-referential key — at any parity

A (Z)-clean slice of the self-referential key is a singleton: the consecutive-pair extraction
plus the parity-free engine of Part 0. -/

/-- Any ordered pair of a finite set refines to a CONSECUTIVE ordered pair. -/
theorem caseSplit_exists_consecutive_pair {S : Finset ℕ} {x z : ℕ}
    (hx : x ∈ S) (hz : z ∈ S) (hxz : x < z) :
    ∃ a ∈ S, ∃ b ∈ S, a < b ∧ ∀ c ∈ S, a < c → b ≤ c := by
  have hne : (S.filter (fun c => x < c)).Nonempty :=
    ⟨z, Finset.mem_filter.mpr ⟨hz, hxz⟩⟩
  have hmem := Finset.min'_mem _ hne
  rw [Finset.mem_filter] at hmem
  exact ⟨x, hx, (S.filter (fun c => x < c)).min' hne, hmem.1, hmem.2,
    fun c hc hxc => Finset.min'_le _ c (Finset.mem_filter.mpr ⟨hc, hxc⟩)⟩

/-- **The clean branch collapses to singletons (PARITY-FREE)**: a (Z)-clean slice of the
self-referential key has at most one member.  Two members would refine to a consecutive clean
pair, refuted by the lift identity (Part 0). -/
theorem sliceZClean_card_le_one (ctx : ActualFailureContext) (y : ℕ)
    (h : SliceZClean ctx (returnSelfRefKey ctx) y) :
    (olcSlice ctx (returnSelfRefKey ctx) y).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  by_contra hne
  have hpair : ∃ u ∈ olcSlice ctx (returnSelfRefKey ctx) y,
      ∃ v ∈ olcSlice ctx (returnSelfRefKey ctx) y, u < v ∧
        ∀ c ∈ olcSlice ctx (returnSelfRefKey ctx) y, u < c → v ≤ c := by
    rcases Nat.lt_trichotomy a b with hab | hab | hab
    · exact caseSplit_exists_consecutive_pair ha hb hab
    · exact absurd hab hne
    · exact caseSplit_exists_consecutive_pair hb ha hab
  obtain ⟨u, hu, v, hv, huv, hcons⟩ := hpair
  have hkey : returnSelfRefKey ctx u = returnSelfRefKey ctx v :=
    (key_eq_of_mem_olcSlice hu).trans (key_eq_of_mem_olcSlice hv).symm
  exact caseSplit_selfRefKey_zeroRun_refuted ctx hkey huv (h u hu v hv huv hcons)

/-- **The clean branch IS the singleton count**: on the self-referential key, (Z)-cleanness of a
slice is EQUIVALENT to the slice being a singleton — the membership predicate of the
complete-return class carries no digit content beyond the count, at any parity. -/
theorem sliceZClean_iff_card_le_one (ctx : ActualFailureContext) (y : ℕ) :
    SliceZClean ctx (returnSelfRefKey ctx) y ↔
      (olcSlice ctx (returnSelfRefKey ctx) y).card ≤ 1 := by
  constructor
  · exact sliceZClean_card_le_one ctx y
  · intro h x hx z hz hxz hcons j hjx hjz
    have := Finset.card_le_one.mp h x hx z hz
    omega

/-- Key injectivity from the dirty-singleton demand: clean slices are singletons by THEOREM, so
demanding singletons only on dirty-classified slices already forces injectivity. -/
theorem keyInjOn_of_dirtySingletons (ctx : ActualFailureContext)
    (h : ∀ y ∈ (olcFibre ctx).image (returnSelfRefKey ctx),
      SliceHasDirtyDatum ctx (returnSelfRefKey ctx) y →
      (olcSlice ctx (returnSelfRefKey ctx) y).card ≤ 1) :
    ReturnKeyInjOn ctx := by
  intro x hx z hz hkey
  have hy : returnSelfRefKey ctx x ∈ (olcFibre ctx).image (returnSelfRefKey ctx) :=
    Finset.mem_image_of_mem _ hx
  have hxs : x ∈ olcSlice ctx (returnSelfRefKey ctx) (returnSelfRefKey ctx x) :=
    mem_own_slice ctx hx
  have hzs : z ∈ olcSlice ctx (returnSelfRefKey ctx) (returnSelfRefKey ctx x) :=
    mem_slice_of_key_eq ctx hz hkey
  have hcard : (olcSlice ctx (returnSelfRefKey ctx) (returnSelfRefKey ctx x)).card ≤ 1 := by
    rcases sliceCaseSplit ctx (returnSelfRefKey ctx) (returnSelfRefKey ctx x) with hclean | hdirty
    · exact sliceZClean_card_le_one ctx _ hclean
    · exact h _ hy hdirty
  exact Finset.card_le_one.mp hcard x hxs z hzs

/-- The converse weakening: key injectivity makes EVERY slice (dirty ones included) a
singleton. -/
theorem dirtySingletons_of_keyInjOn (ctx : ActualFailureContext)
    (hinj : ReturnKeyInjOn ctx) :
    ∀ y ∈ (olcFibre ctx).image (returnSelfRefKey ctx),
      SliceHasDirtyDatum ctx (returnSelfRefKey ctx) y →
      (olcSlice ctx (returnSelfRefKey ctx) y).card ≤ 1 := by
  intro y _ _
  rw [Finset.card_le_one]
  intro a ha b hb
  exact hinj a (mem_olcFibre_of_mem_olcSlice ha) b (mem_olcFibre_of_mem_olcSlice hb)
    ((key_eq_of_mem_olcSlice ha).trans (key_eq_of_mem_olcSlice hb).symm)

/-! ## Part 4.  The rebased demand and the full per-slice charge rebuild (goal 3)

The (M.1) envelope demanded ONLY on slices carrying a dirty datum suffices for the ENTIRE
downstream Return charge: clean slices are singletons by theorem, the envelope covers the dirty
slices, and `OlcSliceData.ofCardLe` manufactures the per-slice data from the counts alone — no
digit field, no clean-step field, same `returnFloor` on the same routed class-4 mass. -/

/-- **The rebased Return-zero demand**: slices of the self-referential key CARRYING A DIRTY
CROSSING DATUM obey the (M.1) envelope `|slice| ≤ liftLevelBound X`.  This is the dirty-package
count demand at the per-slice granularity — strictly weaker in shape than the capstone's key
injectivity (which forbids dirty slices outright), and the ONLY Return-zero demand the per-slice
charge needs. -/
def SliceDirtyEnvelope (ctx : ActualFailureContext) : Prop :=
  ∀ y ∈ (olcFibre ctx).image (returnSelfRefKey ctx),
    SliceHasDirtyDatum ctx (returnSelfRefKey ctx) y →
    (olcSlice ctx (returnSelfRefKey ctx) y).card ≤ liftLevelBound ctx.shell.X

/-- **The case-split rebuild of the envelope on ALL slices**: clean slices are singletons
(theorem, Part 3), dirty slices are demanded — so every slice obeys the (M.1) envelope. -/
theorem sliceCard_le_envelope_of_dirtyEnvelope (ctx : ActualFailureContext)
    (henv : SliceDirtyEnvelope ctx) :
    ∀ y ∈ (olcFibre ctx).image (returnSelfRefKey ctx),
      (olcSlice ctx (returnSelfRefKey ctx) y).card ≤ liftLevelBound ctx.shell.X := by
  intro y hy
  rcases sliceCaseSplit ctx (returnSelfRefKey ctx) y with hclean | hdirty
  · exact le_trans (sliceZClean_card_le_one ctx y hclean)
      (one_le_liftLevelBound ctx.shell.X)
  · exact henv y hy hdirty

/-- **The full per-slice M.2.1 family from the dirty-side counts alone** — no digit input. -/
def caseSplitSlices (ctx : ActualFailureContext) (henv : SliceDirtyEnvelope ctx) :
    ∀ y ∈ (olcFibre ctx).image (returnSelfRefKey ctx),
      OlcSliceData ctx (returnSelfRefKey ctx) y :=
  fun y hy => OlcSliceData.ofCardLe ctx (returnSelfRefKey ctx) y
    (sliceCard_le_envelope_of_dirtyEnvelope ctx henv y hy)

/-- **The full V3 Return/Class-4 charge from the rebased demand**: dirty-slice envelope counts +
the K.1 interior + the `M_L·X` smallness — the same `Class4ReturnPerSliceCharge` the (Z) route
builds, with the slice data manufactured from the counts (`OlcSliceData.ofCardLe`) instead of
from zero-runs.  The dirty-branch charge lands on EXACTLY the ledger contribution the
clean-branch charge would have: the same `returnFloor` on the same `routedClassMassOf … 4`. -/
def Class4ReturnPerSliceCharge.ofDirtyEnvelope (ctx : ActualFailureContext)
    (henv : SliceDirtyEnvelope ctx)
    (hInterior : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4,
      k + ctx.n24CarryData.r + 1
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card)
    (hnumeric : (((olcFibre ctx).image (returnSelfRefKey ctx)).card : ℝ)
        * (liftLevelBound ctx.shell.X : ℝ) * returnDyadicMult ctx
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    Class4ReturnPerSliceCharge ctx :=
  Class4ReturnPerSliceCharge.ofSlicesWindow ctx (returnSelfRefKey ctx)
    (caseSplitSlices ctx henv)
    (returnWindowReach ctx)
    (returnWindowReach_add_one_le ctx)
    (returnClass4Contain_ofInterior ctx hInterior)
    hnumeric

/-- **The rebased Return/Class-4 residual** — the Z-residual with `hzero` and `hcleanStep`
REPLACED by the dirty-slice envelope (the manuscript-faithful case-split demand): the dirty-side
counts, the K.1 interior, and the `M_L·X` smallness.  No digit-valued field remains. -/
structure ReturnCaseSplitChargeResidual (ctx : ActualFailureContext) where
  /-- The (M.1) envelope on the (Z)-failing slices — the whole rebased Return-zero demand. -/
  dirtyEnvelope : SliceDirtyEnvelope ctx
  /-- The K.1 boundary: class-4 descent windows stay strictly inside the shell window. -/
  class4Interior : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4,
    k + ctx.n24CarryData.r + 1
      < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + (supportShell ctx.shell.d ctx.shell.X).card
  /-- The `M_L·X` smallness at the self-referential key count. -/
  hnumeric : (((olcFibre ctx).image (returnSelfRefKey ctx)).card : ℝ)
      * (liftLevelBound ctx.shell.X : ℝ) * returnDyadicMult ctx
    ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6

namespace ReturnCaseSplitChargeResidual

variable {ctx : ActualFailureContext}

/-- The full V3 charge from the rebased residual. -/
def toCharge (R : ReturnCaseSplitChargeResidual ctx) : Class4ReturnPerSliceCharge ctx :=
  Class4ReturnPerSliceCharge.ofDirtyEnvelope ctx R.dirtyEnvelope R.class4Interior R.hnumeric

/-- The Return capacity floor from the rebased residual — the SAME class-4 ledger contribution
the (Z) route delivers. -/
theorem returnFloor (R : ReturnCaseSplitChargeResidual ctx) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 4
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  R.toCharge.returnFloor

/-- The corrected M.2.1 per-slice count from the rebased residual. -/
theorem perSliceCount (R : ReturnCaseSplitChargeResidual ctx) :
    (olcFibre ctx).card
      ≤ ((olcFibre ctx).image (returnSelfRefKey ctx)).card * liftLevelBound ctx.shell.X :=
  routedFibre4_card_le_of_slices ctx (returnSelfRefKey ctx)
    (caseSplitSlices ctx R.dirtyEnvelope)

/-- **The weakening witness from the Z-residual**: the rebased residual demands strictly less —
`hzero` refutes every dirty datum outright (so the envelope is vacuous), and `hcleanStep` is
DROPPED (the count route never needs it); `class4Interior` and `hnumeric` transport.  No converse
is claimed: the envelope keeps no digit data, so no Z-residual can be rebuilt from it. -/
def ofSelfRefZ (R : ReturnSelfRefZResidual ctx) : ReturnCaseSplitChargeResidual ctx where
  dirtyEnvelope := by
    intro y hy hdirty
    rcases hdirty with ⟨W⟩
    have h0 := R.hzero y hy W.left W.left_mem W.right W.right_mem W.lt
      W.pos W.pos_gt W.pos_le
    have h1 := W.hit
    exact (by omega : False).elim
  class4Interior := R.class4Interior
  hnumeric := R.hnumeric

end ReturnCaseSplitChargeResidual

/-- The envelope from key injectivity (the capstone demand): injectivity makes every slice a
singleton, so the dirty-slice envelope is satisfied with room to spare — the rebased demand is
weaker. -/
theorem sliceDirtyEnvelope_of_keyInjOn (ctx : ActualFailureContext)
    (hinj : ReturnKeyInjOn ctx) : SliceDirtyEnvelope ctx :=
  fun y hy hd =>
    le_trans (dirtySingletons_of_keyInjOn ctx hinj y hy hd)
      (one_le_liftLevelBound ctx.shell.X)

/-- The envelope from the verbatim `returnZero` field body (any parity). -/
theorem sliceDirtyEnvelope_of_returnZeroBody (ctx : ActualFailureContext)
    (H : ReturnZeroBody ctx) : SliceDirtyEnvelope ctx :=
  sliceDirtyEnvelope_of_keyInjOn ctx ((returnZeroBody_iff_keyInjOn_uncond ctx).mp H)

/-- The envelope from a whole-fibre envelope count (slices are subsets of the fibre).  Recorded
for completeness: on deep shells `|olcFibre| ≤ liftLevelBound X` is NOT available (the wave-9/10
global-collapse lesson), so this entry is not a closure route. -/
theorem sliceDirtyEnvelope_of_fibre_card_le (ctx : ActualFailureContext)
    (hsmall : (olcFibre ctx).card ≤ liftLevelBound ctx.shell.X) :
    SliceDirtyEnvelope ctx := by
  intro y _ _
  refine le_trans (Finset.card_le_card ?_) hsmall
  rw [olcSlice_def]
  exact Finset.filter_subset _ _

/-! ## Part 5.  The successor surface fields (goal 4, field level)

The capstone's two `returnZero`-shaped fields, re-presented through the case split: the demand is
stated ONLY on slices carrying a dirty crossing datum — on (Z)-clean slices it is a THEOREM
(Part 3), so (Z) is consumed purely as the routing predicate.  Both exchanges are EQUIVALENCES
(honest: a presentation correction, not a weakening); the genuinely weaker faithful target —
the (M.1) envelope in place of singletons — is recorded alongside as the named gap. -/

/-- **The Q-odd case-split successor field**: under the verbatim wave-8 guards at Q-odd contexts,
slices of the self-referential key carrying a dirty crossing datum are singletons.  Equivalent to
the capstone's `ReturnKeyInjectiveField` — but the demand now touches ONLY the (Z)-failing
slices. -/
def ReturnDirtySingletonQOddField : Prop :=
  ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    (∃ k ∈ olcFibre ctx,
      2 ^ carryVal2 ctx k < (supportShell ctx.shell.d ctx.shell.X).card) →
    ¬ ReturnIndexWindowClean ctx →
    ctx.Q % 2 = 1 →
    ∀ y ∈ (olcFibre ctx).image (returnSelfRefKey ctx),
      SliceHasDirtyDatum ctx (returnSelfRefKey ctx) y →
      (olcSlice ctx (returnSelfRefKey ctx) y).card ≤ 1

/-- **The Q-even case-split successor field**: under the verbatim Q-even floor-field guards,
slices carrying a dirty crossing datum are singletons.  Equivalent to the capstone's
`ReturnZeroQEvenFloorField` (through the PARITY-FREE collapse of Part 0) — the Q-even lane sheds
its last digit-valued (trajectory) shape in the exchange. -/
def ReturnDirtySingletonQEvenField : Prop :=
  ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    (∃ k ∈ olcFibre ctx,
      2 ^ carryVal2 ctx k < (supportShell ctx.shell.d ctx.shell.X).card) →
    ¬ ReturnIndexWindowClean ctx →
    2 ^ ctxDyadicPart ctx < (supportShell ctx.shell.d ctx.shell.X).card →
    ctx.Q % 2 = 0 →
    ∀ y ∈ (olcFibre ctx).image (returnSelfRefKey ctx),
      SliceHasDirtyDatum ctx (returnSelfRefKey ctx) y →
      (olcSlice ctx (returnSelfRefKey ctx) y).card ≤ 1

/-- The Q-odd case-split field rebuilds the capstone counting field. -/
theorem returnKeyInjectiveField_of_dirtySingletonQOdd
    (h : ReturnDirtySingletonQOddField) : ReturnKeyInjectiveField :=
  fun ctx hA hB hC hD hQ => keyInjOn_of_dirtySingletons ctx (h ctx hA hB hC hD hQ)

/-- The converse: the capstone counting field already singles out the dirty slices. -/
theorem dirtySingletonQOddField_of_keyInjective
    (h : ReturnKeyInjectiveField) : ReturnDirtySingletonQOddField :=
  fun ctx hA hB hC hD hQ => dirtySingletons_of_keyInjOn ctx (h ctx hA hB hC hD hQ)

/-- **The Q-odd exchange is an EQUIVALENCE** — a presentation correction: the demand moves to
the (Z)-failing slices, the (Z)-clean branch becomes a theorem, the content is unchanged. -/
theorem dirtySingletonQOddField_iff_keyInjective :
    ReturnDirtySingletonQOddField ↔ ReturnKeyInjectiveField :=
  ⟨returnKeyInjectiveField_of_dirtySingletonQOdd, dirtySingletonQOddField_of_keyInjective⟩

/-- The Q-even case-split field rebuilds the verbatim Q-even dyadic-floor trajectory field:
dirty singletons + the free clean branch give key injectivity, the parity-free master
equivalence gives `ReturnZeroBody`, and the wave-10 equivalence restores the trajectory form. -/
theorem returnZeroQEvenFloorField_of_dirtySingletonQEven
    (h : ReturnDirtySingletonQEvenField) : ReturnZeroQEvenFloorField :=
  fun ctx hA hB hC hD hE hQ =>
    (returnZeroBody_iff_belowBandTrajectory_uncond ctx).mp
      ((returnZeroBody_iff_keyInjOn_uncond ctx).mpr
        (keyInjOn_of_dirtySingletons ctx (h ctx hA hB hC hD hE hQ)))

/-- The converse: the verbatim Q-even floor field already singles out the dirty slices —
through the SAME parity-free collapse (the wave-12 engine never needed the Q-odd reset law for
this direction). -/
theorem dirtySingletonQEvenField_of_qEvenFloor
    (h : ReturnZeroQEvenFloorField) : ReturnDirtySingletonQEvenField :=
  fun ctx hA hB hC hD hE hQ =>
    dirtySingletons_of_keyInjOn ctx
      ((returnZeroBody_iff_keyInjOn_uncond ctx).mp
        ((returnZeroBody_iff_belowBandTrajectory_uncond ctx).mpr
          (h ctx hA hB hC hD hE hQ)))

/-- **The Q-even exchange is an EQUIVALENCE** — the Q-even `returnZero` lane is pure counting,
exactly like the Q-odd lane. -/
theorem dirtySingletonQEvenField_iff_qEvenFloor :
    ReturnDirtySingletonQEvenField ↔ ReturnZeroQEvenFloorField :=
  ⟨returnZeroQEvenFloorField_of_dirtySingletonQEven, dirtySingletonQEvenField_of_qEvenFloor⟩

/-- **The faithful STRICTLY WEAKER target, Q-odd lane (the named gap)**: the (M.1) envelope on
the dirty slices, in place of singletons — the manuscript-corrected demand granularity.  The
singleton field implies it; no converse is claimed (the envelope admits up to
`liftLevelBound X` members per dirty slice, which the current capstone chain cannot consume —
its interface transports `ReturnZeroBody`, which forbids dirty slices outright). -/
def ReturnDirtyEnvelopeQOddField : Prop :=
  ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    (∃ k ∈ olcFibre ctx,
      2 ^ carryVal2 ctx k < (supportShell ctx.shell.d ctx.shell.X).card) →
    ¬ ReturnIndexWindowClean ctx →
    ctx.Q % 2 = 1 →
    SliceDirtyEnvelope ctx

/-- The envelope field is a weakening of the case-split singleton field. -/
theorem dirtyEnvelopeQOddField_of_dirtySingleton
    (h : ReturnDirtySingletonQOddField) : ReturnDirtyEnvelopeQOddField :=
  fun ctx hA hB hC hD hQ y hy hd =>
    le_trans (h ctx hA hB hC hD hQ y hy hd) (one_le_liftLevelBound ctx.shell.X)

/-- The envelope field is a weakening of the capstone counting field. -/
theorem dirtyEnvelopeQOddField_of_keyInjective
    (h : ReturnKeyInjectiveField) : ReturnDirtyEnvelopeQOddField :=
  dirtyEnvelopeQOddField_of_dirtySingleton (dirtySingletonQOddField_of_keyInjective h)

/-! ## Part 6.  The successor surface and the endpoint (goal 4)

`Erdos260CaseSplitResidual` — the wave-12 key surface with both `returnZero`-shaped fields
replaced by the case-split (dirty-singleton) forms; 14 fields verbatim.  Endpoint through PUBLIC
bridges only. -/

/-- **The case-split successor surface**: the wave-12 key surface (`Erdos260KeyResidual`) with
the Q-odd counting field `returnKeyInjective` REPLACED by the case-split form
`ReturnDirtySingletonQOddField` and the Q-even dyadic-floor trajectory field
`returnZeroQEvenFloor` REPLACED by the case-split form `ReturnDirtySingletonQEvenField` — both
demanded ONLY on slices carrying a dirty crossing datum ((Z) consumed purely as the routing
predicate; the clean branch is a theorem).  The other 14 fields are verbatim wave-12 shapes. -/
structure Erdos260CaseSplitResidual where
  /-- Tower / class 2 - enumerated part (`q < 107`), with the free aperiodicity guard. -/
  towerEnumLow : ∀ ctx : ActualFailureContext,
    TowerModulusEnumEscapeV2 ctx → (class1SlopeDatum ctx).q < 107 →
    (ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx) →
    Class2CycleInequality ctx
  /-- Tower / class 2 - tail (`107 ≤ q`), with the free aperiodicity guard. -/
  towerEnumTail : ∀ ctx : ActualFailureContext,
    TowerModulusEnumEscapeV2 ctx →
    107 ≤ (class1SlopeDatum ctx).q →
    (ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx) →
    (((Nat.log 2 (class1SlopeDatum ctx).q + 1) * shellWidth ctx
        < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
            (class1SlopeDatum ctx).K₀)))
        ∧ TowerBand4Budget ctx)
      ∨ Class2CycleInequality ctx
  /-- Run / class 5 - enumerated part (`q < 64`); verbatim field. -/
  runNumericLow : ∀ ctx : ActualFailureContext,
    (class1SlopeDatum ctx).q < 64 →
    Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx
  /-- Run / class 5 - tail (`64 ≤ q`); verbatim field. -/
  runNumericTail : ∀ ctx : ActualFailureContext,
    64 ≤ (class1SlopeDatum ctx).q →
    ((Nat.log 2 (class1SlopeDatum ctx).q + 1)
        * (supportShell ctx.shell.d ctx.shell.X).card
      < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
          (class1SlopeDatum ctx).K₀)))
      ∧ RunBandBudget ctx
    ∨ Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx
  /-- Return / class 4 count gates - verbatim field. -/
  returnGates : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    2 * (129 * shellLadderDepth ctx + 64)
      ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
    ReturnGatesBodyUngated ctx
  /-- Return / class 4 digit Z, Q ODD - **the case-split form**: dirty-classified slices are
  singletons ((Z)-clean slices are singletons by THEOREM — `sliceZClean_card_le_one`). -/
  returnDirtySingletonQOdd : ReturnDirtySingletonQOddField
  /-- Return / class 4 digit Z, Q EVEN - **the case-split form** (replaces the dyadic-floor
  trajectory shape through the parity-free collapse — the lane's last digit-valued shape). -/
  returnDirtySingletonQEven : ReturnDirtySingletonQEvenField
  /-- Return / class 4 clean step, Q ODD - the parity-reduced per-datum form; verbatim field. -/
  returnMaxCleanQOddParityReduced : ReturnMaxCleanQOddParityReducedField
  /-- Return / class 4 clean step, Q EVEN - verbatim field. -/
  returnMaxCleanQEven : ReturnMaxCleanQEvenField
  /-- Return / class 4 K.1 interior - verbatim field. -/
  returnInterior : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx
  /-- Chernoff / class 0 survivors - verbatim field. -/
  class0Survivor : ∀ ctx : ActualFailureContext, Class0DatumSurvivor ctx →
    Class0SurvivorResidueMiss ctx
  /-- Chernoff / class 0 mid band - verbatim field. -/
  class0Mid : ∀ ctx : ActualFailureContext, 48 ≤ (class1SlopeDatum ctx).q →
    (class1SlopeDatum ctx).q < 96 → Class0CycleMeetsShallow ctx →
    Class0WindowCycleCheck ctx
  /-- Chernoff / class 0 large moduli (`96 ≤ q`) - verbatim field. -/
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
  /-- CNL / class 1 - enumerated deep part (`q < 101`), with the free aperiodicity guard. -/
  class1DeepLow : ∀ ctx : ActualFailureContext,
    64 ∣ shellLadderDepth ctx →
    9 ≤ (class1SlopeDatum ctx).q →
    ((class1SlopeDatum ctx).q ≤ 15 ∨ 25 ≤ (class1SlopeDatum ctx).q) →
    (class1SlopeDatum ctx).q ∉ class1ClosedModuli →
    ¬ Class1DatumClosed ctx →
    ¬ Class1GcdWindowMiss ctx →
    (class1SlopeDatum ctx).q < 101 →
    (ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx) →
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅
  /-- CNL / class 1 - tail (`101 ≤ q`); verbatim field. -/
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
  /-- DensePack / class 3 - verbatim field. -/
  densePackUngated : DensePackUngatedClosureResidual

namespace Erdos260CaseSplitResidual

/-- **The bridge into the wave-12 key surface**: both case-split fields rebuild their key-surface
counterparts through the PUBLIC equivalences of Part 5 (the clean branch supplied by the Part 3
singleton theorem); the other 14 fields transfer verbatim. -/
def toKey (R : Erdos260CaseSplitResidual) : Erdos260KeyResidual where
  towerEnumLow := R.towerEnumLow
  towerEnumTail := R.towerEnumTail
  runNumericLow := R.runNumericLow
  runNumericTail := R.runNumericTail
  returnGates := R.returnGates
  returnKeyInjective :=
    returnKeyInjectiveField_of_dirtySingletonQOdd R.returnDirtySingletonQOdd
  returnZeroQEvenFloor :=
    returnZeroQEvenFloorField_of_dirtySingletonQEven R.returnDirtySingletonQEven
  returnMaxCleanQOddParityReduced := R.returnMaxCleanQOddParityReduced
  returnMaxCleanQEven := R.returnMaxCleanQEven
  returnInterior := R.returnInterior
  class0Survivor := R.class0Survivor
  class0Mid := R.class0Mid
  class0BigOrder := R.class0BigOrder
  class1DeepLow := R.class1DeepLow
  class1DeepTail := R.class1DeepTail
  densePackUngated := R.densePackUngated

/-- The final statement from the case-split surface, through the wave-12 chain.  Composition
only; nothing re-proved. -/
theorem toStatement (R : Erdos260CaseSplitResidual) : Erdos260Statement :=
  erdos260_of_keyResidual R.toKey

end Erdos260CaseSplitResidual

/-- **The case-split endpoint**: `Erdos260Statement` from the successor surface — the Return
digit-Z lane demanded only on dirty-classified slices, at both parities. -/
theorem erdos260_of_caseSplitResidual (R : Erdos260CaseSplitResidual) : Erdos260Statement :=
  R.toStatement

/-- **The weakening witness**: any wave-12 key provider yields the case-split surface (both
replaced fields through the converse bridges of Part 5). -/
def caseSplitResidual_of_key (R : Erdos260KeyResidual) : Erdos260CaseSplitResidual where
  towerEnumLow := R.towerEnumLow
  towerEnumTail := R.towerEnumTail
  runNumericLow := R.runNumericLow
  runNumericTail := R.runNumericTail
  returnGates := R.returnGates
  returnDirtySingletonQOdd :=
    dirtySingletonQOddField_of_keyInjective R.returnKeyInjective
  returnDirtySingletonQEven :=
    dirtySingletonQEvenField_of_qEvenFloor R.returnZeroQEvenFloor
  returnMaxCleanQOddParityReduced := R.returnMaxCleanQOddParityReduced
  returnMaxCleanQEven := R.returnMaxCleanQEven
  returnInterior := R.returnInterior
  class0Survivor := R.class0Survivor
  class0Mid := R.class0Mid
  class0BigOrder := R.class0BigOrder
  class1DeepLow := R.class1DeepLow
  class1DeepTail := R.class1DeepTail
  densePackUngated := R.densePackUngated

/-- The case-split surface is equivalent to the wave-12 key surface — an honest presentation
refinement, not a weakening. -/
theorem nonempty_caseSplitResidual_iff_key :
    Nonempty Erdos260CaseSplitResidual ↔ Nonempty Erdos260KeyResidual :=
  ⟨fun ⟨R⟩ => ⟨R.toKey⟩, fun ⟨R⟩ => ⟨caseSplitResidual_of_key R⟩⟩

/-- The case-split surface is equivalent to the wave-11 split surface. -/
theorem nonempty_caseSplitResidual_iff_split :
    Nonempty Erdos260CaseSplitResidual ↔ Nonempty Erdos260SplitResidual :=
  nonempty_caseSplitResidual_iff_key.trans nonempty_keyResidual_iff_split

/-! ## Part 7.  Machine-readable status (honest) -/

/-- Honest machine-readable status of the Return (Z) case-split rebase. -/
def returnCaseSplitRebaseStatus : List String :=
  [ "SUBJECT: the manuscript M.2 remark '(Z) is a routing predicate, not a global hypothesis' " ++
      "(proof_v4_unconditional_clean_v5.tex, after Lemma M.2.1).  (Z) enters M.2.1 only as the " ++
      "membership predicate of the complete-return class; slices violating (Z) carry a " ++
      "valuation-dropping 1-digit (a dirty crossing datum) and are routed to the dirty package " ++
      "(K.2, M.3-M.4, P4).  The case split is exhaustive BY DEFINITION; (M.2) needs no digit " ++
      "input.",
    "CONSUMPTION MAP (goal 1): returnKeyInjective -> returnZeroQOddSplitField_of_keyInjective " ++
      "-> wave-11 split -> wave-10 returnZeroTrajectoryFloor -> ... -> ReturnZeroBody under the " ++
      "wave-8 guards -> hzero of ReturnSelfRefZResidual / ReturnClass4DigitResidual " ++
      "(returnZResidualsOfDigitAndCount) -> ReturnAnchoredZResidual.toCharge -> " ++
      "Class4ReturnPerSliceCharge (the V3 Return slot) -> returnFloor: routedClassMassOf ... 4 " ++
      "<= cStar*xi*X/6.  THE EXACT DOWNSTREAM DEMAND: the charge consumes per slice ONLY " ++
      "OlcSliceData, and OlcSliceData is PROVED equivalent to the (M.1) envelope count " ++
      "|slice| <= liftLevelBound X (olcSliceData_nonempty_iff_card_le via the new constructor " ++
      "OlcSliceData.ofCardLe - the order-rank tower assignment).  Zero-runs are used only to " ++
      "manufacture that count.  DIRTY-SIDE ENTRY POINTS: none exist in-tree for actual slices - " ++
      "the dirty consumers (DirtyLeafFibreBound, dirtyLeafFibreBound_card, faithfulFibre_le, " ++
      "DirtyMultiplicityClosedK25ClassicalBoundInputData) count constructed crossing families " ++
      "(dirtyFamilyOfShell, faithfulDirtyFamily), not olcSlice cards.",
    "THE DICHOTOMY (goal 2, closed): SliceZClean (the (Z) membership predicate, proved " ++
      "equivalent to SliceCleanReturns and SliceCompleteReturns) vs SliceHasDirtyDatum (a " ++
      "consecutive pair with an intervening 1-digit, packaged as SliceDirtyWitness with teeth: " ++
      "not_completeReturnArm, carry_strict_deficit R_z < 2^(z-x)*R_x, and the K.2 crossing " ++
      "object toCrossing whose length-1 arm is a genuine 1-run).  sliceCaseSplit is EXHAUSTIVE " ++
      "unconditionally (every ctx, key, slice; BinaryDigits pins the witness digit to 1); " ++
      "sliceHasDirtyDatum_iff_not_clean makes it exclusive; SliceCaseSplit ctx is a THEOREM " ++
      "(sliceCaseSplit_holds).",
    "THE PARITY-FREE COLLAPSE (new, sharpens wave 12): on the self-referential key a (Z)-clean " ++
      "slice is a SINGLETON at ANY parity (sliceZClean_card_le_one, iff form " ++
      "sliceZClean_iff_card_le_one) - same-key starts share carryVal2 while the zero-run lift " ++
      "identity carryVal2_add_zeroRun forces growth (caseSplit_selfRefKey_zeroRun_refuted; no " ++
      "Q-odd reset law).  Hence the PARITY-FREE master equivalence " ++
      "returnZeroBody_iff_keyInjOn_uncond: ReturnZeroBody <-> ReturnKeyInjOn - the Q-EVEN " ++
      "returnZero lane is ALSO pure counting (the wave-12 collapse needed no parity).",
    "WHAT CLOSED (goal 3): (a) the clean branch of the case split - free at any parity " ++
      "(singletons by theorem); (b) the full per-slice charge REBUILD from the dirty-side " ++
      "counts alone - SliceDirtyEnvelope (the (M.1) envelope demanded ONLY on dirty-classified " ++
      "slices) + class4Interior + hnumeric rebuild Class4ReturnPerSliceCharge with NO digit " ++
      "field and NO clean-step field (caseSplitSlices, " ++
      "Class4ReturnPerSliceCharge.ofDirtyEnvelope, ReturnCaseSplitChargeResidual.toCharge / " ++
      "returnFloor / perSliceCount; weakening witness ofSelfRefZ - hzero and hcleanStep both " ++
      "DROPPED); the dirty-branch charge covers EXACTLY the ledger contribution the " ++
      "clean-branch charge would have (same returnFloor on the same routedClassMassOf ... 4); " ++
      "(c) the surface exchange - both returnZero-shaped capstone fields re-presented as " ++
      "case-split fields demanded only on dirty slices, as EQUIVALENCES " ++
      "(dirtySingletonQOddField_iff_keyInjective, dirtySingletonQEvenField_iff_qEvenFloor - " ++
      "the Q-even lane sheds its last digit-valued trajectory shape).",
    "WHAT DID NOT CLOSE (honest): SliceDirtyEnvelope itself.  The case split reduces the whole " ++
      "Return-zero demand to ONE counting statement - dirty-classified slices obey the (M.1) " ++
      "envelope - which is STRICTLY WEAKER in shape than the capstone demand " ++
      "(sliceDirtyEnvelope_of_keyInjOn; injectivity forbids dirty slices outright, the envelope " ++
      "allows liftLevelBound X members), but it is NOT a theorem: no in-tree dirty-package " ++
      "count controls actual olcSlice cards (the DirtyWindowCountCore finding shows the " ++
      "collapsed in-tree dirty model cannot deliver absolute-constant fibre counts at all), " ++
      "and no charging bridge maps slice members into a counted crossing family.  The Return " ++
      "digit lane therefore does not vanish; it REBASES to the dirty-side count at the " ++
      "manuscript's corrected granularity (named weaker target: ReturnDirtyEnvelopeQOddField).",
    "WHY THE SUCCESSOR SURFACE KEEPS SINGLETONS, NOT THE ENVELOPE: the wave-12..1 composition " ++
      "transports the Return field as ReturnZeroBody (hzero), which forbids dirty slices " ++
      "outright; a strictly weaker envelope field cannot pass through that interface.  The " ++
      "envelope enters the proof only at the charge level (ReturnCaseSplitChargeResidual -> " ++
      "the V3 Return slot), where this module wires it; re-basing the WHOLE chain onto the " ++
      "charge-level interface is the named follow-up, not attempted here (it would replace the " ++
      "surfaces of waves 8-12, not add to them).",
    "SUCCESSOR SURFACE (goal 4): Erdos260CaseSplitResidual = the wave-12 key surface with " ++
      "returnKeyInjective REPLACED by ReturnDirtySingletonQOddField and returnZeroQEvenFloor " ++
      "REPLACED by ReturnDirtySingletonQEvenField (both demanded only on slices with a dirty " ++
      "crossing datum; 14 fields verbatim).  Endpoint erdos260_of_caseSplitResidual via toKey " ++
      "and erdos260_of_keyResidual (PUBLIC bridges only).  Witnesses: caseSplitResidual_of_key; " ++
      "equivalences nonempty_caseSplitResidual_iff_key / nonempty_caseSplitResidual_iff_split.",
    "HYGIENE: additive only - no existing module edited; no sorry / admit / new axiom / " ++
      "native_decide; all #print axioms in [propext, Classical.choice, Quot.sound] or fewer." ]

theorem returnCaseSplitRebaseStatus_nonempty : returnCaseSplitRebaseStatus ≠ [] := by
  simp [returnCaseSplitRebaseStatus]

/-! ## Part 8.  Axiom-cleanliness audit -/

#print axioms caseSplit_selfRefKey_zeroRun_refuted
#print axioms returnZeroBody_iff_keyInjOn_uncond
#print axioms caseSplit_liftLevel_le_of_lt_bound
#print axioms caseSplitLevel_lt
#print axioms caseSplitLevel_le
#print axioms caseSplitLevel_succ_le
#print axioms OlcSliceData.ofCardLe
#print axioms olcSliceData_nonempty_iff_card_le
#print axioms sliceZClean_iff_cleanReturns
#print axioms sliceZClean_iff_completeReturns
#print axioms SliceDirtyWitness.not_completeReturnArm
#print axioms SliceDirtyWitness.carry_strict_deficit
#print axioms SliceDirtyWitness.toCrossing
#print axioms SliceDirtyWitness.toCrossing_arm_ones
#print axioms sliceCaseSplit
#print axioms sliceHasDirtyDatum_iff_not_clean
#print axioms sliceCaseSplit_holds
#print axioms caseSplit_exists_consecutive_pair
#print axioms sliceZClean_card_le_one
#print axioms sliceZClean_iff_card_le_one
#print axioms keyInjOn_of_dirtySingletons
#print axioms dirtySingletons_of_keyInjOn
#print axioms sliceCard_le_envelope_of_dirtyEnvelope
#print axioms caseSplitSlices
#print axioms Class4ReturnPerSliceCharge.ofDirtyEnvelope
#print axioms ReturnCaseSplitChargeResidual.toCharge
#print axioms ReturnCaseSplitChargeResidual.returnFloor
#print axioms ReturnCaseSplitChargeResidual.perSliceCount
#print axioms ReturnCaseSplitChargeResidual.ofSelfRefZ
#print axioms sliceDirtyEnvelope_of_keyInjOn
#print axioms sliceDirtyEnvelope_of_returnZeroBody
#print axioms sliceDirtyEnvelope_of_fibre_card_le
#print axioms returnKeyInjectiveField_of_dirtySingletonQOdd
#print axioms dirtySingletonQOddField_of_keyInjective
#print axioms dirtySingletonQOddField_iff_keyInjective
#print axioms returnZeroQEvenFloorField_of_dirtySingletonQEven
#print axioms dirtySingletonQEvenField_of_qEvenFloor
#print axioms dirtySingletonQEvenField_iff_qEvenFloor
#print axioms dirtyEnvelopeQOddField_of_dirtySingleton
#print axioms dirtyEnvelopeQOddField_of_keyInjective
#print axioms Erdos260CaseSplitResidual.toKey
#print axioms Erdos260CaseSplitResidual.toStatement
#print axioms erdos260_of_caseSplitResidual
#print axioms caseSplitResidual_of_key
#print axioms nonempty_caseSplitResidual_iff_key
#print axioms nonempty_caseSplitResidual_iff_split
#print axioms returnCaseSplitRebaseStatus_nonempty

end

end Erdos260
