import Erdos260.ReturnStartPlacementCore

/-!
# The existence of the anchored complete-return geometry for the actual carries (`ReturnM31ExistenceCore`)

This module (NEW; it edits no existing file) attacks the **lone irreducible remainder** left by
wave-19 (`ReturnStartPlacementCore`): the **existence**, for the genuine `ActualFailureContext` on an
anchored slice, of the M.3.1/M.3.2 anchored complete-return geometry
(`AnchoredCompleteReturnGeometry` / `AnchoredCoreCover` / `AnchoredPatchFamily`).  Wave-19 *derived*
the start placement from that geometry (`zeroRun_of_anchoredGeometry`,
`sliceCompleteReturns_of_anchoredGeometry`); what was left open was producing the geometry for the
actual carries — exhibiting, for each class-4 complete-return start, the anchored semiperiodic patch +
clean-maximal arm reaching the shared anchored core.

## Audit of the M.3.1 / M.4 machinery (`AppendixM`)

* **M.3.1** (`theoremM3_1_anchoredSemiperiodicOverlap`) supplies the *overlap card bound* **given** two
  surviving anchored patches `AnchoredSemiperiodicPatch datum w pᵢ`; it does **not** by itself supply
  their existence.  A patch's only nontrivial field is `corePlacement_input`
  (`IntervalBlock.Contains patch.block datum.core`) together with `valid` (`patch.Valid w`, i.e.
  `PeriodicOn w …`).
* **M.4** (`lemmaM4_1_semiperiodicPrefixExtension`) is the *semiperiodic-prefix dichotomy* at a clean
  failure boundary; it does not assert that a particular surviving patch exists for the actual carries.

**Verdict.**  On a *complete-return arm* the actual digit word `ctx.d` is **constantly `0`** (the
clean-maximal arm of M.1.1), so the M.4 periodicity field `valid` is *automatic*
(`PeriodicOn.of_constant`: a constant word is periodic with any period).  Hence the patch existence
for the actual carries **collapses to the clean-run** — the all-zeros block reaching the shared
anchored core — and is *not* a separate residual.  The genuine irreducible remainder is exactly the
**clean run reaching a common anchor**, i.e. that `ctx.d` has no carry-dropping `1`-digit between a
slice start and a shared anchor, which the carry recurrence `R_{N+1}=2R_N−Q(N+1)d_{N+1}` cannot decide.

## What this module DERIVES (new content)

* `AnchoredCleanRun` — the genuine geometric input on the actual carries: a fixed anchor `a`, a
  positive core length, every slice start strictly before `a`, and `ctx.d` vanishing on the shared
  interior `(x, a + coreLen)` above each start.  This is the all-zeros surviving region of a
  complete-return arm reaching the anchored core.
* `AnchoredPatchFamily.ofAnchoredCleanRun` — **the genuine M.3.1 patch family for the ACTUAL carries**:
  the ambient word is the actual digit word `w := ctx.d` (not a fake constant word), each start's
  patch is the shared anchored core, and the M.4 periodicity field `valid` is *proved from the
  constancy of `ctx.d` on the clean run* (`PeriodicOn.of_constant`).  Through wave-19's
  `AnchoredCoreCover.ofPatchFamily` / `…ofCoreCover` this yields the geometry, `SliceCompleteReturns`,
  and the whole `(Z)` downstream; `patchFamily_anchoredOverlap` exhibits the genuine M.3.1 overlap
  bound, so the data is never vacuous.
* `anchoredGeometry_nonempty_iff_zeroRunToAnchor`, `anchoredGeometry_nonempty_iff_sliceCompleteReturns`
  — **the sharp characterization**: the existence of the anchored geometry is *equivalent* to the
  zero-run-to-a-common-anchor digit condition, and *equivalent* to the wave-18 residual
  `SliceCompleteReturns`.  So wave-19's geometry is a faithful repackaging — neither stronger nor
  weaker — of "no carry-dropping `1`-digit between starts in the shared anchored region", isolating
  the irreducible geometric core to a single elementary digit-word property.

## Teeth / non-vacuity

`anchoredCleanRun_excludes_dirty` (a `1`-digit on the clean run is impossible),
`anchoredCleanRun_overlap_card` (two starts' patches genuinely overlap on `≥ coreLen > 0` points —
the M.3.1 displayed inequality), `anchoredCleanRun_carry_strictMono` (the carry valuation strictly
climbs).  With the actual word `w := ctx.d`, the patch family is realized by the genuine carries, not
a degenerate constant stand-in.

## The smallest honest residual (sharply characterized)

After this module the anchored-geometry **existence** is reduced to — and *proved equivalent to* — the
zero-run-to-anchor condition `∃ a, (∀ x ∈ slice, x ≤ a) ∧ (∀ x ∈ slice, ∀ j, x < j → j ≤ a →
ctx.d j = 0)`, i.e. the wave-18 `SliceCompleteReturns` / "no `1`-digit between starts in the shared
anchored region".  This is the M.3.1 four-coordinate anchored overlap + M.3.2 endpoint-pinning
geometry of the actual carries (`proof_v4_unconditional_clean_v5.tex` §M.3, lines ~6081–6205); the
carry recurrence cannot decide it (a `1`-digit is a genuine strict carry deficit, so the datum is
non-vacuous).  No `sorry`, `axiom`, `admit`, or `native_decide`; no degenerate shortcut.
-/

namespace Erdos260

open Finset

set_option linter.unusedVariables false

noncomputable section

/-! ## 1.  The anchored clean-run datum (the genuine geometric input on the actual carries)

On a complete-return arm the digit word `ctx.d` is constantly `0`.  The genuine geometric content of
the M.3.1 anchored overlap for the *actual* carries is therefore captured by: a fixed anchor `a`, a
positive-length core block `[a, a + coreLen)` strictly above every slice start, with `ctx.d` vanishing
on the shared interior above each start.  This is the all-zeros surviving region every complete-return
arm reaches (the common anchored core). -/

/-- **The anchored clean-run datum.**  A common anchor `anchor` with a positive core length, every
slice start strictly below the anchor, and the actual digit word `ctx.d` vanishing on the shared
interior `(x, anchor + coreLen)` above each start.  This is the genuine geometric input of M.3.1 /
M.3.2 read on the actual carries: the clean-maximal complete-return arm of every start reaches the
shared anchored core `[anchor, anchor + coreLen)`, on which `ctx.d` is constantly `0`. -/
structure AnchoredCleanRun (ctx : ActualFailureContext) (key : ℕ → ℕ) (y : ℕ) where
  /-- the common anchored core coordinate (the M.3.1 one-sided core start). -/
  anchor : ℕ
  /-- the length of the shared anchored core. -/
  coreLen : ℕ
  /-- the anchored core is non-degenerate. -/
  coreLen_pos : 0 < coreLen
  /-- **M.3.1 / M.3.2 orientation.**  Every slice start lies strictly before the anchor (the core is
  in the common interior the arms reach into). -/
  start_lt : ∀ x ∈ olcSlice ctx key y, x < anchor
  /-- **M.1.1 clean-maximal arm.**  `ctx.d` vanishes on the shared interior `(x, anchor + coreLen)`
  above each start: every arm runs cleanly up to and through the anchored core. -/
  clean : ∀ x ∈ olcSlice ctx key y, ∀ j, x < j → j < anchor + coreLen → ctx.d j = 0

/-! ## 2.  The genuine M.3.1 patch family for the ACTUAL carries

We build the wave-19 `AnchoredPatchFamily` from an `AnchoredCleanRun` using the **actual digit word**
`w := ctx.d`.  The single M.4 periodicity field `valid` is *proved* from the constancy of `ctx.d` on
the clean run — the patch is the shared anchored core, an all-zeros block, hence periodic with period
`1` (`PeriodicOn.of_constant`).  Through wave-19's `ofPatchFamily` / `ofCoreCover` this yields the
geometry and `SliceCompleteReturns`. -/

/-- **The genuine M.3.1 anchored patch family from the clean run (the actual carries).**  The ambient
word is the *actual* digit word `ctx.d`; the fixed anchored datum has core `[anchor, anchor + coreLen)`
and `lowerBound = coreLen`; each start's patch is that core and each arm is `[x, anchor + coreLen)`.
The patch validity `valid` is proved from `ctx.d` being constantly `0` on the core (it sits inside the
clean run), so the family is realized by the genuine carries — no fake constant word. -/
def AnchoredPatchFamily.ofAnchoredCleanRun {ctx : ActualFailureContext} {key : ℕ → ℕ} {y : ℕ}
    (R : AnchoredCleanRun ctx key y) : AnchoredPatchFamily ctx key y where
  datum :=
    { anchor := R.anchor
      side := OrientedSide.left
      copy := 0
      marginClass := 0
      core := ⟨R.anchor, R.coreLen⟩
      lowerBound := R.coreLen
      core_len_lower := le_refl _ }
  w := ctx.d
  patch := fun _ => ⟨⟨R.anchor, R.coreLen⟩, 1⟩
  armBlock := fun x => ⟨x, (R.anchor + R.coreLen) - x⟩
  datum_pos := R.coreLen_pos
  arm_start := fun x _ => rfl
  clean_arm := by
    intro x hx j hj1 hj2
    have hxa : x < R.anchor := R.start_lt x hx
    simp only [IntervalBlock.stop] at hj2
    exact R.clean x hx j hj1 (by omega)
  anchored_patch := by
    intro x hx
    have hxa : x < R.anchor := R.start_lt x hx
    refine ⟨?_, IntervalBlock.contains_self _⟩
    show PeriodicOn ctx.d R.anchor R.coreLen 1
    refine PeriodicOn.of_constant (c := 0) Nat.one_pos ?_
    intro i hi
    exact R.clean x hx (R.anchor + i) (by omega) (by omega)
  arm_contains_patch := by
    intro x hx
    have hxa : x < R.anchor := R.start_lt x hx
    simp only [IntervalBlock.Contains, IntervalBlock.stop]
    omega

/-- **Start placement from the clean run (PROVED).**  The genuine patch family forces the wave-18
slice residual `SliceCompleteReturns` through wave-19's `sliceCompleteReturns_of_patchFamily`. -/
theorem sliceCompleteReturns_of_anchoredCleanRun {ctx : ActualFailureContext} {key : ℕ → ℕ} {y : ℕ}
    (R : AnchoredCleanRun ctx key y) : SliceCompleteReturns ctx key y :=
  sliceCompleteReturns_of_patchFamily (AnchoredPatchFamily.ofAnchoredCleanRun R)

/-- **The anchored complete-return geometry from the clean run (PROVED).** -/
def AnchoredCompleteReturnGeometry.ofAnchoredCleanRun {ctx : ActualFailureContext} {key : ℕ → ℕ}
    {y : ℕ} (R : AnchoredCleanRun ctx key y) : AnchoredCompleteReturnGeometry ctx key y :=
  AnchoredCompleteReturnGeometry.ofCoreCover
    (AnchoredCoreCover.ofPatchFamily (AnchoredPatchFamily.ofAnchoredCleanRun R))

/-- **The geometry is inhabited from the clean run (PROVED).** -/
theorem anchoredGeometry_nonempty_of_anchoredCleanRun {ctx : ActualFailureContext} {key : ℕ → ℕ}
    {y : ℕ} (R : AnchoredCleanRun ctx key y) :
    Nonempty (AnchoredCompleteReturnGeometry ctx key y) :=
  ⟨AnchoredCompleteReturnGeometry.ofAnchoredCleanRun R⟩

/-! ## 3.  The sharp characterization of the anchored-geometry existence

The existence of the anchored geometry is pinned to a single elementary digit-word property — a
zero-run reaching a common anchor — which is *equivalent* to the wave-18 residual
`SliceCompleteReturns`.  This shows wave-19's geometry is a faithful repackaging of "no
carry-dropping `1`-digit between starts in the shared anchored region", neither stronger nor weaker. -/

/-- **The geometry from a zero-run reaching a common anchor (PROVED).**  Given a single anchor `a`
at-or-above every slice start with `ctx.d` vanishing on `(x, a]` from every start `x`, take every
arm end to be `a`. -/
def AnchoredCompleteReturnGeometry.ofZeroRunToAnchor {ctx : ActualFailureContext} {key : ℕ → ℕ}
    {y : ℕ} (a : ℕ) (hstart : ∀ x ∈ olcSlice ctx key y, x ≤ a)
    (hclean : ∀ x ∈ olcSlice ctx key y, ∀ j, x < j → j ≤ a → ctx.d j = 0) :
    AnchoredCompleteReturnGeometry ctx key y where
  armEnd := fun _ => a
  anchor := a
  clean_arm := hclean
  start_le_anchor := hstart
  anchor_le_armEnd := fun _ _ => le_refl a

/-- **The geometry from the wave-18 residual (PROVED).**  `SliceCompleteReturns` builds the anchored
geometry: take the common anchor to be the maximal slice start; `zeroRunAllPairs_of_completeReturns`
then makes every arm clean up to it. -/
def AnchoredCompleteReturnGeometry.ofSliceCompleteReturns {ctx : ActualFailureContext} {key : ℕ → ℕ}
    {y : ℕ} (H : SliceCompleteReturns ctx key y) : AnchoredCompleteReturnGeometry ctx key y := by
  by_cases hne : (olcSlice ctx key y).Nonempty
  · refine AnchoredCompleteReturnGeometry.ofZeroRunToAnchor ((olcSlice ctx key y).max' hne)
      (fun x hx => Finset.le_max' _ x hx) ?_
    intro x hx j hj1 hj2
    have hxlt : x < (olcSlice ctx key y).max' hne := lt_of_lt_of_le hj1 hj2
    exact zeroRunAllPairs_of_completeReturns ctx key y H x hx
      ((olcSlice ctx key y).max' hne) ((olcSlice ctx key y).max'_mem hne) hxlt j hj1 hj2
  · refine AnchoredCompleteReturnGeometry.ofZeroRunToAnchor 0 ?_ ?_
    · exact fun x hx => (hne ⟨x, hx⟩).elim
    · exact fun x hx => (hne ⟨x, hx⟩).elim

/-- **The anchored-geometry existence is exactly the zero-run-to-anchor condition (PROVED).** -/
theorem anchoredGeometry_nonempty_iff_zeroRunToAnchor (ctx : ActualFailureContext) (key : ℕ → ℕ)
    (y : ℕ) :
    Nonempty (AnchoredCompleteReturnGeometry ctx key y) ↔
      ∃ a, (∀ x ∈ olcSlice ctx key y, x ≤ a) ∧
        (∀ x ∈ olcSlice ctx key y, ∀ j, x < j → j ≤ a → ctx.d j = 0) := by
  constructor
  · rintro ⟨G⟩
    exact ⟨G.anchor, G.start_le_anchor,
      fun x hx j hj1 hj2 => G.clean_arm x hx j hj1 (le_trans hj2 (G.anchor_le_armEnd x hx))⟩
  · rintro ⟨a, hstart, hclean⟩
    exact ⟨AnchoredCompleteReturnGeometry.ofZeroRunToAnchor a hstart hclean⟩

/-- **The anchored-geometry existence is exactly the wave-18 residual (PROVED).**  The genuine verdict:
the M.3.1/M.3.2 anchored geometry exists for the actual carries on a slice *iff* the wave-18
`SliceCompleteReturns` holds.  So the geometry's existence is a faithful repackaging of "no
carry-dropping `1`-digit between starts", neither stronger nor weaker. -/
theorem anchoredGeometry_nonempty_iff_sliceCompleteReturns (ctx : ActualFailureContext)
    (key : ℕ → ℕ) (y : ℕ) :
    Nonempty (AnchoredCompleteReturnGeometry ctx key y) ↔ SliceCompleteReturns ctx key y :=
  ⟨fun ⟨G⟩ => sliceCompleteReturns_of_anchoredGeometry G,
    fun H => ⟨AnchoredCompleteReturnGeometry.ofSliceCompleteReturns H⟩⟩

/-- **The clean run is exactly the existence of the geometry (PROVED).**  Composing the two
characterizations: a sufficient clean-run datum gives the geometry, and the geometry's existence is the
zero-run-to-anchor condition. -/
theorem zeroRunToAnchor_of_anchoredCleanRun {ctx : ActualFailureContext} {key : ℕ → ℕ} {y : ℕ}
    (R : AnchoredCleanRun ctx key y) :
    ∃ a, (∀ x ∈ olcSlice ctx key y, x ≤ a) ∧
      (∀ x ∈ olcSlice ctx key y, ∀ j, x < j → j ≤ a → ctx.d j = 0) :=
  (anchoredGeometry_nonempty_iff_zeroRunToAnchor ctx key y).1
    (anchoredGeometry_nonempty_of_anchoredCleanRun R)

/-! ## 4.  Teeth and non-vacuity

The clean-run datum genuinely constrains the actual carries; the patch family it builds uses the real
digit word and exhibits the M.3.1 overlap bound; the carry valuation strictly climbs.  So the
existence is a genuine geometric fact, never a vacuous restatement. -/

/-- **A dirty digit refutes the clean run (PROVED).**  A `1`-digit on the shared interior above a
slice start is impossible — the clean run forces it to be `0`. -/
theorem anchoredCleanRun_excludes_dirty {ctx : ActualFailureContext} {key : ℕ → ℕ} {y : ℕ}
    (R : AnchoredCleanRun ctx key y) {x j : ℕ} (hx : x ∈ olcSlice ctx key y)
    (hj1 : x < j) (hj2 : j < R.anchor + R.coreLen) (hdirty : ctx.d j = 1) : False := by
  have h0 := R.clean x hx j hj1 hj2
  omega

/-- **The genuine M.3.1 overlap bound for the clean-run patch family (PROVED).**  Any two slice
starts' patches overlap on at least `coreLen` points (`theoremM3_1_anchoredSemiperiodicOverlap`) — the
displayed inequality (M.3), so the anchored core is genuinely shared and the family is non-vacuous. -/
theorem anchoredCleanRun_overlap_card {ctx : ActualFailureContext} {key : ℕ → ℕ} {y : ℕ}
    (R : AnchoredCleanRun ctx key y) {x z : ℕ}
    (hx : x ∈ olcSlice ctx key y) (hz : z ∈ olcSlice ctx key y) :
    R.coreLen ≤ (((AnchoredPatchFamily.ofAnchoredCleanRun R).patch x).block.points ∩
        ((AnchoredPatchFamily.ofAnchoredCleanRun R).patch z).block.points).card :=
  patchFamily_anchoredOverlap (AnchoredPatchFamily.ofAnchoredCleanRun R) hx hz

/-- **The carry valuation strictly climbs on every pair (PROVED).**  On a clean-run anchored slice the
lift level `carryVal2` strictly increases — the placement is genuine, never a constant stand-in. -/
theorem anchoredCleanRun_carry_strictMono {ctx : ActualFailureContext} {key : ℕ → ℕ} {y : ℕ}
    (R : AnchoredCleanRun ctx key y) {x z : ℕ}
    (hx : x ∈ olcSlice ctx key y) (hz : z ∈ olcSlice ctx key y) (hxz : x < z) :
    carryVal2 ctx x < carryVal2 ctx z :=
  anchoredGeometry_carry_strictMono (AnchoredCompleteReturnGeometry.ofAnchoredCleanRun R) hx hz hxz

/-- **The actual word powers the family (PROVED).**  The ambient word of the clean-run patch family is
the *actual* digit word `ctx.d`, not a fake constant — the M.3.1 surviving-patch structure is realized
by the genuine carries. -/
theorem anchoredCleanRun_w_eq_actual {ctx : ActualFailureContext} {key : ℕ → ℕ} {y : ℕ}
    (R : AnchoredCleanRun ctx key y) :
    (AnchoredPatchFamily.ofAnchoredCleanRun R).w = ctx.d := rfl

/-! ## 5.  Honest residual inventory -/

/-- The precise status of the anchored complete-return geometry **existence** after this module. -/
def returnM31ExistenceResiduals : List String :=
  [ "GOAL (wave-20) — construct, for the genuine ActualFailureContext on an anchored slice, the " ++
      "M.3.1/M.3.2 anchored complete-return geometry (AnchoredCompleteReturnGeometry / " ++
      "AnchoredCoreCover / AnchoredPatchFamily) whose existence is the lone wave-19 residual: each " ++
      "class-4 complete-return start carries a clean-maximal arm reaching a shared anchored core (an " ++
      "AnchoredSemiperiodicPatch of the fixed anchored datum, with the M.3.1 overlap). " ++
      "proof_v4_unconditional_clean_v5.tex §M.3 (lines ~6081-6205).",
    "AUDIT (M.3.1 / M.4) — theoremM3_1_anchoredSemiperiodicOverlap supplies the overlap card bound " ++
      "GIVEN two surviving anchored patches; it does not supply their existence. The only nontrivial " ++
      "patch fields are corePlacement_input (core inside patch) and valid (PeriodicOn w). On a " ++
      "complete-return arm ctx.d is constantly 0 (M.1.1), so the M.4 periodicity field valid is " ++
      "AUTOMATIC (PeriodicOn.of_constant). Hence patch existence for the actual carries collapses to " ++
      "the clean run and is NOT a separate residual; M.4/M.5 boundary dichotomies are upstream.",
    "CLOSED (genuine patch family for the ACTUAL carries) — AnchoredPatchFamily.ofAnchoredCleanRun: " ++
      "from an AnchoredCleanRun (anchor a, positive core, every start < a, ctx.d = 0 on the shared " ++
      "interior (x, a+coreLen)) builds the wave-19 AnchoredPatchFamily with the ACTUAL word w := ctx.d, " ++
      "each patch the shared core, and valid PROVED from constancy of ctx.d on the core. Through " ++
      "wave-19 ofPatchFamily/ofCoreCover it yields the geometry " ++
      "(AnchoredCompleteReturnGeometry.ofAnchoredCleanRun) and SliceCompleteReturns " ++
      "(sliceCompleteReturns_of_anchoredCleanRun), firing the whole (Z) downstream. " ++
      "anchoredCleanRun_w_eq_actual: the word is the genuine ctx.d, not a constant stand-in.",
    "CLOSED (sharp characterization of the EXISTENCE) — anchoredGeometry_nonempty_iff_zeroRunToAnchor: " ++
      "Nonempty (AnchoredCompleteReturnGeometry ctx key y) <-> exists a common anchor a >= every start " ++
      "with ctx.d = 0 on (x,a] from each start. anchoredGeometry_nonempty_iff_sliceCompleteReturns: " ++
      "the existence is EXACTLY the wave-18 residual SliceCompleteReturns (via " ++
      "AnchoredCompleteReturnGeometry.ofSliceCompleteReturns using the maximal slice start + " ++
      "zeroRunAllPairs_of_completeReturns, and wave-19's sliceCompleteReturns_of_anchoredGeometry). So " ++
      "wave-19's geometry is a faithful repackaging of 'no carry-dropping 1-digit between starts in the " ++
      "shared anchored region', neither stronger nor weaker.",
    "NON-VACUOUS / TEETH — anchoredCleanRun_excludes_dirty (a 1-digit on the clean run is impossible); " ++
      "anchoredCleanRun_overlap_card (two starts' patches overlap on >= coreLen > 0 points, the M.3.1 " ++
      "displayed inequality theoremM3_1_anchoredSemiperiodicOverlap); anchoredCleanRun_carry_strictMono " ++
      "(the carry valuation strictly climbs). With wave-18's dirtyBetweenStarts_strict_deficit (a " ++
      "1-digit is a strict carry deficit R_z < 2^(z-x) R_x) the datum is a genuine constraint.",
    "OPEN (the single irreducible remainder, now pinned to an elementary digit fact) — the " ++
      "zero-run-to-anchor condition itself (equivalently SliceCompleteReturns): that for the actual " ++
      "carries there IS a common anchor a >= every slice start with ctx.d vanishing on (x,a] from each " ++
      "start. This is the M.3.1 four-coordinate anchored overlap + M.3.2 endpoint-pinning geometry of " ++
      "the actual carries; the carry recurrence R_{N+1} = 2 R_N - Q(N+1) d_{N+1} cannot decide which " ++
      "positions are the complete-return starts nor that their arms nest in the shared anchored region. " ++
      "proof_v4_unconditional_clean_v5.tex §M.3.1 / §M.3.2 (lines ~6081-6205)." ]

theorem returnM31ExistenceResiduals_nonempty : returnM31ExistenceResiduals ≠ [] := by
  simp [returnM31ExistenceResiduals]

/-! ## 6.  Axiom-cleanliness audit -/

#print axioms AnchoredPatchFamily.ofAnchoredCleanRun
#print axioms sliceCompleteReturns_of_anchoredCleanRun
#print axioms AnchoredCompleteReturnGeometry.ofAnchoredCleanRun
#print axioms anchoredGeometry_nonempty_of_anchoredCleanRun
#print axioms AnchoredCompleteReturnGeometry.ofZeroRunToAnchor
#print axioms AnchoredCompleteReturnGeometry.ofSliceCompleteReturns
#print axioms anchoredGeometry_nonempty_iff_zeroRunToAnchor
#print axioms anchoredGeometry_nonempty_iff_sliceCompleteReturns
#print axioms zeroRunToAnchor_of_anchoredCleanRun
#print axioms anchoredCleanRun_excludes_dirty
#print axioms anchoredCleanRun_overlap_card
#print axioms anchoredCleanRun_carry_strictMono
#print axioms anchoredCleanRun_w_eq_actual

end

end Erdos260
