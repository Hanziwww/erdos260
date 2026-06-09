import Erdos260.SliceM31PatchExtractionFromArmCore

/-!
# The genuine M.3.1 anchored long-semiperiodic-return datum, with the four-coordinate overlap DERIVED
(`SliceM31AnchoredReturnCore`)

This module (NEW; it edits no existing file) pushes the Return §M.3 residual one layer **below** the
survivor-family / arm-core-overlap / actual-patch-extraction frontier
(`SliceM31OverlapClosureCore` / `SliceCompleteReturnsClosureCore` / `SliceM31PatchExtractionCore`).

Wave-24's `AnchoredSurvivorFamily` already carries the genuine M.3.1 surviving patches over the actual
word `ctx.d`, but its single deep field `anchored_patch : AnchoredSemiperiodicPatch datum ctx.d
(patch x)` bundles the M.3.1 **conclusion** as an *opaque* `corePlacement_input :
IntervalBlock.Contains (patch x).block datum.core` — the four-coordinate anchored overlap is *assumed*,
not derived.  This module replaces that opaque containment by the genuine **hypotheses** of Lemma
M.3.1 / Lemma M.3.2, and **derives** the containment as a theorem, exactly as the manuscript does.

## What the manuscript actually supplies (the genuinely more primitive datum)

`proof_v4_unconditional_clean_v5.tex` §M.3.1 (lines ~6580–6620) fixes an anchored first-dirty datum
`(t,σ,ι,𝔡,χ)`, and for each long semiperiodic return charging it produces a canonical semiperiodic
patch `P(J)` whose near boundary is **fixed at the anchored coordinate** `a = a(t,σ,ι,𝔡,χ)` (M.3.2
endpoint pinning) and which is **long** (arm scale `τ ≤ |u| < 2τ`).  The displayed one-sided core
\[
  [a + C_QL,\ a + (1-θ)τ - C_QL]
\]
is then literally the **sub-window** of every such patch, and `core ⊆ P(J)` is the elementary
sub-block containment — that is the entire content of M.3.1's containment claim ("Therefore the
displayed core is contained in every surviving patch").

The new datum `AnchoredLongReturnFamily` keeps exactly these manuscript inputs as separate fields:

* `anchor` / `margin` / `coreLen` — the M.3.1 anchored coordinate `a`, the `O_Q(L)` margin, and the
  `(1-2θ)τ - O_Q(L)` core length; the displayed one-sided core is `[anchor+margin, anchor+margin+coreLen)`.
* `patch_anchored` (M.3.2): every start's canonical patch has its near endpoint at the common anchor
  (`(patch x).block.start = anchor`).
* `patch_long` (M.3.1): every patch is long enough to contain the displayed core
  (`margin + coreLen ≤ (patch x).block.length`).
* `patch_valid` (M.4 / cleaning output): each patch is a genuine semiperiodic block over the **actual
  word** `ctx.d` (`(patch x).Valid ctx.d`, i.e. `PeriodicOn ctx.d …`).
* `arm_complete` (M.1.1): the clean-maximal complete-return arm `CompleteReturnArm ctx x …`.
* `arm_contains_patch` (M.3.2), `start_lt_core` (M.3.2 orientation).

## What this module DERIVES (the M.3.1 four-coordinate overlap, no longer assumed)

* `AnchoredLongReturnFamily.core_contained` / `…corePlacement` — **the M.3.1 containment, PROVED** from
  `patch_anchored` (M.3.2) + `patch_long` (M.3.1): the displayed core is the sub-window
  `[anchor+margin, …)` of every anchored long patch, so `IntervalBlock.Contains (patch x).block
  datum.core` follows from the longness inequality alone.  This is the genuine Lemma-M.3.1 endpoint
  geometry (`AnchoredCorePlacement.left`), the step the survivor family currently takes as a black box.
* `AnchoredSurvivorFamily.ofAnchoredLongReturnFamily` — **the construction (the main content)**: the
  wave-24 survivor family is *assembled* from the more primitive datum, with the opaque
  `corePlacement_input` replaced by `core_contained`.  Through wave-24's `…ofSurvivorFamily` discharge
  this forces `SliceCompleteReturns`, `CleanReturnPlacement`, and the whole `(Z)` downstream.
* `anchoredLongReturnFamily_overlap_card` — the genuine M.3 displayed inequality
  `coreLen ≤ |P(J₁) ∩ P(J₂)|` (`theoremM3_1_anchoredSemiperiodicOverlap`) on the **actual** distinct
  surviving patches, so the datum is non-vacuous.

## The faithful equivalence (no circular assumption)

`nonempty_anchoredLongReturnFamily_iff_survivorFamily` /
`nonempty_anchoredLongReturnFamily_iff_armCoreOverlap` /
`nonempty_anchoredLongReturnFamily_iff_actualPatchExtraction` prove the new existence is **equivalent**
to the three frontier residuals.  The forward map is the genuine M.3.1 derivation above; the backward
map (`AnchoredLongReturnFamily.ofSurvivorFamily`) is the degenerate collapse (take each patch to be the
bare core as a period-`1` block, anchored at `core.start`, valid since `ctx.d = 0` on the clean core).
So the datum is a **faithful** reformulation in the genuine M.3.1 *hypothesis* vocabulary — neither
stronger nor weaker — and it does **not** assume `CleanReturnPlacement`, `SliceCompleteReturns`,
`AnchoredSurvivorFamily`, or `AnchoredArmCoreOverlap`: the M.3.1 four-coordinate overlap that those
layers carry as data is here a *theorem*.

## Bridge to the V3 charge (`Class4ReturnPerSliceCharge`)

`OlcSliceData.ofAnchoredLongReturnFamily` produces, from the geometry plus the shell bound and the
carry-period gap divisibility, the per-`(e,τ,P)`-slice M.2.1 datum `OlcSliceData` — exactly the
`slices` field consumed by the V3 Return charge `Class4ReturnPerSliceCharge` (`Erdos260…V3`), whose
`returnFloor` then gives `routedClassMassOf … 4 ≤ c⋆ξX/6`.  This connects the M.3 geometry to the
class-4 capacity floor without fabricating the K.1.2/L.20 window-excess charge numerics.

## The smallest honest residual (sharply characterized)

After this module the complete-return placement `(Z)` / `CleanReturnPlacement` is reduced to the single
residual `Nonempty (AnchoredLongReturnFamily ctx key y)`: that the actual OLC slice's complete-return
starts are **long semiperiodic returns over `ctx.d`, anchored at one common coordinate** (M.3.2),
**long enough to span the displayed one-sided core** (M.3.1), each inside its clean-maximal
complete-return arm (M.1.1) lying strictly below the core (M.3.2).  This is the raw M.2.1 endpoint /
M.3.1 anchored-overlap geometry — the L.6.1 residual-trichotomy output of the actual carries — with the
four-coordinate overlap now *derived* rather than assumed.  The carry recurrence
`R_{N+1} = 2 R_N − Q(N+1) d_{N+1}` cannot decide which positions are the complete-return starts (a
`1`-digit between starts is a genuine strict carry deficit, so the datum is non-vacuous).  No `sorry`,
`axiom`, `admit`, or `native_decide`; no degenerate shortcut.
-/

namespace Erdos260

open Finset

set_option linter.unusedVariables false

noncomputable section

/-! ## 1.  The genuine M.3.1 anchored long-semiperiodic-return datum

The manuscript M.3.1/M.3.2/M.1.1 inputs kept as *separate* fields, with the common one-sided core
recorded only as the displayed window coordinates `(anchor, margin, coreLen)` — never as an opaque
containment hypothesis. -/

/-- **The anchored long-semiperiodic-return family (the genuine M.3.1/M.3.2/M.1.1 datum).**

For every complete-return start `x` on the slice:

* the common anchored coordinate `anchor = a(t,σ,ι,𝔡,χ)` (M.3.1), the `O_Q(L)` margin, and the
  `(1-2θ)τ - O_Q(L)` core length `coreLen`; the displayed one-sided core is the explicit window
  `[anchor+margin, anchor+margin+coreLen)`;
* `patch x` is the start's canonical semiperiodic patch, `armBlock x` its complete-return arm;
* `patch_anchored` (M.3.2): the patch's near endpoint sits at the common anchor;
* `patch_long` (M.3.1): the patch is long enough to span the displayed core
  (`margin + coreLen ≤ (patch x).block.length`);
* `patch_valid` (M.4): the patch is a genuine semiperiodic block over the **actual** word `ctx.d`;
* `arm_complete` (M.1.1): the clean-maximal complete-return arm;
* `arm_contains_patch` (M.3.2): the arm contains its patch;
* `start_lt_core` (M.3.2): the start lies strictly before the core start `anchor + margin`. -/
structure AnchoredLongReturnFamily (ctx : ActualFailureContext) (key : ℕ → ℕ) (y : ℕ) where
  /-- the common anchored coordinate `a = a(t,σ,ι,𝔡,χ)` (M.3.1). -/
  anchor : ℕ
  /-- the `O_Q(L)` margin separating the core start from the anchor (M.3.1 displayed table). -/
  margin : ℕ
  /-- the `(1-2θ)τ - O_Q(L)` length of the displayed one-sided core (M.3.1). -/
  coreLen : ℕ
  /-- the anchored core is non-degenerate. -/
  coreLen_pos : 0 < coreLen
  /-- the canonical semiperiodic patch of each start. -/
  patch : ℕ → SemiperiodicBlock
  /-- the complete-return arm of each start, as a finite half-open block. -/
  armBlock : ℕ → IntervalBlock
  /-- **M.3.2 (endpoint pinning).**  Each start's patch has its near endpoint at the common anchor. -/
  patch_anchored : ∀ x ∈ olcSlice ctx key y, (patch x).block.start = anchor
  /-- **M.3.1 (longness).**  Each patch is long enough to span the displayed one-sided core. -/
  patch_long : ∀ x ∈ olcSlice ctx key y, margin + coreLen ≤ (patch x).block.length
  /-- **M.4 (surviving semiperiodicity over the actual carries).**  Each patch is a genuine
  semiperiodic block of the actual digit word `ctx.d`. -/
  patch_valid : ∀ x ∈ olcSlice ctx key y, (patch x).Valid ctx.d
  /-- the start is the left endpoint of its arm. -/
  arm_start : ∀ x ∈ olcSlice ctx key y, (armBlock x).start = x
  /-- **M.1.1 (clean-maximal complete-return arm).** -/
  arm_complete : ∀ x ∈ olcSlice ctx key y, CompleteReturnArm ctx x ((armBlock x).stop - 1)
  /-- **M.3.2 (the arm contains its patch).** -/
  arm_contains_patch :
    ∀ x ∈ olcSlice ctx key y, IntervalBlock.Contains (armBlock x) (patch x).block
  /-- **M.3.2 (strict orientation).**  Every start sits strictly before the core start. -/
  start_lt_core : ∀ x ∈ olcSlice ctx key y, x < anchor + margin

namespace AnchoredLongReturnFamily

variable {ctx : ActualFailureContext} {key : ℕ → ℕ} {y : ℕ}

/-- **The fixed anchored first-dirty datum of the family (M.3.1).**  The common one-sided core is the
explicit displayed window `[anchor+margin, anchor+margin+coreLen)`; the lower bound is the core length
(`(1-2θ)τ - O_Q(L)`).  The side/copy/margin bookkeeping is the finite anchoring data. -/
def datum (R : AnchoredLongReturnFamily ctx key y) : AnchoredFirstDirtyDatum where
  anchor := R.anchor
  side := OrientedSide.left
  copy := 0
  marginClass := 0
  core := ⟨R.anchor + R.margin, R.coreLen⟩
  lowerBound := R.coreLen
  core_len_lower := le_refl _

@[simp] theorem datum_core (R : AnchoredLongReturnFamily ctx key y) :
    R.datum.core = ⟨R.anchor + R.margin, R.coreLen⟩ := rfl

@[simp] theorem datum_lowerBound (R : AnchoredLongReturnFamily ctx key y) :
    R.datum.lowerBound = R.coreLen := rfl

@[simp] theorem datum_side (R : AnchoredLongReturnFamily ctx key y) :
    R.datum.side = OrientedSide.left := rfl

/-- **The M.3.1 four-coordinate core containment, DERIVED (the main new step).**  The displayed
one-sided core `[anchor+margin, anchor+margin+coreLen)` is the sub-window of every anchored long patch:
from `patch_anchored` (the near endpoint is the anchor) and `patch_long` (the patch spans the core),
`IntervalBlock.Contains (patch x).block datum.core` follows by the elementary endpoint inequalities.
This is exactly the containment claim of Lemma M.3.1, here a theorem rather than an opaque field. -/
theorem core_contained (R : AnchoredLongReturnFamily ctx key y) {x : ℕ}
    (hx : x ∈ olcSlice ctx key y) :
    IntervalBlock.Contains (R.patch x).block R.datum.core := by
  have ha := R.patch_anchored x hx
  have hl := R.patch_long x hx
  refine ⟨?_, ?_⟩
  · show (R.patch x).block.start ≤ R.anchor + R.margin
    omega
  · show R.anchor + R.margin + R.coreLen ≤ (R.patch x).block.start + (R.patch x).block.length
    omega

/-- **The M.3.1 oriented endpoint placement, DERIVED.**  The anchored long patch realises the
manuscript's oriented `AnchoredCorePlacement` (left side): the patch starts at-or-before the core start
and ends at-or-after the core stop.  This is the explicit Lemma-M.3.1 endpoint geometry. -/
theorem corePlacement (R : AnchoredLongReturnFamily ctx key y) {x : ℕ}
    (hx : x ∈ olcSlice ctx key y) :
    AnchoredCorePlacement R.datum (R.patch x).block := by
  have ha := R.patch_anchored x hx
  have hl := R.patch_long x hx
  refine AnchoredCorePlacement.left R.datum_side ?_ ?_
  · show (R.patch x).block.start ≤ R.anchor + R.margin
    omega
  · show R.anchor + R.margin + R.coreLen ≤ (R.patch x).block.start + (R.patch x).block.length
    omega

/-- **The derived genuine M.3.1 anchored semiperiodic patch over the actual carries.**  Packages
`patch_valid` (M.4 periodicity over `ctx.d`) with the *derived* `core_contained` (M.3.1) into the
wave-19 `AnchoredSemiperiodicPatch` of the fixed datum — no opaque containment hypothesis. -/
theorem anchoredPatch (R : AnchoredLongReturnFamily ctx key y) {x : ℕ}
    (hx : x ∈ olcSlice ctx key y) :
    AnchoredSemiperiodicPatch R.datum ctx.d (R.patch x) :=
  ⟨R.patch_valid x hx, R.core_contained hx⟩

end AnchoredLongReturnFamily

/-! ## 2.  The construction: assembling the wave-24 survivor family

The wave-24 `AnchoredSurvivorFamily` is built from the more primitive datum.  Its single opaque deep
field — the M.3.1 containment inside `anchored_patch` — is supplied by the *derived* `core_contained`.
Everything else is reused verbatim. -/

/-- **The wave-24 survivor family from the anchored long-return datum (PROVED — the main
construction).**  The common datum is `R.datum` (the displayed one-sided core); the genuine M.3.1
`anchored_patch` is `R.anchoredPatch` (validity over `ctx.d` + the *derived* core containment).  The
M.1.1 arm, the M.3.2 arm-contains-patch and strict orientation are reused. -/
def AnchoredSurvivorFamily.ofAnchoredLongReturnFamily {ctx : ActualFailureContext} {key : ℕ → ℕ}
    {y : ℕ} (R : AnchoredLongReturnFamily ctx key y) : AnchoredSurvivorFamily ctx key y where
  datum := R.datum
  patch := R.patch
  armBlock := R.armBlock
  datum_pos := R.coreLen_pos
  arm_start := R.arm_start
  arm_complete := R.arm_complete
  anchored_patch := fun x hx => R.anchoredPatch hx
  arm_contains_patch := R.arm_contains_patch
  start_lt_core := fun x hx => R.start_lt_core x hx

/-! ## 3.  The discharge: deriving the placement `(Z)` / `CleanReturnPlacement`

Through wave-24's `…ofSurvivorFamily` discharge the anchored long-return datum forces the slice
placement, the value-level `CleanReturnPlacement`, and the full anchored geometry. -/

/-- **The anchored complete-return geometry from the datum (PROVED).** -/
def AnchoredCompleteReturnGeometry.ofAnchoredLongReturnFamily {ctx : ActualFailureContext}
    {key : ℕ → ℕ} {y : ℕ} (R : AnchoredLongReturnFamily ctx key y) :
    AnchoredCompleteReturnGeometry ctx key y :=
  AnchoredCompleteReturnGeometry.ofSurvivorFamily (AnchoredSurvivorFamily.ofAnchoredLongReturnFamily R)

/-- **The survivor family is inhabited from the datum (PROVED).** -/
theorem nonempty_survivorFamily_of_anchoredLongReturnFamily {ctx : ActualFailureContext}
    {key : ℕ → ℕ} {y : ℕ} (h : Nonempty (AnchoredLongReturnFamily ctx key y)) :
    Nonempty (AnchoredSurvivorFamily ctx key y) :=
  h.elim (fun R => ⟨AnchoredSurvivorFamily.ofAnchoredLongReturnFamily R⟩)

/-- **The arm/core overlap is inhabited from the datum (PROVED).** -/
theorem nonempty_armCoreOverlap_of_anchoredLongReturnFamily {ctx : ActualFailureContext}
    {key : ℕ → ℕ} {y : ℕ} (h : Nonempty (AnchoredLongReturnFamily ctx key y)) :
    Nonempty (AnchoredArmCoreOverlap ctx key y) :=
  h.elim (fun R =>
    nonempty_armCoreOverlap_of_survivorFamily (AnchoredSurvivorFamily.ofAnchoredLongReturnFamily R))

/-- **The slice placement from the datum (PROVED — the main discharge).** -/
theorem sliceCompleteReturns_of_anchoredLongReturnFamily {ctx : ActualFailureContext} {key : ℕ → ℕ}
    {y : ℕ} (R : AnchoredLongReturnFamily ctx key y) : SliceCompleteReturns ctx key y :=
  sliceCompleteReturns_of_survivorFamily (AnchoredSurvivorFamily.ofAnchoredLongReturnFamily R)

/-- **The value-level placement `CleanReturnPlacement` from the datum (PROVED).** -/
theorem cleanReturnPlacement_of_anchoredLongReturnFamily {ctx : ActualFailureContext} {key : ℕ → ℕ}
    {y : ℕ} (R : AnchoredLongReturnFamily ctx key y) : CleanReturnPlacement ctx key y :=
  cleanReturnPlacement_of_survivorFamily (AnchoredSurvivorFamily.ofAnchoredLongReturnFamily R)

/-- **The residual, as a `Nonempty` existence, forces `CleanReturnPlacement` (PROVED).**  The
complete-return placement holds modulo `Nonempty (AnchoredLongReturnFamily …)` — the genuine M.3.1
anchored long-return existence for the actual carries. -/
theorem cleanReturnPlacement_of_nonempty_anchoredLongReturnFamily {ctx : ActualFailureContext}
    {key : ℕ → ℕ} {y : ℕ} (h : Nonempty (AnchoredLongReturnFamily ctx key y)) :
    CleanReturnPlacement ctx key y :=
  h.elim (fun R => cleanReturnPlacement_of_anchoredLongReturnFamily R)

/-- **The residual forces `SliceCompleteReturns` (PROVED).** -/
theorem sliceCompleteReturns_of_nonempty_anchoredLongReturnFamily {ctx : ActualFailureContext}
    {key : ℕ → ℕ} {y : ℕ} (h : Nonempty (AnchoredLongReturnFamily ctx key y)) :
    SliceCompleteReturns ctx key y :=
  h.elim (fun R => sliceCompleteReturns_of_anchoredLongReturnFamily R)

/-! ## 4.  The faithful equivalence (no circular assumption)

The new existence is equivalent to the three frontier residuals.  The forward map is the genuine M.3.1
derivation; the backward map is the degenerate wave-20/24 collapse (the bare core as a period-`1`
constant patch anchored at `core.start`, valid because `ctx.d = 0` on the clean core). -/

/-- **The anchored long-return datum from a survivor family (the degenerate collapse, PROVED).**  Take
the anchor to be the survivor datum's core start, margin `0`, the core itself (as a period-`1`
`SemiperiodicBlock`) as every patch; longness is the trivial `0 + core.length ≤ core.length`, and the
patch validity is `PeriodicOn.of_constant` since `ctx.d = 0` on the core
(`survivorFamily_clean_beyond_starts`).  This discards the genuine overlapping semiperiodic patches and
serves only to witness that the reformulation is faithful (neither stronger nor weaker). -/
def AnchoredLongReturnFamily.ofSurvivorFamily {ctx : ActualFailureContext} {key : ℕ → ℕ} {y : ℕ}
    (S : AnchoredSurvivorFamily ctx key y) : AnchoredLongReturnFamily ctx key y where
  anchor := S.datum.core.start
  margin := 0
  coreLen := S.datum.core.length
  coreLen_pos := S.core_nonempty
  patch := fun _ => ⟨S.datum.core, 1⟩
  armBlock := S.armBlock
  patch_anchored := fun x hx => rfl
  patch_long := fun x hx => by
    show 0 + S.datum.core.length ≤ S.datum.core.length
    omega
  patch_valid := fun x hx => by
    show PeriodicOn ctx.d S.datum.core.start S.datum.core.length 1
    exact PeriodicOn.of_constant Nat.one_pos
      (fun i hi => (survivorFamily_clean_beyond_starts S hx i hi).2)
  arm_start := S.arm_start
  arm_complete := S.arm_complete
  arm_contains_patch := fun x hx =>
    (AnchoredArmCoreOverlap.ofSurvivorFamily S).core_contained x hx
  start_lt_core := fun x hx => by
    have h := S.start_lt_core x hx
    simpa using h

/-- **The anchored long-return datum from the older common clean-run witness (PROVED).**  This is the
direct bridge from wave-20's `AnchoredCleanRun` formulation to the newer lowered M.3.1 surface: use
the clean run's common core `[anchor, anchor + coreLen)` as the anchored patch, period `1`, over the
actual word `ctx.d`.  The M.4 validity is supplied by the clean-run zero digits, while the M.1.1
complete-return arm is reconstructed from `completeReturnArm_iff_zeroRun`. -/
def AnchoredLongReturnFamily.ofAnchoredCleanRun {ctx : ActualFailureContext} {key : ℕ → ℕ}
    {y : ℕ} (R : AnchoredCleanRun ctx key y) : AnchoredLongReturnFamily ctx key y where
  anchor := R.anchor
  margin := 0
  coreLen := R.coreLen
  coreLen_pos := R.coreLen_pos
  patch := fun _ => ⟨⟨R.anchor, R.coreLen⟩, 1⟩
  armBlock := fun x => ⟨x, (R.anchor + R.coreLen) - x⟩
  patch_anchored := fun x hx => rfl
  patch_long := fun x hx => by
    show 0 + R.coreLen ≤ R.coreLen
    omega
  patch_valid := fun x hx => by
    show PeriodicOn ctx.d R.anchor R.coreLen 1
    refine PeriodicOn.of_constant (c := 0) Nat.one_pos ?_
    intro i hi
    have hxa : x < R.anchor := R.start_lt x hx
    exact R.clean x hx (R.anchor + i) (by omega) (by omega)
  arm_start := fun x hx => rfl
  arm_complete := fun x hx => by
    have hxa : x < R.anchor := R.start_lt x hx
    have hxle : x ≤ (⟨x, (R.anchor + R.coreLen) - x⟩ : IntervalBlock).stop - 1 := by
      simp only [IntervalBlock.stop]
      omega
    refine (completeReturnArm_iff_zeroRun ctx hxle).2 ?_
    intro j hj1 hj2
    exact R.clean x hx j hj1 (by
      simp only [IntervalBlock.stop] at hj2
      omega)
  arm_contains_patch := fun x hx => by
    have hxa : x < R.anchor := R.start_lt x hx
    simp only [IntervalBlock.Contains, IntervalBlock.stop]
    omega
  start_lt_core := fun x hx => by
    have h := R.start_lt x hx
    simpa using h

/-- **The older clean-run existence supplies the lowered anchored long-return residual (PROVED).** -/
theorem nonempty_anchoredLongReturnFamily_of_anchoredCleanRun {ctx : ActualFailureContext}
    {key : ℕ → ℕ} {y : ℕ} (h : Nonempty (AnchoredCleanRun ctx key y)) :
    Nonempty (AnchoredLongReturnFamily ctx key y) :=
  h.elim (fun R => ⟨AnchoredLongReturnFamily.ofAnchoredCleanRun R⟩)

/-- **The anchored long-return existence is exactly the survivor-family existence (PROVED).** -/
theorem nonempty_anchoredLongReturnFamily_iff_survivorFamily (ctx : ActualFailureContext)
    (key : ℕ → ℕ) (y : ℕ) :
    Nonempty (AnchoredLongReturnFamily ctx key y) ↔ Nonempty (AnchoredSurvivorFamily ctx key y) :=
  ⟨nonempty_survivorFamily_of_anchoredLongReturnFamily,
    fun h => h.elim (fun S => ⟨AnchoredLongReturnFamily.ofSurvivorFamily S⟩)⟩

/-- **The anchored long-return existence is exactly the arm/core-overlap existence (PROVED).** -/
theorem nonempty_anchoredLongReturnFamily_iff_armCoreOverlap (ctx : ActualFailureContext)
    (key : ℕ → ℕ) (y : ℕ) :
    Nonempty (AnchoredLongReturnFamily ctx key y) ↔ Nonempty (AnchoredArmCoreOverlap ctx key y) :=
  Iff.trans (nonempty_anchoredLongReturnFamily_iff_survivorFamily ctx key y)
    (nonempty_armCoreOverlap_iff_survivorFamily ctx key y).symm

/-- **The anchored long-return existence is exactly the actual-patch-extraction existence (PROVED).** -/
theorem nonempty_anchoredLongReturnFamily_iff_actualPatchExtraction (ctx : ActualFailureContext)
    (key : ℕ → ℕ) (y : ℕ) :
    Nonempty (AnchoredLongReturnFamily ctx key y) ↔
      Nonempty (AnchoredActualPatchExtraction ctx key y) :=
  Iff.trans (nonempty_anchoredLongReturnFamily_iff_survivorFamily ctx key y)
    (nonempty_actualPatchExtraction_iff_survivorFamily ctx key y).symm

/-! ## 5.  Teeth and non-vacuity — the genuine M.3.1 overlap of the actual patches -/

/-- **The genuine M.3.1 four-coordinate overlap for the actual surviving patches (PROVED).**  Any two
slice starts' patches overlap on at least `coreLen` points
(`theoremM3_1_anchoredSemiperiodicOverlap`), the displayed inequality (M.3)
`(1-2θ)τ - O_Q(L) ≤ |P(J₁) ∩ P(J₂)|`.  So the anchored core is genuinely shared. -/
theorem anchoredLongReturnFamily_overlap_card {ctx : ActualFailureContext} {key : ℕ → ℕ} {y : ℕ}
    (R : AnchoredLongReturnFamily ctx key y) {x z : ℕ}
    (hx : x ∈ olcSlice ctx key y) (hz : z ∈ olcSlice ctx key y) :
    R.coreLen ≤ ((R.patch x).block.points ∩ (R.patch z).block.points).card :=
  survivorFamily_overlap_card (AnchoredSurvivorFamily.ofAnchoredLongReturnFamily R) hx hz

/-- **Each start carries a genuine anchored patch over the actual carries (PROVED).** -/
theorem anchoredLongReturnFamily_patch_anchored {ctx : ActualFailureContext} {key : ℕ → ℕ} {y : ℕ}
    (R : AnchoredLongReturnFamily ctx key y) {x : ℕ} (hx : x ∈ olcSlice ctx key y) :
    AnchoredSemiperiodicPatch R.datum ctx.d (R.patch x) :=
  R.anchoredPatch hx

/-- **Each patch is a genuine semiperiodic block over the actual digit word (PROVED).**  The family is
realised by the genuine carries `ctx.d`, not a fake constant word. -/
theorem anchoredLongReturnFamily_patch_valid_actual {ctx : ActualFailureContext} {key : ℕ → ℕ}
    {y : ℕ} (R : AnchoredLongReturnFamily ctx key y) {x : ℕ} (hx : x ∈ olcSlice ctx key y) :
    (R.patch x).Valid ctx.d :=
  R.patch_valid x hx

/-- **The core is clean and strictly beyond every start (PROVED — the strict-strengthening teeth).** -/
theorem anchoredLongReturnFamily_clean_beyond_starts {ctx : ActualFailureContext} {key : ℕ → ℕ}
    {y : ℕ} (R : AnchoredLongReturnFamily ctx key y) {x : ℕ} (hx : x ∈ olcSlice ctx key y) :
    ∀ i, i < R.coreLen →
      x < R.anchor + R.margin + i ∧ ctx.d (R.anchor + R.margin + i) = 0 :=
  survivorFamily_clean_beyond_starts (AnchoredSurvivorFamily.ofAnchoredLongReturnFamily R) hx

/-- **The M.1.1 arm reaches the M.3.1 core (PROVED).**  Each start's clean-maximal arm is a genuine
`CompleteReturnArm` reaching the common anchored core start. -/
theorem anchoredLongReturnFamily_arm_reaches_core {ctx : ActualFailureContext} {key : ℕ → ℕ} {y : ℕ}
    (R : AnchoredLongReturnFamily ctx key y) {x : ℕ} (hx : x ∈ olcSlice ctx key y) :
    CompleteReturnArm ctx x (R.anchor + R.margin) :=
  survivorFamily_arm_reaches_core (AnchoredSurvivorFamily.ofAnchoredLongReturnFamily R) hx

/-- **A dirty digit between two starts refutes the datum (PROVED).** -/
theorem anchoredLongReturnFamily_excludes_dirty {ctx : ActualFailureContext} {key : ℕ → ℕ} {y : ℕ}
    (R : AnchoredLongReturnFamily ctx key y) {x z j : ℕ}
    (hx : x ∈ olcSlice ctx key y) (hz : z ∈ olcSlice ctx key y) (hxz : x < z)
    (hj1 : x < j) (hj2 : j ≤ z) (hdirty : ctx.d j = 1) : False :=
  survivorFamily_excludes_dirty (AnchoredSurvivorFamily.ofAnchoredLongReturnFamily R)
    hx hz hxz hj1 hj2 hdirty

/-- **The carry valuation strictly climbs on every pair (PROVED).** -/
theorem anchoredLongReturnFamily_carry_strictMono {ctx : ActualFailureContext} {key : ℕ → ℕ} {y : ℕ}
    (R : AnchoredLongReturnFamily ctx key y) {x z : ℕ}
    (hx : x ∈ olcSlice ctx key y) (hz : z ∈ olcSlice ctx key y) (hxz : x < z) :
    carryVal2 ctx x < carryVal2 ctx z :=
  survivorFamily_carry_strictMono (AnchoredSurvivorFamily.ofAnchoredLongReturnFamily R) hx hz hxz

/-! ## 6.  Bridge to the V3 Return charge (`Class4ReturnPerSliceCharge.slices`)

The geometry produces the per-`(e,τ,P)`-slice M.2.1 datum `OlcSliceData` that the V3 Return charge
consumes.  No charge numerics are fabricated: only the M.2.1 slice data is supplied. -/

/-- **The per-slice M.2.1 datum from the anchored long-return geometry (PROVED).**  With the shell
bound `hbound` and the carry-period gap divisibility `hgap`, the geometry yields the per-slice
`OlcSliceData` (the genuine carry-side `carryVal2` level map + crossing-freeness + congruence) via
wave-19's `OlcSliceData.ofAnchoredGeometry`.  A per-slice-key family of these is exactly the `slices`
field consumed by the V3 `Class4ReturnPerSliceCharge`, whose `returnFloor` gives the class-4 capacity
floor `routedClassMassOf … 4 ≤ c⋆ξX/6`. -/
def OlcSliceData.ofAnchoredLongReturnFamily (ctx : ActualFailureContext) (key : ℕ → ℕ) (y : ℕ)
    (hbound : ∀ k ∈ olcSlice ctx key y, carryVal2 ctx k ≤ ctx.shell.X)
    (R : AnchoredLongReturnFamily ctx key y)
    (hgap : ∀ x ∈ olcSlice ctx key y, ∀ z ∈ olcSlice ctx key y, x < z →
      (∀ c ∈ olcSlice ctx key y, x < c → z ≤ c) → 2 ^ carryVal2 ctx x ∣ (z - x)) :
    OlcSliceData ctx key y :=
  OlcSliceData.ofAnchoredGeometry ctx key y hbound
    (AnchoredCompleteReturnGeometry.ofAnchoredLongReturnFamily R) hgap

/-! ## 7.  Honest residual inventory -/

/-- The precise status of the complete-return placement after deriving the M.3.1 four-coordinate
overlap from the genuine anchored long-return hypotheses. -/
def sliceM31AnchoredReturnResiduals : List String :=
  [ "GOAL — push the Return §M.3 residual one layer below the survivor-family / arm-core-overlap / " ++
      "actual-patch-extraction frontier by DERIVING the M.3.1 four-coordinate overlap (the opaque " ++
      "corePlacement_input : Contains (patch x).block datum.core inside AnchoredSemiperiodicPatch) " ++
      "from the manuscript M.3.1/M.3.2 hypotheses, rather than carrying it as data. " ++
      "proof_v4_unconditional_clean_v5.tex Lemma M.3.1 / M.3.2 (lines ~6580-6642).",
    "CLOSED (the genuinely more primitive datum) — AnchoredLongReturnFamily keeps the manuscript " ++
      "inputs as SEPARATE fields: anchor/margin/coreLen (the M.3.1 displayed one-sided core window " ++
      "[anchor+margin, anchor+margin+coreLen)), patch_anchored (M.3.2 endpoint pinning), patch_long " ++
      "(M.3.1 longness margin+coreLen <= patch length), patch_valid (M.4 PeriodicOn over the ACTUAL " ++
      "word ctx.d), arm_complete (M.1.1 CompleteReturnArm), arm_contains_patch + start_lt_core (M.3.2). " ++
      "The common core is NEVER an opaque containment hypothesis.",
    "CLOSED (M.3.1 overlap DERIVED, the main step) — core_contained / corePlacement: the displayed " ++
      "core is the sub-window of every anchored long patch, so Contains (patch x).block datum.core " ++
      "(equivalently AnchoredCorePlacement.left) follows from patch_anchored + patch_long by the " ++
      "elementary endpoint inequalities. This is exactly the containment claim of Lemma M.3.1, here a " ++
      "THEOREM. anchoredPatch then assembles the genuine AnchoredSemiperiodicPatch over ctx.d with no " ++
      "opaque field.",
    "CLOSED (the construction + discharge) — AnchoredSurvivorFamily.ofAnchoredLongReturnFamily " ++
      "assembles the wave-24 survivor family with corePlacement_input replaced by the derived " ++
      "core_contained; through wave-24's ...ofSurvivorFamily: sliceCompleteReturns_of_/ " ++
      "cleanReturnPlacement_of_/ nonempty_armCoreOverlap_of_ and the Nonempty forms fire the whole " ++
      "(Z) downstream. AnchoredCompleteReturnGeometry.ofAnchoredLongReturnFamily yields the geometry.",
    "CLOSED (faithful equivalence, NOT circular) — nonempty_anchoredLongReturnFamily_iff_survivorFamily " ++
      "/ _iff_armCoreOverlap / _iff_actualPatchExtraction: the new existence equals the three frontier " ++
      "residuals. Forward = the genuine M.3.1 derivation; backward (AnchoredLongReturnFamily." ++
      "ofSurvivorFamily) = the degenerate collapse (bare core as a period-1 constant patch anchored at " ++
      "core.start, valid since ctx.d = 0 on the clean core). It assumes NONE of CleanReturnPlacement / " ++
      "SliceCompleteReturns / AnchoredSurvivorFamily / AnchoredArmCoreOverlap: the M.3.1 overlap those " ++
      "carry as data is here a theorem.",
    "CLOSED (bridge from older clean-run surface) — AnchoredLongReturnFamily.ofAnchoredCleanRun / " ++
      "nonempty_anchoredLongReturnFamily_of_anchoredCleanRun: wave-20's AnchoredCleanRun common-anchor " ++
      "zero-run datum directly builds the newer lowered anchored-long-return residual, using the common " ++
      "clean core as a period-1 actual-word patch and deriving the M.1.1 CompleteReturnArm from " ++
      "completeReturnArm_iff_zeroRun. Thus any upstream proof of the clean-run-to-anchor datum now " ++
      "feeds V4's anchoredLongReturnFamily field without detouring through SliceCompleteReturns.",
    "NON-VACUOUS / TEETH — anchoredLongReturnFamily_overlap_card fires " ++
      "theoremM3_1_anchoredSemiperiodicOverlap on the ACTUAL distinct surviving patches " ++
      "(coreLen <= |P(J1) cap P(J2)|, the displayed eq M.3); anchoredLongReturnFamily_patch_anchored / " ++
      "patch_valid_actual (genuine AnchoredSemiperiodicPatch / PeriodicOn over ctx.d); " ++
      "clean_beyond_starts (core clean strictly beyond every start); arm_reaches_core; excludes_dirty; " ++
      "carry_strictMono. With a 1-digit a strict carry deficit, the datum is a genuine constraint.",
    "BRIDGE to V3 charge — OlcSliceData.ofAnchoredLongReturnFamily: from the geometry + shell bound + " ++
      "carry-period gap divisibility, the per-(e,tau,P)-slice OlcSliceData (carryVal2 level map + " ++
      "crossing-freeness + congruence), exactly the slices field of Class4ReturnPerSliceCharge " ++
      "(Erdos260...V3), whose returnFloor gives routedClassMassOf ... 4 <= c*xiX/6. No charge numerics " ++
      "fabricated.",
    "OPEN (the single irreducible remainder) — Nonempty (AnchoredLongReturnFamily ctx key y): that " ++
      "the actual OLC slice's complete-return starts are long semiperiodic returns over ctx.d anchored " ++
      "at ONE common coordinate (M.3.2), long enough to span the displayed one-sided core (M.3.1), " ++
      "each inside its clean-maximal complete-return arm (M.1.1) lying strictly below the core (M.3.2). " ++
      "This is the raw M.2.1 endpoint / M.3.1 anchored-overlap geometry — the L.6.1 residual-trichotomy " ++
      "output of the actual carries, with the four-coordinate overlap now DERIVED rather than assumed — " ++
      "which the carry recurrence R_{N+1} = 2 R_N - Q(N+1) d_{N+1} cannot decide. " ++
      "proof_v4_unconditional_clean_v5.tex Lemma M.2.1 / Lemma M.3.1 / Lemma M.3.2 (lines ~6486-6709)." ]

theorem sliceM31AnchoredReturnResiduals_nonempty : sliceM31AnchoredReturnResiduals ≠ [] := by
  simp [sliceM31AnchoredReturnResiduals]

/-! ## 8.  Axiom-cleanliness audit -/

#print axioms AnchoredLongReturnFamily.core_contained
#print axioms AnchoredLongReturnFamily.corePlacement
#print axioms AnchoredLongReturnFamily.anchoredPatch
#print axioms AnchoredSurvivorFamily.ofAnchoredLongReturnFamily
#print axioms AnchoredCompleteReturnGeometry.ofAnchoredLongReturnFamily
#print axioms nonempty_survivorFamily_of_anchoredLongReturnFamily
#print axioms nonempty_armCoreOverlap_of_anchoredLongReturnFamily
#print axioms sliceCompleteReturns_of_anchoredLongReturnFamily
#print axioms cleanReturnPlacement_of_anchoredLongReturnFamily
#print axioms cleanReturnPlacement_of_nonempty_anchoredLongReturnFamily
#print axioms sliceCompleteReturns_of_nonempty_anchoredLongReturnFamily
#print axioms AnchoredLongReturnFamily.ofSurvivorFamily
#print axioms AnchoredLongReturnFamily.ofAnchoredCleanRun
#print axioms nonempty_anchoredLongReturnFamily_of_anchoredCleanRun
#print axioms nonempty_anchoredLongReturnFamily_iff_survivorFamily
#print axioms nonempty_anchoredLongReturnFamily_iff_armCoreOverlap
#print axioms nonempty_anchoredLongReturnFamily_iff_actualPatchExtraction
#print axioms anchoredLongReturnFamily_overlap_card
#print axioms anchoredLongReturnFamily_patch_anchored
#print axioms anchoredLongReturnFamily_patch_valid_actual
#print axioms anchoredLongReturnFamily_clean_beyond_starts
#print axioms anchoredLongReturnFamily_arm_reaches_core
#print axioms anchoredLongReturnFamily_excludes_dirty
#print axioms anchoredLongReturnFamily_carry_strictMono
#print axioms OlcSliceData.ofAnchoredLongReturnFamily

end

end Erdos260
