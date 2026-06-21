import Mathlib
import Erdos260.LocalGeometryFactory
import Erdos260.GlobalCarryShellAssembly
import Erdos260.Constants

/-!
# K.2.5 dirty-multiplicity shell fibre construction
-/

namespace Erdos260

set_option maxHeartbeats 800000

noncomputable section

/-- Identity constructor for the strongest proof-v4 K.2.5 dirty fibre-coding
leaf consumed by the preferred strict endpoint. -/
def dirtyMultiplicityProofV4ShellFibreCodingFromInput
    {shell : FailingDyadicShell}
    (data : DirtyMultiplicityProofV4ShellFibreCodingInputData shell) :
    DirtyMultiplicityProofV4ShellFibreCodingInputData shell :=
  data

/-- Identity constructor for the fixed-shell proof-v4 K.2.5 dirty fibre leaf. -/
def dirtyMultiplicityProofV4ShellFibreFromInput
    {shell : FailingDyadicShell}
    (data : DirtyMultiplicityProofV4ShellFibreInputData shell) :
    DirtyMultiplicityProofV4ShellFibreInputData shell :=
  data

/-- Project a Fin-labelled fibre-coding K.2.5 leaf to the fixed-shell
proof-v4 boundary once its scale parameter is identified with the shell's
dyadic exponent. -/
def dirtyMultiplicityProofV4ShellFibreCodingFromFinFibreCodingInput
    {shell : FailingDyadicShell}
    (data : DirtyMultiplicityFinFibreCodingInputData)
    (hL : data.L = Classical.choose shell.hXdyadic) :
    DirtyMultiplicityProofV4ShellFibreCodingInputData shell := by
  cases data with
  | mk dirtyFamily logStar CM L scale fibreCoding logStar_le_log =>
      subst hL
      exact {
        dirtyFamily := dirtyFamily
        logStar := logStar
        CM := CM
        scale := scale
        fibreCoding := fibreCoding
        logStar_le_log := logStar_le_log }

/-- Project a Fin-labelled fibre-bound K.2.5 leaf to the fixed-shell proof-v4
boundary once its scale parameter is identified with the shell's dyadic
exponent. -/
def dirtyMultiplicityProofV4ShellFibreFromFinFibreInput
    {shell : FailingDyadicShell}
    (data : DirtyMultiplicityFinFibreInputData)
    (hL : data.L = Classical.choose shell.hXdyadic) :
    DirtyMultiplicityProofV4ShellFibreInputData shell := by
  cases data with
  | mk dirtyFamily logStar CM L scale fibre logStar_le_log =>
      subst hL
      exact {
        dirtyFamily := dirtyFamily
        logStar := logStar
        CM := CM
        scale := scale
        fibre := fibre
        logStar_le_log := logStar_le_log }

/-- Project the older split scale/fibre K.2.5 leaf to the fixed-shell proof-v4
boundary when its scale parameter is locked to the active shell. -/
def dirtyMultiplicityProofV4ShellFibreFromSplitInput
    {shell : FailingDyadicShell}
    (data : DirtyMultiplicityInputData)
    (hL : data.L = Classical.choose shell.hXdyadic) :
    DirtyMultiplicityProofV4ShellFibreInputData shell := by
  cases data with
  | mk dirtyFamily logStar CM L scale scaleFiber logStar_le_log =>
      subst hL
      exact {
        dirtyFamily := dirtyFamily
        logStar := logStar
        CM := CM
        scale := scale
        fibre := scaleFiber.fibre
        logStar_le_log := logStar_le_log }

/-- Project a shell-tied fibre-coding K.2.5 leaf to the fixed-shell proof-v4
boundary.  The shell-scale equality is carried by the input record. -/
def dirtyMultiplicityProofV4ShellFibreCodingFromShellFibreCodingInput
    {shell : FailingDyadicShell}
    (data : DirtyMultiplicityShellFibreCodingInputData shell) :
    DirtyMultiplicityProofV4ShellFibreCodingInputData shell :=
  dirtyMultiplicityProofV4ShellFibreCodingFromFinFibreCodingInput
    data.coding data.L_eq

/--
Proof-v4 K.2.5 construction route for the dirty multiplicity leaf.

The strongest concrete route is to build a fixed-shell Fin-labelled
fibre-coding certificate; the existing local-geometry factory then projects the
per-scale fibre bound consumed by the Appendix N endpoint.
-/
def dirtyMultiplicityProofV4ShellFibreFromCoding
    {shell : FailingDyadicShell}
    (data : DirtyMultiplicityProofV4ShellFibreCodingInputData shell) :
    DirtyMultiplicityProofV4ShellFibreInputData shell :=
  data.toDirtyMultiplicityProofV4ShellFibreInputData

/-- Proof-v4 named route for Corollary K.2.5 at the stronger fibre-coding
boundary used by the preferred strict endpoint. -/
def dirtyMultiplicityProofV4ShellFibreCodingFromClosedK25
    {shell : FailingDyadicShell}
    (data : DirtyMultiplicityProofV4ShellFibreCodingInputData shell) :
    DirtyMultiplicityProofV4ShellFibreCodingInputData shell :=
  dirtyMultiplicityProofV4ShellFibreCodingFromInput data

/-- Proof-v4 named route for Corollary K.2.5: the cleaned dirty-boundary family,
its Fin-labelled arm/period scale map, and an explicit per-scale fibre coding
certificate assemble into the fixed-shell dirty multiplicity leaf. -/
def dirtyMultiplicityProofV4ShellFibreFromClosedK25
    {shell : FailingDyadicShell}
    (data : DirtyMultiplicityProofV4ShellFibreCodingInputData shell) :
    DirtyMultiplicityProofV4ShellFibreInputData shell :=
  dirtyMultiplicityProofV4ShellFibreFromCoding data

/-- Route from the separated K.2.5 range/fibre-coding certificates at the active
dyadic shell scale to the strongest fixed-shell dirty coding leaf.

The explicit range certificate is kept at the boundary to match the proof-v4
arm/period decomposition, while the Fin-labelled target type also makes the
range bound recoverable downstream. -/
def dirtyMultiplicityProofV4ShellFibreCodingFromFixedSeparated
    {shell : FailingDyadicShell}
    (dirtyFamily : Finset DirtyCrossing)
    (logStar : Nat -> Nat)
    (CM : Nat)
    (scale :
      DirtyCrossing ->
        Fin ((Nat.log 2 (Classical.choose shell.hXdyadic)) ^ 4))
    (_range :
      DirtyScaleRangeData dirtyFamily logStar CM
        (Classical.choose shell.hXdyadic)
        (Fin ((Nat.log 2 (Classical.choose shell.hXdyadic)) ^ 4))
        inferInstance scale)
    (fibreCoding :
      DirtyScaleFibreCodingData dirtyFamily logStar CM
        (Classical.choose shell.hXdyadic)
        (Fin ((Nat.log 2 (Classical.choose shell.hXdyadic)) ^ 4))
        inferInstance scale)
    (logStar_le_log :
      logStar (Classical.choose shell.hXdyadic) <=
        Nat.log 2 (Classical.choose shell.hXdyadic)) :
    DirtyMultiplicityProofV4ShellFibreCodingInputData shell where
  dirtyFamily := dirtyFamily
  logStar := logStar
  CM := CM
  scale := scale
  fibreCoding := fibreCoding
  logStar_le_log := logStar_le_log

/-- Relabel an arbitrary finite proof-v4 K.2.5 scale family by the canonical
`Fin ((log L)^4)` target required by the strict shell leaf.

The manuscript decomposition naturally supplies a scale label set together with
the range bound `card <= (log L)^4`; this constructor turns that finite range
certificate into an actual Fin-labelled scale map, while preserving the
per-scale fibre coding. -/
def dirtyMultiplicityProofV4ShellFibreCodingFromFiniteScaleRange
    {shell : FailingDyadicShell}
    {scaleLabel : Type} [DecidableEq scaleLabel]
    (dirtyFamily : Finset DirtyCrossing)
    (logStar : Nat -> Nat)
    (CM : Nat)
    (scale : DirtyCrossing -> scaleLabel)
    (scaleTarget_pos :
      0 < (Nat.log 2 (Classical.choose shell.hXdyadic)) ^ 4)
    (range :
      DirtyScaleRangeData dirtyFamily logStar CM
        (Classical.choose shell.hXdyadic) scaleLabel inferInstance scale)
    (fibreCoding :
      DirtyScaleFibreCodingData dirtyFamily logStar CM
        (Classical.choose shell.hXdyadic) scaleLabel inferInstance scale)
    (logStar_le_log :
      logStar (Classical.choose shell.hXdyadic) <=
        Nat.log 2 (Classical.choose shell.hXdyadic)) :
    DirtyMultiplicityProofV4ShellFibreCodingInputData shell := by
  classical
  let L := Classical.choose shell.hXdyadic
  let ScaleImage : Type := {y : scaleLabel // y ∈ dirtyFamily.image scale}
  have hcardScaleImage :
      Fintype.card ScaleImage = (dirtyFamily.image scale).card := by
    dsimp [ScaleImage]
    simp
  have hleScaleImage :
      Fintype.card ScaleImage <=
        Fintype.card (Fin ((Nat.log 2 L) ^ 4)) := by
    rw [hcardScaleImage]
    simpa [L] using range.scale_image_card
  let embed : ScaleImage ↪ Fin ((Nat.log 2 L) ^ 4) :=
    Classical.choice (Function.Embedding.nonempty_of_card_le hleScaleImage)
  let defaultScale : Fin ((Nat.log 2 L) ^ 4) := ⟨0, by simpa [L] using scaleTarget_pos⟩
  let scaleFin : DirtyCrossing -> Fin ((Nat.log 2 L) ^ 4) :=
    fun d =>
      if hd : d ∈ dirtyFamily then
        embed ⟨scale d, by exact Finset.mem_image.mpr ⟨d, hd, rfl⟩⟩
      else
        defaultScale
  refine
    { dirtyFamily := dirtyFamily
      logStar := logStar
      CM := CM
      scale := by
        simpa [L] using scaleFin
      fibreCoding := ?_
      logStar_le_log := logStar_le_log }
  refine
    { code := fibreCoding.code
      code_injective_on_fibre := ?_ }
  intro y _hy a ha b hb hcode
  have hya : scale a ∈ dirtyFamily.image scale :=
    Finset.mem_image.mpr ⟨a, ha.1, rfl⟩
  have hyb : scale b ∈ dirtyFamily.image scale :=
    Finset.mem_image.mpr ⟨b, hb.1, rfl⟩
  have hscaleFin_a :
      scaleFin a = embed ⟨scale a, hya⟩ := by
    simp [scaleFin, ha.1]
  have hscaleFin_b :
      scaleFin b = embed ⟨scale b, hyb⟩ := by
    simp [scaleFin, hb.1]
  have hemb :
      embed ⟨scale a, hya⟩ = embed ⟨scale b, hyb⟩ := by
    calc
      embed ⟨scale a, hya⟩ = scaleFin a := hscaleFin_a.symm
      _ = y := by
        simpa [L] using ha.2
      _ = scaleFin b := by
        simpa [L] using hb.2.symm
      _ = embed ⟨scale b, hyb⟩ := hscaleFin_b
  have hscale_eq : scale a = scale b := by
    exact congrArg Subtype.val (embed.injective hemb)
  exact
    fibreCoding.code_injective_on_fibre (scale a) hya
      ⟨ha.1, rfl⟩ ⟨hb.1, hscale_eq.symm⟩ hcode

/-- Relabel an arbitrary finite proof-v4 K.2.5 scale family by the canonical
`Fin ((log L)^4)` target, preserving only the per-scale fibre cardinal bound.

This is the direct bound-level version of
`dirtyMultiplicityProofV4ShellFibreCodingFromFiniteScaleRange`, matching the
literal conclusion of Corollary K.2.5 before an optional coding refinement is
chosen. -/
def dirtyMultiplicityProofV4ShellFibreFromFiniteScaleRange
    {shell : FailingDyadicShell}
    {scaleLabel : Type} [DecidableEq scaleLabel]
    (dirtyFamily : Finset DirtyCrossing)
    (logStar : Nat -> Nat)
    (CM : Nat)
    (scale : DirtyCrossing -> scaleLabel)
    (scaleTarget_pos :
      0 < (Nat.log 2 (Classical.choose shell.hXdyadic)) ^ 4)
    (range :
      DirtyScaleRangeData dirtyFamily logStar CM
        (Classical.choose shell.hXdyadic) scaleLabel inferInstance scale)
    (fibre :
      DirtyScaleFibreBoundData dirtyFamily logStar CM
        (Classical.choose shell.hXdyadic) scaleLabel inferInstance scale)
    (logStar_le_log :
      logStar (Classical.choose shell.hXdyadic) <=
        Nat.log 2 (Classical.choose shell.hXdyadic)) :
    DirtyMultiplicityProofV4ShellFibreInputData shell := by
  classical
  let L := Classical.choose shell.hXdyadic
  let ScaleImage : Type := {y : scaleLabel // y ∈ dirtyFamily.image scale}
  have hcardScaleImage :
      Fintype.card ScaleImage = (dirtyFamily.image scale).card := by
    dsimp [ScaleImage]
    simp
  have hleScaleImage :
      Fintype.card ScaleImage <=
        Fintype.card (Fin ((Nat.log 2 L) ^ 4)) := by
    rw [hcardScaleImage]
    simpa [L] using range.scale_image_card
  let embed : ScaleImage ↪ Fin ((Nat.log 2 L) ^ 4) :=
    Classical.choice (Function.Embedding.nonempty_of_card_le hleScaleImage)
  let defaultScale : Fin ((Nat.log 2 L) ^ 4) := ⟨0, by simpa [L] using scaleTarget_pos⟩
  let scaleFin : DirtyCrossing -> Fin ((Nat.log 2 L) ^ 4) :=
    fun d =>
      if hd : d ∈ dirtyFamily then
        embed ⟨scale d, by exact Finset.mem_image.mpr ⟨d, hd, rfl⟩⟩
      else
        defaultScale
  refine
    { dirtyFamily := dirtyFamily
      logStar := logStar
      CM := CM
      scale := by
        simpa [L] using scaleFin
      fibre := ?_
      logStar_le_log := logStar_le_log }
  refine
    { scale_fiber_le := ?_ }
  intro y hy
  have hyFin : y ∈ dirtyFamily.image scaleFin := by
    simpa [L] using hy
  rcases Finset.mem_image.1 hyFin with ⟨d0, hd0, hy0⟩
  have hscale_d0 : scale d0 ∈ dirtyFamily.image scale :=
    Finset.mem_image.mpr ⟨d0, hd0, rfl⟩
  have hy0' : scaleFin d0 = y := hy0
  have hsubset :
      (dirtyFamily.filter fun d => scaleFin d = y) ⊆
        (dirtyFamily.filter fun d => scale d = scale d0) := by
    intro d hd
    have hd_mem : d ∈ dirtyFamily := (Finset.mem_filter.1 hd).1
    have hd_y : scaleFin d = y := (Finset.mem_filter.1 hd).2
    have hscale_d : scale d ∈ dirtyFamily.image scale :=
      Finset.mem_image.mpr ⟨d, hd_mem, rfl⟩
    have hscaleFin_d :
        scaleFin d = embed ⟨scale d, hscale_d⟩ := by
      simp [scaleFin, hd_mem]
    have hscaleFin_d0 :
        scaleFin d0 = embed ⟨scale d0, hscale_d0⟩ := by
      simp [scaleFin, hd0]
    have hemb :
        embed ⟨scale d, hscale_d⟩ = embed ⟨scale d0, hscale_d0⟩ := by
      calc
        embed ⟨scale d, hscale_d⟩ = scaleFin d := hscaleFin_d.symm
        _ = y := hd_y
        _ = scaleFin d0 := hy0'.symm
        _ = embed ⟨scale d0, hscale_d0⟩ := hscaleFin_d0
    have hscale_eq : scale d = scale d0 := by
      exact congrArg Subtype.val (embed.injective hemb)
    exact Finset.mem_filter.2 ⟨hd_mem, hscale_eq⟩
  have hbound :
      (dirtyFamily.filter fun d => scaleFin d = y).card <=
        (logStar L) ^ CM := by
    exact (Finset.card_le_card hsubset).trans
      (fibre.scale_fiber_le (scale d0) hscale_d0)
  simpa [L] using hbound

/-- Classical version of `dirtyMultiplicityProofV4ShellFibreCodingFromFiniteScaleRange`.

The scale-label equality instance is chosen internally, matching proof-v4's
finite arm/period scale labels.  The provider still supplies the real K.2.5
content: the cleaned dirty family, the range bound, and per-scale fibre coding.
-/
def dirtyMultiplicityProofV4ShellFibreCodingFromClassicalFiniteScaleRange
    {shell : FailingDyadicShell}
    {scaleLabel : Type}
    (dirtyFamily : Finset DirtyCrossing)
    (logStar : Nat -> Nat)
    (CM : Nat)
    (scale : DirtyCrossing -> scaleLabel)
    (scaleTarget_pos :
      0 < (Nat.log 2 (Classical.choose shell.hXdyadic)) ^ 4)
    (range :
      ClassicalDirtyScaleRangeData dirtyFamily logStar CM
        (Classical.choose shell.hXdyadic) scaleLabel scale)
    (fibreCoding :
      ClassicalDirtyScaleFibreCodingData dirtyFamily logStar CM
        (Classical.choose shell.hXdyadic) scaleLabel scale)
    (logStar_le_log :
      logStar (Classical.choose shell.hXdyadic) <=
        Nat.log 2 (Classical.choose shell.hXdyadic)) :
    DirtyMultiplicityProofV4ShellFibreCodingInputData shell := by
  classical
  exact
    dirtyMultiplicityProofV4ShellFibreCodingFromFiniteScaleRange
      dirtyFamily logStar CM scale scaleTarget_pos
      range.toDirtyScaleRangeData
      fibreCoding.toDirtyScaleFibreCodingData
      logStar_le_log

/-- Classical bound-level version of
`dirtyMultiplicityProofV4ShellFibreFromFiniteScaleRange`.

The scale-label equality instance is chosen internally, matching proof-v4's
finite arm/period scale labels, and the provider supplies only the K.2.5
per-scale fibre cardinal bound. -/
def dirtyMultiplicityProofV4ShellFibreFromClassicalFiniteScaleRange
    {shell : FailingDyadicShell}
    {scaleLabel : Type}
    (dirtyFamily : Finset DirtyCrossing)
    (logStar : Nat -> Nat)
    (CM : Nat)
    (scale : DirtyCrossing -> scaleLabel)
    (scaleTarget_pos :
      0 < (Nat.log 2 (Classical.choose shell.hXdyadic)) ^ 4)
    (range :
      ClassicalDirtyScaleRangeData dirtyFamily logStar CM
        (Classical.choose shell.hXdyadic) scaleLabel scale)
    (fibre :
      ClassicalDirtyScaleFibreBoundData dirtyFamily logStar CM
        (Classical.choose shell.hXdyadic) scaleLabel scale)
    (logStar_le_log :
      logStar (Classical.choose shell.hXdyadic) <=
        Nat.log 2 (Classical.choose shell.hXdyadic)) :
    DirtyMultiplicityProofV4ShellFibreInputData shell := by
  classical
  exact
    dirtyMultiplicityProofV4ShellFibreFromFiniteScaleRange
      dirtyFamily logStar CM scale scaleTarget_pos
      range.toDirtyScaleRangeData
      fibre.toDirtyScaleFibreBoundData
      logStar_le_log

/-- The Appendix N start threshold makes the canonical K.2.5 scale target
nonempty: the carry-large conclusion gives a dyadic exponent at least `25`,
and hence a positive binary logarithm. -/
theorem dirtyScaleTarget_pos_of_appendixNChainCompressionStartThreshold_le
    {shell : FailingDyadicShell}
    (hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
          shell.hnonterm <= shell.X) :
    0 < (Nat.log 2 (Classical.choose shell.hXdyadic)) ^ 4 := by
  have hLarge :=
    carryLarge_of_appendixNChainCompressionStartThreshold_le hXge
  have hL_ge_two : 2 <= Classical.choose shell.hXdyadic := by
    omega
  exact Nat.pow_pos (Nat.log_pos Nat.one_lt_two hL_ge_two)

/-- Final-certificate friendly finite-scale route: the Appendix N start
threshold supplies the nonempty `Fin ((log L)^4)` target, so the provider only
has to supply the proof-v4 dirty family, finite scale range, fibre coding, and
log-star comparison. -/
def dirtyMultiplicityProofV4ShellFibreCodingFromAppendixNStartFiniteScaleRange
    {shell : FailingDyadicShell}
    (hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
          shell.hnonterm <= shell.X)
    {scaleLabel : Type} [DecidableEq scaleLabel]
    (dirtyFamily : Finset DirtyCrossing)
    (logStar : Nat -> Nat)
    (CM : Nat)
    (scale : DirtyCrossing -> scaleLabel)
    (range :
      DirtyScaleRangeData dirtyFamily logStar CM
        (Classical.choose shell.hXdyadic) scaleLabel inferInstance scale)
    (fibreCoding :
      DirtyScaleFibreCodingData dirtyFamily logStar CM
        (Classical.choose shell.hXdyadic) scaleLabel inferInstance scale)
    (logStar_le_log :
      logStar (Classical.choose shell.hXdyadic) <=
        Nat.log 2 (Classical.choose shell.hXdyadic)) :
    DirtyMultiplicityProofV4ShellFibreCodingInputData shell :=
  dirtyMultiplicityProofV4ShellFibreCodingFromFiniteScaleRange
    dirtyFamily logStar CM scale
    (dirtyScaleTarget_pos_of_appendixNChainCompressionStartThreshold_le hXge)
    range fibreCoding logStar_le_log

/-- Classical finite-scale route specialized to the Appendix N start threshold.
This is the closest current Lean boundary to the proof-v4 K.2.5 manuscript
data, whose scale labels are finite arm/period classes rather than an
already-chosen `Fin ((log L)^4)` label. -/
def dirtyMultiplicityProofV4ShellFibreCodingFromAppendixNStartClassicalFiniteScaleRange
    {shell : FailingDyadicShell}
    (hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
          shell.hnonterm <= shell.X)
    {scaleLabel : Type}
    (dirtyFamily : Finset DirtyCrossing)
    (logStar : Nat -> Nat)
    (CM : Nat)
    (scale : DirtyCrossing -> scaleLabel)
    (range :
      ClassicalDirtyScaleRangeData dirtyFamily logStar CM
        (Classical.choose shell.hXdyadic) scaleLabel scale)
    (fibreCoding :
      ClassicalDirtyScaleFibreCodingData dirtyFamily logStar CM
        (Classical.choose shell.hXdyadic) scaleLabel scale)
    (logStar_le_log :
      logStar (Classical.choose shell.hXdyadic) <=
        Nat.log 2 (Classical.choose shell.hXdyadic)) :
    DirtyMultiplicityProofV4ShellFibreCodingInputData shell :=
  dirtyMultiplicityProofV4ShellFibreCodingFromClassicalFiniteScaleRange
    dirtyFamily logStar CM scale
    (dirtyScaleTarget_pos_of_appendixNChainCompressionStartThreshold_le hXge)
    range fibreCoding logStar_le_log

/-- Bound-level classical finite-scale route specialized to the Appendix N
start threshold.  This is the direct proof-v4 K.2.5 boundary for the
manuscript-direct final surface, which consumes a per-scale fibre bound rather
than a stronger fibre-coding certificate. -/
def dirtyMultiplicityProofV4ShellFibreFromAppendixNStartClassicalFiniteScaleRange
    {shell : FailingDyadicShell}
    (hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
          shell.hnonterm <= shell.X)
    {scaleLabel : Type}
    (dirtyFamily : Finset DirtyCrossing)
    (logStar : Nat -> Nat)
    (CM : Nat)
    (scale : DirtyCrossing -> scaleLabel)
    (range :
      ClassicalDirtyScaleRangeData dirtyFamily logStar CM
        (Classical.choose shell.hXdyadic) scaleLabel scale)
    (fibre :
      ClassicalDirtyScaleFibreBoundData dirtyFamily logStar CM
        (Classical.choose shell.hXdyadic) scaleLabel scale)
    (logStar_le_log :
      logStar (Classical.choose shell.hXdyadic) <=
        Nat.log 2 (Classical.choose shell.hXdyadic)) :
    DirtyMultiplicityProofV4ShellFibreInputData shell :=
  dirtyMultiplicityProofV4ShellFibreFromClassicalFiniteScaleRange
    dirtyFamily logStar CM scale
    (dirtyScaleTarget_pos_of_appendixNChainCompressionStartThreshold_le hXge)
    range fibre logStar_le_log

/-- Appendix-N-start route from the literal proof-v4 K.2.5 scale-set and
per-scale fibre-coding data.  The finite scale-set bound supplies the
`(log L)^4` range certificate, and the fibre injections supply the
`(log* L)^CM` per-scale fibres. -/
def dirtyMultiplicityProofV4ShellFibreCodingFromAppendixNStartScaleSet
    {shell : FailingDyadicShell}
    (hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
          shell.hnonterm <= shell.X)
    {scaleLabel : Type}
    (dirtyFamily : Finset DirtyCrossing)
    (logStar : Nat -> Nat)
    (CM : Nat)
    (scale : DirtyCrossing -> scaleLabel)
    (scaleSet : Finset scaleLabel)
    (hscale_mem : ∀ d, d ∈ dirtyFamily -> scale d ∈ scaleSet)
    (hscale_card :
      scaleSet.card <= (Nat.log 2 (Classical.choose shell.hXdyadic)) ^ 4)
    (code : DirtyCrossing -> Fin ((logStar (Classical.choose shell.hXdyadic)) ^ CM))
    (hcode :
      ∀ y, y ∈ scaleSet ->
        Set.InjOn code {d | d ∈ dirtyFamily ∧ scale d = y})
    (logStar_le_log :
      logStar (Classical.choose shell.hXdyadic) <=
        Nat.log 2 (Classical.choose shell.hXdyadic)) :
    DirtyMultiplicityProofV4ShellFibreCodingInputData shell :=
  dirtyMultiplicityProofV4ShellFibreCodingFromAppendixNStartClassicalFiniteScaleRange
    hXge dirtyFamily logStar CM scale
    (ClassicalDirtyScaleRangeData.ofScaleSet
      scaleSet hscale_mem hscale_card)
    (ClassicalDirtyScaleFibreCodingData.ofScaleSet
      scaleSet hscale_mem code hcode)
    logStar_le_log

/-- Appendix-N-start route from the literal proof-v4 K.2.5 scale-set and
per-scale fibre cardinal bounds.  This is the bound-level manuscript-direct
version of `dirtyMultiplicityProofV4ShellFibreCodingFromAppendixNStartScaleSet`. -/
def dirtyMultiplicityProofV4ShellFibreFromAppendixNStartScaleSet
    {shell : FailingDyadicShell}
    (hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
          shell.hnonterm <= shell.X)
    {scaleLabel : Type}
    (dirtyFamily : Finset DirtyCrossing)
    (logStar : Nat -> Nat)
    (CM : Nat)
    (scale : DirtyCrossing -> scaleLabel)
    (scaleSet : Finset scaleLabel)
    (hscale_mem : ∀ d, d ∈ dirtyFamily -> scale d ∈ scaleSet)
    (hscale_card :
      scaleSet.card <= (Nat.log 2 (Classical.choose shell.hXdyadic)) ^ 4)
    (hfibre :
      letI : DecidableEq scaleLabel := Classical.decEq scaleLabel
      ∀ y, y ∈ scaleSet ->
        (dirtyFamily.filter fun d => scale d = y).card <=
          (logStar (Classical.choose shell.hXdyadic)) ^ CM)
    (logStar_le_log :
      logStar (Classical.choose shell.hXdyadic) <=
        Nat.log 2 (Classical.choose shell.hXdyadic)) :
    DirtyMultiplicityProofV4ShellFibreInputData shell :=
  dirtyMultiplicityProofV4ShellFibreFromAppendixNStartClassicalFiniteScaleRange
    hXge dirtyFamily logStar CM scale
    (ClassicalDirtyScaleRangeData.ofScaleSet
      scaleSet hscale_mem hscale_card)
    (ClassicalDirtyScaleFibreBoundData.ofScaleSet
      scaleSet hscale_mem hfibre)
    logStar_le_log

/-- Manuscript-shaped closed K.2.5 dirty-multiplicity data at one Appendix N
shell.

The scale labels are kept as an internal classical type, matching the arm/period
scale classes in proof_v4.  The provider supplies the cleaned dirty family, the
finite scale-range bound, the per-scale fibre coding, and the active-shell
`logStar` envelope; the Appendix N start threshold supplies the nonempty
canonical `Fin ((log L)^4)` target when this record is projected to the strict
provider field. -/
structure DirtyMultiplicityClosedK25ClassicalInputData
    (shell : FailingDyadicShell) where
  scaleLabel : Type
  dirtyFamily : Finset DirtyCrossing
  logStar : Nat -> Nat
  CM : Nat
  scale : DirtyCrossing -> scaleLabel
  range :
    ClassicalDirtyScaleRangeData dirtyFamily logStar CM
      (Classical.choose shell.hXdyadic) scaleLabel scale
  fibreCoding :
    ClassicalDirtyScaleFibreCodingData dirtyFamily logStar CM
      (Classical.choose shell.hXdyadic) scaleLabel scale
  logStar_le_log :
    logStar (Classical.choose shell.hXdyadic) <=
      Nat.log 2 (Classical.choose shell.hXdyadic)

/-- Bound-level manuscript-shaped K.2.5 dirty-multiplicity data at one
Appendix N shell.

This is the literal Corollary K.2.5 boundary: after the cleaned dirty family is
split into finite arm/period scale labels, each scale fibre is bounded by
`(logStar L)^CM`.  No auxiliary injection/coding certificate is required. -/
structure DirtyMultiplicityClosedK25ClassicalBoundInputData
    (shell : FailingDyadicShell) where
  scaleLabel : Type
  dirtyFamily : Finset DirtyCrossing
  logStar : Nat -> Nat
  CM : Nat
  scale : DirtyCrossing -> scaleLabel
  range :
    ClassicalDirtyScaleRangeData dirtyFamily logStar CM
      (Classical.choose shell.hXdyadic) scaleLabel scale
  fibre :
    ClassicalDirtyScaleFibreBoundData dirtyFamily logStar CM
      (Classical.choose shell.hXdyadic) scaleLabel scale
  logStar_le_log :
    logStar (Classical.choose shell.hXdyadic) <=
      Nat.log 2 (Classical.choose shell.hXdyadic)

namespace DirtyMultiplicityClosedK25ClassicalInputData

/-- Package the raw proof-v4 K.2.5 classical scale-range and fibre-coding
fields into the closed manuscript record used by the strict dirty provider. -/
def ofClassicalScaleFibreCoding
    {shell : FailingDyadicShell}
    {scaleLabel : Type}
    (dirtyFamily : Finset DirtyCrossing)
    (logStar : Nat -> Nat)
    (CM : Nat)
    (scale : DirtyCrossing -> scaleLabel)
    (range :
      ClassicalDirtyScaleRangeData dirtyFamily logStar CM
        (Classical.choose shell.hXdyadic) scaleLabel scale)
    (fibreCoding :
      ClassicalDirtyScaleFibreCodingData dirtyFamily logStar CM
        (Classical.choose shell.hXdyadic) scaleLabel scale)
    (logStar_le_log :
      logStar (Classical.choose shell.hXdyadic) <=
        Nat.log 2 (Classical.choose shell.hXdyadic)) :
    DirtyMultiplicityClosedK25ClassicalInputData shell where
  scaleLabel := scaleLabel
  dirtyFamily := dirtyFamily
  logStar := logStar
  CM := CM
  scale := scale
  range := range
  fibreCoding := fibreCoding
  logStar_le_log := logStar_le_log

/-- Package the literal proof-v4 K.2.5 scale-set and fibre-coding data into the
closed manuscript record used by the strict dirty provider. -/
def ofScaleSetFibreCoding
    {shell : FailingDyadicShell}
    {scaleLabel : Type}
    (dirtyFamily : Finset DirtyCrossing)
    (logStar : Nat -> Nat)
    (CM : Nat)
    (scale : DirtyCrossing -> scaleLabel)
    (scaleSet : Finset scaleLabel)
    (hscale_mem : ∀ d, d ∈ dirtyFamily -> scale d ∈ scaleSet)
    (hscale_card :
      scaleSet.card <= (Nat.log 2 (Classical.choose shell.hXdyadic)) ^ 4)
    (code : DirtyCrossing -> Fin ((logStar (Classical.choose shell.hXdyadic)) ^ CM))
    (hcode :
      ∀ y, y ∈ scaleSet ->
        Set.InjOn code {d | d ∈ dirtyFamily ∧ scale d = y})
    (logStar_le_log :
      logStar (Classical.choose shell.hXdyadic) <=
        Nat.log 2 (Classical.choose shell.hXdyadic)) :
    DirtyMultiplicityClosedK25ClassicalInputData shell :=
  DirtyMultiplicityClosedK25ClassicalInputData.ofClassicalScaleFibreCoding
    dirtyFamily logStar CM scale
    (ClassicalDirtyScaleRangeData.ofScaleSet
      scaleSet hscale_mem hscale_card)
    (ClassicalDirtyScaleFibreCodingData.ofScaleSet
      scaleSet hscale_mem code hcode)
    logStar_le_log

/-- Project the closed K.2.5 manuscript record to the strongest fixed-shell
dirty fibre-coding input consumed by the strict endpoint. -/
def toDirtyMultiplicityProofV4ShellFibreCodingInputData
    {shell : FailingDyadicShell}
    (hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
          shell.hnonterm <= shell.X)
    (data : DirtyMultiplicityClosedK25ClassicalInputData shell) :
    DirtyMultiplicityProofV4ShellFibreCodingInputData shell :=
  dirtyMultiplicityProofV4ShellFibreCodingFromAppendixNStartClassicalFiniteScaleRange
    hXge data.dirtyFamily data.logStar data.CM data.scale
    data.range data.fibreCoding data.logStar_le_log

/-- Forget the explicit K.2.5 fibre coding after deriving the per-scale fibre
bound required by older dirty multiplicity routes. -/
def toDirtyMultiplicityProofV4ShellFibreInputData
    {shell : FailingDyadicShell}
    (hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
          shell.hnonterm <= shell.X)
    (data : DirtyMultiplicityClosedK25ClassicalInputData shell) :
    DirtyMultiplicityProofV4ShellFibreInputData shell :=
  data.toDirtyMultiplicityProofV4ShellFibreCodingInputData hXge
    |>.toDirtyMultiplicityProofV4ShellFibreInputData

end DirtyMultiplicityClosedK25ClassicalInputData

namespace DirtyMultiplicityClosedK25ClassicalBoundInputData

/-- Package the raw proof-v4 K.2.5 classical scale-range and per-scale fibre
bound into the closed manuscript record used by the manuscript-direct dirty
provider. -/
def ofClassicalScaleFibreBound
    {shell : FailingDyadicShell}
    {scaleLabel : Type}
    (dirtyFamily : Finset DirtyCrossing)
    (logStar : Nat -> Nat)
    (CM : Nat)
    (scale : DirtyCrossing -> scaleLabel)
    (range :
      ClassicalDirtyScaleRangeData dirtyFamily logStar CM
        (Classical.choose shell.hXdyadic) scaleLabel scale)
    (fibre :
      ClassicalDirtyScaleFibreBoundData dirtyFamily logStar CM
        (Classical.choose shell.hXdyadic) scaleLabel scale)
    (logStar_le_log :
      logStar (Classical.choose shell.hXdyadic) <=
        Nat.log 2 (Classical.choose shell.hXdyadic)) :
    DirtyMultiplicityClosedK25ClassicalBoundInputData shell where
  scaleLabel := scaleLabel
  dirtyFamily := dirtyFamily
  logStar := logStar
  CM := CM
  scale := scale
  range := range
  fibre := fibre
  logStar_le_log := logStar_le_log

/-- Package the literal proof-v4 K.2.5 scale-set and per-scale fibre bounds
into the bound-level closed manuscript record. -/
def ofScaleSetFibreBound
    {shell : FailingDyadicShell}
    {scaleLabel : Type}
    (dirtyFamily : Finset DirtyCrossing)
    (logStar : Nat -> Nat)
    (CM : Nat)
    (scale : DirtyCrossing -> scaleLabel)
    (scaleSet : Finset scaleLabel)
    (hscale_mem : ∀ d, d ∈ dirtyFamily -> scale d ∈ scaleSet)
    (hscale_card :
      scaleSet.card <= (Nat.log 2 (Classical.choose shell.hXdyadic)) ^ 4)
    (hfibre :
      letI : DecidableEq scaleLabel := Classical.decEq scaleLabel
      ∀ y, y ∈ scaleSet ->
        (dirtyFamily.filter fun d => scale d = y).card <=
          (logStar (Classical.choose shell.hXdyadic)) ^ CM)
    (logStar_le_log :
      logStar (Classical.choose shell.hXdyadic) <=
        Nat.log 2 (Classical.choose shell.hXdyadic)) :
    DirtyMultiplicityClosedK25ClassicalBoundInputData shell :=
  DirtyMultiplicityClosedK25ClassicalBoundInputData.ofClassicalScaleFibreBound
    dirtyFamily logStar CM scale
    (ClassicalDirtyScaleRangeData.ofScaleSet
      scaleSet hscale_mem hscale_card)
    (ClassicalDirtyScaleFibreBoundData.ofScaleSet
      scaleSet hscale_mem hfibre)
    logStar_le_log

/-- Project the bound-level closed K.2.5 manuscript record to the fixed-shell
dirty fibre input consumed by the manuscript-direct final surface. -/
def toDirtyMultiplicityProofV4ShellFibreInputData
    {shell : FailingDyadicShell}
    (hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
          shell.hnonterm <= shell.X)
    (data : DirtyMultiplicityClosedK25ClassicalBoundInputData shell) :
    DirtyMultiplicityProofV4ShellFibreInputData shell :=
  dirtyMultiplicityProofV4ShellFibreFromAppendixNStartClassicalFiniteScaleRange
    hXge data.dirtyFamily data.logStar data.CM data.scale
    data.range data.fibre data.logStar_le_log

/-- Strengthen the literal K.2.5 per-scale cardinal bound to the strict
fibre-coding package by noncomputably choosing per-scale injections.

The extra target positivity is exactly the nonemptiness needed for the total
`DirtyCrossing -> Fin ((logStar L)^CM)` coding function outside active fibres. -/
def toClosedK25ClassicalInputData
    {shell : FailingDyadicShell}
    (data : DirtyMultiplicityClosedK25ClassicalBoundInputData shell)
    (target_pos :
      0 < (data.logStar (Classical.choose shell.hXdyadic)) ^ data.CM) :
    DirtyMultiplicityClosedK25ClassicalInputData shell where
  scaleLabel := data.scaleLabel
  dirtyFamily := data.dirtyFamily
  logStar := data.logStar
  CM := data.CM
  scale := data.scale
  range := data.range
  fibreCoding :=
    ClassicalDirtyScaleFibreBoundData.toClassicalDirtyScaleFibreCodingData
      data.fibre target_pos
  logStar_le_log := data.logStar_le_log

/-- Project the bound-level closed K.2.5 manuscript record to the preferred
strict fixed-shell dirty fibre-coding input. -/
def toDirtyMultiplicityProofV4ShellFibreCodingInputData
    {shell : FailingDyadicShell}
    (hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
          shell.hnonterm <= shell.X)
    (data : DirtyMultiplicityClosedK25ClassicalBoundInputData shell)
    (target_pos :
      0 < (data.logStar (Classical.choose shell.hXdyadic)) ^ data.CM) :
    DirtyMultiplicityProofV4ShellFibreCodingInputData shell :=
  DirtyMultiplicityClosedK25ClassicalInputData.toDirtyMultiplicityProofV4ShellFibreCodingInputData
    hXge
    (data.toClosedK25ClassicalInputData target_pos)

end DirtyMultiplicityClosedK25ClassicalBoundInputData

/-- Public proof-v4 K.2.5 route from the classical arm/period scale package to
the strict dirty fibre-coding provider. -/
def dirtyMultiplicityProofV4ShellFibreCodingFromClosedK25Classical
    {shell : FailingDyadicShell}
    (hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
          shell.hnonterm <= shell.X)
    (data : DirtyMultiplicityClosedK25ClassicalInputData shell) :
    DirtyMultiplicityProofV4ShellFibreCodingInputData shell :=
  data.toDirtyMultiplicityProofV4ShellFibreCodingInputData hXge

/-- Public proof-v4 K.2.5 route from the classical arm/period scale package to
the older fixed-shell dirty fibre provider. -/
def dirtyMultiplicityProofV4ShellFibreFromClosedK25Classical
    {shell : FailingDyadicShell}
    (hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
          shell.hnonterm <= shell.X)
    (data : DirtyMultiplicityClosedK25ClassicalInputData shell) :
    DirtyMultiplicityProofV4ShellFibreInputData shell :=
  data.toDirtyMultiplicityProofV4ShellFibreInputData hXge

/-- Public proof-v4 K.2.5 route from the bound-level classical arm/period scale
package to the manuscript-direct dirty fibre provider. -/
def dirtyMultiplicityProofV4ShellFibreFromClosedK25ClassicalBound
    {shell : FailingDyadicShell}
    (hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
          shell.hnonterm <= shell.X)
    (data : DirtyMultiplicityClosedK25ClassicalBoundInputData shell) :
    DirtyMultiplicityProofV4ShellFibreInputData shell :=
  data.toDirtyMultiplicityProofV4ShellFibreInputData hXge

/-- Public strict-provider route from the bound-level classical arm/period
scale package.  This is useful when K.2.5 has been formalized in its natural
cardinal-bound form and the strict endpoint requests a coding object. -/
def dirtyMultiplicityProofV4ShellFibreCodingFromClosedK25ClassicalBound
    {shell : FailingDyadicShell}
    (hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
          shell.hnonterm <= shell.X)
    (data : DirtyMultiplicityClosedK25ClassicalBoundInputData shell)
    (target_pos :
      0 < (data.logStar (Classical.choose shell.hXdyadic)) ^ data.CM) :
    DirtyMultiplicityProofV4ShellFibreCodingInputData shell :=
  data.toDirtyMultiplicityProofV4ShellFibreCodingInputData hXge target_pos

/-- Public strict-provider route from the raw proof-v4 K.2.5 classical
scale-range and fibre-coding fields. -/
def dirtyMultiplicityProofV4ShellFibreCodingFromRawClosedK25Classical
    {shell : FailingDyadicShell}
    (hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
          shell.hnonterm <= shell.X)
    {scaleLabel : Type}
    (dirtyFamily : Finset DirtyCrossing)
    (logStar : Nat -> Nat)
    (CM : Nat)
    (scale : DirtyCrossing -> scaleLabel)
    (range :
      ClassicalDirtyScaleRangeData dirtyFamily logStar CM
        (Classical.choose shell.hXdyadic) scaleLabel scale)
    (fibreCoding :
      ClassicalDirtyScaleFibreCodingData dirtyFamily logStar CM
        (Classical.choose shell.hXdyadic) scaleLabel scale)
    (logStar_le_log :
      logStar (Classical.choose shell.hXdyadic) <=
        Nat.log 2 (Classical.choose shell.hXdyadic)) :
    DirtyMultiplicityProofV4ShellFibreCodingInputData shell :=
  dirtyMultiplicityProofV4ShellFibreCodingFromClosedK25Classical hXge
    (DirtyMultiplicityClosedK25ClassicalInputData.ofClassicalScaleFibreCoding
      dirtyFamily logStar CM scale range fibreCoding logStar_le_log)

/-- Public manuscript-direct route from the raw proof-v4 K.2.5 classical
scale-range and per-scale fibre-bound fields. -/
def dirtyMultiplicityProofV4ShellFibreFromRawClosedK25ClassicalBound
    {shell : FailingDyadicShell}
    (hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
          shell.hnonterm <= shell.X)
    {scaleLabel : Type}
    (dirtyFamily : Finset DirtyCrossing)
    (logStar : Nat -> Nat)
    (CM : Nat)
    (scale : DirtyCrossing -> scaleLabel)
    (range :
      ClassicalDirtyScaleRangeData dirtyFamily logStar CM
        (Classical.choose shell.hXdyadic) scaleLabel scale)
    (fibre :
      ClassicalDirtyScaleFibreBoundData dirtyFamily logStar CM
        (Classical.choose shell.hXdyadic) scaleLabel scale)
    (logStar_le_log :
      logStar (Classical.choose shell.hXdyadic) <=
        Nat.log 2 (Classical.choose shell.hXdyadic)) :
    DirtyMultiplicityProofV4ShellFibreInputData shell :=
  dirtyMultiplicityProofV4ShellFibreFromClosedK25ClassicalBound hXge
    (DirtyMultiplicityClosedK25ClassicalBoundInputData.ofClassicalScaleFibreBound
      dirtyFamily logStar CM scale range fibre logStar_le_log)

/-- Public strict-provider route from raw K.2.5 scale-range and per-scale
fibre-bound fields, choosing the fibre coding noncomputably once the target is
known to be nonempty. -/
def dirtyMultiplicityProofV4ShellFibreCodingFromRawClosedK25ClassicalBound
    {shell : FailingDyadicShell}
    (hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
          shell.hnonterm <= shell.X)
    {scaleLabel : Type}
    (dirtyFamily : Finset DirtyCrossing)
    (logStar : Nat -> Nat)
    (CM : Nat)
    (scale : DirtyCrossing -> scaleLabel)
    (range :
      ClassicalDirtyScaleRangeData dirtyFamily logStar CM
        (Classical.choose shell.hXdyadic) scaleLabel scale)
    (fibre :
      ClassicalDirtyScaleFibreBoundData dirtyFamily logStar CM
        (Classical.choose shell.hXdyadic) scaleLabel scale)
    (logStar_le_log :
      logStar (Classical.choose shell.hXdyadic) <=
        Nat.log 2 (Classical.choose shell.hXdyadic))
    (target_pos :
      0 < (logStar (Classical.choose shell.hXdyadic)) ^ CM) :
    DirtyMultiplicityProofV4ShellFibreCodingInputData shell :=
  dirtyMultiplicityProofV4ShellFibreCodingFromClosedK25ClassicalBound hXge
    (DirtyMultiplicityClosedK25ClassicalBoundInputData.ofClassicalScaleFibreBound
      dirtyFamily logStar CM scale range fibre logStar_le_log)
    target_pos

/-- Route from the separated K.2.5 range/fibre certificates at the active
dyadic shell scale to the fixed-shell dirty leaf.

The explicit range certificate is retained at this construction boundary to
match the proof-v4 decomposition into dyadic arm/period pairs, although the
target `Fin ((log L)^4)` also lets the downstream factory rebuild the range
bound internally. -/
def dirtyMultiplicityProofV4ShellFibreFromFixedSeparated
    {shell : FailingDyadicShell}
    (dirtyFamily : Finset DirtyCrossing)
    (logStar : Nat -> Nat)
    (CM : Nat)
    (scale :
      DirtyCrossing ->
        Fin ((Nat.log 2 (Classical.choose shell.hXdyadic)) ^ 4))
    (_range :
      DirtyScaleRangeData dirtyFamily logStar CM
        (Classical.choose shell.hXdyadic)
        (Fin ((Nat.log 2 (Classical.choose shell.hXdyadic)) ^ 4))
        inferInstance scale)
    (fibre :
      DirtyScaleFibreBoundData dirtyFamily logStar CM
        (Classical.choose shell.hXdyadic)
        (Fin ((Nat.log 2 (Classical.choose shell.hXdyadic)) ^ 4))
        inferInstance scale)
    (logStar_le_log :
      logStar (Classical.choose shell.hXdyadic) <=
        Nat.log 2 (Classical.choose shell.hXdyadic)) :
    DirtyMultiplicityProofV4ShellFibreInputData shell where
  dirtyFamily := dirtyFamily
  logStar := logStar
  CM := CM
  scale := scale
  fibre := fibre
  logStar_le_log := logStar_le_log

/-- Remaining concrete K.2.5 data needed before a no-input dirty leaf provider
can be installed. -/
def dirtyMultiplicityProofV4ShellFibreOpenItems : List String :=
  [ "K.2.1 anchored first-dirty convention and cleaned dirty-boundary family",
    "K.2.3 fixed arm-period scale crossing-chain bound",
    "K.2.5 Fin-labelled arm/period scale map into (log L)^4 dyadic pairs",
    "per-scale fibre coding into Fin ((logStar L)^CM) and the active-shell logStar envelope" ]

theorem dirtyMultiplicityProofV4ShellFibreOpenItems_nonempty :
    dirtyMultiplicityProofV4ShellFibreOpenItems = [] -> False := by
  intro h
  simp [dirtyMultiplicityProofV4ShellFibreOpenItems] at h

theorem dirtyMultiplicityProofV4ShellFibreOpenItems_length :
    dirtyMultiplicityProofV4ShellFibreOpenItems.length = 4 := by
  rfl

theorem dirtyMultiplicityProofV4ShellFibreOpenItems_eq :
    dirtyMultiplicityProofV4ShellFibreOpenItems =
      [ "K.2.1 anchored first-dirty convention and cleaned dirty-boundary family",
        "K.2.3 fixed arm-period scale crossing-chain bound",
        "K.2.5 Fin-labelled arm/period scale map into (log L)^4 dyadic pairs",
        "per-scale fibre coding into Fin ((logStar L)^CM) and the active-shell logStar envelope" ] := by
  rfl

end

end Erdos260
