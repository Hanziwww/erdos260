import Mathlib
import Erdos260.AppendixK1_DensePack
import Erdos260.AppendixM
import Erdos260.CarryDataFactory
import Erdos260.DirtyCrossing

/-!
# Local K/M geometry factory

Appendices K and M provide the local geometric inputs used by the package
estimates: dense-marker covers, dirty-crossing multiplicity, clean-boundary
alternatives, semiperiodic overlap, prefix extension, and low transient tower
exit encoding.

The existing files contain the finite objects and the arithmetic wrappers.
This file keeps the local manuscript obligations as focused factory structures:
DensePack is consumed directly by the final phase data, while dirty
multiplicity and local-closure outcomes remain separately tracked K/M targets.
-/

namespace Erdos260

open Finset

noncomputable section

/-- DensePack K.1 data in the exact shape needed by `DensePackData`. -/
structure DensePackFactoryData (cStar ξ X : ℝ) where
  densePackPoints : Finset Nat
  markersCard : Nat
  spread : Nat
  cStarSmall : ℝ
  hcover :
    densePackPoints.card <= markersCard * (2 * spread + 1)
  hcount :
    (markersCard : ℝ) <= cStarSmall * X
  hsmall :
    cStarSmall * X * ((2 * spread + 1 : Nat) : ℝ) <= cStar * ξ * X / 6

/-- Convert K.1 DensePack factory data into the Phase-6 package data. -/
def DensePackFactoryData.toDensePackData
    {cStar ξ X : ℝ}
    (data : DensePackFactoryData cStar ξ X) :
    DensePackData cStar ξ X where
  densePackPoints := data.densePackPoints
  markersCard := data.markersCard
  spread := data.spread
  cStarSmall := data.cStarSmall
  hcover := data.hcover
  hcount := data.hcount
  hsmall := data.hsmall

/-- K.2.5 dyadic-pair/range count for one cleaned dirty family. -/
structure DirtyScaleRangeData
    (dirtyFamily : Finset DirtyCrossing) (logStar : Nat -> Nat) (CM L : Nat)
    (scaleLabel : Type) (decScaleLabel : DecidableEq scaleLabel)
    (scale : DirtyCrossing -> scaleLabel) where
  scale_image_card :
    letI : DecidableEq scaleLabel := decScaleLabel
    (dirtyFamily.image scale).card <= (Nat.log 2 L) ^ 4

/-- K.2.5 per-scale fibre multiplicity for one cleaned dirty family. -/
structure DirtyScaleFibreBoundData
    (dirtyFamily : Finset DirtyCrossing) (logStar : Nat -> Nat) (CM L : Nat)
    (scaleLabel : Type) (decScaleLabel : DecidableEq scaleLabel)
    (scale : DirtyCrossing -> scaleLabel) where
  scale_fiber_le :
    letI : DecidableEq scaleLabel := decScaleLabel
    forall y, y ∈ dirtyFamily.image scale ->
      (dirtyFamily.filter fun d => scale d = y).card <= (logStar L) ^ CM

/--
K.2.5 per-scale fibre coding certificate.

For every fixed scale label, the crossings in that fibre inject into a code set
of size `(logStar L)^CM`.  The usual per-scale cardinal bound is then a finite
set consequence, rather than a raw provider inequality.
-/
structure DirtyScaleFibreCodingData
    (dirtyFamily : Finset DirtyCrossing) (logStar : Nat -> Nat) (CM L : Nat)
    (scaleLabel : Type) (decScaleLabel : DecidableEq scaleLabel)
    (scale : DirtyCrossing -> scaleLabel) where
  code : DirtyCrossing -> Fin ((logStar L) ^ CM)
  code_injective_on_fibre :
    letI : DecidableEq scaleLabel := decScaleLabel
    forall y, y ∈ dirtyFamily.image scale ->
      Set.InjOn code {d | d ∈ dirtyFamily ∧ scale d = y}

namespace DirtyScaleFibreCodingData

/-- A per-scale fibre coding certificate implies the K.2.5 fibre cardinal bound. -/
def toDirtyScaleFibreBoundData
    {dirtyFamily : Finset DirtyCrossing} {logStar : Nat -> Nat} {CM L : Nat}
    {scaleLabel : Type} {decScaleLabel : DecidableEq scaleLabel}
    {scale : DirtyCrossing -> scaleLabel}
    (data :
      DirtyScaleFibreCodingData dirtyFamily logStar CM L scaleLabel decScaleLabel scale) :
    DirtyScaleFibreBoundData dirtyFamily logStar CM L scaleLabel decScaleLabel scale where
  scale_fiber_le := by
    letI : DecidableEq scaleLabel := decScaleLabel
    intro y hy
    let fibreSet := dirtyFamily.filter fun d => scale d = y
    have hinj : Set.InjOn data.code (↑fibreSet : Set DirtyCrossing) := by
      intro a ha b hb hcode
      have ha' : a ∈ dirtyFamily ∧ scale a = y := by
        simpa [fibreSet] using ha
      have hb' : b ∈ dirtyFamily ∧ scale b = y := by
        simpa [fibreSet] using hb
      exact data.code_injective_on_fibre y hy ha' hb' hcode
    calc
      fibreSet.card = (fibreSet.image data.code).card := by
        exact (Finset.card_image_of_injOn hinj).symm
      _ <= Fintype.card (Fin ((logStar L) ^ CM)) := by
        exact Finset.card_le_univ (fibreSet.image data.code)
      _ = (logStar L) ^ CM := by simp

end DirtyScaleFibreCodingData

/--
The K.2 dirty-crossing multiplicity envelope certificate for one cleaned dirty
family, split into the dyadic-pair range count and the per-pair fibre bound.
-/
structure DirtyScaleFiberData
    (dirtyFamily : Finset DirtyCrossing) (logStar : Nat -> Nat) (CM L : Nat)
    (scaleLabel : Type) (decScaleLabel : DecidableEq scaleLabel)
    (scale : DirtyCrossing -> scaleLabel) where
  range :
    DirtyScaleRangeData dirtyFamily logStar CM L scaleLabel decScaleLabel scale
  fibre :
    DirtyScaleFibreBoundData dirtyFamily logStar CM L scaleLabel decScaleLabel scale

/-- Project the K.2.5 dyadic-pair/range count from the split certificate. -/
theorem DirtyScaleFiberData.scale_image_card
    {dirtyFamily : Finset DirtyCrossing} {logStar : Nat -> Nat} {CM L : Nat}
    {scaleLabel : Type} {decScaleLabel : DecidableEq scaleLabel}
    {scale : DirtyCrossing -> scaleLabel}
    (data :
      DirtyScaleFiberData dirtyFamily logStar CM L scaleLabel decScaleLabel scale) :
    letI : DecidableEq scaleLabel := decScaleLabel
    (dirtyFamily.image scale).card <= (Nat.log 2 L) ^ 4 :=
  data.range.scale_image_card

/-- Project the K.2.5 per-scale fibre multiplicity from the split certificate. -/
theorem DirtyScaleFiberData.scale_fiber_le
    {dirtyFamily : Finset DirtyCrossing} {logStar : Nat -> Nat} {CM L : Nat}
    {scaleLabel : Type} {decScaleLabel : DecidableEq scaleLabel}
    {scale : DirtyCrossing -> scaleLabel}
    (data :
      DirtyScaleFiberData dirtyFamily logStar CM L scaleLabel decScaleLabel scale) :
    letI : DecidableEq scaleLabel := decScaleLabel
    forall y, y ∈ dirtyFamily.image scale ->
      (dirtyFamily.filter fun d => scale d = y).card <= (logStar L) ^ CM :=
  data.fibre.scale_fiber_le

/--
K.2.5 dyadic-pair/range count with scale-label decidability chosen internally.
This matches the manuscript package, where the finite scale labels are part of
the local geometry certificate rather than an external provider condition.
-/
structure ClassicalDirtyScaleRangeData
    (dirtyFamily : Finset DirtyCrossing) (logStar : Nat -> Nat) (CM L : Nat)
    (scaleLabel : Type) (scale : DirtyCrossing -> scaleLabel) where
  scale_image_card :
    letI : DecidableEq scaleLabel := Classical.decEq scaleLabel
    (dirtyFamily.image scale).card <= (Nat.log 2 L) ^ 4

namespace ClassicalDirtyScaleRangeData

/-- Build the internally decided range certificate from the manuscript's
finite arm/period scale set. -/
def ofScaleSet
    {dirtyFamily : Finset DirtyCrossing} {logStar : Nat -> Nat} {CM L : Nat}
    {scaleLabel : Type} {scale : DirtyCrossing -> scaleLabel}
    (scaleSet : Finset scaleLabel)
    (hscale_mem : ∀ d, d ∈ dirtyFamily -> scale d ∈ scaleSet)
    (hscale_card : scaleSet.card <= (Nat.log 2 L) ^ 4) :
    ClassicalDirtyScaleRangeData dirtyFamily logStar CM L scaleLabel scale where
  scale_image_card := by
    classical
    have himg_subset : dirtyFamily.image scale ⊆ scaleSet := by
      intro y hy
      rcases Finset.mem_image.1 hy with ⟨d, hd, rfl⟩
      exact hscale_mem d hd
    exact le_trans (Finset.card_le_card himg_subset) hscale_card

/-- Recover the generic range certificate using the internally chosen instance. -/
def toDirtyScaleRangeData
    {dirtyFamily : Finset DirtyCrossing} {logStar : Nat -> Nat} {CM L : Nat}
    {scaleLabel : Type} {scale : DirtyCrossing -> scaleLabel}
    (data : ClassicalDirtyScaleRangeData dirtyFamily logStar CM L scaleLabel scale) :
    DirtyScaleRangeData dirtyFamily logStar CM L scaleLabel
      (Classical.decEq scaleLabel) scale where
  scale_image_card := data.scale_image_card

end ClassicalDirtyScaleRangeData

/--
K.2.5 per-scale fibre multiplicity with scale-label decidability chosen
internally.
-/
structure ClassicalDirtyScaleFibreBoundData
    (dirtyFamily : Finset DirtyCrossing) (logStar : Nat -> Nat) (CM L : Nat)
    (scaleLabel : Type) (scale : DirtyCrossing -> scaleLabel) where
  scale_fiber_le :
    letI : DecidableEq scaleLabel := Classical.decEq scaleLabel
    forall y, y ∈ dirtyFamily.image scale ->
      (dirtyFamily.filter fun d => scale d = y).card <= (logStar L) ^ CM

namespace ClassicalDirtyScaleFibreBoundData

/-- Build the internally decided per-scale fibre certificate from a finite
manuscript scale set and fibre bounds on that set. -/
def ofScaleSet
    {dirtyFamily : Finset DirtyCrossing} {logStar : Nat -> Nat} {CM L : Nat}
    {scaleLabel : Type} {scale : DirtyCrossing -> scaleLabel}
    (scaleSet : Finset scaleLabel)
    (hscale_mem : ∀ d, d ∈ dirtyFamily -> scale d ∈ scaleSet)
    (hfibre :
      letI : DecidableEq scaleLabel := Classical.decEq scaleLabel
      ∀ y, y ∈ scaleSet ->
        (dirtyFamily.filter fun d => scale d = y).card <= (logStar L) ^ CM) :
    ClassicalDirtyScaleFibreBoundData dirtyFamily logStar CM L scaleLabel scale where
  scale_fiber_le := by
    classical
    intro y hy
    rcases Finset.mem_image.1 hy with ⟨d, hd, rfl⟩
    exact hfibre (scale d) (hscale_mem d hd)

/-- Recover the generic fibre certificate using the internally chosen instance. -/
def toDirtyScaleFibreBoundData
    {dirtyFamily : Finset DirtyCrossing} {logStar : Nat -> Nat} {CM L : Nat}
    {scaleLabel : Type} {scale : DirtyCrossing -> scaleLabel}
    (data :
      ClassicalDirtyScaleFibreBoundData dirtyFamily logStar CM L scaleLabel scale) :
    DirtyScaleFibreBoundData dirtyFamily logStar CM L scaleLabel
      (Classical.decEq scaleLabel) scale where
  scale_fiber_le := data.scale_fiber_le

end ClassicalDirtyScaleFibreBoundData

/--
K.2.5 per-scale fibre coding with scale-label decidability chosen internally.
This matches the manuscript convention that the finite arm/period scale labels
are part of the local certificate, not an externally fixed typeclass instance.
-/
structure ClassicalDirtyScaleFibreCodingData
    (dirtyFamily : Finset DirtyCrossing) (logStar : Nat -> Nat) (CM L : Nat)
    (scaleLabel : Type) (scale : DirtyCrossing -> scaleLabel) where
  code : DirtyCrossing -> Fin ((logStar L) ^ CM)
  code_injective_on_fibre :
    letI : DecidableEq scaleLabel := Classical.decEq scaleLabel
    forall y, y ∈ dirtyFamily.image scale ->
      Set.InjOn code {d | d ∈ dirtyFamily ∧ scale d = y}

namespace ClassicalDirtyScaleFibreCodingData

/-- Build the internally decided per-scale fibre-coding certificate from a
finite manuscript scale set and fibre injections on that set. -/
def ofScaleSet
    {dirtyFamily : Finset DirtyCrossing} {logStar : Nat -> Nat} {CM L : Nat}
    {scaleLabel : Type} {scale : DirtyCrossing -> scaleLabel}
    (scaleSet : Finset scaleLabel)
    (hscale_mem : ∀ d, d ∈ dirtyFamily -> scale d ∈ scaleSet)
    (code : DirtyCrossing -> Fin ((logStar L) ^ CM))
    (hcode :
      ∀ y, y ∈ scaleSet ->
        Set.InjOn code {d | d ∈ dirtyFamily ∧ scale d = y}) :
    ClassicalDirtyScaleFibreCodingData dirtyFamily logStar CM L scaleLabel scale where
  code := code
  code_injective_on_fibre := by
    classical
    intro y hy
    rcases Finset.mem_image.1 hy with ⟨d, hd, rfl⟩
    exact hcode (scale d) (hscale_mem d hd)

/-- Recover the generic fibre-coding certificate using the internally chosen
scale-label equality instance. -/
def toDirtyScaleFibreCodingData
    {dirtyFamily : Finset DirtyCrossing} {logStar : Nat -> Nat} {CM L : Nat}
    {scaleLabel : Type} {scale : DirtyCrossing -> scaleLabel}
    (data :
      ClassicalDirtyScaleFibreCodingData dirtyFamily logStar CM L
        scaleLabel scale) :
    DirtyScaleFibreCodingData dirtyFamily logStar CM L scaleLabel
      (Classical.decEq scaleLabel) scale where
  code := data.code
  code_injective_on_fibre := data.code_injective_on_fibre

/-- Project the per-scale fibre cardinal bound from the internally decided
fibre-coding certificate. -/
def toClassicalDirtyScaleFibreBoundData
    {dirtyFamily : Finset DirtyCrossing} {logStar : Nat -> Nat} {CM L : Nat}
    {scaleLabel : Type} {scale : DirtyCrossing -> scaleLabel}
    (data :
      ClassicalDirtyScaleFibreCodingData dirtyFamily logStar CM L
        scaleLabel scale) :
    ClassicalDirtyScaleFibreBoundData dirtyFamily logStar CM L scaleLabel scale where
  scale_fiber_le := by
    classical
    exact data.toDirtyScaleFibreCodingData.toDirtyScaleFibreBoundData.scale_fiber_le

end ClassicalDirtyScaleFibreCodingData

namespace ClassicalDirtyScaleFibreBoundData

/-- Noncomputably choose per-scale fibre codes from the cardinal K.2.5 bound.

The target `Fin ((logStar L)^CM)` must be nonempty because the coding record is
a total function on `DirtyCrossing`, even though the injectivity requirement is
only on dirty fibres. -/
def toClassicalDirtyScaleFibreCodingData
    {dirtyFamily : Finset DirtyCrossing} {logStar : Nat -> Nat} {CM L : Nat}
    {scaleLabel : Type} {scale : DirtyCrossing -> scaleLabel}
    (data :
      ClassicalDirtyScaleFibreBoundData dirtyFamily logStar CM L scaleLabel scale)
    (target_pos : 0 < (logStar L) ^ CM) :
    ClassicalDirtyScaleFibreCodingData dirtyFamily logStar CM L scaleLabel scale := by
  classical
  let N := (logStar L) ^ CM
  let FibreSet : scaleLabel -> Finset DirtyCrossing := fun y =>
    dirtyFamily.filter fun d => scale d = y
  have hcard_le : ∀ y : scaleLabel, Fintype.card (FibreSet y) <= N := by
    intro y
    rw [Fintype.card_coe (FibreSet y)]
    by_cases hy : y ∈ dirtyFamily.image scale
    · simpa [N, FibreSet] using data.scale_fiber_le y hy
    · have hempty : (FibreSet y).card = 0 := by
        apply Finset.card_eq_zero.mpr
        ext d
        simp [FibreSet]
        intro hd hscale
        exact hy (Finset.mem_image.mpr ⟨d, hd, hscale⟩)
      rw [hempty]
      exact Nat.zero_le N
  let embed : ∀ y : scaleLabel, (FibreSet y) ↪ Fin N := fun y =>
    Classical.choice (Function.Embedding.nonempty_of_card_le (by
      simpa using hcard_le y))
  let defaultCode : Fin N := ⟨0, by simpa [N] using target_pos⟩
  let localCode : scaleLabel -> DirtyCrossing -> Fin N := fun y d =>
    if hd : d ∈ FibreSet y then
      embed y ⟨d, hd⟩
    else
      defaultCode
  have localCode_injective_on_fibre :
      ∀ y : scaleLabel,
        Set.InjOn (localCode y) {d | d ∈ dirtyFamily ∧ scale d = y} := by
    intro y a ha b hb hcode
    have haF : a ∈ FibreSet y := by
      simpa [FibreSet] using ha
    have hbF : b ∈ FibreSet y := by
      simpa [FibreSet] using hb
    have hcode_a : localCode y a = embed y ⟨a, haF⟩ := by
      simp [localCode, haF]
    have hcode_b : localCode y b = embed y ⟨b, hbF⟩ := by
      simp [localCode, hbF]
    have hemb : embed y ⟨a, haF⟩ = embed y ⟨b, hbF⟩ := by
      calc
        embed y ⟨a, haF⟩ = localCode y a := hcode_a.symm
        _ = localCode y b := hcode
        _ = embed y ⟨b, hbF⟩ := hcode_b
    exact congrArg Subtype.val ((embed y).injective hemb)
  let code : DirtyCrossing -> Fin N := fun d => localCode (scale d) d
  exact {
    code := by
      simpa [N] using code
    code_injective_on_fibre := by
      intro y _hy a ha b hb hcode
      have ha' : a ∈ dirtyFamily ∧ scale a = y := by
        simpa using ha
      have hb' : b ∈ dirtyFamily ∧ scale b = y := by
        simpa using hb
      exact localCode_injective_on_fibre y ha' hb' (by
        simpa [code, ha'.2, hb'.2] using hcode) }

end ClassicalDirtyScaleFibreBoundData

/--
K.2.5 split dirty-scale certificate with the scale-label equality instance
kept internal to the certificate.
-/
structure ClassicalDirtyScaleFiberData
    (dirtyFamily : Finset DirtyCrossing) (logStar : Nat -> Nat) (CM L : Nat)
    (scaleLabel : Type) (scale : DirtyCrossing -> scaleLabel) where
  range :
    ClassicalDirtyScaleRangeData dirtyFamily logStar CM L scaleLabel scale
  fibre :
    ClassicalDirtyScaleFibreBoundData dirtyFamily logStar CM L scaleLabel scale

namespace ClassicalDirtyScaleFiberData

/-- Build the split classical K.2.5 certificate directly from the manuscript's
finite scale set and per-scale fibre bounds. -/
def ofScaleSet
    {dirtyFamily : Finset DirtyCrossing} {logStar : Nat -> Nat} {CM L : Nat}
    {scaleLabel : Type} {scale : DirtyCrossing -> scaleLabel}
    (scaleSet : Finset scaleLabel)
    (hscale_mem : ∀ d, d ∈ dirtyFamily -> scale d ∈ scaleSet)
    (hscale_card : scaleSet.card <= (Nat.log 2 L) ^ 4)
    (hfibre :
      letI : DecidableEq scaleLabel := Classical.decEq scaleLabel
      ∀ y, y ∈ scaleSet ->
        (dirtyFamily.filter fun d => scale d = y).card <= (logStar L) ^ CM) :
    ClassicalDirtyScaleFiberData dirtyFamily logStar CM L scaleLabel scale where
  range :=
    ClassicalDirtyScaleRangeData.ofScaleSet
      scaleSet hscale_mem hscale_card
  fibre :=
    ClassicalDirtyScaleFibreBoundData.ofScaleSet
      scaleSet hscale_mem hfibre

/-- Recover the generic split dirty-scale certificate. -/
def toDirtyScaleFiberData
    {dirtyFamily : Finset DirtyCrossing} {logStar : Nat -> Nat} {CM L : Nat}
    {scaleLabel : Type} {scale : DirtyCrossing -> scaleLabel}
    (data : ClassicalDirtyScaleFiberData dirtyFamily logStar CM L scaleLabel scale) :
    DirtyScaleFiberData dirtyFamily logStar CM L scaleLabel
      (Classical.decEq scaleLabel) scale where
  range := data.range.toDirtyScaleRangeData
  fibre := data.fibre.toDirtyScaleFibreBoundData

/-- Project the internally decided K.2.5 dyadic-pair/range count. -/
theorem scale_image_card
    {dirtyFamily : Finset DirtyCrossing} {logStar : Nat -> Nat} {CM L : Nat}
    {scaleLabel : Type} {scale : DirtyCrossing -> scaleLabel}
    (data : ClassicalDirtyScaleFiberData dirtyFamily logStar CM L scaleLabel scale) :
    letI : DecidableEq scaleLabel := Classical.decEq scaleLabel
    (dirtyFamily.image scale).card <= (Nat.log 2 L) ^ 4 :=
  data.range.scale_image_card

/-- Project the internally decided K.2.5 per-scale fibre multiplicity. -/
theorem scale_fiber_le
    {dirtyFamily : Finset DirtyCrossing} {logStar : Nat -> Nat} {CM L : Nat}
    {scaleLabel : Type} {scale : DirtyCrossing -> scaleLabel}
    (data : ClassicalDirtyScaleFiberData dirtyFamily logStar CM L scaleLabel scale) :
    letI : DecidableEq scaleLabel := Classical.decEq scaleLabel
    forall y, y ∈ dirtyFamily.image scale ->
      (dirtyFamily.filter fun d => scale d = y).card <= (logStar L) ^ CM :=
  data.fibre.scale_fiber_le

end ClassicalDirtyScaleFiberData

/--
The K.2 dirty-crossing multiplicity envelope for one cleaned dirty family.
The scale/fibre decomposition is carried as its own proof-v4 certificate.
-/
structure DirtyMultiplicityData where
  dirtyFamily : Finset DirtyCrossing
  logStar : Nat -> Nat
  CM : Nat
  L : Nat
  scale : DirtyCrossing -> Fin ((Nat.log 2 L) ^ 4)
  scaleFiber_input :
    DirtyScaleFibreBoundData dirtyFamily logStar CM L
      (Fin ((Nat.log 2 L) ^ 4)) inferInstance scale
  logStar_le_log :
    logStar L <= Nat.log 2 L

/-- Build the K.2.5 dirty-multiplicity package from a Fin-labelled per-scale
fibre certificate.  The dyadic-pair range bound is then carried by the target
`Fin ((log L)^4)` label type itself. -/
def DirtyMultiplicityData.ofFinScaleFibreBound
    {dirtyFamily : Finset DirtyCrossing} {logStar : Nat -> Nat} {CM L : Nat}
    {scale : DirtyCrossing -> Fin ((Nat.log 2 L) ^ 4)}
    (scaleFiber_input :
      DirtyScaleFibreBoundData dirtyFamily logStar CM L
        (Fin ((Nat.log 2 L) ^ 4)) inferInstance scale)
    (logStar_le_log : logStar L <= Nat.log 2 L) :
    DirtyMultiplicityData where
  dirtyFamily := dirtyFamily
  logStar := logStar
  CM := CM
  L := L
  scale := scale
  scaleFiber_input := scaleFiber_input
  logStar_le_log := logStar_le_log

/-- Build the K.2.5 dirty-multiplicity package from the split Fin-labelled
scale/fibre certificate used by proof-v4. -/
def DirtyMultiplicityData.ofFinScaleFiberData
    {dirtyFamily : Finset DirtyCrossing} {logStar : Nat -> Nat} {CM L : Nat}
    {scale : DirtyCrossing -> Fin ((Nat.log 2 L) ^ 4)}
    (scaleFiber :
      DirtyScaleFiberData dirtyFamily logStar CM L
        (Fin ((Nat.log 2 L) ^ 4)) inferInstance scale)
    (logStar_le_log : logStar L <= Nat.log 2 L) :
  DirtyMultiplicityData :=
  DirtyMultiplicityData.ofFinScaleFibreBound scaleFiber.fibre logStar_le_log

/--
K.2.5 dirty-multiplicity leaf in the proof-v4 split scale/fibre form before it
is packed as `DirtyMultiplicityData`.
-/
structure DirtyMultiplicityInputData where
  dirtyFamily : Finset DirtyCrossing
  logStar : Nat -> Nat
  CM : Nat
  L : Nat
  scale : DirtyCrossing -> Fin ((Nat.log 2 L) ^ 4)
  scaleFiber :
    DirtyScaleFiberData dirtyFamily logStar CM L
      (Fin ((Nat.log 2 L) ^ 4)) inferInstance scale
  logStar_le_log :
    logStar L <= Nat.log 2 L

/--
K.2.5 dirty-multiplicity leaf in the sharpened Fin-labelled form.  Once the
scale map lands in `Fin ((log L)^4)`, the dyadic range count is automatic; the
only remaining manuscript content is the per-scale fibre multiplicity.
-/
structure DirtyMultiplicityFinFibreInputData where
  dirtyFamily : Finset DirtyCrossing
  logStar : Nat -> Nat
  CM : Nat
  L : Nat
  scale : DirtyCrossing -> Fin ((Nat.log 2 L) ^ 4)
  fibre :
    DirtyScaleFibreBoundData dirtyFamily logStar CM L
      (Fin ((Nat.log 2 L) ^ 4)) inferInstance scale
  logStar_le_log :
    logStar L <= Nat.log 2 L

/--
K.2.5 dirty-multiplicity leaf in Fin-labelled fibre-coding form.  The scale
range is closed by the finite target type, and each scale fibre is bounded by an
explicit injection into `Fin ((logStar L)^CM)`.
-/
structure DirtyMultiplicityFinFibreCodingInputData where
  dirtyFamily : Finset DirtyCrossing
  logStar : Nat -> Nat
  CM : Nat
  L : Nat
  scale : DirtyCrossing -> Fin ((Nat.log 2 L) ^ 4)
  fibreCoding :
    DirtyScaleFibreCodingData dirtyFamily logStar CM L
      (Fin ((Nat.log 2 L) ^ 4)) inferInstance scale
  logStar_le_log :
    logStar L <= Nat.log 2 L

/--
K.2.5 dirty-multiplicity leaf tied to the active dyadic shell.  It keeps the
same Fin-labelled fibre-coding content, but locks the local scale `L` to the
dyadic exponent of the failing shell instead of leaving it as a free provider
parameter.
-/
structure DirtyMultiplicityShellFibreCodingInputData
    (shell : FailingDyadicShell) where
  coding : DirtyMultiplicityFinFibreCodingInputData
  L_eq : coding.L = Classical.choose shell.hXdyadic

/--
K.2.5 dirty-multiplicity leaf with the dyadic shell scale fixed
definitionally.  This removes the proof-only `L_eq` field from the strongest
provider surface while keeping the same Fin-labelled fibre-coding content.
-/
structure DirtyMultiplicityProofV4ShellFibreCodingInputData
    (shell : FailingDyadicShell) where
  dirtyFamily : Finset DirtyCrossing
  logStar : Nat -> Nat
  CM : Nat
  scale :
    DirtyCrossing -> Fin ((Nat.log 2 (Classical.choose shell.hXdyadic)) ^ 4)
  fibreCoding :
    DirtyScaleFibreCodingData dirtyFamily logStar CM
      (Classical.choose shell.hXdyadic)
      (Fin ((Nat.log 2 (Classical.choose shell.hXdyadic)) ^ 4))
      inferInstance scale
  logStar_le_log :
    logStar (Classical.choose shell.hXdyadic) <=
      Nat.log 2 (Classical.choose shell.hXdyadic)

/--
K.2.5 dirty-multiplicity leaf with the dyadic shell scale fixed
definitionally and only the per-scale fibre cardinal bound exposed.  This is
the part consumed by the cleaned dirty envelope; the stronger explicit
fibre-coding certificate remains available as a compatibility refinement.
-/
structure DirtyMultiplicityProofV4ShellFibreInputData
    (shell : FailingDyadicShell) where
  dirtyFamily : Finset DirtyCrossing
  logStar : Nat -> Nat
  CM : Nat
  scale :
    DirtyCrossing -> Fin ((Nat.log 2 (Classical.choose shell.hXdyadic)) ^ 4)
  fibre :
    DirtyScaleFibreBoundData dirtyFamily logStar CM
      (Classical.choose shell.hXdyadic)
      (Fin ((Nat.log 2 (Classical.choose shell.hXdyadic)) ^ 4))
      inferInstance scale
  logStar_le_log :
    logStar (Classical.choose shell.hXdyadic) <=
      Nat.log 2 (Classical.choose shell.hXdyadic)

/--
K.2.5 dirty-multiplicity leaf with the two scale/fibre subcertificates exposed
separately: the dyadic-pair range count and the per-scale fibre bound.
-/
structure DirtyMultiplicitySeparatedInputData where
  dirtyFamily : Finset DirtyCrossing
  logStar : Nat -> Nat
  CM : Nat
  L : Nat
  scale : DirtyCrossing -> Fin ((Nat.log 2 L) ^ 4)
  range :
    DirtyScaleRangeData dirtyFamily logStar CM L
      (Fin ((Nat.log 2 L) ^ 4)) inferInstance scale
  fibre :
    DirtyScaleFibreBoundData dirtyFamily logStar CM L
      (Fin ((Nat.log 2 L) ^ 4)) inferInstance scale
  logStar_le_log :
    logStar L <= Nat.log 2 L

namespace DirtyMultiplicityInputData

/-- Convert the split K.2.5 dirty-multiplicity leaf to the grounded envelope. -/
def toDirtyMultiplicityData
    (data : DirtyMultiplicityInputData) : DirtyMultiplicityData :=
  DirtyMultiplicityData.ofFinScaleFiberData data.scaleFiber data.logStar_le_log

end DirtyMultiplicityInputData

namespace DirtyMultiplicityFinFibreInputData

/-- The Fin-labelled target closes the K.2.5 range count by cardinality of
`Fin ((log L)^4)`. -/
def range
    (data : DirtyMultiplicityFinFibreInputData) :
    DirtyScaleRangeData data.dirtyFamily data.logStar data.CM data.L
      (Fin ((Nat.log 2 data.L) ^ 4)) inferInstance data.scale where
  scale_image_card := by
    calc
      (data.dirtyFamily.image data.scale).card <=
          Fintype.card (Fin ((Nat.log 2 data.L) ^ 4)) :=
        Finset.card_le_univ (data.dirtyFamily.image data.scale)
      _ = (Nat.log 2 data.L) ^ 4 := by simp

/-- Recover the older split scale/fibre leaf.  The range component is now
derived from the Fin-labelled scale type, not supplied by the provider. -/
def toDirtyMultiplicityInputData
    (data : DirtyMultiplicityFinFibreInputData) :
    DirtyMultiplicityInputData where
  dirtyFamily := data.dirtyFamily
  logStar := data.logStar
  CM := data.CM
  L := data.L
  scale := data.scale
  scaleFiber := {
    range := data.range
    fibre := data.fibre }
  logStar_le_log := data.logStar_le_log

/-- Convert the sharpened Fin-labelled fibre leaf to the grounded dirty
multiplicity package. -/
def toDirtyMultiplicityData
    (data : DirtyMultiplicityFinFibreInputData) : DirtyMultiplicityData :=
  DirtyMultiplicityData.ofFinScaleFibreBound data.fibre data.logStar_le_log

end DirtyMultiplicityFinFibreInputData

namespace DirtyMultiplicityFinFibreCodingInputData

/-- Project the K.2.5 per-scale fibre bound from the fibre-coding certificate. -/
def fibre
    (data : DirtyMultiplicityFinFibreCodingInputData) :
    DirtyScaleFibreBoundData data.dirtyFamily data.logStar data.CM data.L
      (Fin ((Nat.log 2 data.L) ^ 4)) inferInstance data.scale :=
  data.fibreCoding.toDirtyScaleFibreBoundData

/-- Forget the explicit fibre coding after deriving the per-scale fibre bound. -/
def toDirtyMultiplicityFinFibreInputData
    (data : DirtyMultiplicityFinFibreCodingInputData) :
    DirtyMultiplicityFinFibreInputData where
  dirtyFamily := data.dirtyFamily
  logStar := data.logStar
  CM := data.CM
  L := data.L
  scale := data.scale
  fibre := data.fibre
  logStar_le_log := data.logStar_le_log

/-- Convert the Fin-labelled fibre-coding leaf to the grounded dirty
multiplicity package. -/
def toDirtyMultiplicityData
    (data : DirtyMultiplicityFinFibreCodingInputData) : DirtyMultiplicityData :=
  data.toDirtyMultiplicityFinFibreInputData.toDirtyMultiplicityData

end DirtyMultiplicityFinFibreCodingInputData

namespace DirtyMultiplicityShellFibreCodingInputData

/-- Forget the shell scale lock and recover the Fin-labelled fibre-coding leaf. -/
def toDirtyMultiplicityFinFibreCodingInputData
    {shell : FailingDyadicShell}
    (data : DirtyMultiplicityShellFibreCodingInputData shell) :
    DirtyMultiplicityFinFibreCodingInputData :=
  data.coding

/-- Project the K.2.5 per-scale fibre bound from the shell-tied coding leaf. -/
def fibre
    {shell : FailingDyadicShell}
    (data : DirtyMultiplicityShellFibreCodingInputData shell) :
    DirtyScaleFibreBoundData data.coding.dirtyFamily data.coding.logStar
      data.coding.CM data.coding.L
      (Fin ((Nat.log 2 data.coding.L) ^ 4)) inferInstance data.coding.scale :=
  data.coding.fibre

/-- Forget the explicit fibre coding after deriving the per-scale fibre bound. -/
def toDirtyMultiplicityFinFibreInputData
    {shell : FailingDyadicShell}
    (data : DirtyMultiplicityShellFibreCodingInputData shell) :
    DirtyMultiplicityFinFibreInputData :=
  data.coding.toDirtyMultiplicityFinFibreInputData

/-- Convert the shell-tied fibre-coding leaf to the grounded dirty multiplicity
package. -/
def toDirtyMultiplicityData
    {shell : FailingDyadicShell}
    (data : DirtyMultiplicityShellFibreCodingInputData shell) :
    DirtyMultiplicityData :=
  data.coding.toDirtyMultiplicityData

end DirtyMultiplicityShellFibreCodingInputData

namespace DirtyMultiplicityProofV4ShellFibreCodingInputData

/-- Recover the previous shell-tied dirty leaf; the scale equality is now
definitionally true. -/
def toDirtyMultiplicityShellFibreCodingInputData
    {shell : FailingDyadicShell}
    (data : DirtyMultiplicityProofV4ShellFibreCodingInputData shell) :
    DirtyMultiplicityShellFibreCodingInputData shell where
  coding := {
    dirtyFamily := data.dirtyFamily
    logStar := data.logStar
    CM := data.CM
    L := Classical.choose shell.hXdyadic
    scale := data.scale
    fibreCoding := data.fibreCoding
    logStar_le_log := data.logStar_le_log }
  L_eq := rfl

/-- Forget the definitional shell scale and recover the Fin-labelled
fibre-coding leaf. -/
def toDirtyMultiplicityFinFibreCodingInputData
    {shell : FailingDyadicShell}
    (data : DirtyMultiplicityProofV4ShellFibreCodingInputData shell) :
    DirtyMultiplicityFinFibreCodingInputData :=
  data.toDirtyMultiplicityShellFibreCodingInputData
    |>.toDirtyMultiplicityFinFibreCodingInputData

/-- Project the K.2.5 per-scale fibre bound from the fixed-shell coding leaf. -/
def fibre
    {shell : FailingDyadicShell}
    (data : DirtyMultiplicityProofV4ShellFibreCodingInputData shell) :
    DirtyScaleFibreBoundData data.dirtyFamily data.logStar data.CM
      (Classical.choose shell.hXdyadic)
      (Fin ((Nat.log 2 (Classical.choose shell.hXdyadic)) ^ 4)) inferInstance
      data.scale :=
  data.fibreCoding.toDirtyScaleFibreBoundData

/-- Forget the explicit fibre coding after deriving the per-scale fibre bound. -/
def toDirtyMultiplicityFinFibreInputData
    {shell : FailingDyadicShell}
    (data : DirtyMultiplicityProofV4ShellFibreCodingInputData shell) :
    DirtyMultiplicityFinFibreInputData :=
  data.toDirtyMultiplicityFinFibreCodingInputData
    |>.toDirtyMultiplicityFinFibreInputData

/-- Convert the fixed-shell fibre-coding leaf to the grounded dirty
multiplicity package. -/
def toDirtyMultiplicityData
    {shell : FailingDyadicShell}
    (data : DirtyMultiplicityProofV4ShellFibreCodingInputData shell) :
    DirtyMultiplicityData :=
  data.toDirtyMultiplicityFinFibreCodingInputData.toDirtyMultiplicityData

/-- Forget the explicit fibre coding and keep only the per-scale fibre bound. -/
def toDirtyMultiplicityProofV4ShellFibreInputData
    {shell : FailingDyadicShell}
    (data : DirtyMultiplicityProofV4ShellFibreCodingInputData shell) :
    DirtyMultiplicityProofV4ShellFibreInputData shell where
  dirtyFamily := data.dirtyFamily
  logStar := data.logStar
  CM := data.CM
  scale := data.scale
  fibre := data.fibre
  logStar_le_log := data.logStar_le_log

end DirtyMultiplicityProofV4ShellFibreCodingInputData

namespace DirtyMultiplicityProofV4ShellFibreInputData

/-- Recover the Fin-labelled fibre leaf with the dyadic scale fixed
definitionally by the shell. -/
def toDirtyMultiplicityFinFibreInputData
    {shell : FailingDyadicShell}
    (data : DirtyMultiplicityProofV4ShellFibreInputData shell) :
    DirtyMultiplicityFinFibreInputData where
  dirtyFamily := data.dirtyFamily
  logStar := data.logStar
  CM := data.CM
  L := Classical.choose shell.hXdyadic
  scale := data.scale
  fibre := data.fibre
  logStar_le_log := data.logStar_le_log

/-- Convert the fixed-shell fibre-bound leaf to the grounded dirty
multiplicity package. -/
def toDirtyMultiplicityData
    {shell : FailingDyadicShell}
    (data : DirtyMultiplicityProofV4ShellFibreInputData shell) :
    DirtyMultiplicityData :=
  data.toDirtyMultiplicityFinFibreInputData.toDirtyMultiplicityData

end DirtyMultiplicityProofV4ShellFibreInputData

namespace DirtyMultiplicitySeparatedInputData

/-- Assemble the separated K.2.5 dirty-multiplicity leaf from the dyadic
scale-range and per-scale fibre certificates. -/
def ofClosedK25
    (dirtyFamily : Finset DirtyCrossing)
    (logStar : Nat -> Nat)
    (CM L : Nat)
    (scale : DirtyCrossing -> Fin ((Nat.log 2 L) ^ 4))
    (range :
      DirtyScaleRangeData dirtyFamily logStar CM L
        (Fin ((Nat.log 2 L) ^ 4)) inferInstance scale)
    (fibre :
      DirtyScaleFibreBoundData dirtyFamily logStar CM L
        (Fin ((Nat.log 2 L) ^ 4)) inferInstance scale)
    (logStar_le_log : logStar L <= Nat.log 2 L) :
    DirtyMultiplicitySeparatedInputData where
  dirtyFamily := dirtyFamily
  logStar := logStar
  CM := CM
  L := L
  scale := scale
  range := range
  fibre := fibre
  logStar_le_log := logStar_le_log

/-- Bundle the separated K.2.5 range and fibre leaves into the existing split
scale/fibre input. -/
def toDirtyMultiplicityInputData
    (data : DirtyMultiplicitySeparatedInputData) :
    DirtyMultiplicityInputData where
  dirtyFamily := data.dirtyFamily
  logStar := data.logStar
  CM := data.CM
  L := data.L
  scale := data.scale
  scaleFiber := {
    range := data.range
    fibre := data.fibre }
  logStar_le_log := data.logStar_le_log

/-- Convert the separated K.2.5 dirty-multiplicity leaf to the grounded
envelope. -/
def toDirtyMultiplicityData
    (data : DirtyMultiplicitySeparatedInputData) : DirtyMultiplicityData :=
  data.toDirtyMultiplicityInputData.toDirtyMultiplicityData

/-- Forget the now-redundant explicit range certificate from the separated K.2.5
leaf.  The resulting Fin-labelled fibre leaf rebuilds the range bound
internally from the target type. -/
def toDirtyMultiplicityFinFibreInputData
    (data : DirtyMultiplicitySeparatedInputData) :
    DirtyMultiplicityFinFibreInputData where
  dirtyFamily := data.dirtyFamily
  logStar := data.logStar
  CM := data.CM
  L := data.L
  scale := data.scale
  fibre := data.fibre
  logStar_le_log := data.logStar_le_log

end DirtyMultiplicitySeparatedInputData

/-- Recover the split K.2.5 dirty scale/fibre leaf carried by grounded data. -/
def DirtyMultiplicityData.toInputData
    (data : DirtyMultiplicityData) : DirtyMultiplicityInputData where
  dirtyFamily := data.dirtyFamily
  logStar := data.logStar
  CM := data.CM
  L := data.L
  scale := data.scale
  scaleFiber := {
    range := {
      scale_image_card := by
        calc
          (data.dirtyFamily.image data.scale).card <=
              Fintype.card (Fin ((Nat.log 2 data.L) ^ 4)) :=
            Finset.card_le_univ (data.dirtyFamily.image data.scale)
          _ = (Nat.log 2 data.L) ^ 4 := by simp }
    fibre := data.scaleFiber_input }
  logStar_le_log := data.logStar_le_log

/-- The actual scale labels realized by the cleaned dirty family. -/
def DirtyMultiplicityData.scaleImage
    (data : DirtyMultiplicityData) : Finset (Fin ((Nat.log 2 data.L) ^ 4)) :=
  data.dirtyFamily.image data.scale

theorem DirtyMultiplicityData.scale_mem_image
    (data : DirtyMultiplicityData) :
    forall d, d ∈ data.dirtyFamily ->
      data.scale d ∈ data.scaleImage := by
  intro d hd
  simpa [DirtyMultiplicityData.scaleImage] using
    (Finset.mem_image_of_mem data.scale hd)

/-- The dyadic scale-label range is bounded by construction. -/
theorem DirtyMultiplicityData.scale_image_card
    (data : DirtyMultiplicityData) :
    data.scaleImage.card <= (Nat.log 2 data.L) ^ 4 := by
  classical
  calc
    data.scaleImage.card <=
        Fintype.card (Fin ((Nat.log 2 data.L) ^ 4)) :=
      Finset.card_le_univ data.scaleImage
    _ = (Nat.log 2 data.L) ^ 4 := by
      simp

theorem DirtyMultiplicityData.envelope
    (data : DirtyMultiplicityData) :
    data.dirtyFamily.card <= cleanedDirtyEnvelope data.logStar data.CM data.L := by
  exact
    dirtyMultiplicity_envelope_from_scale_fibres
      (dirtyFamily := data.dirtyFamily) (logStar := data.logStar)
      (CM := data.CM) (L := data.L) data.scale data.scaleImage
      data.scale_mem_image
      data.scale_image_card
      (by
        intro y hy
        simpa [DirtyMultiplicityData.scaleImage] using
          data.scaleFiber_input.scale_fiber_le y hy)

theorem DirtyMultiplicityData.card_le_envelope
    (data : DirtyMultiplicityData) :
    data.dirtyFamily.card <= cleanedDirtyEnvelope data.logStar data.CM data.L :=
  corollaryK2_5_dirtyMultiplicity data.envelope

theorem DirtyMultiplicityData.envelope_le_logBound
    (data : DirtyMultiplicityData) :
    cleanedDirtyEnvelope data.logStar data.CM data.L <=
      (Nat.log 2 data.L) ^ (data.CM + 4) :=
  cleanedDirtyEnvelope_le_logBound data.logStar_le_log

/-- Direct cleaned dirty multiplicity bound in the logarithmic envelope form. -/
theorem DirtyMultiplicityData.card_le_logBound
    (data : DirtyMultiplicityData) :
    data.dirtyFamily.card <= (Nat.log 2 data.L) ^ (data.CM + 4) :=
  data.card_le_envelope.trans data.envelope_le_logBound

namespace DirtyMultiplicityInputData

/-- Corollary K.2.5 projected directly from the split dirty scale/fibre leaf. -/
theorem card_le_logBound
    (data : DirtyMultiplicityInputData) :
    data.dirtyFamily.card <= (Nat.log 2 data.L) ^ (data.CM + 4) :=
  data.toDirtyMultiplicityData.card_le_logBound

end DirtyMultiplicityInputData

namespace DirtyMultiplicityFinFibreInputData

/-- Corollary K.2.5 projected directly from the sharpened Fin-labelled fibre
leaf. -/
theorem card_le_logBound
    (data : DirtyMultiplicityFinFibreInputData) :
    data.dirtyFamily.card <= (Nat.log 2 data.L) ^ (data.CM + 4) :=
  data.toDirtyMultiplicityData.card_le_logBound

end DirtyMultiplicityFinFibreInputData

namespace DirtyMultiplicityFinFibreCodingInputData

/-- Corollary K.2.5 projected directly from the Fin-labelled fibre-coding leaf. -/
theorem card_le_logBound
    (data : DirtyMultiplicityFinFibreCodingInputData) :
    data.dirtyFamily.card <= (Nat.log 2 data.L) ^ (data.CM + 4) :=
  data.toDirtyMultiplicityData.card_le_logBound

end DirtyMultiplicityFinFibreCodingInputData

namespace DirtyMultiplicitySeparatedInputData

/-- Corollary K.2.5 projected directly from the separated dirty range/fibre
leaf. -/
theorem card_le_logBound
    (data : DirtyMultiplicitySeparatedInputData) :
    data.dirtyFamily.card <= (Nat.log 2 data.L) ^ (data.CM + 4) :=
  data.toDirtyMultiplicityData.card_le_logBound

end DirtyMultiplicitySeparatedInputData

/--
Local closure marker required by tower, return, and run package constructors.

The finite-outcome M.1 clean-boundary alternative and M.4 semiperiodic-prefix
extension are closed directly in `AppendixM`.  M.3 no longer asserts the false
universal statement that arbitrary valid semiperiodic blocks have the same
start; instead, the theorem consumes explicit `AnchoredSemiperiodicPatch`
evidence for two patches with the same anchored first-dirty datum.
-/
structure LocalClosureOutcomeData where
  closed : True := by trivial

theorem LocalClosureOutcomeData.cleanBoundaryAlternative
    (_data : LocalClosureOutcomeData) (cert : CleanCertificate) :
    Nonempty CleanBoundaryOutcome :=
  theoremM1_1_cleanBoundaryAlternative_closed cert

theorem LocalClosureOutcomeData.semiperiodicOverlap
    (_data : LocalClosureOutcomeData)
    {datum : AnchoredFirstDirtyDatum} {w : Nat -> Nat}
    {p₁ p₂ : SemiperiodicBlock}
    (hp₁ : AnchoredSemiperiodicPatch datum w p₁)
    (hp₂ : AnchoredSemiperiodicPatch datum w p₂) :
    datum.lowerBound <= (p₁.block.points ∩ p₂.block.points).card :=
  theoremM3_1_anchoredSemiperiodicOverlap hp₁ hp₂

theorem LocalClosureOutcomeData.semiperiodicPrefixExtension
    (_data : LocalClosureOutcomeData)
    {w : Nat -> Nat} {start length p : Nat}
    (hprefix : ShortSemiperiodic w start length p) :
    Nonempty CleanBoundaryOutcome :=
  lemmaM4_1_semiperiodicPrefixExtension_closed hprefix

theorem LocalClosureOutcomeData.lowTransientTowerExits
    (_data : LocalClosureOutcomeData)
    {exits : Finset TowerExit}
    (hlow : ∀ e ∈ exits, e.Low) :
    ∀ e ∈ exits, ∃ k : ℝ, 0 <= k ∧ k <= 1 :=
  lemmaM5_1_lowTransientTowerExits (LowTransientTowerExitEncoding.ofLow hlow)

end

end Erdos260
