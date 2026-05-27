import Erdos260.Residual
import Erdos260.Tower

/-!
# Local closure primitives for Appendices K and M

This file contains finite local objects used by the later DensePack/dirty
crossing/semiperiodic/tower-exit closure arguments.  It records structural
facts only: endpoint projections, semiperiodic restriction, deterministic
orientation filters, and the finite tower low-exit vocabulary.
-/

namespace Erdos260

open Finset

noncomputable section

/-- A half-open integer interval `[start, start + length)`. -/
structure IntervalBlock where
  start : Nat
  length : Nat
deriving DecidableEq, Repr

namespace IntervalBlock

/-- Right endpoint of a block. -/
def stop (I : IntervalBlock) : Nat :=
  I.start + I.length

/-- A sub-block obtained by shifting inside `I`. -/
def subBlock (I : IntervalBlock) (offset length : Nat) : IntervalBlock where
  start := I.start + offset
  length := length

/-- `J` is contained in `I`. -/
def Contains (I J : IntervalBlock) : Prop :=
  I.start <= J.start ∧ J.stop <= I.stop

/-- The finite set of integer points in the half-open block. -/
def points (I : IntervalBlock) : Finset Nat :=
  (range I.length).image fun k => I.start + k

theorem contains_self (I : IntervalBlock) :
    Contains I I := by
  simp [Contains, stop]

theorem contains_trans {I J K : IntervalBlock}
    (hIJ : Contains I J) (hJK : Contains J K) :
    Contains I K := by
  constructor
  · exact hIJ.1.trans hJK.1
  · exact hJK.2.trans hIJ.2

theorem contains_subBlock {I : IntervalBlock} {offset length : Nat}
    (h : offset + length <= I.length) :
    Contains I (I.subBlock offset length) := by
  constructor
  · simp [subBlock]
  · simp [subBlock, stop]
    omega

theorem subBlock_stop (I : IntervalBlock) (offset length : Nat) :
    (I.subBlock offset length).stop = I.start + offset + length := by
  simp [subBlock, stop, Nat.add_assoc]

theorem mem_points {I : IntervalBlock} {x : Nat} :
    x ∈ I.points ↔ I.start <= x ∧ x < I.stop := by
  constructor
  · intro hx
    rcases mem_image.1 hx with ⟨k, hk, rfl⟩
    have hklt : k < I.length := by
      simpa using hk
    constructor
    · simp
    · simp [stop]
      omega
  · intro hx
    refine mem_image.2 ?_
    refine ⟨x - I.start, ?_, ?_⟩
    · simp
      have hxstop : x < I.start + I.length := by
        simpa [stop] using hx.2
      omega
    · exact Nat.add_sub_of_le hx.1

theorem points_card_le (I : IntervalBlock) :
    I.points.card <= I.length := by
  simpa [points] using
    (card_image_le (s := range I.length) (f := fun k => I.start + k))

theorem points_card (I : IntervalBlock) :
    I.points.card = I.length := by
  unfold points
  rw [card_image_of_injOn]
  · simp
  · intro a ha b hb hab
    exact Nat.add_left_cancel hab

theorem points_subset_of_contains {I J : IntervalBlock} (h : Contains I J) :
    J.points ⊆ I.points := by
  intro x hx
  have hxJ := mem_points.1 hx
  exact mem_points.2 ⟨h.1.trans hxJ.1, hxJ.2.trans_le h.2⟩

theorem points_subBlock_subset {I : IntervalBlock} {offset length : Nat}
    (h : offset + length <= I.length) :
    (I.subBlock offset length).points ⊆ I.points :=
  points_subset_of_contains (contains_subBlock h)

theorem points_disjoint_of_stop_le_start {I J : IntervalBlock}
    (h : I.stop <= J.start) :
    Disjoint I.points J.points := by
  rw [Finset.disjoint_left]
  intro x hxI hxJ
  have hI := mem_points.1 hxI
  have hJ := mem_points.1 hxJ
  exact Nat.not_lt_of_ge (h.trans hJ.1) hI.2

theorem points_disjoint_of_stop_le_start' {I J : IntervalBlock}
    (h : J.stop <= I.start) :
    Disjoint I.points J.points :=
  (points_disjoint_of_stop_le_start (I := J) (J := I) h).symm

end IntervalBlock

/-- A side/orientation used for dirty crossing arms. -/
inductive OrientedSide where
  | left
  | right
deriving DecidableEq, Fintype, Repr

/-- A finite semiperiodic block with an explicit period. -/
structure SemiperiodicBlock where
  block : IntervalBlock
  period : Nat
deriving DecidableEq, Repr

namespace SemiperiodicBlock

/-- Validity of a semiperiodic block for a word. -/
def Valid (w : Nat -> Nat) (B : SemiperiodicBlock) : Prop :=
  PeriodicOn w B.block.start B.block.length B.period

/-- Restrict a semiperiodic block to a sub-block with the same period. -/
def subBlock (B : SemiperiodicBlock) (offset length : Nat) : SemiperiodicBlock where
  block := B.block.subBlock offset length
  period := B.period

theorem valid_subBlock {w : Nat -> Nat} {B : SemiperiodicBlock}
    (hvalid : Valid w B) {offset length : Nat}
    (h : offset + length <= B.block.length) :
    Valid w (B.subBlock offset length) := by
  exact hvalid.suffix h

theorem valid_of_contains {w : Nat -> Nat} {B : SemiperiodicBlock}
    (hvalid : Valid w B) {J : IntervalBlock}
    (hJ : IntervalBlock.Contains B.block J) :
    PeriodicOn w J.start J.length B.period := by
  let offset := J.start - B.block.start
  have hstart_le : B.block.start <= J.start := hJ.1
  have hoff : offset + J.length <= B.block.length := by
    have hstop : J.start + J.length <= B.block.start + B.block.length := by
      simpa [IntervalBlock.stop] using hJ.2
    have hstart_eq : B.block.start + (J.start - B.block.start) = J.start :=
      Nat.add_sub_of_le hstart_le
    dsimp [offset]
    omega
  have hstart : B.block.start + offset = J.start := by
    dsimp [offset]
    exact Nat.add_sub_of_le hstart_le
  simpa [hstart] using hvalid.suffix hoff

theorem valid_shortSemiperiodic {w : Nat -> Nat} {B : SemiperiodicBlock}
    (hvalid : Valid w B) {bound : Nat} (hbound : B.period < bound) :
    ShortSemiperiodic w B.block.start B.block.length bound :=
  ⟨B.period, hvalid, hbound⟩

end SemiperiodicBlock

/-- A dirty crossing object with explicit side, anchor, charge, and arm block. -/
structure DirtyCrossing where
  anchor : Nat
  periodScale : Nat
  side : OrientedSide
  charge : Nat
  arm : IntervalBlock
deriving DecidableEq, Repr

/-- Crossings with a fixed charge. -/
def crossingsOfCharge (crossings : Finset DirtyCrossing) (charge : Nat) :
    Finset DirtyCrossing :=
  crossings.filter fun x => x.charge = charge

/-- Crossings with a fixed side. -/
def crossingsOfSide (crossings : Finset DirtyCrossing) (side : OrientedSide) :
    Finset DirtyCrossing :=
  crossings.filter fun x => x.side = side

/-- Charge values appearing in a finite crossing family. -/
def crossingCharges (crossings : Finset DirtyCrossing) : Finset Nat :=
  crossings.image DirtyCrossing.charge

theorem mem_crossingsOfCharge {crossings : Finset DirtyCrossing} {charge : Nat}
    {x : DirtyCrossing} :
    x ∈ crossingsOfCharge crossings charge ↔ x ∈ crossings ∧ x.charge = charge := by
  simp [crossingsOfCharge]

theorem mem_crossingsOfSide {crossings : Finset DirtyCrossing} {side : OrientedSide}
    {x : DirtyCrossing} :
    x ∈ crossingsOfSide crossings side ↔ x ∈ crossings ∧ x.side = side := by
  simp [crossingsOfSide]

theorem mem_crossingCharges {crossings : Finset DirtyCrossing} {charge : Nat} :
    charge ∈ crossingCharges crossings ↔
      ∃ x ∈ crossings, x.charge = charge := by
  simp [crossingCharges]

theorem crossingsOfCharge_subset (crossings : Finset DirtyCrossing) (charge : Nat) :
    crossingsOfCharge crossings charge ⊆ crossings := by
  intro x hx
  exact (mem_crossingsOfCharge.1 hx).1

theorem crossingsOfCharge_card_le (crossings : Finset DirtyCrossing) (charge : Nat) :
    (crossingsOfCharge crossings charge).card <= crossings.card :=
  card_le_card (crossingsOfCharge_subset crossings charge)

theorem disjoint_crossingsOfCharge_of_ne {crossings : Finset DirtyCrossing}
    {charge₁ charge₂ : Nat} (hne : charge₁ ≠ charge₂) :
    Disjoint (crossingsOfCharge crossings charge₁)
      (crossingsOfCharge crossings charge₂) := by
  rw [disjoint_left]
  intro x hx₁ hx₂
  exact hne ((mem_crossingsOfCharge.1 hx₁).2.symm.trans (mem_crossingsOfCharge.1 hx₂).2)

theorem pairwiseDisjoint_crossingsOfCharge
    (crossings : Finset DirtyCrossing) :
    ((crossingCharges crossings : Finset Nat) : Set Nat).PairwiseDisjoint
      (crossingsOfCharge crossings) := by
  intro charge₁ _ charge₂ _ hne
  exact disjoint_crossingsOfCharge_of_ne hne

theorem crossings_eq_biUnion_charge (crossings : Finset DirtyCrossing) :
    crossings =
      (crossingCharges crossings).biUnion (crossingsOfCharge crossings) := by
  ext x
  constructor
  · intro hx
    exact mem_biUnion.2
      ⟨x.charge, mem_crossingCharges.2 ⟨x, hx, rfl⟩,
        mem_crossingsOfCharge.2 ⟨hx, rfl⟩⟩
  · intro hx
    rcases mem_biUnion.1 hx with ⟨charge, _, hcharge⟩
    exact (mem_crossingsOfCharge.1 hcharge).1

theorem crossings_card_eq_sum_charge (crossings : Finset DirtyCrossing) :
    crossings.card =
      ∑ charge ∈ crossingCharges crossings,
        (crossingsOfCharge crossings charge).card := by
  calc
    crossings.card =
        ((crossingCharges crossings).biUnion
          (crossingsOfCharge crossings)).card := by
          exact congrArg Finset.card (crossings_eq_biUnion_charge crossings)
    _ = ∑ charge ∈ crossingCharges crossings,
        (crossingsOfCharge crossings charge).card := by
          exact card_biUnion (pairwiseDisjoint_crossingsOfCharge crossings)

theorem crossingsOfSide_subset (crossings : Finset DirtyCrossing) (side : OrientedSide) :
    crossingsOfSide crossings side ⊆ crossings := by
  intro x hx
  exact (mem_crossingsOfSide.1 hx).1

theorem crossingsOfSide_card_le (crossings : Finset DirtyCrossing) (side : OrientedSide) :
    (crossingsOfSide crossings side).card <= crossings.card :=
  card_le_card (crossingsOfSide_subset crossings side)

theorem disjoint_crossingsOfSide_of_ne {crossings : Finset DirtyCrossing}
    {side₁ side₂ : OrientedSide} (hne : side₁ ≠ side₂) :
    Disjoint (crossingsOfSide crossings side₁) (crossingsOfSide crossings side₂) := by
  rw [disjoint_left]
  intro x hx₁ hx₂
  exact hne ((mem_crossingsOfSide.1 hx₁).2.symm.trans (mem_crossingsOfSide.1 hx₂).2)

theorem pairwiseDisjoint_crossingsOfSide (crossings : Finset DirtyCrossing) :
    ((Finset.univ : Finset OrientedSide) : Set OrientedSide).PairwiseDisjoint
      (crossingsOfSide crossings) := by
  intro side₁ _ side₂ _ hne
  exact disjoint_crossingsOfSide_of_ne hne

theorem crossings_eq_biUnion_side (crossings : Finset DirtyCrossing) :
    crossings =
      (Finset.univ : Finset OrientedSide).biUnion (crossingsOfSide crossings) := by
  ext x
  constructor
  · intro hx
    exact mem_biUnion.2
      ⟨x.side, by simp, mem_crossingsOfSide.2 ⟨hx, rfl⟩⟩
  · intro hx
    rcases mem_biUnion.1 hx with ⟨side, _, hside⟩
    exact (mem_crossingsOfSide.1 hside).1

theorem crossings_card_eq_sum_side (crossings : Finset DirtyCrossing) :
    crossings.card =
      ∑ side : OrientedSide, (crossingsOfSide crossings side).card := by
  calc
    crossings.card =
        ((Finset.univ : Finset OrientedSide).biUnion
          (crossingsOfSide crossings)).card := by
          exact congrArg Finset.card (crossings_eq_biUnion_side crossings)
    _ = ∑ side : OrientedSide, (crossingsOfSide crossings side).card := by
          exact card_biUnion (pairwiseDisjoint_crossingsOfSide crossings)

/-- Union of points covered by a finite family of blocks. -/
def blockPointUnion (blocks : Finset IntervalBlock) : Finset Nat :=
  blocks.biUnion IntervalBlock.points

theorem mem_blockPointUnion {blocks : Finset IntervalBlock} {x : Nat} :
    x ∈ blockPointUnion blocks ↔
      ∃ I ∈ blocks, I.start <= x ∧ x < I.stop := by
  simp [blockPointUnion, IntervalBlock.mem_points]

theorem blockPointUnion_card_le_sum_length (blocks : Finset IntervalBlock) :
    (blockPointUnion blocks).card <= ∑ I ∈ blocks, I.length := by
  calc
    (blockPointUnion blocks).card
        <= ∑ I ∈ blocks, I.points.card := by
          simpa [blockPointUnion] using
            (card_biUnion_le (s := blocks) (t := IntervalBlock.points))
    _ = ∑ I ∈ blocks, I.length := by
          exact sum_congr rfl fun I _ => IntervalBlock.points_card I

theorem blockPointUnion_mono {blocks₁ blocks₂ : Finset IntervalBlock}
    (h : blocks₁ ⊆ blocks₂) :
    blockPointUnion blocks₁ ⊆ blockPointUnion blocks₂ := by
  intro x hx
  rcases mem_blockPointUnion.1 hx with ⟨I, hI, hxI⟩
  exact mem_blockPointUnion.2 ⟨I, h hI, hxI⟩

/-- Endpoint projection used by endpoint-multiplicity estimates. -/
def endpointSet (blocks : Finset IntervalBlock) : Finset Nat :=
  blocks.image IntervalBlock.stop

theorem mem_endpointSet {blocks : Finset IntervalBlock} {x : Nat} :
    x ∈ endpointSet blocks ↔ ∃ I ∈ blocks, I.stop = x := by
  simp [endpointSet]

theorem endpointSet_card_le (blocks : Finset IntervalBlock) :
    (endpointSet blocks).card <= blocks.card := by
  simp [endpointSet, card_image_le]

theorem endpointSet_mono {blocks₁ blocks₂ : Finset IntervalBlock}
    (h : blocks₁ ⊆ blocks₂) :
    endpointSet blocks₁ ⊆ endpointSet blocks₂ := by
  intro x hx
  rcases mem_endpointSet.1 hx with ⟨I, hI, hstop⟩
  exact mem_endpointSet.2 ⟨I, h hI, hstop⟩

namespace DirtyCrossing

/-- The endpoint selected by the crossing orientation. -/
def sideEndpoint (x : DirtyCrossing) : Nat :=
  match x.side with
  | OrientedSide.left => x.arm.start
  | OrientedSide.right => x.arm.stop

end DirtyCrossing

/-- Blocks carried by the dirty-crossing arms. -/
def dirtyCrossingArmBlocks (crossings : Finset DirtyCrossing) : Finset IntervalBlock :=
  crossings.image DirtyCrossing.arm

/-- Right endpoints of all dirty-crossing arm blocks. -/
def dirtyCrossingArmEndpoints (crossings : Finset DirtyCrossing) : Finset Nat :=
  endpointSet (dirtyCrossingArmBlocks crossings)

/-- Orientation-selected endpoints of dirty crossings. -/
def dirtyCrossingSideEndpoints (crossings : Finset DirtyCrossing) : Finset Nat :=
  crossings.image DirtyCrossing.sideEndpoint

/-- Points covered by dirty-crossing arms. -/
def dirtyCrossingArmPointUnion (crossings : Finset DirtyCrossing) : Finset Nat :=
  crossings.biUnion fun x => x.arm.points

theorem mem_dirtyCrossingArmEndpoints {crossings : Finset DirtyCrossing} {x : Nat} :
    x ∈ dirtyCrossingArmEndpoints crossings ↔
      ∃ c ∈ crossings, c.arm.stop = x := by
  simp [dirtyCrossingArmEndpoints, dirtyCrossingArmBlocks, endpointSet]

theorem dirtyCrossingArmEndpoints_card_le (crossings : Finset DirtyCrossing) :
    (dirtyCrossingArmEndpoints crossings).card <= crossings.card := by
  calc
    (dirtyCrossingArmEndpoints crossings).card
        <= (dirtyCrossingArmBlocks crossings).card :=
          endpointSet_card_le (dirtyCrossingArmBlocks crossings)
    _ <= crossings.card := by
          simpa [dirtyCrossingArmBlocks] using
            (card_image_le (s := crossings) (f := DirtyCrossing.arm))

theorem dirtyCrossingSideEndpoints_card_le (crossings : Finset DirtyCrossing) :
    (dirtyCrossingSideEndpoints crossings).card <= crossings.card := by
  simpa [dirtyCrossingSideEndpoints] using
    (card_image_le (s := crossings) (f := DirtyCrossing.sideEndpoint))

theorem dirtyCrossingArmPointUnion_card_le_sum_length
    (crossings : Finset DirtyCrossing) :
    (dirtyCrossingArmPointUnion crossings).card <=
      ∑ x ∈ crossings, x.arm.length := by
  calc
    (dirtyCrossingArmPointUnion crossings).card
        <= ∑ x ∈ crossings, x.arm.points.card := by
          simpa [dirtyCrossingArmPointUnion] using
            (card_biUnion_le (s := crossings) (t := fun x => x.arm.points))
    _ = ∑ x ∈ crossings, x.arm.length := by
          exact sum_congr rfl fun x _ => IntervalBlock.points_card x.arm

theorem dirtyCrossingArmBlocks_mono {crossings₁ crossings₂ : Finset DirtyCrossing}
    (h : crossings₁ ⊆ crossings₂) :
    dirtyCrossingArmBlocks crossings₁ ⊆ dirtyCrossingArmBlocks crossings₂ := by
  intro I hI
  rcases mem_image.1 hI with ⟨x, hx, rfl⟩
  exact mem_image.2 ⟨x, h hx, rfl⟩

theorem dirtyCrossingArmEndpoints_mono {crossings₁ crossings₂ : Finset DirtyCrossing}
    (h : crossings₁ ⊆ crossings₂) :
    dirtyCrossingArmEndpoints crossings₁ ⊆ dirtyCrossingArmEndpoints crossings₂ :=
  endpointSet_mono (dirtyCrossingArmBlocks_mono h)

theorem dirtyCrossingSideEndpoints_mono {crossings₁ crossings₂ : Finset DirtyCrossing}
    (h : crossings₁ ⊆ crossings₂) :
    dirtyCrossingSideEndpoints crossings₁ ⊆ dirtyCrossingSideEndpoints crossings₂ := by
  intro x hx
  rcases mem_image.1 hx with ⟨c, hc, rfl⟩
  exact mem_image.2 ⟨c, h hc, rfl⟩

theorem dirtyCrossingArmPointUnion_mono {crossings₁ crossings₂ : Finset DirtyCrossing}
    (h : crossings₁ ⊆ crossings₂) :
    dirtyCrossingArmPointUnion crossings₁ ⊆ dirtyCrossingArmPointUnion crossings₂ := by
  intro x hx
  simp only [dirtyCrossingArmPointUnion, mem_biUnion] at hx ⊢
  rcases hx with ⟨c, hc, hxarm⟩
  exact ⟨c, h hc, hxarm⟩

/-- Tower exit with an explicit bound on the layer increase. -/
structure TowerExit where
  source : TowerVertex
  target : TowerVertex
  layerBound : Nat
deriving DecidableEq, Repr

/-- A tower exit is low if the target layer stays within the explicit bound. -/
def TowerExit.Low (e : TowerExit) : Prop :=
  e.target.layer <= e.source.layer + e.layerBound

/-- A tower exit is a strict threshold exit if it raises the layer. -/
def TowerExit.Strict (e : TowerExit) : Prop :=
  e.source.layer < e.target.layer

theorem TowerExit.strict_ne_source {e : TowerExit} (h : e.Strict) :
    e.target ≠ e.source := by
  intro heq
  have htarget : e.source.layer < e.target.layer := h
  have hlt : e.source.layer < e.source.layer := by
    rw [heq] at htarget
    exact htarget
  exact (lt_irrefl e.source.layer) hlt

theorem TowerExit.low_strict_layer_bounds {e : TowerExit}
    (hlow : e.Low) (hstrict : e.Strict) :
    e.source.layer < e.target.layer ∧
      e.target.layer <= e.source.layer + e.layerBound :=
  ⟨hstrict, hlow⟩

end

end Erdos260
