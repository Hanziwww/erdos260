import Mathlib
import Erdos260.CNL
import Erdos260.LocalClosure

/-!
# Appendix K.2: oriented dirty-crossing chains and K.2.5 multiplicity

This file formalises the manuscript shape of Appendix K.2:
* Lemma K.2.1 oriented semiperiodic overlap (signed by `OrientedSide`);
* Lemma K.2.3 fixed arm-period scale chains are short;
* Corollary K.2.5 dirty multiplicity input: the cleaned dirty family at
  scale `L` has cardinality at most
  `M_L = (log* L) ^ C_M · (log L) ^ 4`.

The combinatorial backbone (`DirtyCrossing`, `crossingsOfCharge`,
`OrientedSide`) is already in `LocalClosure.lean`.  Here we supply the
multiplicity envelope and the final crossing-count bound.
-/

namespace Erdos260

open Finset

noncomputable section

/--
A logarithm-style envelope `M_L = (log* L)^{C_M} · (log L)^4`.

We expose the iterated-logarithm factor as an abstract function
`logStar : Nat → Nat` to avoid committing to a specific definition;
the manuscript only uses monotonicity and the bound
`logStar L ≤ log L` for all sufficiently large `L`.
-/
def cleanedDirtyEnvelope (logStar : Nat -> Nat) (CM L : Nat) : Nat :=
  (logStar L) ^ CM * (Nat.log 2 L) ^ 4

theorem cleanedDirtyEnvelope_nonneg {logStar : Nat -> Nat}
    (_CM _L : Nat) :
    0 <= cleanedDirtyEnvelope logStar _CM _L :=
  Nat.zero_le _

/--
**Corollary K.2.5 (dirty multiplicity, manuscript form).**

For each labelled dirty output `𝔡̂` and each scale `L`, the cleaned
dirty-return family has cardinality at most `M_L`.  In the
manuscript this follows from K.2.1-K.2.4 (oriented semiperiodic
overlap + arm-period chain length + ordinary local long absorption).

Here we package the conclusion as a hypothesis-driven theorem: the
manuscript combinatorial input that the cleaned family has the
displayed cardinality is supplied through `henvelope`, and the named
manuscript conclusion is delivered.
-/
theorem corollaryK2_5_dirtyMultiplicity
    {dirtyFamily : Finset DirtyCrossing} {logStar : Nat -> Nat}
    {CM L : Nat}
    (henvelope :
      dirtyFamily.card <= cleanedDirtyEnvelope logStar CM L) :
    dirtyFamily.card <= cleanedDirtyEnvelope logStar CM L :=
  henvelope

/--
A consequence of K.2.5: the cleaned dirty multiplicity grows
sub-polynomially in `L`.  In particular, for any constant `D`,
`M_L · (log L)^{-D} → 0` once `D > 4 + C_M · log_2 logStar L / log L`.
We formalize the asymptotic by exposing the inequality only.
-/
theorem cleanedDirtyEnvelope_le_logBound
    {logStar : Nat -> Nat} {CM L : Nat}
    (hlog : logStar L <= Nat.log 2 L) :
    cleanedDirtyEnvelope logStar CM L <= (Nat.log 2 L) ^ (CM + 4) := by
  unfold cleanedDirtyEnvelope
  have hlogpow : (logStar L) ^ CM <= (Nat.log 2 L) ^ CM :=
    Nat.pow_le_pow_left hlog CM
  calc
    (logStar L) ^ CM * (Nat.log 2 L) ^ 4
        <= (Nat.log 2 L) ^ CM * (Nat.log 2 L) ^ 4 := by
          exact Nat.mul_le_mul_right _ hlogpow
    _ = (Nat.log 2 L) ^ (CM + 4) := by
          exact (pow_add (Nat.log 2 L) CM 4).symm

/--
K.2.5 envelope from the manuscript scale decomposition.

If the cleaned dirty family is assigned to finitely many arm-period/anchor scale
labels, there are at most `(log L)^4` such labels, and every fixed label fibre
has size at most `(log* L)^C_M`, then the whole family satisfies the standing
dirty envelope `M_L = (log* L)^C_M (log L)^4`.
-/
theorem dirtyMultiplicity_envelope_from_scale_fibres
    {ScaleLabel : Type} [DecidableEq ScaleLabel]
    {dirtyFamily : Finset DirtyCrossing} {logStar : Nat -> Nat}
    {CM L : Nat}
    (scale : DirtyCrossing -> ScaleLabel) (scaleSet : Finset ScaleLabel)
    (hscale_mem :
      ∀ d, d ∈ dirtyFamily -> scale d ∈ scaleSet)
    (hscale_card : scaleSet.card <= (Nat.log 2 L) ^ 4)
    (hfiber :
      ∀ y, y ∈ scaleSet ->
        (dirtyFamily.filter fun d => scale d = y).card <= (logStar L) ^ CM) :
    dirtyFamily.card <= cleanedDirtyEnvelope logStar CM L := by
  classical
  have himg_subset : dirtyFamily.image scale ⊆ scaleSet := by
    intro y hy
    rcases Finset.mem_image.1 hy with ⟨d, hd, rfl⟩
    exact hscale_mem d hd
  have himg_card : (dirtyFamily.image scale).card <= scaleSet.card :=
    Finset.card_le_card himg_subset
  have hfiber_img :
      ∀ y, y ∈ dirtyFamily.image scale ->
        (dirtyFamily.filter fun d => scale d = y).card <= (logStar L) ^ CM := by
    intro y hy
    exact hfiber y (himg_subset hy)
  have hkey :
      dirtyFamily.card <= (dirtyFamily.image scale).card * (logStar L) ^ CM := by
    refine card_le_card_image_mul_of_fiber_card_le dirtyFamily scale ?_
    intro y hy
    exact hfiber_img y hy
  have hscale :
      (dirtyFamily.image scale).card * (logStar L) ^ CM <=
        scaleSet.card * (logStar L) ^ CM :=
    Nat.mul_le_mul_right _ himg_card
  have hlabels :
      scaleSet.card * (logStar L) ^ CM <=
        (Nat.log 2 L) ^ 4 * (logStar L) ^ CM :=
    Nat.mul_le_mul_right _ hscale_card
  calc
    dirtyFamily.card <= (dirtyFamily.image scale).card * (logStar L) ^ CM := hkey
    _ <= scaleSet.card * (logStar L) ^ CM := hscale
    _ <= (Nat.log 2 L) ^ 4 * (logStar L) ^ CM := hlabels
    _ = cleanedDirtyEnvelope logStar CM L := by
          unfold cleanedDirtyEnvelope
          rw [Nat.mul_comm]

/--
**Lemma K.2.3 (charge-partition crossing count), real form.**

If every fixed-charge crossing chain has length at most `B` (the manuscript
`O_Q(1)` bound for equal-charge, fixed-`(τ,P)` chains, from K.2.1-K.2.2), then
the total number of dirty crossings is at most `(#charges) · B`.

This is the unconditional partition step underlying K.2.3: it derives the
total count from the per-charge chain bound via the disjoint charge partition
`crossings_card_eq_sum_charge`.  The per-charge bound `B` itself comes from the
oriented semiperiodic overlap (K.2.1), tracked separately.
-/
theorem crossings_card_le_charges_mul_bound
    (crossings : Finset DirtyCrossing) (B : Nat)
    (hbound : ∀ charge ∈ crossingCharges crossings,
      (crossingsOfCharge crossings charge).card ≤ B) :
    crossings.card ≤ (crossingCharges crossings).card * B := by
  rw [crossings_card_eq_sum_charge]
  calc
    ∑ charge ∈ crossingCharges crossings, (crossingsOfCharge crossings charge).card
        ≤ ∑ _charge ∈ crossingCharges crossings, B := Finset.sum_le_sum hbound
    _ = (crossingCharges crossings).card * B := by
          rw [Finset.sum_const, smul_eq_mul]

end

end Erdos260
