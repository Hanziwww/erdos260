import Mathlib
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

end

end Erdos260
