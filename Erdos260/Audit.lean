import Mathlib
import Erdos260.TheoremA
import Erdos260.Erdos260Closure

/-!
# Honesty / faithfulness audit certificates

This file records, as machine-checked theorems, the structural *honesty* facts
that a credibility audit of the Erdős 260 formalization should establish.  The
point is that "no `sorry`/`axiom`" by itself says nothing about credibility: a
conditional theorem can be vacuous (uninhabitable hypothesis) or circular.  Here
we verify the opposite for the top-level reduction.

## What is checked here

* `atomicWitnessProp_false` — the per-failure witness proposition
  `AtomicWitnessProp` is **genuinely false** under the manuscript compatibility
  `cStar·ξ < cPr` (for `X > 0`).  Six quantities each `≤ cStar·ξ·X/6` cannot sum
  to `≥ cPr·X`.  This is the *contradiction engine* of the whole proof: the
  reduction shows that a density-failing shell would produce this (impossible)
  witness, so failing shells cannot occur — a real proof-by-contradiction, not a
  vacuous or circular construction.

The statement faithfulness of `Erdos260Statement` (it matches the manuscript /
DeepMind Erdős 260) and the fact that the hard analytic content is still an
*open, un-inhabited* hypothesis bundle (`GlobalAssemblyInputs`) are recorded in
the audit notes; this file holds the parts that are themselves provable.
-/

namespace Erdos260

noncomputable section

/--
**Honesty certificate: the contradiction engine is real.**

`AtomicWitnessProp cPr cStar ξ X` asserts the existence of six reals, each at
most `cStar·ξ·X/6`, whose sum is at least `cPr·X`.  Under the manuscript
compatibility `cStar·ξ < cPr` and `0 < X` this is impossible, because the six
upper bounds force the sum to be at most `cStar·ξ·X < cPr·X`.

Consequently the top-level reduction (`atomicWitnessProp_of_perFailure` ⟶
`theoremA_of_atomic_inputs`) is a genuine proof by contradiction: deriving
`AtomicWitnessProp` from a density-failing dyadic shell refutes the existence of
that shell.  In particular the reduction is **not** vacuously satisfiable.
-/
theorem atomicWitnessProp_false
    {cPr cStar ξ X : ℝ} (hcompat : cStar * ξ < cPr) (hX : 0 < X) :
    ¬ AtomicWitnessProp cPr cStar ξ X := by
  rintro ⟨R, C, T, D, Re, Ru, hR, hC, hT, hD, hRe, hRu, hsum⟩
  have hsum_le : R + C + T + D + Re + Ru ≤ cStar * ξ * X := by linarith
  have hle : cPr * X ≤ cStar * ξ * X := le_trans hsum hsum_le
  have hlt : cStar * ξ * X < cPr * X := mul_lt_mul_of_pos_right hcompat hX
  linarith

/--
**Corollary: the per-failure certificate is uninhabitable.**

Since every `Erdos260PerFailureCertificate` yields `AtomicWitnessProp`
(`atomicWitnessProp_of_perFailure`), and the latter is false under the
compatibility condition, no per-failure certificate exists for a positive
dyadic scale.  This is exactly why supplying one for a failing shell forces a
contradiction (and hence positive density).
-/
theorem perFailureCertificate_uninhabitable
    {cPr cStar ξ X : ℝ} (hcompat : cStar * ξ < cPr) (hX : 0 < X) :
    IsEmpty (Erdos260PerFailureCertificate cPr cStar ξ X) := by
  refine ⟨fun cert => ?_⟩
  exact atomicWitnessProp_false hcompat hX
    (atomicWitnessProp_of_perFailure cert (le_of_lt hX))

end

end Erdos260
