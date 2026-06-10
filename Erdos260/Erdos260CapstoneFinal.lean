import Erdos260.Erdos260CapstoneAssembly
import Erdos260.ReturnInputUnconditional
import Erdos260.RunLeafUnconditional
import Erdos260.HighExcessRoutingUnconditional

/-!
# Erdos 260 -- definitive two-atom capstone

This file consolidates the current boundary after the Return atom was closed
unconditionally by `returnInputUnconditional`.

The remaining machine-checked distance to `Erdos260Statement` is exactly two
analytic atoms:

* Run, class 5: `RunClass5LeafResidual`, the Section 26 base run-area sparsity
  package feeding `RunClass5GenuineLeaf`.
* P9 central charge routing: `HighExcessRoutingCountResidual`, the matched
  count-times-multiplier first-obstruction routing package.

All other providers are already discharged in `erdos260_capstone`.
-/

namespace Erdos260

noncomputable section

/-- The definitive two-atom residual after the Return atom has been closed. -/
structure Erdos260CapstoneFinalResidual where
  /-- Run / class 5 / Appendix L.4 and Section 26. -/
  runResidual : forall ctx : ActualFailureContext, RunClass5LeafResidual ctx
  /-- P9 central charge bridge in the matched count-times-multiplier form. -/
  highExcessResidual : HighExcessRoutingCountResidual

/-- Erdős 260 from the definitive two-atom residual.

Return is no longer a residual field: it is supplied by the unconditional
`returnInputUnconditional`.  The Run residual is converted by
`runLeafFromResidual`; the P9 residual is converted by
`highExcessRoutingFromCountCharge`. -/
theorem erdos260_capstone_final
    (R : Erdos260CapstoneFinalResidual) : Erdos260Statement :=
  erdos260_capstone
    { runLeaf := runLeafFromResidual R.runResidual
      returnInput := returnInputUnconditional
      highExcessRouting := highExcessRoutingFromCountCharge R.highExcessResidual }

/-- Human-readable inventory of the final two remaining manuscript atoms. -/
def erdos260CapstoneFinalInventory : List String :=
  [ "Run/Class 5: RunClass5LeafResidual, the Section 26 base run-area sparsity " ++
      "package plus finite L.4.2 half-decrease and the I.6S stage map.",
    "P9: HighExcessRoutingCountResidual, the matched count-times-multiplier " ++
      "central charge routing package; class 6 old-residual is discharged, " ++
      "while Chernoff/CNL/DensePack/joint-TRT matched bounds remain." ]

theorem erdos260CapstoneFinalInventory_length :
    erdos260CapstoneFinalInventory.length = 2 := by
  simp [erdos260CapstoneFinalInventory]

#print axioms erdos260_capstone_final

end

end Erdos260
