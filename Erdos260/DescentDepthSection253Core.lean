import Erdos260.Erdos260UnconditionalSeedClosureV4
import Erdos260.UnconditionalAssemblyFinal3
import Erdos260.ChernoffUnconditionalClosure
import Erdos260.CNLUnconditionalClosure
import Erdos260.DensePackUnconditionalClosure
import Erdos260.DescentDepthClosureCore
import Erdos260.SingularSquareBoundCore

/-!
# Section 25.3 descent-depth closure aggregator (root endpoint)

This module is the root aggregator for the Erdos 260 unconditional-closure endpoint.
The root library file `Erdos260.lean` imports exactly this module, so `lake build`
verifies the whole endpoint chain assembled here.

It pulls together:

* the SEED-V4 capstone `erdos260_of_minimalResidualV4` (the latest reduction of
  `Erdos260Statement` to the `Erdos260MinimalResidualV4` residual), which transitively
  carries the V3 matched-charge bundles and the wave-23/24 descent-depth /
  return-placement / Q-correct-density fields;
* the per-output-class genuine leaf discharges in `ChernoffUnconditionalClosure`,
  `CNLUnconditionalClosure`, and `DensePackUnconditionalClosure`;
* the Section 25.3 descent-depth chain (`DescentDepthClosureCore`,
  `SingularSquareBoundCore`, and `DescentDepthNoLargeRunCore` via the V4 import) whose
  `UpperBandMatchData.hband` is the centre-free upper residue-band residual.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

namespace Erdos260

/-- Re-export of the current endpoint: Erdos 260 from the V4 capstone residual. -/
theorem erdos260Statement_of_minimalResidualV4 (R : Erdos260MinimalResidualV4) :
    Erdos260Statement :=
  erdos260_of_minimalResidualV4 R

/-! ## Axiom-cleanliness audit of the endpoint -/

#print axioms erdos260_of_minimalResidualV4

end Erdos260
