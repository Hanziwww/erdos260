import Mathlib
import Erdos260.DirtyCrossing
import Erdos260.Ledger
import Erdos260.LocalClosure

/-!
# Proposition 23.1: return packages are lower clean

This file packages the manuscript shape of Proposition 23.1 in
`proof_v2.tex`:  ordinary bounded returns are counted by synchronizing
sets, semiperiodic short non-run returns are absorbed by the short-return
envelope, ordinary local long returns are absorbed into OLC endpoint
multiplicities (Cor M.2.2), and nonlocal long returns are counted by
return-length normalization.

We expose the bound as a packaged inequality `Return^nonrun_{s,j}
≤ C_J · ξ · sX|I_j| + o(sX|I_j|)` which is exactly the input used by
Appendix I.5.1 / I.5.2 to build the joint package estimate.
-/

namespace Erdos260

open Finset

noncomputable section

/--
**Proposition 23.1 (return packages are lower clean, manuscript form).**

The non-run return package mass is bounded by `C_J · ξ · sX|I_j| +
o(sX|I_j|)`.  The manuscript proves this by combining the ordinary
short-return / semiperiodic / OLC / nonlocal-long classification.

Pass 2 form: the four manuscript ingredients are real input bounds,
and the conclusion is a **real linear combination** via `linarith`.

* `hOrdinaryShort`: ordinary short-return contribution
  `≤ C₁ · ξ · s · X · Ij + smallError/4` (synchronizing-set counting).
* `hSemiperiodic`: semiperiodic short non-run return contribution
  `≤ C₂ · ξ · s · X · Ij + smallError/4` (short-return envelope).
* `hOLC`: ordinary local long endpoint contribution
  `≤ C₃ · ξ · s · X · Ij + smallError/4` (Corollary M.2.2).
* `hNonlocalLong`: nonlocal long return contribution
  `≤ C₄ · ξ · s · X · Ij + smallError/4` (return-length normalization).
-/
theorem proposition23_1_returnPackagesLowerClean
    {OrdinaryShort Semiperiodic OLC NonlocalLong : ℝ}
    {C₁ C₂ C₃ C₄ ξ s X Ij smallError : ℝ}
    (hOrdinaryShort :
      OrdinaryShort <= C₁ * ξ * s * X * Ij + smallError / 4)
    (hSemiperiodic :
      Semiperiodic <= C₂ * ξ * s * X * Ij + smallError / 4)
    (hOLC :
      OLC <= C₃ * ξ * s * X * Ij + smallError / 4)
    (hNonlocalLong :
      NonlocalLong <= C₄ * ξ * s * X * Ij + smallError / 4) :
    OrdinaryShort + Semiperiodic + OLC + NonlocalLong <=
      (C₁ + C₂ + C₃ + C₄) * ξ * s * X * Ij + smallError := by
  have hexpand :
      (C₁ + C₂ + C₃ + C₄) * ξ * s * X * Ij =
        C₁ * ξ * s * X * Ij + C₂ * ξ * s * X * Ij +
          C₃ * ξ * s * X * Ij + C₄ * ξ * s * X * Ij := by ring
  linarith [hexpand.le, hexpand.ge]

end

end Erdos260
