import Mathlib
import Erdos260.AppendixI
import Erdos260.AppendixM
import Erdos260.Constants
import Erdos260.Return

/-!
# Phase 8: `nonRunReturnBound` (Proposition I.5.1 → `Return` slot)

The manuscript Proposition I.5.1 (`proof_v2.tex` lines 2434--2465) gives
```
  Return^{nonrun}_{s,j} ≤ X|I_j|(α + M_L) log L + (M_L/α) X|I_j| + o(sX|I_j|)
                       = o(sX|I_j|).
```

The proof has four pieces:
1. Ordinary short returns: synchronizing-set counting `O(αX)` per arm-scale × `O(log L)` scales.
2. Semiperiodic short non-run returns: short-return envelope absorbs into `M_L = (log^* L)^{C_M}(log L)^4`.
3. Ordinary local long returns: feed `corollaryM2_2_OLCEndpointMultiplicity` (real linarith
   in [Erdos260.AppendixM]).
4. Nonlocal long returns: return-length normalization, multiplicity `M_L` per scale.

`proposition23_1_returnPackagesLowerClean` in [Erdos260.Return] already does the
real linarith sum of these four pieces.

Phase 8 wraps the four pieces in a `ReturnPackageData` bundle plus the manuscript
numerical compatibility, and produces `ReturnVal ≤ cStar · ξ · X / 6`.
-/

namespace Erdos260

open Finset

noncomputable section

/--
**Return package data.**

Per-instance manuscript inputs to Proposition I.5.1 / Lemma L.2.2 /
Corollary M.2.2 / Proposition 23.1, expressed in real-arithmetic form
ready for `proposition23_1_returnPackagesLowerClean`.

* `OrdinaryShort` / `Semiperiodic` / `OLC` / `NonlocalLong` — the four
  per-piece masses;
* `C₁`, `C₂`, `C₃`, `C₄` — the manuscript constants;
* `s, Ij, smallError` — auxiliary parameters;
* `hOrdinaryShort, …` — per-piece bounds in the manuscript form;
* `hSmall` — K.4 compatibility to fit into `cStar · ξ · X / 6`.
-/
structure ReturnPackageData (cStar ξ X : ℝ) where
  ordinaryShort : ℝ
  semiperiodic : ℝ
  olc : ℝ
  nonlocalLong : ℝ
  c1 : ℝ
  c2 : ℝ
  c3 : ℝ
  c4 : ℝ
  s : ℝ
  ij : ℝ
  smallError : ℝ
  hMassNonneg :
    0 <= ordinaryShort + semiperiodic + olc + nonlocalLong
  hOrdinaryShort :
    ordinaryShort <= c1 * ξ * s * X * ij + smallError / 4
  hSemiperiodic :
    semiperiodic <= c2 * ξ * s * X * ij + smallError / 4
  hOLC :
    olc <= c3 * ξ * s * X * ij + smallError / 4
  hNonlocalLong :
    nonlocalLong <= c4 * ξ * s * X * ij + smallError / 4
  hSmall :
    (c1 + c2 + c3 + c4) * ξ * s * X * ij + smallError <= cStar * ξ * X / 6

/--
**Phase 8 deliverable: `nonRunReturnBound`.**

Given `ReturnPackageData`, produce `ReturnVal` and the bound
`ReturnVal ≤ cStar · ξ · X / 6`.

Constructed via real linarith summation of the four pieces (Proposition 23.1)
followed by the K.4 numerical compatibility.
-/
theorem nonRunReturnBound
    {cStar ξ X : ℝ}
    (data : ReturnPackageData cStar ξ X) :
    ∃ ReturnVal : ℝ,
      0 <= ReturnVal ∧
      ReturnVal <= cStar * ξ * X / 6 := by
  refine
    ⟨data.ordinaryShort + data.semiperiodic + data.olc + data.nonlocalLong,
     data.hMassNonneg, ?_⟩
  -- Apply Proposition 23.1 (real linarith in Return.lean).
  have hSum :=
    proposition23_1_returnPackagesLowerClean
      data.hOrdinaryShort data.hSemiperiodic data.hOLC data.hNonlocalLong
  exact hSum.trans data.hSmall

end

end Erdos260
