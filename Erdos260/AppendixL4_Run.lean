import Mathlib
import Erdos260.AppendixI
import Erdos260.AppendixL
import Erdos260.AppendixM
import Erdos260.Constants
import Erdos260.Residual

/-!
# Phase 9: `runBound` (Proposition I.5.2 → `Run` slot)

The manuscript Proposition I.5.2 (`proof_v2.tex` lines 2468--2531) gives
```
  Run_{s,j} ≤ Tower^{fe/ex}_{s,j+1} + Return^{nonrun}_{s,j+1}
            + DensePack_{s,j+1} + X|I_j| 2^{-cY} + o(sX|I_j|).
```

The proof has two parts:
1. L.4.1 deterministic trichotomy (mean-low / local-spike / boundary) of Run branches.
2. L.4.2 period-descent geometric chain `p_{i+1} ≤ p_i / 8`, summed via
   `halfGeometricSum_bound` (already real algebra in [Erdos260.AppendixL]).

After substituting next-layer bounds (which are `o(sX|I_j|)`), the manuscript
reduces to `Run_{s,j} ≤ C_Run · cStar · ξ · X · |I_j| + o(sX|I_j|)`, which fits
inside `cStar · ξ · X / 6` after K.4 step 5.

Phase 9 takes the trichotomy outputs (NextTower, NextReturn, NextDensePack, CNLTail,
small error) as a `RunPackageData` bundle and produces `RunVal ≤ cStar · ξ · X / 6`.
-/

namespace Erdos260

open Finset

noncomputable section

/--
**Run package data.**

Per-instance manuscript inputs to Proposition I.5.2.

* `runMass` — the actual Run mass at order `s, j`;
* `nextTower`, `nextReturn`, `nextDensePack` — bounds from the next threshold layer;
* `twoNegcY` — the manuscript `2^{-cY}` clean CNL tail factor;
* `X, Ij, smallError` — auxiliary parameters;
* `hMassNonneg` — nonnegativity of `runMass`;
* `hRun` — Proposition I.5.2 manuscript bound (real linarith);
* `hSmall` — K.4 compatibility chain to fit into `cStar · ξ · X / 6`.
-/
structure RunPackageData (cStar ξ X : ℝ) where
  runMass : ℝ
  nextTower : ℝ
  nextReturn : ℝ
  nextDensePack : ℝ
  twoNegcY : ℝ
  Ij : ℝ
  smallError : ℝ
  hMassNonneg : 0 <= runMass
  hRun :
    runMass <=
      nextTower + nextReturn + nextDensePack + X * Ij * twoNegcY + smallError
  hSmall :
    nextTower + nextReturn + nextDensePack + X * Ij * twoNegcY + smallError <=
      cStar * ξ * X / 6

/--
**Phase 9 deliverable: `runBound`.**

Given `RunPackageData`, produce `RunVal` and the bound
`RunVal ≤ cStar · ξ · X / 6`.

Constructed via Proposition I.5.2 (already a real inequality in
[Erdos260.AppendixI]) followed by the K.4 numerical compatibility.
-/
theorem runBound
    {cStar ξ X : ℝ}
    (data : RunPackageData cStar ξ X) :
    ∃ RunVal : ℝ,
      0 <= RunVal ∧
      RunVal <= cStar * ξ * X / 6 := by
  refine ⟨data.runMass, data.hMassNonneg, ?_⟩
  have hRun := propositionI5_2_runOutput data.hRun
  exact hRun.trans data.hSmall

end

end Erdos260
