import Mathlib
import Erdos260.AppendixI
import Erdos260.AppendixM
import Erdos260.Constants
import Erdos260.RefinedTower

/-!
# Phase 7: `towerPackageBound` (Proposition I.3.1 → `Tower` slot)

The manuscript Proposition I.3.1 (`proof_v2.tex` lines 2317--2376),
combined with the transient-excursion alternative Lemma L.3.1
(`proof_v2.tex` lines 4349--4378) and the charged summability Lemma L.2.4
(`proof_v2.tex` lines 4300--4316), gives
```
  Tower^{fe/ex}_{s,j} ≤ Run_{s,j+1} + Return^{nonrun}_{s,j+1}
                       + DensePack_{s,j+1} + X|I_j| 2^{-cY} + o(sX|I_j|).
```

After substituting the bounds from the *next* threshold layer (which are
already `o(sX|I_j|)` by the descent), the manuscript reduces this to
```
  Tower^{fe/ex}_{s,j} ≤ C_T · cStar · ξ · sX|I_j| + o(sX|I_j|),
```
which after K.4 step 5 fits inside `cStar · ξ · X / 6`.

Phase 7 takes the manuscript inputs (transient-excursion endpoint
disjointness `hDisjointEndpoints`, charged-summability bound `hSummable`,
and a numerical compatibility `hSmall`) and produces a `Tower` real
satisfying `Tower ≤ cStar · ξ · X / 6`.
-/

namespace Erdos260

open Finset

noncomputable section

/--
**Tower package data.**

Per-instance manuscript inputs to Proposition I.3.1.

* `entryExitSet` — the finite set of tower first-entry / first-exit branches;
* `chargedWeight` — the charged weight function `wt(b)`;
* `outputBoundConstant` — the `C_T` from manuscript;
* `nextLayerMass` — the sum of bounds from the next threshold layer (Run + Return + DensePack);
* `smallError` — the `o(sX|I_j|)` error;
* `hSummable` — Lemma L.2.4 charged-summability bound
  `∑_b wt(b) ≤ C_T · nextLayerMass + smallError`;
* `hSmall` — K.4 compatibility chain to fit inside `cStar · ξ · X / 6`.
-/
structure TowerPackageData (cStar ξ X : ℝ) where
  entryExitSet : Finset TowerExit
  chargedWeight : TowerExit -> ℝ
  chargedWeight_nonneg : ∀ b ∈ entryExitSet, 0 <= chargedWeight b
  outputBoundConstant : ℝ
  nextLayerMass : ℝ
  smallError : ℝ
  hSummable :
    ∑ b ∈ entryExitSet, chargedWeight b <=
      outputBoundConstant * nextLayerMass + smallError
  hSmall :
    outputBoundConstant * nextLayerMass + smallError <= cStar * ξ * X / 6
  hMassNonneg : 0 <= ∑ b ∈ entryExitSet, chargedWeight b

/--
**Phase 7 deliverable: `towerPackageBound`.**

Given `TowerPackageData`, produce the `Tower` real and the bound
`Tower ≤ cStar · ξ · X / 6`.

The constructed `Tower` is the sum of charged weights over the
tower entry/exit set.
-/
theorem towerPackageBound
    {cStar ξ X : ℝ}
    (data : TowerPackageData cStar ξ X) :
    ∃ Tower : ℝ,
      0 <= Tower ∧
      Tower <= cStar * ξ * X / 6 := by
  refine
    ⟨∑ b ∈ data.entryExitSet, data.chargedWeight b,
     data.hMassNonneg, ?_⟩
  -- Apply Proposition I.3.1 (manuscript form) which is already proven in
  -- AppendixI.lean via `propositionI3_1_towerOutput` as the real linarith
  -- transformation of `hSummable`.
  have hTower :
      ∑ b ∈ data.entryExitSet, data.chargedWeight b <=
        data.outputBoundConstant * data.nextLayerMass + data.smallError :=
    propositionI3_1_towerOutput data.hSummable
  exact hTower.trans data.hSmall

end

end Erdos260
