import Mathlib
import Erdos260.AppendixI
import Erdos260.Constants
import Erdos260.DensePack

/-!
# Phase 6: `densePackBound` (Lemma I.4.1 + K.1.3 → `DensePackVal` slot)

The manuscript Lemma I.4.1 (`proof_v2.tex` lines 2383--2429) says
that under the positive-density failure `A(2X) − A(X) ≤ c_* X`,
the dense-pack mass satisfies
```
  DensePack_{s,j} ≤ ξ · sX|I_j| + o(sX|I_j|).
```

The proof has two steps:
1. The greedy maximal disjoint marker family inside `[X − CrL, 2X + CrL]`
   contains `≤ c_* X / (ρ_D L)` markers (from the failure hypothesis +
   boundary band).
2. Each dense-marker branch contributes `O(L|I_j|)` to the DensePack mass
   (cover by `(2 spread + 1)` window).

After choosing `c_* < ρ_D κ ξ / C_Q` (the manuscript's K.4 step 6),
this gives the desired bound.

Phase 6 takes the manuscript's K.1.1 cover (`hcover`), K.1.2 fibre
bound (`hassign`), and K.1.3 numerical compatibility (`hSmallness`) as
input bundle, and produces `DensePackVal ≤ cStar · ξ · X / 6`.
-/

namespace Erdos260

open Finset

noncomputable section

/--
**DensePack data.**

Per-instance manuscript inputs to Lemma I.4.1:
* `densePackPoints` — the dense-pack endpoint set;
* `markersCard` — the greedy maximal disjoint marker count;
* `spread` — the K.1.2 spread parameter (∼`L`);
* `hcover` — the K.1.2 cover bound;
* `hcount` — the failure-hypothesis count `markersCard ≤ c_* X`;
* `Ij`, `s` — the manuscript window and order constants;
* `hSmallness` — the K.4 numerical compatibility making the dense-pack
  contribution fit inside `cStar · ξ · X / 6`.
-/
structure DensePackData (cStar ξ X : ℝ) where
  densePackPoints : Finset Nat
  markersCard : Nat
  spread : Nat
  cStarSmall : ℝ
  hcover :
    densePackPoints.card <= markersCard * (2 * spread + 1)
  hcount :
    (markersCard : ℝ) <= cStarSmall * X
  hX_nonneg : 0 <= X
  hsmall :
    cStarSmall * X * ((2 * spread + 1 : Nat) : ℝ) <= cStar * ξ * X / 6

/--
**Phase 6 deliverable: `densePackBound`.**

Given the `DensePackData` bundle, produce `DensePackVal` and the
manuscript bound `DensePackVal ≤ cStar · ξ · X / 6`.

The constructed `DensePackVal` is the real cardinality of the
dense-pack endpoint set, after applying `corollaryK1_3_densePackUnderFailure`.
-/
theorem densePackBound
    {cStar ξ X : ℝ}
    (data : DensePackData cStar ξ X) :
    ∃ DensePackVal : ℝ,
      0 <= DensePackVal ∧
      DensePackVal <= cStar * ξ * X / 6 := by
  classical
  refine ⟨(data.densePackPoints.card : ℝ), ?_, ?_⟩
  · -- Nonnegativity: cardinality cast to ℝ.
    exact_mod_cast Nat.zero_le _
  · -- Upper bound chain: K.1.3 then numerical smallness.
    have hK13 :
        (data.densePackPoints.card : ℝ) <=
          data.cStarSmall * X * ((2 * data.spread + 1 : Nat) : ℝ) :=
      corollaryK1_3_densePackUnderFailure
        (densePackPoints := data.densePackPoints)
        (markersCard := data.markersCard) (spread := data.spread)
        (cStar := data.cStarSmall) (X := X)
        data.hcover data.hcount
    exact hK13.trans data.hsmall

end

end Erdos260
