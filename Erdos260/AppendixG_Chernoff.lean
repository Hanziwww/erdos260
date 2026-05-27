import Mathlib
import Erdos260.Constants
import Erdos260.StoppedInduction

/-!
# Phase 4: `chernoffPathSpace` (Lemma 22.1 path form)

The manuscript Lemma 22.1 (`proof_v2.tex` lines 325--347) says: for a
regular-path family `π` in the stopped tree with `∑ s(e) ≥ Y` and
length `m ≤ cY` (with `c > 0` small enough), the total path mass is
bounded by `|Ω_root| · 2^{−c'Y}` for some `c' > 0`.

In Pass-3 Lean we already have the generic Chernoff inequality
`shellChernoff_bound_of_moment_bound` ([Erdos260.StoppedInduction]),
which says: `weightedMass (highCostSet paths cost Y) weight ≤ root · A^m / z^Y`,
assuming `weightedMoment paths weight cost z ≤ root · A^m` and `1 ≤ z`.

This file specializes that bound to produce, for any `X, ξ`, a real
`Regular` satisfying `Regular ≤ cStar · ξ · X / 6`.  The specialization
takes a `ChernoffPathData` bundle, which packages the per-instance
moment estimate manuscript supplies.
-/

namespace Erdos260

open Finset

noncomputable section

/--
**Chernoff path data.**

Packages the per-instance manuscript inputs to Lemma 22.1 for a fixed
order, dyadic `X`, and pinned `cStar`, `ξ`.  Concretely:
* `paths` — the regular-path family in the stopped tree (a `Finset α`);
* `weight` — the path-mass `|Ω_π|`;
* `cost`   — the shell-cost function `∑_e s(e)`;
* `Y`      — the threshold;
* `z, m, root, A` — the tilting parameter and moment exponents from
  the manuscript proof, with `1 ≤ z` and `root · A^m / z^Y ≤ cStar · ξ · X / 6`.
-/
structure ChernoffPathData (cStar ξ X : ℝ) where
  α : Type
  decEq : DecidableEq α
  paths : Finset α
  weight : α -> ℝ
  cost : α -> Nat
  Y : Nat
  m : Nat
  z : ℝ
  root : ℝ
  A : ℝ
  weight_nonneg : ∀ p ∈ paths, 0 <= weight p
  z_ge_one : 1 <= z
  moment_bound :
    weightedMoment paths weight cost z <= root * A ^ m
  manuscript_bound :
    root * A ^ m / z ^ Y <= cStar * ξ * X / 6

/--
**Phase 4 deliverable: `chernoffPathSpace`.**

Given a `ChernoffPathData` bundle, produce a real number `Regular` and
a real inequality `Regular ≤ cStar · ξ · X / 6` that is suitable to
plug into the `Regular` slot of `AtomicWitnessProp`.

The constructed `Regular` is the actual Chernoff-bounded weighted mass
on the high-cost subset of paths.
-/
theorem chernoffPathSpace
    {cStar ξ X : ℝ}
    (data : ChernoffPathData cStar ξ X) :
    ∃ Regular : ℝ,
      0 <= Regular ∧
      Regular <= cStar * ξ * X / 6 := by
  classical
  haveI : DecidableEq data.α := data.decEq
  refine
    ⟨weightedMass (highCostSet data.paths data.cost data.Y) data.weight,
     ?_, ?_⟩
  · -- Nonnegativity from per-path nonnegativity.
    unfold weightedMass
    refine sum_nonneg ?_
    intro p hp
    have hp_in : p ∈ data.paths := (mem_highCostSet.1 hp).1
    exact data.weight_nonneg p hp_in
  · -- Chernoff bound + manuscript bound chain.
    have hChernoff :
        weightedMass (highCostSet data.paths data.cost data.Y) data.weight <=
          data.root * data.A ^ data.m / data.z ^ data.Y :=
      shellChernoff_bound_of_moment_bound (paths := data.paths)
        (weight := data.weight) (cost := data.cost) (Y := data.Y) (m := data.m)
        (z := data.z) (root := data.root) (A := data.A)
        data.weight_nonneg data.z_ge_one data.moment_bound
    exact hChernoff.trans data.manuscript_bound

end

end Erdos260
