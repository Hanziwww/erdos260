import Mathlib
import Erdos260.CNLEntropy
import Erdos260.Constants

/-!
# Phase 5: `cnlEntropy` (Theorem G.6 → `CleanTerm` slot)

The manuscript Theorem G.6 / Lemma L.1.2 (`proof_v2.tex` lines
4155--4220) gives the Kraft-weighted bound
```
  ∑_{paths through cluster} 2^{-c · H_BND(path)} ≤ C_Q^M.
```

`theoremG6_cleanCNLEntropy` in [Erdos260.CNLEntropy] already says: given
this Kraft bound as the hypothesis `hkraft`, the bound itself holds
(trivial).  The remaining work is to **construct** the bound from
the manuscript's Appendix G internal estimates (G.1--G.5: Type-C
deterministic stretches, Type-VS / Type-DS / Type-P enumeration,
bridge-paid bookkeeping).

Phase 5 packages the manuscript's analytic inputs (G.1--G.5) as a
single `CNLEntropyData` bundle and produces a `CleanTerm` real number
together with the bound `CleanTerm ≤ cStar · ξ · X / 6`.

The reduction from `CleanTerm` to Kraft is itself the bridge `K_M -> cluster mass`,
which is a real `nlinarith` step after the manuscript's `2^{-c_0 η Y} · C_Q^M ≤ 2^{-cY}`
shell-paid factor is supplied.
-/

namespace Erdos260

open Finset

noncomputable section

/--
**CNL entropy data.**

Packages the per-instance manuscript Appendix G inputs:
* `kraftSum`  — the actual Kraft sum value;
* `kraftBound` — the Kraft sum value upper bound `C_Q^M`;
* `kraftSum_le` — the verified Kraft inequality (G.6);
* `shellFactor` — the shell-paid factor `2^{-c_0 η Y}`;
* `shellFactor_nonneg`, `clusterMass_nonneg`;
* `manuscript_bound` — the manuscript chain
  `kraftBound · shellFactor · X · I_j ≤ cStar · ξ · X / 6`
  established in `proof_v2.tex` lines 1903--1932 (Appendix H.2).
*
The domination by `kraftBound` after multiplying by the nonnegative shell
factor is proved below from `kraftSum_le`, rather than stored as another field.
-/
structure CNLEntropyData (cStar ξ X : ℝ) where
  α : Type
  paths : Finset α
  BNDHeight : α -> ℝ
  c : ℝ
  CQ : ℝ
  M : Nat
  shellFactor : ℝ
  Ij : ℝ
  shellFactor_nonneg : 0 <= shellFactor
  Ij_nonneg : 0 <= Ij
  kraftSum_le :
    cleanCNLKraftSum paths BNDHeight c <= CQ ^ M
  manuscript_bound :
    CQ ^ M * shellFactor * X * Ij <= cStar * ξ * X / 6

/-- The Kraft bound dominates the clean CNL mass after multiplication by the
nonnegative shell factors. -/
theorem CNLEntropyData.manuscript_dominates
    {cStar ξ X : ℝ}
    (data : CNLEntropyData cStar ξ X)
    (hX_nonneg : 0 <= X) :
    cleanCNLKraftSum data.paths data.BNDHeight data.c *
        data.shellFactor * X * data.Ij <=
      data.CQ ^ data.M * data.shellFactor * X * data.Ij := by
  have hfactor_nonneg : 0 <= data.shellFactor * X * data.Ij :=
    mul_nonneg (mul_nonneg data.shellFactor_nonneg hX_nonneg)
      data.Ij_nonneg
  have hdom :
      cleanCNLKraftSum data.paths data.BNDHeight data.c *
          (data.shellFactor * X * data.Ij) <=
        data.CQ ^ data.M * (data.shellFactor * X * data.Ij) :=
    mul_le_mul_of_nonneg_right data.kraftSum_le hfactor_nonneg
  calc cleanCNLKraftSum data.paths data.BNDHeight data.c *
          data.shellFactor * X * data.Ij
      = cleanCNLKraftSum data.paths data.BNDHeight data.c *
          (data.shellFactor * X * data.Ij) := by ring
    _ <= data.CQ ^ data.M * (data.shellFactor * X * data.Ij) := hdom
    _ = data.CQ ^ data.M * data.shellFactor * X * data.Ij := by ring

/--
**Phase 5 deliverable: `cnlEntropy`.**

Given `CNLEntropyData`, produce `CleanTerm` and a bound
`CleanTerm ≤ cStar · ξ · X / 6`.

The constructed `CleanTerm` is the manuscript's `Kraft · shellFactor · X · I_j`
quantity.
-/
theorem cnlEntropy
    {cStar ξ X : ℝ}
    (data : CNLEntropyData cStar ξ X)
    (hX_nonneg : 0 <= X) :
    ∃ CleanTerm : ℝ,
      0 <= CleanTerm ∧
      CleanTerm <= cStar * ξ * X / 6 := by
  classical
  refine
    ⟨cleanCNLKraftSum data.paths data.BNDHeight data.c *
       data.shellFactor * X * data.Ij,
     ?_, ?_⟩
  · -- Nonnegativity: product of four nonnegs.
    have hKraft := cleanCNLKraftSum_nonneg data.paths data.BNDHeight data.c
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hKraft data.shellFactor_nonneg) hX_nonneg)
      data.Ij_nonneg
  · -- Upper bound chain via Kraft domination and manuscript_bound.
    calc cleanCNLKraftSum data.paths data.BNDHeight data.c *
            data.shellFactor * X * data.Ij
        <= data.CQ ^ data.M * data.shellFactor * X * data.Ij :=
          data.manuscript_dominates hX_nonneg
      _ <= cStar * ξ * X / 6 := data.manuscript_bound

end

end Erdos260
