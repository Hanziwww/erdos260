import Mathlib
import Erdos260.AppendixG_Chernoff
import Erdos260.CarryDataFactory

/-!
# Chernoff phase data provider

This file isolates the stopped-tree moment estimate required to construct the
`ChernoffPathData` field of `SixPhaseFactoryData`.
-/

namespace Erdos260

open Finset

noncomputable section

/-- Per-shell provider for the regular-path Chernoff data. -/
structure ChernoffDataProvider where
  constants : Erdos260Constants
  data :
    ∀ shell : FailingDyadicShell,
      shell.cQ = constants.cQ ->
        ChernoffPathData constants.cStar constants.ξ (shell.X : ℝ)

theorem ChernoffDataProvider.bound
    (provider : ChernoffDataProvider)
    {shell : FailingDyadicShell}
    (hcQ : shell.cQ = provider.constants.cQ) :
    ∃ Regular : ℝ,
      0 <= Regular ∧
      Regular <= provider.constants.cStar * provider.constants.ξ * (shell.X : ℝ) / 6 :=
  chernoffPathSpace (provider.data shell hcQ)

end

end Erdos260
