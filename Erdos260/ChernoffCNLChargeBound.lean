import Mathlib
import Erdos260.Lemma221Regular
import Erdos260.AppendixG_Ladder
import Erdos260.AppendixK3_CNL
import Erdos260.CNLEntropy
import Erdos260.AppendixI_PhaseMass

/-!
# Wiring the proved 22.1 / Kraft cores to the charge-bridge phase terms

`AppendixI_PhaseMass.lean` names the six explicit summands of `ClosurePhaseMass`.
Two of them are the analytic phases this file connects to their **already-proved**
cores:

* `termChernoff data = weightedMass (highCostSet …) data.chernoff.weight`
  — the high-cost regular-path tail mass (Lemma 22.1);
* `termCnl data = cleanCNLKraftSum … * shellFactor * X * Ij`
  — the clean Kraft-weighted CNL tail (Theorem G.6 / Appendix L.1).

`AppendixI_PackageBounds.lean` already shows each term fits the per-phase budget
`cStar·ξ·X/6` **through the opaque `ChernoffPathData.moment_bound` /
`CNLEntropyData.kraftSum_le` fields**.  Here we instead ground those two budgets
in the genuine analytic cores:

## Chernoff connector

`Lemma221Regular.lean` proves the regular-path moment factorization
(`regular_weightedMoment_le`), the shell-Chernoff tail bound
(`regular_shellChernoff_tail_le_budget`), and the 22.1A area-weighted closed form
(`regular_areaWeighted_le_closed`) as **unconditional theorems**, and packages the
geometric content as a `RegularStoppedChernoffFamily` (regularity + length
calibration).  We build a `ClosurePhaseData` whose Chernoff slot is
`RegularStoppedChernoffFamily.toChernoffPathData fam`, and prove

```
termChernoff (chargeBridgeClosurePhaseData fam …) ≤ cStar·ξ·X/6
```

by feeding `fam.calibration` straight into `regular_shellChernoff_tail_le_budget`.
So the bound holds with a **proved** moment factorization, not an assumed one.

## CNL connector

`AppendixG_Ladder.lean` proves the depth-`M` Kraft collapse `∑ 2^{-cH} ≤ C_Q^M`
(`pathKraft_le`, `liftPathKraft_le`) unconditionally; `AppendixK3_CNL.lean`
packages it as `CNLClusterEncodingData.kraftSum_le`.  The connector
`termCnl_le_budget_of_kraft` takes exactly the Kraft bound
`cleanCNLKraftSum … ≤ C_Q^M` plus the shell budget
`C_Q^M·shellFactor·X·Ij ≤ cStar·ξ·X/6` and concludes `termCnl ≤ cStar·ξ·X/6`.
Specialized to `SixPhaseFactoryData` (whose CNL slot already *is* a
`CNLClusterEncodingData`), the Kraft hypothesis is discharged by the proved
collapse, giving `termCnl phases.toClosurePhaseData ≤ cStar·ξ·X/6` directly.

## What stays a faithful primitive (not fabricated)

* the `RegularStoppedChernoffFamily` itself — i.e. *the selected stopped paths are
  regular* with the manuscript per-path mass bound and the length-vs-threshold
  calibration `m ≤ c₁Y` (the genuinely geometric content of Lemma 22.1);
* the identification of the concrete selected-transition CNL cluster with the
  abstract ladder Kraft sum (carried inside `CNLClusterEncodingData.kraftSum_le`),
  and the shell-budget calibration `C_Q^M·shellFactor·X·Ij ≤ cStar·ξ·X/6`;
* the four non-analytic phase bundles (tower / DensePack / return / run), carried
  through unchanged.

No `sorry`, `axiom`, or `admit`.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## Charge-bridge phase data grounded in the two analytic cores

`chargeBridgeClosurePhaseData` plugs the proved Lemma 22.1 regular family into the
Chernoff slot (via `RegularStoppedChernoffFamily.toChernoffPathData`) and the
proved Kraft-collapse cluster encoding into the CNL slot (via
`CNLClusterEncodingData.toCNLEntropyData`).  The remaining four phase bundles are
supplied as the non-analytic leaves. -/

/-- A `ClosurePhaseData` whose Chernoff phase is the proved regular-path family of
Lemma 22.1 and whose CNL phase is the proved Kraft-collapse cluster encoding.  The
tower / DensePack / return / run phases are the supplied non-analytic leaves. -/
def chargeBridgeClosurePhaseData
    {cStar ξ X : ℝ}
    (fam : RegularStoppedChernoffFamily cStar ξ X)
    (cnl : CNLClusterEncodingData cStar ξ X)
    (tower : TowerPackageData cStar ξ X)
    (densePack : DensePackData cStar ξ X)
    (returnPkg : ReturnPackageData cStar ξ X)
    (run : RunPackageData cStar ξ X) :
    ClosurePhaseData cStar ξ X where
  chernoff := fam.toChernoffPathData
  cnl := cnl.toCNLEntropyData
  tower := tower
  densePack := densePack
  returnPkg := returnPkg
  run := run

/-! ## Chernoff connector (Lemma 22.1 tail → `termChernoff`) -/

/--
**Regular shell-Chernoff tail = the `termChernoff` value (faithful).**

For a regular stopped family, the proved tail bound
`regular_shellChernoff_tail_le_budget` already controls exactly the weighted
high-cost mass that *is* `termChernoff` of any `ClosurePhaseData` whose Chernoff
slot is `fam.toChernoffPathData`.  Calibrated against the Chernoff phase budget
(`budget := cStar·ξ·X/6`, which is `fam.calibration`), this gives the budget
bound on the raw tail mass. -/
theorem weightedMass_regularHighCost_le_budget
    {cStar ξ X : ℝ} (fam : RegularStoppedChernoffFamily cStar ξ X) :
    weightedMass
        (highCostSet
          (Fintype.piFinset (fun _ : Fin fam.m => Finset.range (fam.G + 1)))
          (fun σ => ∑ i, shellCost fam.Csh (σ i)) fam.Y)
        fam.weight
      ≤ cStar * ξ * X / 6 :=
  regular_shellChernoff_tail_le_budget fam.Csh fam.G fam.m fam.Y
    fam.rootMass fam.K fam.z (cStar * ξ * X / 6) fam.z_ge_one fam.weight
    fam.weight_nonneg fam.regular fam.calibration

/--
**Chernoff phase budget from a regular family (faithful).**

The Chernoff phase term of `chargeBridgeClosurePhaseData` fits the manuscript
per-phase budget `cStar·ξ·X/6`.  This ties the **proved** Lemma 22.1 shell-Chernoff
tail (`regular_shellChernoff_tail_le_budget`, whose moment factorization is the
proved `regular_weightedMoment_le`) to the charge-bridge `termChernoff`: the only
analytic input is the regular family's `calibration`, i.e. the manuscript length
condition `m ≤ c₁Y`. -/
theorem termChernoff_chargeBridge_le
    {cStar ξ X : ℝ}
    (fam : RegularStoppedChernoffFamily cStar ξ X)
    (cnl : CNLClusterEncodingData cStar ξ X)
    (tower : TowerPackageData cStar ξ X)
    (densePack : DensePackData cStar ξ X)
    (returnPkg : ReturnPackageData cStar ξ X)
    (run : RunPackageData cStar ξ X) :
    termChernoff
        (chargeBridgeClosurePhaseData fam cnl tower densePack returnPkg run)
      ≤ cStar * ξ * X / 6 :=
  weightedMass_regularHighCost_le_budget fam

/--
**Chernoff phase witness from a regular family (faithful).**

The existence form `∃ Regular, 0 ≤ Regular ∧ Regular ≤ cStar·ξ·X/6` consumed by
the atomic witness; this is `chernoffPathSpace_of_regularFamily`, whose witness is
exactly the `termChernoff` value bounded above. -/
theorem chargeBridge_chernoffPhase_exists
    {cStar ξ X : ℝ} (fam : RegularStoppedChernoffFamily cStar ξ X) :
    ∃ Regular : ℝ, 0 ≤ Regular ∧ Regular ≤ cStar * ξ * X / 6 :=
  chernoffPathSpace_of_regularFamily fam

/--
**Lemma 22.1A area-weighted shell-paid budget (faithful companion).**

The proved 22.1A closed form `regular_areaWeighted_le_closed` resums the layered
Chernoff sum into `rootMass·(K·tiltSum)^m·z/(z-1)`.  Calibrated against the
Chernoff phase budget, the area-weighted shell mass `∑_b weight(b)·Nsh(b)` of the
regular family fits `cStar·ξ·X/6`.  The shell-paid multiplier `Nsh`, its per-level
calibration `hcal` (`Nsh(b) > j ⟹ cost(b) ≥ j`), the strict tilt `1 < z`, the
mass nonnegativity, and the area budget calibration `hbudget` are the faithful
22.1A inputs. -/
theorem regularFamily_areaWeighted_le_budget
    {cStar ξ X : ℝ} (fam : RegularStoppedChernoffFamily cStar ξ X)
    (Ymax : ℕ) (Nsh : (Fin fam.m → ℕ) → ℕ)
    (hz : 1 < fam.z) (hroot : 0 ≤ fam.rootMass) (hK : 0 ≤ fam.K)
    (hNsh_le :
      ∀ σ ∈ Fintype.piFinset (fun _ : Fin fam.m => Finset.range (fam.G + 1)),
        Nsh σ ≤ Ymax)
    (hcal :
      ∀ (j : ℕ) (σ),
        σ ∈ Fintype.piFinset (fun _ : Fin fam.m => Finset.range (fam.G + 1)) →
          j < Nsh σ → j ≤ ∑ i, shellCost fam.Csh (σ i))
    (hbudget :
      fam.rootMass * (fam.K * regularTiltSum fam.Csh fam.G fam.z) ^ fam.m
          * (fam.z / (fam.z - 1))
        ≤ cStar * ξ * X / 6) :
    ∑ σ ∈ Fintype.piFinset (fun _ : Fin fam.m => Finset.range (fam.G + 1)),
        fam.weight σ * (Nsh σ : ℝ)
      ≤ cStar * ξ * X / 6 :=
  (regular_areaWeighted_le_closed fam.Csh fam.G fam.m Ymax fam.rootMass fam.K fam.z
    hz hroot hK fam.weight Nsh fam.weight_nonneg fam.regular hNsh_le hcal).trans
    hbudget

/-! ## CNL connector (Kraft collapse → `termCnl`) -/

/--
**CNL phase budget from the Kraft bound (faithful connector).**

Given the proved Kraft collapse `cleanCNLKraftSum … ≤ C_Q^M` (Theorem G.6 /
Proposition G.2 via `pathKraft_le` / `liftPathKraft_le`) and the shell budget
`C_Q^M·shellFactor·X·Ij ≤ cStar·ξ·X/6`, the charge-bridge `termCnl` fits the CNL
phase budget `cStar·ξ·X/6`.

The argument is the nonnegative shell-factor monotonicity used by `cnlEntropy`:
multiply the Kraft bound by `shellFactor·X·Ij ≥ 0`, then chain the shell budget.
No analytic input beyond the two supplied bounds. -/
theorem termCnl_le_budget_of_kraft
    {cStar ξ X : ℝ} (data : ClosurePhaseData cStar ξ X)
    (hX_nonneg : 0 ≤ X)
    {CQ : ℝ} {M : ℕ}
    (hkraft :
      cleanCNLKraftSum data.cnl.paths data.cnl.BNDHeight data.cnl.c ≤ CQ ^ M)
    (hbudget :
      CQ ^ M * data.cnl.shellFactor * X * data.cnl.Ij ≤ cStar * ξ * X / 6) :
    termCnl data ≤ cStar * ξ * X / 6 := by
  show cleanCNLKraftSum data.cnl.paths data.cnl.BNDHeight data.cnl.c *
      data.cnl.shellFactor * X * data.cnl.Ij ≤ cStar * ξ * X / 6
  have hfac : 0 ≤ data.cnl.shellFactor * X * data.cnl.Ij :=
    mul_nonneg (mul_nonneg data.cnl.shellFactor_nonneg hX_nonneg) data.cnl.Ij_nonneg
  calc cleanCNLKraftSum data.cnl.paths data.cnl.BNDHeight data.cnl.c *
          data.cnl.shellFactor * X * data.cnl.Ij
      = cleanCNLKraftSum data.cnl.paths data.cnl.BNDHeight data.cnl.c *
          (data.cnl.shellFactor * X * data.cnl.Ij) := by ring
    _ ≤ CQ ^ M * (data.cnl.shellFactor * X * data.cnl.Ij) :=
        mul_le_mul_of_nonneg_right hkraft hfac
    _ = CQ ^ M * data.cnl.shellFactor * X * data.cnl.Ij := by ring
    _ ≤ cStar * ξ * X / 6 := hbudget

/--
**CNL phase budget for the charge-bridge phase data (faithful).**

Specializes `termCnl_le_budget_of_kraft` to `chargeBridgeClosurePhaseData`, whose
CNL slot is `cnl.toCNLEntropyData`.  The Kraft hypothesis is discharged by the
cluster encoding's `kraftSum_le` (the proved G.2/G.6 ladder collapse), and the
shell budget by its `manuscript_bound`. -/
theorem termCnl_chargeBridge_le
    {cStar ξ X : ℝ}
    (fam : RegularStoppedChernoffFamily cStar ξ X)
    (cnl : CNLClusterEncodingData cStar ξ X)
    (tower : TowerPackageData cStar ξ X)
    (densePack : DensePackData cStar ξ X)
    (returnPkg : ReturnPackageData cStar ξ X)
    (run : RunPackageData cStar ξ X)
    (hX_nonneg : 0 ≤ X) :
    termCnl
        (chargeBridgeClosurePhaseData fam cnl tower densePack returnPkg run)
      ≤ cStar * ξ * X / 6 :=
  termCnl_le_budget_of_kraft
    (chargeBridgeClosurePhaseData fam cnl tower densePack returnPkg run)
    hX_nonneg cnl.kraftSum_le cnl.manuscript_bound

/--
**CNL phase budget at the charge bridge (faithful).**

The charge bridge consumes `phases.toClosurePhaseData` for a
`SixPhaseFactoryData`, whose CNL slot already *is* a `CNLClusterEncodingData`.
Hence the proved Kraft collapse `phases.cnl.kraftSum_le` discharges the Kraft
hypothesis directly, giving `termCnl phases.toClosurePhaseData ≤ cStar·ξ·X/6`
with no opaque CNL field consumed. -/
theorem termCnl_sixPhase_le_budget
    {cStar ξ X : ℝ} (phases : SixPhaseFactoryData cStar ξ X)
    (hX_nonneg : 0 ≤ X) :
    termCnl phases.toClosurePhaseData ≤ cStar * ξ * X / 6 :=
  termCnl_le_budget_of_kraft phases.toClosurePhaseData hX_nonneg
    phases.cnl.kraftSum_le phases.cnl.manuscript_bound

end

end Erdos260
