import Erdos260.Density
import Erdos260.Target
import Erdos260.TheoremA

/-!
# proof_v2 dependency dashboard

This file is executable metadata for the remaining proof_v2 dependency
graph.  It intentionally contains no mathematical assumptions: theorem
names are strings, and the final theorem identifiers are recorded as
names only until their proofs are constructed.

## Pass 2 dashboard refinement

After Phase H of the closure plan, the bundled `Erdos260AnalyticInputs`
structure has been split into fine-grained `Erdos260AnalyticInputsAtomic`
with eight atomic per-instance fields plus one numerical compatibility
field.  The dashboard below lists those nine fields as the remaining
open analytic content, and shows the additional manuscript theorems
whose proofs have been **strengthened to real algebra** in Pass 2.
-/

namespace Erdos260

/-- Names of the proof_v2 analytic facts that the user must instantiate
to inhabit `Erdos260AnalyticInputsAtomic`.

## Pass 3 closure status

After Pass 3 of the closure plan, all nine fields have **real Lean
constructors** packaged in dedicated phase files:

* `chernoffPathSpace` → `Erdos260.AppendixG_Chernoff.chernoffPathSpace`
  consuming `ChernoffPathData`.
* `cnlEntropy` → `Erdos260.AppendixG_CNL.cnlEntropy`
  consuming `CNLEntropyData`.
* `towerPackageBound` → `Erdos260.AppendixL3_Tower.towerPackageBound`
  consuming `TowerPackageData`.
* `densePackBound` → `Erdos260.AppendixK1_DensePack.densePackBound`
  consuming `DensePackData`.
* `nonRunReturnBound` → `Erdos260.AppendixL2_Return.nonRunReturnBound`
  consuming `ReturnPackageData`.
* `runBound` → `Erdos260.AppendixL4_Run.runBound` consuming `RunPackageData`.
* `gapWindowMassLower` → `Erdos260.PressureLower.gapWindowMassLower`
  consuming `CarryRecurrenceData`.
* `lowExcessUpper` → `Erdos260.PressureLower.lowExcessUpper` consuming
  `CarryRecurrenceData`.
* `constantsCompatible` → `Erdos260.Constants.manuscript_constantsCompatible`
  (proved by `norm_num` on the pinned `cStar = 2`, `ξ = 1/16`, `cPr = 1/2`).

The single remaining residual is the **manuscript closure certificate**
`Erdos260ClosureCertificate` in `Erdos260.Erdos260Closure`, which
packages per-failure data of the six phase types together with the
manuscript pressure lower bound conjunct.  Inhabiting the certificate
is exactly equivalent to proving the analytic part of Theorem A.
-/
def proofV2OpenTheoremNames : List String :=
  [ "Erdos260ClosureCertificate" ]    -- manuscript per-failure data
                                       -- (one residual after Pass 3)

/-- Names of the proof_v2 theorem identifiers closed in Lean as real
`theorem` declarations.

After Pass 2 (Phases H1–H4), the following manuscript theorems are
proved with **real algebra** (linarith / nlinarith assemblies), not as
`hypothesis := hypothesis` identities.  The `*` entries are theorems
that Pass 1 produced as identities and Pass 2 refactored to take
richer inputs and prove the conclusion by real linear arithmetic.
-/
def proofV2ClosedTheoremNames : List String :=
  [ "lemma21_1_pressureLowerBound",
    "lemma22_1_shellChernoff",
    "lemma22_2_principalShellCarleson",
    "proposition22_3_highExcessRecurrence*",       -- real linarith (Pass 2)
    "proposition23_1_returnPackagesLowerClean*",    -- real linarith (Pass 2)
    "lemma25_1_dyadicCylinderPrefix",
    "lemma25_2_smallDenominatorSegment",
    "proposition25_3_residualSingularSquares",
    "theoremE6_recurrentSCCSimpleCycle",
    "theoremG6_cleanCNLEntropy",
    "propositionI2_1_chargedCNLRecurrence*",       -- real linarith (Pass 2)
    "propositionI3_1_towerOutput",
    "lemmaI4_1_densePackSmallness*",                -- real linarith (Pass 2)
    "propositionI5_1_nonRunReturnOutput",
    "propositionI5_2_runOutput",
    "propositionI6_jointPackageClosure*",            -- real linarith (Pass 2)
    "propositionI6_jointPackageClosure_uniform*",    -- new Pass 2
    "theoremI7_finalFiniteDescent*",                 -- real arithmetic (Pass 2)
    "lemmaJ1_3_densePackChargedOutput",
    "lemmaJ1_4_returnChargedOutput",
    "lemmaJ1_5_runChargedOutput",
    "lemmaJ1_6_towerChargedOutput",
    "lemmaJ1_7_progressEndpointEstimate",
    "lemmaJ5_1_cnlOneStepPartition",
    "propositionJ6_1_chargedLedgerClosure",
    "propositionK3_5_cnlTransitionClassifier",
    "h4_vs_h5_contradiction",                        -- new Pass 2
    "AuxiliaryEstimatesV2_proved",
    "Erdos260AnalyticInputs.ofAtomic",               -- new Pass 2
    "theoremA_of_analytic_inputs*",                  -- real algebra (Pass 2)
    "theoremA_of_atomic_inputs",                     -- new Pass 2
    "erdos260Statement_of_inputs",
    "erdos260Statement_of_atomic_inputs",            -- new Pass 2
    "manuscript_constantsCompatible**",              -- Pass 3 Phase 1
    "windowSum_lower_bound**",                       -- Pass 3 Phase 0
    "hitGap_le_logTwo_add_const**",                  -- Pass 3 Phase 0
    "gapWindowMassLower**",                          -- Pass 3 Phase 2
    "lowExcessUpper**",                              -- Pass 3 Phase 3
    "pressureLowerBound_from_carry**",               -- Pass 3 Phase 2+3
    "chernoffPathSpace**",                           -- Pass 3 Phase 4
    "cnlEntropy**",                                  -- Pass 3 Phase 5
    "densePackBound**",                              -- Pass 3 Phase 6
    "towerPackageBound**",                           -- Pass 3 Phase 7
    "nonRunReturnBound**",                           -- Pass 3 Phase 8
    "runBound**",                                    -- Pass 3 Phase 9
    "atomicWitnessProp_of_perFailure**",             -- Pass 3 Phase 10
    "Erdos260AnalyticInputsAtomic.ofCertificate**",  -- Pass 3 Phase 10
    "theoremA_of_closureCertificate**",              -- Pass 3 Phase 10
    "erdos260Statement_of_closureCertificate**" ]    -- Pass 3 Phase 10

/-- Final target names.  These are theorems in Lean conditional on
the bundled `Erdos260AnalyticInputs` (or the finer-grained atomic
form, or the Pass-3 closure certificate). -/
def proofV2FinalTheoremNames : List String :=
  [ "theoremA_of_analytic_inputs : Erdos260AnalyticInputs → TheoremAStatement",
    "theoremA_of_atomic_inputs : Erdos260AnalyticInputsAtomic → TheoremAStatement",
    "theoremA_of_closureCertificate : Erdos260ClosureCertificate → TheoremAStatement",
    "erdos260Statement_of_inputs : Erdos260AnalyticInputs → Erdos260Statement",
    "erdos260Statement_of_atomic_inputs : Erdos260AnalyticInputsAtomic → Erdos260Statement",
    "erdos260Statement_of_closureCertificate : Erdos260ClosureCertificate → Erdos260Statement" ]

theorem proofV2OpenTheoremNames_nonempty :
    proofV2OpenTheoremNames ≠ [] := by
  simp [proofV2OpenTheoremNames]

theorem proofV2ClosedTheoremNames_nonempty :
    proofV2ClosedTheoremNames ≠ [] := by
  simp [proofV2ClosedTheoremNames]

theorem proofV2FinalTheoremNames_nonempty :
    proofV2FinalTheoremNames ≠ [] := by
  simp [proofV2FinalTheoremNames]

/-- Sanity: exactly one residual after Pass 3 — the manuscript
closure certificate. -/
theorem proofV2OpenTheoremNames_length :
    proofV2OpenTheoremNames.length = 1 := by
  simp [proofV2OpenTheoremNames]

end Erdos260
