import Erdos260.RunSupportMaxCore
import Erdos260.RunClass5Routing
import Erdos260.RunClass5BoundaryClosure
import Erdos260.RunNumericSettlement
import Erdos260.Lemma251Prop253Cylinder
import Erdos260.FailingShellPeriodicityCore
import Erdos260.RunDescentConstruction
import Erdos260.GlobalRunAssembly

/-!
# §26 positive-density run-area estimate — support-numeric formalization tower

Root-wired support-numeric bridge for the manuscript §26
(`positive-density-runarea-estimate`, lines 1638–1687 of the target tex) lemma tower
toward the sharp Run residual `RunClass5LeafSupportMaxCoreResidual` / `RunClass5LeafResidual`.

## Manuscript §26 → Lean roadmap (statement-level)

| Manuscript step | Lean target | Status in repo |
|---|---|---|
| Convention: `κ < min{1/(40Q), c₀(Q,½)/10, ρ_D(Q)/8}`, `r = ⌊κL⌋` | `erdos260Constants`, `ctx.n24CarryData.r`, `proofV4CarryOrder_le_L` | **proved** (constants layer) |
| Split positive runs: mean-low / local-spike / boundary | `RunLocalSplitData`, `RunOutputAbsorptionData`, `RunBranchTrichotomy` | **interface proved** (`GlobalRunAssembly`, `RunDescentConstruction`) |
| Mean-low-density runs: density `< 2κ < ρ₀(Q)` | `MeanLowRunWindow`, `classify … = 0` | **interface proved** (`PackageRealization`) |
| Prop 24.3: low density ⇒ no long repetition | `fixedDensity_carry_repetition`, `fixedDensity_low_density_excludes_completion` | **proved** (`FailingShellPeriodicityCore`) |
| Prop 25.3: near-square residual squares controlled | `proposition_25_3_certified`, `residual_dense_branch_excluded` | **proved** (`Lemma251Prop253Cylinder`) |
| Local-spike: deep `(r+1)`-gap block → low atom / AP tower | `localSpike_le_return`, tower routing | **routing proved**; **§26 budget assembly open** |
| Boundary windows → dirty recursion / merge | `boundary_le_return` | **routing proved**; **§26 budget assembly open** |
| Appendices D–F same-threshold compression → (26.1) | `RunOutputAbsorptionData`, `termRun_bound_of_construction` | **I.5.2 `/6` floor proved**; **`/12` base slot open** |
| Linear max-form: `c₀·#fibre·max excess ≤ (c⋆ξ/12)·#support` | `RunClass5LeafSupportMaxCoreResidual.hproduct` | **proved from `Section26SupportNumericHyp`** |
| Consequence `#fibre ≲ X/Y` | `runSupportMaxCore_forces_linear_support` | **proved** (consequence of `hproduct`) |
| I.6S stage map + L.4.2 half-decrease on shortenings | `stageOf`, `hhalf` fields of residual | **OPEN** (genuine charge geometry) |
| Equivalence max-core ↔ leaf residual | `toLeafResidual` / `toSupportMaxCoreResidual` | **proved** (`RunSupportMaxCore`) |
| Obstruction: quadratic product-core over-claims | `runSupportProductCore_forces_quadratic_X` | **proved** |
| Obstruction: dyadic-count pins multiplier ~ L deep | `runSupportDyadicCount_forces_mult_X` | **proved** |

## What this scratch file delivers

1. **Structural packaging** of the §26 run trichotomy and the linear max-form target.
2. **Proved bridges** from the dyadic-count settlement inequality `RunNumericIneq` to the
   honest max-form residual (via `runBaseMaxExcess_le_runDyadicMult_uncond`).
3. **Proved regime fragments** inherited from `RunNumericSettlement` (vacuous on actual
   contexts where `n24_gate_violated` forces `r ≥ 1`, but logically correct).
4. **A sharp residual core** `Section26SupportNumericHyp`: the support-relative
   I.4.1/K.4 numeric at the realized multiplier `runBaseMaxExcess`.
5. **Proved bridge** `Section26SupportNumericHyp → Section26PositiveDensityRunAreaHyp`;
   no no-input theorem is asserted.

Root imported by `Erdos260.lean`.  No `sorry`, no `admit`, no new `axiom`.
-/

namespace Erdos260

open Finset

noncomputable section

set_option linter.unusedVariables false
set_option maxHeartbeats 400000

/-! ## Part 1 — the §26 run trichotomy packaging (manuscript lines 1647–1653) -/

/-- **§26 run-slot trichotomy masses** — the mean-low-density, local-spike, and boundary
contributions before same-threshold compression (display 26.1 left-hand side). -/
structure Section26RunTrichotomy where
  meanLow : ℝ
  localSpike : ℝ
  boundary : ℝ
  h_nonneg : 0 ≤ meanLow ∧ 0 ≤ localSpike ∧ 0 ≤ boundary

/-- The §26 charged run mass is bounded by the trichotomy sum plus absorbed terms
(tower / return / dense-pack / variation-drop / old-residual / small error).  The
manuscript display (26.1) packages these; here we record only the trichotomy slice. -/
def Section26RunTrichotomy.total (T : Section26RunTrichotomy) : ℝ :=
  T.meanLow + T.localSpike + T.boundary

theorem Section26RunTrichotomy.total_nonneg (T : Section26RunTrichotomy) :
    0 ≤ T.total := by
  unfold Section26RunTrichotomy.total
  linarith [T.h_nonneg.1, T.h_nonneg.2.1, T.h_nonneg.2.2]

/-! ## Part 2 — Prop 24.3 / 25.3 hooks (manuscript lines 1648–1650)

Mean-low-density exclusion (Prop 25.3 dense branch):
`Lemma251Prop253Cylinder.residual_dense_branch_excluded`,
`Lemma251Prop253Cylinder.density_contradiction`.

Fixed-density repetition bound (Prop 24.3):
`FailingShellPeriodicityCore.fixedDensity_carry_repetition`,
`FailingShellPeriodicityCore.fixedDensity_low_density_excludes_completion`.
-/

/-! ## Part 3 — the linear max-form target and its sparsity consequence -/

/-- **The §26 linear max-form product inequality** at a context — verbatim the
`hproduct` field of `RunClass5LeafSupportMaxCoreResidual`, specialised to the
zero stage map (where `runBaseFibre = fibre₅`). -/
def Section26LinearMaxForm (ctx : ActualFailureContext) : Prop :=
  erdos260Constants.c0
      * ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card : ℝ)
      * runBaseMaxExcess ctx (fun _ => 0)
    ≤ (erdos260Constants.cStar * erdos260Constants.ξ / 12)
      * ((supportShell ctx.d ctx.X).card : ℝ)

/-- **`hproduct` forces linear sparsity at the zero-stage base fibre** — the
`runSupportMaxCore_forces_linear_support` conclusion specialised to `stageOf := fun _ => 0`. -/
theorem section26_linearMaxForm_forces_fibre_sparsity (ctx : ActualFailureContext)
    (h : Section26LinearMaxForm ctx) :
    erdos260Constants.c0 * ((runBaseFibre ctx (fun _ => 0)).card : ℝ) * ctx.n24CarryData.Y
      ≤ (erdos260Constants.cStar * erdos260Constants.ξ / 12)
        * ((supportShell ctx.d ctx.X).card : ℝ) :=
  runSupportMaxCore_forces_linear_support (runCoreOfClass5ProductBound ctx h)

/-- **Routed-fibre form** of the sparsity consequence (`runBaseFibre_zeroStage`). -/
theorem section26_linearMaxForm_forces_routed_fibre_sparsity (ctx : ActualFailureContext)
    (h : Section26LinearMaxForm ctx) :
    erdos260Constants.c0
        * ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ (erdos260Constants.cStar * erdos260Constants.ξ / 12)
        * ((supportShell ctx.d ctx.X).card : ℝ) := by
  rw [← runBaseFibre_zeroStage]
  exact section26_linearMaxForm_forces_fibre_sparsity ctx h

/-! ## Part 4 — proved bridges from the dyadic-count settlement route -/

/-- **Sound shrink: `RunNumericIneq` (dyadic multiplier) ⇒ §26 linear max-form
(genuine max multiplier).**  Uses `runBaseMaxExcess ≤ runDyadicMult` unconditionally
(`runBaseMaxExcess_le_runDyadicMult_uncond`).  NOTE: this direction is sound but
NOT the manuscript's sharp §26 input — the dyadic settlement `RunNumericSettlementHyp`
still over-pins the multiplier on deep shells (`runSupportDyadicCount_forces_mult_X`). -/
theorem section26_linearMaxForm_of_runNumericIneq (ctx : ActualFailureContext)
    (h : RunNumericIneq ctx) : Section26LinearMaxForm ctx := by
  unfold Section26LinearMaxForm
  have hc0N : 0 ≤ erdos260Constants.c0
      * ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card : ℝ) :=
    mul_nonneg erdos260Constants.c0_pos.le (Nat.cast_nonneg _)
  calc erdos260Constants.c0
          * ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card : ℝ)
          * runBaseMaxExcess ctx (fun _ => 0)
      ≤ erdos260Constants.c0
          * ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card : ℝ)
          * runDyadicMult ctx :=
        mul_le_mul_of_nonneg_left
          (runBaseMaxExcess_le_runDyadicMult_uncond ctx (fun _ => 0)) hc0N
    _ ≤ (erdos260Constants.cStar * erdos260Constants.ξ / 12)
          * ((supportShell ctx.d ctx.X).card : ℝ) := h

/-- **`RunNumericIneq` ⇒ the max-form Run residual** at the zero stage map. -/
def runSupportMaxCoreResidual_of_runNumericIneq (ctx : ActualFailureContext)
    (h : RunNumericIneq ctx) : RunClass5LeafSupportMaxCoreResidual ctx :=
  runCoreOfClass5ProductBound ctx (section26_linearMaxForm_of_runNumericIneq ctx h)

/-- **`RunNumericIneq` ⇒ the sharp leaf residual.** -/
def runClass5LeafResidual_of_runNumericIneq (ctx : ActualFailureContext)
    (h : RunNumericIneq ctx) : RunClass5LeafResidual ctx :=
  (runSupportMaxCoreResidual_of_runNumericIneq ctx h).toLeafResidual

/-- **Family bridge: dyadic settlement hypothesis ⇒ max-form residual family.** -/
def runSupportMaxCoreResidual_of_runNumericSettlement
    (h : RunNumericSettlementHyp) (ctx : ActualFailureContext) :
    RunClass5LeafSupportMaxCoreResidual ctx := by
  by_cases hr : ctx.n24CarryData.r = 0
  · exact runCoreOfClass5FibreEmpty ctx (class5Fibre_empty_of_r_eq_zero ctx hr)
  · have hnum := h ctx (by omega)
    exact runSupportMaxCoreResidual_of_runNumericIneq ctx
      (runNumericIneq_of_cycleNumericCloses ctx hnum)

/-! ## Part 5 — proved regime fragments (vacuous on actual ungated contexts) -/

/-- On **`r = 0` shells** the class-5 fibre is empty, so §26 linear max-form holds
trivially.  On every `ActualFailureContext`, `n24_gate_violated` forces `r ≥ 1`, so
this lemma is vacuous there — recorded for logical completeness. -/
theorem section26_linearMaxForm_of_r_eq_zero (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0) : Section26LinearMaxForm ctx := by
  have hcard : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card = 0 :=
    Finset.card_eq_zero.mpr (class5Fibre_empty_of_r_eq_zero ctx hr)
  have hmax : runBaseMaxExcess ctx (fun _ => 0) = 0 := by
    have hbase0 : (runBaseFibre ctx (fun _ => 0)).card = 0 := by
      rw [runBaseFibre_zeroStage, hcard]
    exact runBaseMaxExcess_eq_zero_of_card_eq_zero ctx (fun _ => 0) hbase0
  unfold Section26LinearMaxForm
  rw [hcard, hmax]
  have hA : 0 ≤ erdos260Constants.cStar * erdos260Constants.ξ / 12 :=
    div_nonneg
      (mul_nonneg erdos260Constants.cStar_pos.le erdos260Constants.ξ_pos.le)
      (by norm_num)
  have hS : (0 : ℝ) ≤ ((supportShell ctx.d ctx.X).card : ℝ) := Nat.cast_nonneg _
  simpa using mul_nonneg hA hS

/-- **Modulus `< 5` shells** — class-5 fibre empty (`runCoreOfModulusLtFive`). -/
theorem section26_linearMaxForm_of_modulusLtFive (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q < 5) : Section26LinearMaxForm ctx := by
  have hempty := class5Fibre_empty_of_modulus_lt_five ctx hq
  have hcard : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card = 0 :=
    Finset.card_eq_zero.mpr hempty
  have hmax : runBaseMaxExcess ctx (fun _ => 0) = 0 := by
    have hbase0 : (runBaseFibre ctx (fun _ => 0)).card = 0 := by
      rw [runBaseFibre_zeroStage, hcard]
    exact runBaseMaxExcess_eq_zero_of_card_eq_zero ctx (fun _ => 0) hbase0
  unfold Section26LinearMaxForm
  rw [hcard, hmax]
  have hA : 0 ≤ erdos260Constants.cStar * erdos260Constants.ξ / 12 :=
    div_nonneg
      (mul_nonneg erdos260Constants.cStar_pos.le erdos260Constants.ξ_pos.le)
      (by norm_num)
  have hS : (0 : ℝ) ≤ ((supportShell ctx.d ctx.X).card : ℝ) := Nat.cast_nonneg _
  simpa using mul_nonneg hA hS

/-! ## Part 6 — the open §26 core (manuscript positive-density assembly) -/

/-- **The irreducible §26 positive-density run-area hypothesis** — the manuscript's
full trichotomy split + Appendices D–F same-threshold compression, delivering the
genuine linear max-form at the *realized* multiplier `runBaseMaxExcess`, not the
dyadic ceiling pin.  This is strictly stronger than `RunNumericSettlementHyp` on deep
shells where `runBaseMaxExcess ≪ runDyadicMult`. -/
def Section26PositiveDensityRunAreaHyp : Prop :=
  ∀ ctx : ActualFailureContext, Section26LinearMaxForm ctx

/-!
The next bridge records exactly what the proved dyadic-count settlement gives at
the Section 26 interface: it is a sound conditional route to the linear max-form,
but it is still not the manuscript's no-input run-area assembly.
-/

/-- **Conditional Section 26 bridge from dyadic numeric settlement.**  If every
`r >= 1` shell satisfies the cycle-density numeric condition, then the Section 26
linear max-form holds at every actual context. -/
theorem section26_positiveDensityRunArea_of_runNumericSettlement
    (h : RunNumericSettlementHyp) :
    Section26PositiveDensityRunAreaHyp := by
  intro ctx
  exact section26_linearMaxForm_of_runNumericIneq ctx ((runNumericField_settled h) ctx)

/-- **Target residual family** — at the zero stage map, equivalent to
`RunClass5LeafResidual` by the proved equivalence in `RunSupportMaxCore`. -/
abbrev RunClass5Section26Family :=
  ∀ ctx : ActualFailureContext, RunClass5LeafSupportMaxCoreResidual ctx

/-- §26 hypothesis ⇒ max-form residual at a context (zero stage map). -/
def runSupportMaxCoreResidual_of_section26
    (h : Section26PositiveDensityRunAreaHyp) (ctx : ActualFailureContext) :
    RunClass5LeafSupportMaxCoreResidual ctx :=
  runCoreOfClass5ProductBound ctx (h ctx)

/-- §26 hypothesis ⇒ sharp leaf residual at a context. -/
def runClass5LeafResidual_of_section26
    (h : Section26PositiveDensityRunAreaHyp) (ctx : ActualFailureContext) :
    RunClass5LeafResidual ctx :=
  (runSupportMaxCoreResidual_of_section26 h ctx).toLeafResidual

/-- **The capstone endpoint from §26** — would discharge the Run atom of
`erdos260_capstone_final` if proved unconditionally. -/
theorem erdos260_of_section26_and_highExcess
    (h : Section26PositiveDensityRunAreaHyp)
    (he : HighExcessRoutingCountResidual) : Erdos260Statement :=
  erdos260_ofSupportMaxCore_and_highExcess
    (fun ctx => runSupportMaxCoreResidual_of_section26 h ctx) he

/-- **Conditional capstone endpoint through the dyadic numeric route.**  This
packages the proved Section 26 bridge with the existing high-excess capstone:
`RunNumericSettlementHyp` supplies the max-form Run residual, while
`HighExcessRoutingCountResidual` supplies the independent high-excess atom. -/
theorem erdos260_of_runNumericSettlement_and_highExcess
    (h : RunNumericSettlementHyp)
    (he : HighExcessRoutingCountResidual) : Erdos260Statement :=
  erdos260_of_section26_and_highExcess
    (section26_positiveDensityRunArea_of_runNumericSettlement h) he

/-- **The support-relative §26 numeric at one context.**

This is the sharp spread-0 form isolated in `RunLeafUnconditional`: a per-hit
dense-marker floor `rhoL`, support packing of the base-stage fibre, and the K.4
smallness bound for the genuine pointwise max multiplier `runBaseMaxExcess`.
It is exactly the missing numerical content needed to read off the support-relative
linear max-form. -/
structure Section26SupportNumericInputs (ctx : ActualFailureContext) where
  /-- The per-hit dense-marker floor, manuscript `ρ_D L`. -/
  rhoL : ℝ
  /-- The per-hit dense-marker floor is positive. -/
  hrhoL_pos : 0 < rhoL
  /-- I.4.1 hit packing of base-stage fibre markers into the shell support. -/
  hpack : ((runBaseFibre ctx (fun _ => 0)).card : ℝ) * rhoL
    ≤ ((supportShell ctx.d ctx.X).card : ℝ)
  /-- K.4 smallness at the `/12` run-area budget for the pointwise max multiplier. -/
  hsmall : (erdos260Constants.c0 / rhoL) * runBaseMaxExcess ctx (fun _ => 0)
    ≤ erdos260Constants.cStar * erdos260Constants.ξ / 12

/-- **Support-relative §26 numeric ⇒ linear max-form.**

This is the exact algebraic read-off of the manuscript §26 support-relative
estimate:
`c₀ · #fibre₅ · max_excess ≤ (c⋆ξ/12) · #supportShell`. -/
theorem section26_linearMaxForm_of_supportNumeric (ctx : ActualFailureContext)
    (I : Section26SupportNumericInputs ctx) : Section26LinearMaxForm ctx := by
  have hC : 0 ≤ erdos260Constants.cStar * erdos260Constants.ξ / 12 :=
    div_nonneg
      (mul_nonneg erdos260Constants.cStar_pos.le erdos260Constants.ξ_pos.le)
      (by norm_num)
  have hN : 0 ≤ ((runBaseFibre ctx (fun _ => 0)).card : ℝ) := Nat.cast_nonneg _
  have hsmall' :
      erdos260Constants.c0 * runBaseMaxExcess ctx (fun _ => 0)
        ≤ (erdos260Constants.cStar * erdos260Constants.ξ / 12) * I.rhoL := by
    have h := I.hsmall
    rw [div_mul_eq_mul_div, div_le_iff₀ I.hrhoL_pos] at h
    exact h
  unfold Section26LinearMaxForm
  rw [← runBaseFibre_zeroStage ctx]
  calc erdos260Constants.c0
          * ((runBaseFibre ctx (fun _ => 0)).card : ℝ)
          * runBaseMaxExcess ctx (fun _ => 0)
      = ((runBaseFibre ctx (fun _ => 0)).card : ℝ)
          * (erdos260Constants.c0 * runBaseMaxExcess ctx (fun _ => 0)) := by ring
    _ ≤ ((runBaseFibre ctx (fun _ => 0)).card : ℝ)
          * ((erdos260Constants.cStar * erdos260Constants.ξ / 12) * I.rhoL) :=
        mul_le_mul_of_nonneg_left hsmall' hN
    _ = (erdos260Constants.cStar * erdos260Constants.ξ / 12)
          * (((runBaseFibre ctx (fun _ => 0)).card : ℝ) * I.rhoL) := by ring
    _ ≤ (erdos260Constants.cStar * erdos260Constants.ξ / 12)
          * ((supportShell ctx.d ctx.X).card : ℝ) :=
        mul_le_mul_of_nonneg_left I.hpack hC

/-- The current faithful §26 residual: the support-relative numeric at every
actual failure context. -/
def Section26SupportNumericHyp : Prop :=
  ∀ ctx : ActualFailureContext, Nonempty (Section26SupportNumericInputs ctx)

/-- **Conditional Section 26 bridge from the sharp support-relative numeric.** -/
theorem section26_positiveDensityRunArea_of_supportNumeric
    (h : Section26SupportNumericHyp) :
    Section26PositiveDensityRunAreaHyp := by
  intro ctx
  obtain ⟨I⟩ := h ctx
  exact section26_linearMaxForm_of_supportNumeric ctx I

/-- Corollary: the Run atom closes from the support-relative §26 numeric. -/
def runClass5Section26_of_supportNumeric (h : Section26SupportNumericHyp)
    (ctx : ActualFailureContext) :
    RunClass5LeafSupportMaxCoreResidual ctx :=
  runSupportMaxCoreResidual_of_section26
    (section26_positiveDensityRunArea_of_supportNumeric h) ctx

/-- Direct sharp leaf-residual form of the Section 26 support-numeric bridge. -/
def runClass5LeafResidual_of_supportNumeric (h : Section26SupportNumericHyp)
    (ctx : ActualFailureContext) :
    RunClass5LeafResidual ctx :=
  (runClass5Section26_of_supportNumeric h ctx).toLeafResidual

/-! ## Part 7 — honest status inventory -/

/-- Family form of the Run class-5 residual supplied by the sharp support-relative
Section 26 numeric. -/
def runClass5Section26Family_of_supportNumeric (h : Section26SupportNumericHyp) :
    RunClass5Section26Family :=
  fun ctx => runClass5Section26_of_supportNumeric h ctx

/-- Sharp leaf-residual family supplied by the support-relative Section 26 numeric. -/
def runClass5LeafResidualFamily_of_supportNumeric (h : Section26SupportNumericHyp) :
    ∀ ctx : ActualFailureContext, RunClass5LeafResidual ctx :=
  fun ctx => runClass5LeafResidual_of_supportNumeric h ctx

/-- **Capstone endpoint through the sharp support-relative Section 26 numeric.**
The support-relative I.4.1/K.4 numeric supplies the Run residual, and the
independent high-excess atom supplies the other capstone input. -/
theorem erdos260_of_supportNumeric_and_highExcess
    (h : Section26SupportNumericHyp)
    (he : HighExcessRoutingCountResidual) : Erdos260Statement :=
  erdos260_ofSupportMaxCore_and_highExcess
    (runClass5Section26Family_of_supportNumeric h) he

def runClass5Section26Status : List String :=
  [ "ROOT-WIRED MODULE - imported by Erdos260.lean; no sorry/admit/axiom. The previous " ++
      "no-input placeholder section26_positiveDensityRunArea_unconditional has been replaced " ++
      "by the honest residual Section26SupportNumericHyp.",
    "ROADMAP - manuscript §26 trichotomy + Prop 24.3/25.3 + Appendices D-F compression " ++
      "→ Section26LinearMaxForm (= RunClass5LeafSupportMaxCoreResidual.hproduct at zero stage).",
    "PROVED HERE - section26_linearMaxForm_of_runNumericIneq: RunNumericIneq → linear max-form " ++
      "(sound shrink via runBaseMaxExcess_le_runDyadicMult_uncond; NOT the sharp §26 input).",
    "PROVED HERE - runSupportMaxCoreResidual_of_runNumericSettlement: RunNumericSettlementHyp → " ++
      "max-form residual (inherits dyadic-count over-pin on r >= 1 shells).",
    "PROVED HERE - section26_positiveDensityRunArea_of_runNumericSettlement: " ++
      "RunNumericSettlementHyp -> Section26PositiveDensityRunAreaHyp, making the conditional " ++
      "dyadic numeric route explicit while keeping the no-input Section 26 theorem open.",
    "PROVED HERE - erdos260_of_runNumericSettlement_and_highExcess: RunNumericSettlementHyp " ++
      "plus the independent HighExcessRoutingCountResidual reaches the final capstone through " ++
      "the Section 26 max-form bridge.",
    "PROVED HERE - section26_linearMaxForm_of_supportNumeric: sharp support-relative I.4.1/K.4 " ++
      "numeric for the zero-stage base fibre implies Section26LinearMaxForm.",
    "PROVED HERE - section26_positiveDensityRunArea_of_supportNumeric: " ++
      "Section26SupportNumericHyp -> Section26PositiveDensityRunAreaHyp.",
    "PROVED HERE - runClass5LeafResidualFamily_of_supportNumeric: the support-relative " ++
      "Section 26 numeric supplies the sharp RunClass5LeafResidual family through the " ++
      "proved max-core/leaf equivalence.",
    "PROVED HERE - section26_linearMaxForm_forces_fibre_sparsity: hproduct → #fibre·Y ≤ budget.",
    "PROVED REGIMES - r=0 and modulus<5 fibre emptiness (vacuous on ActualFailureContext " ++
      "where n24_gate_violated forces r >= 1 and L >= 15421).",
    "OPEN CORE - Section26SupportNumericHyp: genuine §26 support-relative I.4.1/K.4 assembly at " ++
      "the realized multiplier runBaseMaxExcess; cannot be derived from ctx.hfailure or " ++
      "RunNumericSettlementHyp alone (obstruction theorems runSupportProductCore_forces_quadratic_X " ++
      "and runSupportDyadicCount_forces_mult_X).",
    "OPEN FIELDS for full leaf (even after §26) - genuine I.6S stageOf and L.4.2 stage-mass " ++
      "hhalf (RunClass5GenuineLeaf); zero stage map collapses geometry and is not the manuscript map." ]

theorem runClass5Section26Status_nonempty : runClass5Section26Status ≠ [] := by
  simp [runClass5Section26Status]

#print axioms section26_linearMaxForm_of_runNumericIneq
#print axioms runSupportMaxCoreResidual_of_runNumericIneq
#print axioms section26_positiveDensityRunArea_of_runNumericSettlement
#print axioms erdos260_of_runNumericSettlement_and_highExcess
#print axioms section26_linearMaxForm_of_supportNumeric
#print axioms section26_positiveDensityRunArea_of_supportNumeric
#print axioms runClass5LeafResidual_of_supportNumeric
#print axioms runClass5LeafResidualFamily_of_supportNumeric
#print axioms erdos260_of_supportNumeric_and_highExcess
#print axioms section26_linearMaxForm_forces_fibre_sparsity
#print axioms section26_linearMaxForm_of_r_eq_zero

end

end Erdos260
