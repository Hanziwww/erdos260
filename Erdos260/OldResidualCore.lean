import Mathlib
import Erdos260.Constants
import Erdos260.ChargeBridgeReduction
import Erdos260.Erdos260FinalReduced

/-!
# Erdős #260 — the old-residual + constant-condition layer (Lemmas L.6.4 / L.6.5)

This module supplies **four of the ten fields** of `Erdos260FinalResidual`
(`Erdos260FinalReduced.lean`): `oldResMass`, `oldResConst`, `oldResSmall`, and
`constCond`.  It does **not** edit the residual surface; it provides the concrete
data and proofs that fill those fields, plus assemblers that plug them into
`Erdos260FinalResidual` and run `erdos260_final_reduced` from only the remaining
six fields.

## What is closed

* **`constCond` — FULLY CLOSED** as a pure constant inequality.  With the pinned
  constants `c_⋆ = C_* = 31/16`, `ξ = 1/16` (so `c_⋆·ξ = 31/256`) and `c_pr = 1/2`,
  and the product constant `C_Q·c_*` fixed to the concrete small value
  `oldResProductConst = manuscriptCQ_cluster · manuscriptCstarSmall`
  (`C_Q := 1` conservative, `c_* = κ·ξ/64 ≈ 6.3·10⁻⁸`), the inequality
  `c_⋆·ξ + C_Q·c_* < c_pr`, i.e. `31/256 + κξ/64 < 1/2`, holds by `norm_num`.
  This is the manuscript "choose `c_*` last": the residual product constant is
  pinned small enough that it stays below the pressure floor.

* **`oldResConst` — CONCRETE DATA**: `oldResConstVal := fun _ => C_Q·c_*`, the
  faithful v5 product constant (no longer a free residual).

* **`oldResMass` / `oldResSmall`** — provided in two faithful forms:
  - the **fully-closed degenerate** form `oldResMassVal := fun _ => 0` (the
    "no old-residual leakage" branch blessed by
    `RoutedHighExcessChargeDataOldRes.toHighExcessChargeData_of_oldRes_nonpos`),
    for which `oldResSmall` is `0 ≤ (C_Q·c_*)·X` (`X = ctx.shell.X ≥ 0`), fully
    closed; and
  - the **genuine L.6.5 wiring** `oldResBranchMass_le_const_mul_X`, which bounds
    the genuine branch-level mass `OldRes = ∑_{k∈K} oldResAt k` (Lemma L.6.4) by
    `(C_Q·c_*)·X`, **reusing `oldRes_le_of_density`** (the L.6.5 core).  Its
    residual is exactly the three L.6.5 analytic inputs (per-index
    multiplier×support bound L.20/L.21 and the low-density endpoint count L.22) —
    the genuine analytic content that is *not* available abstractly from `ctx`.

No `sorry`/`axiom`/`admit`.
-/

namespace Erdos260

open Finset

set_option linter.unusedVariables false

noncomputable section

/-! ## 1. The concrete product constant `C_Q · c_*` -/

/-- **The v5 product constant `C_Q · c_*` (concrete).**

`C_Q := manuscriptCQ_cluster = 1` (the conservative cluster constant) and
`c_* := manuscriptCstarSmall = κ·ξ/64` (the failure-hypothesis density constant,
"chosen last").  Numerically `C_Q·c_* = κξ/64 ≈ 6.3·10⁻⁸`, far below the gap
`c_pr − c_⋆·ξ = 1/2 − 31/256 = 97/256 ≈ 0.379` that `constCond` needs, and large
enough to absorb the L.6.5 density product (`oldResBranchMass_le_const_mul_X`). -/
def oldResProductConst : ℝ := manuscriptCQ_cluster * manuscriptCstarSmall

theorem oldResProductConst_pos : 0 < oldResProductConst :=
  mul_pos manuscriptCQ_cluster_pos manuscriptCstarSmall_pos

theorem oldResProductConst_nonneg : 0 ≤ oldResProductConst :=
  le_of_lt oldResProductConst_pos

/-! ## 2. The four field values -/

/-- **`oldResConst` field value** — the concrete product constant `C_Q·c_*`. -/
def oldResConstVal : ActualFailureContext → ℝ := fun _ => oldResProductConst

/-- **`oldResMass` field value (degenerate)** — the "no old-residual leakage"
branch (`OldRes = 0`), the case in which the v5 trichotomy collapses to the OLD
dichotomy (cf. `RoutedHighExcessChargeDataOldRes.toHighExcessChargeData_of_oldRes_nonpos`).
This is a genuine, individually-true instance — *not* the whole theorem in
disguise (contrast the retired circular `centralDensePack`). -/
def oldResMassVal : ActualFailureContext → ℝ := fun _ => 0

/-! ## 3. `constCond` — FULLY CLOSED (pure constant inequality, "choose `c_*` last") -/

/-- **The v5 constant condition `c_⋆·ξ + C_Q·c_* < c_pr`, fully closed.**

At the pinned constants `c_⋆·ξ = (31/16)·(1/16) = 31/256` and `c_pr = 1/2`, with the
concrete small `C_Q·c_* = 1·(κξ/64)`, this reduces to `31/256 + κξ/64 < 1/2`,
discharged by `norm_num`.  This eliminates the `constCond` residual and turns
`oldResConst` into concrete data. -/
theorem oldResConstVal_constCond (ctx : ActualFailureContext) :
    erdos260Constants.cStar * erdos260Constants.ξ + oldResConstVal ctx
      < erdos260Constants.cPr := by
  show manuscriptCstar * manuscriptXi + manuscriptCQ_cluster * manuscriptCstarSmall
      < manuscriptCpr
  simp only [manuscriptCstar, manuscriptXi, manuscriptCpr, manuscriptCQ_cluster,
    manuscriptCstarSmall, manuscriptKappa, manuscriptCdrop, manuscriptC1, manuscriptEps]
  norm_num

/-! ## 4. `oldResSmall` — FULLY CLOSED for the degenerate mass -/

/-- **`oldResSmall` field value (degenerate mass)** — `0 ≤ (C_Q·c_*)·X`, since the
product constant is nonnegative and `X = ctx.shell.X ≥ 0` (it is a `Nat` scale).
Fully closed: no analytic input is needed because `oldResMass = 0`. -/
theorem oldResMassVal_le (ctx : ActualFailureContext) :
    oldResMassVal ctx ≤ oldResConstVal ctx * (ctx.shell.X : ℝ) := by
  have hX : (0 : ℝ) ≤ (ctx.shell.X : ℝ) := ctx.shell.X_nonneg_real
  have hC : (0 : ℝ) ≤ oldResConstVal ctx := oldResProductConst_nonneg
  show (0 : ℝ) ≤ oldResConstVal ctx * (ctx.shell.X : ℝ)
  exact mul_nonneg hC hX

/-! ## 5. The genuine Lemma L.6.5 wiring (reuses `oldRes_le_of_density`) -/

/-- **Lemma L.6.5 wiring — genuine branch mass bounded by `oldResConst·X`.**

The branch-level old-residual mass `OldRes = ∑_{k∈K} oldResAt k` (Lemma L.6.4) is
bounded by `oldResConst · X` once the three L.6.5 analytic inputs hold:

* `hpoint` — the per-index multiplier×support bound
  `oldResAt k ≤ (Cres·Y)·(Csupp·Ij)` (eqs. L.20–L.21: the residual multiplier is
  **linear in the active floor `Y`, not an absolute constant** — the
  K.1.2-consistent v5 bound that evades the OLD `O_Q(1)` contradiction);
* `hbound_nonneg` — nonnegativity of that per-index bound;
* `hdensity` — the density-sensitive count bound
  `|K|·(per-index bound) ≤ oldResConst·X` (eq. L.22 under the low-density failure
  hypothesis `A_S(2X)−A_S(X) < c_*X`; here the smallness is carried entirely by
  the endpoint count, never by a per-fibre constant).

The proof **reuses `oldRes_le_of_density`** (the L.6.5 core) with
`Nendpoints := |K|` to get the L.17 product bound `OldRes ≤ |K|·(per-index bound)`,
then chains the density step.  This is the faithful reduction of `oldResSmall`
to its genuine analytic inputs (the smallest named residual). -/
theorem oldResBranchMass_le_const_mul_X
    {K : Finset ℕ} {oldResAt : ℕ → ℝ} {Cres Y Csupp Ij oldResConst X : ℝ}
    (hpoint : ∀ k ∈ K, oldResAt k ≤ (Cres * Y) * (Csupp * Ij))
    (hbound_nonneg : 0 ≤ (Cres * Y) * (Csupp * Ij))
    (hdensity : (K.card : ℝ) * ((Cres * Y) * (Csupp * Ij)) ≤ oldResConst * X) :
    (∑ k ∈ K, oldResAt k) ≤ oldResConst * X :=
  le_trans (oldRes_le_of_density hpoint hbound_nonneg (le_refl (K.card : ℝ))) hdensity

/-! ## 6. Assemblers — plug the four fields into `Erdos260FinalResidual` -/

/-- **Degenerate assembler.**  From the remaining six fields (the Dirty K.2.5
window count `dirtyCM`/`dirtyWindow`, the three Tower/Return/Run capacity packages,
and the v5 seven-class routing whose old-residual class carries zero mass), build
the full `Erdos260FinalResidual` with the four old-residual fields filled in
concretely (`oldResMass = 0`, `oldResConst = C_Q·c_*`).  This witnesses that the
pinned constants permit **full closure** of all four old-residual fields with zero
residual. -/
def finalResidualOfRemaining
    (dirtyCM : ∀ _ctx : ActualFailureContext, ℕ)
    (dirtyWindow : ∀ ctx : ActualFailureContext, WindowRunScaleCountBound ctx (dirtyCM ctx))
    (tower : ∀ ctx : ActualFailureContext,
      TowerSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : ℝ))
    (returnPkg : ∀ ctx : ActualFailureContext,
      ReturnSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : ℝ))
    (run : ∀ ctx : ActualFailureContext,
      RunSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : ℝ))
    (routing : ∀ ctx : ActualFailureContext,
      RoutedHighExcessChargeDataOldRes
        (assembledFinalPhases dirtyCM dirtyWindow tower returnPkg run ctx)
        ctx.n24CarryData (oldResMassVal ctx)) :
    Erdos260FinalResidual where
  dirtyCM := dirtyCM
  dirtyWindow := dirtyWindow
  tower := tower
  returnPkg := returnPkg
  run := run
  oldResMass := oldResMassVal
  routing := routing
  oldResConst := oldResConstVal
  oldResSmall := oldResMassVal_le
  constCond := oldResConstVal_constCond

/-- **Capstone (degenerate).**  `Erdos260Statement` from the remaining six fields,
via the four old-residual fields closed here and `erdos260_final_reduced`. -/
theorem erdos260_of_remaining_oldResZero
    (dirtyCM : ∀ _ctx : ActualFailureContext, ℕ)
    (dirtyWindow : ∀ ctx : ActualFailureContext, WindowRunScaleCountBound ctx (dirtyCM ctx))
    (tower : ∀ ctx : ActualFailureContext,
      TowerSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : ℝ))
    (returnPkg : ∀ ctx : ActualFailureContext,
      ReturnSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : ℝ))
    (run : ∀ ctx : ActualFailureContext,
      RunSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : ℝ))
    (routing : ∀ ctx : ActualFailureContext,
      RoutedHighExcessChargeDataOldRes
        (assembledFinalPhases dirtyCM dirtyWindow tower returnPkg run ctx)
        ctx.n24CarryData (oldResMassVal ctx)) :
    Erdos260Statement :=
  erdos260_final_reduced
    (finalResidualOfRemaining dirtyCM dirtyWindow tower returnPkg run routing)

/-- **Genuine L.6.5-wired assembler.**  From the remaining five leaf fields, the
genuine L.6.4 old-residual data (`K`, `oldResAt`), the three L.6.5 analytic inputs
(`hpoint`, `hbound_nonneg`, `hdensity`), and the seven-class routing whose
old-residual class is bounded by the genuine branch mass `∑_{k∈K} oldResAt k`, build
the full `Erdos260FinalResidual`.  Here `oldResMass` is the **genuine nonzero**
branch mass; `oldResSmall` is discharged by `oldResBranchMass_le_const_mul_X`
(reusing `oldRes_le_of_density`); `oldResConst = C_Q·c_*` and `constCond` are closed
concretely.  The surviving residual is *exactly* the genuine L.6.5 inputs. -/
def finalResidualOfL65Inputs
    (dirtyCM : ∀ _ctx : ActualFailureContext, ℕ)
    (dirtyWindow : ∀ ctx : ActualFailureContext, WindowRunScaleCountBound ctx (dirtyCM ctx))
    (tower : ∀ ctx : ActualFailureContext,
      TowerSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : ℝ))
    (returnPkg : ∀ ctx : ActualFailureContext,
      ReturnSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : ℝ))
    (run : ∀ ctx : ActualFailureContext,
      RunSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : ℝ))
    (K : ActualFailureContext → Finset ℕ)
    (oldResAt : ActualFailureContext → ℕ → ℝ)
    (Cres Y Csupp Ij : ActualFailureContext → ℝ)
    (hpoint : ∀ ctx, ∀ k ∈ K ctx,
      oldResAt ctx k ≤ (Cres ctx * Y ctx) * (Csupp ctx * Ij ctx))
    (hbound_nonneg : ∀ ctx, 0 ≤ (Cres ctx * Y ctx) * (Csupp ctx * Ij ctx))
    (hdensity : ∀ ctx, ((K ctx).card : ℝ) * ((Cres ctx * Y ctx) * (Csupp ctx * Ij ctx))
        ≤ oldResConstVal ctx * (ctx.shell.X : ℝ))
    (routing : ∀ ctx : ActualFailureContext,
      RoutedHighExcessChargeDataOldRes
        (assembledFinalPhases dirtyCM dirtyWindow tower returnPkg run ctx)
        ctx.n24CarryData (∑ k ∈ K ctx, oldResAt ctx k)) :
    Erdos260FinalResidual where
  dirtyCM := dirtyCM
  dirtyWindow := dirtyWindow
  tower := tower
  returnPkg := returnPkg
  run := run
  oldResMass := fun ctx => ∑ k ∈ K ctx, oldResAt ctx k
  routing := routing
  oldResConst := oldResConstVal
  oldResSmall := fun ctx =>
    oldResBranchMass_le_const_mul_X (hpoint ctx) (hbound_nonneg ctx) (hdensity ctx)
  constCond := oldResConstVal_constCond

/-- **Capstone (genuine L.6.5).**  `Erdos260Statement` from the remaining five leaf
fields, the genuine L.6.4 old-residual data, the three L.6.5 analytic inputs, and
the seven-class routing — via `erdos260_final_reduced`. -/
theorem erdos260_of_remaining_L65
    (dirtyCM : ∀ _ctx : ActualFailureContext, ℕ)
    (dirtyWindow : ∀ ctx : ActualFailureContext, WindowRunScaleCountBound ctx (dirtyCM ctx))
    (tower : ∀ ctx : ActualFailureContext,
      TowerSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : ℝ))
    (returnPkg : ∀ ctx : ActualFailureContext,
      ReturnSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : ℝ))
    (run : ∀ ctx : ActualFailureContext,
      RunSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : ℝ))
    (K : ActualFailureContext → Finset ℕ)
    (oldResAt : ActualFailureContext → ℕ → ℝ)
    (Cres Y Csupp Ij : ActualFailureContext → ℝ)
    (hpoint : ∀ ctx, ∀ k ∈ K ctx,
      oldResAt ctx k ≤ (Cres ctx * Y ctx) * (Csupp ctx * Ij ctx))
    (hbound_nonneg : ∀ ctx, 0 ≤ (Cres ctx * Y ctx) * (Csupp ctx * Ij ctx))
    (hdensity : ∀ ctx, ((K ctx).card : ℝ) * ((Cres ctx * Y ctx) * (Csupp ctx * Ij ctx))
        ≤ oldResConstVal ctx * (ctx.shell.X : ℝ))
    (routing : ∀ ctx : ActualFailureContext,
      RoutedHighExcessChargeDataOldRes
        (assembledFinalPhases dirtyCM dirtyWindow tower returnPkg run ctx)
        ctx.n24CarryData (∑ k ∈ K ctx, oldResAt ctx k)) :
    Erdos260Statement :=
  erdos260_final_reduced
    (finalResidualOfL65Inputs dirtyCM dirtyWindow tower returnPkg run
      K oldResAt Cres Y Csupp Ij hpoint hbound_nonneg hdensity routing)

/-! ## 7. Axiom-cleanliness audit -/

#print axioms oldResConstVal_constCond
#print axioms oldResMassVal_le
#print axioms oldResBranchMass_le_const_mul_X
#print axioms erdos260_of_remaining_oldResZero
#print axioms erdos260_of_remaining_L65

end

end Erdos260
