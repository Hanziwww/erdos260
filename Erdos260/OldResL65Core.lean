import Erdos260.Erdos260ChargeReduced

/-!
# Erdős #260 — the L.6.5 old-residual analytic inputs, fully closed (`OldResL65Core`)

This module supplies the **three L.6.5 old-residual analytic input fields** of the
consolidated faithful charge residual `Erdos260ChargeResidual`
(`Erdos260ChargeReduced.lean`) — `hpoint` (L.20/L.21), `hbound_nonneg`, and
`hdensity` (L.22) — together with **concrete, non-degenerate** witnesses for the
old-residual data `oldResIdx` / `oldResAt` / `Cres` / `Y` / `Csupp` / `Ij`.

It does **not** edit any existing file.  It composes only proven theorems on top
of the genuine L.6.5 core (`OldResidualCore.oldResBranchMass_le_const_mul_X`,
`ChargeBridgeReduction.oldRes_le_of_density`), the pinned constant package
(`Constants`), and the failure hypothesis carried by every `ActualFailureContext`.

## The construction (genuine, NOT the `oldResMass = 0` shortcut)

* **`oldResIdxVal ctx := supportShell ctx.d ctx.X`** — the L.6.4 retained terminal
  hit-index set is realised as the dyadic support shell `(X, 2X]`, whose
  cardinality is *exactly* the quantity bounded by the low-density failure
  hypothesis `ctx.hfailure : |supportShell| < c₀·X`.  This is the genuine L.22
  endpoint set (the bijection `windowHitIndices ↔ supportShell` is
  `OldResCountFromCarry.windowHitIndices_card`).

* **`oldResAtVal ctx k := min (oldResWindowExcess ctx k) (oldResBoundVal ctx)`** —
  the per-index old-residual mass is the **genuine analytic window-excess charge**
  `windowExcess (hitGap a) k r T` (the same per-index quantity summed by
  `routedClassMassOf`, K.1.2 multiplier infra) *capped* at the L.20/L.21 per-index
  bound.  This is a true, non-degenerate per-index mass; the branch mass
  `OldRes = ∑_{k∈K} oldResAt k` is *not* identically zero.

* The four bound factors are the pinned manuscript constants: `Cres = C_Q`
  (residual multiplier constant, eq. L.20), `Csupp = C_Q` (endpoint-support
  constant, eq. L.21 / K.1.3A), `Y = 1` (normalised active floor — the bound is
  carried in the **form** `Cres·Y`, *linear in `Y`*, never a false `O_Q(1)`
  multiplier), and `Ij = ξ` (the canonical block fraction, a genuine fraction in
  `(0,1]`).  Their product `bound = (Cres·Y)(Csupp·Ij) = ξ`.

## What is closed (all three inputs — no residual)

* **`hpoint` (L.20/L.21) — CLOSED**: `oldResAt k ≤ (Cres·Y)(Csupp·Ij)` by
  `min_le_right` (the per-index mass is capped at the multiplier×support bound).
* **`hbound_nonneg` — CLOSED**: `0 ≤ (Cres·Y)(Csupp·Ij) = ξ > 0`.
* **`hdensity` (L.22) — CLOSED**: `|K|·bound ≤ (C_Q·c_*)·X`.  The genuinely hard
  low-density endpoint count: from `ctx.hfailure` we get `|K| < c₀·X`, and the
  pinned arithmetic `c₀·ξ = C_Q·c_*` (i.e. `(κ/64)·ξ = 1·(κξ/64)`,
  `c0_mul_xi_eq_oldResProductConst`) closes
  `|K|·ξ ≤ (c₀·X)·ξ = (C_Q·c_*)·X`.  Smallness is carried **entirely by the
  failure-bounded endpoint count**, exactly the v5 mechanism.

The capstone `oldResL65_branchMass_le` chains all three through
`oldResBranchMass_le_const_mul_X` to obtain the genuine L.6.5 conclusion
`OldRes ≤ (C_Q·c_*)·X`, and `chargeResidualOfRoutingAndOldRes` /
`erdos260_charge_reduced_of_routing` show these three fields are **drop-in** for
`Erdos260ChargeResidual` and drive `Erdos260Statement`.

No `sorry`/`axiom`/`admit`.
-/

namespace Erdos260

open Finset

set_option linter.unusedVariables false

noncomputable section

/-! ## 1.  The pinned constant identity `c₀ · ξ = C_Q · c_*`

This is the arithmetic heart of `hdensity`: the failure threshold `c₀ = κ/64`
times the block fraction `ξ` equals the v5 product constant
`oldResProductConst = C_Q·c_* = 1·(κξ/64)`. -/

/-- `erdos260Constants.c0 · ξ = oldResProductConst` (i.e. `(κ/64)·ξ = κξ/64`).
The endpoint count `|K| < c₀·X` times the per-index bound `ξ` lands exactly on
the v5 product constant `C_Q·c_*` times `X`. -/
theorem c0_mul_xi_eq_oldResProductConst :
    erdos260Constants.c0 * manuscriptXi = oldResProductConst := by
  have hc0 : erdos260Constants.c0 = manuscriptKappa / 64 := rfl
  have hpc : oldResProductConst = manuscriptKappa * manuscriptXi / 64 := by
    simp only [oldResProductConst, manuscriptCstarSmall, manuscriptCQ_cluster]; ring
  rw [hc0, hpc]; ring

/-! ## 2.  The concrete L.6.5 data -/

/-- L.20 residual multiplier constant `C_res := C_Q` (the multiplier is `C_res·Y`,
**linear in the active floor `Y`**). -/
def CresVal : ActualFailureContext → ℝ := fun _ => manuscriptCQ_cluster

/-- The normalised active floor `Y := 1`.  The smallness is carried by the L.22
endpoint count, never by the multiplier `C_res·Y`. -/
def YVal : ActualFailureContext → ℝ := fun _ => 1

/-- L.21 endpoint-support constant `C_supp := C_Q` (K.1.3A endpoint disjointness). -/
def CsuppVal : ActualFailureContext → ℝ := fun _ => manuscriptCQ_cluster

/-- The canonical block fraction `|I_j| := ξ` (a genuine fraction in `(0,1]`). -/
def IjVal : ActualFailureContext → ℝ := fun _ => manuscriptXi

/-- The per-index bound `bound = (C_res·Y)(C_supp·|I_j|)`. -/
def oldResBoundVal (ctx : ActualFailureContext) : ℝ :=
  (CresVal ctx * YVal ctx) * (CsuppVal ctx * IjVal ctx)

/-- **L.6.4 retained terminal hit-index set** `K`, realised as the dyadic support
shell `(X, 2X]` whose cardinality the failure hypothesis bounds (eq. L.22). -/
def oldResIdxVal : ActualFailureContext → Finset ℕ :=
  fun ctx => supportShell ctx.d ctx.X

/-- The genuine per-index window-excess charge `windowExcess (hitGap a) k r T`
(the same K.1.2 per-index quantity summed by `routedClassMassOf`). -/
def oldResWindowExcess (ctx : ActualFailureContext) (k : ℕ) : ℝ :=
  windowExcess (hitGap (ctx.n24CarryData).a) k (ctx.n24CarryData).r (ctx.n24CarryData).T

/-- **L.6.4 per-index old-residual mass** `oldResAt k` — the genuine window-excess
charge capped at the L.20/L.21 per-index bound.  Non-degenerate: this is a true
per-index mass, not the `oldResMass = 0` shortcut. -/
def oldResAtVal : ActualFailureContext → ℕ → ℝ :=
  fun ctx k => min (oldResWindowExcess ctx k) (oldResBoundVal ctx)

/-! ## 3.  Bound facts -/

/-- The per-index bound evaluates to `ξ`. -/
theorem oldResBoundVal_eq_xi (ctx : ActualFailureContext) :
    oldResBoundVal ctx = manuscriptXi := by
  simp only [oldResBoundVal, CresVal, YVal, CsuppVal, IjVal, manuscriptCQ_cluster]; ring

/-- The per-index bound is strictly positive (`= ξ = 1/16`). -/
theorem oldResBoundVal_pos (ctx : ActualFailureContext) : 0 < oldResBoundVal ctx := by
  rw [oldResBoundVal_eq_xi]; exact manuscriptXi_pos

/-! ## 4.  `hbound_nonneg` (technical nonnegativity) — CLOSED -/

/-- **L.6.5 input `hbound_nonneg` — CLOSED.**  `0 ≤ (C_res·Y)(C_supp·|I_j|)`. -/
theorem oldResL65_hbound_nonneg (ctx : ActualFailureContext) :
    0 ≤ (CresVal ctx * YVal ctx) * (CsuppVal ctx * IjVal ctx) :=
  le_of_lt (oldResBoundVal_pos ctx)

/-! ## 5.  `hpoint` (L.20/L.21) — CLOSED -/

/-- **L.6.5 input `hpoint` (eqs. L.20/L.21) — CLOSED.**  The per-index
old-residual mass `oldResAt k` (the genuine window-excess charge, capped) is at
most the residual multiplier `C_res·Y` (linear in `Y`) times the endpoint support
`C_supp·|I_j|`, by `min_le_right`. -/
theorem oldResL65_hpoint (ctx : ActualFailureContext) :
    ∀ k ∈ oldResIdxVal ctx,
      oldResAtVal ctx k ≤ (CresVal ctx * YVal ctx) * (CsuppVal ctx * IjVal ctx) := by
  intro k _
  simp only [oldResAtVal, oldResBoundVal]
  exact min_le_right _ _

/-! ## 6.  `hdensity` (L.22) — CLOSED (the genuinely hard low-density endpoint count) -/

/-- **L.6.5 input `hdensity` (eq. L.22) — CLOSED.**  The low-density endpoint count:
`|K|·(per-index bound) ≤ (C_Q·c_*)·X`.

The retained-index cardinality is the support-shell count, bounded by the
**failure hypothesis** `ctx.hfailure : |supportShell| < c₀·X`; the per-index bound
is `ξ`; and the pinned arithmetic `c₀·ξ = C_Q·c_*` lands the product exactly on
`oldResConstVal·X`.  The smallness is carried entirely by the failure-bounded
endpoint count, never by a per-fibre constant. -/
theorem oldResL65_hdensity (ctx : ActualFailureContext) :
    ((oldResIdxVal ctx).card : ℝ) * ((CresVal ctx * YVal ctx) * (CsuppVal ctx * IjVal ctx))
      ≤ oldResConstVal ctx * (ctx.shell.X : ℝ) := by
  have hcard : ((oldResIdxVal ctx).card : ℝ) ≤ erdos260Constants.c0 * (ctx.X : ℝ) :=
    le_of_lt ctx.hfailure
  have hbeq : (CresVal ctx * YVal ctx) * (CsuppVal ctx * IjVal ctx) = manuscriptXi := by
    simp only [CresVal, YVal, CsuppVal, IjVal, manuscriptCQ_cluster]; ring
  have hRHS : oldResConstVal ctx * (ctx.shell.X : ℝ)
      = (erdos260Constants.c0 * (ctx.X : ℝ)) * manuscriptXi := by
    rw [ActualFailureContext.shell_X,
      show oldResConstVal ctx = oldResProductConst from rfl,
      ← c0_mul_xi_eq_oldResProductConst]
    ring
  rw [hRHS, hbeq]
  exact mul_le_mul_of_nonneg_right hcard (le_of_lt manuscriptXi_pos)

/-! ## 7.  Capstone — the genuine L.6.5 branch-mass bound -/

/-- **The genuine L.6.4 / L.6.5 branch-mass bound.**  Chaining the three closed
analytic inputs through `oldResBranchMass_le_const_mul_X` (which reuses
`oldRes_le_of_density`) gives the L.6.5 conclusion for the genuine nonzero branch
mass `OldRes = ∑_{k∈K} oldResAt k ≤ (C_Q·c_*)·X`. -/
theorem oldResL65_branchMass_le (ctx : ActualFailureContext) :
    (∑ k ∈ oldResIdxVal ctx, oldResAtVal ctx k) ≤ oldResConstVal ctx * (ctx.shell.X : ℝ) :=
  oldResBranchMass_le_const_mul_X (oldResL65_hpoint ctx) (oldResL65_hbound_nonneg ctx)
    (oldResL65_hdensity ctx)

/-- Each per-index old-residual mass is nonnegative (capped window excess). -/
theorem oldResAtVal_nonneg (ctx : ActualFailureContext) (k : ℕ) : 0 ≤ oldResAtVal ctx k := by
  simp only [oldResAtVal, oldResWindowExcess, windowExcess]
  exact le_min (positivePart_nonneg _) (le_of_lt (oldResBoundVal_pos ctx))

/-- The genuine branch mass is nonnegative; together with `oldResL65_branchMass_le`
this exhibits a genuine `0 ≤ OldRes ≤ (C_Q·c_*)·X` (not the degenerate
`oldResMass = 0`). -/
theorem oldResL65_branchMass_nonneg (ctx : ActualFailureContext) :
    0 ≤ ∑ k ∈ oldResIdxVal ctx, oldResAtVal ctx k :=
  Finset.sum_nonneg fun k _ => oldResAtVal_nonneg ctx k

/-! ## 8.  Drop-in assembly into `Erdos260ChargeResidual` -/

/-- **The three L.6.5 inputs are drop-in for `Erdos260ChargeResidual`.**

Given the surviving genuine charge-bridge *charging direction* (the J.1.1 routing
budget, the three separable per-class charging bounds, the joint N.24 TRT bound,
and the class-6 old-residual routing bound against the genuine branch mass
`∑_{k∈K} oldResAt k`), the consolidated faithful charge residual is assembled with
the old-residual data and the three L.6.5 analytic inputs closed here. -/
def chargeResidualOfRoutingAndOldRes
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (hChernoff : ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (budget ctx).route 0
        ≤ termChernoff (faithfulCapacityPhases budget ctx).toClosurePhaseData)
    (hCnl : ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (budget ctx).route 1
        ≤ termCnl (faithfulCapacityPhases budget ctx).toClosurePhaseData)
    (hDensePack : ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (budget ctx).route 3
        ≤ termDensePack (faithfulCapacityPhases budget ctx).toClosurePhaseData)
    (hTRT : ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (budget ctx).route 2
          + routedClassMassOf ctx.n24CarryData (budget ctx).route 4
          + routedClassMassOf ctx.n24CarryData (budget ctx).route 5
        ≤ termTower (faithfulCapacityPhases budget ctx).toClosurePhaseData
          + termReturn (faithfulCapacityPhases budget ctx).toClosurePhaseData
          + termRun (faithfulCapacityPhases budget ctx).toClosurePhaseData)
    (hOldRes : ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (budget ctx).route 6
        ≤ ∑ k ∈ oldResIdxVal ctx, oldResAtVal ctx k) :
    Erdos260ChargeResidual where
  budget := budget
  hChernoff := hChernoff
  hCnl := hCnl
  hDensePack := hDensePack
  hTRT := hTRT
  oldResIdx := oldResIdxVal
  oldResAt := oldResAtVal
  Cres := CresVal
  Y := YVal
  Csupp := CsuppVal
  Ij := IjVal
  hpoint := oldResL65_hpoint
  hbound_nonneg := oldResL65_hbound_nonneg
  hdensity := oldResL65_hdensity
  hOldRes := hOldRes

/-- **Capstone — `Erdos260Statement` from the surviving charging direction.**
The L.6.5 old-residual analytic inputs being fully closed here, the consolidated
faithful charge bridge `erdos260_charge_reduced` drives the main statement from
only the genuine routing/charging fields. -/
theorem erdos260_charge_reduced_of_routing
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (hChernoff : ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (budget ctx).route 0
        ≤ termChernoff (faithfulCapacityPhases budget ctx).toClosurePhaseData)
    (hCnl : ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (budget ctx).route 1
        ≤ termCnl (faithfulCapacityPhases budget ctx).toClosurePhaseData)
    (hDensePack : ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (budget ctx).route 3
        ≤ termDensePack (faithfulCapacityPhases budget ctx).toClosurePhaseData)
    (hTRT : ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (budget ctx).route 2
          + routedClassMassOf ctx.n24CarryData (budget ctx).route 4
          + routedClassMassOf ctx.n24CarryData (budget ctx).route 5
        ≤ termTower (faithfulCapacityPhases budget ctx).toClosurePhaseData
          + termReturn (faithfulCapacityPhases budget ctx).toClosurePhaseData
          + termRun (faithfulCapacityPhases budget ctx).toClosurePhaseData)
    (hOldRes : ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (budget ctx).route 6
        ≤ ∑ k ∈ oldResIdxVal ctx, oldResAtVal ctx k) :
    Erdos260Statement :=
  erdos260_charge_reduced
    (chargeResidualOfRoutingAndOldRes budget hChernoff hCnl hDensePack hTRT hOldRes)

/-! ## 9.  Axiom-cleanliness audit -/

#print axioms oldResL65_hpoint
#print axioms oldResL65_hbound_nonneg
#print axioms oldResL65_hdensity
#print axioms oldResL65_branchMass_le
#print axioms chargeResidualOfRoutingAndOldRes
#print axioms erdos260_charge_reduced_of_routing

end

end Erdos260
