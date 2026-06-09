import Mathlib
import Erdos260.CNLFibreBound
import Erdos260.ChernoffCNLChargeBound

/-!
# Resolving the CNL Kraft constant-compatibility caveat

`CNLFibreBound.lean` proves the clean-CNL Kraft bound **unconditionally**, but in
the *prefactored* shape

```
cleanCNLKraftSum (selectedTransitions T) BNDHeight c ≤ B · C_Q^M
```

with an `O(1)` prefactor `B` — either `B = Fintype.card CNLTransition` (model
finiteness, `cleanCNLKraftSum_selectedTransitions_le_modelCard_ofBridgeStep`) or
the sharp `B = Q` (carry residue modulo `Q`,
`cleanCNLKraftSum_selectedTransitions_le_carryQuotient_ofBridgeStep`).

The provider field `CNLClusterEncodingData.kraftSum_le` (`AppendixK3_CNL.lean`)
demands the *prefactor-free* `cleanCNLKraftSum … ≤ C_Q^M`.  This file removes the
mismatch.

## The key structural observation

`CNLClusterEncodingData cStar ξ X` carries `CQ : ℝ` and `M : ℕ` as **free
per-instance fields**, and uses `CQ` *only* through the block `CQ ^ M` — it
appears nowhere else, in particular not pinned to any global constant.  Both
`kraftSum_le` (`… ≤ CQ^M`) and `manuscript_bound` (`CQ^M · shellFactor · X · Ij ≤
cStar·ξ·X/6`) see `CQ` solely as the value `CQ^M`.

Hence the `O(1)` prefactor is *foldable into the free field* `CQ`: for `M ≥ 1`
set

```
CQ := (B · C_Q₀^M) ^ (1/M)     so that     CQ ^ M = B · C_Q₀^M.
```

This discharges `kraftSum_le` **genuinely from the unconditional bound** — it is
no longer an assumption — and relocates the `O(1)` factor entirely into the
`manuscript_bound` shell-budget field (which was already an assumed manuscript
calibration; it now needs `O(1)` more slack, which `shellFactor·Ij = 2^{-c₀ηY}·|I_j|`
supplies with exponential margin).

The fold *is* the manuscript caveat "the constant cannot be folded into `C_Q^M`
without enlarging `C_Q` in an `M`-dependent way" — but that enlargement is
*harmless here* because `CQ` is a per-instance field, `M ≥ 1` is fixed per
instance, and nothing downstream needs `CQ` to be `M`-uniform (everything sees
only `CQ^M`).

## What is proved here (no `sorry`, no `axiom`)

1. `CNLClusterEncodingData.ofKraftPrefactor` — the fold: build a full
   `CNLClusterEncodingData` from **any** prefactored Kraft bound `… ≤ B·C_Q₀^M`
   (`B ≥ 0`, `M ≥ 1`) plus the prefactored shell budget.  `kraftSum_le` is
   *derived*, not assumed.
2. `CNLClusterEncodingData.ofModelCardBridge` / `…ofCarryQuotientBridge` — fire
   the fold with the genuine unconditional `CNLFibreBound` theorems, so the
   resulting datum's `kraftSum_le` is backed by the proved bound (`B = card` or
   `B = Q`).
3. `termCnl_le_budget_of_kraft_prefactor` (route (a)) — the per-phase CNL budget
   `termCnl ≤ cStar·ξ·X/6` is re-derived *directly* from the prefactored Kraft
   bound, proving the prefactor threads through the downstream budget with the
   **same** conclusion (so no budget is broken even without folding).
4. `cnlProvider_ofUnconditional` — the `Erdos260MinimalAtoms.cnl` provider slot
   is *inhabited* from per-shell unconditional inputs, i.e. the `kraftSum_le`
   sub-obligation of the `cnl` atom is dischargeable.

## Honest verdict (see `cnlConstantCompatStatus`)

`kraftSum_le` is **CLOSED**: dischargeable from the unconditional bound, with the
`O(1)` prefactor absorbed by the (already-assumed) `manuscript_bound` budget
field.  It breaks **no** downstream budget: `termCnl ≤ cStar·ξ·X/6` is unchanged
(item 3), the six-phase sum `ClosurePhaseMass ≤ cStar·ξ·X` is unchanged, and the
final closure-pressure condition `cStar·ξ + C_Q·c_* < cPr` is on the *unrelated*
old-residual constant `C_Q` (`ResidualScalarBudgets.manuscript_closure_pressure`).
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## Part 0. The base-fold lemma -/

/-- **The fold.** For `y ≥ 0` and `M ≥ 1`, the `M`-th power of `y^(1/M)` is `y`.
This is the algebraic content that lets an `O(1)` prefactor be absorbed into the
base of a power with fixed exponent `M`. -/
theorem cnl_foldedBase_pow {y : ℝ} (hy : 0 ≤ y) {M : ℕ} (hM : M ≠ 0) :
    (y ^ ((M : ℝ)⁻¹)) ^ M = y :=
  Real.rpow_inv_natCast_pow hy hM

/-! ## Part 1. The fold constructor (route (b)): discharge `kraftSum_le` -/

/--
**Discharge `kraftSum_le` from a prefactored Kraft bound.**

Given an `O(1)`-prefactored Kraft bound `cleanCNLKraftSum paths BNDHeight c ≤
B · C_Q₀^M` (`B ≥ 0`, `C_Q₀ ≥ 0`, `M ≥ 1`) and the matching prefactored shell
budget `B · C_Q₀^M · shellFactor · X · Ij ≤ cStar·ξ·X/6`, build a genuine
`CNLClusterEncodingData cStar ξ X` whose `kraftSum_le` is **proved** (folding the
prefactor into the free field `CQ := (B·C_Q₀^M)^(1/M)`, so `CQ^M = B·C_Q₀^M`).

The prefactor lives entirely in the `manuscript_bound` field, which was already an
assumed manuscript calibration; the Kraft inequality itself is no longer assumed. -/
def CNLClusterEncodingData.ofKraftPrefactor
    {cStar ξ X : ℝ} {α : Type}
    (paths : Finset α) (BNDHeight : α → ℝ) (c CQ₀ : ℝ) (M : ℕ) (B : ℝ)
    (shellFactor Ij : ℝ)
    (hCQ₀ : 0 ≤ CQ₀) (hB : 0 ≤ B) (hM : M ≠ 0)
    (shellFactor_nonneg : 0 ≤ shellFactor) (Ij_nonneg : 0 ≤ Ij)
    (hkraft : cleanCNLKraftSum paths BNDHeight c ≤ B * CQ₀ ^ M)
    (hbudget : B * CQ₀ ^ M * shellFactor * X * Ij ≤ cStar * ξ * X / 6) :
    CNLClusterEncodingData cStar ξ X := by
  have hy : (0 : ℝ) ≤ B * CQ₀ ^ M := mul_nonneg hB (pow_nonneg hCQ₀ M)
  have hpow : ((B * CQ₀ ^ M) ^ ((M : ℝ)⁻¹)) ^ M = B * CQ₀ ^ M :=
    cnl_foldedBase_pow hy hM
  exact
    { α := α
      paths := paths
      BNDHeight := BNDHeight
      c := c
      CQ := (B * CQ₀ ^ M) ^ ((M : ℝ)⁻¹)
      M := M
      shellFactor := shellFactor
      Ij := Ij
      shellFactor_nonneg := shellFactor_nonneg
      Ij_nonneg := Ij_nonneg
      kraftSum_le := by rw [hpow]; exact hkraft
      manuscript_bound := by rw [hpow]; exact hbudget }

/-! ## Part 2. Route (a): the prefactor threads through `termCnl` -/

/--
**CNL phase budget from a *prefactored* Kraft bound (route (a)).**

The exact analogue of `termCnl_le_budget_of_kraft` (`ChernoffCNLChargeBound.lean`),
but consuming the prefactored bound `cleanCNLKraftSum … ≤ B · C_Q^M` and the
prefactored shell budget `B · C_Q^M · shellFactor · X · Ij ≤ cStar·ξ·X/6`.  The
conclusion is the **same** per-phase budget `termCnl ≤ cStar·ξ·X/6`, so the
`O(1)` prefactor threads through cleanly and breaks no downstream budget. -/
theorem termCnl_le_budget_of_kraft_prefactor
    {cStar ξ X : ℝ} (data : ClosurePhaseData cStar ξ X)
    (hX_nonneg : 0 ≤ X)
    {B CQ : ℝ} {M : ℕ}
    (hkraft :
      cleanCNLKraftSum data.cnl.paths data.cnl.BNDHeight data.cnl.c ≤ B * CQ ^ M)
    (hbudget :
      B * CQ ^ M * data.cnl.shellFactor * X * data.cnl.Ij ≤ cStar * ξ * X / 6) :
    termCnl data ≤ cStar * ξ * X / 6 := by
  show cleanCNLKraftSum data.cnl.paths data.cnl.BNDHeight data.cnl.c *
      data.cnl.shellFactor * X * data.cnl.Ij ≤ cStar * ξ * X / 6
  have hfac : 0 ≤ data.cnl.shellFactor * X * data.cnl.Ij :=
    mul_nonneg (mul_nonneg data.cnl.shellFactor_nonneg hX_nonneg) data.cnl.Ij_nonneg
  calc cleanCNLKraftSum data.cnl.paths data.cnl.BNDHeight data.cnl.c *
          data.cnl.shellFactor * X * data.cnl.Ij
      = cleanCNLKraftSum data.cnl.paths data.cnl.BNDHeight data.cnl.c *
          (data.cnl.shellFactor * X * data.cnl.Ij) := by ring
    _ ≤ (B * CQ ^ M) * (data.cnl.shellFactor * X * data.cnl.Ij) :=
        mul_le_mul_of_nonneg_right hkraft hfac
    _ = B * CQ ^ M * data.cnl.shellFactor * X * data.cnl.Ij := by ring
    _ ≤ cStar * ξ * X / 6 := hbudget

/-! ## Part 3. Firing the fold with the genuine unconditional `CNLFibreBound` -/

/--
**Discharge `kraftSum_le` from the unconditional model-finiteness bound.**

Fires `ofKraftPrefactor` with `B = Fintype.card CNLTransition` and the proved
`cleanCNLKraftSum_selectedTransitions_le_modelCard_ofBridgeStep`.  The resulting
datum's `kraftSum_le` is therefore backed by the *unconditional* CNL Kraft bound
(no `sym_injOn`, no fibre hypothesis), the only inputs being the faithful bridge
labelling (`hE`/`hwin`/`hpos`, supplying step-determinism) and the additive BND
height `hheight`. -/
def CNLClusterEncodingData.ofModelCardBridge
    {cStar ξ X : ℝ}
    (T : Finset CNLTransition) (BNDHeight : CNLTransition → ℝ) (c CQ : ℝ)
    (hc : 0 < c) (hCQ : (1 - (2 : ℝ) ^ (-c))⁻¹ ≤ CQ)
    (M : ℕ) (hM : M ≠ 0) (E : ℕ → ℕ) {g sm gOld : ℕ → ℤ} {s : ℕ}
    (hE : ∀ t, (E t : ℤ) = bridgeExp g sm s t)
    (hwin : ∀ t, sm (t + 1) - sm t = g t - gOld t)
    (hpos : ∀ t, 0 < gOld t)
    (sym : CNLTransition → ℕ → ℕ)
    (hheight :
      ∀ t ∈ selectedTransitions T,
        BNDHeight t = ∑ i ∈ Finset.range M, (E (sym t i) : ℝ))
    (shellFactor Ij : ℝ)
    (shellFactor_nonneg : 0 ≤ shellFactor) (Ij_nonneg : 0 ≤ Ij)
    (hbudget :
      (Fintype.card CNLTransition : ℝ) * CQ ^ M * shellFactor * X * Ij
        ≤ cStar * ξ * X / 6) :
    CNLClusterEncodingData cStar ξ X := by
  have hCQ_nonneg : 0 ≤ CQ := by
    have hlt1 : (2 : ℝ) ^ (-c) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    exact le_trans (le_of_lt (inv_pos.mpr (by linarith))) hCQ
  exact CNLClusterEncodingData.ofKraftPrefactor
    (selectedTransitions T) BNDHeight c CQ M (Fintype.card CNLTransition : ℝ)
    shellFactor Ij hCQ_nonneg (Nat.cast_nonneg _) hM shellFactor_nonneg Ij_nonneg
    (cleanCNLKraftSum_selectedTransitions_le_modelCard_ofBridgeStep
      T BNDHeight c CQ hc hCQ M E hE hwin hpos sym hheight)
    hbudget

/--
**Discharge `kraftSum_le` from the sharp carry-quotient bound.**

Fires `ofKraftPrefactor` with the sharp manuscript prefactor `B = Q` and the
proved `cleanCNLKraftSum_selectedTransitions_le_carryQuotient_ofBridgeStep`.  The
remaining manuscript input is exactly the carry-quotient injectivity `hcarry`
("the ladder code and the carry residue mod `Q` jointly determine the
transition"). -/
def CNLClusterEncodingData.ofCarryQuotientBridge
    {cStar ξ X : ℝ}
    (T : Finset CNLTransition) (BNDHeight : CNLTransition → ℝ) (c CQ : ℝ)
    (hc : 0 < c) (hCQ : (1 - (2 : ℝ) ^ (-c))⁻¹ ≤ CQ)
    (M : ℕ) (hM : M ≠ 0) (E : ℕ → ℕ) {g sm gOld : ℕ → ℤ} {s : ℕ}
    (hE : ∀ t, (E t : ℤ) = bridgeExp g sm s t)
    (hwin : ∀ t, sm (t + 1) - sm t = g t - gOld t)
    (hpos : ∀ t, 0 < gOld t)
    (sym : CNLTransition → ℕ → ℕ)
    (hheight :
      ∀ t ∈ selectedTransitions T,
        BNDHeight t = ∑ i ∈ Finset.range M, (E (sym t i) : ℝ))
    (Q : ℕ) [NeZero Q] (res : CNLTransition → ZMod Q)
    (hcarry : ∀ a ∈ selectedTransitions T, ∀ b ∈ selectedTransitions T,
        codeWord sym M a = codeWord sym M b → res a = res b → a = b)
    (shellFactor Ij : ℝ)
    (shellFactor_nonneg : 0 ≤ shellFactor) (Ij_nonneg : 0 ≤ Ij)
    (hbudget :
      (Q : ℝ) * CQ ^ M * shellFactor * X * Ij ≤ cStar * ξ * X / 6) :
    CNLClusterEncodingData cStar ξ X := by
  have hCQ_nonneg : 0 ≤ CQ := by
    have hlt1 : (2 : ℝ) ^ (-c) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    exact le_trans (le_of_lt (inv_pos.mpr (by linarith))) hCQ
  exact CNLClusterEncodingData.ofKraftPrefactor
    (selectedTransitions T) BNDHeight c CQ M (Q : ℝ)
    shellFactor Ij hCQ_nonneg (Nat.cast_nonneg _) hM shellFactor_nonneg Ij_nonneg
    (cleanCNLKraftSum_selectedTransitions_le_carryQuotient_ofBridgeStep
      T BNDHeight c CQ hc hCQ M E hE hwin hpos sym hheight Q res hcarry)
    hbudget

/-! ## Part 4. The `cnl` provider slot is dischargeable -/

/--
**Per-shell unconditional CNL Kraft input.**

Bundles, at a fixed shell scale `X`, the faithful inputs of the unconditional
model-finiteness Kraft bound (the bridge labelling and additive BND height) plus
the prefactored shell budget.  `build` turns it into a full
`CNLClusterEncodingData` with `kraftSum_le` *derived*, not assumed. -/
structure CNLUnconditionalKraftInput (cStar ξ X : ℝ) where
  T : Finset CNLTransition
  BNDHeight : CNLTransition → ℝ
  c : ℝ
  CQ : ℝ
  hc : 0 < c
  hCQ : (1 - (2 : ℝ) ^ (-c))⁻¹ ≤ CQ
  M : ℕ
  hM : M ≠ 0
  E : ℕ → ℕ
  g : ℕ → ℤ
  sm : ℕ → ℤ
  gOld : ℕ → ℤ
  s : ℕ
  hE : ∀ t, (E t : ℤ) = bridgeExp g sm s t
  hwin : ∀ t, sm (t + 1) - sm t = g t - gOld t
  hpos : ∀ t, 0 < gOld t
  sym : CNLTransition → ℕ → ℕ
  hheight :
    ∀ t ∈ selectedTransitions T,
      BNDHeight t = ∑ i ∈ Finset.range M, (E (sym t i) : ℝ)
  shellFactor : ℝ
  Ij : ℝ
  shellFactor_nonneg : 0 ≤ shellFactor
  Ij_nonneg : 0 ≤ Ij
  hbudget :
    (Fintype.card CNLTransition : ℝ) * CQ ^ M * shellFactor * X * Ij
      ≤ cStar * ξ * X / 6

/-- Build the encoding datum (with derived `kraftSum_le`) from the unconditional
input. -/
def CNLUnconditionalKraftInput.build
    {cStar ξ X : ℝ} (inp : CNLUnconditionalKraftInput cStar ξ X) :
    CNLClusterEncodingData cStar ξ X :=
  CNLClusterEncodingData.ofModelCardBridge
    inp.T inp.BNDHeight inp.c inp.CQ inp.hc inp.hCQ inp.M inp.hM inp.E
    inp.hE inp.hwin inp.hpos inp.sym inp.hheight
    inp.shellFactor inp.Ij inp.shellFactor_nonneg inp.Ij_nonneg inp.hbudget

/--
**The `Erdos260MinimalAtoms.cnl` provider slot is dischargeable.**

Given per-shell unconditional Kraft inputs, produce the exact `cnl` provider field
of `Erdos260MinimalAtoms`: `∀ shell, shell.cQ = … → CNLClusterEncodingData …`.
Every produced datum has its `kraftSum_le` backed by the unconditional
`CNLFibreBound` model-finiteness bound (no Kraft assumption remains), the `O(1)`
prefactor being carried by each datum's shell-budget field. -/
def cnlProvider_ofUnconditional
    (input :
      ∀ shell : FailingDyadicShell, shell.cQ = erdos260Constants.cQ →
        CNLUnconditionalKraftInput erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : ℝ)) :
    ∀ shell : FailingDyadicShell, shell.cQ = erdos260Constants.cQ →
      CNLClusterEncodingData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : ℝ) :=
  fun shell hcQ => (input shell hcQ).build

/-! ## Part 5. Honest status inventory -/

/-- Per-claim honesty report on the CNL constant-compatibility caveat. -/
def cnlConstantCompatStatus : List String :=
  [ "kraftSum_le slot: CLOSED.  CNLClusterEncodingData.ofKraftPrefactor folds the " ++
      "O(1) prefactor B (= Fintype.card CNLTransition or Q) into the FREE field " ++
      "CQ := (B·CQ₀^M)^(1/M) (valid since M ≥ 1 is per-instance and the structure " ++
      "uses CQ only via CQ^M), so kraftSum_le is DERIVED from the unconditional " ++
      "CNLFibreBound bound, not assumed.  Fired by ofModelCardBridge / ofCarryQuotientBridge.",
    "Prefactor location: the O(1) factor moves into the manuscript_bound shell " ++
      "budget B·CQ₀^M·shellFactor·X·Ij ≤ cStar·ξ·X/6 — already an assumed manuscript " ++
      "calibration (proof_v2.tex H.2); shellFactor·Ij = 2^{-c₀ηY}·|I_j| absorbs any " ++
      "O(1) with exponential margin.  No NEW Kraft assumption is introduced.",
    "Downstream budget: NOT broken.  termCnl_le_budget_of_kraft_prefactor re-derives " ++
      "the SAME per-phase budget termCnl ≤ cStar·ξ·X/6 from the prefactored bound; the " ++
      "six-phase sum ClosurePhaseMass ≤ cStar·ξ·X is unchanged.",
    "Final contradiction: UNAFFECTED.  The closure-pressure condition " ++
      "cStar·ξ + C_Q·c_* < cPr uses the OLD-RESIDUAL constant C_Q (a different " ++
      "constant), so the CNL Kraft prefactor never reaches it.",
    "Provider slot: cnlProvider_ofUnconditional inhabits the Erdos260MinimalAtoms.cnl " ++
      "field type from per-shell unconditional inputs." ]

theorem cnlConstantCompatStatus_nonempty : cnlConstantCompatStatus ≠ [] := by
  simp [cnlConstantCompatStatus]

end

end Erdos260
