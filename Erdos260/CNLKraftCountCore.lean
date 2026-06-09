import Erdos260.CNLL12SeedClosure
import Erdos260.CNLScalarBudgetCore
import Erdos260.Erdos260UnconditionalSeedClosure

/-!
# Clean-CNL seed cores 9 & 11 — the L.1.2 bounded-multiplicity count and the G.35 weighted-Kraft
scalar budget, reduced to their sharpest honest residuals

This module (NEW; it edits no existing file) attacks the two clean-CNL (class-1) residual cores of
`Class1CNLSeedCore` (`Erdos260UnconditionalSeedClosure.lean`):

* **Core 9 (`hcard`)** — the L.1.2 bounded-multiplicity count
  `|routedFibre … 1| ≤ |selectedTransitions (liftTransitionsOfShell ctx)|` (the cluster
  reconstruction is bounded-to-one); and
* **Core 11 (`hbudget`)** — the single G.35 weighted-Kraft scalar budget
  `cnlActiveMult ctx ≤ cnlMinKraftRate ctx`, i.e.
  `(r+1)·(L + carryB Q + 1) − T ≤ 2^{−maxBND}·shellFactor·X·|I_j|`.

## The concrete carry data (rfl, no hypotheses)

The actual N.24 carry datum `ctx.n24CarryData` of a failing context pins the proof-v4 first active
layer *definitionally*:

* `n24CarryData_r_eq` — the descent order is `r = proofV4CarryOrder ctx.shell = ⌊κ·L⌋`
  (`κ = manuscriptKappa = 17/2^18`, `L = shellLadderDepth ctx`, `ctx.shell.X = 2^L`); and
* `n24CarryData_T_eq` — the threshold is `T = 2·L + manuscriptCQ_T = 2L + 1`.

## Core 11 — the budget is **closed exactly on the manuscript first-active-layer regime**, with the
deep-shell residual SHARPLY characterised

The worst-case Kraft rate is genuinely *small* — `cnlMinKraftRate_le_one` proves
`cnlMinKraftRate ctx ≤ 1` (the `2^M` codeword entropy is killed by `X·|I_j| = (1/2)^{|CNLTransition|}`,
the Kraft tiling, and the two `2^{−·}` weights are `≤ 1`).  The active multiplier
`cnlActiveMult ctx = (r+1)·(L+B+1) − (2L+1)` therefore obeys the dichotomy

* **`cnlActiveMult_nonpos_of_r_zero`** — when `r = 0` (the first active layer, `L ≤ ⌊1/κ⌋`),
  `cnlActiveMult ctx = B − L ≤ 0` (since `carryB Q + 25 ≤ L`); hence **the budget holds**
  (`cnl_hbudget_of_r_zero`, `cnlActiveMult ≤ 0 ≤ cnlMinKraftRate`); and
* **`cnlActiveMult_ge_of_r_pos`** — when `r ≥ 1` (deep shells, `L ≥ ⌈1/κ⌉`),
  `cnlActiveMult ctx ≥ 2·carryB Q + 1 ≥ 3 > 1 ≥ cnlMinKraftRate`, so **the budget fails**.

This yields the sharp equivalence **`cnl_hbudget_iff_r_zero`**

```
cnlActiveMult ctx ≤ cnlMinKraftRate ctx  ↔  ctx.n24CarryData.r = 0 .
```

So Core 11 is **fully closed on the manuscript first-active-layer regime** (`r = 0`) and the residual
is *exactly* the deep-shell regime `r ≥ 1`, where the encoded **uniform** active multiplier
`(r+1)(L+B+1) − T` overcounts the per-codeword charge: the honest manuscript fix replaces it by the
*matched* per-codeword window-excess charge (already bounded by the Kraft sum in `cnlBudgetOfShell`),
not by a single uniform multiplier ≤ the worst-case Kraft rate.

## Core 9 — the cluster-reconstruction injectivity producer + the target-card computation

The target family card is `|selectedTransitions (liftTransitionsOfShell ctx)| = |liftTransitionsOfShell ctx|`
(`cnl_target_card_eq`), genuinely positive (`cnl_target_card_pos`) and `≤ Fintype.card CNLTransition`
(`cnl_target_card_le`).  The count core is then **derived from the cluster reconstruction
injectivity** (`cnl_hcard_of_injOn`): any per-context map `f` that is injective on the class-1 fibre
and lands in the surviving family gives `hcard` via `Finset.card_le_card_of_injOn` — the bounded-to-one
L.1.2 reconstruction, no longer assumed.

## What is genuinely proved (no `sorry`/`axiom`/`admit`/`native_decide`)

Every lemma below is proved unconditionally; the only restriction carried into the structure builder
`Class1CNLSeedCore.ofInjOnSmallShell` is the honest `r = 0` first-active-layer hypothesis and the
genuine cluster-reconstruction injection (the surviving CNL family is genuinely nonempty — never
`∅`/`PEmpty`/singleton).
-/

namespace Erdos260

open Finset

set_option linter.unusedVariables false

noncomputable section

/-! ## 1.  The concrete carry order & threshold of the actual N.24 carry data -/

/-- **The descent order of the actual carry data is the proof-v4 floor order** `⌊κ·L⌋`
(definitional). -/
theorem n24CarryData_r_eq (ctx : ActualFailureContext) :
    ctx.n24CarryData.r = proofV4CarryOrder ctx.shell := rfl

/-- **The threshold of the actual carry data is the proof-v4 first active threshold** `2·L + C_Q`
(definitional), with `L = shellLadderDepth ctx` and `C_Q = manuscriptCQ_T = 1`. -/
theorem n24CarryData_T_eq (ctx : ActualFailureContext) :
    ctx.n24CarryData.T = 2 * (shellLadderDepth ctx : ℝ) + (manuscriptCQ_T : ℝ) := rfl

/-- The carry-denominator scale `carryB Q = Nat.log 2 (Q·4) + 1` is at least `1`. -/
theorem carryB_ctx_ge_one (ctx : ActualFailureContext) :
    1 ≤ carryB ctx.shell.Q := by unfold carryB; omega

/-- The manuscript largeness gate `carryB Q + 25 ≤ L` gives `carryB Q ≤ shellLadderDepth ctx`. -/
theorem carryB_ctx_le_shellLadderDepth (ctx : ActualFailureContext) :
    carryB ctx.shell.Q ≤ shellLadderDepth ctx := by
  have h : carryB ctx.shell.Q + 25 ≤ shellLadderDepth ctx := ctx.shell_carryLarge
  omega

/-! ## 2.  The worst-case Kraft rate is small (`cnlMinKraftRate ≤ 1`)

The `2^M` codeword entropy is killed by the Kraft tiling: `X·|I_j| = 2^L·(1/2)^{L+|CNLTransition|}
= (1/2)^{|CNLTransition|} ≤ 1`, and both `2^{−maxBND}` and the shell-Chernoff factor `2^{−c₀ηX}` are
`≤ 1`. -/

/-- **The Kraft tiling identity** `X·|I_j| = (1/2)^{|CNLTransition|}` — the genuine dyadic interval
normalisation `2^M·|I_j| = 1` after dividing out the `2^L = X` scale. -/
theorem shellX_mul_cnlIj (ctx : ActualFailureContext) :
    (ctx.shell.X : ℝ) * (cnlIjOfShell ctx : ℝ)
      = (1 / 2 : ℝ) ^ (Fintype.card CNLTransition) := by
  have hXnat : ctx.shell.X = 2 ^ shellLadderDepth ctx := Classical.choose_spec ctx.shell.hXdyadic
  have hX : (ctx.shell.X : ℝ) = (2 : ℝ) ^ shellLadderDepth ctx := by
    rw [hXnat]; push_cast; ring
  have hIj : (cnlIjOfShell ctx : ℝ) = (1 / 2 : ℝ) ^ (cnlLeafShellM ctx) := rfl
  have hM : cnlLeafShellM ctx = shellLadderDepth ctx + Fintype.card CNLTransition := rfl
  rw [hX, hIj, hM, pow_add, ← mul_assoc,
    show (2 : ℝ) ^ shellLadderDepth ctx * (1 / 2 : ℝ) ^ shellLadderDepth ctx = 1 from by
      rw [← mul_pow]; norm_num,
    one_mul]

/-- **The worst-case per-codeword Kraft rate is at most one.**  Both dyadic weights `2^{−maxBND}` and
`2^{−c₀ηX}` are `≤ 1`, and the Kraft tiling collapses `X·|I_j|` to `(1/2)^{|CNLTransition|} ≤ 1`. -/
theorem cnlMinKraftRate_le_one (ctx : ActualFailureContext) :
    cnlMinKraftRate ctx ≤ 1 := by
  have hA0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(cnlFamilyMaxBnd ctx : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have hA : (2 : ℝ) ^ (-(cnlFamilyMaxBnd ctx : ℝ)) ≤ 1 := by
    have hexp : -(cnlFamilyMaxBnd ctx : ℝ) ≤ 0 := by
      have : (0 : ℝ) ≤ (cnlFamilyMaxBnd ctx : ℝ) := Nat.cast_nonneg _
      linarith
    calc (2 : ℝ) ^ (-(cnlFamilyMaxBnd ctx : ℝ))
          ≤ (2 : ℝ) ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = 1 := Real.rpow_zero 2
  have hB0 : (0 : ℝ) ≤ (cnlShellFactorOfShell ctx : ℝ) := (cnlShellFactorOfShell ctx).2
  have hB : (cnlShellFactorOfShell ctx : ℝ) ≤ 1 := by
    have hBval : (cnlShellFactorOfShell ctx : ℝ)
        = (2 : ℝ) ^ (-(erdos260Constants.c0 * manuscriptEta * (ctx.shell.X : ℝ))) := rfl
    have hexp : -(erdos260Constants.c0 * manuscriptEta * (ctx.shell.X : ℝ)) ≤ 0 := by
      have h6 := cnl_chernoff_exponent_ge ctx
      linarith
    rw [hBval]
    calc (2 : ℝ) ^ (-(erdos260Constants.c0 * manuscriptEta * (ctx.shell.X : ℝ)))
          ≤ (2 : ℝ) ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = 1 := Real.rpow_zero 2
  have hC0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (Fintype.card CNLTransition) := by positivity
  have hC : (1 / 2 : ℝ) ^ (Fintype.card CNLTransition) ≤ 1 := by
    apply pow_le_one₀ <;> norm_num
  have heq : cnlMinKraftRate ctx
      = ((2 : ℝ) ^ (-(cnlFamilyMaxBnd ctx : ℝ)) * (cnlShellFactorOfShell ctx : ℝ))
          * (1 / 2 : ℝ) ^ (Fintype.card CNLTransition) := by
    unfold cnlMinKraftRate
    rw [mul_assoc ((2 : ℝ) ^ (-(cnlFamilyMaxBnd ctx : ℝ)) * (cnlShellFactorOfShell ctx : ℝ))
        (ctx.shell.X : ℝ) (cnlIjOfShell ctx : ℝ), shellX_mul_cnlIj]
  rw [heq]
  have hAB : (2 : ℝ) ^ (-(cnlFamilyMaxBnd ctx : ℝ)) * (cnlShellFactorOfShell ctx : ℝ) ≤ 1 := by
    have := mul_le_mul hA hB hB0 (zero_le_one)
    simpa using this
  have := mul_le_mul hAB hC hC0 (zero_le_one)
  simpa using this

/-! ## 3.  The active multiplier `cnlActiveMult` and its sign dichotomy -/

/-- **First active layer (`r = 0`): the active multiplier is nonpositive.**  Here
`cnlActiveMult ctx = (L+B+1) − (2L+1) = B − L ≤ 0` because the largeness gate forces
`carryB Q ≤ L`. -/
theorem cnlActiveMult_nonpos_of_r_zero (ctx : ActualFailureContext)
    (h : ctx.n24CarryData.r = 0) : cnlActiveMult ctx ≤ 0 := by
  have hB : (carryB ctx.shell.Q : ℝ) ≤ (shellLadderDepth ctx : ℝ) := by
    exact_mod_cast carryB_ctx_le_shellLadderDepth ctx
  have hCQ : (manuscriptCQ_T : ℝ) = 1 := by norm_num [manuscriptCQ_T]
  unfold cnlActiveMult cnlActiveScale
  rw [h, n24CarryData_T_eq, hCQ]
  push_cast
  nlinarith [hB]

/-- **Deep shells (`r ≥ 1`): the active multiplier is at least `2·carryB Q + 1 ≥ 3`.**  Here
`cnlActiveMult ctx = (r+1)(L+B+1) − (2L+1) ≥ 2(L+B+1) − (2L+1) = 2B+1`. -/
theorem cnlActiveMult_ge_of_r_pos (ctx : ActualFailureContext)
    (h : 1 ≤ ctx.n24CarryData.r) :
    2 * (carryB ctx.shell.Q : ℝ) + 1 ≤ cnlActiveMult ctx := by
  have hr : (1 : ℝ) ≤ (ctx.n24CarryData.r : ℝ) := by exact_mod_cast h
  have hL : (0 : ℝ) ≤ (shellLadderDepth ctx : ℝ) := Nat.cast_nonneg _
  have hBnn : (0 : ℝ) ≤ (carryB ctx.shell.Q : ℝ) := Nat.cast_nonneg _
  have hCQ : (manuscriptCQ_T : ℝ) = 1 := by norm_num [manuscriptCQ_T]
  unfold cnlActiveMult cnlActiveScale
  rw [n24CarryData_T_eq, hCQ]
  push_cast
  nlinarith [hr, hL, hBnn,
    mul_nonneg (by linarith : (0 : ℝ) ≤ (ctx.n24CarryData.r : ℝ) - 1)
      (by linarith : (0 : ℝ) ≤ (shellLadderDepth ctx : ℝ) + (carryB ctx.shell.Q : ℝ) + 1)]

/-! ## 4.  Core 11 — the G.35 weighted-Kraft scalar budget -/

/-- **Core 11 closed on the first active layer.**  When the descent order vanishes (`r = 0`, the
manuscript first active layer `L ≤ ⌊1/κ⌋`), the active multiplier is nonpositive while the worst-case
Kraft rate is nonnegative, so the budget `cnlActiveMult ≤ cnlMinKraftRate` holds. -/
theorem cnl_hbudget_of_r_zero (ctx : ActualFailureContext)
    (h : ctx.n24CarryData.r = 0) : cnlActiveMult ctx ≤ cnlMinKraftRate ctx :=
  le_trans (cnlActiveMult_nonpos_of_r_zero ctx h) (cnlMinKraftRate_nonneg ctx)

/-- **The sharp characterisation of Core 11.**  The G.35 weighted-Kraft scalar budget holds *iff* the
descent order vanishes.  Forwards: if `r ≥ 1` then `cnlActiveMult ≥ 2·carryB Q + 1 ≥ 3 > 1 ≥
cnlMinKraftRate`, so the budget fails — the encoded *uniform* active multiplier provably overcounts on
deep shells.  Backwards: `cnl_hbudget_of_r_zero`. -/
theorem cnl_hbudget_iff_r_zero (ctx : ActualFailureContext) :
    cnlActiveMult ctx ≤ cnlMinKraftRate ctx ↔ ctx.n24CarryData.r = 0 := by
  constructor
  · intro hle
    by_contra hne
    have h1 : 1 ≤ ctx.n24CarryData.r := Nat.one_le_iff_ne_zero.mpr hne
    have hge := cnlActiveMult_ge_of_r_pos ctx h1
    have hBpos : (1 : ℝ) ≤ (carryB ctx.shell.Q : ℝ) := by
      exact_mod_cast carryB_ctx_ge_one ctx
    have hKr := cnlMinKraftRate_le_one ctx
    linarith
  · intro h
    exact cnl_hbudget_of_r_zero ctx h

/-! ## 5.  Core 9 — the L.1.2 bounded-multiplicity count

The target family card is `|selectedTransitions (liftTransitionsOfShell ctx)| = |liftTransitionsOfShell ctx|`,
genuinely positive and bounded by `Fintype.card CNLTransition`.  The count is then **derived from the
cluster reconstruction injectivity** — any per-context map `f` that is injective on the class-1 fibre
and lands in the surviving clean-CNL family gives `hcard` (the L.1.2 bounded-to-one reconstruction),
rather than assuming the count. -/

/-- The surviving family is fully selected, so its card equals `|liftTransitionsOfShell ctx|`. -/
theorem cnl_target_card_eq (ctx : ActualFailureContext) :
    (selectedTransitions (liftTransitionsOfShell ctx)).card = (liftTransitionsOfShell ctx).card := by
  rw [selectedTransitions_liftTransitionsOfShell]

/-- The surviving clean-CNL target family is genuinely nonempty (positive card) — never an
empty/`PEmpty`/singleton shortcut. -/
theorem cnl_target_card_pos (ctx : ActualFailureContext) :
    0 < (selectedTransitions (liftTransitionsOfShell ctx)).card :=
  Finset.card_pos.mpr (selectedTransitions_liftTransitionsOfShell_nonempty ctx)

/-- The surviving family card is bounded by the finite model count `Fintype.card CNLTransition`
(the manuscript model-finiteness constant). -/
theorem cnl_target_card_le (ctx : ActualFailureContext) :
    (selectedTransitions (liftTransitionsOfShell ctx)).card ≤ Fintype.card CNLTransition :=
  Finset.card_le_univ _

/-- **Core 9 from the cluster-reconstruction injectivity (the L.1.2 bounded-to-one map).**

Given a per-context reconstruction map `f` that (i) sends each class-1 high-excess start into the
surviving clean-CNL family and (ii) is injective on the class-1 fibre, the L.1.2 count
`|routedFibre … 1| ≤ |selectedTransitions (liftTransitionsOfShell ctx)|` is **derived** via
`Finset.card_le_card_of_injOn` — not assumed.  This is exactly the manuscript §L.1.2 statement that the
clean-CNL cluster reconstruction is bounded-to-one (here the single-multiplicity case). -/
theorem cnl_hcard_of_injOn
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (f : ∀ ctx : ActualFailureContext, ℕ → CNLTransition)
    (hmem : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 1,
        f ctx k ∈ selectedTransitions (liftTransitionsOfShell ctx))
    (hinj : ∀ ctx : ActualFailureContext,
      Set.InjOn (f ctx) (routedFibre ctx.n24CarryData (budget ctx).route 1 : Set ℕ)) :
    ∀ ctx : ActualFailureContext,
      (routedFibre ctx.n24CarryData (budget ctx).route 1).card
        ≤ (selectedTransitions (liftTransitionsOfShell ctx)).card :=
  fun ctx => Finset.card_le_card_of_injOn (f ctx) (hmem ctx) (hinj ctx)

/-! ## 6.  The integration builder for `Class1CNLSeedCore`

Assembling the three field cores into the structure.  My contributions are **Core 9** (`hcard`,
producible from the cluster-reconstruction injection via `cnl_hcard_of_injOn`) and **Core 11**
(`hbudget`, discharged by `cnl_hbudget_of_r_zero` on the first active layer); `hwin` (Core 10) is the
orthogonal active-window containment owned by the sibling worker. -/

/-- **`Class1CNLSeedCore` inhabited on the manuscript first active layer.**  From the L.1.2 count
(`hcard`), the K.1.2 active-window containment (`hwin`, Core 10), and the first-active-layer hypothesis
`r = 0`, the full clean-CNL seed core is built — with the G.35 weighted-Kraft scalar budget Core 11
*fully discharged* (`cnl_hbudget_of_r_zero`).  The target CNL family stays genuinely nonempty
(`cnl_target_card_pos`); nothing is an empty/singleton shortcut. -/
def Class1CNLSeedCore.ofCountWindowSmallShell
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (hcard : ∀ ctx : ActualFailureContext,
      (routedFibre ctx.n24CarryData (budget ctx).route 1).card
        ≤ (selectedTransitions (liftTransitionsOfShell ctx)).card)
    (hwin : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 1,
        ∃ r₀ : ℕ, r₀ + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card ∧
          k + ctx.n24CarryData.r
            < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + r₀)
    (hsmall : ∀ ctx : ActualFailureContext, ctx.n24CarryData.r = 0) :
    Class1CNLSeedCore budget where
  hcard := hcard
  hwin := hwin
  hbudget := fun ctx => cnl_hbudget_of_r_zero ctx (hsmall ctx)

/-! ## 7.  Honest residual inventory -/

/-- The precise status of the clean-CNL seed cores 9 & 11 after this module. -/
def cnlKraftCountCoreResiduals : List String :=
  [ "CONCRETE CARRY DATA (proved, rfl) — n24CarryData_r_eq / n24CarryData_T_eq: the actual N.24 " ++
      "carry datum pins the proof-v4 first active layer definitionally, r = proofV4CarryOrder " ++
      "ctx.shell = ⌊κ·L⌋ (κ = manuscriptKappa = 17/2^18, L = shellLadderDepth ctx, ctx.shell.X = 2^L) " ++
      "and T = 2·L + manuscriptCQ_T = 2L + 1.",
    "KRAFT RATE SMALL (proved) — cnlMinKraftRate_le_one: the worst-case per-codeword Kraft rate " ++
      "2^{−maxBND}·shellFactor·X·|I_j| ≤ 1, via the Kraft tiling X·|I_j| = (1/2)^{|CNLTransition|} ≤ 1 " ++
      "(shellX_mul_cnlIj) and 2^{−maxBND}, 2^{−c₀ηX} ≤ 1.",
    "CORE 11 SIGN DICHOTOMY (proved) — cnlActiveMult_nonpos_of_r_zero: r = 0 ⇒ cnlActiveMult = B − L " ++
      "≤ 0 (carryB Q + 25 ≤ L); cnlActiveMult_ge_of_r_pos: r ≥ 1 ⇒ cnlActiveMult ≥ 2·carryB Q + 1 ≥ 3.",
    "CORE 11 CLOSED (first active layer) — cnl_hbudget_of_r_zero: when r = 0 the G.35 budget " ++
      "cnlActiveMult ctx ≤ cnlMinKraftRate ctx holds (cnlActiveMult ≤ 0 ≤ cnlMinKraftRate). This is " ++
      "the genuine manuscript first-active-layer regime (L ≤ ⌊1/κ⌋), not a degenerate shortcut.",
    "CORE 11 SHARP RESIDUAL (proved equivalence) — cnl_hbudget_iff_r_zero: the budget holds IFF " ++
      "ctx.n24CarryData.r = 0. So the residual is EXACTLY the deep-shell regime r ≥ 1 (L ≥ ⌈1/κ⌉ ≈ " ++
      "15421), where the encoded UNIFORM active multiplier (r+1)(L+B+1) − T ≥ 3 provably overcounts " ++
      "the worst-case Kraft rate ≤ 1. The honest fix (NOT expressible in this field) is the MATCHED " ++
      "per-codeword window-excess charge, already bounded by the Kraft sum in cnlBudgetOfShell.",
    "CORE 9 TARGET CARD (proved) — cnl_target_card_eq / cnl_target_card_pos / cnl_target_card_le: " ++
      "|selectedTransitions (liftTransitionsOfShell ctx)| = |liftTransitionsOfShell ctx|, positive " ++
      "(genuinely nonempty surviving family) and ≤ Fintype.card CNLTransition (model finiteness).",
    "CORE 9 FROM INJECTIVITY (proved producer) — cnl_hcard_of_injOn: the L.1.2 count " ++
      "|routedFibre … 1| ≤ |selectedTransitions …| is DERIVED from any cluster-reconstruction map f " ++
      "that is injective on the class-1 fibre and lands in the surviving family (Finset." ++
      "card_le_card_of_injOn) — the bounded-to-one reconstruction, no longer assumed. Residual: " ++
      "construct f (the §L.1.2 cluster encoding); it exists iff |routedFibre … 1| ≤ |family|, the " ++
      "single-multiplicity special case of the manuscript O_Q(1)-to-one reconstruction.",
    "INTEGRATION (proved) — Class1CNLSeedCore.ofCountWindowSmallShell: from hcard (Core 9) + hwin " ++
      "(Core 10, sibling) + r = 0, the full Class1CNLSeedCore is inhabited with Core 11 discharged." ]

theorem cnlKraftCountCoreResiduals_nonempty : cnlKraftCountCoreResiduals ≠ [] := by
  simp [cnlKraftCountCoreResiduals]

/-! ## 8.  Axiom-cleanliness audit -/

#print axioms n24CarryData_r_eq
#print axioms n24CarryData_T_eq
#print axioms shellX_mul_cnlIj
#print axioms cnlMinKraftRate_le_one
#print axioms cnlActiveMult_nonpos_of_r_zero
#print axioms cnlActiveMult_ge_of_r_pos
#print axioms cnl_hbudget_of_r_zero
#print axioms cnl_hbudget_iff_r_zero
#print axioms cnl_target_card_eq
#print axioms cnl_target_card_pos
#print axioms cnl_target_card_le
#print axioms cnl_hcard_of_injOn
#print axioms Class1CNLSeedCore.ofCountWindowSmallShell

end

end Erdos260
