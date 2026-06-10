import Erdos260.CNLMatchedClosure

/-!
# The multiplicity-aware CNL charge surface, audited to its sharp truth

This module (NEW; it edits no existing file) performs the AUDIT-FIRST closure attempt of the
remaining clean-CNL (class 1) gap: the multiplicity-aware charged-preimage data
`CNLMultiChargeDataForBudget` over the canonical `v3Budget` / `faithfulCapacityPhases`.

## AUDIT VERDICT — the faithful `termCnl` target is WRONG-SCALE; the datum is EQUIVALENT to
outright class-1 fibre emptiness

The canonical N.24 carry datum pins (Part 1, all `rfl`-level):

* `Y = ε·L = L/64` (`n24CarryData_Y_eq`), so `Y ≥ 28/64 = 7/16 > 0` on every shell
  (`shellLadderDepth_ge`);
* `T = 2L + 1` (`cnlMulti_n24_T_eq`); `r = ⌊κL⌋` (`cnlMulti_n24_r_eq`).

The genuine first-obstruction route assigns class `1` only on its terminal catch-all branch, which
*requires* `returnCls = 0`, i.e. `windowExcess ≤ Y`; membership in the high-excess fibre requires
`Y ≤ windowExcess`.  Hence (Part 2) **every class-1 routed start has window excess exactly `Y`**
(`windowExcess_eq_Y_of_mem_class1Fibre`) and the routed class-1 mass is exactly `card·Y`
(`routedClassMass_one_eq_card_mul_Y`).

But the faithful clean-CNL phase term is astronomically small (Part 3): the surviving family has
`≤ 14` codewords, the shell-Chernoff factor is `≤ 2^{-6} = 1/64`, and the Kraft tiling gives
`X·|I_j| ≤ 1`, so `termCnl ≤ 14/64 = 7/32 < 7/16 ≤ Y` (`termCnl_faithful_le_7_32`,
`termCnl_faithful_lt_Y`).

Therefore (Part 4) for EVERY budget the class-1 ledger field
`routedClassMassOf … 1 ≤ termCnl (faithfulCapacityPhases …)` holds at a context **iff** the class-1
routed fibre is empty (`class1Ledger_iff_fibre_empty`); and all three CNL charge surfaces —
`Class1CNLInjection`, `CNLMatchedChargeDataForBudget`, `CNLMultiChargeDataForBudget` — are
inhabitable **iff** the single named Prop

```
Class1FibreEmpty budget : ∀ ctx, routedFibre ctx.n24CarryData (budget ctx).route 1 = ∅
```

holds (`cnlMultiChargeData_iff_class1FibreEmpty`, `cnlMatchedChargeData_iff_multi`).  In particular
the multiplicity-aware relaxation (`O_Q(1)`-to-one reindexing) gains **nothing** for this target:
each per-codeword Kraft cap `cnlShellKraftCap` is `< Y`, so it cannot carry even ONE pinned class-1
excess.  This sharpens the previous one-step obstruction `|fibre₁| ≤ 14` to the exact truth
`|fibre₁| = 0` (`cnlMultiChargeData_forces_fibre_card_zero`).

## What IS closed unconditionally (Parts 5–6c)

* the reindexing map `g` and the landing `hmem` — by the genuine cyclic cluster codeword
  `cnlCanonicalCodeword` (a real member of the genuinely nonempty surviving family, for EVERY
  start, with no hypotheses);
* the **integrality partial closure**: every class-1 routed start has its gap window pinned to
  the exact rational value `gapWindow = (129L + 64)/64` (`class1Fibre_gapWindow_eq`, a `ℕ`-exact
  identity; telescoped hit-position form `class1Fibre_hitPosition_eq`), hence the fibre is
  PROVABLY EMPTY on every shell whose ladder depth is not divisible by `64`
  (`class1Fibre_empty_of_not_dvd64`); the residual shrinks to the `64 ∣ L` subfamily
  (`class1FibreEmpty_of_dvd64_case`);
* the **E.13 band partial closure** (Part 6b): class 1 fires only on the band-4 window of the
  recurrent slope orbit, `canonGap q K_k = 4 ⟺ 8K_k ≤ q < 16K_k` (`class1Fibre_canonGap_eq`,
  `class1Fibre_orbit_band`, successor pin `class1Fibre_orbit_step`), so the fibre is PROVABLY
  EMPTY whenever the closed AP-subfibre modulus is `< 9`
  (`class1Fibre_empty_of_modulus_lt_nine`);
* the **shell-window gap-ceiling partial closure** (Part 6c): the carry starts are definitionally
  the dyadic window `Ico (firstIndexAbove X) (… + |supportShell|)` and the PROVED ceiling
  `hitGap ≤ L + B + 1` holds there, so whenever `64(r+1)(L+B+1) < 129L + 64` the class-1 fibre
  sits in the top `r + 1` boundary band (`class1Fibre_window_overrun`,
  `class1Fibre_card_le_of_gapCeiling`); on every `r = ⌊κL⌋ = 0` shell (ALL `L ≤ 15420`) the gate
  is automatic and `|fibre₁| ≤ 1`, pinned to the single topmost window start
  (`class1Fibre_top_of_r_eq_zero`, `class1Fibre_card_le_one_of_r_eq_zero`).

## The honest minimal residual (sharp arithmetic form, Part 6d)

`Class1FibreEmpty (v3Budget …)` — necessary AND sufficient (so no weaker residual can suffice).
The SHARP membership characterization `mem_class1Fibre_iff` / `class1Fibre_eq_pinnedFilter`
reduces it to the pinned arithmetic form (`v3_class1FibreEmpty_iff_pinned`): no carry-window
start may realize the gap-window pin `64·gapWindow = 129L + 64` and the band-4 pin
`canonGap q K_k = 4` simultaneously.  After the proved closures the surviving subfamily has
`64 ∣ L`, modulus `q ≥ 9`, and (on every `r = 0` shell) only the topmost window start.  There the
hit-gap pin (a property of the actual hit sequence) and the band pin (a property of the recurrent
slope orbit) remain mutually unconstrained in the model — no formalized bridge ties `hitGap a` to
`canonGap` along the orbit for the actual ctx.  We do NOT claim unconditional closure; the
constructive bridges `erdos260_p9V3_of_class1FibreEmpty` / `erdos260_p9V3_of_pinned_arithmetic`
expose the P9 endpoint from exactly this residual.

No `sorry`, `admit`, `axiom`, or `native_decide`.
-/

namespace Erdos260

open Finset

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 1.  The canonical N.24 carry parameters, pinned (`rfl`-level) -/

/-- The canonical N.24 carry order is the manuscript floor order `r = ⌊κL⌋` (local alias of the
upstream `n24CarryData_r_eq`, renamed to avoid the clash with `CNLKraftCountCore`). -/
theorem cnlMulti_n24_r_eq (ctx : ActualFailureContext) :
    ctx.n24CarryData.r = proofV4CarryOrder ctx.shell := rfl

/-- The canonical N.24 carry threshold is the proof-v4 first active threshold `T = 2L + C_Q`. -/
theorem n24CarryData_T_eq_raw (ctx : ActualFailureContext) :
    ctx.n24CarryData.T
      = 2 * ((shellLadderDepth ctx : ℕ) : ℝ) + ((manuscriptCQ_T : ℕ) : ℝ) := rfl

/-- The canonical N.24 active floor is the proof-v4 first active excess `Y = ε·L`. -/
theorem n24CarryData_Y_eq (ctx : ActualFailureContext) :
    ctx.n24CarryData.Y = manuscriptEps * ((shellLadderDepth ctx : ℕ) : ℝ) := rfl

/-- Numeric form of the threshold: `T = 2L + 1` (the pinned `C_Q = 1`).  This is the form the
arithmetic proofs below need; the upstream `n24CarryData_T_eq` keeps the opaque `manuscriptCQ_T`. -/
theorem cnlMulti_n24_T_eq (ctx : ActualFailureContext) :
    ctx.n24CarryData.T = 2 * ((shellLadderDepth ctx : ℕ) : ℝ) + 1 := by
  rw [n24CarryData_T_eq_raw]
  norm_num [manuscriptCQ_T]

/-- Numeric form of the active floor: `Y = L/64` (the pinned `ε = 1/64`). -/
theorem n24CarryData_Y_eq_div (ctx : ActualFailureContext) :
    ctx.n24CarryData.Y = ((shellLadderDepth ctx : ℕ) : ℝ) / 64 := by
  rw [n24CarryData_Y_eq, manuscriptEps]
  ring

/-- **The active floor is uniformly large**: `Y ≥ 28/64 = 7/16` on every actual failure shell
(the large-`X` gate forces `L ≥ 28`). -/
theorem n24CarryData_Y_ge (ctx : ActualFailureContext) :
    (7 : ℝ) / 16 ≤ ctx.n24CarryData.Y := by
  rw [n24CarryData_Y_eq_div]
  have hL : (28 : ℝ) ≤ ((shellLadderDepth ctx : ℕ) : ℝ) := by
    exact_mod_cast shellLadderDepth_ge ctx
  linarith

/-- The canonical active floor is strictly positive — the class-1 fibre filter is genuine. -/
theorem n24CarryData_Y_pos (ctx : ActualFailureContext) :
    0 < ctx.n24CarryData.Y := by
  have h := n24CarryData_Y_ge ctx
  linarith

/-! ## Part 2.  The class-1 window-excess pinning on the genuine route -/

/-- Routed-fibre membership forces the high-excess floor `Y ≤ windowExcess` (any route, any class). -/
theorem Y_le_windowExcess_of_mem_routedFibre
    {shell : FailingDyadicShell} {cPr : ℝ} {ι : Type*} [DecidableEq ι]
    (carryData : CarryDataFromFailure shell cPr) (route : ℕ → ι) (i : ι)
    {k : ℕ} (hk : k ∈ routedFibre carryData route i) :
    carryData.Y ≤ windowExcess (hitGap carryData.a) k carryData.r carryData.T := by
  have hmem := Finset.mem_filter.mp hk
  exact (mem_highExcessStarts.mp hmem.1).2

/-- A `Fin 3` value differing from `1` and `2` is `0`. -/
private theorem fin3_eq_zero_of_ne {c : Fin 3} (h1 : c ≠ 1) (h2 : c ≠ 2) : c = 0 := by
  fin_cases c <;> simp_all

/-- The K.4 return band classifier returns `0` exactly on the low band `windowExcess ≤ Y`. -/
theorem returnCls_eq_zero_iff (ctx : ActualFailureContext) (k : ℕ) :
    returnCls ctx k = 0
      ↔ windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
          ≤ ctx.n24CarryData.Y := by
  unfold returnCls
  split_ifs with h1 h2
  · exact ⟨fun _ => h1, fun _ => rfl⟩
  · exact ⟨fun hc => absurd hc (by decide), fun hc => absurd hc h1⟩
  · exact ⟨fun hc => absurd hc (by decide), fun hc => absurd hc h1⟩

/-- **The genuine route reaches class `1` only through its terminal catch-all branch**, which
requires the return classifier to sit in the low band `returnCls = 0`. -/
theorem returnCls_eq_zero_of_genuineChargeRoute_eq_one
    (ctx : ActualFailureContext) {k : ℕ}
    (h : genuineChargeRoute ctx k = 1) :
    returnCls ctx k = 0 := by
  unfold genuineChargeRoute at h
  split_ifs at h with h3 h0 h5 h4 hrun hret2 hret1
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact fin3_eq_zero_of_ne hret1 hret2

/-- **The class-1 window-excess pinning.**  On the genuine first-obstruction route, every class-1
routed start has window excess EXACTLY equal to the active floor `Y`: the high-excess filter gives
`Y ≤ windowExcess`, and the terminal catch-all branch (`returnCls = 0`) gives `windowExcess ≤ Y`.
The class-1 band of the v3 route is the razor-thin level set `{windowExcess = Y}`. -/
theorem windowExcess_eq_Y_of_mem_class1Fibre
    (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1) :
    windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
      = ctx.n24CarryData.Y := by
  have hge := Y_le_windowExcess_of_mem_routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 hk
  have hroute : genuineChargeRoute ctx k = 1 := (Finset.mem_filter.mp hk).2
  have hle := (returnCls_eq_zero_iff ctx k).mp
    (returnCls_eq_zero_of_genuineChargeRoute_eq_one ctx hroute)
  exact le_antisymm hle hge

/-- **The routed class-1 mass identity**: on the genuine route the class-1 mass is exactly
`card(fibre₁) · Y`. -/
theorem routedClassMass_one_eq_card_mul_Y (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 1
      = ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
          * ctx.n24CarryData.Y := by
  rw [routedClassMassOf_eq_sum_fibre]
  rw [Finset.sum_congr rfl (fun k hk => windowExcess_eq_Y_of_mem_class1Fibre ctx hk)]
  rw [Finset.sum_const, nsmul_eq_mul]

/-! ## Part 3.  The faithful clean-CNL phase term is below the active floor -/

/-- The faithful clean-CNL phase term, written out through the concrete shell data. -/
theorem termCnl_faithful_eq
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    termCnl (faithfulCapacityPhases budget ctx).toClosurePhaseData
      = cleanCNLKraftSum (faithfulCnlData budget ctx).paths
          (faithfulCnlData budget ctx).BNDHeight (faithfulCnlData budget ctx).c
        * (faithfulCnlData budget ctx).shellFactor * (ctx.shell.X : ℝ)
        * (faithfulCnlData budget ctx).Ij := rfl

/-- The faithful clean-CNL Kraft sum is at most the fixed alphabet count `14`. -/
theorem faithful_kraftSum_le_14
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    cleanCNLKraftSum (faithfulCnlData budget ctx).paths
        (faithfulCnlData budget ctx).BNDHeight (faithfulCnlData budget ctx).c ≤ 14 := by
  have h1 : cleanCNLKraftSum (faithfulCnlData budget ctx).paths
      (faithfulCnlData budget ctx).BNDHeight (faithfulCnlData budget ctx).c
      ≤ ((faithfulCnlData budget ctx).paths.card : ℝ) := by
    refine cleanCNLKraftSum_le_card_of_nonneg_height _ _ ?_ ?_
    · rw [faithfulCnlData_c]; norm_num
    · intro p _hp
      rw [faithfulCnlData_BNDHeight]
      exact Nat.cast_nonneg _
  have h2 : ((faithfulCnlData budget ctx).paths.card : ℝ) ≤ 14 := by
    rw [faithfulCnlData_paths]
    exact_mod_cast cnlFamily_card_le_14 ctx
  exact h1.trans h2

/-- The faithful shell-Chernoff factor is at most `2^{-6} = 1/64` (the large-`X` gate). -/
theorem faithful_shellFactor_le
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    (faithfulCnlData budget ctx).shellFactor ≤ 1 / 64 := by
  rw [faithfulCnlData_shellFactor]
  have hsf : (cnlShellFactorOfShell ctx : ℝ)
      = (2 : ℝ) ^ (-(erdos260Constants.c0 * manuscriptEta * (ctx.shell.X : ℝ))) := rfl
  rw [hsf]
  have h6 : (6 : ℝ) ≤ erdos260Constants.c0 * manuscriptEta * (ctx.shell.X : ℝ) :=
    cnl_chernoff_exponent_ge ctx
  have hmono : (2 : ℝ) ^ (-(erdos260Constants.c0 * manuscriptEta * (ctx.shell.X : ℝ)))
      ≤ (2 : ℝ) ^ (-(6 : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    linarith
  have hval : (2 : ℝ) ^ (-(6 : ℝ)) = 1 / 64 := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      show (6 : ℝ) = ((6 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
    norm_num
  rw [hval] at hmono
  exact hmono

/-- The Kraft tiling collapses the shell scale: `X · |I_j| ≤ 1` for the faithful interval length
`|I_j| = 2^{-(L + |CNLTransition|)}` at the dyadic scale `X = 2^L`. -/
theorem faithful_X_mul_Ij_le_one
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    (ctx.shell.X : ℝ) * (faithfulCnlData budget ctx).Ij ≤ 1 := by
  rw [faithfulCnlData_Ij]
  have hij : (cnlIjOfShell ctx : ℝ) = ((1 : ℝ) / 2) ^ cnlLeafShellM ctx := rfl
  rw [hij]
  have hXeq : ctx.shell.X = 2 ^ shellLadderDepth ctx := Classical.choose_spec ctx.shell.hXdyadic
  have hXr : (ctx.shell.X : ℝ) = (2 : ℝ) ^ shellLadderDepth ctx := by
    rw [hXeq]; push_cast; ring
  rw [hXr]
  have hM : shellLadderDepth ctx ≤ cnlLeafShellM ctx := by
    unfold cnlLeafShellM; omega
  have hmono : ((1 : ℝ) / 2) ^ cnlLeafShellM ctx ≤ ((1 : ℝ) / 2) ^ shellLadderDepth ctx :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hM
  calc (2 : ℝ) ^ shellLadderDepth ctx * ((1 : ℝ) / 2) ^ cnlLeafShellM ctx
      ≤ (2 : ℝ) ^ shellLadderDepth ctx * ((1 : ℝ) / 2) ^ shellLadderDepth ctx :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = 1 := by rw [← mul_pow]; norm_num

/-- **The faithful clean-CNL phase term is at most `7/32`** — `14` codewords, shell factor
`≤ 1/64`, Kraft tiling `X·|I_j| ≤ 1`. -/
theorem termCnl_faithful_le_7_32
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    termCnl (faithfulCapacityPhases budget ctx).toClosurePhaseData ≤ 7 / 32 := by
  have hK := faithful_kraftSum_le_14 budget ctx
  have hK0 : 0 ≤ cleanCNLKraftSum (faithfulCnlData budget ctx).paths
      (faithfulCnlData budget ctx).BNDHeight (faithfulCnlData budget ctx).c :=
    cleanCNLKraftSum_nonneg _ _ _
  have hsf := faithful_shellFactor_le budget ctx
  have hsf0 : 0 ≤ (faithfulCnlData budget ctx).shellFactor :=
    (faithfulCnlData budget ctx).shellFactor_nonneg
  have hXIj := faithful_X_mul_Ij_le_one budget ctx
  have hXIj0 : 0 ≤ (ctx.shell.X : ℝ) * (faithfulCnlData budget ctx).Ij :=
    mul_nonneg ctx.shell.X_nonneg_real (faithfulCnlData budget ctx).Ij_nonneg
  calc termCnl (faithfulCapacityPhases budget ctx).toClosurePhaseData
      = (cleanCNLKraftSum (faithfulCnlData budget ctx).paths
            (faithfulCnlData budget ctx).BNDHeight (faithfulCnlData budget ctx).c
          * (faithfulCnlData budget ctx).shellFactor)
        * ((ctx.shell.X : ℝ) * (faithfulCnlData budget ctx).Ij) := by
        rw [termCnl_faithful_eq budget ctx]; ring
    _ ≤ ((14 : ℝ) * (1 / 64)) * 1 := by
        refine mul_le_mul ?_ hXIj hXIj0 (by norm_num)
        exact mul_le_mul hK hsf hsf0 (by norm_num)
    _ ≤ 7 / 32 := by norm_num

/-- The faithful clean-CNL phase term is nonnegative. -/
theorem termCnl_faithful_nonneg
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    0 ≤ termCnl (faithfulCapacityPhases budget ctx).toClosurePhaseData := by
  rw [termCnl_faithful_eq budget ctx]
  have hK0 : 0 ≤ cleanCNLKraftSum (faithfulCnlData budget ctx).paths
      (faithfulCnlData budget ctx).BNDHeight (faithfulCnlData budget ctx).c :=
    cleanCNLKraftSum_nonneg _ _ _
  exact mul_nonneg (mul_nonneg (mul_nonneg hK0
    (faithfulCnlData budget ctx).shellFactor_nonneg) ctx.shell.X_nonneg_real)
    (faithfulCnlData budget ctx).Ij_nonneg

/-- **The scale gap**: the faithful clean-CNL phase term is strictly below the pinned class-1
per-start excess `Y = L/64 ≥ 7/16`, on every context and for every budget.  No per-codeword Kraft
cap can carry even a single pinned class-1 excess. -/
theorem termCnl_faithful_lt_Y
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    termCnl (faithfulCapacityPhases budget ctx).toClosurePhaseData < ctx.n24CarryData.Y := by
  have h1 := termCnl_faithful_le_7_32 budget ctx
  have h2 := n24CarryData_Y_ge ctx
  linarith

/-! ## Part 4.  The sharp characterization: ledger field ⟺ fibre emptiness ⟺ datum -/

/-- **The class-1 ledger field is EQUIVALENT to class-1 fibre emptiness** (any budget, any route).
Forward: a fibre member contributes window excess `≥ Y > termCnl`.  Backward: the empty sum is
`0 ≤ termCnl`. -/
theorem class1Ledger_iff_fibre_empty
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    (routedClassMassOf ctx.n24CarryData (budget ctx).route 1
        ≤ termCnl (faithfulCapacityPhases budget ctx).toClosurePhaseData)
      ↔ routedFibre ctx.n24CarryData (budget ctx).route 1 = ∅ := by
  constructor
  · intro hled
    by_contra hne
    obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hwk : ctx.n24CarryData.Y
        ≤ windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T :=
      Y_le_windowExcess_of_mem_routedFibre ctx.n24CarryData (budget ctx).route 1 hk
    have hmass : windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        ≤ routedClassMassOf ctx.n24CarryData (budget ctx).route 1 := by
      rw [routedClassMassOf_eq_sum_fibre]
      exact Finset.single_le_sum
        (f := fun j => windowExcess (hitGap ctx.n24CarryData.a) j ctx.n24CarryData.r
          ctx.n24CarryData.T)
        (fun j _ => windowExcess_nonneg _ _ _ _) hk
    have hterm := termCnl_faithful_lt_Y budget ctx
    linarith
  · intro hempty
    rw [routedClassMassOf_eq_sum_fibre, hempty, Finset.sum_empty]
    exact termCnl_faithful_nonneg budget ctx

/-- **THE minimal residual of the v3 clean-CNL atom**: the class-1 routed fibre is empty on every
actual failure context.  By the equivalences below this is necessary AND sufficient for all three
CNL charge surfaces over the faithful `termCnl` target. -/
def Class1FibreEmpty
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx) : Prop :=
  ∀ ctx : ActualFailureContext, routedFibre ctx.n24CarryData (budget ctx).route 1 = ∅

/-- The ∀-ctx class-1 ledger field is equivalent to the named residual. -/
theorem hCnlField_iff_class1FibreEmpty
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx) :
    (∀ ctx : ActualFailureContext,
        routedClassMassOf ctx.n24CarryData (budget ctx).route 1
          ≤ termCnl (faithfulCapacityPhases budget ctx).toClosurePhaseData)
      ↔ Class1FibreEmpty budget :=
  forall_congr' (fun ctx => class1Ledger_iff_fibre_empty budget ctx)

/-- The multiplicity-aware datum forces the class-1 fibre to be empty on every context (the sharp
strengthening of the one-step `≤ 14` obstruction: the count collapses to `0`). -/
theorem cnlMultiChargeData_forces_class1FibreEmpty
    {budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}
    (R : CNLMultiChargeDataForBudget budget) :
    Class1FibreEmpty budget :=
  fun ctx => (class1Ledger_iff_fibre_empty budget ctx).mp (R.hCnlField ctx)

/-- The multiplicity-aware datum forces `|fibre₁| = 0` — strictly sharper than the proved one-step
obstruction `|fibre₁| ≤ |selectedTransitions| ≤ 14`. -/
theorem cnlMultiChargeData_forces_fibre_card_zero
    {budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}
    (R : CNLMultiChargeDataForBudget budget) (ctx : ActualFailureContext) :
    (routedFibre ctx.n24CarryData (budget ctx).route 1).card = 0 := by
  rw [cnlMultiChargeData_forces_class1FibreEmpty R ctx]
  exact Finset.card_empty

/-- **A single context with ONE class-1 routed start refutes the multiplicity-aware datum.**  The
sharp numeric obstruction: the previous `Class1CNLInjection` obstruction needed `14 < |fibre₁|`;
the faithful-target audit needs only `0 < |fibre₁|`. -/
theorem no_cnlMultiChargeData_of_fibre_nonempty
    {budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}
    (ctx : ActualFailureContext)
    (h : (routedFibre ctx.n24CarryData (budget ctx).route 1).Nonempty) :
    ¬ Nonempty (CNLMultiChargeDataForBudget budget) := by
  rintro ⟨R⟩
  rw [cnlMultiChargeData_forces_class1FibreEmpty R ctx] at h
  exact Finset.not_nonempty_empty h

/-! ## Part 5.  The constructive bridge: `g`/`hmem` closed, residual = `Class1FibreEmpty` -/

/-- The per-codeword Kraft cap is nonnegative. -/
theorem cnlShellKraftCap_nonneg (ctx : ActualFailureContext) (t : CNLTransition) :
    0 ≤ cnlShellKraftCap ctx t :=
  mul_nonneg
    (mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (cnlShellFactorOfShell ctx).2)
      ctx.shell.X_nonneg_real)
    (cnlIjOfShell ctx).2

/-- **The multiplicity-aware datum from the named residual.**  The reindexing map is the genuine
cyclic cluster codeword `cnlCanonicalCodeword` (a real member of the genuinely nonempty surviving
family for EVERY start — `g` and `hmem` are closed constructively, with no hypotheses); the
charged-preimage bound is discharged by the residual. -/
def cnlMultiChargeDataOfClass1FibreEmpty
    {budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}
    (hempty : Class1FibreEmpty budget) :
    CNLMultiChargeDataForBudget budget where
  g := fun ctx => cnlCanonicalCodeword ctx
  hmem := fun ctx k _hk => cnlCanonicalCodeword_mem ctx k
  hcharged := fun ctx t _ht => by
    rw [hempty ctx, Finset.filter_empty, Finset.sum_empty]
    exact cnlShellKraftCap_nonneg ctx t

/-- The one-step matched datum from the named residual (the injectivity over the empty fibre is
immediate; the map and landing are the genuine cyclic codeword as above). -/
def cnlMatchedChargeDataOfClass1FibreEmpty
    {budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}
    (hempty : Class1FibreEmpty budget) :
    CNLMatchedChargeDataForBudget budget where
  g := fun ctx => cnlCanonicalCodeword ctx
  hmem := fun ctx k _hk => cnlCanonicalCodeword_mem ctx k
  hinj := fun ctx k₁ hk₁ k₂ hk₂ _heq =>
    absurd (hempty ctx ▸ hk₁) (Finset.notMem_empty k₁)
  hcharge := fun ctx k hk =>
    absurd (hempty ctx ▸ hk) (Finset.notMem_empty k)

/-- **The multiplicity-aware CNL charge surface is inhabitable IFF the class-1 fibre is empty.**
This is the exact satisfiability frontier of the v3 clean-CNL atom over the faithful target. -/
theorem cnlMultiChargeData_iff_class1FibreEmpty
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx) :
    Nonempty (CNLMultiChargeDataForBudget budget) ↔ Class1FibreEmpty budget :=
  ⟨fun ⟨R⟩ => cnlMultiChargeData_forces_class1FibreEmpty R,
   fun h => ⟨cnlMultiChargeDataOfClass1FibreEmpty h⟩⟩

/-- The one-step matched surface is inhabitable iff the class-1 fibre is empty. -/
theorem cnlMatchedChargeData_iff_class1FibreEmpty
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx) :
    Nonempty (CNLMatchedChargeDataForBudget budget) ↔ Class1FibreEmpty budget :=
  ⟨fun ⟨R⟩ => cnlMultiChargeData_forces_class1FibreEmpty (.ofMatched R),
   fun h => ⟨cnlMatchedChargeDataOfClass1FibreEmpty h⟩⟩

/-- **The multiplicity-aware relaxation gains NOTHING over the faithful target**: the matched
(injective) and multiplicity-aware surfaces are equi-inhabitable.  The `O_Q(1)`-to-one freedom is
swallowed by the scale gap `cnlShellKraftCap < Y`. -/
theorem cnlMatchedChargeData_iff_multi
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx) :
    Nonempty (CNLMatchedChargeDataForBudget budget)
      ↔ Nonempty (CNLMultiChargeDataForBudget budget) := by
  rw [cnlMatchedChargeData_iff_class1FibreEmpty, cnlMultiChargeData_iff_class1FibreEmpty]

/-- Any `Class1CNLInjection` already forces full class-1 fibre emptiness — the sharp strengthening
of `class1CNLInjection_fibre_card_le_14` from `≤ 14` to `= 0`. -/
theorem class1CNLInjection_forces_class1FibreEmpty
    {budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}
    (R : Class1CNLInjection budget) :
    Class1FibreEmpty budget :=
  cnlMultiChargeData_forces_class1FibreEmpty
    (.ofMatched (CNLMatchedChargeDataForBudget.ofInjection R))

/-! ## Part 6.  Partial unconditional closure of the residual: the integrality pinning -/

/-- **The class-1 gap-window pinning (exact `ℕ` identity).**  Every class-1 routed start of the
genuine route has its `(r+1)`-step gap window pinned to the exact rational value
`gapWindow = (129·L + 64)/64`: in integers, `64·gapWindow = 129·L + 64`. -/
theorem class1Fibre_gapWindow_eq (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1) :
    64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
      = 129 * shellLadderDepth ctx + 64 := by
  have heq := windowExcess_eq_Y_of_mem_class1Fibre ctx hk
  -- Rewrite with the NUMERIC pins first (T = 2L + 1, Y = L/64), then unfold the excess.
  rw [cnlMulti_n24_T_eq, n24CarryData_Y_eq_div] at heq
  have hL : (28 : ℝ) ≤ ((shellLadderDepth ctx : ℕ) : ℝ) := by
    exact_mod_cast shellLadderDepth_ge ctx
  unfold windowExcess positivePart at heq
  by_cases hle : ((gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r : ℕ) : ℝ)
      - (2 * ((shellLadderDepth ctx : ℕ) : ℝ) + 1) ≤ 0
  · rw [max_eq_right hle] at heq
    linarith
  · rw [max_eq_left (not_le.mp hle).le] at heq
    have hreal : (64 : ℝ) * ((gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r : ℕ) : ℝ)
        = 129 * ((shellLadderDepth ctx : ℕ) : ℝ) + 64 := by
      linarith
    exact_mod_cast hreal

/-- **Integrality partial closure**: the class-1 routed fibre of the genuine route is PROVABLY
EMPTY on every shell whose dyadic ladder depth is not divisible by `64` — the pinned excess
`Y = L/64` cannot be realized by an integer gap window unless `64 ∣ L`. -/
theorem class1Fibre_empty_of_not_dvd64 (ctx : ActualFailureContext)
    (h : ¬ (64 ∣ shellLadderDepth ctx)) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro k hk
  have hg := class1Fibre_gapWindow_eq ctx hk
  exact h (by omega)

/-- The v3 seed budget routes through the genuine route, so the integrality closure applies to it
verbatim. -/
theorem v3_class1Fibre_empty_of_not_dvd64
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runChain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (ctx : ActualFailureContext)
    (h : ¬ (64 ∣ shellLadderDepth ctx)) :
    routedFibre ctx.n24CarryData
      ((v3Budget towerCount runChain returnCharge) ctx).route 1 = ∅ :=
  class1Fibre_empty_of_not_dvd64 ctx h

/-- **The residual shrinks to the `64 ∣ L` shell subfamily**: to close `Class1FibreEmpty` for the
v3 budget it suffices to treat the shells whose ladder depth is divisible by `64`. -/
theorem class1FibreEmpty_of_dvd64_case
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runChain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (h : ∀ ctx : ActualFailureContext, 64 ∣ shellLadderDepth ctx →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅) :
    Class1FibreEmpty (v3Budget towerCount runChain returnCharge) := by
  intro ctx
  by_cases hdvd : 64 ∣ shellLadderDepth ctx
  · exact h ctx hdvd
  · exact class1Fibre_empty_of_not_dvd64 ctx hdvd

/-! ## Part 6b.  The slope-orbit band pinning (the SECOND exact constraint)

The routing side: class 1 fires only on `towerClsOfShell ctx k = cnlTail`, i.e. only when the E.13
canonical-gap band index of the recurrent slope orbit at `k` is EXACTLY `4`.  By the proved E.13
band bounds this pins the orbit numerator into the dyadic band `q/16 < K_k ≤ q/8`; in particular
the AP-subfibre modulus must satisfy `q ≥ 9`, so the class-1 fibre is PROVABLY EMPTY on every shell
whose closed AP-subfibre modulus is `< 9`. -/

/-- **The closed AP-subfibre slope datum of the shell** — the very datum through which
`towerClsOfShell` routes (`S = carryAPSubfibreOfFailingShellClosed ctx.shell P (η = P/Q)`). -/
def class1SlopeDatum (ctx : ActualFailureContext) :
    CarryAPSubfibre ctx.shell.Q ctx.shell.hrational.choose :=
  carryAPSubfibreOfFailingShellClosed ctx.shell
    ctx.shell.hrational.choose ctx.shell.hrational.choose_spec

/-- The L.3.1 classifier IS the band readout of the slope datum (definitional). -/
theorem towerClsOfShell_eq_band (ctx : ActualFailureContext) (k : ℕ) :
    towerClsOfShell ctx k
      = towerExitClassOfGap
          (canonGap (class1SlopeDatum ctx).q
            (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k)) := rfl

/-- The band classifier hits `cnlTail` exactly on band index `4`. -/
theorem towerExitClassOfGap_eq_cnlTail_iff (g : ℕ) :
    towerExitClassOfGap g = TowerExitClass.cnlTail ↔ g = 4 := by
  constructor
  · intro h
    rcases g with _ | _ | _ | _ | _ | n
    · cases h
    · cases h
    · cases h
    · cases h
    · rfl
    · cases h
  · intro h
    subst h
    rfl

/-- **The E.13 band-4 window**: `canonGap q K = 4` iff `8K ≤ q < 16K` (for `K ≥ 1`). -/
theorem canonGap_eq_four_iff {q K : ℕ} (hK : 1 ≤ K) :
    canonGap q K = 4 ↔ 8 * K ≤ q ∧ q < 16 * K := by
  unfold canonGap
  constructor
  · intro h
    have hlog : Nat.log 2 (q / K) = 3 := by omega
    have hne : q / K ≠ 0 := by
      intro h0
      rw [h0, Nat.log_zero_right] at hlog
      exact absurd hlog (by norm_num)
    have h8 : 8 ≤ q / K := by
      have hpow := Nat.pow_log_le_self 2 hne
      rw [hlog] at hpow
      norm_num at hpow
      exact hpow
    have h16 : q / K < 16 := by
      have hpow := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (q / K)
      rw [hlog] at hpow
      norm_num at hpow
      exact hpow
    exact ⟨(Nat.le_div_iff_mul_le hK).mp h8, (Nat.div_lt_iff_lt_mul hK).mp h16⟩
  · rintro ⟨h8, h16⟩
    have h8' : 8 ≤ q / K := (Nat.le_div_iff_mul_le hK).mpr h8
    have h16' : q / K < 16 := (Nat.div_lt_iff_lt_mul hK).mpr h16
    have hlog : Nat.log 2 (q / K) = 3 :=
      Nat.log_eq_of_pow_le_of_lt_pow (by norm_num; omega) (by norm_num; omega)
    omega

/-- **The class-1 band pin**: every class-1 routed start of the genuine route has its slope-orbit
canonical-gap band index EXACTLY `4`. -/
theorem class1Fibre_canonGap_eq (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1) :
    canonGap (class1SlopeDatum ctx).q
      (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 4 := by
  have hroute : genuineChargeRoute ctx k = 1 := (Finset.mem_filter.mp hk).2
  have htower := ((genuineChargeRoute_eq_one_iff ctx k).mp hroute).1
  rw [towerClsOfShell_eq_band] at htower
  exact (towerExitClassOfGap_eq_cnlTail_iff _).mp htower

/-- **The class-1 orbit-band pin**: the slope-orbit numerator at every class-1 start sits in the
dyadic band `8·K_k ≤ q < 16·K_k`, i.e. `q/16 < K_k ≤ q/8`. -/
theorem class1Fibre_orbit_band (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1) :
    8 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
        ≤ (class1SlopeDatum ctx).q
      ∧ (class1SlopeDatum ctx).q
        < 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k := by
  have hband := class1Fibre_canonGap_eq ctx hk
  have horb := slopeOrbit_mem (class1SlopeDatum ctx).hq_odd (class1SlopeDatum ctx).hK₀_pos
    (class1SlopeDatum ctx).hK₀_lt k
  exact (canonGap_eq_four_iff horb.1).mp hband

/-- **The class-1 orbit-step pin**: at every class-1 start the E.12/E.13 successor numerator is
EXACTLY `16·K_k − q` (the band-4 carry-doubling step). -/
theorem class1Fibre_orbit_step (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1) :
    slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (k + 1)
      = 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
        - (class1SlopeDatum ctx).q := by
  have hband := class1Fibre_canonGap_eq ctx hk
  have hstep : slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (k + 1)
      = boundedSlopeStep (class1SlopeDatum ctx).q
          (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) := rfl
  rw [hstep]
  unfold boundedSlopeStep
  rw [hband]
  norm_num

/-- **A nonempty class-1 fibre forces a large AP-subfibre modulus**: `q ≥ 9` (the band `8K ≤ q`
needs `q ≥ 8`, and `q` is odd). -/
theorem modulus_ge_nine_of_class1Fibre_nonempty (ctx : ActualFailureContext)
    (h : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).Nonempty) :
    9 ≤ (class1SlopeDatum ctx).q := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨h8, h16⟩ := class1Fibre_orbit_band ctx hk
  have horb := slopeOrbit_mem (class1SlopeDatum ctx).hq_odd (class1SlopeDatum ctx).hK₀_pos
    (class1SlopeDatum ctx).hK₀_lt k
  obtain ⟨m, hm⟩ := (class1SlopeDatum ctx).hq_odd
  have h1 := horb.1
  omega

/-- **Small-modulus closure**: the class-1 routed fibre of the genuine route is PROVABLY EMPTY on
every shell whose closed AP-subfibre modulus is `< 9` (`q ∈ {3, 5, 7}`) — the E.13 band-4 window
`8K ≤ q < 16K` is unsatisfiable below `q = 9`. -/
theorem class1Fibre_empty_of_modulus_lt_nine (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q < 9) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro k hk
  have h9 := modulus_ge_nine_of_class1Fibre_nonempty ctx ⟨k, hk⟩
  omega

/-- The v3 seed budget routes through the genuine route, so the small-modulus closure applies. -/
theorem v3_class1Fibre_empty_of_modulus_lt_nine
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runChain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q < 9) :
    routedFibre ctx.n24CarryData
      ((v3Budget towerCount runChain returnCharge) ctx).route 1 = ∅ :=
  class1Fibre_empty_of_modulus_lt_nine ctx hq

/-! ## Part 6c.  The shell-window gap ceiling: class-1 starts are window-boundary starts

The carry start set is *definitionally* the dyadic shell index window
`Ico (firstIndexAbove X) (firstIndexAbove X + |supportShell d X|)`, and on that window the PROVED
dyadic-scale estimate `hitGap a j ≤ L + B + 1` holds (`HitSequence.hitGap_le_of_shell_window`).
Since the class-1 pin demands the much larger window sum `gapWindow = (129L+64)/64 > 2L`, every
class-1 start must push its descent window past the ceiling's reach: it lives in the top `r + 1`
boundary band of the shell window.  On `r = 0` shells (all `L ≤ 15420`, since `r = ⌊κL⌋`,
`κ = 17/2^18`) this pins the fibre inside the SINGLE topmost start: `|fibre₁| ≤ 1`. -/

/-- **The carry start set is the dyadic shell index window** (definitional through the entire
`appendixNGapCanonicalYCarryLocalAt … ofShellAndLowExcess` construction chain). -/
theorem cnlMulti_starts_eq_window (ctx : ActualFailureContext) :
    ctx.n24CarryData.starts
      = Finset.Ico (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X)
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card) := rfl

/-- The stored descent order fits the window: `r + 1 ≤ |supportShell d X|`. -/
theorem cnlMulti_r_add_one_le_width (ctx : ActualFailureContext) :
    ctx.n24CarryData.r + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card :=
  ctx.n24CarryLocal.hKr

/-- **The dyadic-scale gap ceiling on the shell window** (the PROVED
`HitSequence.hitGap_le_of_shell_window` on the actual carry hits): every index `j` with
`j + 1 < firstIndexAbove X + |supportShell d X|` has `hitGap a j ≤ L + B + 1`. -/
theorem n24_hitGap_le_window (ctx : ActualFailureContext) {j : ℕ}
    (hj : j + 1 < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
        + (supportShell ctx.shell.d ctx.shell.X).card) :
    hitGap ctx.n24CarryData.a j ≤ shellLadderDepth ctx + carryB ctx.shell.Q + 1 := by
  have hK1 : 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card := by
    have h := cnlMulti_r_add_one_le_width ctx
    omega
  exact ctx.n24CarryData.carry.hits.hitGap_le_of_shell_window
    ctx.shell.hd ctx.shell.hQ
    (Classical.choose_spec ctx.shell.hrational)
    (Classical.choose_spec ctx.shell.hXdyadic)
    ctx.shell.X_pos
    (carryB_spec ctx.shell.hQ)
    (r := (supportShell ctx.shell.d ctx.shell.X).card - 1)
    (by omega) (by omega)

/-- Every class-1 routed start lies in the dyadic shell index window `i ≤ k < i + K`. -/
theorem class1Fibre_mem_window (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1) :
    ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X ≤ k
      ∧ k < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + (supportShell ctx.shell.d ctx.shell.X).card := by
  have hstart : k ∈ ctx.n24CarryData.starts :=
    (mem_highExcessStarts.mp (Finset.mem_filter.mp hk).1).1
  rw [cnlMulti_starts_eq_window, Finset.mem_Ico] at hstart
  exact hstart

/-- **The window-overrun pin.**  Whenever the gap ceiling beats the class-1 window-sum pin
numerically (`64·(r+1)·(L+B+1) < 129·L + 64`), every class-1 start's descent window must overrun
the shell window: `firstIndexAbove X + |supportShell d X| ≤ k + r + 1`.  In particular class-1
starts live ONLY in the top `r + 1` boundary band of the shell window. -/
theorem class1Fibre_window_overrun (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hnum : 64 * ((ctx.n24CarryData.r + 1)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
        < 129 * shellLadderDepth ctx + 64) :
    ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
        + (supportShell ctx.shell.d ctx.shell.X).card
      ≤ k + ctx.n24CarryData.r + 1 := by
  by_contra hint
  have hint' : k + ctx.n24CarryData.r + 1
      < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
        + (supportShell ctx.shell.d ctx.shell.X).card := Nat.lt_of_not_le hint
  have hgap : ∀ m ∈ Finset.range (ctx.n24CarryData.r + 1),
      hitGap ctx.n24CarryData.a (k + m)
        ≤ shellLadderDepth ctx + carryB ctx.shell.Q + 1 := by
    intro m hm
    rw [Finset.mem_range] at hm
    exact n24_hitGap_le_window ctx (by omega)
  have hsum : gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
      ≤ (ctx.n24CarryData.r + 1) * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) := by
    unfold gapWindow
    calc ∑ m ∈ Finset.range (ctx.n24CarryData.r + 1), hitGap ctx.n24CarryData.a (k + m)
        ≤ ∑ _m ∈ Finset.range (ctx.n24CarryData.r + 1),
            (shellLadderDepth ctx + carryB ctx.shell.Q + 1) := Finset.sum_le_sum hgap
      _ = (ctx.n24CarryData.r + 1) * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hpin := class1Fibre_gapWindow_eq ctx hk
  have h64 : 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
      ≤ 64 * ((ctx.n24CarryData.r + 1)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) :=
    Nat.mul_le_mul_left 64 hsum
  omega

/-- **`r = 0` shells: the class-1 fibre is pinned to the SINGLE topmost window start**
`k = firstIndexAbove X + |supportShell d X| − 1`.  The numeric gate holds automatically:
`64·(L+B+1) < 129·L + 64` from the largeness gate `B + 25 ≤ L`. -/
theorem class1Fibre_top_of_r_eq_zero (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1) :
    k + 1 = ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
        + (supportShell ctx.shell.d ctx.shell.X).card := by
  have hB : carryB ctx.shell.Q + 25 ≤ shellLadderDepth ctx := ctx.shell_carryLarge
  have hnum : 64 * ((ctx.n24CarryData.r + 1)
        * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
      < 129 * shellLadderDepth ctx + 64 := by
    rw [hr]
    omega
  have hover := class1Fibre_window_overrun ctx hk hnum
  have hwin := class1Fibre_mem_window ctx hk
  omega

/-- **`r = 0` shells: at most ONE class-1 routed start** (`|fibre₁| ≤ 1`).  Note `r = ⌊κL⌋ = 0`
covers every shell with `L ≤ 15420`. -/
theorem class1Fibre_card_le_one_of_r_eq_zero (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card ≤ 1 := by
  refine Finset.card_le_one.mpr ?_
  intro x hx y hy
  have hxe := class1Fibre_top_of_r_eq_zero ctx hr hx
  have hye := class1Fibre_top_of_r_eq_zero ctx hr hy
  omega

/-- **The `r = 0` regime is the explicit shell range `L ≤ 15420`**: the manuscript order is
`r = ⌊κL⌋` with `κ = 17/2^18 = 17/262144`, and `17·15420 = 262140 < 262144`. -/
theorem n24_r_eq_zero_of_L_le (ctx : ActualFailureContext)
    (hL : shellLadderDepth ctx ≤ 15420) :
    ctx.n24CarryData.r = 0 := by
  rw [cnlMulti_n24_r_eq]
  unfold proofV4CarryOrder
  rw [Nat.floor_eq_zero]
  have hL' : ((Classical.choose ctx.shell.hXdyadic : ℕ) : ℝ) ≤ 15420 := by
    exact_mod_cast hL
  have hk : manuscriptKappa = 17 / 262144 := by
    unfold manuscriptKappa manuscriptCdrop manuscriptC1 manuscriptEps
    norm_num
  rw [hk]
  linarith

/-- **Every shell with `L ≤ 15420` has at most ONE class-1 routed start** (the explicit-numeral
form of the `r = 0` boundary pinning). -/
theorem class1Fibre_card_le_one_of_L_le (ctx : ActualFailureContext)
    (hL : shellLadderDepth ctx ≤ 15420) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card ≤ 1 :=
  class1Fibre_card_le_one_of_r_eq_zero ctx (n24_r_eq_zero_of_L_le ctx hL)

/-- **The boundary-band cardinality bound**: under the numeric gate
`64·(r+1)·(L+B+1) < 129·L + 64` the class-1 fibre has at most `r + 1` elements (it sits inside the
top `r + 1` positions of the shell window). -/
theorem class1Fibre_card_le_of_gapCeiling (ctx : ActualFailureContext)
    (hnum : 64 * ((ctx.n24CarryData.r + 1)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
        < 129 * shellLadderDepth ctx + 64) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ ctx.n24CarryData.r + 1 := by
  have hsub : routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
      ⊆ Finset.Ico
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card - (ctx.n24CarryData.r + 1))
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card) := by
    intro k hk
    have hover := class1Fibre_window_overrun ctx hk hnum
    have hwin := class1Fibre_mem_window ctx hk
    rw [Finset.mem_Ico]
    omega
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (Finset.Ico
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card - (ctx.n24CarryData.r + 1))
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card)).card :=
        Finset.card_le_card hsub
    _ ≤ ctx.n24CarryData.r + 1 := by
        rw [Nat.card_Ico]
        omega

/-- **The hit-position pin** (the telescoped form of the gap-window pin): every class-1 start has
its `(r+1)`-st following hit EXACTLY `(129L+64)/64` above its own hit position, in integers
`64·(a(k+r+1) − a(k)) = 129·L + 64`. -/
theorem class1Fibre_hitPosition_eq (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1) :
    64 * (ctx.n24CarryData.a (k + ctx.n24CarryData.r + 1) - ctx.n24CarryData.a k)
      = 129 * shellLadderDepth ctx + 64 := by
  have h := class1Fibre_gapWindow_eq ctx hk
  rwa [ctx.n24CarryData.carry.hits.gapWindow_hitGap_eq] at h

/-! ## Part 6d.  The SHARP membership characterization and the pinned arithmetic residual

Putting the three exact pins together: class-1 membership is EQUIVALENT to (start in the shell
window) ∧ (the ℕ gap-window pin) ∧ (the E.13 band-4 pin).  This is the honest irreducible
arithmetic form of the residual: `Class1FibreEmpty (v3Budget …)` holds IFF no window start
realizes the two pins simultaneously. -/

/-- **The sharp class-1 membership characterization**: `k ∈ fibre₁` iff `k` is a carry-window
start realizing BOTH exact pins — the ℕ gap-window identity `64·gapWindow = 129·L + 64` and the
E.13 band-4 identity `canonGap q K_k = 4`. -/
theorem mem_class1Fibre_iff (ctx : ActualFailureContext) (k : ℕ) :
    k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
      ↔ k ∈ ctx.n24CarryData.starts
        ∧ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
            = 129 * shellLadderDepth ctx + 64
        ∧ canonGap (class1SlopeDatum ctx).q
            (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 4 := by
  constructor
  · intro hk
    exact ⟨(mem_highExcessStarts.mp (Finset.mem_filter.mp hk).1).1,
      class1Fibre_gapWindow_eq ctx hk, class1Fibre_canonGap_eq ctx hk⟩
  · rintro ⟨hstart, hgw, hband⟩
    have hY := n24CarryData_Y_pos ctx
    have hwE : windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        = ctx.n24CarryData.Y := by
      have h64 : (64 : ℝ)
            * ((gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r : ℕ) : ℝ)
          = 129 * ((shellLadderDepth ctx : ℕ) : ℝ) + 64 := by exact_mod_cast hgw
      have hL : (28 : ℝ) ≤ ((shellLadderDepth ctx : ℕ) : ℝ) := by
        exact_mod_cast shellLadderDepth_ge ctx
      rw [cnlMulti_n24_T_eq, n24CarryData_Y_eq_div]
      unfold windowExcess positivePart
      rw [max_eq_left (by linarith)]
      linarith
    have htower : towerClsOfShell ctx k = TowerExitClass.cnlTail := by
      rw [towerClsOfShell_eq_band, hband]
      rfl
    have hret0 : returnCls ctx k = 0 := (returnCls_eq_zero_iff ctx k).mpr (le_of_eq hwE)
    have hrun : runClsOfShell ctx k ≠ 1 := by
      unfold runClsOfShell
      split_ifs with h0 h2
      · decide
      · exfalso
        rw [hwE] at h2
        linarith
      · decide
    have hroute : genuineChargeRoute ctx k = 1 :=
      (genuineChargeRoute_eq_one_iff ctx k).mpr
        ⟨htower, hrun, by rw [hret0]; decide, by rw [hret0]; decide⟩
    exact Finset.mem_filter.mpr
      ⟨mem_highExcessStarts.mpr ⟨hstart, le_of_eq hwE.symm⟩, hroute⟩

/-- **The class-1 fibre IS the doubly-pinned window filter** (the irreducible arithmetic form). -/
theorem class1Fibre_eq_pinnedFilter (ctx : ActualFailureContext) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
      = ctx.n24CarryData.starts.filter (fun k =>
          64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
              = 129 * shellLadderDepth ctx + 64
            ∧ canonGap (class1SlopeDatum ctx).q
                (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 4) := by
  ext k
  rw [Finset.mem_filter, mem_class1Fibre_iff]

/-- **The residual in its sharpest necessary-and-sufficient arithmetic form**: the v3 clean-CNL
atom `Class1FibreEmpty (v3Budget …)` holds IFF no carry-window start simultaneously realizes the
gap-window pin and the band-4 pin. -/
theorem v3_class1FibreEmpty_iff_pinned
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runChain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx) :
    Class1FibreEmpty (v3Budget towerCount runChain returnCharge)
      ↔ ∀ ctx : ActualFailureContext, ∀ k ∈ ctx.n24CarryData.starts,
          ¬(64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
                = 129 * shellLadderDepth ctx + 64
            ∧ canonGap (class1SlopeDatum ctx).q
                (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 4) := by
  constructor
  · intro hemp ctx k hkstart hpins
    have h := hemp ctx
    rw [v3Budget_route] at h
    have hmem : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 :=
      (mem_class1Fibre_iff ctx k).mpr ⟨hkstart, hpins.1, hpins.2⟩
    rw [h] at hmem
    exact Finset.notMem_empty k hmem
  · intro h ctx
    rw [v3Budget_route, Finset.eq_empty_iff_forall_notMem]
    intro k hk
    rw [mem_class1Fibre_iff] at hk
    exact h ctx k hk.1 ⟨hk.2.1, hk.2.2⟩

/-- **The pinned arithmetic SUFFICIENT condition, with all proved obstructions folded in**: to
close the atom it suffices to refute the simultaneous pins on the shells that survive every proved
closure — `64 ∣ L` (integrality) AND `q ≥ 9` (band) — for window starts only. -/
theorem class1FibreEmpty_of_pinned_arithmetic
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runChain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (h : ∀ ctx : ActualFailureContext, ∀ k ∈ ctx.n24CarryData.starts,
      64 ∣ shellLadderDepth ctx →
      9 ≤ (class1SlopeDatum ctx).q →
      64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
          = 129 * shellLadderDepth ctx + 64 →
      canonGap (class1SlopeDatum ctx).q
          (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) ≠ 4) :
    Class1FibreEmpty (v3Budget towerCount runChain returnCharge) := by
  rw [v3_class1FibreEmpty_iff_pinned]
  intro ctx k hkstart hpins
  obtain ⟨hgw, hband⟩ := hpins
  have hdvd : 64 ∣ shellLadderDepth ctx := by omega
  have hq9 : 9 ≤ (class1SlopeDatum ctx).q := by
    have horb := slopeOrbit_mem (class1SlopeDatum ctx).hq_odd (class1SlopeDatum ctx).hK₀_pos
      (class1SlopeDatum ctx).hK₀_lt k
    obtain ⟨h8, h16⟩ := (canonGap_eq_four_iff horb.1).mp hband
    obtain ⟨m, hm⟩ := (class1SlopeDatum ctx).hq_odd
    have h1 := horb.1
    omega
  exact h ctx k hkstart hdvd hq9 hgw hband

/-! ## Part 7.  The P9 endpoint from the named residual -/

/-- **Erdős #260 (P9/V3 endpoint) with the clean-CNL slot reduced to the named residual
`Class1FibreEmpty`.**  All four CNL fields (`g`, `hmem`, `hinj`, `hcharge`) are supplied by the
constructive bridge; the other atoms are carried as hypotheses exactly as in
`P9V3RunMatchedCNLResidual`. -/
theorem erdos260_p9V3_of_class1FibreEmpty
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runResidual : ∀ ctx : ActualFailureContext, RunClass5LeafResidual ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (chernoff : Class0ChernoffInjection
      (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge))
    (hempty : Class1FibreEmpty
      (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge))
    (densePackCount : ∀ ctx : ActualFailureContext,
      (genuineDensePackStarts ctx).card
        ≤ (densePackMarkers
          (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge) ctx).card)
    (windowReach : ActualFailureContext → ℕ)
    (hReach : ∀ ctx : ActualFailureContext,
      windowReach ctx + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hContain : ∀ ctx : ActualFailureContext, ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + windowReach ctx)
    (hScale : ∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ) - ctx.n24CarryData.T ≤ 1) :
    Erdos260Statement :=
  P9V3RunMatchedCNLResidual.toStatement
    { towerCount := towerCount
      runResidual := runResidual
      returnCharge := returnCharge
      chernoff := chernoff
      cnl := cnlMatchedChargeDataOfClass1FibreEmpty hempty
      densePackCount := densePackCount
      windowReach := windowReach
      hReach := hReach
      hContain := hContain
      hScale := hScale }

/-- **The P9/V3 endpoint from the pinned arithmetic residual** — the clean-CNL slot carried in its
sharpest arithmetic form: refute the simultaneous gap-window/band-4 pins on `64 ∣ L`, `q ≥ 9`
window starts. -/
theorem erdos260_p9V3_of_pinned_arithmetic
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runResidual : ∀ ctx : ActualFailureContext, RunClass5LeafResidual ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (chernoff : Class0ChernoffInjection
      (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge))
    (hpin : ∀ ctx : ActualFailureContext, ∀ k ∈ ctx.n24CarryData.starts,
      64 ∣ shellLadderDepth ctx →
      9 ≤ (class1SlopeDatum ctx).q →
      64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
          = 129 * shellLadderDepth ctx + 64 →
      canonGap (class1SlopeDatum ctx).q
          (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) ≠ 4)
    (densePackCount : ∀ ctx : ActualFailureContext,
      (genuineDensePackStarts ctx).card
        ≤ (densePackMarkers
          (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge) ctx).card)
    (windowReach : ActualFailureContext → ℕ)
    (hReach : ∀ ctx : ActualFailureContext,
      windowReach ctx + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hContain : ∀ ctx : ActualFailureContext, ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + windowReach ctx)
    (hScale : ∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ) - ctx.n24CarryData.T ≤ 1) :
    Erdos260Statement :=
  erdos260_p9V3_of_class1FibreEmpty towerCount runResidual returnCharge chernoff
    (class1FibreEmpty_of_pinned_arithmetic towerCount
      (p9V3RunChainOfResidual runResidual) returnCharge hpin)
    densePackCount windowReach hReach hContain hScale

/-! ## Part 8.  Machine-readable status (brutally honest) -/

/-- Honest machine-readable status of the multiplicity-aware CNL closure attempt. -/
def cnlMultiChargeUnconditionalStatus : List String :=
  [ "CLOSED (parameter pins, rfl-level): the canonical N.24 carry datum has r = ⌊κL⌋, " ++
      "T = 2L + 1, Y = εL = L/64 (cnlMulti_n24_r_eq / cnlMulti_n24_T_eq / n24CarryData_Y_eq); " ++
      "the large-X gate gives Y ≥ 7/16 > 0 (n24CarryData_Y_ge).",
    "CLOSED (excess pinning): on the genuine first-obstruction route, class 1 is reached only " ++
      "through the terminal catch-all branch with returnCls = 0, so EVERY class-1 routed start " ++
      "has windowExcess EXACTLY = Y (windowExcess_eq_Y_of_mem_class1Fibre); the routed class-1 " ++
      "mass is exactly card(fibre₁)·Y (routedClassMass_one_eq_card_mul_Y).  The v3 class-1 band " ++
      "is the razor-thin level set {windowExcess = Y}.",
    "CLOSED (scale gap): the faithful clean-CNL term obeys termCnl ≤ 14·(1/64)·1 = 7/32 < 7/16 " ++
      "≤ Y (termCnl_faithful_le_7_32, termCnl_faithful_lt_Y) — |family| ≤ 14, shellFactor = " ++
      "2^{-c₀ηX} ≤ 2^{-6}, Kraft tiling X·|I_j| ≤ 1.  Every per-codeword cap cnlShellKraftCap " ++
      "is < Y, so no multiplicity-aware (or injective) reindexing can charge even ONE pinned " ++
      "class-1 excess.",
    "OBSTRUCTION PROVED (the sharp characterization): for EVERY budget, the class-1 ledger " ++
      "field routedClassMassOf … 1 ≤ termCnl(faithfulCapacityPhases …) holds at ctx IFF the " ++
      "class-1 routed fibre is empty (class1Ledger_iff_fibre_empty); hence " ++
      "Nonempty(CNLMultiChargeDataForBudget budget) ⟺ Nonempty(CNLMatchedChargeDataForBudget " ++
      "budget) ⟺ Class1FibreEmpty budget (cnlMultiChargeData_iff_class1FibreEmpty, " ++
      "cnlMatchedChargeData_iff_multi).  The O_Q(1)-to-one relaxation gains NOTHING for the " ++
      "faithful termCnl target.  This sharpens the one-step obstruction |fibre₁| ≤ 14 to " ++
      "|fibre₁| = 0 (cnlMultiChargeData_forces_fibre_card_zero); a SINGLE context with ONE " ++
      "class-1 start refutes all three CNL surfaces (no_cnlMultiChargeData_of_fibre_nonempty).",
    "CLOSED (g and hmem, constructive, non-vacuous): the reindexing map g = cnlCanonicalCodeword " ++
      "(the genuine cyclic cluster codeword) lands in the genuinely nonempty surviving family " ++
      "for EVERY start with NO hypotheses (cnlMultiChargeDataOfClass1FibreEmpty); the charged " ++
      "bound hcharged is discharged from the named residual.",
    "REDUCED (the minimal residual, necessary AND sufficient): Class1FibreEmpty (v3Budget …) : " ++
      "∀ ctx, routedFibre ctx.n24CarryData (budget ctx).route 1 = ∅.  By the iff, NO weaker " ++
      "residual can inhabit the datum.  Lean type: ∀ ctx : ActualFailureContext, " ++
      "routedFibre ctx.n24CarryData (budget ctx).route 1 = ∅.",
    "PARTIALLY CLOSED (integrality): every class-1 start has 64·gapWindow = 129·L + 64 exactly " ++
      "(class1Fibre_gapWindow_eq, a ℕ identity; telescoped hit-position form " ++
      "class1Fibre_hitPosition_eq: 64·(a(k+r+1) − a(k)) = 129L + 64), so the fibre is PROVABLY " ++
      "EMPTY whenever ¬(64 ∣ L) (class1Fibre_empty_of_not_dvd64 / " ++
      "v3_class1Fibre_empty_of_not_dvd64); the residual shrinks to the 64 ∣ L shell subfamily " ++
      "(class1FibreEmpty_of_dvd64_case).",
    "PARTIALLY CLOSED (the E.13 band pin, NEW): class 1 fires only on towerClsOfShell = cnlTail " ++
      "= band index 4 of the recurrent slope orbit (towerClsOfShell_eq_band, " ++
      "towerExitClassOfGap_eq_cnlTail_iff), so every class-1 start has canonGap q K_k = 4 " ++
      "(class1Fibre_canonGap_eq), equivalently 8·K_k ≤ q < 16·K_k (canonGap_eq_four_iff, " ++
      "class1Fibre_orbit_band), and the successor numerator is pinned to 16·K_k − q " ++
      "(class1Fibre_orbit_step).  Hence q ≥ 9 on any shell with a class-1 start " ++
      "(modulus_ge_nine_of_class1Fibre_nonempty): the fibre is PROVABLY EMPTY whenever the " ++
      "closed AP-subfibre modulus is < 9 (class1Fibre_empty_of_modulus_lt_nine / " ++
      "v3_class1Fibre_empty_of_modulus_lt_nine).",
    "PARTIALLY CLOSED (the shell-window gap ceiling, NEW): starts = Ico (firstIndexAbove X) " ++
      "(firstIndexAbove X + |supportShell|) definitionally (cnlMulti_starts_eq_window) and the " ++
      "PROVED dyadic ceiling hitGap ≤ L + B + 1 holds on the window (n24_hitGap_le_window), " ++
      "while the pin demands gapWindow ≈ 2.016·L; so when 64(r+1)(L+B+1) < 129L + 64 every " ++
      "class-1 start overruns the window top (class1Fibre_window_overrun) and |fibre₁| ≤ r + 1 " ++
      "(class1Fibre_card_le_of_gapCeiling).  On r = ⌊κL⌋ = 0 shells the gate holds " ++
      "automatically from B + 25 ≤ L: the fibre is pinned inside the SINGLE topmost window " ++
      "start (class1Fibre_top_of_r_eq_zero, class1Fibre_card_le_one_of_r_eq_zero); the r = 0 " ++
      "regime is the explicit numeral range L ≤ 15420, κ = 17/2^18 (n24_r_eq_zero_of_L_le, " ++
      "class1Fibre_card_le_one_of_L_le).",
    "OBSTRUCTION PROVED (the sharp membership characterization, NEW): k ∈ fibre₁ IFF k is a " ++
      "window start realizing BOTH exact pins — 64·gapWindow = 129L + 64 AND canonGap = 4 " ++
      "(mem_class1Fibre_iff, class1Fibre_eq_pinnedFilter).  Consequently Class1FibreEmpty " ++
      "(v3Budget …) ⟺ no carry-window start realizes the two pins simultaneously " ++
      "(v3_class1FibreEmpty_iff_pinned) — the residual's sharpest arithmetic form, necessary " ++
      "AND sufficient.",
    "BRIDGE PROVED: erdos260_p9V3_of_class1FibreEmpty — the ctx-pinned P9 endpoint with the " ++
      "clean-CNL slot carried as the single named Prop Class1FibreEmpty (other atoms as " ++
      "hypotheses); and erdos260_p9V3_of_pinned_arithmetic — the same endpoint from the pinned " ++
      "arithmetic residual (class1FibreEmpty_of_pinned_arithmetic), which only demands refuting " ++
      "the simultaneous pins on 64 ∣ L, q ≥ 9 window starts.",
    "NOT CLOSED (honest): the remaining subfamily is shells with 64 ∣ L, AP-subfibre modulus " ++
      "q ≥ 9, and (when 64(r+1)(L+B+1) < 129L+64, e.g. ALL r = 0 shells) only the top r+1 " ++
      "boundary starts of the carry window.  There the hit-gap pin (a property of the actual " ++
      "hit sequence a) and the band-4 pin (a property of the recurrent slope orbit) remain " ++
      "mutually unconstrained in the model: no formalized bridge ties hitGap a to canonGap " ++
      "along the orbit for the ACTUAL ctx (integerCarry_realizes_boundedSlopeStep is " ++
      "conditional on canonical-gap zero-runs).  We do NOT claim unconditional closure of the " ++
      "atom.",
    "ROOT CAUSE (for the genuine deep close): the faithful leaf calibrates shellFactor = " ++
      "2^{-c₀ηX} and |I_j| = 2^{-M} to FIT the budget cStar·ξ·X/6, making every Kraft cap " ++
      "below the manuscript's per-start charge scale Y = εL.  A genuine length-M/O_Q(1)-to-one " ++
      "close needs a recalibrated CNL leaf whose per-codeword caps carry the windowExcess scale " ++
      "(the manuscript H.1/H.2 Y-dependent calibration), i.e. a different faithfulCnlData — a " ++
      "cross-atom interface change, out of scope for new-module-only work." ]

theorem cnlMultiChargeUnconditionalStatus_nonempty :
    cnlMultiChargeUnconditionalStatus ≠ [] := by
  simp [cnlMultiChargeUnconditionalStatus]

/-! ## Part 9.  Axiom-cleanliness audit -/

#print axioms cnlMulti_n24_r_eq
#print axioms cnlMulti_n24_T_eq
#print axioms n24CarryData_Y_eq
#print axioms n24CarryData_Y_ge
#print axioms windowExcess_eq_Y_of_mem_class1Fibre
#print axioms routedClassMass_one_eq_card_mul_Y
#print axioms termCnl_faithful_le_7_32
#print axioms termCnl_faithful_lt_Y
#print axioms class1Ledger_iff_fibre_empty
#print axioms hCnlField_iff_class1FibreEmpty
#print axioms cnlMultiChargeData_forces_class1FibreEmpty
#print axioms cnlMultiChargeData_forces_fibre_card_zero
#print axioms no_cnlMultiChargeData_of_fibre_nonempty
#print axioms cnlMultiChargeDataOfClass1FibreEmpty
#print axioms cnlMatchedChargeDataOfClass1FibreEmpty
#print axioms cnlMultiChargeData_iff_class1FibreEmpty
#print axioms cnlMatchedChargeData_iff_class1FibreEmpty
#print axioms cnlMatchedChargeData_iff_multi
#print axioms class1CNLInjection_forces_class1FibreEmpty
#print axioms class1Fibre_gapWindow_eq
#print axioms class1Fibre_empty_of_not_dvd64
#print axioms v3_class1Fibre_empty_of_not_dvd64
#print axioms class1FibreEmpty_of_dvd64_case
#print axioms class1SlopeDatum
#print axioms towerClsOfShell_eq_band
#print axioms towerExitClassOfGap_eq_cnlTail_iff
#print axioms canonGap_eq_four_iff
#print axioms class1Fibre_canonGap_eq
#print axioms class1Fibre_orbit_band
#print axioms class1Fibre_orbit_step
#print axioms modulus_ge_nine_of_class1Fibre_nonempty
#print axioms class1Fibre_empty_of_modulus_lt_nine
#print axioms v3_class1Fibre_empty_of_modulus_lt_nine
#print axioms cnlMulti_starts_eq_window
#print axioms cnlMulti_r_add_one_le_width
#print axioms n24_hitGap_le_window
#print axioms class1Fibre_mem_window
#print axioms class1Fibre_window_overrun
#print axioms class1Fibre_top_of_r_eq_zero
#print axioms class1Fibre_card_le_one_of_r_eq_zero
#print axioms n24_r_eq_zero_of_L_le
#print axioms class1Fibre_card_le_one_of_L_le
#print axioms class1Fibre_card_le_of_gapCeiling
#print axioms class1Fibre_hitPosition_eq
#print axioms mem_class1Fibre_iff
#print axioms class1Fibre_eq_pinnedFilter
#print axioms v3_class1FibreEmpty_iff_pinned
#print axioms class1FibreEmpty_of_pinned_arithmetic
#print axioms erdos260_p9V3_of_class1FibreEmpty
#print axioms erdos260_p9V3_of_pinned_arithmetic

end

end Erdos260
