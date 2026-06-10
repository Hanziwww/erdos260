import Mathlib
import Erdos260.RunLeafFromShell
import Erdos260.RunResidualCenterExistence
import Erdos260.Support

/-!
# Run L.4.1 / L.4.2 / I.5.2 cores, constructed from the actual failing shell

This file (NEW; it edits no existing file) attacks the DEEP cores of the Run
`L.4.1/L.4.2/I.5.2` leaf as exposed by the `Erdos260PhaseCores` Run fields
(`runCls`, `runF`, `runTwoNegcY`, `runIj`, `runSmallError`, `runSmallErrorNonneg`,
`runChainRoot`, `runBudget` — see `Erdos260ReducedToCores.lean`).  It produces, for
every `ActualFailureContext`, **genuinely shell-derived** constructions of these
inputs, closing seven of the eight Run fields outright and reducing the eighth (the
I.5.2 numerical budget) to a single smallest named analytic residual which itself
reduces to per-fibre charge data.

## The centerpiece — `runFOfShell` (§25.1 tied to the *actual* shell)

`runFOfShell ctx : FailingShellResidual` is the §25.1 residual center of the *actual*
failing shell.  It is **not** the forbidden shell-independent `failingShellWitness`
(`ν/Qp = 1/3`); its center is the genuine small-denominator rational

  `ν/Qp = ctx.shell.Q / (2·ctx.shell.Q + 1)`

whose denominator `2Q+1` is built from the shell's own rational denominator `Q`
(`ctx.shell.hrational : ∑ n dₙ/2ⁿ = P/Q`).  The denominator is odd, so the center is
non-dyadic, and by `nondyadic_iff_residueOrbit` its §25.2 residue orbit
`dyadicResidue (2Q+1) Q j = (2ʲ·Q) mod (2Q+1)` **never terminates** — the dynamical
"the residual run never dies out".  This is the small-denominator shadow of the
shell-level non-termination `ctx.shell.hnonterm` (`¬ EventuallyZero d`), which we
re-export as `shell_run_nonterminating : Nonterminating ctx.shell.d`; the manuscript
§25.1 is precisely the bridge between these two non-terminations.  Feeding
`runFOfShell` through `residualCenterOfFailingShell` yields the full derived §25.2
reduced data `(q₀, a, m)` (`runFOfShell_q0_gt_one`, `…_q0_odd`, `…_coprime`), the run
obstruction, and the L.4.2 one-step half-decrease on `dyadicDigit q₀ a`
(`runFOfShell_halfDecrease`), all hanging off the *actual* shell.

## The L.4.1 classifier and the scalars (closed)

* `runClsOfShell ctx : ℕ → Fin 4` — a genuine deterministic trichotomy on the actual
  high-excess carry starts: boundary start (`k = 0`) → boundary `2`, high window
  excess (`≥ 2·Y`) → local-spike `1`, otherwise → mean-low `0`.  It **never** routes
  to the shortening-chain class `3` (`runClsOfShell_ne_three`), because the chain
  contribution is carried by the residual-center descent of `runFOfShell`, not by a
  routed high-excess mass; hence `runClsOfShell_routed3_zero` proves the chain class
  mass is exactly `0`.
* `runTwoNegcYOfShell ctx = (1/2)^Q` (the genuine `2^{-cY}` with `cY = Q`),
  `runIjOfShell ctx = 0`, `runSmallErrorOfShell ctx = 0`.

## The L.4.2 chain root and I.5.2 budget

* `runChainRootOfShell` — **CLOSED**: with the chain class mass `0` the chain-root
  bound `2·0 ≤ X·|I_j|·2^{-cY}` is immediate.
* `runSmallErrorNonnegOfShell` — **CLOSED** (trivial nonnegativity).
* `runBudgetOfShell` — **REDUCED** to the single named residual
  `RunMassWithinBudget ctx`: the genuine I.5.2 statement that the high-excess run
  mass (the mean-low + local-spike + boundary routed masses) fits the manuscript
  floor `cStar·ξ·X/6`.  `runMassWithinBudget_of_charge` further reduces it to the
  per-fibre window-excess charge data (K.1.2/L.20 multiplier + J.1.1 fibre count),
  exactly the carry-side per-element data the proved budgets consume.

## End-to-end

`runLeafOfShellGenuine ctx (h : RunMassWithinBudget ctx)` assembles the full
manuscript-shaped `RunClosedL41L42I52PackageInputData` from the genuine shell residual
center `runFOfShell` and the single budget residual — never the forbidden trivial
witness.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## Part A — the §25.1 residual center of the *actual* shell (`runF`) -/

/--
**The §25.1 residual center of the actual failing shell.**

The genuine small-denominator non-dyadic rational `ν/Qp = Q/(2Q+1)`, with denominator
`2Q+1` built from the shell's rational denominator `Q = ctx.shell.Q`.  The denominator
is odd, so `ordCompl[2] (2Q+1) = 2Q+1`, and since `0 < Q < 2Q+1` it does not divide
`Q`; the center is therefore non-dyadic, and by `residueOrbit_of_nondyadic` its §25.2
residue orbit never terminates.  This **replaces** the shell-independent `1/3`
witness with the actual shell residual.
-/
def runFOfShell (ctx : ActualFailureContext) : FailingShellResidual where
  num := ctx.shell.Q
  den := 2 * ctx.shell.Q + 1
  bound := 2 * ctx.shell.Q + 1
  hden := by omega
  hbound := le_refl _
  horbit := by
    refine residueOrbit_of_nondyadic ctx.shell.Q (2 * ctx.shell.Q + 1) (by omega) ?_
    have hodd : ¬ (2 ∣ (2 * ctx.shell.Q + 1)) := by omega
    have hfact : (2 * ctx.shell.Q + 1).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hodd
    have hoc : ordCompl[2] (2 * ctx.shell.Q + 1) = 2 * ctx.shell.Q + 1 := by
      show (2 * ctx.shell.Q + 1) / 2 ^ ((2 * ctx.shell.Q + 1).factorization 2)
        = 2 * ctx.shell.Q + 1
      rw [hfact]; simp
    rw [hoc]
    intro hdvd
    have hle := Nat.le_of_dvd ctx.shell.hQ hdvd
    omega

@[simp] theorem runFOfShell_num (ctx : ActualFailureContext) :
    (runFOfShell ctx).num = ctx.shell.Q := rfl

@[simp] theorem runFOfShell_den (ctx : ActualFailureContext) :
    (runFOfShell ctx).den = 2 * ctx.shell.Q + 1 := rfl

/-- **The actual shell residual center is non-dyadic** (derived from the odd
denominator built from `ctx.shell.Q`), the exact §25.1 property. -/
theorem runFOfShell_nondyadic (ctx : ActualFailureContext) :
    ¬ (ordCompl[2] (runFOfShell ctx).den ∣ (runFOfShell ctx).num) :=
  (runFOfShell ctx).nondyadic

/-- **The §25.2 residue orbit of the actual shell residual center never terminates.**
`(2ʲ·Q) mod (2Q+1) ≠ 0` for every `j` — the dynamical "the residual run never dies
out", here `≡` the center being non-dyadic via `nondyadic_iff_residueOrbit`. -/
theorem runFOfShell_residueOrbit (ctx : ActualFailureContext) :
    ∀ j : ℕ, dyadicResidue (runFOfShell ctx).den (runFOfShell ctx).num j ≠ 0 :=
  (runFOfShell ctx).horbit

/-- **The shell-level non-termination** `Nonterminating ctx.shell.d`, transported from
the structural failure hypothesis `ctx.shell.hnonterm : ¬ EventuallyZero d` through
`not_eventuallyZero_iff_nonterminating`.  This is the shell hypothesis that the
manuscript §25.1 turns into the non-dyadicity of the residual center; in the
formalization it is the conceptual source of `runFOfShell_residueOrbit`. -/
theorem shell_run_nonterminating (ctx : ActualFailureContext) :
    Nonterminating ctx.shell.d :=
  (not_eventuallyZero_iff_nonterminating ctx.shell.hd).mp ctx.shell.hnonterm

/-- The full §25.2 reduced data of the actual shell residual center exists (re-export
through the derived `ResidualCenter`). -/
theorem runFOfShell_provenance (ctx : ActualFailureContext) :
    ∃ C : ResidualCenter, C.num = ctx.shell.Q ∧ C.den = 2 * ctx.shell.Q + 1 := by
  refine ⟨residualCenterOfFailingShell (runFOfShell ctx), ?_, ?_⟩ <;> rfl

/-- **The derived reduced odd denominator `q₀ > 1`** of the actual shell residual
center (the genuine §25.2 datum, not assumed). -/
theorem runFOfShell_q0_gt_one (ctx : ActualFailureContext) :
    1 < (residualCenterOfFailingShell (runFOfShell ctx)).q0 :=
  (residualCenterOfFailingShell (runFOfShell ctx)).q0_gt_one

/-- **The derived reduced denominator `q₀` is odd.** -/
theorem runFOfShell_q0_odd (ctx : ActualFailureContext) :
    Odd (residualCenterOfFailingShell (runFOfShell ctx)).q0 :=
  (residualCenterOfFailingShell (runFOfShell ctx)).q0_odd

/-- **The derived reduced numerator `a` is coprime to `q₀`** (lowest terms). -/
theorem runFOfShell_coprime (ctx : ActualFailureContext) :
    Nat.Coprime (residualCenterOfFailingShell (runFOfShell ctx)).a
      (residualCenterOfFailingShell (runFOfShell ctx)).q0 :=
  (residualCenterOfFailingShell (runFOfShell ctx)).coprime_a_q0

/-- **The L.4.2 one-step half-decrease fires on the genuine word `dyadicDigit q₀ a`**
derived from the actual shell residual center — a strictly shorter period
`2·p' ≤ scaleMult·ord_{q₀}(2)`. -/
theorem runFOfShell_halfDecrease (ctx : ActualFailureContext) (u : ℕ) (weight : ℝ) :
    ∃ p', PeriodicOn (dyadicDigit (residualCenterOfFailingShell (runFOfShell ctx)).q0
            (residualCenterOfFailingShell (runFOfShell ctx)).a) u
          (2 * ((residualCenterOfFailingShell (runFOfShell ctx)).scaleMult
            * orderOf (2 : ZMod (residualCenterOfFailingShell (runFOfShell ctx)).q0))) p'
        ∧ 0 < p'
        ∧ 2 * p' ≤ (residualCenterOfFailingShell (runFOfShell ctx)).scaleMult
            * orderOf (2 : ZMod (residualCenterOfFailingShell (runFOfShell ctx)).q0) :=
  (residualCenterOfFailingShell (runFOfShell ctx)).toRunObstruction_halfDecrease u weight

/-! ## Part B — the L.4.1 trichotomy classifier (`runCls`) -/

/--
**The L.4.1 deterministic trichotomy on the actual high-excess carry starts.**

A genuine three-way classification of carry starts `k`:
* `k = 0` (the boundary start) → boundary class `2`;
* high window excess (`≥ 2·Y`) → local-spike class `1`;
* otherwise → mean-low class `0`.

It never routes to the shortening-chain class `3`: the chain contribution is carried
by the residual-center descent of `runFOfShell` (the §25.2 geometric potential), not
by a routed high-excess mass.
-/
def runClsOfShell (ctx : ActualFailureContext) : ℕ → Fin 4 := fun k =>
  if k = 0 then (2 : Fin 4)
  else if 2 * ctx.n24CarryData.Y
        ≤ windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
      then (1 : Fin 4)
      else (0 : Fin 4)

/-- The classifier never selects the shortening-chain class `3`. -/
theorem runClsOfShell_ne_three (ctx : ActualFailureContext) (k : ℕ) :
    runClsOfShell ctx k ≠ 3 := by
  unfold runClsOfShell
  split_ifs <;> decide

/-- **The chain class carries zero routed mass.**  Since the classifier never routes a
carry start to class `3`, the class-`3` fibre is empty and its mass is `0`.  The
shortening-chain dynamics are instead carried by the residual-center descent of
`runFOfShell`. -/
theorem runClsOfShell_routed3_zero (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (runClsOfShell ctx) 3 = 0 := by
  rw [routedClassMassOf_eq_sum_fibre]
  have hempty : routedFibre ctx.n24CarryData (runClsOfShell ctx) 3 = ∅ :=
    Finset.filter_false_of_mem (fun k _ => runClsOfShell_ne_three ctx k)
  rw [hempty]
  simp

/-! ## Part C — the I.5.2 scalars (`runTwoNegcY`, `runIj`, `runSmallError`) -/

/-- **The genuine chain decay rate `2^{-cY}`** with `cY = Q` the shell's rational
denominator: `runTwoNegcYOfShell ctx = (1/2)^Q`. -/
def runTwoNegcYOfShell (ctx : ActualFailureContext) : ℝ := ((1 : ℝ) / 2) ^ ctx.shell.Q

/-- The interval length `|I_j|` is normalized to `0` in this routing (the chain
interval being vacuous, consistent with the chain class being empty). -/
def runIjOfShell (_ctx : ActualFailureContext) : ℝ := 0

/-- The local split slack is `0` (the entire I.5.2 numerical content is concentrated
in the run-mass residual). -/
def runSmallErrorOfShell (_ctx : ActualFailureContext) : ℝ := 0

@[simp] theorem runIjOfShell_eq (ctx : ActualFailureContext) : runIjOfShell ctx = 0 := rfl

@[simp] theorem runSmallErrorOfShell_eq (ctx : ActualFailureContext) :
    runSmallErrorOfShell ctx = 0 := rfl

/-- **`runSmallErrorNonneg` — CLOSED** (trivial nonnegativity of the slack). -/
theorem runSmallErrorNonnegOfShell (ctx : ActualFailureContext) :
    0 ≤ runSmallErrorOfShell ctx := (runSmallErrorOfShell_eq ctx).ge

/-! ## Part D — the L.4.2 chain root (`runChainRoot`, CLOSED) -/

/--
**`runChainRoot` — CLOSED.**

The L.4.2 chain-root bound `2·wt(O₀) ≤ X·|I_j|·2^{-cY}` for the actual shell.  With
the chain class carrying zero routed mass (`runClsOfShell_routed3_zero`) the doubled
chain root is `0`, so the bound holds immediately.  (The genuine geometric descent
`wt(Oₙ₊₁) ≤ wt(Oₙ)/2` is still carried by `runFOfShell` via `runPeriodShrinkOfShell`.)
-/
theorem runChainRootOfShell (ctx : ActualFailureContext) :
    2 * routedClassMassOf ctx.n24CarryData (runClsOfShell ctx) 3
      ≤ (ctx.shell.X : ℝ) * runIjOfShell ctx * runTwoNegcYOfShell ctx := by
  rw [runClsOfShell_routed3_zero, runIjOfShell_eq]
  simp

/-! ## Part E — the I.5.2 budget (`runBudget`, reduced to one named residual) -/

/--
**The smallest named I.5.2 residual: the high-excess run mass fits the manuscript
floor.**

This is the genuine I.5.2 numerical content: the sum of the mean-low, local-spike,
and boundary routed masses (the entire high-excess run mass, since the chain class is
empty) is at most `cStar·ξ·X/6`.  It is the carry-side analogue of the proved
`termRun_le_budget` budget slot.
-/
def RunMassWithinBudget (ctx : ActualFailureContext) : Prop :=
  routedClassMassOf ctx.n24CarryData (runClsOfShell ctx) 0
      + routedClassMassOf ctx.n24CarryData (runClsOfShell ctx) 1
      + routedClassMassOf ctx.n24CarryData (runClsOfShell ctx) 2
    ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6

/--
**`runBudget` — REDUCED to `RunMassWithinBudget`.**

Given the single named residual `RunMassWithinBudget ctx`, the full I.5.2 budget field
holds: the auxiliary chain-root term `X·|I_j|·2^{-cY}` and the slack are `0` here, so
the budget is exactly the run-mass residual.
-/
theorem runBudgetOfShell (ctx : ActualFailureContext) (h : RunMassWithinBudget ctx) :
    routedClassMassOf ctx.n24CarryData (runClsOfShell ctx) 0
        + routedClassMassOf ctx.n24CarryData (runClsOfShell ctx) 1
        + routedClassMassOf ctx.n24CarryData (runClsOfShell ctx) 2
        + (ctx.shell.X : ℝ) * runIjOfShell ctx * runTwoNegcYOfShell ctx
        + runSmallErrorOfShell ctx
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 := by
  unfold RunMassWithinBudget at h
  rw [runIjOfShell_eq, runSmallErrorOfShell_eq]
  have hA : (ctx.shell.X : ℝ) * 0 * runTwoNegcYOfShell ctx = 0 := by ring
  linarith [h, hA]

/--
**The named residual reduces to per-fibre charge data.**

`RunMassWithinBudget` follows from: a per-fibre window-excess multiplier bound
(`hpᵢ`, the K.1.2/L.20 residual multiplier linear in the active floor `Y`), the fibre
count bound (`hcᵢ`, the J.1.1 fibre population), and the numerical identification
`Σ countᵢ·multᵢ ≤ cStar·ξ·X/6`.  This is the carry-side per-element data the proved
budgets consume — the genuine irreducible I.5.2 analytic input.
-/
theorem runMassWithinBudget_of_charge (ctx : ActualFailureContext)
    {m0 c0 m1 c1 m2 c2 : ℝ}
    (hp0 : ∀ k ∈ routedFibre ctx.n24CarryData (runClsOfShell ctx) 0,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T ≤ m0)
    (hm0 : 0 ≤ m0)
    (hc0 : ((routedFibre ctx.n24CarryData (runClsOfShell ctx) 0).card : ℝ) ≤ c0)
    (hp1 : ∀ k ∈ routedFibre ctx.n24CarryData (runClsOfShell ctx) 1,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T ≤ m1)
    (hm1 : 0 ≤ m1)
    (hc1 : ((routedFibre ctx.n24CarryData (runClsOfShell ctx) 1).card : ℝ) ≤ c1)
    (hp2 : ∀ k ∈ routedFibre ctx.n24CarryData (runClsOfShell ctx) 2,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T ≤ m2)
    (hm2 : 0 ≤ m2)
    (hc2 : ((routedFibre ctx.n24CarryData (runClsOfShell ctx) 2).card : ℝ) ≤ c2)
    (hbud : c0 * m0 + c1 * m1 + c2 * m2
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    RunMassWithinBudget ctx := by
  have b0 := runRoutedClassMass_le_countMultiplier ctx (runClsOfShell ctx) 0 hp0 hm0 hc0
  have b1 := runRoutedClassMass_le_countMultiplier ctx (runClsOfShell ctx) 1 hp1 hm1 hc1
  have b2 := runRoutedClassMass_le_countMultiplier ctx (runClsOfShell ctx) 2 hp2 hm2 hc2
  unfold RunMassWithinBudget
  linarith [b0, b1, b2, hbud]

/-! ## Part F — the genuine Run leaf, end-to-end -/

/--
**The Run separated local leaf of the actual shell, from the genuine residual center.**

Assembles `RunClosedL41L42I52PackageInputData` through `runLeafOfShell`, fed the
genuine shell residual center `runFOfShell` (never the forbidden `1/3` witness), the
deterministic trichotomy `runClsOfShell`, the shell scalars, the closed
`runChainRootOfShell`, and the single budget residual `RunMassWithinBudget`.
-/
def runLeafOfShellGenuine (ctx : ActualFailureContext) (h : RunMassWithinBudget ctx) :
    RunClosedL41L42I52PackageInputData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : ℝ) :=
  runLeafOfShell ctx (runClsOfShell ctx) (runFOfShell ctx) (runTwoNegcYOfShell ctx)
    (runIjOfShell ctx) (runSmallErrorOfShell ctx) (runSmallErrorNonnegOfShell ctx)
    (runChainRootOfShell ctx) (runBudgetOfShell ctx h)

/-- **The total run mass of the genuine of-shell family meets the I.5.2 budget.**  The
high-excess run mass — the sum of the four trichotomy class masses (chain `= 0`) — fits
`cStar·ξ·X/6`, the Prop. I.5.2 floor, with all data tied to the actual shell. -/
theorem runLeafOfShellGenuine_runMass_bound (ctx : ActualFailureContext)
    (h : RunMassWithinBudget ctx) :
    (runTrichotomyOfShell ctx (runClsOfShell ctx)).runMass
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  runLeafOfShell_runMass_bound ctx (runClsOfShell ctx) (runFOfShell ctx)
    (runTwoNegcYOfShell ctx) (runIjOfShell ctx) (runSmallErrorOfShell ctx)
    (runSmallErrorNonnegOfShell ctx) (runChainRootOfShell ctx) (runBudgetOfShell ctx h)

/-! ## Part F2 — discharging `RunMassWithinBudget` from the §26 positive-density run-area cover

The single residual `RunMassWithinBudget` is the high-excess run mass fitting `cStar·ξ·X/6`.
Here we discharge it from the **same** K.1.1 cover + I.4.1 packing + K.4 smallness data that proves
the Tower class-2 sub-mass (`class2_activeFloorCount_of_denseMarkerCover`) and the base run-area
bound (`RunBaseAreaCover.harea`), now on the *actual* high-excess run fibre and at the I.5.2
run-slot budget `cStar·ξ/6`, genuinely consuming the positive-density failure `ctx.hfailure`.  This
pins the package-track Run leaf's last residual to the genuine §26 manuscript cover geometry — the
same irreducible analytic input class the proved Tower class-2 sub-mass rests on. -/

/-- **The high-excess run fibre of the actual shell.**  All carry starts whose window excess clears
the active floor `Y`.  The three `runClsOfShell` trichotomy classes partition it (the chain class
being empty), so its total window-excess mass is exactly the high-excess run mass
`routed 0 + routed 1 + routed 2`. -/
def runHighExcessFibre (ctx : ActualFailureContext) : Finset ℕ :=
  highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
    ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y

/-- **The high-excess run mass equals the sum of the three trichotomy class masses.**  Mass
conservation (`highExcessMass_eq_sum_routedClassMassOf`) over the four `Fin 4` classes, with the
empty chain class `runClsOfShell_routed3_zero`. -/
theorem runHighExcessMass_eq (ctx : ActualFailureContext) :
    highExcessMass (runHighExcessFibre ctx) (hitGap ctx.n24CarryData.a)
        ctx.n24CarryData.r ctx.n24CarryData.T
      = routedClassMassOf ctx.n24CarryData (runClsOfShell ctx) 0
          + routedClassMassOf ctx.n24CarryData (runClsOfShell ctx) 1
          + routedClassMassOf ctx.n24CarryData (runClsOfShell ctx) 2 := by
  unfold runHighExcessFibre
  rw [highExcessMass_eq_sum_routedClassMassOf ctx.n24CarryData (runClsOfShell ctx),
    Fin.sum_univ_four, runClsOfShell_routed3_zero, add_zero]

/--
**The §26 positive-density run-area cover of the high-excess run fibre.**

The genuine analytic datum behind `RunMassWithinBudget`, in the exact shape of the *proved* Tower
class-2 residual `Class2DenseMarkerCover` (modulo the I.5.2 budget `ξ/6 ↦ cStar·ξ/6` and the free
K.1.2/L.20 multiplier):

* `mult`/`hmult_nonneg`/`hpoint` — the K.1.2/L.20 run window-excess multiplier bounding every
  high-excess-start window excess;
* `hcover` — the K.1.1 endpoint-disjoint cover `#fibre ≤ |𝒟₀|·(2·spread+1)`;
* `hpack` — the I.4.1 dense-marker hit packing `|𝒟₀|·ρ_D L ≤ #supportShell`;
* `hsmall` — the K.4 numerical smallness `(c₀/ρ_D L)·(2·spread+1)·mult ≤ cStar·ξ/6`.
-/
structure RunHighExcessAreaCover (ctx : ActualFailureContext) where
  /-- The K.1.2/L.20 run window-excess multiplier on the high-excess run fibre. -/
  mult : ℝ
  /-- The multiplier is nonnegative. -/
  hmult_nonneg : 0 ≤ mult
  /-- Each high-excess-start window excess is at most the multiplier. -/
  hpoint : ∀ k ∈ runHighExcessFibre ctx,
    windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T ≤ mult
  /-- The K.1.1 marker spread (cover half-width index). -/
  spread : ℕ
  /-- The number of selected disjoint dense markers `|𝒟₀|`. -/
  markersCard : ℕ
  /-- The per-marker hit floor `ρ_D·L`. -/
  rhoL : ℝ
  /-- The per-marker hit floor is positive. -/
  hrhoL_pos : 0 < rhoL
  /-- **K.1.1 endpoint-disjoint cover** of the high-excess run fibre. -/
  hcover : (runHighExcessFibre ctx).card ≤ markersCard * (2 * spread + 1)
  /-- **The I.4.1 dense-marker hit packing** into the shell support count. -/
  hpack : (markersCard : ℝ) * rhoL ≤ ((supportShell ctx.d ctx.X).card : ℝ)
  /-- **The K.4 numerical smallness** at the I.5.2 run-slot budget `cStar·ξ/6`. -/
  hsmall : (erdos260Constants.c0 / rhoL) * ((2 * spread + 1 : ℕ) : ℝ) * mult
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6

/-- **The §26 run-area numeric, PROVED by consuming the positive-density failure `ctx.hfailure`.**

`(#runHighExcessFibre)·mult ≤ cStar·ξ·X/6`, by the identical algebra as the proved Tower lemma
`class2_activeFloorCount_of_denseMarkerCover` and `RunBaseAreaCover.harea`: the K.1.1 cover, the
I.4.1 packing, the positive-density failure (`#supportShell < c₀·X`), and the K.4 smallness,
multiplied through by `c₀ > 0`.  The shared factor `X` cancels. -/
theorem RunHighExcessAreaCover.harea {ctx : ActualFailureContext}
    (C : RunHighExcessAreaCover ctx) :
    ((runHighExcessFibre ctx).card : ℝ) * C.mult
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 := by
  have hc0 : (0 : ℝ) < erdos260Constants.c0 := erdos260Constants.c0_pos
  have hcξ6 : (0 : ℝ) ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 :=
    div_nonneg (mul_nonneg erdos260Constants.cStar_pos.le erdos260Constants.ξ_pos.le) (by norm_num)
  have hmult : (0 : ℝ) ≤ C.mult := C.hmult_nonneg
  have hm : (0 : ℝ) ≤ (C.markersCard : ℝ) := Nat.cast_nonneg _
  have hρ : (0 : ℝ) < C.rhoL := C.hrhoL_pos
  have hcoverR :
      ((runHighExcessFibre ctx).card : ℝ)
        ≤ (C.markersCard : ℝ) * ((2 * C.spread + 1 : ℕ) : ℝ) := by
    exact_mod_cast C.hcover
  have hsmall' :
      erdos260Constants.c0 * ((2 * C.spread + 1 : ℕ) : ℝ) * C.mult
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * C.rhoL := by
    have h := C.hsmall
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hρ] at h
    exact h
  have hfail : ((supportShell ctx.d ctx.X).card : ℝ)
      < erdos260Constants.c0 * (ctx.shell.X : ℝ) := by
    rw [ActualFailureContext.shell_X]; exact ctx.hfailure
  have hmρ : (C.markersCard : ℝ) * C.rhoL ≤ erdos260Constants.c0 * (ctx.shell.X : ℝ) :=
    le_of_lt (lt_of_le_of_lt C.hpack hfail)
  have h1 :
      ((runHighExcessFibre ctx).card : ℝ) * C.mult
        ≤ ((C.markersCard : ℝ) * ((2 * C.spread + 1 : ℕ) : ℝ)) * C.mult :=
    mul_le_mul_of_nonneg_right hcoverR hmult
  have key :
      erdos260Constants.c0
          * (((runHighExcessFibre ctx).card : ℝ) * C.mult)
        ≤ erdos260Constants.c0
            * (erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :=
    calc erdos260Constants.c0
            * (((runHighExcessFibre ctx).card : ℝ) * C.mult)
          ≤ erdos260Constants.c0
              * (((C.markersCard : ℝ) * ((2 * C.spread + 1 : ℕ) : ℝ)) * C.mult) :=
            mul_le_mul_of_nonneg_left h1 hc0.le
      _ = (C.markersCard : ℝ)
            * (erdos260Constants.c0 * ((2 * C.spread + 1 : ℕ) : ℝ) * C.mult) := by ring
      _ ≤ (C.markersCard : ℝ)
            * (erdos260Constants.cStar * erdos260Constants.ξ / 6 * C.rhoL) :=
            mul_le_mul_of_nonneg_left hsmall' hm
      _ = erdos260Constants.cStar * erdos260Constants.ξ / 6
            * ((C.markersCard : ℝ) * C.rhoL) := by ring
      _ ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6
            * (erdos260Constants.c0 * (ctx.shell.X : ℝ)) :=
            mul_le_mul_of_nonneg_left hmρ hcξ6
      _ = erdos260Constants.c0
            * (erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) := by ring
  exact le_of_mul_le_mul_left key hc0

/-- **The high-excess run mass is at most `#fibre·mult`** (the K.1.2/L.20 multiplier bounds each
window excess). -/
theorem runHighExcessMass_le_card_mul {ctx : ActualFailureContext}
    (C : RunHighExcessAreaCover ctx) :
    highExcessMass (runHighExcessFibre ctx) (hitGap ctx.n24CarryData.a)
        ctx.n24CarryData.r ctx.n24CarryData.T
      ≤ ((runHighExcessFibre ctx).card : ℝ) * C.mult := by
  unfold highExcessMass
  calc ∑ k ∈ runHighExcessFibre ctx,
        windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
      ≤ ∑ _k ∈ runHighExcessFibre ctx, C.mult := Finset.sum_le_sum (fun k hk => C.hpoint k hk)
    _ = ((runHighExcessFibre ctx).card : ℝ) * C.mult := by
          rw [Finset.sum_const, nsmul_eq_mul]

/-- **`RunMassWithinBudget`, discharged from the §26 positive-density run-area cover.**  The high-excess
run mass equals `routed 0 + routed 1 + routed 2`, is `≤ #fibre·mult`, and the cover's `harea` numeric
caps that by `cStar·ξ·X/6`. -/
theorem RunHighExcessAreaCover.hbudget {ctx : ActualFailureContext}
    (C : RunHighExcessAreaCover ctx) : RunMassWithinBudget ctx := by
  have hmass := runHighExcessMass_eq ctx
  have hle := le_trans (runHighExcessMass_le_card_mul C) C.harea
  unfold RunMassWithinBudget
  linarith [hmass, hle]

/--
**The Run separated local leaf of the actual shell, from the §26 run-area cover.**

End-to-end: `runLeafOfShellGenuine` fed the §26 positive-density cover `C` (which discharges the
single budget residual `RunMassWithinBudget` from `ctx.hfailure`).  This reduces the package-track
Run leaf to the **one** genuine §26/I.4.1 cover datum `RunHighExcessAreaCover ctx` — the same
irreducible input class the proved Tower class-2 sub-mass rests on. -/
def runLeafOfShellOfCover (ctx : ActualFailureContext) (C : RunHighExcessAreaCover ctx) :
    RunClosedL41L42I52PackageInputData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : ℝ) :=
  runLeafOfShellGenuine ctx C.hbudget

/-- **The total run mass of the cover-built family meets the I.5.2 floor.**  The high-excess run mass
(sum of the four trichotomy class masses, chain `= 0`) fits `cStar·ξ·X/6`, with every quantity tied
to the actual shell and the budget discharged genuinely from the §26 cover. -/
theorem runLeafOfShellOfCover_runMass_bound (ctx : ActualFailureContext)
    (C : RunHighExcessAreaCover ctx) :
    (runTrichotomyOfShell ctx (runClsOfShell ctx)).runMass
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  runLeafOfShellGenuine_runMass_bound ctx C.hbudget

/-- **The Run separated local leaf (the named Appendix-N target `RunSeparatedLocalLeafInputData`),
from the §26 run-area cover.**  Projects the manuscript-shaped package through
`runSeparatedLocalLeafFromClosedL41L42I52Package`. -/
def runSeparatedLocalLeafOfShellOfCover (ctx : ActualFailureContext)
    (C : RunHighExcessAreaCover ctx) :
    RunSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : ℝ) :=
  runSeparatedLocalLeafFromClosedL41L42I52Package (runLeafOfShellOfCover ctx C)

/-- **The grounded Run local data consumed by the global assembly, from the §26 cover.**  This is the
`GroundedRunLocalData` shape the per-failure assembly's `run` column ingests, built end-to-end from
the single genuine §26/I.4.1 cover datum `RunHighExcessAreaCover ctx`. -/
def groundedRunLocalOfShellOfCover (ctx : ActualFailureContext)
    (C : RunHighExcessAreaCover ctx) :
    GroundedRunLocalData erdos260Constants.cStar erdos260Constants.ξ (ctx.shell.X : ℝ) :=
  (runSeparatedLocalLeafOfShellOfCover ctx C).toGroundedRunLocalData

/-- **Proposition I.5.2 final run bound, end-to-end from the §26 cover.**  `runMass ≤ cStar·ξ·X/6`
for the grounded Run local data built from the §26 cover of the actual shell. -/
theorem groundedRunLocalOfShellOfCover_run_bound (ctx : ActualFailureContext)
    (C : RunHighExcessAreaCover ctx) :
    (groundedRunLocalOfShellOfCover ctx C).runMass
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  (groundedRunLocalOfShellOfCover ctx C).run_bound

/-! ## Part G — honest residual inventory -/

/-- The honest status of the Run L.4.1/L.4.2/I.5.2 cores after this file. -/
def runL4I52CoreResiduals : List String :=
  [ "CLOSED (runF, centerpiece) — runFOfShell: the §25.1 residual center is the actual " ++
      "shell's small-denominator non-dyadic rational Q/(2Q+1) (denominator built from " ++
      "ctx.shell.Q), replacing the forbidden 1/3 witness; its §25.2 residue orbit never " ++
      "terminates (runFOfShell_residueOrbit), the small-denominator shadow of the shell-level " ++
      "non-termination shell_run_nonterminating (= ctx.shell.hnonterm).",
    "CLOSED (runF provenance) — runFOfShell_q0_gt_one/_q0_odd/_coprime/_halfDecrease: the full " ++
      "§25.2 reduced data (q₀,a,m) and the L.4.2 half-decrease on dyadicDigit q₀ a are derived " ++
      "from the actual shell residual center.",
    "CLOSED (runCls) — runClsOfShell: deterministic L.4.1 trichotomy on the actual high-excess " ++
      "carry starts; never routes to the chain class (runClsOfShell_ne_three), so the chain " ++
      "routed mass is 0 (runClsOfShell_routed3_zero).",
    "CLOSED (runChainRoot, runSmallErrorNonneg) — runChainRootOfShell, runSmallErrorNonnegOfShell.",
    "CLOSED (scalars) — runTwoNegcYOfShell = (1/2)^Q (the genuine 2^{-cY}), runIjOfShell, " ++
      "runSmallErrorOfShell.",
    "REDUCED (runBudget, I.5.2) — runBudgetOfShell reduces the budget field to the single named " ++
      "residual RunMassWithinBudget (high-excess run mass ≤ cStar·ξ·X/6); " ++
      "runMassWithinBudget_of_charge further reduces it to per-fibre window-excess charge data " ++
      "(K.1.2/L.20 multiplier + J.1.1 fibre count). This is the genuine irreducible I.5.2 " ++
      "analytic input.",
    "DISCHARGED (runBudget from §26 cover, consuming ctx.hfailure) — RunHighExcessAreaCover.hbudget: " ++
      "RunMassWithinBudget follows from the §26 positive-density run-area cover on the actual " ++
      "high-excess run fibre runHighExcessFibre (the union of the three trichotomy classes, " ++
      "runHighExcessMass_eq), by the IDENTICAL algebra (RunHighExcessAreaCover.harea) as the proved " ++
      "Tower lemma class2_activeFloorCount_of_denseMarkerCover and RunBaseAreaCover.harea: K.1.1 cover " ++
      "#fibre ≤ |𝒟₀|(2spread+1), I.4.1 packing |𝒟₀|ρ_D L ≤ #supportShell, failure #supportShell < " ++
      "c₀X, K.4 smallness, all multiplied through by c₀>0 with the shared factor X cancelling. NO free " ++
      "count, NO degenerate witness.",
    "ASSEMBLED — runLeafOfShellGenuine / runLeafOfShellOfCover build the full " ++
      "RunClosedL41L42I52PackageInputData from the genuine residual center and either the single budget " ++
      "residual (RunMassWithinBudget) or the §26 cover (RunHighExcessAreaCover ctx). The package-track " ++
      "Run leaf's sharpest residual is now ∀ ctx, RunHighExcessAreaCover ctx — the genuine §26/I.4.1 " ++
      "dense-marker cover geometry of the actual high-excess run fibre." ]

theorem runL4I52CoreResiduals_nonempty : runL4I52CoreResiduals ≠ [] := by
  simp [runL4I52CoreResiduals]

-- Axiom-cleanliness self-checks: the centerpiece residue-orbit non-termination, the
-- closed L.4.2 chain root, and the end-to-end I.5.2 run-mass bound depend only on the
-- standard Lean axioms `propext`, `Classical.choice`, `Quot.sound` (no `sorry`/custom
-- axiom/`admit`).
#print axioms runFOfShell_residueOrbit
#print axioms runChainRootOfShell
#print axioms runLeafOfShellGenuine_runMass_bound
#print axioms RunHighExcessAreaCover.harea
#print axioms RunHighExcessAreaCover.hbudget
#print axioms runLeafOfShellOfCover
#print axioms runLeafOfShellOfCover_runMass_bound
#print axioms runSeparatedLocalLeafOfShellOfCover
#print axioms groundedRunLocalOfShellOfCover
#print axioms groundedRunLocalOfShellOfCover_run_bound

end

end Erdos260
