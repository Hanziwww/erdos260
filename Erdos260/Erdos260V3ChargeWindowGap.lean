import Erdos260.Erdos260V3ClassBundles

/-!
# Discharging the Chernoff / clean-CNL active-window gap from the PROVED dyadic ceiling

This module (NEW; it edits no existing file) removes the active-window **gap geometry** (`g₀` and
`hgap`) from the genuine charge-injection residuals `Class0ChernoffInjection` (class 0) and
`Class1CNLInjection` (class 1).

The key observation is that the dyadic-shell gap ceiling `hitGap a j ≤ L+B+1`
(`hitGap_le_densePackDyadicG0_of_window`, proved in `DensePackK11SeedClosure` from
`HitSequence.hitGap_le_of_shell_window`) is **class-agnostic**: it bounds the carry hit gap at *any*
index `j` inside the shell window, regardless of which routed fibre `j` belongs to.  DensePack
(class 3) already exploits this (`densePackGap_ofContainment`); here we do the same for classes 0/1.

So the Chernoff/CNL `hgap` field is no longer assumed: it is **derived** from the proved ceiling and
the single shared geometric residual — the **active-window containment** that each charged start's
descent window `[k, k+r]` stays below `firstIndexAbove X + windowReach` (the manuscript active-window
structure, the `hfibre_win` core, shared with DensePack Core 13).  After this reduction the
Chernoff/CNL residual is exactly the genuine charge injection (the §22.1A high-cost embedding / the
L.1.2 cluster reconstruction map + the area/Kraft cap + the K.1.2 calibration), with `g₀ := L+B+1`
fixed and the gap proved.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

namespace Erdos260

open Finset

noncomputable section

set_option linter.unusedVariables false

/-! ## 1.  The class-agnostic active-window gap, from the proved dyadic ceiling + containment -/

/-- **Every routed fibre is a sub-collection of the carry start set.**  `routedFibre` is a double
`Finset.filter` of `carryData.starts` (through `highExcessStarts`), so it is contained in the start
set — independent of the route. -/
theorem routedFibre_subset_starts {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr) (route : ℕ → Fin 7) (i : Fin 7) :
    routedFibre carryData route i ⊆ carryData.starts := by
  intro k hk
  rw [routedFibre, Finset.mem_filter] at hk
  exact (Finset.mem_filter.mp hk.1).1

/-- **The active-window gap bound on any routed fibre, derived from the proved dyadic ceiling.**

For any class `c` and any budget, if each class-`c` charged start's descent window `[k, k+r]` stays
below `firstIndexAbove X + windowReach` (the active-window containment, `hContain`) for a reach inside
the support shell (`hReach`), then the carry hit gap on that window obeys `hitGap a j ≤ L+B+1`
(`= densePackDyadicG0`).  This is the proved `hitGap_le_densePackDyadicG0_of_window`, now read off any
class fibre — the gap field is constructed, not assumed. -/
theorem chargeWindowGap_of_containment
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx) (c : Fin 7)
    (windowReach : ActualFailureContext → ℕ)
    (hReach : ∀ ctx : ActualFailureContext,
      windowReach ctx + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hContain : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route c,
        k + ctx.n24CarryData.r
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + windowReach ctx) :
    ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route c,
        ∀ j, k ≤ j → j ≤ k + ctx.n24CarryData.r →
          hitGap ctx.n24CarryData.a j ≤ densePackDyadicG0 ctx := by
  intro ctx k hk j _hkj hjr
  have hcontain := hContain ctx k hk
  have hj : j < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + windowReach ctx := by omega
  exact hitGap_le_densePackDyadicG0_of_window ctx (hReach ctx) hj

/-! ## 2.  The Chernoff (class-0) injection with the gap field DISCHARGED -/

/-- **Build `Class0ChernoffInjection` with `g₀ := L+B+1` and `hgap` derived from the proved ceiling.**

The active-window gap geometry (`g₀`/`hgap`) is no longer a free residual field: `g₀` is the definite
dyadic ceiling `densePackDyadicG0` and `hgap` is `chargeWindowGap_of_containment`.  The only carried
residual is the genuine §22.1A charge injection (`chargeOf`/`hmaps`/`hinj`/`hcap`, the high-cost
embedding + area cap), the K.1.2 calibration (`hscale`/`hmult_nonneg`), and the shared active-window
containment (`windowReach`/`hReach`/`hContain`). -/
def Class0ChernoffInjection.ofWindowContainment
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (chargeOf : ∀ ctx : ActualFailureContext,
      ℕ → ((faithfulCapacityPhases budget ctx).toClosurePhaseData).chernoff.α)
    (hmaps : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
        chargeOf ctx k ∈ highCostSet
          ((faithfulCapacityPhases budget ctx).toClosurePhaseData).chernoff.paths
          ((faithfulCapacityPhases budget ctx).toClosurePhaseData).chernoff.cost
          ((faithfulCapacityPhases budget ctx).toClosurePhaseData).chernoff.Y)
    (hinj : ∀ ctx : ActualFailureContext,
      ∀ x ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
        ∀ y ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
          chargeOf ctx x = chargeOf ctx y → x = y)
    (mult : ∀ _ctx : ActualFailureContext, ℝ)
    (hmult_nonneg : ∀ ctx : ActualFailureContext, 0 ≤ mult ctx)
    (hscale : ∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ) - ctx.n24CarryData.T ≤ mult ctx)
    (hcap : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
        mult ctx ≤ ((faithfulCapacityPhases budget ctx).toClosurePhaseData).chernoff.weight
          (chargeOf ctx k))
    (windowReach : ActualFailureContext → ℕ)
    (hReach : ∀ ctx : ActualFailureContext,
      windowReach ctx + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hContain : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
        k + ctx.n24CarryData.r
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + windowReach ctx) :
    Class0ChernoffInjection budget where
  chargeOf := chargeOf
  hmaps := hmaps
  hinj := hinj
  g₀ := densePackDyadicG0
  mult := mult
  hgap := chargeWindowGap_of_containment budget 0 windowReach hReach hContain
  hscale := hscale
  hmult_nonneg := hmult_nonneg
  hcap := hcap

/-! ## 3.  The clean-CNL (class-1) injection with the gap field DISCHARGED -/

/-- **Build `Class1CNLInjection` with `g₀ := L+B+1` and `hgap` derived from the proved ceiling.**

As for Chernoff: the active-window gap geometry is discharged from the proved dyadic ceiling and the
shared containment.  The only carried residual is the genuine L.1.2 cluster reconstruction map
(`g`/`hmem`/`hinj`), the G.6 per-codeword Kraft cap (`hcap`), the K.1.2 calibration, and the
active-window containment. -/
def Class1CNLInjection.ofWindowContainment
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (g : ∀ _ctx : ActualFailureContext, ℕ → CNLTransition)
    (hmem : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 1,
        g ctx k ∈ selectedTransitions (liftTransitionsOfShell ctx))
    (hinj : ∀ ctx : ActualFailureContext,
      ∀ k₁ ∈ routedFibre ctx.n24CarryData (budget ctx).route 1,
        ∀ k₂ ∈ routedFibre ctx.n24CarryData (budget ctx).route 1,
          g ctx k₁ = g ctx k₂ → k₁ = k₂)
    (mult : ∀ _ctx : ActualFailureContext, ℝ)
    (hmult_nonneg : ∀ ctx : ActualFailureContext, 0 ≤ mult ctx)
    (hscale : ∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ) - ctx.n24CarryData.T ≤ mult ctx)
    (hcap : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 1,
        mult ctx ≤ (2 : ℝ) ^ (-(bndHeightNatOfShell ctx (g ctx k) : ℝ))
          * (cnlShellFactorOfShell ctx : ℝ) * (ctx.shell.X : ℝ) * (cnlIjOfShell ctx : ℝ))
    (windowReach : ActualFailureContext → ℕ)
    (hReach : ∀ ctx : ActualFailureContext,
      windowReach ctx + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hContain : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 1,
        k + ctx.n24CarryData.r
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + windowReach ctx) :
    Class1CNLInjection budget where
  g := g
  hmem := hmem
  hinj := hinj
  g₀ := densePackDyadicG0
  mult := mult
  hgap := chargeWindowGap_of_containment budget 1 windowReach hReach hContain
  hscale := hscale
  hmult_nonneg := hmult_nonneg
  hcap := hcap

/-! ## 4.  Axiom-cleanliness audit -/

#print axioms routedFibre_subset_starts
#print axioms chargeWindowGap_of_containment
#print axioms Class0ChernoffInjection.ofWindowContainment
#print axioms Class1CNLInjection.ofWindowContainment

end

end Erdos260
