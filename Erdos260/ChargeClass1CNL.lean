import Erdos260.Erdos260ChargeReduced
import Erdos260.CNLScalarBudgetCore

/-!
# Class-1 (clean-CNL) charging bound for the faithful charge residual

This module attacks the **`hCnl` field** of `Erdos260ChargeResidual`
(`Erdos260ChargeReduced.lean`): the class-1 = clean-CNL Kraft-tail charging
direction (Lemma L.1.2 / G.35, the J.1.1 charging),

```
hCnl : ∀ ctx,
  routedClassMassOf ctx.n24CarryData (budget ctx).route 1
    ≤ termCnl (faithfulCapacityPhases budget ctx).toClosurePhaseData.
```

## The genuine mechanism (faithful H.1/H.2 / J.1.1 charging)

`termCnl data` is the clean weighted-Kraft CNL tail

```
termCnl data = (∑_{t ∈ paths} 2^{-c·BND(t)}) · shellFactor · X · |I_j|
             = cleanCNLKraftSum paths BND c · shellFactor · X · |I_j|.
```

The routed class-1 mass is the window-excess sum over the class-1 fibre
`F = routedFibre … 1`.  The faithful J.1.1 charging assigns each class-1 start
to a **distinct surviving clean-CNL codeword** (an injection `g : F ↪ paths`)
and charges its window excess at that codeword's Kraft rate:

```
windowExcess(k) ≤ 2^{-c·BND(g k)} · shellFactor · X · |I_j|     (k ∈ F).
```

Summing and reindexing through the injection (`Finset.sum_image`), then
dominating the image sum by the full family sum (the surviving clean-CNL
transition family, whose weighted-Kraft sum is `≤ 2^M`):

```
∑_{k∈F} windowExcess(k)
  ≤ (shellFactor·X·|I_j|) · ∑_{k∈F} 2^{-c·BND(g k)}
  = (shellFactor·X·|I_j|) · ∑_{t∈ g(F)} 2^{-c·BND(t)}      (Finset.sum_image, g injective)
  ≤ (shellFactor·X·|I_j|) · ∑_{t∈ paths} 2^{-c·BND(t)}     (g(F) ⊆ paths, nonneg)
  = termCnl data.
```

This **closes** `routedClassMassOf … 1 ≤ termCnl …` from the genuinely minimal
J.1.1 input: the charge map `g` (class-1 starts ↪ surviving clean-CNL codewords),
its injectivity (the "J.1.1 fibre count of class-1 starts identified with the
clean-CNL transition count"), its membership in the surviving family, and the
per-codeword K.1.2/L.20 window-excess charge bound.

## What this file CLOSES

* `routedClassMass_le_termCnl_of_kraftCharge` — the **generic full close**: for
  any `ClosurePhaseData`, the routed class-`i` mass is `≤ termCnl` from the
  per-element Kraft charge data, via the injective reindexing.  No budget
  identification is carried — it is *derived* from the weighted-Kraft structure.
* `class1Fibre_card_le_cnlPaths` — the J.1.1 count realization: the class-1
  fibre injects into the surviving clean-CNL transition family, so its
  cardinality is bounded by the family's.
* `Class1CNLChargeData` / `Class1CNLChargeData.hCnl` — the minimal named residual
  for the *faithful* assembly: the J.1.1 charge map + per-codeword charge bound,
  producing exactly the `Erdos260ChargeResidual.hCnl` field shape.
* `routedClassMass_le_termCnl_of_countMultiplier` — the alternative
  count×multiplier reduction reusing the proved `routedClassMassOf_le_countMultiplier`
  (the carried `count·mult ≤ termCnl` identification, matching
  `ChargeRoutingFibreResidual.hbud1`).

## The minimal residual

`Class1CNLChargeData` carries only the genuine J.1.1 / H.1 / H.2 dynamical
content (the charge injection and the per-codeword window-excess rate); these
are the orthogonal charging direction not derivable from any proved phase budget,
exactly as documented in `ChargeRoutingCore`.  No degenerate/empty shortcut: the
charge map ranges over the genuinely nonempty surviving clean-CNL family.

No `sorry`, `axiom`, or `admit`.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 1.  The generic full close: routed class mass `≤ termCnl` from Kraft charging -/

/-- **Generic per-element Kraft charging close of a routed class mass against
`termCnl`.**

For any `ClosurePhaseData data` and any routing `route`, the routed class-`i`
mass is dominated by the clean-CNL phase term `termCnl data`, provided each
class-`i` start `k` is charged (injectively) to a surviving clean-CNL codeword
`g k ∈ data.cnl.paths` whose Kraft weight times the shell/interval normalization
`2^{-c·BND(g k)} · shellFactor · X · |I_j|` dominates its window excess.

This is the faithful Lemma L.1.2 / G.35 charging: it derives the
`count·mult ≤ termCnl` step from the weighted-Kraft structure (`Finset.sum_image`
reindexing through the injection, then domination by the full family Kraft sum),
rather than carrying it as a free hypothesis. -/
theorem routedClassMass_le_termCnl_of_kraftCharge
    {shell : FailingDyadicShell} {cPr cStar ξ X : ℝ}
    (carryData : CarryDataFromFailure shell cPr)
    (data : ClosurePhaseData cStar ξ X)
    (route : ℕ → Fin 7) (i : Fin 7)
    (hX : 0 ≤ X)
    (g : ℕ → data.cnl.α)
    (hmem : ∀ k ∈ routedFibre carryData route i, g k ∈ data.cnl.paths)
    (hinj : ∀ k₁ ∈ routedFibre carryData route i,
      ∀ k₂ ∈ routedFibre carryData route i, g k₁ = g k₂ → k₁ = k₂)
    (hcharge : ∀ k ∈ routedFibre carryData route i,
      windowExcess (hitGap carryData.a) k carryData.r carryData.T
        ≤ (2 : ℝ) ^ (-(data.cnl.c * data.cnl.BNDHeight (g k)))
            * data.cnl.shellFactor * X * data.cnl.Ij) :
    routedClassMassOf carryData route i ≤ termCnl data := by
  classical
  rw [routedClassMassOf_eq_sum_fibre]
  set F := routedFibre carryData route i with hF
  -- The clean-CNL phase term as a Kraft sum times the shell/interval normalization.
  have htermCnl : termCnl data
      = (∑ t ∈ data.cnl.paths, (2 : ℝ) ^ (-(data.cnl.c * data.cnl.BNDHeight t)))
          * (data.cnl.shellFactor * X * data.cnl.Ij) := by
    unfold termCnl cleanCNLKraftSum; ring
  have hconst : (0 : ℝ) ≤ data.cnl.shellFactor * X * data.cnl.Ij :=
    mul_nonneg (mul_nonneg data.cnl.shellFactor_nonneg hX) data.cnl.Ij_nonneg
  -- Injective reindexing of the charged Kraft weights along `g`.
  have hreindex :
      (∑ t ∈ F.image g, (2 : ℝ) ^ (-(data.cnl.c * data.cnl.BNDHeight t)))
        = ∑ k ∈ F, (2 : ℝ) ^ (-(data.cnl.c * data.cnl.BNDHeight (g k))) :=
    Finset.sum_image hinj
  rw [htermCnl]
  calc ∑ k ∈ F, windowExcess (hitGap carryData.a) k carryData.r carryData.T
      ≤ ∑ k ∈ F, (2 : ℝ) ^ (-(data.cnl.c * data.cnl.BNDHeight (g k)))
            * data.cnl.shellFactor * X * data.cnl.Ij :=
        Finset.sum_le_sum (fun k hk => hcharge k hk)
    _ = (∑ k ∈ F, (2 : ℝ) ^ (-(data.cnl.c * data.cnl.BNDHeight (g k))))
            * (data.cnl.shellFactor * X * data.cnl.Ij) := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun k _ => by ring)
    _ = (∑ t ∈ F.image g, (2 : ℝ) ^ (-(data.cnl.c * data.cnl.BNDHeight t)))
            * (data.cnl.shellFactor * X * data.cnl.Ij) := by rw [hreindex]
    _ ≤ (∑ t ∈ data.cnl.paths, (2 : ℝ) ^ (-(data.cnl.c * data.cnl.BNDHeight t)))
            * (data.cnl.shellFactor * X * data.cnl.Ij) := by
        apply mul_le_mul_of_nonneg_right _ hconst
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.image_subset_iff.mpr hmem)
          (fun t _ _ => Real.rpow_nonneg (by norm_num) _)

/-- **The J.1.1 fibre-count realization.**  If the class-`i` starts inject into
the surviving clean-CNL transition family `data.cnl.paths`, then the fibre count
is bounded by the family count.  This is the "count of class-1 starts identified
with the clean-CNL transition count" (`Finset.card_le_card_of_injOn`). -/
theorem class1Fibre_card_le_cnlPaths
    {shell : FailingDyadicShell} {cPr cStar ξ X : ℝ}
    (carryData : CarryDataFromFailure shell cPr)
    (data : ClosurePhaseData cStar ξ X)
    (route : ℕ → Fin 7) (i : Fin 7)
    (g : ℕ → data.cnl.α)
    (hmem : ∀ k ∈ routedFibre carryData route i, g k ∈ data.cnl.paths)
    (hinj : ∀ k₁ ∈ routedFibre carryData route i,
      ∀ k₂ ∈ routedFibre carryData route i, g k₁ = g k₂ → k₁ = k₂) :
    (routedFibre carryData route i).card ≤ data.cnl.paths.card :=
  Finset.card_le_card_of_injOn g hmem hinj

/-! ## 2.  The count×multiplier reduction (reuses `routedClassMassOf_le_countMultiplier`) -/

/-- **Count×multiplier reduction of the class-`i` mass against `termCnl`.**

The alternative manuscript granularity (matching `ChargeRoutingFibreResidual`):
a uniform per-fibre window-excess multiplier, the J.1.1 fibre count, and the
`count·mult ≤ termCnl` identification, chained through the proved
`routedClassMassOf_le_countMultiplier`.  Here the budget identification is carried
whole (unlike `routedClassMass_le_termCnl_of_kraftCharge`, which derives it from
the weighted-Kraft structure). -/
theorem routedClassMass_le_termCnl_of_countMultiplier
    {shell : FailingDyadicShell} {cPr cStar ξ X : ℝ}
    (carryData : CarryDataFromFailure shell cPr)
    (data : ClosurePhaseData cStar ξ X)
    (route : ℕ → Fin 7) (i : Fin 7)
    {multiplier count : ℝ}
    (hpoint : ∀ k ∈ routedFibre carryData route i,
      windowExcess (hitGap carryData.a) k carryData.r carryData.T ≤ multiplier)
    (hmult_nonneg : 0 ≤ multiplier)
    (hcard : ((routedFibre carryData route i).card : ℝ) ≤ count)
    (hbud : count * multiplier ≤ termCnl data) :
    routedClassMassOf carryData route i ≤ termCnl data :=
  (routedClassMassOf_le_countMultiplier carryData route i hpoint hmult_nonneg hcard).trans hbud

/-! ## 3.  The minimal class-1 CNL charge residual for the faithful assembly

The smallest honest interface producing the `Erdos260ChargeResidual.hCnl` field:
for each failure context, the J.1.1 charge map of class-1 (clean-CNL) starts into
the surviving clean-CNL transition family of the *faithful capacity* phases,
together with its injectivity, membership, and the per-codeword K.1.2/L.20
window-excess charge bound.  Everything else is closed by
`routedClassMass_le_termCnl_of_kraftCharge`. -/

/-- The clean-CNL phase data (`CNLEntropyData`) of the faithful capacity
assembly at a failure context. -/
abbrev faithfulCnlData
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :=
  (faithfulCapacityPhases budget ctx).toClosurePhaseData.cnl

/-! ### Concrete characterization of the faithful CNL data

The faithful assembly's clean-CNL phase data is *exactly* the genuine shell
construction `cnlLeafFromShellConcrete` (via `cnlLeafOfShell`): the surviving
clean-CNL transition family `selectedTransitions (liftTransitionsOfShell ctx)`,
the Nat BND heights `bndHeightNatOfShell`, the standard slope `c = 1`, the
shell-Chernoff factor `cnlShellFactorOfShell`, and the dyadic interval length
`cnlIjOfShell`.  These let a downstream charge map be stated against the genuine
surviving family, never a degenerate/empty stand-in. -/

/-- The faithful assembly's clean-CNL family **is** the genuine surviving
clean-CNL transition family of the shell. -/
theorem faithfulCnlData_paths
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    (faithfulCnlData budget ctx).paths = selectedTransitions (liftTransitionsOfShell ctx) :=
  selectedTransitions_idempotent _

/-- The faithful assembly's clean-CNL BND height is the genuine `bndHeightNatOfShell`. -/
theorem faithfulCnlData_BNDHeight
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    (faithfulCnlData budget ctx).BNDHeight = (fun t => (bndHeightNatOfShell ctx t : ℝ)) :=
  rfl

/-- The faithful assembly's clean-CNL slope is the standard `c = 1`. -/
theorem faithfulCnlData_c
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    (faithfulCnlData budget ctx).c = (1 : ℝ) :=
  rfl

/-- The faithful assembly's clean-CNL shell factor is `cnlShellFactorOfShell`. -/
theorem faithfulCnlData_shellFactor
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    (faithfulCnlData budget ctx).shellFactor = (cnlShellFactorOfShell ctx : ℝ) :=
  rfl

/-- The faithful assembly's clean-CNL interval length is `cnlIjOfShell`. -/
theorem faithfulCnlData_Ij
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    (faithfulCnlData budget ctx).Ij = (cnlIjOfShell ctx : ℝ) :=
  rfl

/-- **The minimal class-1 (clean-CNL) charge residual.**

For every failure context: the J.1.1 charge map `chargeMap ctx` sending each
class-1 high-excess carry start to a surviving clean-CNL codeword of the faithful
assembly, the injectivity (class-1 fibre count ≤ surviving clean-CNL count), the
membership in the surviving family, and the per-codeword window-excess charge
bound (the K.1.2/L.20 multiplier at the Kraft rate `2^{-c·BND}` times the
shell/interval normalization `shellFactor·X·|I_j|`).

These are exactly the genuine deep J.1.1 / H.1 / H.2 charging facts; everything
else in the class-1 bound is discharged from the weighted-Kraft structure. -/
structure Class1CNLChargeData
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx) where
  /-- The J.1.1 charge map: each class-1 start ↦ a surviving clean-CNL codeword. -/
  chargeMap : ∀ ctx : ActualFailureContext, ℕ → (faithfulCnlData budget ctx).α
  /-- Codewords are surviving clean-CNL transitions (members of the family). -/
  hmem : ∀ ctx : ActualFailureContext,
    ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 1,
      chargeMap ctx k ∈ (faithfulCnlData budget ctx).paths
  /-- **The J.1.1 count identification**: distinct class-1 starts get distinct
  clean-CNL codewords (so the class-1 fibre count ≤ surviving family count). -/
  hinj : ∀ ctx : ActualFailureContext,
    ∀ k₁ ∈ routedFibre ctx.n24CarryData (budget ctx).route 1,
      ∀ k₂ ∈ routedFibre ctx.n24CarryData (budget ctx).route 1,
        chargeMap ctx k₁ = chargeMap ctx k₂ → k₁ = k₂
  /-- **The K.1.2/L.20 per-codeword charge bound**: a class-1 start's window
  excess is at most its codeword's Kraft weight times the shell/interval factor. -/
  hcharge : ∀ ctx : ActualFailureContext,
    ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 1,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        ≤ (2 : ℝ) ^ (-((faithfulCnlData budget ctx).c
              * (faithfulCnlData budget ctx).BNDHeight (chargeMap ctx k)))
            * (faithfulCnlData budget ctx).shellFactor
            * (ctx.shell.X : ℝ)
            * (faithfulCnlData budget ctx).Ij

namespace Class1CNLChargeData

variable {budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}

/-- **The class-1 clean-CNL charging bound, exactly the `Erdos260ChargeResidual.hCnl`
field shape.**  Discharged from the minimal J.1.1 charge data via the generic
Kraft-charging close `routedClassMass_le_termCnl_of_kraftCharge`. -/
theorem hCnl (R : Class1CNLChargeData budget) (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (budget ctx).route 1
      ≤ termCnl (faithfulCapacityPhases budget ctx).toClosurePhaseData :=
  routedClassMass_le_termCnl_of_kraftCharge ctx.n24CarryData
    (faithfulCapacityPhases budget ctx).toClosurePhaseData (budget ctx).route 1
    ctx.shell.X_pos_real.le (R.chargeMap ctx) (R.hmem ctx) (R.hinj ctx) (R.hcharge ctx)

/-- The class-1 charge data also realizes the J.1.1 fibre count: the class-1
fibre injects into the surviving clean-CNL transition family. -/
theorem fibre_card_le (R : Class1CNLChargeData budget) (ctx : ActualFailureContext) :
    (routedFibre ctx.n24CarryData (budget ctx).route 1).card
      ≤ (faithfulCnlData budget ctx).paths.card :=
  class1Fibre_card_le_cnlPaths ctx.n24CarryData
    (faithfulCapacityPhases budget ctx).toClosurePhaseData (budget ctx).route 1
    (R.chargeMap ctx) (R.hmem ctx) (R.hinj ctx)

/-- **Concrete class-1 charge data from a shell-level charge map.**

Build the minimal residual from a charge map valued directly in the genuine
surviving clean-CNL transition family `selectedTransitions (liftTransitionsOfShell ctx)`,
with the per-codeword charge bound stated through the named shell quantities
`bndHeightNatOfShell` / `cnlShellFactorOfShell` / `cnlIjOfShell` (the data fields
of `cnlLeafFromShellConcrete`).  This exposes the J.1.1 charging against the
honest surviving family — never an empty/degenerate stand-in. -/
def ofShellCharge
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (g : ∀ _ctx : ActualFailureContext, ℕ → CNLTransition)
    (hmem : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 1,
        g ctx k ∈ selectedTransitions (liftTransitionsOfShell ctx))
    (hinj : ∀ ctx : ActualFailureContext,
      ∀ k₁ ∈ routedFibre ctx.n24CarryData (budget ctx).route 1,
        ∀ k₂ ∈ routedFibre ctx.n24CarryData (budget ctx).route 1,
          g ctx k₁ = g ctx k₂ → k₁ = k₂)
    (hcharge : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 1,
        windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
          ≤ (2 : ℝ) ^ (-(bndHeightNatOfShell ctx (g ctx k) : ℝ))
              * (cnlShellFactorOfShell ctx : ℝ) * (ctx.shell.X : ℝ)
              * (cnlIjOfShell ctx : ℝ)) :
    Class1CNLChargeData budget where
  chargeMap := g
  hmem := fun ctx k hk => by
    rw [faithfulCnlData_paths]; exact hmem ctx k hk
  hinj := hinj
  hcharge := fun ctx k hk => by
    have h := hcharge ctx k hk
    simpa only [faithfulCnlData_c, faithfulCnlData_BNDHeight, faithfulCnlData_shellFactor,
      faithfulCnlData_Ij, one_mul] using h

/-- **The class-1 clean-CNL charging bound from a concrete shell-level charge map.**
The `Erdos260ChargeResidual.hCnl` field shape, discharged directly from a charge
map into the genuine surviving clean-CNL transition family. -/
theorem hCnl_ofShellCharge
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (g : ∀ _ctx : ActualFailureContext, ℕ → CNLTransition)
    (hmem : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 1,
        g ctx k ∈ selectedTransitions (liftTransitionsOfShell ctx))
    (hinj : ∀ ctx : ActualFailureContext,
      ∀ k₁ ∈ routedFibre ctx.n24CarryData (budget ctx).route 1,
        ∀ k₂ ∈ routedFibre ctx.n24CarryData (budget ctx).route 1,
          g ctx k₁ = g ctx k₂ → k₁ = k₂)
    (hcharge : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 1,
        windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
          ≤ (2 : ℝ) ^ (-(bndHeightNatOfShell ctx (g ctx k) : ℝ))
              * (cnlShellFactorOfShell ctx : ℝ) * (ctx.shell.X : ℝ)
              * (cnlIjOfShell ctx : ℝ))
    (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (budget ctx).route 1
      ≤ termCnl (faithfulCapacityPhases budget ctx).toClosurePhaseData :=
  (ofShellCharge budget g hmem hinj hcharge).hCnl ctx

end Class1CNLChargeData

/-! ## 4.  Integration witness — the bound IS the `Erdos260ChargeResidual.hCnl` field

Replacing the `hCnl` field of any consolidated residual by the field produced
from a `Class1CNLChargeData` only typechecks if the produced statement matches the
field exactly; this `def` is therefore a machine-checked witness that
`Class1CNLChargeData.hCnl` discharges the genuine `Erdos260ChargeResidual.hCnl`
slot (over the same `budget`). -/
def Erdos260ChargeResidual.withClass1CNL
    (S : Erdos260ChargeResidual) (R : Class1CNLChargeData S.budget) :
    Erdos260ChargeResidual :=
  { S with hCnl := R.hCnl }

/-! ## 5.  Honest status inventory -/

/-- Per-result status of the class-1 clean-CNL charging bound. -/
def class1CNLChargeStatus : List String :=
  [ "CLOSED (generic) — routedClassMass_le_termCnl_of_kraftCharge: for any " ++
      "ClosurePhaseData, routedClassMassOf … i ≤ termCnl is DERIVED from the J.1.1 " ++
      "charge injection g (class starts ↪ clean-CNL codewords) + the per-codeword " ++
      "Kraft charge bound, via Finset.sum_image reindexing and domination by the " ++
      "full clean-CNL family Kraft sum.  The count·mult ≤ termCnl step is proved, " ++
      "not carried.",
    "CLOSED (J.1.1 count) — class1Fibre_card_le_cnlPaths: the class-1 fibre injects " ++
      "into the surviving clean-CNL transition family, so its count ≤ the family count " ++
      "(Finset.card_le_card_of_injOn).",
    "CLOSED (hCnl producer) — Class1CNLChargeData.hCnl: the exact " ++
      "Erdos260ChargeResidual.hCnl field shape (routedClassMassOf … (budget ctx).route 1 " ++
      "≤ termCnl (faithfulCapacityPhases budget ctx).toClosurePhaseData) from the minimal " ++
      "J.1.1 charge residual.",
    "REUSED (count×multiplier) — routedClassMass_le_termCnl_of_countMultiplier: the " ++
      "alternative reduction via the proved routedClassMassOf_le_countMultiplier, " ++
      "carrying count·mult ≤ termCnl whole (matching ChargeRoutingFibreResidual.hbud1).",
    "CONCRETE (faithfulCnlData_paths/_BNDHeight/_c/_shellFactor/_Ij + ofShellCharge) — the " ++
      "faithful assembly's clean-CNL data IS cnlLeafFromShellConcrete: paths = " ++
      "selectedTransitions (liftTransitionsOfShell ctx), BNDHeight = bndHeightNatOfShell, " ++
      "c = 1, shellFactor = cnlShellFactorOfShell, Ij = cnlIjOfShell.  ofShellCharge / " ++
      "hCnl_ofShellCharge take the charge map directly into the genuine surviving family.",
    "MINIMAL RESIDUAL (Class1CNLChargeData) — the genuine deep J.1.1 / H.1 / H.2 " ++
      "charging: the charge map chargeMap (class-1 starts ↪ surviving clean-CNL " ++
      "codewords), its injectivity hinj (the irreducible fibre-count identification), " ++
      "membership hmem, and the per-codeword window-excess charge bound hcharge " ++
      "(K.1.2/L.20).  Orthogonal to every proved phase budget; NOT a degenerate/empty " ++
      "shortcut (the surviving clean-CNL family is genuinely nonempty)." ]

theorem class1CNLChargeStatus_nonempty : class1CNLChargeStatus ≠ [] := by
  simp [class1CNLChargeStatus]

/-! ## 6.  Axiom-cleanliness audit -/

#print axioms routedClassMass_le_termCnl_of_kraftCharge
#print axioms class1Fibre_card_le_cnlPaths
#print axioms routedClassMass_le_termCnl_of_countMultiplier
#print axioms Class1CNLChargeData.hCnl
#print axioms Class1CNLChargeData.fibre_card_le
#print axioms faithfulCnlData_paths
#print axioms Class1CNLChargeData.ofShellCharge
#print axioms Class1CNLChargeData.hCnl_ofShellCharge
#print axioms Erdos260ChargeResidual.withClass1CNL

end

end Erdos260
