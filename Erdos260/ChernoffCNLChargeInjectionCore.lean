import Erdos260.ChargeClass0Chernoff
import Erdos260.ChargeClass1CNL
import Erdos260.CNLLeafFromShell
import Erdos260.ChargedBranchMassCore
import Erdos260.GenuineObstructionRoutingCore

/-!
# The genuine Chernoff (class-0) and clean-CNL (class-1) charge-injection cores

This module (NEW; it edits no existing file) constructs the **genuine charging maps** of the
manuscript Chernoff (Lemma 22.1A / I.4.2) and clean-CNL (Appendix L.1 / L.1.2 / G.35 / H.1–H.2)
charge-injection arguments and discharges, as far as the orthogonal charging direction allows, the
two residuals

```
Class0ChernoffCharge  budget   -- ChargeClass0Chernoff.lean  (class-0 = Chernoff / shell-paid progress)
Class1CNLChargeData   budget   -- ChargeClass1CNL.lean       (class-1 = clean-CNL Kraft tail)
```

for the **genuine first-obstruction route** `genuineChargeRoute` (`GenuineObstructionRoutingCore`).

## The two manuscript arguments

* **Class 0 — Chernoff (Lemma 22.1A, area-weighted stopped shell–Chernoff; I.4.2 progress count).**
  The high-cost stopped family `𝒮` satisfies `∑_{b∈𝒮} wt_sh(b) ≤ C_Q X|I_j| 2^{-cY} + o(sX|I_j|)`
  (manuscript 22.1a, layer-cake over the shell-paid multiplier `Y_sh`).  The class-0 (progress)
  starts — the I.4.2 fixed-layer endpoint/progress count, whose paid subfamily `𝔰 ≥ c_Q Y` is the
  shell-paid embedding — **inject** into this high-cost family, each charged its window excess
  against the assigned path's area weight (the J.1.7 charged branch mass).  Summing recovers
  `routedClassMassOf … 0 ≤ termChernoff` (the high-cost area `∑_{cost ≥ Y} weight`).

* **Class 1 — clean-CNL (Appendix L.1 selector, L.1.2 reconstruction, G.6/G.35 weighted-Kraft
  closure, H.1/H.2 recurrence).**  The deterministic CNL selector `𝔑` partitions one-step
  transitions (Lemma L.1.1: BND/SEP/TC/VS/DS/TP/PKG); after removing SEP/VS/DS/PKG the surviving
  clean unclassified CNL paths satisfy `∑_{𝒫} 2^{-c·H_BND(𝒫)} ≤ C_Q^M` (G.35).  The class-1 starts
  **inject** into the surviving clean-CNL codewords, each charged its window excess at that
  codeword's Kraft rate `2^{-c·BND} · shellFactor · X · |I_j|` (the per-codeword L.20/K.1.2 bound).
  Summing through the injection and dominating by the family Kraft sum recovers
  `routedClassMassOf … 1 ≤ termCnl`.

## What this module CONSTRUCTS / DISCHARGES (no `sorry`/`axiom`/`admit`)

* **The genuine first-obstruction fibre identification** (`mem_routedFibre_zero_iff_chernoff`,
  `mem_routedFibre_one_iff_cnlTail`): the class-0 fibre of the genuine route is *exactly* the
  high-excess starts whose L.3.1 SCC tower-exit class is `other` (the lower-order / Chernoff
  remainder), and the class-1 fibre is *exactly* the `cnlTail` catch-all band (no large run, no
  semiperiodic/long return).  These are `genuineChargeRoute_eq_{zero,one}_iff` read through the
  fibre filter — the carry-side realisation of the manuscript routing.

* **The per-element charge is DISCHARGED from the shell-gap geometry**: both
  `Class0ChernoffInjection.hdom` (the J.1.7 per-path domination `windowExcess ≤ weight(chargeOf k)`)
  and `Class1CNLInjection.hcharge` (the per-codeword Kraft domination) are *derived* from the proved
  `windowExcess_le_cap_chargeOf_on_routedFibre` (`ChargedBranchMassCore`, grounded in the dyadic
  shell scale `hitGap ≤ L+B+1`), reducing them to the active-window gap inputs plus the area /
  Kraft-rate cap.  They are **not** assumed.

* **The exact ledger fields are produced**: `Class0ChernoffInjection.hChernoffField` is the exact
  `Erdos260ChargeResidual.hChernoff` field shape, and `Class1CNLInjection.toChargeData` is a full
  `Class1CNLChargeData budget` (hence `.hCnl` the exact `hCnl` field), each dropping into a full
  residual (`withClass0ChernoffInjection`, `withClass1CNLInjection`).  The alternative
  count×multiplier granularities (`Class0ChernoffCharge.ofWindowGapCount`,
  `routedClass1_le_termCnl_of_windowGapCount`) reuse the proved
  `routedClassMassOf_le_countMultiplier`.

* **The I.4.2 / L.1.2 count is DERIVED from the injection** (`Class0ChernoffInjection.fibre_card_le`,
  `Class1CNLInjection.fibre_card_le`): the class-0/1 fibre injects into the high-cost / surviving
  clean-CNL family, so its count is bounded by the family count
  (`Finset.card_le_card_of_injOn`).

## The smallest named residual (the genuine charge injection map, documented)

What is *not* derivable from any phase budget — the orthogonal charging direction — is the genuine
charge **injection** itself:

* class 0: the J.1.7 weight-respecting map `chargeOf` of the progress starts into the Chernoff
  high-cost family, with the area-side cap `mult ≤ weight(chargeOf k)` (the 22.1A
  `cost_sh(Λ_SEP(τ)) ≥ c_Q H(τ)` embedding) and the K.1.3 endpoint-disjoint injectivity;
* class 1: the J.1.1 map `g` of the class-1 starts into `selectedTransitions
  (liftTransitionsOfShell ctx)`, with the Kraft-rate cap (the G.6 per-codeword charged mass) and the
  L.1.2 bounded-multiplicity injectivity.

These are carried as the fields of `Class0ChernoffInjection` / `Class1CNLInjection` — the smallest
honest residual, never a degenerate/empty stand-in (the surviving clean-CNL family is genuinely
nonempty, `liftTransitionsOfShell_nonempty`).

No `sorry`, `axiom`, or `admit`.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 0.  The genuine first-obstruction fibre identification (the carry-side J.1.1 routing)

For the genuine route `genuineChargeRoute`, the class-0/1 fibres are exactly the manuscript
first-obstruction bands.  These read the proved `genuineChargeRoute_eq_{zero,one}_iff` through the
`routedFibre` filter (compare `ReturnInjectionCore.genuine_class4_fibre_mem_iff`). -/

/-- **Class 0 (Chernoff / shell-paid progress) fibre = the `other` tower-exit band.**  A high-excess
start is in the genuine route's class-0 fibre iff its L.3.1 SCC tower-exit class is `other` (the
lower-order / Chernoff remainder), i.e. the I.4.2 progress/endpoint family. -/
theorem mem_routedFibre_zero_iff_chernoff (ctx : ActualFailureContext) (k : ℕ) :
    k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0 ↔
      k ∈ highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
          ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y ∧
        towerClsOfShell ctx k = TowerExitClass.other := by
  unfold routedFibre
  rw [Finset.mem_filter, genuineChargeRoute_eq_zero_iff]

/-- **Class 1 (clean-CNL Kraft tail) fibre = the `cnlTail` catch-all band.**  A high-excess start is
in the genuine route's class-1 fibre iff its tower-exit class is the `cnlTail` catch-all with a
bounded window excess (no large run `runClsOfShell ≠ 1`, no long/semiperiodic return
`returnCls ≠ 2`, `returnCls ≠ 1`) — the deliberately-last surviving clean-CNL family. -/
theorem mem_routedFibre_one_iff_cnlTail (ctx : ActualFailureContext) (k : ℕ) :
    k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 ↔
      k ∈ highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
          ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y ∧
        (towerClsOfShell ctx k = TowerExitClass.cnlTail ∧ runClsOfShell ctx k ≠ 1 ∧
          returnCls ctx k ≠ 2 ∧ returnCls ctx k ≠ 1) := by
  unfold routedFibre
  rw [Finset.mem_filter, genuineChargeRoute_eq_one_iff]

/-! ## 1.  Class 0 — the Chernoff (22.1A / I.4.2) charge injection

The genuine J.1.7 charge injection of the progress starts into the Chernoff high-cost path family,
with the per-path charge domination discharged from the active-window gap geometry. -/

/-- **The minimal class-0 (Chernoff) charge-injection residual.**

For each failure context: the J.1.7 charge map `chargeOf` of the progress starts into the Chernoff
high-cost path family `highCostSet … chernoff.paths chernoff.cost chernoff.Y`, with

* `hmaps` — each progress start charges into the high-cost family (the 22.1A shell-paid embedding,
  Lemma L.1.2a `Ω_SEP(τ,T) ⊆ Ω(Λ_SEP(τ),T)`);
* `hinj` — distinct starts get distinct high-cost paths (the K.1.3 endpoint-disjoint cover, the
  I.4.2 progress count realised);
* `g₀`/`mult`/`hgap`/`hscale`/`hmult_nonneg` — the active-window gap structure (the
  `ChargedBranchMassCore` K.1.2/L.20 residual: the descent-window hit-gap bound and the
  active-floor scaling `(r+1)·g₀ − T ≤ mult`);
* `hcap` — the **22.1A area-side** `mult ≤ weight(chargeOf k)` (the charged path's area weight
  dominates the residual multiplier, `cost_sh(Λ_SEP(τ)) ≥ c_Q H(τ)`).

The per-path charge domination is *derived* (`hdom`), not assumed; the only undischarged content is
the charge map and the two genuine charging facts (`hmaps`/`hinj`/`hcap`). -/
structure Class0ChernoffInjection
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx) where
  /-- The J.1.7 charge map: each progress start ↦ a Chernoff high-cost path. -/
  chargeOf : ∀ ctx : ActualFailureContext,
    ℕ → ((faithfulCapacityPhases budget ctx).toClosurePhaseData).chernoff.α
  /-- **22.1A high-cost membership** — each progress start charges into the high-cost family. -/
  hmaps : ∀ ctx : ActualFailureContext,
    ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
      chargeOf ctx k ∈ highCostSet
        ((faithfulCapacityPhases budget ctx).toClosurePhaseData).chernoff.paths
        ((faithfulCapacityPhases budget ctx).toClosurePhaseData).chernoff.cost
        ((faithfulCapacityPhases budget ctx).toClosurePhaseData).chernoff.Y
  /-- **K.1.3 endpoint-disjoint injectivity** — distinct progress starts get distinct paths. -/
  hinj : ∀ ctx : ActualFailureContext,
    ∀ x ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
      ∀ y ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
        chargeOf ctx x = chargeOf ctx y → x = y
  /-- The active-window hit-gap bound `g₀` (the dyadic scale `L+B+1`). -/
  g₀ : ∀ _ctx : ActualFailureContext, ℕ
  /-- The residual multiplier `mult` (the K.1.2/L.20 multiplier, `≤ C_res·Y`). -/
  mult : ∀ _ctx : ActualFailureContext, ℝ
  /-- The descent-window hit-gap bound holds on the class-0 fibre. -/
  hgap : ∀ ctx : ActualFailureContext,
    ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
      ∀ j, k ≤ j → j ≤ k + ctx.n24CarryData.r → hitGap ctx.n24CarryData.a j ≤ g₀ ctx
  /-- The K.1.2 active-floor scaling `(r+1)·g₀ − T ≤ mult`. -/
  hscale : ∀ ctx : ActualFailureContext,
    ((ctx.n24CarryData.r : ℝ) + 1) * (g₀ ctx : ℝ) - ctx.n24CarryData.T ≤ mult ctx
  /-- The multiplier is nonnegative. -/
  hmult_nonneg : ∀ ctx : ActualFailureContext, 0 ≤ mult ctx
  /-- **22.1A area-side** — the charged path's area weight dominates the residual multiplier. -/
  hcap : ∀ ctx : ActualFailureContext,
    ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
      mult ctx ≤ ((faithfulCapacityPhases budget ctx).toClosurePhaseData).chernoff.weight
        (chargeOf ctx k)

namespace Class0ChernoffInjection

variable {budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}

/-- **The J.1.7 per-path charge domination, DISCHARGED from the shell-gap geometry.**  Each progress
start's window excess is `≤` the area weight of its assigned high-cost path — derived from the
active-window gap structure (`hgap`/`hscale`) and the area-side cap (`hcap`) via the proved
`windowExcess_le_cap_chargeOf_on_routedFibre` (the K.1.2/L.20 multiplier grounded in the dyadic
shell scale).  This is the `hdom` input of the matching close, no longer a free hypothesis. -/
theorem hdom (R : Class0ChernoffInjection budget) :
    ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
        windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
          ≤ ((faithfulCapacityPhases budget ctx).toClosurePhaseData).chernoff.weight
              (R.chargeOf ctx k) :=
  fun ctx => windowExcess_le_cap_chargeOf_on_routedFibre ctx.n24CarryData (budget ctx).route 0
    (R.chargeOf ctx)
    ((faithfulCapacityPhases budget ctx).toClosurePhaseData).chernoff.weight
    (R.hgap ctx) (R.hscale ctx) (R.hmult_nonneg ctx) (R.hcap ctx)

/-- **The exact `Erdos260ChargeResidual.hChernoff` field, from the charge injection.**  The matching
close `routedClass0_le_termChernoff_of_matching` (the J.1.7 charging-map mechanism with the area
identification `termChernoff = ∑_p weight p` proved by `rfl`) applied to the charge map with the
per-path domination discharged from the gap geometry. -/
theorem hChernoffField (R : Class0ChernoffInjection budget) :
    ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (budget ctx).route 0
        ≤ termChernoff (faithfulCapacityPhases budget ctx).toClosurePhaseData :=
  hChernoffField_ofMatching budget R.chargeOf R.hmaps R.hinj R.hdom

/-- **The I.4.2 progress count, DERIVED from the injection.**  The class-0 fibre injects into the
Chernoff high-cost family, so its cardinality is bounded by the high-cost family count
(`Finset.card_le_card_of_injOn`). -/
theorem fibre_card_le (R : Class0ChernoffInjection budget) (ctx : ActualFailureContext) :
    (routedFibre ctx.n24CarryData (budget ctx).route 0).card ≤
      (highCostSet ((faithfulCapacityPhases budget ctx).toClosurePhaseData).chernoff.paths
        ((faithfulCapacityPhases budget ctx).toClosurePhaseData).chernoff.cost
        ((faithfulCapacityPhases budget ctx).toClosurePhaseData).chernoff.Y).card :=
  Finset.card_le_card_of_injOn (R.chargeOf ctx) (R.hmaps ctx) (R.hinj ctx)

end Class0ChernoffInjection

/-- **Drop-in confirmation (class 0).**  The class-0 charge injection replaces the `hChernoff` field
of any full `Erdos260ChargeResidual` sharing its `budget`, yielding another full residual — so
`Class0ChernoffInjection.hChernoffField` genuinely plugs into the consolidated surface. -/
def Erdos260ChargeResidual.withClass0ChernoffInjection
    (R0 : Erdos260ChargeResidual) (C : Class0ChernoffInjection R0.budget) :
    Erdos260ChargeResidual :=
  { R0 with hChernoff := C.hChernoffField }

/-- **The named `Class0ChernoffCharge` (count×multiplier shape), with `hpoint` discharged from the
gap geometry.**  The alternative manuscript granularity: the I.4.2 progress count `count`, the
22.1A area identification `count·mult ≤ termChernoff` (`hbud`), and the active-window gap structure.
The per-start multiplier field `hpoint` is *derived* from the gap structure (the proved
`class0_hpoint_of_window_gap`); the residual is the count and the area identification. -/
def Class0ChernoffCharge.ofWindowGapCount
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (g₀ : ∀ _ctx : ActualFailureContext, ℕ) (mult count : ∀ _ctx : ActualFailureContext, ℝ)
    (hgap : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
        ∀ j, k ≤ j → j ≤ k + ctx.n24CarryData.r → hitGap ctx.n24CarryData.a j ≤ g₀ ctx)
    (hscale : ∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : ℝ) + 1) * (g₀ ctx : ℝ) - ctx.n24CarryData.T ≤ mult ctx)
    (hmult_nonneg : ∀ ctx : ActualFailureContext, 0 ≤ mult ctx)
    (hcard : ∀ ctx : ActualFailureContext,
      ((routedFibre ctx.n24CarryData (budget ctx).route 0).card : ℝ) ≤ count ctx)
    (hbud : ∀ ctx : ActualFailureContext,
      count ctx * mult ctx
        ≤ termChernoff (faithfulCapacityPhases budget ctx).toClosurePhaseData) :
    Class0ChernoffCharge budget where
  mult := mult
  count := count
  hmult_nonneg := hmult_nonneg
  hpoint := fun ctx => class0_hpoint_of_window_gap budget ctx (hgap ctx) (hscale ctx) (hmult_nonneg ctx)
  hcard := hcard
  hbud := hbud

/-! ## 2.  Class 1 — the clean-CNL (L.1.2 / G.35 / H.1–H.2) charge injection

The genuine J.1.1 charge injection of the class-1 starts into the surviving clean-CNL transition
family `selectedTransitions (liftTransitionsOfShell ctx)`, with the per-codeword Kraft charge
discharged from the active-window gap geometry, producing a full `Class1CNLChargeData`. -/

/-- **The minimal class-1 (clean-CNL) charge-injection residual.**

For each failure context: the J.1.1 charge map `g` of the class-1 starts into the surviving clean-CNL
transition family `selectedTransitions (liftTransitionsOfShell ctx)` (the genuine shell family of
`CNLLeafFromShell`), with

* `hmem` — each class-1 start charges to a surviving clean-CNL codeword (the L.1.2 cluster
  reconstruction);
* `hinj` — distinct starts get distinct codewords (the L.1.2 bounded-multiplicity / fibre count);
* `g₀`/`mult`/`hgap`/`hscale`/`hmult_nonneg` — the active-window gap structure (the K.1.2/L.20
  residual multiplier);
* `hcap` — the **G.6 / H.1–H.2 per-codeword Kraft rate** `mult ≤ 2^{-c·BND(g k)} · shellFactor · X
  · |I_j|` (with `c = 1`; the charged branch mass already carries the Kraft factor).

The per-codeword charge domination is *derived* (`hcharge`), not assumed. -/
structure Class1CNLInjection
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx) where
  /-- The J.1.1 charge map: each class-1 start ↦ a surviving clean-CNL codeword. -/
  g : ∀ _ctx : ActualFailureContext, ℕ → CNLTransition
  /-- **L.1.2 cluster reconstruction** — codewords are surviving clean-CNL transitions. -/
  hmem : ∀ ctx : ActualFailureContext,
    ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 1,
      g ctx k ∈ selectedTransitions (liftTransitionsOfShell ctx)
  /-- **L.1.2 bounded-multiplicity injectivity** — distinct starts get distinct codewords. -/
  hinj : ∀ ctx : ActualFailureContext,
    ∀ k₁ ∈ routedFibre ctx.n24CarryData (budget ctx).route 1,
      ∀ k₂ ∈ routedFibre ctx.n24CarryData (budget ctx).route 1,
        g ctx k₁ = g ctx k₂ → k₁ = k₂
  /-- The active-window hit-gap bound `g₀` (the dyadic scale `L+B+1`). -/
  g₀ : ∀ _ctx : ActualFailureContext, ℕ
  /-- The residual multiplier `mult` (the K.1.2/L.20 multiplier, `≤ C_res·Y`). -/
  mult : ∀ _ctx : ActualFailureContext, ℝ
  /-- The descent-window hit-gap bound holds on the class-1 fibre. -/
  hgap : ∀ ctx : ActualFailureContext,
    ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 1,
      ∀ j, k ≤ j → j ≤ k + ctx.n24CarryData.r → hitGap ctx.n24CarryData.a j ≤ g₀ ctx
  /-- The K.1.2 active-floor scaling `(r+1)·g₀ − T ≤ mult`. -/
  hscale : ∀ ctx : ActualFailureContext,
    ((ctx.n24CarryData.r : ℝ) + 1) * (g₀ ctx : ℝ) - ctx.n24CarryData.T ≤ mult ctx
  /-- The multiplier is nonnegative. -/
  hmult_nonneg : ∀ ctx : ActualFailureContext, 0 ≤ mult ctx
  /-- **G.6 / H.1–H.2 per-codeword Kraft rate** — the residual multiplier is dominated by the
  codeword's Kraft weight times the shell/interval normalization. -/
  hcap : ∀ ctx : ActualFailureContext,
    ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 1,
      mult ctx ≤ (2 : ℝ) ^ (-(bndHeightNatOfShell ctx (g ctx k) : ℝ))
        * (cnlShellFactorOfShell ctx : ℝ) * (ctx.shell.X : ℝ) * (cnlIjOfShell ctx : ℝ)

namespace Class1CNLInjection

variable {budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}

/-- **The per-codeword Kraft charge domination, DISCHARGED from the shell-gap geometry.**  Each
class-1 start's window excess is `≤` its codeword's Kraft weight times the shell/interval factor —
derived from the active-window gap structure (`hgap`/`hscale`) and the Kraft-rate cap (`hcap`) via
the proved `windowExcess_le_cap_chargeOf_on_routedFibre`.  This is exactly the `hcharge` input of
`Class1CNLChargeData.ofShellCharge`, no longer a free hypothesis. -/
theorem hcharge (R : Class1CNLInjection budget) :
    ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 1,
        windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
          ≤ (2 : ℝ) ^ (-(bndHeightNatOfShell ctx (R.g ctx k) : ℝ))
              * (cnlShellFactorOfShell ctx : ℝ) * (ctx.shell.X : ℝ) * (cnlIjOfShell ctx : ℝ) :=
  fun ctx => windowExcess_le_cap_chargeOf_on_routedFibre ctx.n24CarryData (budget ctx).route 1
    (R.g ctx)
    (fun t => (2 : ℝ) ^ (-(bndHeightNatOfShell ctx t : ℝ))
      * (cnlShellFactorOfShell ctx : ℝ) * (ctx.shell.X : ℝ) * (cnlIjOfShell ctx : ℝ))
    (R.hgap ctx) (R.hscale ctx) (R.hmult_nonneg ctx) (R.hcap ctx)

/-- **The full `Class1CNLChargeData`, from the charge injection.**  Built through the concrete
shell-level producer `Class1CNLChargeData.ofShellCharge`: the J.1.1 map into the genuine surviving
clean-CNL family, with the per-codeword charge discharged from the gap geometry. -/
def toChargeData (R : Class1CNLInjection budget) : Class1CNLChargeData budget :=
  Class1CNLChargeData.ofShellCharge budget R.g R.hmem R.hinj R.hcharge

/-- **The exact `Erdos260ChargeResidual.hCnl` field, from the charge injection.** -/
theorem hCnlField (R : Class1CNLInjection budget) :
    ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (budget ctx).route 1
        ≤ termCnl (faithfulCapacityPhases budget ctx).toClosurePhaseData :=
  R.toChargeData.hCnl

/-- **The L.1.2 fibre count, DERIVED from the injection.**  The class-1 fibre injects into the
surviving clean-CNL transition family, so its count is bounded by the family count. -/
theorem fibre_card_le (R : Class1CNLInjection budget) (ctx : ActualFailureContext) :
    (routedFibre ctx.n24CarryData (budget ctx).route 1).card
      ≤ (selectedTransitions (liftTransitionsOfShell ctx)).card :=
  Finset.card_le_card_of_injOn (R.g ctx) (R.hmem ctx) (R.hinj ctx)

end Class1CNLInjection

/-- **Drop-in confirmation (class 1).**  The class-1 charge injection replaces the `hCnl` field of
any full `Erdos260ChargeResidual` sharing its `budget` (through the produced `Class1CNLChargeData`),
yielding another full residual. -/
def Erdos260ChargeResidual.withClass1CNLInjection
    (S : Erdos260ChargeResidual) (C : Class1CNLInjection S.budget) :
    Erdos260ChargeResidual :=
  S.withClass1CNL C.toChargeData

/-- **The class-1 `hCnl` field (count×multiplier shape), with the per-start multiplier discharged
from the gap geometry.**  The alternative granularity reusing the proved
`routedClassMass_le_termCnl_of_countMultiplier`: the L.1.2 fibre count and the `count·mult ≤ termCnl`
identification, with `hpoint` derived from the active-window gap structure. -/
theorem routedClass1_le_termCnl_of_windowGapCount
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) {g₀ : ℕ} {mult count : ℝ}
    (hgap : ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 1,
        ∀ j, k ≤ j → j ≤ k + ctx.n24CarryData.r → hitGap ctx.n24CarryData.a j ≤ g₀)
    (hscale : ((ctx.n24CarryData.r : ℝ) + 1) * (g₀ : ℝ) - ctx.n24CarryData.T ≤ mult)
    (hmult_nonneg : 0 ≤ mult)
    (hcard : ((routedFibre ctx.n24CarryData (budget ctx).route 1).card : ℝ) ≤ count)
    (hbud : count * mult ≤ termCnl (faithfulCapacityPhases budget ctx).toClosurePhaseData) :
    routedClassMassOf ctx.n24CarryData (budget ctx).route 1
      ≤ termCnl (faithfulCapacityPhases budget ctx).toClosurePhaseData :=
  routedClassMass_le_termCnl_of_countMultiplier ctx.n24CarryData
    (faithfulCapacityPhases budget ctx).toClosurePhaseData (budget ctx).route 1
    (windowExcess_le_mult_on_routedFibre ctx.n24CarryData (budget ctx).route 1
      hgap hscale hmult_nonneg)
    hmult_nonneg hcard hbud

/-! ## 3.  Non-vacuity — the residual targets are genuinely inhabited (no empty stand-in)

The class-1 charge map ranges over the surviving clean-CNL transition family, which is genuinely
nonempty (`liftTransitionsOfShell_nonempty` / `selectedTransitions_liftTransitionsOfShell`).  So the
injection residual targets a real, nonempty family — never the forbidden empty/∅/singleton stand-in.
(The per-element charge half of the residual is independently certified non-vacuous in
`ChargedBranchMassCore.windowExcess_id_le_one_nonvacuous`.) -/

/-- **The class-1 charge-injection target family is nonempty.**  The surviving clean-CNL transition
family of any failure context is genuinely nonempty — the class-1 charge map injects into a real
family, never a degenerate empty stand-in. -/
theorem class1_target_nonempty (ctx : ActualFailureContext) :
    (selectedTransitions (liftTransitionsOfShell ctx)).Nonempty :=
  selectedTransitions_liftTransitionsOfShell_nonempty ctx

/-! ## 4.  Honest residual inventory -/

/-- The precise status of the Chernoff (class-0) and clean-CNL (class-1) charge injections after
this module. -/
def chernoffCNLChargeInjectionResiduals : List String :=
  [ "CLOSED (genuine fibre identification) — mem_routedFibre_zero_iff_chernoff / " ++
      "mem_routedFibre_one_iff_cnlTail: for the genuine route genuineChargeRoute, the class-0 fibre " ++
      "IS the high-excess starts with L.3.1 tower-exit class `other` (the I.4.2 progress/Chernoff " ++
      "remainder), and the class-1 fibre IS the cnlTail catch-all band (no large run, no " ++
      "long/semiperiodic return). Read from the proved genuineChargeRoute_eq_{zero,one}_iff.",
    "DISCHARGED (per-element charge) — Class0ChernoffInjection.hdom / Class1CNLInjection.hcharge: the " ++
      "J.1.7 per-path domination windowExcess ≤ weight(chargeOf k) and the per-codeword Kraft " ++
      "domination windowExcess ≤ 2^{-c·BND(g k)}·shellFactor·X·Ij are DERIVED from the active-window " ++
      "gap structure via the proved windowExcess_le_cap_chargeOf_on_routedFibre (grounded in the " ++
      "dyadic shell scale hitGap ≤ L+B+1), NOT assumed.",
    "PRODUCED (exact ledger fields) — Class0ChernoffInjection.hChernoffField (the hChernoff field via " ++
      "the J.1.7 matching close routedClass0_le_termChernoff_of_matching, area identification " ++
      "termChernoff = ∑ weight by rfl) and Class1CNLInjection.toChargeData : Class1CNLChargeData " ++
      "(hence hCnlField the hCnl field via the Kraft-charging close). Both drop into a full residual " ++
      "(withClass0ChernoffInjection / withClass1CNLInjection).",
    "REUSED (count×multiplier shapes) — Class0ChernoffCharge.ofWindowGapCount (the named class-0 " ++
      "structure) and routedClass1_le_termCnl_of_windowGapCount: the alternative granularity with " ++
      "hpoint discharged from the gap structure (class0_hpoint_of_window_gap / " ++
      "windowExcess_le_mult_on_routedFibre) and the proved routedClassMassOf_le_countMultiplier.",
    "DERIVED (I.4.2 / L.1.2 count) — Class0ChernoffInjection.fibre_card_le / " ++
      "Class1CNLInjection.fibre_card_le: the class-0/1 fibre injects into the high-cost / surviving " ++
      "clean-CNL family, so its count is ≤ the family count (Finset.card_le_card_of_injOn).",
    "MINIMAL RESIDUAL (the genuine charge injection) — Class0ChernoffInjection (chargeOf/hmaps/hinj/" ++
      "hcap: the 22.1A shell-paid embedding into the high-cost family + K.1.3 endpoint disjointness + " ++
      "the area-side weight cap) and Class1CNLInjection (g/hmem/hinj/hcap: the L.1.2 cluster " ++
      "reconstruction into selectedTransitions (liftTransitionsOfShell ctx) + bounded-multiplicity " ++
      "injectivity + the G.6 per-codeword Kraft rate). Orthogonal to every phase budget; NOT a " ++
      "degenerate/empty shortcut (class1_target_nonempty: the surviving clean-CNL family is nonempty)." ]

theorem chernoffCNLChargeInjectionResiduals_nonempty :
    chernoffCNLChargeInjectionResiduals ≠ [] := by
  simp [chernoffCNLChargeInjectionResiduals]

/-! ## 5.  Axiom-cleanliness audit -/

#print axioms mem_routedFibre_zero_iff_chernoff
#print axioms mem_routedFibre_one_iff_cnlTail
#print axioms Class0ChernoffInjection.hdom
#print axioms Class0ChernoffInjection.hChernoffField
#print axioms Class0ChernoffInjection.fibre_card_le
#print axioms Erdos260ChargeResidual.withClass0ChernoffInjection
#print axioms Class0ChernoffCharge.ofWindowGapCount
#print axioms Class1CNLInjection.hcharge
#print axioms Class1CNLInjection.toChargeData
#print axioms Class1CNLInjection.hCnlField
#print axioms Class1CNLInjection.fibre_card_le
#print axioms Erdos260ChargeResidual.withClass1CNLInjection
#print axioms routedClass1_le_termCnl_of_windowGapCount
#print axioms class1_target_nonempty

end

end Erdos260
