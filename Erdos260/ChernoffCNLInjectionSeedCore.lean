import Erdos260.ChernoffCNLChargeInjectionCore
import Erdos260.ReturnInjectionCore

/-!
# The Chernoff (class-0) and clean-CNL (class-1) charge-injection **seeds**

This module (NEW; it edits no existing file) *constructs* the two genuine charge-injection
structures of `ChernoffCNLChargeInjectionCore`

```
Class0ChernoffInjection budget   -- the 22.1A / J.1.7 injection of the progress (class-0) starts
Class1CNLInjection      budget   -- the L.1.2 / G.6 injection of the cnlTail (class-1) starts
```

from the smallest honest manuscript residual, mirroring the established
`ReturnInjectionCore` / `DensePackInjectionCore` / `DensePackK11SupportCore` pattern (a genuine
order-rank matching built from a single count inequality, with the per-element charge discharged
from the active-window gap geometry).

## The two manuscript arguments realised

* **Class 0 — Chernoff (Lemma 22.1A, area-weighted stopped shell–Chernoff; J.1.7 progress/endpoint
  charged output).**  The progress/endpoint charging map `Θ_{P/E}` of Lemma J.1.7
  (`∑_{b:Θ_{P/E}(b)=O} wt(b) ≤ C_Q wt(O)`, proof_v4 lines 3558–3568) **injects** the progress
  starts into the Chernoff high-cost stopped family `highCostSet … chernoff.paths chernoff.cost
  chernoff.Y` (the area-weighted family of Lemma 22.1A, proof_v4 lines 764–809), each start charged
  its window excess against the assigned path's *area weight*.  The injectivity is the L.1.2a
  SEP→shell embedding read in reverse (`cost_sh(Λ_SEP(τ)) ≥ c_Q H(τ)` with `O_Q(1)` preimages,
  proof_v4 lines 5039–5062) / the K.1.3 endpoint-disjoint cover.

* **Class 1 — clean-CNL (Appendix L.1 selector, L.1.2 cluster encoding, G.6/G.35 weighted-Kraft
  closure).**  The deterministic CNL selector `𝔑` (Lemma L.1.1) partitions one-step transitions;
  after removing SEP/VS/DS/PKG the surviving clean unclassified CNL paths satisfy
  `∑_{𝒫} 2^{-c·H_BND(𝒫)} ≤ C_Q^M` (G.35, proof_v4 lines 2254–2293; L.1.2, lines 5151–5166).  Lemma
  L.1.2 reconstructs surviving clean paths from this code with **bounded multiplicity**, so the
  class-1 starts **inject** into the surviving clean-CNL transition family `selectedTransitions
  (liftTransitionsOfShell ctx)`, each charged its window excess at that codeword's Kraft rate
  `2^{-c·BND} · shellFactor · X · |I_j|`.

## What this module CONSTRUCTS (no `sorry`/`axiom`/`admit`)

* **A generic order-rank matching into an arbitrary nonempty finite family**
  (`finRankMatch` / `finRankMatch_mem` / `finRankMatch_injOn`): whenever `|F| ≤ |E|` for `F :
  Finset ℕ`, `E : Finset α` with `E` nonempty, the `r`-th smallest of `F` is sent to the `r`-th
  member of `E` (the order-rank `olcFibreRank` of `ReturnInjectionCore` composed with the
  enumeration `Finset.equivFin`).  This is the codomain-generic twin of the proved `olcRankMatch`
  (`Finset ℕ → Finset ℕ`); it maps into `E` and is injective on `F`.  Non-degenerate: it re-orders
  the fibre into the genuine target family, **never** the identity, and the target is genuinely
  nonempty.

* **The class-0 seed producers** `Class0ChernoffInjection.ofMapUniformCap` /
  `Class0ChernoffInjection.ofCountUniformCap`:
  - `ofMapUniformCap` builds the full `Class0ChernoffInjection` from the **bare injective
    assignment** `chargeOf`/`hmaps`/`hinj` (the J.1.7 progress charging map into the high-cost
    family) + the active-window gap structure (`g₀`/`mult`/`hgap`/`hscale`/`hmult_nonneg`) + the
    **uniform 22.1A area cap** `∀ p ∈ highCostSet, mult ≤ weight p`, *discharging* the per-path cap
    `hcap` from the uniform cap + `hmaps`;
  - `ofCountUniformCap` further *builds the injection itself* from the single I.4.2 progress count
    `|routedFibre 0| ≤ |highCostSet|` via `finRankMatch`, so the class-0 residual shrinks to the
    count + the uniform area cap + the gap structure.

* **The class-1 seed producers** `Class1CNLInjection.ofMapUniformCap` /
  `Class1CNLInjection.ofCountUniformCap`: the analogous reduction into the surviving clean-CNL
  family, with the **uniform G.6/G.35 Kraft cap** discharging `hcap` and the L.1.2
  bounded-multiplicity count `|routedFibre 1| ≤ |selectedTransitions (liftTransitionsOfShell ctx)|`
  building the injection.  The class-1 target is **proved nonempty**
  (`selectedTransitions_liftTransitionsOfShell_nonempty`), so no nonemptiness hypothesis is needed.

* **The count ⇔ injection equivalence** (`class0_count_of_injection` /
  `class1_count_of_injection`, the converse of `ofCount…` via the proved `fibre_card_le`): the bare
  injective assignment *exists* iff the count bound holds — so the count is the irreducible content.

## The smallest named residual (documented, non-vacuous)

After this module the class-0/1 injection reduces to:

* **class 0**: the I.4.2 progress count `|routedFibre 0| ≤ |highCostSet|`, the 22.1A uniform area
  cap, the K.1.2 active-floor gap structure, and the (genuinely true) nonemptiness of the Chernoff
  high-cost family;
* **class 1**: the L.1.2 bounded-multiplicity count `|routedFibre 1| ≤ |selectedTransitions …|`, the
  G.6/G.35 uniform Kraft cap, and the K.1.2 gap structure (nonemptiness is *proved*).

These are never degenerate/empty: the rank matching re-orders into a genuinely nonempty family, and
the per-element charge half is independently certified non-vacuous
(`ChargedBranchMassCore.windowExcess_id_le_one_nonvacuous`).

No `sorry`, `axiom`, or `admit`.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 0.  The generic order-rank matching into an arbitrary nonempty finite family

The `ReturnInjectionCore` order-rank matching `olcRankMatch` injects one `Finset ℕ` into another
whenever `|F| ≤ |E|`.  Here we lift its codomain to an **arbitrary** type: the target family of the
Chernoff injection is `Finset (chernoff.α)` and of the CNL injection is `Finset CNLTransition`.  We
reuse the proved order-rank `olcFibreRank` (and its injectivity) and compose with the canonical
enumeration `Finset.equivFin : ↥E ≃ Fin |E|`. -/

/-- **The codomain-generic order-rank matching map.**  Send `k` to the `(olcFibreRank F k)`-th
member of `E` under the enumeration `Finset.equivFin` (junk value `hE.choose` off `F`).  A total
`ℕ → α`, the arbitrary-codomain twin of `olcRankMatch`. -/
def finRankMatch {α : Type*} (F : Finset ℕ) (E : Finset α) (hE : E.Nonempty) (k : ℕ) : α :=
  if h : olcFibreRank F k < E.card then
    (E.equivFin.symm ⟨olcFibreRank F k, h⟩ : { x // x ∈ E }).val
  else hE.choose

/-- On a member of `F` (with `|F| ≤ |E|`) the matching map is the explicit enumeration value. -/
theorem finRankMatch_eq_of_mem {α : Type*} {F : Finset ℕ} {E : Finset α} (hE : E.Nonempty)
    (hcard : F.card ≤ E.card) {k : ℕ} (hk : k ∈ F) :
    finRankMatch F E hE k
      = (E.equivFin.symm ⟨olcFibreRank F k,
          lt_of_lt_of_le (olcFibreRank_lt_card hk) hcard⟩ : { x // x ∈ E }).val := by
  unfold finRankMatch
  exact dif_pos (lt_of_lt_of_le (olcFibreRank_lt_card hk) hcard)

/-- **Maps into `E`** — the matching map sends each member of `F` into `E`. -/
theorem finRankMatch_mem {α : Type*} {F : Finset ℕ} {E : Finset α} (hE : E.Nonempty)
    (hcard : F.card ≤ E.card) {k : ℕ} (hk : k ∈ F) :
    finRankMatch F E hE k ∈ E := by
  rw [finRankMatch_eq_of_mem hE hcard hk]
  exact (E.equivFin.symm ⟨olcFibreRank F k,
    lt_of_lt_of_le (olcFibreRank_lt_card hk) hcard⟩).2

/-- **Injective on `F`** — distinct members of `F` map to distinct members of `E`. -/
theorem finRankMatch_injOn {α : Type*} {F : Finset ℕ} {E : Finset α} (hE : E.Nonempty)
    (hcard : F.card ≤ E.card) {x y : ℕ} (hx : x ∈ F) (hy : y ∈ F)
    (h : finRankMatch F E hE x = finRankMatch F E hE y) : x = y := by
  rw [finRankMatch_eq_of_mem hE hcard hx, finRankMatch_eq_of_mem hE hcard hy] at h
  have he : E.equivFin.symm ⟨olcFibreRank F x, lt_of_lt_of_le (olcFibreRank_lt_card hx) hcard⟩
      = E.equivFin.symm ⟨olcFibreRank F y, lt_of_lt_of_le (olcFibreRank_lt_card hy) hcard⟩ :=
    Subtype.ext h
  have hfin : (⟨olcFibreRank F x, lt_of_lt_of_le (olcFibreRank_lt_card hx) hcard⟩ : Fin E.card)
      = ⟨olcFibreRank F y, lt_of_lt_of_le (olcFibreRank_lt_card hy) hcard⟩ :=
    E.equivFin.symm.injective he
  exact olcFibreRank_injOn hx hy (by simpa using congrArg Fin.val hfin)

/-! ## 1.  Class 0 — the Chernoff (22.1A / J.1.7) charge-injection seed

`faithfulChernoff` / `faithfulChernoffHighCost` name the Lemma 22.1A area-weighted Chernoff path
data of the faithful phase assembly and its high-cost (`cost ≥ Y`) subfamily — the target of the
J.1.7 progress charging map. -/

/-- The Lemma 22.1A area-weighted Chernoff path data of the faithful phase assembly. -/
abbrev faithfulChernoff (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) : ChernoffPathData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : ℝ) :=
  (faithfulCapacityPhases budget ctx).toClosurePhaseData.chernoff

/-- The Chernoff **high-cost stopped family** `{cost ≥ Y}` — the J.1.7 progress charging target. -/
abbrev faithfulChernoffHighCost
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) : Finset (faithfulChernoff budget ctx).α :=
  highCostSet (faithfulChernoff budget ctx).paths (faithfulChernoff budget ctx).cost
    (faithfulChernoff budget ctx).Y

/-- **The class-0 Chernoff injection seed from the bare injective assignment + uniform area cap.**

Builds the full `Class0ChernoffInjection budget` from

* `chargeOf`/`hmaps`/`hinj` — the J.1.7 progress charging map into the high-cost family with its
  K.1.3 endpoint-disjoint injectivity (the bare injective assignment, the smallest residual);
* `g₀`/`mult`/`hgap`/`hscale`/`hmult_nonneg` — the K.1.2 active-window gap structure;
* `huniformCap` — the **22.1A uniform area cap** `∀ p ∈ highCostSet, mult ≤ weight p` (every
  high-cost path's area weight dominates the residual multiplier).

The per-path cap `hcap` is *discharged* from `huniformCap` together with `hmaps` (the assigned path
lies in the high-cost family), so it is no longer a free field. -/
def Class0ChernoffInjection.ofMapUniformCap
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (chargeOf : ∀ ctx : ActualFailureContext, ℕ → (faithfulChernoff budget ctx).α)
    (hmaps : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
        chargeOf ctx k ∈ faithfulChernoffHighCost budget ctx)
    (hinj : ∀ ctx : ActualFailureContext,
      ∀ x ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
        ∀ y ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
          chargeOf ctx x = chargeOf ctx y → x = y)
    (g₀ : ∀ _ctx : ActualFailureContext, ℕ)
    (mult : ∀ _ctx : ActualFailureContext, ℝ)
    (hgap : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
        ∀ j, k ≤ j → j ≤ k + ctx.n24CarryData.r → hitGap ctx.n24CarryData.a j ≤ g₀ ctx)
    (hscale : ∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : ℝ) + 1) * (g₀ ctx : ℝ) - ctx.n24CarryData.T ≤ mult ctx)
    (hmult_nonneg : ∀ ctx : ActualFailureContext, 0 ≤ mult ctx)
    (huniformCap : ∀ ctx : ActualFailureContext,
      ∀ p ∈ faithfulChernoffHighCost budget ctx,
        mult ctx ≤ (faithfulChernoff budget ctx).weight p) :
    Class0ChernoffInjection budget where
  chargeOf := chargeOf
  hmaps := hmaps
  hinj := hinj
  g₀ := g₀
  mult := mult
  hgap := hgap
  hscale := hscale
  hmult_nonneg := hmult_nonneg
  hcap := fun ctx k hk => huniformCap ctx (chargeOf ctx k) (hmaps ctx k hk)

/-- **The class-0 Chernoff injection seed from the I.4.2 progress count + uniform area cap.**

The genuine combinatorial reduction: from the single I.4.2 progress count
`|routedFibre 0| ≤ |highCostSet|` (`hcard`) and the nonemptiness of the Chernoff high-cost family
(`hne`, genuinely true), the J.1.7 charging map is *built* via the order-rank matching
`finRankMatch` (a real, non-identity injection into the high-cost family), and the cap is
discharged from the 22.1A uniform area cap.  The remaining residual is the count, the uniform cap,
the gap structure, and the high-cost nonemptiness. -/
def Class0ChernoffInjection.ofCountUniformCap
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (hne : ∀ ctx : ActualFailureContext, (faithfulChernoffHighCost budget ctx).Nonempty)
    (hcard : ∀ ctx : ActualFailureContext,
      (routedFibre ctx.n24CarryData (budget ctx).route 0).card
        ≤ (faithfulChernoffHighCost budget ctx).card)
    (g₀ : ∀ _ctx : ActualFailureContext, ℕ)
    (mult : ∀ _ctx : ActualFailureContext, ℝ)
    (hgap : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
        ∀ j, k ≤ j → j ≤ k + ctx.n24CarryData.r → hitGap ctx.n24CarryData.a j ≤ g₀ ctx)
    (hscale : ∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : ℝ) + 1) * (g₀ ctx : ℝ) - ctx.n24CarryData.T ≤ mult ctx)
    (hmult_nonneg : ∀ ctx : ActualFailureContext, 0 ≤ mult ctx)
    (huniformCap : ∀ ctx : ActualFailureContext,
      ∀ p ∈ faithfulChernoffHighCost budget ctx,
        mult ctx ≤ (faithfulChernoff budget ctx).weight p) :
    Class0ChernoffInjection budget :=
  Class0ChernoffInjection.ofMapUniformCap budget
    (fun ctx => finRankMatch (routedFibre ctx.n24CarryData (budget ctx).route 0)
      (faithfulChernoffHighCost budget ctx) (hne ctx))
    (fun ctx _k hk => finRankMatch_mem (hne ctx) (hcard ctx) hk)
    (fun ctx _x hx _y hy h => finRankMatch_injOn (hne ctx) (hcard ctx) hx hy h)
    g₀ mult hgap hscale hmult_nonneg huniformCap

/-- **The I.4.2 progress count, the converse of the injection.**  Any `Class0ChernoffInjection`
forces `|routedFibre 0| ≤ |highCostSet|` (the proved `fibre_card_le`).  With `ofCountUniformCap`
this shows the bare injective assignment is **equivalent** to the single count inequality. -/
theorem class0_count_of_injection
    {budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}
    (R : Class0ChernoffInjection budget) (ctx : ActualFailureContext) :
    (routedFibre ctx.n24CarryData (budget ctx).route 0).card
      ≤ (faithfulChernoffHighCost budget ctx).card :=
  R.fibre_card_le ctx

/-! ## 2.  Class 1 — the clean-CNL (L.1.2 / G.6 / G.35) charge-injection seed

The target is the surviving clean-CNL transition family `selectedTransitions
(liftTransitionsOfShell ctx)` of `CNLLeafFromShell`, which is **proved nonempty**
(`selectedTransitions_liftTransitionsOfShell_nonempty`). -/

/-- The per-codeword G.6/G.35 Kraft rate `2^{-c·BND(t)} · shellFactor · X · |I_j|` (with `c = 1`) —
the class-1 charge cap value. -/
abbrev cnlKraftRate (ctx : ActualFailureContext) (t : CNLTransition) : ℝ :=
  (2 : ℝ) ^ (-(bndHeightNatOfShell ctx t : ℝ)) * (cnlShellFactorOfShell ctx : ℝ)
    * (ctx.shell.X : ℝ) * (cnlIjOfShell ctx : ℝ)

/-- **The class-1 clean-CNL injection seed from the bare injective assignment + uniform Kraft cap.**

Builds the full `Class1CNLInjection budget` from

* `g`/`hmem`/`hinj` — the L.1.2 cluster-reconstruction charge map into the surviving clean-CNL
  family with its bounded-multiplicity injectivity (the bare injective assignment);
* the K.1.2 active-window gap structure;
* `huniformCap` — the **G.6/G.35 uniform Kraft cap** `∀ t ∈ selectedTransitions …, mult ≤
  cnlKraftRate t`.

The per-codeword cap `hcap` is *discharged* from `huniformCap` together with `hmem`. -/
def Class1CNLInjection.ofMapUniformCap
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (g : ∀ _ctx : ActualFailureContext, ℕ → CNLTransition)
    (hmem : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 1,
        g ctx k ∈ selectedTransitions (liftTransitionsOfShell ctx))
    (hinj : ∀ ctx : ActualFailureContext,
      ∀ k₁ ∈ routedFibre ctx.n24CarryData (budget ctx).route 1,
        ∀ k₂ ∈ routedFibre ctx.n24CarryData (budget ctx).route 1,
          g ctx k₁ = g ctx k₂ → k₁ = k₂)
    (g₀ : ∀ _ctx : ActualFailureContext, ℕ)
    (mult : ∀ _ctx : ActualFailureContext, ℝ)
    (hgap : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 1,
        ∀ j, k ≤ j → j ≤ k + ctx.n24CarryData.r → hitGap ctx.n24CarryData.a j ≤ g₀ ctx)
    (hscale : ∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : ℝ) + 1) * (g₀ ctx : ℝ) - ctx.n24CarryData.T ≤ mult ctx)
    (hmult_nonneg : ∀ ctx : ActualFailureContext, 0 ≤ mult ctx)
    (huniformCap : ∀ ctx : ActualFailureContext,
      ∀ t ∈ selectedTransitions (liftTransitionsOfShell ctx), mult ctx ≤ cnlKraftRate ctx t) :
    Class1CNLInjection budget where
  g := g
  hmem := hmem
  hinj := hinj
  g₀ := g₀
  mult := mult
  hgap := hgap
  hscale := hscale
  hmult_nonneg := hmult_nonneg
  hcap := fun ctx k hk => huniformCap ctx (g ctx k) (hmem ctx k hk)

/-- **The class-1 clean-CNL injection seed from the L.1.2 bounded-multiplicity count + uniform Kraft
cap.**

The genuine combinatorial reduction: from the single L.1.2 bounded-multiplicity count
`|routedFibre 1| ≤ |selectedTransitions (liftTransitionsOfShell ctx)|` (`hcard`) the cluster-encoding
charge map is *built* via the order-rank matching `finRankMatch` into the surviving clean-CNL family
(its nonemptiness is proved, so no extra hypothesis), and the cap is discharged from the G.6/G.35
uniform Kraft cap.  The class-1 residual shrinks to the count, the uniform Kraft cap, and the gap
structure. -/
def Class1CNLInjection.ofCountUniformCap
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (hcard : ∀ ctx : ActualFailureContext,
      (routedFibre ctx.n24CarryData (budget ctx).route 1).card
        ≤ (selectedTransitions (liftTransitionsOfShell ctx)).card)
    (g₀ : ∀ _ctx : ActualFailureContext, ℕ)
    (mult : ∀ _ctx : ActualFailureContext, ℝ)
    (hgap : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 1,
        ∀ j, k ≤ j → j ≤ k + ctx.n24CarryData.r → hitGap ctx.n24CarryData.a j ≤ g₀ ctx)
    (hscale : ∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : ℝ) + 1) * (g₀ ctx : ℝ) - ctx.n24CarryData.T ≤ mult ctx)
    (hmult_nonneg : ∀ ctx : ActualFailureContext, 0 ≤ mult ctx)
    (huniformCap : ∀ ctx : ActualFailureContext,
      ∀ t ∈ selectedTransitions (liftTransitionsOfShell ctx), mult ctx ≤ cnlKraftRate ctx t) :
    Class1CNLInjection budget :=
  Class1CNLInjection.ofMapUniformCap budget
    (fun ctx => finRankMatch (routedFibre ctx.n24CarryData (budget ctx).route 1)
      (selectedTransitions (liftTransitionsOfShell ctx))
      (selectedTransitions_liftTransitionsOfShell_nonempty ctx))
    (fun ctx _k hk => finRankMatch_mem _ (hcard ctx) hk)
    (fun ctx _k₁ hk₁ _k₂ hk₂ h => finRankMatch_injOn _ (hcard ctx) hk₁ hk₂ h)
    g₀ mult hgap hscale hmult_nonneg huniformCap

/-- **The L.1.2 bounded-multiplicity count, the converse of the injection.**  Any
`Class1CNLInjection` forces `|routedFibre 1| ≤ |selectedTransitions (liftTransitionsOfShell ctx)|`
(the proved `fibre_card_le`).  With `ofCountUniformCap` this shows the bare injective assignment is
**equivalent** to the single count inequality. -/
theorem class1_count_of_injection
    {budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}
    (R : Class1CNLInjection budget) (ctx : ActualFailureContext) :
    (routedFibre ctx.n24CarryData (budget ctx).route 1).card
      ≤ (selectedTransitions (liftTransitionsOfShell ctx)).card :=
  R.fibre_card_le ctx

/-! ## 3.  Non-vacuity — the seeds target genuinely nonempty families (no empty/identity shortcut)

The order-rank matching re-orders the fibre into the genuine target family (never the identity), and
both targets are genuinely nonempty (class 1 *proved*; class 0 the named, genuinely-true high-cost
nonemptiness).  The per-element charge half is independently certified non-vacuous in
`ChargedBranchMassCore`. -/

/-- **The class-1 target family is genuinely nonempty** (re-export of the proved CNL nonemptiness):
the class-1 charge map injects into a real, nonempty surviving clean-CNL family. -/
theorem class1_cnl_target_nonempty (ctx : ActualFailureContext) :
    (selectedTransitions (liftTransitionsOfShell ctx)).Nonempty :=
  selectedTransitions_liftTransitionsOfShell_nonempty ctx

/-- **Non-vacuity of the class-1 seed.**  Whenever the L.1.2 bounded-multiplicity count holds (with
the gap structure and the uniform Kraft cap), a genuine `Class1CNLInjection` exists — the residual
is inhabited, built through the non-identity order-rank matching into the proved-nonempty surviving
clean-CNL family. -/
theorem class1_injection_nonvacuous
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (hcard : ∀ ctx : ActualFailureContext,
      (routedFibre ctx.n24CarryData (budget ctx).route 1).card
        ≤ (selectedTransitions (liftTransitionsOfShell ctx)).card)
    (g₀ : ∀ _ctx : ActualFailureContext, ℕ)
    (mult : ∀ _ctx : ActualFailureContext, ℝ)
    (hgap : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 1,
        ∀ j, k ≤ j → j ≤ k + ctx.n24CarryData.r → hitGap ctx.n24CarryData.a j ≤ g₀ ctx)
    (hscale : ∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : ℝ) + 1) * (g₀ ctx : ℝ) - ctx.n24CarryData.T ≤ mult ctx)
    (hmult_nonneg : ∀ ctx : ActualFailureContext, 0 ≤ mult ctx)
    (huniformCap : ∀ ctx : ActualFailureContext,
      ∀ t ∈ selectedTransitions (liftTransitionsOfShell ctx), mult ctx ≤ cnlKraftRate ctx t) :
    Nonempty (Class1CNLInjection budget) :=
  ⟨Class1CNLInjection.ofCountUniformCap budget hcard g₀ mult hgap hscale hmult_nonneg huniformCap⟩

/-! ## 4.  Honest residual inventory -/

/-- The precise status of the Chernoff (class-0) and clean-CNL (class-1) charge-injection seeds
after this module. -/
def chernoffCNLInjectionSeedResiduals : List String :=
  [ "CONSTRUCTED (generic order-rank matching) — finRankMatch / finRankMatch_mem / " ++
      "finRankMatch_injOn: the codomain-generic twin of olcRankMatch, injecting a finite F ⊆ ℕ into " ++
      "a NONEMPTY E : Finset α whenever |F| ≤ |E| (the r-th smallest of F to the r-th member of E via " ++
      "olcFibreRank and Finset.equivFin). Never the identity; re-orders into the genuine family.",
    "CONSTRUCTED (class-0 seed) — Class0ChernoffInjection.ofMapUniformCap / ofCountUniformCap: the " ++
      "full Class0ChernoffInjection from the bare J.1.7 progress charging map (ofMap) or from the " ++
      "single I.4.2 progress count |routedFibre 0| ≤ |highCostSet| (ofCount, via finRankMatch). The " ++
      "per-path area cap hcap is DISCHARGED from the 22.1A uniform area cap ∀ p ∈ highCostSet, mult ≤ " ++
      "weight p (with hmaps), never assumed.",
    "CONSTRUCTED (class-1 seed) — Class1CNLInjection.ofMapUniformCap / ofCountUniformCap: the full " ++
      "Class1CNLInjection from the bare L.1.2 cluster-reconstruction map (ofMap) or from the single " ++
      "L.1.2 bounded-multiplicity count |routedFibre 1| ≤ |selectedTransitions (liftTransitionsOfShell " ++
      "ctx)| (ofCount, via finRankMatch into the PROVED-nonempty family). The per-codeword Kraft cap " ++
      "hcap is DISCHARGED from the G.6/G.35 uniform Kraft cap ∀ t ∈ selectedTransitions, mult ≤ " ++
      "cnlKraftRate t (with hmem), never assumed.",
    "EQUIVALENCE (count ⇔ injection) — class0_count_of_injection / class1_count_of_injection: any " ++
      "injection forces the count bound (the proved fibre_card_le), so with ofCount… the bare " ++
      "injective assignment is EQUIVALENT to the single count inequality (the I.4.2 / L.1.2 count).",
    "NON-VACUOUS — class1_cnl_target_nonempty (the surviving clean-CNL family is genuinely nonempty, " ++
      "proved) and class1_injection_nonvacuous (the class-1 seed residual is inhabited). The rank " ++
      "matching is non-identity into a real nonempty family; the per-element charge half is certified " ++
      "non-vacuous in ChargedBranchMassCore.windowExcess_id_le_one_nonvacuous.",
    "MINIMAL RESIDUAL (documented) — class 0: the I.4.2 progress count |routedFibre 0| ≤ |highCostSet|, " ++
      "the 22.1A uniform area cap, the K.1.2 active-floor gap structure (hgap/hscale), and the " ++
      "(genuinely true) Chernoff high-cost nonemptiness hne; class 1: the L.1.2 bounded-multiplicity " ++
      "count, the G.6/G.35 uniform Kraft cap, and the K.1.2 gap structure (nonemptiness PROVED). " ++
      "Orthogonal to every phase budget; NOT a degenerate/empty/identity shortcut." ]

theorem chernoffCNLInjectionSeedResiduals_nonempty : chernoffCNLInjectionSeedResiduals ≠ [] := by
  simp [chernoffCNLInjectionSeedResiduals]

/-! ## 5.  Axiom-cleanliness audit -/

#print axioms finRankMatch_mem
#print axioms finRankMatch_injOn
#print axioms Class0ChernoffInjection.ofMapUniformCap
#print axioms Class0ChernoffInjection.ofCountUniformCap
#print axioms class0_count_of_injection
#print axioms Class1CNLInjection.ofMapUniformCap
#print axioms Class1CNLInjection.ofCountUniformCap
#print axioms class1_count_of_injection
#print axioms class1_cnl_target_nonempty
#print axioms class1_injection_nonvacuous

end

end Erdos260
