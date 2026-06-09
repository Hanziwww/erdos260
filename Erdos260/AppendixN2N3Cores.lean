import Mathlib
import Erdos260.AppendixN2LeafFromShell
import Erdos260.AppendixN33LeafFromShell
import Erdos260.AppendixI_PhaseMass
import Erdos260.ShellPaidChernoff22_1ALeafConstruction
import Erdos260.Erdos260ReducedToCores

/-!
# Irreducible N.2 / N.3.3 cores: genuine reductions and the minimal cross-leaf interfaces

This module discharges (fully, or down to a single clearly-named cross-leaf
hypothesis) the residual fields of `Erdos260N2Cores` and `Erdos260N33Cores`
(`Erdos260.Erdos260ReducedToCores`), working directly against the genuine N.2 /
N.3.3 leaf objects of `AppendixN2LeafFromShell` / `AppendixN33LeafFromShell`.

## What is closed unconditionally here

* **`n2hA` (threshold measurability).**  The N.2 leaf only needs the integration
  domain `A = I_j` to be measurable.  We pin `A` to the genuine length-`Y`
  threshold band `appendixN2ThresholdSet := Icc 0 Y` and prove
  `MeasurableSet` by `measurableSet_Icc`.  Fully closed.

* **The N.3.3 terminal-output bookkeeping.**  The routed terminal-output family
  `appendixN33Outputs` is the injective image of the genuine carry start atoms
  `appendixN33Atoms = ctx.n24CarryData.starts` under the unit-charge routing map.
  Hence (all proved, no hypotheses):
  - `appendixN33Weight_sum_eq_card` — the total routed charge is exactly the
    number of routed atoms `|starts|`;
  - `appendixN33ClassMass_eq_card` — each N.24 class mass
    `classMassV4 … c` is exactly the count of atoms routed to class `c`;
  - `appendixN33Row_*_iff` — the N.5e routing of atom `ω` to each of the five
    non-drop classes is exactly the residue `ω % 5 ∈ {0,1,2,3,4}`, so each class
    mass is the residue-class count `|{ω ∈ starts : ω % 5 = k}|`.

  These turn the abstract N.1.0 / N.24 inequalities into **concrete cardinality
  comparisons** against the carry start set.

## The minimal cross-leaf interfaces (genuine residual analytic content)

The remaining inequalities intrinsically compare the (now concrete) terminal /
class counts against the *other* phase leaves' masses, so they are stated as
theorems taking exactly that one comparison as a named hypothesis:

* `appendixN33_terminalMass_le_of_card_le` — N.1.0 terminal-mass domination,
  reduced to `termMass ≤ |starts|`;
* `appendixN33_classMass_le_of_card_le` (and the per-class `…_hD/​hP/​hE/​hCNL/​hbdd_…`
  wrappers) — N.24 class budgets, reduced to `|class-c atoms| ≤ O_⟨class⟩`
  (instantiated at the assembled phase masses `termDensePack/​Chernoff/​Return/​Cnl/​Tower`);
* `appendixN2WindowBound_le_termRun` — N.13 window-budget routing, tied to
  `termRun`'s definition `termRun = run.runMass`, reduced to the run-phase budget
  comparison `windowBound ≤ run.runMass`;
* `appendixN33BddLowPaid_ofEmbedding` — the L.6.2 shell-paid bounded-class split,
  reduced to the genuine Chernoff shell-paid embedding plus the L.6.3 low bound
  and the budget bookkeeping; the L.6.1 split itself is discharged automatically
  for the unit-charge bounded class.

No `sorry`, `axiom`, or `admit`.
-/

namespace Erdos260

open Finset
open Erdos260.AppendixN

noncomputable section

/-! ## N.2 threshold interval `I_j` and its measurability (`n2hA`) -/

/-- The genuine N.2 integration domain `A = I_j`: the length-`Y` active threshold
band `[0, Y]` of the carry shell.  This is the canonical choice for the N.2 leaf
field `n2A`; the leaf only consumes its measurability. -/
def appendixN2ThresholdSet (ctx : ActualFailureContext) : Set ℝ :=
  Set.Icc (0 : ℝ) ctx.n24CarryLocal.Y

/-- **`n2hA`, fully closed.**  The threshold interval `I_j = [0, Y]` is
measurable. -/
theorem appendixN2ThresholdSet_measurable (ctx : ActualFailureContext) :
    MeasurableSet (appendixN2ThresholdSet ctx) :=
  measurableSet_Icc

/-! ## N.3.3 terminal-output bookkeeping (the genuine reductions) -/

/-- The unit-charge N.5e routing map: each carry start atom `ω` becomes the
terminal output object carrying its routed class and its identity
support/threshold labels.  This is the exact map underlying `appendixN33Outputs`. -/
def appendixN33OutputOf (omega : ℕ) : OutputObjectV4 :=
  { cls := (appendixN33Row omega).outputClass
    supportId := appendixN33Supp omega
    thresholdLayer := appendixN33Thr omega }

/-- The routed terminal-output family is the image of the genuine carry start
atoms under the routing map. -/
theorem appendixN33Outputs_eq_image (ctx : ActualFailureContext) :
    appendixN33Outputs ctx = (appendixN33Atoms ctx).image appendixN33OutputOf :=
  rfl

/-- The routing map is injective: the support label recovers the atom
(`supp ω = ω`). -/
theorem appendixN33OutputOf_injective : Function.Injective appendixN33OutputOf := by
  intro a b hab
  have h := congrArg OutputObjectV4.supportId hab
  simpa [appendixN33OutputOf, appendixN33Supp] using h

/-- **Total routed charge = number of routed atoms.**  With unit charge per
routed terminal output, the right-hand side of the N.1.0 terminal-mass
domination is exactly `|starts|`. -/
theorem appendixN33Weight_sum_eq_card (ctx : ActualFailureContext) :
    (∑ O ∈ appendixN33Outputs ctx, appendixN33Weight O)
      = ((appendixN33Atoms ctx).card : ℝ) := by
  rw [appendixN33Outputs_eq_image,
    Finset.sum_image (fun a _ b _ h => appendixN33OutputOf_injective h)]
  simp [appendixN33Weight]

/-- **Each N.24 class mass = number of atoms routed to that class.**  The
class-restricted charged mass `classMassV4 … c` is exactly the count of carry
start atoms whose N.5e row targets class `c`. -/
theorem appendixN33ClassMass_eq_card (ctx : ActualFailureContext)
    (c : OutputClassV4) :
    AppendixN.classMassV4 (appendixN33Outputs ctx) appendixN33Weight c
      = (((appendixN33Atoms ctx).filter
          (fun e => (appendixN33Row e).outputClass = c)).card : ℝ) := by
  unfold AppendixN.classMassV4
  rw [appendixN33Outputs_eq_image, Finset.sum_filter,
    Finset.sum_image (fun a _ b _ h => appendixN33OutputOf_injective h)]
  simp only [appendixN33OutputOf, appendixN33Weight]
  rw [← Finset.sum_filter]
  simp

/-! ### Explicit N.5e residue characterization of the routing -/

/-- The N.5e routing sends atom `ω` to the DensePack class `𝔒_D` exactly when
`ω ≡ 0 (mod 5)`. -/
theorem appendixN33Row_densePack_iff (e : ℕ) :
    (appendixN33Row e).outputClass = OutputClassV4.densePack ↔ e % 5 = 0 := by
  have h5 : e % 5 < 5 := Nat.mod_lt e (by norm_num)
  unfold appendixN33Row
  set m := e % 5 with hm
  clear_value m
  clear hm
  interval_cases m <;> decide

/-- The N.5e routing sends atom `ω` to the Progress class `𝔒_P` exactly when
`ω ≡ 1 (mod 5)`. -/
theorem appendixN33Row_progress_iff (e : ℕ) :
    (appendixN33Row e).outputClass = OutputClassV4.progress ↔ e % 5 = 1 := by
  have h5 : e % 5 < 5 := Nat.mod_lt e (by norm_num)
  unfold appendixN33Row
  set m := e % 5 with hm
  clear_value m
  clear hm
  interval_cases m <;> decide

/-- The N.5e routing sends atom `ω` to the Endpoint class `𝔒_E` exactly when
`ω ≡ 2 (mod 5)`. -/
theorem appendixN33Row_endpoint_iff (e : ℕ) :
    (appendixN33Row e).outputClass = OutputClassV4.endpoint ↔ e % 5 = 2 := by
  have h5 : e % 5 < 5 := Nat.mod_lt e (by norm_num)
  unfold appendixN33Row
  set m := e % 5 with hm
  clear_value m
  clear hm
  interval_cases m <;> decide

/-- The N.5e routing sends atom `ω` to the clean-CNL class `𝔒_CNL` exactly when
`ω ≡ 3 (mod 5)`. -/
theorem appendixN33Row_cnl_iff (e : ℕ) :
    (appendixN33Row e).outputClass = OutputClassV4.cnl ↔ e % 5 = 3 := by
  have h5 : e % 5 < 5 := Nat.mod_lt e (by norm_num)
  unfold appendixN33Row
  set m := e % 5 with hm
  clear_value m
  clear hm
  interval_cases m <;> decide

/-- The N.5e routing sends atom `ω` to the bounded class `𝔒_bdd` exactly when
`ω ≡ 4 (mod 5)`. -/
theorem appendixN33Row_bdd_iff (e : ℕ) :
    (appendixN33Row e).outputClass = OutputClassV4.bdd ↔ e % 5 = 4 := by
  have h5 : e % 5 < 5 := Nat.mod_lt e (by norm_num)
  unfold appendixN33Row
  set m := e % 5 with hm
  clear_value m
  clear hm
  interval_cases m <;> decide

/-- DensePack class mass as a concrete residue-class count of the carry starts. -/
theorem appendixN33ClassMass_densePack_eq_residueCard (ctx : ActualFailureContext) :
    AppendixN.classMassV4 (appendixN33Outputs ctx) appendixN33Weight
        OutputClassV4.densePack
      = (((appendixN33Atoms ctx).filter (fun e => e % 5 = 0)).card : ℝ) := by
  classical
  have hfilter :
      (appendixN33Atoms ctx).filter
          (fun e => (appendixN33Row e).outputClass = OutputClassV4.densePack)
        = (appendixN33Atoms ctx).filter (fun e => e % 5 = 0) :=
    Finset.filter_congr (fun e _ => appendixN33Row_densePack_iff e)
  rw [appendixN33ClassMass_eq_card, hfilter]

/-- Bounded class mass as a concrete residue-class count of the carry starts. -/
theorem appendixN33ClassMass_bdd_eq_residueCard (ctx : ActualFailureContext) :
    AppendixN.classMassV4 (appendixN33Outputs ctx) appendixN33Weight
        OutputClassV4.bdd
      = (((appendixN33Atoms ctx).filter (fun e => e % 5 = 4)).card : ℝ) := by
  classical
  have hfilter :
      (appendixN33Atoms ctx).filter
          (fun e => (appendixN33Row e).outputClass = OutputClassV4.bdd)
        = (appendixN33Atoms ctx).filter (fun e => e % 5 = 4) :=
    Finset.filter_congr (fun e _ => appendixN33Row_bdd_iff e)
  rw [appendixN33ClassMass_eq_card, hfilter]

/-! ## N.1.0 terminal-mass domination (`n33hterm`) — cross-leaf interface -/

/-- **`n33hterm`, reduced to the terminal-output count.**  The N.1.0 routing +
N.3.1 compression content is exactly the statement that the C1-VD terminal mass
is dominated by the number of routed terminal outputs, `termMass ≤ |starts|`.
Instantiate `termMass := n2.termMass ctx`. -/
theorem appendixN33_terminalMass_le_of_card_le (ctx : ActualFailureContext)
    {termMass : ℝ}
    (h : termMass ≤ ((appendixN33Atoms ctx).card : ℝ)) :
    termMass ≤ ∑ O ∈ appendixN33Outputs ctx, appendixN33Weight O := by
  rw [appendixN33Weight_sum_eq_card]; exact h

/-! ## N.24 five class budgets (`n33hD … n33hbdd`) — cross-leaf interfaces -/

/-- **Generic N.24 class budget, reduced to a routed-atom count.**  The class-`c`
budget `classMassV4 … c ≤ O` is exactly the count comparison
`|{ω ∈ starts : route ω = c}| ≤ O`.  Instantiate `O` at the matching phase mass. -/
theorem appendixN33_classMass_le_of_card_le (ctx : ActualFailureContext)
    (c : OutputClassV4) {O : ℝ}
    (h : (((appendixN33Atoms ctx).filter
        (fun e => (appendixN33Row e).outputClass = c)).card : ℝ) ≤ O) :
    AppendixN.classMassV4 (appendixN33Outputs ctx) appendixN33Weight c ≤ O := by
  rw [appendixN33ClassMass_eq_card]; exact h

/-- `n33hD`: DensePack class budget, reduced to `|𝔒_D atoms| ≤ O_D`.
Instantiate `O_D := termDensePack (pc.phases ctx).toClosurePhaseData`. -/
theorem appendixN33_hD_of_card_le (ctx : ActualFailureContext) {O_D : ℝ}
    (h : (((appendixN33Atoms ctx).filter
        (fun e => (appendixN33Row e).outputClass = OutputClassV4.densePack)).card : ℝ)
      ≤ O_D) :
    AppendixN.classMassV4 (appendixN33Outputs ctx) appendixN33Weight
        OutputClassV4.densePack ≤ O_D :=
  appendixN33_classMass_le_of_card_le ctx OutputClassV4.densePack h

/-- `n33hP`: Progress class budget, reduced to `|𝔒_P atoms| ≤ O_P`.
Instantiate `O_P := termChernoff (pc.phases ctx).toClosurePhaseData`. -/
theorem appendixN33_hP_of_card_le (ctx : ActualFailureContext) {O_P : ℝ}
    (h : (((appendixN33Atoms ctx).filter
        (fun e => (appendixN33Row e).outputClass = OutputClassV4.progress)).card : ℝ)
      ≤ O_P) :
    AppendixN.classMassV4 (appendixN33Outputs ctx) appendixN33Weight
        OutputClassV4.progress ≤ O_P :=
  appendixN33_classMass_le_of_card_le ctx OutputClassV4.progress h

/-- `n33hE`: Endpoint class budget, reduced to `|𝔒_E atoms| ≤ O_E`.
Instantiate `O_E := termReturn (pc.phases ctx).toClosurePhaseData`. -/
theorem appendixN33_hE_of_card_le (ctx : ActualFailureContext) {O_E : ℝ}
    (h : (((appendixN33Atoms ctx).filter
        (fun e => (appendixN33Row e).outputClass = OutputClassV4.endpoint)).card : ℝ)
      ≤ O_E) :
    AppendixN.classMassV4 (appendixN33Outputs ctx) appendixN33Weight
        OutputClassV4.endpoint ≤ O_E :=
  appendixN33_classMass_le_of_card_le ctx OutputClassV4.endpoint h

/-- `n33hCNL`: clean-CNL class budget, reduced to `|𝔒_CNL atoms| ≤ O_CNL`.
Instantiate `O_CNL := termCnl (pc.phases ctx).toClosurePhaseData`. -/
theorem appendixN33_hCNL_of_card_le (ctx : ActualFailureContext) {O_CNL : ℝ}
    (h : (((appendixN33Atoms ctx).filter
        (fun e => (appendixN33Row e).outputClass = OutputClassV4.cnl)).card : ℝ)
      ≤ O_CNL) :
    AppendixN.classMassV4 (appendixN33Outputs ctx) appendixN33Weight
        OutputClassV4.cnl ≤ O_CNL :=
  appendixN33_classMass_le_of_card_le ctx OutputClassV4.cnl h

/-- `n33hbdd`: bounded class budget, reduced to `|𝔒_bdd atoms| ≤ O_bdd`.
Instantiate `O_bdd := termTower (pc.phases ctx).toClosurePhaseData`. -/
theorem appendixN33_hbdd_of_card_le (ctx : ActualFailureContext) {O_bdd : ℝ}
    (h : (((appendixN33Atoms ctx).filter
        (fun e => (appendixN33Row e).outputClass = OutputClassV4.bdd)).card : ℝ)
      ≤ O_bdd) :
    AppendixN.classMassV4 (appendixN33Outputs ctx) appendixN33Weight
        OutputClassV4.bdd ≤ O_bdd :=
  appendixN33_classMass_le_of_card_le ctx OutputClassV4.bdd h

/-! ## N.13 window-budget routing (`n2Window`) — tied to `termRun` -/

/-- **`n2Window`, tied to `termRun`'s definition.**  Since
`termRun phases.toClosurePhaseData = phases.run.runMass` definitionally, the N.13
rolling-window budget routes into the run-phase budget exactly when it fits
inside the run-phase mass `run.runMass`.  Instantiate `phases := pc.phases ctx`;
the hypothesis is the genuine N.2.2/I.5.2 window-vs-run-budget comparison. -/
theorem appendixN2WindowBound_le_termRun
    {cStar ξ X : ℝ} (ctx : ActualFailureContext)
    (phases : SixPhaseFactoryData cStar ξ X)
    (h : appendixN2WindowBound ctx ≤ phases.run.runMass) :
    appendixN2WindowBound ctx ≤ termRun phases.toClosurePhaseData := by
  rw [termRun_toClosurePhaseData_eq_runMass]; exact h

/-! ## L.6.2 shell-paid bounded-class split (`bddLowPaid`) — cross-leaf interface -/

/-- **`bddLowPaid`, reduced to the genuine Chernoff shell-paid embedding.**

For the unit-charge bounded terminal class, the L.6.1 pointwise split
`wt = wtLow + wtPaid` is discharged automatically by taking `wtLow := 1 - wtPaid`.
What remains is exactly the genuine cross-leaf content of Lemma L.6.2: the
shell-paid embedding of the paid bounded outputs into the §22.1A Chernoff
stopped family (`embedding`, with its `paid_eq` mass-matching), the L.6.3
low-residual bound (`low_le`), and the constant budget bookkeeping
(`output_budget`).  Instantiate
`O_bdd := termTower (pc.phases ctx).toClosurePhaseData`. -/
def appendixN33BddLowPaid_ofEmbedding (ctx : ActualFailureContext) {O_bdd : ℝ}
    (embedding : ShellPaidTerminalEmbeddingData (chernoff22_1ALeafOfShell ctx))
    (wtPaid : OutputObjectV4 → ℝ)
    (remLow : ℝ)
    (paid_eq : embedding.paidMass
      = ∑ o ∈ (appendixN33Outputs ctx).filter
          (fun o => o.cls = OutputClassV4.bdd), wtPaid o)
    (low_le : (∑ o ∈ (appendixN33Outputs ctx).filter
        (fun o => o.cls = OutputClassV4.bdd), (1 - wtPaid o)) ≤ remLow)
    (output_budget : embedding.mainPaid + (remLow + embedding.remPaid) ≤ O_bdd) :
    ShellPaidBddClassBoundData.LowPaidSplitData (chernoff22_1ALeafOfShell ctx)
      (appendixN33Outputs ctx) appendixN33Weight O_bdd where
  wtLow := fun o => 1 - wtPaid o
  wtPaid := wtPaid
  remLow := remLow
  embedding := embedding
  paid_eq := paid_eq
  split := by
    intro o _ho
    show appendixN33Weight o = (1 - wtPaid o) + wtPaid o
    have : appendixN33Weight o = 1 := rfl
    rw [this]; ring
  low_le := low_le
  output_budget := output_budget

/-! ## Assembling the exact residual surfaces from the minimal interfaces

These two assemblers demonstrate that the reductions above match the *exact*
field shapes of `Erdos260N2Cores` / `Erdos260N33Cores`
(`Erdos260.Erdos260ReducedToCores`): given only the genuine cross-leaf
comparisons, the full residual surfaces are inhabited.  The N.2 measurability
field `n2hA` is supplied unconditionally. -/

/-- **The N.2 residual surface, assembled from a single genuine comparison.**

`n2A := I_j = [0,Y]` and `n2hA` are supplied unconditionally; the only input is
the N.2.2/I.5.2 window-vs-run-budget comparison `hwin : windowBound ≤ run.runMass`. -/
def erdos260N2Cores_ofRunBudget (pc : Erdos260PhaseCores)
    (hwin : ∀ ctx : ActualFailureContext,
      appendixN2WindowBound ctx ≤ (pc.phases ctx).run.runMass) :
    Erdos260N2Cores pc where
  n2A := appendixN2ThresholdSet
  n2hA := appendixN2ThresholdSet_measurable
  n2Window := fun ctx =>
    appendixN2WindowBound_le_termRun ctx (pc.phases ctx) (hwin ctx)

/-- **The N.3.3 residual surface, assembled from the concrete count budgets.**

Every N.1.0 / N.24 inequality is reduced to a routed-atom count comparison
against the matching assembled phase mass; the L.6.2 bounded-class split is the
genuine Chernoff shell-paid datum `bddLP`.  This is the complete `Erdos260N33Cores`
surface modulo exactly those cross-leaf inputs. -/
def erdos260N33Cores_ofCardBudgets (pc : Erdos260PhaseCores)
    (n2 : Erdos260N2Cores pc)
    (hterm : ∀ ctx : ActualFailureContext,
      n2.termMass ctx ≤ ((appendixN33Atoms ctx).card : ℝ))
    (hD : ∀ ctx : ActualFailureContext,
      (((appendixN33Atoms ctx).filter
          (fun e => (appendixN33Row e).outputClass = OutputClassV4.densePack)).card : ℝ)
        ≤ termDensePack (pc.phases ctx).toClosurePhaseData)
    (hP : ∀ ctx : ActualFailureContext,
      (((appendixN33Atoms ctx).filter
          (fun e => (appendixN33Row e).outputClass = OutputClassV4.progress)).card : ℝ)
        ≤ termChernoff (pc.phases ctx).toClosurePhaseData)
    (hE : ∀ ctx : ActualFailureContext,
      (((appendixN33Atoms ctx).filter
          (fun e => (appendixN33Row e).outputClass = OutputClassV4.endpoint)).card : ℝ)
        ≤ termReturn (pc.phases ctx).toClosurePhaseData)
    (hCNL : ∀ ctx : ActualFailureContext,
      (((appendixN33Atoms ctx).filter
          (fun e => (appendixN33Row e).outputClass = OutputClassV4.cnl)).card : ℝ)
        ≤ termCnl (pc.phases ctx).toClosurePhaseData)
    (hbdd : ∀ ctx : ActualFailureContext,
      (((appendixN33Atoms ctx).filter
          (fun e => (appendixN33Row e).outputClass = OutputClassV4.bdd)).card : ℝ)
        ≤ termTower (pc.phases ctx).toClosurePhaseData)
    (bddLP : ∀ ctx : ActualFailureContext,
      ShellPaidBddClassBoundData.LowPaidSplitData (chernoff22_1ALeafOfShell ctx)
        (appendixN33Outputs ctx) appendixN33Weight
        (termTower (pc.phases ctx).toClosurePhaseData)) :
    Erdos260N33Cores pc n2 where
  n33hterm := fun ctx => appendixN33_terminalMass_le_of_card_le ctx (hterm ctx)
  n33hD := fun ctx => appendixN33_hD_of_card_le ctx (hD ctx)
  n33hP := fun ctx => appendixN33_hP_of_card_le ctx (hP ctx)
  n33hE := fun ctx => appendixN33_hE_of_card_le ctx (hE ctx)
  n33hCNL := fun ctx => appendixN33_hCNL_of_card_le ctx (hCNL ctx)
  n33hbdd := fun ctx => appendixN33_hbdd_of_card_le ctx (hbdd ctx)
  bddLowPaid := bddLP

end

/-! ## Axiom audit

Every result above is axiom-clean: it depends only on the standard Lean/Mathlib
foundational axioms `propext`, `Classical.choice`, `Quot.sound` (no `sorry`,
`axiom`, or `admit`). -/

#print axioms appendixN2ThresholdSet_measurable
#print axioms appendixN33Weight_sum_eq_card
#print axioms appendixN33ClassMass_eq_card
#print axioms appendixN33Row_densePack_iff
#print axioms appendixN33_terminalMass_le_of_card_le
#print axioms appendixN33_classMass_le_of_card_le
#print axioms appendixN2WindowBound_le_termRun
#print axioms appendixN33BddLowPaid_ofEmbedding
#print axioms erdos260N2Cores_ofRunBudget
#print axioms erdos260N33Cores_ofCardBudgets

end Erdos260
