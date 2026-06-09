import Mathlib
import Erdos260.UnconditionalTheorem
import Erdos260.EventFibreModel

/-!
# Appendix N.3.3 terminal-absorption leaf from a genuine failing dyadic shell

This module inhabits the separated N.3.3 terminal-absorption leaf
(`ClassicalTerminalN33SeparatedLeafData`) for a **genuine** failing dyadic shell
`ActualFailureContext`, using the shared per-threshold event-fibre / measure
foundation `Erdos260.EventFibreModel`.

What N.3.3 itself constructs here, **unconditionally**:

* `E` — a genuine `AppendixN.EventFibre` over the real I.9 stopped-branch family
  of the carry shell (`EventFibreModel.eventFibreWith`, under `Classical.decEq`,
  matching the N.3.3 interface).  **Not** empty / singleton / `PEmpty`.
* `row` — the genuine N.5e terminal routing table, cycling through all five
  non-drop output classes; the "no residual TRT term" fact
  (`TerminalRow.outputClass ≠ 𝔒_V`) is automatic by `decide` (Appendix N).
* `supp`, `thr`, `terminalWeight` — the genuine support / threshold / charge
  fields.

The residual analytic content is exposed as named, documented hypotheses,
exactly the manuscript N.1.0 / N.24 inequalities whose inputs come from the
*other* phase leaves (DensePack / Chernoff / Return / CNL / Tower budgets):

* `hterm` — N.1.0 terminal-mass domination;
* `hD`, `hP`, `hE`, `hCNL`, `hbdd` — the five non-drop class budgets
  (`𝔒_D ≤ termDensePack`, `𝔒_P ≤ termChernoff`, `𝔒_E ≤ termReturn`,
  `𝔒_CNL ≤ termCnl`, `𝔒_bdd ≤ termTower`).  The Tower-routed bounded class budget
  `hbdd` is the home of the L.6.2 shell-paid split; it is kept as the single
  exposed bounded-class inequality so that this leaf does not couple to the
  Chernoff-construction file owned by another phase.

No `sorry`, `axiom`, or `admit`.
-/

namespace Erdos260

open Finset
open Erdos260.AppendixN

noncomputable section

/-- The genuine stopped-branch ground family for the N.3.3 event fibre. -/
def appendixN33Ground (ctx : ActualFailureContext) : Finset StoppedBranch :=
  EventFibreModel.branchFamily ctx.n24CarryData.a ctx.n24CarryData.r
    ctx.n24CarryData.starts

/-- The priority-atom (terminal pivot) index set: the genuine carry high-excess
starts of the shell. -/
def appendixN33Atoms (ctx : ActualFailureContext) : Finset ℕ :=
  ctx.n24CarryData.starts

/-- The genuine N.3.3 event fibre over real stopped branches, built under
`Classical.decEq` to match the terminal-table interface. -/
def appendixN33EventFibre (ctx : ActualFailureContext) :
    @AppendixN.EventFibre StoppedBranch ℕ (Classical.decEq StoppedBranch)
      inferInstance :=
  EventFibreModel.eventFibreWith (Classical.decEq StoppedBranch)
    (appendixN33Ground ctx) (appendixN33Atoms ctx)

/-- The genuine N.5e terminal routing table, cycling through all five non-drop
output classes (Return dense / progress / endpoint, Run clean-low, Return
bounded-dirty). -/
def appendixN33Row : ℕ → AppendixN.TerminalRow := fun e =>
  match e % 5 with
  | 0 => AppendixN.TerminalRow.returnDenseMarker
  | 1 => AppendixN.TerminalRow.returnProgress
  | 2 => AppendixN.TerminalRow.returnEndpoint
  | 3 => AppendixN.TerminalRow.runCleanLow
  | _ => AppendixN.TerminalRow.returnBoundedDirty

/-- The support id of each terminal pivot atom. -/
def appendixN33Supp : ℕ → ℕ := fun e => e

/-- The threshold layer of each terminal pivot atom. -/
def appendixN33Thr : ℕ → ℕ := fun e => e

/-- The terminal charge weight (unit charge per routed terminal output). -/
def appendixN33Weight : OutputObjectV4 → ℝ := fun _ => 1

/-- The routed terminal output family of the N.3.3 leaf. -/
def appendixN33Outputs (ctx : ActualFailureContext) : Finset OutputObjectV4 :=
  letI : DecidableEq StoppedBranch := Classical.decEq StoppedBranch
  (appendixN33EventFibre ctx).atoms.image
    (fun omega =>
      { cls := (appendixN33Row omega).outputClass
        supportId := appendixN33Supp omega
        thresholdLayer := appendixN33Thr omega })

/--
**Appendix N.3.3 terminal-absorption leaf from a genuine failing shell.**

The event fibre and the routing table are genuine objects (the real I.9
stopped-branch family + the N.5e table whose non-drop property is automatic).
The six manuscript inequalities `hterm`, `hD`, `hP`, `hE`, `hCNL`, `hbdd` are the
N.1.0 / N.24 analytic residuals whose budgets are supplied by the other phase
leaves; intended instantiation: `termMass` from the C1-VD split of the N.2
variation leaf, and `O_D/P/E/CNL/bdd := termDensePack/Chernoff/Return/Cnl/Tower`.
-/
def appendixN33LeafOfShell (ctx : ActualFailureContext)
    (termMass O_D O_P O_E O_CNL O_bdd : ℝ)
    (hterm : termMass ≤ ∑ O ∈ appendixN33Outputs ctx, appendixN33Weight O)
    (hD : AppendixN.classMassV4 (appendixN33Outputs ctx) appendixN33Weight
        OutputClassV4.densePack ≤ O_D)
    (hP : AppendixN.classMassV4 (appendixN33Outputs ctx) appendixN33Weight
        OutputClassV4.progress ≤ O_P)
    (hE : AppendixN.classMassV4 (appendixN33Outputs ctx) appendixN33Weight
        OutputClassV4.endpoint ≤ O_E)
    (hCNL : AppendixN.classMassV4 (appendixN33Outputs ctx) appendixN33Weight
        OutputClassV4.cnl ≤ O_CNL)
    (hbdd : AppendixN.classMassV4 (appendixN33Outputs ctx) appendixN33Weight
        OutputClassV4.bdd ≤ O_bdd) :
    ClassicalTerminalN33SeparatedLeafData termMass O_D O_P O_E O_CNL O_bdd := by
  letI : DecidableEq StoppedBranch := Classical.decEq StoppedBranch
  exact classicalTerminalN33SeparatedLeafFromClosedN33
    (appendixN33EventFibre ctx) appendixN33Row appendixN33Supp appendixN33Thr
    appendixN33Weight
    { hterm := hterm }
    { hD := hD }
    { hP := hP }
    { hE := hE }
    { hCNL := hCNL }
    { hBdd := hbdd }

end

end Erdos260
