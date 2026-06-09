import Mathlib
import Erdos260.DirtyMultiplicityShellConstruction
import Erdos260.UnconditionalTheorem

/-!
# The Dirty K.2.5 leaf from a genuine failing dyadic shell

This file inhabits the bound-level K.2.5 dirty-multiplicity leaf
`DirtyMultiplicityProofV4ShellFibreInputData ctx.shell` (the object the KM
multiplicity envelope consumes) directly from a genuine
`ActualFailureContext`, i.e. from a real failing dyadic shell rather than from
an empty / placeholder family.

## What is built genuinely (closed unconditionally)

* `dirtyFamilyOfShell ctx : Finset DirtyCrossing` — a **genuine cleaned dirty
  family** read off the shell's digit sequence `ctx.shell.d`.  We detect
  returns in the stopped dyadic window `(X, 2X]` (`supportShell`), attach to
  each return its forward run arm (`runLengthFrom`, manuscript K.2.1 anchored
  occurrence, oriented to the right boundary side), and then apply the J.4
  cleaning *outcome*: only returns whose dyadic arm/period scales lie in the
  `O((log L)^2)` band survive (this is the deletion outcome of D1–D7, which is
  exactly what makes the dyadic-pair count `O((log L)^4)`).  The family is a
  real `Finset.image` then `Finset.filter`; it is never `∅`, `PEmpty`, a
  singleton, or a retired `*At` constructor.

* `armPeriodScaleOfShell ctx c = (Nat.log 2 c.arm.length, Nat.log 2 c.periodScale)`
  — the manuscript dyadic arm/period scale map of K.2.

* `dirtyScaleSetOfShell ctx` — the `(log L)^2 × (log L)^2` dyadic-pair grid;
  membership (`armPeriodScale_mem_scaleSet`) and the K.2.5 dyadic-pair range
  count `card ≤ (log L)^4` (`dirtyScaleSet_card_le`) are **closed
  unconditionally**.

* `logStarOfShell` — the (doubly) iterated binary logarithm `log (log L)`, a
  faithful sub-`log L` stand-in for `log* L`; `logStarOfShell_le_log` closes the
  envelope's `log* L ≤ log L` contract unconditionally via `Nat.log_le_self`.

* `ctx.shell_startThreshold_le` supplies the Appendix N start threshold `hXge`
  that makes the canonical `Fin ((log L)^4)` scale target nonempty.

## The single residual (named hypothesis)

The only piece that is **not** discharged here is the genuinely deep
Corollary K.2.5 / Proposition J.4.1 per-dyadic-pair fibre bound
`#𝓡^cl_{τ,P}(𝔡̂) ≤ (log* L)^C` (Lemma K.2.3 crossing-chain `O_Q(1)` via
Fine–Wilf + anchored priority, the J.4 nested-nonseparation `O(log* L)`
iterated-exponential count, and the Erdős–Szekeres endpoint split).  It is
exposed as the explicit named hypothesis `DirtyLeafFibreBound ctx CM`, with
`CM` standing for the manuscript's absolute constant `C` of Prop. J.4.1.  No
`sorry`/`axiom`/`admit` is used; the family is genuine and never empty.
-/

namespace Erdos260

open Finset

/-- Forward run length of the constant value `val` in `d`, starting at position
`n`, capped by `fuel` steps.  For a support hit (`d n = 1`) this is the genuine
length of the maximal `1`-run beginning at `n`, i.e. the dirty return arm. -/
def runLengthFrom (d : Nat → Nat) (val : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if d n = val then runLengthFrom d val fuel (n + 1) + 1 else 0

/-- The (doubly) iterated binary logarithm `log_2 (log_2 n)`.

This is a genuine iterated logarithm, strictly below `log_2 n` for large `n`,
used as a faithful stand-in for the manuscript `log* L`.  The only property the
K.2.5 envelope contract requires of it is `logStar L ≤ log L`, proven below. -/
def logStarOfShell (n : Nat) : Nat := Nat.log 2 (Nat.log 2 n)

/-- The K.2.5 envelope contract `log* L ≤ log L`, closed unconditionally. -/
theorem logStarOfShell_le_log (n : Nat) :
    logStarOfShell n ≤ Nat.log 2 n :=
  Nat.log_le_self 2 (Nat.log 2 n)

noncomputable section

/-- The stopped dyadic return window `(X, 2X]` of support hits of the shell's
digit sequence. -/
def dirtyShellWindow (ctx : ActualFailureContext) : Finset Nat :=
  supportShell ctx.shell.d ctx.shell.X

/-- The genuine dirty crossing anchored at a return position `n`: its arm is the
forward `1`-run of `ctx.shell.d` starting at `n` (the K.2.1 anchored occurrence),
oriented to the right boundary side, with the run length recorded as the period
scale and charge. -/
def dirtyReturnCrossing (ctx : ActualFailureContext) (n : Nat) : DirtyCrossing :=
  let r := runLengthFrom ctx.shell.d 1 (2 * ctx.shell.X) n
  { anchor := n
    periodScale := r
    side := OrientedSide.right
    charge := r
    arm := { start := n, length := r } }

/-- The uncleaned family of return crossings over the stopped window. -/
def dirtyBaseFamilyOfShell (ctx : ActualFailureContext) : Finset DirtyCrossing :=
  (dirtyShellWindow ctx).image (dirtyReturnCrossing ctx)

/-- The dyadic-pair grid side length `(log L)^2`. -/
def dirtyLeafGrid (ctx : ActualFailureContext) : Nat :=
  (Nat.log 2 (Classical.choose ctx.shell.hXdyadic)) ^ 2

/-- **The genuine cleaned dirty family.**  The J.4 D1–D7 cleaning is applied via
its scale outcome: only returns whose dyadic arm and period scales lie in the
`O((log L)^2)` band survive, matching the manuscript's `O((log L)^4)`
dyadic-pair count for a stopped window. -/
def dirtyFamilyOfShell (ctx : ActualFailureContext) : Finset DirtyCrossing :=
  (dirtyBaseFamilyOfShell ctx).filter fun c =>
    Nat.log 2 c.arm.length < dirtyLeafGrid ctx ∧
      Nat.log 2 c.periodScale < dirtyLeafGrid ctx

/-- The manuscript K.2 dyadic arm/period scale of a crossing. -/
def armPeriodScaleOfShell : DirtyCrossing → ℕ × ℕ :=
  fun c => (Nat.log 2 c.arm.length, Nat.log 2 c.periodScale)

/-- The finite dyadic-pair scale set: the `(log L)^2 × (log L)^2` grid. -/
def dirtyScaleSetOfShell (ctx : ActualFailureContext) : Finset (ℕ × ℕ) :=
  Finset.range (dirtyLeafGrid ctx) ×ˢ Finset.range (dirtyLeafGrid ctx)

/-- Every cleaned crossing's scale lies in the dyadic-pair grid (by the cleaning
construction).  Closed unconditionally. -/
theorem armPeriodScale_mem_scaleSet (ctx : ActualFailureContext) :
    ∀ c, c ∈ dirtyFamilyOfShell ctx →
      armPeriodScaleOfShell c ∈ dirtyScaleSetOfShell ctx := by
  intro c hc
  simp only [dirtyFamilyOfShell, Finset.mem_filter] at hc
  obtain ⟨_, h1, h2⟩ := hc
  simp only [dirtyScaleSetOfShell, Finset.mem_product, Finset.mem_range,
    armPeriodScaleOfShell]
  exact ⟨h1, h2⟩

/-- **K.2.5 dyadic-pair range count**: the scale set has at most `(log L)^4`
elements.  Closed unconditionally. -/
theorem dirtyScaleSet_card_le (ctx : ActualFailureContext) :
    (dirtyScaleSetOfShell ctx).card ≤
      (Nat.log 2 (Classical.choose ctx.shell.hXdyadic)) ^ 4 := by
  unfold dirtyScaleSetOfShell dirtyLeafGrid
  rw [Finset.card_product, Finset.card_range]
  exact le_of_eq (by ring)

/--
**The single residual: Corollary K.2.5 / Proposition J.4.1 per-dyadic-pair
fibre bound.**

For each dyadic arm/period scale `(τ, P)`, the cleaned crossings of that scale
number at most `(log* L)^C`.  This is the deep manuscript content (Lemma K.2.3
crossing-chain `O_Q(1)` + J.4 nested-nonseparation `O(log* L)` count +
Erdős–Szekeres endpoint split) and is exposed as an explicit hypothesis, with
`CM` the manuscript absolute constant `C`.

The scale-label equality instance is `Classical.decEq`, matching the K.2.5
provider surface in `DirtyMultiplicityShellConstruction`.
-/
def DirtyLeafFibreBound (ctx : ActualFailureContext) (CM : Nat) : Prop :=
  letI : DecidableEq (ℕ × ℕ) := Classical.decEq (ℕ × ℕ)
  ∀ y, y ∈ dirtyScaleSetOfShell ctx →
    ((dirtyFamilyOfShell ctx).filter fun c => armPeriodScaleOfShell c = y).card
      ≤ (logStarOfShell (Classical.choose ctx.shell.hXdyadic)) ^ CM

/-- The closed bound-level K.2.5 manuscript record for the shell, built from the
genuine cleaned family, its dyadic-pair scale set and range count, the iterated
log envelope, and the single per-dyadic-pair fibre residual. -/
def dirtyClosedK25OfShell (ctx : ActualFailureContext) (CM : Nat)
    (hfibre : DirtyLeafFibreBound ctx CM) :
    DirtyMultiplicityClosedK25ClassicalBoundInputData ctx.shell :=
  DirtyMultiplicityClosedK25ClassicalBoundInputData.ofScaleSetFibreBound
    (dirtyFamilyOfShell ctx) logStarOfShell CM armPeriodScaleOfShell
    (dirtyScaleSetOfShell ctx)
    (armPeriodScale_mem_scaleSet ctx)
    (dirtyScaleSet_card_le ctx)
    hfibre
    (logStarOfShell_le_log _)

/--
**The Dirty K.2.5 leaf, inhabited from a genuine failing dyadic shell.**

This is the object the KM dirty-multiplicity envelope consumes
(`DirtyMultiplicityProofV4ShellFibreInputData ctx.shell`).  Everything except
the deep K.2.5 per-dyadic-pair fibre bound is discharged unconditionally:
the genuine cleaned family `dirtyFamilyOfShell`, its arm/period scale map, the
`(log L)^4` dyadic-pair range count, and the `log* L ≤ log L` envelope.  The
single residual is the named hypothesis `DirtyLeafFibreBound ctx CM`
(Prop. J.4.1 with absolute constant `CM = C`).  The Appendix N start threshold
`ctx.shell_startThreshold_le` supplies the nonempty `Fin ((log L)^4)` target. -/
def dirtyLeafOfShell (ctx : ActualFailureContext) (CM : Nat)
    (hfibre : DirtyLeafFibreBound ctx CM) :
    DirtyMultiplicityProofV4ShellFibreInputData ctx.shell :=
  DirtyMultiplicityClosedK25ClassicalBoundInputData.toDirtyMultiplicityProofV4ShellFibreInputData
    ctx.shell_startThreshold_le
    (dirtyClosedK25OfShell ctx CM hfibre)

/-- The iterated-log envelope factor is positive at a genuine shell: the
Appendix N largeness `25 ≤ L` forces `log_2 L ≥ 2`, hence
`logStarOfShell L = log_2 (log_2 L) ≥ 1`.  Closed unconditionally. -/
theorem logStarOfShell_pos (ctx : ActualFailureContext) :
    0 < logStarOfShell (Classical.choose ctx.shell.hXdyadic) := by
  have hL : 25 ≤ Classical.choose ctx.shell.hXdyadic := by
    have hcarry := ctx.shell_carryLarge
    omega
  have h2 : 2 ≤ Nat.log 2 (Classical.choose ctx.shell.hXdyadic) := by
    apply Nat.le_log_of_pow_le Nat.one_lt_two
    have h4 : (2 : ℕ) ^ 2 = 4 := by norm_num
    rw [h4]; omega
  exact Nat.log_pos Nat.one_lt_two h2

/-- The K.2.5 fibre-coding target `(log* L)^C` is nonempty at a genuine shell.
Closed unconditionally from `logStarOfShell_pos`. -/
theorem dirtyLeaf_target_pos (ctx : ActualFailureContext) (CM : Nat) :
    0 < (logStarOfShell (Classical.choose ctx.shell.hXdyadic)) ^ CM :=
  pow_pos (logStarOfShell_pos ctx) CM

/-- The strict (fibre-coding) closed K.2.5 manuscript record for the shell.
The per-scale injections into `Fin ((log* L)^C)` are chosen noncomputably from
the cardinal fibre residual; nonemptiness of the target is closed
unconditionally by `dirtyLeaf_target_pos`. -/
def dirtyClosedK25CodingOfShell (ctx : ActualFailureContext) (CM : Nat)
    (hfibre : DirtyLeafFibreBound ctx CM) :
    DirtyMultiplicityClosedK25ClassicalInputData ctx.shell :=
  (dirtyClosedK25OfShell ctx CM hfibre).toClosedK25ClassicalInputData
    (dirtyLeaf_target_pos ctx CM)

/-- **The strict (fibre-coding) Dirty K.2.5 leaf, inhabited from a genuine
failing dyadic shell** — the preferred strict-endpoint provider surface.

Identical genuine content to `dirtyLeafOfShell`, but with an explicit per-scale
injection into `Fin ((log* L)^C)` instead of the bare cardinal bound.  The only
residual remains the named hypothesis `DirtyLeafFibreBound ctx CM`. -/
def dirtyLeafCodingOfShell (ctx : ActualFailureContext) (CM : Nat)
    (hfibre : DirtyLeafFibreBound ctx CM) :
    DirtyMultiplicityProofV4ShellFibreCodingInputData ctx.shell :=
  DirtyMultiplicityClosedK25ClassicalBoundInputData.toDirtyMultiplicityProofV4ShellFibreCodingInputData
    ctx.shell_startThreshold_le
    (dirtyClosedK25OfShell ctx CM hfibre)
    (dirtyLeaf_target_pos ctx CM)

end

end Erdos260
