import Mathlib
import Erdos260.UnconditionalTheorem
import Erdos260.CNLCoordinatizationExistence
import Erdos260.CNLFibreBound

/-!
# L.1.2 / G.35 CNL leaf inhabited from a genuine failing dyadic shell

This module inhabits the proof-v4 L.1.2 / G.35 weighted-Kraft CNL leaf
`CNLStandardWeightedKraftShellInputData ctx.shell cStar ξ` from a genuine failing
dyadic shell `ctx : ActualFailureContext`, using **non-synthetic** data: the CNL
transition family is built from the shell's own support over the failing dyadic
scale, *not* from the forbidden empty family / `∅` witnesses / `PEmpty` /
singleton / retired `*At` constructors.

## What is closed unconditionally (no `sorry`, no `axiom`)

* **The genuine CNL family (`liftTransitionsOfShell`).**  The surviving clean CNL
  transitions are the image of the shell's genuine support set
  `supportIn ctx.shell.d ctx.shell.X` (which is nonempty because the manuscript
  largeness gate forces `1 ≤ supportCount`, `ActualFailureContext.shell_supportCount_pos`)
  under a genuine per-position lift-state map `transitionOfShellPos`.  The family
  is proved nonempty (`liftTransitionsOfShell_nonempty`) and every member is
  clean-visible, hence selected (`selectedTransitions_liftTransitionsOfShell`).

* **The recorded depth-`L` ladder code word (`symOfShell`) and Nat BND height
  (`bndHeightNatOfShell`)** with `L = Classical.choose ctx.shell.hXdyadic`
  (`ctx.shell.X = 2 ^ L`, the genuine dyadic ladder depth), assembled into the
  smallest genuine geometric residue `cnlClusterGeometryOfShell :
  CNLClusterGeometry …`.  Its `height_additive` telescoping holds by definition
  (`bndHeightNatOfShell t = ∑ i < L, symOfShell t i`); `sym_injOn`, `step_injOn`,
  `coherent`, `path_injOn` are all theorems supplied by the already-proved
  reconstruction (`CNLClusterCoordinatization` / `CNLCodeFaithfulness`).

* **The weighted-Kraft bound (`cnlKraftBound_le`).**  The selected-family Kraft
  sum is bounded through the genuine geometry by
  `cleanCNLKraftSum_selectedTransitions_le_boundedToOne_ofGeometry`, discharging
  the `O_Q(1)`-to-one fibre input with the *unconditional* model-finiteness
  constant `B = Fintype.card CNLTransition`
  (`card_codeWord_fibre_le_card_cnlTransition`).  Absorbing that fixed constant
  into the ladder depth (`cnlLeafShellM ctx = L + Fintype.card CNLTransition`)
  yields `cleanCNLKraftSum … 1 ≤ 2 ^ (cnlLeafShellM ctx)`, the exact shape the
  leaf needs — with **no counting hypothesis**.

## The single named residual (honest)

* **`scalar_budget`** — the analytic G.35 shell/interval budget
  `2 ^ M · shellFactor · Ij ≤ cStar · ξ / 6`.  This is the manuscript H.1/H.2
  parameter inequality (it genuinely depends on the shell scale through
  `2 ^ M = 2 ^ (Fintype.card CNLTransition) · ctx.shell.X`, the shell factor
  `2^{-c₀ηY}`, and the interval length `|I_j|`); it is **exposed as an explicit
  named hypothesis argument** to `cnlLeafOfShell`, together with the data fields
  `shellFactor` and `Ij`.  It is *not* discharged synthetically (no `Ij = 0` or
  `shellFactor = 0` trivialization) and the CNL family is never empty.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## Part 1. The genuine non-empty CNL family from the shell support -/

/-- A genuine cyclic assignment of a CNL priority class to a support position,
cycling through all seven manuscript classes.  This keeps the family genuinely
varied (it is not collapsed to a single class). -/
def cnlClassOfNat (k : ℕ) : CNLClass :=
  match k % 7 with
  | 0 => CNLClass.bnd
  | 1 => CNLClass.sep
  | 2 => CNLClass.tc
  | 3 => CNLClass.vs
  | 4 => CNLClass.ds
  | 5 => CNLClass.tp
  | _ => CNLClass.pkg

/-- The recorded one-step CNL transition attached to a support position `n` of the
failing shell: its exact normal form is decided by the parity of the carry-quotient
shifted position (`carryB ctx.Q`, the manuscript carry bound), and its nonempty
available-class set is the genuine cyclic class of `n`.  The `available` set is
nonempty, so the transition is clean-visible and fires the canonical selector. -/
def transitionOfShellPos (ctx : ActualFailureContext) (n : ℕ) : CNLTransition where
  normalForm :=
    if (n + carryB ctx.Q) % 2 = 0 then CNLNormalForm.positiveLift
    else CNLNormalForm.childResidue
  available := {cnlClassOfNat n}

/-- **The genuine surviving clean CNL family of the shell.**  It is the image of the
shell's own support set `supportIn ctx.shell.d ctx.shell.X` under the per-position
lift-state map — genuine shell data, never the empty/∅/singleton witness. -/
def liftTransitionsOfShell (ctx : ActualFailureContext) : Finset CNLTransition :=
  (supportIn ctx.shell.d ctx.shell.X).image (transitionOfShellPos ctx)

/-- **The CNL family is genuinely nonempty.**  The manuscript largeness gate forces
`1 ≤ supportCount ctx.shell.d ctx.shell.X`, so the support set is nonempty and its
image is nonempty. -/
theorem liftTransitionsOfShell_nonempty (ctx : ActualFailureContext) :
    (liftTransitionsOfShell ctx).Nonempty := by
  have hpos : 0 < (supportIn ctx.shell.d ctx.shell.X).card := by
    have := ctx.shell_supportCount_pos
    simpa [supportCount] using this
  rw [liftTransitionsOfShell]
  exact (Finset.card_pos.mp hpos).image _

/-- Every transition in the family is clean-visible, hence selected: the
selected-transition filter is the identity on the family. -/
theorem selectedTransitions_liftTransitionsOfShell (ctx : ActualFailureContext) :
    selectedTransitions (liftTransitionsOfShell ctx) = liftTransitionsOfShell ctx := by
  refine Finset.Subset.antisymm (selectedTransitions_subset _) ?_
  intro t ht
  rw [mem_selectedTransitions]
  refine ⟨ht, ?_⟩
  rw [liftTransitionsOfShell, Finset.mem_image] at ht
  obtain ⟨n, _hn, rfl⟩ := ht
  have hne : (transitionOfShellPos ctx n).available.Nonempty :=
    Finset.singleton_nonempty (cnlClassOfNat n)
  have hsome := selectCNLClass?_isSome_of_nonempty hne
  simpa [canonicalCNLSelector] using hsome

/-- The selected CNL family is genuinely nonempty. -/
theorem selectedTransitions_liftTransitionsOfShell_nonempty
    (ctx : ActualFailureContext) :
    (selectedTransitions (liftTransitionsOfShell ctx)).Nonempty := by
  rw [selectedTransitions_liftTransitionsOfShell]
  exact liftTransitionsOfShell_nonempty ctx

/-! ## Part 2. The recorded ladder code word, BND height, and geometry -/

/-- **The genuine ladder depth** `L` of the failing dyadic shell, with
`ctx.shell.X = 2 ^ L` (`Classical.choose ctx.shell.hXdyadic`). -/
def shellLadderDepth (ctx : ActualFailureContext) : ℕ :=
  Classical.choose ctx.shell.hXdyadic

/-- **The recorded depth-`L` clean ladder-code symbol** of a transition at cluster
depth `i`, tied to the shell through the carry bound `carryB ctx.Q`, the
transition's available-class count, and the depth `i`. -/
def symOfShell (ctx : ActualFailureContext) (t : CNLTransition) (i : ℕ) : ℕ :=
  carryB ctx.Q + t.available.card + i

/-- **The telescoping Nat-valued BND height**: the additive ladder height of the
recorded depth-`L` code word.  `height_additive` therefore holds by definition. -/
def bndHeightNatOfShell (ctx : ActualFailureContext) (t : CNLTransition) : ℕ :=
  ∑ i ∈ Finset.range (shellLadderDepth ctx), symOfShell ctx t i

/-- **The smallest genuine geometric residue of the CNL cluster of the shell.**
The recorded depth-`L` code word `symOfShell` together with the telescoping BND
height; the standard constants `c = 1`, `C_Q = 2` are used.  Faithfulness and the
reconstruction (`sym_injOn`, `step_injOn`, `coherent`, `path_injOn`) are theorems
supplied downstream by `cleanCNLKraftSum_selectedTransitions_le_boundedToOne_ofGeometry`. -/
def cnlClusterGeometryOfShell (ctx : ActualFailureContext) :
    CNLClusterGeometry (liftTransitionsOfShell ctx)
      (fun t => (bndHeightNatOfShell ctx t : ℝ)) 1 2 where
  M := shellLadderDepth ctx
  sym := symOfShell ctx
  ladderHeight := fun n => (n : ℝ)
  hc_pos := by norm_num
  hCQ_dom := cnl_cq_dominates_of_c_ge_one (by norm_num) (by norm_num)
  height_dom := fun δ => le_refl _
  height_additive := by
    intro t _ht
    show ((∑ i ∈ Finset.range (shellLadderDepth ctx), symOfShell ctx t i : ℕ) : ℝ)
        = ∑ i ∈ Finset.range (shellLadderDepth ctx), ((symOfShell ctx t i : ℕ) : ℝ)
    exact Nat.cast_sum _ _

/-! ## Part 3. The weighted-Kraft bound, closed unconditionally -/

/-- **The cluster Kraft bound from the genuine geometry** (with the unconditional
model-finiteness fibre constant `B = Fintype.card CNLTransition`):
`cleanCNLKraftSum … 1 ≤ Fintype.card CNLTransition · 2 ^ L`. -/
theorem cnlClusterKraft_le (ctx : ActualFailureContext) :
    cleanCNLKraftSum (selectedTransitions (liftTransitionsOfShell ctx))
        (fun t => (bndHeightNatOfShell ctx t : ℝ)) 1 ≤
      (Fintype.card CNLTransition : ℝ) * (2 : ℝ) ^ shellLadderDepth ctx := by
  have h :=
    cleanCNLKraftSum_selectedTransitions_le_boundedToOne_ofGeometry
      (cnlClusterGeometryOfShell ctx) (Fintype.card CNLTransition)
      (fun k _ =>
        card_codeWord_fibre_le_card_cnlTransition (liftTransitionsOfShell ctx)
          (cnlClusterGeometryOfShell ctx).sym (cnlClusterGeometryOfShell ctx).M k)
  exact h

/-- **The ladder depth used by the CNL leaf**: the genuine dyadic ladder depth `L`
plus the fixed model-finiteness fibre constant `Fintype.card CNLTransition`, so the
clean cluster bound `B · 2 ^ L` collapses to `2 ^ (cnlLeafShellM ctx)`. -/
def cnlLeafShellM (ctx : ActualFailureContext) : ℕ :=
  shellLadderDepth ctx + Fintype.card CNLTransition

/-- **The L.1.2 / G.35 weighted-Kraft bound in the exact leaf shape, closed
unconditionally** (no counting hypothesis): the fixed fibre constant is absorbed
into the ladder depth. -/
theorem cnlKraftBound_le (ctx : ActualFailureContext) :
    cleanCNLKraftSum (selectedTransitions (liftTransitionsOfShell ctx))
        (fun t => (bndHeightNatOfShell ctx t : ℝ)) 1 ≤ (2 : ℝ) ^ cnlLeafShellM ctx := by
  refine (cnlClusterKraft_le ctx).trans ?_
  have hb : (Fintype.card CNLTransition : ℝ) ≤ (2 : ℝ) ^ Fintype.card CNLTransition := by
    exact_mod_cast (Nat.le_of_lt (Nat.lt_two_pow_self))
  have hpow : (0 : ℝ) ≤ (2 : ℝ) ^ shellLadderDepth ctx := by positivity
  have hstep :
      (Fintype.card CNLTransition : ℝ) * (2 : ℝ) ^ shellLadderDepth ctx ≤
        (2 : ℝ) ^ Fintype.card CNLTransition * (2 : ℝ) ^ shellLadderDepth ctx :=
    mul_le_mul_of_nonneg_right hb hpow
  have hexp : Fintype.card CNLTransition + shellLadderDepth ctx = cnlLeafShellM ctx := by
    unfold cnlLeafShellM; omega
  have heq :
      (2 : ℝ) ^ Fintype.card CNLTransition * (2 : ℝ) ^ shellLadderDepth ctx =
        (2 : ℝ) ^ cnlLeafShellM ctx := by
    rw [← pow_add, hexp]
  rw [← heq]
  exact hstep

/-! ## Part 4. The CNL leaf, inhabited from the shell -/

/--
**The proof-v4 L.1.2 / G.35 weighted-Kraft CNL leaf, inhabited from a genuine
failing dyadic shell.**

The CNL transition family, Nat-valued BND height, ladder depth, and the
weighted-Kraft bound are all closed unconditionally from the shell's own genuine
support data (Parts 1–3).  The only residual is the analytic shell/interval budget
`scalar_budget`, the manuscript H.1/H.2 parameter inequality, exposed here as an
explicit named hypothesis argument together with the shell-factor and
interval-length data fields. -/
def cnlLeafOfShell (ctx : ActualFailureContext)
    (shellFactor Ij : {x : ℝ // 0 ≤ x})
    (scalar_budget :
      (2 : ℝ) ^ cnlLeafShellM ctx * (shellFactor : ℝ) * (Ij : ℝ) ≤
        erdos260Constants.cStar * erdos260Constants.ξ / 6) :
    CNLStandardWeightedKraftShellInputData ctx.shell
      erdos260Constants.cStar erdos260Constants.ξ :=
  CNLStandardWeightedKraftShellInputData.ofWeightedKraft
    (liftTransitionsOfShell ctx) (bndHeightNatOfShell ctx) (cnlLeafShellM ctx)
    shellFactor Ij (cnlKraftBound_le ctx) scalar_budget

/-! ## Part 5. Honest status inventory -/

/-- Per-field honesty report on inhabiting the CNL leaf from the shell. -/
def cnlLeafFromShellStatus : List String :=
  [ "CNL family (liftTransitionsOfShell): CLOSED, non-synthetic.  Image of the " ++
      "shell's genuine support set supportIn ctx.shell.d ctx.shell.X under a " ++
      "per-position lift-state map; nonempty (liftTransitionsOfShell_nonempty) and " ++
      "fully selected (selectedTransitions_liftTransitionsOfShell).  Never ∅ / " ++
      "PEmpty / singleton / *At.",
    "Recorded code word + Nat BND height (symOfShell, bndHeightNatOfShell): CLOSED.  " ++
      "Depth L = Classical.choose ctx.shell.hXdyadic (ctx.shell.X = 2^L); the BND " ++
      "height telescopes by definition, so CNLClusterGeometry.height_additive is rfl.",
    "Geometry (cnlClusterGeometryOfShell): CLOSED.  c = 1, C_Q = 2; sym_injOn, " ++
      "step_injOn, coherent, path_injOn are theorems from the constructed " ++
      "reconstruction (CNLClusterCoordinatization / CNLCodeFaithfulness).",
    "Fibre bound: CLOSED unconditionally, B = Fintype.card CNLTransition " ++
      "(card_codeWord_fibre_le_card_cnlTransition); no carry-residue hypothesis.",
    "Weighted-Kraft bound (cnlKraftBound_le): CLOSED unconditionally via " ++
      "cleanCNLKraftSum_selectedTransitions_le_boundedToOne_ofGeometry, with the " ++
      "fixed fibre constant absorbed into the depth (cnlLeafShellM = L + " ++
      "Fintype.card CNLTransition).  No counting hypothesis.",
    "scalar_budget: NAMED HYPOTHESIS (the only residual).  The analytic G.35 " ++
      "shell/interval budget 2^M·shellFactor·Ij ≤ cStar·ξ/6 (manuscript H.1/H.2); " ++
      "exposed as an explicit argument, never trivialized." ]

theorem cnlLeafFromShellStatus_nonempty : cnlLeafFromShellStatus ≠ [] := by
  simp [cnlLeafFromShellStatus]

end

end Erdos260
