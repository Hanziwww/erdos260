import Mathlib
import Erdos260.CNLConstantCompat
import Erdos260.CNLClusterCoordinatization

/-!
# Reducing the per-shell CNL bridge/budget input from the proved coordinatization core

`CNLConstantCompat.lean` (round 1) discharged the *Kraft* sub-field of the `cnl`
provider slot from the unconditional `CNLFibreBound` bound, packaging the per-shell
residue as

```
structure CNLUnconditionalKraftInput (cStar ξ X : ℝ) where
  T, BNDHeight, c, CQ, hc, hCQ, M, hM,
  E, g, sm, gOld, s, hE, hwin, hpos,          -- the BRIDGE LABELLING
  sym,
  hheight,                                     -- the additive BND height
  shellFactor, Ij, shellFactor_nonneg, Ij_nonneg,
  hbudget                                      -- the shell-budget calibration
```

and built `CNLClusterEncodingData` from it via `CNLClusterEncodingData.ofModelCardBridge`
(the model-finiteness route, folding the `O(1)` prefactor into `CQ`).  The capstone
`erdos260_reduced_minimal''` consumes this through `cnlProvider_ofUnconditional`.

This file (NEW; it edits nothing upstream) reduces the *remaining* bridge/budget
fields from the **proved CNL coordinatization core**
(`ClusterLadderCoordinatization` / `CleanClusterReconstruction`).  The headline is
a precise, honest, and somewhat surprising structural fact.

## 1. The bridge-labelling fields `hE`/`hwin`/`hpos` are JOINTLY VACUOUS

`hwin` + `hpos` are *exactly* the hypotheses of Lemma G.3 `bridgeExp_strictAnti`,
so they force `t ↦ bridgeExp g sm s t` to be `StrictAnti` on **all of `ℕ`** —
strictly decreasing by `≥ 1` at every step, hence `→ -∞`.  But `hE` (with
`E : ℕ → ℕ`) forces `bridgeExp g sm s t = (E t : ℤ) ≥ 0` for **every** `t`.  No
strictly decreasing `ℤ`-valued sequence on `ℕ` stays `≥ 0`.  Therefore the three
fields cannot be simultaneously satisfied:

* `bridge_labelling_vacuous : (hE) → (hwin) → (hpos) → False`;
* `cnlUnconditionalKraftInput_uninhabited : CNLUnconditionalKraftInput cStar ξ X → False`.

So `CNLUnconditionalKraftInput` is **uninhabited**, and the round-2 `cnlInput`
slot of `Erdos260MinimalAtoms''` can never be filled (non-vacuously) for a shell
satisfying the `cQ` hypothesis.  The bridge labelling is not merely "reducible" —
*as literally stated it is a vacuous hypothesis*.  This is the precise reason a
genuine reduction must **bypass** the bridge labelling rather than instantiate it.

## 2. The genuine reduction: coordinatization → encoding data (bridge-free)

The proved core supplies, with **no** bridge labelling, the prefactor-free Kraft
bound `cleanCNLKraftSum (selectedTransitions T) BNDHeight c ≤ CQ ^ M` from a
`ClusterLadderCoordinatization` (whose step-determinism `step_injOn` comes from a
*genuinely injective* step — the projection decode of `ofReplicatedInjectiveLabel`,
not the contradictory global bridge realization; and whose `sym_injOn` is closed
on the cleaned family by the transversal in `CNLCodeFaithfulness`).  From it
`cnlClusterEncodingDataOfCoordinatization` builds a full `CNLClusterEncodingData`
with `kraftSum_le` taken directly from `coord.kraftSum_le` and `manuscript_bound`
the **prefactor-free** shell budget `CQ ^ M · shellFactor · X · Ij ≤ cStar·ξ·X/6`.

* The bridge fields `E/g/sm/gOld/s/hE/hwin/hpos` are **ELIMINATED** (not needed).
* `hM : M ≠ 0` is **ELIMINATED** (no `(·)^(1/M)` fold is performed).
* `hheight` is **REDUCED** to the coordinatization's `height_additive`, which is
  the proved `pathHeight_descentBranch` telescoping
  (`bndHeight_eq_pathHeight_of_coordinatization`).
* `hbudget` is the **only** genuine remaining numeric input, and it is now
  *prefactor-free* (strictly weaker than round 1's `(card)·CQ^M·…` budget).

`cnlProvider_ofCoordinatization` inhabits the `Erdos260MinimalAtoms.cnl` provider
slot (the round-1 base that `erdos260_reduced_minimal` consumes) from per-shell
`CNLCoordinatizedShellInput`s — genuinely, non-vacuously.

## 3. Non-vacuity

`cnlClusterEncodingDataOfReplicatedInjectiveLabel` fires the whole pipeline from
any lift-exponent labelling injective on the selected family (the established
depth-`(m+1)` witness of `ofReplicatedInjectiveLabel`), and
`cnlEncodingData_witness` / `cnlCoordinatizedShellInput_witness` are concrete
closed inhabitants with a genuine (positive `shellFactor`, `Ij`) budget.

No `sorry`, `admit`, `native_decide`, or new `axiom`; no false/vacuous hypotheses
in any constructor below.  `#print axioms` of the headlines is the three standard
logical axioms only.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## Part 1. The bridge-labelling fields are jointly vacuous -/

/-- **There is no strictly decreasing `ℕ → ℕ` sequence.**  `Nat` is well-founded:
from `StrictAnti E` one gets `E n + n ≤ E 0` for all `n`, which fails at
`n = E 0 + 1`.  This is the well-ordering obstruction behind the vacuity of the
bridge labelling. -/
theorem no_strictAnti_nat (E : ℕ → ℕ) (h : StrictAnti E) : False := by
  have key : ∀ n, E n + n ≤ E 0 := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
        have hlt : E (k + 1) < E k := h (Nat.lt_succ_self k)
        omega
  have hbad := key (E 0 + 1)
  omega

/-- **The bridge-labelling fields `hE`/`hwin`/`hpos` are jointly contradictory.**

`hwin` + `hpos` are exactly the hypotheses of `bridgeExp_strictAnti` (Lemma G.3),
making `t ↦ bridgeExp g sm s t` strictly decreasing on all of `ℕ`.  Via `hE` this
transports to `StrictAnti E` for `E : ℕ → ℕ`, which is impossible
(`no_strictAnti_nat`).  Hence no `(E, g, sm, gOld, s)` satisfies all three. -/
theorem bridge_labelling_vacuous {E : ℕ → ℕ} {g sm gOld : ℕ → ℤ} {s : ℕ}
    (hE : ∀ t, (E t : ℤ) = bridgeExp g sm s t)
    (hwin : ∀ t, sm (t + 1) - sm t = g t - gOld t)
    (hpos : ∀ t, 0 < gOld t) : False := by
  have hSA : StrictAnti (fun t => bridgeExp g sm s t) :=
    bridgeExp_strictAnti g sm gOld s hwin hpos
  have hEanti : StrictAnti E := by
    intro a b hab
    have hlt : bridgeExp g sm s b < bridgeExp g sm s a := hSA hab
    rw [← hE a, ← hE b] at hlt
    exact_mod_cast hlt
  exact no_strictAnti_nat E hEanti

/-- **`CNLUnconditionalKraftInput` is uninhabited.**  Its bridge-labelling fields
`hE`/`hwin`/`hpos` are jointly vacuous (`bridge_labelling_vacuous`).  Consequently
`cnlProvider_ofUnconditional` and the `cnlInput` slot of `Erdos260MinimalAtoms''`
can never be filled non-vacuously for a shell satisfying the `cQ` hypothesis: the
honest reduction must bypass the bridge labelling. -/
theorem cnlUnconditionalKraftInput_uninhabited {cStar ξ X : ℝ}
    (inp : CNLUnconditionalKraftInput cStar ξ X) : False :=
  bridge_labelling_vacuous inp.hE inp.hwin inp.hpos

/-! ## Part 2. `hheight` is the coordinatization's telescoping height
(the proved `pathHeight_descentBranch`) -/

/-- **The additive BND height is the telescoped path height of the threaded
descent path.**  Directly from the coordinatization's `height_additive` and the
proved telescoping `pathHeight_descentBranch`:
`BNDHeight t = pathHeight ladderHeight (descentBranch (nodeOf t) M)`.  This is the
manuscript's additive `ℋ_BND`, and it is exactly the content reduced into the
`hheight` field — now a theorem, not an assumption. -/
theorem bndHeight_eq_pathHeight_of_coordinatization
    {T : Finset CNLTransition} {BNDHeight : CNLTransition → ℝ} {c CQ : ℝ}
    (coord : ClusterLadderCoordinatization T BNDHeight c CQ)
    {t : CNLTransition} (ht : t ∈ selectedTransitions T) :
    BNDHeight t
      = pathHeight coord.ladderHeight (descentBranch (coord.nodeOf t) coord.M) := by
  rw [coord.height_additive t ht]
  exact (pathHeight_descentBranch coord.ladderHeight coord.M (coord.nodeOf t)).symm

/-- The same telescoping for the bridge-step realization (`ladderHeight = id`,
`nodeOf = reconNode`): the `∑ E (sym t i)` shape of the round-1 `hheight` field is
the coordinatization height of the reconstructed node sequence.  Stated abstractly
over a deterministic `step` so that no (vacuous) bridge data is needed. -/
theorem reconHeight_eq_sum
    (step : ℕ → ℕ → ℕ) (root : ℕ) (sym : ℕ → ℕ) (H : ℕ → ℝ) (M : ℕ) :
    pathHeight H (descentBranch (reconNode step root sym) M)
      = ∑ i ∈ Finset.range M, H (reconNode step root sym (i + 1)) :=
  pathHeight_descentBranch H M (reconNode step root sym)

/-! ## Part 3. The genuine reduction: coordinatization → `CNLClusterEncodingData` -/

/--
**Build the K.3/L.1 cluster encoding datum directly from the proved
coordinatization (bridge-free, prefactor-free).**

Given a `ClusterLadderCoordinatization` of the selected clean cluster — whose
`coherent`, `path_injOn`, `root_eq`, `height_additive` are all *theorems* in the
proved core, and whose `kraftSum_le : cleanCNLKraftSum (selectedTransitions T)
BNDHeight c ≤ CQ ^ M` holds with **no** `O(1)` prefactor — plus the prefactor-free
shell budget `CQ ^ M · shellFactor · X · Ij ≤ cStar·ξ·X/6`, assemble a full
`CNLClusterEncodingData`.  `kraftSum_le` is taken verbatim from the coordinatization;
no bridge labelling, no `M ≠ 0`, and no prefactor fold are used. -/
def cnlClusterEncodingDataOfCoordinatization
    {cStar ξ X : ℝ}
    {T : Finset CNLTransition} {BNDHeight : CNLTransition → ℝ} {c CQ : ℝ}
    (coord : ClusterLadderCoordinatization T BNDHeight c CQ)
    (shellFactor Ij : ℝ)
    (shellFactor_nonneg : 0 ≤ shellFactor) (Ij_nonneg : 0 ≤ Ij)
    (hbudget : CQ ^ coord.M * shellFactor * X * Ij ≤ cStar * ξ * X / 6) :
    CNLClusterEncodingData cStar ξ X where
  α := CNLTransition
  paths := selectedTransitions T
  BNDHeight := BNDHeight
  c := c
  CQ := CQ
  M := coord.M
  shellFactor := shellFactor
  Ij := Ij
  shellFactor_nonneg := shellFactor_nonneg
  Ij_nonneg := Ij_nonneg
  kraftSum_le := coord.kraftSum_le
  manuscript_bound := hbudget

/-! ## Part 4. The reduced per-shell input and its provider -/

/--
**The reduced per-shell CNL input.**

Replaces `CNLUnconditionalKraftInput` (whose bridge fields are vacuous) by the
genuine residue: a proved `ClusterLadderCoordinatization` of the selected cluster
plus the *prefactor-free* shell budget.  No bridge labelling, no `M ≠ 0`. -/
structure CNLCoordinatizedShellInput (cStar ξ X : ℝ) where
  /-- The selected-transition cluster. -/
  T : Finset CNLTransition
  /-- The additive BND height. -/
  BNDHeight : CNLTransition → ℝ
  /-- The CNL entropy slope. -/
  c : ℝ
  /-- The one-step Kraft constant. -/
  CQ : ℝ
  /-- The proved depth-`M` coordinatization of the selected cluster: `coherent`,
  `path_injOn`, `root_eq`, `height_additive` are theorems, and it yields the
  prefactor-free Kraft bound `cleanCNLKraftSum … ≤ CQ ^ M`. -/
  coord : ClusterLadderCoordinatization T BNDHeight c CQ
  /-- The shell entropy factor `2^{-c₀ηY}`. -/
  shellFactor : ℝ
  /-- The dyadic interval length `|I_j|`. -/
  Ij : ℝ
  shellFactor_nonneg : 0 ≤ shellFactor
  Ij_nonneg : 0 ≤ Ij
  /-- The **prefactor-free** shell-budget calibration (the only genuine numeric
  residue). -/
  hbudget : CQ ^ coord.M * shellFactor * X * Ij ≤ cStar * ξ * X / 6

/-- Build the cluster encoding datum (with `kraftSum_le` derived from the proved
coordinatization) from the reduced per-shell input. -/
def CNLCoordinatizedShellInput.build {cStar ξ X : ℝ}
    (inp : CNLCoordinatizedShellInput cStar ξ X) :
    CNLClusterEncodingData cStar ξ X :=
  cnlClusterEncodingDataOfCoordinatization inp.coord inp.shellFactor inp.Ij
    inp.shellFactor_nonneg inp.Ij_nonneg inp.hbudget

/--
**The `Erdos260MinimalAtoms.cnl` provider slot is dischargeable, non-vacuously.**

Given per-shell reduced inputs, produce the exact `cnl` provider field of the
round-1 `Erdos260MinimalAtoms`
(`∀ shell, shell.cQ = … → CNLClusterEncodingData …`).  Each produced datum's
`kraftSum_le` is the proved coordinatization bound, with **no** bridge labelling
and **no** `O(1)` prefactor — unlike `cnlProvider_ofUnconditional`, whose input
type `CNLUnconditionalKraftInput` is uninhabited. -/
def cnlProvider_ofCoordinatization
    (input :
      ∀ shell : FailingDyadicShell, shell.cQ = erdos260Constants.cQ →
        CNLCoordinatizedShellInput erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : ℝ)) :
    ∀ shell : FailingDyadicShell, shell.cQ = erdos260Constants.cQ →
      CNLClusterEncodingData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : ℝ) :=
  fun shell hcQ => (input shell hcQ).build

/-! ## Part 5. Non-vacuity -/

/--
**The pipeline fires from any injective lift-exponent labelling.**

Composes the established depth-`(m+1)` witness
`CleanClusterReconstruction.ofReplicatedInjectiveLabel` (projection step; genuine
`step_injOn`; `sym_injOn` from label injectivity) with the bridge-free encoding
builder.  No bridge data, no prefactor: a genuine, non-vacuous `CNLClusterEncodingData`. -/
def cnlClusterEncodingDataOfReplicatedInjectiveLabel
    {cStar ξ X : ℝ}
    (T : Finset CNLTransition) (BNDHeight : CNLTransition → ℝ) (c CQ : ℝ)
    (hc : 0 < c) (hCQ : (1 - (2 : ℝ) ^ (-c))⁻¹ ≤ CQ) (m : ℕ)
    (liftExp : CNLTransition → ℕ)
    (hinj :
      ∀ t₁ ∈ selectedTransitions T, ∀ t₂ ∈ selectedTransitions T,
        liftExp t₁ = liftExp t₂ → t₁ = t₂)
    (hheight :
      ∀ t ∈ selectedTransitions T, BNDHeight t = ((m + 1 : ℕ) : ℝ) * (liftExp t : ℝ))
    (shellFactor Ij : ℝ)
    (shellFactor_nonneg : 0 ≤ shellFactor) (Ij_nonneg : 0 ≤ Ij)
    (hbudget : CQ ^ (m + 1) * shellFactor * X * Ij ≤ cStar * ξ * X / 6) :
    CNLClusterEncodingData cStar ξ X :=
  cnlClusterEncodingDataOfCoordinatization
    (CleanClusterReconstruction.ofReplicatedInjectiveLabel
      T BNDHeight c CQ hc hCQ m liftExp hinj hheight).toCoordinatization
    shellFactor Ij shellFactor_nonneg Ij_nonneg hbudget

/-- The analogous reduced per-shell input from an injective lift-exponent labelling. -/
def CNLCoordinatizedShellInput.ofReplicatedInjectiveLabel
    {cStar ξ X : ℝ}
    (T : Finset CNLTransition) (BNDHeight : CNLTransition → ℝ) (c CQ : ℝ)
    (hc : 0 < c) (hCQ : (1 - (2 : ℝ) ^ (-c))⁻¹ ≤ CQ) (m : ℕ)
    (liftExp : CNLTransition → ℕ)
    (hinj :
      ∀ t₁ ∈ selectedTransitions T, ∀ t₂ ∈ selectedTransitions T,
        liftExp t₁ = liftExp t₂ → t₁ = t₂)
    (hheight :
      ∀ t ∈ selectedTransitions T, BNDHeight t = ((m + 1 : ℕ) : ℝ) * (liftExp t : ℝ))
    (shellFactor Ij : ℝ)
    (shellFactor_nonneg : 0 ≤ shellFactor) (Ij_nonneg : 0 ≤ Ij)
    (hbudget : CQ ^ (m + 1) * shellFactor * X * Ij ≤ cStar * ξ * X / 6) :
    CNLCoordinatizedShellInput cStar ξ X where
  T := T
  BNDHeight := BNDHeight
  c := c
  CQ := CQ
  coord :=
    (CleanClusterReconstruction.ofReplicatedInjectiveLabel
      T BNDHeight c CQ hc hCQ m liftExp hinj hheight).toCoordinatization
  shellFactor := shellFactor
  Ij := Ij
  shellFactor_nonneg := shellFactor_nonneg
  Ij_nonneg := Ij_nonneg
  hbudget := hbudget

/-- **Concrete closed inhabitant of the reduced input** (no free hypotheses): the
empty cluster at slope `c = 1`, `C_Q = 2`, depth `M = 1`, with a genuine positive
budget `2 · (1/12) · 1 · 1 = 1/6 ≤ 1/6`.  Witnesses that `CNLCoordinatizedShellInput`
is inhabited. -/
def cnlCoordinatizedShellInput_witness :
    CNLCoordinatizedShellInput (1 : ℝ) (1 : ℝ) (1 : ℝ) :=
  CNLCoordinatizedShellInput.ofReplicatedInjectiveLabel
    (∅ : Finset CNLTransition) (fun _ => 0) 1 2
    (by norm_num)
    (cnl_cq_dominates_of_c_ge_one (by norm_num) (by norm_num))
    0 (fun _ => 0)
    (by intro t₁ ht₁; simp [selectedTransitions] at ht₁)
    (by intro t ht; simp [selectedTransitions] at ht)
    (1 / 12) 1 (by norm_num) (by norm_num)
    (by norm_num)

/-- **Concrete closed inhabitant of the encoding datum** built from the reduced
input — the bridge-free, prefactor-free analogue of an inhabited `cnl` payload. -/
def cnlEncodingData_witness : CNLClusterEncodingData (1 : ℝ) (1 : ℝ) (1 : ℝ) :=
  cnlCoordinatizedShellInput_witness.build

/-! ## Part 6. Headline statements -/

/-- **Headline.**  The proved coordinatization core plus the prefactor-free shell
budget yield a genuine `CNLClusterEncodingData` — the bridge labelling having been
eliminated (and shown vacuous), the additive BND height reduced to
`pathHeight_descentBranch`, and only the shell-budget calibration remaining. -/
theorem cnlClusterEncodingData_ofCoordinatization_exists
    {cStar ξ X : ℝ}
    {T : Finset CNLTransition} {BNDHeight : CNLTransition → ℝ} {c CQ : ℝ}
    (coord : ClusterLadderCoordinatization T BNDHeight c CQ)
    (shellFactor Ij : ℝ)
    (shellFactor_nonneg : 0 ≤ shellFactor) (Ij_nonneg : 0 ≤ Ij)
    (hbudget : CQ ^ coord.M * shellFactor * X * Ij ≤ cStar * ξ * X / 6) :
    Nonempty (CNLClusterEncodingData cStar ξ X) :=
  ⟨cnlClusterEncodingDataOfCoordinatization coord shellFactor Ij shellFactor_nonneg
    Ij_nonneg hbudget⟩

/-! ## Part 7. Honest status inventory -/

/-- Per-field honesty report on reducing `CNLUnconditionalKraftInput` (the round-2
`cnlInput` slot) from the proved coordinatization core. -/
def cnlBridgeReductionStatus : List String :=
  [ "hE/hwin/hpos (bridge labelling): VACUOUS, hence ELIMINATED.  hwin+hpos force " ++
      "bridgeExp StrictAnti on all of ℕ (Lemma G.3 bridgeExp_strictAnti); hE with " ++
      "E : ℕ → ℕ forces bridgeExp ≥ 0 everywhere; no strictly decreasing ℤ-sequence " ++
      "stays ≥ 0 (no_strictAnti_nat).  Proved: bridge_labelling_vacuous, " ++
      "cnlUnconditionalKraftInput_uninhabited.  The genuine reduction bypasses the " ++
      "bridge labelling and uses a genuinely injective step (projection decode).",
    "g/sm/gOld/s/E/sym (bridge data): ELIMINATED.  Not needed by the coordinatization " ++
      "route; step-determinism is supplied by a genuine injective step, sym_injOn is " ++
      "closed on the cleaned family (CNLCodeFaithfulness.exists_codeClean_subfamily).",
    "hM (M ≠ 0): ELIMINATED.  Used in round 1 only for the (B·CQ₀^M)^(1/M) fold; the " ++
      "coordinatization route takes kraftSum_le ≤ CQ^M verbatim, no fold, no M ≠ 0.",
    "hheight (additive BND height): REDUCED to the coordinatization's height_additive, " ++
      "i.e. BNDHeight t = pathHeight ladderHeight (descentBranch (nodeOf t) M) via the " ++
      "proved telescoping pathHeight_descentBranch " ++
      "(bndHeight_eq_pathHeight_of_coordinatization, reconHeight_eq_sum).",
    "T/BNDHeight/c/CQ/hc/hCQ: REDUCED — subsumed as the parameters/fields of the " ++
      "ClusterLadderCoordinatization (c via hc_pos, CQ via hCQ_dom, M via coord.M).",
    "shellFactor/Ij/shellFactor_nonneg/Ij_nonneg: basic shell data, carried verbatim.",
    "hbudget (shell-budget calibration): IRREDUCIBLE, and now PREFACTOR-FREE " ++
      "(CQ^M·shellFactor·X·Ij ≤ cStar·ξ·X/6) — strictly weaker than round 1's " ++
      "(Fintype.card CNLTransition)·CQ^M·…  This is the single genuine numeric residue.",
    "Existence of the coordinatization (the deep residue): reduced to sym_injOn, which " ++
      "is CLOSED on the cleaned family by the L.1.2a–d transversal; coherent/path_injOn/" ++
      "root_eq/height_additive are theorems in the proved core.",
    "Provider: cnlProvider_ofCoordinatization inhabits Erdos260MinimalAtoms.cnl " ++
      "(round-1 base of erdos260_reduced_minimal) NON-VACUOUSLY; non-vacuity witnessed " ++
      "by cnlClusterEncodingDataOfReplicatedInjectiveLabel and cnlEncodingData_witness." ]

theorem cnlBridgeReductionStatus_nonempty : cnlBridgeReductionStatus ≠ [] := by
  simp [cnlBridgeReductionStatus]

end

end Erdos260
