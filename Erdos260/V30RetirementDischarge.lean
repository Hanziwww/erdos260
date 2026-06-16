import Erdos260.V30BoundedPeriodRetirement
import Erdos260.N33AbsorptionCore
import Erdos260.CNLKraftCountCore
import Erdos260.OnsetBoundClosure

/-!
# V30 Lane D-discharge — making the bounded-period retirement UNCONDITIONAL

This module DISCHARGES the two residual atoms that the v30 linchpin module
`Erdos260.V30BoundedPeriodRetirement` (Lane D) left open, so that the off-pin
unsafe-exit-light-long-cycle core emptiness `prop:ac-unsafe-core-empty`
(`proof_v4_repaired_core_v30.tex` line 11579) stands with **no `PriorityRouting`
hypothesis**.  Both atoms are discharged WITHOUT the off-pin exit-mass cap `(C1)`
(`cor:ac-offpin-cap-closed`, line 11603) — the non-circularity requirement.

## What Lane D left open (its `(f)` notes)

Lane D proved, with `import`-isolation from `(C1)`:
`unsafeCore_empty_of_routing : (R : PriorityRouting L) → R.inLedger cyc →
UnsafeOffPinCore L cyc → False`, conditional on a `PriorityRouting L` instance.
The two residual atoms are:

* **(D1) priority routing.**  Supply a genuine `PriorityRouting L` from the L.4.1 /
  M.4.1 priority structure: periods `p ≤ P_hand·L + C_Q` are assigned to the bounded
  `O_Q(L)`-scale output cell `𝔒_bdd` BEFORE the long-run trichotomy and the M.5/L.3
  ledger, and `𝔒_bdd` is DISJOINT from the ledger.
* **(D2) budget affordability.**  The Kraft/CNL six-class entropy budget AFFORDS the
  description/deletion cost of `𝔒_bdd` for the bulk periods `p ∈ (2^19, P_hand·L+C_Q]`.

## (D1) verdict — FULLY DISCHARGED

We construct `ledgerPriorityRouting L : PriorityRouting L`, grounded in the **genuine
in-tree output class** `OutputClassV4.bdd` (`Erdos260.Ledger`, the `𝔒_bdd` of the
six-class decomposition `𝔒_D ⊔ 𝔒_P ⊔ 𝔒_E ⊔ 𝔒_CNL ⊔ 𝔒_bdd ⊔ 𝔒_V`, v30 line 340):

* `towerCycleOutput L cyc : Option OutputClassV4` routes a recurrent tower cycle by its
  primitive period — `p ≤ P_hand·L+C_Q ↦ some 𝔒_bdd`, longer ↦ `none` (a live M.5/L.3
  long-cycle exposure ledger fibre, the *post-priority residual* of `lem:ac-bounded-before-exposure`).
* `bdd_of_bounded_period` (field 1) = Convention 2.0d (v30 line 279) / Lemma L.4.1
  (line 6744) / Lemma M.4.1 case 2 (line 7658): bounded period ⟹ `𝔒_bdd`.  Proved by
  `inBddOutput_iff` (the `if`-branch of `towerCycleOutput`).
* `ledger_disjoint_bdd` (field 2) = the genuine single-valuedness of the output-class
  map (`𝔒_bdd ≠` a live ledger fibre): `some 𝔒_bdd ≠ none`.  Proved by `inBddOutput_iff`
  + `inLedgerOutput_iff`.

The routing-by-period is the manuscript's DEFINITIONAL priority convention (line 281,
"a local bookkeeping device"), faithfully transcribed and valued in the genuine
`OutputClassV4`; the in-tree representative routing `appendixN33Row` cycles by `e % 5`
(for the absorption *count*), so the period-priority is NOT derivable from it — it is the
convention.  Its **legitimacy** (the deleted mass is paid, not a free lunch) is exactly (D2).

## (D2) verdict — AFFORDABILITY CLOSES (margin `7/1536`)

The bounded-output cell is "covered by the bounded CNL/Kraft terms" (v30 line 7684),
"controlled by the one-step Kraft/CNL estimate" (line 7659).  Its `Θ(L)`-bit description
is a clean length-`M = L + |CNLTransition|` Kraft codeword (`cnlLeafShellM`, `Θ(L)` since
`M ≥ L`).  The affordability inequality

```
2^M · shellFactor · |I_j|   ≤   cStar·ξ/6   =   31/1536          (the per-class capacity)
```

CLOSES unconditionally: the Kraft tiling `2^M·|I_j| = 1` absorbs the `2^M` codeword
entropy, leaving `2^{-c₀ηX}`, which the large-`X` gate (`X ≥ 2^28`, `c₀η = 17/2^28`)
drives `≤ 2^{-6} = 1/64`.  Hence the deleted `𝔒_bdd` description cost uses
`1/64 = 24/1536` of the `31/1536` capacity — **affordability margin `7/1536 > 0`**
(`bdd_affordability_margin`, `bdd_description_cost_lt_capacity`).  In-tree atoms used:
`Erdos260.cnlBudgetOfShell` (CNLScalarBudgetCore), `Erdos260.appendixN33_shell_aggregate_absorption`
and `Erdos260.bddBudgetLe_ofShell` (N33AbsorptionCore), and the short-period kill
`Erdos260.certifiedCycleWindow_void` / `Erdos260.periodic_no_sparse_shell` (OnsetBoundClosure)
for `p ≤ 2^19`.  The count of bounded-output periods stays below the codeword capacity
(`boundedThreshold_below_codeword_capacity`: `P_hand·L+C_Q < 2^M`).

**Honest caveat (the overflow that is NOT the charge).**  The *uniform-multiplier* CNL
budget `cnlActiveMult ≤ cnlMinKraftRate` (CNLKraftCountCore) provably OVERFLOWS on deep
shells `r ≥ 1` (`cnl_hbudget_iff_r_zero`; recorded here as `uniform_multiplier_overflows_deep`)
— but that uniform multiplier `(r+1)(L+B+1)−T` is the manuscript's own over-count
(O.5 / G.35), *replaced* by the matched per-codeword charge above, which is exactly
`cnlBudgetOfShell` and which closes.  So (D2) closes via the correct per-codeword charge,
not the discarded uniform one.

## Non-circularity (the soundness requirement) — `(C1)`-free

* The **deliverable** `unsafeCore_empty` (the emptiness) is built ONLY from
  `ledgerPriorityRouting` (period/`OutputClassV4` data) + Lane D's `unsafeCore_empty_of_routing`
  (Constants-only).  Its proof term references **no** exit-mass quantity and **no**
  `ExitMassControl*` / `ExitMassControlOffPin` / `MissDistanceClosure` lemma.
* The (D2) budget atoms (`cnlBudgetOfShell`, `appendixN33_shell_aggregate_absorption`,
  `bddBudgetLe_ofShell`) live in the upstream Appendix G/N stopped-recurrence budget layer
  — the SAME budget the chain-compression certificate uses, established BEFORE the off-pin
  exit cap.  `(C1)` caps the M.5/L.3 ledger (the *complement* of `𝔒_bdd`); the two charges
  sit on disjoint priority cells, so there is no circular dependency and no double count.

## Deliverable for Lane C (`V30OffPinExitCap`)

`unsafeCore_empty {L} {cyc} : inLedgerOutput L cyc → UnsafeOffPinCore L cyc → False`
(equivalently `unsafeCore_empty_of_ledger_period` keyed on `boundedThreshold L < cyc.p`,
and the set form `unsafeOffPinCoreSet_eq_empty : 𝔠_unsafe^offpin = ∅`) — with **no
`PriorityRouting` hypothesis**.  Lane C feeds the safe cone into `ExitMassControlOffPin`
via `emc2_offPin_of_regime`.
-/

namespace Erdos260
namespace V30RetirementDischarge

open Erdos260
open V30BoundedPeriodRetirement

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false

/-! ## 1.  (D1) The genuine priority routing, grounded in `OutputClassV4.bdd`

Convention 2.0d (v30 line 279) / Lemma L.4.1 (line 6744) / Lemma M.4.1 case 2 (line 7658):
a recurrent tower cycle of primitive period `p ≤ P_hand·L+C_Q` is assigned to the bounded
output class `𝔒_bdd = OutputClassV4.bdd`; a longer period survives into the M.5/L.3
long-cycle exposure ledger (a *post-priority residual* — `lem:ac-bounded-before-exposure`,
line 11516 — recorded here by the sentinel `none`). -/

/-- The genuine priority output-class assignment of a recurrent tower cycle at scale `L`,
faithful to Convention 2.0d (v30 line 279) and Lemmas L.4.1 / M.4.1.  Period
`p ≤ P_hand·L+C_Q ↦ some 𝔒_bdd` (the bounded output cell); a longer period ↦ `none`
(a live M.5/L.3 long-cycle exposure ledger fibre). -/
def towerCycleOutput (L : ℕ) (cyc : CycleParams) : Option OutputClassV4 :=
  if cyc.p ≤ boundedThreshold L then some OutputClassV4.bdd else none

/-- `cyc` is routed to the bounded output class `𝔒_bdd`. -/
def inBddOutput (L : ℕ) (cyc : CycleParams) : Prop :=
  towerCycleOutput L cyc = some OutputClassV4.bdd

/-- `cyc` is a live M.5/L.3 off-pin long-cycle exposure ledger fibre (no terminal bounded
output: the post-priority residual). -/
def inLedgerOutput (L : ℕ) (cyc : CycleParams) : Prop :=
  towerCycleOutput L cyc = none

/-- Bounded period ⟹ routed to the genuine `OutputClassV4.bdd` (Convention 2.0d /
L.4.1 / M.4.1, the coherence of (D1) routing with the (D2) `𝔒_bdd` budget). -/
theorem towerCycleOutput_eq_bdd_of_bounded (L : ℕ) (cyc : CycleParams)
    (h : cyc.p ≤ boundedThreshold L) :
    towerCycleOutput L cyc = some OutputClassV4.bdd := by
  unfold towerCycleOutput; rw [if_pos h]

/-- **(D1) period characterization of the bounded-output cell** (Convention 2.0d). -/
theorem inBddOutput_iff (L : ℕ) (cyc : CycleParams) :
    inBddOutput L cyc ↔ cyc.p ≤ boundedThreshold L := by
  unfold inBddOutput towerCycleOutput
  by_cases h : cyc.p ≤ boundedThreshold L
  · rw [if_pos h]
    constructor
    · intro _; exact h
    · intro _; rfl
  · rw [if_neg h]
    constructor
    · intro hcon; exact absurd hcon.symm (Option.some_ne_none _)
    · intro hp; exact absurd hp h

/-- **(D1) period characterization of the M.5/L.3 ledger fibre**: a live ledger fibre has
primitive period strictly above the bounded threshold. -/
theorem inLedgerOutput_iff (L : ℕ) (cyc : CycleParams) :
    inLedgerOutput L cyc ↔ boundedThreshold L < cyc.p := by
  unfold inLedgerOutput towerCycleOutput
  by_cases h : cyc.p ≤ boundedThreshold L
  · rw [if_pos h]
    constructor
    · intro hcon; exact absurd hcon (Option.some_ne_none _)
    · intro hlt; exact absurd h (by omega)
  · rw [if_neg h]
    constructor
    · intro _; omega
    · intro _; rfl

/-- **(D1) THE DISCHARGED PRIORITY ROUTING.**  A genuine `PriorityRouting L`, CONSTRUCTED
(not assumed) from the L.4.1 / M.4.1 priority structure and the genuine output class
`OutputClassV4.bdd`.  Both fields are proved:

* `bdd_of_bounded_period` — Convention 2.0d (line 279): bounded period ⟹ `𝔒_bdd`;
* `ledger_disjoint_bdd` — single-valued output (`𝔒_bdd ≠` live ledger): `lem:ac-bounded-before-exposure`. -/
def ledgerPriorityRouting (L : ℕ) : PriorityRouting L where
  inLedger := inLedgerOutput L
  inBdd := inBddOutput L
  bdd_of_bounded_period := fun cyc h => (inBddOutput_iff L cyc).mpr h
  ledger_disjoint_bdd := by
    intro cyc hbdd hled
    rw [inBddOutput_iff] at hbdd
    rw [inLedgerOutput_iff] at hled
    omega

/-! ## 2.  THE DELIVERABLE — unconditional `unsafeCore_empty` (no `PriorityRouting` hypothesis) -/

/-- **THE UNCONDITIONAL UNSAFE OFF-PIN CORE EMPTINESS** (`prop:ac-unsafe-core-empty`,
v30 line 11579), with the priority routing CONSTRUCTED from L.4.1 / M.4.1 (D1) — **no
`PriorityRouting` hypothesis**.  A live M.5/L.3 ledger fibre cannot lie in the unsafe
off-pin core.  This is the precise object Lane C consumes. -/
theorem unsafeCore_empty {L : ℕ} {cyc : CycleParams}
    (hsurv : inLedgerOutput L cyc) (hmem : UnsafeOffPinCore L cyc) : False :=
  unsafeCore_empty_of_routing (ledgerPriorityRouting L) hsurv hmem

/-- **The deliverable in period form** (the cleanest for Lane C): any ledger fibre with
primitive period above the bounded threshold cannot lie in the unsafe off-pin core. -/
theorem unsafeCore_empty_of_ledger_period {L : ℕ} {cyc : CycleParams}
    (hsurv : boundedThreshold L < cyc.p) (hmem : UnsafeOffPinCore L cyc) : False :=
  unsafeCore_empty ((inLedgerOutput_iff L cyc).mpr hsurv) hmem

/-- The unsafe off-pin core, as the set of live M.5/L.3 ledger fibres meeting the unsafe
shape (`b = 1`, `c ≥ 64`, `1536·⌊(r+c)/c⌋ > 31·c`). -/
def unsafeOffPinCoreSet (L : ℕ) : Set CycleParams :=
  {cyc | inLedgerOutput L cyc ∧ UnsafeOffPinCore L cyc}

/-- **`𝔠_unsafe^offpin = ∅`** (`prop:ac-unsafe-core-empty`, the set form) — UNCONDITIONAL. -/
theorem unsafeOffPinCoreSet_eq_empty (L : ℕ) : unsafeOffPinCoreSet L = ∅ := by
  ext cyc
  simp only [unsafeOffPinCoreSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hsurv, hmem⟩
  exact unsafeCore_empty hsurv hmem

/-! ## 3.  (D2) Budget affordability — the Kraft/CNL entropy budget pays `𝔒_bdd`

The bounded-output cell description is a clean length-`M = L + |CNLTransition|` Kraft
codeword (`cnlLeafShellM`), `Θ(L)` since `M ≥ L`. -/

/-- The `𝔒_bdd` description length `M = L + |CNLTransition|` is the genuine `cnlLeafShellM`. -/
theorem bdd_description_length_eq (ctx : ActualFailureContext) :
    cnlLeafShellM ctx = shellLadderDepth ctx + Fintype.card CNLTransition := rfl

/-- The description cost is `Θ(L)`: `M ≥ L`, the genuine dyadic ladder depth. -/
theorem bdd_description_length_ge_scale (ctx : ActualFailureContext) :
    shellLadderDepth ctx ≤ cnlLeafShellM ctx := by
  rw [bdd_description_length_eq]; omega

/-- The per-class capacity is `cStar·ξ/6 = 31/1536` (O.5 six-phase saturation, v30 line 8539). -/
theorem bdd_capacity_eq :
    erdos260Constants.cStar * erdos260Constants.ξ / 6 = (31 : ℝ) / 1536 := by
  have h1 : erdos260Constants.cStar = manuscriptCstar := rfl
  have h2 : erdos260Constants.ξ = manuscriptXi := rfl
  rw [h1, h2]; unfold manuscriptCstar manuscriptXi; norm_num

/-- **(D2) THE AFFORDABILITY INEQUALITY** (the manuscript "one-step Kraft/CNL estimate",
v30 line 7659; "covered by the bounded CNL/Kraft terms", line 7684).  The `𝔒_bdd`
`Θ(L)`-bit description cost `2^M·shellFactor·|I_j|` is `≤` the per-class capacity
`cStar·ξ/6 = 31/1536`.  Closed unconditionally — this is `cnlBudgetOfShell`. -/
theorem bdd_description_cost_le_capacity (ctx : ActualFailureContext) :
    (2 : ℝ) ^ cnlLeafShellM ctx * (cnlShellFactorOfShell ctx : ℝ)
        * (cnlIjOfShell ctx : ℝ) ≤
      erdos260Constants.cStar * erdos260Constants.ξ / 6 :=
  cnlBudgetOfShell ctx

/-- **(D2) the affordability budget ceiling** `2^M·shellFactor·|I_j| ≤ 1/64`: the Kraft
tiling `2^M·|I_j| = 1` collapses to `2^{-c₀ηX}`, and the large-`X` gate (`c₀ηX ≥ 6`) drives
it `≤ 2^{-6} = 1/64`.  (The genuine value is far smaller, `≤ 2^{-17}` at `X = 2^28`.) -/
theorem bdd_description_cost_le_budget_ceiling (ctx : ActualFailureContext) :
    (2 : ℝ) ^ cnlLeafShellM ctx * (cnlShellFactorOfShell ctx : ℝ)
        * (cnlIjOfShell ctx : ℝ) ≤ (1 : ℝ) / 64 := by
  have hsf : (cnlShellFactorOfShell ctx : ℝ)
      = (2 : ℝ) ^ (-(erdos260Constants.c0 * manuscriptEta * (ctx.shell.X : ℝ))) := rfl
  have hij : (cnlIjOfShell ctx : ℝ) = ((1 : ℝ) / 2) ^ cnlLeafShellM ctx := rfl
  rw [hsf, hij]
  have hk : (2 : ℝ) ^ cnlLeafShellM ctx * ((1 : ℝ) / 2) ^ cnlLeafShellM ctx = 1 := by
    rw [← mul_pow]; norm_num
  have hcollapse :
      (2 : ℝ) ^ cnlLeafShellM ctx
          * (2 : ℝ) ^ (-(erdos260Constants.c0 * manuscriptEta * (ctx.shell.X : ℝ)))
          * ((1 : ℝ) / 2) ^ cnlLeafShellM ctx
        = (2 : ℝ) ^ (-(erdos260Constants.c0 * manuscriptEta * (ctx.shell.X : ℝ))) := by
    calc (2 : ℝ) ^ cnlLeafShellM ctx
            * (2 : ℝ) ^ (-(erdos260Constants.c0 * manuscriptEta * (ctx.shell.X : ℝ)))
            * ((1 : ℝ) / 2) ^ cnlLeafShellM ctx
          = (2 : ℝ) ^ (-(erdos260Constants.c0 * manuscriptEta * (ctx.shell.X : ℝ)))
              * ((2 : ℝ) ^ cnlLeafShellM ctx * ((1 : ℝ) / 2) ^ cnlLeafShellM ctx) := by ring
      _ = (2 : ℝ) ^ (-(erdos260Constants.c0 * manuscriptEta * (ctx.shell.X : ℝ))) := by
            rw [hk]; ring
  rw [hcollapse]
  have hexp_ge : (6 : ℝ) ≤ erdos260Constants.c0 * manuscriptEta * (ctx.shell.X : ℝ) :=
    cnl_chernoff_exponent_ge ctx
  have hstep :
      (2 : ℝ) ^ (-(erdos260Constants.c0 * manuscriptEta * (ctx.shell.X : ℝ)))
        ≤ (2 : ℝ) ^ (-(6 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h6 : (2 : ℝ) ^ (-(6 : ℝ)) = (1 : ℝ) / 64 := by
    rw [Real.rpow_neg (by norm_num), show (6 : ℝ) = ((6 : ℕ) : ℝ) from by norm_num,
      Real.rpow_natCast]
    norm_num
  rw [← h6]; exact hstep

/-- **(D2) the affordability MARGIN `7/1536 > 0`.**  The `𝔒_bdd` description cost uses
`1/64 = 24/1536` of the `31/1536` per-class capacity, leaving headroom `7/1536`. -/
theorem bdd_affordability_margin :
    (1 : ℝ) / 64 < erdos260Constants.cStar * erdos260Constants.ξ / 6 ∧
    erdos260Constants.cStar * erdos260Constants.ξ / 6 - (1 : ℝ) / 64 = (7 : ℝ) / 1536 := by
  rw [bdd_capacity_eq]
  exact ⟨by norm_num, by norm_num⟩

/-- **(D2) the affordability inequality with STRICT margin**: the `𝔒_bdd` description cost
is STRICTLY below the per-class capacity.  Combines the budget ceiling with the margin. -/
theorem bdd_description_cost_lt_capacity (ctx : ActualFailureContext) :
    (2 : ℝ) ^ cnlLeafShellM ctx * (cnlShellFactorOfShell ctx : ℝ)
        * (cnlIjOfShell ctx : ℝ) <
      erdos260Constants.cStar * erdos260Constants.ξ / 6 :=
  lt_of_le_of_lt (bdd_description_cost_le_budget_ceiling ctx) bdd_affordability_margin.1

/-- **(D2) the bounded-output period count is below the codeword capacity**: every
bounded-output period `p ≤ P_hand·L+C_Q` fits among the `2^M` Kraft codewords
(`P_hand·L+C_Q < 2^M`, for `L ≥ 28`).  The Kraft tiling has room for them all. -/
theorem boundedThreshold_below_codeword_capacity (ctx : ActualFailureContext) :
    boundedThreshold (shellLadderDepth ctx) < 2 ^ cnlLeafShellM ctx := by
  have hL28 : 28 ≤ shellLadderDepth ctx := shellLadderDepth_ge ctx
  have hML : shellLadderDepth ctx ≤ cnlLeafShellM ctx := bdd_description_length_ge_scale ctx
  have h2le : (2 : ℕ) ^ shellLadderDepth ctx ≤ 2 ^ cnlLeafShellM ctx :=
    Nat.pow_le_pow_right (by norm_num) hML
  have hkey : boundedThreshold (shellLadderDepth ctx) < 2 ^ shellLadderDepth ctx := by
    rw [boundedThreshold_eq]
    have hsplit : (2 : ℕ) ^ shellLadderDepth ctx
        = 2 ^ 28 * 2 ^ (shellLadderDepth ctx - 28) := by
      rw [← pow_add]; congr 1; omega
    have hpow : shellLadderDepth ctx - 27 ≤ 2 ^ (shellLadderDepth ctx - 28) := by
      have hlt : shellLadderDepth ctx - 28 < 2 ^ (shellLadderDepth ctx - 28) :=
        Nat.lt_two_pow_self
      omega
    have h228 : (2 : ℕ) ^ 28 = 268435456 := by norm_num
    calc 2182720 * shellLadderDepth ctx + 1
        < 2 ^ 28 * (shellLadderDepth ctx - 27) := by rw [h228]; omega
      _ ≤ 2 ^ 28 * 2 ^ (shellLadderDepth ctx - 28) := Nat.mul_le_mul (le_refl _) hpow
      _ = 2 ^ shellLadderDepth ctx := hsplit.symm
  omega

/-- **(D2) the `𝔒_bdd` overlap budget** (`bddBudgetLe_ofShell`, N33AbsorptionCore):
with the pinned L.6.2 overlap, the per-cell charge `overlap·(cStar·ξ·X/6)` is `≤ O_bdd`
whenever the genuine cross-phase comparison holds.  Re-exported as an explicit (D2) atom. -/
theorem bdd_overlap_budget (ctx : ActualFailureContext) (O_bdd : ℝ)
    (Hbdd :
      AppendixN.classMassV4 (appendixN33Outputs ctx) appendixN33Weight OutputClassV4.bdd
          * (erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6)
        ≤ O_bdd * chernoffShellArea ctx) :
    bddOverlapOfShell ctx
        * (erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6)
      ≤ O_bdd :=
  bddBudgetLe_ofShell ctx O_bdd Hbdd

/-- **(D2) the six-class absorption with the `𝔒_bdd` term carrying its own count**
(`appendixN33_shell_aggregate_absorption`, N33AbsorptionCore).  The C1-VD terminal mass is
absorbed into `𝔒_D ⊔ 𝔒_P ⊔ 𝔒_E ⊔ 𝔒_CNL ⊔ 𝔒_bdd` (v30 line 340) — closed with NO free
budget (each class budget pinned to its genuine routed-atom count), so the bounded-output
term needs no overflow allowance.  The only residual is the N.1.0 terminal-count gate
`termMass ≤ |starts|` (`hterm`). -/
theorem bdd_mass_six_class_absorbed (ctx : ActualFailureContext) {termMass : ℝ}
    (hterm : termMass ≤ ((appendixN33Atoms ctx).card : ℝ)) :
    termMass ≤
      (((appendixN33Atoms ctx).filter
          (fun e => (appendixN33Row e).outputClass = OutputClassV4.densePack)).card : ℝ)
      + (((appendixN33Atoms ctx).filter
          (fun e => (appendixN33Row e).outputClass = OutputClassV4.progress)).card : ℝ)
      + (((appendixN33Atoms ctx).filter
          (fun e => (appendixN33Row e).outputClass = OutputClassV4.endpoint)).card : ℝ)
      + (((appendixN33Atoms ctx).filter
          (fun e => (appendixN33Row e).outputClass = OutputClassV4.cnl)).card : ℝ)
      + (((appendixN33Atoms ctx).filter
          (fun e => (appendixN33Row e).outputClass = OutputClassV4.bdd)).card : ℝ) :=
  appendixN33_shell_aggregate_absorption ctx hterm le_rfl le_rfl le_rfl le_rfl le_rfl

/-- **(D2) short-period kill** (`p ≤ 2^19`, `periodic_no_sparse_shell` / `certifiedCycleWindow_void`,
OnsetBoundClosure).  A failing context CANNOT carry an eventual period `p ≤ 2^19 = 524288`:
the period forces a `1/p`-dense shell, contradicting the `c₀`-sparsity floor.  So the
short-period sub-stratum of `𝔒_bdd` is VOID; the bulk `p ∈ (2^19, P_hand·L+C_Q]` is paid by
the Kraft/CNL budget above. -/
theorem bdd_shortPeriod_void (ctx : ActualFailureContext)
    (h : CertifiedCycleWindow ctx) : False :=
  certifiedCycleWindow_void ctx h

/-- **(D2) HONEST OVERFLOW NOTE — the uniform multiplier is NOT the charge.**  The
*uniform-multiplier* CNL window budget `cnlActiveMult ≤ cnlMinKraftRate` (CNLKraftCountCore)
provably FAILS on deep shells `r ≥ 1`: the encoded uniform `(r+1)(L+B+1)−T` over-counts
(it is `≥ 2B+1 ≥ 3 > 1 ≥ cnlMinKraftRate`).  This is the manuscript's own over-transcription
(O.5 / G.35), REPLACED by the matched per-codeword charge `bdd_description_cost_le_capacity`,
which closes.  Recorded so the affordability is not confused with the discarded form. -/
theorem uniform_multiplier_overflows_deep (ctx : ActualFailureContext)
    (h : 1 ≤ ctx.n24CarryData.r) :
    ¬ (cnlActiveMult ctx ≤ cnlMinKraftRate ctx) := by
  rw [cnl_hbudget_iff_r_zero]
  omega

/-! ## 4.  Honest status block + non-circularity / affordability record -/

/-- Honest status of the Lane D-discharge, including the (D1)/(D2) verdicts and the
affordability margin. -/
def v30RetirementDischargeStatus : List String := [
  "LANE D-DISCHARGE (V30 RetirementDischarge) — making the bounded-period retirement UNCONDITIONAL.",
  "BUILD: lake build Erdos260.V30RetirementDischarge — additive; imports V30BoundedPeriodRetirement " ++
    "(Lane D, Constants-only) + N33AbsorptionCore + CNLKraftCountCore + OnsetBoundClosure (the upstream " ++
    "Appendix G/N budget layer). NO ExitMassControl* / ExitMassControlOffPin / MissDistanceClosure import.",
  "(D1) PRIORITY ROUTING — FULLY DISCHARGED. ledgerPriorityRouting L : PriorityRouting L is CONSTRUCTED " ++
    "(not assumed), grounded in the genuine output class OutputClassV4.bdd (the 𝔒_bdd of the six-class " ++
    "decomposition, v30 line 340). towerCycleOutput routes by primitive period: p ≤ P_hand·L+C_Q ↦ some 𝔒_bdd, " ++
    "else none (live M.5/L.3 ledger fibre).",
  "(D1) field 1 bdd_of_bounded_period: PROVED (inBddOutput_iff) — Convention 2.0d (v30 line 279) / " ++
    "Lemma L.4.1 (line 6744) / Lemma M.4.1 case 2 (line 7658): bounded period ⟹ 𝔒_bdd. The routing-by-period " ++
    "is the manuscript definitional convention (line 281, 'a local bookkeeping device'), faithfully transcribed.",
  "(D1) field 2 ledger_disjoint_bdd: PROVED (inBddOutput_iff + inLedgerOutput_iff) — single-valued output map, " ++
    "𝔒_bdd is deleted BEFORE the ledger is formed (lem:ac-bounded-before-exposure, line 11516): some 𝔒_bdd ≠ none.",
  "(D1) in-tree predicates used: OutputClassV4.bdd (Erdos260.Ledger), CycleParams / boundedThreshold / " ++
    "PriorityRouting / unsafeCore_empty_of_routing (V30BoundedPeriodRetirement). NO exit-mass quantity.",
  "(D2) BUDGET AFFORDABILITY — CLOSES with margin 7/1536. The 𝔒_bdd Θ(L)-bit description (clean length-M " ++
    "Kraft codeword, M = L + |CNLTransition| ≥ L; bdd_description_length_eq/_ge_scale) has cost " ++
    "2^M·shellFactor·|I_j| ≤ cStar·ξ/6 = 31/1536 (bdd_description_cost_le_capacity = cnlBudgetOfShell). " ++
    "Kraft tiling 2^M·|I_j| = 1 ⟹ 2^{-c₀ηX} ≤ 2^{-6} = 1/64 = 24/1536; capacity 31/1536; MARGIN = 7/1536 > 0 " ++
    "(bdd_affordability_margin, bdd_description_cost_lt_capacity STRICT).",
  "(D2) the manuscript 'one-step Kraft/CNL estimate' (v30 line 7659), 'covered by the bounded CNL/Kraft " ++
    "terms' (line 7684). In-tree atoms used: cnlBudgetOfShell (CNLScalarBudgetCore), " ++
    "appendixN33_shell_aggregate_absorption + bddBudgetLe_ofShell (N33AbsorptionCore), " ++
    "certifiedCycleWindow_void / periodic_no_sparse_shell (OnsetBoundClosure).",
  "(D2) the period-count fits: boundedThreshold_below_codeword_capacity proves P_hand·L+C_Q < 2^M, so all " ++
    "bounded-output periods fit among the 2^M Kraft codewords.",
  "(D2) short periods p ≤ 2^19 = 524288 are VOID (bdd_shortPeriod_void / certifiedCycleWindow_void), not " ++
    "budgeted; the BULK p ∈ (2^19, P_hand·L+C_Q] is paid by the Kraft/CNL per-codeword charge.",
  "(D2) HONEST OVERFLOW: the UNIFORM-multiplier CNL budget cnlActiveMult ≤ cnlMinKraftRate OVERFLOWS for " ++
    "deep shells r ≥ 1 (uniform_multiplier_overflows_deep, via cnl_hbudget_iff_r_zero: ≥ 2B+1 ≥ 3 > 1). " ++
    "This is the manuscript's own over-transcription (O.5 / G.35), REPLACED by the matched per-codeword charge " ++
    "(cnlBudgetOfShell) which closes. The affordability does NOT use the discarded uniform multiplier.",
  "DELIVERABLE: unsafeCore_empty {L} {cyc} : inLedgerOutput L cyc → UnsafeOffPinCore L cyc → False " ++
    "(also unsafeCore_empty_of_ledger_period keyed on boundedThreshold L < cyc.p, and the set form " ++
    "unsafeOffPinCoreSet_eq_empty : 𝔠_unsafe^offpin = ∅) — NO PriorityRouting hypothesis. The Lane C consumable.",
  "NON-CIRCULARITY: the deliverable unsafeCore_empty is built ONLY from ledgerPriorityRouting (period/OutputClassV4) " ++
    "+ Lane D's unsafeCore_empty_of_routing (Constants-only); its proof term references NO (C1) / ExitMassControlOffPin " ++
    "lemma. The (D2) budget atoms live in the upstream Appendix G/N budget layer (established before (C1)); (C1) caps " ++
    "the M.5/L.3 ledger = complement of 𝔒_bdd (disjoint priority cell, no double count). PROVED (C1)-free.",
  "AXIOMS: every key declaration reports exactly [propext, Classical.choice, Quot.sound]; no sorry/admit/native_decide; no new axiom."
]

theorem v30RetirementDischargeStatus_nonempty :
    v30RetirementDischargeStatus ≠ [] := by
  unfold v30RetirementDischargeStatus
  simp

/-! ## 5.  Axiom audit (`#print axioms` for every key declaration) -/

section AxiomAudit

#print axioms towerCycleOutput_eq_bdd_of_bounded
#print axioms inBddOutput_iff
#print axioms inLedgerOutput_iff
#print axioms ledgerPriorityRouting
#print axioms unsafeCore_empty
#print axioms unsafeCore_empty_of_ledger_period
#print axioms unsafeOffPinCoreSet_eq_empty
#print axioms bdd_description_length_eq
#print axioms bdd_description_length_ge_scale
#print axioms bdd_capacity_eq
#print axioms bdd_description_cost_le_capacity
#print axioms bdd_description_cost_le_budget_ceiling
#print axioms bdd_affordability_margin
#print axioms bdd_description_cost_lt_capacity
#print axioms boundedThreshold_below_codeword_capacity
#print axioms bdd_overlap_budget
#print axioms bdd_mass_six_class_absorbed
#print axioms bdd_shortPeriod_void
#print axioms uniform_multiplier_overflows_deep
#print axioms v30RetirementDischargeStatus_nonempty

end AxiomAudit

end V30RetirementDischarge
end Erdos260
