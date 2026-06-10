import Erdos260.ChernoffMatchedClosure
import Erdos260.ChernoffAntichainCore
import Erdos260.PressureFloorConstruction
import Erdos260.ChargedBranchMassCore

/-!
# Erdős #260 — the genuine §22 Chernoff seed: three fields CLOSED, the fourth PINNED

This module (NEW; it edits no existing file) attacks the four fields of
`ChernoffGenuineAreaSeedForBudget` (`ChernoffMatchedClosure.lean`), the multiplicity-aware
class-0 Chernoff seed over the genuine stopped-branch family `genuineCarryChern`:

```
hK    : ∀ ctx, chernoffClass0KraftSum ctx ≤ 1            (§22 antichain/Kraft measure-sum)
hne   : the genuine high-cost stopped-branch family is nonempty
hcard : |routedFibre … 0| ≤ |highCostSet (genuineCarryChern ctx)|   (I.4.2 shell-scaling count)
hdom  : windowExcess(k) ≤ weight (finRankMatch … k)       (matched J.1.7 per-path area domination)
```

## What is CLOSED unconditionally here (three of the four fields)

* **`hne` — CLOSED** (`chernoffGenuine_hne`).  The Lemma 21.1 pressure floor
  `carryData_pressureFloor` gives `cPr·X ≤ highExcessMass (highExcessStarts …)` with the pinned
  `cPr = 1/2 > 0` and `X ≥ 1`, so the high-excess start set is nonempty
  (`chernoffClass0_highExcessStarts_nonempty`); its image under the injective branch indexing is the
  stopped-branch family (`chernoffClass0_stoppedBranches_nonempty`), and with `Y = 0` the genuine
  high-cost set IS the whole family (`genuineCarryChern_highCostSet_eq`).  No hypothesis.

* **`hcard` — CLOSED, for EVERY routed budget** (`chernoffGenuine_hcard`).  The routed class-0 fibre
  is a filter of the high-excess starts (`routedFibre ⊆ highExcessStarts`), and
  `stoppedBranchOf a r` is injective on starts (`stoppedBranchOf_injective`, from hit-sequence
  strict monotonicity), so `|stoppedBranches| = |highExcessStarts| ≥ |routedFibre … 0|` — the
  genuine SHELL-SCALING I.4.2 progress count, with no `≤ 4` collapse and no hypothesis.

* **`hK` — CLOSED, together with the full §22 disjoint-fibre datum `kraft`**
  (`chernoffClass0KraftSum_le_one`, `chernoffClass0KraftFibres`).  Over a BARE
  `CarryDataFromFailure` the Kraft sum can exceed `1` (overlapping windows, repeated masses) — that
  caveat was correct.  But the CANONICAL N.24 carry datum is pinned (`rfl`-level, restated
  module-locally as `chernArea_*`): `T = 2L+1`, `Y = L/64` with `L = shellLadderDepth ≥ 28`,
  `starts` = the shell index window with `|starts| = |supportShell d X| < c₀·X < X = 2^L`.  Hence
  every stopped branch pays recorded cost `= gapWindow ≥ T + Y > 2L+1`, i.e. `≥ 2L+2`
  (`chernoffClass0_branchCost_ge`), the family has `< 2^L` members
  (`chernoffClass0_stoppedBranches_card_lt`), and the Kraft sum is `≤ 2^L·2^{-(2L+2)} = 2^{-(L+2)}
  ≤ 1`.  The disjoint-fibre datum `KraftAntichainFibres stoppedBranches (fun b => (1/2)^cost b)` is
  then CONSTRUCTED outright by converse-Kraft interval packing
  (`exists_disjoint_packed_fibres`, `kraftAntichainFibresOfPowSumLe`): consecutive dyadic blocks of
  exact size `2^{maxCost − cost b}` inside the root `[0, 2^{maxCost})`.  (The packing realizes the
  masses as genuine normalized disjoint fibre counts; it is a formal converse-Kraft realization —
  the manuscript's integer-carry fibres `Ω_π` themselves are not expressible from
  `CarryDataFromFailure`, which records hit/gap words, not carry digits.)

## What is PINNED (the fourth field): `small`/`hdom` ⟺ class-0 routing emptiness

The same pins produce a SCALE SEPARATION that pins the remaining field exactly: the family's
minimal dyadic weight is `2^{-maxCost} ≤ 2^{-(2L+2)} ≤ 1/4` (`chernoffClass0MinWeight_le_quarter`)
while every routed class-0 start carries `windowExcess ≥ Y = L/64 ≥ 7/16`
(`chernArea_Y_ge`).  Consequently:

* the uniform 22.1A small-excess calibration `hsmall : windowExcess(k) ≤ chernoffClass0MinWeight`
  holds IFF the routing assigns NO start to class 0 (`smallExcess_iff_class0FibreEmpty`); its
  intended nonempty-fibre reading FAILS for genuine carry data, and both entry forms
  (`…_of_costPaid`, `…_of_windowGapFloor`) force the same emptiness;
* the seed's own `hdom` forces the same emptiness (`class0FibreEmpty_of_genuineAreaSeed`), and
  conversely emptiness rebuilds the full seed from the closed `hK` with `hdom` vacuous, so
  **`ChernoffGenuineAreaSeedForBudget budget` is inhabited IFF
  `∀ ctx, routedFibre … (budget ctx).route 0 = ∅`** (`genuineAreaSeed_iff_class0FibreEmpty`) —
  the corrected calibrated surface is the routing statement itself.

## Assembly

`chernoffGenuineAreaSeed_of_kraft_smallExcess` builds the full
`ChernoffGenuineAreaSeedForBudget budget` from `(hK, hsmall)`;
`chernoffGenuineAreaSeed_of_smallExcess` needs `hsmall` alone (hK is closed);
`ChernoffGenuineAreaKraftSmallResidual` packages (`kraft`, `small`) — now constructible from
`small` alone (`ofSmall`) or from class-0 emptiness (`ofClass0FibreEmpty`), and conversely forcing
that emptiness (`chernoffKraftSmallResidual_iff_class0FibreEmpty`) — and produces the seed, the
exact ctx-pinned V3 ledger field `hChernoffField`, and the P9 endpoint
`erdos260_p9V3_of_chernoffKraftSmall`.  The sharpest entry is
`P9V3RunChernoffClass0EmptyResidual`, whose class-0 field is the SINGLE routing statement
`class0Empty : ∀ ctx, routedFibre … 0 = ∅`, with endpoint `erdos260_p9V3_of_chernoffClass0Empty`.

No `sorry`, `axiom`, `admit`, or `native_decide`; no empty/degenerate witness: the family is the
actual carry stopped-branch family, nonempty by the proved pressure floor, and the packed Kraft
fibres are genuine dyadic blocks of the exact prescribed positive sizes.
-/

namespace Erdos260

open Finset

set_option linter.unusedVariables false

noncomputable section

/-! ## 1.  `hne` — CLOSED: the genuine stopped-branch family is nonempty -/

/-- **The high-excess start set of the actual N.24 carry data is nonempty — unconditional.**
The Lemma 21.1 pressure floor `carryData_pressureFloor` gives
`cPr·X ≤ highExcessMass (highExcessStarts …)` with `cPr = 1/2 > 0` and `X ≥ 1`, and the
high-excess mass of the empty set is `0`. -/
theorem chernoffClass0_highExcessStarts_nonempty (ctx : ActualFailureContext) :
    (highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
      ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y).Nonempty := by
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  have hfloor := carryData_pressureFloor erdos260Constants.cPr_pos.le ctx.n24CarryData
  rw [hempty, highExcessMass_empty] at hfloor
  have hXpos : (0 : ℝ) < (ctx.shell.X : ℝ) := by exact_mod_cast ctx.shell.X_pos
  have hpos : 0 < erdos260Constants.cPr * (ctx.shell.X : ℝ) :=
    mul_pos erdos260Constants.cPr_pos hXpos
  linarith

/-- **The actual carry stopped-branch family is nonempty — unconditional.**  The family is the
image of the nonempty high-excess start set under the genuine I.9 branch indexing. -/
theorem chernoffClass0_stoppedBranches_nonempty (ctx : ActualFailureContext) :
    ctx.n24CarryData.stoppedBranches.Nonempty := by
  have h := chernoffClass0_highExcessStarts_nonempty ctx
  simpa [CarryDataFromFailure.stoppedBranches] using
    h.image (stoppedBranchOf ctx.n24CarryData.a ctx.n24CarryData.r)

/-- **The genuine high-cost set IS the stopped-branch family.**  `genuineCarryChern` has `Y = 0`,
so the high-cost filter keeps every branch. -/
theorem genuineCarryChern_highCostSet_eq (ctx : ActualFailureContext)
    (hK : chernoffClass0KraftSum ctx ≤ 1) :
    highCostSet (genuineCarryChern ctx hK).paths (genuineCarryChern ctx hK).cost
        (genuineCarryChern ctx hK).Y
      = ctx.n24CarryData.stoppedBranches :=
  highCostSet_eq_self_of_forall_ge (fun p _ => Nat.zero_le _)

/-- **Seed field 2 (`hne`) — CLOSED unconditionally.**  The genuine high-cost stopped-branch family
is nonempty at every failure context, for every Kraft input `hK`. -/
theorem chernoffGenuine_hne (ctx : ActualFailureContext)
    (hK : chernoffClass0KraftSum ctx ≤ 1) :
    (highCostSet (genuineCarryChern ctx hK).paths (genuineCarryChern ctx hK).cost
      (genuineCarryChern ctx hK).Y).Nonempty := by
  rw [genuineCarryChern_highCostSet_eq ctx hK]
  exact chernoffClass0_stoppedBranches_nonempty ctx

/-! ## 2.  `hcard` — CLOSED: the shell-scaling I.4.2 progress count, for every budget -/

/-- **The stopped-branch count equals the high-excess start count — unconditional.**  The I.9
branch indexing `stoppedBranchOf a r` is injective (hit-sequence strict monotonicity), so the
image count is exact. -/
theorem chernoffClass0_stoppedBranches_card_eq (ctx : ActualFailureContext) :
    ctx.n24CarryData.stoppedBranches.card
      = (highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
          ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y).card := by
  show ((highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
      ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y).image
        (stoppedBranchOf ctx.n24CarryData.a ctx.n24CarryData.r)).card = _
  exact Finset.card_image_of_injective _
    (stoppedBranchOf_injective ctx.n24CarryData.carry.hits ctx.n24CarryData.r)

/-- **Seed field 3 (`hcard`) — CLOSED unconditionally, for EVERY routed budget.**  The routed
class-0 fibre is a filter of the high-excess starts, and the genuine family has exactly one branch
per high-excess start, so the I.4.2 progress count holds with the genuine SHELL-SCALING right-hand
side `|stoppedBranches|` (never the deep-shell-false `4`). -/
theorem chernoffGenuine_hcard
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) (hK : chernoffClass0KraftSum ctx ≤ 1) :
    (routedFibre ctx.n24CarryData (budget ctx).route 0).card
      ≤ (highCostSet (genuineCarryChern ctx hK).paths (genuineCarryChern ctx hK).cost
          (genuineCarryChern ctx hK).Y).card :=
  calc (routedFibre ctx.n24CarryData (budget ctx).route 0).card
      ≤ (highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
          ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
    _ = ctx.n24CarryData.stoppedBranches.card :=
        (chernoffClass0_stoppedBranches_card_eq ctx).symm
    _ = (highCostSet (genuineCarryChern ctx hK).paths (genuineCarryChern ctx hK).cost
          (genuineCarryChern ctx hK).Y).card :=
        congrArg Finset.card (genuineCarryChern_highCostSet_eq ctx hK).symm

/-! ## 3.  `hK` — reduced to the §22 antichain disjoint-fibre datum (proof_v4 line 818) -/

/-- **Seed field 1 (`hK`) from the disjoint-fibre Kraft datum.**  The §22 antichain measure-sum
`chernoffClass0KraftSum ctx ≤ 1` follows from `KraftAntichainFibres` on the actual stopped
branches — the formal "`Ω_π` are disjoint subsets of `Ω_u`" of proof_v4 line 818 — via the proved
Kraft inequality `KraftAntichainFibres.sum_le_one`.  Over a BARE `CarryDataFromFailure` the
disjointness datum is a genuine input (overlapping windows can repeat dyadic masses and overflow
`1`); at the canonical N.24 pins it is CONSTRUCTED outright below (`chernoffClass0KraftFibres`),
so this bridge is now fed by a closed theorem rather than a hypothesis. -/
theorem chernoffClass0KraftSum_le_one_of_fibres
    (kraft : ∀ ctx : ActualFailureContext,
      KraftAntichainFibres ctx.n24CarryData.stoppedBranches
        (fun b => (1 / 2 : ℝ) ^ branchShellCost b)) :
    ∀ ctx : ActualFailureContext, chernoffClass0KraftSum ctx ≤ 1 :=
  fun ctx => (kraft ctx).sum_le_one

/-! ## 3b.  The canonical N.24 parameter pins (module-local restatements)

The canonical carry datum `ctx.n24CarryData` is pinned, `rfl`-level through the whole
`appendixNGapCanonicalYCarryLocalAt → … → toCarryData` construction chain, to the proof-v4
parameters `T = 2L + C_Q = 2L + 1`, `Y = ε·L = L/64`, `r = ⌊κL⌋`, and
`starts = Ico (firstIndexAbove X) (firstIndexAbove X + |supportShell d X|)`, where
`L = shellLadderDepth ctx` is the dyadic exponent `X = 2^L`.  The same pins exist in sibling
modules (`CNLMultiChargeUnconditional`, `ActiveWindowContainmentCore`, `CNLKraftCountCore`)
that are not in this import closure; they are restated here under module-local names. -/

/-- **Pin: the active floor is `Y = ε·L`** (`rfl` through the construction chain). -/
theorem chernArea_Y_eq (ctx : ActualFailureContext) :
    ctx.n24CarryData.Y = manuscriptEps * ((shellLadderDepth ctx : ℕ) : ℝ) := rfl

/-- Numeric form of the active floor: `Y = L/64` (the pinned `ε = 1/64`). -/
theorem chernArea_Y_eq_div (ctx : ActualFailureContext) :
    ctx.n24CarryData.Y = ((shellLadderDepth ctx : ℕ) : ℝ) / 64 := by
  rw [chernArea_Y_eq, manuscriptEps]
  ring

/-- **The active floor is uniformly large**: `Y ≥ 28/64 = 7/16` (the large-`X` gate forces
`L ≥ 28`). -/
theorem chernArea_Y_ge (ctx : ActualFailureContext) :
    (7 : ℝ) / 16 ≤ ctx.n24CarryData.Y := by
  rw [chernArea_Y_eq_div]
  have hL : (28 : ℝ) ≤ ((shellLadderDepth ctx : ℕ) : ℝ) := by
    exact_mod_cast shellLadderDepth_ge ctx
  linarith

/-- The canonical active floor is strictly positive. -/
theorem chernArea_Y_pos (ctx : ActualFailureContext) : 0 < ctx.n24CarryData.Y := by
  have h := chernArea_Y_ge ctx
  linarith

/-- **Pin: the residual threshold is `T = 2L + 1`** (`rfl` up to the pinned `C_Q = 1`). -/
theorem chernArea_T_eq (ctx : ActualFailureContext) :
    ctx.n24CarryData.T = 2 * ((shellLadderDepth ctx : ℕ) : ℝ) + 1 := by
  have h : ctx.n24CarryData.T
      = 2 * ((shellLadderDepth ctx : ℕ) : ℝ) + ((manuscriptCQ_T : ℕ) : ℝ) := rfl
  rw [h]
  norm_num [manuscriptCQ_T]

/-- **Pin: the start set is the dyadic shell index window** (`rfl`). -/
theorem chernArea_starts_eq (ctx : ActualFailureContext) :
    ctx.n24CarryData.starts
      = Finset.Ico (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X)
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card) := rfl

/-- **Pin: the shell scale is the dyadic power `X = 2^L`.** -/
theorem chernArea_X_eq (ctx : ActualFailureContext) :
    ctx.shell.X = 2 ^ shellLadderDepth ctx :=
  Classical.choose_spec ctx.shell.hXdyadic

/-- The start window has exactly `|supportShell d X|` members. -/
theorem chernArea_starts_card_eq (ctx : ActualFailureContext) :
    ctx.n24CarryData.starts.card = (supportShell ctx.shell.d ctx.shell.X).card := by
  rw [chernArea_starts_eq, Nat.card_Ico]
  omega

/-- **The failure hypothesis caps the support count below the scale**: on every failing shell,
`|supportShell d X| < X` (from `K < c₀·X` with `c₀ < κ < 1/16 < 1`). -/
theorem supportShell_card_lt_X (shell : FailingDyadicShell) :
    (supportShell shell.d shell.X).card < shell.X := by
  have hk16 : manuscriptKappa < 1 / 16 := manuscriptKappa_lt_one_sixteenth
  have hc1 : shell.c0 < 1 := lt_trans shell.hc0_lt_kappa (by linarith)
  have hlt : ((supportShell shell.d shell.X).card : ℝ) < (shell.X : ℝ) := by
    have h1 := shell.hfailure
    have h2 : shell.c0 * (shell.X : ℝ) < 1 * (shell.X : ℝ) :=
      mul_lt_mul_of_pos_right hc1 shell.X_pos_real
    rw [one_mul] at h2
    linarith
  exact_mod_cast hlt

/-! ## 3c.  The high-excess cost floor and the family count bound

The two genuinely quantitative facts behind the §22 Kraft closure: every stopped branch pays
recorded shell cost `≥ 2L + 2` (its start clears `windowExcess ≥ Y > 0`, so its gap window
clears `T + Y > 2L + 1`), while the whole family has fewer than `2^L` branches (one branch per
high-excess start, starts inside the failing shell window of size `< c₀·X < X = 2^L`).  Hence
the dyadic masses `2^{-cost}` sum to at most `2^L·2^{-(2L+2)} = 2^{-(L+2)} ≤ 1`. -/

/-- **The high-excess gap-window floor**: every high-excess start of the canonical carry datum
has `gapWindow ≥ 2L + 2` (its real window excess clears the positive floor `Y = L/64`, so the
window clears `T + Y > 2L + 1`). -/
theorem chernoffClass0_gapWindow_ge (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
      ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y) :
    2 * shellLadderDepth ctx + 2
      ≤ gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r := by
  have hY : ctx.n24CarryData.Y
      ≤ windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T :=
    (mem_highExcessStarts.mp hk).2
  have hL : (28 : ℝ) ≤ ((shellLadderDepth ctx : ℕ) : ℝ) := by
    exact_mod_cast shellLadderDepth_ge ctx
  rw [chernArea_Y_eq_div] at hY
  unfold windowExcess at hY
  rw [chernArea_T_eq] at hY
  unfold positivePart at hY
  by_cases h0 : (((gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r : ℕ) : ℝ)
      - (2 * ((shellLadderDepth ctx : ℕ) : ℝ) + 1)) ≤ 0
  · rw [max_eq_right h0] at hY
    exfalso
    linarith
  · have h0' := not_le.mp h0
    rw [max_eq_left h0'.le] at hY
    have hgt : 2 * shellLadderDepth ctx + 1
        < gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r := by
      have hcast : ((2 * shellLadderDepth ctx + 1 : ℕ) : ℝ)
          < ((gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r : ℕ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast hcast
    omega

/-- **The branch shell-cost floor**: every actual stopped branch records shell cost `≥ 2L + 2`
(the genuine telescoping `branchShellCost = gapWindow` plus the gap-window floor). -/
theorem chernoffClass0_branchCost_ge (ctx : ActualFailureContext) {b : StoppedBranch}
    (hb : b ∈ ctx.n24CarryData.stoppedBranches) :
    2 * shellLadderDepth ctx + 2 ≤ branchShellCost b := by
  have hb' : b ∈ (highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
      ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y).image
        (stoppedBranchOf ctx.n24CarryData.a ctx.n24CarryData.r) := by
    simpa [CarryDataFromFailure.stoppedBranches] using hb
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hb'
  rw [branchShellCost_stoppedBranchOf]
  exact chernoffClass0_gapWindow_ge ctx hk

/-- **The family count bound**: the actual stopped-branch family has fewer than `2^L` members
(one branch per high-excess start; the starts window has `|supportShell d X| < X = 2^L`
members by the failure hypothesis). -/
theorem chernoffClass0_stoppedBranches_card_lt (ctx : ActualFailureContext) :
    ctx.n24CarryData.stoppedBranches.card < 2 ^ shellLadderDepth ctx := by
  have h1 : ctx.n24CarryData.stoppedBranches.card ≤ ctx.n24CarryData.starts.card := by
    rw [chernoffClass0_stoppedBranches_card_eq ctx]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have h2 := chernArea_starts_card_eq ctx
  have h3 := supportShell_card_lt_X ctx.shell
  have h4 := chernArea_X_eq ctx
  omega

/-- **The maximal recorded shell cost of the genuine stopped-branch family.** -/
def chernoffClass0MaxCost (ctx : ActualFailureContext) : ℕ :=
  ctx.n24CarryData.stoppedBranches.sup branchShellCost

/-- **The ℕ-level Kraft packing bound**: at the root resolution `N = maxCost`, the prescribed
dyadic fibre sizes `2^{N − cost b}` of the actual stopped branches total at most `2^N`
(each size is `≤ 2^{N−(2L+2)}` by the cost floor; the family has `< 2^L ≤ 2^{2L+2}` members). -/
theorem chernoffClass0_powSum_le (ctx : ActualFailureContext) :
    ∑ b ∈ ctx.n24CarryData.stoppedBranches,
        2 ^ (chernoffClass0MaxCost ctx - branchShellCost b)
      ≤ 2 ^ chernoffClass0MaxCost ctx := by
  obtain ⟨b₀, hb₀⟩ := chernoffClass0_stoppedBranches_nonempty ctx
  have hc₀N : 2 * shellLadderDepth ctx + 2 ≤ chernoffClass0MaxCost ctx :=
    le_trans (chernoffClass0_branchCost_ge ctx hb₀) (Finset.le_sup hb₀)
  have hterm : ∀ b ∈ ctx.n24CarryData.stoppedBranches,
      2 ^ (chernoffClass0MaxCost ctx - branchShellCost b)
        ≤ 2 ^ (chernoffClass0MaxCost ctx - (2 * shellLadderDepth ctx + 2)) := by
    intro b hb
    exact Nat.pow_le_pow_right (by norm_num)
      (Nat.sub_le_sub_left (chernoffClass0_branchCost_ge ctx hb) _)
  calc ∑ b ∈ ctx.n24CarryData.stoppedBranches,
        2 ^ (chernoffClass0MaxCost ctx - branchShellCost b)
      ≤ ∑ _b ∈ ctx.n24CarryData.stoppedBranches,
          2 ^ (chernoffClass0MaxCost ctx - (2 * shellLadderDepth ctx + 2)) :=
        Finset.sum_le_sum hterm
    _ = ctx.n24CarryData.stoppedBranches.card
          * 2 ^ (chernoffClass0MaxCost ctx - (2 * shellLadderDepth ctx + 2)) :=
        Finset.sum_const_nat (fun _ _ => rfl)
    _ ≤ 2 ^ shellLadderDepth ctx
          * 2 ^ (chernoffClass0MaxCost ctx - (2 * shellLadderDepth ctx + 2)) :=
        Nat.mul_le_mul (chernoffClass0_stoppedBranches_card_lt ctx).le le_rfl
    _ = 2 ^ (shellLadderDepth ctx
          + (chernoffClass0MaxCost ctx - (2 * shellLadderDepth ctx + 2))) :=
        (pow_add 2 _ _).symm
    _ ≤ 2 ^ chernoffClass0MaxCost ctx :=
        Nat.pow_le_pow_right (by norm_num) (by omega)

/-! ## 3d.  The disjoint-fibre packing — `kraft` CLOSED, hence `hK` CLOSED

The converse-Kraft interval packing: whenever the prescribed dyadic sizes `2^{N − cost i}` of a
finite family total at most `2^N`, consecutive dyadic blocks inside the root `[0, 2^N)` realize
every mass `2^{-cost i}` as a normalized disjoint fibre count — exactly the
`KraftAntichainFibres` datum.  With the ℕ-level bound `chernoffClass0_powSum_le` this CLOSES the
`kraft` residual of this module outright, and `hK` follows through the proved
`KraftAntichainFibres.sum_le_one`. -/

/-- **Dyadic interval packing.**  For any finite family with prescribed sizes `2^{N − cost i}`,
there are pairwise-disjoint fibres of exactly those sizes packed consecutively from `base`
(inside `Ico base (base + total)`). -/
theorem exists_disjoint_packed_fibres {ι : Type*} [DecidableEq ι]
    (cost : ι → ℕ) (N : ℕ) (S : Finset ι) :
    ∀ base : ℕ,
      ∃ fibre : ι → Finset ℕ,
        (∀ i ∈ S, fibre i ⊆ Finset.Ico base (base + ∑ j ∈ S, 2 ^ (N - cost j))) ∧
        (∀ i ∈ S, (fibre i).card = 2 ^ (N - cost i)) ∧
        (∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (fibre i) (fibre j)) := by
  induction S using Finset.induction_on with
  | empty =>
      intro base
      exact ⟨fun _ => ∅,
        fun i hi => absurd hi (Finset.notMem_empty i),
        fun i hi => absurd hi (Finset.notMem_empty i),
        fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | @insert a S' ha ih =>
      intro base
      obtain ⟨fibre', hsub', hcard', hdisj'⟩ := ih (base + 2 ^ (N - cost a))
      refine ⟨fun i => if i = a then Finset.Ico base (base + 2 ^ (N - cost a)) else fibre' i,
        ?_, ?_, ?_⟩
      · intro i hi
        dsimp only
        rcases Finset.mem_insert.mp hi with heq | hi'
        · rw [if_pos heq, Finset.sum_insert ha]
          exact Finset.Ico_subset_Ico le_rfl (by omega)
        · have hia : i ≠ a := fun h => ha (h ▸ hi')
          rw [if_neg hia, Finset.sum_insert ha]
          exact (hsub' i hi').trans (Finset.Ico_subset_Ico (Nat.le_add_right base _)
            (le_of_eq (Nat.add_assoc base _ _)))
      · intro i hi
        dsimp only
        rcases Finset.mem_insert.mp hi with heq | hi'
        · rw [if_pos heq, heq, Nat.card_Ico]
          exact Nat.add_sub_cancel_left _ _
        · have hia : i ≠ a := fun h => ha (h ▸ hi')
          rw [if_neg hia]
          exact hcard' i hi'
      · intro i hi j hj hij
        dsimp only
        rcases Finset.mem_insert.mp hi with heqi | hi' <;>
          rcases Finset.mem_insert.mp hj with heqj | hj'
        · exact absurd (heqi.trans heqj.symm) hij
        · have hja : j ≠ a := fun h => ha (h ▸ hj')
          rw [if_pos heqi, if_neg hja]
          refine Finset.disjoint_left.mpr fun x hx hx' => ?_
          have h1 := Finset.mem_Ico.mp hx
          have h2 := Finset.mem_Ico.mp (hsub' j hj' hx')
          omega
        · have hia : i ≠ a := fun h => ha (h ▸ hi')
          rw [if_neg hia, if_pos heqj]
          refine Finset.disjoint_left.mpr fun x hx hx' => ?_
          have h1 := Finset.mem_Ico.mp (hsub' i hi' hx)
          have h2 := Finset.mem_Ico.mp hx'
          omega
        · have hia : i ≠ a := fun h => ha (h ▸ hi')
          have hja : j ≠ a := fun h => ha (h ▸ hj')
          rw [if_neg hia, if_neg hja]
          exact hdisj' i hi' j hj' hij

/-- **Converse Kraft packaging.**  From the per-branch resolution bound `cost ≤ N` and the
ℕ-level packing bound `∑ 2^{N − cost} ≤ 2^N`, the full `KraftAntichainFibres` datum for the
symbolic masses `2^{-cost}` exists outright: pack the dyadic blocks from `0` inside
`range (2^N)` and read the masses as normalized fibre counts (`ofCardPow`). -/
noncomputable def kraftAntichainFibresOfPowSumLe {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (cost : ι → ℕ) (N : ℕ)
    (hcost : ∀ i ∈ S, cost i ≤ N)
    (hsum : ∑ j ∈ S, 2 ^ (N - cost j) ≤ 2 ^ N) :
    KraftAntichainFibres S (fun i => (1 / 2 : ℝ) ^ cost i) :=
  let h := exists_disjoint_packed_fibres cost N S 0
  KraftAntichainFibres.ofCardPow S cost N h.choose hcost
    (fun i hi =>
      (h.choose_spec.1 i hi).trans
        (by
          rw [Finset.range_eq_Ico]
          exact Finset.Ico_subset_Ico le_rfl (by simpa using hsum)))
    (fun i hi => h.choose_spec.2.1 i hi)
    h.choose_spec.2.2

/-- **The §22 antichain disjoint-fibre datum — CLOSED unconditionally at the genuine carry
data.**  The `kraft` field of `ChernoffGenuineAreaKraftSmallResidual` is constructed outright:
the root resolution is `N = maxCost`, each stopped branch receives a genuine dyadic block of
exactly `2^{N − cost b}` integers, the blocks are pairwise disjoint inside `[0, 2^N)`, and each
branch mass `2^{-cost b}` is its normalized fibre count.  Inhabitation is possible because of
the proved cost floor (`≥ 2L+2`) and count bound (`< 2^L`): the total prescribed size is at
most `2^{N−(L+2)} ≤ 2^N`. -/
noncomputable def chernoffClass0KraftFibres (ctx : ActualFailureContext) :
    KraftAntichainFibres ctx.n24CarryData.stoppedBranches
      (fun b => (1 / 2 : ℝ) ^ branchShellCost b) :=
  kraftAntichainFibresOfPowSumLe ctx.n24CarryData.stoppedBranches branchShellCost
    (chernoffClass0MaxCost ctx)
    (fun _ hb => Finset.le_sup hb)
    (chernoffClass0_powSum_le ctx)

/-- **Seed field 1 (`hK`) — CLOSED unconditionally.**  The §22 antichain/Kraft measure-sum
`∑_{b ∈ stoppedBranches} 2^{-cost b} ≤ 1` holds at every actual failure context, through the
packed disjoint fibres and the proved Kraft inequality.  (Quantitatively the sum is even
`≤ 2^{-(L+2)}`.)  The earlier caveat stands for a BARE `CarryDataFromFailure` — overlapping
windows can repeat masses and overflow `1` — but the canonical N.24 pins `T = 2L+1`,
`Y = L/64 > 0`, `|starts| < 2^L` close it for the actual carry datum. -/
theorem chernoffClass0KraftSum_le_one (ctx : ActualFailureContext) :
    chernoffClass0KraftSum ctx ≤ 1 :=
  (chernoffClass0KraftFibres ctx).sum_le_one

/-! ## 4.  `hdom` — reduced to the uniform 22.1A small-excess calibration -/

/-- **The minimal dyadic area weight of the genuine stopped-branch family**, `2^{-maxCost}`.
Every branch weight of `genuineCarryChern` is `≥ chernoffClass0MinWeight ctx`. -/
def chernoffClass0MinWeight (ctx : ActualFailureContext) : ℝ :=
  (1 / 2 : ℝ) ^ chernoffClass0MaxCost ctx

theorem chernoffClass0MinWeight_pos (ctx : ActualFailureContext) :
    0 < chernoffClass0MinWeight ctx := by
  unfold chernoffClass0MinWeight
  positivity

/-- **Every genuine branch weight dominates the family's minimal dyadic weight.** -/
theorem chernoffClass0MinWeight_le_weight (ctx : ActualFailureContext)
    (hK : chernoffClass0KraftSum ctx ≤ 1) {b : StoppedBranch}
    (hb : b ∈ ctx.n24CarryData.stoppedBranches) :
    chernoffClass0MinWeight ctx ≤ (genuineCarryChern ctx hK).weight b := by
  show chernoffClass0MinWeight ctx ≤ (1 / 2 : ℝ) ^ branchShellCost b
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Finset.le_sup hb)

/-- **Seed field 4 (`hdom`) from the uniform small-excess calibration.**  If every routed class-0
start has `windowExcess(k) ≤ chernoffClass0MinWeight ctx` (the uniform 22.1A area-vs-measure
calibration), then the matched per-path area domination holds against the order-rank matching:
the match lands in the stopped family (by the CLOSED `hne`/`hcard`), and every landed weight is
`≥ chernoffClass0MinWeight ctx`.  This removes every `finRankMatch` reference from the residual.
(Section 4b below pins `hsmall` exactly: at the genuine carry data it is EQUIVALENT to class-0
routing emptiness, `smallExcess_iff_class0FibreEmpty`.) -/
theorem chernoffGenuine_hdom_of_smallExcess
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (hK : ∀ ctx : ActualFailureContext, chernoffClass0KraftSum ctx ≤ 1)
    (hne : ∀ ctx : ActualFailureContext,
      (highCostSet (genuineCarryChern ctx (hK ctx)).paths
        (genuineCarryChern ctx (hK ctx)).cost
        (genuineCarryChern ctx (hK ctx)).Y).Nonempty)
    (hsmall : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
        windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
          ≤ chernoffClass0MinWeight ctx) :
    ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
        windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
          ≤ (genuineCarryChern ctx (hK ctx)).weight
              (finRankMatch (routedFibre ctx.n24CarryData (budget ctx).route 0)
                (highCostSet (genuineCarryChern ctx (hK ctx)).paths
                  (genuineCarryChern ctx (hK ctx)).cost
                  (genuineCarryChern ctx (hK ctx)).Y)
                (hne ctx) k) := by
  intro ctx k hk
  have hmem := finRankMatch_mem (hne ctx)
    (chernoffGenuine_hcard budget ctx (hK ctx)) hk
  exact le_trans (hsmall ctx k hk)
    (chernoffClass0MinWeight_le_weight ctx (hK ctx) (mem_highCostSet.1 hmem).1)

/-! ### Entry forms for the small-excess calibration -/

/-- **Cost-paid entry form (the literal 22.1A shell-paid shape).**  If the recorded shell cost of
each routed class-0 start's own branch is paid by the residual threshold up to the minimal dyadic
weight (`branchShellCost − T ≤ 2^{-maxCost}`), the uniform small-excess calibration follows. -/
theorem chernoffClass0_smallExcess_of_costPaid
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (hpaid : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
        (branchShellCost (stoppedBranchOf ctx.n24CarryData.a ctx.n24CarryData.r k) : ℝ)
            - ctx.n24CarryData.T
          ≤ chernoffClass0MinWeight ctx) :
    ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
        windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
          ≤ chernoffClass0MinWeight ctx := by
  intro ctx k hk
  refine windowExcess_le_of_gapWindow_sub_le ?_ (chernoffClass0MinWeight_pos ctx).le
  have h := hpaid ctx k hk
  rwa [branchShellCost_stoppedBranchOf] at h

/-- **K.1.2 pointwise-gap entry form.**  Under an active-window gap ceiling
`hitGap a j ≤ g₀` on each routed class-0 descent window and the active-floor calibration
`(r+1)·g₀ − T ≤ 2^{-maxCost}`, the uniform small-excess calibration follows
(`windowExcess_le_window_gap_multiplier`). -/
theorem chernoffClass0_smallExcess_of_windowGapFloor
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (g₀ : ActualFailureContext → ℕ)
    (hgap : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
        ∀ j, k ≤ j → j ≤ k + ctx.n24CarryData.r → hitGap ctx.n24CarryData.a j ≤ g₀ ctx)
    (hfloor : ∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : ℝ) + 1) * (g₀ ctx : ℝ) - ctx.n24CarryData.T
        ≤ chernoffClass0MinWeight ctx) :
    ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
        windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
          ≤ chernoffClass0MinWeight ctx :=
  fun ctx k hk =>
    windowExcess_le_window_gap_multiplier (hgap ctx k hk) (hfloor ctx)
      (chernoffClass0MinWeight_pos ctx).le

/-! ## 4b.  The exact pin: the small-excess calibration ⟺ class-0 fibre emptiness

The genuine carry data PIN the calibration.  Scale separation: the family's minimal dyadic
weight is `2^{-maxCost} ≤ 2^{-(2L+2)} ≤ 1/4` (the family is nonempty and every branch costs
`≥ 2L+2`), while every routed class-0 start is a high-excess start with
`windowExcess ≥ Y = L/64 ≥ 7/16 > 1/4`.  So `hsmall` can never hold at a member of the routed
class-0 fibre: the uniform 22.1A small-excess calibration `windowExcess ≤ 2^{-maxCost}` is
EQUIVALENT to the routing statement `routedFibre … 0 = ∅`.  This is the class-0 analogue of the
class-1 pinning (`windowExcess_eq_Y_of_mem_class1Fibre` in `CNLMultiChargeUnconditional.lean`),
except that class 0 needs only the floor `Y ≤ windowExcess`, not an exact level set. -/

/-- The minimal dyadic weight of the genuine family is at most `1/4` (nonempty family, every
recorded cost `≥ 2L + 2 ≥ 2`). -/
theorem chernoffClass0MinWeight_le_quarter (ctx : ActualFailureContext) :
    chernoffClass0MinWeight ctx ≤ 1 / 4 := by
  obtain ⟨b₀, hb₀⟩ := chernoffClass0_stoppedBranches_nonempty ctx
  have hcost := chernoffClass0_branchCost_ge ctx hb₀
  have hsup : branchShellCost b₀ ≤ chernoffClass0MaxCost ctx := Finset.le_sup hb₀
  have h2 : 2 ≤ chernoffClass0MaxCost ctx := by omega
  calc chernoffClass0MinWeight ctx
      = (1 / 2 : ℝ) ^ chernoffClass0MaxCost ctx := rfl
    _ ≤ (1 / 2 : ℝ) ^ 2 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) h2
    _ ≤ 1 / 4 := by norm_num

/-- **Scale separation**: the minimal dyadic weight lies strictly below the active floor,
`2^{-maxCost} ≤ 1/4 < 7/16 ≤ Y`. -/
theorem chernoffClass0MinWeight_lt_Y (ctx : ActualFailureContext) :
    chernoffClass0MinWeight ctx < ctx.n24CarryData.Y := by
  have h1 := chernoffClass0MinWeight_le_quarter ctx
  have h2 := chernArea_Y_ge ctx
  linarith

/-- Every genuine branch weight is at most `1/4` (the per-branch form of the scale
separation). -/
theorem chernoffClass0_weight_le_quarter (ctx : ActualFailureContext)
    (hK : chernoffClass0KraftSum ctx ≤ 1) {b : StoppedBranch}
    (hb : b ∈ ctx.n24CarryData.stoppedBranches) :
    (genuineCarryChern ctx hK).weight b ≤ 1 / 4 := by
  have hcost := chernoffClass0_branchCost_ge ctx hb
  show (1 / 2 : ℝ) ^ branchShellCost b ≤ 1 / 4
  calc (1 / 2 : ℝ) ^ branchShellCost b
      ≤ (1 / 2 : ℝ) ^ 2 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    _ ≤ 1 / 4 := by norm_num

/-- Routed class-0 membership forces the high-excess floor `Y ≤ windowExcess`. -/
theorem chernArea_Y_le_windowExcess_of_mem_class0Fibre
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0) :
    ctx.n24CarryData.Y
      ≤ windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T :=
  (mem_highExcessStarts.mp (Finset.mem_filter.mp hk).1).2

/-- **The forcing direction**: the uniform small-excess calibration empties the routed class-0
fibre at every context (`windowExcess ≥ Y ≥ 7/16 > 1/4 ≥ 2^{-maxCost}` on any member). -/
theorem class0FibreEmpty_of_smallExcess
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (hsmall : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
        windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
          ≤ chernoffClass0MinWeight ctx) :
    ∀ ctx : ActualFailureContext,
      routedFibre ctx.n24CarryData (budget ctx).route 0 = ∅ := by
  intro ctx
  by_contra hne
  obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  have h1 := hsmall ctx k hk
  have h2 := chernArea_Y_le_windowExcess_of_mem_class0Fibre budget ctx hk
  have h3 := chernoffClass0MinWeight_lt_Y ctx
  linarith

/-- **The exact pin (`small` ⟺ emptiness)**: at the genuine carry data, the uniform 22.1A
small-excess calibration on the routed class-0 fibre holds IF AND ONLY IF the routing assigns
no start to class 0.  In particular the intended nonempty-fibre reading of the calibrated
surface FAILS for genuine carry data; the surface degenerates to a routing statement. -/
theorem smallExcess_iff_class0FibreEmpty
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx) :
    (∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
        windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
          ≤ chernoffClass0MinWeight ctx)
      ↔ ∀ ctx : ActualFailureContext,
          routedFibre ctx.n24CarryData (budget ctx).route 0 = ∅ := by
  constructor
  · exact class0FibreEmpty_of_smallExcess budget
  · intro hempty ctx k hk
    rw [hempty ctx] at hk
    exact absurd hk (Finset.notMem_empty k)

/-- The cost-paid entry premise (`branchShellCost − T ≤ 2^{-maxCost}`) likewise forces class-0
fibre emptiness — the literal 22.1A shell-paid shape is equally pinned. -/
theorem class0FibreEmpty_of_costPaid
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (hpaid : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
        (branchShellCost (stoppedBranchOf ctx.n24CarryData.a ctx.n24CarryData.r k) : ℝ)
            - ctx.n24CarryData.T
          ≤ chernoffClass0MinWeight ctx) :
    ∀ ctx : ActualFailureContext,
      routedFibre ctx.n24CarryData (budget ctx).route 0 = ∅ :=
  class0FibreEmpty_of_smallExcess budget
    (chernoffClass0_smallExcess_of_costPaid budget hpaid)

/-- The K.1.2 pointwise-gap entry premises likewise force class-0 fibre emptiness. -/
theorem class0FibreEmpty_of_windowGapFloor
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (g₀ : ActualFailureContext → ℕ)
    (hgap : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
        ∀ j, k ≤ j → j ≤ k + ctx.n24CarryData.r → hitGap ctx.n24CarryData.a j ≤ g₀ ctx)
    (hfloor : ∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : ℝ) + 1) * (g₀ ctx : ℝ) - ctx.n24CarryData.T
        ≤ chernoffClass0MinWeight ctx) :
    ∀ ctx : ActualFailureContext,
      routedFibre ctx.n24CarryData (budget ctx).route 0 = ∅ :=
  class0FibreEmpty_of_smallExcess budget
    (chernoffClass0_smallExcess_of_windowGapFloor budget g₀ hgap hfloor)

/-! ## 5.  Assembly — the seed from exactly the two reduced inputs -/

/-- **The full genuine area seed from `(hK, hsmall)`.**  Fields `hne` and `hcard` are the CLOSED
theorems above; `hdom` is derived from the uniform small-excess calibration.  This is the sharpest
current boundary of the class-0 Chernoff line: exactly two residual inputs remain. -/
def chernoffGenuineAreaSeed_of_kraft_smallExcess
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (hK : ∀ ctx : ActualFailureContext, chernoffClass0KraftSum ctx ≤ 1)
    (hsmall : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
        windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
          ≤ chernoffClass0MinWeight ctx) :
    ChernoffGenuineAreaSeedForBudget budget where
  hK := hK
  hne := fun ctx => chernoffGenuine_hne ctx (hK ctx)
  hcard := fun ctx => chernoffGenuine_hcard budget ctx (hK ctx)
  hdom := chernoffGenuine_hdom_of_smallExcess budget hK
    (fun ctx => chernoffGenuine_hne ctx (hK ctx)) hsmall

/-- **The full genuine area seed from `hsmall` alone** — the Kraft input is now the CLOSED
`chernoffClass0KraftSum_le_one`. -/
def chernoffGenuineAreaSeed_of_smallExcess
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (hsmall : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
        windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
          ≤ chernoffClass0MinWeight ctx) :
    ChernoffGenuineAreaSeedForBudget budget :=
  chernoffGenuineAreaSeed_of_kraft_smallExcess budget
    (fun ctx => chernoffClass0KraftSum_le_one ctx) hsmall

/-- **The full genuine area seed from class-0 routing emptiness** (`hdom` is vacuous, `hK`,
`hne`, `hcard` are the closed theorems). -/
def chernoffGenuineAreaSeed_of_class0FibreEmpty
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (hempty : ∀ ctx : ActualFailureContext,
      routedFibre ctx.n24CarryData (budget ctx).route 0 = ∅) :
    ChernoffGenuineAreaSeedForBudget budget :=
  chernoffGenuineAreaSeed_of_smallExcess budget
    (fun ctx k hk => by
      rw [hempty ctx] at hk
      exact absurd hk (Finset.notMem_empty k))

/-- **The seed itself forces class-0 routing emptiness.**  Any
`ChernoffGenuineAreaSeedForBudget` empties the routed class-0 fibre at every context: its
`hdom` charges each routed start's window excess (`≥ Y ≥ 7/16`) to a genuine branch weight
(`≤ 1/4`).  So `hdom` over the genuine family is NOT satisfiable on a nonempty fibre — the
sharpest impossibility form of the 22.1A area-vs-measure mismatch. -/
theorem class0FibreEmpty_of_genuineAreaSeed
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (S : ChernoffGenuineAreaSeedForBudget budget) :
    ∀ ctx : ActualFailureContext,
      routedFibre ctx.n24CarryData (budget ctx).route 0 = ∅ := by
  intro ctx
  by_contra hne
  obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  have hdom := S.hdom ctx k hk
  have hmem := finRankMatch_mem (S.hne ctx) (S.hcard ctx) hk
  have hw := chernoffClass0_weight_le_quarter ctx (S.hK ctx) (mem_highCostSet.1 hmem).1
  have hY := chernArea_Y_le_windowExcess_of_mem_class0Fibre budget ctx hk
  have hYge := chernArea_Y_ge ctx
  linarith

/-- **The genuine §22 area seed EXISTS iff the budget routes no start to class 0.**  The
class-0 Chernoff line of the V3 ledger collapses, at the genuine carry data, to this single
routing statement — the corrected calibrated surface. -/
theorem genuineAreaSeed_iff_class0FibreEmpty
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx) :
    Nonempty (ChernoffGenuineAreaSeedForBudget budget)
      ↔ ∀ ctx : ActualFailureContext,
          routedFibre ctx.n24CarryData (budget ctx).route 0 = ∅ :=
  ⟨fun h => class0FibreEmpty_of_genuineAreaSeed budget h.some,
   fun h => ⟨chernoffGenuineAreaSeed_of_class0FibreEmpty budget h⟩⟩

/-- **The two-field residual of the class-0 Chernoff line.**  After this module, the genuine
§22 area-family seed is reduced to exactly:

* `kraft` — the §22 antichain disjoint-fibre datum (proof_v4 line 818, `Ω_π ⊆ Ω_u` pairwise
  disjoint) realizing each stopped branch's dyadic mass as a normalized fibre count;
* `small` — the uniform 22.1A area-vs-measure calibration: every routed class-0 window excess is at
  most the family's minimal dyadic weight `2^{-maxCost}`. -/
structure ChernoffGenuineAreaKraftSmallResidual
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx) where
  /-- The §22 antichain disjoint-fibre realization on the actual stopped branches. -/
  kraft : ∀ ctx : ActualFailureContext,
    KraftAntichainFibres ctx.n24CarryData.stoppedBranches
      (fun b => (1 / 2 : ℝ) ^ branchShellCost b)
  /-- The uniform 22.1A small-excess calibration on the routed class-0 fibre. -/
  small : ∀ ctx : ActualFailureContext,
    ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        ≤ chernoffClass0MinWeight ctx

namespace ChernoffGenuineAreaKraftSmallResidual

variable {budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}

/-- The two-field residual builds the full genuine area seed. -/
def toSeed (R : ChernoffGenuineAreaKraftSmallResidual budget) :
    ChernoffGenuineAreaSeedForBudget budget :=
  chernoffGenuineAreaSeed_of_kraft_smallExcess budget
    (chernoffClass0KraftSum_le_one_of_fibres R.kraft) R.small

/-- The exact ctx-pinned V3 class-0 Chernoff ledger field from the two-field residual. -/
theorem hChernoffField (R : ChernoffGenuineAreaKraftSmallResidual budget) :
    ∀ ctx : ActualFailureContext,
      routedClassMassOf ctx.n24CarryData (budget ctx).route 0
        ≤ termChernoff (faithfulCapacityPhases budget ctx).toClosurePhaseData :=
  R.toSeed.hChernoffField

/-- The routed class-0 mass is `≤ 1` (via the genuine Kraft area sum). -/
theorem routedMass_le_one (R : ChernoffGenuineAreaKraftSmallResidual budget)
    (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (budget ctx).route 0 ≤ 1 :=
  R.toSeed.hAreaBound_le_one ctx

/-- **The two-field residual from `small` alone** — the `kraft` field is the CLOSED
`chernoffClass0KraftFibres`. -/
noncomputable def ofSmall
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (small : ∀ ctx : ActualFailureContext,
      ∀ k ∈ routedFibre ctx.n24CarryData (budget ctx).route 0,
        windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
          ≤ chernoffClass0MinWeight ctx) :
    ChernoffGenuineAreaKraftSmallResidual budget where
  kraft := fun ctx => chernoffClass0KraftFibres ctx
  small := small

/-- **The two-field residual from class-0 routing emptiness** — `small` is vacuous on the
empty fibre, `kraft` is closed. -/
noncomputable def ofClass0FibreEmpty
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (hempty : ∀ ctx : ActualFailureContext,
      routedFibre ctx.n24CarryData (budget ctx).route 0 = ∅) :
    ChernoffGenuineAreaKraftSmallResidual budget :=
  ofSmall budget
    (fun ctx k hk => by
      rw [hempty ctx] at hk
      exact absurd hk (Finset.notMem_empty k))

/-- Conversely, every two-field residual forces class-0 routing emptiness (through its `small`
field). -/
theorem class0FibreEmpty (R : ChernoffGenuineAreaKraftSmallResidual budget) :
    ∀ ctx : ActualFailureContext,
      routedFibre ctx.n24CarryData (budget ctx).route 0 = ∅ :=
  class0FibreEmpty_of_smallExcess budget R.small

end ChernoffGenuineAreaKraftSmallResidual

/-- **The two-field residual EXISTS iff the budget routes no start to class 0** — the honest
inhabitation boundary of `ChernoffGenuineAreaKraftSmallResidual` at the genuine carry data. -/
theorem chernoffKraftSmallResidual_iff_class0FibreEmpty
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx) :
    Nonempty (ChernoffGenuineAreaKraftSmallResidual budget)
      ↔ ∀ ctx : ActualFailureContext,
          routedFibre ctx.n24CarryData (budget ctx).route 0 = ∅ :=
  ⟨fun h => h.some.class0FibreEmpty,
   fun h => ⟨ChernoffGenuineAreaKraftSmallResidual.ofClass0FibreEmpty budget h⟩⟩

/-! ## 6.  P9 endpoint with class 0 reduced to the two-field residual -/

/-- P9/V3 run residual with the class-0 Chernoff seed opened to the two-field
`(kraft, small)` residual.  All other fields are exactly those of
`P9V3RunGenuineChernoffAreaResidual`. -/
structure P9V3RunChernoffKraftSmallResidual where
  towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx
  runResidual : ∀ ctx : ActualFailureContext, RunClass5LeafResidual ctx
  returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx
  chernoff : ChernoffGenuineAreaKraftSmallResidual
    (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge)
  cnl : Class1CNLInjection
    (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge)
  densePackCount : ∀ ctx : ActualFailureContext,
    (genuineDensePackStarts ctx).card
      ≤ (densePackMarkers
        (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge) ctx).card
  windowReach : ActualFailureContext → ℕ
  hReach : ∀ ctx : ActualFailureContext,
    windowReach ctx + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card
  hContain : ∀ ctx : ActualFailureContext, ∀ k ∈ genuineDensePackStarts ctx,
    k + ctx.n24CarryData.r
      < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + windowReach ctx
  hScale : ∀ ctx : ActualFailureContext,
    ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ) - ctx.n24CarryData.T ≤ 1

namespace P9V3RunChernoffKraftSmallResidual

/-- Convert to the genuine-area P9/V3 run residual by building the seed. -/
def toGenuine (R : P9V3RunChernoffKraftSmallResidual) :
    P9V3RunGenuineChernoffAreaResidual where
  towerCount := R.towerCount
  runResidual := R.runResidual
  returnCharge := R.returnCharge
  chernoff := R.chernoff.toSeed
  cnl := R.cnl
  densePackCount := R.densePackCount
  windowReach := R.windowReach
  hReach := R.hReach
  hContain := R.hContain
  hScale := R.hScale

/-- The P9 endpoint from the two-field class-0 residual. -/
theorem toStatement (R : P9V3RunChernoffKraftSmallResidual) : Erdos260Statement :=
  R.toGenuine.toStatement

end P9V3RunChernoffKraftSmallResidual

/-- P9/V3 endpoint with the class-0 Chernoff line reduced to the §22 antichain disjoint-fibre
datum and the uniform 22.1A small-excess calibration. -/
theorem erdos260_p9V3_of_chernoffKraftSmall
    (R : P9V3RunChernoffKraftSmallResidual) : Erdos260Statement :=
  R.toStatement

/-! ## 6b.  P9 endpoint with class 0 reduced to the SINGLE routing-emptiness statement

With `kraft` closed and `small ⟺ emptiness`, the honest class-0 entry of the P9/V3 run residual
is the one routing fact `routedFibre … 0 = ∅`.  This is the sharpest, and the only possible,
class-0 Chernoff input over the genuine carry family. -/

/-- P9/V3 run residual with the class-0 Chernoff line opened to its exact boundary: the single
statement that the genuine V3 budget routes no start to class 0.  All other fields are exactly
those of `P9V3RunChernoffKraftSmallResidual`. -/
structure P9V3RunChernoffClass0EmptyResidual where
  towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx
  runResidual : ∀ ctx : ActualFailureContext, RunClass5LeafResidual ctx
  returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx
  class0Empty : ∀ ctx : ActualFailureContext,
    routedFibre ctx.n24CarryData
      ((v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge) ctx).route 0
      = ∅
  cnl : Class1CNLInjection
    (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge)
  densePackCount : ∀ ctx : ActualFailureContext,
    (genuineDensePackStarts ctx).card
      ≤ (densePackMarkers
        (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge) ctx).card
  windowReach : ActualFailureContext → ℕ
  hReach : ∀ ctx : ActualFailureContext,
    windowReach ctx + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card
  hContain : ∀ ctx : ActualFailureContext, ∀ k ∈ genuineDensePackStarts ctx,
    k + ctx.n24CarryData.r
      < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + windowReach ctx
  hScale : ∀ ctx : ActualFailureContext,
    ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ) - ctx.n24CarryData.T ≤ 1

namespace P9V3RunChernoffClass0EmptyResidual

/-- Convert to the two-field `(kraft, small)` residual: `kraft` is the closed packing datum and
`small` holds vacuously on the empty class-0 fibre. -/
noncomputable def toKraftSmall (R : P9V3RunChernoffClass0EmptyResidual) :
    P9V3RunChernoffKraftSmallResidual where
  towerCount := R.towerCount
  runResidual := R.runResidual
  returnCharge := R.returnCharge
  chernoff := ChernoffGenuineAreaKraftSmallResidual.ofClass0FibreEmpty _ R.class0Empty
  cnl := R.cnl
  densePackCount := R.densePackCount
  windowReach := R.windowReach
  hReach := R.hReach
  hContain := R.hContain
  hScale := R.hScale

/-- The P9 endpoint from the single class-0 routing-emptiness input. -/
theorem toStatement (R : P9V3RunChernoffClass0EmptyResidual) : Erdos260Statement :=
  R.toKraftSmall.toStatement

end P9V3RunChernoffClass0EmptyResidual

/-- P9/V3 endpoint with the class-0 Chernoff line reduced to the SINGLE routing statement
`routedFibre … 0 = ∅` — its exact boundary at the genuine carry data (`kraft` and `hK` are
closed; `small` and the whole seed are equivalent to this statement). -/
theorem erdos260_p9V3_of_chernoffClass0Empty
    (R : P9V3RunChernoffClass0EmptyResidual) : Erdos260Statement :=
  R.toStatement

/-! ## 7.  Machine-readable status -/

/-- The precise status of the genuine §22 area-family Chernoff seed after this module. -/
def chernoffAreaUnconditionalStatus : List String :=
  [ "CLOSED UNCONDITIONALLY (hne) — chernoffGenuine_hne: the genuine high-cost stopped-branch " ++
      "family is nonempty at every ActualFailureContext. Proof: carryData_pressureFloor gives " ++
      "cPr·X ≤ highExcessMass (highExcessStarts …) with the pinned cPr = 1/2 > 0 and X ≥ 1, so " ++
      "highExcessStarts ≠ ∅ (chernoffClass0_highExcessStarts_nonempty); stoppedBranches is its " ++
      "image (chernoffClass0_stoppedBranches_nonempty); Y = 0 makes the high-cost set the whole " ++
      "family (genuineCarryChern_highCostSet_eq). NO hypothesis.",
    "CLOSED UNCONDITIONALLY (hcard, for EVERY budget) — chernoffGenuine_hcard: " ++
      "|routedFibre … 0| ≤ |highCostSet (genuineCarryChern ctx)|. Proof: routedFibre is a filter " ++
      "of highExcessStarts, and stoppedBranchOf a r is injective (stoppedBranchOf_injective, " ++
      "hit-sequence strict monotonicity), so |stoppedBranches| = |highExcessStarts| " ++
      "(chernoffClass0_stoppedBranches_card_eq) ≥ |routedFibre … 0|. The genuine SHELL-SCALING " ++
      "I.4.2 count; NO hypothesis, NO ≤ 4 collapse.",
    "CLOSED UNCONDITIONALLY (hK, the §22 antichain/Kraft measure-sum) — " ++
      "chernoffClass0KraftSum_le_one: ∑_{b∈stoppedBranches} (1/2)^branchShellCost b ≤ 1 at every " ++
      "ActualFailureContext, with NO hypothesis. Proof: the canonical N.24 pins (restated " ++
      "module-locally, rfl-level: chernArea_T_eq T = 2L+1, chernArea_Y_eq Y = εL = L/64, " ++
      "chernArea_starts_eq starts = Ico(firstIndexAbove X, +|supportShell d X|), chernArea_X_eq " ++
      "X = 2^L, with L = shellLadderDepth ≥ 28) give the COST FLOOR branchShellCost ≥ 2L+2 on " ++
      "every stopped branch (chernoffClass0_branchCost_ge: windowExcess ≥ Y > 0 forces gapWindow " ++
      "≥ T+Y > 2L+1) and the COUNT BOUND |stoppedBranches| < 2^L (chernoffClass0_" ++
      "stoppedBranches_card_lt: one branch per high-excess start, |starts| = |supportShell d X| " ++
      "< c0·X < X by the failure hypothesis, supportShell_card_lt_X), so the Kraft sum is ≤ " ++
      "2^L·2^{-(2L+2)} = 2^{-(L+2)} ≤ 1 (ℕ packing form chernoffClass0_powSum_le). The old " ++
      "caveat stands for a BARE CarryDataFromFailure (overlapping windows can overflow 1); the " ++
      "canonical pins close it for the actual carry datum.",
    "CLOSED UNCONDITIONALLY (kraft, the §22 disjoint-fibre datum) — chernoffClass0KraftFibres : " ++
      "KraftAntichainFibres ctx.n24CarryData.stoppedBranches (fun b => (1/2)^branchShellCost b) " ++
      "is CONSTRUCTED outright by converse-Kraft interval packing " ++
      "(exists_disjoint_packed_fibres + kraftAntichainFibresOfPowSumLe): at root resolution N = " ++
      "maxCost, each branch receives a genuine dyadic block of exactly 2^{N−cost b} integers, " ++
      "pairwise disjoint inside [0, 2^N), with mass_eq via half_pow_eq_pow_sub_div — a genuine, " ++
      "non-degenerate realization of each mass as a normalized disjoint fibre count. Honest " ++
      "note: the fibres are formal packing intervals, not the manuscript's integer-carry fibres " ++
      "Ω_π themselves (the formalized StoppedBranch records hit/gap words, no carry digits, so " ++
      "line-818 prefix-incompatibility is not expressible from CarryDataFromFailure); the datum " ++
      "exists exactly because the proved cost floor + count bound make the packing fit, and it " ++
      "discharges hK through the proved KraftAntichainFibres.sum_le_one.",
    "PINNED / IMPOSSIBILITY (small ⟺ class-0 routing emptiness) — " ++
      "smallExcess_iff_class0FibreEmpty: the uniform 22.1A small-excess calibration " ++
      "windowExcess(k) ≤ chernoffClass0MinWeight ctx on the routed class-0 fibre holds IFF " ++
      "∀ ctx, routedFibre … 0 = ∅. Scale separation: minWeight = 2^{-maxCost} ≤ 2^{-(2L+2)} ≤ " ++
      "1/4 (chernoffClass0MinWeight_le_quarter) < 7/16 ≤ Y = L/64 ≤ windowExcess on any routed " ++
      "class-0 start (chernArea_Y_ge, chernoffClass0MinWeight_lt_Y). So the intended " ++
      "nonempty-fibre calibration FAILS for genuine carry data; both entry forms force emptiness " ++
      "too (class0FibreEmpty_of_costPaid, class0FibreEmpty_of_windowGapFloor). Class-1 analogue: " ++
      "windowExcess_eq_Y_of_mem_class1Fibre pins an exact level set; class 0 needs only the " ++
      "floor Y ≤ windowExcess.",
    "PINNED / IMPOSSIBILITY (the seed itself ⟺ class-0 routing emptiness) — " ++
      "genuineAreaSeed_iff_class0FibreEmpty: ANY ChernoffGenuineAreaSeedForBudget budget forces " ++
      "∀ ctx, routedFibre … 0 = ∅ (class0FibreEmpty_of_genuineAreaSeed: its hdom charges a " ++
      "routed excess ≥ Y ≥ 7/16 to a genuine branch weight ≤ 1/4, " ++
      "chernoffClass0_weight_le_quarter); conversely emptiness rebuilds the full seed from the " ++
      "closed hK with hdom vacuous (chernoffGenuineAreaSeed_of_class0FibreEmpty). The matched " ++
      "J.1.7 domination over the genuine §22 family is NOT satisfiable on a nonempty routed " ++
      "class-0 fibre — the corrected calibrated surface is the routing statement itself.",
    "ASSEMBLY — chernoffGenuineAreaSeed_of_kraft_smallExcess builds the full " ++
      "ChernoffGenuineAreaSeedForBudget from (hK, hsmall); chernoffGenuineAreaSeed_of_smallExcess " ++
      "needs hsmall alone (hK closed); ChernoffGenuineAreaKraftSmallResidual packages (kraft, " ++
      "small) — now constructible from small alone (ofSmall) or from emptiness " ++
      "(ofClass0FibreEmpty), and conversely forcing emptiness (class0FibreEmpty, " ++
      "chernoffKraftSmallResidual_iff_class0FibreEmpty) — and yields toSeed, hChernoffField, " ++
      "routedMass_le_one, and the P9 endpoint erdos260_p9V3_of_chernoffKraftSmall (through " ++
      "P9V3RunChernoffKraftSmallResidual).",
    "SHARP RESIDUAL BOUNDARY (UPDATED) — the class-0 Chernoff line is now exactly ONE statement: " ++
      "class0Empty : ∀ ctx, routedFibre ctx.n24CarryData ((v3Budget …) ctx).route 0 = ∅ — the " ++
      "genuine V3 budget routes no start to class 0. P9V3RunChernoffClass0EmptyResidual carries " ++
      "it in place of the old (kraft, small) pair and yields the P9 endpoint " ++
      "erdos260_p9V3_of_chernoffClass0Empty via toKraftSmall. kraft/hK are closed theorems; " ++
      "small, hdom, the seed, and the two-field residual are all EQUIVALENT to class0Empty, so " ++
      "no smaller class-0 input exists over the genuine carry family." ]

theorem chernoffAreaUnconditionalStatus_nonempty :
    chernoffAreaUnconditionalStatus ≠ [] := by
  simp [chernoffAreaUnconditionalStatus]

/-! ## 8.  Axiom-cleanliness audit -/

#print axioms chernoffClass0_highExcessStarts_nonempty
#print axioms chernoffClass0_stoppedBranches_nonempty
#print axioms genuineCarryChern_highCostSet_eq
#print axioms chernoffGenuine_hne
#print axioms chernoffClass0_stoppedBranches_card_eq
#print axioms chernoffGenuine_hcard
#print axioms chernoffClass0KraftSum_le_one_of_fibres
#print axioms chernArea_Y_eq
#print axioms chernArea_Y_eq_div
#print axioms chernArea_Y_ge
#print axioms chernArea_Y_pos
#print axioms chernArea_T_eq
#print axioms chernArea_starts_eq
#print axioms chernArea_X_eq
#print axioms chernArea_starts_card_eq
#print axioms supportShell_card_lt_X
#print axioms chernoffClass0_gapWindow_ge
#print axioms chernoffClass0_branchCost_ge
#print axioms chernoffClass0_stoppedBranches_card_lt
#print axioms chernoffClass0_powSum_le
#print axioms exists_disjoint_packed_fibres
#print axioms kraftAntichainFibresOfPowSumLe
#print axioms chernoffClass0KraftFibres
#print axioms chernoffClass0KraftSum_le_one
#print axioms chernoffClass0MinWeight_pos
#print axioms chernoffClass0MinWeight_le_weight
#print axioms chernoffGenuine_hdom_of_smallExcess
#print axioms chernoffClass0_smallExcess_of_costPaid
#print axioms chernoffClass0_smallExcess_of_windowGapFloor
#print axioms chernoffClass0MinWeight_le_quarter
#print axioms chernoffClass0MinWeight_lt_Y
#print axioms chernoffClass0_weight_le_quarter
#print axioms chernArea_Y_le_windowExcess_of_mem_class0Fibre
#print axioms class0FibreEmpty_of_smallExcess
#print axioms smallExcess_iff_class0FibreEmpty
#print axioms class0FibreEmpty_of_costPaid
#print axioms class0FibreEmpty_of_windowGapFloor
#print axioms chernoffGenuineAreaSeed_of_kraft_smallExcess
#print axioms chernoffGenuineAreaSeed_of_smallExcess
#print axioms chernoffGenuineAreaSeed_of_class0FibreEmpty
#print axioms class0FibreEmpty_of_genuineAreaSeed
#print axioms genuineAreaSeed_iff_class0FibreEmpty
#print axioms ChernoffGenuineAreaKraftSmallResidual.toSeed
#print axioms ChernoffGenuineAreaKraftSmallResidual.hChernoffField
#print axioms ChernoffGenuineAreaKraftSmallResidual.routedMass_le_one
#print axioms ChernoffGenuineAreaKraftSmallResidual.ofSmall
#print axioms ChernoffGenuineAreaKraftSmallResidual.ofClass0FibreEmpty
#print axioms ChernoffGenuineAreaKraftSmallResidual.class0FibreEmpty
#print axioms chernoffKraftSmallResidual_iff_class0FibreEmpty
#print axioms P9V3RunChernoffKraftSmallResidual.toGenuine
#print axioms P9V3RunChernoffKraftSmallResidual.toStatement
#print axioms erdos260_p9V3_of_chernoffKraftSmall
#print axioms P9V3RunChernoffClass0EmptyResidual.toKraftSmall
#print axioms P9V3RunChernoffClass0EmptyResidual.toStatement
#print axioms erdos260_p9V3_of_chernoffClass0Empty

end

end Erdos260
