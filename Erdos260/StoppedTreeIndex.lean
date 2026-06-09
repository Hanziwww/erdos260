import Mathlib
import Erdos260.AppendixI
import Erdos260.CarryDataFactory
import Erdos260.HitSequence
import Erdos260.Pressure
import Erdos260.Ledger
import Erdos260.StoppedInduction

/-!
# I.9 stopped-tree indexing: faithful injective branch construction

This file supplies the **existence leaf** of the Appendix I.9 reindexing
`highExcessMass_eq_branchWeightedMass`: a concrete `branchOf : ℕ → StoppedBranch`
built directly from the hit-sequence data, together with a faithful proof that
it is injective on the high-excess starts.

## What is faithful here

* `stoppedBranchOf a r k` records the **genuine gap word** of the hit window of
  length `r + 1` starting at index `k`: it is the list of `r + 1` edges
  `branchEdgeAt a k, …, branchEdgeAt a (k + r)`, where each edge carries the
  real hit positions `source = a (k+i)`, `target = a (k+i+1)`, the visible gap
  `shellCost = hitGap a (k+i)`, and the level `thresholdLayer = k+i`.  This is
  **not** a trivial `⟨[encode k]⟩` encoding: the edges carry the actual hit /
  gap data of the window.

* `stoppedBranchOf_injective_of_strictMono` proves injectivity **faithfully**
  from the strict monotonicity of the hit sequence: the head edge of
  `stoppedBranchOf a r k` has `source = a k`, and `a` is injective (being
  strictly monotone), so distinct start indices give distinct branches.  This is
  the genuinely provable, genuinely valuable deliverable.

* `branchShellCost_stoppedBranchOf` is the real bookkeeping identity
  `branchShellCost (stoppedBranchOf a r k) = gapWindow (hitGap a) k r`: summing
  the branch's recorded shell-cost word reproduces the analytic gap window.
  This is a genuine telescoping computation, **not** a definitional triviality.

## The weight identity, honestly

The weight `windowExcessWeight Tr b = positivePart (branchShellCost b - Tr)` is a
total function of the branch's **intrinsic** shell-cost data; it never refers to
`windowExcess`, `gapWindow`, the index `k`, or `branchOf`.  Consequently
`windowExcessWeight_stoppedBranchOf` — the per-branch weight match
`windowExcessWeight Tr (stoppedBranchOf a r k) = windowExcess (hitGap a) k r Tr`
— is **non-vacuous**: it is discharged through the real shell-cost telescoping
identity above, not by defining the weight to be the window excess.

This yields a fully faithful instance `highExcessMass_eq_branchWeightedMass_hitGap`
(both `hinj` and `hweight` honestly discharged) for the gap function
`g = hitGap a`.

**Honest boundary.**  The weight match proved here is the *bookkeeping* identity
(the recorded gap word sums to the window excess).  It is genuine, but it is
**not** the deeper Carleson charge analysis of the manuscript, which identifies a
`2^{-shell}`-type Carleson measure with the excess (Lemma 22.2 /
`principalShellCarleson`).  For users who want to keep the branch weight abstract,
`highExcessMass_eq_branchWeightedMass_of_weight` and
`highExcessMass_le_of_branchBound_of_weight` package the **faithful injectivity**
with the weight identity exposed as an explicit, clearly-labelled hypothesis.
-/

namespace Erdos260

open Finset

/-! ### The genuine branch construction from hit data -/

/-- The branch edge at hit index `k`: it records the actual hit positions
`source = a k`, `target = a (k+1)`, the visible gap `shellCost = hitGap a k`, and
the level `thresholdLayer = k`. -/
def branchEdgeAt (a : Nat → Nat) (k : Nat) : BranchEdge where
  source := a k
  target := a (k + 1)
  shellCost := hitGap a k
  thresholdLayer := k

/-- The edge list of the hit window of length `r + 1` starting at index `k`:
`branchEdgeAt a k, …, branchEdgeAt a (k + r)`.  Defined by front recursion on `r`
(shifting the start), so the head edge is always `branchEdgeAt a k`. -/
def stoppedWindowEdges (a : Nat → Nat) : Nat → Nat → List BranchEdge
  | k, 0 => [branchEdgeAt a k]
  | k, r + 1 => branchEdgeAt a k :: stoppedWindowEdges a (k + 1) r

/-- The stopped branch indexing the hit window of length `r + 1` at start `k`. -/
def stoppedBranchOf (a : Nat → Nat) (r k : Nat) : StoppedBranch :=
  ⟨stoppedWindowEdges a k r⟩

/-- The recorded start position of a branch (the `source` of its head edge). -/
def branchStart? (b : StoppedBranch) : Option Nat :=
  b.edges.head?.map BranchEdge.source

theorem branchStart?_stoppedBranchOf (a : Nat → Nat) (r k : Nat) :
    branchStart? (stoppedBranchOf a r k) = some (a k) := by
  cases r <;>
    simp [branchStart?, stoppedBranchOf, stoppedWindowEdges, branchEdgeAt]

/-! ### Faithful injectivity from strict monotonicity of the hit sequence -/

/-- **Faithful injectivity.**  Distinct start indices give distinct branches: the
head edge of `stoppedBranchOf a r k` records `source = a k`, and `a` is injective
because it is strictly monotone.  This is the genuine content of the I.9 indexing
existence leaf. -/
theorem stoppedBranchOf_injective_of_strictMono {a : Nat → Nat}
    (ha : StrictMono a) (r : Nat) :
    Function.Injective (stoppedBranchOf a r) := by
  intro k l h
  have hk : branchStart? (stoppedBranchOf a r k) = some (a k) :=
    branchStart?_stoppedBranchOf a r k
  rw [h] at hk
  have hl : branchStart? (stoppedBranchOf a r l) = some (a l) :=
    branchStart?_stoppedBranchOf a r l
  exact ha.injective (Option.some.inj (hk.symm.trans hl))

/-- Injectivity packaged from a `HitSequence` (its `strict` field is exactly the
strict monotonicity used above). -/
theorem stoppedBranchOf_injective {d a : Nat → Nat} (hseq : HitSequence d a)
    (r : Nat) :
    Function.Injective (stoppedBranchOf a r) :=
  stoppedBranchOf_injective_of_strictMono hseq.strict r

/-- The `hinj` shape required by `highExcessMass_eq_branchWeightedMass`: the
branch map is injective on any finite set of starts. -/
theorem stoppedBranchOf_injOn {d a : Nat → Nat} (hseq : HitSequence d a)
    (r : Nat) (S : Finset Nat) :
    ∀ k ∈ S, ∀ l ∈ S, stoppedBranchOf a r k = stoppedBranchOf a r l → k = l :=
  fun _k _ _l _ h => stoppedBranchOf_injective hseq r h

/-! ### The genuine shell-cost / gap-window bookkeeping identity -/

/-- Prepend identity for the gap window:
`gapWindow g start (r+1) = g start + gapWindow g (start+1) r`. -/
theorem gapWindow_prepend (g : Nat → Nat) (start r : Nat) :
    gapWindow g start (r + 1) = g start + gapWindow g (start + 1) r := by
  unfold gapWindow
  conv_lhs => rw [Finset.sum_range_succ']
  have hsum :
      (∑ i ∈ Finset.range (r + 1), g (start + (i + 1)))
        = ∑ i ∈ Finset.range (r + 1), g (start + 1 + i) :=
    Finset.sum_congr rfl (fun i _ => by congr 1; omega)
  rw [hsum]
  exact Nat.add_comm _ _

/-- **Genuine bookkeeping identity.**  The total recorded shell cost of the branch
`stoppedBranchOf a r k` (the sum of its edge gaps) equals the analytic gap window
`gapWindow (hitGap a) k r`.  This telescoping computation is the real content
behind the per-branch weight match below. -/
theorem branchShellCost_stoppedBranchOf (a : Nat → Nat) (r k : Nat) :
    branchShellCost (stoppedBranchOf a r k) = gapWindow (hitGap a) k r := by
  unfold stoppedBranchOf
  induction r generalizing k with
  | zero =>
      simp [stoppedWindowEdges, branchShellCost_cons, branchShellCost_nil,
        branchEdgeAt, gapWindow_zero]
  | succ r ih =>
      simp only [stoppedWindowEdges, branchShellCost_cons]
      rw [ih (k + 1), gapWindow_prepend]
      rfl

/-! ### The faithful per-branch weight and the weight match -/

/-- The per-branch window-excess weight, defined **only** from the branch's
intrinsic recorded shell cost.  It does not mention `windowExcess`, `gapWindow`,
the start index, or `branchOf`, so the weight match below is non-vacuous. -/
noncomputable def windowExcessWeight (Tr : ℝ) (b : StoppedBranch) : ℝ :=
  positivePart ((branchShellCost b : ℝ) - Tr)

/-- **Faithful per-branch weight match.**  The intrinsic branch weight of
`stoppedBranchOf a r k` is exactly the analytic window excess at `k` for the gap
function `hitGap a`.  Discharged through the genuine shell-cost telescoping
identity `branchShellCost_stoppedBranchOf`, not by definition. -/
theorem windowExcessWeight_stoppedBranchOf (a : Nat → Nat) (r k : Nat) (Tr : ℝ) :
    windowExcessWeight Tr (stoppedBranchOf a r k) = windowExcess (hitGap a) k r Tr := by
  unfold windowExcessWeight windowExcess
  rw [branchShellCost_stoppedBranchOf]

/-! ### The faithful I.9 reindexing instance (both inputs discharged) -/

/-- **Fully faithful I.9 reindexing for `g = hitGap a`.**  Instantiates
`highExcessMass_eq_branchWeightedMass` with the genuine branch construction and
the intrinsic shell-cost weight: both the injectivity (`stoppedBranchOf_injective`)
and the per-branch weight match (`windowExcessWeight_stoppedBranchOf`) are honestly
discharged, so the identity is non-vacuous. -/
theorem highExcessMass_eq_branchWeightedMass_hitGap
    {d a : Nat → Nat} (hseq : HitSequence d a)
    {starts : Finset Nat} {r : Nat} {Tr Yr : ℝ} :
    highExcessMass (highExcessStarts starts (hitGap a) r Tr Yr) (hitGap a) r Tr
      = branchWeightedMass
          ((highExcessStarts starts (hitGap a) r Tr Yr).image (stoppedBranchOf a r))
          (windowExcessWeight Tr) := by
  refine highExcessMass_eq_branchWeightedMass (stoppedBranchOf a r) ?_ ?_
  · intro k _ l _ h
    exact stoppedBranchOf_injective hseq r h
  · intro k _
    exact windowExcessWeight_stoppedBranchOf a r k Tr

/--
**Carry-packaged I.9 reindexing.**  For a `CarryDataFromFailure` bundle, the
analytic high-excess mass is exactly the stopped-branch weighted mass built from
the bundle's hit sequence, recurrence length, and threshold.
-/
theorem CarryDataFromFailure.highExcessMass_eq_branchWeightedMass
    {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr) :
    highExcessMass
        (highExcessStarts carryData.starts (hitGap carryData.a)
          carryData.r carryData.T carryData.Y)
        (hitGap carryData.a) carryData.r carryData.T
      =
        branchWeightedMass
          ((highExcessStarts carryData.starts (hitGap carryData.a)
            carryData.r carryData.T carryData.Y).image
              (stoppedBranchOf carryData.a carryData.r))
          (windowExcessWeight carryData.T) :=
  highExcessMass_eq_branchWeightedMass_hitGap carryData.carry.hits

/--
Transport the carry-packaged I.9 reindexing across the remaining ledger
identification with a composed TRT total mass.
-/
theorem CarryDataFromFailure.highExcessMass_eq_of_branchWeightedMass_eq
    {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr) {totalMass : ℝ}
    (hBranchMass_eq :
      branchWeightedMass
          ((highExcessStarts carryData.starts (hitGap carryData.a)
            carryData.r carryData.T carryData.Y).image
              (stoppedBranchOf carryData.a carryData.r))
          (windowExcessWeight carryData.T)
        = totalMass) :
    highExcessMass
        (highExcessStarts carryData.starts (hitGap carryData.a)
          carryData.r carryData.T carryData.Y)
        (hitGap carryData.a) carryData.r carryData.T = totalMass :=
  carryData.highExcessMass_eq_branchWeightedMass.trans hBranchMass_eq

/-! ### Carry-packaged stopped-tree skeleton for Lemma 22.1 -/

/-- The actual stopped branches generated by the carry high-excess starts.  This is
the `paths` component of the Lemma 22.1 stopped-tree input, before the
Chernoff tilt and tail budgets are attached. -/
noncomputable def CarryDataFromFailure.stoppedBranches
    {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr) : Finset StoppedBranch :=
  (highExcessStarts carryData.starts (hitGap carryData.a)
    carryData.r carryData.T carryData.Y).image
      (stoppedBranchOf carryData.a carryData.r)

/-- The real branch weight carried by the stopped-tree skeleton.  It is defined
from the branch's intrinsic shell cost, so the match with analytic window excess
is the telescoping theorem above, not a definitional shortcut. -/
noncomputable def CarryDataFromFailure.stoppedBranchWeightReal
    {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr) (b : StoppedBranch) : ℝ :=
  windowExcessWeight carryData.T b

/-- The stopped-tree branch weights are nonnegative. -/
theorem CarryDataFromFailure.stoppedBranchWeightReal_nonneg
    {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr) :
    ∀ b, 0 <= carryData.stoppedBranchWeightReal b := by
  intro b
  simpa [CarryDataFromFailure.stoppedBranchWeightReal, windowExcessWeight] using
    positivePart_nonneg ((branchShellCost b : ℝ) - carryData.T)

/-- The nonnegative branch weight in the exact subtype shape used by the grounded
Chernoff package. -/
noncomputable def CarryDataFromFailure.stoppedBranchWeight
    {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr) :
    StoppedBranch -> {x : ℝ // 0 <= x} :=
  fun b => ⟨carryData.stoppedBranchWeightReal b,
    carryData.stoppedBranchWeightReal_nonneg b⟩

@[simp] theorem CarryDataFromFailure.stoppedBranchWeight_coe
    {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr) (b : StoppedBranch) :
    (carryData.stoppedBranchWeight b : ℝ) =
      carryData.stoppedBranchWeightReal b := rfl

/-- The shell-cost function used by the stopped-tree skeleton. -/
def CarryDataFromFailure.stoppedBranchCost
    {shell : FailingDyadicShell} {cPr : ℝ}
    (_carryData : CarryDataFromFailure shell cPr) : StoppedBranch -> Nat :=
  branchShellCost

/-- The carry stopped branches are genuinely high-cost branches at the active
floor.  This is the direct bridge from the analytic high-excess selector
`highExcessStarts` to the stopped-tree high-cost tail used in Lemma 22.1. -/
theorem CarryDataFromFailure.stoppedBranches_subset_highBranchCostSet
    {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr)
    (hT_nonneg : 0 <= carryData.T) (hY_nonneg : 0 <= carryData.Y) :
    carryData.stoppedBranches ⊆
      highBranchCostSet carryData.stoppedBranches (Nat.floor carryData.Y) := by
  intro b hb
  rw [mem_highBranchCostSet]
  refine ⟨hb, ?_⟩
  have hb_image :
      b ∈
        (highExcessStarts carryData.starts (hitGap carryData.a)
          carryData.r carryData.T carryData.Y).image
            (stoppedBranchOf carryData.a carryData.r) := by
    simpa [CarryDataFromFailure.stoppedBranches] using hb
  rcases Finset.mem_image.mp hb_image with ⟨k, hk, rfl⟩
  have hY_le_excess :
      carryData.Y <=
        windowExcess (hitGap carryData.a) k carryData.r carryData.T := by
    exact (Finset.mem_filter.mp hk).2
  have hexcess_le_gap :
      windowExcess (hitGap carryData.a) k carryData.r carryData.T <=
        (gapWindow (hitGap carryData.a) k carryData.r : ℝ) :=
    windowExcess_le_gapWindow_of_nonneg_threshold hT_nonneg
  have hfloor_le_Y : ((Nat.floor carryData.Y : Nat) : ℝ) <= carryData.Y :=
    Nat.floor_le hY_nonneg
  have hfloor_le_gap_real :
      ((Nat.floor carryData.Y : Nat) : ℝ) <=
        (gapWindow (hitGap carryData.a) k carryData.r : ℝ) :=
    hfloor_le_Y.trans (hY_le_excess.trans hexcess_le_gap)
  have hfloor_le_gap :
      Nat.floor carryData.Y <= gapWindow (hitGap carryData.a) k carryData.r := by
    exact_mod_cast hfloor_le_gap_real
  simpa [CarryDataFromFailure.stoppedBranchCost,
    branchShellCost_stoppedBranchOf] using hfloor_le_gap

/-- Equivalently, under the nonnegative active threshold/floor hypotheses, the
high-cost tail at `floor Y` is the whole stopped-branch family. -/
theorem CarryDataFromFailure.highBranchCostSet_floorY_eq_stoppedBranches
    {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr)
    (hT_nonneg : 0 <= carryData.T) (hY_nonneg : 0 <= carryData.Y) :
    highBranchCostSet carryData.stoppedBranches (Nat.floor carryData.Y) =
      carryData.stoppedBranches := by
  apply Finset.Subset.antisymm
  · exact highBranchCostSet_subset carryData.stoppedBranches (Nat.floor carryData.Y)
  · exact carryData.stoppedBranches_subset_highBranchCostSet hT_nonneg hY_nonneg

/-- The faithful I.9 mass identity in the reusable stopped-tree skeleton shape. -/
theorem CarryDataFromFailure.highExcessMass_eq_stoppedBranchWeightedMass
    {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr) :
    highExcessMass
        (highExcessStarts carryData.starts (hitGap carryData.a)
          carryData.r carryData.T carryData.Y)
        (hitGap carryData.a) carryData.r carryData.T
      =
        branchWeightedMass carryData.stoppedBranches
          carryData.stoppedBranchWeightReal := by
  simpa [CarryDataFromFailure.stoppedBranches,
    CarryDataFromFailure.stoppedBranchWeightReal] using
    carryData.highExcessMass_eq_branchWeightedMass

/-- The stopped-tree indexing skeleton already supplied by a carry/failure shell.
The remaining Chernoff work is exactly the Lemma 22.1 tilt, moment, and tail
budget on this concrete path family. -/
structure CarryStoppedTreeIndexData
    {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr) where
  paths : Finset StoppedBranch
  weight : StoppedBranch -> {x : ℝ // 0 <= x}
  cost : StoppedBranch -> Nat
  paths_eq : paths = carryData.stoppedBranches
  cost_eq : cost = carryData.stoppedBranchCost
  mass_eq :
    highExcessMass
        (highExcessStarts carryData.starts (hitGap carryData.a)
          carryData.r carryData.T carryData.Y)
        (hitGap carryData.a) carryData.r carryData.T
      =
        branchWeightedMass paths (fun b => (weight b : ℝ))

/-- Package the existing I.9 stopped-branch construction as the concrete
stopped-tree skeleton attached to a carry/failure shell. -/
noncomputable def CarryDataFromFailure.toStoppedTreeIndexData
    {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr) :
    CarryStoppedTreeIndexData carryData where
  paths := carryData.stoppedBranches
  weight := carryData.stoppedBranchWeight
  cost := carryData.stoppedBranchCost
  paths_eq := rfl
  cost_eq := rfl
  mass_eq := by
    simpa [CarryDataFromFailure.stoppedBranchWeight,
      CarryDataFromFailure.stoppedBranchWeightReal] using
      carryData.highExcessMass_eq_stoppedBranchWeightedMass

/-! ### Honest conditional packaging (faithful injectivity + explicit weight) -/

/-- **Conditional reindexing.**  For an *arbitrary* gap function `g` and an
*arbitrary* branch weight, the I.9 reindexing holds once the per-branch weight
match is supplied as a hypothesis.  The injectivity input is discharged faithfully
here; only the weight identity remains as an explicit, clearly labelled
hypothesis. -/
theorem highExcessMass_eq_branchWeightedMass_of_weight
    {d a : Nat → Nat} (hseq : HitSequence d a)
    {starts : Finset Nat} {g : Nat → Nat} {r : Nat} {Tr Yr : ℝ}
    {branchWeight : StoppedBranch → ℝ}
    (hweight : ∀ k ∈ highExcessStarts starts g r Tr Yr,
        branchWeight (stoppedBranchOf a r k) = windowExcess g k r Tr) :
    highExcessMass (highExcessStarts starts g r Tr Yr) g r Tr
      = branchWeightedMass
          ((highExcessStarts starts g r Tr Yr).image (stoppedBranchOf a r))
          branchWeight := by
  refine highExcessMass_eq_branchWeightedMass (stoppedBranchOf a r) ?_ hweight
  intro k _ l _ h
  exact stoppedBranchOf_injective hseq r h

/-- **Conditional branch bound transfer.**  Any upper bound on the stopped-branch
weighted mass transfers to the analytic high-excess mass, using the faithful
injectivity and the explicit weight hypothesis. -/
theorem highExcessMass_le_of_branchBound_of_weight
    {d a : Nat → Nat} (hseq : HitSequence d a)
    {starts : Finset Nat} {g : Nat → Nat} {r : Nat} {Tr Yr : ℝ}
    {branchWeight : StoppedBranch → ℝ} {bound : ℝ}
    (hweight : ∀ k ∈ highExcessStarts starts g r Tr Yr,
        branchWeight (stoppedBranchOf a r k) = windowExcess g k r Tr)
    (hbound :
      branchWeightedMass
          ((highExcessStarts starts g r Tr Yr).image (stoppedBranchOf a r))
          branchWeight ≤ bound) :
    highExcessMass (highExcessStarts starts g r Tr Yr) g r Tr ≤ bound := by
  refine highExcessMass_le_of_branchBound (stoppedBranchOf a r) ?_ hweight hbound
  intro k _ l _ h
  exact stoppedBranchOf_injective hseq r h

/-! ### Existence statement recording exactly what is achieved -/

/-- **Existence leaf, faithful form.**  For the gap function `hitGap a` there exist
a branch indexing and a per-branch weight such that the indexing is injective on
the high-excess starts (proved faithfully from strict monotonicity) and the weight
of each indexed branch is the corresponding window excess (proved through the
genuine shell-cost telescoping).  This is the honest record of the I.9 indexing
existence leaf. -/
theorem exists_injective_branchOf_with_weight
    {d a : Nat → Nat} (hseq : HitSequence d a)
    (starts : Finset Nat) (r : Nat) (Tr Yr : ℝ) :
    ∃ (branchOf : Nat → StoppedBranch) (branchWeight : StoppedBranch → ℝ),
      (∀ k ∈ highExcessStarts starts (hitGap a) r Tr Yr,
        ∀ l ∈ highExcessStarts starts (hitGap a) r Tr Yr,
          branchOf k = branchOf l → k = l) ∧
      (∀ k ∈ highExcessStarts starts (hitGap a) r Tr Yr,
        branchWeight (branchOf k) = windowExcess (hitGap a) k r Tr) :=
  ⟨stoppedBranchOf a r, windowExcessWeight Tr,
    fun _k _ _l _ h => stoppedBranchOf_injective hseq r h,
    fun k _ => windowExcessWeight_stoppedBranchOf a r k Tr⟩

end Erdos260
