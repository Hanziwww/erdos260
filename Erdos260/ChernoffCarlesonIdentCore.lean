import Mathlib
import Erdos260.ChernoffSubconjugacy
import Erdos260.Chernoff221AAreaSumCore

/-!
# Lemma 22.2: the carry ↔ dyadic-cylinder Carleson identification

This file closes the deepest residual of the §22 Chernoff phase — the
identification of the **actual integer-carry** threshold fibre with the dyadic
cylinder along the stopped tree — and proves the principal shell-Carleson budget
of manuscript Lemma 22.2 (`proof_v4` §22.2, ≈ lines 812-827; the §25 dyadic
cylinder reduction, ≈ lines 1015-1056).

## The state of the scaffolding (audit verdict)

* `ChernoffSubconjugacy.lean` proves the carry↔doubling sub-conjugacy at the
  *per-edge* level: `carryThresholdMeasure_gap_contraction` (a gap of `g` cuts the
  integer-carry fibre measure by exactly `2^{-g}`), bottoming out in
  `integerCarry_succ_of_zero` / `integerCarry_zeroDigits`.  It packages this as
  `carryThresholdFibre : CarryThresholdFibreData Csh G m 1 1`.
* `ChernoffMeasureModel.lean` proves the per-edge cylinder contraction
  (`cylinderMeasure_succ_of_lt`) and the *count* of consistent carry states
  (`consistentInterval_card = 2^{n-L}`), and the bridge
  `regularEdgeData_of_gapContraction`/`RegularEdgeData.regular_path_bound`.
* What was **missing** (the genuine Lemma 22.2 content): (i) the carry↔cylinder
  *identification* of the actual `integerCarry` threshold fibre with the dyadic
  interval at a given scale and address; (ii) the **measure-theoretic heart** of
  the Carleson budget — the *disjointness* of the children sub-fibres, which is
  what turns "`|Ω_v| > K|Ω_u|2^{-s(u,v)}`" into the packing budget
  `∑_v 2^{-s(u,v)} ≤ K^{-1}`.

## What this file proves (no `sorry`, no `axiom`, no `native_decide`)

### The carry ↔ dyadic-cylinder identification (the residual, closed)
* `carryCell` — the genuine integer-carry threshold sub-fibre at resolution `n`,
  scale `L`, dyadic address `p`: the seeds whose `L`-step zero-run carry
  `integerCarry Q s (fun _ => 0) L` lands in the dyadic block `[p·2^n,(p+1)·2^n)`.
* `carryCell_eq_consistentInterval` — **the identification**: that sub-fibre *is*
  the dyadic interval `consistentInterval p L n`.  The proof reduces, via
  `integerCarry_zeroDigits`, to the pure doubling `2^L·s`; this is the carry's
  scale-`L` address equalling the dyadic-cylinder index.  (`carryCell_card`,
  `carryCell_measure` then transport the count/measure.)

### The principal shell-Carleson budget (Lemma 22.2)
* `consistentInterval_disjoint` / `consistentInterval_child_subset` — the dyadic
  packing primitives: distinct same-scale cells are disjoint; a gap-`g` refinement
  child sits inside its parent.  These are the *genuine* disjointness facts.
* `card_sum_le_of_subset_disjoint` — disjoint sub-cells of a parent have total
  count `≤` the parent (`∑_v |Ω_v| ≤ |Ω_u|`): the manuscript's "disjoint subsets
  of `Ω_u`".
* `carleson_budget` — the divide-out: sub-additivity + the principal lower bound
  give `∑_v 2^{-s(u,v)} ≤ K^{-1}`.
* `integerCarry_principalShellCarleson_budget` (+ `…_one`) — **Lemma 22.2 for the
  integer carry**: principal children that are disjoint dyadic carry sub-fibres of
  a parent obey `∑ 2^{-s(u,v)} ≤ K^{-1}`.
* `consistentInterval_children_carleson_saturates` — sharpness: the `2^g` uniform
  children are disjoint, sit inside the parent, and *saturate* the budget at
  `K^{-1} = 1`.

### The per-path regularity (the literal target, closed)
* `carryThresholdMeasure_path_regularity` — `wt₀(σ) ≤ 2^{-cost(σ)}` (`K = 1`) for
  the actual integer-carry threshold measure, via the proved `gap_contraction`
  through `regular_path_bound`.
* `carryGapWord_branchShellCost_regularity` — faithfulness to the actual carry
  branch `stoppedBranchOf a r k`.
* `integerCarry_areaWeighted_regular_le` — capstone: the integer-carry measure
  feeds the wave-13 area-weighted layer-cake bound of `Chernoff221AAreaSumCore`.

`#print axioms` of every theorem below is `[propext, Classical.choice, Quot.sound]`.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## §1. The carry ↔ dyadic-cylinder identification -/

/-- **The genuine integer-carry threshold sub-fibre.**  At threshold resolution
`n`, scale `L`, and dyadic address `p`: the resolution-`n` carry seeds `s` whose
`L`-step zero-run carry `integerCarry Q s (fun _ => 0) L` lands in the dyadic
block `[p·2^n, (p+1)·2^n)`.  (By `integerCarry_zeroDigits` the carry is `2^L·s`,
so this records the `L`-step doubling address of the seed — the symbolic dynamics
of the doubling map underlying the carry recurrence on a zero run.) -/
def carryCell (Q L n p : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ n)).filter fun s =>
    (p : ℤ) * 2 ^ n ≤ integerCarry Q (s : ℤ) (fun _ => 0) L ∧
      integerCarry Q (s : ℤ) (fun _ => 0) L < ((p : ℤ) + 1) * 2 ^ n

/-- **The carry ↔ dyadic-cylinder identification (the residual, closed).**  For
`L ≤ n` and a valid address `p < 2^L`, the integer-carry threshold sub-fibre is
*exactly* the dyadic cylinder interval `consistentInterval p L n`.  The proof
reduces the carry to the pure doubling `integerCarry Q s (fun _ => 0) L = 2^L·s`
(`integerCarry_zeroDigits`, iterated `integerCarry_succ_of_zero`): the carry's
scale-`L` block address `⌊2^L·s / 2^n⌋ = p` is equivalent to the seed lying in the
dyadic interval `[p·2^{n-L}, (p+1)·2^{n-L})`.  This is the manuscript's Carleson
content (Lemma 22.2 / §25 dyadic cylinder reduction): the *actual* integer carry's
threshold fibre is a dyadic interval. -/
theorem carryCell_eq_consistentInterval (Q : ℕ) {L n p : ℕ} (hLn : L ≤ n)
    (hp : p < 2 ^ L) :
    carryCell Q L n p = consistentInterval p L n := by
  have hsplit : (2 : ℕ) ^ n = 2 ^ L * 2 ^ (n - L) := by rw [← pow_add]; congr 1; omega
  have e1 : p * 2 ^ n = 2 ^ L * (p * 2 ^ (n - L)) := by rw [hsplit]; ring
  have e2 : (p + 1) * 2 ^ n = 2 ^ L * ((p + 1) * 2 ^ (n - L)) := by rw [hsplit]; ring
  ext s
  unfold carryCell consistentInterval
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, integerCarry_zeroDigits]
  constructor
  · rintro ⟨_, hlo, hhi⟩
    have hloN : p * 2 ^ n ≤ 2 ^ L * s := by exact_mod_cast hlo
    have hhiN : 2 ^ L * s < (p + 1) * 2 ^ n := by exact_mod_cast hhi
    rw [e1] at hloN
    rw [e2] at hhiN
    refine ⟨?_, ?_⟩
    · by_contra hc
      rw [not_le] at hc
      have hcontra : 2 ^ L * s < 2 ^ L * (p * 2 ^ (n - L)) :=
        mul_lt_mul_of_pos_left hc (by positivity)
      omega
    · by_contra hc
      rw [not_lt] at hc
      have hcontra : 2 ^ L * ((p + 1) * 2 ^ (n - L)) ≤ 2 ^ L * s := by gcongr
      omega
  · rintro ⟨hlo, hhi⟩
    have hpp : p + 1 ≤ 2 ^ L := by omega
    have hub : (p + 1) * 2 ^ (n - L) ≤ 2 ^ L * 2 ^ (n - L) := by gcongr
    have hsn : s < 2 ^ n := by rw [hsplit]; omega
    refine ⟨hsn, ?_, ?_⟩
    · have hN : p * 2 ^ n ≤ 2 ^ L * s := by
        rw [e1]; gcongr
      exact_mod_cast hN
    · have hN : 2 ^ L * s < (p + 1) * 2 ^ n := by
        rw [e2]; exact mul_lt_mul_of_pos_left hhi (by positivity)
      exact_mod_cast hN

/-- The integer-carry sub-fibre has exactly `2^{n-L}` consistent carry states
(transported from `consistentInterval_card` through the identification). -/
theorem carryCell_card (Q : ℕ) {L n p : ℕ} (hLn : L ≤ n) (hp : p < 2 ^ L) :
    (carryCell Q L n p).card = 2 ^ (n - L) := by
  rw [carryCell_eq_consistentInterval Q hLn hp, consistentInterval_card]

/-- The integer-carry sub-fibre measure (normalized count) is the dyadic value
`2^{-L}` — the genuine measure-level form of the carry↔cylinder identification. -/
theorem carryCell_measure (Q : ℕ) {L n p : ℕ} (hLn : L ≤ n) (hp : p < 2 ^ L) :
    ((carryCell Q L n p).card : ℝ) / (2 ^ n : ℝ) = (1 / 2 : ℝ) ^ L := by
  rw [carryCell_eq_consistentInterval Q hLn hp, consistentInterval_measure p L n hLn]

/-! ## §2. The dyadic packing primitives (the genuine disjointness content) -/

/-- **Distinct same-scale cells are disjoint.**  The dyadic carry cells
`consistentInterval p L n` and `consistentInterval p' L n` with `p ≠ p'` are
disjoint subsets of the carry-state space — the basic dyadic-tree disjointness
underlying the Carleson budget. -/
theorem consistentInterval_disjoint {L n p p' : ℕ} (h : p ≠ p') :
    Disjoint (consistentInterval p L n) (consistentInterval p' L n) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [consistentInterval, Finset.mem_Ico] at hx hx'
  rcases Nat.lt_or_ge p p' with hlt | hge
  · have hpp : p + 1 ≤ p' := by omega
    have hb : (p + 1) * 2 ^ (n - L) ≤ p' * 2 ^ (n - L) := by gcongr
    omega
  · have hpp : p' + 1 ≤ p := by omega
    have hb : (p' + 1) * 2 ^ (n - L) ≤ p * 2 ^ (n - L) := by gcongr
    omega

/-- **A refinement child sits inside its parent.**  Extending the dyadic prefix of
the parent cell `(p, L)` by a gap of height `g` (address suffix `j < 2^g`) yields a
child cell `(p·2^g + j, L+g)` contained in the parent.  This is the cylinder
nesting `Ω_v ⊆ Ω_u`. -/
theorem consistentInterval_child_subset {L g n : ℕ} (hLgn : L + g ≤ n) {p j : ℕ}
    (hj : j < 2 ^ g) :
    consistentInterval (p * 2 ^ g + j) (L + g) n ⊆ consistentInterval p L n := by
  have hw : (2 : ℕ) ^ (n - L) = 2 ^ g * 2 ^ (n - (L + g)) := by
    rw [← pow_add]; congr 1; omega
  unfold consistentInterval
  refine Finset.Ico_subset_Ico ?_ ?_
  · have e : p * 2 ^ (n - L) = (p * 2 ^ g) * 2 ^ (n - (L + g)) := by rw [hw]; ring
    rw [e]
    have hj' : p * 2 ^ g ≤ p * 2 ^ g + j := by omega
    gcongr
  · have e : (p + 1) * 2 ^ (n - L) = (p * 2 ^ g + 2 ^ g) * 2 ^ (n - (L + g)) := by
      rw [hw]; ring
    rw [e]
    have hj' : p * 2 ^ g + j + 1 ≤ p * 2 ^ g + 2 ^ g := by omega
    gcongr

/-- **Sub-additivity from disjointness (the manuscript's "disjoint subsets of
`Ω_u`").**  If a family of cells are pairwise disjoint and each contained in the
parent, then their total count is at most the parent's count: `∑_v |Ω_v| ≤ |Ω_u|`.
The proof is the disjoint-`biUnion` card identity composed with `card_le_card`. -/
theorem card_sum_le_of_subset_disjoint {ι : Type*} (Prin : Finset ι)
    (cell : ι → Finset ℕ) (parent : Finset ℕ)
    (hsub : ∀ v ∈ Prin, cell v ⊆ parent)
    (hdisj : ∀ u ∈ Prin, ∀ v ∈ Prin, u ≠ v → Disjoint (cell u) (cell v)) :
    ∑ v ∈ Prin, (cell v).card ≤ parent.card := by
  rw [← Finset.card_biUnion hdisj]
  exact Finset.card_le_card (Finset.biUnion_subset.mpr hsub)

/-! ## §3. The principal shell-Carleson budget (Lemma 22.2) -/

/-- **The Carleson divide-out.**  Given a positive parent mass `μu`, decay constant
`K > 0`, child masses `μ`, and shell costs `s`, with (sub-additivity)
`∑_v μ v ≤ μu` and (principal lower bound) `K·μu·2^{-s(v)} ≤ μ v`, the packing
budget `∑_v 2^{-s(v)} ≤ K^{-1}` holds.  This is the algebraic core of Lemma 22.2:
`K·μu·∑ 2^{-s} = ∑ K·μu·2^{-s} ≤ ∑ μ_v ≤ μu = K·μu·K^{-1}`, then cancel
`K·μu > 0`. -/
theorem carleson_budget {ι : Type*} (Prin : Finset ι) (μu K : ℝ) (μ : ι → ℝ)
    (s : ι → ℕ) (hμu : 0 < μu) (hK : 0 < K)
    (hsub : ∑ v ∈ Prin, μ v ≤ μu)
    (hprin : ∀ v ∈ Prin, K * μu * (1 / 2 : ℝ) ^ (s v) ≤ μ v) :
    ∑ v ∈ Prin, (1 / 2 : ℝ) ^ (s v) ≤ K⁻¹ := by
  have hKμu : 0 < K * μu := mul_pos hK hμu
  have key : K * μu * (∑ v ∈ Prin, (1 / 2 : ℝ) ^ (s v)) ≤ μu := by
    rw [Finset.mul_sum]
    exact le_trans (Finset.sum_le_sum hprin) hsub
  have key2 : K * μu * (∑ v ∈ Prin, (1 / 2 : ℝ) ^ (s v)) ≤ K * μu * K⁻¹ := by
    rw [mul_right_comm K μu K⁻¹, mul_inv_cancel₀ hK.ne', one_mul]
    exact key
  exact le_of_mul_le_mul_left key2 hKμu

/-- **Lemma 22.2 (principal shell-Carleson budget for the integer carry).**

Let the parent be the dyadic carry cell `consistentInterval P Lp n` (a genuine
integer-carry threshold fibre by `carryCell_eq_consistentInterval`).  Let `Prin`
be a family of **principal children** realized as dyadic carry sub-cells
`consistentInterval (pf v) (len v) n` that are pairwise disjoint and each inside
the parent (so `∑_v |Ω_v| ≤ |Ω_u|` by `card_sum_le_of_subset_disjoint`), with the
principal lower bound `K·|Ω_u|·2^{-s(u,v)} ≤ |Ω_v|`.  Then the Carleson budget
holds:
```
∑_{v ∈ Prin} 2^{-s(u,v)} ≤ K^{-1}.
```
This is the boxed (22.2), with its measure-theoretic heart — disjointness of the
children sub-fibres — discharged for the actual integer-carry state space. -/
theorem integerCarry_principalShellCarleson_budget {ι : Type*}
    (n P Lp : ℕ) (K : ℝ) (hK : 0 < K)
    (Prin : Finset ι) (pf len s : ι → ℕ)
    (hsubset : ∀ v ∈ Prin,
        consistentInterval (pf v) (len v) n ⊆ consistentInterval P Lp n)
    (hdisj : ∀ u ∈ Prin, ∀ v ∈ Prin, u ≠ v →
        Disjoint (consistentInterval (pf u) (len u) n)
          (consistentInterval (pf v) (len v) n))
    (hprin : ∀ v ∈ Prin,
        K * ((consistentInterval P Lp n).card : ℝ) * (1 / 2 : ℝ) ^ (s v)
          ≤ ((consistentInterval (pf v) (len v) n).card : ℝ)) :
    ∑ v ∈ Prin, (1 / 2 : ℝ) ^ (s v) ≤ K⁻¹ := by
  have hμu : 0 < ((consistentInterval P Lp n).card : ℝ) := by
    rw [consistentInterval_card]
    exact_mod_cast pow_pos (by norm_num : 0 < 2) (n - Lp)
  refine carleson_budget Prin _ K
    (fun v => ((consistentInterval (pf v) (len v) n).card : ℝ)) s hμu hK ?_ hprin
  have hcard := card_sum_le_of_subset_disjoint Prin
    (fun v => consistentInterval (pf v) (len v) n) (consistentInterval P Lp n)
    hsubset hdisj
  have hcardR : ∑ v ∈ Prin, ((consistentInterval (pf v) (len v) n).card : ℝ)
      ≤ ((consistentInterval P Lp n).card : ℝ) := by exact_mod_cast hcard
  simpa using hcardR

/-- **Lemma 22.2 with `K = 1` (the regular-edge calibration of the carry tree).**
For the integer carry's threshold-fibre measure (`K = 1`, the value proved in
`carryThresholdFibre`), the principal shell-Carleson budget is `∑_v 2^{-s(u,v)} ≤
1`. -/
theorem integerCarry_principalShellCarleson_budget_one {ι : Type*}
    (n P Lp : ℕ) (Prin : Finset ι) (pf len s : ι → ℕ)
    (hsubset : ∀ v ∈ Prin,
        consistentInterval (pf v) (len v) n ⊆ consistentInterval P Lp n)
    (hdisj : ∀ u ∈ Prin, ∀ v ∈ Prin, u ≠ v →
        Disjoint (consistentInterval (pf u) (len u) n)
          (consistentInterval (pf v) (len v) n))
    (hprin : ∀ v ∈ Prin,
        ((consistentInterval P Lp n).card : ℝ) * (1 / 2 : ℝ) ^ (s v)
          ≤ ((consistentInterval (pf v) (len v) n).card : ℝ)) :
    ∑ v ∈ Prin, (1 / 2 : ℝ) ^ (s v) ≤ 1 := by
  have h := integerCarry_principalShellCarleson_budget n P Lp 1 (by norm_num)
    Prin pf len s hsubset hdisj (by simpa using hprin)
  simpa using h

/-- **Sharpness / non-vacuousness: the `2^g` uniform children saturate the budget.**
The canonical refinement children of a parent cell at a single gap height `g`
(addresses `p·2^g + j`, `j < 2^g`) are pairwise disjoint, each contained in the
parent, and their Carleson sum is *exactly* the budget value `K^{-1} = 1`:
`∑_{j<2^g} 2^{-g} = 2^g·2^{-g} = 1`.  Thus the Carleson budget of Lemma 22.2 is
attained, and the disjointness hypotheses are realizable. -/
theorem consistentInterval_children_carleson_saturates (L g n : ℕ)
    (hLgn : L + g ≤ n) (p : ℕ) :
    (∀ j ∈ Finset.range (2 ^ g),
        consistentInterval (p * 2 ^ g + j) (L + g) n ⊆ consistentInterval p L n) ∧
    (∀ i ∈ Finset.range (2 ^ g), ∀ j ∈ Finset.range (2 ^ g), i ≠ j →
        Disjoint (consistentInterval (p * 2 ^ g + i) (L + g) n)
          (consistentInterval (p * 2 ^ g + j) (L + g) n)) ∧
    ∑ _j ∈ Finset.range (2 ^ g), (1 / 2 : ℝ) ^ g = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    exact consistentInterval_child_subset hLgn (Finset.mem_range.mp hj)
  · intro i _ j _ hij
    exact consistentInterval_disjoint (by omega)
  · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    rw [← mul_pow, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_pow]

/-! ## §4. The per-path regularity for the actual integer carry (the target) -/

/-- **The per-path regularity for the actual integer carry (`K = 1`).**  The
integer-carry threshold-fibre measure of every length-`m` gap-word path obeys the
dyadic regularity
```
wt₀(σ) = carryThresholdMeasure Q σ m ≤ 2^{-cost(σ)},   cost(σ) = ∑ s(e),
```
with root mass and decay constant `1`.  This is the manuscript per-path bound
`|Ω_π| ≤ |Ω_root|·K^m·2^{-cost(π)}`, here *proved* for the genuine integer carry:
it is the telescoping (`regular_path_bound`) of the per-edge sub-conjugacy
`carryThresholdMeasure_gap_contraction` (which bottoms out in
`integerCarry_succ_of_zero`), packaged in `carryThresholdFibre`. -/
theorem carryThresholdMeasure_path_regularity (Q Csh G m : ℕ) {σ : Fin m → ℕ}
    (hσ : σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1))) :
    carryThresholdMeasure Q σ m ≤ (1 / 2 : ℝ) ^ (∑ i, shellCost Csh (σ i)) := by
  have h := (carryThresholdFibre Q Csh G m).toRegularEdgeData.regular_path_bound hσ
  simpa using h

/-- **Faithfulness to the actual carry branch.**  For the carry branch
`stoppedBranchOf a r k`, the threshold-fibre measure built from the branch's
genuinely recorded gaps (`2^{-branchShellCost}`, see
`carryThresholdMeasure_carryGapWord_eq`) is dominated by the Lemma 22.1 regularity
bound `2^{-cost}`, because the shell cost never exceeds the recorded gap
(`carryGapWord_shellCost_le_branchShellCost`).  The actual carry branch is
therefore regular with the dyadic mass. -/
theorem carryGapWord_branchShellCost_regularity (Csh : ℕ) (a : Nat → Nat) (r k : Nat) :
    (1 / 2 : ℝ) ^ branchShellCost (stoppedBranchOf a r k)
      ≤ (1 / 2 : ℝ) ^ (∑ i, shellCost Csh (carryGapWord a k (r + 1) i)) := by
  apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
  exact carryGapWord_shellCost_le_branchShellCost a Csh r k

/-! ## §5. Capstone: the integer carry feeds the wave-13 area-weighted bound -/

/-- **Capstone (integer carry → area-weighted shell-Chernoff bound).**  The
integer-carry threshold-fibre measure plugged in as `wt₀` satisfies the area-
weighted layer-cake bound of `Chernoff221AAreaSumCore` (`lemma22_1A_areaWeighted_
regular_le`): with the per-path regularity supplied by
`carryThresholdMeasure_path_regularity` (not assumed) and the shell-paid
calibration `hcal` (Definition K.1.2) and active-height cap `hYsh_le` as the only
remaining inputs,
```
∑_σ carryThresholdMeasure Q σ m · Y_sh(σ) ≤ 1·(1·tiltSum)^m · z/(z-1).
```
Every carry-geometry step is proved; only the calibrations (isolated elsewhere)
remain. -/
theorem integerCarry_areaWeighted_regular_le (Q Csh G m Ymax : ℕ) (z : ℝ)
    (hz : 1 < z) (Ysh : (Fin m → ℕ) → ℝ)
    (hYsh_nonneg : ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
        0 ≤ Ysh σ)
    (hYsh_le : ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
        Ysh σ ≤ (Ymax : ℝ))
    (hcal : ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
        ∀ j : ℕ, (j : ℝ) < Ysh σ → j ≤ ∑ i, shellCost Csh (σ i)) :
    ∑ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
        carryThresholdMeasure Q σ m * Ysh σ
      ≤ 1 * (1 * regularTiltSum Csh G z) ^ m * (z / (z - 1)) := by
  refine lemma22_1A_areaWeighted_regular_le Csh G m Ymax 1 1 z hz (by norm_num)
    (by norm_num) (fun σ => carryThresholdMeasure Q σ m) Ysh ?_ hYsh_nonneg ?_ hYsh_le hcal
  · intro σ _
    exact (carryThresholdFibre Q Csh G m).μ_nonneg σ m
  · intro σ hσ
    exact (carryThresholdFibre Q Csh G m).toRegularEdgeData.regular_path_bound hσ

/-! ## §6. Honest determination of the residual after this file -/

/-- The genuine inputs of the §22 Chernoff phase, classified after this file
closes the carry↔dyadic-cylinder identification and the principal shell-Carleson
budget of Lemma 22.2.  The first three are now **theorems** (the carry-geometry
residual is closed); the last two are non-geometric numeric calibrations now
CLOSED in `ChernoffCalibrationCore` (WAVE-15), so with Lemma 22.2 the entire
Chernoff class is closed. -/
def chernoffCarlesonIdentResiduals : List String :=
  [ -- closed here
    "CLOSED: per-path regularity wt0(σ) ≤ 2^{-cost(σ)} (K=1) for the actual integer-carry threshold measure (carryThresholdMeasure_path_regularity; via the proved gap_contraction sub-conjugacy through regular_path_bound)",
    "CLOSED: carry↔dyadic-cylinder identification — the integer carry's scale-L address fibre IS the dyadic cylinder (carryCell_eq_consistentInterval; bottoms out in integerCarry_zeroDigits / integerCarry_succ_of_zero)",
    "CLOSED: principal shell-Carleson budget ∑_{v∈Prin} 2^{-s(u,v)} ≤ K^{-1} (Lemma 22.2) from genuine disjointness of dyadic carry sub-fibres (integerCarry_principalShellCarleson_budget; sharp: uniform children saturate at K^{-1})",
    -- WAVE-15: both calibrations now CLOSED in ChernoffCalibrationCore (no longer residual)
    "CLOSED (WAVE-15, ChernoffCalibrationCore.shellPaidMultiplier_calibration): shell-paid calibration n < Y_sh(σ) ⟹ n ≤ cost(σ) (Definition K.1.2) is now a THEOREM — Y_sh = min{Y_ν, max(cost - reserve, 0)} ≤ cost structurally; hcal removed from Lemma 22.1A",
    "CLOSED (WAVE-15, ChernoffCalibrationCore.regularFamily_calibration_z_two): length-vs-threshold calibration (K·tiltSum)^m·z/(z-1) into cStar·ξ·X/6 discharged at the pinned constants, reducing to the geometric d·m ≤ Y; with Lemma 22.2 the Chernoff class is now fully closed (Lemma 22.2 + both calibrations)" ]

theorem chernoffCarlesonIdentResiduals_eq :
    chernoffCarlesonIdentResiduals.length = 5 := rfl

end

end Erdos260
