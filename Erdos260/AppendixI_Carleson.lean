import Mathlib
import Erdos260.StoppedInduction
import Erdos260.StoppedTree
import Erdos260.StoppedTreeIndex

/-!
# Appendix I — principal shell-Carleson budget, branch charge, and the
principal-chain dichotomy

This file strengthens **Lemma 22.2** of `proof_v4.tex`
(`§ principal-shell-Carleson-budget`)

```
  ∑_{v ∈ Prin(u)} 2^{-𝔰(u,v)} ≤ K⁻¹
```

and pushes it toward the **stopped-branch shell-cost accounting** that feeds the
shell-Chernoff bound (Lemma 22.1).  The faithful abstract budget is already
recorded upstream as `Erdos260.lemma22_2_principalShellCarleson`; here we draw
its genuine consequences.

## What is proved (and how faithful)

* **Charge ↔ moment vocabulary (unconditional).**
  `principalShellCharge_eq_weightedMoment` identifies the Carleson charge
  `∑ 2^{-𝔰}` with the dyadic exponential moment `weightedMoment _ 1 shell (1/2)`,
  and `branchShellCharge_eq_branchWeightedMoment` identifies the single-branch
  charge `2^{-branchShellCost}` with the branch moment `branchWeightedMoment`.
  These connect the Carleson charge to the exact `weightedMoment`/
  `branchWeightedMoment` machinery used by the Chernoff tail (which itself runs
  at a tilt `z > 1`; the charge is the `z = 1/2` discount, stated honestly).

* **Per-node Carleson consequences (conditional on the geometric principal
  hypotheses, which are exactly those of Lemma 22.2).**
  From the budget we derive that each principal child pays at least `log₂ K`
  shell (`principalChild_two_pow_shell_ge` : `K ≤ 2^{𝔰}`), and a genuine
  **bounded-branching** count: at most `K⁻¹ · 2^M` principal children have shell
  `≤ M` (`principal_lowShell_card_le'`).  Both go through
  `lemma22_2_principalShellCarleson`.

* **Principal-chain telescoping (the manuscript "multiply along a principal
  chain").**  `principalChain_mass_ge` is the literal primal statement
  `|Ω_n| ≥ Kⁿ|Ω₀| 2^{-∑𝔰}`.  Dually, `principalChain_pow_le_two_pow_shellSum_of_budget`
  multiplies the *per-node Carleson budget* along the chain to get
  `Kⁿ ≤ 2^{∑𝔰}`.

* **The dichotomy ("large cumulative shell cost ⇒ Chernoff tail").**
  `principalChain_shellSum_ge_of_pow_le` / `..._of_mass`: if `2^c ≤ K` then a
  principal chain of length `n` has cumulative shell cost `≥ c·n`, so long
  chains have proportionally large cumulative shell.  Modelling the chain as a
  genuine `StoppedBranch` (`shellChainBranch`) whose recorded shell word sums to
  the cumulative cost (`branchShellCost_shellChainBranch`), the chain branch
  lands in the high shell-cost set `highBranchCostSet` (the Chernoff-tail set of
  `StoppedInduction`).  This is packaged as `lemma22_2_principalChainDichotomy`.

## Honest boundary

The geometric inputs of Lemma 22.2 — that principal children satisfy
`|Ω_v| ≥ K|Ω_u| 2^{-𝔰}` and are disjoint subsets of `Ω_u` (so their masses sum
to `≤ |Ω_u|`) — are taken as **explicit hypotheses** exactly as in
`lemma22_2_principalShellCarleson`; they are the analytic content proved
elsewhere.  Everything in this file above those hypotheses is a real, fully
discharged inequality.  No `sorry`, `axiom`, or `admit`.
-/

namespace Erdos260

open Finset

/-! ### A real-power bridge for the dyadic Carleson charge

`principalShellCharge` is written with the integer power `2 ^ (-(s : ℤ))`.  The
moment / Chernoff machinery is written with the natural power `(1/2) ^ s`.  This
bridge lets us move between the two faithfully. -/

/-- `2 ^ (-(n : ℤ)) = (1/2) ^ n`: the dyadic Carleson weight is the `z = 1/2`
exponential weight. -/
theorem two_zpow_neg_natCast (n : ℕ) :
    (2 : ℝ) ^ (-(n : ℤ)) = (1 / 2 : ℝ) ^ n := by
  rw [zpow_neg, zpow_natCast, one_div, inv_pow]

/-! ### Charge ↔ moment vocabulary link -/

/-- **Carleson charge = dyadic moment.**  The principal shell-Carleson charge
`∑_{v} 2^{-𝔰(v)}` is exactly the exponential `weightedMoment` of the shell cost
at tilt `z = 1/2` with unit weights.  This is the precise bridge between the
Lemma 22.2 budget and the moment vocabulary of the shell-Chernoff bound. -/
theorem principalShellCharge_eq_weightedMoment (children : Finset PrincipalChild) :
    principalShellCharge children
      = weightedMoment children (fun _ => (1 : ℝ)) (fun v => v.shell) (1 / 2) := by
  unfold principalShellCharge weightedMoment
  refine Finset.sum_congr rfl (fun v _ => ?_)
  simp only [one_mul]
  exact two_zpow_neg_natCast v.shell

/-- **Single-branch charge = branch moment.**  The dyadic charge of one stopped
branch, `2^{-branchShellCost(b)}`, equals the `z = 1/2` `branchWeightedMoment`
of the singleton family `{b}`.  This is the per-branch instance of the
charge ↔ moment identity along a principal chain. -/
theorem branchShellCharge_eq_branchWeightedMoment (b : StoppedBranch) :
    (2 : ℝ) ^ (-(branchShellCost b : ℤ))
      = branchWeightedMoment {b} (fun _ => (1 : ℝ)) (1 / 2) := by
  simp only [branchWeightedMoment, weightedMoment, Finset.sum_singleton, one_mul]
  exact two_zpow_neg_natCast _

/-! ### Per-node consequences of the Lemma 22.2 budget

All of these take exactly the geometric hypotheses of
`lemma22_2_principalShellCarleson` and use it as a black box. -/

/-- A single principal child's charge is at most the whole Carleson charge. -/
theorem principalShellCharge_term_le {children : Finset PrincipalChild}
    {v : PrincipalChild} (hv : v ∈ children) :
    (2 : ℝ) ^ (-(v.shell : ℤ)) ≤ principalShellCharge children := by
  unfold principalShellCharge
  exact Finset.single_le_sum (f := fun w => (2 : ℝ) ^ (-(w.shell : ℤ)))
    (fun w _ => by positivity) hv

/-- **Per-child Carleson bound.**  Each principal child has dyadic charge at most
`K⁻¹`.  This is the pointwise specialisation of the Lemma 22.2 budget. -/
theorem principalChild_charge_le_inv_K
    {children : Finset PrincipalChild} {parent K : ℝ}
    (hparent : 0 < parent) (hK : 0 < K)
    (hdisjoint : principalWeight children ≤ parent)
    (hprincipal :
      ∀ v ∈ children, K * parent * (2 : ℝ) ^ (-(v.shell : ℤ)) ≤ v.weight)
    {v : PrincipalChild} (hv : v ∈ children) :
    (2 : ℝ) ^ (-(v.shell : ℤ)) ≤ K⁻¹ :=
  (principalShellCharge_term_le hv).trans
    (lemma22_2_principalShellCarleson hparent hK hdisjoint hprincipal)

/-- **Each principal child pays at least `log₂ K` shell.**  Reading the per-child
Carleson bound `2^{-𝔰} ≤ K⁻¹` as `K ≤ 2^{𝔰}`: a large Carleson constant `K`
forces each principal child to carry a correspondingly large shell cost.  This is
the seed of the principal-chain dichotomy. -/
theorem principalChild_two_pow_shell_ge
    {children : Finset PrincipalChild} {parent K : ℝ}
    (hparent : 0 < parent) (hK : 0 < K)
    (hdisjoint : principalWeight children ≤ parent)
    (hprincipal :
      ∀ v ∈ children, K * parent * (2 : ℝ) ^ (-(v.shell : ℤ)) ≤ v.weight)
    {v : PrincipalChild} (hv : v ∈ children) :
    K ≤ (2 : ℝ) ^ v.shell := by
  have hle : (2 : ℝ) ^ (-(v.shell : ℤ)) ≤ K⁻¹ :=
    principalChild_charge_le_inv_K hparent hK hdisjoint hprincipal hv
  rw [zpow_neg, zpow_natCast] at hle
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ v.shell := by positivity
  exact (inv_le_inv₀ h2pos hK).1 hle

/-- **Bounded branching, budget form.**  The total dyadic weight `card · 2^{-M}`
of the principal children with shell `≤ M` is at most `K⁻¹`. -/
theorem principal_lowShell_card_le
    {children : Finset PrincipalChild} {parent K : ℝ} {M : ℕ}
    (hparent : 0 < parent) (hK : 0 < K)
    (hdisjoint : principalWeight children ≤ parent)
    (hprincipal :
      ∀ v ∈ children, K * parent * (2 : ℝ) ^ (-(v.shell : ℤ)) ≤ v.weight) :
    ((children.filter fun v => v.shell ≤ M).card : ℝ) * (2 : ℝ) ^ (-(M : ℤ)) ≤ K⁻¹ := by
  set F := children.filter fun v => v.shell ≤ M with hF
  have hbudget : principalShellCharge children ≤ K⁻¹ :=
    lemma22_2_principalShellCarleson hparent hK hdisjoint hprincipal
  have step1 :
      ∑ v ∈ F, (2 : ℝ) ^ (-(M : ℤ)) ≤ ∑ v ∈ F, (2 : ℝ) ^ (-(v.shell : ℤ)) := by
    refine Finset.sum_le_sum (fun v hv => ?_)
    have hvM : v.shell ≤ M := (Finset.mem_filter.1 hv).2
    exact zpow_le_zpow_right₀ (by norm_num) (neg_le_neg (by exact_mod_cast hvM))
  have step2 :
      ∑ v ∈ F, (2 : ℝ) ^ (-(v.shell : ℤ)) ≤ principalShellCharge children := by
    unfold principalShellCharge
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
    intro v _ _; positivity
  have step3 :
      ∑ _v ∈ F, (2 : ℝ) ^ (-(M : ℤ)) = (F.card : ℝ) * (2 : ℝ) ^ (-(M : ℤ)) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [step3] at step1
  exact step1.trans (step2.trans hbudget)

/-- **Bounded branching, count form.**  At most `K⁻¹ · 2^M` principal children
have shell cost `≤ M`.  The Carleson budget controls the number of low-shell
principal children. -/
theorem principal_lowShell_card_le'
    {children : Finset PrincipalChild} {parent K : ℝ} {M : ℕ}
    (hparent : 0 < parent) (hK : 0 < K)
    (hdisjoint : principalWeight children ≤ parent)
    (hprincipal :
      ∀ v ∈ children, K * parent * (2 : ℝ) ^ (-(v.shell : ℤ)) ≤ v.weight) :
    ((children.filter fun v => v.shell ≤ M).card : ℝ) ≤ K⁻¹ * (2 : ℝ) ^ M := by
  have h := principal_lowShell_card_le hparent hK hdisjoint hprincipal (M := M)
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ M := by positivity
  rw [zpow_neg, zpow_natCast] at h
  have hmul := mul_le_mul_of_nonneg_right h h2pos.le
  rwa [mul_assoc, inv_mul_cancel₀ h2pos.ne', mul_one] at hmul

/-! ### The principal-chain telescoping (primal) -/

/-- **Multiplying along a principal chain (primal mass form).**  If at each step
`i < n` the child mass dominates `K · |Ω_i| · 2^{-𝔰_i}` (the principal
condition), then the terminal mass satisfies
`|Ω_n| ≥ Kⁿ · |Ω_0| · 2^{-∑ 𝔰_i}`.  This is the literal manuscript telescoping
behind the dichotomy. -/
theorem principalChain_mass_ge
    {Ω : ℕ → ℝ} {s : ℕ → ℕ} {K : ℝ} (hK : 0 ≤ K) {n : ℕ}
    (hstep : ∀ i, i < n → K * Ω i * (2 : ℝ) ^ (-(s i : ℤ)) ≤ Ω (i + 1)) :
    K ^ n * Ω 0 * (2 : ℝ) ^ (-((∑ i ∈ Finset.range n, s i : ℕ) : ℤ)) ≤ Ω n := by
  simp only [two_zpow_neg_natCast] at hstep ⊢
  induction n with
  | zero => simp
  | succ n ih =>
      have hIH := ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi))
      have hlast := hstep n (Nat.lt_succ_self n)
      rw [Finset.sum_range_succ, pow_succ, pow_add]
      calc
        K ^ n * K * Ω 0
            * ((1 / 2 : ℝ) ^ (∑ i ∈ Finset.range n, s i) * (1 / 2 : ℝ) ^ s n)
            = (K * (1 / 2 : ℝ) ^ s n)
                * (K ^ n * Ω 0 * (1 / 2 : ℝ) ^ (∑ i ∈ Finset.range n, s i)) := by ring
        _ ≤ (K * (1 / 2 : ℝ) ^ s n) * Ω n :=
            mul_le_mul_of_nonneg_left hIH (mul_nonneg hK (by positivity))
        _ = K * Ω n * (1 / 2 : ℝ) ^ s n := by ring
        _ ≤ Ω (n + 1) := hlast

/-- **Carleson budget along a chain, primal form.**  Combining the telescoping
mass bound with mass monotonicity `|Ω_n| ≤ |Ω_0|` (the children are nested
subsets) gives the cumulative budget `Kⁿ ≤ 2^{∑ 𝔰_i}`. -/
theorem principalChain_pow_le_two_pow_sum_of_mass
    {Ω : ℕ → ℝ} {s : ℕ → ℕ} {K : ℝ} (hK : 0 ≤ K) {n : ℕ}
    (hpos : 0 < Ω 0) (hmono : Ω n ≤ Ω 0)
    (hstep : ∀ i, i < n → K * Ω i * (2 : ℝ) ^ (-(s i : ℤ)) ≤ Ω (i + 1)) :
    K ^ n ≤ (2 : ℝ) ^ (∑ i ∈ Finset.range n, s i) := by
  have hmass := principalChain_mass_ge hK hstep
  set S := ∑ i ∈ Finset.range n, s i with hSdef
  rw [zpow_neg, zpow_natCast] at hmass
  have h1 : K ^ n * Ω 0 * ((2 : ℝ) ^ S)⁻¹ ≤ Ω 0 := hmass.trans hmono
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ S := by positivity
  have hm := mul_le_mul_of_nonneg_right h1 h2pos.le
  rw [mul_assoc, inv_mul_cancel₀ h2pos.ne', mul_one] at hm
  rw [mul_comm (Ω 0) ((2 : ℝ) ^ S)] at hm
  exact le_of_mul_le_mul_right hm hpos

/-! ### The principal-chain telescoping (dual: multiply the Carleson budget) -/

/-- Elementary multiplicative telescoping: from the per-node bound `K ≤ 2^{s i}`
along a chain of length `n` we get `Kⁿ ≤ 2^{∑ s i}`. -/
theorem principalChain_pow_le_two_pow_sum
    {K : ℝ} {s : ℕ → ℕ} (hKpos : 0 ≤ K) {n : ℕ}
    (hstep : ∀ i, i < n → K ≤ (2 : ℝ) ^ s i) :
    K ^ n ≤ (2 : ℝ) ^ (∑ i ∈ Finset.range n, s i) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hIH := ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi))
      have hlast := hstep n (Nat.lt_succ_self n)
      rw [Finset.sum_range_succ, pow_succ, pow_add]
      exact mul_le_mul hIH hlast hKpos (by positivity)

/-- **Carleson budget along a chain, dual form.**  Feeding the per-node Lemma
22.2 consequence `K ≤ 2^{𝔰_i}` (one chosen principal child per node) into the
telescoping gives `Kⁿ ≤ 2^{∑ 𝔰_i}`.  This is the genuine use of
`lemma22_2_principalShellCarleson` in the branch-charge accounting. -/
theorem principalChain_pow_le_two_pow_shellSum_of_budget
    {K : ℝ} (hK : 0 < K) {n : ℕ}
    {parent : ℕ → ℝ} {prin : ℕ → Finset PrincipalChild} {child : ℕ → PrincipalChild}
    (hmem : ∀ i, i < n → child i ∈ prin i)
    (hparent : ∀ i, i < n → 0 < parent i)
    (hdisjoint : ∀ i, i < n → principalWeight (prin i) ≤ parent i)
    (hprincipal :
      ∀ i, i < n → ∀ v ∈ prin i,
        K * parent i * (2 : ℝ) ^ (-(v.shell : ℤ)) ≤ v.weight) :
    K ^ n ≤ (2 : ℝ) ^ (∑ i ∈ Finset.range n, (child i).shell) :=
  principalChain_pow_le_two_pow_sum hK.le
    (fun i hi =>
      principalChild_two_pow_shell_ge (hparent i hi) hK (hdisjoint i hi)
        (hprincipal i hi) (hmem i hi))

/-! ### The dichotomy: long principal chains have large cumulative shell cost -/

/-- **Principal-chain dichotomy (dual form).**  If each principal step pays shell
at least `c` in the sense `2^c ≤ K`, then a chain with per-node bounds
`K ≤ 2^{s i}` has cumulative shell cost `≥ c · n`.  Hence a long principal chain
necessarily accumulates large shell cost — the input to the Chernoff tail. -/
theorem principalChain_shellSum_ge_of_pow_le
    {K : ℝ} {s : ℕ → ℕ} {n c : ℕ} (hKpos : 0 ≤ K)
    (hc : (2 : ℝ) ^ c ≤ K)
    (hstep : ∀ i, i < n → K ≤ (2 : ℝ) ^ s i) :
    c * n ≤ ∑ i ∈ Finset.range n, s i := by
  have hpow : K ^ n ≤ (2 : ℝ) ^ (∑ i ∈ Finset.range n, s i) :=
    principalChain_pow_le_two_pow_sum hKpos hstep
  have hle : (2 : ℝ) ^ (c * n) ≤ (2 : ℝ) ^ (∑ i ∈ Finset.range n, s i) := by
    calc
      (2 : ℝ) ^ (c * n) = ((2 : ℝ) ^ c) ^ n := by rw [pow_mul]
      _ ≤ K ^ n := pow_le_pow_left₀ (by positivity) hc n
      _ ≤ (2 : ℝ) ^ (∑ i ∈ Finset.range n, s i) := hpow
  exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 hle

/-- **Principal-chain dichotomy (primal form).**  Same conclusion `c · n ≤ ∑ 𝔰_i`
obtained directly from the manuscript telescoping of masses plus mass
monotonicity. -/
theorem principalChain_shellSum_ge_of_mass
    {Ω : ℕ → ℝ} {s : ℕ → ℕ} {K : ℝ} {n c : ℕ} (hKpos : 0 ≤ K)
    (hc : (2 : ℝ) ^ c ≤ K)
    (hpos : 0 < Ω 0) (hmono : Ω n ≤ Ω 0)
    (hstep : ∀ i, i < n → K * Ω i * (2 : ℝ) ^ (-(s i : ℤ)) ≤ Ω (i + 1)) :
    c * n ≤ ∑ i ∈ Finset.range n, s i := by
  have hpow := principalChain_pow_le_two_pow_sum_of_mass hKpos hpos hmono hstep
  have hle : (2 : ℝ) ^ (c * n) ≤ (2 : ℝ) ^ (∑ i ∈ Finset.range n, s i) := by
    calc
      (2 : ℝ) ^ (c * n) = ((2 : ℝ) ^ c) ^ n := by rw [pow_mul]
      _ ≤ K ^ n := pow_le_pow_left₀ (by positivity) hc n
      _ ≤ (2 : ℝ) ^ (∑ i ∈ Finset.range n, s i) := hpow
  exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 hle

/-! ### Realising the cumulative shell cost as a genuine `branchShellCost`

A principal chain of shell costs `s 0, …, s (n-1)` is realised as a genuine
`StoppedBranch` whose recorded shell word sums to the cumulative cost.  This
connects the abstract chain sum to the `branchShellCost` / `highBranchCostSet`
vocabulary of the stopped induction (the Chernoff-tail set). -/

/-- The stopped branch recording a chain of shell costs `s 0, …, s (n-1)`. -/
def shellChainBranch (s : ℕ → ℕ) (n : ℕ) : StoppedBranch :=
  ⟨(List.range n).map fun i =>
    { source := i, target := i + 1, shellCost := s i, thresholdLayer := i }⟩

/-- **Bookkeeping identity.**  The recorded shell word of `shellChainBranch s n`
sums to the cumulative chain shell cost `∑ i < n, s i`. -/
theorem branchShellCost_shellChainBranch (s : ℕ → ℕ) (n : ℕ) :
    branchShellCost (shellChainBranch s n) = ∑ i ∈ Finset.range n, s i := by
  simp only [branchShellCost, shellChainBranch]
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.map_append, List.sum_append,
        Finset.sum_range_succ, ih]
      simp

/-- The chain branch lies in the high shell-cost (Chernoff-tail) set as soon as
its cumulative shell cost reaches the threshold `Y`. -/
theorem shellChainBranch_mem_highBranchCostSet
    {s : ℕ → ℕ} {n Y : ℕ} (hY : Y ≤ ∑ i ∈ Finset.range n, s i) :
    shellChainBranch s n ∈ highBranchCostSet {shellChainBranch s n} Y := by
  rw [mem_highBranchCostSet]
  refine ⟨Finset.mem_singleton_self _, ?_⟩
  rw [branchShellCost_shellChainBranch]
  exact hY

/-! ### Manuscript-named packaging -/

/-- **Lemma 22.2 principal-chain dichotomy (branch-charge form).**

A principal chain `child 0, …, child (n-1)` whose nodes each satisfy the Lemma
22.2 geometric hypotheses (positivity, disjointness, principal mass bound), with
per-step Carleson constant satisfying `2^c ≤ K`, has cumulative shell cost at
least `c · n`.  Modelled as a genuine `StoppedBranch`, the chain therefore lies
in the high shell-cost set `highBranchCostSet` once `Y ≤ c · n`, i.e. it enters
the Chernoff tail of Lemma 22.1.

This is the faithful realisation of the manuscript sentence *"A principal chain
either has large cumulative shell/defect cost, hence enters the Chernoff tail,
…"*, with the principal-child geometry isolated as explicit hypotheses. -/
theorem lemma22_2_principalChainDichotomy
    {K : ℝ} (hK : 0 < K) {n c Y : ℕ}
    {parent : ℕ → ℝ} {prin : ℕ → Finset PrincipalChild} {child : ℕ → PrincipalChild}
    (hc : (2 : ℝ) ^ c ≤ K)
    (hmem : ∀ i, i < n → child i ∈ prin i)
    (hparent : ∀ i, i < n → 0 < parent i)
    (hdisjoint : ∀ i, i < n → principalWeight (prin i) ≤ parent i)
    (hprincipal :
      ∀ i, i < n → ∀ v ∈ prin i,
        K * parent i * (2 : ℝ) ^ (-(v.shell : ℤ)) ≤ v.weight)
    (hYn : Y ≤ c * n) :
    shellChainBranch (fun i => (child i).shell) n
      ∈ highBranchCostSet {shellChainBranch (fun i => (child i).shell) n} Y := by
  have hshell : c * n ≤ ∑ i ∈ Finset.range n, (child i).shell :=
    principalChain_shellSum_ge_of_pow_le hK.le hc
      (fun i hi =>
        principalChild_two_pow_shell_ge (hparent i hi) hK (hdisjoint i hi)
          (hprincipal i hi) (hmem i hi))
  exact shellChainBranch_mem_highBranchCostSet (hYn.trans hshell)

end Erdos260
