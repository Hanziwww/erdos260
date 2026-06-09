import Erdos260.Ledger

/-!
# Shell-weighted stopped induction primitives

This file contains the finite shell-cost vocabulary for Section 22 of
`proof_v2.tex`: shell cost, branch cost, and the elementary principal
Carleson inequality in the form used by the stopped induction.
-/

namespace Erdos260

open Finset

noncomputable section

/-- Shell cost `max(h - Csh, 0)` as natural subtraction. -/
def shellCost (Csh h : Nat) : Nat :=
  h - Csh

/-- Total shell cost of a stopped branch. -/
def branchShellCost (b : StoppedBranch) : Nat :=
  (b.edges.map fun e => e.shellCost).sum

@[simp]
theorem shellCost_eq_zero_of_le {Csh h : Nat} (hh : h <= Csh) :
    shellCost Csh h = 0 := by
  simp [shellCost, Nat.sub_eq_zero_of_le hh]

theorem shellCost_pos_iff {Csh h : Nat} :
    0 < shellCost Csh h ↔ Csh < h := by
  unfold shellCost
  omega

theorem shellCost_le_height (Csh h : Nat) :
    shellCost Csh h <= h := by
  unfold shellCost
  exact Nat.sub_le h Csh

theorem height_le_shellCost_add_margin (Csh h : Nat) :
    h <= shellCost Csh h + Csh := by
  unfold shellCost
  omega

theorem le_shellCost_of_margin_le {Csh h Y : Nat}
    (hY : Csh + Y <= h) :
    Y <= shellCost Csh h := by
  unfold shellCost
  omega

@[simp]
theorem branchShellCost_nil :
    branchShellCost ⟨[]⟩ = 0 := rfl

@[simp]
theorem branchShellCost_cons (e : BranchEdge) (es : List BranchEdge) :
    branchShellCost ⟨e :: es⟩ =
      e.shellCost + branchShellCost ⟨es⟩ := by
  unfold branchShellCost
  simp

theorem branchShellCost_append (xs ys : List BranchEdge) :
    branchShellCost ⟨xs ++ ys⟩ =
      branchShellCost ⟨xs⟩ + branchShellCost ⟨ys⟩ := by
  unfold branchShellCost
  simp [List.map_append]

theorem branchShellCost_eq_zero_of_edges_zero {b : StoppedBranch}
    (hzero : ∀ e ∈ b.edges, e.shellCost = 0) :
    branchShellCost b = 0 := by
  cases b with
  | mk edges =>
      induction edges with
      | nil => rfl
      | cons e es ih =>
          have he : e.shellCost = 0 := hzero e (by simp)
          have hes : ∀ e' ∈ es, e'.shellCost = 0 := by
            intro e' he'
            exact hzero e' (by simp [he'])
          have ih' : branchShellCost ⟨es⟩ = 0 := ih hes
          rw [branchShellCost_cons, he, ih']

theorem edges_zero_of_branchShellCost_eq_zero {b : StoppedBranch}
    (hzero : branchShellCost b = 0) :
    ∀ e ∈ b.edges, e.shellCost = 0 := by
  cases b with
  | mk edges =>
      induction edges with
      | nil =>
          intro e he
          simp at he
      | cons e es ih =>
          rw [branchShellCost_cons] at hzero
          have he_zero : e.shellCost = 0 := by omega
          have htail_zero : branchShellCost ⟨es⟩ = 0 := by omega
          intro e' he'
          simp at he'
          rcases he' with heq | hemem
          · subst heq
            exact he_zero
          · exact ih htail_zero e' hemem

theorem branchShellCost_eq_zero_iff_edges_zero {b : StoppedBranch} :
    branchShellCost b = 0 ↔ ∀ e ∈ b.edges, e.shellCost = 0 :=
  ⟨edges_zero_of_branchShellCost_eq_zero, branchShellCost_eq_zero_of_edges_zero⟩

theorem branchShellCost_le_length_mul_of_edgeCost_le
    {b : StoppedBranch} {B : Nat}
    (hB : ∀ e ∈ b.edges, e.shellCost <= B) :
    branchShellCost b <= b.edges.length * B := by
  cases b with
  | mk edges =>
      induction edges with
      | nil =>
          simp [branchShellCost]
      | cons e es ih =>
          have he : e.shellCost <= B := hB e (by simp)
          have hes : ∀ e' ∈ es, e'.shellCost <= B := by
            intro e' he'
            exact hB e' (by simp [he'])
          have ih' := ih hes
          rw [branchShellCost_cons]
          calc
            e.shellCost + branchShellCost ⟨es⟩ <= B + es.length * B := by
              exact Nat.add_le_add he ih'
            _ = (es.length + 1) * B := by ring

theorem branchShellCost_pos_of_edgeCost_pos
    {b : StoppedBranch} {e : BranchEdge}
    (he : e ∈ b.edges) (hpos : 0 < e.shellCost) :
    0 < branchShellCost b := by
  cases b with
  | mk edges =>
      induction edges with
      | nil =>
          simp at he
      | cons e' es ih =>
          rw [branchShellCost_cons]
          simp at he
          rcases he with heq | hes
          · subst heq
            omega
          · have ih' : 0 < branchShellCost ⟨es⟩ := ih hes
            omega

/-- Finite mass of a family of paths. -/
def weightedMass {α : Type*} (paths : Finset α) (weight : α -> ℝ) : ℝ :=
  ∑ p ∈ paths, weight p

/-- Exponential moment of shell cost. -/
def weightedMoment {α : Type*} (paths : Finset α) (weight : α -> ℝ)
    (cost : α -> Nat) (z : ℝ) : ℝ :=
  ∑ p ∈ paths, weight p * z ^ cost p

/-- Subfamily with shell cost at least `Y`. -/
def highCostSet {α : Type*} (paths : Finset α) (cost : α -> Nat) (Y : Nat) :
    Finset α :=
  paths.filter fun p => Y <= cost p

theorem mem_highCostSet {α : Type*}
    {paths : Finset α} {cost : α -> Nat} {Y : Nat} {p : α} :
    p ∈ highCostSet paths cost Y <-> p ∈ paths ∧ Y <= cost p := by
  simp [highCostSet]

theorem weightedMass_nonneg {α : Type*} {paths : Finset α} {weight : α -> ℝ}
    (hweight : ∀ p ∈ paths, 0 <= weight p) :
    0 <= weightedMass paths weight := by
  unfold weightedMass
  exact sum_nonneg hweight

theorem weightedMoment_nonneg {α : Type*} {paths : Finset α} {weight : α -> ℝ}
    {cost : α -> Nat} {z : ℝ}
    (hweight : ∀ p ∈ paths, 0 <= weight p) (hz : 0 <= z) :
    0 <= weightedMoment paths weight cost z := by
  unfold weightedMoment
  exact sum_nonneg fun p hp => mul_nonneg (hweight p hp) (pow_nonneg hz _)

theorem weightedMass_mono_subset {α : Type*} {s t : Finset α}
    {weight : α -> ℝ} (hst : s ⊆ t)
    (hweight : ∀ p ∈ t, 0 <= weight p) :
    weightedMass s weight <= weightedMass t weight := by
  unfold weightedMass
  exact sum_le_sum_of_subset_of_nonneg hst fun p hp _ => hweight p hp

theorem weightedMoment_mono_subset {α : Type*} {s t : Finset α}
    {weight : α -> ℝ} {cost : α -> Nat} {z : ℝ}
    (hst : s ⊆ t) (hweight : ∀ p ∈ t, 0 <= weight p) (hz : 0 <= z) :
    weightedMoment s weight cost z <= weightedMoment t weight cost z := by
  unfold weightedMoment
  exact sum_le_sum_of_subset_of_nonneg hst fun p hp _ =>
    mul_nonneg (hweight p hp) (pow_nonneg hz _)

theorem weightedMass_union_of_disjoint {α : Type*} [DecidableEq α]
    {s t : Finset α} {weight : α -> ℝ} (hdisj : Disjoint s t) :
    weightedMass (s ∪ t) weight = weightedMass s weight + weightedMass t weight := by
  unfold weightedMass
  exact sum_union hdisj

theorem weightedMoment_union_of_disjoint {α : Type*} [DecidableEq α]
    {s t : Finset α} {weight : α -> ℝ} {cost : α -> Nat} {z : ℝ}
    (hdisj : Disjoint s t) :
    weightedMoment (s ∪ t) weight cost z =
      weightedMoment s weight cost z + weightedMoment t weight cost z := by
  unfold weightedMoment
  exact sum_union hdisj

theorem weightedMass_eq_add_sdiff {α : Type*} [DecidableEq α]
    {s t : Finset α} {weight : α -> ℝ} (hts : t ⊆ s) :
    weightedMass s weight = weightedMass t weight + weightedMass (s \ t) weight := by
  have hsplit : s = t ∪ (s \ t) := by
    ext x
    constructor
    · intro hx
      by_cases hxt : x ∈ t
      · exact mem_union.2 (Or.inl hxt)
      · exact mem_union.2 (Or.inr (mem_sdiff.2 ⟨hx, hxt⟩))
    · intro hx
      rcases mem_union.1 hx with hxt | hxs
      · exact hts hxt
      · exact (mem_sdiff.1 hxs).1
  calc
    weightedMass s weight = weightedMass (t ∪ (s \ t)) weight := by
      exact congrArg (fun u => weightedMass u weight) hsplit
    _ = weightedMass t weight + weightedMass (s \ t) weight := by
      exact weightedMass_union_of_disjoint
        (s := t) (t := s \ t) (weight := weight) disjoint_sdiff

theorem weightedMoment_eq_add_sdiff {α : Type*} [DecidableEq α]
    {s t : Finset α} {weight : α -> ℝ} {cost : α -> Nat} {z : ℝ}
    (hts : t ⊆ s) :
    weightedMoment s weight cost z =
      weightedMoment t weight cost z + weightedMoment (s \ t) weight cost z := by
  have hsplit : s = t ∪ (s \ t) := by
    ext x
    constructor
    · intro hx
      by_cases hxt : x ∈ t
      · exact mem_union.2 (Or.inl hxt)
      · exact mem_union.2 (Or.inr (mem_sdiff.2 ⟨hx, hxt⟩))
    · intro hx
      rcases mem_union.1 hx with hxt | hxs
      · exact hts hxt
      · exact (mem_sdiff.1 hxs).1
  calc
    weightedMoment s weight cost z =
        weightedMoment (t ∪ (s \ t)) weight cost z := by
      exact congrArg (fun u => weightedMoment u weight cost z) hsplit
    _ = weightedMoment t weight cost z +
        weightedMoment (s \ t) weight cost z := by
      exact weightedMoment_union_of_disjoint
        (s := t) (t := s \ t) (weight := weight) (cost := cost) (z := z)
        disjoint_sdiff

theorem weightedMoment_one {α : Type*} (paths : Finset α)
    (weight : α -> ℝ) (cost : α -> Nat) :
    weightedMoment paths weight cost 1 = weightedMass paths weight := by
  simp [weightedMoment, weightedMass]

theorem weightedMass_le_weightedMoment_of_one_le {α : Type*}
    {paths : Finset α} {weight : α -> ℝ} {cost : α -> Nat} {z : ℝ}
    (hweight : ∀ p ∈ paths, 0 <= weight p) (hz : 1 <= z) :
    weightedMass paths weight <= weightedMoment paths weight cost z := by
  unfold weightedMass weightedMoment
  exact sum_le_sum fun p hp => by
    have hpow : (1 : ℝ) <= z ^ cost p := by
      simpa using (pow_le_pow_right₀ hz (Nat.zero_le (cost p)) :
        z ^ 0 <= z ^ cost p)
    calc
      weight p = weight p * 1 := by ring
      _ <= weight p * z ^ cost p :=
          mul_le_mul_of_nonneg_left hpow (hweight p hp)

theorem weightedMoment_le_mass_mul_pow_of_cost_le {α : Type*}
    {paths : Finset α} {weight : α -> ℝ} {cost : α -> Nat}
    {z : ℝ} {M : Nat}
    (hweight : ∀ p ∈ paths, 0 <= weight p) (hz : 1 <= z)
    (hcost : ∀ p ∈ paths, cost p <= M) :
    weightedMoment paths weight cost z <= weightedMass paths weight * z ^ M := by
  unfold weightedMoment weightedMass
  calc
    (∑ p ∈ paths, weight p * z ^ cost p) <=
        ∑ p ∈ paths, weight p * z ^ M := by
          exact sum_le_sum fun p hp => by
            exact mul_le_mul_of_nonneg_left
              (pow_le_pow_right₀ hz (hcost p hp)) (hweight p hp)
    _ = (∑ p ∈ paths, weight p) * z ^ M := by
          rw [Finset.sum_mul]

theorem weightedMoment_le_card_mul_of_le {α : Type*}
    {paths : Finset α} {weight : α -> ℝ} {cost : α -> Nat}
    {z B : ℝ}
    (hpoint : ∀ p ∈ paths, weight p * z ^ cost p <= B) :
    weightedMoment paths weight cost z <= (paths.card : ℝ) * B := by
  unfold weightedMoment
  calc
    (∑ p ∈ paths, weight p * z ^ cost p) <= ∑ _p ∈ paths, B := by
      exact sum_le_sum hpoint
    _ = (paths.card : ℝ) * B := by
      simp [mul_comm]

theorem weightedMoment_le_card_mul_const_of_weight_le {α : Type*}
    {paths : Finset α} {weight : α -> ℝ} {cost : α -> Nat}
    {z B : ℝ} {M : Nat}
    (hweight : ∀ p ∈ paths, weight p <= B)
    (hz : 1 <= z) (hB : 0 <= B)
    (hcost : ∀ p ∈ paths, cost p <= M) :
    weightedMoment paths weight cost z <= (paths.card : ℝ) * (B * z ^ M) := by
  exact weightedMoment_le_card_mul_of_le fun p hp => by
    have hznonneg : 0 <= z := by linarith
    have hpow : z ^ cost p <= z ^ M := pow_le_pow_right₀ hz (hcost p hp)
    calc
      weight p * z ^ cost p <= B * z ^ cost p := by
        exact mul_le_mul_of_nonneg_right (hweight p hp) (pow_nonneg hznonneg _)
      _ <= B * z ^ M := by
        exact mul_le_mul_of_nonneg_left hpow hB

theorem weightedMass_le_card_mul_of_le {α : Type*}
    {paths : Finset α} {weight : α -> ℝ} {B : ℝ}
    (hweight : ∀ p ∈ paths, weight p <= B) :
    weightedMass paths weight <= (paths.card : ℝ) * B := by
  unfold weightedMass
  calc
    (∑ p ∈ paths, weight p) <= ∑ _p ∈ paths, B := by
      exact sum_le_sum hweight
    _ = (paths.card : ℝ) * B := by
      simp [mul_comm]

theorem weightedMass_eq_sum_fiberwise
    {α β : Type*} [DecidableEq β]
    (paths : Finset α) (code : α -> β) (weight : α -> ℝ) :
    weightedMass paths weight =
      ∑ y ∈ paths.image code,
        weightedMass (paths.filter fun x => code x = y) weight := by
  unfold weightedMass
  symm
  simpa using
    (Finset.sum_fiberwise_of_maps_to
      (s := paths)
      (t := paths.image code)
      (g := code)
      (fun x hx => mem_image_of_mem code hx)
      weight)

theorem weightedMass_le_card_image_mul_of_fiber_mass_le
    {α β : Type*} [DecidableEq β]
    (paths : Finset α) (code : α -> β) (weight : α -> ℝ) {B : ℝ}
    (hfiber :
      ∀ y ∈ paths.image code,
        weightedMass (paths.filter fun x => code x = y) weight <= B) :
    weightedMass paths weight <= ((paths.image code).card : ℝ) * B := by
  calc
    weightedMass paths weight =
        ∑ y ∈ paths.image code,
          weightedMass (paths.filter fun x => code x = y) weight := by
            exact weightedMass_eq_sum_fiberwise paths code weight
    _ <= ∑ _y ∈ paths.image code, B := by
          exact sum_le_sum hfiber
    _ = ((paths.image code).card : ℝ) * B := by
          simp [mul_comm]

theorem weightedMass_le_code_bound_mul_of_fiber_mass_le
    {α β : Type*} [DecidableEq β]
    (paths : Finset α) (code : α -> β) (weight : α -> ℝ)
    {codeBound : Nat} {B : ℝ} (hB : 0 <= B)
    (hcodes : (paths.image code).card <= codeBound)
    (hfiber :
      ∀ y ∈ paths.image code,
        weightedMass (paths.filter fun x => code x = y) weight <= B) :
    weightedMass paths weight <= (codeBound : ℝ) * B := by
  exact (weightedMass_le_card_image_mul_of_fiber_mass_le
      paths code weight hfiber).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hcodes) hB)

theorem weightedMass_le_code_bound_mul_fiber_bound_mul_of_le
    {α β : Type*} [DecidableEq β]
    (paths : Finset α) (code : α -> β) (weight : α -> ℝ)
    {codeBound fiberBound : Nat} {W : ℝ} (hW : 0 <= W)
    (hcodes : (paths.image code).card <= codeBound)
    (hfiber :
      ∀ y ∈ paths.image code,
        (paths.filter fun x => code x = y).card <= fiberBound)
    (hweight : ∀ x ∈ paths, weight x <= W) :
    weightedMass paths weight <=
      (codeBound : ℝ) * ((fiberBound : ℝ) * W) := by
  have hfiberMass :
      ∀ y ∈ paths.image code,
        weightedMass (paths.filter fun x => code x = y) weight <=
          (fiberBound : ℝ) * W := by
    intro y hy
    have hpoint :
        ∀ x ∈ paths.filter fun x => code x = y, weight x <= W := by
      intro x hx
      exact hweight x (mem_filter.1 hx).1
    exact (weightedMass_le_card_mul_of_le hpoint).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hfiber y hy) hW)
  exact weightedMass_le_code_bound_mul_of_fiber_mass_le
    paths code weight (mul_nonneg (by positivity) hW) hcodes hfiberMass

theorem highCostSet_subset {α : Type*}
    (paths : Finset α) (cost : α -> Nat) (Y : Nat) :
    highCostSet paths cost Y ⊆ paths := by
  intro p hp
  exact (mem_highCostSet.1 hp).1

theorem highCostSet_card_le {α : Type*}
    (paths : Finset α) (cost : α -> Nat) (Y : Nat) :
    (highCostSet paths cost Y).card <= paths.card :=
  card_le_card (highCostSet_subset paths cost Y)

theorem highCostSet_mono_threshold {α : Type*}
    {paths : Finset α} {cost : α -> Nat} {Y₁ Y₂ : Nat}
    (hY : Y₁ <= Y₂) :
    highCostSet paths cost Y₂ ⊆ highCostSet paths cost Y₁ := by
  intro p hp
  rcases mem_highCostSet.1 hp with ⟨hmem, hcost⟩
  exact mem_highCostSet.2 ⟨hmem, hY.trans hcost⟩

theorem highCostSet_mono_subset {α : Type*}
    {s t : Finset α} {cost : α -> Nat} {Y : Nat}
    (hst : s ⊆ t) :
    highCostSet s cost Y ⊆ highCostSet t cost Y := by
  intro p hp
  rcases mem_highCostSet.1 hp with ⟨hmem, hcost⟩
  exact mem_highCostSet.2 ⟨hst hmem, hcost⟩

theorem highCostSet_eq_empty_of_forall_lt {α : Type*}
    {paths : Finset α} {cost : α -> Nat} {Y : Nat}
    (hcost : ∀ p ∈ paths, cost p < Y) :
    highCostSet paths cost Y = ∅ := by
  ext p
  constructor
  · intro hp
    rcases mem_highCostSet.1 hp with ⟨hmem, hY⟩
    exact False.elim (not_le_of_gt (hcost p hmem) hY)
  · intro hp
    simp at hp

theorem highCostSet_eq_self_of_forall_ge {α : Type*}
    {paths : Finset α} {cost : α -> Nat} {Y : Nat}
    (hcost : ∀ p ∈ paths, Y <= cost p) :
    highCostSet paths cost Y = paths := by
  ext p
  constructor
  · intro hp
    exact (mem_highCostSet.1 hp).1
  · intro hp
    exact mem_highCostSet.2 ⟨hp, hcost p hp⟩

theorem weightedMass_highCostSet_le {α : Type*}
    {paths : Finset α} {cost : α -> Nat} {Y : Nat} {weight : α -> ℝ}
    (hweight : ∀ p ∈ paths, 0 <= weight p) :
    weightedMass (highCostSet paths cost Y) weight <= weightedMass paths weight :=
  weightedMass_mono_subset (highCostSet_subset paths cost Y) hweight

theorem weightedMoment_highCostSet_le {α : Type*}
    {paths : Finset α} {cost : α -> Nat} {Y : Nat} {weight : α -> ℝ}
    {z : ℝ} (hweight : ∀ p ∈ paths, 0 <= weight p) (hz : 0 <= z) :
    weightedMoment (highCostSet paths cost Y) weight cost z <=
      weightedMoment paths weight cost z :=
  weightedMoment_mono_subset (highCostSet_subset paths cost Y) hweight hz

theorem shellChernoff_bound_of_moment {α : Type*}
    {paths : Finset α} {weight : α -> ℝ} {cost : α -> Nat} {Y : Nat} {z : ℝ}
    (hweight : ∀ p ∈ paths, 0 <= weight p) (hz : 1 <= z) :
    weightedMass (highCostSet paths cost Y) weight <=
      weightedMoment paths weight cost z / z ^ Y := by
  have hzpos : 0 < z := by linarith
  have hznonneg : 0 <= z := hzpos.le
  have hpowYpos : 0 < z ^ Y := pow_pos hzpos _
  have hpoint :
      ∀ p ∈ highCostSet paths cost Y,
        weight p <= (weight p * z ^ cost p) / z ^ Y := by
    intro p hp
    have hp' := mem_highCostSet.1 hp
    have hcost : Y <= cost p := hp'.2
    have hw : 0 <= weight p := hweight p hp'.1
    have hpow_le : z ^ Y <= z ^ cost p :=
      pow_le_pow_right₀ hz hcost
    calc
      weight p = weight p * z ^ Y / z ^ Y := by
        field_simp [hpowYpos.ne']
      _ <= weight p * z ^ cost p / z ^ Y := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow_le hw) hpowYpos.le
  calc
    weightedMass (highCostSet paths cost Y) weight
        <= ∑ p ∈ highCostSet paths cost Y, (weight p * z ^ cost p) / z ^ Y := by
          unfold weightedMass
          exact sum_le_sum hpoint
    _ = (∑ p ∈ highCostSet paths cost Y, weight p * z ^ cost p) / z ^ Y := by
          rw [sum_div]
    _ <= (∑ p ∈ paths, weight p * z ^ cost p) / z ^ Y := by
          exact div_le_div_of_nonneg_right
            (sum_le_sum_of_subset_of_nonneg
              (highCostSet_subset paths cost Y)
              (fun p hp_paths _ => by
                exact mul_nonneg (hweight p hp_paths) (pow_nonneg hznonneg _)))
            hpowYpos.le
    _ = weightedMoment paths weight cost z / z ^ Y := by rfl

theorem shellChernoff_bound_of_moment_bound {α : Type*}
    {paths : Finset α} {weight : α -> ℝ} {cost : α -> Nat}
    {Y m : Nat} {z root A : ℝ}
    (hweight : ∀ p ∈ paths, 0 <= weight p) (hz : 1 <= z)
    (hmoment : weightedMoment paths weight cost z <= root * A ^ m) :
    weightedMass (highCostSet paths cost Y) weight <= root * A ^ m / z ^ Y := by
  have hzpos : 0 < z := by linarith
  exact (shellChernoff_bound_of_moment hweight hz).trans
    (div_le_div_of_nonneg_right hmoment (pow_pos hzpos Y).le)

theorem shellChernoff_bound_of_pointwise_tilt
    {α : Type*}
    {paths : Finset α} {weight : α -> ℝ} {cost : α -> Nat}
    {Y : Nat} {z B : ℝ}
    (hweight : ∀ p ∈ paths, 0 <= weight p) (hz : 1 <= z)
    (hpoint : ∀ p ∈ paths, weight p * z ^ cost p <= B) :
    weightedMass (highCostSet paths cost Y) weight <=
      ((paths.card : ℝ) * B) / z ^ Y := by
  have hmoment :
      weightedMoment paths weight cost z <= (paths.card : ℝ) * B :=
    weightedMoment_le_card_mul_of_le hpoint
  exact (shellChernoff_bound_of_moment hweight hz).trans
    (div_le_div_of_nonneg_right hmoment (pow_pos (by linarith) Y).le)

theorem shellChernoff_bound_of_pointwise_weight_and_cost
    {α : Type*}
    {paths : Finset α} {weight : α -> ℝ} {cost : α -> Nat}
    {Y M : Nat} {z B : ℝ}
    (hweight_nonneg : ∀ p ∈ paths, 0 <= weight p)
    (hweight : ∀ p ∈ paths, weight p <= B)
    (hz : 1 <= z) (hB : 0 <= B)
    (hcost : ∀ p ∈ paths, cost p <= M) :
    weightedMass (highCostSet paths cost Y) weight <=
      ((paths.card : ℝ) * (B * z ^ M)) / z ^ Y := by
  have hmoment :
      weightedMoment paths weight cost z <=
        (paths.card : ℝ) * (B * z ^ M) :=
    weightedMoment_le_card_mul_const_of_weight_le hweight hz hB hcost
  exact (shellChernoff_bound_of_moment hweight_nonneg hz).trans
    (div_le_div_of_nonneg_right hmoment (pow_pos (by linarith) Y).le)

/-- Branches with total shell cost at least `Y`. -/
def highBranchCostSet (branches : Finset StoppedBranch) (Y : Nat) :
    Finset StoppedBranch :=
  highCostSet branches branchShellCost Y

/-- Total branch mass. -/
def branchWeightedMass (branches : Finset StoppedBranch)
    (weight : StoppedBranch -> ℝ) : ℝ :=
  weightedMass branches weight

/-- Exponential shell-cost moment for stopped branches. -/
def branchWeightedMoment (branches : Finset StoppedBranch)
    (weight : StoppedBranch -> ℝ) (z : ℝ) : ℝ :=
  weightedMoment branches weight branchShellCost z

theorem branchWeightedMoment_one (branches : Finset StoppedBranch)
    (weight : StoppedBranch -> ℝ) :
    branchWeightedMoment branches weight 1 = branchWeightedMass branches weight := by
  simp [branchWeightedMoment, branchWeightedMass, weightedMoment_one]

theorem branchWeightedMass_le_branchWeightedMoment_of_one_le
    {branches : Finset StoppedBranch} {weight : StoppedBranch -> ℝ} {z : ℝ}
    (hweight : ∀ b ∈ branches, 0 <= weight b) (hz : 1 <= z) :
    branchWeightedMass branches weight <= branchWeightedMoment branches weight z := by
  simpa [branchWeightedMass, branchWeightedMoment] using
    (weightedMass_le_weightedMoment_of_one_le
      (paths := branches) (weight := weight) (cost := branchShellCost)
      (z := z) hweight hz)

theorem branchWeightedMoment_le_mass_mul_pow_of_cost_le
    {branches : Finset StoppedBranch} {weight : StoppedBranch -> ℝ}
    {z : ℝ} {M : Nat}
    (hweight : ∀ b ∈ branches, 0 <= weight b) (hz : 1 <= z)
    (hcost : ∀ b ∈ branches, branchShellCost b <= M) :
    branchWeightedMoment branches weight z <=
      branchWeightedMass branches weight * z ^ M := by
  simpa [branchWeightedMass, branchWeightedMoment] using
    (weightedMoment_le_mass_mul_pow_of_cost_le
      (paths := branches) (weight := weight) (cost := branchShellCost)
      (z := z) (M := M) hweight hz hcost)

theorem branchWeightedMoment_le_card_mul_of_le
    {branches : Finset StoppedBranch} {weight : StoppedBranch -> ℝ}
    {z B : ℝ}
    (hpoint : ∀ b ∈ branches, weight b * z ^ branchShellCost b <= B) :
    branchWeightedMoment branches weight z <= (branches.card : ℝ) * B := by
  simpa [branchWeightedMoment] using
    (weightedMoment_le_card_mul_of_le
      (paths := branches) (weight := weight) (cost := branchShellCost)
      (z := z) (B := B) hpoint)

theorem branchWeightedMoment_le_card_mul_const_of_weight_le
    {branches : Finset StoppedBranch} {weight : StoppedBranch -> ℝ}
    {z B : ℝ} {M : Nat}
    (hweight : ∀ b ∈ branches, weight b <= B)
    (hz : 1 <= z) (hB : 0 <= B)
    (hcost : ∀ b ∈ branches, branchShellCost b <= M) :
    branchWeightedMoment branches weight z <=
      (branches.card : ℝ) * (B * z ^ M) := by
  simpa [branchWeightedMoment] using
    (weightedMoment_le_card_mul_const_of_weight_le
      (paths := branches) (weight := weight) (cost := branchShellCost)
      (z := z) (B := B) (M := M) hweight hz hB hcost)

theorem branchWeightedMass_le_card_mul_of_le
    {branches : Finset StoppedBranch} {weight : StoppedBranch -> ℝ} {B : ℝ}
    (hweight : ∀ b ∈ branches, weight b <= B) :
    branchWeightedMass branches weight <= (branches.card : ℝ) * B := by
  simpa [branchWeightedMass] using
    (weightedMass_le_card_mul_of_le
      (paths := branches) (weight := weight) (B := B) hweight)

theorem mem_highBranchCostSet {branches : Finset StoppedBranch} {Y : Nat}
    {b : StoppedBranch} :
    b ∈ highBranchCostSet branches Y ↔ b ∈ branches ∧ Y <= branchShellCost b := by
  simp [highBranchCostSet, mem_highCostSet]

theorem highBranchCostSet_subset (branches : Finset StoppedBranch) (Y : Nat) :
    highBranchCostSet branches Y ⊆ branches :=
  highCostSet_subset branches branchShellCost Y

theorem highBranchCostSet_card_le (branches : Finset StoppedBranch) (Y : Nat) :
    (highBranchCostSet branches Y).card <= branches.card :=
  highCostSet_card_le branches branchShellCost Y

theorem highBranchCostSet_mono_threshold {branches : Finset StoppedBranch}
    {Y₁ Y₂ : Nat} (hY : Y₁ <= Y₂) :
    highBranchCostSet branches Y₂ ⊆ highBranchCostSet branches Y₁ :=
  highCostSet_mono_threshold hY

theorem highBranchCostSet_mono_subset {s t : Finset StoppedBranch}
    {Y : Nat} (hst : s ⊆ t) :
    highBranchCostSet s Y ⊆ highBranchCostSet t Y :=
  highCostSet_mono_subset hst

theorem highBranchCostSet_eq_empty_of_forall_lt
    {branches : Finset StoppedBranch} {Y : Nat}
    (hcost : ∀ b ∈ branches, branchShellCost b < Y) :
    highBranchCostSet branches Y = ∅ :=
  highCostSet_eq_empty_of_forall_lt hcost

theorem highBranchCostSet_eq_self_of_forall_ge
    {branches : Finset StoppedBranch} {Y : Nat}
    (hcost : ∀ b ∈ branches, Y <= branchShellCost b) :
    highBranchCostSet branches Y = branches :=
  highCostSet_eq_self_of_forall_ge hcost

theorem branchWeightedMass_mono_subset {s t : Finset StoppedBranch}
    {weight : StoppedBranch -> ℝ} (hst : s ⊆ t)
    (hweight : ∀ b ∈ t, 0 <= weight b) :
    branchWeightedMass s weight <= branchWeightedMass t weight := by
  simpa [branchWeightedMass] using
    (weightedMass_mono_subset (s := s) (t := t) (weight := weight)
      hst hweight)

theorem branchWeightedMass_highBranchCostSet_le
    {branches : Finset StoppedBranch} {Y : Nat}
    {weight : StoppedBranch -> ℝ}
    (hweight : ∀ b ∈ branches, 0 <= weight b) :
    branchWeightedMass (highBranchCostSet branches Y) weight <=
      branchWeightedMass branches weight := by
  simpa [branchWeightedMass, highBranchCostSet] using
    (weightedMass_highCostSet_le
      (paths := branches) (cost := branchShellCost) (Y := Y)
      (weight := weight) hweight)

theorem branchWeightedMoment_highBranchCostSet_le
    {branches : Finset StoppedBranch} {Y : Nat}
    {weight : StoppedBranch -> ℝ} {z : ℝ}
    (hweight : ∀ b ∈ branches, 0 <= weight b) (hz : 0 <= z) :
    branchWeightedMoment (highBranchCostSet branches Y) weight z <=
      branchWeightedMoment branches weight z := by
  simpa [branchWeightedMoment, highBranchCostSet] using
    (weightedMoment_highCostSet_le
      (paths := branches) (cost := branchShellCost) (Y := Y)
      (weight := weight) (z := z) hweight hz)

theorem branchShellChernoff_bound_of_moment
    {branches : Finset StoppedBranch} {weight : StoppedBranch -> ℝ}
    {Y : Nat} {z : ℝ}
    (hweight : ∀ b ∈ branches, 0 <= weight b) (hz : 1 <= z) :
    branchWeightedMass (highBranchCostSet branches Y) weight <=
      branchWeightedMoment branches weight z / z ^ Y := by
  simpa [branchWeightedMass, branchWeightedMoment, highBranchCostSet]
    using
      (shellChernoff_bound_of_moment
        (paths := branches) (weight := weight) (cost := branchShellCost)
        (Y := Y) (z := z) hweight hz)

theorem branchShellChernoff_bound_of_moment_bound
    {branches : Finset StoppedBranch} {weight : StoppedBranch -> ℝ}
    {Y m : Nat} {z root A : ℝ}
    (hweight : ∀ b ∈ branches, 0 <= weight b) (hz : 1 <= z)
    (hmoment : branchWeightedMoment branches weight z <= root * A ^ m) :
    branchWeightedMass (highBranchCostSet branches Y) weight <=
      root * A ^ m / z ^ Y := by
  simpa [branchWeightedMass, branchWeightedMoment, highBranchCostSet]
    using
      (shellChernoff_bound_of_moment_bound
        (paths := branches) (weight := weight) (cost := branchShellCost)
        (Y := Y) (m := m) (z := z) (root := root) (A := A)
        hweight hz hmoment)

theorem branchShellChernoff_bound_of_pointwise_tilt
    {branches : Finset StoppedBranch} {weight : StoppedBranch -> ℝ}
    {Y : Nat} {z B : ℝ}
    (hweight : ∀ b ∈ branches, 0 <= weight b) (hz : 1 <= z)
    (hpoint : ∀ b ∈ branches, weight b * z ^ branchShellCost b <= B) :
    branchWeightedMass (highBranchCostSet branches Y) weight <=
      ((branches.card : ℝ) * B) / z ^ Y := by
  simpa [branchWeightedMass, highBranchCostSet] using
    (shellChernoff_bound_of_pointwise_tilt
      (paths := branches) (weight := weight) (cost := branchShellCost)
      (Y := Y) (z := z) (B := B) hweight hz hpoint)

theorem branchShellChernoff_bound_of_pointwise_weight_and_cost
    {branches : Finset StoppedBranch} {weight : StoppedBranch -> ℝ}
    {Y M : Nat} {z B : ℝ}
    (hweight_nonneg : ∀ b ∈ branches, 0 <= weight b)
    (hweight : ∀ b ∈ branches, weight b <= B)
    (hz : 1 <= z) (hB : 0 <= B)
    (hcost : ∀ b ∈ branches, branchShellCost b <= M) :
    branchWeightedMass (highBranchCostSet branches Y) weight <=
      ((branches.card : ℝ) * (B * z ^ M)) / z ^ Y := by
  simpa [branchWeightedMass, highBranchCostSet] using
    (shellChernoff_bound_of_pointwise_weight_and_cost
      (paths := branches) (weight := weight) (cost := branchShellCost)
      (Y := Y) (M := M) (z := z) (B := B)
      hweight_nonneg hweight hz hB hcost)

/--
Finite stopped-recurrence skeleton with a CNL input and a package ledger input.
This is the algebraic combination used before the proof_v2-specific local
estimates are substituted: high shell cost is paid by Chernoff, clean CNL mass is
an explicit term, and non-CNL package output cost is another explicit term.
-/
theorem stoppedRecurrence_with_CNL_input
    {branches : Finset StoppedBranch}
    {branchWeight : StoppedBranch -> ℝ}
    {packageOutputs : Finset OutputObject}
    {packageCostFn : OutputObject -> ℝ}
    {Y m : Nat} {z root A cnlMass packageMass : ℝ}
    (hbranch_nonneg : ∀ b ∈ branches, 0 <= branchWeight b)
    (hz : 1 <= z)
    (hmoment :
      branchWeightedMoment branches branchWeight z <= root * A ^ m)
    (hpackage :
      packageCost packageOutputs packageCostFn <= packageMass)
    (hdecomp :
      branchWeightedMass branches branchWeight <=
        branchWeightedMass (highBranchCostSet branches Y) branchWeight +
          cnlMass + packageCost packageOutputs packageCostFn) :
    branchWeightedMass branches branchWeight <=
      root * A ^ m / z ^ Y + cnlMass + packageMass := by
  have hcher :=
    branchShellChernoff_bound_of_moment_bound
      (branches := branches) (weight := branchWeight)
      (Y := Y) (m := m) (z := z) (root := root) (A := A)
      hbranch_nonneg hz hmoment
  calc
    branchWeightedMass branches branchWeight
        <= branchWeightedMass (highBranchCostSet branches Y) branchWeight +
            cnlMass + packageCost packageOutputs packageCostFn := hdecomp
    _ <= root * A ^ m / z ^ Y + cnlMass +
          packageCost packageOutputs packageCostFn := by
          linarith
    _ <= root * A ^ m / z ^ Y + cnlMass + packageMass := by
          linarith

/--
Stopped-recurrence skeleton after substituting the charged ledger's uniform
package estimate for the package term.
-/
theorem stoppedRecurrence_with_chargedLedger
    {branches : Finset StoppedBranch} {Φ : PriorityMap}
    {branchWeight : StoppedBranch -> ℝ}
    {packageCostFn packageWeight : OutputObject -> ℝ}
    {Cmax : ℝ} {C : PackageKind -> ℝ}
    {Y m : Nat} {z root A cnlMass : ℝ}
    (hbranch_nonneg : ∀ b ∈ branches, 0 <= branchWeight b)
    (hz : 1 <= z)
    (hmoment :
      branchWeightedMoment branches branchWeight z <= root * A ^ m)
    (hC : ∀ kind : PackageKind, C kind <= Cmax)
    (hpackageWeight :
      ∀ o ∈ branchOutputs branches Φ, 0 <= packageWeight o)
    (hpackagePoint :
      ∀ kind o, o ∈ branchOutputsOf branches Φ kind ->
        packageCostFn o <= C kind * packageWeight o)
    (hdecomp :
      branchWeightedMass branches branchWeight <=
        branchWeightedMass (highBranchCostSet branches Y) branchWeight +
          cnlMass + packageCost (branchOutputs branches Φ) packageCostFn) :
    branchWeightedMass branches branchWeight <=
      root * A ^ m / z ^ Y + cnlMass +
        Cmax * chargedMass (branchOutputs branches Φ) packageWeight := by
  exact stoppedRecurrence_with_CNL_input
    (branches := branches) (branchWeight := branchWeight)
    (packageOutputs := branchOutputs branches Φ)
    (packageCostFn := packageCostFn)
    (Y := Y) (m := m) (z := z) (root := root) (A := A)
    (cnlMass := cnlMass)
    (packageMass := Cmax * chargedMass (branchOutputs branches Φ) packageWeight)
    hbranch_nonneg hz hmoment
    (packageCost_branchOutputs_le_uniform_const_mul_chargedMass
      hC hpackageWeight hpackagePoint)
    hdecomp

/--
Stopped recurrence after applying the charged ledger closure: this packages the
mass recurrence and the strict-threshold feedback conclusion together in the
shape used by Appendix H/I.
-/
theorem stoppedRecurrence_with_chargedLedgerClosure
    {branches : Finset StoppedBranch} {Φ : PriorityMap}
    {branchWeight : StoppedBranch -> ℝ}
    {packageCostFn packageWeight : OutputObject -> ℝ}
    {Cmax : ℝ} {C : PackageKind -> ℝ}
    {j Y m : Nat} {z root A cnlMass : ℝ}
    (hbranch_nonneg : ∀ b ∈ branches, 0 <= branchWeight b)
    (hz : 1 <= z)
    (hmoment :
      branchWeightedMoment branches branchWeight z <= root * A ^ m)
    (hC : ∀ kind : PackageKind, C kind <= Cmax)
    (hpackageWeight :
      ∀ o ∈ branchOutputs branches Φ, 0 <= packageWeight o)
    (hpackagePoint :
      ∀ kind o, o ∈ branchOutputsOf branches Φ kind ->
        packageCostFn o <= C kind * packageWeight o)
    (hfree : BranchOutputsFeedbackFree branches Φ j)
    (hdecomp :
      branchWeightedMass branches branchWeight <=
        branchWeightedMass (highBranchCostSet branches Y) branchWeight +
          cnlMass + packageCost (branchOutputs branches Φ) packageCostFn) :
    branchWeightedMass branches branchWeight <=
        root * A ^ m / z ^ Y + cnlMass +
          Cmax * chargedMass (branchOutputs branches Φ) packageWeight ∧
      ∀ {kind : PackageKind} {o : OutputObject},
        IsFeedbackPackage kind ->
        o ∈ branchOutputsOf branches Φ kind ->
          j < o.thresholdLayer := by
  have hledger :=
    chargedLedgerClosure_skeleton
      (branches := branches) (Φ := Φ)
      (cost := packageCostFn) (weight := packageWeight)
      (Cmax := Cmax) (C := C) (j := j)
      hC hpackageWeight hpackagePoint hfree
  constructor
  · exact stoppedRecurrence_with_CNL_input
      (branches := branches) (branchWeight := branchWeight)
      (packageOutputs := branchOutputs branches Φ)
      (packageCostFn := packageCostFn)
      (Y := Y) (m := m) (z := z) (root := root) (A := A)
      (cnlMass := cnlMass)
      (packageMass :=
        Cmax * chargedMass (branchOutputs branches Φ) packageWeight)
      hbranch_nonneg hz hmoment hledger.1 hdecomp
  · exact hledger.2

/-- Abstract principal child data for the shell-Carleson step. -/
structure PrincipalChild where
  shell : Nat
  weight : ℝ
  nonneg : 0 <= weight

/-- Sum of principal child weights. -/
def principalWeight (children : Finset PrincipalChild) : ℝ :=
  ∑ v ∈ children, v.weight

/-- Sum of principal shell charges. -/
def principalShellCharge (children : Finset PrincipalChild) : ℝ :=
  ∑ v ∈ children, (2 : ℝ) ^ (-(v.shell : Int))

theorem principalWeight_nonneg (children : Finset PrincipalChild) :
    0 <= principalWeight children := by
  unfold principalWeight
  exact sum_nonneg fun v _ => v.nonneg

theorem principalShellCharge_nonneg (children : Finset PrincipalChild) :
    0 <= principalShellCharge children := by
  unfold principalShellCharge
  exact sum_nonneg fun v _ => by positivity

theorem principalShellCarleson
    {children : Finset PrincipalChild} {parent K : ℝ}
    (hparent : 0 < parent) (hK : 0 < K)
    (hdisjoint : principalWeight children <= parent)
    (hprincipal :
      ∀ v ∈ children, K * parent * (2 : ℝ) ^ (-(v.shell : Int)) <= v.weight) :
    principalShellCharge children <= K⁻¹ := by
  have hmain :
      K * parent * principalShellCharge children <= principalWeight children := by
    unfold principalShellCharge principalWeight
    rw [mul_sum]
    exact sum_le_sum fun v hv => hprincipal v hv
  have hbound : K * parent * principalShellCharge children <= parent :=
    hmain.trans hdisjoint
  have hfactor_pos : 0 < K * parent := mul_pos hK hparent
  calc
    principalShellCharge children <= parent / (K * parent) := by
      exact (le_div_iff₀ hfactor_pos).2 (by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hbound)
    _ = K⁻¹ := by
      field_simp [hK.ne', hparent.ne']

/-! ### Manuscript-named theorems for Section 22 -/

/--
**Lemma 22.1 (bundled shell-Chernoff path bound, manuscript form).**

For a finite path space `paths` with weighted mass and shell cost
satisfying the moment hypothesis `hmoment`, the weighted mass of paths
with shell cost at least `Y` is bounded by `root * A^m / z^Y`.  In the
manuscript this is the explicit Chernoff bound used for regular
branches in the stopped recurrence.

This is just a renaming of `shellChernoff_bound_of_moment_bound` for
naming consistency with `proofV2OpenTheoremNames`.
-/
theorem lemma22_1_shellChernoff {α : Type*} [DecidableEq α]
    {paths : Finset α} {weight : α -> ℝ} {cost : α -> Nat}
    {Y m : Nat} {z root A : ℝ}
    (hweight : ∀ p ∈ paths, 0 <= weight p) (hz : 1 <= z)
    (hmoment : weightedMoment paths weight cost z <= root * A ^ m) :
    weightedMass (highCostSet paths cost Y) weight <=
      root * A ^ m / z ^ Y :=
  shellChernoff_bound_of_moment_bound hweight hz hmoment

/--
**Lemma 22.2 (principal shell-Carleson bound, manuscript form).**

Disjoint principal weights give a Carleson-type bound
`∑ 2^{-shell(v)} ≤ K^{-1}`.

This is the same statement as `principalShellCarleson`, renamed for
manuscript consistency.
-/
theorem lemma22_2_principalShellCarleson
    {children : Finset PrincipalChild} {parent K : ℝ}
    (hparent : 0 < parent) (hK : 0 < K)
    (hdisjoint : principalWeight children <= parent)
    (hprincipal :
      ∀ v ∈ children, K * parent * (2 : ℝ) ^ (-(v.shell : Int)) <= v.weight) :
    principalShellCharge children <= K⁻¹ :=
  principalShellCarleson hparent hK hdisjoint hprincipal

/--
**Proposition 22.3 (positive-density high-excess recurrence, manuscript
form).**

The high-excess mass `𝒜_{s,j}(Y)` is bounded by
`C_η · 𝒜_{s-m,j}^*((1-η)Y) + X|I_j|·2^{-cY} + 𝒫_{s,j} + DensePack_{s,j} +
o(sX|I_j|)`.

Pass 2 form: the five summand bounds (Chernoff regular term, CNL
clean term, package term, DensePack term, small-error term) are each
real input hypotheses.  The conclusion is a **real linear combination**
of the five inputs via `linarith`.

* `hChernoff`: regular branch mass `≤ C_η · 𝒜_{s-m,j}^*((1-η)Y)` from
  Lemma 22.1 path-space Chernoff.
* `hCNL`: clean CNL term `≤ X · I_j · 2^{-cY}` from Theorem G.6 entropy
  estimate.
* `hPackage`: package mass `≤ 𝒫_{s,j}` (just a name change).
* `hDensePack`: dense-pack term `≤ D` (just a name change).
* `hSmall`: residual small-error `≤ smallError` (just a name change).
* `hDecomp`: the decomposition `𝒜 ≤ Regular + CleanTerm + Package +
  DensePack + Small` from the stopped-induction split.
-/
theorem proposition22_3_highExcessRecurrence
    {𝒜 Regular CleanTerm PackageMass DensePackMass SmallTerm : ℝ}
    {𝒜prime X Ij P D smallError : ℝ}
    {Cη twoNegcY : ℝ}
    (hDecomp :
      𝒜 <= Regular + CleanTerm + PackageMass + DensePackMass + SmallTerm)
    (hChernoff : Regular <= Cη * 𝒜prime)
    (hCNL : CleanTerm <= X * Ij * twoNegcY)
    (hPackage : PackageMass <= P)
    (hDensePack : DensePackMass <= D)
    (hSmall : SmallTerm <= smallError) :
    𝒜 <= Cη * 𝒜prime + X * Ij * twoNegcY + P + D + smallError := by
  linarith

end

end Erdos260
