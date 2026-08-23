import Erdos260.PolynomialWindow.Carry
import Erdos260.Pressure
import Erdos260.AffineLocking

/-!
# Polynomial-scale support windows

This module separates the exact combinatorics of moving windows from the
asymptotic choice of their scale.  In particular, the mass identity and its
endpoint losses are proved for an arbitrary increasing support enumeration.
-/

noncomputable section

open Filter Set
open scoped BigOperators

namespace Erdos260.PolynomialWindow

/-- Finite census of positive gap words with bounded span and length. -/
def boundedPositiveGapWords (H rMax : ℕ) : Finset Erdos260.GapWord :=
  (Erdos260.positiveGapWords_bounded_finite H rMax).toFinset

@[simp]
theorem mem_boundedPositiveGapWords_iff {H rMax : ℕ}
    {w : Erdos260.GapWord} :
    w ∈ boundedPositiveGapWords H rMax ↔
      Erdos260.GapWord.Positive w ∧
        Erdos260.GapWord.span w ≤ H ∧ w.length ≤ rMax := by
  simp [boundedPositiveGapWords, Erdos260.GapWord.Positive]

/-- Exact positive-word census used by `lem:windows`. -/
theorem boundedPositiveGapWords_card_le (H rMax : ℕ) :
    (boundedPositiveGapWords H rMax).card ≤
      ∑ r ∈ Finset.Icc 0 rMax, H.choose r := by
  apply Erdos260.positiveGapWords_card_le_compositions
  · intro p hp g hg
    exact (mem_boundedPositiveGapWords_iff.mp hp).1 g hg
  · intro p hp
    exact (mem_boundedPositiveGapWords_iff.mp hp).2.1
  · intro p hp
    exact (mem_boundedPositiveGapWords_iff.mp hp).2.2

/-- Entropy form of the positive-word census.  It is deliberately stated with
an explicit density parameter so later uniform estimates can choose that
parameter before the window. -/
theorem boundedPositiveGapWords_entropy (H rMax : ℕ)
    (α : ℝ) (hHtwo : 2 ≤ H + 1) (hα0 : 0 < α)
    (hαhalf : α ≤ 1 / 2)
    (hratio : ((rMax + 1 : ℕ) : ℝ) ≤ α * (H + 1 : ℕ)) :
    ((boundedPositiveGapWords H rMax).card : ℝ) ≤
      ((H + 1 : ℕ) : ℝ) ^ 2 *
        Real.rpow 2
          (((H + 1 : ℕ) : ℝ) * Erdos260.binaryEntropy α) := by
  have hcomp := Erdos260.lem_composition_entropy
    (H + 1) (rMax + 1) α hHtwo hα0 hαhalf hratio
  have hcardNat := boundedPositiveGapWords_card_le H rMax
  have hcardReal :
      ((boundedPositiveGapWords H rMax).card : ℝ) ≤
        ((∑ r ∈ Finset.Icc 0 rMax, H.choose r : ℕ) : ℝ) := by
    exact_mod_cast hcardNat
  calc
    ((boundedPositiveGapWords H rMax).card : ℝ) ≤
        ((∑ r ∈ Finset.Icc 0 rMax, H.choose r : ℕ) : ℝ) := hcardReal
    _ = ((∑ q ∈ Finset.Icc 1 (rMax + 1),
          H.choose (q - 1) : ℕ) : ℝ) := by
      rw [Erdos260.sum_choose_Icc_zero_eq_shift]
    _ ≤ ((H + 1 : ℕ) : ℝ) ^ 2 *
        Real.rpow 2
          (((H + 1 : ℕ) : ℝ) * Erdos260.binaryEntropy α) := hcomp

/-- Formula label `eq:prefixcount` in its finite, fully quantitative form. -/
theorem eq_prefixcount_entropy (H rMax : ℕ)
    (α : ℝ) (hHtwo : 2 ≤ H + 1) (hα0 : 0 < α)
    (hαhalf : α ≤ 1 / 2)
    (hratio : ((rMax + 1 : ℕ) : ℝ) ≤ α * (H + 1 : ℕ)) :
    ((boundedPositiveGapWords H rMax).card : ℝ) ≤
      ((H + 1 : ℕ) : ℝ) ^ 2 *
        Real.rpow 2
          (((H + 1 : ℕ) : ℝ) * Erdos260.binaryEntropy α) :=
  boundedPositiveGapWords_entropy H rMax α hHtwo hα0 hαhalf hratio

namespace CarrySeries

/-- Canonical increasing enumeration after removing the irrelevant zero
index. -/
def positiveEnumeration (D : CarrySeries) :
    Erdos260.SupportEnumeration (Erdos260.positiveSupport D.support) :=
  Erdos260.supportEnumerationOfInfinite
    (Erdos260.positiveSupport D.support)
    (Erdos260.positiveSupport_infinite D.support_infinite)
    (by intro n hn; exact hn.2)

@[simp]
theorem positiveEnumeration_range (D : CarrySeries) :
    Set.range D.positiveEnumeration.a = Erdos260.positiveSupport D.support :=
  D.positiveEnumeration.range_eq

/-- Consecutive points of the canonical positive enumeration form a carry
gap for the original support. -/
theorem positiveEnumeration_gap_isSupportGap (D : CarrySeries) (k : ℕ) :
    D.IsSupportGap (D.positiveEnumeration.a k)
      (Erdos260.supportGap D.positiveEnumeration k) := by
  let e := D.positiveEnumeration
  have hgap := Erdos260.supportGap_isSupportGap e k
  refine ⟨hgap.1, ?_, ?_, ?_⟩
  · exact hgap.2.1.1
  · exact hgap.2.2.1.1
  · intro n hleft hright hn
    apply hgap.2.2.2 n hleft hright
    refine ⟨hn, ?_⟩
    have hpos : 0 < e.a k := e.positive k
    omega

end CarrySeries

section EnumerationWindows

variable {S : Set ℕ} (e : Erdos260.SupportEnumeration S)

/-- First support index strictly after the left endpoint. -/
def firstWindowIndex (N : ℕ) : ℕ := Erdos260.firstIndexAbove e N

/-- First support index strictly after the right endpoint. -/
def afterWindowIndex (N W : ℕ) : ℕ :=
  Erdos260.firstIndexAbove e (N + W)

/-- Indices of support points in `(N,N+W]`. -/
def windowIndices (N W : ℕ) : Finset ℕ :=
  Finset.Ico (firstWindowIndex e N) (afterWindowIndex e N W)

/-- Number of enumerated support points in `(N,N+W]`. -/
def enumeratedWindowCount (N W : ℕ) : ℕ :=
  afterWindowIndex e N W - firstWindowIndex e N

/-- The actual support points in `(N,N+W]`, packaged once so that classical
decidability does not leak into theorem signatures. -/
def supportWindowFinset (N W : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc N (N + W)).filter fun n => n ∈ S

theorem firstWindowIndex_le_afterWindowIndex (N W : ℕ) :
    firstWindowIndex e N ≤ afterWindowIndex e N W := by
  by_contra hnot
  have hlt : afterWindowIndex e N W < firstWindowIndex e N :=
    Nat.lt_of_not_ge hnot
  dsimp [firstWindowIndex, afterWindowIndex] at hlt ⊢
  have hminimal := Erdos260.firstIndexAbove_minimal e N
    (Erdos260.firstIndexAbove e (N + W)) hlt
  have hspec := Erdos260.firstIndexAbove_spec e (N + W)
  omega

theorem card_windowIndices (N W : ℕ) :
    (windowIndices e N W).card = enumeratedWindowCount e N W := by
  simp [windowIndices, enumeratedWindowCount]

theorem image_windowIndices_eq (N W : ℕ) :
    (windowIndices e N W).image e.a =
      supportWindowFinset (S := S) N W := by
  classical
  ext n
  simp only [Finset.mem_image, supportWindowFinset,
    Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk' := Finset.mem_Ico.mp hk
    have hlower : N < e.a k :=
      (Erdos260.firstIndexAbove_spec e N).trans_le
        (e.strictMono.monotone hk'.1)
    have hupper : e.a k ≤ N + W :=
      Erdos260.firstIndexAbove_minimal e (N + W) k hk'.2
    have hmem : e.a k ∈ S := by
      exact (Set.ext_iff.mp e.range_eq (e.a k)).mp ⟨k, rfl⟩
    exact ⟨⟨hlower, hupper⟩, hmem⟩
  · rintro ⟨⟨hlower, hupper⟩, hnS⟩
    have hnRange : n ∈ Set.range e.a := by
      exact (Set.ext_iff.mp e.range_eq n).mpr hnS
    obtain ⟨k, rfl⟩ := hnRange
    have hik : firstWindowIndex e N ≤ k := by
      by_contra hnot
      have hklt : k < firstWindowIndex e N := Nat.lt_of_not_ge hnot
      exact (not_lt_of_ge
        (Erdos260.firstIndexAbove_minimal e N k hklt)) hlower
    have hkj : k < afterWindowIndex e N W := by
      by_contra hnot
      have hjk : afterWindowIndex e N W ≤ k := Nat.le_of_not_gt hnot
      dsimp [afterWindowIndex] at hjk
      have hspec := Erdos260.firstIndexAbove_spec e (N + W)
      have hmono := e.strictMono.monotone hjk
      omega
    exact ⟨k, Finset.mem_Ico.mpr ⟨hik, hkj⟩, rfl⟩

theorem enumeratedWindowCount_eq_finset (N W : ℕ) :
    enumeratedWindowCount e N W =
      (supportWindowFinset (S := S) N W).card := by
  rw [← image_windowIndices_eq e N W,
    Finset.card_image_of_injective _ e.strictMono.injective,
    card_windowIndices]

theorem supportWindowFinset_card_eq_windowCount (N W : ℕ) :
    (supportWindowFinset (S := S) N W).card = windowCount S N W := by
  rfl

theorem enumeratedWindowCount_eq_windowCount (N W : ℕ) :
    enumeratedWindowCount e N W = windowCount S N W := by
  rw [enumeratedWindowCount_eq_finset,
    supportWindowFinset_card_eq_windowCount]

/-- Forward span of the next `m` support gaps. -/
def forwardSpan (k m : ℕ) : ℕ := e.a (k + m) - e.a k

/-- Sum of all forward spans based at support points of `(N,N+W]`. -/
def forwardSpanMass (N W m : ℕ) : ℕ :=
  ∑ k ∈ windowIndices e N W, forwardSpan e k m

theorem forwardSpan_zero (k : ℕ) : forwardSpan e k 0 = 0 := by
  simp [forwardSpan]

theorem forwardSpan_succ (k m : ℕ) :
    forwardSpan e k (m + 1) =
      forwardSpan e k m + Erdos260.supportGap e (k + m) := by
  have hk : e.a k ≤ e.a (k + m) :=
    e.strictMono.monotone (Nat.le_add_right k m)
  have hstep : e.a (k + m) ≤ e.a (k + (m + 1)) := by
    apply e.strictMono.monotone
    omega
  simp only [forwardSpan, Erdos260.supportGap]
  have hindex : k + m + 1 = k + (m + 1) := by omega
  rw [hindex]
  omega

theorem forwardSpan_eq_sum_gaps (k m : ℕ) :
    forwardSpan e k m =
      ∑ r ∈ Finset.range m, Erdos260.supportGap e (k + r) := by
  induction m with
  | zero => simp [forwardSpan]
  | succ m ih =>
      rw [show m + 1 = m + 1 by rfl, forwardSpan_succ, ih,
        Finset.sum_range_succ]

theorem sum_shifted_gaps (i j m : ℕ) (hij : i ≤ j) :
    (∑ k ∈ Finset.Ico i j, Erdos260.supportGap e (k + m)) =
      e.a (j + m) - e.a (i + m) := by
  rw [Finset.sum_Ico_add' (fun k => Erdos260.supportGap e k) i j m]
  exact Erdos260.sum_supportGap_Ico e (i + m) (j + m) (Nat.add_le_add_right hij m)

/-- Exact double-counting identity behind the window-mass estimate. -/
theorem sum_forwardSpan_Ico (i j m : ℕ) (hij : i ≤ j) :
    (∑ k ∈ Finset.Ico i j, forwardSpan e k m) =
      ∑ r ∈ Finset.range m, (e.a (j + r) - e.a (i + r)) := by
  induction m with
  | zero => simp [forwardSpan]
  | succ m ih =>
      simp_rw [forwardSpan_succ e]
      rw [Finset.sum_add_distrib, ih, Finset.sum_range_succ]
      congr 1
      exact sum_shifted_gaps e i j m hij

/-- Data certifying that all gaps touched by a family of forward windows are
bounded by `G`, including the single gap crossing the left endpoint. -/
structure WindowGeometry (N W m G : ℕ) : Prop where
  first_le : e.a (firstWindowIndex e N) ≤ N + G
  gaps_le : ∀ q ∈ Finset.Ico (firstWindowIndex e N)
      (afterWindowIndex e N W + m), Erdos260.supportGap e q ≤ G

theorem WindowGeometry.forwardSpan_le {N W m G : ℕ}
    (h : WindowGeometry e N W m G) {k : ℕ}
    (hk : k ∈ windowIndices e N W) :
    forwardSpan e k m ≤ m * G := by
  have hk' := Finset.mem_Ico.mp hk
  have hiJ := firstWindowIndex_le_afterWindowIndex e N W
  unfold forwardSpan
  have hbound := Erdos260.sum_supportGap_le_mul e k (k + m) G (by omega)
    (fun q hq => by
      apply h.gaps_le q
      apply Finset.mem_Ico.mpr
      have hq' := Finset.mem_Ico.mp hq
      constructor
      · exact hk'.1.trans hq'.1
      · omega)
  simpa using hbound

theorem WindowGeometry.forwardSpan_le_of_le {N W m G : ℕ}
    (h : WindowGeometry e N W m G) {k r : ℕ}
    (hk : k ∈ windowIndices e N W) (hr : r ≤ m) :
    forwardSpan e k r ≤ r * G := by
  have hk' := Finset.mem_Ico.mp hk
  unfold forwardSpan
  have hbound := Erdos260.sum_supportGap_le_mul e k (k + r) G (by omega)
    (fun q hq => by
      apply h.gaps_le q
      have hq' := Finset.mem_Ico.mp hq
      apply Finset.mem_Ico.mpr
      constructor
      · exact hk'.1.trans hq'.1
      · omega)
  simpa using hbound

theorem WindowGeometry.first_shift_le {N W m G : ℕ}
    (h : WindowGeometry e N W m G) {r : ℕ} (hr : r < m) :
    e.a (firstWindowIndex e N + r) ≤ N + m * G := by
  let i := firstWindowIndex e N
  let j := afterWindowIndex e N W
  have hij : i ≤ j := firstWindowIndex_le_afterWindowIndex e N W
  have hspan : e.a (i + r) - e.a i ≤ r * G := by
    have hbound := Erdos260.sum_supportGap_le_mul e i (i + r) G (by omega)
      (fun q hq => by
        apply h.gaps_le q
        have hq' := Finset.mem_Ico.mp hq
        apply Finset.mem_Ico.mpr
        constructor
        · simpa only [i] using hq'.1
        · dsimp [i, j] at hij ⊢
          omega)
    simpa using hbound
  have hmono : e.a i ≤ e.a (i + r) :=
    e.strictMono.monotone (Nat.le_add_right i r)
  have hfirst : e.a i ≤ N + G := by
    simpa only [i] using h.first_le
  have hrG : G + r * G ≤ m * G := by
    calc
      G + r * G = (r + 1) * G := by ring
      _ ≤ m * G := Nat.mul_le_mul_right G (Nat.succ_le_of_lt hr)
  dsimp [i] at hspan hmono hfirst ⊢
  omega

/-- Exact form of the manuscript's window-mass lower bound.  Dividing by
`mW` gives `1 - O(mG/W)` without using asymptotic notation. -/
theorem WindowGeometry.mass_lower {N W m G : ℕ}
    (h : WindowGeometry e N W m G) :
    m * W ≤ forwardSpanMass e N W m + m * m * G := by
  let i := firstWindowIndex e N
  let j := afterWindowIndex e N W
  have hij : i ≤ j := firstWindowIndex_le_afterWindowIndex e N W
  have hidentity := sum_forwardSpan_Ico e i j m hij
  have hterm (r : ℕ) (hr : r ∈ Finset.range m) :
      W ≤ (e.a (j + r) - e.a (i + r)) + m * G := by
    have hrm : r < m := Finset.mem_range.mp hr
    have hleft : e.a (i + r) ≤ N + m * G := by
      simpa only [i] using WindowGeometry.first_shift_le e h hrm
    have hright0 : N + W < e.a j := by
      dsimp [j, afterWindowIndex]
      exact Erdos260.firstIndexAbove_spec e (N + W)
    have hright : e.a j ≤ e.a (j + r) :=
      e.strictMono.monotone (Nat.le_add_right j r)
    omega
  have hsum :
      ∑ _r ∈ Finset.range m, W ≤
        ∑ r ∈ Finset.range m,
          ((e.a (j + r) - e.a (i + r)) + m * G) := by
    exact Finset.sum_le_sum hterm
  have hleftsum : (∑ _r ∈ Finset.range m, W) = m * W := by simp
  have hrightsum :
      (∑ r ∈ Finset.range m,
          ((e.a (j + r) - e.a (i + r)) + m * G)) =
        (∑ r ∈ Finset.range m, (e.a (j + r) - e.a (i + r))) +
          m * m * G := by
    rw [Finset.sum_add_distrib]
    simp
    ring
  rw [hleftsum, hrightsum] at hsum
  unfold forwardSpanMass windowIndices
  dsimp [i, j] at hidentity
  rw [hidentity]
  exact hsum

/-- The support count cannot be smaller than one point per `G` units, up to
the single gap crossing the left endpoint. -/
theorem WindowGeometry.width_le_count_add_one_mul {N W m G : ℕ}
    (h : WindowGeometry e N W m G) :
    W ≤ (enumeratedWindowCount e N W + 1) * G := by
  let i := firstWindowIndex e N
  let j := afterWindowIndex e N W
  have hij : i ≤ j := firstWindowIndex_le_afterWindowIndex e N W
  have hspan : e.a j - e.a i ≤ (j - i) * G := by
    apply Erdos260.sum_supportGap_le_mul e i j G hij
    intro q hq
    apply h.gaps_le q
    have hq' := Finset.mem_Ico.mp hq
    apply Finset.mem_Ico.mpr
    constructor
    · simpa only [i] using hq'.1
    · change q < afterWindowIndex e N W + m
      exact hq'.2.trans_le (Nat.le_add_right _ _)
  have hmono : e.a i ≤ e.a j := e.strictMono.monotone hij
  have hfirst : e.a i ≤ N + G := by simpa only [i] using h.first_le
  have hafter : N + W < e.a j := by
    dsimp [j, afterWindowIndex]
    exact Erdos260.firstIndexAbove_spec e (N + W)
  have hcount : enumeratedWindowCount e N W = j - i := by
    rfl
  rw [hcount]
  have hW : W < G + (j - i) * G := by omega
  calc
    W ≤ G + (j - i) * G := hW.le
    _ = (j - i + 1) * G := by ring

theorem WindowGeometry.future_point_le {N W m G : ℕ}
    (h : WindowGeometry e N W m G) {k r : ℕ}
    (hk : k ∈ windowIndices e N W) (hr : r ≤ m) :
    e.a (k + r) ≤ N + W + m * G := by
  have hk' := Finset.mem_Ico.mp hk
  have hbase : e.a k ≤ N + W :=
    Erdos260.firstIndexAbove_minimal e (N + W) k hk'.2
  have hspan := WindowGeometry.forwardSpan_le_of_le e h hk hr
  have hmono : e.a k ≤ e.a (k + r) :=
    e.strictMono.monotone (Nat.le_add_right k r)
  unfold forwardSpan at hspan
  have hrG : r * G ≤ m * G := Nat.mul_le_mul_right G hr
  omega

/-- Paper label `lem:windows`, in explicit error-term form. -/
theorem lem_windows {N W m G : ℕ} (h : WindowGeometry e N W m G) :
    m * W ≤ forwardSpanMass e N W m + m * m * G ∧
      ∀ k ∈ windowIndices e N W, forwardSpan e k m ≤ m * G := by
  exact ⟨WindowGeometry.mass_lower e h,
    fun _ hk => WindowGeometry.forwardSpan_le e h hk⟩

/-- Paper label `lem:localscale`, with every asymptotic loss replaced by its
explicit finite counterpart. -/
theorem lem_localscale {N W m G : ℕ} (h : WindowGeometry e N W m G) :
    W ≤ (enumeratedWindowCount e N W + 1) * G ∧
      (∀ k ∈ windowIndices e N W, ∀ r ≤ m,
        e.a (k + r) ≤ N + W + m * G) ∧
      (∀ q ∈ Finset.Ico (firstWindowIndex e N)
        (afterWindowIndex e N W + m), Erdos260.supportGap e q ≤ G) := by
  exact ⟨WindowGeometry.width_le_count_add_one_mul e h,
    fun _ hk _ hr => WindowGeometry.future_point_le e h hk hr,
    h.gaps_le⟩

/-! ## Short windows and locking prefixes -/

/-- Windows whose forward span is at most the manuscript cutoff. -/
def shortWindows {Window : Type*} [DecidableEq Window]
    (windows : Finset Window) (span : Window → ℕ) (C0 L : ℕ) :
    Finset Window :=
  windows.filter fun k => span k ≤ C0 * L

theorem shortWindows_sum_le {Window : Type*} [DecidableEq Window]
    (windows : Finset Window) (span : Window → ℕ) (C0 L : ℕ) :
    ∑ k ∈ shortWindows windows span C0 L, span k ≤
      C0 * L * windows.card := by
  calc
    ∑ k ∈ shortWindows windows span C0 L, span k ≤
        ∑ _k ∈ shortWindows windows span C0 L, C0 * L := by
      gcongr with k hk
      exact (Finset.mem_filter.mp hk).2
    _ = C0 * L * (shortWindows windows span C0 L).card := by
      simp [mul_comm]
    _ ≤ C0 * L * windows.card := by
      apply Nat.mul_le_mul_left
      apply Finset.card_le_card
      intro k hk
      exact (Finset.mem_filter.mp hk).1

/-- Formula label `eq:short`, with all constants and the square-root density
comparison explicit. -/
theorem eq_short {Window : Type*} [DecidableEq Window]
    (windows : Finset Window) (span : Window → ℕ) (C0 L m W : ℕ)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hcard : (windows.card : ℝ) ≤ δ * W)
    (hm : (L : ℝ) * Real.sqrt δ ≤ 2 * m) :
    ((∑ k ∈ shortWindows windows span C0 L, span k : ℕ) : ℝ) ≤
      2 * C0 * Real.sqrt δ * m * W := by
  have hsumNat := shortWindows_sum_le windows span C0 L
  have hsumReal :
      ((∑ k ∈ shortWindows windows span C0 L, span k : ℕ) : ℝ) ≤
        (C0 : ℝ) * L * windows.card := by
    exact_mod_cast hsumNat
  have hsqrt : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg _
  have hsquare : (Real.sqrt δ) ^ 2 = δ := Real.sq_sqrt hδ
  calc
    ((∑ k ∈ shortWindows windows span C0 L, span k : ℕ) : ℝ) ≤
        (C0 : ℝ) * L * windows.card := hsumReal
    _ ≤ (C0 : ℝ) * L * (δ * W) := by
      gcongr
    _ = (C0 : ℝ) * L * ((Real.sqrt δ) ^ 2 * W) := by
      rw [hsquare]
    _ = (C0 : ℝ) * ((L : ℝ) * Real.sqrt δ) *
        Real.sqrt δ * W := by ring
    _ ≤ (C0 : ℝ) * (2 * m) * Real.sqrt δ * W := by
      gcongr
    _ = 2 * C0 * Real.sqrt δ * m * W := by ring

/-- Formula label `eq:prefixspan`: a shortest strictly crossing prefix
overshoots by at most one bounded gap, and a sufficiently long ambient window
retains at least three quarters of its span. -/
theorem eq_prefixspan (word : Erdos260.GapWord) (bound cap V : ℕ)
    (hcross : bound < Erdos260.GapWord.span word)
    (hcap : ∀ g ∈ word, g ≤ cap)
    (hlong : 4 * (bound + cap) ≤ V) :
    bound < Erdos260.GapWord.span (word.firstPrefixAbove bound) ∧
      Erdos260.GapWord.span (word.firstPrefixAbove bound) ≤ bound + cap ∧
      3 * V ≤
        4 * (V - Erdos260.GapWord.span (word.firstPrefixAbove bound)) := by
  have hlower :=
    Erdos260.GapWord.lt_span_firstPrefixAbove_of_lt_span word bound hcross
  have hupper :=
    Erdos260.GapWord.span_firstPrefixAbove_le_add word bound cap hcap
  exact ⟨hlower, hupper, by omega⟩

/-- A finite family of admissible prefixes embeds in the explicit positive
composition census.  This is formula label `eq:prefixcount` before applying
the entropy estimate to the binomial sum. -/
theorem eq_prefixcount (prefixes : Finset Erdos260.GapWord) (H m : ℕ)
    (hadmissible : ∀ p ∈ prefixes,
      Erdos260.GapWord.Positive p ∧
        Erdos260.GapWord.span p ≤ H ∧ p.length ≤ m) :
    prefixes.card ≤ ∑ r ∈ Finset.Icc 0 m, H.choose r := by
  have hsubset : prefixes ⊆ boundedPositiveGapWords H m := by
    intro p hp
    exact mem_boundedPositiveGapWords_iff.mpr (hadmissible p hp)
  exact (Finset.card_le_card hsubset).trans
    (boundedPositiveGapWords_card_le H m)

/-! ## Rare-prefix fibres -/

/-- Windows whose canonical prefix belongs to a chosen rare-prefix family. -/
def rarePrefixWindows {Window Prefix : Type*}
    [DecidableEq Window] [DecidableEq Prefix]
    (windows : Finset Window) (prefixOf : Window → Prefix)
    (rarePrefixes : Finset Prefix) : Finset Window :=
  windows.filter fun k => prefixOf k ∈ rarePrefixes

theorem rarePrefixWindows_card_le {Window Prefix : Type*}
    [DecidableEq Window] [DecidableEq Prefix]
    (windows : Finset Window) (prefixOf : Window → Prefix)
    (rarePrefixes : Finset Prefix) (d : ℕ)
    (hrare : ∀ p ∈ rarePrefixes,
      (windows.filter fun k => prefixOf k = p).card ≤ d + 1) :
    (rarePrefixWindows windows prefixOf rarePrefixes).card ≤
      rarePrefixes.card * (d + 1) := by
  let rare := rarePrefixWindows windows prefixOf rarePrefixes
  have hprefix (k : Window) (hk : k ∈ rare) : prefixOf k ∈ rarePrefixes := by
    exact (Finset.mem_filter.mp hk).2
  have hpartition :
      rare.card =
        ∑ p ∈ rarePrefixes, (rare.filter fun k => prefixOf k = p).card := by
    exact Finset.card_eq_sum_card_fiberwise hprefix
  rw [hpartition]
  calc
    ∑ p ∈ rarePrefixes, (rare.filter fun k => prefixOf k = p).card ≤
        ∑ _p ∈ rarePrefixes, (d + 1) := by
      apply Finset.sum_le_sum
      intro p hp
      apply (Finset.card_le_card ?_).trans (hrare p hp)
      intro k hk
      have hk' := Finset.mem_filter.mp hk
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hk'.1).1, hk'.2⟩
    _ = rarePrefixes.card * (d + 1) := by
      simp

/-- Formula label `eq:rare`: fibre rarity plus a uniform per-window span
bound gives the exact mass estimate used before taking the uniform limit. -/
theorem eq_rare {Window Prefix : Type*}
    [DecidableEq Window] [DecidableEq Prefix]
    (windows : Finset Window) (prefixOf : Window → Prefix)
    (rarePrefixes : Finset Prefix) (span : Window → ℕ) (d m G : ℕ)
    (hrare : ∀ p ∈ rarePrefixes,
      (windows.filter fun k => prefixOf k = p).card ≤ d + 1)
    (hspan : ∀ k ∈ rarePrefixWindows windows prefixOf rarePrefixes,
      span k ≤ m * G) :
    ∑ k ∈ rarePrefixWindows windows prefixOf rarePrefixes, span k ≤
      rarePrefixes.card * (d + 1) * (m * G) := by
  calc
    ∑ k ∈ rarePrefixWindows windows prefixOf rarePrefixes, span k ≤
        ∑ _k ∈ rarePrefixWindows windows prefixOf rarePrefixes, m * G := by
      gcongr with k hk
      exact hspan k hk
    _ = (rarePrefixWindows windows prefixOf rarePrefixes).card * (m * G) := by
      simp
    _ ≤ (rarePrefixes.card * (d + 1)) * (m * G) := by
      gcongr
      exact rarePrefixWindows_card_le windows prefixOf rarePrefixes d hrare
    _ = _ := rfl

/-! ## Canonical forward words and realized prefixes -/

/-- The actual next `m` gaps based at enumeration index `k`. -/
def forwardGapWord (k m : ℕ) : Erdos260.GapWord :=
  Erdos260.enumerationGapWord e k m

@[simp]
theorem forwardGapWord_length (k m : ℕ) :
    (forwardGapWord e k m).length = m := by
  simp [forwardGapWord, Erdos260.enumerationGapWord]

theorem forwardGapWord_positive (k m : ℕ) :
    Erdos260.GapWord.Positive (forwardGapWord e k m) := by
  intro g hg
  simp only [forwardGapWord, Erdos260.enumerationGapWord,
    List.mem_map, List.mem_range] at hg
  obtain ⟨r, hr, rfl⟩ := hg
  unfold Erdos260.supportGap
  exact Nat.sub_pos_of_lt (e.strictMono (Nat.lt_succ_self (k + r)))

theorem forwardGapWord_span (k m : ℕ) :
    Erdos260.GapWord.span (forwardGapWord e k m) =
      forwardSpan e k m := by
  exact Erdos260.enumerationGapWord_span e k m

/-- Windows whose next `m` gaps cross the locking threshold. -/
def longWindowIndices (N W m bound : ℕ) : Finset ℕ :=
  (windowIndices e N W).filter fun k => bound < forwardSpan e k m

/-- Canonical shortest crossing prefix of a long forward word. -/
def lockingPrefix (k m bound : ℕ) : Erdos260.GapWord :=
  (forwardGapWord e k m).firstPrefixAbove bound

/-- Prefix words actually realized by long windows. -/
def realizedLockingPrefixes (N W m bound : ℕ) : Finset Erdos260.GapWord :=
  (longWindowIndices e N W m bound).image fun k =>
    lockingPrefix e k m bound

theorem mem_longWindowIndices_iff {N W m bound k : ℕ} :
    k ∈ longWindowIndices e N W m bound ↔
      k ∈ windowIndices e N W ∧ bound < forwardSpan e k m := by
  simp [longWindowIndices]

/-- Every realized locking prefix has the exact positivity, span, and length
bounds used by the word census. -/
theorem realizedLockingPrefix_bounds {N W m G bound : ℕ}
    (hgeom : WindowGeometry e N W m G) {pfx : Erdos260.GapWord}
    (hpfx : pfx ∈ realizedLockingPrefixes e N W m bound) :
    Erdos260.GapWord.Positive pfx ∧
      bound < Erdos260.GapWord.span pfx ∧
      Erdos260.GapWord.span pfx ≤ bound + G ∧
      pfx.length ≤ m := by
  classical
  rw [realizedLockingPrefixes, Finset.mem_image] at hpfx
  obtain ⟨k, hk, rfl⟩ := hpfx
  have hkdata : k ∈ windowIndices e N W ∧ bound < forwardSpan e k m := by
    simpa [longWindowIndices] using hk
  let word := forwardGapWord e k m
  have hwordPositive : Erdos260.GapWord.Positive word :=
    forwardGapWord_positive e k m
  have hcross : bound < Erdos260.GapWord.span word := by
    rw [forwardGapWord_span]
    exact hkdata.2
  have hcap : ∀ g ∈ word, g ≤ G := by
    intro g hg
    simp only [word, forwardGapWord, Erdos260.enumerationGapWord,
      List.mem_map, List.mem_range] at hg
    obtain ⟨r, hr, rfl⟩ := hg
    apply hgeom.gaps_le
    have hkIco := Finset.mem_Ico.mp hkdata.1
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  refine ⟨Erdos260.GapWord.firstPrefixAbove_positive
      word bound hwordPositive,
    (Erdos260.GapWord.lt_span_firstPrefixAbove_of_lt_span
      word bound hcross),
    Erdos260.GapWord.span_firstPrefixAbove_le_add word bound G hcap, ?_⟩
  exact (Erdos260.GapWord.firstPrefixAbove_length_le word bound).trans
    (by simp [word])

/-- Actual form of `eq:prefixcount`: realized prefixes inject into the finite
positive-word census. -/
theorem realizedLockingPrefixes_card_le {N W m G bound : ℕ}
    (hgeom : WindowGeometry e N W m G) :
    (realizedLockingPrefixes e N W m bound).card ≤
      (boundedPositiveGapWords (bound + G) m).card := by
  apply Finset.card_le_card
  intro pfx hpfx
  rw [mem_boundedPositiveGapWords_iff]
  have h := realizedLockingPrefix_bounds e hgeom hpfx
  exact ⟨h.1, h.2.2.1, h.2.2.2⟩

theorem realizedLockingPrefixes_card_le_compositions
    {N W m G bound : ℕ}
    (hgeom : WindowGeometry e N W m G) :
    (realizedLockingPrefixes e N W m bound).card ≤
      ∑ r ∈ Finset.Icc 0 m, (bound + G).choose r :=
  (realizedLockingPrefixes_card_le e hgeom).trans
    (boundedPositiveGapWords_card_le (bound + G) m)

end EnumerationWindows

theorem windowCount_positiveSupport (S : Set ℕ) (N W : ℕ) :
    windowCount (Erdos260.positiveSupport S) N W = windowCount S N W := by
  classical
  unfold windowCount
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_Ioc, Erdos260.positiveSupport,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨hIoc, hS, _⟩
    exact ⟨hIoc, hS⟩
  · rintro ⟨hIoc, hS⟩
    exact ⟨hIoc, hS, lt_of_le_of_lt (Nat.zero_le N) hIoc.1⟩

namespace CarrySeries

theorem enumeratedWindowCount_eq_windowCount (D : CarrySeries) (N W : ℕ) :
    enumeratedWindowCount D.positiveEnumeration N W =
      windowCount D.support N W := by
  rw [Erdos260.PolynomialWindow.enumeratedWindowCount_eq_windowCount,
    windowCount_positiveSupport]

/-- Turn the eventual carry-gap estimate into a uniform geometry certificate
whenever all touched endpoints are known to lie below `B`. -/
theorem exists_windowGeometry_of_endpoint_cap (D : CarrySeries) :
    ∃ Cgap N₀ : ℕ, ∀ N W m B : ℕ, N₀ ≤ N → N ≤ B →
      D.positiveEnumeration.a
          (afterWindowIndex D.positiveEnumeration N W + m) ≤ B →
      WindowGeometry D.positiveEnumeration N W m
        (D.weight.natDegree * Nat.log D.base B + Cgap) := by
  obtain ⟨Cgap, xgap, hgap⟩ := D.eventual_gap_log_bound
  let e := D.positiveEnumeration
  let k₀ := Erdos260.firstIndexAbove e xgap
  let N₀ := e.a k₀
  refine ⟨Cgap, N₀, ?_⟩
  intro N W m B hN hNB hcap
  let i := firstWindowIndex e N
  let j := afterWindowIndex e N W
  have hk₀i : k₀ < i := by
    by_contra hnot
    have hik₀ : i ≤ k₀ := Nat.le_of_not_gt hnot
    have hmono : e.a i ≤ e.a k₀ := e.strictMono.monotone hik₀
    have hiSpec : N < e.a i := by
      dsimp [i, firstWindowIndex]
      exact Erdos260.firstIndexAbove_spec e N
    dsimp [N₀] at hN
    omega
  have hiPos : 0 < i := lt_of_le_of_lt (Nat.zero_le k₀) hk₀i
  let p := i - 1
  have hpSucc : p + 1 = i := by dsimp [p]; omega
  have hk₀p : k₀ ≤ p := by dsimp [p]; omega
  have hpI : p < i := by dsimp [p]; omega
  have hpUpper : e.a p ≤ N := by
    dsimp [i, firstWindowIndex] at hpI
    exact Erdos260.firstIndexAbove_minimal e N p hpI
  have hpGapStart : xgap ≤ e.a p := by
    have hk₀Spec : xgap < e.a k₀ := by
      dsimp [k₀]
      exact Erdos260.firstIndexAbove_spec e xgap
    have hmono := e.strictMono.monotone hk₀p
    omega
  let G := D.weight.natDegree * Nat.log D.base B + Cgap
  have hpGap : Erdos260.supportGap e p ≤ G := by
    have hraw := hgap (e.a p) hpGapStart
      (Erdos260.supportGap e p)
      (D.positiveEnumeration_gap_isSupportGap p)
    have hlog : Nat.log D.base (e.a p) ≤ Nat.log D.base B := by
      apply Nat.log_mono_right
      exact hpUpper.trans hNB
    have hmul := Nat.mul_le_mul_left D.weight.natDegree hlog
    exact hraw.trans (Nat.add_le_add_right hmul Cgap)
  refine ⟨?_, ?_⟩
  · change e.a i ≤ N + G
    have hpMono : e.a p ≤ e.a i := e.strictMono.monotone hpI.le
    have hgapEq : Erdos260.supportGap e p = e.a i - e.a p := by
      simp only [Erdos260.supportGap, hpSucc]
    rw [hgapEq] at hpGap
    omega
  · intro q hq
    have hq' := Finset.mem_Ico.mp hq
    have hiSpec : N < e.a i := by
      dsimp [i, firstWindowIndex]
      exact Erdos260.firstIndexAbove_spec e N
    have hqStart : xgap ≤ e.a q := by
      have hiq : i ≤ q := by simpa only [i] using hq'.1
      have hmono := e.strictMono.monotone hiq
      omega
    have hqEnd : e.a q ≤ B := by
      have hqle : q ≤ j + m := by
        have hupper : q < j + m := by
          simpa only [e, j] using hq'.2
        exact hupper.le
      have hmono := e.strictMono.monotone hqle
      exact hmono.trans hcap
    have hraw := hgap (e.a q) hqStart
      (Erdos260.supportGap e q)
      (D.positiveEnumeration_gap_isSupportGap q)
    have hlog : Nat.log D.base (e.a q) ≤ Nat.log D.base B :=
      Nat.log_mono_right hqEnd
    have hmul := Nat.mul_le_mul_left D.weight.natDegree hlog
    exact hraw.trans (Nat.add_le_add_right hmul Cgap)

/-- Bootstrap used in `lem:localscale`: logarithmic gaps keep the first `m`
future points below `3N` as soon as their total worst-case displacement is
smaller than `N`. -/
theorem endpoint_cap_of_gap_bound (D : CarrySeries)
    {Cgap xgap N W m : ℕ}
    (hgap : ∀ x : ℕ, xgap ≤ x → ∀ g : ℕ,
      D.IsSupportGap x g →
        g ≤ D.weight.natDegree * Nat.log D.base x + Cgap)
    (hN : D.positiveEnumeration.a
      (Erdos260.firstIndexAbove D.positiveEnumeration xgap) ≤ N)
    (hW : W ≤ N)
    (hsmall : (m + 1) *
      (D.weight.natDegree * Nat.log D.base (3 * N) + Cgap) < N) :
    D.positiveEnumeration.a
        (afterWindowIndex D.positiveEnumeration N W + m) ≤ 3 * N := by
  let e := D.positiveEnumeration
  let k₀ := Erdos260.firstIndexAbove e xgap
  let j := afterWindowIndex e N W
  let G := D.weight.natDegree * Nat.log D.base (3 * N) + Cgap
  have hk₀j : k₀ < j := by
    by_contra hnot
    have hjk₀ : j ≤ k₀ := Nat.le_of_not_gt hnot
    have hmono : e.a j ≤ e.a k₀ := e.strictMono.monotone hjk₀
    have hjSpec : N + W < e.a j := by
      dsimp [j, afterWindowIndex]
      exact Erdos260.firstIndexAbove_spec e (N + W)
    have hN' : e.a k₀ ≤ N := by
      dsimp [e, k₀]
      exact hN
    omega
  have hjPos : 0 < j := lt_of_le_of_lt (Nat.zero_le k₀) hk₀j
  let p := j - 1
  have hpSucc : p + 1 = j := by dsimp [p]; omega
  have hk₀p : k₀ ≤ p := by dsimp [p]; omega
  have hpj : p < j := by dsimp [p]; omega
  have hpUpper : e.a p ≤ N + W := by
    dsimp [j, afterWindowIndex] at hpj
    exact Erdos260.firstIndexAbove_minimal e (N + W) p hpj
  have hpStart : xgap ≤ e.a p := by
    have hk₀Spec : xgap < e.a k₀ := by
      dsimp [k₀]
      exact Erdos260.firstIndexAbove_spec e xgap
    have hmono := e.strictMono.monotone hk₀p
    omega
  have hpBound : Erdos260.supportGap e p ≤ G := by
    have hraw := hgap (e.a p) hpStart (Erdos260.supportGap e p)
      (D.positiveEnumeration_gap_isSupportGap p)
    have hp3N : e.a p ≤ 3 * N := by omega
    have hlog : Nat.log D.base (e.a p) ≤ Nat.log D.base (3 * N) :=
      Nat.log_mono_right (b := D.base) hp3N
    have hmul := Nat.mul_le_mul_left D.weight.natDegree hlog
    exact hraw.trans (Nat.add_le_add_right hmul Cgap)
  have hjBase : e.a j ≤ N + W + G := by
    have hpMono : e.a p ≤ e.a j := e.strictMono.monotone hpj.le
    have hgapEq : Erdos260.supportGap e p = e.a j - e.a p := by
      simp only [Erdos260.supportGap, hpSucc]
    rw [hgapEq] at hpBound
    omega
  have hfuture : ∀ r : ℕ, r ≤ m → e.a (j + r) ≤ N + W + (r + 1) * G := by
    intro r hr
    induction r with
    | zero => simpa using hjBase
    | succ r ih =>
        have hrm : r ≤ m := r.le_succ.trans hr
        have hprev := ih hrm
        have hrOne : (r + 1) * G ≤ (m + 1) * G :=
          Nat.mul_le_mul_right G (Nat.add_le_add_right hrm 1)
        have hprev3N : e.a (j + r) ≤ 3 * N := by
          have hdisp : (r + 1) * G < N := hrOne.trans_lt hsmall
          omega
        have hstart : xgap ≤ e.a (j + r) := by
          have hkj : k₀ ≤ j + r := by omega
          have hmono := e.strictMono.monotone hkj
          have hk₀Spec : xgap < e.a k₀ := by
            dsimp [k₀]
            exact Erdos260.firstIndexAbove_spec e xgap
          omega
        have hgapRaw := hgap (e.a (j + r)) hstart
          (Erdos260.supportGap e (j + r))
          (D.positiveEnumeration_gap_isSupportGap (j + r))
        have hlog : Nat.log D.base (e.a (j + r)) ≤
            Nat.log D.base (3 * N) :=
          Nat.log_mono_right (b := D.base) hprev3N
        have hmul := Nat.mul_le_mul_left D.weight.natDegree hlog
        have hgapG : Erdos260.supportGap e (j + r) ≤ G :=
          hgapRaw.trans (Nat.add_le_add_right hmul Cgap)
        have hstep : e.a (j + (r + 1)) =
            e.a (j + r) + Erdos260.supportGap e (j + r) := by
          have hmono : e.a (j + r) ≤ e.a (j + r + 1) :=
            e.strictMono.monotone (by omega)
          rw [show j + (r + 1) = j + r + 1 by omega]
          simp only [Erdos260.supportGap]
          omega
        rw [hstep]
        calc
          e.a (j + r) + Erdos260.supportGap e (j + r) ≤
              (N + W + (r + 1) * G) + G :=
            Nat.add_le_add hprev hgapG
          _ = N + W + (r + 1 + 1) * G := by ring
  have hend := hfuture m le_rfl
  have hdisp : (m + 1) * G < N := by simpa only [G] using hsmall
  dsimp [e, j] at hend ⊢
  omega

/-- Unconditional local geometry once the explicit small-displacement
inequality is supplied.  The same `Cgap` works for every numerator, support,
and window attached to `D`. -/
theorem exists_windowGeometry (D : CarrySeries) :
    ∃ Cgap N₀ : ℕ, ∀ N W m : ℕ, N₀ ≤ N → W ≤ N →
      (m + 1) *
        (D.weight.natDegree * Nat.log D.base (3 * N) + Cgap) < N →
      WindowGeometry D.positiveEnumeration N W m
        (D.weight.natDegree * Nat.log D.base (3 * N) + Cgap) := by
  obtain ⟨Cgeom, Ngeom, hgeom⟩ := D.exists_windowGeometry_of_endpoint_cap
  obtain ⟨Craw, xraw, hraw⟩ := D.eventual_gap_log_bound
  let e := D.positiveEnumeration
  let Nraw := e.a (Erdos260.firstIndexAbove e xraw)
  let Cgap := max Cgeom Craw
  refine ⟨Cgap, max Ngeom Nraw, ?_⟩
  intro N W m hN hW hsmall
  have hNgeom : Ngeom ≤ N := (le_max_left _ _).trans hN
  have hNraw : Nraw ≤ N := (le_max_right _ _).trans hN
  have hsmallRaw :
      (m + 1) *
          (D.weight.natDegree * Nat.log D.base (3 * N) + Craw) < N := by
    apply lt_of_le_of_lt _ hsmall
    gcongr
    exact le_max_right Cgeom Craw
  have hcap : e.a (afterWindowIndex e N W + m) ≤ 3 * N := by
    apply D.endpoint_cap_of_gap_bound hraw
    · simpa only [e, Nraw] using hNraw
    · exact hW
    · exact hsmallRaw
  have hbaseGeom := hgeom N W m (3 * N) hNgeom (by omega) (by
    simpa only [e] using hcap)
  let Ggeom := D.weight.natDegree * Nat.log D.base (3 * N) + Cgeom
  let G := D.weight.natDegree * Nat.log D.base (3 * N) + Cgap
  have hGG : Ggeom ≤ G := by
    dsimp [Ggeom, G, Cgap]
    exact Nat.add_le_add_left (le_max_left Cgeom Craw) _
  refine ⟨?_, ?_⟩
  · exact hbaseGeom.first_le.trans (Nat.add_le_add_left hGG N)
  · intro q hq
    exact (hbaseGeom.gaps_le q hq).trans hGG

end CarrySeries

end Erdos260.PolynomialWindow
