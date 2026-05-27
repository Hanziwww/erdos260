import Mathlib
import Erdos260.HitSequence

/-!
# Positive-density pressure primitives

This file introduces finite window sums and high-excess masses for Lemma 21.1
and Section 22 of `proof_v2.tex`.  The analytic estimates are proved later; the
objects here are closed finite sums with basic algebraic lemmas.
-/

namespace Erdos260

open Finset

noncomputable section

/-- Forward gap window `g_start + ... + g_{start+r}`. -/
def gapWindow (g : Nat -> Nat) (start r : Nat) : Nat :=
  ∑ i ∈ range (r + 1), g (start + i)

/-- Positive part of a real number. -/
def positivePart (x : ℝ) : ℝ :=
  max x 0

/-- Real excess of a finite gap window above threshold `T`. -/
def windowExcess (g : Nat -> Nat) (start r : Nat) (T : ℝ) : ℝ :=
  positivePart ((gapWindow g start r : ℝ) - T)

/-- High-excess mass over a finite set of starting indices. -/
def highExcessMass (starts : Finset Nat) (g : Nat -> Nat) (r : Nat) (T : ℝ) : ℝ :=
  ∑ k ∈ starts, windowExcess g k r T

/-- Total real gap-window mass over a finite set of starting indices. -/
def gapWindowMass (starts : Finset Nat) (g : Nat -> Nat) (r : Nat) : ℝ :=
  ∑ k ∈ starts, (gapWindow g k r : ℝ)

/-- Starting indices whose window excess is at least `Y`. -/
def highExcessStarts (starts : Finset Nat) (g : Nat -> Nat) (r : Nat)
    (T Y : ℝ) : Finset Nat :=
  starts.filter fun k => Y <= windowExcess g k r T

@[simp]
theorem gapWindow_zero (g : Nat -> Nat) (start : Nat) :
    gapWindow g start 0 = g start := by
  simp [gapWindow]

theorem gapWindow_succ (g : Nat -> Nat) (start r : Nat) :
    gapWindow g start (r + 1) =
      gapWindow g start r + g (start + (r + 1)) := by
  simp [gapWindow, sum_range_succ, Nat.add_assoc]

theorem gapWindow_append (g : Nat -> Nat) (start r s : Nat) :
    gapWindow g start (r + s + 1) =
      gapWindow g start r + gapWindow g (start + r + 1) s := by
  induction s with
  | zero =>
      rw [Nat.add_zero, gapWindow_succ]
      simp [gapWindow, Nat.add_assoc]
  | succ s ih =>
      have hleft :
          gapWindow g start (r + (s + 1) + 1) =
            gapWindow g start (r + s + 1) + g (start + (r + s + 1 + 1)) := by
        simpa [Nat.add_assoc] using gapWindow_succ g start (r + s + 1)
      rw [hleft, ih, gapWindow_succ]
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem gapWindow_nonneg (g : Nat -> Nat) (start r : Nat) :
    0 <= gapWindow g start r := Nat.zero_le _

theorem gapWindow_le_of_pointwise {g : Nat -> Nat} {start r B : Nat}
    (hB : ∀ i : Nat, i <= r -> g (start + i) <= B) :
    gapWindow g start r <= (r + 1) * B := by
  unfold gapWindow
  calc
    (∑ i ∈ range (r + 1), g (start + i)) <= ∑ i ∈ range (r + 1), B := by
      exact sum_le_sum fun i hi => by
        rw [mem_range] at hi
        exact hB i (by omega)
    _ = (r + 1) * B := by simp [Nat.mul_comm]

theorem gapWindow_le_of_pointwise_on_range {g : Nat -> Nat} {start r B : Nat}
    (hB : ∀ k : Nat, start <= k -> k <= start + r -> g k <= B) :
    gapWindow g start r <= (r + 1) * B :=
  gapWindow_le_of_pointwise fun i hi =>
    hB (start + i) (by omega) (by omega)

theorem gapWindow_ge_of_pointwise {g : Nat -> Nat} {start r B : Nat}
    (hB : ∀ i : Nat, i <= r -> B <= g (start + i)) :
    (r + 1) * B <= gapWindow g start r := by
  unfold gapWindow
  calc
    (r + 1) * B = ∑ _i ∈ range (r + 1), B := by simp [Nat.mul_comm]
    _ <= ∑ i ∈ range (r + 1), g (start + i) := by
          exact sum_le_sum fun i hi => by
            rw [mem_range] at hi
            exact hB i (by omega)

theorem gapWindow_eq_zero_of_pointwise_zero {g : Nat -> Nat} {start r : Nat}
    (hzero : ∀ i : Nat, i <= r -> g (start + i) = 0) :
    gapWindow g start r = 0 := by
  unfold gapWindow
  exact sum_eq_zero fun i hi => by
    rw [mem_range] at hi
    exact hzero i (by omega)

theorem gapWindow_hitGap_eq_of_strictMono {a : Nat -> Nat}
    (ha : StrictMono a) (start r : Nat) :
    gapWindow (hitGap a) start r = a (start + r + 1) - a start := by
  induction r with
  | zero =>
      simp [gapWindow, hitGap]
  | succ r ih =>
      rw [gapWindow_succ, ih]
      have hle₁ : a start <= a (start + r + 1) := ha.monotone (by omega)
      have hle₂ : a (start + r + 1) <= a (start + r + 1 + 1) :=
        ha.monotone (by omega)
      unfold hitGap
      rw [show start + (r + 1) = start + r + 1 by omega]
      omega

theorem HitSequence.gapWindow_hitGap_eq {d a : Nat -> Nat}
    (hseq : HitSequence d a) (start r : Nat) :
    gapWindow (hitGap a) start r = a (start + r + 1) - a start :=
  gapWindow_hitGap_eq_of_strictMono hseq.strict start r

theorem positivePart_nonneg (x : ℝ) :
    0 <= positivePart x := by
  simp [positivePart]

theorem self_le_positivePart (x : ℝ) :
    x <= positivePart x := by
  unfold positivePart
  exact le_max_left x 0

theorem le_positivePart_self {x : ℝ} (hx : 0 <= x) :
    positivePart x = x := by
  simp [positivePart, hx]

theorem positivePart_eq_zero_of_nonpos {x : ℝ} (hx : x <= 0) :
    positivePart x = 0 := by
  simp [positivePart, hx]

theorem positivePart_mono {x y : ℝ} (hxy : x <= y) :
    positivePart x <= positivePart y := by
  exact max_le_max hxy le_rfl

theorem positivePart_le_of_le {x B : ℝ} (hx : x <= B) (hB : 0 <= B) :
    positivePart x <= B := by
  unfold positivePart
  exact max_le hx hB

theorem windowExcess_nonneg (g : Nat -> Nat) (start r : Nat) (T : ℝ) :
    0 <= windowExcess g start r T :=
  positivePart_nonneg _

theorem gapWindow_sub_threshold_le_windowExcess
    (g : Nat -> Nat) (start r : Nat) (T : ℝ) :
    (gapWindow g start r : ℝ) - T <= windowExcess g start r T := by
  unfold windowExcess
  exact self_le_positivePart _

theorem windowExcess_pos_iff {g : Nat -> Nat} {start r : Nat} {T : ℝ} :
    0 < windowExcess g start r T ↔ T < (gapWindow g start r : ℝ) := by
  unfold windowExcess positivePart
  by_cases h : (gapWindow g start r : ℝ) - T <= 0
  · have hmax : max ((gapWindow g start r : ℝ) - T) 0 = 0 := by
      exact max_eq_right h
    simp [hmax]
    linarith
  · have hpos : 0 < (gapWindow g start r : ℝ) - T := lt_of_not_ge h
    have hmax : max ((gapWindow g start r : ℝ) - T) 0 =
        (gapWindow g start r : ℝ) - T := by
      exact max_eq_left hpos.le
    simp [hmax]

theorem windowExcess_pos_of_threshold_lt {g : Nat -> Nat} {start r : Nat} {T : ℝ}
    (hT : T < (gapWindow g start r : ℝ)) :
    0 < windowExcess g start r T :=
  windowExcess_pos_iff.2 hT

theorem windowExcess_eq_zero_of_gapWindow_le {g : Nat -> Nat} {start r : Nat}
    {T : ℝ} (h : (gapWindow g start r : ℝ) <= T) :
    windowExcess g start r T = 0 := by
  unfold windowExcess
  exact positivePart_eq_zero_of_nonpos (by linarith)

theorem windowExcess_mono_threshold {g : Nat -> Nat} {start r : Nat}
    {T₁ T₂ : ℝ} (hT : T₁ <= T₂) :
    windowExcess g start r T₂ <= windowExcess g start r T₁ := by
  unfold windowExcess
  exact positivePart_mono (by linarith)

theorem windowExcess_mono_gapWindow {g₁ g₂ : Nat -> Nat} {start r : Nat}
    {T : ℝ}
    (hgap : gapWindow g₁ start r <= gapWindow g₂ start r) :
    windowExcess g₁ start r T <= windowExcess g₂ start r T := by
  unfold windowExcess
  have hgapℝ : (gapWindow g₁ start r : ℝ) <= (gapWindow g₂ start r : ℝ) := by
    exact_mod_cast hgap
  exact positivePart_mono (by linarith)

theorem windowExcess_eq_gapWindow_sub_of_threshold_le
    {g : Nat -> Nat} {start r : Nat} {T : ℝ}
    (hT : T <= (gapWindow g start r : ℝ)) :
    windowExcess g start r T = (gapWindow g start r : ℝ) - T := by
  unfold windowExcess
  exact le_positivePart_self (by linarith)

theorem windowExcess_le_gapWindow_of_nonneg_threshold
    {g : Nat -> Nat} {start r : Nat} {T : ℝ}
    (hT : 0 <= T) :
    windowExcess g start r T <= (gapWindow g start r : ℝ) := by
  unfold windowExcess
  apply positivePart_le_of_le
  · linarith
  · positivity

theorem windowExcess_le_of_gapWindow_sub_le {g : Nat -> Nat} {start r : Nat}
    {T B : ℝ} (h : (gapWindow g start r : ℝ) - T <= B) (hB : 0 <= B) :
    windowExcess g start r T <= B := by
  unfold windowExcess
  exact positivePart_le_of_le h hB

theorem highExcessMass_nonneg (starts : Finset Nat) (g : Nat -> Nat) (r : Nat) (T : ℝ) :
    0 <= highExcessMass starts g r T := by
  unfold highExcessMass
  exact sum_nonneg fun k _ => windowExcess_nonneg g k r T

theorem highExcessMass_empty (g : Nat -> Nat) (r : Nat) (T : ℝ) :
    highExcessMass ∅ g r T = 0 := by
  simp [highExcessMass]

@[simp]
theorem highExcessMass_singleton (k : Nat) (g : Nat -> Nat) (r : Nat) (T : ℝ) :
    highExcessMass {k} g r T = windowExcess g k r T := by
  simp [highExcessMass]

theorem gapWindowMass_empty (g : Nat -> Nat) (r : Nat) :
    gapWindowMass ∅ g r = 0 := by
  simp [gapWindowMass]

@[simp]
theorem gapWindowMass_singleton (k : Nat) (g : Nat -> Nat) (r : Nat) :
    gapWindowMass {k} g r = (gapWindow g k r : ℝ) := by
  simp [gapWindowMass]

theorem gapWindowMass_mono_subset {s t : Finset Nat} {g : Nat -> Nat} {r : Nat}
    (hst : s ⊆ t) :
    gapWindowMass s g r <= gapWindowMass t g r := by
  unfold gapWindowMass
  exact sum_le_sum_of_subset_of_nonneg hst fun _ _ _ => by positivity

theorem gapWindowMass_le_card_mul {starts : Finset Nat}
    {g : Nat -> Nat} {r B : Nat}
    (hB : ∀ k ∈ starts, gapWindow g k r <= B) :
    gapWindowMass starts g r <= (starts.card : ℝ) * (B : ℝ) := by
  unfold gapWindowMass
  calc
    (∑ k ∈ starts, (gapWindow g k r : ℝ)) <=
        ∑ _k ∈ starts, (B : ℝ) := by
          exact sum_le_sum fun k hk => by exact_mod_cast hB k hk
    _ = (starts.card : ℝ) * (B : ℝ) := by
          simp [mul_comm]

theorem card_mul_le_gapWindowMass {starts : Finset Nat}
    {g : Nat -> Nat} {r B : Nat}
    (hB : ∀ k ∈ starts, B <= gapWindow g k r) :
    (starts.card : ℝ) * (B : ℝ) <= gapWindowMass starts g r := by
  unfold gapWindowMass
  calc
    (starts.card : ℝ) * (B : ℝ) = ∑ _k ∈ starts, (B : ℝ) := by
      simp [mul_comm]
    _ <= ∑ k ∈ starts, (gapWindow g k r : ℝ) := by
      exact sum_le_sum fun k hk => by exact_mod_cast hB k hk

theorem gapWindowMass_hitGap_eq_sum_span {a : Nat -> Nat}
    (ha : StrictMono a) (starts : Finset Nat) (r : Nat) :
    gapWindowMass starts (hitGap a) r =
      ∑ k ∈ starts, ((a (k + r + 1) - a k : Nat) : ℝ) := by
  unfold gapWindowMass
  exact sum_congr rfl fun k _ => by
    rw [gapWindow_hitGap_eq_of_strictMono ha]

theorem gapWindowMass_sub_card_mul_threshold_le_highExcessMass
    (starts : Finset Nat) (g : Nat -> Nat) (r : Nat) (T : ℝ) :
    gapWindowMass starts g r - (starts.card : ℝ) * T <=
      highExcessMass starts g r T := by
  have hpoint :
      ∀ k ∈ starts, (gapWindow g k r : ℝ) - T <= windowExcess g k r T := by
    intro k _
    exact gapWindow_sub_threshold_le_windowExcess g k r T
  calc
    gapWindowMass starts g r - (starts.card : ℝ) * T =
        ∑ k ∈ starts, ((gapWindow g k r : ℝ) - T) := by
          simp [gapWindowMass, sum_sub_distrib, mul_comm]
    _ <= ∑ k ∈ starts, windowExcess g k r T := by
          exact sum_le_sum hpoint
    _ = highExcessMass starts g r T := by
          rfl

theorem highExcessMass_ge_of_gapWindowMass_ge_card_mul_le
    {starts : Finset Nat} {g : Nat -> Nat} {r : Nat} {T M E : ℝ}
    (hM : M <= gapWindowMass starts g r)
    (hE : (starts.card : ℝ) * T <= E) :
    M - E <= highExcessMass starts g r T := by
  have hbase :=
    gapWindowMass_sub_card_mul_threshold_le_highExcessMass starts g r T
  linarith

theorem highExcessMass_pos_of_card_mul_threshold_lt_gapWindowMass
    {starts : Finset Nat} {g : Nat -> Nat} {r : Nat} {T : ℝ}
    (h : (starts.card : ℝ) * T < gapWindowMass starts g r) :
    0 < highExcessMass starts g r T := by
  have hbase :=
    gapWindowMass_sub_card_mul_threshold_le_highExcessMass starts g r T
  linarith

theorem highExcessMass_mono_subset {s t : Finset Nat} {g : Nat -> Nat} {r : Nat} {T : ℝ}
    (hst : s ⊆ t) :
    highExcessMass s g r T <= highExcessMass t g r T := by
  unfold highExcessMass
  exact sum_le_sum_of_subset_of_nonneg hst fun x _ _ =>
    windowExcess_nonneg g x r T

theorem highExcessMass_mono_gapWindow {starts : Finset Nat}
    {g₁ g₂ : Nat -> Nat} {r : Nat} {T : ℝ}
    (hgap : ∀ k ∈ starts, gapWindow g₁ k r <= gapWindow g₂ k r) :
    highExcessMass starts g₁ r T <= highExcessMass starts g₂ r T := by
  unfold highExcessMass
  exact sum_le_sum fun k hk => windowExcess_mono_gapWindow (hgap k hk)

theorem highExcessMass_union_of_disjoint {s t : Finset Nat}
    {g : Nat -> Nat} {r : Nat} {T : ℝ} (hdisj : Disjoint s t) :
    highExcessMass (s ∪ t) g r T =
      highExcessMass s g r T + highExcessMass t g r T := by
  unfold highExcessMass
  exact sum_union hdisj

theorem highExcessMass_eq_add_sdiff {s t : Finset Nat}
    {g : Nat -> Nat} {r : Nat} {T : ℝ} (hts : t ⊆ s) :
    highExcessMass s g r T =
      highExcessMass t g r T + highExcessMass (s \ t) g r T := by
  have hsplit : s = t ∪ (s \ t) := by
    ext k
    constructor
    · intro hk
      by_cases hkt : k ∈ t
      · exact mem_union.2 (Or.inl hkt)
      · exact mem_union.2 (Or.inr (mem_sdiff.2 ⟨hk, hkt⟩))
    · intro hk
      rcases mem_union.1 hk with hkt | hks
      · exact hts hkt
      · exact (mem_sdiff.1 hks).1
  calc
    highExcessMass s g r T =
        highExcessMass (t ∪ (s \ t)) g r T := by
          exact congrArg (fun u => highExcessMass u g r T) hsplit
    _ = highExcessMass t g r T + highExcessMass (s \ t) g r T := by
          exact highExcessMass_union_of_disjoint
            (s := t) (t := s \ t) (g := g) (r := r) (T := T)
            disjoint_sdiff

theorem highExcessMass_filter_add_filter_not
    (starts : Finset Nat) (p : Nat -> Prop) [DecidablePred p]
    (g : Nat -> Nat) (r : Nat) (T : ℝ) :
    highExcessMass starts g r T =
      highExcessMass (starts.filter p) g r T +
        highExcessMass (starts.filter fun k => ¬ p k) g r T := by
  have hsubset : starts.filter p ⊆ starts := filter_subset _ _
  have hsdiff :
      starts \ starts.filter p = starts.filter fun k => ¬ p k := by
    ext k
    constructor
    · intro hk
      rcases mem_sdiff.1 hk with ⟨hkstarts, hknot⟩
      exact mem_filter.2
        ⟨hkstarts, fun hpk => hknot (mem_filter.2 ⟨hkstarts, hpk⟩)⟩
    · intro hk
      rcases mem_filter.1 hk with ⟨hkstarts, hpknot⟩
      exact mem_sdiff.2
        ⟨hkstarts, fun hkfilter => hpknot (mem_filter.1 hkfilter).2⟩
  simpa [hsdiff] using
    highExcessMass_eq_add_sdiff
      (s := starts) (t := starts.filter p) (g := g) (r := r) (T := T)
      hsubset

theorem mem_highExcessStarts {starts : Finset Nat} {g : Nat -> Nat}
    {r : Nat} {T Y : ℝ} {k : Nat} :
    k ∈ highExcessStarts starts g r T Y ↔
      k ∈ starts ∧ Y <= windowExcess g k r T := by
  simp [highExcessStarts]

theorem highExcessStarts_subset (starts : Finset Nat) (g : Nat -> Nat)
    (r : Nat) (T Y : ℝ) :
    highExcessStarts starts g r T Y ⊆ starts := by
  intro k hk
  exact (mem_highExcessStarts.1 hk).1

theorem highExcessStarts_card_le (starts : Finset Nat) (g : Nat -> Nat)
    (r : Nat) (T Y : ℝ) :
    (highExcessStarts starts g r T Y).card <= starts.card :=
  card_le_card (highExcessStarts_subset starts g r T Y)

theorem highExcessStarts_mono_cutoff {starts : Finset Nat} {g : Nat -> Nat}
    {r : Nat} {T Y₁ Y₂ : ℝ} (hY : Y₁ <= Y₂) :
    highExcessStarts starts g r T Y₂ ⊆ highExcessStarts starts g r T Y₁ := by
  intro k hk
  rcases mem_highExcessStarts.1 hk with ⟨hmem, hexcess⟩
  exact mem_highExcessStarts.2 ⟨hmem, hY.trans hexcess⟩

theorem highExcessStarts_mono_threshold {starts : Finset Nat} {g : Nat -> Nat}
    {r : Nat} {T₁ T₂ Y : ℝ} (hT : T₁ <= T₂) :
    highExcessStarts starts g r T₂ Y ⊆ highExcessStarts starts g r T₁ Y := by
  intro k hk
  rcases mem_highExcessStarts.1 hk with ⟨hmem, hexcess⟩
  exact mem_highExcessStarts.2
    ⟨hmem, hexcess.trans (windowExcess_mono_threshold hT)⟩

theorem card_highExcessStarts_mul_le_highExcessMass
    {starts : Finset Nat} {g : Nat -> Nat} {r : Nat} {T Y : ℝ} :
    ((highExcessStarts starts g r T Y).card : ℝ) * Y <=
      highExcessMass starts g r T := by
  let high := highExcessStarts starts g r T Y
  have hterm : ∀ k ∈ high, Y <= windowExcess g k r T := by
    intro k hk
    exact (mem_highExcessStarts.1 hk).2
  calc
    ((highExcessStarts starts g r T Y).card : ℝ) * Y
        = ∑ _k ∈ high, Y := by
          simp [high, mul_comm]
    _ <= ∑ k ∈ high, windowExcess g k r T := by
          exact sum_le_sum hterm
    _ = highExcessMass high g r T := by
          rfl
    _ <= highExcessMass starts g r T := by
          exact highExcessMass_mono_subset
            (highExcessStarts_subset starts g r T Y)

theorem card_highExcessStarts_le_div_of_mass_le
    {starts : Finset Nat} {g : Nat -> Nat} {r : Nat} {T Y M : ℝ}
    (hY : 0 < Y) (hmass : highExcessMass starts g r T <= M) :
    ((highExcessStarts starts g r T Y).card : ℝ) <= M / Y := by
  have hmul :=
    card_highExcessStarts_mul_le_highExcessMass
      (starts := starts) (g := g) (r := r) (T := T) (Y := Y)
  have hcard :
      ((highExcessStarts starts g r T Y).card : ℝ) <=
        highExcessMass starts g r T / Y := by
    exact (le_div_iff₀ hY).2 hmul
  exact hcard.trans (div_le_div_of_nonneg_right hmass hY.le)

theorem highExcessMass_le_card_mul {starts : Finset Nat} {g : Nat -> Nat}
    {r : Nat} {T B : ℝ}
    (h : ∀ k ∈ starts, windowExcess g k r T <= B) :
    highExcessMass starts g r T <= (starts.card : ℝ) * B := by
  unfold highExcessMass
  calc
    (∑ k ∈ starts, windowExcess g k r T) <= ∑ k ∈ starts, B := by
      exact sum_le_sum h
    _ = (starts.card : ℝ) * B := by
      simp [mul_comm]

theorem highExcessMass_sdiff_highExcessStarts_le_card_mul
    {starts : Finset Nat} {g : Nat -> Nat} {r : Nat} {T Y : ℝ} :
    highExcessMass (starts \ highExcessStarts starts g r T Y) g r T <=
      (((starts \ highExcessStarts starts g r T Y).card : Nat) : ℝ) * Y := by
  exact highExcessMass_le_card_mul fun k hk => by
    rcases mem_sdiff.1 hk with ⟨hkstarts, hkhigh⟩
    have hnot : ¬ Y <= windowExcess g k r T := by
      intro hY
      exact hkhigh (mem_highExcessStarts.2 ⟨hkstarts, hY⟩)
    exact (lt_of_not_ge hnot).le

theorem highExcessMass_le_highPart_add_low_card_mul
    {starts : Finset Nat} {g : Nat -> Nat} {r : Nat} {T Y : ℝ} :
    highExcessMass starts g r T <=
      highExcessMass (highExcessStarts starts g r T Y) g r T +
        (((starts \ highExcessStarts starts g r T Y).card : Nat) : ℝ) * Y := by
  have hsplit :=
    highExcessMass_eq_add_sdiff
      (s := starts) (t := highExcessStarts starts g r T Y)
      (g := g) (r := r) (T := T)
      (highExcessStarts_subset starts g r T Y)
  rw [hsplit]
  have hlow :=
    highExcessMass_sdiff_highExcessStarts_le_card_mul
      (starts := starts) (g := g) (r := r) (T := T) (Y := Y)
  linarith

theorem highExcessMass_highPart_ge_sub_of_mass_ge_low_le
    {starts : Finset Nat} {g : Nat -> Nat} {r : Nat} {T Y M E : ℝ}
    (hmass : M <= highExcessMass starts g r T)
    (hlow :
      highExcessMass (starts \ highExcessStarts starts g r T Y) g r T <= E) :
    M - E <= highExcessMass (highExcessStarts starts g r T Y) g r T := by
  have hsplit :=
    highExcessMass_eq_add_sdiff
      (s := starts) (t := highExcessStarts starts g r T Y)
      (g := g) (r := r) (T := T)
      (highExcessStarts_subset starts g r T Y)
  linarith

theorem highExcessMass_highPart_pos_of_mass_gt_low_bound
    {starts : Finset Nat} {g : Nat -> Nat} {r : Nat} {T Y E : ℝ}
    (hmass : E < highExcessMass starts g r T)
    (hlow :
      highExcessMass (starts \ highExcessStarts starts g r T Y) g r T <= E) :
    0 < highExcessMass (highExcessStarts starts g r T Y) g r T := by
  have hsplit :=
    highExcessMass_eq_add_sdiff
      (s := starts) (t := highExcessStarts starts g r T Y)
      (g := g) (r := r) (T := T)
      (highExcessStarts_subset starts g r T Y)
  linarith

theorem highExcessMass_highPart_ge_from_gapWindowMass
    {starts : Finset Nat} {g : Nat -> Nat} {r : Nat} {T Y M E Low : ℝ}
    (hM : M <= gapWindowMass starts g r)
    (hE : (starts.card : ℝ) * T <= E)
    (hlow :
      highExcessMass (starts \ highExcessStarts starts g r T Y) g r T <= Low) :
    M - E - Low <= highExcessMass (highExcessStarts starts g r T Y) g r T := by
  have hmass :
      M - E <= highExcessMass starts g r T :=
    highExcessMass_ge_of_gapWindowMass_ge_card_mul_le hM hE
  have hhigh :=
    highExcessMass_highPart_ge_sub_of_mass_ge_low_le
      (starts := starts) (g := g) (r := r) (T := T) (Y := Y)
      (M := M - E) (E := Low) hmass hlow
  linarith

/--
Finite, explicit-constant form of Lemma 21.1's pressure extraction.  The
mathematical content still required later is to prove the three displayed
hypotheses from the carry/gap recurrence and dyadic shell assumptions.
-/
theorem lemma21_1_pressureLowerBound_finite
    {starts : Finset Nat} {g : Nat -> Nat} {r : Nat} {T Y M E Low : ℝ}
    (hwindow : M <= gapWindowMass starts g r)
    (hthreshold : (starts.card : ℝ) * T <= E)
    (hlow :
      highExcessMass (starts \ highExcessStarts starts g r T Y) g r T <= Low) :
    M - E - Low <= highExcessMass (highExcessStarts starts g r T Y) g r T :=
  highExcessMass_highPart_ge_from_gapWindowMass hwindow hthreshold hlow

theorem highExcessStarts_nonempty_from_gapWindowMass
    {starts : Finset Nat} {g : Nat -> Nat} {r : Nat} {T Y M E Low : ℝ}
    (hM : M <= gapWindowMass starts g r)
    (hE : (starts.card : ℝ) * T <= E)
    (hgap : E + Low < M)
    (hlow :
      highExcessMass (starts \ highExcessStarts starts g r T Y) g r T <= Low) :
    (highExcessStarts starts g r T Y).Nonempty := by
  have hhigh :
      0 < highExcessMass (highExcessStarts starts g r T Y) g r T := by
    have hle :=
      highExcessMass_highPart_ge_from_gapWindowMass
        (starts := starts) (g := g) (r := r) (T := T) (Y := Y)
        (M := M) (E := E) (Low := Low) hM hE hlow
    linarith
  by_contra hnone
  have hempty : highExcessStarts starts g r T Y = ∅ := by
    ext k
    constructor
    · intro hk
      exact False.elim (hnone ⟨k, hk⟩)
    · intro hk
      simp at hk
  have hzero :
      highExcessMass (highExcessStarts starts g r T Y) g r T = 0 := by
    rw [hempty, highExcessMass_empty]
  linarith

theorem highExcessMass_le_card_mul_of_gapWindow_sub_le
    {starts : Finset Nat} {g : Nat -> Nat} {r : Nat} {T B : ℝ}
    (hB : 0 <= B)
    (h : ∀ k ∈ starts, (gapWindow g k r : ℝ) - T <= B) :
    highExcessMass starts g r T <= (starts.card : ℝ) * B :=
  highExcessMass_le_card_mul fun k hk =>
    windowExcess_le_of_gapWindow_sub_le (h k hk) hB

theorem exists_windowExcess_gt_of_card_mul_lt_highExcessMass
    {starts : Finset Nat} {g : Nat -> Nat} {r : Nat} {T Y : ℝ}
    (h : (starts.card : ℝ) * Y < highExcessMass starts g r T) :
    ∃ k ∈ starts, Y < windowExcess g k r T := by
  by_contra hnone
  have hle_point : ∀ k ∈ starts, windowExcess g k r T <= Y := by
    intro k hk
    by_contra hknot
    exact hnone ⟨k, hk, lt_of_not_ge hknot⟩
  have hle := highExcessMass_le_card_mul hle_point
  linarith

theorem highExcessStarts_nonempty_of_card_mul_lt_highExcessMass
    {starts : Finset Nat} {g : Nat -> Nat} {r : Nat} {T Y : ℝ}
    (h : (starts.card : ℝ) * Y < highExcessMass starts g r T) :
    (highExcessStarts starts g r T Y).Nonempty := by
  rcases exists_windowExcess_gt_of_card_mul_lt_highExcessMass h with
    ⟨k, hk, hkY⟩
  exact ⟨k, mem_highExcessStarts.2 ⟨hk, hkY.le⟩⟩

theorem exists_pos_windowExcess_of_highExcessMass_pos
    {starts : Finset Nat} {g : Nat -> Nat} {r : Nat} {T : ℝ}
    (hpos : 0 < highExcessMass starts g r T) :
    ∃ k ∈ starts, 0 < windowExcess g k r T := by
  by_contra hnone
  have hnonpos : ∀ k ∈ starts, windowExcess g k r T <= 0 := by
    intro k hk
    by_contra hgt
    exact hnone ⟨k, hk, lt_of_not_ge hgt⟩
  have hzero : ∀ k ∈ starts, windowExcess g k r T = 0 := by
    intro k hk
    have hnonneg := windowExcess_nonneg g k r T
    exact le_antisymm (hnonpos k hk) hnonneg
  have hmass_zero : highExcessMass starts g r T = 0 := by
    unfold highExcessMass
    exact sum_eq_zero hzero
  linarith

theorem highExcessStarts_zero_nonempty_of_highExcessMass_pos
    {starts : Finset Nat} {g : Nat -> Nat} {r : Nat} {T : ℝ}
    (hpos : 0 < highExcessMass starts g r T) :
    (highExcessStarts starts g r T 0).Nonempty := by
  rcases exists_pos_windowExcess_of_highExcessMass_pos hpos with
    ⟨k, hk, hkpos⟩
  exact ⟨k, mem_highExcessStarts.2 ⟨hk, hkpos.le⟩⟩

/-! ### Lemma 21.1 manuscript-level form -/

/--
**Lemma 21.1 (manuscript level pressure lower bound).**
This is the manuscript shape of `proof_v2.tex` Lemma 21.1.  Under
the carry/gap-derived bound `hM` saying that the raw window mass
minus the threshold accounting dominates `cpr * X * (r + 1) + Low`,
together with the low-excess upper bound `hlow`, the high-excess
mass on the high-excess starts is at least `cpr * X * (r + 1)`.

The hypotheses are exactly the package supplied by Appendix H.1
of `proof_v2.tex`:
* `hM` encodes the area-pressure conclusion
  `(starts.card) * T + cpr X (r+1) + Low ≤ gapWindowMass`
  obtained from the dyadic-shell counting + carry recurrence;
* `hlow` is the low-excess tail bound, supplied by the choice of
  `Y = ε L` and the gap bound `g_k ≤ L + O_Q(1)`.
-/
theorem lemma21_1_pressureLowerBound
    {starts : Finset Nat} {g : Nat -> Nat} {r : Nat}
    {T Y X cpr Low : ℝ}
    (hM : cpr * X * ((r : ℝ) + 1) + Low ≤
        gapWindowMass starts g r - (starts.card : ℝ) * T)
    (hlow :
      highExcessMass (starts \ highExcessStarts starts g r T Y) g r T <= Low) :
    cpr * X * ((r : ℝ) + 1) <=
      highExcessMass (highExcessStarts starts g r T Y) g r T := by
  have hbase :
      gapWindowMass starts g r - (starts.card : ℝ) * T <=
        highExcessMass starts g r T := by
    have h :=
      gapWindowMass_sub_card_mul_threshold_le_highExcessMass starts g r T
    linarith
  have hmass : cpr * X * ((r : ℝ) + 1) + Low <= highExcessMass starts g r T := by
    linarith
  have hsplit :=
    highExcessMass_highPart_ge_sub_of_mass_ge_low_le
      (starts := starts) (g := g) (r := r) (T := T) (Y := Y)
      (M := cpr * X * ((r : ℝ) + 1) + Low) (E := Low) hmass hlow
  linarith

/--
A nonemptiness corollary of `lemma21_1_pressureLowerBound`: under the
manuscript pressure hypotheses with `cpr X (r + 1) > 0`, the high-excess
starts form a nonempty set.  This is exactly the input used by
Appendix H to extract a positive-excess witness.
-/
theorem lemma21_1_highExcessStarts_nonempty
    {starts : Finset Nat} {g : Nat -> Nat} {r : Nat}
    {T Y X cpr Low : ℝ}
    (hpos : 0 < cpr * X * ((r : ℝ) + 1))
    (hM : cpr * X * ((r : ℝ) + 1) + Low <=
        gapWindowMass starts g r - (starts.card : ℝ) * T)
    (hlow :
      highExcessMass (starts \ highExcessStarts starts g r T Y) g r T <= Low) :
    (highExcessStarts starts g r T Y).Nonempty := by
  have hge := lemma21_1_pressureLowerBound (Y := Y) hM hlow
  by_contra hnone
  have hempty : highExcessStarts starts g r T Y = ∅ := by
    ext k
    constructor
    · intro hk; exact False.elim (hnone ⟨k, hk⟩)
    · intro hk; simp at hk
  have hzero :
      highExcessMass (highExcessStarts starts g r T Y) g r T = 0 := by
    rw [hempty, highExcessMass_empty]
  linarith

/-! ### Appendix H.4 vs H.5 contradiction (Pass 2) -/

/--
**`h4_vs_h5_contradiction` (manuscript Appendix H.4 ∧ H.5 contradiction).**

If a real quantity `M` is simultaneously bounded above by `Cstar · ξ · V`
(Theorem I.7 / H.4) and below by `cPr · V` (Lemma 21.1 / H.5), with
`Cstar · ξ < cPr` (the manuscript's numerical compatibility) and
`0 < V`, then `False`.

This is the pure algebra closure used by `theoremA_of_analytic_inputs`
in `TheoremA.lean`.
-/
theorem h4_vs_h5_contradiction
    {M Cstar ξ cPr V : ℝ}
    (hV : 0 < V)
    (hcompat : Cstar * ξ < cPr)
    (hUpper : M <= Cstar * ξ * V)
    (hLower : cPr * V <= M) : False := by
  nlinarith

/--
A `Decidable`-friendly variant of `h4_vs_h5_contradiction`: given the
two bounds and the numerical compatibility, the failure
`M_failure < cQ · X` cannot occur for the witness mass `M = (high
excess mass at parameters chosen by Appendix H)`.

This is used inside `theoremA_of_analytic_inputs` after `by_contra`.
-/
theorem not_failure_of_compatible_bounds
    {M Cstar ξ cPr V : ℝ}
    (hV : 0 < V)
    (hcompat : Cstar * ξ < cPr)
    (hUpper : M <= Cstar * ξ * V)
    (hLower : cPr * V <= M) : (False : Prop) :=
  h4_vs_h5_contradiction hV hcompat hUpper hLower

end

end Erdos260
