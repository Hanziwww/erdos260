import Mathlib
import Erdos260.Ledger
import Erdos260.Constants

/-!
# Appendix N.2: rolling-window variation and the variation-drop package

This module formalizes **Appendix N.2** of `proof_v4.tex` (the rolling-window
total variation `V_s`, the gap-difference identity, the discrete coarea bound,
the fixed-crossing-edge multiplicity, and the window-drop estimate `VarDrop`),
which underpins the window-drop bound (eq 2.3v) of
Theorem `thm:trt-chain-compression`.

The order-`s` window-sum sequence is modelled **abstractly** as a real sequence
`W : ℕ → ℝ` (so the module is independent of the sibling Appendix N event-fibre
module).  When `W` is the manuscript window sum `W_k^{(s)} = g_{k-s}+⋯+g_k`
derived from a gap sequence `g`, the gap-difference identity (N.12) and the
variation bound (N.13) are proved as *real, unconditional* theorems.

## What is formalized

* `Vs` — the rolling-window total variation `V_s(𝒦)` (eq N.11).
* `windowSum`, `windowSum_succ_sub` — the window sums and the **gap-difference
  identity** `W^{(s)}_{k+1} − W^{(s)}_k = g_{k+1} − g_{k-s}` (eq N.12), a real
  telescoping theorem.
* `Vs_windowSum_le_sum_gaps`, `windowVariation` — the **variation bound**
  `V_s ≤ ∑_k (g_{k+1}+g_{k-s}) ≤ 2 M ·|𝒦|`, the explicit finite form of
  `V_s ≤ C_Q X + O_Q(sL)` (eq N.13).  Real theorems.
* `crossingCount` (`N_u`), `crossingIndicator`, `integral_crossingIndicator`,
  `coarea`, `coarea_setIntegral_le`, `coarea_shift_setIntegral_le` — the
  **discrete coarea identity** `∫_ℝ N_u(W^{(s)}) du = V_s` (eq N.14) and the
  restriction `∫_{I_j} N_{T+Y} dT ≤ V_s` (eq N.15).  Real theorems built on the
  per-edge length identity `∫ 𝟙[u between a,b] du = |b−a|` and the sum/integral
  swap.
* `AnchorCollarData` — **Lemma N.2.0** (local-anchor collar, eq N.15a) encoded as
  a `conditional` hypothesis bundle (it depends on the finite local-closure
  alternatives L.1/L.6).
* `CrossingMultiplicityData` — **Lemma N.2.1** (fixed-crossing-edge multiplicity,
  eq N.16) encoded as a `conditional` hypothesis bundle (it depends on carry
  determinacy and the finite pivot labels of N.2.0); its summed corollary
  `CrossingMultiplicityData.sum_le_count` is a real theorem tying the bundle to
  `crossingCountReal`.
* `varDrop_le`, `WindowDropEstimateData.bound`, `variationDropMass_le_Vs`,
  `varDrop_le_explicit` — **Lemma N.2.2** (window-drop estimate, eq N.18 / 2.3v):
  the inequality CHAIN `VarDrop ≤ C_Q Y ∫_{I_j} N_{T+Y} dT ≤ C_Q Y V_s`, proved
  as a real theorem given the conditional fibre-integration first step, using the
  proven coarea bound (N.15) for the second step and connecting to
  `Erdos260.variationDropMass`.

There is no `sorry`, `axiom`, or `admit` anywhere in this file.
-/

namespace Erdos260

noncomputable section

open MeasureTheory Finset
open scoped ENNReal

namespace AppendixN

/-! ## N.2.a Rolling-window total variation `V_s` (eq N.11)

For an interval of terminal window indices `𝒦`,
`V_s(𝒦) = ∑_{k,k+1 ∈ 𝒦} |W_{k+1}^{(s)} − W_k^{(s)}|`  (eq N.11).

We model the order-`s` window sequence abstractly as `W : ℕ → ℝ` and take the
finite index set `K : Finset ℕ` to range over the edges `(k,k+1)`. -/

/-- **`V_s(𝒦)` (eq N.11).** The rolling-window total variation of the abstract
order-`s` window sequence `W` over the finite edge index set `K`. -/
def Vs (K : Finset ℕ) (W : ℕ → ℝ) : ℝ :=
  ∑ k ∈ K, |W (k + 1) - W k|

theorem Vs_nonneg (K : Finset ℕ) (W : ℕ → ℝ) : 0 ≤ Vs K W :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

@[simp] theorem Vs_empty (W : ℕ → ℝ) : Vs ∅ W = 0 := by
  simp [Vs]

/-- `V_s` is monotone in the edge index set (all terms are nonnegative). -/
theorem Vs_mono_subset {K₁ K₂ : Finset ℕ} (W : ℕ → ℝ) (h : K₁ ⊆ K₂) :
    Vs K₁ W ≤ Vs K₂ W :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun _ _ _ => abs_nonneg _

/-- A global additive shift of the window sequence leaves the total variation
unchanged (used for the `u = T + Y` restriction of the coarea bound, eq N.15). -/
theorem Vs_sub_const (K : Finset ℕ) (W : ℕ → ℝ) (Y : ℝ) :
    Vs K (fun n => W n - Y) = Vs K W := by
  unfold Vs
  refine Finset.sum_congr rfl fun k _ => ?_
  have h : W (k + 1) - Y - (W k - Y) = W (k + 1) - W k := by ring
  simp only [h]

/-! ## N.2.b Window sums and the gap-difference identity (eq N.12)

The manuscript window sum is `W_k^{(s)} = g_{k-s} + ⋯ + g_k`
(Preliminaries, around eq 0.1), and the rolling difference telescopes:
`W_{k+1}^{(s)} − W_k^{(s)} = g_{k+1} − g_{k-s}`  (eq N.12). -/

/-- **`W_k^{(s)}` (manuscript Preliminaries).** The order-`s` window sum of a gap
sequence `g`, `W_k^{(s)} = ∑_{i=k-s}^{k} g_i`. -/
def windowSum (g : ℕ → ℝ) (s k : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc (k - s) k, g i

/-- **Gap-difference identity (eq N.12).** For a full window (`s ≤ k`),
`W_{k+1}^{(s)} − W_k^{(s)} = g_{k+1} − g_{k-s}`.  A real telescoping theorem. -/
theorem windowSum_succ_sub (g : ℕ → ℝ) (s k : ℕ) (hsk : s ≤ k) :
    windowSum g s (k + 1) - windowSum g s k = g (k + 1) - g (k - s) := by
  unfold windowSum
  have hbot : k + 1 - s = (k - s) + 1 := by omega
  rw [hbot]
  set m := k - s with hm
  have e1 : Finset.Icc m k = insert m (Finset.Icc (m + 1) k) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have e2 : Finset.Icc (m + 1) (k + 1) = insert (k + 1) (Finset.Icc (m + 1) k) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have h1 : m ∉ Finset.Icc (m + 1) k := by simp only [Finset.mem_Icc]; omega
  have h2 : (k + 1) ∉ Finset.Icc (m + 1) k := by simp only [Finset.mem_Icc]; omega
  rw [e1, e2, Finset.sum_insert h1, Finset.sum_insert h2]
  ring

/-! ## N.2.c Variation bound (eq N.13)

Using the gap-difference identity and the dyadic gap bound `g_k ≤ L + O_Q(1)`
(here an abstract bound `g_k ≤ M`), `V_s ≤ ∑_k (g_{k+1}+g_{k-s}) ≤ C_Q X + O_Q(sL)`
(eq N.13).  The explicit finite form is `V_s ≤ 2 M ·|𝒦|`. -/

/-- **Variation bound, first form (eq N.13).** With nonnegative gaps and full
windows, `V_s ≤ ∑_{k∈K} (g_{k+1} + g_{k-s})`. -/
theorem Vs_windowSum_le_sum_gaps (g : ℕ → ℝ) (s : ℕ) (K : Finset ℕ)
    (hg : ∀ n, 0 ≤ g n) (hK : ∀ k ∈ K, s ≤ k) :
    Vs K (windowSum g s) ≤ ∑ k ∈ K, (g (k + 1) + g (k - s)) := by
  unfold Vs
  refine Finset.sum_le_sum fun k hk => ?_
  rw [windowSum_succ_sub g s k (hK k hk), abs_le]
  have h1 := hg (k + 1)
  have h2 := hg (k - s)
  constructor <;> linarith

/-- **Variation bound, explicit form (eq N.13).** With `0 ≤ g_k ≤ M` and full
windows, `V_s ≤ 2 M ·|𝒦|`.  This is the manuscript `V_s ≤ C_Q X + O_Q(sL)` in
explicit finite form, and is the tracker anchor for `N.2 rolling-window
variation V_s (N.11–N.13)`. -/
theorem windowVariation (g : ℕ → ℝ) (s : ℕ) (K : Finset ℕ) (M : ℝ)
    (hg : ∀ n, 0 ≤ g n) (hM : ∀ n, g n ≤ M) (hK : ∀ k ∈ K, s ≤ k) :
    Vs K (windowSum g s) ≤ 2 * M * (K.card : ℝ) := by
  calc Vs K (windowSum g s)
      ≤ ∑ k ∈ K, (g (k + 1) + g (k - s)) := Vs_windowSum_le_sum_gaps g s K hg hK
    _ ≤ ∑ _k ∈ K, (M + M) := by
        refine Finset.sum_le_sum fun k _ => ?_
        have h1 := hM (k + 1)
        have h2 := hM (k - s)
        linarith
    _ = 2 * M * (K.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **Windowed variation bound (eq N.13, dyadic-region form).**  The manuscript
gap bound `g_k ≤ L + O_Q(1)` is local: it holds "in the dyadic region", i.e. only
on the indices the order-`s` windows over `K` actually touch (`k - s` and `k + 1`
for `k ∈ K`), not globally.  This windowed version of `windowVariation` requires
the bound `≤ M` only on those touched indices and still concludes
`V_s ≤ 2 M·|𝒦|`.  This is the form dischargeable from the real carry-recurrence
hit-gap bound (`HitSequence.hitGap_le_of_shell_window`). -/
theorem windowVariation_of_windowBound (g : ℕ → ℝ) (s : ℕ) (K : Finset ℕ) (M : ℝ)
    (hg : ∀ n, 0 ≤ g n) (hK : ∀ k ∈ K, s ≤ k)
    (hMlo : ∀ k ∈ K, g (k - s) ≤ M) (hMhi : ∀ k ∈ K, g (k + 1) ≤ M) :
    Vs K (windowSum g s) ≤ 2 * M * (K.card : ℝ) := by
  calc Vs K (windowSum g s)
      ≤ ∑ k ∈ K, (g (k + 1) + g (k - s)) := Vs_windowSum_le_sum_gaps g s K hg hK
    _ ≤ ∑ _k ∈ K, (M + M) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have h1 := hMhi k hk
        have h2 := hMlo k hk
        linarith
    _ = 2 * M * (K.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-! ## N.2.d Discrete coarea identity (eq N.14, N.15)

For a real level `u`, `N_u(W^{(s)})` is the number of oriented crossing edges
`(k,k+1)` for which `u` lies strictly between `W_k^{(s)}` and `W_{k+1}^{(s)}`.
The discrete coarea identity is `∫_ℝ N_u(W^{(s)}) du = V_s` (eq N.14), and
restricting to `u = T + Y` gives `∫_{I_j} N_{T+Y}(W^{(s)}) dT ≤ V_s` (eq N.15). -/

/-- The open interval between `W k` and `W (k+1)` (the level set of edge
`e=(k,k+1)`). -/
def crossingSet (W : ℕ → ℝ) (k : ℕ) : Set ℝ :=
  Set.Ioo (min (W k) (W (k + 1))) (max (W k) (W (k + 1)))

/-- `𝟙_{X_e}` for the edge `e=(k,k+1)` at level `u`: the indicator that `u` lies
strictly between `W k` and `W (k+1)` (eq N.14, used in N.16). -/
def crossingIndicator (u : ℝ) (W : ℕ → ℝ) (k : ℕ) : ℝ :=
  (crossingSet W k).indicator (fun _ => 1) u

theorem crossingIndicator_nonneg (u : ℝ) (W : ℕ → ℝ) (k : ℕ) :
    0 ≤ crossingIndicator u W k :=
  Set.indicator_nonneg (fun _ _ => zero_le_one) u

/-- **`N_u(W^{(s)})` (eq N.14).** The number of oriented crossing edges `(k,k+1)`
in `K` whose window endpoints straddle the level `u`. -/
def crossingCount (u : ℝ) (W : ℕ → ℝ) (K : Finset ℕ) : ℕ := by
  classical
  exact (K.filter (fun k => min (W k) (W (k + 1)) < u ∧ u < max (W k) (W (k + 1)))).card

/-- `N_u` as a real number, for integration in `u`. -/
def crossingCountReal (u : ℝ) (W : ℕ → ℝ) (K : Finset ℕ) : ℝ :=
  (crossingCount u W K : ℝ)

/-- `N_u` is the finite sum of the per-edge crossing indicators `𝟙_{X_e}`. -/
theorem crossingCountReal_eq_sum_indicator (u : ℝ) (W : ℕ → ℝ) (K : Finset ℕ) :
    crossingCountReal u W K = ∑ k ∈ K, crossingIndicator u W k := by
  classical
  unfold crossingCountReal crossingCount crossingIndicator crossingSet
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h : min (W k) (W (k + 1)) < u ∧ u < max (W k) (W (k + 1))
  · rw [if_pos h, Nat.cast_one, Set.indicator_of_mem (Set.mem_Ioo.mpr h)]
  · rw [if_neg h, Nat.cast_zero, Set.indicator_of_notMem (fun hc => h (Set.mem_Ioo.mp hc))]

theorem crossingCountReal_nonneg (u : ℝ) (W : ℕ → ℝ) (K : Finset ℕ) :
    0 ≤ crossingCountReal u W K := by
  unfold crossingCountReal; exact Nat.cast_nonneg _

/-- Each per-edge crossing indicator is integrable (indicator of a finite-measure
open interval). -/
theorem crossingIndicator_integrable (W : ℕ → ℝ) (k : ℕ) :
    Integrable (fun u => crossingIndicator u W k) volume := by
  have hfin :
      volume (Set.Ioo (min (W k) (W (k + 1))) (max (W k) (W (k + 1)))) ≠ ⊤ := by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  have h : Integrable
      ((Set.Ioo (min (W k) (W (k + 1))) (max (W k) (W (k + 1)))).indicator
        (fun _ => (1 : ℝ))) volume := by
    rw [integrable_indicator_iff measurableSet_Ioo]
    exact integrableOn_const hfin
  simpa only [crossingIndicator, crossingSet] using h

theorem crossingCountReal_integrable (W : ℕ → ℝ) (K : Finset ℕ) :
    Integrable (fun u => crossingCountReal u W K) volume := by
  have h : (fun u => crossingCountReal u W K)
        = fun u => ∑ k ∈ K, crossingIndicator u W k :=
    funext fun u => crossingCountReal_eq_sum_indicator u W K
  rw [h]
  exact integrable_finset_sum K fun k _ => crossingIndicator_integrable W k

/-- **Per-edge length identity.** `∫_ℝ 𝟙[u between W k, W (k+1)] du = |W (k+1) − W k|`,
the length of the open interval between the two window endpoints. -/
theorem integral_crossingIndicator (W : ℕ → ℝ) (k : ℕ) :
    ∫ u, crossingIndicator u W k ∂volume = |W (k + 1) - W k| := by
  unfold crossingIndicator crossingSet
  rw [integral_indicator_const (1 : ℝ) measurableSet_Ioo, smul_eq_mul, mul_one,
      measureReal_def, Real.volume_Ioo,
      ENNReal.toReal_ofReal (sub_nonneg.mpr min_le_max), max_sub_min_eq_abs, abs_sub_comm]

/-- **Discrete coarea identity (eq N.14).** `∫_ℝ N_u(W^{(s)}) du = V_s`: the
integral of the crossing count equals the rolling-window total variation.  Proved
via the per-edge length identity and the finite sum/integral swap. -/
theorem coarea (W : ℕ → ℝ) (K : Finset ℕ) :
    ∫ u, crossingCountReal u W K ∂volume = Vs K W := by
  calc ∫ u, crossingCountReal u W K ∂volume
      = ∫ u, ∑ k ∈ K, crossingIndicator u W k ∂volume := by
        simp only [crossingCountReal_eq_sum_indicator]
    _ = ∑ k ∈ K, ∫ u, crossingIndicator u W k ∂volume :=
        integral_finset_sum K fun k _ => crossingIndicator_integrable W k
    _ = ∑ k ∈ K, |W (k + 1) - W k| :=
        Finset.sum_congr rfl fun k _ => integral_crossingIndicator W k
    _ = Vs K W := rfl

/-- **Coarea bound on a level set (eq N.14 restricted).** For any level set `A`,
`∫_{u ∈ A} N_u(W^{(s)}) du ≤ V_s`. -/
theorem coarea_setIntegral_le (W : ℕ → ℝ) (K : Finset ℕ) (A : Set ℝ) :
    ∫ u in A, crossingCountReal u W K ∂volume ≤ Vs K W := by
  calc ∫ u in A, crossingCountReal u W K ∂volume
      ≤ ∫ u, crossingCountReal u W K ∂volume :=
        setIntegral_le_integral (crossingCountReal_integrable W K)
          (Filter.Eventually.of_forall fun u => crossingCountReal_nonneg u W K)
    _ = Vs K W := coarea W K

/-- Shifting the level by `Y` shifts the window sequence by `−Y` (eq N.15 setup). -/
theorem crossingIndicator_add_shift (u Y : ℝ) (W : ℕ → ℝ) (k : ℕ) :
    crossingIndicator (u + Y) W k = crossingIndicator u (fun n => W n - Y) k := by
  unfold crossingIndicator crossingSet
  rw [Set.indicator_apply, Set.indicator_apply]
  have hiff :
      (u + Y ∈ Set.Ioo (min (W k) (W (k + 1))) (max (W k) (W (k + 1))))
        ↔ (u ∈ Set.Ioo (min (W k - Y) (W (k + 1) - Y))
                       (max (W k - Y) (W (k + 1) - Y))) := by
    simp only [Set.mem_Ioo]
    rcases le_total (W k) (W (k + 1)) with hle | hle
    · rw [min_eq_left hle, max_eq_right hle,
          min_eq_left (show W k - Y ≤ W (k + 1) - Y by linarith),
          max_eq_right (show W k - Y ≤ W (k + 1) - Y by linarith)]
      constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩
    · rw [min_eq_right hle, max_eq_left hle,
          min_eq_right (show W (k + 1) - Y ≤ W k - Y by linarith),
          max_eq_left (show W (k + 1) - Y ≤ W k - Y by linarith)]
      constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩
  simp only [hiff]

theorem crossingCountReal_add_shift (u Y : ℝ) (W : ℕ → ℝ) (K : Finset ℕ) :
    crossingCountReal (u + Y) W K = crossingCountReal u (fun n => W n - Y) K := by
  rw [crossingCountReal_eq_sum_indicator, crossingCountReal_eq_sum_indicator]
  exact Finset.sum_congr rfl fun k _ => crossingIndicator_add_shift u Y W k

/-- **Coarea bound at level `T + Y` (eq N.15).** `∫_{I_j} N_{T+Y}(W^{(s)}) dT ≤ V_s`.
Obtained from the level-set coarea bound applied to the `−Y`-shifted window. -/
theorem coarea_shift_setIntegral_le (W : ℕ → ℝ) (K : Finset ℕ) (Y : ℝ) (A : Set ℝ) :
    ∫ T in A, crossingCountReal (T + Y) W K ∂volume ≤ Vs K W := by
  calc ∫ T in A, crossingCountReal (T + Y) W K ∂volume
      = ∫ T in A, crossingCountReal T (fun n => W n - Y) K ∂volume := by
        simp only [crossingCountReal_add_shift]
    _ ≤ Vs K (fun n => W n - Y) := coarea_setIntegral_le (fun n => W n - Y) K A
    _ = Vs K W := Vs_sub_const K W Y

/-! ## Lemma N.2.0 Local-anchor collar (eq N.15a) — CONDITIONAL

If the priority pivot anchor of a live Return/Run/Tower hand-off has relative
coordinate `|a_piv| > C_×(Q)` with respect to the first crossing edge `e`, then
the event state is assigned *earlier* (to DensePack/Progress/Endpoint/bounded/CNL),
not to the variation-drop subfibre of `e`.  Equivalently, any state actually
assigned to `e` satisfies `|a_piv| ≤ C_×(Q)`.

The proof in `proof_v4.tex` (the finite case analysis N.15b/N.15c) uses the local
finite-closure alternatives of Appendix L.  We therefore encode the conclusion as
a `conditional` hypothesis bundle. -/

/-- **Lemma N.2.0 input bundle (eq N.15a) — CONDITIONAL.** The local-anchor collar
constant `C_×(Q)` and the property that any state assigned to the first
variation-drop edge has bounded local anchor coordinate. -/
structure AnchorCollarData (State : Type*) where
  /-- The collar constant `C_×(Q)`. -/
  Cx : ℝ
  Cx_pos : 0 < Cx
  /-- The local anchor coordinate `a_piv` relative to the crossing edge. -/
  anchorCoord : State → ℝ
  /-- The event "this state is assigned to the variation-drop subfibre of its
  first crossing edge". -/
  assignedToFirstEdge : State → Prop
  /-- Lemma N.2.0 (eq N.15a): a state assigned to the first variation-drop edge has
  `|a_piv| ≤ C_×(Q)`. -/
  collar : ∀ ζ, assignedToFirstEdge ζ → |anchorCoord ζ| ≤ Cx

/-- The collar bound (eq N.15a) extracted from the bundle. -/
theorem AnchorCollarData.anchor_bounded {State : Type*} (D : AnchorCollarData State)
    {ζ : State} (h : D.assignedToFirstEdge ζ) : |D.anchorCoord ζ| ≤ D.Cx :=
  D.collar ζ h

/-! ## Lemma N.2.1 Fixed-crossing-edge multiplicity (eq N.16) — CONDITIONAL

For every fixed threshold `T` and oriented order-`s` window edge `e`, the drop
subfibres assigned to `e` satisfy `∑_b μ_T(Ω^V_{b,e}(T)) ≤ C_Q · 𝟙_{X_e(T)}`
(eq N.16).  The manuscript proof uses the carry recurrence (carry determinacy),
the finite first-crossing record `Π_e` (eq N.17), and the finite pivot labels of
Lemma N.2.0.  We encode the conclusion as a `conditional` hypothesis bundle, and
prove its summed corollary (the per-`T` input to N.2.2) as a real theorem. -/

/-- **Lemma N.2.1 input bundle (eq N.16) — CONDITIONAL.** At a fixed threshold `T`,
for each edge `e` (indexed by `k`) the drop subfibre masses `μ_T(Ω^V_{b,e})` over
branches `b` are bounded by `C_Q · 𝟙_{X_e}`. -/
structure CrossingMultiplicityData (Branch : Type*) where
  /-- The (finite) branch family. -/
  branches : Finset Branch
  /-- The multiplicity constant `C_Q`. -/
  C : ℝ
  C_nonneg : 0 ≤ C
  /-- `μ_T(Ω^V_{b,e})`: the drop subfibre mass for branch `b` and edge `e`. -/
  dropMass : Branch → ℕ → ℝ
  dropMass_nonneg : ∀ b e, 0 ≤ dropMass b e
  /-- `𝟙_{X_e(T)}`: the per-edge crossing indicator (nonnegative; `0`/`1` valued
  in applications). -/
  crossingIndic : ℕ → ℝ
  crossingIndic_nonneg : ∀ e, 0 ≤ crossingIndic e
  /-- Lemma N.2.1 (eq N.16): per-edge multiplicity bound. -/
  multiplicity_le : ∀ e, (∑ b ∈ branches, dropMass b e) ≤ C * crossingIndic e

/-- Summed over a window-index set, `∑_{e∈K} ∑_b μ_T(Ω^V_{b,e}) ≤ C_Q ∑_{e∈K} 𝟙_{X_e}`.
A real consequence of the N.2.1 bundle. -/
theorem CrossingMultiplicityData.sum_le {Branch : Type*}
    (D : CrossingMultiplicityData Branch) (K : Finset ℕ) :
    (∑ e ∈ K, ∑ b ∈ D.branches, D.dropMass b e) ≤ D.C * ∑ e ∈ K, D.crossingIndic e := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun e _ => D.multiplicity_le e

/-- **N.2.1 summed against the crossing count.** If the per-edge indicators are the
genuine crossing indicators at level `T + Y` for the window `W`, then
`∑_{e∈K} ∑_b μ_T(Ω^V_{b,e}) ≤ C_Q · N_{T+Y}(W^{(s)})`.  This is the per-`T` input
to the window-drop estimate (the displayed inequality in the N.2.2 proof). -/
theorem CrossingMultiplicityData.sum_le_count {Branch : Type*}
    (D : CrossingMultiplicityData Branch) (K : Finset ℕ) (T Y : ℝ) (W : ℕ → ℝ)
    (hindic : ∀ e, D.crossingIndic e = crossingIndicator (T + Y) W e) :
    (∑ e ∈ K, ∑ b ∈ D.branches, D.dropMass b e) ≤ D.C * crossingCountReal (T + Y) W K := by
  have hsum : (∑ e ∈ K, D.crossingIndic e) = crossingCountReal (T + Y) W K := by
    rw [crossingCountReal_eq_sum_indicator]
    exact Finset.sum_congr rfl fun e _ => hindic e
  rw [← hsum]
  exact D.sum_le K

/-- **Multiplicity counting core (faithful).** A per-branch mass `f` supported on
at most `C` branches (`support`, with `f = 0` off it) and pointwise `≤ M` sums to
at most `C · M`.  This is the combinatorial heart of the N.2.1 multiplicity bound:
the `C_Q`-to-one first-crossing record (the support) times the unit
represented-edge mass `M`. -/
theorem multiplicity_count_bound {Branch : Type*} (branches support : Finset Branch)
    (f : Branch → ℝ) (C M : ℝ)
    (hM_nonneg : 0 ≤ M)
    (hf_le : ∀ b, f b ≤ M)
    (hsupp : support ⊆ branches)
    (hzero : ∀ b ∈ branches, b ∉ support → f b = 0)
    (hcard : (support.card : ℝ) ≤ C) :
    (∑ b ∈ branches, f b) ≤ C * M := by
  have hsplit : (∑ b ∈ branches, f b) = ∑ b ∈ support, f b :=
    (Finset.sum_subset hsupp hzero).symm
  rw [hsplit]
  calc (∑ b ∈ support, f b)
      ≤ ∑ _b ∈ support, M := Finset.sum_le_sum fun b _ => hf_le b
    _ = (support.card : ℝ) * M := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ C * M := mul_le_mul_of_nonneg_right hcard hM_nonneg

/-- **N.2.1 from the first-crossing record (faithful derivation).** Builds the
`CrossingMultiplicityData` bundle — in particular **deriving** the per-edge
multiplicity bound `∑_b μ_T(Ω^V_{b,e}) ≤ C · 𝟙_{X_e}` rather than assuming it —
from the two genuine manuscript facts:

* `hlift_le` — each variation-drop lift has mass at most the unit
  represented-edge mass (Definition K.1.2 / eq N.17 normalization);
* `hcard` (with `support`/`hzero`) — for each edge `e` the first-crossing record
  `Π_e` is `C`-to-one, so at most `C` branches carry nonzero drop mass.

The `≤ C · 𝟙` derivation is now the faithful `multiplicity_count_bound`; only the
support identification and the `C`-to-one count remain conditional (carry
determinacy, Lemma N.2.0 finite labels). -/
def CrossingMultiplicityData.ofFirstCrossingRecord {Branch : Type*}
    (branches : Finset Branch) (C : ℝ) (hC : 0 ≤ C)
    (dropMass : Branch → ℕ → ℝ) (hdrop_nonneg : ∀ b e, 0 ≤ dropMass b e)
    (crossingIndic : ℕ → ℝ) (hindic_nonneg : ∀ e, 0 ≤ crossingIndic e)
    (hlift_le : ∀ b e, dropMass b e ≤ crossingIndic e)
    (support : ℕ → Finset Branch)
    (hsupp : ∀ e, support e ⊆ branches)
    (hzero : ∀ e, ∀ b ∈ branches, b ∉ support e → dropMass b e = 0)
    (hcard : ∀ e, ((support e).card : ℝ) ≤ C) :
    CrossingMultiplicityData Branch where
  branches := branches
  C := C
  C_nonneg := hC
  dropMass := dropMass
  dropMass_nonneg := hdrop_nonneg
  crossingIndic := crossingIndic
  crossingIndic_nonneg := hindic_nonneg
  multiplicity_le := fun e =>
    multiplicity_count_bound branches (support e) (fun b => dropMass b e)
      C (crossingIndic e) (hindic_nonneg e) (fun b => hlift_le b e)
      (hsupp e) (hzero e) (hcard e)

/-! ## Lemma N.2.2 Window-drop estimate (eq N.18 / 2.3v)

The total residual variation-drop mass satisfies
`VarDrop ≤ C_Q Y ∫_{I_j} N_{T+Y}(W^{(s)}) dT ≤ C_Q Y V_s = o(sX|I_j|)` (eq N.18).

The **second** inequality is the coarea bound (N.15), proved above unconditionally.
The **first** inequality bundles the active-residual-multiplier bound `≤ C_Q Y`
(Definition K.1.2) with the fixed-`T` multiplicity (N.2.1) integrated in `T`; this
fibre-integration step is the deep input and is taken as a hypothesis.  The
inequality chain itself is a real theorem. -/

/-- **Lemma N.2.2 inequality chain (eq N.18 / 2.3v).** Given the (conditional)
first inequality `VarDrop ≤ C_Q Y ∫_{A} N_{T+Y} dT`, the proven coarea bound (N.15)
yields `VarDrop ≤ C_Q Y V_s`.  Tracker anchor for `Lemma N.2.2`. -/
theorem varDrop_le (VarDrop CQ Y : ℝ) (W : ℕ → ℝ) (K : Finset ℕ) (A : Set ℝ)
    (hCQY : 0 ≤ CQ * Y)
    (h1 : VarDrop ≤ CQ * Y * ∫ T in A, crossingCountReal (T + Y) W K ∂volume) :
    VarDrop ≤ CQ * Y * Vs K W :=
  h1.trans (mul_le_mul_of_nonneg_left (coarea_shift_setIntegral_le W K Y A) hCQY)

/-- The shifted crossing count is integrable on any measurable threshold set. -/
theorem crossingCountReal_shift_integrableOn (W : ℕ → ℝ) (K : Finset ℕ)
    (Y : ℝ) (A : Set ℝ) :
    IntegrableOn (fun T => crossingCountReal (T + Y) W K) A volume := by
  have hglobal :
      Integrable (fun T => crossingCountReal T (fun n => W n - Y) K) volume :=
    crossingCountReal_integrable (fun n => W n - Y) K
  have heq :
      (fun T => crossingCountReal (T + Y) W K)
        = fun T => crossingCountReal T (fun n => W n - Y) K :=
    funext fun T => crossingCountReal_add_shift T Y W K
  rw [heq]
  exact hglobal.integrableOn

/--
**N.2.2 first-inequality bridge from a drop-density integrand.**

If the total variation-drop mass is controlled by the residual multiplier times
an integrated drop-density, and the fixed-`T` N.2.1 multiplicity estimate gives
`dropDensity T ≤ N_{T+Y}` on the threshold set, then Lean supplies the integrated
first inequality of N.2.2:
`VarDrop ≤ C_Q Y ∫ N_{T+Y}`.
-/
theorem varDrop_firstIneq_from_dropDensity_bound
    (VarDrop CQ Y : ℝ) (dropDensity : ℝ → ℝ)
    (W : ℕ → ℝ) (K : Finset ℕ) (A : Set ℝ)
    (hCQY : 0 ≤ CQ * Y)
    (hA : MeasurableSet A)
    (hdrop_int : IntegrableOn dropDensity A volume)
    (hvar :
      VarDrop ≤ CQ * Y * ∫ T in A, dropDensity T ∂volume)
    (hpoint :
      ∀ T ∈ A, dropDensity T ≤ crossingCountReal (T + Y) W K) :
    VarDrop ≤ CQ * Y * ∫ T in A, crossingCountReal (T + Y) W K ∂volume := by
  have hcount_int := crossingCountReal_shift_integrableOn W K Y A
  have hmono :
      ∫ T in A, dropDensity T ∂volume
        ≤ ∫ T in A, crossingCountReal (T + Y) W K ∂volume :=
    MeasureTheory.setIntegral_mono_on hdrop_int hcount_int hA hpoint
  exact hvar.trans (mul_le_mul_of_nonneg_left hmono hCQY)

/--
**Scaled N.2.2 first-inequality bridge from a drop-density integrand.**

This is the manuscript form in which the residual multiplier and the
fixed-threshold N.2.1 multiplicity constant are exposed separately:
if `VarDrop ≤ Cmul Y ∫ dropDensity` and
`dropDensity T ≤ Cfiber · N_{T+Y}`, then the first inequality holds with
the product constant `Cmul · Cfiber`.
-/
theorem varDrop_firstIneq_from_scaled_dropDensity_bound
    (VarDrop Cmul Cfiber Y : ℝ) (dropDensity : ℝ → ℝ)
    (W : ℕ → ℝ) (K : Finset ℕ) (A : Set ℝ)
    (hCmulY : 0 ≤ Cmul * Y)
    (hA : MeasurableSet A)
    (hdrop_int : IntegrableOn dropDensity A volume)
    (hvar :
      VarDrop ≤ Cmul * Y * ∫ T in A, dropDensity T ∂volume)
    (hpoint :
      ∀ T ∈ A, dropDensity T ≤ Cfiber * crossingCountReal (T + Y) W K) :
    VarDrop ≤ (Cmul * Cfiber) * Y *
      ∫ T in A, crossingCountReal (T + Y) W K ∂volume := by
  have hcount_int := crossingCountReal_shift_integrableOn W K Y A
  have hcount_scaled_int :
      IntegrableOn (fun T => Cfiber * crossingCountReal (T + Y) W K) A volume :=
    hcount_int.const_mul Cfiber
  have hmono :
      ∫ T in A, dropDensity T ∂volume
        ≤ ∫ T in A, Cfiber * crossingCountReal (T + Y) W K ∂volume :=
    MeasureTheory.setIntegral_mono_on hdrop_int hcount_scaled_int hA hpoint
  have hmono' :
      ∫ T in A, dropDensity T ∂volume
        ≤ Cfiber * ∫ T in A, crossingCountReal (T + Y) W K ∂volume := by
    simpa [MeasureTheory.integral_const_mul] using hmono
  have hscaled :
      Cmul * Y * ∫ T in A, dropDensity T ∂volume
        ≤ Cmul * Y *
          (Cfiber * ∫ T in A, crossingCountReal (T + Y) W K ∂volume) :=
    mul_le_mul_of_nonneg_left hmono' hCmulY
  exact hvar.trans (by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled)

/--
**Scaled N.2.2 window-drop bound from a drop-density integrand.**

This composes the scaled first-inequality bridge with coarea, exposing the two
constant factors used in the manuscript proof before absorbing them into the
single `C_Q`-style product constant.
-/
theorem varDrop_le_from_scaled_dropDensity_bound
    (VarDrop Cmul Cfiber Y : ℝ) (dropDensity : ℝ → ℝ)
    (W : ℕ → ℝ) (K : Finset ℕ) (A : Set ℝ)
    (hCmulY : 0 ≤ Cmul * Y)
    (hCfiber : 0 ≤ Cfiber)
    (hA : MeasurableSet A)
    (hdrop_int : IntegrableOn dropDensity A volume)
    (hvar :
      VarDrop ≤ Cmul * Y * ∫ T in A, dropDensity T ∂volume)
    (hpoint :
      ∀ T ∈ A, dropDensity T ≤ Cfiber * crossingCountReal (T + Y) W K) :
    VarDrop ≤ (Cmul * Cfiber) * Y * Vs K W := by
  have htotal : 0 ≤ (Cmul * Cfiber) * Y := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using mul_nonneg hCfiber hCmulY
  exact varDrop_le VarDrop (Cmul * Cfiber) Y W K A htotal
    (varDrop_firstIneq_from_scaled_dropDensity_bound
      VarDrop Cmul Cfiber Y dropDensity W K A hCmulY hA hdrop_int hvar hpoint)

/--
Scale the explicit N.13 variation bound by the active window-drop multiplier.

This is the algebraic bridge used after N.2.2: once
`Vs K (windowSum g s) ≤ 2 M |K|`, the corresponding window-drop term is bounded
by the same explicit right-hand side.
-/
theorem scaled_windowTerm_le_explicit_windowBound
    (C Y M : ℝ) (g : ℕ → ℝ) (s : ℕ) (K : Finset ℕ)
    (hCY : 0 ≤ C * Y)
    (hg : ∀ n, 0 ≤ g n)
    (hKidx : ∀ k ∈ K, s ≤ k)
    (hMlo : ∀ k ∈ K, g (k - s) ≤ M)
    (hMhi : ∀ k ∈ K, g (k + 1) ≤ M) :
    C * Y * Vs K (windowSum g s)
      ≤ C * Y * (2 * M * (K.card : ℝ)) :=
  mul_le_mul_of_nonneg_left
    (windowVariation_of_windowBound g s K M hg hKidx hMlo hMhi) hCY

/--
Scaled drop-density window drop with the explicit N.13 variation bound.

This is the direct composition of the scaled first inequality, coarea, and the
local dyadic-region variation estimate `Vs ≤ 2M|K|`.
-/
theorem varDrop_le_from_scaled_dropDensity_bound_explicitWindow
    (VarDrop Cmul Cfiber Y M : ℝ) (dropDensity : ℝ → ℝ)
    (g : ℕ → ℝ) (s : ℕ) (K : Finset ℕ) (A : Set ℝ)
    (hCmulY : 0 ≤ Cmul * Y)
    (hCfiber : 0 ≤ Cfiber)
    (hA : MeasurableSet A)
    (hdrop_int : IntegrableOn dropDensity A volume)
    (hvar :
      VarDrop ≤ Cmul * Y * ∫ T in A, dropDensity T ∂volume)
    (hpoint :
      ∀ T ∈ A,
        dropDensity T ≤
          Cfiber * crossingCountReal (T + Y) (windowSum g s) K)
    (hg : ∀ n, 0 ≤ g n)
    (hKidx : ∀ k ∈ K, s ≤ k)
    (hMlo : ∀ k ∈ K, g (k - s) ≤ M)
    (hMhi : ∀ k ∈ K, g (k + 1) ≤ M) :
    VarDrop ≤ (Cmul * Cfiber) * Y * (2 * M * (K.card : ℝ)) := by
  have hdrop :
      VarDrop ≤ (Cmul * Cfiber) * Y * Vs K (windowSum g s) :=
    varDrop_le_from_scaled_dropDensity_bound VarDrop Cmul Cfiber Y
      dropDensity (windowSum g s) K A hCmulY hCfiber hA hdrop_int hvar hpoint
  have htotal : 0 ≤ (Cmul * Cfiber) * Y := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using mul_nonneg hCfiber hCmulY
  exact hdrop.trans
    (scaled_windowTerm_le_explicit_windowBound (Cmul * Cfiber) Y M g s K
      htotal hg hKidx hMlo hMhi)

/--
**N.2.2 window-drop bound from a drop-density integrand.**

This combines `varDrop_firstIneq_from_dropDensity_bound` with the coarea bound.
The remaining hypotheses are precisely the integrated residual-density
domination and the fixed-`T` multiplicity comparison.
-/
theorem varDrop_le_from_dropDensity_bound
    (VarDrop CQ Y : ℝ) (dropDensity : ℝ → ℝ)
    (W : ℕ → ℝ) (K : Finset ℕ) (A : Set ℝ)
    (hCQY : 0 ≤ CQ * Y)
    (hA : MeasurableSet A)
    (hdrop_int : IntegrableOn dropDensity A volume)
    (hvar :
      VarDrop ≤ CQ * Y * ∫ T in A, dropDensity T ∂volume)
    (hpoint :
      ∀ T ∈ A, dropDensity T ≤ crossingCountReal (T + Y) W K) :
    VarDrop ≤ CQ * Y * Vs K W :=
  varDrop_le VarDrop CQ Y W K A hCQY
    (varDrop_firstIneq_from_dropDensity_bound
      VarDrop CQ Y dropDensity W K A hCQY hA hdrop_int hvar hpoint)

/-- **Lemma N.2.2 input bundle.** Packages the window-drop residual mass with the
nonnegative residual multiplier `C_Q Y` and the conditional fibre-integration
first inequality of eq N.18. -/
structure WindowDropEstimateData where
  /-- `VarDrop_{s,j}(Y)`: the total residual variation-drop mass. -/
  varDrop : ℝ
  /-- The multiplicity constant `C_Q`. -/
  CQ : ℝ
  /-- The active floor / residual multiplier scale `Y`. -/
  Y : ℝ
  /-- The (abstract order-`s`) window sequence `W^{(s)}`. -/
  W : ℕ → ℝ
  /-- The window-edge index set. -/
  K : Finset ℕ
  /-- The threshold interval `I_j`. -/
  Ij : Set ℝ
  CQY_nonneg : 0 ≤ CQ * Y
  /-- First inequality of eq N.18 (residual multiplier `≤ C_Q Y` + N.2.1 integrated). -/
  firstIneq :
    varDrop ≤ CQ * Y * ∫ T in Ij, crossingCountReal (T + Y) W K ∂volume

/-- Build the bundled N.2.2 input from scaled drop-density data. -/
def WindowDropEstimateData.ofScaledDropDensityBound
    (VarDrop Cmul Cfiber Y : ℝ) (dropDensity : ℝ → ℝ)
    (W : ℕ → ℝ) (K : Finset ℕ) (A : Set ℝ)
    (hCmulY : 0 ≤ Cmul * Y)
    (hCfiber : 0 ≤ Cfiber)
    (hA : MeasurableSet A)
    (hdrop_int : IntegrableOn dropDensity A volume)
    (hvar :
      VarDrop ≤ Cmul * Y * ∫ T in A, dropDensity T ∂volume)
    (hpoint :
      ∀ T ∈ A, dropDensity T ≤ Cfiber * crossingCountReal (T + Y) W K) :
    WindowDropEstimateData where
  varDrop := VarDrop
  CQ := Cmul * Cfiber
  Y := Y
  W := W
  K := K
  Ij := A
  CQY_nonneg := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using mul_nonneg hCfiber hCmulY
  firstIneq :=
    varDrop_firstIneq_from_scaled_dropDensity_bound VarDrop Cmul Cfiber Y
      dropDensity W K A hCmulY hA hdrop_int hvar hpoint

/-- **Lemma N.2.2 (eq N.18 / 2.3v), bundled form.** `VarDrop ≤ C_Q Y V_s`. -/
theorem WindowDropEstimateData.bound (D : WindowDropEstimateData) :
    D.varDrop ≤ D.CQ * D.Y * Vs D.K D.W :=
  varDrop_le D.varDrop D.CQ D.Y D.W D.K D.Ij D.CQY_nonneg D.firstIneq

/-- **Ledger tie-in.** The `Erdos260.variationDropMass` of a finite output family
obeys the window-drop estimate `VarDrop ≤ C_Q Y V_s` (eq N.18), given the
conditional first inequality. -/
theorem variationDropMass_le_Vs (objects : Finset OutputObjectV4)
    (weight : OutputObjectV4 → ℝ) (CQ Y : ℝ) (W : ℕ → ℝ) (K : Finset ℕ) (A : Set ℝ)
    (hCQY : 0 ≤ CQ * Y)
    (h1 : variationDropMass objects weight ≤
            CQ * Y * ∫ T in A, crossingCountReal (T + Y) W K ∂volume) :
    variationDropMass objects weight ≤ CQ * Y * Vs K W :=
  varDrop_le _ CQ Y W K A hCQY h1

/-- **Window-drop estimate, explicit form.** Combining N.2.2 with the variation
bound N.13 gives the explicit `VarDrop ≤ C_Q Y · 2 M ·|𝒦|`, the finite analog of
`VarDrop = o(sX|I_j|)`. -/
theorem varDrop_le_explicit (VarDrop CQ Y M : ℝ) (g : ℕ → ℝ) (s : ℕ) (K : Finset ℕ)
    (A : Set ℝ) (hCQY : 0 ≤ CQ * Y) (hg : ∀ n, 0 ≤ g n) (hM : ∀ n, g n ≤ M)
    (hKidx : ∀ k ∈ K, s ≤ k)
    (h1 : VarDrop ≤
            CQ * Y * ∫ T in A, crossingCountReal (T + Y) (windowSum g s) K ∂volume) :
    VarDrop ≤ CQ * Y * (2 * M * (K.card : ℝ)) :=
  (varDrop_le VarDrop CQ Y (windowSum g s) K A hCQY h1).trans
    (mul_le_mul_of_nonneg_left (windowVariation g s K M hg hM hKidx) hCQY)

/-- **Window-drop estimate, local dyadic-region form.**  This is the version
used after the carry hit-gap bound: the gap upper bound `g ≤ M` is required only
on the indices touched by the order-`s` windows over `K`, namely `k - s` and
`k + 1`.  It combines N.2.2 with the local variation estimate N.13. -/
theorem varDrop_le_explicit_windowBound (VarDrop CQ Y M : ℝ) (g : ℕ -> ℝ)
    (s : ℕ) (K : Finset ℕ) (A : Set ℝ)
    (hCQY : 0 ≤ CQ * Y) (hg : ∀ n, 0 ≤ g n)
    (hKidx : ∀ k ∈ K, s ≤ k)
    (hMlo : ∀ k ∈ K, g (k - s) ≤ M)
    (hMhi : ∀ k ∈ K, g (k + 1) ≤ M)
    (h1 : VarDrop ≤
            CQ * Y * ∫ T in A, crossingCountReal (T + Y) (windowSum g s) K ∂volume) :
    VarDrop ≤ CQ * Y * (2 * M * (K.card : ℝ)) :=
    (varDrop_le VarDrop CQ Y (windowSum g s) K A hCQY h1).trans
    (mul_le_mul_of_nonneg_left
      (windowVariation_of_windowBound g s K M hg hKidx hMlo hMhi) hCQY)

/-! ## N.2.c′ Sharp and additive forms of the variation bound (eq N.12 → N.13)

The variation bound `Vs_windowSum_le_sum_gaps` (N.13) drops the cancellation
inside `|·|` and replaces the two shifted index sets by the running index `k`.
The two theorems below recover the two manuscript renderings of N.13 that the
multiplicative `windowVariation` form (`V_s ≤ 2 M ·|𝒦|`) discards:

* the **sharp identity** `V_s = ∑_k |g_{k+1} − g_{k-s}|`, the exact summed
  gap-difference identity (eq N.12 summed over the block); and
* the **additive block bound** `V_s ≤ (forward block) + (trailing block)` on a
  *consecutive* window-edge block `𝒦 = Ico i (i+n)`, where each block is a gap
  sum over a *consecutive* index range — the manuscript's additive
  `V_s ≤ C_Q X + O_Q(sL)` form (each consecutive-range gap sum telescopes against
  a hit sequence to a span).  Both are pure telescoping/reindexing theorems. -/

/-- **Sharp gap-difference variation identity (eq N.12 summed).** For a
window-edge index set `K` with full windows (`s ≤ k` for every `k ∈ K`), the
rolling-window total variation of the order-`s` window sequence
`W^{(s)} = windowSum g s` equals *exactly* the sum of absolute gap differences
`∑_{k∈K} |g_{k+1} − g_{k-s}|`.  This is the sharp form of
`Vs_windowSum_le_sum_gaps` (which further bounds `|g_{k+1} − g_{k-s}|` by
`g_{k+1} + g_{k-s}`), obtained by summing the gap-difference identity
`windowSum_succ_sub`. -/
theorem Vs_windowSum_eq_sum_abs_gap_diff (g : ℕ → ℝ) (s : ℕ) (K : Finset ℕ)
    (hK : ∀ k ∈ K, s ≤ k) :
    Vs K (windowSum g s) = ∑ k ∈ K, |g (k + 1) - g (k - s)| := by
  unfold Vs
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [windowSum_succ_sub g s k (hK k hk)]

/-- **Additive block form of the variation bound (eq N.13, `C_Q X + O_Q(sL)`).**
On a *consecutive* window-edge block `K = Ico i (i+n)` with full windows
(guaranteed by `s ≤ i`), the rolling-window variation is bounded by the sum of
two consecutive-range gap sums: the forward block `∑_{Ico (i+1) (i+n+1)} g` and
the trailing block `∑_{Ico (i-s) (i+n-s)} g`.  This is the manuscript's additive
`V_s ≤ C_Q X + O_Q(sL)` decomposition (each consecutive-range gap sum telescopes
against a hit sequence to a span), the additive companion of the multiplicative
explicit form `windowVariation` (`V_s ≤ 2 M ·|𝒦|`). -/
theorem Vs_windowSum_Ico_le_forward_add_trailing (g : ℕ → ℝ) (s i n : ℕ)
    (hg : ∀ m, 0 ≤ g m) (hsi : s ≤ i) :
    Vs (Finset.Ico i (i + n)) (windowSum g s) ≤
      (∑ j ∈ Finset.Ico (i + 1) (i + n + 1), g j) +
        (∑ j ∈ Finset.Ico (i - s) (i + n - s), g j) := by
  have hK : ∀ k ∈ Finset.Ico i (i + n), s ≤ k := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    omega
  have hforward :
      (∑ k ∈ Finset.Ico i (i + n), g (k + 1)) =
        ∑ j ∈ Finset.Ico (i + 1) (i + n + 1), g j := by
    rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
    have e1 : i + n - i = n := by omega
    have e2 : i + n + 1 - (i + 1) = n := by omega
    rw [e1, e2]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    omega
  have htrailing :
      (∑ k ∈ Finset.Ico i (i + n), g (k - s)) =
        ∑ j ∈ Finset.Ico (i - s) (i + n - s), g j := by
    rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
    have e1 : i + n - i = n := by omega
    have e2 : i + n - s - (i - s) = n := by omega
    rw [e1, e2]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    omega
  calc Vs (Finset.Ico i (i + n)) (windowSum g s)
      ≤ ∑ k ∈ Finset.Ico i (i + n), (g (k + 1) + g (k - s)) :=
        Vs_windowSum_le_sum_gaps g s _ hg hK
    _ = (∑ k ∈ Finset.Ico i (i + n), g (k + 1)) +
          (∑ k ∈ Finset.Ico i (i + n), g (k - s)) := Finset.sum_add_distrib
    _ = (∑ j ∈ Finset.Ico (i + 1) (i + n + 1), g j) +
          (∑ j ∈ Finset.Ico (i - s) (i + n - s), g j) := by
        rw [hforward, htrailing]

end AppendixN

end

end Erdos260
