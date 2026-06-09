import Mathlib
import Erdos260.LiftState
import Erdos260.AppendixG_Ladder
import Erdos260.CNL
import Erdos260.CNLEntropy

/-!
# Appendix G.5–G.10 + K.3.5: the CNL transition classifier algebra

This file formalizes the *algebraic cores* of the manuscript's correlated
nonseparation ladder (CNL) transition classifier (`proof_v4.tex`), which the
alignment tracker previously listed as **absent**:

* **G.5 Type-C coefficient resonance** (G.16–G.18, K.17, K.24).  The coefficient
  `c_k = a_k + h_{k+1} - h_k`; resonance `c_k = 0` is *equivalent* to the
  deterministic lift relation `h_k = a_k + h_{k+1}`, and a clean Type-C stretch
  telescopes to `h_k = (∑ a) + h_{k+t}`.  This forces a dense-marker length
  bound (real corollary).
* **G.7 strict monotonicity of the bridge exponents** (Lemma G.3 / G.26–G.27).
  The bridge exponent `E_t = A_s - A_t + σ_{k+t}^-` has forward difference
  `E_{t+1} - E_t = -(g_t) + (σ_{t+1}^- - σ_t^-)` (unconditional identity); under
  the recent-window slide identity for `σ^-` (proved here as `recentWindow_succ_sub`)
  this becomes `E_{t+1} - E_t = -g^{old}_t < 0`, so the `E_t` are strictly
  decreasing (`StrictAnti`).
* **G.8 finite 2-adic power-sum dichotomy** (Lemma G.4).  For a strictly
  decreasing exponent family with odd coefficients, the finite 2-adic power sum
  `∑ u_t 2^{E_t}` has 2-adic valuation exactly the minimum exponent; this yields
  the vanishing-suffix / determined-suffix dichotomy of the bridge congruence.
* **G.9 true-bridge gap count** (G.30–G.32, K.20–K.21).  The substitution
  `σ^-_t ≤ A_t - a_k + a_{k+s} + C` and the gap-count core
  `∑ (positive gaps) ≤ K ⟹ count ≤ K` (the heart of the Bridge-`s` exclusion).
* **K.3.5 classifier connection**.  The priority selector `selectCNLClass?` from
  `Erdos260.CNL` is characterized on the Type-C and Type-P branches
  (`selected_eq_tc_iff`, `selected_eq_tp_iff`), and the algebraic resonance /
  suffix dichotomy is tied to the `CNLClass` partition.

**Faithful vs conditional.**  The difference identities, telescopings,
2-adic valuation/divisibility lemmas, window slide, and gap-count bounds are
*unconditional real theorems* (no `sorry`/`axiom`).  What stays manuscript
conditional (supplied as explicit hypotheses) is the deep dynamics: the Type-P
bridge congruence (G.19–G.25, the `U`-elimination), the analytic right-side
bound `|Z| ≤ C_Q s L^3 ⋯` (G.28), the value of the working precision `P_k`, and
the classification input linking a transition's `available` set to the local
algebra (e.g. `tc ∈ available ↔ resonance`).
-/

namespace Erdos260

open Finset

/-! ## G.5. Type-C coefficient resonance is deterministic (G.16–G.18, K.17, K.24) -/

/-- **Manuscript (G.16).**  The Type-C coefficient of a one-step transition,
`c_k = a_k + h_{k+1} - h_k`, where `a_k` is the gap and `h_k` the lift height. -/
def cCoeff (a h : ℕ → ℤ) (k : ℕ) : ℤ := a k + h (k + 1) - h k

/-- **Manuscript (G.16)⟹(G.17), equivalently (K.17).**  The coefficient vanishes
*iff* the deterministic Type-C lift relation `h_k = a_k + h_{k+1}` holds.  (High
coefficient resonance forces `c_k = 0`; the algebraic equivalence is exact.) -/
theorem cCoeff_eq_zero_iff (a h : ℕ → ℤ) (k : ℕ) :
    cCoeff a h k = 0 ↔ h k = a k + h (k + 1) := by
  unfold cCoeff
  constructor
  · intro hh; linarith
  · intro hh; linarith

/-- **Manuscript (G.18) / (K.24).**  Telescoping a clean Type-C stretch where
`c_i = 0` for `i = k, k+1, …, k+t-1` gives the closed form
`h_k = (∑_{i<t} a_{k+i}) + h_{k+t}`.  All intermediate lift states are forced by
the initial state and the terminal value. -/
theorem typeC_chain (a h : ℕ → ℤ) (k t : ℕ)
    (hres : ∀ i, i < t → cCoeff a h (k + i) = 0) :
    h k = (∑ i ∈ Finset.range t, a (k + i)) + h (k + t) := by
  induction t with
  | zero => simp
  | succ n ih =>
      have hn : h k = (∑ i ∈ Finset.range n, a (k + i)) + h (k + n) :=
        ih (fun i hi => hres i (Nat.lt_succ_of_lt hi))
      have hstep : h (k + n) = a (k + n) + h (k + n + 1) :=
        (cCoeff_eq_zero_iff a h (k + n)).1 (hres n (Nat.lt_succ_self n))
      rw [Finset.sum_range_succ]
      have hk1 : k + (n + 1) = k + n + 1 := by omega
      rw [hk1]
      linarith [hn, hstep]

/-- **Manuscript (K.24)⟹dense marker length bound.**  If a clean Type-C stretch
has `c_i = 0` throughout, all gaps positive (`≥ 1`) and the terminal lift is
nonnegative, then the stretch length is bounded by the initial lift height:
`t ≤ h_k`.  (This is the spatial-interval bound `t+1` hits within `O(L)` that
makes a long Type-C chain a dense marker.) -/
theorem typeC_chain_length_le (a h : ℕ → ℤ) (k t : ℕ)
    (hres : ∀ i, i < t → cCoeff a h (k + i) = 0)
    (hgap : ∀ i, i < t → 1 ≤ a (k + i)) (hterm : 0 ≤ h (k + t)) :
    (t : ℤ) ≤ h k := by
  have hchain := typeC_chain a h k t hres
  have hsum : (t : ℤ) ≤ ∑ i ∈ Finset.range t, a (k + i) := by
    have h1 : ∑ i ∈ Finset.range t, (1 : ℤ) ≤ ∑ i ∈ Finset.range t, a (k + i) :=
      Finset.sum_le_sum (fun i hi => hgap i (Finset.mem_range.1 hi))
    simpa using h1
  linarith [hchain, hsum, hterm]

/-! ## G.7. Strict monotonicity of the bridge exponents (Lemma G.3, G.26–G.27) -/

/-- Partial gap sum `A_t = ∑_{i<t} g_i` (manuscript `A_t = a_k + ⋯ + a_{k+t-1}`,
with the cluster offset `g_i = a_{k+i}` folded into `g`), `A_0 = 0`. -/
def gapPartial (g : ℕ → ℤ) (t : ℕ) : ℤ := ∑ i ∈ Finset.range t, g i

theorem gapPartial_succ (g : ℕ → ℤ) (t : ℕ) :
    gapPartial g (t + 1) = gapPartial g t + g t := by
  simp [gapPartial, Finset.sum_range_succ]

/-- **Manuscript (G.26).**  The bridge exponent `E_t = A_s - A_t + σ_{k+t}^-`,
with `σ^-` the recent-suffix partial sum passed as `sm`. -/
def bridgeExp (g sm : ℕ → ℤ) (s t : ℕ) : ℤ := gapPartial g s - gapPartial g t + sm t

/-- **Unconditional forward-difference identity** underlying Lemma G.3:
`E_{t+1} - E_t = -(g_t) + (σ_{t+1}^- - σ_t^-)`.  (The `-(g_t)` is `-(A_{t+1}-A_t)`.) -/
theorem bridgeExp_succ_sub (g sm : ℕ → ℤ) (s t : ℕ) :
    bridgeExp g sm s (t + 1) - bridgeExp g sm s t
      = -(g t) + (sm (t + 1) - sm t) := by
  unfold bridgeExp
  rw [gapPartial_succ]
  ring

/-- Width-window recent-suffix sum `σ^-_t = ∑_{oldL t ≤ i < t} g_i`, with `oldL`
the (advancing) left endpoint of the recent window. -/
def recentWindow (g : ℕ → ℤ) (oldL : ℕ → ℕ) (t : ℕ) : ℤ :=
  ∑ i ∈ Finset.Ico (oldL t) t, g i

/-- **Window-slide identity (the `σ^-` mechanism, G.4/G.5 family).**  When the
recent window advances (`oldL (t+1) = oldL t + 1`) and is non-degenerate
(`oldL t < t`), its sum gains the new top gap `g_t` and drops the leaving gap
`g_{oldL t}`:  `σ^-_{t+1} - σ^-_t = g_t - g_{oldL t}`.  This is a genuine
identity (no manuscript hypothesis). -/
theorem recentWindow_succ_sub (g : ℕ → ℤ) (oldL : ℕ → ℕ) (t : ℕ)
    (hslide : oldL (t + 1) = oldL t + 1) (hlt : oldL t < t) :
    recentWindow g oldL (t + 1) - recentWindow g oldL t = g t - g (oldL t) := by
  unfold recentWindow
  rw [hslide]
  set b := oldL t with hb
  have hbt : b + 1 ≤ t := by omega
  rw [Finset.sum_Ico_succ_top hbt]
  have hsplit : ∑ i ∈ Finset.Ico b t, g i
      = g b + ∑ i ∈ Finset.Ico (b + 1) t, g i := by
    rw [← Finset.sum_Ico_consecutive g (Nat.le_succ b) hbt]
    have h1 : ∑ i ∈ Finset.Ico b (b + 1), g i = g b := by
      rw [Finset.sum_Ico_succ_top (le_refl b)]
      simp
    rw [h1]
  rw [hsplit]
  ring

/-- **Lemma G.3 / (G.27), windowed realization (unconditional).**  With
`σ^- = recentWindow g oldL`, the bridge exponent step is exactly
`E_{t+1} - E_t = -g_{oldL t}`. -/
theorem bridgeExp_recentWindow_succ_sub (g : ℕ → ℤ) (oldL : ℕ → ℕ) (s t : ℕ)
    (hslide : oldL (t + 1) = oldL t + 1) (hlt : oldL t < t) :
    bridgeExp g (recentWindow g oldL) s (t + 1)
      - bridgeExp g (recentWindow g oldL) s t = -g (oldL t) := by
  rw [bridgeExp_succ_sub, recentWindow_succ_sub g oldL t hslide hlt]
  ring

/-- **Lemma G.3 / (G.27), single strict step.**  If the leaving gap is positive,
the bridge exponent strictly decreases: `E_{t+1} < E_t`. -/
theorem bridgeExp_recentWindow_succ_lt (g : ℕ → ℤ) (oldL : ℕ → ℕ) (s t : ℕ)
    (hslide : oldL (t + 1) = oldL t + 1) (hlt : oldL t < t)
    (hpos : 0 < g (oldL t)) :
    bridgeExp g (recentWindow g oldL) s (t + 1)
      < bridgeExp g (recentWindow g oldL) s t := by
  have h := bridgeExp_recentWindow_succ_sub g oldL s t hslide hlt
  linarith

/-- **Lemma G.3 (strict monotonicity `E_0 > E_1 > ⋯`).**  Given the `σ^-`
window-slide identity for every step (`sm (t+1) - sm t = g_t - g^{old}_t`) and
positive leaving gaps, the bridge exponents are strictly decreasing.  This is
the manuscript conclusion `E_0 > E_1 > ⋯ > E_{s-1}`, here as `StrictAnti`. -/
theorem bridgeExp_strictAnti (g sm gOld : ℕ → ℤ) (s : ℕ)
    (hwin : ∀ t, sm (t + 1) - sm t = g t - gOld t)
    (hpos : ∀ t, 0 < gOld t) :
    StrictAnti (fun t => bridgeExp g sm s t) := by
  refine strictAnti_nat_of_succ_lt (fun t => ?_)
  show bridgeExp g sm s (t + 1) < bridgeExp g sm s t
  have hsub : bridgeExp g sm s (t + 1) - bridgeExp g sm s t = -gOld t := by
    rw [bridgeExp_succ_sub, hwin t]; ring
  have hp := hpos t
  linarith [hsub, hp]

/-! ## G.8. Finite 2-adic power-sum dichotomy (Lemma G.4) -/

/-- The finite 2-adic power sum `∑_{t<s} u_t 2^{E_t}` as an integer. -/
def powerSum (E : ℕ → ℕ) (u : ℕ → ℤ) (s : ℕ) : ℤ :=
  ∑ t ∈ Finset.range s, u t * (2 : ℤ) ^ (E t)

/-- If every exponent in the range is `≥ m`, then `2^m` divides the power sum. -/
theorem two_pow_dvd_powerSum {E : ℕ → ℕ} {u : ℕ → ℤ} {s m : ℕ}
    (hm : ∀ t ∈ Finset.range s, m ≤ E t) :
    (2 : ℤ) ^ m ∣ powerSum E u s := by
  unfold powerSum
  refine Finset.dvd_sum ?_
  intro t ht
  exact (pow_dvd_pow 2 (hm t ht)).mul_left (u t)

/-- **Exact minimum valuation (the nonarchimedean core of Lemma G.4).**  If the
exponents `E_0 > ⋯ > E_n` are strictly decreasing (so `E n` is the strict
minimum over `range (n+1)`) and the bottom coefficient `u n` is odd, then
`2^{E n + 1}` does *not* divide the power sum: the bottom term dominates the
valuation, which is therefore exactly `E n`. -/
theorem not_two_pow_succ_dvd_powerSum {E : ℕ → ℕ} {u : ℕ → ℤ} {n : ℕ}
    (hdec : ∀ t ∈ Finset.range n, E n < E t) (hodd : Odd (u n)) :
    ¬ (2 : ℤ) ^ (E n + 1) ∣ powerSum E u (n + 1) := by
  intro hdvd
  have hsplit : powerSum E u (n + 1) = powerSum E u n + u n * (2 : ℤ) ^ (E n) := by
    unfold powerSum; rw [Finset.sum_range_succ]
  have hfirst : (2 : ℤ) ^ (E n + 1) ∣ powerSum E u n := by
    apply two_pow_dvd_powerSum
    intro t ht
    have := hdec t ht
    omega
  have hlast : (2 : ℤ) ^ (E n + 1) ∣ u n * (2 : ℤ) ^ (E n) := by
    have he : u n * (2 : ℤ) ^ (E n) = powerSum E u (n + 1) + -(powerSum E u n) := by
      rw [hsplit]; ring
    rw [he]; exact dvd_add hdvd (dvd_neg.mpr hfirst)
  rw [pow_succ, mul_comm (u n) ((2 : ℤ) ^ (E n))] at hlast
  have h2ne : (2 : ℤ) ^ (E n) ≠ 0 := by positivity
  have hdvd2 : (2 : ℤ) ∣ u n := (mul_dvd_mul_iff_left h2ne).1 hlast
  obtain ⟨c, hc⟩ := hdvd2
  obtain ⟨d, hd⟩ := hodd
  omega

/-- **Lemma G.4 (finite 2-adic power-sum dichotomy).**  For a strictly
decreasing exponent family `E_0 > ⋯ > E_n` with odd coefficients, and a
congruence `∑_{t≤n} u_t 2^{E_t} ≡ Z (mod 2^M)`, *exactly one* of the following
holds (the two cases are mutually exclusive since `M ≤ E n` and `E n < M`
cannot both hold):

* **vanishing suffix:** `M ≤ E n` (every exponent `≥ M`) and `2^M ∣ Z`;
* **determined suffix:** `E n < M`, and `v_2(Z) = E n`, i.e. `2^{E n} ∣ Z` but
  `¬ 2^{E n + 1} ∣ Z`.  The colliding suffix index `t = n` is unique because the
  exponents are distinct. -/
theorem powerSum_dichotomy {E : ℕ → ℕ} {u : ℕ → ℤ} {n M : ℕ} {Z : ℤ}
    (hdec : ∀ t ∈ Finset.range n, E n < E t) (hodd : Odd (u n))
    (hcong : (2 : ℤ) ^ M ∣ (powerSum E u (n + 1) - Z)) :
    (M ≤ E n ∧ (2 : ℤ) ^ M ∣ Z) ∨
      (E n < M ∧ (2 : ℤ) ^ (E n) ∣ Z ∧ ¬ (2 : ℤ) ^ (E n + 1) ∣ Z) := by
  by_cases hMle : M ≤ E n
  · left
    refine ⟨hMle, ?_⟩
    have hdvdP : (2 : ℤ) ^ M ∣ powerSum E u (n + 1) := by
      apply two_pow_dvd_powerSum
      intro t ht
      by_cases hte : t = n
      · subst hte; exact hMle
      · have htn : t < n := by have := Finset.mem_range.1 ht; omega
        have := hdec t (Finset.mem_range.2 htn)
        omega
    have hZeq : Z = powerSum E u (n + 1) + -(powerSum E u (n + 1) - Z) := by ring
    rw [hZeq]; exact dvd_add hdvdP (dvd_neg.mpr hcong)
  · have hMgt : E n < M := by omega
    right
    refine ⟨hMgt, ?_, ?_⟩
    · have hdvdP : (2 : ℤ) ^ (E n) ∣ powerSum E u (n + 1) := by
        apply two_pow_dvd_powerSum
        intro t ht
        by_cases hte : t = n
        · subst hte; exact le_refl _
        · have htn : t < n := by have := Finset.mem_range.1 ht; omega
          have := hdec t (Finset.mem_range.2 htn)
          omega
      have hdvdcong : (2 : ℤ) ^ (E n) ∣ (powerSum E u (n + 1) - Z) :=
        dvd_trans (pow_dvd_pow 2 (le_of_lt hMgt)) hcong
      have hZeq : Z = powerSum E u (n + 1) + -(powerSum E u (n + 1) - Z) := by ring
      rw [hZeq]; exact dvd_add hdvdP (dvd_neg.mpr hdvdcong)
    · intro hZ
      have hdvdcong : (2 : ℤ) ^ (E n + 1) ∣ (powerSum E u (n + 1) - Z) :=
        dvd_trans (pow_dvd_pow 2 (by omega : E n + 1 ≤ M)) hcong
      have hdvdP : (2 : ℤ) ^ (E n + 1) ∣ powerSum E u (n + 1) := by
        have hPeq : powerSum E u (n + 1) = (powerSum E u (n + 1) - Z) + Z := by ring
        rw [hPeq]; exact dvd_add hdvdcong hZ
      exact not_two_pow_succ_dvd_powerSum hdec hodd hdvdP

/-- **Lemma G.4, fed by Lemma G.3.**  The strict-decrease hypothesis of the
dichotomy is exactly the conclusion of the bridge-exponent strict monotonicity
(`StrictAnti`); this packages the two manuscript steps together. -/
theorem powerSum_dichotomy_of_strictAnti {E : ℕ → ℕ} {u : ℕ → ℤ} {n M : ℕ} {Z : ℤ}
    (hSA : StrictAnti E) (hodd : Odd (u n))
    (hcong : (2 : ℤ) ^ M ∣ (powerSum E u (n + 1) - Z)) :
    (M ≤ E n ∧ (2 : ℤ) ^ M ∣ Z) ∨
      (E n < M ∧ (2 : ℤ) ^ (E n) ∣ Z ∧ ¬ (2 : ℤ) ^ (E n + 1) ∣ Z) :=
  powerSum_dichotomy (fun _ ht => hSA (Finset.mem_range.1 ht)) hodd hcong

/-- **Lemma G.3/G.4 bridge package.**  If the natural exponents `E_t` are the
integer bridge exponents `A_s - A_t + σ^-_t`, and the window-slide identity makes
those bridge exponents strictly decrease, then the Type-P bridge power sum has
the manuscript vanishing-suffix / determined-suffix dichotomy.  This packages
the strict bridge-exponent descent together with the finite 2-adic power-sum
lemma, so the algebraic Type-P bridge can be cited as one closed theorem. -/
theorem bridgeExp_powerSum_dichotomy {E : ℕ → ℕ} {g sm gOld : ℕ → ℤ}
    {u : ℕ → ℤ} {s n M : ℕ} {Z : ℤ}
    (hE : ∀ t, (E t : ℤ) = bridgeExp g sm s t)
    (hwin : ∀ t, sm (t + 1) - sm t = g t - gOld t)
    (hpos : ∀ t, 0 < gOld t)
    (hodd : Odd (u n))
    (hcong : (2 : ℤ) ^ M ∣ (powerSum E u (n + 1) - Z)) :
    (M ≤ E n ∧ (2 : ℤ) ^ M ∣ Z) ∨
      (E n < M ∧ (2 : ℤ) ^ (E n) ∣ Z ∧ ¬ (2 : ℤ) ^ (E n + 1) ∣ Z) := by
  have hSAz : StrictAnti (fun t => bridgeExp g sm s t) :=
    bridgeExp_strictAnti g sm gOld s hwin hpos
  have hSA : StrictAnti E := by
    intro a b hab
    have hz : (E b : ℤ) < (E a : ℤ) := by
      rw [hE b, hE a]
      exact hSAz hab
    exact_mod_cast hz
  exact powerSum_dichotomy_of_strictAnti hSA hodd hcong

/-! ## G.9. True-bridge gap count (G.30–G.32, K.20–K.21) -/

/-- **(G.29)⟹(G.30).**  From the determined-suffix bound
`E_t ≤ A_s - a_k + a_{k+s} + C` and the definition `E_t = A_s - A_t + σ^-_t`, the
recent-suffix sum obeys `σ^-_t ≤ A_t - a_k + a_{k+s} + C`.  (Pure substitution.) -/
theorem sigmaMinus_le_of_bridgeExp_le (g sm : ℕ → ℤ) (s t : ℕ)
    (firstGap termGap C : ℤ)
    (hE : bridgeExp g sm s t ≤ gapPartial g s - firstGap + termGap + C) :
    sm t ≤ gapPartial g t - firstGap + termGap + C := by
  unfold bridgeExp at hE
  linarith

/-- **(G.31)⟹(G.32), gap-count core.**  If a recent-suffix block consists of
`W.card` gaps each `≥ 1`, and the block sum is bounded by `K`, then the number of
gaps is at most `K`.  This is the manuscript step "the left side contains at
least `r - s - O(1)` positive gaps, hence `r ≤ s + C'(\log L + \log s) + O(1)`". -/
theorem card_le_of_sum_ge_one_le {ι : Type*} (W : Finset ι) (g : ι → ℤ)
    (hg : ∀ i ∈ W, 1 ≤ g i) {K : ℤ} (hsum : ∑ i ∈ W, g i ≤ K) :
    (W.card : ℤ) ≤ K := by
  have hcard : (W.card : ℤ) = ∑ _i ∈ W, (1 : ℤ) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hcard]
  exact le_trans (Finset.sum_le_sum hg) hsum

/-! ## K.3.5. Connection to the CNL priority classifier -/

/-- Algebraic Type-C resonance predicate for a one-step transition: the
coefficient vanishes (equivalently the deterministic relation `h_k = a_k+h_{k+1}`
of (K.17) holds). -/
def IsTypeCResonant (a h : ℕ → ℤ) (k : ℕ) : Prop := cCoeff a h k = 0

/-- **Priority-scan characterization of the Type-C branch (K.3.1/K.3.5 NF2).**
The selector returns `TC` exactly when `TC` is available and all strictly
higher-priority classes (`PKG`, `SEP`, `BND`) are absent. -/
theorem selected_eq_tc_iff (av : Finset CNLClass) :
    selectCNLClass? av = some CNLClass.tc ↔
      CNLClass.tc ∈ av ∧ CNLClass.pkg ∉ av ∧ CNLClass.sep ∉ av ∧ CNLClass.bnd ∉ av := by
  constructor
  · intro h
    have htc : CNLClass.tc ∈ av := selectCNLClass?_eq_some_mem h
    have hpkg : CNLClass.pkg ∉ av := by
      intro hp; rw [selectCNLClass?_eq_pkg_of_mem hp] at h; exact absurd h (by decide)
    have hsep : CNLClass.sep ∉ av := by
      intro hs; rw [selectCNLClass?_eq_sep_of_mem hs hpkg] at h; exact absurd h (by decide)
    have hbnd : CNLClass.bnd ∉ av := by
      intro hb; rw [selectCNLClass?_eq_bnd_of_mem hb hpkg hsep] at h; exact absurd h (by decide)
    exact ⟨htc, hpkg, hsep, hbnd⟩
  · rintro ⟨htc, hpkg, hsep, hbnd⟩
    exact selectCNLClass?_eq_tc_of_mem htc hpkg hsep hbnd

/-- **Priority-scan characterization of the Type-P (bridge) branch.**  The
selector returns `TP` exactly when `TP` is available and all six higher-priority
classes are absent — i.e. after BND/SEP/TC/VS/DS and PKG have all been excluded,
exactly the manuscript situation in which "the remaining high-precision
dependence is through the pivot `U_k`" (K.3.1). -/
theorem selected_eq_tp_iff (av : Finset CNLClass) :
    selectCNLClass? av = some CNLClass.tp ↔
      CNLClass.tp ∈ av ∧ CNLClass.pkg ∉ av ∧ CNLClass.sep ∉ av ∧ CNLClass.bnd ∉ av
        ∧ CNLClass.tc ∉ av ∧ CNLClass.vs ∉ av ∧ CNLClass.ds ∉ av := by
  constructor
  · intro h
    have htp : CNLClass.tp ∈ av := selectCNLClass?_eq_some_mem h
    have hpkg : CNLClass.pkg ∉ av := by
      intro hp; rw [selectCNLClass?_eq_pkg_of_mem hp] at h; exact absurd h (by decide)
    have hsep : CNLClass.sep ∉ av := by
      intro hs; rw [selectCNLClass?_eq_sep_of_mem hs hpkg] at h; exact absurd h (by decide)
    have hbnd : CNLClass.bnd ∉ av := by
      intro hb; rw [selectCNLClass?_eq_bnd_of_mem hb hpkg hsep] at h; exact absurd h (by decide)
    have htc : CNLClass.tc ∉ av := by
      intro ht; rw [selectCNLClass?_eq_tc_of_mem ht hpkg hsep hbnd] at h
      exact absurd h (by decide)
    have hvs : CNLClass.vs ∉ av := by
      intro hv; rw [selectCNLClass?_eq_vs_of_mem hv hpkg hsep hbnd htc] at h
      exact absurd h (by decide)
    have hds : CNLClass.ds ∉ av := by
      intro hd; rw [selectCNLClass?_eq_ds_of_mem hd hpkg hsep hbnd htc hvs] at h
      exact absurd h (by decide)
    exact ⟨htp, hpkg, hsep, hbnd, htc, hvs, hds⟩
  · rintro ⟨htp, hpkg, hsep, hbnd, htc, hvs, hds⟩
    exact selectCNLClass?_eq_tp_of_mem htp hpkg hsep hbnd htc hvs hds

/-- **K.3.5 (NF2)→(K.17): Type-C selection forces the deterministic relation.**
If a transition's availability reflects the local algebra via the manuscript
classification input `tc ∈ available ↔ resonance`, and the priority selector
classifies it as `TC`, then the deterministic Type-C lift relation
`h_k = a_k + h_{k+1}` holds.  The link `hlink` is the manuscript's local
classification (conditional); the forcing of the relation is then a real
consequence of `cCoeff_eq_zero_iff`. -/
theorem typeC_selection_forces_relation (a h : ℕ → ℤ) (k : ℕ) (t : CNLTransition)
    (hlink : CNLClass.tc ∈ t.available ↔ IsTypeCResonant a h k)
    (hsel : canonicalCNLSelector t = some CNLClass.tc) :
    h k = a k + h (k + 1) := by
  have hmem : CNLClass.tc ∈ t.available := canonicalCNLSelector_eq_some_mem hsel
  have hres : IsTypeCResonant a h k := hlink.1 hmem
  exact (cCoeff_eq_zero_iff a h k).1 hres

/--
**G.18/K.24, selector-routed form.**  If the priority classifier selects
Type-C at every step of a clean stretch, and Type-C availability is exactly the
local resonance predicate, then the whole stretch is deterministic:
`h_k = (∑ a_{k+i}) + h_{k+t}`.
-/
theorem typeC_selected_chain (a h : ℕ → ℤ) (k t : ℕ)
    (tr : ℕ → CNLTransition)
    (hlink :
      ∀ i, i < t ->
        (CNLClass.tc ∈ (tr i).available ↔ IsTypeCResonant a h (k + i)))
    (hsel :
      ∀ i, i < t -> canonicalCNLSelector (tr i) = some CNLClass.tc) :
    h k = (∑ i ∈ Finset.range t, a (k + i)) + h (k + t) := by
  refine typeC_chain a h k t ?_
  intro i hi
  have hmem : CNLClass.tc ∈ (tr i).available :=
    canonicalCNLSelector_eq_some_mem (hsel i hi)
  exact (hlink i hi).1 hmem

/--
**K.24 dense-marker consequence, selector-routed form.**  A clean stretch on
which the classifier keeps selecting Type-C has length at most the initial lift
height, provided the visible gaps are positive and the terminal lift is
nonnegative.
-/
theorem typeC_selected_chain_length_le (a h : ℕ → ℤ) (k t : ℕ)
    (tr : ℕ → CNLTransition)
    (hlink :
      ∀ i, i < t ->
        (CNLClass.tc ∈ (tr i).available ↔ IsTypeCResonant a h (k + i)))
    (hsel :
      ∀ i, i < t -> canonicalCNLSelector (tr i) = some CNLClass.tc)
    (hgap : ∀ i, i < t -> 1 <= a (k + i))
    (hterm : 0 <= h (k + t)) :
    (t : ℤ) <= h k := by
  refine typeC_chain_length_le a h k t ?_ hgap hterm
  intro i hi
  have hmem : CNLClass.tc ∈ (tr i).available :=
    canonicalCNLSelector_eq_some_mem (hsel i hi)
  exact (hlink i hi).1 hmem

/-- **G.8 dichotomy ↦ VS / DS class assignment.**  The vanishing-suffix /
determined-suffix dichotomy assigns the bridge step to one of the two *distinct*
suffix classes `VS`, `DS` of the CNL partition (Lemma K.3.2), together with the
corresponding 2-adic data. -/
theorem suffix_dichotomy_class {E : ℕ → ℕ} {u : ℕ → ℤ} {n M : ℕ} {Z : ℤ}
    (hdec : ∀ t ∈ Finset.range n, E n < E t) (hodd : Odd (u n))
    (hcong : (2 : ℤ) ^ M ∣ (powerSum E u (n + 1) - Z)) :
    ∃ cls : CNLClass, (cls = CNLClass.vs ∨ cls = CNLClass.ds) ∧
      (cls = CNLClass.vs → M ≤ E n ∧ (2 : ℤ) ^ M ∣ Z) ∧
      (cls = CNLClass.ds → E n < M ∧ (2 : ℤ) ^ (E n) ∣ Z ∧ ¬ (2 : ℤ) ^ (E n + 1) ∣ Z) := by
  rcases powerSum_dichotomy hdec hodd hcong with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · exact ⟨CNLClass.vs, Or.inl rfl, fun _ => ⟨h1, h2⟩, fun h => absurd h (by decide)⟩
  · exact ⟨CNLClass.ds, Or.inr rfl, fun h => absurd h (by decide), fun _ => ⟨h1, h2, h3⟩⟩

end Erdos260
