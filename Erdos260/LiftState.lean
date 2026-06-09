import Mathlib
import Erdos260.CNLEntropy

/-!
# Appendix G.1–G.3: 2-adic lift states, slide identities, one-step Kraft bound

This file formalizes the foundational objects of `proof_v2.tex` Appendix G that
were previously **absent** from the Lean development:

* the *shadow data* `C_k = ∑_{i<r} 2^{σ_i}` and `D_k = ∑_{i<r} σ_i 2^{σ_i}`
  (manuscript G.1);
* the *lift state* `(δ_k, q_k)` (G.1–G.2);
* the *exact slide identities* (G.4)–(G.5) for the shadow data under a window
  slide, proved here as genuine integer identities;
* the *2-adic separation lemma* underlying the one-step lift Kraft bound
  (Lemma G.1 / G.10): compatible children `δ'` all reduce to a common 2-adic
  centre `Ξ`, hence any two distinct children jump by `δ'₂ ≥ δ'₁ + 2^{δ'₁}`;
* the *one-step Kraft bound* `∑_{δ'} 2^{-c·H(δ')} ≤ (1 - 2^{-c})⁻¹`, connected
  to the `cleanCNLKraftSum` vocabulary used by Appendix G.6 / L.1.

These are unconditional theorems (no `sorry`, no manuscript hypothesis input).
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## Shadow data and the window slide -/

/-- Shadow numerator `C_k = ∑_{i<r} 2^{σ i}` of manuscript (G.1), where
`s i = σ_i(k)` are the reverse partial gap sums (`s 0 = 0`). -/
def shadowC (r : ℕ) (s : ℕ → ℕ) : ℤ :=
  ∑ i ∈ Finset.range r, (2 : ℤ) ^ (s i)

/-- Shadow numerator `D_k = ∑_{i<r} σ_i 2^{σ_i}` of manuscript (G.1).  (The
manuscript sum starts at `i = 1`, but the `i = 0` term vanishes because
`σ_0 = 0`.) -/
def shadowD (r : ℕ) (s : ℕ → ℕ) : ℤ :=
  ∑ i ∈ Finset.range r, (s i : ℤ) * (2 : ℤ) ^ (s i)

/-- The slide of the partial-sum sequence when a new gap `a = a_k = g_k` is
prepended to the reverse window: `σ'_0 = 0` and `σ'_{i+1} = a + σ_i`. -/
def slidePartial (a : ℕ) (s : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | (i + 1) => a + s i

@[simp] theorem slidePartial_zero (a : ℕ) (s : ℕ → ℕ) :
    slidePartial a s 0 = 0 := rfl

@[simp] theorem slidePartial_succ (a : ℕ) (s : ℕ → ℕ) (i : ℕ) :
    slidePartial a s (i + 1) = a + s i := rfl

theorem shadowC_succ (n : ℕ) (s : ℕ → ℕ) :
    shadowC (n + 1) s = shadowC n s + (2 : ℤ) ^ (s n) := by
  simp [shadowC, Finset.sum_range_succ]

theorem shadowD_succ (n : ℕ) (s : ℕ → ℕ) :
    shadowD (n + 1) s = shadowD n s + (s n : ℤ) * (2 : ℤ) ^ (s n) := by
  simp [shadowD, Finset.sum_range_succ]

/-- **Manuscript identity (G.4), base form.**  Under a window slide prepending
gap `a`, the shadow `C` satisfies `C_{k+1} = 1 + 2^{a}·(∑_{i<m} 2^{σ_i})`. -/
theorem shadowC_slide_base (a m : ℕ) (s : ℕ → ℕ) :
    shadowC (m + 1) (slidePartial a s) = 1 + (2 : ℤ) ^ a * shadowC m s := by
  induction m with
  | zero => simp [shadowC]
  | succ n ih =>
      rw [shadowC_succ (n + 1) (slidePartial a s), ih, slidePartial_succ,
        shadowC_succ n s, pow_add]
      ring

/-- **Manuscript identity (G.5), base form.**  Under a window slide prepending
gap `a`, the shadow `D` satisfies
`D_{k+1} = 2^{a}·(a·(∑_{i<m} 2^{σ_i}) + ∑_{i<m} σ_i 2^{σ_i})`. -/
theorem shadowD_slide_base (a m : ℕ) (s : ℕ → ℕ) :
    shadowD (m + 1) (slidePartial a s)
      = (2 : ℤ) ^ a * ((a : ℤ) * shadowC m s + shadowD m s) := by
  induction m with
  | zero => simp [shadowC, shadowD]
  | succ n ih =>
      rw [shadowD_succ (n + 1) (slidePartial a s), ih, slidePartial_succ,
        shadowC_succ n s, shadowD_succ n s]
      push_cast
      ring

/-- **Manuscript slide identity (G.4).**  Writing `T_k = 2^{σ_{r-1}}` for the
top window term and `C_k = shadowC (m+1) s`, the slide reads
`C_{k+1} = 1 + 2^{a_k}(C_k - T_k)`. -/
theorem shadowC_slide (a m : ℕ) (s : ℕ → ℕ) :
    shadowC (m + 1) (slidePartial a s)
      = 1 + (2 : ℤ) ^ a * (shadowC (m + 1) s - (2 : ℤ) ^ (s m)) := by
  rw [shadowC_slide_base, shadowC_succ]; ring

/-- **Manuscript slide identity (G.5).**  With `σ_k = σ_{r-1} = s m`,
`T_k = 2^{σ_k}`, `C_k = shadowC (m+1) s`, `D_k = shadowD (m+1) s`, the slide
reads `D_{k+1} = 2^{a_k}(D_k - σ_k T_k + a_k(C_k - T_k))`. -/
theorem shadowD_slide (a m : ℕ) (s : ℕ → ℕ) :
    shadowD (m + 1) (slidePartial a s)
      = (2 : ℤ) ^ a *
          (shadowD (m + 1) s - (s m : ℤ) * (2 : ℤ) ^ (s m)
            + (a : ℤ) * (shadowC (m + 1) s - (2 : ℤ) ^ (s m))) := by
  rw [shadowD_slide_base, shadowC_succ, shadowD_succ]; ring

/-! ## Lift states and 2-adic compatibility -/

/-- A lift state `(δ, q)` of manuscript G.1: the lift exponent `δ = V_k - h_k`
and the lift residue `q`. -/
structure LiftState where
  δ : ℕ
  q : ℤ
deriving DecidableEq

/-- A candidate next exponent `δ'` is *2-adically compatible* with the common
2-adic centre `Ξ` (manuscript G.7: `δ' ≡ Ξ (mod 2^{δ'})`). -/
def TwoAdicCompatible (Ξ : ℤ) (δ' : ℕ) : Prop :=
  (2 : ℤ) ^ δ' ∣ ((δ' : ℤ) - Ξ)

/-- **Manuscript Lemma G.1, separation step.**  If two distinct exponents are
both compatible with the same 2-adic centre, the larger exceeds the smaller by
at least `2^{δ'₁}`.  This is the rapid (iterated-exponential) growth that makes
the one-step Kraft sum converge. -/
theorem twoAdic_separation {Ξ : ℤ} {δ₁ δ₂ : ℕ}
    (h₁ : TwoAdicCompatible Ξ δ₁) (h₂ : TwoAdicCompatible Ξ δ₂)
    (hlt : δ₁ < δ₂) :
    δ₁ + 2 ^ δ₁ ≤ δ₂ := by
  have hdvd12 : (2 : ℤ) ^ δ₁ ∣ (2 : ℤ) ^ δ₂ := pow_dvd_pow 2 (le_of_lt hlt)
  have h2' : (2 : ℤ) ^ δ₁ ∣ ((δ₂ : ℤ) - Ξ) := dvd_trans hdvd12 h₂
  have hsub : (2 : ℤ) ^ δ₁ ∣ ((δ₂ : ℤ) - (δ₁ : ℤ)) := by
    have h := dvd_sub h2' h₁
    have heq : ((δ₂ : ℤ) - Ξ) - ((δ₁ : ℤ) - Ξ) = (δ₂ : ℤ) - (δ₁ : ℤ) := by ring
    rwa [heq] at h
  have hpos : (0 : ℤ) < (δ₂ : ℤ) - (δ₁ : ℤ) := by
    have : (δ₁ : ℤ) < (δ₂ : ℤ) := by exact_mod_cast hlt
    linarith
  have hge : (2 : ℤ) ^ δ₁ ≤ (δ₂ : ℤ) - (δ₁ : ℤ) := Int.le_of_dvd hpos hsub
  have hcast : ((δ₁ + 2 ^ δ₁ : ℕ) : ℤ) ≤ ((δ₂ : ℕ) : ℤ) := by
    push_cast
    linarith [hge]
  exact_mod_cast hcast

/-! ## One-step lift Kraft bound (Lemma G.1 / G.10) -/

/-- The geometric Kraft tail: a finite sum of `r^n` over distinct naturals is
bounded by the full geometric series `(1 - r)⁻¹`. -/
theorem finset_geom_sum_le {S : Finset ℕ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑ n ∈ S, r ^ n ≤ (1 - r)⁻¹ := by
  have hgeom : HasSum (fun n : ℕ => r ^ n) (1 - r)⁻¹ :=
    hasSum_geometric_of_lt_one hr0 hr1
  calc
    ∑ n ∈ S, r ^ n ≤ ∑' n : ℕ, r ^ n :=
      Summable.sum_le_tsum S (fun i _ => pow_nonneg hr0 i) hgeom.summable
    _ = (1 - r)⁻¹ := hgeom.tsum_eq

/-- `2^{-(c·n)} = (2^{-c})^n` as a real number, for natural `n`. -/
theorem two_rpow_neg_mul_nat (c : ℝ) (n : ℕ) :
    (2 : ℝ) ^ (-(c * (n : ℝ))) = ((2 : ℝ) ^ (-c)) ^ n := by
  rw [← Real.rpow_natCast ((2 : ℝ) ^ (-c)) n,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

/-- **Lemma G.1 / G.10 (one-step lift Kraft bound), real form.**
For any finite set `S` of lift exponents, any positive tilt `c`, and any lift
height function `H` dominating the exponent (`δ ≤ H δ`, manuscript `H ≥ δ`),
the weighted Kraft sum is bounded by the universal constant `(1 - 2^{-c})⁻¹`.

This is unconditional: the bound holds for *every* finite exponent set, in
particular for the compatible-children set whose elements obey the 2-adic
separation above. -/
theorem liftOneStepKraft_le {S : Finset ℕ} {c : ℝ} (hc : 0 < c)
    (H : ℕ → ℝ) (hH : ∀ δ ∈ S, (δ : ℝ) ≤ H δ) :
    cleanCNLKraftSum S H c ≤ (1 - (2 : ℝ) ^ (-c))⁻¹ := by
  set r : ℝ := (2 : ℝ) ^ (-c) with hr
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr1 : r < 1 := by
    rw [hr]; exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  -- step 1: replace each height by the exponent (monotone in the tilt).
  have hmono : cleanCNLKraftSum S H c ≤ cleanCNLKraftSum S (fun n => (n : ℝ)) c := by
    unfold cleanCNLKraftSum
    refine Finset.sum_le_sum ?_
    intro δ hδ
    have hle : -(c * H δ) ≤ -(c * (δ : ℝ)) := by
      have := hH δ hδ
      nlinarith [this, hc]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hle
  -- step 2: the exponent-weighted sum is a geometric Kraft tail.
  have hgeom : cleanCNLKraftSum S (fun n => (n : ℝ)) c ≤ (1 - r)⁻¹ := by
    have hcong : cleanCNLKraftSum S (fun n => (n : ℝ)) c = ∑ n ∈ S, r ^ n := by
      unfold cleanCNLKraftSum
      refine Finset.sum_congr rfl ?_
      intro n _
      rw [hr]
      exact two_rpow_neg_mul_nat c n
    rw [hcong]
    exact finset_geom_sum_le hr0 hr1
  exact le_trans hmono hgeom

/-- The compatible-children formulation: the set of compatible next exponents
satisfies the one-step Kraft bound.  (`H ≥ δ` is the manuscript `H_k ≥ δ_k`.) -/
theorem compatibleChildren_kraft_le {Ξ : ℤ} {c : ℝ} (hc : 0 < c)
    (S : Finset ℕ) (_hcompat : ∀ δ ∈ S, TwoAdicCompatible Ξ δ)
    (H : ℕ → ℝ) (hH : ∀ δ ∈ S, (δ : ℝ) ≤ H δ) :
    cleanCNLKraftSum S H c ≤ (1 - (2 : ℝ) ^ (-c))⁻¹ :=
  liftOneStepKraft_le hc H hH

end

end Erdos260
