/-
  Lemma 25.1 (Dyadic cylinder reduction) + Proposition 25.3 (Residual singular
  squares are controlled) — Erdős-#260, §8 "Residual singular-square cleanup".

  Manuscript: `proof_v4_repaired_core_v71_p2_preprint_hygiene.tex`.

  * §8 header                                          line 1662
  * display (25.1) fractional approximation            lines 1667–1679
  * **Lemma 25.1** "Dyadic cylinder reduction"         lines 1681–1722
        (trichotomy: dense all-one block / all-zero block / prefix of length
         ≥ p/2 agreeing with a denominator-≤ Qp binary segment)
  * Lemma 25.2 "Small-denominator segment density"     lines 1735–1794
        (the SEGMENT companion — already formalized in
         `Erdos260.Lemma252SegmentDensity`)
  * **Proposition 25.3** "Residual singular squares are controlled"
                                                        lines 1796–1809

  These are the QUICK-WIN number-theory companions to the proved §25.2 segment
  density; together (25.1 + 25.2 + 25.3) they complete the dyadic-cylinder
  certificate LC3 used by the singular-square lane.

  STYLE: the established `P1HotspotAudit` / `P2TrustBoundary` /
  `Lemma252SegmentDensity` "kernel with explicit hypotheses".  The genuine
  geometry (the carry-tail structure, the dense-block / gap-bound routing, the
  semiperiodic geometry) is taken as explicit hypotheses; everything else is
  genuine Lean with no `sorry` and no custom `axiom`.  Each theorem's
  `#print axioms` lands on the trusted base `[propext, Classical.choice,
  Quot.sound]` (or fewer).

  ============================================================================
  WHAT IS GENUINELY CHECKABLE HERE
  ============================================================================
  Lemma 25.1:
  * `cylinder_approx_eq`            — the exact identity behind display (25.1):
                                      `M/D − ν/(Qp) = R/(QpD)` from the
                                      denominator-drop congruence `QpM = R + νD`.
  * `cylinder_approx_bound`         — (25.1) verbatim: `|M/D − ν/(Qp)| ≤
                                      K(X+p)/(QpD)` from `|R| ≤ K(X+p)`.
  * `cylinder_equal_or_adjacent`    — binary cylinder stability: two reals within
                                      distance `< 1` have floors that are equal
                                      or adjacent (differ by exactly one carry).
  * `dyadic_cylinder_equal_or_adjacent` — the scaled (depth-`n`) form: `|α−β| <
                                      2^{-n}` ⟹ the first `n` binary cylinders
                                      are equal or adjacent (occupancy ≤ 2).
  * `cylinder_reduction_from_approx`— (25.1) ⇒ depth-`n` cylinders equal/adjacent.
  * `cylinder_reduction_route`      — the trichotomy assembly: the surviving
                                      prefix has length `≥ p/2`, or there is an
                                      all-one / all-zero block of length `> L+CQ`.

  Proposition 25.3:
  * `density_contradiction`         — the quantitative core: a dense prefix
                                      (`≥ c₀ p − 1` ones) is impossible in a
                                      mean-low-density run (`≤ 2κ p` ones) once
                                      `2κ < c₀` and `p` is large.
  * `residual_dense_branch_excluded`— the §25.2 bridge: `segment_density_const`
                                      with `C = Q`, `β = 1/2` gives `c₀ = 1/(8Q)`
                                      ones, contradicting mean-low-density.
  * `semiperiodic_shorter_period`   — Fine–Wilf: a residual square of period `p`
                                      that is also semiperiodic with period
                                      `s < p` has a strictly shorter period
                                      `gcd(p,s) ≤ s` (the "shorter-period run").
  * `proposition_25_3_routing`      — the logical packaging of the 4-way routing
                                      (shorter-period run / dirty boundary / AP
                                      tower / local spike).
  * `proposition_25_3_certified`    — the end-to-end assembly chaining the 25.1
                                      trichotomy, the 25.2 dense/semiperiodic
                                      dichotomy, and the 25.3 routing.
-/
import Mathlib
import Erdos260.Lemma252SegmentDensity
import Erdos260.P1LeavesB
import Erdos260.P2TrustBoundary

namespace Erdos260.Lemma251Prop253Cylinder

open Finset

/-! ===========================================================================
    LEMMA 25.1, PART A — the fractional approximation display (25.1).

    Manuscript (lines 1667–1679): denominator-drop gives `QpM ≡ R (mod D)` with
    `D = 2^p − 1` and `|R| ≪_Q X + p`, hence for some integer `ν`
        ‖ M/D − ν/(Qp) ‖_{ℝ/ℤ}  ≪_Q  (X + p)/(pD).
    The congruence `QpM ≡ R (mod D)` is, for a witness `ν`, the exact identity
    `Qp·M = R + ν·D`.  From it the approximation is a clean field computation.
    =========================================================================== -/

/-- **Display (25.1), exact identity.**  If the denominator-drop congruence holds
    in the witnessed form `Q·p·M = R + ν·D` (i.e. `QpM ≡ R (mod D)` with quotient
    `ν`), then the fractional defect is exactly `R/(Qp·D)`. -/
theorem cylinder_approx_eq (M D Q p R ν : ℝ) (hD : D ≠ 0) (hQp : Q * p ≠ 0)
    (hcong : Q * p * M = R + ν * D) :
    M / D - ν / (Q * p) = R / (Q * p * D) := by
  have hM : M = (R + ν * D) / (Q * p) := by
    rw [eq_div_iff hQp]; linear_combination hcong
  rw [hM]; field_simp; ring

/-- **Display (25.1), the approximation bound.**  With `D > 0`, `Qp > 0`, the
    witnessed denominator-drop congruence `Qp·M = R + ν·D`, and the residual
    bound `|R| ≤ K(X+p)`, the fractional defect obeys
    `|M/D − ν/(Qp)| ≤ K(X+p)/(Qp·D)` — i.e. (25.1) verbatim. -/
theorem cylinder_approx_bound (M D Q p R ν K X : ℝ)
    (hD : 0 < D) (hQp : 0 < Q * p)
    (hcong : Q * p * M = R + ν * D)
    (hR : |R| ≤ K * (X + p)) :
    |M / D - ν / (Q * p)| ≤ K * (X + p) / (Q * p * D) := by
  have hden : (0 : ℝ) < Q * p * D := mul_pos hQp hD
  rw [cylinder_approx_eq M D Q p R ν (ne_of_gt hD) (ne_of_gt hQp) hcong, abs_div,
    abs_of_pos hden]
  have hstep := mul_le_mul_of_nonneg_right hR (le_of_lt (inv_pos.mpr hden))
  rwa [← div_eq_mul_inv, ← div_eq_mul_inv] at hstep

/-! ===========================================================================
    LEMMA 25.1, PART B — binary cylinder stability ("equal or adjacent").

    Manuscript (lines 1709–1711): "Binary cylinder stability on ℝ/ℤ shows that
    the first n₀ binary cylinders are equal or adjacent.  In the equal case there
    is exact agreement.  In the adjacent case, binary carry structure gives words
    ξ0 1⋯1 / ξ1 0⋯0."

    The genuine, checkable core: for reals within distance `< 1` the integer parts
    differ by at most one carry; scaled by `2^n` this is exactly "the first `n`
    binary digits agree, or they differ by a single carry" (cylinder occupancy of
    a point is at most two).
    =========================================================================== -/

/-- **Cylinder stability (unit scale).**  Two reals within distance `< 1` have
    integer parts that are equal or differ by exactly one. -/
theorem cylinder_equal_or_adjacent {x y : ℝ} (h : |x - y| < 1) :
    ⌊x⌋ = ⌊y⌋ ∨ ⌊x⌋ = ⌊y⌋ + 1 ∨ ⌊y⌋ = ⌊x⌋ + 1 := by
  rw [abs_sub_lt_iff] at h
  obtain ⟨h1, h2⟩ := h
  have hfx := Int.floor_le x
  have hfy := Int.floor_le y
  have hfx' := Int.lt_floor_add_one x
  have hfy' := Int.lt_floor_add_one y
  have k1 : (⌊x⌋ : ℝ) < (⌊y⌋ : ℝ) + 2 := by linarith
  have k2 : (⌊y⌋ : ℝ) < (⌊x⌋ : ℝ) + 2 := by linarith
  have i1 : ⌊x⌋ < ⌊y⌋ + 2 := by exact_mod_cast k1
  have i2 : ⌊y⌋ < ⌊x⌋ + 2 := by exact_mod_cast k2
  omega

/-- **Binary cylinder stability (depth `n`).**  If `|α − β| < 2^{-n}` then the
    depth-`n` dyadic cylinders `⌊2^n α⌋` and `⌊2^n β⌋` are equal or adjacent;
    equivalently the first `n` binary digits of `α` and `β` agree, or they differ
    by a single carry.  (A point lies in at most two depth-`n` cylinders of any
    `2^{-n}`-close neighbour, so cylinder occupancy is ≤ 2.) -/
theorem dyadic_cylinder_equal_or_adjacent (α β : ℝ) (n : ℕ)
    (h : |α - β| < 1 / 2 ^ n) :
    ⌊2 ^ n * α⌋ = ⌊2 ^ n * β⌋
      ∨ ⌊2 ^ n * α⌋ = ⌊2 ^ n * β⌋ + 1
      ∨ ⌊2 ^ n * β⌋ = ⌊2 ^ n * α⌋ + 1 := by
  apply cylinder_equal_or_adjacent
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hmul : (2 : ℝ) ^ n * |α - β| < 1 := by
    have hlt := mul_lt_mul_of_pos_left h h2
    rwa [mul_one_div, div_self (ne_of_gt h2)] at hlt
  calc |2 ^ n * α - 2 ^ n * β|
      = |2 ^ n * (α - β)| := by rw [mul_sub]
    _ = (2 : ℝ) ^ n * |α - β| := by rw [abs_mul, abs_of_pos h2]
    _ < 1 := hmul

/-- **Cylinder reduction step (25.1 ⇒ cylinders equal/adjacent).**  From the
    witnessed denominator-drop congruence and residual bound (25.1), if the (25.1)
    bound beats `2^{-n}` (the manuscript's `n = n₀ = p − B`), then the depth-`n`
    binary cylinders of `M/D` and the small-denominator rational `ν/(Qp)` are
    equal or adjacent. -/
theorem cylinder_reduction_from_approx
    (M D Q p R ν K X : ℝ) (n : ℕ)
    (hD : 0 < D) (hQp : 0 < Q * p)
    (hcong : Q * p * M = R + ν * D)
    (hR : |R| ≤ K * (X + p))
    (hsmall : K * (X + p) / (Q * p * D) < 1 / 2 ^ n) :
    ⌊2 ^ n * (M / D)⌋ = ⌊2 ^ n * (ν / (Q * p))⌋
      ∨ ⌊2 ^ n * (M / D)⌋ = ⌊2 ^ n * (ν / (Q * p))⌋ + 1
      ∨ ⌊2 ^ n * (ν / (Q * p))⌋ = ⌊2 ^ n * (M / D)⌋ + 1 := by
  have hb := cylinder_approx_bound M D Q p R ν K X hD hQp hcong hR
  exact dyadic_cylinder_equal_or_adjacent (M / D) (ν / (Q * p)) n
    (lt_of_le_of_lt hb hsmall)

/-! ===========================================================================
    LEMMA 25.1, PART C — the trichotomy assembly.

    Manuscript (lines 1681–1722): with `p > 8L + C_Q log L` and the cut depth
    `B = L + C_Q log p + C_Q`, the equal/adjacent cylinder dichotomy resolves into
    exactly three alternatives:
      1. a dense all-one block of length `> L + C_Q`  (→ local-spike stopping);
      2. an all-zero block of length `> L + C_Q`      (→ rational gap bound);
      3. a prefix of length `≥ p/2` agreeing with a denominator-`≤ Qp` segment.

    Proof bookkeeping (lines 1718–1722): in the equal case the agreement length
    is `n₀ = p − B`; in the adjacent case with a short carry tail (`≤ B`),
    discarding `O(B)` bits leaves agreement of length `p − 2B − O(1) ≥ p/2`; a long
    carry tail (`> B > L + C_Q`) is all-ones (case 1) or all-zeros (case 2).

    Below the carry-tail structure (which of the four micro-cases holds) and the
    "all ones / all zeros" tags are explicit hypotheses; the genuine length
    arithmetic `≥ p/2` and `> L + C_Q` is discharged.  The bound `4B ≤ p`
    abstracts `B = L + C_Q log p + C_Q ≤ p/4` valid once `p > 8L + C_Q log L`. -/

/-- **Lemma 25.1, trichotomy routing.**  Given the cut bounds `4B ≤ p` (so
    `B ≤ p/4`) and `L + C_Q < B`, and the four micro-cases produced by the
    equal/adjacent cylinder dichotomy and the carry-tail dichotomy, the three
    manuscript alternatives follow: a prefix-agreement of length `≥ p/2`
    (`p ≤ 2·agreeLen`), or an all-one / all-zero block of length `> L + C_Q`. -/
theorem cylinder_reduction_route
    (L CQ p B agreeLen tailLen : ℕ) (Ones Zeros : Prop)
    (hB : 4 * B ≤ p) (hBL : L + CQ < B)
    (hcase :
        agreeLen = p - B                  -- equal cylinders: exact agreement
      ∨ agreeLen = p - 2 * B              -- adjacent, short carry tail (discard 2B)
      ∨ (B < tailLen ∧ Ones)             -- adjacent, long tail, all ones
      ∨ (B < tailLen ∧ Zeros)) :         -- adjacent, long tail, all zeros
    (p ≤ 2 * agreeLen)                                -- case 3: prefix ≥ p/2
      ∨ (L + CQ < tailLen ∧ Ones)                     -- case 1: dense all-one block
      ∨ (L + CQ < tailLen ∧ Zeros) := by              -- case 2: all-zero block
  rcases hcase with h | h | ⟨ht, ho⟩ | ⟨ht, hz⟩
  · left; omega
  · left; omega
  · right; left; exact ⟨by omega, ho⟩
  · right; right; exact ⟨by omega, hz⟩

/-! ===========================================================================
    PROPOSITION 25.3, PART A — the density contradiction (the quantitative core).

    Manuscript (lines 1804–1806): "Apply Lemma 25.2 with C = Q, β = 1/2.  Positive
    prefix density contradicts mean-low-density if κ is chosen sufficiently
    small."  Quantitatively: the §25.2 dense branch gives at least `c₀ p − 1` ones
    on the prefix (`c₀ = β²/(2C)`), while mean-low-density caps the ones at `2κ p`.
    Once `2κ < c₀`, these force `p ≤ 1/(c₀ − 2κ)`, contradicting large `p`. -/

/-- **Proposition 25.3, density contradiction.**  A dense prefix (`c₀ p − 1 ≤ E`
    ones, from §25.2) cannot occur in a mean-low-density run (`E ≤ 2κ p`) once the
    density gap is positive (`2κ < c₀`) and `p` exceeds the threshold
    `1/(c₀ − 2κ)`. -/
theorem density_contradiction (E κ p c₀ : ℝ)
    (hdense : c₀ * p - 1 ≤ E)
    (hlow : E ≤ 2 * κ * p)
    (hκ : 2 * κ < c₀)
    (hpbig : 1 / (c₀ - 2 * κ) < p) :
    False := by
  have hpos : 0 < c₀ - 2 * κ := by linarith
  have h1 : c₀ * p - 1 ≤ 2 * κ * p := le_trans hdense hlow
  have h2 : (c₀ - 2 * κ) * p ≤ 1 := by nlinarith
  have h4 : p ≤ 1 / (c₀ - 2 * κ) := by
    rw [le_div_iff₀ hpos]; nlinarith [h2]
  linarith [hpbig, h4]

/-- **Proposition 25.3, §25.2 bridge.**  Instantiating `Lemma 25.2`
    (`segment_density_const`) with `C = Q`, `β = 1/2` gives the dense constant
    `c₀ = (1/2)²/(2Q) = 1/(8Q)`: the agreeing prefix of length `N ≥ p/2` of a
    rational with denominator `q ≤ Qp` carries `≥ p/(8Q) − 1` ones.  Under
    mean-low-density (`≤ 2κ p` ones) with `2κ < 1/(8Q)` and `p` large this is
    contradictory — so a residual square in a mean-low-density run is NOT in the
    §25.2 dense branch. -/
theorem residual_dense_branch_excluded
    (q N p : ℕ) (Q κ : ℝ) (hq : 0 < q) (r : ℕ → ℕ)
    (hpos : ∀ i, i < N → 1 ≤ r i) (hbound : r N < q)
    (hstep : ∀ i, i < N → r (i + 1) = (2 * r i) % q)
    (hinj : Set.InjOn r (Set.Iio N))
    (hp : 0 < p) (hQ : 0 < Q)
    (hqQp : (q : ℝ) ≤ Q * p)
    (hNβp : (1 / 2 : ℝ) * p ≤ (N : ℝ))
    (hlow : ((∑ i ∈ Finset.range N, (2 * r i) / q : ℕ) : ℝ) ≤ 2 * κ * p)
    (hκ : 2 * κ < 1 / (8 * Q))
    (hpbig : 1 / (1 / (8 * Q) - 2 * κ) < (p : ℝ)) :
    False := by
  have hQne : (Q : ℝ) ≠ 0 := ne_of_gt hQ
  have hdense := Erdos260.Lemma252SegmentDensity.segment_density_const
    q N p Q (1 / 2) hq r hpos hbound hstep hinj (by norm_num) hp hqQp hNβp
  have hc0 : ((1 : ℝ) / 2) ^ 2 / (2 * Q) = 1 / (8 * Q) := by
    field_simp; ring
  rw [hc0] at hdense
  exact density_contradiction _ κ (p : ℝ) (1 / (8 * Q)) hdense hlow hκ hpbig

/-! ===========================================================================
    PROPOSITION 25.3, PART B — Fine–Wilf shorter-period extraction.

    Manuscript (lines 1806–1809): "Otherwise the prefix is short semiperiodic;
    since ww occurs in the true word, this semiperiodic region either extends to a
    shorter-period run, fails at a dirty boundary, or repeats heavily and enters AP
    tower."  The "extends to a shorter-period run" step is Fine–Wilf
    (`Erdos260.P1LeavesB.fine_wilf`): a residual square has period `p`; the §25.2
    semiperiodic branch gives a period `s < p` (`s < βp/4 = p/8`); if the overlap
    reaches the Fine–Wilf threshold, the common period `gcd(p,s) ≤ s < p` is a
    strictly shorter run period. -/

/-- **Proposition 25.3, shorter-period run (Fine–Wilf).**  A word with periods `p`
    and `s` (`0 < s < p`) whose length reaches the Fine–Wilf threshold
    `p + s − gcd(p,s)` has a strictly shorter common period `gcd(p,s) ≤ s`. -/
theorem semiperiodic_shorter_period {α : Type*} {w : List α} {p s : ℕ}
    (hp : w.HasPeriod p) (hs : w.HasPeriod s) (hspos : 0 < s) (hsp : s < p)
    (hlen : p + s - Nat.gcd p s ≤ w.length) :
    ∃ d, w.HasPeriod d ∧ d ≤ s ∧ d < p := by
  refine ⟨Nat.gcd p s, Erdos260.P1LeavesB.fine_wilf hp hs hlen, ?_, ?_⟩
  · exact Nat.le_of_dvd hspos (Nat.gcd_dvd_right p s)
  · exact lt_of_le_of_lt (Nat.le_of_dvd hspos (Nat.gcd_dvd_right p s)) hsp

/-! ===========================================================================
    PROPOSITION 25.3, PART C — the routing packaging.

    Manuscript (lines 1798–1800): "If a residual singular square ww with
    p > 8L + C_Q log L belongs to a mean-low-density positive run, then it enters a
    shorter-period run, clean-boundary dirty recursion, AP tower, or local-spike
    package."  This is the logical assembly of the Lemma 25.1 trichotomy with the
    Lemma 25.2 dense/semiperiodic dichotomy. -/

/-- **Proposition 25.3, routing (logical packaging).**  Given the Lemma 25.1
    trichotomy, the routing of its controlled cases (dense block → local spike,
    all-zero block → dirty boundary), the Lemma 25.2 dichotomy on the agreeing
    prefix, the exclusion of the dense prefix (mean-low-density, see
    `residual_dense_branch_excluded`), and the semiperiodic routing, the residual
    square enters one of the four packages. -/
theorem proposition_25_3_routing
    {DenseBlock ZeroBlock PrefixAgrees DensePrefix Semiperiodic
      ShorterPeriodRun DirtyBoundary APTower LocalSpike : Prop}
    (h251 : DenseBlock ∨ ZeroBlock ∨ PrefixAgrees)
    (hdense_block : DenseBlock → LocalSpike)
    (hzero_block : ZeroBlock → DirtyBoundary)
    (h252 : PrefixAgrees → DensePrefix ∨ Semiperiodic)
    (hexcl : ¬ DensePrefix)
    (hsemi : Semiperiodic → ShorterPeriodRun ∨ DirtyBoundary ∨ APTower) :
    ShorterPeriodRun ∨ DirtyBoundary ∨ APTower ∨ LocalSpike := by
  rcases h251 with hd | hz | hpref
  · exact Or.inr (Or.inr (Or.inr (hdense_block hd)))
  · exact Or.inr (Or.inl (hzero_block hz))
  · rcases h252 hpref with hdp | hs
    · exact absurd hdp hexcl
    · rcases hsemi hs with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))

/-- **Proposition 25.3, certified end-to-end (LC3).**  The full §8 dyadic-cylinder
    certificate assembled from genuine §25.1 + §25.2 cores: the Lemma 25.1
    trichotomy routes the dense/all-zero blocks; on the agreeing prefix, the
    §25.2 length split (`(1/2)p ≤ N` dense vs. `N < (1/2)p` semiperiodic) either
    contradicts mean-low-density via `residual_dense_branch_excluded` (which calls
    `Lemma252SegmentDensity.segment_density_const`) or forces semiperiodicity,
    which routes onward.  Conclusion: the residual square enters a shorter-period
    run, a dirty-boundary recursion, an AP tower, or a local-spike package. -/
theorem proposition_25_3_certified
    {DenseBlock ZeroBlock PrefixAgrees Semiperiodic
      ShorterPeriodRun DirtyBoundary APTower LocalSpike : Prop}
    (q N p : ℕ) (Q κ : ℝ) (hq : 0 < q) (r : ℕ → ℕ)
    (hpos : ∀ i, i < N → 1 ≤ r i) (hbound : r N < q)
    (hstep : ∀ i, i < N → r (i + 1) = (2 * r i) % q)
    (hinj : Set.InjOn r (Set.Iio N))
    (hp : 0 < p) (hQ : 0 < Q) (hqQp : (q : ℝ) ≤ Q * p)
    (hlow : ((∑ i ∈ Finset.range N, (2 * r i) / q : ℕ) : ℝ) ≤ 2 * κ * p)
    (hκ : 2 * κ < 1 / (8 * Q))
    (hpbig : 1 / (1 / (8 * Q) - 2 * κ) < (p : ℝ))
    (h251 : DenseBlock ∨ ZeroBlock ∨ PrefixAgrees)
    (hdense_block : DenseBlock → LocalSpike)
    (hzero_block : ZeroBlock → DirtyBoundary)
    (hshort : (N : ℝ) < (1 / 2 : ℝ) * p → Semiperiodic)
    (hsemi : Semiperiodic → ShorterPeriodRun ∨ DirtyBoundary ∨ APTower) :
    ShorterPeriodRun ∨ DirtyBoundary ∨ APTower ∨ LocalSpike := by
  rcases h251 with hd | hz | _ipref
  · exact Or.inr (Or.inr (Or.inr (hdense_block hd)))
  · exact Or.inr (Or.inl (hzero_block hz))
  · by_cases hge : (1 / 2 : ℝ) * p ≤ (N : ℝ)
    · exact (residual_dense_branch_excluded q N p Q κ hq r hpos hbound hstep hinj
        hp hQ hqQp hge hlow hκ hpbig).elim
    · rw [not_le] at hge
      rcases hsemi (hshort hge) with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))

end Erdos260.Lemma251Prop253Cylinder
