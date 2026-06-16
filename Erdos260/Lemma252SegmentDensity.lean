/-
  Lemma 25.2 — Small-denominator SEGMENT density (Erdős-#260, §25.2).

  Manuscript: `proof_v4_repaired_core_v71_p2_preprint_hygiene.tex`,
  §25.2 "Small-denominator segment density"
  (`\subsection{...}\label{lemma-25.2.-small-denominator-segment-density}`,
  lines 1735–1794).  The headline statement (lines 1737–1743) is:

    "Fix `C ≥ 1`, `β ∈ (0,1)`.  There is `c₀ = c₀(C,β) > 0` such that any binary
     segment of length `n ≥ βp` of a rational with denominator `q ≤ Cp` either
     has at least `c₀ p` ones, or is semiperiodic with period `< βp/4`."

  The genuine, checkable number-theoretic core is the segment estimate (25.2a),
  line 1785, obtained from the carry recurrence `2 r_j = ε_{j+1} q₀ + r_{j+1}`
  (line 1774) summed over a consecutive block `[u, u+N)` of `N ≤ t = ord_{q₀}(2)`
  *distinct* residues `r_j ≡ 2^j a (mod q₀) ∈ {1,…,q₀-1}`.  The telescoping
  produces the exact identity (display before 25.2a, lines 1777–1779)

      q₀ · Σ_{j=u}^{u+N-1} ε_{j+1}  =  Σ_{j=u}^{u+N-1} r_j + r_u − r_{u+N},     (★)

  and, since the `N` distinct positive residues sum to `≥ N(N+1)/2` and the
  endpoint term `r_u − r_{u+N} ≥ −q₀`, the ones-count obeys (25.2a):

      Σ_{j=u}^{u+N-1} ε_{j+1}  ≥  N(N+1)/(2 q₀) − 1.                            (25.2a)

  This is the SEGMENT companion to §24's full-period density
  (`Erdos260.P1LeavesB.lemma_24_1_core` / `lemma_24_1_ones_density`); the only
  difference is that the cyclic-shift `r_t = r_0` of a full period is replaced by
  the endpoint correction `+ r_u − r_{u+N}`.  We reuse the same residue / orbit /
  triangular machinery (`P2TrustBoundary.o3_triangular`,
  `P2TrustBoundary.o3_doubling_orbit_injective`).

  STYLE: P1HotspotAudit/P2TrustBoundary "kernel with explicit hypotheses".  The
  geometric/periodicity inputs (the carry recurrence, residue positivity/bound,
  and the `N ≤ t` distinctness of the orbit) are taken as hypotheses; everything
  else is genuine Lean with no `sorry` and no custom `axiom`.  Each theorem's
  `#print axioms` lands on the trusted base `[propext, Classical.choice,
  Quot.sound]`.

  Contents:
  * `segment_telescope`        — the exact ℕ telescoping identity (★).
  * `segment_density_core`     — (25.2a) as the clean ℕ floor `N(N+1) ≤ 2q(E+1)`.
  * `segment_density_real`     — (25.2a) verbatim in ℝ: `E ≥ N(N+1)/(2q) − 1`.
  * `segment_density_orbit`    — concrete instantiation to the doubling orbit of
                                 `a/q` (q odd ≥ 3) on a block of length `N ≤ ord_q(2)`.
  * `segment_density_orbit_real` — the ℝ floor for the doubling orbit.
  * `segment_density_const`    — the manuscript "≥ c₀ p ones" shape: on the dense
                                 branch (`βp ≤ N ≤ t`, `q ≤ Cp`) the ones-count is
                                 `≥ (β²/(2C)) p − 1`, i.e. `c₀ = β²/(2C)`.
-/
import Mathlib
import Erdos260.P2TrustBoundary

namespace Erdos260.Lemma252SegmentDensity

open Finset

/-! ===========================================================================
    LEAF 1 — the exact telescoping identity (★).

    Summing the carry recurrence `2 r_i = q·((2 r_i)/q) + r_{i+1}` over the block
    `[0, N)` and reindexing telescopes to

        (Σ_{i<N} r_i) + r_0 = q · (Σ_{i<N} (2 r_i)/q) + r_N.

    (Block start `u` is taken to be `0` without loss of generality; the general
    block `[u, u+N)` of (★) is the special case `r := fun j => r₀ (u + j)`.)  No
    positivity / distinctness is needed for the identity itself — only the carry
    step.
    =========================================================================== -/

/-- The §25.2 telescoping identity (★): for the binary carry step
    `r (i+1) = (2 · r i) % q`, summing over a segment `[0, N)` gives
    `(Σ_{i<N} r i) + r 0 = q · (Σ_{i<N} (2·r i)/q) + r N`. -/
theorem segment_telescope
    (q N : ℕ) (r : ℕ → ℕ)
    (hstep : ∀ i, i < N → r (i + 1) = (2 * r i) % q) :
    (∑ i ∈ Finset.range N, r i) + r 0
      = q * (∑ i ∈ Finset.range N, (2 * r i) / q) + r N := by
  classical
  -- per-term carry identity `2 r_i = q·((2 r_i)/q) + r_{i+1}`
  have hterm : ∑ i ∈ Finset.range N, (2 * r i)
      = ∑ i ∈ Finset.range N, (q * ((2 * r i) / q) + r (i + 1)) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hiN : i < N := Finset.mem_range.mp hi
    have hdm := Nat.div_add_mod (2 * r i) q
    rw [hstep i hiN]
    omega
  -- `2·S = q·E + Σ r_{i+1}`
  have h2S : 2 * (∑ i ∈ Finset.range N, r i)
      = q * (∑ i ∈ Finset.range N, (2 * r i) / q)
          + ∑ i ∈ Finset.range N, r (i + 1) := by
    calc 2 * (∑ i ∈ Finset.range N, r i)
        = ∑ i ∈ Finset.range N, (2 * r i) := by rw [Finset.mul_sum]
      _ = ∑ i ∈ Finset.range N, (q * ((2 * r i) / q) + r (i + 1)) := hterm
      _ = (∑ i ∈ Finset.range N, q * ((2 * r i) / q))
            + ∑ i ∈ Finset.range N, r (i + 1) := by rw [Finset.sum_add_distrib]
      _ = q * (∑ i ∈ Finset.range N, (2 * r i) / q)
            + ∑ i ∈ Finset.range N, r (i + 1) := by rw [Finset.mul_sum]
  -- reindexing: `(Σ r_{i+1}) + r_0 = (Σ r_i) + r_N`
  have hshift : (∑ i ∈ Finset.range N, r (i + 1)) + r 0
      = (∑ i ∈ Finset.range N, r i) + r N := by
    have h1 := Finset.sum_range_succ r N
    have h2 := Finset.sum_range_succ' r N
    omega
  omega

/-! ===========================================================================
    LEAF 2 — (25.2a) as the clean integer density floor.

    `N` distinct positive residues `r 0,…,r_{N-1} ∈ {1,…,q-1}` with the carry
    step and `r N < q` (the endpoint residue is also `< q`) satisfy

        N (N+1) ≤ 2 q (E + 1),       E := Σ_{i<N} (2 r_i)/q,

    equivalently the ones-count `E ≥ N(N+1)/(2q) − 1`.
    =========================================================================== -/

/-- **Lemma 25.2, arithmetic core (25.2a).**  Let the segment residues `r 0,…`
    be a binary carry sequence (`r (i+1) = (2 r i) % q`) which on the block
    `[0, N)` is positive (`hpos`) and *distinct* (`hinj`, i.e. `N ≤ ord_q(2)` in
    the orbit model), with endpoint residue `r N < q` (`hbound`).  Then the
    number of one-digits `E = Σ_{i<N} (2 r_i)/q` satisfies the segment density
    floor `N (N+1) ≤ 2 q (E + 1)`. -/
theorem segment_density_core
    (q N : ℕ) (r : ℕ → ℕ)
    (hpos : ∀ i, i < N → 1 ≤ r i)
    (hbound : r N < q)
    (hstep : ∀ i, i < N → r (i + 1) = (2 * r i) % q)
    (hinj : Set.InjOn r (Set.Iio N)) :
    N * (N + 1) ≤ 2 * q * ((∑ i ∈ Finset.range N, (2 * r i) / q) + 1) := by
  classical
  have htel := segment_telescope q N r hstep
  -- the `N` distinct positive residues sum to `≥ N(N+1)/2`
  have hinj_coe : Set.InjOn r ↑(Finset.range N) := by
    rw [Finset.coe_range]; exact hinj
  have hcard : (Finset.image r (Finset.range N)).card = N := by
    rw [Finset.card_image_of_injOn hinj_coe, Finset.card_range]
  have hpos_img : ∀ x ∈ Finset.image r (Finset.range N), 1 ≤ x := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact hpos i (Finset.mem_range.mp hi)
  have htri := Erdos260.P2TrustBoundary.o3_triangular N
    (Finset.image r (Finset.range N)) hcard hpos_img
  have hsum_img : ∑ x ∈ Finset.image r (Finset.range N), x
      = ∑ i ∈ Finset.range N, r i := Finset.sum_image hinj_coe
  rw [hsum_img] at htri
  -- htri : N*(N+1) ≤ 2 * (Σ r_i);  htel : (Σ r_i) + r 0 = q*E + r N;  hbound : r N < q
  nlinarith [htri, htel, hbound, Nat.zero_le (r 0)]

/-- **Lemma 25.2 (25.2a), real form** — the manuscript inequality verbatim:
    the segment ones-count is `≥ N(N+1)/(2q) − 1`. -/
theorem segment_density_real
    (q N : ℕ) (hq : 0 < q) (r : ℕ → ℕ)
    (hpos : ∀ i, i < N → 1 ≤ r i)
    (hbound : r N < q)
    (hstep : ∀ i, i < N → r (i + 1) = (2 * r i) % q)
    (hinj : Set.InjOn r (Set.Iio N)) :
    (N : ℝ) * (N + 1) / (2 * q) - 1
      ≤ ((∑ i ∈ Finset.range N, (2 * r i) / q : ℕ) : ℝ) := by
  have hcore := segment_density_core q N r hpos hbound hstep hinj
  have hqR : (0 : ℝ) < 2 * (q : ℝ) := by positivity
  have hcast : (N : ℝ) * ((N : ℝ) + 1)
      ≤ 2 * (q : ℝ) * (((∑ i ∈ Finset.range N, (2 * r i) / q : ℕ) : ℝ) + 1) := by
    exact_mod_cast hcore
  rw [sub_le_iff_le_add, div_le_iff₀ hqR]
  nlinarith [hcast]

/-! ===========================================================================
    LEAF 3 — concrete instantiation to the doubling orbit of `a/q`.

    For odd `q ≥ 3`, the unit `2 ∈ (ZMod q)ˣ` is the doubling; the residues
    `r_j = (u^j a).val ∈ {1,…,q-1}` realize the binary expansion of `a/q`, and on
    any block `[0, N)` with `N ≤ t = ord_q(2)` they are distinct
    (`o3_doubling_orbit_injective`).  Hence the §25.2 floor holds for the genuine
    binary digits of `a/q`.
    =========================================================================== -/

/-- **Lemma 25.2 for the doubling orbit.**  With `q ≥ 3`, `u, a` units of
    `ZMod q` with `(u : ZMod q) = 2`, and a segment length `N ≤ ord_q(2)`, the
    number of binary one-digits in positions `[0, N)` of `a/q`,
    `E = Σ_{i<N} (2 r_i)/q` with `r_i = (u^i a).val`, satisfies
    `N (N+1) ≤ 2 q (E + 1)`. -/
theorem segment_density_orbit {q : ℕ} (hq : 3 ≤ q) (u a : (ZMod q)ˣ)
    (hu : (u : ZMod q) = 2) (N : ℕ) (hN : N ≤ orderOf u) :
    N * (N + 1) ≤ 2 * q *
      ((∑ i ∈ Finset.range N,
          (2 * ((u ^ i * a : (ZMod q)ˣ) : ZMod q).val) / q) + 1) := by
  haveI : NeZero q := ⟨by omega⟩
  haveI : Fact (1 < q) := ⟨by omega⟩
  have hval2 : ((2 : ZMod q)).val = 2 := by
    have h : ((2 : ℕ) : ZMod q) = (2 : ZMod q) := by norm_cast
    rw [← h, ZMod.val_natCast]
    exact Nat.mod_eq_of_lt (by omega)
  have hpos : ∀ i, i < N → 1 ≤ ((u ^ i * a : (ZMod q)ˣ) : ZMod q).val := by
    intro i _
    rw [Nat.one_le_iff_ne_zero]
    intro hzero
    have hx0 : ((u ^ i * a : (ZMod q)ˣ) : ZMod q) = 0 :=
      ZMod.val_injective q (by rw [ZMod.val_zero]; exact hzero)
    exact (Units.ne_zero (u ^ i * a)) hx0
  have hbound : ((u ^ N * a : (ZMod q)ˣ) : ZMod q).val < q := ZMod.val_lt _
  have hstep : ∀ i, i < N →
      ((u ^ (i + 1) * a : (ZMod q)ˣ) : ZMod q).val
        = (2 * ((u ^ i * a : (ZMod q)ˣ) : ZMod q).val) % q := by
    intro i _
    have hunit : (u ^ (i + 1) * a : (ZMod q)ˣ) = u * (u ^ i * a) := by
      rw [pow_succ', mul_assoc]
    have hx : ((u ^ (i + 1) * a : (ZMod q)ˣ) : ZMod q)
            = (2 : ZMod q) * ((u ^ i * a : (ZMod q)ˣ) : ZMod q) := by
      rw [hunit]; push_cast; rw [hu]
    rw [hx, ZMod.val_mul, hval2]
  have hinj : Set.InjOn (fun j : ℕ => ((u ^ j * a : (ZMod q)ˣ) : ZMod q).val)
      (Set.Iio N) := by
    have hfull : Set.InjOn (fun j : ℕ => ((u ^ j * a : (ZMod q)ˣ) : ZMod q).val)
        (Set.Iio (orderOf u)) := by
      intro x hx y hy hxy
      have h1 : ((u ^ x * a : (ZMod q)ˣ) : ZMod q) = ((u ^ y * a : (ZMod q)ˣ) : ZMod q) :=
        ZMod.val_injective q hxy
      have h2 : (u ^ x * a : (ZMod q)ˣ) = (u ^ y * a : (ZMod q)ˣ) := Units.ext h1
      exact Erdos260.P2TrustBoundary.o3_doubling_orbit_injective u a hx hy h2
    exact hfull.mono (Set.Iio_subset_Iio hN)
  exact segment_density_core q N
    (fun i => ((u ^ i * a : (ZMod q)ˣ) : ZMod q).val) hpos hbound hstep hinj

/-- **Lemma 25.2 for the doubling orbit, real form (25.2a).**  The binary
    ones-density of `a/q` on `[0, N)` (`N ≤ ord_q(2)`) is `≥ N(N+1)/(2q) − 1`. -/
theorem segment_density_orbit_real {q : ℕ} (hq : 3 ≤ q) (u a : (ZMod q)ˣ)
    (hu : (u : ZMod q) = 2) (N : ℕ) (hN : N ≤ orderOf u) :
    (N : ℝ) * (N + 1) / (2 * q) - 1
      ≤ ((∑ i ∈ Finset.range N,
            (2 * ((u ^ i * a : (ZMod q)ˣ) : ZMod q).val) / q : ℕ) : ℝ) := by
  have hcore := segment_density_orbit hq u a hu N hN
  have hqR : (0 : ℝ) < 2 * (q : ℝ) := by positivity
  have hcast : (N : ℝ) * ((N : ℝ) + 1)
      ≤ 2 * (q : ℝ) * (((∑ i ∈ Finset.range N,
            (2 * ((u ^ i * a : (ZMod q)ˣ) : ZMod q).val) / q : ℕ) : ℝ) + 1) := by
    exact_mod_cast hcore
  rw [sub_le_iff_le_add, div_le_iff₀ hqR]
  nlinarith [hcast]

/-! ===========================================================================
    LEAF 4 — the manuscript "≥ c₀ p ones" shape (dense branch).

    On the dense branch of Lemma 25.2 (period long enough that a block of length
    `N` with `βp ≤ N ≤ t` of distinct residues fits), with denominator `q ≤ Cp`,
    the ones-count is `≥ c₀ p` with the explicit constant `c₀ = β²/(2C)`
    (matching `c₀ = c₀(C,β) > 0`, lines 1737–1743):

        N(N+1)/(2q) − 1 ≥ N²/(2q) − 1 ≥ (βp)²/(2·Cp) − 1 = (β²/(2C)) p − 1.
    =========================================================================== -/

/-- **Lemma 25.2, "`≥ c₀ p` ones" (dense branch).**  Under the §25.2 carry /
    positivity / distinctness hypotheses on a block `[0, N)`, if additionally
    `0 < β`, `0 < p`, `q ≤ C p` and `β p ≤ N`, then the ones-count exceeds
    `(β²/(2C)) p − 1`; i.e. the segment-density constant is `c₀ = β²/(2C) > 0`. -/
theorem segment_density_const
    (q N p : ℕ) (C β : ℝ) (hq : 0 < q) (r : ℕ → ℕ)
    (hpos : ∀ i, i < N → 1 ≤ r i) (hbound : r N < q)
    (hstep : ∀ i, i < N → r (i + 1) = (2 * r i) % q)
    (hinj : Set.InjOn r (Set.Iio N))
    (hβ : 0 < β) (hp : 0 < p)
    (hqCp : (q : ℝ) ≤ C * p) (hNβp : β * p ≤ (N : ℝ)) :
    (β ^ 2 / (2 * C)) * p - 1 ≤ ((∑ i ∈ Finset.range N, (2 * r i) / q : ℕ) : ℝ) := by
  have hreal := segment_density_real q N hq r hpos hbound hstep hinj
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hNR : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hCpos : 0 < C := by
    by_contra h
    rw [not_lt] at h
    have hCp : C * (p : ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (le_of_lt hpR)
    linarith [hqCp, hqR]
  -- `(β²/(2C)) p ≤ N(N+1)/(2q)`
  have hkey : (β ^ 2 / (2 * C)) * p ≤ (N : ℝ) * ((N : ℝ) + 1) / (2 * q) := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    -- goal: (β²·p)·(2·q) ≤ (N·(N+1))·(2·C)
    have e1 : (0 : ℝ) ≤ ((N : ℝ) - β * p) * ((N : ℝ) + β * p) :=
      mul_nonneg (by linarith [hNβp]) (add_nonneg hNR (le_of_lt (mul_pos hβ hpR)))
    have e2 : (0 : ℝ) ≤ (C * p - q) * (β ^ 2 * p) :=
      mul_nonneg (by linarith [hqCp]) (mul_nonneg (sq_nonneg β) (le_of_lt hpR))
    have e3 : (0 : ℝ) ≤ C * (N : ℝ) := mul_nonneg (le_of_lt hCpos) hNR
    nlinarith [e1, e2, e3, hCpos, hβ, hpR, hqR]
  linarith [hreal, hkey]

end Erdos260.Lemma252SegmentDensity
