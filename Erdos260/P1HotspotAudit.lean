/-
  P1 hotspot audit (O1–O4): error-prone arithmetic/logic kernels.

  Purpose.  Each P1 core mixes (a) a finite/arithmetic/logical KERNEL with
  (b) a structural/dynamical claim about the carry recurrence.  This file machine-
  checks the kernels (a).  The structural claims (b) appear as explicit HYPOTHESES;
  they are the trust boundary that formalizing the kernel does NOT discharge, and
  each is flagged in a comment "TRUST BOUNDARY".

  Every lemma is standalone (depends only on Mathlib), so a reviewer sees exactly
  what is certified and what is assumed.

  NOTE: the author was unable to run `lake build` in the audit session; build with
  `lake build Erdos260.P1HotspotAudit`.  Proofs are elementary; any failure should
  be a Mathlib name/signature tweak, not a mathematical gap.
-/
import Mathlib

namespace Erdos260.P1HotspotAudit

open Finset

/-! ===========================================================================
    O2 — faithful (start,threshold) indexing  ⇒  ambient mass bound
    Manuscript: lem:ak-faithful-start-threshold-indexing, lem:ak-ambient-support-bound.

    TRUST BOUNDARY (`hmaps`,`hinj`): the post-priority event carrier really injects
    into the start×threshold rectangle, i.e. (x,T) determines the event.
    KERNEL: an injection into a finite rectangle bounds carrier card by rect card
    (`M_tot ≤ X·|I_j|`).
    =========================================================================== -/

theorem o2_faithful_mass_bound
    {Ω β : Type*} (carrier : Finset Ω) (rect : Finset β) (π : Ω → β)
    (hmaps : ∀ ω ∈ carrier, π ω ∈ rect)
    (hinj : Set.InjOn π carrier) :
    carrier.card ≤ rect.card :=
  Finset.card_le_card_of_injOn π hmaps hinj

/-! ===========================================================================
    O1.A — high-support phase count  Σ_λ c_λ · R ≤ N   (the v70 P0.1 fix)
    Manuscript: lem:i-high-support-cycle-phase-count.

    TRUST BOUNDARY (`hbig`,`hdisj`,`hsub`,`hUcard`): each selected phase owns ≥ R
    realized starts (tower-high); distinct phases own DISJOINT starts (= O2); all
    starts live in the active shell of size ≤ N (= O_Q(X)).
    KERNEL: disjoint sets each of card ≥ R inside a universe of card ≤ N force
    (#phases)·R ≤ N.
    =========================================================================== -/

theorem o1_high_support_count
    {ι α : Type*} [DecidableEq α]
    (P : Finset ι) (U : Finset α) (own : ι → Finset α) (R N : ℕ)
    (hsub : ∀ i ∈ P, own i ⊆ U)
    (hUcard : U.card ≤ N)
    (hbig : ∀ i ∈ P, R ≤ (own i).card)
    (hdisj : ∀ i ∈ P, ∀ j ∈ P, i ≠ j → Disjoint (own i) (own j)) :
    P.card * R ≤ N := by
  have hbu : (P.biUnion own).card = ∑ i ∈ P, (own i).card :=
    Finset.card_biUnion hdisj
  have hle : (P.biUnion own).card ≤ U.card :=
    Finset.card_le_card (Finset.biUnion_subset.mpr hsub)
  have hsum : P.card * R ≤ ∑ i ∈ P, (own i).card := by
    have h := Finset.sum_le_sum hbig
    simpa [Finset.sum_const, smul_eq_mul] using h
  calc P.card * R ≤ ∑ i ∈ P, (own i).card := hsum
    _ = (P.biUnion own).card := hbu.symm
    _ ≤ U.card := hle
    _ ≤ N := hUcard

/-- O1.A magnitude surrogate: once the high-support threshold dominates any fixed
    power of the log factor (`L^A ≤ R`, true for `R = X^{1/2+ρ}`, `L = log₂X`), the
    exposure-weighted phase count stays `≤ N = O_Q(X)`.  (The genuine `o(X)` is this
    with `R/L^A → ∞`; here we certify the `O(X)` step, which is the load-bearing
    cancellation.) -/
theorem o1_weighted_count_le (L A M R N : ℕ)
    (hcount : M * R ≤ N) (hRdom : L ^ A ≤ R) :
    L ^ A * M ≤ N := by
  calc L ^ A * M ≤ R * M := Nat.mul_le_mul hRdom (le_refl M)
    _ = M * R := Nat.mul_comm R M
    _ ≤ N := hcount

/-! ===========================================================================
    O1.B — ambient domination of exit mass  ExitMass(F) ≤ (b/c)·M_tot
    Manuscript: lem:al-complete-lap (AL.7), prop:r-exit-share-closed (R.2′).

    TRUST BOUNDARY (`hexit_le`): the retained exit-light fibre's exit part lies in
    the `b` ambient exit-phase fibres, each of equal mass `Cmass` (complete-lap atlas).
    KERNEL: integer form of `ExitMass(F) ≤ (b/c)·M_tot`, `M_tot = c·Cmass`, valid
    even if F is phase-concentrated (no per-fibre saturation needed).
    =========================================================================== -/

theorem o1_ambient_domination
    (b c Cmass exitMassF : ℕ)
    (hexit_le : exitMassF ≤ b * Cmass) :
    c * exitMassF ≤ b * (c * Cmass) := by
  calc c * exitMassF ≤ c * (b * Cmass) := Nat.mul_le_mul (le_refl c) hexit_le
    _ = b * (c * Cmass) := by ring

/-! ===========================================================================
    O3 — §24 distinct-residue density floor + constant consistency
    Manuscript: Lemma 24.1, Lemma 24.2, lem:fixed-slope-exact-completion, Conv 2.0f.
    =========================================================================== -/

/-- KERNEL of Lemma 24.1: with `∑ residues = q·k` and `q ≤ C·t`, the triangular
    bound `t(t+1) ≤ 2·∑` forces `t+1 ≤ 2·C·k` (i.e. density `k/t ≥ 1/(2C)`).
    TRUST BOUNDARY (`htri`): the textbook fact that `t` distinct positive integers
    sum to ≥ `t(t+1)/2`. -/
theorem o3_density_floor_arith
    (q t k C : ℕ) (ht : 1 ≤ t)
    (htri : t * (t + 1) ≤ 2 * (q * k))
    (hqCt : q ≤ C * t) :
    t + 1 ≤ 2 * C * k := by
  have hp : q * k ≤ C * t * k := Nat.mul_le_mul hqCt (le_refl k)
  have key : t * (t + 1) ≤ t * (2 * C * k) := by nlinarith [htri, hp]
  exact Nat.le_of_mul_le_mul_left key ht

/-- Constant consistency (Convention 2.0f vs §24 floor): the sparse cap
    `c_* < 1/(6Q)` lies strictly below the genuine density floor `1/(3Q)`, so a
    retained bounded-period pin (density ≥ 1/(3Q)) contradicts sparsity. -/
theorem o3_floor_above_cap (Q : ℕ) (hQ : 1 ≤ Q) (cstar : ℚ)
    (hc : cstar < 1 / (6 * Q)) : cstar < 1 / (3 * Q) := by
  have hQ0 : (0 : ℚ) < (Q : ℚ) := by exact_mod_cast (show 0 < Q by omega)
  have h3 : (3 * (Q : ℚ)) ≠ 0 := by positivity
  have h6 : (6 * (Q : ℚ)) ≠ 0 := by positivity
  have e : (1 : ℚ) / (3 * Q) - 1 / (6 * Q) = 1 / (6 * Q) := by field_simp; ring
  have hpos : (0 : ℚ) < 1 / (6 * Q) := by positivity
  linarith [e, hpos]

/-! ===========================================================================
    O4.a — cocycle telescoping  Δ_B = Δ_L + Δ_R  (midpoint cancels)
    Manuscript: lem:y-boundary-cocycle, AS.2e.  No trust boundary (pure identity).
    =========================================================================== -/

theorem o4_cocycle {G : Type*} [AddCommGroup G] (Ca Cm Cb : G) :
    (Cb - Ca) = (Cm - Ca) + (Cb - Cm) := by abel

/-- The composed child transfer from the neutral state lands at Δ_B:
    translate 0 by Δ_L then by Δ_R to reach Δ_L+Δ_R = Δ_B (so the off-neutral
    charge below is read at Δ_B). -/
theorem o4_transfer_lands_at_cocycle {G : Type*} [AddCommGroup G] (Ca Cm Cb : G) :
    (0 + (Cm - Ca)) + (Cb - Cm) = (Cb - Ca) := by abel

/-! ===========================================================================
    O4.b — class-1 valuation floor  ϑ₁ = 1  (off-neutral indicator)
    Manuscript: lem:as-finite-h5-classone-table, def:as-h5-cut-kernel.

    TRUST BOUNDARY: that the actual H.5 class-1 row charge equals the off-neutral
    mass of the composed transfer, i.e. `R^{H5}_1 = 1_{Δ_B≠0}`
    (lem:j-classone-residual-subslot — the ledger audit — NOT checkable here).
    KERNEL: GIVEN the off-neutral-indicator form, the charge is 0 on the neutral
    class and ≥ ϑ₁ = 1 on every nonzero class; and a positive class-1 excess (sum
    of nonneg charges) must expose a nonzero-class row of positive weight.
    =========================================================================== -/

/-- `w₁(δ) = ‖(I-P₀)e_δ‖² = 1_{δ≠0}` (off-neutral mass of a single basis state). -/
noncomputable def w1 {G : Type*} [DecidableEq G] (zero δ : G) : ℚ :=
  if δ = zero then 0 else 1

theorem o4_floor_zero {G : Type*} [DecidableEq G] (zero : G) :
    w1 zero zero = 0 := by simp [w1]

theorem o4_floor_pos {G : Type*} [DecidableEq G] (zero δ : G) (hδ : δ ≠ zero) :
    (1 : ℚ) ≤ w1 zero δ := by simp [w1, hδ]

/-- O4.b consequence: a positive corrected class-1 excess forces a nonzero-class
    row of positive weight (existence-of-positive-term WITH floor ϑ₁ = 1).  This is
    exactly the quantitative faithful-realization input flagged as the missing
    "carry-valuation floor". -/
theorem o4_excess_exposes_nonzero
    {ι G : Type*} [DecidableEq G] (zero : G)
    (S : Finset ι) (Δ : ι → G) (wt : ι → ℚ)
    (hwt : ∀ i ∈ S, 0 ≤ wt i)
    (hpos : 0 < ∑ i ∈ S, wt i * w1 zero (Δ i)) :
    ∃ i ∈ S, Δ i ≠ zero ∧ 0 < wt i := by
  by_contra h
  simp only [not_exists, not_and, not_lt] at h
  have hzero : ∀ i ∈ S, wt i * w1 zero (Δ i) = 0 := by
    intro i hi
    rcases eq_or_ne (Δ i) zero with hΔ | hΔ
    · simp [w1, hΔ]
    · have hle : wt i ≤ 0 := h i hi hΔ
      have : wt i = 0 := le_antisymm hle (hwt i hi)
      simp [this]
  rw [Finset.sum_eq_zero hzero] at hpos
  exact lt_irrefl _ hpos

/-! ===========================================================================
    O4.c — Y priority-heredity descent  ⇒  no class-1 atom at any depth
    Manuscript: lem:y-priority-heredity, prop:y-bisection-defect-empty, X.2.

    TRUST BOUNDARY (`hstep`,`hbase`): `hstep` is priority heredity (a retained
    depth-(v+1) atom has a retained depth-v child — from lem:y-priority-monotone);
    `hbase` is depth-0 emptiness (one-cell parity).
    KERNEL: the well-founded descent itself forces emptiness at every depth.
    =========================================================================== -/

theorem o4_descent_no_atom (Atom : ℕ → Prop)
    (hbase : ¬ Atom 0)
    (hstep : ∀ v, Atom (v + 1) → Atom v) :
    ∀ v, ¬ Atom v := by
  intro v
  induction v with
  | zero => exact hbase
  | succ n ih => intro h; exact ih (hstep n h)

/-- Realization bridge skeleton (AA/AN): emptiness of the formal-atom family
    transports back to the retained-row family along the mass-preserving map.
    TRUST BOUNDARY (`hmaps`): the ledger-row ↦ formal-atom map is total into the
    atom family (lem:aa-ledger-row-realizes-formal-row,
    lem:an-nonzero-row-formal-atom-equivalence).
    KERNEL: if the atom family is empty, no retained nonzero row exists, so a
    failed R2 cap (which would populate it) is impossible. -/
theorem o4_realization_empty
    {R A : Type*} (rows : Finset R) (atoms : Finset A) (real : R → A)
    (hmaps : ∀ r ∈ rows, real r ∈ atoms) (hatoms : atoms = ∅) :
    rows = ∅ := by
  rcases Finset.eq_empty_or_nonempty rows with h | ⟨r, hr⟩
  · exact h
  · exact absurd (hmaps r hr) (by simp [hatoms])

end Erdos260.P1HotspotAudit
