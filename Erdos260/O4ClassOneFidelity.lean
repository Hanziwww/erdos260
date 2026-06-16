/-
  O4 faithful class-1 realization / carry-valuation floor  (RISK / R2).

  Falsifiable arithmetic hotspots of the Erdős-#260 **O4 faithful class-1
  realization / carry-valuation floor** lane, formalized sorry-free.  Every
  theorem depends only on Mathlib plus the already-verified leaf files
  `Erdos260.P1HotspotAudit` and `Erdos260.P1LeavesB`; the genuine ledger SUPPLY
  (the row-to-formal-atom carrier map, priority heredity, depth-0 parity) appears
  as explicit hypotheses, so a reviewer sees exactly what is certified and what is
  assumed.

  Manuscript map (proof_v4_repaired_core_v71_p2_preprint_hygiene.tex):

  * Appendix AS — "Proof of AP3: H.5 class-1 fidelity" (§ at line 12604).
      def:as-h5-literal-transfer-row (12617): the literal transfer row
        `R^{H5}_1(ω) = ‖(I-P₀) T_{Δ_R} T_{Δ_L} e₀‖²`.
      def:as-h5-cut-kernel (12696): the character expansion `K^{H5}_1` (AS.0).
      lem:as-finite-h5-classone-table (12745): the central falsifiable identity
        `R^{H5}_1 = K^{H5}_1 = w₁(Δ_B)` (AS.2a) with floor `w₁(0)=0`,
        `w₁(δ)=1 (δ≠0)`, i.e. `ϑ₁ = 1` (AS.2b).
    Formalized here as `h5Charge_eq_indicator`, `h5CutKernel_eq_indicator`,
    `h5Charge_eq_cutKernel`, `h5Charge_eq_w1`, `h5Charge_floor`, `h5Charge_neutral`.

  * Appendix Y — "Formal midpoint-priority closure" (§ at line 10031).
      lem:y-boundary-cocycle (10130) / lem:y-midpoint-additivity (10157):
        `Δ_B = Δ_L + Δ_R` (Y.1a, Y.1).
      lem:y-nonzero-child (10172): `Δ_B ≠ 0 → Δ_L ≠ 0 ∨ Δ_R ≠ 0`.
      Y.3 midpoint table (10358) / prop:y-bisection-defect-empty (10382) /
      cor:y-classone-atom-voiding (10404): `𝔄^deep_{1,v} = ∅`.
    Formalized here (concretely on `G₁ = ZMod 6`) as `cocycle_additivity_zmod6`,
    `nonzero_child_zmod6`, `midpoint_table_zmod6`, and (the descent) `o4_excess_voids`.

  * Appendix AN — "Reducing the final class-1 realization bridge" (§ at line 11897).
      lem:an-nonzero-row-formal-atom-equivalence (11949): retained nonzero rows are
        exactly the formal class-1 atoms (mass-preserving carrier map).
      def:an-o4sharp (11991): the excess-support obligation (O4♯) (AN.3).
    The carrier map is the hypothesis `hrealize` of `o4_excess_voids`.

  * Appendix AO — "Class-1 excess support…" (§ at line 12050).
      lem:ao-zero-quotient-neutral (12081): `Δ_B = 0 ⇒ Γ₁ = 0` (AO.1).
      lem:ao-excess-supported-nonzero (12102): `𝒳_{1,v} ≤ Σ_{Δ_B≠0} Γ₁` (AO.2).
      prop:ao-o4sharp-discharged (12133): positive excess ⇒ positive nonzero mass.
    Formalized via `Erdos260.P1HotspotAudit.o4_excess_exposes_nonzero` inside
    `o4_excess_voids` / `o4_class1_cap`.

  * Appendix AA — "Faithful class-1 realization" (§ at line 10465).
      lem:aa-failure-exposes-row (10595), prop:aa-c2-closed (10615),
      cor:aa-r2-closed (10636): `¬(R2) ⇒ 𝔄≠∅`, hence (with Y voiding) `(R2)`.
    The full implication is `o4_excess_voids` / `o4_class1_cap`.

  No `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/
import Mathlib
import Erdos260.P1HotspotAudit
import Erdos260.P1LeavesB

namespace Erdos260.O4ClassOneFidelity

open Finset
open Erdos260.P1HotspotAudit Erdos260.P1LeavesB

/-! ===========================================================================
    Hotspot 1.  H.5 transfer-mass fidelity identity  (Appendix AS, the central
    falsifiable point).

    We model the class-1 group algebra `ℂ[G₁]` as functions `G₁ → ℂ`, with the
    standard basis vectors `e_g`, the translation operators `T_α e_g = e_{g+α}`
    (def:as-h5-literal-transfer-row, AS.0a), and the off-neutral ℓ²-mass
    functional `‖(I-P₀)·‖²` (the projection away from the neutral line `ℂ e₀`).

    The actual H.5 row charge is the off-neutral mass of the composed child
    transfer applied to `e₀` (AS.0b).  We PROVE that this literal transfer mass
    equals the off-neutral indicator `1_{Δ_B ≠ 0}` (so it equals the boundary
    defect functional `w₁(Δ_B)` of AS.1a and the character kernel `K^{H5}_1` of
    AS.0), reusing `o4_cocycle` (Δ_B = Δ_L + Δ_R) and `o4_character_floor`
    (the Fourier/Pontryagin floor `ϑ₁ = 1`).  This is the "faithfulness" that the
    manuscript only asserted.
    =========================================================================== -/

section Fidelity

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Standard basis vector `e_g` of the class-1 group algebra `ℂ[G₁]`. -/
def basisVec (g : G) : G → ℂ := fun x => if x = g then 1 else 0

/-- Translation operator `T_α` on `ℂ[G₁]`: `(T_α f)(x) = f(x - α)`
    (def:as-h5-literal-transfer-row, AS.0a).  See `transferOp_basisVec` for the
    basic identity `T_α e_g = e_{g+α}`. -/
def transferOp (α : G) (f : G → ℂ) : G → ℂ := fun x => f (x - α)

/-- Off-neutral mass `‖(I - P₀) f‖²`, where `P₀` is orthogonal projection onto the
    neutral basis line `ℂ e₀`.  Concretely the squared ℓ²-mass of `f` away from the
    neutral coordinate (def:as-h5-literal-transfer-row, AS.0b). -/
noncomputable def offNeutralMass (f : G → ℂ) : ℝ :=
  ∑ x : G, if x = 0 then (0 : ℝ) else ‖f x‖ ^ 2

omit [Fintype G] in
/-- `T_α e_g = e_{g+α}`: translations act on basis states by addition (AS.0a). -/
theorem transferOp_basisVec (α g : G) :
    transferOp α (basisVec g) = basisVec (g + α) := by
  funext x
  simp only [transferOp, basisVec]
  by_cases h : x = g + α
  · have h' : x - α = g := by rw [h]; abel
    rw [if_pos h', if_pos h]
  · have h' : x - α ≠ g := by
      intro hc; exact h (by rw [← hc]; abel)
    rw [if_neg h', if_neg h]

/-- The off-neutral mass of a single basis state is the off-neutral indicator
    `‖(I-P₀) e_δ‖² = 1_{δ ≠ 0}` (this is `w₁` of AS.1a evaluated on a basis vector). -/
theorem offNeutralMass_basisVec (δ : G) :
    offNeutralMass (basisVec δ) = if δ = 0 then (0 : ℝ) else 1 := by
  unfold offNeutralMass basisVec
  by_cases hδ : δ = 0
  · subst hδ
    rw [if_pos rfl]
    apply Finset.sum_eq_zero
    intro x _
    by_cases hx : x = 0
    · rw [if_pos hx]
    · rw [if_neg hx]; simp [hx, pow_two]
  · rw [if_neg hδ, Finset.sum_eq_single δ]
    · rw [if_neg hδ, if_pos rfl]; simp
    · intro x _ hx
      by_cases hx0 : x = 0
      · rw [if_pos hx0]
      · rw [if_neg hx0, if_neg hx]; simp [pow_two]
    · intro h; exact absurd (Finset.mem_univ δ) h

/-- The actual H.5 class-1 row charge: the off-neutral output mass of the composed
    child transfer `T_{Δ_R} T_{Δ_L}` applied to the neutral state `e₀`
    (def:as-h5-literal-transfer-row, AS.0b), with `Δ_L = π₁(C_m)-π₁(C_a)`,
    `Δ_R = π₁(C_b)-π₁(C_m)`. -/
noncomputable def h5Charge (Ca Cm Cb : G) : ℝ :=
  offNeutralMass (transferOp (Cb - Cm) (transferOp (Cm - Ca) (basisVec 0)))

/-- The H.5 class-1 cut kernel `K^{H5}_1` (def:as-h5-cut-kernel, AS.0): the
    character expansion of the off-neutral scalar. -/
noncomputable def h5CutKernel (Ca Cm Cb : G) : ℂ :=
  1 - (1 / (Fintype.card G : ℂ)) * ∑ χ : AddChar G ℂ, χ (Cm - Ca) * χ (Cb - Cm)

/-- **Faithful transfer-mass identity (AS.2a, AS.2c–2e).**  The literal H.5 row
    charge equals the off-neutral indicator `1_{Δ_B ≠ 0}`.  Proof: the two child
    transfers compose to a single translation `T_{Δ_R} T_{Δ_L} e₀ = e_{Δ_L+Δ_R}`
    (`transferOp_basisVec`), the midpoint label cancels by the cocycle
    `Δ_L+Δ_R = Δ_B` (`o4_cocycle`, AS.2e), and the off-neutral mass of a basis
    state is the indicator (`offNeutralMass_basisVec`). -/
theorem h5Charge_eq_indicator (Ca Cm Cb : G) :
    h5Charge Ca Cm Cb = if (Cb - Ca) = 0 then (0 : ℝ) else 1 := by
  have hcomp : transferOp (Cb - Cm) (transferOp (Cm - Ca) (basisVec (0 : G)))
      = basisVec (Cb - Ca) := by
    rw [transferOp_basisVec, transferOp_basisVec, zero_add, ← o4_cocycle Ca Cm Cb]
  unfold h5Charge
  rw [hcomp, offNeutralMass_basisVec]

/-- **Character-kernel identity (AS.2a, AS.2d).**  The H.5 cut kernel `K^{H5}_1`
    also equals the off-neutral indicator.  Proof: additive characters are
    multiplicative (`AddChar.map_add_eq_mul`), so `χ(Δ_L)χ(Δ_R) = χ(Δ_L+Δ_R) =
    χ(Δ_B)` (`o4_cocycle`); the spectral floor `o4_character_floor` then evaluates
    the resulting Fourier sum to the indicator (Pontryagin/character orthogonality). -/
theorem h5CutKernel_eq_indicator (Ca Cm Cb : G) :
    h5CutKernel Ca Cm Cb = if (Cb - Ca) = 0 then (0 : ℂ) else 1 := by
  have hchar : ∀ χ : AddChar G ℂ, χ (Cm - Ca) * χ (Cb - Cm) = χ (Cb - Ca) := by
    intro χ
    rw [← AddChar.map_add_eq_mul χ (Cm - Ca) (Cb - Cm), ← o4_cocycle Ca Cm Cb]
  unfold h5CutKernel
  simp_rw [hchar]
  exact o4_character_floor (Cb - Ca)

/-- **AS.2a in full: `R^{H5}_1 = K^{H5}_1`.**  The literal stopped-recursion
    transfer mass coincides (after the real→complex coercion) with the character
    cut kernel.  This is the faithful identification of the actual H.5 row charge
    with the boundary-defect functional. -/
theorem h5Charge_eq_cutKernel (Ca Cm Cb : G) :
    ((h5Charge Ca Cm Cb : ℝ) : ℂ) = h5CutKernel Ca Cm Cb := by
  rw [h5Charge_eq_indicator, h5CutKernel_eq_indicator]
  split_ifs <;> simp

/-- **AS.2a / AS.1a: `R^{H5}_1 = w₁(Δ_B)`.**  The faithful H.5 charge equals the
    `w₁` boundary-defect valuation of `Erdos260.P1HotspotAudit`. -/
theorem h5Charge_eq_w1 (Ca Cm Cb : G) :
    h5Charge Ca Cm Cb = ((w1 (0 : G) (Cb - Ca) : ℚ) : ℝ) := by
  rw [h5Charge_eq_indicator]
  simp only [w1]
  split_ifs <;> simp

/-- **AS.2b: the neutral class is not charged** (`w₁(0) = 0`). -/
theorem h5Charge_neutral (Ca Cm Cb : G) (h : Cb - Ca = 0) :
    h5Charge Ca Cm Cb = 0 := by
  rw [h5Charge_eq_indicator, if_pos h]

/-- **AS.2b: the class-1/band-4 carry-valuation floor `ϑ₁ = 1`.**  Every
    off-neutral boundary defect contributes charge exactly `1` — the positive
    floor obtained from the actual stopped-recursion transfer row itself. -/
theorem h5Charge_floor (Ca Cm Cb : G) (h : Cb - Ca ≠ 0) :
    h5Charge Ca Cm Cb = 1 := by
  rw [h5Charge_eq_indicator, if_neg h]

/-- Nonnegativity of the faithful H.5 charge (it is a squared ℓ²-mass). -/
theorem h5Charge_nonneg (Ca Cm Cb : G) : 0 ≤ h5Charge Ca Cm Cb := by
  rw [h5Charge_eq_indicator]; split_ifs <;> norm_num

end Fidelity

/-! ===========================================================================
    Hotspot 2.  Cocycle additivity (Y.1) and the finite midpoint table (Y.2),
    concretely on the class-1 quotient `G₁ = ZMod 6`.

    These are the decidable finite checks the manuscript's `G₁` table is verified
    against (Appendix Y, lem:y-boundary-cocycle / lem:y-midpoint-additivity /
    lem:y-nonzero-child / the Y.3 midpoint table).  We verify them by exhaustion
    over the finite group via `decide` (NOT `native_decide`).
    =========================================================================== -/

section ZMod6

/-- Concrete instantiation of the faithful H.5 transfer-mass identity on the
    representative class-1 quotient `G₁ = ZMod 6` (Appendix AS on the finite
    quotient automaton). -/
theorem h5Charge_zmod6 (Ca Cm Cb : ZMod 6) :
    h5Charge Ca Cm Cb = if (Cb - Ca) = 0 then (0 : ℝ) else 1 :=
  h5Charge_eq_indicator Ca Cm Cb

/-- Concrete `R^{H5}_1 = K^{H5}_1` on `G₁ = ZMod 6`. -/
theorem h5Charge_eq_cutKernel_zmod6 (Ca Cm Cb : ZMod 6) :
    ((h5Charge Ca Cm Cb : ℝ) : ℂ) = h5CutKernel Ca Cm Cb :=
  h5Charge_eq_cutKernel Ca Cm Cb

/-- **Boundary cocycle / midpoint additivity, Y.1a–Y.1, on `ZMod 6`.**
    `Δ_B = Δ_L + Δ_R` with `(Δ_L,Δ_R,Δ_B) = (m-a, b-m, b-a)`.  Verified by
    exhaustion over the finite quotient. -/
theorem cocycle_additivity_zmod6 :
    ∀ a m b : ZMod 6, (b - a) = (m - a) + (b - m) := by decide

/-- **Nonzero parent label has a nonzero child label (lem:y-nonzero-child)** on
    `ZMod 6`: if `Δ_B ≠ 0` then `Δ_L ≠ 0` or `Δ_R ≠ 0`. -/
theorem nonzero_child_zmod6 :
    ∀ a m b : ZMod 6, b - a ≠ 0 → (m - a ≠ 0 ∨ b - m ≠ 0) := by decide

/-- **The finite midpoint table (Y.2) on `ZMod 6`.**  The decidable content of the
    retained-parent midpoint classification:
    * both child labels neutral ⇒ parent neutral (row "0 / clean / 0":
      `Δ_B = 0`, not class-1);
    * a nonzero parent label is carried by at least one child (rows 3,4: a child
      is retained or the parent is terminal).
    Verified by exhaustion over the finite quotient. -/
theorem midpoint_table_zmod6 :
    ∀ a m b : ZMod 6,
      ((m - a = 0 ∧ b - m = 0) → b - a = 0) ∧
      (b - a ≠ 0 → (m - a ≠ 0 ∨ b - m ≠ 0)) := by decide

end ZMod6

/-! ===========================================================================
    Hotspot 3.  Excess ⇒ positive retained nonzero row ⇒ formal atom ⇒ void
    (Appendices AO + AN + Y; the faithful-realization implication of AA).

    Chain:
      `o4_excess_exposes_nonzero`  (AO: a positive class-1 excess, a sum of
        nonnegative `w₁(Δ_B)`-weighted charges, has a nonzero-quotient row of
        positive weight),
      `hrealize`  (AN: the mass-preserving row-to-formal-atom carrier map, taken
        as a hypothesis — `lem:an-nonzero-row-formal-atom-equivalence`),
      `o4_descent_no_atom`  (Y: priority-heredity well-founded descent voids the
        formal-atom family at every depth — `cor:y-classone-atom-voiding`),
      `o4_realization_empty`  (AA/AN: emptiness of the atom family forces the
        retained-row family empty).
    Conclusion: no positive class-1 excess can survive, i.e. the corrected class-1
    aligned cap (R2) holds (cor:aa-r2-closed / cor:ao-r2-unconditional).
    =========================================================================== -/

section Chain

/-- **Faithful-realization voiding (AA.2 + AO + Y).**  Given the mass-preserving
    carrier map `hrealize` (AN) and the priority-heredity descent data `hbase`
    (depth-0 parity void) and `hstep` (a depth-`w+1` atom has a depth-`w` child),
    a positive corrected class-1 excess `Σ_i wt_i · w₁(Δ_i)` is impossible.

    `S` is the post-priority retained-row carrier, `Δ` the projected class-1
    boundary quotient `Δ_B`, `wt` the nonnegative counting weight, `atomFamily v`
    the Appendix-Y formal class-1 atom family at depth `v`, and `realize` the
    `lem:an-nonzero-row-formal-atom-equivalence` carrier map. -/
theorem o4_excess_voids
    {ι A H : Type*} [DecidableEq H] (zero : H)
    (S : Finset ι) (Δ : ι → H) (wt : ι → ℚ)
    (atomFamily : ℕ → Finset A) (depth : ℕ) (realize : ι → A)
    (hwt : ∀ i ∈ S, 0 ≤ wt i)
    (hrealize : ∀ i ∈ S, Δ i ≠ zero → realize i ∈ atomFamily depth)
    (hbase : ¬ (atomFamily 0).Nonempty)
    (hstep : ∀ w, (atomFamily (w + 1)).Nonempty → (atomFamily w).Nonempty) :
    ¬ (0 < ∑ i ∈ S, wt i * w1 zero (Δ i)) := by
  intro hpos
  obtain ⟨i, hiS, hiΔ, _⟩ := o4_excess_exposes_nonzero zero S Δ wt hwt hpos
  have hvoid : ∀ w, ¬ (atomFamily w).Nonempty := o4_descent_no_atom _ hbase hstep
  have hempty : atomFamily depth = ∅ := Finset.not_nonempty_iff_eq_empty.mp (hvoid depth)
  have hmaps : ∀ r ∈ ({i} : Finset ι), realize r ∈ atomFamily depth := by
    intro r hr
    rw [Finset.mem_singleton] at hr
    subst r
    exact hrealize i hiS hiΔ
  have hsingle : ({i} : Finset ι) = ∅ :=
    o4_realization_empty {i} (atomFamily depth) realize hmaps hempty
  exact (Finset.singleton_ne_empty i) hsingle

/-- **The corrected class-1 aligned cap (R2)** (cor:aa-r2-closed /
    cor:ao-r2-unconditional): under the realization and descent hypotheses the
    corrected class-1 excess is `≤ 0`. -/
theorem o4_class1_cap
    {ι A H : Type*} [DecidableEq H] (zero : H)
    (S : Finset ι) (Δ : ι → H) (wt : ι → ℚ)
    (atomFamily : ℕ → Finset A) (depth : ℕ) (realize : ι → A)
    (hwt : ∀ i ∈ S, 0 ≤ wt i)
    (hrealize : ∀ i ∈ S, Δ i ≠ zero → realize i ∈ atomFamily depth)
    (hbase : ¬ (atomFamily 0).Nonempty)
    (hstep : ∀ w, (atomFamily (w + 1)).Nonempty → (atomFamily w).Nonempty) :
    ∑ i ∈ S, wt i * w1 zero (Δ i) ≤ 0 :=
  not_lt.mp
    (o4_excess_voids zero S Δ wt atomFamily depth realize hwt hrealize hbase hstep)

end Chain

end Erdos260.O4ClassOneFidelity
