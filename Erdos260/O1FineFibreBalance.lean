/-
  Erdős #260 — O1 fine-fibre measure-preservation core: the FALSIFIABLE
  arithmetic hotspots, formalized sorry-free in the kernel-with-hypotheses style.

  Scope.  This module (NEW; it edits no existing file) machine-checks the three
  error-prone "hearts" of the O1 fine-fibre complete-lap mass-balance lane of the
  v71 manuscript `proof_v4_repaired_core_v71_p2_preprint_hygiene.tex`.  The genuine
  measure-theoretic SUPPLY (existence of the complete-lap atlas, the phase charts,
  the start coordinate, the boundary little-oh estimate) is abstracted into
  explicit HYPOTHESES; what is certified here is the checkable arithmetic that the
  manuscript leans on, including the load-bearing NON-COVERING guard.

  Manuscript anchors
  ------------------
  * App R  "Fine-fibre complete-lap mass balance"            (§ starts line 8689)
      - Lemma `lem:r-global-phase-error`  (R.1b)             line 8779
      - Prop  `prop:r-exit-share-closed`  (R.2′ valid bound) line 8822
      - Lemma `lem:r-strong-share-not-from-saturation` (R.2 FALSE) line 8844
  * App AL "Same-carrier consequences of a certified fine-fibre cyclic atlas"
                                                              (§ starts line 11582)
      - Lemma `lem:al-successor-same-carrier-bijection`      line 11645
      - Lemma `lem:al-cyclic-bad-carrier-exposure-owned` (AL.4) line 11673
      - Lemma `lem:al-complete-lap` (AL.6 phase masses equal; AL.7) line 11721
  * App AQ "Proof of AP1: fine-fibre cyclic-atlas closure"   (§ starts line 12186)
      - Lemma `lem:aq-simple-cycle-atlas-row` (AQ.5/AQ.6, the affine relabelling
        and the start-coordinate injectivity argument)       line 12266
      - Lemma `lem:aq-failed-atlas-paid` (Bij_a: x ↦ x+g injective on ℤ) line 12338

  Hotspots formalized
  -------------------
  (1) The spaced-share NON-COVERING guard (highest-value falsifiable point).  The
      proportional total-exit share  `ExitMass(F) ≤ (b/c)·ExitMass(Tot)` (R.2 false)
      does NOT follow from spacing / phase balance.  We give a clean separation:
      the witness `F = Tot` (phase-uniform interior) satisfies the VALID
      mass-normalized identity `c·ExitMass(F) = b·M_tot` yet REFUTES the
      proportional share, plus a concrete `b=1,c=2` numeric witness and a rational
      "mass exceeds (b/c) of the total" form.  In-tree mirror:
      `emfc_spacedShare_not_covering` (Erdos260.ExitMassFamilyClosure).
  (2) Fine-fibre injectivity via start-coordinate translation + ambient domination
      (App AQ).  The per-fibre affine relabelling `u ↦ ambient(start u + G)` is
      injective; injectivity ⇒ the count/mass inequality `|C_λ| ≤ |Ω_a|`, reusing
      the same `card_le_card_of_injOn` kernel as `o1_ambient_domination`.
  (3) Complete-lap phase-mass identity (App AL/R).  The mass-normalized balance
      `c·ExitMass(F) = b·M_tot` on the common carrier (equality form), with the
      incomplete-lap boundary controlled by the high-support count bound
      `Σ c_λ ≤ X/R` (reusing `sum_phasecount_le_div`).

  Reuse (imported): `o1_ambient_domination` (P1HotspotAudit),
  `sum_phasecount_le_div` (HighSupportPhaseCount),
  `functional_graph_has_periodic_point` (P1Leaves).

  No `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/
import Mathlib
import Erdos260.P1HotspotAudit
import Erdos260.HighSupportPhaseCount
import Erdos260.P1Leaves

namespace Erdos260.O1FineFibreBalance

open Finset

/-! ===========================================================================
    ## Section A.  Complete-lap phase-mass identity and the R.2′ valid bound.

    Manuscript: App AL Lemma `lem:al-complete-lap` (AL.6/AL.7, line 11721) and
    App R `lem:r-global-phase-error` (R.1b, line 8779), `prop:r-exit-share-closed`
    (R.2′, line 8822).

    We model the ambient complete-lap carrier by a finite phase set `phases`, a
    counting-measure phase mass `μ : φ → ℕ` (with `μ a = Mass(Ω°_{λ,a})`), and an
    exit-phase subset `E ⊆ phases` (`#E = b`, `#phases = c`).  "Complete-lap /
    phase-uniform" is the hypothesis `μ a = Cmass` for all phases (= |C_λ|, AL.6).
    No invariance of a retained subfibre under the cyclic successor is assumed.
    =========================================================================== -/

variable {φ : Type*}

/-- Total ambient phase mass `M_tot = Σ_a Mass(Ω_{λ,a})`. -/
def Mtot (phases : Finset φ) (μ : φ → ℕ) : ℕ := ∑ a ∈ phases, μ a

/-- Ambient exit mass `ExitMass(Tot) = Σ_{a ∈ E} Mass(Ω_{λ,a})` over the `b` exit
    phases `E`. -/
def exitMass (E : Finset φ) (μ : φ → ℕ) : ℕ := ∑ a ∈ E, μ a

/-- Phase-uniform total mass: `M_tot = c · Cmass` (every phase chart has the same
    finite domain `C_λ`, so all phase masses equal `|C_λ| = Cmass`; AL.6). -/
theorem Mtot_uniform (phases : Finset φ) (μ : φ → ℕ) (Cmass : ℕ)
    (huniform : ∀ a ∈ phases, μ a = Cmass) :
    Mtot phases μ = phases.card * Cmass := by
  unfold Mtot
  have h : ∑ a ∈ phases, μ a = ∑ _a ∈ phases, Cmass :=
    Finset.sum_congr rfl (fun a ha => huniform a ha)
  rw [h, Finset.sum_const, smul_eq_mul]

/-- Phase-uniform exit mass: `ExitMass(Tot) = b · Cmass`. -/
theorem exitMass_uniform (phases E : Finset φ) (μ : φ → ℕ) (Cmass : ℕ)
    (hE : E ⊆ phases) (huniform : ∀ a ∈ phases, μ a = Cmass) :
    exitMass E μ = E.card * Cmass := by
  unfold exitMass
  have h : ∑ a ∈ E, μ a = ∑ _a ∈ E, Cmass :=
    Finset.sum_congr rfl (fun a ha => huniform a (hE ha))
  rw [h, Finset.sum_const, smul_eq_mul]

/-- **Complete-lap phase-mass identity (AL.6 ⇒ R.1b, equality form).**
    On the phase-uniform common carrier the exit phases occupy exactly a `b/c`
    fraction of the total mass:  `c · ExitMass(Tot) = b · M_tot`.  This is the
    mass-normalized balance the corrected lane actually uses (the integer
    cross-multiplied form of `ExitMass(Tot) = (b/c) M_tot`). -/
theorem completeLap_phase_mass_identity (phases E : Finset φ) (μ : φ → ℕ) (Cmass : ℕ)
    (hE : E ⊆ phases) (huniform : ∀ a ∈ phases, μ a = Cmass) :
    phases.card * exitMass E μ = E.card * Mtot phases μ := by
  rw [exitMass_uniform phases E μ Cmass hE huniform, Mtot_uniform phases μ Cmass huniform]
  ring

/-- **R.2′ valid mass-normalized bound (`prop:r-exit-share-closed`, line 8822).**
    A retained subfibre `F` is described by its per-phase mass `fExit a ≤ μ a` on
    the exit phases (NO invariance / saturation assumed: phase concentration is
    allowed).  Its exit part is dominated by the ambient exit phases, hence
        `c · ExitMass(F) ≤ b · M_tot`.
    The proof routes through the imported integer kernel `o1_ambient_domination`
    (App R/AL ambient domination), exactly the manuscript's "by ambient
    domination, not by saturation of `F`". -/
theorem fineFibre_exitMass_valid_bound
    (phases E : Finset φ) (μ fExit : φ → ℕ) (Cmass : ℕ)
    (hE : E ⊆ phases) (huniform : ∀ a ∈ phases, μ a = Cmass)
    (hdom : ∀ a ∈ E, fExit a ≤ μ a) :
    phases.card * (∑ a ∈ E, fExit a) ≤ E.card * Mtot phases μ := by
  have hsub0 : (∑ a ∈ E, fExit a) ≤ ∑ a ∈ E, μ a := Finset.sum_le_sum hdom
  have hsub : (∑ a ∈ E, fExit a) ≤ E.card * Cmass := by
    rw [← exitMass_uniform phases E μ Cmass hE huniform]
    exact hsub0
  have key := Erdos260.P1HotspotAudit.o1_ambient_domination
    E.card phases.card Cmass (∑ a ∈ E, fExit a) hsub
  rwa [← Mtot_uniform phases μ Cmass huniform] at key

/-! ===========================================================================
    ## Section B.  The spaced-share NON-COVERING guard  (HOTSPOT 1 — highest value)

    Manuscript: App R Lemma `lem:r-strong-share-not-from-saturation` (R.2 FALSE),
    line 8844.  In-tree mirror: `emfc_spacedShare_not_covering`
    (Erdos260.ExitMassFamilyClosure).

    The manuscript explicitly WARNS that the proportional total-exit share
        `ExitMass(F) ≤ (b/c)·ExitMass(Tot)`         (R.2, FALSE)
    does NOT follow from phase balance / spacing.  Its witness is `F = Tot`
    interior, phase-uniform, `0 < b < c`, `M_tot > 0`: this `F` satisfies the
    VALID `c·ExitMass(F) = b·M_tot` but VIOLATES R.2.  We certify both the
    pure arithmetic kernel and the manuscript witness.
    =========================================================================== -/

/-- **NON-COVERING guard, pure kernel.**  If the exit phases carry positive mass
    (`0 < ExitMass(Tot)`) and there are strictly more phases than exit phases
    (`b < c`), then the proportional total-exit share, applied to a fibre `F`
    whose exit mass equals the ambient exit mass `ExitMass(Tot)` (e.g. `F = Tot`),
    is FALSE in the cross-multiplied integer form:
        ¬ ( c · ExitMass(F) ≤ b · ExitMass(Tot) ),   with ExitMass(F) = ExitMass(Tot).
    This is the load-bearing "do not over-claim" separation: spacing forces
    `b < c`, which makes the proportional share strictly fail. -/
theorem spacedShare_not_covering_of_pos
    (phases E : Finset φ) (μ : φ → ℕ)
    (hbc : E.card < phases.card) (hpos : 0 < exitMass E μ) :
    ¬ (phases.card * exitMass E μ ≤ E.card * exitMass E μ) :=
  not_le.mpr (mul_lt_mul_of_pos_right hbc hpos)

/-- **NON-COVERING guard, manuscript witness (`F = Tot`, phase-uniform).**
    On the phase-uniform interior carrier with `0 < b`, `b < c`, `0 < Cmass`, the
    proportional total-exit share `c·ExitMass(F) ≤ b·ExitMass(Tot)` is FALSE for
    `F = Tot`.  Manuscript R.2-false (line 8844). -/
theorem spacedShare_not_covering
    (phases E : Finset φ) (μ : φ → ℕ) (Cmass : ℕ)
    (hE : E ⊆ phases) (huniform : ∀ a ∈ phases, μ a = Cmass)
    (hb : 0 < E.card) (hbc : E.card < phases.card) (hC : 0 < Cmass) :
    ¬ (phases.card * exitMass E μ ≤ E.card * exitMass E μ) := by
  apply spacedShare_not_covering_of_pos phases E μ hbc
  rw [exitMass_uniform phases E μ Cmass hE huniform]
  exact mul_pos hb hC

/-- **The separation, packaged.**  On the phase-uniform interior carrier the
    VALID mass-normalized balance `c·ExitMass(Tot) = b·M_tot` holds, yet the
    proportional total-exit share `c·ExitMass(Tot) ≤ b·ExitMass(Tot)` FAILS.
    Together this is exactly `lem:r-strong-share-not-from-saturation`: phase
    balance does not deliver (R1)/(R.2), so the final proof must use only the
    mass-normalized (R.2′) bound of `fineFibre_exitMass_valid_bound`. -/
theorem spacedShare_separation
    (phases E : Finset φ) (μ : φ → ℕ) (Cmass : ℕ)
    (hE : E ⊆ phases) (huniform : ∀ a ∈ phases, μ a = Cmass)
    (hb : 0 < E.card) (hbc : E.card < phases.card) (hC : 0 < Cmass) :
    (phases.card * exitMass E μ = E.card * Mtot phases μ)
      ∧ ¬ (phases.card * exitMass E μ ≤ E.card * exitMass E μ) :=
  ⟨completeLap_phase_mass_identity phases E μ Cmass hE huniform,
   spacedShare_not_covering phases E μ Cmass hE huniform hb hbc hC⟩

/-- **Rational "mass exceeds (b/c) of the total" form.**  With `F = Tot`,
    `ExitMass(F) = ExitMass(Tot)`, the fibre's exit mass strictly EXCEEDS the
    `(b/c)`-share of the total's exit mass:
        (b/c) · ExitMass(Tot)  <  ExitMass(F).
    Concrete refutation of the proportional bound `ExitMass(F) ≤ (b/c)·ExitMass(Tot)`. -/
theorem spacedShare_ratio_strict
    (phases E : Finset φ) (μ : φ → ℕ)
    (hbc : E.card < phases.card) (hpos : 0 < exitMass E μ) :
    ((E.card : ℚ) / (phases.card : ℚ)) * (exitMass E μ : ℚ) < (exitMass E μ : ℚ) := by
  have hcpos : 0 < phases.card := lt_of_le_of_lt (Nat.zero_le _) hbc
  have hc0 : (0 : ℚ) < (phases.card : ℚ) := by exact_mod_cast hcpos
  have hM : (0 : ℚ) < (exitMass E μ : ℚ) := by exact_mod_cast hpos
  have hlt : (E.card : ℚ) / (phases.card : ℚ) < 1 := by
    rw [div_lt_one hc0]; exact_mod_cast hbc
  calc ((E.card : ℚ) / (phases.card : ℚ)) * (exitMass E μ : ℚ)
      < 1 * (exitMass E μ : ℚ) := mul_lt_mul_of_pos_right hlt hM
    _ = (exitMass E μ : ℚ) := one_mul _

/-- **Concrete finite witness** (`c = 2`, `b = 1`, every phase mass `1`).
    `phases = {0,1}`, `E = {0}`: then `M_tot = 2`, `ExitMass(Tot) = 1`, the VALID
    identity reads `2·1 = 1·2`, but the proportional total-exit share would force
    `2·1 ≤ 1·1`, i.e. `2 ≤ 1` — FALSE.  A self-contained counterexample showing
    the proportional share does not follow from spacing alone. -/
theorem spacedShare_concrete_witness :
    ¬ ( ({0, 1} : Finset ℕ).card * exitMass ({0} : Finset ℕ) (fun _ => 1)
          ≤ ({0} : Finset ℕ).card * exitMass ({0} : Finset ℕ) (fun _ => 1) ) := by
  apply spacedShare_not_covering ({0, 1} : Finset ℕ) ({0} : Finset ℕ) (fun _ => 1) 1
  · decide
  · intro a _; rfl
  · decide
  · decide
  · decide

/-! ===========================================================================
    ## Section C.  Fine-fibre injectivity via start-coordinate translation.
                                                          (HOTSPOT 2)

    Manuscript: App AQ `lem:aq-simple-cycle-atlas-row` (AQ.5/AQ.6, line 12266) and
    `lem:aq-failed-atlas-paid` (Bij_a, line 12363): the phase chart relabels a base
    event `u` to the transported event at the integer start `x(u) + G_a`; the
    target start map `x ↦ x + g` is injective on integers, so distinct fibre
    states map to distinct ambient states.  Injectivity ⇒ the per-phase ambient
    domination `|C_λ| ≤ |Ω_a|` (App AL `lem:al-successor-same-carrier-bijection`).

    The affine relabelling is taken as a HYPOTHESIS (the genuine analytic supply):
    an injective start coordinate `start : C → ℤ` and an injective ambient
    embedding `ambient : ℤ → Ω`.  We certify injectivity ⇒ the count/mass bound.
    =========================================================================== -/

/-- The target-start translation `x ↦ x + G` is injective on the integers
    (App AQ, `lem:aq-failed-atlas-paid`: "the target start is `x ↦ x + g_a`, which
    is injective on integers"). -/
theorem startTranslation_injective (G : ℤ) :
    Function.Injective (fun x : ℤ => x + G) := by
  intro a b h
  dsimp only at h
  omega

/-- The per-phase affine relabelling `ι_a : u ↦ ambient(start u + G_a)`
    (App AQ, AQ.5). -/
def fineRelabel {C Ω : Type*} (start : C → ℤ) (ambient : ℤ → Ω) (G : ℤ) : C → Ω :=
  fun u => ambient (start u + G)

/-- **Fine-fibre injectivity (App AQ, AQ.6 injectivity step).**  If the start
    coordinate `start` is injective on the fibre and the ambient embedding
    `ambient` is injective, then the per-phase relabelling is injective: distinct
    base events `u ≠ u'` have distinct ambient starts `x(u)+G ≠ x(u')+G`, hence map
    to distinct ambient states.  This is the fine-fibre replacement for the false
    "incoming-edge uniqueness in the recurrent vertex graph". -/
theorem fineRelabel_injective {C Ω : Type*}
    (start : C → ℤ) (ambient : ℤ → Ω) (G : ℤ)
    (hstart : Function.Injective start) (hamb : Function.Injective ambient) :
    Function.Injective (fineRelabel start ambient G) := by
  intro u u' h
  unfold fineRelabel at h
  have h2 : start u + G = start u' + G := hamb h
  exact hstart (by omega)

/-- **Injectivity ⇒ count/mass inequality (App AL `lem:al-complete-lap`, AL.7
    domination at the cardinality level).**  If the injective relabelling maps the
    base carrier `Cset` into the ambient phase fibre `ambientSet`, then
        |C_λ| = |Cset| ≤ |ambientSet| = Mass(Ω_a),
    the per-phase ambient domination.  Same `card_le_card_of_injOn` kernel as
    `o1_ambient_domination` / `o2_faithful_mass_bound`. -/
theorem fineFibre_card_le_ambient {C Ω : Type*}
    (Cset : Finset C) (ambientSet : Finset Ω)
    (start : C → ℤ) (ambient : ℤ → Ω) (G : ℤ)
    (hstart : Function.Injective start) (hamb : Function.Injective ambient)
    (hmaps : ∀ u ∈ Cset, fineRelabel start ambient G u ∈ ambientSet) :
    Cset.card ≤ ambientSet.card :=
  Finset.card_le_card_of_injOn (fineRelabel start ambient G) hmaps
    (fun _ _ _ _ h => fineRelabel_injective start ambient G hstart hamb h)

/-- **Same-carrier measure preservation (App AL `lem:al-successor-same-carrier-bijection`,
    AL.6).**  Two phase fibres `Ωa`, `Ωb` charted by the SAME finite carrier `Cset`
    via injective charts have equal counting mass `Mass(Ω_a) = |C_λ| = Mass(Ω_b)`.
    This is the measure-preservation consequence of the chart bijections (the
    successor `ι_{a+1} ∘ ι_a⁻¹` is a same-carrier bijection): all phase masses are
    equal, which is precisely the uniform hypothesis feeding Section A. -/
theorem fineFibre_phaseMass_eq {C Ω : Type*} [DecidableEq Ω]
    (Cset : Finset C) (Ωa Ωb : Finset Ω) (ιa ιb : C → Ω)
    (haInj : Set.InjOn ιa ↑Cset) (hbInj : Set.InjOn ιb ↑Cset)
    (haImg : Ωa = Cset.image ιa) (hbImg : Ωb = Cset.image ιb) :
    Ωa.card = Ωb.card := by
  rw [haImg, hbImg, Finset.card_image_of_injOn haInj, Finset.card_image_of_injOn hbInj]

/-- The phase set `ℤ/cℤ` of the cyclic atlas is genuinely realized: a finite
    functional successor graph (App E.6: each refined recurrent vertex has at most
    one recurrent outgoing edge) has a directed cycle, i.e. a periodic point.
    Re-exports the imported `functional_graph_has_periodic_point` (P1Leaves). -/
theorem recurrent_component_has_cycle {V : Type*} [Finite V] [Nonempty V] (f : V → V) :
    ∃ (x : V) (n : ℕ), 0 < n ∧ f^[n] x = x :=
  Erdos260.P1Leaves.functional_graph_has_periodic_point f

/-! ===========================================================================
    ## Section D.  Incomplete-lap bounded boundary.       (HOTSPOT 3b)

    Manuscript: App AL `lem:al-cyclic-bad-carrier-exposure-owned` (AL.4a–AL.4c,
    line 11673) and App AQ `lem:aq-boundary-exposure-owned` (line 12386).  The
    incomplete-lap part is NOT bounded pointwise by `c_λ = O_Q(L)`; it is bounded
    in AGGREGATE by the high-support phase count `Σ_λ c_λ ≤ X/R`
    (reusing `sum_phasecount_le_div`), times the per-lap displacement width
    `G_λ ≤ (L+O(1))·c_λ` (AL.4a) and the exposure weight `h_λ ≤ r+1 = O_Q(L)`.
    =========================================================================== -/

variable {ι : Type*}

/-- The aggregate incomplete-lap phase count `Σ_λ c_λ ≤ X/R` — re-export of the
    imported `sum_phasecount_le_div` (HighSupportPhaseCount), the (I.2a) boundary
    lever.  Each selected cell `λ` occupies a region `seg λ ⊆ range X`, the
    regions are pairwise disjoint, and `c λ · R ≤ |seg λ|`. -/
theorem incompleteLap_count_le_div
    (S : Finset ι) (seg : ι → Finset ℕ) (c : ι → ℕ) (X R : ℕ) (hR1 : 0 < R)
    (hsub : ∀ i ∈ S, seg i ⊆ Finset.range X)
    (hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (seg i) (seg j))
    (hcR : ∀ i ∈ S, c i * R ≤ (seg i).card) :
    ∑ i ∈ S, c i ≤ X / R :=
  Erdos260.HighSupportPhaseCount.sum_phasecount_le_div S seg c X R hR1 hsub hdisj hcR

/-- **Aggregate incomplete-lap mass bound (AL.4b).**  If each cell's incomplete-lap
    mass obeys the per-lap width bound `bd i ≤ W · c_i` (with `W = L + O_Q(1)`,
    AL.4a) and the phase count is `Σ c_i ≤ X/R`, then the total incomplete-lap mass
    is `≤ W·(X/R)`.  With `W = O_Q(L)` this is the `O_Q(L·X/R·|I_j|)` of (AL.4b). -/
theorem incompleteLap_mass_le
    (S : Finset ι) (bd cph : ι → ℕ) (W X R : ℕ)
    (hbd : ∀ i ∈ S, bd i ≤ W * cph i)
    (hcount : ∑ i ∈ S, cph i ≤ X / R) :
    ∑ i ∈ S, bd i ≤ W * (X / R) := by
  calc ∑ i ∈ S, bd i ≤ ∑ i ∈ S, W * cph i := Finset.sum_le_sum hbd
    _ = W * ∑ i ∈ S, cph i := by rw [← Finset.mul_sum]
    _ ≤ W * (X / R) := Nat.mul_le_mul (le_refl W) hcount

/-- **Exposure-weighted incomplete-lap mass bound (AL.4c).**  Multiplying the
    aggregate boundary mass by the exposure weight `H = r+1 = O_Q(L)` keeps the
    incomplete-lap contribution `≤ H·W·(X/R)` (`= O_Q(L²·X/R·|I_j|) = o(X|I_j|)`
    since `R = X^{1/2+ρ}`, `ρ>0`). -/
theorem incompleteLap_exposureWeighted_le
    (S : Finset ι) (bd cph : ι → ℕ) (H W X R : ℕ)
    (hbd : ∀ i ∈ S, bd i ≤ W * cph i)
    (hcount : ∑ i ∈ S, cph i ≤ X / R) :
    ∑ i ∈ S, H * bd i ≤ H * (W * (X / R)) := by
  have hHbd : ∀ i ∈ S, H * bd i ≤ (H * W) * cph i := by
    intro i hi
    calc H * bd i ≤ H * (W * cph i) := Nat.mul_le_mul (le_refl H) (hbd i hi)
      _ = (H * W) * cph i := by ring
  calc ∑ i ∈ S, H * bd i ≤ (H * W) * (X / R) := incompleteLap_mass_le S (fun i => H * bd i) cph (H * W) X R hHbd hcount
    _ = H * (W * (X / R)) := by ring

/-- **Complete-lap exact ratio + bounded incomplete-lap boundary (R.2′ with
    boundary, R.1c form).**  Splitting a retained fibre into its interior
    complete-lap part and its incomplete-lap boundary part,
        ExitMass(F) = ExitMass(F°) + ExitMass(F ∩ ∂),
    the interior obeys the exact mass-normalized bound `c·ExitMass(F°) ≤ b·M_tot`
    (Section A), so
        c · ExitMass(F)  ≤  b · M_tot  +  c · ExitMass(F ∩ ∂),
    where the second term is the bounded boundary controlled aggregately by
    `incompleteLap_mass_le`.  This is the arithmetic of "complete laps give the
    exact ratio, incomplete laps contribute only the bounded boundary". -/
theorem fineFibre_balance_with_boundary
    (b c interiorExit boundaryExit Mtotal : ℕ)
    (hinterior : c * interiorExit ≤ b * Mtotal) :
    c * (interiorExit + boundaryExit) ≤ b * Mtotal + c * boundaryExit := by
  have h : c * (interiorExit + boundaryExit) = c * interiorExit + c * boundaryExit := by ring
  rw [h]
  exact Nat.add_le_add_right hinterior _

end Erdos260.O1FineFibreBalance
