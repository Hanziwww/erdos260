/-
  Erdős #260 — O1 SUPPLY side: explicit construction of the fine-fibre cyclic
  atlas of Appendix AQ, discharging the chart-injectivity and successor-
  compatibility HYPOTHESES that `O1MeasurePreservation` / `O1FineFibreBalance`
  abstracted.  NEW module; it edits no existing file.

  Where `O1MeasurePreservation.cycle_charts_balance` *assumes*
    (hInj)    `∀ a, Set.InjOn (ι a) C_λ`            -- injective phase charts
    (hcompat) `∀ a u, τ a (ι a u) = ι (a+1) u`      -- successor compatibility (AL.3/AQ.6)
  this module *constructs* `ι`, `τ` explicitly from the start coordinate and the
  cumulative visible gaps of Appendix AQ and proves both as THEOREMS:

  * AQ.4  `G_a = g_0 + ⋯ + g_{a-1}`  (`cumGap`, `cumGap_succ`, `cumGap_eq_sum`).
  * AQ.5  `ι_a(u) = ambient(x(u) + G_a)`  is the affine chart (`fineRelabel`,
          reused from `O1FineFibreBalance`); it is injective on the cell from
          start-faithfulness + ambient injectivity (`fineRelabel_injOn`).
  * AQ.6  the successor `τ_a` is the start translation by `g_a`
          (`shiftSucc`); `shiftSucc_cumGap` proves `τ_a(ι_a u)=ι_{a+1}u`, and
          `affineSucc_bijOn` upgrades it to a measure-preserving bijection
          `Ω°_{λ,a} → Ω°_{λ,a+1}` (this is `lem:r-cycle-map-preserves-measure`,
          obtained from the explicit translation rather than assumed).
  * AL.6  all phase masses equal `|C_λ|` (`fineRelabel_image_card`); hence the
          exact complete-lap balance `c·ExitMass = b·M_tot` (`affine_atlas_balance`,
          R.1b / AL.7), routed through `O1FineFibreBalance`.
  * AL.4a `G_λ = ∑_{a<c} g_a ≤ W·c` from the dyadic gap bound `g_a ≤ W`
          (`lapDisplacement_le`); the aggregate exposure-weighted incomplete-lap
          mass `o(X|I_j|)` (AL.4b/AL.4c) via `incompleteLap_aggregate` /
          `incompleteLap_exposure_aggregate` folding AL.4a into the
          high-support phase count `∑ c_λ ≤ X/R`.

  Honest scope.  The genuinely irreducible analytic/geometric inputs remain
  hypotheses (and only these):
    - `hx : Set.InjOn x C_λ`  — the actual start coordinate is faithful on a
       fixed cell (App AQ "the visible event coordinates coincide ⇒ u = u'");
    - `hemb : Function.Injective emb` — the ambient embedding of starts as event
       states (the event carrier of Def `def:al-certified-cyclic-atlas`);
    - `hg : g_a ≤ W` — the dyadic gap bound (0.1), `W = L + O_Q(1)`;
    - existence of the gaps `g` / cell `C_λ` (the recurrence dynamics, App E.6,
       which is `P1Leaves.functional_graph_has_periodic_point`).
  These are exactly the "SUPPLY" of App AQ; everything they feed is proved here.

  The `ℤ/cℤ`-cyclic closure with a *single* global displacement `G` would force
  `∑_a g_a = 0` (the full lap returns to its start), which is FALSE for a lap of
  positive spatial length.  This is precisely the boundary-lap defect `∂_X C`:
  the honest resolution is the `o(X|I_j|)` deletion, after which the balance is
  proved over `Fin c` via per-chart injectivity (AL.6: "all phase charts have the
  same domain `C_λ`"), NOT via a wrap-around edge.

  No `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/
import Mathlib
import Erdos260.O1FineFibreBalance
import Erdos260.O1MeasurePreservation
import Erdos260.HighSupportPhaseCount

namespace Erdos260.O1SupplyAtlas

open Finset
open Erdos260.O1FineFibreBalance
open Erdos260.O1MeasurePreservation

/-! ===========================================================================
    ## Section A.  Cumulative spatial displacement of a lap.  (AQ.4)

    Manuscript: App AQ (AQ.4, line 12293): `G_0 = 0`, `G_a = g_0 + ⋯ + g_{a-1}`,
    where `g_a` is the visible gap of the recurrent edge from phase `a` to `a+1`.
    =========================================================================== -/

/-- The cumulative spatial displacement `G_a = g_0 + ⋯ + g_{a-1}` (AQ.4). -/
def cumGap (g : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | (a + 1) => cumGap g a + g a

@[simp] theorem cumGap_zero (g : ℕ → ℤ) : cumGap g 0 = 0 := rfl

/-- The defining one-step recurrence `G_{a+1} = G_a + g_a`. -/
theorem cumGap_succ (g : ℕ → ℤ) (a : ℕ) : cumGap g (a + 1) = cumGap g a + g a := rfl

/-- Closed form: `G_a = ∑_{i<a} g_i`. -/
theorem cumGap_eq_sum (g : ℕ → ℤ) (a : ℕ) : cumGap g a = ∑ i ∈ Finset.range a, g i := by
  induction a with
  | zero => simp
  | succ k ih => rw [cumGap_succ, ih, Finset.sum_range_succ]

/-! ===========================================================================
    ## Section B.  Affine phase charts and their injectivity.  (AQ.5)

    Manuscript: App AQ `lem:aq-simple-cycle-atlas-row` (AQ.5, line 12305):
    `ι_a(u) = ` the transported event of `u` at start `x(u) + G_a`.  We realize
    this as `fineRelabel x emb (G_a)` (`O1FineFibreBalance.fineRelabel`,
    `u ↦ emb(x u + G)`), with `emb : ℤ → Ω` the ambient embedding of starts as
    event states.  Injectivity on the cell discharges the (hInj) hypothesis of
    `O1MeasurePreservation`.
    =========================================================================== -/

/-- **Charts inject on the cell (AQ.6 injectivity step).**  The affine chart is
    injective on `C_λ` from start-faithfulness `hx` and ambient injectivity
    `hemb`: distinct base events have distinct starts `x(u)+G ≠ x(u')+G`, hence
    distinct event states.  Discharges `Set.InjOn (ι a) C_λ`. -/
theorem fineRelabel_injOn {C Ω : Type*} (emb : ℤ → Ω) (x : C → ℤ) (G : ℤ) (Cset : Finset C)
    (hx : Set.InjOn x ↑Cset) (hemb : Function.Injective emb) :
    Set.InjOn (fineRelabel x emb G) ↑Cset := by
  intro u hu u' hu' h
  unfold fineRelabel at h
  exact hx hu hu' (add_right_cancel (hemb h))

/-- **Phase mass equals the carrier size (AL.6).**  `Mass(Ω°_{λ,a}) = |C_λ|`,
    since the chart relabels the carrier injectively onto the phase fibre. -/
theorem fineRelabel_image_card {C Ω : Type*} [DecidableEq Ω] (emb : ℤ → Ω)
    (hemb : Function.Injective emb) (x : C → ℤ) (G : ℤ) (Cset : Finset C)
    (hx : Set.InjOn x ↑Cset) :
    (Cset.image (fineRelabel x emb G)).card = Cset.card :=
  Finset.card_image_of_injOn (fineRelabel_injOn emb x G Cset hx hemb)

/-! ===========================================================================
    ## Section C.  The successor translation and the per-edge bijection.
                                              (AQ.6, `lem:r-cycle-map-preserves-measure`)

    Manuscript: App AQ (AQ.6, line 12317) `τ_a(ι_a(u)) = ι_{a+1}(u)`, and the
    injectivity/surjectivity argument (line 12322): the target start is
    `x ↦ x + g_a`.  We realize `τ_a` as the start translation by `g_a`
    (`shiftSucc`) and PROVE the compatibility identity and the two-sided
    bijection `Ω°_{λ,a} → Ω°_{λ,a+1}` (the measure-preservation of App R),
    discharging the (hcompat) hypothesis.
    =========================================================================== -/

/-- The cyclic successor `τ_a`, realized on the event carrier as the start
    translation by the visible gap `g`: read the start back with `emb⁻¹`, add `g`,
    re-embed.  (`noncomputable` only through `Function.invFun`.) -/
noncomputable def shiftSucc {Ω : Type*} (emb : ℤ → Ω) (g : ℤ) : Ω → Ω :=
  fun ω => emb (Function.invFun emb ω + g)

/-- The successor translates the chart start: `τ_g(ι_G u) = ι_{G+g}(u)`. -/
theorem shiftSucc_fineRelabel {C Ω : Type*} (emb : ℤ → Ω) (hemb : Function.Injective emb)
    (x : C → ℤ) (G g : ℤ) (u : C) :
    shiftSucc emb g (fineRelabel x emb G u) = fineRelabel x emb (G + g) u := by
  unfold shiftSucc fineRelabel
  rw [Function.leftInverse_invFun hemb (x u + G), add_assoc]

/-- **Successor compatibility (AQ.6 / AL.3).**  `τ_{g_a}(ι_{G_a} u) = ι_{G_{a+1}} u`,
    using `G_{a+1} = G_a + g_a`.  This is exactly the (hcompat) hypothesis. -/
theorem shiftSucc_cumGap {C Ω : Type*} (emb : ℤ → Ω) (hemb : Function.Injective emb)
    (x : C → ℤ) (g : ℕ → ℤ) (a : ℕ) (u : C) :
    shiftSucc emb (g a) (fineRelabel x emb (cumGap g a) u)
      = fineRelabel x emb (cumGap g (a + 1)) u := by
  rw [shiftSucc_fineRelabel emb hemb x (cumGap g a) (g a) u, cumGap_succ]

/-- **The successor is a measure-preserving bijection on the fibres
    (`lem:r-cycle-map-preserves-measure`).**  From the constructed compatibility
    and chart injectivity, the start translation `τ_{g_a}` restricts to a bijection
    `Ω°_{λ,a} → Ω°_{λ,a+1}`.  Routed through `O1MeasurePreservation.cycleMap_bijOn`,
    so the geometric supply now feeds a *proved* bijection. -/
theorem affineSucc_bijOn {C Ω : Type*} [DecidableEq Ω] (emb : ℤ → Ω)
    (hemb : Function.Injective emb) (x : C → ℤ) (g : ℕ → ℤ) (a : ℕ) (Cset : Finset C)
    (hx : Set.InjOn x ↑Cset) :
    Set.BijOn (shiftSucc emb (g a))
      ↑(Cset.image (fineRelabel x emb (cumGap g a)))
      ↑(Cset.image (fineRelabel x emb (cumGap g (a + 1)))) :=
  cycleMap_bijOn Cset _ _ (fineRelabel x emb (cumGap g a))
    (fineRelabel x emb (cumGap g (a + 1))) (shiftSucc emb (g a)) rfl rfl
    (fineRelabel_injOn emb x (cumGap g (a + 1)) Cset hx hemb)
    (fun u _ => shiftSucc_cumGap emb hemb x g a u)

/-- Measure preservation, cardinality form: `|Ω°_{λ,a+1}| = |Ω°_{λ,a}|`, from the
    bijection itself (not from the two images sharing a domain). -/
theorem affineSucc_card_eq {C Ω : Type*} [DecidableEq Ω] (emb : ℤ → Ω)
    (hemb : Function.Injective emb) (x : C → ℤ) (g : ℕ → ℤ) (a : ℕ) (Cset : Finset C)
    (hx : Set.InjOn x ↑Cset) :
    (Cset.image (fineRelabel x emb (cumGap g (a + 1)))).card
      = (Cset.image (fineRelabel x emb (cumGap g a))).card :=
  (bijOn_finset_card_eq (affineSucc_bijOn emb hemb x g a Cset hx)).symm

/-- Measure preservation, integral form: the successor preserves counting-measure
    integrals, `∑_{Ω°_a} w(τ ω) = ∑_{Ω°_{a+1}} w`. -/
theorem affineSucc_measure_preserving {C Ω M : Type*} [DecidableEq Ω] [AddCommMonoid M]
    (emb : ℤ → Ω) (hemb : Function.Injective emb) (x : C → ℤ) (g : ℕ → ℤ) (a : ℕ)
    (Cset : Finset C) (hx : Set.InjOn x ↑Cset) (w : Ω → M) :
    ∑ ω ∈ Cset.image (fineRelabel x emb (cumGap g a)), w (shiftSucc emb (g a) ω)
      = ∑ ω' ∈ Cset.image (fineRelabel x emb (cumGap g (a + 1))), w ω' :=
  bijOn_finset_sum_eq w (affineSucc_bijOn emb hemb x g a Cset hx)

/-! ===========================================================================
    ## Section D.  Equal phase masses (AL.6) and the complete-lap balance.
                                                          (R.1b / AL.7)

    Manuscript: App AL `lem:al-complete-lap` (AL.6, line 11736): all interior
    phase fibres have equal mass `|C_λ|`, hence the exit phases occupy exactly a
    `b/c` fraction (R.1b, line 8790).  We feed the constructed uniform masses
    into `O1FineFibreBalance.completeLap_phase_mass_identity`.
    =========================================================================== -/

/-- **Complete-lap balance from the explicit affine atlas (R.1b / AL.6+AL.7).**
    For ANY phase index set with cumulative-gap coordinates `phaseG`, every phase
    mass equals `|C_λ|`, so the exit phases occupy exactly a `b/c` fraction:
        `c · ExitMass(Tot°) = b · M_tot°`.
    The two assumed hypotheses of `cycle_charts_balance` are now discharged by the
    construction; only `hx`, `hemb` (the genuine supply) remain. -/
theorem affine_atlas_balance {C Ω φ : Type*} [DecidableEq Ω] (emb : ℤ → Ω)
    (hemb : Function.Injective emb) (x : C → ℤ) (Cset : Finset C) (hx : Set.InjOn x ↑Cset)
    (phaseG : φ → ℤ) (phases E : Finset φ) (hE : E ⊆ phases) :
    phases.card * (∑ a ∈ E, (Cset.image (fineRelabel x emb (phaseG a))).card)
      = E.card * (∑ a ∈ phases, (Cset.image (fineRelabel x emb (phaseG a))).card) :=
  completeLap_phase_mass_identity phases E
    (fun a => (Cset.image (fineRelabel x emb (phaseG a))).card) Cset.card hE
    (fun a _ => fineRelabel_image_card emb hemb x (phaseG a) Cset hx)

/-- **O1 supply capstone over the cyclic phase set `Fin c`.**  Given only the
    genuine supply (`hemb`, `hx`, the gaps `g`), the affine atlas
    `ι_a(u) = emb(x u + G_a)` simultaneously:
    (1) has injective charts on every phase (discharges hInj);
    (2) has a measure-preserving successor bijection on every edge `a → a+1`
        (`lem:r-cycle-map-preserves-measure`, discharges hcompat);
    (3) satisfies the exact complete-lap mass balance `c·ExitMass = b·M_tot`
        (R.1b / AL.7).
    The cyclic count uses per-chart injectivity over `Fin c`, NOT a wrap edge. -/
theorem o1_affine_atlas_capstone {C Ω : Type*} [DecidableEq Ω] (c : ℕ)
    (emb : ℤ → Ω) (hemb : Function.Injective emb) (x : C → ℤ) (g : ℕ → ℤ)
    (Cset : Finset C) (hx : Set.InjOn x ↑Cset) (E : Finset (Fin c)) :
    (∀ a : Fin c, Set.InjOn (fineRelabel x emb (cumGap g a.val)) ↑Cset) ∧
    (∀ a : ℕ, Set.BijOn (shiftSucc emb (g a))
        ↑(Cset.image (fineRelabel x emb (cumGap g a)))
        ↑(Cset.image (fineRelabel x emb (cumGap g (a + 1))))) ∧
    c * (∑ a ∈ E, (Cset.image (fineRelabel x emb (cumGap g a.val))).card)
      = E.card * (∑ a : Fin c, (Cset.image (fineRelabel x emb (cumGap g a.val))).card) := by
  refine ⟨fun a => fineRelabel_injOn emb x (cumGap g a.val) Cset hx hemb,
          fun a => affineSucc_bijOn emb hemb x g a Cset hx, ?_⟩
  have hc : (Finset.univ : Finset (Fin c)).card = c := by simp
  have hb := affine_atlas_balance emb hemb x Cset hx (fun a : Fin c => cumGap g a.val)
    Finset.univ E (Finset.subset_univ E)
  rwa [hc] at hb

/-- If `a.val + 1` stays inside the chosen representatives, the `ZMod c`
    successor has representative `a.val + 1`.  This is the non-wrapping edge in
    the cyclic chart bookkeeping. -/
theorem zmod_val_add_one_of_lt (c : ℕ) [NeZero c] (a : ZMod c)
    (hlt : a.val + 1 < c) :
    (a + 1).val = a.val + 1 := by
  have hcast : (((a.val + 1 : ℕ) : ZMod c)) = a + 1 := by
    rw [Nat.cast_add, ZMod.natCast_zmod_val]
    norm_num
  rw [← hcast]
  exact ZMod.val_natCast_of_lt hlt

/-- If `a.val + 1` leaves the chosen representatives, it is exactly the wrap
    edge, and the successor representative is `0`. -/
theorem zmod_val_add_one_eq_zero_of_wrap (c : ℕ) [NeZero c] (a : ZMod c)
    (hwrap : ¬ a.val + 1 < c) :
    (a + 1).val = 0 := by
  have hsum : a.val + 1 = c := by
    have haval : a.val < c := ZMod.val_lt a
    omega
  have hcast : (((a.val + 1 : ℕ) : ZMod c)) = a + 1 := by
    rw [Nat.cast_add, ZMod.natCast_zmod_val]
    norm_num
  have hzero : a + 1 = 0 := by
    rw [← hcast, hsum, ZMod.natCast_self]
  rw [hzero, ZMod.val_zero]

/-- **Closed-lap bridge to the `ZMod c` O1 surface.**  The affine atlas over
    natural representatives supplies `O1CycleChartInputs` exactly when the final
    wrap edge is separately certified as a genuine lap return.  Without this
    return hypothesis the honest O1 supply remains the `Fin c` capstone above:
    the manuscript's positive spatial displacement is a boundary-lap defect, not
    a cyclic affine translation. -/
theorem affineCycleChartInputs_of_closedLap {C Ω : Type*} [DecidableEq Ω]
    (c : ℕ) [NeZero c] (emb : ℤ → Ω) (hemb : Function.Injective emb)
    (x : C → ℤ) (g : ℕ → ℤ) (Cset : Finset C) (hx : Set.InjOn x ↑Cset)
    (hreturn : ∀ u : C, u ∈ Cset →
      fineRelabel x emb (cumGap g c) u = fineRelabel x emb 0 u) :
    O1CycleChartInputs c Cset
      (fun a : ZMod c => fineRelabel x emb (cumGap g a.val))
      (fun a : ZMod c => shiftSucc emb (g a.val)) where
  hInj := fun a => fineRelabel_injOn emb x (cumGap g a.val) Cset hx hemb
  hcompat := by
    intro a u hu
    rw [shiftSucc_cumGap emb hemb x g a.val u]
    by_cases hlt : a.val + 1 < c
    · rw [zmod_val_add_one_of_lt c a hlt]
    · have hsum : a.val + 1 = c := by
        have haval : a.val < c := ZMod.val_lt a
        omega
      rw [hsum, zmod_val_add_one_eq_zero_of_wrap c a hlt, cumGap_zero]
      exact hreturn u hu

/-- Balance over `ZMod c` from the affine atlas plus the explicit closed-lap
    return needed for the wrap edge. -/
theorem affine_closedLap_cycle_balance {C Ω : Type*} [DecidableEq Ω]
    (c : ℕ) [NeZero c] (emb : ℤ → Ω) (hemb : Function.Injective emb)
    (x : C → ℤ) (g : ℕ → ℤ) (Cset : Finset C) (hx : Set.InjOn x ↑Cset)
    (E : Finset (ZMod c))
    (hreturn : ∀ u : C, u ∈ Cset →
      fineRelabel x emb (cumGap g c) u = fineRelabel x emb 0 u) :
    c * (∑ a ∈ E, (Cset.image (fineRelabel x emb (cumGap g a.val))).card)
      = E.card *
        (∑ a : ZMod c, (Cset.image (fineRelabel x emb (cumGap g a.val))).card) :=
  O1CycleChartInputs.balance c Cset
    (fun a : ZMod c => fineRelabel x emb (cumGap g a.val))
    (fun a : ZMod c => shiftSucc emb (g a.val)) E
    (affineCycleChartInputs_of_closedLap c emb hemb x g Cset hx hreturn)

/-- Weighted per-edge measure preservation over `ZMod c` from the affine atlas
plus the explicit closed-lap return needed for the wrap edge.  This is the
concrete App R edge statement, not only the aggregated complete-lap balance. -/
theorem affine_closedLap_edge_measure_preserving {C Ω M : Type*}
    [DecidableEq Ω] [AddCommMonoid M]
    (c : ℕ) [NeZero c] (emb : ℤ → Ω) (hemb : Function.Injective emb)
    (x : C → ℤ) (g : ℕ → ℤ) (Cset : Finset C) (hx : Set.InjOn x ↑Cset)
    (a : ZMod c) (w : Ω → M)
    (hreturn : ∀ u : C, u ∈ Cset →
      fineRelabel x emb (cumGap g c) u = fineRelabel x emb 0 u) :
    ∑ ω ∈ Cset.image (fineRelabel x emb (cumGap g a.val)),
        w (shiftSucc emb (g a.val) ω)
      =
    ∑ ω' ∈ Cset.image (fineRelabel x emb (cumGap g (a + 1).val)), w ω' :=
  O1CycleChartInputs.edge_measure_preserving c Cset
    (fun a : ZMod c => fineRelabel x emb (cumGap g a.val))
    (fun a : ZMod c => shiftSucc emb (g a.val)) a w
    (affineCycleChartInputs_of_closedLap c emb hemb x g Cset hx hreturn)

/-- A fully closed affine lap is a sufficient concrete source of the wrap-edge
    return hypothesis.  This is the exact zero-displacement subcase: if the full
    cumulative gap satisfies `G_c = 0`, the final chart is definitionally the
    initial chart. -/
theorem affineCycleChartInputs_of_zeroLap {C Ω : Type*} [DecidableEq Ω]
    (c : ℕ) [NeZero c] (emb : ℤ → Ω) (hemb : Function.Injective emb)
    (x : C → ℤ) (g : ℕ → ℤ) (Cset : Finset C) (hx : Set.InjOn x ↑Cset)
    (hzero : cumGap g c = 0) :
    O1CycleChartInputs c Cset
      (fun a : ZMod c => fineRelabel x emb (cumGap g a.val))
      (fun a : ZMod c => shiftSucc emb (g a.val)) :=
  affineCycleChartInputs_of_closedLap c emb hemb x g Cset hx (by
    intro u _hu
    rw [hzero])

/-- Balance over `ZMod c` in the exact zero-displacement subcase `G_c = 0`.
    This closes the closed-lap bridge without an extra `hreturn` hypothesis when
    the full lap displacement has already been certified to vanish. -/
theorem affine_zeroLap_cycle_balance {C Ω : Type*} [DecidableEq Ω]
    (c : ℕ) [NeZero c] (emb : ℤ → Ω) (hemb : Function.Injective emb)
    (x : C → ℤ) (g : ℕ → ℤ) (Cset : Finset C) (hx : Set.InjOn x ↑Cset)
    (E : Finset (ZMod c)) (hzero : cumGap g c = 0) :
    c * (∑ a ∈ E, (Cset.image (fineRelabel x emb (cumGap g a.val))).card)
      = E.card *
        (∑ a : ZMod c, (Cset.image (fineRelabel x emb (cumGap g a.val))).card) :=
  affine_closedLap_cycle_balance c emb hemb x g Cset hx E (by
    intro u _hu
    rw [hzero])

/-- Weighted per-edge measure preservation over `ZMod c` in the exact
zero-displacement subcase `G_c = 0`. -/
theorem affine_zeroLap_edge_measure_preserving {C Ω M : Type*}
    [DecidableEq Ω] [AddCommMonoid M]
    (c : ℕ) [NeZero c] (emb : ℤ → Ω) (hemb : Function.Injective emb)
    (x : C → ℤ) (g : ℕ → ℤ) (Cset : Finset C) (hx : Set.InjOn x ↑Cset)
    (a : ZMod c) (w : Ω → M) (hzero : cumGap g c = 0) :
    ∑ ω ∈ Cset.image (fineRelabel x emb (cumGap g a.val)),
        w (shiftSucc emb (g a.val) ω)
      =
    ∑ ω' ∈ Cset.image (fineRelabel x emb (cumGap g (a + 1).val)), w ω' :=
  affine_closedLap_edge_measure_preserving c emb hemb x g Cset hx a w (by
    intro u _hu
    rw [hzero])

/-- Sum-form source of the exact zero-displacement cyclic atlas.  This is the
    AQ.4 normal form `G_c = ∑_{a<c} g_a`, exposed so later AL/AQ code can feed
    the complete-lap bridge using the manuscript's explicit phase-increment sum. -/
theorem affineCycleChartInputs_of_sumGap_zero {C Ω : Type*} [DecidableEq Ω]
    (c : ℕ) [NeZero c] (emb : ℤ → Ω) (hemb : Function.Injective emb)
    (x : C → ℤ) (g : ℕ → ℤ) (Cset : Finset C) (hx : Set.InjOn x ↑Cset)
    (hsum : (∑ i ∈ Finset.range c, g i) = 0) :
    O1CycleChartInputs c Cset
      (fun a : ZMod c => fineRelabel x emb (cumGap g a.val))
      (fun a : ZMod c => shiftSucc emb (g a.val)) :=
  affineCycleChartInputs_of_zeroLap c emb hemb x g Cset hx (by
    rw [cumGap_eq_sum]
    exact hsum)

/-- Balance over `ZMod c` from the manuscript sum-form zero-displacement input
    `∑_{a<c} g_a = 0`. -/
theorem affine_sumGap_zero_cycle_balance {C Ω : Type*} [DecidableEq Ω]
    (c : ℕ) [NeZero c] (emb : ℤ → Ω) (hemb : Function.Injective emb)
    (x : C → ℤ) (g : ℕ → ℤ) (Cset : Finset C) (hx : Set.InjOn x ↑Cset)
    (E : Finset (ZMod c)) (hsum : (∑ i ∈ Finset.range c, g i) = 0) :
    c * (∑ a ∈ E, (Cset.image (fineRelabel x emb (cumGap g a.val))).card)
      = E.card *
        (∑ a : ZMod c, (Cset.image (fineRelabel x emb (cumGap g a.val))).card) :=
  affine_zeroLap_cycle_balance c emb hemb x g Cset hx E (by
    rw [cumGap_eq_sum]
    exact hsum)

/-- Weighted per-edge measure preservation over `ZMod c` from the manuscript
sum-form zero-displacement input `∑_{i<c} g_i = 0`. -/
theorem affine_sumGap_zero_edge_measure_preserving {C Ω M : Type*}
    [DecidableEq Ω] [AddCommMonoid M]
    (c : ℕ) [NeZero c] (emb : ℤ → Ω) (hemb : Function.Injective emb)
    (x : C → ℤ) (g : ℕ → ℤ) (Cset : Finset C) (hx : Set.InjOn x ↑Cset)
    (a : ZMod c) (w : Ω → M) (hsum : (∑ i ∈ Finset.range c, g i) = 0) :
    ∑ ω ∈ Cset.image (fineRelabel x emb (cumGap g a.val)),
        w (shiftSucc emb (g a.val) ω)
      =
    ∑ ω' ∈ Cset.image (fineRelabel x emb (cumGap g (a + 1).val)), w ω' :=
  affine_zeroLap_edge_measure_preserving c emb hemb x g Cset hx a w (by
    rw [cumGap_eq_sum]
    exact hsum)

/-! ## Section D'. Packaged affine complete-lap atlas surfaces (AQ.5--AQ.6 / AL.6) -/

/-- Packaged affine complete-lap atlas with an explicit wrap-return certificate.
The fields are exactly the remaining geometric facts needed by the AQ/AL affine
construction: faithful ambient start embedding, injective base start coordinate
on the common carrier, and the final-lap return identifying the wrap edge. -/
structure O1AffineClosedLapInputs {C Omega : Type*}
    (c : Nat) [NeZero c] (emb : Int -> Omega) (x : C -> Int)
    (g : Nat -> Int) (Cset : Finset C) where
  hemb : Function.Injective emb
  hx : Set.InjOn x ↑Cset
  hreturn : forall u : C, u ∈ Cset ->
    fineRelabel x emb (cumGap g c) u = fineRelabel x emb 0 u

namespace O1AffineClosedLapInputs

/-- The packaged affine complete-lap atlas supplies the cyclic chart surface
expected by `O1MeasurePreservation`. -/
def toCycleChartInputs {C Omega : Type*} [DecidableEq Omega]
    {c : Nat} [NeZero c] {emb : Int -> Omega} {x : C -> Int}
    {g : Nat -> Int} {Cset : Finset C}
    (I : O1AffineClosedLapInputs c emb x g Cset) :
    O1CycleChartInputs c Cset
      (fun a : ZMod c => fineRelabel x emb (cumGap g a.val))
      (fun a : ZMod c => shiftSucc emb (g a.val)) :=
  affineCycleChartInputs_of_closedLap c emb I.hemb x g Cset I.hx I.hreturn

/-- Packaged per-edge fibre equivalence from the affine closed-lap surface. -/
noncomputable def edge_equiv {C Omega : Type*} [DecidableEq Omega]
    {c : Nat} [NeZero c] {emb : Int -> Omega} {x : C -> Int}
    {g : Nat -> Int} {Cset : Finset C}
    (a : ZMod c) (I : O1AffineClosedLapInputs c emb x g Cset) :
    {omega : Omega //
        omega ∈ (↑(Cset.image (fineRelabel x emb (cumGap g a.val))) : Set Omega)} ≃
      {omega : Omega //
        omega ∈ (↑(Cset.image (fineRelabel x emb (cumGap g (a + 1).val))) : Set Omega)} :=
  O1CycleChartInputs.edge_equiv c Cset
    (fun a : ZMod c => fineRelabel x emb (cumGap g a.val))
    (fun a : ZMod c => shiftSucc emb (g a.val)) a (toCycleChartInputs I)

/-- Packaged complete-lap balance from the affine closed-lap surface. -/
theorem balance {C Omega : Type*} [DecidableEq Omega]
    {c : Nat} [NeZero c] {emb : Int -> Omega} {x : C -> Int}
    {g : Nat -> Int} {Cset : Finset C}
    (E : Finset (ZMod c)) (I : O1AffineClosedLapInputs c emb x g Cset) :
    c * (∑ a ∈ E, (Cset.image (fineRelabel x emb (cumGap g a.val))).card)
      = E.card *
        (∑ a : ZMod c, (Cset.image (fineRelabel x emb (cumGap g a.val))).card) :=
  affine_closedLap_cycle_balance c emb I.hemb x g Cset I.hx E I.hreturn

/-- Packaged weighted per-edge measure preservation from the affine closed-lap
surface. -/
theorem edge_measure_preserving {C Omega M : Type*}
    [DecidableEq Omega] [AddCommMonoid M]
    {c : Nat} [NeZero c] {emb : Int -> Omega} {x : C -> Int}
    {g : Nat -> Int} {Cset : Finset C}
    (a : ZMod c) (w : Omega -> M) (I : O1AffineClosedLapInputs c emb x g Cset) :
    ∑ omega ∈ Cset.image (fineRelabel x emb (cumGap g a.val)),
        w (shiftSucc emb (g a.val) omega)
      =
    ∑ omega' ∈ Cset.image (fineRelabel x emb (cumGap g (a + 1).val)), w omega' :=
  affine_closedLap_edge_measure_preserving c emb I.hemb x g Cset I.hx a w I.hreturn

end O1AffineClosedLapInputs

/-- Packaged affine complete-lap atlas in the exact zero-displacement form
`G_c = cumGap g c = 0`.  This is the direct finite certificate between an
explicit wrap-return hypothesis and the manuscript sum-form `sum_{i<c} g_i = 0`.
-/
structure O1AffineZeroLapInputs {C Omega : Type*}
    (c : Nat) [NeZero c] (emb : Int -> Omega) (x : C -> Int)
    (g : Nat -> Int) (Cset : Finset C) where
  hemb : Function.Injective emb
  hx : Set.InjOn x ↑Cset
  hzero : cumGap g c = 0

namespace O1AffineZeroLapInputs

/-- Zero-displacement data produces the explicit wrap-return closed-lap surface.
-/
def toClosedLapInputs {C Omega : Type*}
    {c : Nat} [NeZero c] {emb : Int -> Omega} {x : C -> Int}
    {g : Nat -> Int} {Cset : Finset C}
    (I : O1AffineZeroLapInputs c emb x g Cset) :
    O1AffineClosedLapInputs c emb x g Cset where
  hemb := I.hemb
  hx := I.hx
  hreturn := by
    intro u _hu
    rw [I.hzero]

/-- The zero-displacement package supplies the cyclic chart surface expected by
`O1MeasurePreservation`. -/
def toCycleChartInputs {C Omega : Type*} [DecidableEq Omega]
    {c : Nat} [NeZero c] {emb : Int -> Omega} {x : C -> Int}
    {g : Nat -> Int} {Cset : Finset C}
    (I : O1AffineZeroLapInputs c emb x g Cset) :
    O1CycleChartInputs c Cset
      (fun a : ZMod c => fineRelabel x emb (cumGap g a.val))
      (fun a : ZMod c => shiftSucc emb (g a.val)) :=
  affineCycleChartInputs_of_zeroLap c emb I.hemb x g Cset I.hx I.hzero

/-- Packaged per-edge fibre equivalence from the zero-displacement surface. -/
noncomputable def edge_equiv {C Omega : Type*} [DecidableEq Omega]
    {c : Nat} [NeZero c] {emb : Int -> Omega} {x : C -> Int}
    {g : Nat -> Int} {Cset : Finset C}
    (a : ZMod c) (I : O1AffineZeroLapInputs c emb x g Cset) :
    {omega : Omega //
        omega ∈ (↑(Cset.image (fineRelabel x emb (cumGap g a.val))) : Set Omega)} ≃
      {omega : Omega //
        omega ∈ (↑(Cset.image (fineRelabel x emb (cumGap g (a + 1).val))) : Set Omega)} :=
  O1AffineClosedLapInputs.edge_equiv a (toClosedLapInputs I)

/-- Packaged complete-lap balance from the zero-displacement surface. -/
theorem balance {C Omega : Type*} [DecidableEq Omega]
    {c : Nat} [NeZero c] {emb : Int -> Omega} {x : C -> Int}
    {g : Nat -> Int} {Cset : Finset C}
    (E : Finset (ZMod c)) (I : O1AffineZeroLapInputs c emb x g Cset) :
    c * (∑ a ∈ E, (Cset.image (fineRelabel x emb (cumGap g a.val))).card)
      = E.card *
        (∑ a : ZMod c, (Cset.image (fineRelabel x emb (cumGap g a.val))).card) :=
  affine_zeroLap_cycle_balance c emb I.hemb x g Cset I.hx E I.hzero

/-- Packaged weighted per-edge measure preservation from the zero-displacement
complete-lap surface. -/
theorem edge_measure_preserving {C Omega M : Type*}
    [DecidableEq Omega] [AddCommMonoid M]
    {c : Nat} [NeZero c] {emb : Int -> Omega} {x : C -> Int}
    {g : Nat -> Int} {Cset : Finset C}
    (a : ZMod c) (w : Omega -> M) (I : O1AffineZeroLapInputs c emb x g Cset) :
    ∑ omega ∈ Cset.image (fineRelabel x emb (cumGap g a.val)),
        w (shiftSucc emb (g a.val) omega)
      =
    ∑ omega' ∈ Cset.image (fineRelabel x emb (cumGap g (a + 1).val)), w omega' :=
  affine_zeroLap_edge_measure_preserving c emb I.hemb x g Cset I.hx a w I.hzero

end O1AffineZeroLapInputs

/-- Packaged affine complete-lap atlas in the manuscript sum-form
`sum_{i<c} g_i = 0`.  This is a sufficient source of the wrap-return field above
when the full displacement has already been certified to vanish. -/
structure O1AffineSumGapZeroInputs {C Omega : Type*}
    (c : Nat) [NeZero c] (emb : Int -> Omega) (x : C -> Int)
    (g : Nat -> Int) (Cset : Finset C) where
  hemb : Function.Injective emb
  hx : Set.InjOn x ↑Cset
  hsum : (∑ i ∈ Finset.range c, g i) = 0

namespace O1AffineSumGapZeroInputs

/-- Sum-gap-zero data produces the explicit wrap-return closed-lap surface. -/
def toClosedLapInputs {C Omega : Type*}
    {c : Nat} [NeZero c] {emb : Int -> Omega} {x : C -> Int}
    {g : Nat -> Int} {Cset : Finset C}
    (I : O1AffineSumGapZeroInputs c emb x g Cset) :
    O1AffineClosedLapInputs c emb x g Cset where
  hemb := I.hemb
  hx := I.hx
  hreturn := by
    intro u _hu
    rw [cumGap_eq_sum, I.hsum]

/-- The manuscript sum-form package supplies the cyclic chart surface expected by
`O1MeasurePreservation`. -/
def toCycleChartInputs {C Omega : Type*} [DecidableEq Omega]
    {c : Nat} [NeZero c] {emb : Int -> Omega} {x : C -> Int}
    {g : Nat -> Int} {Cset : Finset C}
    (I : O1AffineSumGapZeroInputs c emb x g Cset) :
    O1CycleChartInputs c Cset
      (fun a : ZMod c => fineRelabel x emb (cumGap g a.val))
      (fun a : ZMod c => shiftSucc emb (g a.val)) :=
  affineCycleChartInputs_of_sumGap_zero c emb I.hemb x g Cset I.hx I.hsum

/-- Packaged per-edge fibre equivalence from the manuscript sum-gap-zero surface. -/
noncomputable def edge_equiv {C Omega : Type*} [DecidableEq Omega]
    {c : Nat} [NeZero c] {emb : Int -> Omega} {x : C -> Int}
    {g : Nat -> Int} {Cset : Finset C}
    (a : ZMod c) (I : O1AffineSumGapZeroInputs c emb x g Cset) :
    {omega : Omega //
        omega ∈ (↑(Cset.image (fineRelabel x emb (cumGap g a.val))) : Set Omega)} ≃
      {omega : Omega //
        omega ∈ (↑(Cset.image (fineRelabel x emb (cumGap g (a + 1).val))) : Set Omega)} :=
  O1AffineClosedLapInputs.edge_equiv a (toClosedLapInputs I)

/-- Packaged complete-lap balance from the manuscript sum-gap-zero surface. -/
theorem balance {C Omega : Type*} [DecidableEq Omega]
    {c : Nat} [NeZero c] {emb : Int -> Omega} {x : C -> Int}
    {g : Nat -> Int} {Cset : Finset C}
    (E : Finset (ZMod c)) (I : O1AffineSumGapZeroInputs c emb x g Cset) :
    c * (∑ a ∈ E, (Cset.image (fineRelabel x emb (cumGap g a.val))).card)
      = E.card *
        (∑ a : ZMod c, (Cset.image (fineRelabel x emb (cumGap g a.val))).card) :=
  affine_sumGap_zero_cycle_balance c emb I.hemb x g Cset I.hx E I.hsum

/-- Packaged weighted per-edge measure preservation from the manuscript
sum-gap-zero complete-lap surface. -/
theorem edge_measure_preserving {C Omega M : Type*}
    [DecidableEq Omega] [AddCommMonoid M]
    {c : Nat} [NeZero c] {emb : Int -> Omega} {x : C -> Int}
    {g : Nat -> Int} {Cset : Finset C}
    (a : ZMod c) (w : Omega -> M) (I : O1AffineSumGapZeroInputs c emb x g Cset) :
    ∑ omega ∈ Cset.image (fineRelabel x emb (cumGap g a.val)),
        w (shiftSucc emb (g a.val) omega)
      =
    ∑ omega' ∈ Cset.image (fineRelabel x emb (cumGap g (a + 1).val)), w omega' :=
  affine_sumGap_zero_edge_measure_preserving c emb I.hemb x g Cset I.hx a w I.hsum

end O1AffineSumGapZeroInputs

/-! ===========================================================================
    ## Section E.  Lap-displacement bound (AL.4a) and the aggregate `o(X|I_j|)`.
                                                          (AL.4a / AL.4b / AL.4c)

    Manuscript: App AL `lem:al-cyclic-bad-carrier-exposure-owned` (AL.4, line 11673).
    AL.4a: `G_λ ≤ (L + O_Q(1))·c_λ` from the dyadic gap bound (0.1).  AL.4b: the
    aggregate incomplete-lap carrier `≤ O_Q(L·X/R·|I_j|)` via the high-support
    phase count `∑ c_λ ≤ X/R`.  AL.4c: the exposure-weighted version
    `≤ O_Q(L²·X/R·|I_j|) = o(X|I_j|)`.
    =========================================================================== -/

/-- **AL.4a lap-displacement bound.**  If each visible gap obeys the dyadic gap
    bound `g_a ≤ W` (the genuine analytic input (0.1), `W = L + O_Q(1)`), then the
    full-lap displacement is `G_λ = ∑_{a<c} g_a ≤ W·c`. -/
theorem lapDisplacement_le (g : ℕ → ℤ) (W : ℤ) (c : ℕ) (hg : ∀ a, a < c → g a ≤ W) :
    cumGap g c ≤ W * c := by
  rw [cumGap_eq_sum]
  calc ∑ i ∈ Finset.range c, g i
      ≤ ∑ _i ∈ Finset.range c, W :=
        Finset.sum_le_sum (fun i hi => hg i (Finset.mem_range.mp hi))
    _ = (c : ℤ) * W := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = W * c := by ring

/-- **AL.4b aggregate incomplete-lap bound, with AL.4a folded in.**  Each cell's
    unweighted incomplete-lap mass is the two shell collars of total width
    `O(G_λ)` across the `|I_j|` threshold rows and the fixed finite row
    coordinates: `bd_λ ≤ K·|I_j|·G_λ`.  With AL.4a in count form (`G_λ ≤ W·c_λ`)
    and the high-support phase count `∑ c_λ ≤ X/R`
    (`HighSupportPhaseCount`/`incompleteLap_count_le_div`), the aggregate is
    `≤ K·|I_j|·W·(X/R) = O_Q(L·X/R·|I_j|)`. -/
theorem incompleteLap_aggregate {ι : Type*} (S : Finset ι) (bd cph lapLen : ι → ℕ)
    (K cardIj W X R : ℕ)
    (hbd : ∀ i ∈ S, bd i ≤ K * cardIj * lapLen i)
    (hlap : ∀ i ∈ S, lapLen i ≤ W * cph i)
    (hcount : ∑ i ∈ S, cph i ≤ X / R) :
    ∑ i ∈ S, bd i ≤ K * cardIj * W * (X / R) := by
  have hbd2 : ∀ i ∈ S, bd i ≤ (K * cardIj * W) * cph i := by
    intro i hi
    calc bd i ≤ K * cardIj * lapLen i := hbd i hi
      _ ≤ K * cardIj * (W * cph i) := Nat.mul_le_mul (le_refl _) (hlap i hi)
      _ = (K * cardIj * W) * cph i := by ring
  exact Erdos260.O1FineFibreBalance.incompleteLap_mass_le S bd cph (K * cardIj * W) X R hbd2 hcount

/-- **AL.4c exposure-weighted aggregate incomplete-lap bound.**  Multiplying by
    the exposure weight `h_λ ≤ H = r + 1 = O_Q(L)` keeps the incomplete-lap
    contribution `≤ H·K·|I_j|·W·(X/R) = O_Q(L²·X/R·|I_j|)`, which is `o(X|I_j|)`
    because `R = X^{1/2+ρ}` with `ρ > 0`. -/
theorem incompleteLap_exposure_aggregate {ι : Type*} (S : Finset ι)
    (bd cph lapLen hh : ι → ℕ) (H K cardIj W X R : ℕ)
    (hbd : ∀ i ∈ S, bd i ≤ K * cardIj * lapLen i)
    (hlap : ∀ i ∈ S, lapLen i ≤ W * cph i)
    (hexp : ∀ i ∈ S, hh i ≤ H)
    (hcount : ∑ i ∈ S, cph i ≤ X / R) :
    ∑ i ∈ S, hh i * bd i ≤ H * (K * cardIj * W * (X / R)) := by
  have hagg := incompleteLap_aggregate S bd cph lapLen K cardIj W X R hbd hlap hcount
  calc ∑ i ∈ S, hh i * bd i
      ≤ ∑ i ∈ S, H * bd i :=
        Finset.sum_le_sum (fun i hi => Nat.mul_le_mul (hexp i hi) (le_refl (bd i)))
    _ = H * ∑ i ∈ S, bd i := by rw [Finset.mul_sum]
    _ ≤ H * (K * cardIj * W * (X / R)) := Nat.mul_le_mul (le_refl H) hagg

/-- The high-support phase count `∑_λ c_λ ≤ X/R` re-exported in the exact shape
    consumed by `incompleteLap_aggregate` (the (I.2a) boundary lever). -/
theorem incompleteLap_count_le_div {ι : Type*}
    (S : Finset ι) (seg : ι → Finset ℕ) (c : ι → ℕ) (X R : ℕ) (hR1 : 0 < R)
    (hsub : ∀ i ∈ S, seg i ⊆ Finset.range X)
    (hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (seg i) (seg j))
    (hcR : ∀ i ∈ S, c i * R ≤ (seg i).card) :
    ∑ i ∈ S, c i ≤ X / R :=
  Erdos260.HighSupportPhaseCount.sum_phasecount_le_div S seg c X R hR1 hsub hdisj hcR

/-! ## Section F. Packaged incomplete-lap boundary surfaces (AL.4a--AL.4c) -/

/-- Residual input surface for AL.4b after the local lap-displacement and
high-support phase-count hypotheses have been exposed.  The conclusion is the
unweighted aggregate incomplete-lap bound. -/
structure O1IncompleteLapInputs {ι : Type*} (S : Finset ι)
    (bd cph lapLen : ι → ℕ) (K cardIj W X R : ℕ) where
  hbd : ∀ i ∈ S, bd i ≤ K * cardIj * lapLen i
  hlap : ∀ i ∈ S, lapLen i ≤ W * cph i
  hcount : ∑ i ∈ S, cph i ≤ X / R

namespace O1IncompleteLapInputs

/-- Packaged AL.4b aggregate incomplete-lap bound. -/
theorem aggregate {ι : Type*} (S : Finset ι) (bd cph lapLen : ι → ℕ)
    (K cardIj W X R : ℕ)
    (I : O1IncompleteLapInputs S bd cph lapLen K cardIj W X R) :
    ∑ i ∈ S, bd i ≤ K * cardIj * W * (X / R) :=
  incompleteLap_aggregate S bd cph lapLen K cardIj W X R I.hbd I.hlap I.hcount

end O1IncompleteLapInputs

/-- Segment-level AL.4b surface: the high-support phase-count estimate is
derived from disjoint segment witnesses instead of being supplied as a summed
inequality. -/
structure O1IncompleteLapSegmentInputs {ι : Type*} (S : Finset ι)
    (seg : ι → Finset ℕ) (bd cph lapLen : ι → ℕ) (K cardIj W X R : ℕ) where
  hR1 : 0 < R
  hsub : ∀ i ∈ S, seg i ⊆ Finset.range X
  hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (seg i) (seg j)
  hcR : ∀ i ∈ S, cph i * R ≤ (seg i).card
  hbd : ∀ i ∈ S, bd i ≤ K * cardIj * lapLen i
  hlap : ∀ i ∈ S, lapLen i ≤ W * cph i

namespace O1IncompleteLapSegmentInputs

/-- Convert segment-level AL.4 data into the summed AL.4b package. -/
def toInputs {ι : Type*} (S : Finset ι) (seg : ι → Finset ℕ)
    (bd cph lapLen : ι → ℕ) (K cardIj W X R : ℕ)
    (I : O1IncompleteLapSegmentInputs S seg bd cph lapLen K cardIj W X R) :
    O1IncompleteLapInputs S bd cph lapLen K cardIj W X R where
  hbd := I.hbd
  hlap := I.hlap
  hcount := incompleteLap_count_le_div S seg cph X R I.hR1 I.hsub I.hdisj I.hcR

/-- Packaged AL.4b bound from disjoint high-support segment witnesses. -/
theorem aggregate {ι : Type*} (S : Finset ι) (seg : ι → Finset ℕ)
    (bd cph lapLen : ι → ℕ) (K cardIj W X R : ℕ)
    (I : O1IncompleteLapSegmentInputs S seg bd cph lapLen K cardIj W X R) :
    ∑ i ∈ S, bd i ≤ K * cardIj * W * (X / R) :=
  O1IncompleteLapInputs.aggregate S bd cph lapLen K cardIj W X R
    (toInputs S seg bd cph lapLen K cardIj W X R I)

end O1IncompleteLapSegmentInputs

/-- Convert the dyadic per-edge gap bound of AL.4a into the count-form
lap-length hypothesis consumed by the AL.4b/AL.4c aggregate packages.  The
integer displacement `cumGap` is turned into the non-negative carrier length by
`Int.toNat`. -/
theorem incompleteLap_lapLen_le_of_gapBound {Iota : Type*} (S : Finset Iota)
    (gap : Iota -> Nat -> Int) (lapLen cph : Iota -> Nat) (W : Nat)
    (hlapDef : forall i, i ∈ S -> lapLen i = Int.toNat (cumGap (gap i) (cph i)))
    (hgap : forall i, i ∈ S -> forall a, a < cph i -> gap i a <= (W : Int)) :
    forall i, i ∈ S -> lapLen i <= W * cph i := by
  intro i hi
  rw [hlapDef i hi]
  rw [Int.toNat_le]
  have h := lapDisplacement_le (gap i) (W : Int) (cph i) (hgap i hi)
  simpa using h

/-- Segment-level AL.4b surface with AL.4a supplied in its manuscript form:
actual per-phase gap bounds plus the definition of the lap length from the
cumulative displacement. -/
structure O1IncompleteLapGapSegmentInputs {Iota : Type*} (S : Finset Iota)
    (seg : Iota -> Finset Nat) (gap : Iota -> Nat -> Int)
    (bd cph lapLen : Iota -> Nat) (K cardIj W X R : Nat) where
  hR1 : 0 < R
  hsub : forall i, i ∈ S -> seg i ⊆ Finset.range X
  hdisj : forall i, i ∈ S -> forall j, j ∈ S -> i ≠ j -> Disjoint (seg i) (seg j)
  hcR : forall i, i ∈ S -> cph i * R <= (seg i).card
  hbd : forall i, i ∈ S -> bd i <= K * cardIj * lapLen i
  hlapDef : forall i, i ∈ S -> lapLen i = Int.toNat (cumGap (gap i) (cph i))
  hgap : forall i, i ∈ S -> forall a, a < cph i -> gap i a <= (W : Int)

namespace O1IncompleteLapGapSegmentInputs

/-- Forget the pointwise gap witnesses after deriving the lap-length bound. -/
def toSegmentInputs {Iota : Type*} (S : Finset Iota) (seg : Iota -> Finset Nat)
    (gap : Iota -> Nat -> Int) (bd cph lapLen : Iota -> Nat) (K cardIj W X R : Nat)
    (J : O1IncompleteLapGapSegmentInputs S seg gap bd cph lapLen K cardIj W X R) :
    O1IncompleteLapSegmentInputs S seg bd cph lapLen K cardIj W X R where
  hR1 := J.hR1
  hsub := J.hsub
  hdisj := J.hdisj
  hcR := J.hcR
  hbd := J.hbd
  hlap := incompleteLap_lapLen_le_of_gapBound S gap lapLen cph W J.hlapDef J.hgap

/-- Manuscript-form gap witnesses also feed the summed AL.4b package directly. -/
def toInputs {Iota : Type*} (S : Finset Iota) (seg : Iota -> Finset Nat)
    (gap : Iota -> Nat -> Int) (bd cph lapLen : Iota -> Nat) (K cardIj W X R : Nat)
    (J : O1IncompleteLapGapSegmentInputs S seg gap bd cph lapLen K cardIj W X R) :
    O1IncompleteLapInputs S bd cph lapLen K cardIj W X R :=
  O1IncompleteLapSegmentInputs.toInputs S seg bd cph lapLen K cardIj W X R
    (toSegmentInputs S seg gap bd cph lapLen K cardIj W X R J)

/-- Packaged AL.4b bound from manuscript-form gap witnesses and high-support
segment witnesses. -/
theorem aggregate {Iota : Type*} (S : Finset Iota) (seg : Iota -> Finset Nat)
    (gap : Iota -> Nat -> Int) (bd cph lapLen : Iota -> Nat) (K cardIj W X R : Nat)
    (J : O1IncompleteLapGapSegmentInputs S seg gap bd cph lapLen K cardIj W X R) :
    ∑ i ∈ S, bd i <= K * cardIj * W * (X / R) :=
  O1IncompleteLapInputs.aggregate S bd cph lapLen K cardIj W X R
    (toInputs S seg gap bd cph lapLen K cardIj W X R J)

end O1IncompleteLapGapSegmentInputs

/-- Residual input surface for AL.4c, the exposure-weighted incomplete-lap
bound.  This folds AL.4a and AL.4b into one reusable package. -/
structure O1IncompleteLapExposureInputs {ι : Type*} (S : Finset ι)
    (bd cph lapLen hh : ι → ℕ) (H K cardIj W X R : ℕ) where
  hbd : ∀ i ∈ S, bd i ≤ K * cardIj * lapLen i
  hlap : ∀ i ∈ S, lapLen i ≤ W * cph i
  hexp : ∀ i ∈ S, hh i ≤ H
  hcount : ∑ i ∈ S, cph i ≤ X / R

namespace O1IncompleteLapExposureInputs

/-- Packaged AL.4c exposure-weighted aggregate incomplete-lap bound. -/
theorem aggregate {ι : Type*} (S : Finset ι) (bd cph lapLen hh : ι → ℕ)
    (H K cardIj W X R : ℕ)
    (I : O1IncompleteLapExposureInputs S bd cph lapLen hh H K cardIj W X R) :
    ∑ i ∈ S, hh i * bd i ≤ H * (K * cardIj * W * (X / R)) :=
  incompleteLap_exposure_aggregate S bd cph lapLen hh H K cardIj W X R
    I.hbd I.hlap I.hexp I.hcount

end O1IncompleteLapExposureInputs

/-- Segment-level AL.4c surface: high-support phase count is derived from
disjoint segment witnesses, and exposure weights are bounded by `H`. -/
structure O1IncompleteLapExposureSegmentInputs {ι : Type*} (S : Finset ι)
    (seg : ι → Finset ℕ) (bd cph lapLen hh : ι → ℕ)
    (H K cardIj W X R : ℕ) where
  hR1 : 0 < R
  hsub : ∀ i ∈ S, seg i ⊆ Finset.range X
  hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (seg i) (seg j)
  hcR : ∀ i ∈ S, cph i * R ≤ (seg i).card
  hbd : ∀ i ∈ S, bd i ≤ K * cardIj * lapLen i
  hlap : ∀ i ∈ S, lapLen i ≤ W * cph i
  hexp : ∀ i ∈ S, hh i ≤ H

namespace O1IncompleteLapExposureSegmentInputs

/-- Convert segment-level AL.4c data into the summed exposure package. -/
def toInputs {ι : Type*} (S : Finset ι) (seg : ι → Finset ℕ)
    (bd cph lapLen hh : ι → ℕ) (H K cardIj W X R : ℕ)
    (I : O1IncompleteLapExposureSegmentInputs S seg bd cph lapLen hh H K cardIj W X R) :
    O1IncompleteLapExposureInputs S bd cph lapLen hh H K cardIj W X R where
  hbd := I.hbd
  hlap := I.hlap
  hexp := I.hexp
  hcount := incompleteLap_count_le_div S seg cph X R I.hR1 I.hsub I.hdisj I.hcR

/-- Packaged AL.4c bound from disjoint high-support segment witnesses. -/
theorem aggregate {ι : Type*} (S : Finset ι) (seg : ι → Finset ℕ)
    (bd cph lapLen hh : ι → ℕ) (H K cardIj W X R : ℕ)
    (I : O1IncompleteLapExposureSegmentInputs S seg bd cph lapLen hh H K cardIj W X R) :
    ∑ i ∈ S, hh i * bd i ≤ H * (K * cardIj * W * (X / R)) :=
  O1IncompleteLapExposureInputs.aggregate S bd cph lapLen hh H K cardIj W X R
    (toInputs S seg bd cph lapLen hh H K cardIj W X R I)

end O1IncompleteLapExposureSegmentInputs

/-- Segment-level AL.4c surface with the AL.4a dyadic gap bound supplied before
conversion to the lap-length hypothesis. -/
structure O1IncompleteLapGapExposureSegmentInputs {Iota : Type*} (S : Finset Iota)
    (seg : Iota -> Finset Nat) (gap : Iota -> Nat -> Int)
    (bd cph lapLen hh : Iota -> Nat) (H K cardIj W X R : Nat) where
  hR1 : 0 < R
  hsub : forall i, i ∈ S -> seg i ⊆ Finset.range X
  hdisj : forall i, i ∈ S -> forall j, j ∈ S -> i ≠ j -> Disjoint (seg i) (seg j)
  hcR : forall i, i ∈ S -> cph i * R <= (seg i).card
  hbd : forall i, i ∈ S -> bd i <= K * cardIj * lapLen i
  hlapDef : forall i, i ∈ S -> lapLen i = Int.toNat (cumGap (gap i) (cph i))
  hgap : forall i, i ∈ S -> forall a, a < cph i -> gap i a <= (W : Int)
  hexp : forall i, i ∈ S -> hh i <= H

namespace O1IncompleteLapGapExposureSegmentInputs

/-- Forget the pointwise gap witnesses after deriving the AL.4a lap-length
bound, retaining the exposure and high-support segment data. -/
def toExposureSegmentInputs {Iota : Type*} (S : Finset Iota)
    (seg : Iota -> Finset Nat) (gap : Iota -> Nat -> Int)
    (bd cph lapLen hh : Iota -> Nat) (H K cardIj W X R : Nat)
    (J : O1IncompleteLapGapExposureSegmentInputs S seg gap bd cph lapLen hh
        H K cardIj W X R) :
    O1IncompleteLapExposureSegmentInputs S seg bd cph lapLen hh H K cardIj W X R where
  hR1 := J.hR1
  hsub := J.hsub
  hdisj := J.hdisj
  hcR := J.hcR
  hbd := J.hbd
  hlap := incompleteLap_lapLen_le_of_gapBound S gap lapLen cph W J.hlapDef J.hgap
  hexp := J.hexp

/-- Manuscript-form gap and exposure witnesses feed the summed AL.4c package directly. -/
def toInputs {Iota : Type*} (S : Finset Iota)
    (seg : Iota -> Finset Nat) (gap : Iota -> Nat -> Int)
    (bd cph lapLen hh : Iota -> Nat) (H K cardIj W X R : Nat)
    (J : O1IncompleteLapGapExposureSegmentInputs S seg gap bd cph lapLen hh
        H K cardIj W X R) :
    O1IncompleteLapExposureInputs S bd cph lapLen hh H K cardIj W X R :=
  O1IncompleteLapExposureSegmentInputs.toInputs S seg bd cph lapLen hh H K cardIj W X R
    (toExposureSegmentInputs S seg gap bd cph lapLen hh H K cardIj W X R J)

/-- Packaged AL.4c exposure-weighted bound from manuscript-form gap witnesses
and high-support segment witnesses. -/
theorem aggregate {Iota : Type*} (S : Finset Iota) (seg : Iota -> Finset Nat)
    (gap : Iota -> Nat -> Int) (bd cph lapLen hh : Iota -> Nat)
    (H K cardIj W X R : Nat)
    (J : O1IncompleteLapGapExposureSegmentInputs S seg gap bd cph lapLen hh
        H K cardIj W X R) :
    ∑ i ∈ S, hh i * bd i <= H * (K * cardIj * W * (X / R)) :=
  O1IncompleteLapExposureInputs.aggregate S bd cph lapLen hh H K cardIj W X R
    (toInputs S seg gap bd cph lapLen hh H K cardIj W X R J)

end O1IncompleteLapGapExposureSegmentInputs

/-- Machine-readable summary of the O1 supply-atlas surfaces closed here. -/
def o1SupplyAtlasClosedItems : List String :=
  [ "affine row charts are injective on each cell",
    "affine successor maps preserve per-edge counting measure",
    "closed-lap, zero-lap, and sum-gap-zero bridges produce O1CycleChartInputs",
    "packaged affine closed-lap, zero-lap, and sum-gap-zero atlas surfaces feed O1CycleChartInputs and edge measure preservation",
    "affine complete-lap packages produce per-edge fibre equivalences",
    "unweighted incomplete-lap aggregate bound is packaged",
    "exposure-weighted incomplete-lap aggregate bound is packaged",
    "high-support segment witnesses feed the incomplete-lap aggregate packages",
    "dyadic per-gap bounds derive the incomplete-lap lap-length packages",
    "manuscript-form gap and segment witnesses feed the final AL.4 aggregate packages directly" ]

/-- Machine-readable summary of O1 supply-atlas inputs still external here. -/
def o1SupplyAtlasOpenItems : List String :=
  [ "actual complete-lap return/wrap-edge or sum-gap-zero certificate for recurrent cells",
    "actual fine-fibre affine chart data from the terminal-labelled recurrent graph",
    "actual dyadic gap-bound witnesses and high-support segment witnesses for concrete cells",
    "asymptotic little-o conversion of the finite incomplete-lap bound" ]

theorem o1SupplyAtlasClosedItems_length :
    o1SupplyAtlasClosedItems.length = 10 := by
  rfl

theorem o1SupplyAtlasOpenItems_length :
    o1SupplyAtlasOpenItems.length = 4 := by
  rfl

end Erdos260.O1SupplyAtlas
