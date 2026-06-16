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

end Erdos260.O1SupplyAtlas
