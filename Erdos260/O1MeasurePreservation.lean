/-
  Erdős #260 — O1 discrete measure-PRESERVATION core (Appendix R, the single
  highest-risk analytic input).  NEW module; it edits no existing file.

  Goal.  Upgrade the O1 fine-fibre lane from "injectivity + a one-sided valid
  bound" toward the genuine TWO-SIDED measure preservation that
  `lem:r-cycle-map-preserves-measure` actually asserts: the cyclic transition
  `τ_a : Ω°_{λ,a} → Ω°_{λ,a+1}` is a *measure-preserving bijection* between the
  interior event fibres.  Where `O1FineFibreBalance.fineFibre_phaseMass_eq`
  derives the phase-mass equality from the two charts being injective, and
  `fineFibre_card_le_ambient` only gives the inequality `|C_λ| ≤ |Ω_a|`, here we
  prove the EQUALITY from an *explicit bijection* and propagate it to the exact
  complete-lap balance.

  Manuscript anchors (`proof_v4_repaired_core_v71_p2_preprint_hygiene.tex`):
  * App R  Def `def:r-complete-lap`                              (line 8703)
           Lemma `lem:r-cycle-map-preserves-measure` (THE target) (line 8733)
           Lemma `lem:r-global-phase-error` (R.1b, equality)      (line 8779)
           Prop  `prop:r-exit-share-closed`  (R.2′ valid bound)   (line 8822)
  * App AL Lemma `lem:al-successor-same-carrier-bijection` (AL.2/AL.3) (line 11645)
           Lemma `lem:al-complete-lap` (AL.6 phase masses equal)  (line 11721)
  * App AQ Lemma `lem:aq-simple-cycle-atlas-row` (AQ.5/AQ.6 charts, τ_a(ι_a u)=ι_{a+1}u,
           injectivity + surjectivity, the affine relabelling)    (line 12266)
           Lemma `lem:aq-failed-atlas-paid` (Bij_a: x ↦ x+g_a)    (line 12338)

  What is machine-checked here (sorry-free):
  (A) Pure discrete measure preservation under a Finset bijection (two-sided):
      a bijection `φ` between Finsets preserves counting measure
      (`(F.image φ).card = F.card`) and counting-measure integrals
      (`∑_{x∈F} w(φ x) = ∑_{y∈φ(F)} w y`), via `Finset.card_bij`/`Finset.sum_bij`.
  (B) The cyclic transition `τ_a` is a measure-preserving bijection between the
      fibres: from the chart-compatibility `τ_a(ι_a u) = ι_{a+1} u` (AQ.6) and the
      injectivity of the target chart, `Set.BijOn τ_a Ω_a Ω_{a+1}` — both injective
      AND surjective — hence `|Ω_a| = |Ω_{a+1}|` (the ≤ → = upgrade) and the
      weighted preservation; packaged as a genuine `Equiv` on the fibres.
  (C) The affine relabelling kernel: `x ↦ a·x + t` with `a` a unit is a bijection
      (an `Equiv`) on any commutative ring, specialised to `ℤ` (`x ↦ x + g_a`, the
      two-sided upgrade of `startTranslation_injective`) and to the finite index
      set `ZMod n` (giving the invertibility the manuscript asserts in one line).
  (D) Cycle-saturation ⇒ equal phase mass over a complete lap: the per-edge
      bijections (B) give `|Ω_a| = |Ω_{a+1}|`; a complete lap visits each phase of
      `ZMod c` exactly once, so all phase masses are equal, and feeding this into
      `O1FineFibreBalance.completeLap_phase_mass_identity` yields the EXACT ratio
      `c · ExitMass(F) = b · M_tot` (equality, both directions), discharging the
      one-sided bound to the genuine balance from the explicit bijection.

  Only the genuinely geometric inputs are hypotheses (charts inject on the carrier;
  the successor satisfies `τ_a(ι_a u) = ι_{a+1} u`; the phase set is the cycle
  `ZMod c`).  The measure-preservation / bijection ARITHMETIC is proved.

  No `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/
import Mathlib
import Erdos260.O1FineFibreBalance

namespace Erdos260.O1MeasurePreservation

open Finset

/-! ===========================================================================
    ## Section A.  Discrete measure preservation under a bijection (two-sided).

    The pure arithmetic core: a bijection between finite sets preserves counting
    measure, both as a cardinality and as a counting-measure integral.  These are
    the `Finset.card_bij` / `Finset.sum_bij` kernels the manuscript leans on when
    it says "a bijection preserves counting measure on a finite set" (AL proof,
    line 11658).
    =========================================================================== -/

/-- **Counting measure is preserved by a Finset bijection (cardinality form).**
    If `φ` maps `s` into `t`, is injective on `s`, and is surjective onto `t`, then
    `|s| = |t|`.  This is the genuine two-sided fact (`≤` in both directions),
    upgrading any one-sided injection bound to an equality. -/
theorem measurePreserving_card_of_bij {α β : Type*}
    (s : Finset α) (t : Finset β) (φ : α → β)
    (hmaps : ∀ x ∈ s, φ x ∈ t)
    (hinj : ∀ x ∈ s, ∀ y ∈ s, φ x = φ y → x = y)
    (hsurj : ∀ y ∈ t, ∃ x ∈ s, φ x = y) :
    s.card = t.card := by
  refine Finset.card_bij (fun a _ => φ a) (fun a ha => hmaps a ha)
    (fun a ha b hb h => hinj a ha b hb h) ?_
  intro b hb
  obtain ⟨x, hx, hxb⟩ := hsurj b hb
  exact ⟨x, hx, hxb⟩

/-- **Counting measure is preserved by a Finset bijection (integral form).**
    With the same bijection hypotheses, the counting-measure integral of any weight
    `w` transports: `∑_{x∈s} w(φ x) = ∑_{y∈t} w y`.  This is the genuine
    measure-preservation statement beyond cardinality. -/
theorem measurePreserving_sum_of_bij {α β M : Type*} [AddCommMonoid M]
    (s : Finset α) (t : Finset β) (φ : α → β) (w : β → M)
    (hmaps : ∀ x ∈ s, φ x ∈ t)
    (hinj : ∀ x ∈ s, ∀ y ∈ s, φ x = φ y → x = y)
    (hsurj : ∀ y ∈ t, ∃ x ∈ s, φ x = y) :
    ∑ x ∈ s, w (φ x) = ∑ y ∈ t, w y := by
  refine Finset.sum_bij (fun a _ => φ a) (fun a ha => hmaps a ha)
    (fun a ha b hb h => hinj a ha b hb h) ?_ (fun a _ => rfl)
  intro b hb
  obtain ⟨x, hx, hxb⟩ := hsurj b hb
  exact ⟨x, hx, hxb⟩

/-- The `(F.image φ).card = F.card` form requested by the task: an injective `φ`
    relabels `F` onto its image preserving counting measure. -/
theorem image_card_eq_of_injOn {α β : Type*} [DecidableEq β]
    (s : Finset α) (φ : α → β) (hinj : Set.InjOn φ ↑s) :
    (s.image φ).card = s.card :=
  Finset.card_image_of_injOn hinj

/-- The weighted `∑_{y∈φ(F)} w y = ∑_{x∈F} w(φ x)` form: counting-measure integral
    is preserved under the injective relabelling onto the image. -/
theorem image_sum_eq_of_injOn {α β M : Type*} [DecidableEq β] [AddCommMonoid M]
    (s : Finset α) (φ : α → β) (w : β → M)
    (hinj : ∀ x ∈ s, ∀ y ∈ s, φ x = φ y → x = y) :
    ∑ y ∈ s.image φ, w y = ∑ x ∈ s, w (φ x) :=
  Finset.sum_image (fun x hx y hy h => hinj x hx y hy h)

/-- Cardinality preservation read off directly from `Set.BijOn` between the
    coercions of two Finsets (the bridge from a genuine bijection to the count). -/
theorem bijOn_finset_card_eq {α β : Type*} {φ : α → β} {s : Finset α} {t : Finset β}
    (h : Set.BijOn φ ↑s ↑t) : s.card = t.card := by
  refine Finset.card_bij (fun a _ => φ a) ?_ ?_ ?_
  · intro a ha; exact Finset.mem_coe.mp (h.mapsTo (Finset.mem_coe.mpr ha))
  · intro a ha b hb hab; exact h.injOn (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab
  · intro b hb
    obtain ⟨a, ha, hab⟩ := h.surjOn (Finset.mem_coe.mpr hb)
    exact ⟨a, Finset.mem_coe.mp ha, hab⟩

/-- Counting-measure integral preservation read off directly from `Set.BijOn`. -/
theorem bijOn_finset_sum_eq {α β M : Type*} [AddCommMonoid M] {φ : α → β}
    {s : Finset α} {t : Finset β} (w : β → M) (h : Set.BijOn φ ↑s ↑t) :
    ∑ x ∈ s, w (φ x) = ∑ y ∈ t, w y := by
  refine Finset.sum_bij (fun a _ => φ a) ?_ ?_ ?_ (fun a _ => rfl)
  · intro a ha; exact Finset.mem_coe.mp (h.mapsTo (Finset.mem_coe.mpr ha))
  · intro a ha b hb hab; exact h.injOn (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab
  · intro b hb
    obtain ⟨a, ha, hab⟩ := h.surjOn (Finset.mem_coe.mpr hb)
    exact ⟨a, Finset.mem_coe.mp ha, hab⟩

/-! ===========================================================================
    ## Section B.  The cyclic transition `τ_a` is a measure-preserving bijection.
                                                            (THE App R target)

    Manuscript: App AL `lem:al-successor-same-carrier-bijection` (line 11645) and
    App AQ `lem:aq-simple-cycle-atlas-row` (AQ.6, line 12317): in the complete-lap
    coordinates the successor satisfies `τ_a(ι_a u) = ι_{a+1} u`.  The fibres are
    the chart images `Ω_a = ι_a(C_λ)`, `Ω_{a+1} = ι_{a+1}(C_λ)`.

    We take the genuinely geometric facts as HYPOTHESES — the charts realize the
    fibres (`Ω_a = Cset.image ι_a`), the target chart `ι_{a+1}` is injective on
    the carrier, and the compatibility `τ(ι_a u) = ι_{a+1} u` — and PROVE that the
    transition is a bijection (mapsTo + injOn + surjOn) between the fibres, hence
    measure-preserving: `|Ω_a| = |Ω_{a+1}|` (the upgrade of
    `fineFibre_card_le_ambient` from `≤` to `=`) and the weighted preservation.
    =========================================================================== -/

variable {C Ω : Type*} [DecidableEq Ω]

/-- **The cyclic transition is a bijection between the interior event fibres
    (`lem:r-cycle-map-preserves-measure`, via AL.2/AL.3 and AQ.6).**  From the
    chart-compatibility `τ(ι_a u) = ι_{a+1} u` and injectivity of the target chart,
    `τ` restricts to a bijection `Ω_a → Ω_{a+1}`: it maps the fibre into the next
    fibre, is injective there (distinct base events have distinct images), and is
    surjective onto it (the next fibre is the charted image of the same carrier).
    This is the explicit two-sided bijection the manuscript asserts in one line. -/
theorem cycleMap_bijOn
    (Cset : Finset C) (Ωa Ωb : Finset Ω) (ιa ιb : C → Ω) (τ : Ω → Ω)
    (haImg : Ωa = Cset.image ιa) (hbImg : Ωb = Cset.image ιb)
    (hbInj : Set.InjOn ιb ↑Cset)
    (hcompat : ∀ u ∈ Cset, τ (ιa u) = ιb u) :
    Set.BijOn τ ↑Ωa ↑Ωb := by
  subst haImg hbImg
  refine ⟨?_, ?_, ?_⟩
  · -- MapsTo: τ sends the fibre into the next fibre.
    intro ω hω
    rw [Finset.mem_coe, Finset.mem_image] at hω
    obtain ⟨u, hu, rfl⟩ := hω
    rw [Finset.mem_coe, Finset.mem_image]
    exact ⟨u, hu, (hcompat u hu).symm⟩
  · -- InjOn: distinct base events have distinct images (via the target chart).
    intro ω hω ω' hω' hτ
    rw [Finset.mem_coe, Finset.mem_image] at hω hω'
    obtain ⟨u, hu, rfl⟩ := hω
    obtain ⟨u', hu', rfl⟩ := hω'
    rw [hcompat u hu, hcompat u' hu'] at hτ
    rw [hbInj (Finset.mem_coe.mpr hu) (Finset.mem_coe.mpr hu') hτ]
  · -- SurjOn: the next fibre is the charted image of the same carrier.
    intro ω' hω'
    rw [Finset.mem_coe, Finset.mem_image] at hω'
    obtain ⟨u, hu, rfl⟩ := hω'
    exact ⟨ιa u, by rw [Finset.mem_coe, Finset.mem_image]; exact ⟨u, hu, rfl⟩, hcompat u hu⟩

/-- **Measure preservation, cardinality form (R.1b at the fibre level; the
    `fineFibre_card_le_ambient` ≤ → = upgrade).**  The cyclic transition gives
    `|Ω_a| = |Ω_{a+1}|`: equal counting mass, derived from the *bijection* `τ`
    itself (not from the two images sharing a domain). -/
theorem cycleMap_card_eq
    (Cset : Finset C) (Ωa Ωb : Finset Ω) (ιa ιb : C → Ω) (τ : Ω → Ω)
    (haImg : Ωa = Cset.image ιa) (hbImg : Ωb = Cset.image ιb)
    (hbInj : Set.InjOn ιb ↑Cset)
    (hcompat : ∀ u ∈ Cset, τ (ιa u) = ιb u) :
    Ωa.card = Ωb.card :=
  bijOn_finset_card_eq (cycleMap_bijOn Cset Ωa Ωb ιa ιb τ haImg hbImg hbInj hcompat)

/-- **Measure preservation, integral form.**  The cyclic transition preserves the
    counting-measure integral of any weight: `∑_{ω∈Ω_a} w(τ ω) = ∑_{ω∈Ω_{a+1}} w ω`.
    This is the full "measure-preserving" content of
    `lem:r-cycle-map-preserves-measure`, beyond mere cardinality. -/
theorem cycleMap_measure_preserving {M : Type*} [AddCommMonoid M]
    (Cset : Finset C) (Ωa Ωb : Finset Ω) (ιa ιb : C → Ω) (τ : Ω → Ω) (w : Ω → M)
    (haImg : Ωa = Cset.image ιa) (hbImg : Ωb = Cset.image ιb)
    (hbInj : Set.InjOn ιb ↑Cset)
    (hcompat : ∀ u ∈ Cset, τ (ιa u) = ιb u) :
    ∑ ω ∈ Ωa, w (τ ω) = ∑ ω' ∈ Ωb, w ω' :=
  bijOn_finset_sum_eq w (cycleMap_bijOn Cset Ωa Ωb ιa ιb τ haImg hbImg hbInj hcompat)

/-- **The cyclic transition packaged as a genuine `Equiv` on the fibres.**  The
    bijection of `cycleMap_bijOn` induces `Ω_a ≃ Ω_{a+1}` (the same-carrier
    bijection of AL.6), an honest invertible relabelling of the interior event
    fibres — the object `lem:r-cycle-map-preserves-measure` calls `τ_a`. -/
noncomputable def cycleEquiv
    (Cset : Finset C) (Ωa Ωb : Finset Ω) (ιa ιb : C → Ω) (τ : Ω → Ω)
    (haImg : Ωa = Cset.image ιa) (hbImg : Ωb = Cset.image ιb)
    (hbInj : Set.InjOn ιb ↑Cset)
    (hcompat : ∀ u ∈ Cset, τ (ιa u) = ιb u) :
    {ω : Ω // ω ∈ (↑Ωa : Set Ω)} ≃ {ω : Ω // ω ∈ (↑Ωb : Set Ω)} :=
  Set.BijOn.equiv τ (cycleMap_bijOn Cset Ωa Ωb ιa ιb τ haImg hbImg hbInj hcompat)

/-! ===========================================================================
    ## Section C.  The affine-relabelling bijectivity kernel.

    Manuscript: App AQ `lem:aq-simple-cycle-atlas-row` (AQ.4/AQ.5, line 12290): the
    chart `ι_a` transports a base event at start `x(u)` to start `x(u) + G_a`; and
    `lem:aq-failed-atlas-paid` (Bij_a, line 12365): "the target start is
    `x ↦ x + g_a`, which is injective on integers".  We give the genuine TWO-SIDED
    statement: `x ↦ a·x + t` with `a` a unit is a *bijection* (an `Equiv`), which
    is what makes the transition surjective onto the target fibre.
    =========================================================================== -/

/-- **The affine relabelling `x ↦ a·x + t` as an `Equiv`**, for a unit `a` of any
    commutative ring (inverse `y ↦ a⁻¹·(y − t)`).  This is the invertibility the
    manuscript asserts for the endpoint/carry coordinate map in one paragraph. -/
def affineEquiv {R : Type*} [CommRing R] (a : Rˣ) (t : R) : R ≃ R where
  toFun x := (a : R) * x + t
  invFun y := (↑a⁻¹ : R) * (y - t)
  left_inv := fun x => by
    have h1 : (↑a⁻¹ : R) * (↑a : R) = 1 := a.inv_mul
    show (↑a⁻¹ : R) * ((↑a : R) * x + t - t) = x
    have e : (↑a : R) * x + t - t = (↑a : R) * x := by ring
    rw [e, ← mul_assoc, h1, one_mul]
  right_inv := fun y => by
    have h2 : (↑a : R) * (↑a⁻¹ : R) = 1 := a.mul_inv
    show (↑a : R) * ((↑a⁻¹ : R) * (y - t)) + t = y
    have e : (↑a : R) * ((↑a⁻¹ : R) * (y - t)) = y - t := by
      rw [← mul_assoc, h2, one_mul]
    rw [e]; ring

@[simp] theorem affineEquiv_apply {R : Type*} [CommRing R] (a : Rˣ) (t x : R) :
    affineEquiv a t x = (a : R) * x + t := rfl

/-- **The affine relabelling is a bijection** (`Bij_a`, two-sided form). -/
theorem affineMap_bijective {R : Type*} [CommRing R] (a : Rˣ) (t : R) :
    Function.Bijective (fun x : R => (a : R) * x + t) :=
  (affineEquiv a t).bijective

/-- **Integer start translation `x ↦ x + g` is a bijection** — the two-sided
    upgrade of `O1FineFibreBalance.startTranslation_injective` (which gave only
    injectivity).  Surjectivity is what the manuscript needs for the transition to
    hit every target start. -/
theorem intTranslation_bijective (g : ℤ) :
    Function.Bijective (fun x : ℤ => x + g) :=
  (Equiv.addRight g).bijective

/-- **The affine relabelling is a bijection on the finite index set `ZMod n`.** -/
theorem affineZMod_bijective {n : ℕ} (a : (ZMod n)ˣ) (t : ZMod n) :
    Function.Bijective (fun x : ZMod n => (a : ZMod n) * x + t) :=
  affineMap_bijective a t

/-- On the finite index set `ZMod n` the affine relabelling permutes the whole set:
    its image of the universe has full cardinality `n` (counting measure preserved
    on the finite carrier). -/
theorem affineZMod_image_card {n : ℕ} [NeZero n] (a : (ZMod n)ˣ) (t : ZMod n) :
    (Finset.univ.image (fun x : ZMod n => (a : ZMod n) * x + t)).card = n := by
  have hinj : Set.InjOn (fun x : ZMod n => (a : ZMod n) * x + t)
      ↑(Finset.univ : Finset (ZMod n)) :=
    fun x _ y _ h => (affineMap_bijective a t).injective h
  rw [Finset.card_image_of_injOn hinj, Finset.card_univ]
  exact ZMod.card n

/-- **Concrete realization: the start-translation transition is a measure-preserving
    bijection between integer-start fibres.**  Taking the events to be their integer
    start coordinates and the cyclic transition to be `x ↦ x + g_a` (AQ.6 read on
    starts), `τ` maps the fibre `Ω_a ⊆ ℤ` bijectively onto its translate. -/
theorem startShift_bijOn (g : ℤ) (Ωa : Finset ℤ) :
    Set.BijOn (fun x : ℤ => x + g) ↑Ωa ↑(Ωa.image (fun x : ℤ => x + g)) := by
  refine ⟨fun x hx => ?_,
          fun x _ y _ h => (intTranslation_bijective g).injective h,
          fun y hy => ?_⟩
  · rw [Finset.mem_coe, Finset.mem_image]
    exact ⟨x, Finset.mem_coe.mp hx, rfl⟩
  · rw [Finset.mem_coe, Finset.mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, Finset.mem_coe.mpr hx, rfl⟩

/-- Cardinality preservation for the integer-start transition (≤ → = at the
    concrete level). -/
theorem startShift_card_eq (g : ℤ) (Ωa : Finset ℤ) :
    (Ωa.image (fun x : ℤ => x + g)).card = Ωa.card :=
  image_card_eq_of_injOn Ωa (fun x : ℤ => x + g)
    (fun _ _ _ _ h => (intTranslation_bijective g).injective h)

/-- Counting-measure integral preservation for the integer-start transition. -/
theorem startShift_measure_preserving {M : Type*} [AddCommMonoid M]
    (g : ℤ) (Ωa : Finset ℤ) (w : ℤ → M) :
    ∑ x ∈ Ωa, w (x + g) = ∑ y ∈ Ωa.image (fun x : ℤ => x + g), w y :=
  (image_sum_eq_of_injOn Ωa (fun x : ℤ => x + g) w
    (fun _ _ _ _ h => (intTranslation_bijective g).injective h)).symm

/-! ===========================================================================
    ## Section D.  Cycle-saturation ⇒ equal phase mass ⇒ exact complete-lap balance.

    Manuscript: App AL `lem:al-complete-lap` (AL.6, line 11736): "the ambient phase
    fibres have equal counting mass `Mass(Ω°_{λ,a}) = |C_λ|`" — because the
    successor bijections force consecutive phase masses to agree, and a complete
    lap visits each phase of `ℤ/cℤ` exactly once (the saturation), so all masses
    are equal.  Combining with `O1FineFibreBalance.completeLap_phase_mass_identity`
    discharges the one-sided R.2′ bound to the genuine equality
    `c · ExitMass(F) = b · M_tot` (both directions).
    =========================================================================== -/

/-- **Saturation kernel: consecutive equality around the cycle ⇒ constancy.**  If
    a phase mass `μ : ZMod c → ℕ` satisfies `μ(a+1) = μ a` for every phase
    (the per-edge measure preservation of Section B), then `μ` is constant — a
    complete lap visits each phase exactly once, so all phase masses coincide. -/
theorem phaseMass_const_of_succ_eq (c : ℕ) [NeZero c] (μ : ZMod c → ℕ)
    (h : ∀ a : ZMod c, μ (a + 1) = μ a) : ∀ a : ZMod c, μ a = μ 0 := by
  have key : ∀ n : ℕ, μ (n : ZMod c) = μ 0 := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
        have hcast : ((k + 1 : ℕ) : ZMod c) = (k : ZMod c) + 1 := by push_cast; ring
        rw [hcast, h (k : ZMod c), ih]
  intro a
  obtain ⟨k, rfl⟩ := ZMod.natCast_zmod_surjective a
  exact key k

/-- **Complete-lap balance from per-edge bijections (App R / AL, equality form).**
    Phases are the cycle `ZMod c`; `fib a = Ω°_{λ,a}` is the interior event fibre at
    phase `a`; the genuine geometric input is that the transition `τ a` is a
    bijection `Ω°_{λ,a} → Ω°_{λ,a+1}` for every edge (the relabelling maps fibre
    onto fibre).  Then the per-phase masses `μ a = |Ω°_{λ,a}|` are all equal, and
    the exit phases occupy exactly a `b/c` fraction of the total interior mass:
        `c · ExitMass(F°) = b · M_tot°`,
    an EQUALITY (both directions) — the discharge of `prop:r-exit-share-closed`'s
    one-sided bound to the genuine `lem:r-global-phase-error` (R.1b) balance,
    obtained from the explicit bijections rather than an assumed mass equality. -/
theorem cycle_saturation_balance {Ω : Type*} (c : ℕ) [NeZero c]
    (fib : ZMod c → Finset Ω) (τ : ZMod c → (Ω → Ω)) (E : Finset (ZMod c))
    (hbij : ∀ a : ZMod c, Set.BijOn (τ a) ↑(fib a) ↑(fib (a + 1))) :
    c * (∑ a ∈ E, (fib a).card) = E.card * (∑ a : ZMod c, (fib a).card) := by
  have hsucc : ∀ a : ZMod c, (fib (a + 1)).card = (fib a).card :=
    fun a => (bijOn_finset_card_eq (hbij a)).symm
  have hconst := phaseMass_const_of_succ_eq c (fun b => (fib b).card) hsucc
  have hc : (Finset.univ : Finset (ZMod c)).card = c := by
    rw [Finset.card_univ]; exact ZMod.card c
  have hid := Erdos260.O1FineFibreBalance.completeLap_phase_mass_identity
    (Finset.univ : Finset (ZMod c)) E (fun b => (fib b).card) ((fib 0).card)
    (Finset.subset_univ E) (fun a _ => hconst a)
  rw [hc] at hid
  unfold Erdos260.O1FineFibreBalance.exitMass Erdos260.O1FineFibreBalance.Mtot at hid
  exact hid

/-- **Full capstone: App R complete-lap balance straight from the certified atlas
    data.**  Given a common finite carrier `Cset`, injective phase charts `ι a`
    (AQ.5), and the successor compatibility `τ a (ι a u) = ι (a+1) u` (AQ.6 / AL.3)
    over the cyclic phase set `ZMod c`, the interior fibres `Ω°_{λ,a} = ι a (C_λ)`
    satisfy the exact mass-normalized balance
        `c · ExitMass(F°) = b · M_tot°`,
    with measure preservation proved from the explicit per-edge bijections.  This
    is `lem:r-cycle-map-preserves-measure` + `lem:al-complete-lap` (AL.6/AL.7) +
    the equality direction of `lem:r-global-phase-error` (R.1b), machine-checked
    from the geometric supply alone. -/
theorem cycle_charts_balance {C Ω : Type*} [DecidableEq Ω] (c : ℕ) [NeZero c]
    (Cset : Finset C) (ι : ZMod c → C → Ω) (τ : ZMod c → (Ω → Ω)) (E : Finset (ZMod c))
    (hInj : ∀ a : ZMod c, Set.InjOn (ι a) ↑Cset)
    (hcompat : ∀ (a : ZMod c) (u : C), u ∈ Cset → τ a (ι a u) = ι (a + 1) u) :
    c * (∑ a ∈ E, (Cset.image (ι a)).card)
      = E.card * (∑ a : ZMod c, (Cset.image (ι a)).card) := by
  refine cycle_saturation_balance c (fun a => Cset.image (ι a)) τ E ?_
  intro a
  exact cycleMap_bijOn Cset (Cset.image (ι a)) (Cset.image (ι (a + 1)))
    (ι a) (ι (a + 1)) (τ a) rfl rfl (hInj (a + 1)) (fun u hu => hcompat a u hu)

/-! ===========================================================================
    ## Section E.  Packaged O1 residual surface.

    The arithmetic of measure preservation is proved above.  The remaining O1
    supply from the manuscript is exactly the certified atlas data: injective
    charts on the common carrier and successor compatibility between adjacent
    phase fibres.
    =========================================================================== -/

/-- Residual O1 atlas inputs after the finite-bijection and cycle-balance
    arithmetic have been discharged. -/
structure O1CycleChartInputs {C Ω : Type*} [DecidableEq Ω] (c : ℕ) [NeZero c]
    (Cset : Finset C) (chart : ZMod c → C → Ω) (tau : ZMod c → Ω → Ω) where
  hInj : ∀ a : ZMod c, Set.InjOn (chart a) ↑Cset
  hcompat : ∀ (a : ZMod c) (u : C), u ∈ Cset → tau a (chart a u) = chart (a + 1) u

namespace O1CycleChartInputs

/-- Packaged per-edge bijection from the certified cyclic atlas inputs.  This is
the direct `lem:r-cycle-map-preserves-measure` surface for one adjacent phase
edge. -/
theorem edge_bijOn {C Ω : Type*} [DecidableEq Ω] (c : ℕ) [NeZero c]
    (Cset : Finset C) (chart : ZMod c → C → Ω) (tau : ZMod c → Ω → Ω)
    (a : ZMod c) (I : O1CycleChartInputs c Cset chart tau) :
    Set.BijOn (tau a)
      ↑(Cset.image (chart a))
      ↑(Cset.image (chart (a + 1))) :=
  cycleMap_bijOn Cset (Cset.image (chart a)) (Cset.image (chart (a + 1)))
    (chart a) (chart (a + 1)) (tau a) rfl rfl (I.hInj (a + 1))
    (fun u hu => I.hcompat a u hu)

/-- Packaged per-edge equivalence of adjacent fibres from the certified cyclic
atlas inputs.  This is the invertible object behind the per-edge counting
measure preservation statement. -/
noncomputable def edge_equiv {C Ω : Type*} [DecidableEq Ω] (c : ℕ) [NeZero c]
    (Cset : Finset C) (chart : ZMod c → C → Ω) (tau : ZMod c → Ω → Ω)
    (a : ZMod c) (I : O1CycleChartInputs c Cset chart tau) :
    {ω : Ω // ω ∈ (↑(Cset.image (chart a)) : Set Ω)} ≃
      {ω : Ω // ω ∈ (↑(Cset.image (chart (a + 1))) : Set Ω)} :=
  Set.BijOn.equiv (tau a) (edge_bijOn c Cset chart tau a I)

/-- Packaged per-edge cardinality preservation from the certified cyclic atlas
inputs. -/
theorem edge_card_eq {C Ω : Type*} [DecidableEq Ω] (c : ℕ) [NeZero c]
    (Cset : Finset C) (chart : ZMod c → C → Ω) (tau : ZMod c → Ω → Ω)
    (a : ZMod c) (I : O1CycleChartInputs c Cset chart tau) :
    (Cset.image (chart a)).card = (Cset.image (chart (a + 1))).card :=
  bijOn_finset_card_eq (edge_bijOn c Cset chart tau a I)

/-- Packaged per-edge weighted measure preservation from the certified cyclic
atlas inputs. -/
theorem edge_measure_preserving {C Ω M : Type*} [DecidableEq Ω] [AddCommMonoid M]
    (c : ℕ) [NeZero c] (Cset : Finset C) (chart : ZMod c → C → Ω)
    (tau : ZMod c → Ω → Ω) (a : ZMod c) (w : Ω → M)
    (I : O1CycleChartInputs c Cset chart tau) :
    ∑ ω ∈ Cset.image (chart a), w (tau a ω)
      = ∑ ω' ∈ Cset.image (chart (a + 1)), w ω' :=
  bijOn_finset_sum_eq w (edge_bijOn c Cset chart tau a I)

/-- Packaged O1 complete-lap balance from the certified cyclic atlas inputs. -/
theorem balance {C Ω : Type*} [DecidableEq Ω] (c : ℕ) [NeZero c]
    (Cset : Finset C) (chart : ZMod c → C → Ω) (tau : ZMod c → Ω → Ω)
    (E : Finset (ZMod c))
    (I : O1CycleChartInputs c Cset chart tau) :
    c * (∑ a ∈ E, (Cset.image (chart a)).card)
      = E.card * (∑ a : ZMod c, (Cset.image (chart a)).card) :=
  cycle_charts_balance c Cset chart tau E I.hInj I.hcompat

end O1CycleChartInputs

/-- Machine-readable list of O1 components now closed in Lean. -/
def o1MeasurePreservationClosedItems : List String :=
  [ "finite bijections preserve cardinality",
    "finite bijections preserve counting-measure sums",
    "cyclic chart transition is a bijection between adjacent fibres",
    "packaged cyclic atlas inputs give per-edge fibre equivalences",
    "packaged cyclic atlas inputs preserve per-edge weighted counting measure",
    "affine and integer-start relabellings are bijective",
    "per-edge bijections force constant phase mass around ZMod c",
    "complete-lap balance follows from certified cyclic atlas inputs" ]

/-- Machine-readable list of O1 geometric inputs still external to this file. -/
def o1MeasurePreservationOpenItems : List String :=
  [ "charts are injective on the common carrier",
    "successor transition maps each charted carrier point to the next phase chart" ]

theorem o1MeasurePreservationClosedItems_length :
    o1MeasurePreservationClosedItems.length = 8 := by
  rfl

theorem o1MeasurePreservationOpenItems_length :
    o1MeasurePreservationOpenItems.length = 2 := by
  rfl

end Erdos260.O1MeasurePreservation
