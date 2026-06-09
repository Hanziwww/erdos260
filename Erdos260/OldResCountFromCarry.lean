import Mathlib
import Erdos260.ChargeBridgeReduction
import Erdos260.CarryDataFactory
import Erdos260.HitSequence
import Erdos260.Support

/-!
# Old-residual endpoint count from carry failure data (Lemma L.6.5, eq. L.22)

This file derives, **from the carry data of a failing dyadic shell**, the
density-sensitive input of the old-residual estimate Lemma L.6.5 that is already
formalised abstractly in `Erdos260.ChargeBridgeReduction`
(`oldRes_le_of_density` / `oldRes_le_lowDensityWindow`).

It mirrors the DensePack *count-from-failure* pattern of
`Erdos260.DensePackChargeBound` (`corollaryK1_3_densePackUnderFailure`): the
smallness of the old-residual mass is carried entirely by an **endpoint count**
that is bounded by the positive-density failure hypothesis, never by a per-fibre
constant.

## What is genuinely proved here (the failure hypothesis applied to the support)

The deep, genuinely-derivable content is the manuscript's eq. **L.22**:
\[
  \#\{k : a_k\in[X-CrL,\,2X+CrL]\}\;\le\;c_*X+O(rL)=c_*X+o(X).
\]

For a `HitSequence d a` (the strictly increasing enumeration of the support of
`d`), the map `k ↦ a k` is a bijection from the endpoint index set
`{k : a_k ∈ window}` onto the support positions inside `window`.  Hence the
*endpoint index count* equals the number of support hits in the window.  For the
enlarged dyadic window `[X − CrL, 2X + CrL]` this support count splits as

* the middle band `(X, 2X]`, whose hit set **is exactly** `supportShell d X` — the
  set whose cardinality the failure hypothesis `FailingDyadicShell.hfailure`
  bounds by `c₀·X`; and
* two collars `[X − CrL, X]` and `(2X, 2X + CrL]`, each of length `O(rL)`,
  contributing at most `2·CrL + 1` extra positions **without any density input**.

So `#{k : a_k ∈ [X − CrL, 2X + CrL]} ≤ (supportShell d X).card + (2·CrL + 1)
< c₀·X + (2·CrL + 1)` — eq. L.22, with collar `2·CrL + 1 = O(rL) = o(X)`.  Each
step (`windowHitIndices_image`, `windowHitIndices_card`,
`supportFilterIcc_collar_card_le`, `endpointHitIndices_card_lt_failure`) is fully
proved with no `sorry`/`axiom`.

## What remains a faithful analytic primitive

The per-retained-index bounds of Lemma L.6.5 are *not* derivable from the carry
data and are supplied as hypotheses, exactly as in the abstract
`oldRes_le_of_density`:

* the residual multiplier `Y_res ≤ Cres·Y` (eq. L.20, K.1.2-consistent, **linear
  in the active floor `Y`**, no false `O_Q(1)` bound); and
* the per-index endpoint/carry support `≤ Csupp·Ij` (eq. L.21, K.1.3A
  endpoint-disjointness),

packaged as `hpoint : oldResAt k ≤ (Cres·Y)·(Csupp·Ij)` and `hbound_nonneg`.  The
identification of the retained terminal indices as a subset of the enlarged
window (`hKsub : K ⊆ windowHitIndices …`) is the manuscript sentence "the
terminal indices lie in the enlarged dyadic window" (eq. L.22).

## Capstone

`oldRes_le_of_carryFailure` feeds the genuinely-derived endpoint count into the
existing `oldRes_le_lowDensityWindow` to obtain, from the carry failure data
alone (plus the L.20/L.21 primitives),
\[
  \OldRes=\sum_{k\in K}\mathrm{oldResAt}\,k
  \;\le\; c_*\,X\cdot\bigl((C_{\rm res}Y)(C_{\rm supp}I_j)\bigr)
        + \mathrm{collar}\cdot\bigl((C_{\rm res}Y)(C_{\rm supp}I_j)\bigr),
\]
the L.17 split into the genuinely-small main term `c_*·X·bound` and the
`o(sX|I_j|)` collar term, exactly the v5 recurrence I.11' specialised by
Lemma L.6.5.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## Index ≤ value for a hit enumeration -/

/-- For a `HitSequence d a`, the index never exceeds its hit value: `k ≤ a k`.
This is the unbounded-growth fact of a strictly increasing `ℕ → ℕ` enumeration,
and is what makes the endpoint index set finite (contained in `range (hi+1)`). -/
theorem hitSeq_index_le {d a : Nat → Nat} (hseq : HitSequence d a) (k : Nat) :
    k ≤ a k := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have hstep : a n < a (n + 1) := hseq.strict (Nat.lt_succ_self n)
    omega

/-! ## The endpoint hit-index set in a window -/

/-- The set of hit indices `k` whose hit `a k` lands in the closed window
`[lo, hi]`, i.e. the manuscript's `{k : a_k ∈ [lo, hi]}`.  It is realised as a
`Finset` by filtering over `range (hi + 1)`, which is harmless since `k ≤ a k`
forces `a k ≤ hi → k ≤ hi`. -/
def windowHitIndices (a : Nat → Nat) (lo hi : Nat) : Finset Nat :=
  (Finset.range (hi + 1)).filter (fun k => lo ≤ a k ∧ a k ≤ hi)

theorem mem_windowHitIndices {a : Nat → Nat} {lo hi k : Nat} :
    k ∈ windowHitIndices a lo hi ↔ k ≤ hi ∧ lo ≤ a k ∧ a k ≤ hi := by
  unfold windowHitIndices
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hk, hlo, hhi⟩
    exact ⟨by omega, hlo, hhi⟩
  · rintro ⟨hk, hlo, hhi⟩
    exact ⟨by omega, hlo, hhi⟩

/-- **Endpoint index ↔ support position (faithful bijection core).**

For a `HitSequence d a`, the strictly increasing enumeration `a` maps the
endpoint index set `{k : a_k ∈ [lo, hi]}` bijectively onto the support positions
`{n ∈ [lo, hi] : d n = 1}`.  This identity is the reason the endpoint *index*
count equals the support *position* count in the window. -/
theorem windowHitIndices_image {d a : Nat → Nat} (hseq : HitSequence d a)
    (lo hi : Nat) :
    (windowHitIndices a lo hi).image a
      = (Finset.Icc lo hi).filter (fun n => d n = 1) := by
  ext n
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [mem_windowHitIndices] at hk
    exact ⟨⟨hk.2.1, hk.2.2⟩, hseq.hit k⟩
  · rintro ⟨⟨hlo, hhi⟩, hd1⟩
    obtain ⟨k, rfl⟩ := hseq.complete n hd1
    refine ⟨k, ?_, rfl⟩
    rw [mem_windowHitIndices]
    exact ⟨le_trans (hitSeq_index_le hseq k) hhi, hlo, hhi⟩

/-- **Endpoint index count = support position count in the window.**  A direct
consequence of the bijection `windowHitIndices_image` and the injectivity of the
strictly increasing `a`. -/
theorem windowHitIndices_card {d a : Nat → Nat} (hseq : HitSequence d a)
    (lo hi : Nat) :
    (windowHitIndices a lo hi).card
      = ((Finset.Icc lo hi).filter (fun n => d n = 1)).card := by
  have hinj : Set.InjOn a ↑(windowHitIndices a lo hi) :=
    fun x _ y _ hxy => hseq.strict.injective hxy
  have h := Finset.card_image_of_injOn hinj
  rw [windowHitIndices_image hseq lo hi] at h
  exact h.symm

/-! ## Collar decomposition of the support count in the enlarged window -/

/-- **Collar decomposition (eq. L.22 support split) — fully proved.**

The number of support positions in the enlarged dyadic window
`[X − cW, 2X + cW]` is bounded by the shell count plus the two collars:
\[
  \#\{n\in[X-cW,2X+cW] : d_n = 1\}\;\le\;|\,\mathrm{supportShell}\;d\;X\,|+(2cW+1).
\]
The middle band `(X, 2X]` filtered by `d · = 1` **is** `supportShell d X`
(`mem_supportShell`); the lower collar `[X − cW, X]` has `≤ cW + 1` positions and
the upper collar `(2X, 2X + cW]` has `≤ cW` positions, **independently of any
density hypothesis** — this is the manuscript's "the two added collars have
length `O(rL) = O(L²) = o(X)`". -/
theorem supportFilterIcc_collar_card_le (d : Nat → Nat) (X cW : Nat) :
    ((Finset.Icc (X - cW) (2 * X + cW)).filter (fun n => d n = 1)).card
      ≤ (supportShell d X).card + (2 * cW + 1) := by
  classical
  have hsub : Finset.Icc (X - cW) (2 * X + cW) ⊆
      (Finset.Icc (X - cW) X) ∪ (Finset.Ioc X (2 * X))
        ∪ (Finset.Ioc (2 * X) (2 * X + cW)) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hmidcard :
      ((Finset.Ioc X (2 * X)).filter (fun n => d n = 1)).card
        = (supportShell d X).card := by
    congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc, mem_supportShell]
    tauto
  have hlo : ((Finset.Icc (X - cW) X).filter (fun n => d n = 1)).card ≤ cW + 1 := by
    refine le_trans (Finset.card_filter_le _ _) ?_
    rw [Nat.card_Icc]; omega
  have hhi :
      ((Finset.Ioc (2 * X) (2 * X + cW)).filter (fun n => d n = 1)).card ≤ cW := by
    refine le_trans (Finset.card_filter_le _ _) ?_
    rw [Nat.card_Ioc]; omega
  calc ((Finset.Icc (X - cW) (2 * X + cW)).filter (fun n => d n = 1)).card
      ≤ (((Finset.Icc (X - cW) X) ∪ (Finset.Ioc X (2 * X))
            ∪ (Finset.Ioc (2 * X) (2 * X + cW))).filter (fun n => d n = 1)).card :=
        Finset.card_le_card (Finset.filter_subset_filter (fun n => d n = 1) hsub)
    _ ≤ (supportShell d X).card + (2 * cW + 1) := by
        rw [Finset.filter_union, Finset.filter_union]
        refine le_trans (Finset.card_union_le _ _) ?_
        refine le_trans (Nat.add_le_add_right (Finset.card_union_le _ _) _) ?_
        rw [hmidcard]
        omega

/-! ## L.22 endpoint count from the failure hypothesis -/

/-- **Endpoint count = shell + collar (Nat form).**  Combining the bijection
`windowHitIndices_card` with the collar decomposition
`supportFilterIcc_collar_card_le`. -/
theorem endpointHitIndices_card_le {d a : Nat → Nat} (hseq : HitSequence d a)
    (X cW : Nat) :
    (windowHitIndices a (X - cW) (2 * X + cW)).card
      ≤ (supportShell d X).card + (2 * cW + 1) := by
  rw [windowHitIndices_card hseq (X - cW) (2 * X + cW)]
  exact supportFilterIcc_collar_card_le d X cW

/-- **Lemma L.6.5, eq. L.22 — the failure hypothesis applied to the support set.**

For a failing dyadic shell and any hit enumeration `a` of its support, the
endpoint index count in the enlarged dyadic window `[X − cW, 2X + cW]` obeys
\[
  \#\{k : a_k\in[X-cW,2X+cW]\}\;<\;c_0\,X+(2cW+1),
\]
where `c₀·X` is the failure bound `FailingDyadicShell.hfailure` on the shell
count and `2cW + 1` is the collar enlargement `O(rL) = o(X)`.  This is the L.22
density-sensitive endpoint estimate, derived genuinely from the carry failure
data (no per-fibre constant bound). -/
theorem endpointHitIndices_card_lt_failure
    (shell : FailingDyadicShell) {a : Nat → Nat} (hseq : HitSequence shell.d a)
    (cW : Nat) :
    ((windowHitIndices a (shell.X - cW) (2 * shell.X + cW)).card : ℝ)
      < shell.c0 * (shell.X : ℝ) + (2 * (cW : ℝ) + 1) := by
  have hnat := endpointHitIndices_card_le hseq shell.X cW
  have hcast :
      ((windowHitIndices a (shell.X - cW) (2 * shell.X + cW)).card : ℝ)
        ≤ ((supportShell shell.d shell.X).card : ℝ) + (2 * (cW : ℝ) + 1) := by
    have h := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at h
    linarith
  have hfail := shell.hfailure
  linarith

/-- **Retained-index count bound (L.22 for a retained subfamily).**

The manuscript's retained terminal indices `K` form a *subset* of the enlarged
window index set (the L.22 sentence "the terminal indices lie in the enlarged
dyadic window").  Their count is therefore controlled by the failure bound:
`|K| ≤ c₀·X + (2cW + 1)`.  This is exactly the `hcard` input demanded by
`oldRes_le_lowDensityWindow`. -/
theorem retainedIndices_card_le_failure
    (shell : FailingDyadicShell) {a : Nat → Nat} (hseq : HitSequence shell.d a)
    (cW : Nat) {K : Finset ℕ}
    (hKsub : K ⊆ windowHitIndices a (shell.X - cW) (2 * shell.X + cW)) :
    (K.card : ℝ) ≤ shell.c0 * (shell.X : ℝ) + (2 * (cW : ℝ) + 1) := by
  have hcard_le :
      (K.card : ℝ)
        ≤ ((windowHitIndices a (shell.X - cW) (2 * shell.X + cW)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hKsub
  have hwin := endpointHitIndices_card_lt_failure shell hseq cW
  linarith

/-! ## Capstone: L.6.5 conclusion from the carry failure data -/

/-- **Lemma L.6.5 from the carry failure data (capstone).**

Given the carry data of a failing dyadic shell, the genuinely-derived L.22
endpoint count (`retainedIndices_card_le_failure`) feeds the existing abstract
estimate `oldRes_le_lowDensityWindow` (`Erdos260.ChargeBridgeReduction`).  The
retained terminal indices `K` lie in the enlarged window (`hKsub`, eq. L.22), the
per-index residual contribution is the multiplier × support bound
`(Cres·Y)·(Csupp·Ij)` (eqs. L.20/L.21, faithful analytic primitives `hpoint` /
`hbound_nonneg`), and the conclusion is the L.17 product bound
\[
  \sum_{k\in K}\mathrm{oldResAt}\,k
    \;\le\; c_0\,X\cdot\bigl((C_{\rm res}Y)(C_{\rm supp}I_j)\bigr)
          + (2cW+1)\cdot\bigl((C_{\rm res}Y)(C_{\rm supp}I_j)\bigr),
\]
the genuinely-small main term `c_*·X·bound` plus the `o(sX|I_j|)` collar term.
The **smallness is carried entirely by the failure-bounded endpoint count**,
exactly as for DensePack in `Erdos260.DensePackChargeBound`. -/
theorem oldRes_le_of_carryFailure
    {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr) (cW : Nat)
    {K : Finset ℕ} {oldResAt : ℕ → ℝ} {Cres Y Csupp Ij : ℝ}
    (hKsub : K ⊆ windowHitIndices carryData.a (shell.X - cW) (2 * shell.X + cW))
    (hpoint : ∀ k ∈ K, oldResAt k ≤ (Cres * Y) * (Csupp * Ij))
    (hbound_nonneg : 0 ≤ (Cres * Y) * (Csupp * Ij)) :
    (∑ k ∈ K, oldResAt k)
      ≤ shell.c0 * (shell.X : ℝ) * ((Cres * Y) * (Csupp * Ij))
        + (2 * (cW : ℝ) + 1) * ((Cres * Y) * (Csupp * Ij)) := by
  have hcard := retainedIndices_card_le_failure shell carryData.carry.hits cW hKsub
  exact oldRes_le_lowDensityWindow hpoint hbound_nonneg hcard

/-- **L.6.5 capstone with the collar realised as the manuscript `C·r·L` band.**

Specialises `oldRes_le_of_carryFailure` to the manuscript collar width
`cW = Ccollar · r · L` of the enlarged window `[X − CrL, 2X + CrL]`, where
`r = carryData.r` is the descent order and `L = carryData.L = log₂ X`.  The
resulting collar term `2·CrL + 1 = O(rL) = o(X)` is the manuscript's harmless
boundary band; the main term `c₀·X·bound` is the genuinely-small
`C_Q·c_*·sX|I_j|`. -/
theorem oldRes_le_of_carryFailure_rL
    {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr) (Ccollar : Nat)
    {K : Finset ℕ} {oldResAt : ℕ → ℝ} {Cres Y Csupp Ij : ℝ}
    (hKsub : K ⊆ windowHitIndices carryData.a
        (shell.X - Ccollar * carryData.r * carryData.L)
        (2 * shell.X + Ccollar * carryData.r * carryData.L))
    (hpoint : ∀ k ∈ K, oldResAt k ≤ (Cres * Y) * (Csupp * Ij))
    (hbound_nonneg : 0 ≤ (Cres * Y) * (Csupp * Ij)) :
    (∑ k ∈ K, oldResAt k)
      ≤ shell.c0 * (shell.X : ℝ) * ((Cres * Y) * (Csupp * Ij))
        + (2 * ((Ccollar * carryData.r * carryData.L : ℕ) : ℝ) + 1)
            * ((Cres * Y) * (Csupp * Ij)) :=
  oldRes_le_of_carryFailure carryData (Ccollar * carryData.r * carryData.L)
    hKsub hpoint hbound_nonneg

end

end Erdos260
