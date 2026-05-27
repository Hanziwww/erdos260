import Mathlib
import Erdos260.CNL
import Erdos260.LocalClosure
import Erdos260.Support

/-!
# DensePack support estimates (Appendix K.1)

This file formalises the manuscript shape of K.1 in `proof_v2.tex`:
Lemma K.1.1 (endpoint-disjoint terminal cover), Lemma K.1.2 (DensePack
support cover by `O(L)`-neighbourhoods of a maximal disjoint marker
family), and Corollary K.1.3 (DensePack under positive-density failure).

The combinatorial cover is supplied through a parametric hypothesis;
this file produces the named conclusions in the form used by
Appendix J / L.2.
-/

namespace Erdos260

open Finset

noncomputable section

/-- Abstract dense marker data: a finite collection of endpoint
positions on `[1, 2X]`, each carrying a charged weight on the line. -/
structure DenseMarkerFamily where
  markers : Finset Nat
  weight : Nat -> ℝ
  weight_nonneg : ∀ x ∈ markers, 0 <= weight x

/-- Total charged weight of the marker family. -/
def DenseMarkerFamily.totalWeight (D : DenseMarkerFamily) : ℝ :=
  ∑ x ∈ D.markers, D.weight x

theorem DenseMarkerFamily.totalWeight_nonneg (D : DenseMarkerFamily) :
    0 <= D.totalWeight := by
  unfold totalWeight
  exact Finset.sum_nonneg fun x hx => D.weight_nonneg x hx

theorem DenseMarkerFamily.totalWeight_le_card_mul_max
    {D : DenseMarkerFamily} {M : ℝ}
    (hM : ∀ x ∈ D.markers, D.weight x <= M) :
    D.totalWeight <= (D.markers.card : ℝ) * M := by
  unfold totalWeight
  calc
    (∑ x ∈ D.markers, D.weight x) <= ∑ _x ∈ D.markers, M := by
      exact Finset.sum_le_sum hM
    _ = (D.markers.card : ℝ) * M := by simp [mul_comm]

/--
**Lemma K.1.1 (endpoint-disjoint DensePack cover, manuscript form).**

A maximal disjoint marker family `D` covers all DensePack endpoint
sets after the shell-paid part has been removed.  The cover is
recorded as the hypothesis `hcover`; the manuscript supplies the
greedy disjoint construction.
-/
theorem lemmaK1_1_endpointDisjointDensePackCover
    {D : DenseMarkerFamily} {endpointSet : Finset Nat}
    (hcover : endpointSet ⊆ D.markers) :
    endpointSet.card <= D.markers.card :=
  Finset.card_le_card hcover

/--
**Lemma K.1.2 (DensePack support cover) — quantitative form.**

If every dense-pack point is assigned to a marker (e.g. nearest marker
within `spread` distance) and the fibre of every marker has size at
most `2·spread+1`, then the total number of dense-pack points is
bounded by the marker count times the window size `2·spread+1`.
-/
theorem lemmaK1_2_densePackSupportCover'
    {D : DenseMarkerFamily} {densePackPoints : Finset Nat} {spread : Nat}
    (assign : Nat -> Nat)
    (hassign_into : ∀ x ∈ densePackPoints, assign x ∈ D.markers)
    (hfiber_le :
      ∀ m ∈ D.markers,
        (densePackPoints.filter fun x => assign x = m).card <= 2 * spread + 1) :
    densePackPoints.card <= D.markers.card * (2 * spread + 1) := by
  classical
  -- Bound via `card_le_card_image_mul_of_fiber_card_le` on the image.
  have himg_subset : densePackPoints.image assign ⊆ D.markers := by
    intro y hy
    rcases Finset.mem_image.1 hy with ⟨x, hx, rfl⟩
    exact hassign_into x hx
  have himg_card : (densePackPoints.image assign).card <= D.markers.card :=
    Finset.card_le_card himg_subset
  have hfiber_img :
      ∀ y ∈ densePackPoints.image assign,
        (densePackPoints.filter fun x => assign x = y).card <= 2 * spread + 1 := by
    intro y hy
    exact hfiber_le y (himg_subset hy)
  -- Apply the encoding bound.
  have hkey :
      densePackPoints.card <=
        (densePackPoints.image assign).card * (2 * spread + 1) := by
    refine card_le_card_image_mul_of_fiber_card_le densePackPoints assign ?_
    intro y hy
    exact hfiber_img y hy
  exact hkey.trans (Nat.mul_le_mul_right _ himg_card)

/--
**Corollary K.1.3 (DensePack under positive-density failure).**

Under the failing positive-density hypothesis `hcount : K ≤ c_* X`,
the dense-pack point count is at most `K · (2 spread + 1) ≤ c_* X · (2 spread + 1)`.
The manuscript chooses `c_*` small enough that this is absorbed into
the `ξ s X |I_j|` budget of Appendix H.

We package the conclusion as the inequality `densePackPoints.card ≤
cStar * X * (2 spread + 1)`, supplied as a hypothesis through the
combinatorial K.1.2 cover.
-/
theorem corollaryK1_3_densePackUnderFailure
    {densePackPoints : Finset Nat} {markersCard : Nat} {spread : Nat}
    {cStar X : ℝ}
    (hcover : densePackPoints.card <= markersCard * (2 * spread + 1))
    (hcount : (markersCard : ℝ) <= cStar * X) :
    (densePackPoints.card : ℝ) <= cStar * X * ((2 * spread + 1 : Nat) : ℝ) := by
  calc
    (densePackPoints.card : ℝ) <=
        ((markersCard * (2 * spread + 1) : Nat) : ℝ) := by exact_mod_cast hcover
    _ = (markersCard : ℝ) * ((2 * spread + 1 : Nat) : ℝ) := by push_cast; ring
    _ <= cStar * X * ((2 * spread + 1 : Nat) : ℝ) := by
          have hspread_nonneg : (0 : ℝ) <= ((2 * spread + 1 : Nat) : ℝ) := by
            exact_mod_cast Nat.zero_le _
          exact mul_le_mul_of_nonneg_right hcount hspread_nonneg

end

end Erdos260
