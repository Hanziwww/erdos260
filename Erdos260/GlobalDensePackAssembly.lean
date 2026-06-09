import Mathlib
import Erdos260.GlobalCarryAssembly

/-!
# Global DensePack assembly

This module grounds the DensePack phase one layer further.  Instead of asking
globally for a `DensePackFactoryData` carrying the K.1 cover inequality as a raw
field, it builds that inequality from a marker assignment whose fibres lie in
explicit `O(L)` marker-neighbourhoods.
-/

namespace Erdos260

open Finset

noncomputable section

/--
K.1 marker assignment certificate.

This packages the two local facts used by the DensePack support cover: each
dense-pack point is assigned to an actual marker, and it lies in that marker's
`spread`-neighbourhood.
-/
structure DensePackAssignmentData
    (densePackPoints : Finset Nat) (markers : DenseMarkerFamily)
    (spread : Nat) where
  assign : Nat -> Nat
  into :
    forall x, x ∈ densePackPoints -> assign x ∈ markers.markers
  dist :
    forall x, x ∈ densePackPoints -> Nat.dist x (assign x) <= spread

namespace DensePackAssignmentData

/-- Build the K.1 marker assignment from the manuscript support statement:
every dense-pack point lies in the `spread`-neighbourhood of some selected
marker. -/
noncomputable def ofExists
    {densePackPoints : Finset Nat} {markers : DenseMarkerFamily}
    {spread : Nat}
    (hcover :
      forall x, x ∈ densePackPoints ->
        ∃ m, m ∈ markers.markers ∧ Nat.dist x m <= spread) :
    DensePackAssignmentData densePackPoints markers spread where
  assign := fun x =>
    if hx : x ∈ densePackPoints then Classical.choose (hcover x hx) else 0
  into := by
    intro x hx
    rw [dif_pos hx]
    exact (Classical.choose_spec (hcover x hx)).1
  dist := by
    intro x hx
    rw [dif_pos hx]
    exact (Classical.choose_spec (hcover x hx)).2

/-- K.1.2 per-marker fibre bound from the local assignment certificate. -/
theorem fiber_le
    {densePackPoints : Finset Nat} {markers : DenseMarkerFamily}
    {spread : Nat}
    (cert : DensePackAssignmentData densePackPoints markers spread) :
    forall m, m ∈ markers.markers ->
      (densePackPoints.filter fun x => cert.assign x = m).card <=
        2 * spread + 1 := by
  intro m _hm
  exact
    densePack_fiber_card_le_of_dist
      (densePackPoints := densePackPoints)
      (spread := spread) cert.assign m
      (by
        intro x hx hassign
        have hxdist := cert.dist x hx
        simpa [hassign] using hxdist)

/-- K.1.2 DensePack support cover from the assignment certificate. -/
theorem cover_bound
    {densePackPoints : Finset Nat} {markers : DenseMarkerFamily}
    {spread : Nat}
    (cert : DensePackAssignmentData densePackPoints markers spread) :
    densePackPoints.card <= markers.markers.card * (2 * spread + 1) :=
  lemmaK1_2_densePackSupportCover'
    (D := markers) (densePackPoints := densePackPoints)
    (spread := spread) cert.assign cert.into cert.fiber_le

end DensePackAssignmentData

/--
Proof-v4 aligned DensePack local data.

The `hcover` field of `DensePackFactoryData` is not assumed here.  It is derived
from the manuscript neighbourhood-cover statement: every dense-pack point has a
selected marker within its `spread`-neighbourhood.  The explicit assignment
used by the fibre-counting proof is chosen canonically from that cover.
-/
structure GroundedDensePackLocalData (cStar xi X : Real) where
  densePackPoints : Finset Nat
  markers : DenseMarkerFamily
  spread : Nat
  cover_input :
    forall x, x ∈ densePackPoints ->
      ∃ m, m ∈ markers.markers ∧ Nat.dist x m <= spread
  cStarSmall : Real
  hcount :
    (markers.markers.card : Real) <= cStarSmall * X
  hsmall :
    cStarSmall * X * ((2 * spread + 1 : Nat) : Real) <= cStar * xi * X / 6

/--
K.1 DensePack support leaf before it is packed as grounded DensePack local data.
It keeps the manuscript neighbourhood cover and the two scalar budget
comparisons explicit.
-/
structure DensePackSupportInputData (cStar xi X : Real) where
  densePackPoints : Finset Nat
  markers : DenseMarkerFamily
  spread : Nat
  cover_input :
    forall x, x ∈ densePackPoints ->
      ∃ m, m ∈ markers.markers ∧ Nat.dist x m <= spread
  cStarSmall : Real
  hcount :
    (markers.markers.card : Real) <= cStarSmall * X
  hsmall :
    cStarSmall * X * ((2 * spread + 1 : Nat) : Real) <= cStar * xi * X / 6

/-- K.1 manuscript neighbourhood-cover input for DensePack support. -/
structure DensePackCoverInputData
    (densePackPoints : Finset Nat) (markers : DenseMarkerFamily)
    (spread : Nat) where
  cover_input :
    forall x, x ∈ densePackPoints ->
      ∃ m, m ∈ markers.markers ∧ Nat.dist x m <= spread

/--
K.1 maximal separated marker cover.

This is the finite form of the manuscript's greedy maximal disjoint marker
choice: if a dense-pack point were farther than `spread` from every selected
marker, maximality would force it to have been selected already.  Hence every
dense-pack point lies in a selected marker neighbourhood.
-/
structure DensePackMaximalSeparatedCoverData
    (densePackPoints : Finset Nat) (markers : DenseMarkerFamily)
    (spread : Nat) where
  maximal :
    forall x, x ∈ densePackPoints ->
      (forall m, m ∈ markers.markers -> spread < Nat.dist x m) ->
        x ∈ markers.markers

/-- A finite marker set is `spread`-separated if distinct markers are farther
than `spread` from each other. -/
def DensePackSeparated (points : Finset Nat) (spread : Nat) : Prop :=
  forall a, a ∈ points -> forall b, b ∈ points -> a ≠ b ->
    spread < Nat.dist a b

/-- All `spread`-separated subfamilies of the given finite dense-marker set. -/
def densePackSeparatedSubsets (densePackPoints : Finset Nat) (spread : Nat) :
    Finset (Finset Nat) := by
  classical
  exact densePackPoints.powerset.filter fun points =>
    DensePackSeparated points spread

namespace DensePackSeparated

theorem empty (spread : Nat) :
    DensePackSeparated (∅ : Finset Nat) spread := by
  intro a ha
  simp at ha

end DensePackSeparated

theorem densePackSeparatedSubsets_nonempty
    (densePackPoints : Finset Nat) (spread : Nat) :
    (densePackSeparatedSubsets densePackPoints spread).Nonempty := by
  classical
  refine ⟨∅, ?_⟩
  simp [densePackSeparatedSubsets, DensePackSeparated.empty]

theorem exists_densePackMaximalSeparatedSubset
    (densePackPoints : Finset Nat) (spread : Nat) :
    ∃ points ∈ densePackSeparatedSubsets densePackPoints spread,
      ∀ other ∈ densePackSeparatedSubsets densePackPoints spread,
        other.card <= points.card :=
  Finset.exists_max_image (densePackSeparatedSubsets densePackPoints spread)
    Finset.card (densePackSeparatedSubsets_nonempty densePackPoints spread)

/-- A canonical maximal separated subfamily, chosen by finite cardinal
maximization among separated subsets of `densePackPoints`. -/
noncomputable def densePackMaximalSeparatedMarkers
    (densePackPoints : Finset Nat) (spread : Nat) : DenseMarkerFamily where
  markers :=
    Classical.choose (exists_densePackMaximalSeparatedSubset densePackPoints spread)
  weight := fun _ => 0
  weight_nonneg := by simp

theorem densePackMaximalSeparatedMarkers_mem
    (densePackPoints : Finset Nat) (spread : Nat) :
    (densePackMaximalSeparatedMarkers densePackPoints spread).markers ∈
      densePackSeparatedSubsets densePackPoints spread :=
  (Classical.choose_spec
    (exists_densePackMaximalSeparatedSubset densePackPoints spread)).1

theorem densePackMaximalSeparatedMarkers_subset
    (densePackPoints : Finset Nat) (spread : Nat) :
    (densePackMaximalSeparatedMarkers densePackPoints spread).markers ⊆
      densePackPoints := by
  classical
  have hmem := densePackMaximalSeparatedMarkers_mem densePackPoints spread
  exact (Finset.mem_powerset.mp (Finset.mem_filter.mp hmem).1)

theorem densePackMaximalSeparatedMarkers_separated
    (densePackPoints : Finset Nat) (spread : Nat) :
    DensePackSeparated
      (densePackMaximalSeparatedMarkers densePackPoints spread).markers
      spread := by
  classical
  have hmem := densePackMaximalSeparatedMarkers_mem densePackPoints spread
  exact (Finset.mem_filter.mp hmem).2

theorem densePackMaximalSeparatedMarkers_card_max
    (densePackPoints : Finset Nat) (spread : Nat) :
    ∀ other ∈ densePackSeparatedSubsets densePackPoints spread,
      other.card <=
        (densePackMaximalSeparatedMarkers densePackPoints spread).markers.card :=
  (Classical.choose_spec
    (exists_densePackMaximalSeparatedSubset densePackPoints spread)).2

theorem densePackMaximalSeparatedMarkers_maximal
    (densePackPoints : Finset Nat) (spread : Nat) :
    DensePackMaximalSeparatedCoverData densePackPoints
      (densePackMaximalSeparatedMarkers densePackPoints spread) spread where
  maximal := by
    classical
    intro x hx hfar
    by_contra hxnot
    let markers := (densePackMaximalSeparatedMarkers densePackPoints spread).markers
    have hmarkers_subset : markers ⊆ densePackPoints :=
      densePackMaximalSeparatedMarkers_subset densePackPoints spread
    have hmarkers_sep : DensePackSeparated markers spread :=
      densePackMaximalSeparatedMarkers_separated densePackPoints spread
    have hinsert_subset : insert x markers ⊆ densePackPoints := by
      intro y hy
      rw [Finset.mem_insert] at hy
      rcases hy with rfl | hym
      · exact hx
      · exact hmarkers_subset hym
    have hinsert_sep : DensePackSeparated (insert x markers) spread := by
      intro a ha b hb hne
      rw [Finset.mem_insert] at ha hb
      rcases ha with rfl | ha
      · rcases hb with rfl | hb
        · exact (hne rfl).elim
        · exact hfar b hb
      · rcases hb with rfl | hb
        · simpa [Nat.dist_comm] using hfar a ha
        · exact hmarkers_sep a ha b hb hne
    have hinsert_mem :
        insert x markers ∈ densePackSeparatedSubsets densePackPoints spread := by
      simp [densePackSeparatedSubsets, hinsert_subset, hinsert_sep]
    have hmax :=
      densePackMaximalSeparatedMarkers_card_max densePackPoints spread
        (insert x markers) hinsert_mem
    have hcard_gt : markers.card < (insert x markers).card := by
      simp [markers, hxnot]
    exact (not_lt_of_ge hmax) hcard_gt

namespace DensePackMaximalSeparatedCoverData

/-- Maximal separated marker data gives the K.1 neighbourhood-cover leaf. -/
def toDensePackCoverInputData
    {densePackPoints : Finset Nat} {markers : DenseMarkerFamily}
    {spread : Nat}
    (data :
      DensePackMaximalSeparatedCoverData densePackPoints markers spread) :
    DensePackCoverInputData densePackPoints markers spread where
  cover_input := by
    classical
    intro x hx
    by_cases hxmark : x ∈ markers.markers
    · exact ⟨x, hxmark, by simp⟩
    · by_contra hcover
      have hfar :
          forall m, m ∈ markers.markers -> spread < Nat.dist x m := by
        intro m hm
        have hnotle : ¬ Nat.dist x m <= spread := by
          intro hle
          exact hcover ⟨m, hm, hle⟩
        omega
      exact hxmark (data.maximal x hx hfar)

end DensePackMaximalSeparatedCoverData

/-- K.1.3 marker-count input under the positive-density failure hypothesis. -/
structure DensePackMarkerCountInputData
    (markers : DenseMarkerFamily) (cStarSmall X : Real) where
  hcount :
    (markers.markers.card : Real) <= cStarSmall * X

/--
K.1.3 shell-support packing certificate for selected dense markers.

Each selected marker is assigned a finite set of support hits in the failing
dyadic shell.  The assigned hit sets are disjoint and each has at least
`minHits` elements; hence the marker count times `minHits` is bounded by the
total shell support.
-/
structure DensePackMarkerSupportPackingData
    (shell : FailingDyadicShell) (markers : DenseMarkerFamily)
    (minHits : Nat) where
  supportAt : Nat -> Finset Nat
  support_subset :
    forall m, m ∈ markers.markers ->
      supportAt m ⊆ supportShell shell.d shell.X
  support_pairwiseDisjoint :
    ((markers.markers : Finset Nat) : Set Nat).PairwiseDisjoint supportAt
  support_card :
    forall m, m ∈ markers.markers -> minHits <= (supportAt m).card

/--
K.1.3 marker-count input in shell-packing form.  The manuscript count comes
from the low-density shell failure: each selected dense marker consumes at
least `minHits` shell-support hits, and those consumed hits are disjoint, so the
marker count is bounded by the failing shell count.
-/
structure DensePackFailureMarkerCountInputData
    (shell : FailingDyadicShell) (markers : DenseMarkerFamily)
    (cStarSmall : Real) where
  minHits : Nat
  minHits_pos : 0 < minHits
  packing :
    DensePackMarkerSupportPackingData shell markers minHits
  c0_div_minHits_le :
    shell.c0 / (minHits : Real) <= cStarSmall

/-- I.4.1/K.1 final scalar DensePack smallness comparison. -/
structure DensePackSmallnessInputData
    (cStar xi X cStarSmall : Real) (spread : Nat) where
  hsmall :
    cStarSmall * X * ((2 * spread + 1 : Nat) : Real) <= cStar * xi * X / 6

/--
K.1 DensePack support leaf with cover, marker-count, and scalar smallness kept
as separate proof-v4 inputs.
-/
structure DensePackSeparatedSupportInputData (cStar xi X : Real) where
  densePackPoints : Finset Nat
  markers : DenseMarkerFamily
  spread : Nat
  cStarSmall : Real
  cover :
    DensePackCoverInputData densePackPoints markers spread
  count :
    DensePackMarkerCountInputData markers cStarSmall X
  smallness :
    DensePackSmallnessInputData cStar xi X cStarSmall spread

/--
K.1 DensePack support leaf tied to the actual failing shell.  The cover and
final scalar smallness remain manuscript leaves, while the marker-count scalar
inequality is derived from `DensePackFailureMarkerCountInputData` and
`shell.hfailure`.
-/
structure DensePackShellSeparatedSupportInputData
    (shell : FailingDyadicShell) (cStar xi : Real) where
  densePackPoints : Finset Nat
  markers : DenseMarkerFamily
  spread : Nat
  cStarSmall : Real
  cover :
    DensePackCoverInputData densePackPoints markers spread
  count :
    DensePackFailureMarkerCountInputData shell markers cStarSmall
  smallness :
    DensePackSmallnessInputData cStar xi (shell.X : Real) cStarSmall spread

/--
K.1 DensePack support leaf in canonical failing-shell form.  The marker-count
scale is fixed to `shell.c0 / minHits`, so the only remaining scalar input is
the final DensePack smallness comparison for that canonical value.
-/
structure DensePackCanonicalShellSupportInputData
    (shell : FailingDyadicShell) (cStar xi : Real) where
  densePackPoints : Finset Nat
  markers : DenseMarkerFamily
  spread : Nat
  minHits : Nat
  minHits_pos : 0 < minHits
  cover :
    DensePackCoverInputData densePackPoints markers spread
  packing :
    DensePackMarkerSupportPackingData shell markers minHits
  smallness :
    DensePackSmallnessInputData cStar xi (shell.X : Real)
      (shell.c0 / (minHits : Real)) spread

/-- Proof-v4 DensePack marker-support threshold `floor(ρ_D L)` at the active
dyadic shell. -/
def proofV4DensePackMinHits (shell : FailingDyadicShell) : Nat :=
  Nat.floor
    (manuscriptRhoD * ((Classical.choose shell.hXdyadic : Nat) : Real))

/-- The large-shell carry threshold makes the proof-v4 DensePack hit threshold
positive. -/
theorem proofV4DensePackMinHits_pos_of_carryLarge
    {shell : FailingDyadicShell}
    (hCarryLarge : carryB shell.Q + 25 <= Classical.choose shell.hXdyadic) :
    0 < proofV4DensePackMinHits shell := by
  have hLge4Nat : 4 <= Classical.choose shell.hXdyadic := by
    omega
  have hLge4 : (4 : Real) <=
      ((Classical.choose shell.hXdyadic : Nat) : Real) := by
    exact_mod_cast hLge4Nat
  have hone :
      (1 : Real) <=
        manuscriptRhoD * ((Classical.choose shell.hXdyadic : Nat) : Real) := by
    unfold manuscriptRhoD
    nlinarith
  have hfloor :
      (1 : Nat) <= proofV4DensePackMinHits shell := by
    unfold proofV4DensePackMinHits
    have honeNat :
        ((1 : Nat) : Real) <=
          manuscriptRhoD * ((Classical.choose shell.hXdyadic : Nat) : Real) := by
      simpa using hone
    exact Nat.le_floor honeNat
  omega

/-- Proof-v4 DensePack marker-neighbourhood spread at the active dyadic shell. -/
def proofV4DensePackSpread (shell : FailingDyadicShell) : Nat :=
  Classical.choose shell.hXdyadic + carryB shell.Q + 1

/-- The one-sided shell-support packet attached to a proof-v4 DensePack marker
start.  It is intentionally tied to `supportShell shell.d shell.X`; therefore
any selected marker packet consumes genuine hits from the failing dyadic shell. -/
def proofV4DensePackSupportWindow (shell : FailingDyadicShell) (m : Nat) :
    Finset Nat :=
  (supportShell shell.d shell.X).filter fun n =>
    m <= n ∧ n <= m + proofV4DensePackSpread shell

/-- Canonical finite set of actual proof-v4 DensePack marker starts visible in
the shell: a start is retained only when its support packet contains the
manuscript threshold `floor(rho_D L)` many shell hits.  The ambient finite window
is deliberately larger than the shell; the packet definition itself filters back
to `(X, 2X]`. -/
def proofV4DensePackActualPoints (shell : FailingDyadicShell) : Finset Nat :=
  (Finset.Icc 0 (3 * shell.X + proofV4DensePackSpread shell)).filter fun m =>
    proofV4DensePackMinHits shell <=
      (proofV4DensePackSupportWindow shell m).card

/-- The fixed K.1 marker hit threshold is at least `L / 8` on large shells. -/
theorem proofV4DensePackMinHits_ge_L_div_eight_of_carryLarge
    {shell : FailingDyadicShell}
    (hCarryLarge : carryB shell.Q + 25 <= Classical.choose shell.hXdyadic) :
    ((Classical.choose shell.hXdyadic : Nat) : Real) / 8 <=
      (proofV4DensePackMinHits shell : Real) := by
  let L := Classical.choose shell.hXdyadic
  have hLge4Nat : 4 <= L := by
    omega
  have hLge4 : (4 : Real) <= (L : Real) := by
    exact_mod_cast hLge4Nat
  let a : Real := manuscriptRhoD * (L : Real)
  have hone : (1 : Real) <= a := by
    unfold a manuscriptRhoD
    nlinarith
  have hfloorOne : (1 : Nat) <= Nat.floor a := by
    have honeNat : ((1 : Nat) : Real) <= a := by
      simpa using hone
    exact Nat.le_floor honeNat
  have hfloorOneReal : (1 : Real) <= ((Nat.floor a : Nat) : Real) := by
    exact_mod_cast hfloorOne
  have hlt : a < ((Nat.floor a : Nat) : Real) + 1 := by
    exact Nat.lt_floor_add_one a
  have ha_half : a / 2 <= ((Nat.floor a : Nat) : Real) := by
    nlinarith
  have ha_eq : a / 2 = (L : Real) / 8 := by
    unfold a manuscriptRhoD
    ring
  unfold proofV4DensePackMinHits
  simpa [L, a, ha_eq] using ha_half

/-- The fixed proof-v4 DensePack spread is at most `2L` on large shells. -/
theorem proofV4DensePackSpread_le_two_L_of_carryLarge
    {shell : FailingDyadicShell}
    (hCarryLarge : carryB shell.Q + 25 <= Classical.choose shell.hXdyadic) :
    proofV4DensePackSpread shell <=
      2 * Classical.choose shell.hXdyadic := by
  unfold proofV4DensePackSpread
  omega

/-- The scalar factor `2 * spread + 1` is at most `5L` for the fixed proof-v4
DensePack spread on large shells. -/
theorem proofV4DensePackSpread_factor_le_five_L_of_carryLarge
    {shell : FailingDyadicShell}
    (hCarryLarge : carryB shell.Q + 25 <= Classical.choose shell.hXdyadic) :
    (((2 * proofV4DensePackSpread shell + 1 : Nat) : Real)) <=
      5 * ((Classical.choose shell.hXdyadic : Nat) : Real) := by
  let L := Classical.choose shell.hXdyadic
  have hspread : proofV4DensePackSpread shell <= 2 * L := by
    simpa [L] using proofV4DensePackSpread_le_two_L_of_carryLarge
      (shell := shell) hCarryLarge
  have hLge1Nat : 1 <= L := by
    omega
  have hnat : 2 * proofV4DensePackSpread shell + 1 <= 5 * L := by
    nlinarith
  exact_mod_cast hnat

/-- Pinned constants have more than enough room for the fixed DensePack scalar
smallness comparison. -/
theorem erdos260_densePack_fixed_smallness_budget :
    (5 / 2 : Real) * manuscriptKappa <=
      erdos260Constants.cStar * erdos260Constants.ξ / 6 := by
  unfold erdos260Constants manuscriptKappa manuscriptCdrop manuscriptC1
    manuscriptEps manuscriptCstar manuscriptXi
  norm_num

/-- The fixed proof-v4 DensePack spread makes the final scalar K.1 smallness
automatic from the small-large shell hypotheses. -/
theorem proofV4DensePackSmallness_of_smallLarge
    {shell : FailingDyadicShell}
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (hCarryLarge : carryB shell.Q + 25 <= Classical.choose shell.hXdyadic) :
    DensePackSmallnessInputData erdos260Constants.cStar erdos260Constants.ξ
      (shell.X : Real)
      (shell.c0 / (proofV4DensePackMinHits shell : Real))
      (proofV4DensePackSpread shell) where
  hsmall := by
    let L := Classical.choose shell.hXdyadic
    let m : Real := (proofV4DensePackMinHits shell : Real)
    let S : Real := ((2 * proofV4DensePackSpread shell + 1 : Nat) : Real)
    let C : Real := erdos260Constants.cStar * erdos260Constants.ξ / 6
    have hLge4Nat : 4 <= L := by
      omega
    have hLpos : (0 : Real) < (L : Real) := by
      exact_mod_cast (by omega : 0 < L)
    have hm_lb : (L : Real) / 8 <= m := by
      simpa [L, m] using
        proofV4DensePackMinHits_ge_L_div_eight_of_carryLarge
          (shell := shell) hCarryLarge
    have hm_pos : 0 < m := by
      nlinarith
    have hS_nonneg : 0 <= S := by
      dsimp [S]
      exact_mod_cast Nat.zero_le (2 * proofV4DensePackSpread shell + 1)
    have hS_le : S <= 5 * (L : Real) := by
      simpa [L, S] using
        proofV4DensePackSpread_factor_le_five_L_of_carryLarge
          (shell := shell) hCarryLarge
    have hk_nonneg : 0 <= manuscriptKappa / 16 := by
      exact le_of_lt (div_pos manuscriptKappa_pos (by norm_num))
    have hc0S :
        shell.c0 * S <= (manuscriptKappa / 16) * (5 * (L : Real)) := by
      exact mul_le_mul hc0Small hS_le hS_nonneg hk_nonneg
    have hconst :
        (manuscriptKappa / 16) * (5 * (L : Real)) <= C * ((L : Real) / 8) := by
      have hbudget := erdos260_densePack_fixed_smallness_budget
      dsimp [C] at hbudget ⊢
      nlinarith [hbudget, hLpos]
    have hCm : C * ((L : Real) / 8) <= C * m := by
      have hC_nonneg : 0 <= C := by
        dsimp [C]
        exact le_of_lt
          (div_pos
            (mul_pos erdos260Constants.cStar_pos erdos260Constants.ξ_pos)
            (by norm_num))
      exact mul_le_mul_of_nonneg_left hm_lb hC_nonneg
    have hmul : shell.c0 * S <= C * m :=
      hc0S.trans (hconst.trans hCm)
    have hcoef : shell.c0 / m * S <= C := by
      have hcoef' : shell.c0 * S / m <= C := by
        rw [div_le_iff₀ hm_pos]
        exact hmul
      calc
        shell.c0 / m * S = shell.c0 * S / m := by ring
        _ <= C := hcoef'
    have hX_nonneg : 0 <= (shell.X : Real) := shell.X_nonneg_real
    calc
      (shell.c0 / (proofV4DensePackMinHits shell : Real)) *
          (shell.X : Real) *
          (((2 * proofV4DensePackSpread shell + 1 : Nat) : Real))
          =
            (shell.c0 / m * S) * (shell.X : Real) := by
              simp [m, S]
              ring
      _ <= C * (shell.X : Real) :=
            mul_le_mul_of_nonneg_right hcoef hX_nonneg
      _ = erdos260Constants.cStar * erdos260Constants.ξ *
            (shell.X : Real) / 6 := by
            dsimp [C]
            ring

/--
K.1 DensePack support leaf with the marker hit threshold fixed to the manuscript
choice `floor(ρ_D L)`.  The cover, disjoint shell-support packing, and final
smallness comparison remain the actual K.1 content.
-/
structure DensePackFixedShellSupportInputData
    (shell : FailingDyadicShell) (cStar xi : Real) where
  densePackPoints : Finset Nat
  markers : DenseMarkerFamily
  spread : Nat
  cover :
    DensePackCoverInputData densePackPoints markers spread
  packing :
    DensePackMarkerSupportPackingData shell markers
      (proofV4DensePackMinHits shell)
  smallness :
    DensePackSmallnessInputData cStar xi (shell.X : Real)
      (shell.c0 / (proofV4DensePackMinHits shell : Real)) spread

/--
K.1 DensePack support leaf with both proof-v4 numerical choices fixed.  The
provider now supplies only the actual K.1 cover at spread `L + B(Q) + 1` and
the disjoint support packing at threshold `floor(rho_D L)`; the final scalar
smallness comparison is proved from the small-large shell hypotheses.
-/
structure DensePackProofV4ShellSupportInputData
    (shell : FailingDyadicShell) where
  densePackPoints : Finset Nat
  markers : DenseMarkerFamily
  cover :
    DensePackCoverInputData densePackPoints markers
      (proofV4DensePackSpread shell)
  packing :
    DensePackMarkerSupportPackingData shell markers
      (proofV4DensePackMinHits shell)

/--
K.1 DensePack support leaf in the scalar form actually consumed by the final
K.1.3 estimate.  The manuscript disjoint support packing projects to the
product count `#markers * floor(rho_D L) <= #supportShell`; downstream only
uses this count, the fixed neighbourhood cover, and the closed scalar
smallness arithmetic.
-/
structure DensePackProofV4ShellCardinalityInputData
    (shell : FailingDyadicShell) where
  densePackPoints : Finset Nat
  markers : DenseMarkerFamily
  cover :
    DensePackCoverInputData densePackPoints markers
      (proofV4DensePackSpread shell)
  marker_count_mul_le_shell :
    markers.markers.card * proofV4DensePackMinHits shell <=
      (supportShell shell.d shell.X).card

/--
K.1 DensePack support leaf in the proof-v4 greedy maximal-marker form.

The neighbourhood cover is not exposed as a raw provider field here: it is
recovered from the maximal separated marker principle.  The remaining numerical
content is the scalar shell-support product count used by K.1.3.
-/
structure DensePackProofV4ShellMaximalSeparatedInputData
    (shell : FailingDyadicShell) where
  densePackPoints : Finset Nat
  markers : DenseMarkerFamily
  maximalCover :
    DensePackMaximalSeparatedCoverData densePackPoints markers
      (proofV4DensePackSpread shell)
  marker_count_mul_le_shell :
    markers.markers.card * proofV4DensePackMinHits shell <=
      (supportShell shell.d shell.X).card

/--
K.1 DensePack support leaf after closing the finite greedy maximal-marker
construction.  The canonical selected marker family is the cardinal-maximal
`spread`-separated subfamily of the actual dense marker set; the only remaining
DensePack input is the scalar shell-support count for that selected family.
-/
structure DensePackProofV4ShellGreedyInputData
    (shell : FailingDyadicShell) where
  densePackPoints : Finset Nat
  marker_count_mul_le_shell :
    (densePackMaximalSeparatedMarkers densePackPoints
        (proofV4DensePackSpread shell)).markers.card *
        proofV4DensePackMinHits shell <=
      (supportShell shell.d shell.X).card

namespace DensePackSupportInputData

/-- Convert the K.1 support leaf to the grounded DensePack package. -/
def toGroundedDensePackLocalData
    {cStar xi X : Real}
    (data : DensePackSupportInputData cStar xi X) :
    GroundedDensePackLocalData cStar xi X where
  densePackPoints := data.densePackPoints
  markers := data.markers
  spread := data.spread
  cover_input := data.cover_input
  cStarSmall := data.cStarSmall
  hcount := data.hcount
  hsmall := data.hsmall

end DensePackSupportInputData

namespace DensePackMarkerSupportPackingData

/-- A scalar product count yields the current abstract shell-support packing:
embed `markers x Fin minHits` into the support shell and take one fibre per
marker. -/
noncomputable def ofCardMulLe
    {shell : FailingDyadicShell} {markers : DenseMarkerFamily}
    {minHits : Nat}
    (hcount :
      markers.markers.card * minHits <=
        (supportShell shell.d shell.X).card) :
    DensePackMarkerSupportPackingData shell markers minHits := by
  classical
  let Index := {m : Nat // m ∈ markers.markers} × Fin minHits
  have hcardIndex :
      Fintype.card Index = markers.markers.card * minHits := by
    dsimp [Index]
    rw [Fintype.card_prod, Fintype.card_fin]
    simp
  have hle :
      Fintype.card Index <= (supportShell shell.d shell.X).card := by
    simpa [hcardIndex] using hcount
  have hleSubtype :
      Fintype.card Index <=
        Fintype.card (supportShell shell.d shell.X) := by
    simpa using hle
  let embed : Index ↪ (supportShell shell.d shell.X) :=
    Classical.choice (Function.Embedding.nonempty_of_card_le hleSubtype)
  refine
    { supportAt := fun m =>
        if hm : m ∈ markers.markers then
          Finset.univ.image (fun i : Fin minHits =>
            ((embed (⟨⟨m, hm⟩, i⟩ : Index) :
              supportShell shell.d shell.X) : Nat))
        else ∅
      support_subset := ?_
      support_pairwiseDisjoint := ?_
      support_card := ?_ }
  · intro m hm x hx
    rw [dif_pos hm] at hx
    rcases Finset.mem_image.mp hx with ⟨i, _hi, hix⟩
    rw [← hix]
    exact (embed (⟨⟨m, hm⟩, i⟩ : Index)).property
  · intro m hm n hn hmn
    have hmFin : m ∈ markers.markers := by simpa using hm
    have hnFin : n ∈ markers.markers := by simpa using hn
    change Disjoint
      (if hm : m ∈ markers.markers then
        Finset.univ.image (fun i : Fin minHits =>
          ((embed (⟨⟨m, hm⟩, i⟩ : Index) :
            supportShell shell.d shell.X) : Nat))
       else ∅)
      (if hn : n ∈ markers.markers then
       Finset.univ.image (fun i : Fin minHits =>
          ((embed (⟨⟨n, hn⟩, i⟩ : Index) :
            supportShell shell.d shell.X) : Nat))
       else ∅)
    rw [Finset.disjoint_left]
    intro x hx_m hx_n
    rw [dif_pos hmFin] at hx_m
    rw [dif_pos hnFin] at hx_n
    rcases Finset.mem_image.mp hx_m with ⟨i, _hi, hix⟩
    rcases Finset.mem_image.mp hx_n with ⟨j, _hj, hjx⟩
    have heq :
        (⟨⟨m, hmFin⟩, i⟩ : Index) = (⟨⟨n, hnFin⟩, j⟩ : Index) :=
      embed.injective (Subtype.ext (hix.trans hjx.symm))
    have hmn_eq : m = n := by
      exact congrArg (fun p : Index => (p.1 : Nat)) heq
    exact hmn hmn_eq
  · intro m hm
    rw [dif_pos hm]
    have hinj :
        Set.InjOn
          (fun i : Fin minHits =>
            ((embed (⟨⟨m, hm⟩, i⟩ : Index) :
              supportShell shell.d shell.X) : Nat))
          ((Finset.univ : Finset (Fin minHits)) : Set (Fin minHits)) := by
      intro i _hi j _hj hij
      have heq :
          (⟨⟨m, hm⟩, i⟩ : Index) = (⟨⟨m, hm⟩, j⟩ : Index) :=
        embed.injective (Subtype.ext hij)
      exact congrArg Prod.snd heq
    have hcard_eq :
        (Finset.univ.image
          (fun i : Fin minHits =>
            ((embed (⟨⟨m, hm⟩, i⟩ : Index) :
              supportShell shell.d shell.X) : Nat))).card = minHits := by
      rw [Finset.card_image_of_injOn hinj]
      simp
    exact le_of_eq hcard_eq.symm

/-- The shell-support packing certificate implies the marker-count product
bound used in K.1.3. -/
theorem marker_count_mul_le_shell
    {shell : FailingDyadicShell} {markers : DenseMarkerFamily}
    {minHits : Nat}
    (data : DensePackMarkerSupportPackingData shell markers minHits) :
    markers.markers.card * minHits <=
      (supportShell shell.d shell.X).card := by
  have hminsum :
      markers.markers.card * minHits <=
        Finset.sum markers.markers (fun m => (data.supportAt m).card) := by
    calc
      markers.markers.card * minHits
          = Finset.sum markers.markers (fun _m => minHits) := by
              simp [Finset.sum_const]
      _ <= Finset.sum markers.markers (fun m => (data.supportAt m).card) := by
              exact Finset.sum_le_sum data.support_card
  have hunion_subset :
      markers.markers.biUnion data.supportAt ⊆
        supportShell shell.d shell.X := by
    intro x hx
    rcases mem_biUnion.1 hx with ⟨m, hm, hxmem⟩
    exact data.support_subset m hm hxmem
  have hsum_eq :
      (markers.markers.biUnion data.supportAt).card =
        Finset.sum markers.markers (fun m => (data.supportAt m).card) := by
    exact card_biUnion data.support_pairwiseDisjoint
  have hsum_le_shell :
      Finset.sum markers.markers (fun m => (data.supportAt m).card) <=
        (supportShell shell.d shell.X).card := by
    rw [← hsum_eq]
    exact card_le_card hunion_subset
  exact hminsum.trans hsum_le_shell

end DensePackMarkerSupportPackingData

/--
K.1 greedy DensePack leaf in actual support-packing form.

This is the manuscript-facing strengthening of
`DensePackProofV4ShellGreedyInputData`: instead of providing only the scalar
product count for the canonical maximal separated marker family, it provides
the disjoint support-hit packets whose cardinalities imply that count.
-/
structure DensePackProofV4ShellGreedySupportInputData
    (shell : FailingDyadicShell) where
  densePackPoints : Finset Nat
  packing :
    DensePackMarkerSupportPackingData shell
      (densePackMaximalSeparatedMarkers densePackPoints
        (proofV4DensePackSpread shell))
      (proofV4DensePackMinHits shell)

namespace DensePackProofV4ShellGreedySupportInputData

/-- Forget the actual support-hit packets to the current scalar greedy leaf. -/
noncomputable def toDensePackProofV4ShellGreedyInputData
    {shell : FailingDyadicShell}
    (data : DensePackProofV4ShellGreedySupportInputData shell) :
    DensePackProofV4ShellGreedyInputData shell where
  densePackPoints := data.densePackPoints
  marker_count_mul_le_shell :=
    data.packing.marker_count_mul_le_shell

/-- The canonical actual-support marker set supplies the proof-v4 greedy
support-packet leaf.  This is the finite K.1.5 counting core: selected marker
starts are `spread`-separated, while their one-sided support packets have length
`spread + 1`, so two selected packets cannot share a shell hit. -/
noncomputable def ofActualSupportWindows
    (shell : FailingDyadicShell) :
    DensePackProofV4ShellGreedySupportInputData shell where
  densePackPoints := proofV4DensePackActualPoints shell
  packing := by
    classical
    let points := proofV4DensePackActualPoints shell
    let spread := proofV4DensePackSpread shell
    let markers := densePackMaximalSeparatedMarkers points spread
    refine
      { supportAt := proofV4DensePackSupportWindow shell
        support_subset := ?_
        support_pairwiseDisjoint := ?_
        support_card := ?_ }
    · intro m _hm x hx
      exact (Finset.mem_filter.mp hx).1
    · intro a ha b hb hne
      change Disjoint (proofV4DensePackSupportWindow shell a)
        (proofV4DensePackSupportWindow shell b)
      rw [Finset.disjoint_left]
      intro x hxa hxb
      have hsep :
          spread < Nat.dist a b :=
        densePackMaximalSeparatedMarkers_separated points spread a ha b hb hne
      have hxa_window :
          a <= x ∧ x <= a + spread := by
        simpa [proofV4DensePackSupportWindow, spread] using
          (Finset.mem_filter.mp hxa).2
      have hxb_window :
          b <= x ∧ x <= b + spread := by
        simpa [proofV4DensePackSupportWindow, spread] using
          (Finset.mem_filter.mp hxb).2
      have hdist_le : Nat.dist a b <= spread := by
        unfold Nat.dist
        omega
      exact (not_lt_of_ge hdist_le) hsep
    · intro m hm
      have hsubset :
          markers.markers ⊆ points :=
        densePackMaximalSeparatedMarkers_subset points spread
      have hm_points : m ∈ points := hsubset hm
      simpa [points, proofV4DensePackActualPoints] using
        (Finset.mem_filter.mp hm_points).2

end DensePackProofV4ShellGreedySupportInputData

namespace DensePackProofV4ShellGreedyInputData

/-- The canonical actual-support marker set also supplies the scalar greedy
DensePack leaf consumed by the current strongest phase-core endpoint. -/
noncomputable def ofActualSupportWindows
    (shell : FailingDyadicShell) :
    DensePackProofV4ShellGreedyInputData shell :=
  (DensePackProofV4ShellGreedySupportInputData.ofActualSupportWindows shell)
    |>.toDensePackProofV4ShellGreedyInputData

end DensePackProofV4ShellGreedyInputData

namespace DensePackFailureMarkerCountInputData

/-- Derive the K.1.3 marker-count scalar inequality from shell failure and the
marker-packing count. -/
theorem hcount
    {shell : FailingDyadicShell} {markers : DenseMarkerFamily}
    {cStarSmall : Real}
    (data : DensePackFailureMarkerCountInputData shell markers cStarSmall) :
    (markers.markers.card : Real) <= cStarSmall * (shell.X : Real) := by
  have hpack :
      (markers.markers.card : Real) * (data.minHits : Real) <=
        ((supportShell shell.d shell.X).card : Real) := by
    exact_mod_cast data.packing.marker_count_mul_le_shell
  have hmul_lt :
      (markers.markers.card : Real) * (data.minHits : Real) <
        shell.c0 * (shell.X : Real) :=
    lt_of_le_of_lt hpack shell.hfailure
  have hmin_pos : (0 : Real) < (data.minHits : Real) := by
    exact_mod_cast data.minHits_pos
  have hcard_lt :
      (markers.markers.card : Real) <
        shell.c0 * (shell.X : Real) / (data.minHits : Real) := by
    rw [lt_div_iff₀ hmin_pos]
    exact hmul_lt
  have hscale :
      shell.c0 * (shell.X : Real) / (data.minHits : Real) <=
        cStarSmall * (shell.X : Real) := by
    calc
      shell.c0 * (shell.X : Real) / (data.minHits : Real)
          = (shell.c0 / (data.minHits : Real)) * (shell.X : Real) := by ring
      _ <= cStarSmall * (shell.X : Real) :=
        mul_le_mul_of_nonneg_right data.c0_div_minHits_le shell.X_nonneg_real
  exact le_of_lt (hcard_lt.trans_le hscale)

/-- Convert shell-packing marker-count data to the older scalar K.1.3 count
input. -/
def toMarkerCountInputData
    {shell : FailingDyadicShell} {markers : DenseMarkerFamily}
    {cStarSmall : Real}
    (data : DensePackFailureMarkerCountInputData shell markers cStarSmall) :
    DensePackMarkerCountInputData markers cStarSmall (shell.X : Real) where
  hcount := data.hcount

end DensePackFailureMarkerCountInputData

namespace DensePackSeparatedSupportInputData

/-- Assemble the separated K.1 DensePack support leaf from the manuscript
cover, marker-count, and final scalar smallness subcertificates. -/
def ofClosedK1
    {cStar xi X : Real}
    (densePackPoints : Finset Nat)
    (markers : DenseMarkerFamily)
    (spread : Nat)
    (cStarSmall : Real)
    (cover : DensePackCoverInputData densePackPoints markers spread)
    (count : DensePackMarkerCountInputData markers cStarSmall X)
    (smallness : DensePackSmallnessInputData cStar xi X cStarSmall spread) :
    DensePackSeparatedSupportInputData cStar xi X where
  densePackPoints := densePackPoints
  markers := markers
  spread := spread
  cStarSmall := cStarSmall
  cover := cover
  count := count
  smallness := smallness

/-- Bundle the separated K.1 cover/count/smallness leaves into the existing
DensePack support input. -/
def toDensePackSupportInputData
    {cStar xi X : Real}
    (data : DensePackSeparatedSupportInputData cStar xi X) :
    DensePackSupportInputData cStar xi X where
  densePackPoints := data.densePackPoints
  markers := data.markers
  spread := data.spread
  cover_input := data.cover.cover_input
  cStarSmall := data.cStarSmall
  hcount := data.count.hcount
  hsmall := data.smallness.hsmall

/-- Convert the separated K.1 support leaf to the grounded DensePack package. -/
def toGroundedDensePackLocalData
    {cStar xi X : Real}
    (data : DensePackSeparatedSupportInputData cStar xi X) :
    GroundedDensePackLocalData cStar xi X :=
  data.toDensePackSupportInputData.toGroundedDensePackLocalData

end DensePackSeparatedSupportInputData

namespace DensePackShellSeparatedSupportInputData

/-- Bundle shell-packing K.1 support data into the previous separated
cover/count/smallness leaf, with marker count derived from the failing shell. -/
def toDensePackSeparatedSupportInputData
    {shell : FailingDyadicShell} {cStar xi : Real}
    (data : DensePackShellSeparatedSupportInputData shell cStar xi) :
    DensePackSeparatedSupportInputData cStar xi (shell.X : Real) where
  densePackPoints := data.densePackPoints
  markers := data.markers
  spread := data.spread
  cStarSmall := data.cStarSmall
  cover := data.cover
  count := data.count.toMarkerCountInputData
  smallness := data.smallness

/-- Forget the shell-packing derivation after deriving the scalar count. -/
def toDensePackSupportInputData
    {shell : FailingDyadicShell} {cStar xi : Real}
    (data : DensePackShellSeparatedSupportInputData shell cStar xi) :
    DensePackSupportInputData cStar xi (shell.X : Real) :=
  data.toDensePackSeparatedSupportInputData.toDensePackSupportInputData

/-- Convert the shell-packing K.1 support leaf to the grounded DensePack
package. -/
def toGroundedDensePackLocalData
    {shell : FailingDyadicShell} {cStar xi : Real}
    (data : DensePackShellSeparatedSupportInputData shell cStar xi) :
    GroundedDensePackLocalData cStar xi (shell.X : Real) :=
  data.toDensePackSeparatedSupportInputData.toGroundedDensePackLocalData

end DensePackShellSeparatedSupportInputData

namespace DensePackCanonicalShellSupportInputData

/-- Expand the canonical failing-shell K.1 leaf to the previous shell-separated
form; the marker-count scale domination is now reflexive. -/
def toDensePackShellSeparatedSupportInputData
    {shell : FailingDyadicShell} {cStar xi : Real}
    (data : DensePackCanonicalShellSupportInputData shell cStar xi) :
    DensePackShellSeparatedSupportInputData shell cStar xi where
  densePackPoints := data.densePackPoints
  markers := data.markers
  spread := data.spread
  cStarSmall := shell.c0 / (data.minHits : Real)
  cover := data.cover
  count := {
    minHits := data.minHits
    minHits_pos := data.minHits_pos
    packing := data.packing
    c0_div_minHits_le := le_rfl }
  smallness := data.smallness

/-- Convert the canonical failing-shell K.1 support leaf to grounded DensePack
local data. -/
def toGroundedDensePackLocalData
    {shell : FailingDyadicShell} {cStar xi : Real}
    (data : DensePackCanonicalShellSupportInputData shell cStar xi) :
    GroundedDensePackLocalData cStar xi (shell.X : Real) :=
  data.toDensePackShellSeparatedSupportInputData.toGroundedDensePackLocalData

end DensePackCanonicalShellSupportInputData

namespace DensePackFixedShellSupportInputData

/-- Forget the fixed proof-v4 hit threshold after deriving its positivity from
the closed large-shell inequality. -/
def toDensePackCanonicalShellSupportInputData
    {shell : FailingDyadicShell} {cStar xi : Real}
    (data : DensePackFixedShellSupportInputData shell cStar xi)
    (hCarryLarge : carryB shell.Q + 25 <= Classical.choose shell.hXdyadic) :
    DensePackCanonicalShellSupportInputData shell cStar xi where
  densePackPoints := data.densePackPoints
  markers := data.markers
  spread := data.spread
  minHits := proofV4DensePackMinHits shell
  minHits_pos := proofV4DensePackMinHits_pos_of_carryLarge hCarryLarge
  cover := data.cover
  packing := data.packing
  smallness := data.smallness

/-- Convert the fixed proof-v4 DensePack support leaf to grounded DensePack
local data. -/
def toGroundedDensePackLocalData
    {shell : FailingDyadicShell} {cStar xi : Real}
    (data : DensePackFixedShellSupportInputData shell cStar xi)
    (hCarryLarge : carryB shell.Q + 25 <= Classical.choose shell.hXdyadic) :
    GroundedDensePackLocalData cStar xi (shell.X : Real) :=
  (data.toDensePackCanonicalShellSupportInputData hCarryLarge).toGroundedDensePackLocalData

end DensePackFixedShellSupportInputData

namespace DensePackProofV4ShellSupportInputData

/-- Insert the closed proof-v4 spread and scalar-smallness arithmetic to recover
the previous fixed-threshold DensePack leaf. -/
def toDensePackFixedShellSupportInputData
    {shell : FailingDyadicShell}
    (data : DensePackProofV4ShellSupportInputData shell)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (hCarryLarge : carryB shell.Q + 25 <= Classical.choose shell.hXdyadic) :
    DensePackFixedShellSupportInputData shell erdos260Constants.cStar
      erdos260Constants.ξ where
  densePackPoints := data.densePackPoints
  markers := data.markers
  spread := proofV4DensePackSpread shell
  cover := data.cover
  packing := data.packing
  smallness := proofV4DensePackSmallness_of_smallLarge hc0Small hCarryLarge

/-- Convert the proof-v4 fixed-spread DensePack support leaf to grounded
DensePack local data. -/
def toGroundedDensePackLocalData
    {shell : FailingDyadicShell}
    (data : DensePackProofV4ShellSupportInputData shell)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (hCarryLarge : carryB shell.Q + 25 <= Classical.choose shell.hXdyadic) :
    GroundedDensePackLocalData erdos260Constants.cStar erdos260Constants.ξ
      (shell.X : Real) :=
  (data.toDensePackFixedShellSupportInputData hc0Small hCarryLarge)
    |>.toGroundedDensePackLocalData hCarryLarge

end DensePackProofV4ShellSupportInputData

namespace DensePackProofV4ShellCardinalityInputData

/-- Build the fixed-spread scalar-count K.1 leaf from maximal separated marker
cover data.  This replaces the raw neighbourhood-cover field by the
proof-v4 greedy maximality principle, while leaving the genuine shell-support
count as the remaining packing input. -/
def ofMaximalSeparatedCover
    {shell : FailingDyadicShell}
    (densePackPoints : Finset Nat)
    (markers : DenseMarkerFamily)
    (maximalCover :
      DensePackMaximalSeparatedCoverData densePackPoints markers
        (proofV4DensePackSpread shell))
    (marker_count_mul_le_shell :
      markers.markers.card * proofV4DensePackMinHits shell <=
        (supportShell shell.d shell.X).card) :
    DensePackProofV4ShellCardinalityInputData shell where
  densePackPoints := densePackPoints
  markers := markers
  cover := maximalCover.toDensePackCoverInputData
  marker_count_mul_le_shell := marker_count_mul_le_shell

/-- Recover the older support-packing proof-v4 leaf from the scalar product
count.  This is a compatibility projection for endpoints that still expose the
abstract packing interface. -/
noncomputable def toDensePackProofV4ShellSupportInputData
    {shell : FailingDyadicShell}
    (data : DensePackProofV4ShellCardinalityInputData shell) :
    DensePackProofV4ShellSupportInputData shell where
  densePackPoints := data.densePackPoints
  markers := data.markers
  cover := data.cover
  packing :=
    DensePackMarkerSupportPackingData.ofCardMulLe
      data.marker_count_mul_le_shell

/-- Compatibility projection to the previous fixed-threshold DensePack leaf. -/
noncomputable def toDensePackFixedShellSupportInputData
    {shell : FailingDyadicShell}
    (data : DensePackProofV4ShellCardinalityInputData shell)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (hCarryLarge : carryB shell.Q + 25 <= Classical.choose shell.hXdyadic) :
    DensePackFixedShellSupportInputData shell erdos260Constants.cStar
      erdos260Constants.ξ :=
  data.toDensePackProofV4ShellSupportInputData
    |>.toDensePackFixedShellSupportInputData hc0Small hCarryLarge

/-- The scalar K.1.3 marker count, after the failing-shell density bound, gives
the marker-count estimate required by grounded DensePack. -/
theorem hcount
    {shell : FailingDyadicShell}
    (data : DensePackProofV4ShellCardinalityInputData shell)
    (hCarryLarge : carryB shell.Q + 25 <= Classical.choose shell.hXdyadic) :
    (data.markers.markers.card : Real) <=
      (shell.c0 / (proofV4DensePackMinHits shell : Real)) *
        (shell.X : Real) := by
  let minHits := proofV4DensePackMinHits shell
  have hmin_pos_nat : 0 < minHits := by
    simpa [minHits] using proofV4DensePackMinHits_pos_of_carryLarge
      (shell := shell) hCarryLarge
  have hpack :
      (data.markers.markers.card : Real) * (minHits : Real) <=
        ((supportShell shell.d shell.X).card : Real) := by
    exact_mod_cast data.marker_count_mul_le_shell
  have hmul_lt :
      (data.markers.markers.card : Real) * (minHits : Real) <
        shell.c0 * (shell.X : Real) :=
    lt_of_le_of_lt hpack shell.hfailure
  have hmin_pos : (0 : Real) < (minHits : Real) := by
    exact_mod_cast hmin_pos_nat
  have hcard_lt :
      (data.markers.markers.card : Real) <
        shell.c0 * (shell.X : Real) / (minHits : Real) := by
    rw [lt_div_iff₀ hmin_pos]
    exact hmul_lt
  calc
    (data.markers.markers.card : Real)
        <= shell.c0 * (shell.X : Real) / (minHits : Real) := le_of_lt hcard_lt
    _ = (shell.c0 / (minHits : Real)) * (shell.X : Real) := by ring
    _ = (shell.c0 / (proofV4DensePackMinHits shell : Real)) *
          (shell.X : Real) := by simp [minHits]

/-- Convert the scalar-count proof-v4 DensePack leaf directly to grounded
DensePack local data. -/
def toGroundedDensePackLocalData
    {shell : FailingDyadicShell}
    (data : DensePackProofV4ShellCardinalityInputData shell)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (hCarryLarge : carryB shell.Q + 25 <= Classical.choose shell.hXdyadic) :
    GroundedDensePackLocalData erdos260Constants.cStar erdos260Constants.ξ
      (shell.X : Real) where
  densePackPoints := data.densePackPoints
  markers := data.markers
  spread := proofV4DensePackSpread shell
  cover_input := data.cover.cover_input
  cStarSmall := shell.c0 / (proofV4DensePackMinHits shell : Real)
  hcount := data.hcount hCarryLarge
  hsmall := (proofV4DensePackSmallness_of_smallLarge hc0Small hCarryLarge).hsmall

end DensePackProofV4ShellCardinalityInputData

namespace DensePackProofV4ShellMaximalSeparatedInputData

/-- Forget the greedy maximality certificate after deriving the fixed-spread
neighbourhood cover. -/
def toDensePackProofV4ShellCardinalityInputData
    {shell : FailingDyadicShell}
    (data : DensePackProofV4ShellMaximalSeparatedInputData shell) :
    DensePackProofV4ShellCardinalityInputData shell :=
  DensePackProofV4ShellCardinalityInputData.ofMaximalSeparatedCover
    data.densePackPoints data.markers data.maximalCover
    data.marker_count_mul_le_shell

/-- Compatibility projection to the older fixed-threshold DensePack leaf. -/
noncomputable def toDensePackFixedShellSupportInputData
    {shell : FailingDyadicShell}
    (data : DensePackProofV4ShellMaximalSeparatedInputData shell)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (hCarryLarge : carryB shell.Q + 25 <= Classical.choose shell.hXdyadic) :
    DensePackFixedShellSupportInputData shell erdos260Constants.cStar
      erdos260Constants.ξ :=
  (data.toDensePackProofV4ShellCardinalityInputData).toDensePackFixedShellSupportInputData
    hc0Small hCarryLarge

/-- The scalar K.1.3 marker count projected from the maximal-marker leaf. -/
theorem hcount
    {shell : FailingDyadicShell}
    (data : DensePackProofV4ShellMaximalSeparatedInputData shell)
    (hCarryLarge : carryB shell.Q + 25 <= Classical.choose shell.hXdyadic) :
    (data.markers.markers.card : Real) <=
      (shell.c0 / (proofV4DensePackMinHits shell : Real)) *
        (shell.X : Real) :=
  data.toDensePackProofV4ShellCardinalityInputData.hcount hCarryLarge

/-- Convert the maximal-marker proof-v4 DensePack leaf directly to grounded
DensePack local data. -/
def toGroundedDensePackLocalData
    {shell : FailingDyadicShell}
    (data : DensePackProofV4ShellMaximalSeparatedInputData shell)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (hCarryLarge : carryB shell.Q + 25 <= Classical.choose shell.hXdyadic) :
    GroundedDensePackLocalData erdos260Constants.cStar erdos260Constants.ξ
      (shell.X : Real) :=
  (data.toDensePackProofV4ShellCardinalityInputData).toGroundedDensePackLocalData
    hc0Small hCarryLarge

end DensePackProofV4ShellMaximalSeparatedInputData

namespace DensePackProofV4ShellGreedyInputData

/-- Recover the maximal-separated marker leaf using the finite cardinal-maximal
subfamily construction. -/
noncomputable def toDensePackProofV4ShellMaximalSeparatedInputData
    {shell : FailingDyadicShell}
    (data : DensePackProofV4ShellGreedyInputData shell) :
    DensePackProofV4ShellMaximalSeparatedInputData shell where
  densePackPoints := data.densePackPoints
  markers :=
    densePackMaximalSeparatedMarkers data.densePackPoints
      (proofV4DensePackSpread shell)
  maximalCover :=
    densePackMaximalSeparatedMarkers_maximal data.densePackPoints
      (proofV4DensePackSpread shell)
  marker_count_mul_le_shell := data.marker_count_mul_le_shell

/-- Compatibility projection to the scalar-count leaf. -/
noncomputable def toDensePackProofV4ShellCardinalityInputData
    {shell : FailingDyadicShell}
    (data : DensePackProofV4ShellGreedyInputData shell) :
    DensePackProofV4ShellCardinalityInputData shell :=
  data.toDensePackProofV4ShellMaximalSeparatedInputData
    |>.toDensePackProofV4ShellCardinalityInputData

/-- Compatibility projection to the previous fixed-threshold DensePack leaf. -/
noncomputable def toDensePackFixedShellSupportInputData
    {shell : FailingDyadicShell}
    (data : DensePackProofV4ShellGreedyInputData shell)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (hCarryLarge : carryB shell.Q + 25 <= Classical.choose shell.hXdyadic) :
    DensePackFixedShellSupportInputData shell erdos260Constants.cStar
      erdos260Constants.ξ :=
  data.toDensePackProofV4ShellMaximalSeparatedInputData
    |>.toDensePackFixedShellSupportInputData hc0Small hCarryLarge

/-- Convert the greedy proof-v4 DensePack leaf directly to grounded DensePack
local data. -/
noncomputable def toGroundedDensePackLocalData
    {shell : FailingDyadicShell}
    (data : DensePackProofV4ShellGreedyInputData shell)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (hCarryLarge : carryB shell.Q + 25 <= Classical.choose shell.hXdyadic) :
    GroundedDensePackLocalData erdos260Constants.cStar erdos260Constants.ξ
      (shell.X : Real) :=
  data.toDensePackProofV4ShellMaximalSeparatedInputData
    |>.toGroundedDensePackLocalData hc0Small hCarryLarge

end DensePackProofV4ShellGreedyInputData

namespace DensePackProofV4ShellGreedySupportInputData

/-- Project the support-hit packet leaf to the maximal-separated marker leaf. -/
noncomputable def toDensePackProofV4ShellMaximalSeparatedInputData
    {shell : FailingDyadicShell}
    (data : DensePackProofV4ShellGreedySupportInputData shell) :
    DensePackProofV4ShellMaximalSeparatedInputData shell :=
  data.toDensePackProofV4ShellGreedyInputData
    |>.toDensePackProofV4ShellMaximalSeparatedInputData

/-- Project the support-hit packet leaf to the scalar-count compatibility leaf. -/
noncomputable def toDensePackProofV4ShellCardinalityInputData
    {shell : FailingDyadicShell}
    (data : DensePackProofV4ShellGreedySupportInputData shell) :
    DensePackProofV4ShellCardinalityInputData shell :=
  data.toDensePackProofV4ShellGreedyInputData
    |>.toDensePackProofV4ShellCardinalityInputData

/-- Compatibility projection to the previous fixed-threshold DensePack leaf. -/
noncomputable def toDensePackFixedShellSupportInputData
    {shell : FailingDyadicShell}
    (data : DensePackProofV4ShellGreedySupportInputData shell)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (hCarryLarge : carryB shell.Q + 25 <= Classical.choose shell.hXdyadic) :
    DensePackFixedShellSupportInputData shell erdos260Constants.cStar
      erdos260Constants.ξ :=
  data.toDensePackProofV4ShellGreedyInputData
    |>.toDensePackFixedShellSupportInputData hc0Small hCarryLarge

/-- Convert the support-hit packet leaf directly to grounded DensePack data. -/
noncomputable def toGroundedDensePackLocalData
    {shell : FailingDyadicShell}
    (data : DensePackProofV4ShellGreedySupportInputData shell)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (hCarryLarge : carryB shell.Q + 25 <= Classical.choose shell.hXdyadic) :
    GroundedDensePackLocalData erdos260Constants.cStar erdos260Constants.ξ
      (shell.X : Real) :=
  data.toDensePackProofV4ShellGreedyInputData
    |>.toGroundedDensePackLocalData hc0Small hCarryLarge

end DensePackProofV4ShellGreedySupportInputData

/-- Recover the K.1 support leaf carried by grounded DensePack data. -/
def GroundedDensePackLocalData.toSupportInputData
    {cStar xi X : Real}
    (data : GroundedDensePackLocalData cStar xi X) :
    DensePackSupportInputData cStar xi X where
  densePackPoints := data.densePackPoints
  markers := data.markers
  spread := data.spread
  cover_input := data.cover_input
  cStarSmall := data.cStarSmall
  hcount := data.hcount
  hsmall := data.hsmall

/-- K.1 pointwise marker-neighbourhood cover carried in manuscript form. -/
theorem GroundedDensePackLocalData.cover
    {cStar xi X : Real} (data : GroundedDensePackLocalData cStar xi X) :
    forall x, x ∈ data.densePackPoints ->
      ∃ m, m ∈ data.markers.markers ∧ Nat.dist x m <= data.spread := by
  exact data.cover_input

/-- K.1 explicit assignment certificate used by the fibre-counting proof,
chosen canonically from the neighbourhood-cover statement. -/
def GroundedDensePackLocalData.assignment
    {cStar xi X : Real} (data : GroundedDensePackLocalData cStar xi X) :
    DensePackAssignmentData data.densePackPoints data.markers data.spread :=
  DensePackAssignmentData.ofExists data.cover

/-- The K.1.2 per-marker fibre bound follows from the `O(L)` neighbourhood cover. -/
theorem GroundedDensePackLocalData.fiber_le
    {cStar xi X : Real} (data : GroundedDensePackLocalData cStar xi X) :
    forall m, m ∈ data.markers.markers ->
      (data.densePackPoints.filter fun x => data.assignment.assign x = m).card <=
        2 * data.spread + 1 := by
  exact data.assignment.fiber_le

/-- K.1.2 DensePack support cover derived from marker assignment and fibre bound. -/
theorem GroundedDensePackLocalData.cover_bound
    {cStar xi X : Real} (data : GroundedDensePackLocalData cStar xi X) :
    data.densePackPoints.card <=
      data.markers.markers.card * (2 * data.spread + 1) :=
  lemmaK1_2_densePackSupportCover'
    (D := data.markers) (densePackPoints := data.densePackPoints)
    (spread := data.spread) data.assignment.assign data.assignment.into
    data.fiber_le

/-- K.1.3 DensePack cardinal bound after the failure-count estimate. -/
theorem GroundedDensePackLocalData.card_bound
    {cStar xi X : Real} (data : GroundedDensePackLocalData cStar xi X) :
    (data.densePackPoints.card : Real) <=
      data.cStarSmall * X * ((2 * data.spread + 1 : Nat) : Real) :=
  corollaryK1_3_densePackUnderFailure
    (densePackPoints := data.densePackPoints)
    (markersCard := data.markers.markers.card) (spread := data.spread)
    (cStar := data.cStarSmall) (X := X)
    data.cover_bound data.hcount

/-- Lemma I.4.1 / K.1 final bound for the current grounded DensePack package. -/
theorem GroundedDensePackLocalData.densePack_bound
    {cStar xi X : Real} (data : GroundedDensePackLocalData cStar xi X) :
    (data.densePackPoints.card : Real) <= cStar * xi * X / 6 :=
  data.card_bound.trans data.hsmall

namespace DensePackProofV4ShellCardinalityInputData

/-- Lemma I.4.1/K.1 final bound projected from the scalar-count proof-v4 leaf. -/
theorem densePack_bound
    {shell : FailingDyadicShell}
    (data : DensePackProofV4ShellCardinalityInputData shell)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (hCarryLarge : carryB shell.Q + 25 <= Classical.choose shell.hXdyadic) :
    (data.densePackPoints.card : Real) <=
      erdos260Constants.cStar * erdos260Constants.ξ * (shell.X : Real) / 6 :=
  (data.toGroundedDensePackLocalData hc0Small hCarryLarge).densePack_bound

end DensePackProofV4ShellCardinalityInputData

namespace DensePackProofV4ShellMaximalSeparatedInputData

/-- Lemma I.4.1/K.1 final bound projected from the maximal-marker proof-v4
leaf. -/
theorem densePack_bound
    {shell : FailingDyadicShell}
    (data : DensePackProofV4ShellMaximalSeparatedInputData shell)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (hCarryLarge : carryB shell.Q + 25 <= Classical.choose shell.hXdyadic) :
    (data.densePackPoints.card : Real) <=
      erdos260Constants.cStar * erdos260Constants.ξ * (shell.X : Real) / 6 :=
  (data.toGroundedDensePackLocalData hc0Small hCarryLarge).densePack_bound

end DensePackProofV4ShellMaximalSeparatedInputData

namespace DensePackProofV4ShellGreedyInputData

/-- The scalar K.1.3 marker count projected from the greedy maximal-marker
leaf. -/
theorem hcount
    {shell : FailingDyadicShell}
    (data : DensePackProofV4ShellGreedyInputData shell)
    (hCarryLarge : carryB shell.Q + 25 <= Classical.choose shell.hXdyadic) :
    ((densePackMaximalSeparatedMarkers data.densePackPoints
        (proofV4DensePackSpread shell)).markers.card : Real) <=
      (shell.c0 / (proofV4DensePackMinHits shell : Real)) *
        (shell.X : Real) :=
  data.toDensePackProofV4ShellMaximalSeparatedInputData.hcount hCarryLarge

/-- Lemma I.4.1/K.1 final bound projected from the greedy maximal-marker
proof-v4 leaf. -/
theorem densePack_bound
    {shell : FailingDyadicShell}
    (data : DensePackProofV4ShellGreedyInputData shell)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (hCarryLarge : carryB shell.Q + 25 <= Classical.choose shell.hXdyadic) :
    (data.densePackPoints.card : Real) <=
      erdos260Constants.cStar * erdos260Constants.ξ * (shell.X : Real) / 6 :=
  (data.toGroundedDensePackLocalData hc0Small hCarryLarge).densePack_bound

end DensePackProofV4ShellGreedyInputData

namespace DensePackSupportInputData

/-- Lemma I.4.1/K.1 final bound projected directly from the support leaf. -/
theorem densePack_bound
    {cStar xi X : Real} (data : DensePackSupportInputData cStar xi X) :
    (data.densePackPoints.card : Real) <= cStar * xi * X / 6 :=
  data.toGroundedDensePackLocalData.densePack_bound

end DensePackSupportInputData

namespace DensePackSeparatedSupportInputData

/-- Lemma I.4.1/K.1 final bound projected directly from the separated support
leaf. -/
theorem densePack_bound
    {cStar xi X : Real} (data : DensePackSeparatedSupportInputData cStar xi X) :
    (data.densePackPoints.card : Real) <= cStar * xi * X / 6 :=
  data.toGroundedDensePackLocalData.densePack_bound

end DensePackSeparatedSupportInputData

namespace DensePackShellSeparatedSupportInputData

/-- Lemma I.4.1/K.1 final bound projected directly from the shell-packing
support leaf. -/
theorem densePack_bound
    {shell : FailingDyadicShell} {cStar xi : Real}
    (data : DensePackShellSeparatedSupportInputData shell cStar xi) :
    (data.densePackPoints.card : Real) <= cStar * xi * (shell.X : Real) / 6 :=
  data.toGroundedDensePackLocalData.densePack_bound

end DensePackShellSeparatedSupportInputData

namespace DensePackCanonicalShellSupportInputData

/-- Lemma I.4.1/K.1 final bound projected directly from the canonical
failing-shell support leaf. -/
theorem densePack_bound
    {shell : FailingDyadicShell} {cStar xi : Real}
    (data : DensePackCanonicalShellSupportInputData shell cStar xi) :
    (data.densePackPoints.card : Real) <= cStar * xi * (shell.X : Real) / 6 :=
  data.toGroundedDensePackLocalData.densePack_bound

end DensePackCanonicalShellSupportInputData

/-- Convert marker-assignment DensePack data into the existing factory data. -/
def GroundedDensePackLocalData.toDensePackFactoryData
    {cStar xi X : Real}
    (data : GroundedDensePackLocalData cStar xi X) :
    DensePackFactoryData cStar xi X where
  densePackPoints := data.densePackPoints
  markersCard := data.markers.markers.card
  spread := data.spread
  cStarSmall := data.cStarSmall
  hcover := data.cover_bound
  hcount := data.hcount
  hsmall := data.hsmall

/--
Core global assembly where carry, DensePack, and high-excess use their grounded
proof-v4 interfaces.
-/
structure GlobalAssemblyCoreGroundedCarryDensePackHighExcessInputs where
  carry :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedCarryLocalData shell erdos260Constants.cPr
  chernoff :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        ChernoffPathData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  cnl :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        CNLClusterEncodingData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  densePack :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedDensePackLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  tower :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        TowerTransientFactoryData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  returnPkg :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        ReturnFactoryData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  run :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        RunFactoryData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  highExcess :
    forall (shell : FailingDyadicShell)
      (hcQ : shell.cQ = erdos260Constants.cQ)
      (phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real)),
        GroundedHighExcessLocalData phases ((carry shell hcQ).toCarryData)

/-- Convert the grounded carry/DensePack/high-excess interface to per-failure assembly. -/
def GlobalAssemblyCoreGroundedCarryDensePackHighExcessInputs.toGlobalPerFailureAssembly
    (data : GlobalAssemblyCoreGroundedCarryDensePackHighExcessInputs) :
    GlobalPerFailureAssembly where
  constants := erdos260Constants
  startThreshold := by
    intro Q d hQ hd hnonterm hrational
    exact (canonicalThresholds Q d hQ hd hnonterm hrational).startThreshold
  perFailureAssembly := by
    intro Q d hQ hd hnonterm hrational X hXdyadic _hXge hfailure
    let shell :=
      FailingDyadicShell.ofGlobalConstants erdos260Constants Q d X
        hQ hd hnonterm hrational hXdyadic
        erdos260Constants.c0 erdos260Constants.c0_pos
        manuscriptC0_lt_kappa erdos260Constants.c0_le_cQ hfailure
    have hcQ : shell.cQ = erdos260Constants.cQ := rfl
    let phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
        (X : Real) := {
      chernoff := data.chernoff shell hcQ
      cnl := data.cnl shell hcQ
      tower := data.tower shell hcQ
      densePack := (data.densePack shell hcQ).toDensePackFactoryData
      returnPkg := data.returnPkg shell hcQ
      run := data.run shell hcQ }
    exact
      PerFailureAssemblyData.ofHighExcessCharge phases
        ((data.carry shell hcQ).toCarryData)
        ((data.highExcess shell hcQ phases).toHighExcessChargeData)

/--
Erdos 260 from the core interface whose carry package, DensePack package, and
high-excess package are supplied through current proof-v4 aligned constructors.
-/
theorem erdos260_final_core_grounded_carry_densePack_highExcess
    (data : GlobalAssemblyCoreGroundedCarryDensePackHighExcessInputs) :
    Erdos260Statement :=
  erdos260Statement_of_globalPerFailureAssembly data.toGlobalPerFailureAssembly

end

end Erdos260
