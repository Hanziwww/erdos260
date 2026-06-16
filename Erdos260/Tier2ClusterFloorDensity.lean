/-
  Erdős #260 — Tier-2 surface cap, **Appendix K (K.1.1 cluster-floor + density + Hall)**:
  the FALSIFIABLE counting hearts of the DensePack Hall marginal lower bound (R4) and the
  coarea hit-density floor.

  Manuscript reference (`proof_v4_repaired_core_v71_p2_preprint_hygiene.tex`):
  * Lemma "Hall from disjoint owned endpoint blocks" (`lem:p-hall-from-owned-blocks`,
    lines 8343–8364): disjoint owned blocks `Ω^♯(k) ⊆ Ω(k)` with `#Ω^♯(k) ≥ ρ_D L` give
    the Hall marginal `#⋃_{k∈S} Ω(k) ≥ ρ_D L · #S`.
  * Remark "Owner-fibre interpretation of the endpoint floor" (`rem:k-owner-fibre`,
    lines 5197–5208): the first-stop owner map realizes Hall's marginal inequality by
    construction (every endpoint has exactly one owner — multiplicity one).
  * Lemma K.1.3 "Endpoint-disjoint residual packages" (lines 5161–5195): the terminal
    endpoint sets `Ω(b)` are pairwise disjoint (the SUPPLY of disjointness).
  * Lemma K.1.1 "Coarea-bin equivalence" (lines 5018–5046) and the DensePack support
    estimate (Lemma K.1.4 / Corollary K.1.5): the coarea hit-density `⌊ρ_D L⌋ ≤
    |supportWindow(m)|` at the descent endpoint.
  * §O.6 "DensePack needs a Hall/SDR hypothesis" (`lem:o-densepack-hall`, lines
    8166–8186): the bare singleton bound is insufficient; the correct hypothesis is the
    Hall marginal (R4), equivalently disjoint owned blocks of size `≥ ρ_D L`.

  CERTIFIED here (sorry-free):
  * `hall_marginal_lower_bound_nat` / `hall_marginal_lower_bound` — the R4 Hall marginal
    lower bound `⌊ρ_D L⌋ · #S ≤ #⋃ Ω(k)` (ℕ and ℝ forms), from disjoint owned blocks
    `Ω^♯(k) ⊆ Ω(k)` each of size `≥ ⌊ρ_D L⌋` (the geometric SUPPLY abstracted as
    hypotheses).  This is exactly `lem:p-hall-from-owned-blocks` / `rem:k-owner-fibre`.
  * `coarea_hitDensity_floor_le_supportWindow` — the K.1.1 coarea hit-density
    `⌊ρ_D(q₀) L⌋ ≤ |supportWindow(m)|`, REUSED verbatim from
    `Erdos260.densePackMinHitsFloor_rhoDQ_le_supportWindow` (RhoDQ-calibrated, correct
    for ALL Q).
  * `clusterFloor_hall_marginal_from_coarea` — the composition: the coarea floor SUPPLIES
    the per-owner block floor `⌊ρ_D(q₀) L⌋ ≤ #(supportWindow(m k))`, and with the K.1.3
    endpoint disjointness as hypothesis, the Hall marginal `#S · ⌊ρ_D(q₀) L⌋ ≤ #⋃ Ω(k)`
    (R4) follows for ALL Q.

  REUSE: `Erdos260.densePackMinHitsFloor_rhoDQ_le_supportWindow` (RhoDQCalibrationCore).

  No `sorry`, `axiom`, `admit`, or `native_decide`.
-/
import Erdos260.RhoDQCalibrationCore

namespace Erdos260.Tier2ClusterFloorDensity

open Finset

/-! ## K.  The DensePack Hall marginal lower bound (R4) from disjoint owned blocks.

`lem:p-hall-from-owned-blocks` / `rem:k-owner-fibre`.  For a finite family `S` of
genuine DensePack starts, each owning a block `Ωsharp k ⊆ Ω k` of size at least the
cluster floor `M = ⌊ρ_D L⌋`, with the owned blocks pairwise disjoint (the first-stop
owner multiplicity-one SUPPLY of Lemma K.1.3), the union of full endpoint sets satisfies
Hall's marginal inequality `M · #S ≤ #⋃ Ω(k)`. -/

/-- **Hall marginal lower bound (R4), `ℕ` cluster floor form.**  Disjoint owned blocks
`Ωsharp k ⊆ Ω k` each of card `≥ M` give `#S · M ≤ #⋃_{k∈S} Ω(k)`.

FALSIFIABLE POINT (`hfloor` + `hdisj`): the owned-block cluster floor `M ≤ #Ω^♯(k)` and
their pairwise disjointness — the geometric content of the owner-fibre interpretation of
Lemma K.1.3 / §O.6. -/
theorem hall_marginal_lower_bound_nat
    {ι : Type*} (S : Finset ι) (Ω Ωsharp : ι → Finset ℕ) (M : ℕ)
    (hsub : ∀ k ∈ S, Ωsharp k ⊆ Ω k)
    (hfloor : ∀ k ∈ S, M ≤ (Ωsharp k).card)
    (hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (Ωsharp i) (Ωsharp j)) :
    S.card * M ≤ (S.biUnion Ω).card := by
  have hcard : (S.biUnion Ωsharp).card = ∑ k ∈ S, (Ωsharp k).card :=
    Finset.card_biUnion hdisj
  have hmono : (S.biUnion Ωsharp).card ≤ (S.biUnion Ω).card :=
    Finset.card_le_card (by
      intro x hx
      rw [Finset.mem_biUnion] at hx ⊢
      obtain ⟨i, hi, hxi⟩ := hx
      exact ⟨i, hi, hsub i hi hxi⟩)
  have hsum : S.card * M ≤ ∑ k ∈ S, (Ωsharp k).card := by
    have h := Finset.sum_le_sum hfloor
    simpa [Finset.sum_const, smul_eq_mul] using h
  calc S.card * M ≤ ∑ k ∈ S, (Ωsharp k).card := hsum
    _ = (S.biUnion Ωsharp).card := hcard.symm
    _ ≤ (S.biUnion Ω).card := hmono

/-- **Hall marginal lower bound (R4), real `ρ_D L` form.**  In the manuscript spelling
`#Ω^♯(k) ≥ ρ_D L`: disjoint owned blocks with `(ρDL : ℝ) ≤ #Ω^♯(k)` give the marginal
`ρ_D L · #S ≤ #⋃_{k∈S} Ω(k)`.  This is exactly the displayed inequality of
`lem:p-hall-from-owned-blocks`. -/
theorem hall_marginal_lower_bound
    {ι : Type*} (S : Finset ι) (Ω Ωsharp : ι → Finset ℕ) (ρDL : ℝ)
    (hsub : ∀ k ∈ S, Ωsharp k ⊆ Ω k)
    (hfloor : ∀ k ∈ S, ρDL ≤ ((Ωsharp k).card : ℝ))
    (hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (Ωsharp i) (Ωsharp j)) :
    ρDL * (S.card : ℝ) ≤ ((S.biUnion Ω).card : ℝ) := by
  have hcard : (S.biUnion Ωsharp).card = ∑ k ∈ S, (Ωsharp k).card :=
    Finset.card_biUnion hdisj
  have hmono : (S.biUnion Ωsharp).card ≤ (S.biUnion Ω).card :=
    Finset.card_le_card (by
      intro x hx
      rw [Finset.mem_biUnion] at hx ⊢
      obtain ⟨i, hi, hxi⟩ := hx
      exact ⟨i, hi, hsub i hi hxi⟩)
  have h1 : ∑ k ∈ S, ρDL ≤ ∑ k ∈ S, ((Ωsharp k).card : ℝ) := Finset.sum_le_sum hfloor
  have h2 : ∑ k ∈ S, ρDL = (S.card : ℝ) * ρDL := by rw [Finset.sum_const, nsmul_eq_mul]
  have h3 : ∑ k ∈ S, ((Ωsharp k).card : ℝ) = ((S.biUnion Ωsharp).card : ℝ) := by
    rw [hcard]; push_cast; ring
  have h4 : ((S.biUnion Ωsharp).card : ℝ) ≤ ((S.biUnion Ω).card : ℝ) := by
    exact_mod_cast hmono
  calc ρDL * (S.card : ℝ) = (S.card : ℝ) * ρDL := by ring
    _ = ∑ k ∈ S, ρDL := h2.symm
    _ ≤ ∑ k ∈ S, ((Ωsharp k).card : ℝ) := h1
    _ = ((S.biUnion Ωsharp).card : ℝ) := h3
    _ ≤ ((S.biUnion Ω).card : ℝ) := h4

/-! ## K.1.1.  The coarea hit-density floor `⌊ρ_D(q₀) L⌋ ≤ |supportWindow(m)|`.

REUSED verbatim from `Erdos260.densePackMinHitsFloor_rhoDQ_le_supportWindow`: the
RhoDQ-calibrated coarea hit-density at the descent endpoint, correct for ALL `Q`. -/

/-- **Coarea hit-density floor (K.1.1).**  A shell-contained descent window matching the
residual-center orbit word `dyadicDigit q₀ a` packs `⌊ρ_D(q₀) L⌋ ≤ |supportWindow(m)|`.
This is the per-endpoint SUPPLY of the cluster floor consumed by the Hall marginal. -/
theorem coarea_hitDensity_floor_le_supportWindow
    (shell : FailingDyadicShell) {m L q0 a : ℕ}
    (hlo : shell.X < m)
    (hhi : m + proofV4DensePackSpread shell ≤ 2 * shell.X)
    (hq0 : 1 < q0) (hodd : Odd q0) (hcop : Nat.Coprime a q0)
    (hle : orderOf (2 : ZMod q0) ≤ proofV4DensePackSpread shell + 1)
    (hlen : L + orderOf (2 : ZMod q0) ≤ proofV4DensePackSpread shell + 2)
    (hmatch : WindowMatch shell.d (dyadicDigit q0 a) m (proofV4DensePackSpread shell + 1)) :
    Nat.floor (rhoDQ q0 * (L : ℝ)) ≤ (proofV4DensePackSupportWindow shell m).card :=
  densePackMinHitsFloor_rhoDQ_le_supportWindow shell hlo hhi hq0 hodd hcop hle hlen hmatch

/-! ## K.  Composition: coarea floor SUPPLIES the cluster floor ⇒ Hall marginal (R4).

The coarea hit-density supplies the per-owner block floor `⌊ρ_D(q₀) L⌋ ≤
#(supportWindow(m k))` for every genuine start; with the K.1.3 endpoint disjointness of
the owned support windows as hypothesis, the Hall marginal `#S · ⌊ρ_D(q₀) L⌋ ≤ #⋃ Ω(k)`
(R4) follows — for ALL `Q`. -/

/-- **Cluster-floor Hall marginal from the coarea hit-density (R4 for ALL Q).**  For a
finite family `S` of genuine DensePack starts (common odd part `q₀ > 1`, common length
`L`, per-start marker `m k` and residue numerator `a k`), the coarea hit-density of
Lemma K.1.1 supplies the cluster floor `⌊ρ_D(q₀) L⌋ ≤ #(supportWindow(m k))` for each
start.  With the support windows pairwise disjoint (K.1.3 endpoint disjointness) and
each contained in its full endpoint set `Ω k`, the Hall marginal lower bound holds:
`#S · ⌊ρ_D(q₀) L⌋ ≤ #⋃_{k∈S} Ω(k)`. -/
theorem clusterFloor_hall_marginal_from_coarea
    (shell : FailingDyadicShell) (S : Finset ℕ)
    (L q0 : ℕ) (a m : ℕ → ℕ) (Ω : ℕ → Finset ℕ)
    (hq0 : 1 < q0) (hodd : Odd q0)
    (hle : orderOf (2 : ZMod q0) ≤ proofV4DensePackSpread shell + 1)
    (hlen : L + orderOf (2 : ZMod q0) ≤ proofV4DensePackSpread shell + 2)
    (hlo : ∀ k ∈ S, shell.X < m k)
    (hhi : ∀ k ∈ S, m k + proofV4DensePackSpread shell ≤ 2 * shell.X)
    (hcop : ∀ k ∈ S, Nat.Coprime (a k) q0)
    (hmatch : ∀ k ∈ S,
        WindowMatch shell.d (dyadicDigit q0 (a k)) (m k) (proofV4DensePackSpread shell + 1))
    (hsub : ∀ k ∈ S, proofV4DensePackSupportWindow shell (m k) ⊆ Ω k)
    (hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
        Disjoint (proofV4DensePackSupportWindow shell (m i))
          (proofV4DensePackSupportWindow shell (m j))) :
    S.card * Nat.floor (rhoDQ q0 * (L : ℝ)) ≤ (S.biUnion Ω).card :=
  hall_marginal_lower_bound_nat S Ω (fun k => proofV4DensePackSupportWindow shell (m k))
    (Nat.floor (rhoDQ q0 * (L : ℝ))) hsub
    (fun k hk => coarea_hitDensity_floor_le_supportWindow shell (hlo k hk) (hhi k hk)
      hq0 hodd (hcop k hk) hle hlen (hmatch k hk))
    hdisj

end Erdos260.Tier2ClusterFloorDensity
