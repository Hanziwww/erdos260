import Erdos260.TowerSDRCore

/-!
# The class-2 SDR / maximal-disjoint selection via Hall's marriage theorem `(K.1.3 selection)`

This module (NEW; it edits no existing file) is the wave-16 closure pass over the **selection half**
of the shared coarea SDR.  After wave-15 (`TowerSDRCore.lean`) the class-2 sub-mass is reduced to the
existence of **disjoint hit-index blocks of size `≥ ρ_D L`** per class-2 start (`Class2IndexSDR`,
`Class2ShellSDR`, `Class2OwnershipPacking`).  Wave-15 left two genuine inputs:

1. **per-start density** — each class-2 start's descent window carries `≥ ⌊ρ_D L⌋` of its own hits
   (the semiperiodic / Fine–Wilf content; **owned by a sibling worker, taken here as a hypothesis**);
2. **maximal-disjoint selection** — the descent windows of distinct selected starts can be made
   pairwise disjoint (the K.1.3 endpoint-disjointness).

This file discharges **(2) from (a union form of) (1) by Hall's marriage theorem**.

## What this module proves — the Hall selection engine, and the sharp characterization

The genuine combinatorial content of "extract pairwise-disjoint blocks of a fixed size `m` from a
family of (possibly overlapping) windows `W k`" is, by Hall's theorem, **exactly** the
*marginal / union condition*

  `(Hallₘ)   ∀ S,  m · #S  ≤  #(⋃_{k ∈ S} W k).`

* `exists_disjoint_blocks_iff_marginal` — **the sharp characterization (an iff)**: pairwise-disjoint
  blocks `B k ⊆ W k`, each of card *exactly* `m`, exist **iff** `(Hallₘ)` holds.  The hard direction
  (`⟸`) is Mathlib's `Finset.all_card_le_biUnion_card_iff_exists_injective` applied to the blown-up
  family `ι × Fin m ∋ (k,i) ↦ W k`; the easy direction (`⟹`) is the disjoint-`biUnion` count.
* `exists_disjoint_blocks_of_marginal`, `exists_disjoint_blocks_of_marginal_on` — the existence side,
  the latter localised to a finite universe `F : Finset ι` (only `S ⊆ F` constrained).

## Inhabiting the wave-15 SDR structures

* `Class2IndexSDR.ofWindowsHall` — from descent windows `W : ℕ → Finset ℕ` (in hit-index space) that
  land in the shell under the injective enumeration `a`, the block size `m` with `ρ_D L ≤ m`, and the
  marginal condition `(Hallₘ)` over the class-2 fibre, Hall selects disjoint hit-index blocks of card
  `m ≥ ρ_D L` — i.e. it **builds a `Class2IndexSDR`**.  Via `toShellSDR` / `ofShellSDR` this feeds
  `Class2ShellSDR`, `Class2OwnershipPacking`, Tower Core 3 and the full closure (wave-15 chain).
* `Class2ShellSDR.ofWindowsHall` — the position-space twin (windows `⊆ supportShell` directly), no
  enumeration needed; **builds a `Class2ShellSDR`**.

## Honest status — AUDIT VERDICT

The SDR (disjoint-block) existence is **closed, as an iff, from the marginal/union condition `(Hallₘ)`
via Hall's theorem** — `exists_disjoint_blocks_iff_marginal`.  This is the *sharp* characterization:
`(Hallₘ)` is both necessary and sufficient.

Per-start density alone — `∀ k, m ≤ #(W k)`, i.e. the `#S = 1` (singleton) case of `(Hallₘ)` — is
**necessary but NOT sufficient**: if two starts share one common window of size `m`, no two disjoint
size-`m` blocks exist (`m · 2 > m = #(⋃)`), so the singleton condition does not give the SDR.  Hence
the genuine residual that Hall reduces the selection to is the **full** marginal condition `(Hallₘ)`,
of which per-start density is the singleton slice.

The manuscript (Lemma K.1.3, .tex §K.1) realises `(Hallₘ)` *structurally*: the first-stop owner
retraction `Φ=(·−r)`, `end=start+r`, makes each shell position have **exactly one** owner
(multiplicity one), so the owner-fibres are disjoint outright and `(Hallₘ)` is automatic — this is the
route already formalised by `sdrOwnerOf` / `ownWindow_disjoint`.  The Hall engine here is the
**complementary** route: it manufactures the multiplicity-one disjoint blocks from the union lower
bound `(Hallₘ)` *without* presupposing the retraction, so a density worker who can only certify the
union/marginal bound (not hand over an owner map) still obtains the SDR.

No `sorry`, `axiom`, `admit`, or `native_decide`.  No degenerate/empty/zero-block shortcut: the block
size is `m ≥ ρ_D L > 0`, the windows live in the real class-2 fibre of the genuine route, and
disjointness is the genuine injective-SDR (multiplicity-one) property delivered by Hall.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 1.  The Hall disjoint-block selection engine (pure Finset, fully proved)

The heart of the selection: pairwise-disjoint blocks of a fixed size `m`, one inside each window
`W k`, exist **iff** the marginal/union condition `∀ S, m·#S ≤ #(⋃_{k∈S} W k)` holds.  This is Hall's
marriage theorem applied to the `m`-fold blow-up `(k, i) ↦ W k` over `ι × Fin m`. -/

/-- **The sharp Hall characterization of disjoint-block selection.**  For a window family
`W : ι → Finset α` and a block size `m`, the following are equivalent:

* there is a family of pairwise-disjoint blocks `B k ⊆ W k`, each of card exactly `m`;
* the marginal / union (Hall) condition `∀ S : Finset ι, m · #S ≤ #(S.biUnion W)` holds.

The forward (necessity) direction is the disjoint-`biUnion` cardinality identity; the backward
(sufficiency) direction is Mathlib's `Finset.all_card_le_biUnion_card_iff_exists_injective` applied to
the blow-up `t : ι × Fin m → Finset α`, `t (k,i) = W k`. -/
theorem exists_disjoint_blocks_iff_marginal {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (W : ι → Finset α) (m : ℕ) :
    (∃ B : ι → Finset α, (∀ k, B k ⊆ W k) ∧ (∀ k, (B k).card = m) ∧
        (∀ j k, j ≠ k → Disjoint (B j) (B k))) ↔
      (∀ S : Finset ι, m * S.card ≤ (S.biUnion W).card) := by
  constructor
  · -- necessity: disjoint size-`m` blocks pack into the union with total card `m·#S`
    rintro ⟨B, hsub, hcard, hdisj⟩ S
    rw [Nat.mul_comm]
    calc S.card * m
          = ∑ _k ∈ S, m := by rw [Finset.sum_const, smul_eq_mul]
      _ = ∑ k ∈ S, (B k).card := Finset.sum_congr rfl (fun k _ => (hcard k).symm)
      _ = (S.biUnion B).card := (Finset.card_biUnion (fun j _ k _ h => hdisj j k h)).symm
      _ ≤ (S.biUnion W).card :=
            Finset.card_le_card (Finset.biUnion_subset.mpr
              (fun k hk => (hsub k).trans (Finset.subset_biUnion_of_mem W hk)))
  · -- sufficiency: Hall on the blow-up `ι × Fin m`
    intro hmarg
    have hcond : ∀ s : Finset (ι × Fin m),
        s.card ≤ (s.biUnion (fun p => W p.1)).card := by
      intro s
      have hssub : s ⊆ (s.image Prod.fst) ×ˢ (Finset.univ : Finset (Fin m)) := by
        intro p hp
        rw [Finset.mem_product]
        exact ⟨Finset.mem_image_of_mem _ hp, Finset.mem_univ _⟩
      have hscard : s.card ≤ (s.image Prod.fst).card * m := by
        calc s.card
              ≤ ((s.image Prod.fst) ×ˢ (Finset.univ : Finset (Fin m))).card :=
                Finset.card_le_card hssub
          _ = (s.image Prod.fst).card * m := by
                rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
      have hbiUnion : s.biUnion (fun p => W p.1) = (s.image Prod.fst).biUnion W := by
        ext x
        simp only [Finset.mem_biUnion, Finset.mem_image]
        constructor
        · rintro ⟨p, hp, hx⟩
          exact ⟨p.1, ⟨p, hp, rfl⟩, hx⟩
        · rintro ⟨k, ⟨p, hp, rfl⟩, hx⟩
          exact ⟨p, hp, hx⟩
      rw [hbiUnion]
      calc s.card
            ≤ (s.image Prod.fst).card * m := hscard
        _ = m * (s.image Prod.fst).card := Nat.mul_comm _ _
        _ ≤ ((s.image Prod.fst).biUnion W).card := hmarg _
    obtain ⟨f, hfinj, hft⟩ :=
      (Finset.all_card_le_biUnion_card_iff_exists_injective (fun p : ι × Fin m => W p.1)).mp hcond
    refine ⟨fun k => (Finset.univ : Finset (Fin m)).image (fun i => f (k, i)), ?_, ?_, ?_⟩
    · intro k x hx
      rw [Finset.mem_image] at hx
      obtain ⟨i, _, rfl⟩ := hx
      exact hft (k, i)
    · intro k
      have hinj : Function.Injective (fun i : Fin m => f (k, i)) :=
        fun i j hij => congrArg Prod.snd (hfinj hij)
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    · intro j k hjk
      rw [Finset.disjoint_left]
      intro x hxj hxk
      rw [Finset.mem_image] at hxj hxk
      obtain ⟨i, _, hi⟩ := hxj
      obtain ⟨i', _, hi'⟩ := hxk
      exact hjk (congrArg Prod.fst (hfinj (hi.trans hi'.symm)))

/-- **Disjoint-block selection (existence side).**  The marginal/union condition produces
pairwise-disjoint blocks `B k ⊆ W k`, each of card exactly `m`. -/
theorem exists_disjoint_blocks_of_marginal {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (W : ι → Finset α) (m : ℕ)
    (hmarg : ∀ S : Finset ι, m * S.card ≤ (S.biUnion W).card) :
    ∃ B : ι → Finset α, (∀ k, B k ⊆ W k) ∧ (∀ k, (B k).card = m) ∧
        (∀ j k, j ≠ k → Disjoint (B j) (B k)) :=
  (exists_disjoint_blocks_iff_marginal W m).mpr hmarg

/-- **Disjoint-block selection over a finite universe `F : Finset ι`.**  Only the windows of
`k ∈ F` matter, and the marginal condition is only required for `S ⊆ F`.  This is the form the
class-2 fibre packing consumes: `F` is the fibre, `W k` the descent window of `k`. -/
theorem exists_disjoint_blocks_of_marginal_on
    {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (F : Finset ι) (W : ι → Finset α) (m : ℕ)
    (hmarg : ∀ S ⊆ F, m * S.card ≤ (S.biUnion W).card) :
    ∃ B : ι → Finset α,
      (∀ k ∈ F, B k ⊆ W k) ∧
      (∀ k ∈ F, (B k).card = m) ∧
      (∀ j ∈ F, ∀ k ∈ F, j ≠ k → Disjoint (B j) (B k)) := by
  -- transport the marginal condition to the fibre subtype and run the engine there
  have hsub_marg : ∀ S : Finset {x // x ∈ F},
      m * S.card ≤ (S.biUnion (fun k : {x // x ∈ F} => W k.val)).card := by
    intro S
    have hbi : S.biUnion (fun k : {x // x ∈ F} => W k.val)
        = (S.image Subtype.val).biUnion W := by
      ext x
      simp only [Finset.mem_biUnion, Finset.mem_image]
      constructor
      · rintro ⟨k, hk, hx⟩
        exact ⟨k.val, ⟨k, hk, rfl⟩, hx⟩
      · rintro ⟨y, ⟨k, hk, rfl⟩, hx⟩
        exact ⟨k, hk, hx⟩
    have hcard : (S.image Subtype.val).card = S.card :=
      Finset.card_image_of_injective S Subtype.val_injective
    have hSF : S.image Subtype.val ⊆ F :=
      Finset.image_subset_iff.mpr (fun x _ => x.2)
    rw [hbi]
    calc m * S.card
          = m * (S.image Subtype.val).card := by rw [hcard]
      _ ≤ ((S.image Subtype.val).biUnion W).card := hmarg _ hSF
  obtain ⟨B', hsub', hcard', hdisj'⟩ :=
    exists_disjoint_blocks_of_marginal (fun k : {x // x ∈ F} => W k.val) m hsub_marg
  refine ⟨fun k => if h : k ∈ F then B' ⟨k, h⟩ else ∅, ?_, ?_, ?_⟩
  · intro k hk
    simp only [dif_pos hk]
    exact hsub' ⟨k, hk⟩
  · intro k hk
    simp only [dif_pos hk]
    exact hcard' ⟨k, hk⟩
  · intro j hj k hk hjk
    simp only [dif_pos hj, dif_pos hk]
    refine hdisj' ⟨j, hj⟩ ⟨k, hk⟩ ?_
    intro hcontra
    exact hjk (congrArg Subtype.val hcontra)

/-! ## 2.  Building the class-2 index-space SDR by Hall selection

Given descent windows in **hit-index** space, the injective enumeration `a`, a block size `m` with
`ρ_D L ≤ m`, the "windows land in the shell" geometry, and the marginal condition over the class-2
fibre, Hall selects disjoint index blocks of card `m ≥ ρ_D L` — a `Class2IndexSDR`. -/

/-- **`Class2IndexSDR` from descent windows + Hall.**  The genuine selection step: from
(possibly overlapping) hit-index descent windows `W k` satisfying the marginal condition
`∀ S ⊆ fibre₂, m · #S ≤ #(⋃ W)`, the per-block floor `ρ_D L ≤ m`, and the shell-landing geometry
`a (W k) ⊆ supportShell`, Hall produces pairwise-disjoint hit-index blocks of card `m`, inhabiting
`Class2IndexSDR`.  The scalar/boundary data (`rhoD … hbdry`) is the wave-15 `L`-free residual,
threaded through unchanged. -/
def Class2IndexSDR.ofWindowsHall (ctx : ActualFailureContext)
    (a : ℕ → ℕ) (hainj : Function.Injective a)
    (rhoD eps L : ℝ) (hrhoD_pos : 0 < rhoD) (hL_pos : 0 < L)
    (hYnn : 0 ≤ ctx.n24CarryData.Y)
    (hcalib : 2 * ctx.n24CarryData.Y ≤ 2 * eps * L)
    (huniform : 2 * (erdos260Constants.c0 * eps) ≤ erdos260Constants.ξ / 6 * rhoD)
    (hbdry : 0 ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2)
    (W : ℕ → Finset ℕ) (m : ℕ) (hmfloor : rhoD * L ≤ (m : ℝ))
    (hlands : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
      ∀ j ∈ W k, a j ∈ supportShell ctx.d ctx.X)
    (hmarg : ∀ S ⊆ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
      m * S.card ≤ (S.biUnion W).card) :
    Class2IndexSDR ctx :=
  let hsel := exists_disjoint_blocks_of_marginal_on
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2) W m hmarg
  { a := a
    hainj := hainj
    rhoD := rhoD
    eps := eps
    L := L
    hrhoD_pos := hrhoD_pos
    hL_pos := hL_pos
    hYnn := hYnn
    hcalib := hcalib
    huniform := huniform
    hbdry := hbdry
    idxOwned := hsel.choose
    hidx_lands := fun k hk j hj => hlands k hk j (hsel.choose_spec.1 k hk hj)
    hidx_disj := fun j hj k hk hjk => hsel.choose_spec.2.2 j hj k hk hjk
    hidx_floor := by
      intro k hk
      rw [hsel.choose_spec.2.1 k hk]
      exact hmfloor }

/-! ## 3.  Building the class-2 shell SDR by Hall selection (position space)

The position-space twin: descent windows already inside `supportShell` (no enumeration needed). -/

/-- **`Class2ShellSDR` from shell windows + Hall.**  From windows `W k ⊆ supportShell` satisfying the
marginal condition and the per-block floor `ρ_D L ≤ m`, Hall produces pairwise-disjoint owned sets of
card `m ≥ ρ_D L` inside the shell, inhabiting `Class2ShellSDR` directly. -/
def Class2ShellSDR.ofWindowsHall (ctx : ActualFailureContext)
    (rhoD eps L : ℝ) (hrhoD_pos : 0 < rhoD) (hL_pos : 0 < L)
    (hYnn : 0 ≤ ctx.n24CarryData.Y)
    (hcalib : 2 * ctx.n24CarryData.Y ≤ 2 * eps * L)
    (huniform : 2 * (erdos260Constants.c0 * eps) ≤ erdos260Constants.ξ / 6 * rhoD)
    (hbdry : 0 ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2)
    (W : ℕ → Finset ℕ) (m : ℕ) (hmfloor : rhoD * L ≤ (m : ℝ))
    (hsubW : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
      W k ⊆ supportShell ctx.d ctx.X)
    (hmarg : ∀ S ⊆ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
      m * S.card ≤ (S.biUnion W).card) :
    Class2ShellSDR ctx :=
  let hsel := exists_disjoint_blocks_of_marginal_on
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2) W m hmarg
  { rhoD := rhoD
    eps := eps
    L := L
    hrhoD_pos := hrhoD_pos
    hL_pos := hL_pos
    hYnn := hYnn
    hcalib := hcalib
    huniform := huniform
    hbdry := hbdry
    owned := hsel.choose
    howned_sub := fun k hk => (hsel.choose_spec.1 k hk).trans (hsubW k hk)
    howned_disj := fun j hj k hk hjk => hsel.choose_spec.2.2 j hj k hk hjk
    howned_floor := by
      intro k hk
      rw [hsel.choose_spec.2.1 k hk]
      exact hmfloor }

/-! ## 4.  Tower Core 3 / closure from the Hall-selected SDR

Both constructors feed the wave-15 chain verbatim: `Class2IndexSDR.htowerSubMass`,
`Class2ShellSDR.htowerSubMass`, `buildTowerRunSeedClosureFromIndexSDR`, … apply to the result. -/

/-- **Tower Core 3 from the Hall-selected index SDR** (`routedClassMassOf … 2 ≤ ξ·X/6`).  Certifies
end-to-end that the Hall selection discharges the class-2 sub-mass through the wave-15 chain. -/
theorem htowerSubMass_of_indexWindowsHall (ctx : ActualFailureContext)
    (a : ℕ → ℕ) (hainj : Function.Injective a)
    (rhoD eps L : ℝ) (hrhoD_pos : 0 < rhoD) (hL_pos : 0 < L)
    (hYnn : 0 ≤ ctx.n24CarryData.Y)
    (hcalib : 2 * ctx.n24CarryData.Y ≤ 2 * eps * L)
    (huniform : 2 * (erdos260Constants.c0 * eps) ≤ erdos260Constants.ξ / 6 * rhoD)
    (hbdry : 0 ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2)
    (W : ℕ → Finset ℕ) (m : ℕ) (hmfloor : rhoD * L ≤ (m : ℝ))
    (hlands : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
      ∀ j ∈ W k, a j ∈ supportShell ctx.d ctx.X)
    (hmarg : ∀ S ⊆ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
      m * S.card ≤ (S.biUnion W).card) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
      ≤ erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  (Class2IndexSDR.ofWindowsHall ctx a hainj rhoD eps L hrhoD_pos hL_pos hYnn hcalib huniform
    hbdry W m hmfloor hlands hmarg).htowerSubMass

/-! ## 5.  Honest residual inventory -/

/-- The precise status of the K.1.3 maximal-disjoint selection after this wave-16 module. -/
def sdrSelectionResiduals : List String :=
  [ "ENGINE (PROVED, SHARP IFF) — exists_disjoint_blocks_iff_marginal: pairwise-disjoint blocks " ++
      "B k ⊆ W k each of card EXACTLY m exist ⟺ the marginal/union (Hall) condition ∀ S, m·#S ≤ " ++
      "#(⋃_{k∈S} W k). Hard direction (⟸) = Mathlib Finset.all_card_le_biUnion_card_iff_exists_" ++
      "injective on the blow-up (k,i)↦W k over ι×Fin m; easy direction (⟹) = disjoint-biUnion count.",
    "EXISTENCE (PROVED) — exists_disjoint_blocks_of_marginal / _of_marginal_on: the marginal " ++
      "condition (the latter only for S ⊆ F, F = the class-2 fibre) yields the disjoint size-m " ++
      "blocks, via the engine and a subtype (↥F) bridge.",
    "INDEX SDR (PROVED) — Class2IndexSDR.ofWindowsHall: from hit-index descent windows W landing in " ++
      "the shell under the injective enumeration a, block size m with ρ_D L ≤ m, and the marginal " ++
      "condition over fibre₂, Hall selects disjoint index blocks of card m ≥ ρ_D L — a Class2IndexSDR.",
    "SHELL SDR (PROVED) — Class2ShellSDR.ofWindowsHall: the position-space twin (windows ⊆ " ++
      "supportShell directly, no enumeration) — a Class2ShellSDR.",
    "CHAIN (PROVED) — htowerSubMass_of_indexWindowsHall: the Hall-selected index SDR discharges " ++
      "Tower Core 3 (routedClassMassOf … 2 ≤ ξ·X/6) through the wave-15 chain " ++
      "(toShellSDR ⟹ ofShellSDR ⟹ Class2OwnershipPacking ⟹ Core 3), and feeds " ++
      "buildTowerRunSeedClosureFromIndexSDR / erdos260_of_minimalResidual.",
    "AUDIT VERDICT — the SDR (disjoint-block) existence is CLOSED, as an IFF, from the marginal/" ++
      "union condition (Hallₘ) via Hall's theorem (exists_disjoint_blocks_iff_marginal): (Hallₘ) is " ++
      "NECESSARY AND SUFFICIENT — the sharp characterization. Per-start density alone (∀ k, m ≤ #(W " ++
      "k) = the singleton #S=1 slice of (Hallₘ)) is NECESSARY but NOT SUFFICIENT (two starts sharing " ++
      "one size-m window admit no two disjoint size-m blocks: m·2 > m). So the genuine residual the " ++
      "selection reduces to is the FULL marginal condition (Hallₘ), not the per-start floor.",
    "MANUSCRIPT ALIGNMENT — Lemma K.1.3 (.tex §K.1) realises (Hallₘ) STRUCTURALLY via the first-stop " ++
      "owner retraction Φ=(·−r), end=start+r (multiplicity one ⟹ owner-fibres disjoint ⟹ (Hallₘ) " ++
      "automatic); that route is the wave-15 sdrOwnerOf / ownWindow_disjoint. This Hall engine is the " ++
      "COMPLEMENTARY route: it manufactures the disjoint blocks from the union lower bound alone, " ++
      "without presupposing the owner map.",
    "NON-DEGENERATE — block size m ≥ ρ_D L > 0 over the real class-2 fibre of the genuine route; " ++
      "disjointness is the genuine injective-SDR (multiplicity-one) property from Hall; no empty / " ++
      "zero-block / vacuous shortcut." ]

theorem sdrSelectionResiduals_nonempty : sdrSelectionResiduals ≠ [] := by
  simp [sdrSelectionResiduals]

/-! ## 6.  Axiom-cleanliness audit -/

#print axioms exists_disjoint_blocks_iff_marginal
#print axioms exists_disjoint_blocks_of_marginal
#print axioms exists_disjoint_blocks_of_marginal_on
#print axioms Class2IndexSDR.ofWindowsHall
#print axioms Class2ShellSDR.ofWindowsHall
#print axioms htowerSubMass_of_indexWindowsHall

end

end Erdos260
