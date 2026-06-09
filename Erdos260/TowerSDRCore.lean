import Erdos260.TowerK13PackingExistenceCore

/-!
# Lemma K.1.3 — the class-2 system of distinct representatives `(K.1.3★)`

This module (NEW; it edits no existing file) is the wave-15 closure pass over the **single** surviving
geometric residual of the wave-14 ownership packing `Class2OwnershipPacking`
(`TowerK13PackingExistenceCore.lean`):

  `(K.1.3★)  ∀ k ∈ fibre₂,  ρ_D·L ≤ #{ m ∈ supportShell d X : ownerOf m = k }`,

i.e. *every class-2 (semiperiodic, no-large-run) start owns at least `ρ_D L` of its own
pairwise-disjoint shell support hits* — a **system of distinct representatives** at density `ρ_D L`.

Wave-14 reduced the four geometric obligations of `Class2AreaPacking` to this one scalar family by
making `window`/`hsub`/`hdisj` structural through an *abstract* ownership map `ownerOf : ℕ → ℕ`.
But `ownerOf` itself — the descent-shift retraction — was left as a *given*: the caller had to
produce both the map and the floor on its fibres simultaneously.

## What this module does — the SDR reformulation, with the retraction CONSTRUCTED

We retire the requirement to *guess* `ownerOf`.  The genuine combinatorial content of K.1.3 is a
**system of distinct representatives**: a per-start family of *pairwise-disjoint* shell-support
"owned" sets, each of size `≥ ρ_D L`.  From that family the descent-shift retraction is **built**
(`sdrOwnerOf`, `sdrOwnerOf_eq`) and the abstract `Class2OwnershipPacking` discharged in full:

* `sdrOwnerOf` — the ownership retraction sending each shell support position to the *unique* class-2
  start owning it (single-owner property = multiplicity one, the genuine K.1.3 endpoint structure).
* `Class2ShellSDR` — the SDR residual: disjoint owned sets `owned k ⊆ supportShell d X`, each of
  card `≥ ρ_D L`, over the genuine class-2 fibre, plus the `L`-free scalar data.
* `Class2OwnershipPacking.ofShellSDR` — **the reduction** `Class2ShellSDR ⟹ Class2OwnershipPacking`:
  builds `ownerOf := sdrOwnerOf`, proves `hfloor` from the owned-set floor.  Hence Tower Core 3,
  the `Θ(X/Y)` sparsity, and the full closure follow through the wave-14 chain.

## The index-space form — where the no-large-run combinatorics live

The owned sets are not abstract: in the manuscript a class-2 start `k` owns the *hits in its descent
window*.  Hits are enumerated by the strictly-increasing carry enumeration `a` (`carryData.a`), so
the natural data is a family of **disjoint index sets** `idxOwned k ⊆ ℕ`, each landing in the shell
(`a j ∈ supportShell d X`) and of size `≥ ρ_D L`.  Pushing forward through the *injective* `a`
(strict monotonicity of the hit enumeration) turns disjoint index blocks into disjoint shell-position
owned sets, with the count preserved:

* `Class2IndexSDR` + `Class2IndexSDR.toShellSDR` — the index-space SDR and its transport to
  `Class2ShellSDR` (disjoint hit-index blocks of size `≥ ρ_D L`, landing in the shell ⟹ the SDR).
* `Class2IndexSDR.ofIntervals` — the explicit **descent-window** form: the index block of `k` is an
  interval `[lo k, lo k + n k)` of `n k ≥ ρ_D L` consecutive hit indices.  This is the manuscript
  picture: the descent window of a no-large-run start carries `≥ ρ_D L` of its own hits, and the
  windows of distinct selected starts are disjoint (the K.1.3 maximal-disjoint selection).

## Honest status — AUDIT VERDICT

`(K.1.3★)` is **NOT discharged unconditionally** here, and we do not fabricate it.  What this module
proves is the *full reduction chain* to the sharpest combinatorial shape and the **construction of the
retraction** from the SDR (so `ownerOf` is no longer an input):

  `Class2IndexSDR ⟹ Class2ShellSDR ⟹ Class2OwnershipPacking ⟹ (Tower Core 3, Θ(X/Y) sparsity, closure).`

The irreducible open input is then *exactly* the **existence of the disjoint hit-index blocks of size
`≥ ρ_D L` landing in the shell** for each class-2 start, which decomposes into the two genuine
semiperiodic facts the manuscript supplies (Appendix K.2 Fine–Wilf + Lemma K.1.3):

1. **Per-start density** (no-large-run ⟹ semiperiodic recurrence ⟹ bounded primitive period ⟹
   density `≥ ρ_D` over an `O(L)` window): a window of `O(L)` carries `≥ ρ_D L` hits.  *This is the
   genuine analytic content; the currently-formalised `HitSequence` gap bounds control the **total**
   shell support `#supportShell ≥ N` from a run of short gaps, but not the **per-start** ownership.*
2. **Maximal-disjoint selection** (Lemma K.1.3 endpoint disjointness): the selected starts' descent
   windows are pairwise disjoint, i.e. the index blocks `idxOwned k` are disjoint.

So the no-large-run semiperiodic structure *does* force the floor in the manuscript — via the
semiperiodic-density + maximal-selection input — and that input is precisely the residual, now in its
tightest, fully concrete index-block form.

No `sorry`, `axiom`, `admit`, or `native_decide`.  No degenerate/empty/zero-floor shortcut: the floor
is `ρ_D·L > 0`, the owned sets live in the real class-2 fibre of the genuine route, and disjointness
is the genuine single-owner / endpoint-disjointness property.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 1.  A pure-Finset engine: injective push-forward preserves disjointness and cardinality

The descent enumeration `a` is strictly increasing, hence injective.  Two facts about pushing finite
index sets forward through an injection are all the geometry the SDR transport needs. -/

/-- **Disjoint push-forward.**  Distinct (disjoint) index sets have disjoint images under an injective
map — the genuine endpoint-disjointness transported from index space to position space. -/
theorem disjoint_image_of_disjoint {α β : Type*} [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) {s t : Finset α} (h : Disjoint s t) :
    Disjoint (s.image f) (t.image f) := by
  rw [Finset.disjoint_left]
  intro b hbs hbt
  rw [Finset.mem_image] at hbs hbt
  obtain ⟨x, hx, hxb⟩ := hbs
  obtain ⟨y, hy, hyb⟩ := hbt
  have hxy : x = y := hf (hxb.trans hyb.symm)
  subst hxy
  exact (Finset.disjoint_left.mp h hx) hy

/-! ## 2.  The ownership retraction, CONSTRUCTED from a disjoint owned-set family

Given pairwise-disjoint owned sets over the class-2 fibre, every shell support position has at most
one owner.  `sdrOwnerOf` retracts each position to that owner (default `0`, the excluded boundary
start).  `sdrOwnerOf_eq` is the single-owner identity: on the owned set of `k ∈ fibre₂`, the
retraction returns `k`.  This is the descent-shift endpoint structure of K.1.3, no longer assumed but
*derived* from disjointness. -/

open Classical in
/-- **The descent-shift ownership retraction** built from a per-start owned-set family `owned`.
A shell support position `m` is sent to the (disjointness-unique) class-2 start that owns it, or to
the excluded boundary start `0` if none does. -/
noncomputable def sdrOwnerOf (ctx : ActualFailureContext) (owned : ℕ → Finset ℕ) (m : ℕ) : ℕ :=
  if h : ∃ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2, m ∈ owned k then
    h.choose
  else 0

/-- **Single-owner identity (multiplicity one).**  If the owned sets are pairwise disjoint over the
class-2 fibre, then on `owned k` (for `k` in the fibre) the retraction returns `k`. -/
theorem sdrOwnerOf_eq (ctx : ActualFailureContext) (owned : ℕ → Finset ℕ)
    (hdisj : ∀ j ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
      ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
      j ≠ k → Disjoint (owned j) (owned k))
    {k m : ℕ} (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2)
    (hm : m ∈ owned k) :
    sdrOwnerOf ctx owned m = k := by
  have hex : ∃ j ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2, m ∈ owned j :=
    ⟨k, hk, hm⟩
  have hval : sdrOwnerOf ctx owned m = hex.choose := dif_pos hex
  rw [hval]
  have hspec := hex.choose_spec
  by_contra hne
  exact (Finset.disjoint_left.mp (hdisj hex.choose hspec.1 k hk hne) hspec.2) hm

/-! ## 3.  The class-2 SDR residual and its reduction to the ownership packing

`Class2ShellSDR` is `Class2OwnershipPacking` with the abstract `ownerOf` replaced by the genuine
SDR data: a per-start family of pairwise-disjoint owned shell-support sets, each of card `≥ ρ_D L`.
The two scalar fields (`hcalib`, `huniform`) and the boundary exclusion (`hbdry`) are carried
unchanged from the wave-14 residual. -/

/-- **The class-2 system of distinct representatives `(K.1.3★)`.**

* `rhoD`, `eps`, `L` — the manuscript constants `ρ_D`, `ε`, the dyadic scale `L`, with `ρ_D, L > 0`;
* `hYnn`, `hcalib`, `huniform`, `hbdry` — the `L`-free scalar / boundary data (identical to
  `Class2OwnershipPacking`);
* `owned k` — the shell-support positions owned by the class-2 start `k`;
* `howned_sub` — each owned set lies in the shell support;
* `howned_disj` — **endpoint-disjointness**: distinct class-2 starts own disjoint sets;
* `howned_floor` — **the per-start floor** `ρ_D·L ≤ #(owned k)`.

This is the textbook SDR: distinct representatives, density `ρ_D L`.  Unlike `Class2OwnershipPacking`
the ownership map is **not** a field — it is constructed from this data by `sdrOwnerOf`. -/
structure Class2ShellSDR (ctx : ActualFailureContext) where
  /-- The manuscript dense-packing density `ρ_D`. -/
  rhoD : ℝ
  /-- The manuscript active-floor slope `ε` (so `Y ≍ εL`). -/
  eps : ℝ
  /-- The dyadic scale `L` (`X = 2^L`). -/
  L : ℝ
  /-- `ρ_D > 0`. -/
  hrhoD_pos : 0 < rhoD
  /-- `L > 0`. -/
  hL_pos : 0 < L
  /-- The active floor `Y` is nonnegative. -/
  hYnn : 0 ≤ ctx.n24CarryData.Y
  /-- The I.3 active-floor calibration `2·Y ≤ 2·ε·L`. -/
  hcalib : 2 * ctx.n24CarryData.Y ≤ 2 * eps * L
  /-- The `L`-FREE K.4 constant inequality `2·c₀·ε ≤ (ξ/6)·ρ_D`. -/
  huniform : 2 * (erdos260Constants.c0 * eps) ≤ erdos260Constants.ξ / 6 * rhoD
  /-- **Boundary exclusion** — the boundary start `0` is not class-2 routed. -/
  hbdry : 0 ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2
  /-- The shell-support positions owned by each class-2 start. -/
  owned : ℕ → Finset ℕ
  /-- Each owned set lies in the shell support. -/
  howned_sub : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
      owned k ⊆ supportShell ctx.d ctx.X
  /-- **Endpoint-disjointness** — distinct class-2 starts own disjoint sets. -/
  howned_disj : ∀ j ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
      ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
      j ≠ k → Disjoint (owned j) (owned k)
  /-- **`(K.1.3★)` — the per-start SDR floor** `ρ_D·L ≤ #(owned k)`. -/
  howned_floor : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
      rhoD * L ≤ ((owned k).card : ℝ)

/-- **`Class2ShellSDR ⟹ Class2OwnershipPacking`** — the K.1.3 SDR reduction, with the retraction
constructed.  Sets `ownerOf := sdrOwnerOf` and proves the abstract floor `hfloor` from the owned-set
floor: `owned k ⊆ ownWindow … k` (each owned position has owner `k` by `sdrOwnerOf_eq`), so
`#(owned k) ≤ #(ownWindow … k)` and the floor transfers. -/
def Class2OwnershipPacking.ofShellSDR {ctx : ActualFailureContext}
    (S : Class2ShellSDR ctx) : Class2OwnershipPacking ctx where
  ownerOf := sdrOwnerOf ctx S.owned
  rhoD := S.rhoD
  eps := S.eps
  L := S.L
  hrhoD_pos := S.hrhoD_pos
  hL_pos := S.hL_pos
  hYnn := S.hYnn
  hcalib := S.hcalib
  huniform := S.huniform
  hbdry := S.hbdry
  hfloor := by
    intro k hk
    have hsub : S.owned k ⊆ ownWindow ctx.d ctx.X (sdrOwnerOf ctx S.owned) k := by
      intro m hm
      rw [mem_ownWindow]
      exact ⟨S.howned_sub k hk hm, sdrOwnerOf_eq ctx S.owned S.howned_disj hk hm⟩
    have hcard : (S.owned k).card ≤ (ownWindow ctx.d ctx.X (sdrOwnerOf ctx S.owned) k).card :=
      Finset.card_le_card hsub
    calc S.rhoD * S.L
          ≤ ((S.owned k).card : ℝ) := S.howned_floor k hk
      _ ≤ ((ownWindow ctx.d ctx.X (sdrOwnerOf ctx S.owned) k).card : ℝ) := by exact_mod_cast hcard

/-- **`Class2OwnershipPacking ⟹ Class2ShellSDR`** — the reverse reduction, machine-certifying that
the SDR reformulation is *loss-free*: the wave-14 ownership packing yields an SDR by taking
`owned k := ownWindow … k` (subset/disjointness are the structural `ownWindow_subset`/
`ownWindow_disjoint`, the floor is `hfloor` verbatim).  Together with `ofShellSDR` this exhibits
`Class2ShellSDR ⟺ Class2OwnershipPacking`: the SDR is an equivalent shape with the retraction made
constructive, *not* a weakening. -/
def Class2ShellSDR.ofOwnershipPacking {ctx : ActualFailureContext}
    (P : Class2OwnershipPacking ctx) : Class2ShellSDR ctx where
  rhoD := P.rhoD
  eps := P.eps
  L := P.L
  hrhoD_pos := P.hrhoD_pos
  hL_pos := P.hL_pos
  hYnn := P.hYnn
  hcalib := P.hcalib
  huniform := P.huniform
  hbdry := P.hbdry
  owned := fun k => ownWindow ctx.d ctx.X P.ownerOf k
  howned_sub := fun k _ => ownWindow_subset ctx.d ctx.X P.ownerOf k
  howned_disj := fun _ _ _ _ hjk => ownWindow_disjoint ctx.d ctx.X P.ownerOf hjk
  howned_floor := P.hfloor

/-- **Tower Core 3 from the SDR** (`routedClassMassOf … 2 ≤ ξ·X/6`), via the ownership packing. -/
theorem Class2ShellSDR.htowerSubMass {ctx : ActualFailureContext}
    (S : Class2ShellSDR ctx) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
      ≤ erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  (Class2OwnershipPacking.ofShellSDR S).htowerSubMass

/-- **The explicit `Θ(X/Y)` sparsity from the SDR** — `#fibre₂ ≤ c₀·X/(ρ_D·L)`. -/
theorem Class2ShellSDR.class2_card_le {ctx : ActualFailureContext}
    (S : Class2ShellSDR ctx) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).card : ℝ)
      ≤ erdos260Constants.c0 * (ctx.shell.X : ℝ) / (S.rhoD * S.L) :=
  (Class2OwnershipPacking.ofShellSDR S).class2_card_le

/-! ## 4.  The index-space SDR — disjoint hit-index blocks landing in the shell

The hits are enumerated by the strictly-increasing carry enumeration `a` (`carryData.a`; injective by
strict monotonicity, `HitSequence.strict.injective`).  The genuine per-start data is a family of
disjoint **index** sets `idxOwned k`, each landing in the shell support under `a` and of size
`≥ ρ_D L`.  Pushing forward through the injective `a` yields a `Class2ShellSDR`. -/

/-- **The class-2 index-space SDR.**  Disjoint hit-index blocks, each landing in the shell and of size
`≥ ρ_D L`, over the genuine class-2 fibre.

* `a`, `hainj` — the (injective) hit enumeration; intended `a := ctx.n24CarryData.a`, with `hainj`
  from the strict monotonicity of the hit sequence;
* `idxOwned k` — the hit indices owned by the class-2 start `k`;
* `hidx_lands` — each owned index lands in the shell support: `a j ∈ supportShell d X`;
* `hidx_disj` — **endpoint-disjointness** of the index blocks (the K.1.3 maximal-disjoint selection);
* `hidx_floor` — **the per-block floor** `ρ_D·L ≤ #(idxOwned k)` (the no-large-run density). -/
structure Class2IndexSDR (ctx : ActualFailureContext) where
  /-- The hit enumeration (intended `ctx.n24CarryData.a`). -/
  a : ℕ → ℕ
  /-- Injectivity of the enumeration (strict monotonicity of the hit sequence). -/
  hainj : Function.Injective a
  /-- The manuscript dense-packing density `ρ_D`. -/
  rhoD : ℝ
  /-- The manuscript active-floor slope `ε`. -/
  eps : ℝ
  /-- The dyadic scale `L`. -/
  L : ℝ
  /-- `ρ_D > 0`. -/
  hrhoD_pos : 0 < rhoD
  /-- `L > 0`. -/
  hL_pos : 0 < L
  /-- The active floor `Y` is nonnegative. -/
  hYnn : 0 ≤ ctx.n24CarryData.Y
  /-- The I.3 active-floor calibration `2·Y ≤ 2·ε·L`. -/
  hcalib : 2 * ctx.n24CarryData.Y ≤ 2 * eps * L
  /-- The `L`-FREE K.4 constant inequality `2·c₀·ε ≤ (ξ/6)·ρ_D`. -/
  huniform : 2 * (erdos260Constants.c0 * eps) ≤ erdos260Constants.ξ / 6 * rhoD
  /-- **Boundary exclusion** — the boundary start `0` is not class-2 routed. -/
  hbdry : 0 ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2
  /-- The hit indices owned by each class-2 start. -/
  idxOwned : ℕ → Finset ℕ
  /-- Each owned index lands in the shell support under `a`. -/
  hidx_lands : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
      ∀ j ∈ idxOwned k, a j ∈ supportShell ctx.d ctx.X
  /-- **Endpoint-disjointness** of the index blocks. -/
  hidx_disj : ∀ j ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
      ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
      j ≠ k → Disjoint (idxOwned j) (idxOwned k)
  /-- **The per-block floor** `ρ_D·L ≤ #(idxOwned k)`. -/
  hidx_floor : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
      rhoD * L ≤ ((idxOwned k).card : ℝ)

/-- **`Class2IndexSDR ⟹ Class2ShellSDR`** — the index-to-position transport.  Owned sets
`owned k := (idxOwned k).image a`: subset of shell by `hidx_lands`, pairwise disjoint by
`disjoint_image_of_disjoint`, and `#(owned k) = #(idxOwned k) ≥ ρ_D L` since `a` is injective. -/
def Class2IndexSDR.toShellSDR {ctx : ActualFailureContext}
    (S : Class2IndexSDR ctx) : Class2ShellSDR ctx where
  rhoD := S.rhoD
  eps := S.eps
  L := S.L
  hrhoD_pos := S.hrhoD_pos
  hL_pos := S.hL_pos
  hYnn := S.hYnn
  hcalib := S.hcalib
  huniform := S.huniform
  hbdry := S.hbdry
  owned := fun k => (S.idxOwned k).image S.a
  howned_sub := by
    intro k hk m hm
    simp only [Finset.mem_image] at hm
    obtain ⟨j, hj, rfl⟩ := hm
    exact S.hidx_lands k hk j hj
  howned_disj := by
    intro j hj k hk hjk
    exact disjoint_image_of_disjoint S.hainj (S.hidx_disj j hj k hk hjk)
  howned_floor := by
    intro k hk
    have h := S.hidx_floor k hk
    rwa [← Finset.card_image_of_injective (S.idxOwned k) S.hainj] at h

/-- **Tower Core 3 from the index-space SDR.** -/
theorem Class2IndexSDR.htowerSubMass {ctx : ActualFailureContext}
    (S : Class2IndexSDR ctx) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
      ≤ erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  S.toShellSDR.htowerSubMass

/-- **The descent-window form of the index SDR.**  Each class-2 start `k` owns the interval of
`n k` consecutive hit indices `[lo k, lo k + n k)`; the floor `ρ_D·L ≤ n k` is exactly "the descent
window carries `≥ ρ_D L` of its own hits", and the intervals of distinct selected starts are
disjoint (the K.1.3 maximal-disjoint selection). -/
def Class2IndexSDR.ofIntervals (ctx : ActualFailureContext)
    (a : ℕ → ℕ) (hainj : Function.Injective a)
    (rhoD eps L : ℝ) (hrhoD_pos : 0 < rhoD) (hL_pos : 0 < L)
    (hYnn : 0 ≤ ctx.n24CarryData.Y)
    (hcalib : 2 * ctx.n24CarryData.Y ≤ 2 * eps * L)
    (huniform : 2 * (erdos260Constants.c0 * eps) ≤ erdos260Constants.ξ / 6 * rhoD)
    (hbdry : 0 ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2)
    (lo n : ℕ → ℕ)
    (hlands : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
      ∀ j ∈ Finset.Ico (lo k) (lo k + n k), a j ∈ supportShell ctx.d ctx.X)
    (hdisj : ∀ j ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
      ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2, j ≠ k →
      Disjoint (Finset.Ico (lo j) (lo j + n j)) (Finset.Ico (lo k) (lo k + n k)))
    (hfloor : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
      rhoD * L ≤ (n k : ℝ)) :
    Class2IndexSDR ctx where
  a := a
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
  idxOwned := fun k => Finset.Ico (lo k) (lo k + n k)
  hidx_lands := hlands
  hidx_disj := hdisj
  hidx_floor := by
    intro k hk
    have hcard : (Finset.Ico (lo k) (lo k + n k)).card = n k := by
      rw [Nat.card_Ico]; omega
    rw [hcard]
    exact hfloor k hk

/-! ## 5.  End-to-end — the full Tower+Run seed closure from the SDR -/

/-- **Build the full Tower+Run seed closure from the class-2 SDR + run chain.**  Pre-composes the
K.1.3 SDR reduction with the wave-14 `buildTowerRunSeedClosureFromOwnershipPacking`: an SDR for every
shell feeds `erdos260_of_minimalResidual` end-to-end (Core 3 via the multiplicity-one ownership
packing, Cores 4+5 via the run stage chain). -/
def buildTowerRunSeedClosureFromShellSDR
    (pack : ∀ ctx : ActualFailureContext, Class2ShellSDR ctx)
    (chain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx) :
    TowerRunSeedClosureData :=
  buildTowerRunSeedClosureFromOwnershipPacking
    (fun ctx => Class2OwnershipPacking.ofShellSDR (pack ctx)) chain

/-- **Build the closure from the index-space SDR + run chain.** -/
def buildTowerRunSeedClosureFromIndexSDR
    (pack : ∀ ctx : ActualFailureContext, Class2IndexSDR ctx)
    (chain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx) :
    TowerRunSeedClosureData :=
  buildTowerRunSeedClosureFromShellSDR (fun ctx => (pack ctx).toShellSDR) chain

/-! ## 6.  Honest residual inventory -/

/-- The precise status of Lemma K.1.3 `(K.1.3★)` after this wave-15 module. -/
def towerSDRResiduals : List String :=
  [ "REFORMULATION (SDR) — Class2ShellSDR: the wave-14 residual (K.1.3★) recast as a system of " ++
      "distinct representatives — a per-start family of PAIRWISE-DISJOINT owned shell-support sets " ++
      "owned k ⊆ supportShell d X, each of card ≥ ρ_D L, over the genuine class-2 fibre. The " ++
      "abstract ownership map ownerOf is NO LONGER an input.",
    "RETRACTION CONSTRUCTED (PROVED) — sdrOwnerOf + sdrOwnerOf_eq: the descent-shift retraction is " ++
      "BUILT from the disjoint owned sets (each shell position has a unique owner = multiplicity " ++
      "one), not assumed. sdrOwnerOf_eq is the single-owner identity ownerOf m = k on owned k.",
    "REDUCTION A (PROVED, EQUIVALENCE) — Class2OwnershipPacking.ofShellSDR: Class2ShellSDR ⟹ " ++
      "Class2OwnershipPacking, with ownerOf := sdrOwnerOf and hfloor proved from the owned-set floor " ++
      "via owned k ⊆ ownWindow … k. The reverse Class2ShellSDR.ofOwnershipPacking (owned k := " ++
      "ownWindow … k) machine-certifies Class2ShellSDR ⟺ Class2OwnershipPacking — the SDR is a " ++
      "LOSS-FREE reformulation with the retraction made constructive, not a weakening. Hence Tower " ++
      "Core 3 (Class2ShellSDR.htowerSubMass) and the Θ(X/Y) sparsity (Class2ShellSDR.class2_card_le) " ++
      "follow through the wave-14 chain.",
    "ENGINE (PROVED) — disjoint_image_of_disjoint: an injective push-forward preserves disjointness; " ++
      "with Finset.card_image_of_injective it transports the index-space SDR to position space.",
    "TRANSPORT B (PROVED) — Class2IndexSDR.toShellSDR: disjoint HIT-INDEX blocks idxOwned k, each " ++
      "landing in the shell (a j ∈ supportShell) and of card ≥ ρ_D L, push forward through the " ++
      "injective enumeration a to the position-space SDR. This is the index-space form where the " ++
      "no-large-run combinatorics live (a := carryData.a, injective by HitSequence strict mono).",
    "DESCENT-WINDOW FORM (PROVED) — Class2IndexSDR.ofIntervals: the concrete picture — idxOwned k is " ++
      "an interval [lo k, lo k + n k) of n k ≥ ρ_D L consecutive hit indices; the floor is exactly " ++
      "'the descent window carries ≥ ρ_D L of its own hits', and the windows of distinct selected " ++
      "starts are disjoint (the K.1.3 maximal-disjoint selection).",
    "AUDIT VERDICT — (K.1.3★) is NOT discharged unconditionally (not fabricated). The no-large-run " ++
      "semiperiodic structure DOES force the floor in the manuscript, but via two genuine inputs " ++
      "that remain the irreducible residual, now in tightest index-block form: (1) per-start " ++
      "DENSITY (no-large-run ⟹ semiperiodic recurrence ⟹ bounded primitive period ⟹ density ≥ ρ_D " ++
      "over an O(L) window; Appendix K.2 Fine–Wilf) — the formalised HitSequence gap bounds control " ++
      "the TOTAL shell support, not per-start ownership; and (2) MAXIMAL-DISJOINT SELECTION (Lemma " ++
      "K.1.3 endpoint disjointness) — the index blocks idxOwned k are pairwise disjoint.",
    "CHAIN — Class2IndexSDR ⟹ Class2ShellSDR ⟹ Class2OwnershipPacking ⟹ Tower Core 3 / Θ(X/Y) " ++
      "sparsity / full TowerRunSeedClosureData (buildTowerRunSeedClosureFromShellSDR, " ++
      "buildTowerRunSeedClosureFromIndexSDR), feeding erdos260_of_minimalResidual.",
    "NON-DEGENERATE — floor = ρ_D·L > 0 over the real class-2 fibre of the genuine route; " ++
      "disjointness is the genuine single-owner / endpoint-disjointness property; no empty / " ++
      "zero-floor / vacuous shortcut.",
    "WAVE-16 UPDATE — both genuine inputs of the AUDIT VERDICT are now DISCHARGED to their bare " ++
      "structural cores. (1) per-start DENSITY: the semiperiodic-density MECHANISM is PROVED " ++
      "unconditionally in SDRDensityCore (windowWeight_ge_rhoD_mul_L = ρ_D·L ≤ windowWeight via the " ++
      "telescoped periodic count periodicWindow_count_lower + the §24/Fine–Wilf period-density floor; " ++
      "Class2IndexSDR.ofSemiperiodicDensity supplies hidx_floor), leaving only the EXISTENCE of the " ++
      "semiperiodic descent window (no-large-run ⟹ bounded primitive period of density ≥ ρ_D, " ++
      "manuscript K.2 / §I.4). (2) MAXIMAL-DISJOINT SELECTION: PROVED as a SHARP iff in " ++
      "SDRSelectionCore (exists_disjoint_blocks_iff_marginal; Class2IndexSDR.ofWindowsHall builds this " ++
      "very SDR) — disjoint size-m blocks exist ⟺ the Hall union/marginal bound #⋃_{k∈S} Ω(k) ≥ " ++
      "ρ_D L·|S|; per-start density alone (the #S=1 slice) is necessary but NOT sufficient. The " ++
      "residual here is therefore now just the semiperiodic-window EXISTENCE — one of the three bare " ++
      "structural frontier facts (with CNL exp_injOn and Return (Z))." ]

theorem towerSDRResiduals_nonempty : towerSDRResiduals ≠ [] := by
  simp [towerSDRResiduals]

/-! ## 7.  Axiom-cleanliness audit -/

#print axioms disjoint_image_of_disjoint
#print axioms sdrOwnerOf
#print axioms sdrOwnerOf_eq
#print axioms Class2OwnershipPacking.ofShellSDR
#print axioms Class2ShellSDR.ofOwnershipPacking
#print axioms Class2ShellSDR.htowerSubMass
#print axioms Class2ShellSDR.class2_card_le
#print axioms Class2IndexSDR.toShellSDR
#print axioms Class2IndexSDR.ofIntervals
#print axioms Class2IndexSDR.htowerSubMass
#print axioms buildTowerRunSeedClosureFromShellSDR
#print axioms buildTowerRunSeedClosureFromIndexSDR

end

end Erdos260
