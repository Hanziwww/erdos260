import Erdos260.TowerI41PackingCore

/-!
# Lemma K.1.3 — endpoint-disjoint window-packing *existence* for the class-2 fibre

This module (NEW; it edits no existing file) supplies the **existence side** of the wave-13 area
packing `Class2AreaPacking` (`TowerI41PackingCore.lean`): the genuine I.4.1/K.1.3 dense-marker input
inhabiting that structure for the real `ActualFailureContext`.

Wave-13 PROVED the *consequences* of `Class2AreaPacking` (the multiplicity-one engine
`card_mul_floor_le_of_disjoint_windows`, the reduction to Tower Core 3, the `Θ(X/Y)` sparsity, and
the `L`-uniform constant certificate `areaPacking_hconst_of_Luniform`).  What remained open is the
*construction* of the endpoint-disjoint window system itself — the K.1.3
**maximal-disjoint-selection + per-hit floor**.  This file isolates that residual in its sharpest
shape and discharges everything around it.

## The endpoint = ownership/retraction reformulation

In `Class2AreaPacking` the field `window : ℕ → Finset ℕ` is *free* and the two geometric obligations
`hsub` (`window k ⊆ supportShell d X`) and `hdisj` (pairwise disjointness — the carry descent-shift
endpoint structure `end(k) = k+r`, retraction `·−r`) are *constraints*.  We make them **structural**:
choose an **ownership map** `ownerOf : ℕ → ℕ` (the descent-shift retraction sending each shell
support position back to the class-2 start that owns it) and set

  `ownWindow d X ownerOf k := (supportShell d X).filter (fun m => ownerOf m = k)`.

Then *by construction*:

* `hsub`  — `ownWindow … k ⊆ supportShell d X` is `Finset.filter_subset` (FREE, `ownWindow_subset`);
* `hdisj` — distinct fibres of a function are disjoint (FREE, `ownWindow_disjoint`): a support
  position has exactly **one** owner, i.e. *multiplicity one* is automatic, not assumed.

So the four geometric obligations `(window, hsub, hdisj, hcard)` collapse to the **single** residual

  `(K.1.3★)  ∀ k ∈ fibre₂,  ρ_D·L ≤ #{ m ∈ supportShell d X : ownerOf m = k }`,

i.e. *every class-2 start owns at least `ρ_D L` of its own pairwise-disjoint shell support hits*.
This is exactly the K.1.3 maximal-disjoint-selection bundled with the per-hit floor — a **system of
distinct representatives at density `ρ_D L`** for the class-2 fibre in the shell support.

## Deliverable

* `ownWindow` / `mem_ownWindow` — the ownership (descent-retraction) window, with membership.
* `ownWindow_subset`, `ownWindow_disjoint` — `hsub` and `hdisj` **proved structurally** (FREE).
* `Class2OwnershipPacking ctx` — the **sharp K.1.3 residual**: an ownership map + the genuine
  geometric floor `(K.1.3★)` + the `L`-FREE scalar data (`hcalib 2Y ≤ 2εL`, `huniform 2c₀ε ≤
  (ξ/6)ρ_D`).  It carries NO abstract `hconst` and NO free `window`/`hsub`/`hdisj`: the only
  geometric content is `hfloor`.
* `Class2AreaPacking.ofOwnershipPacking` — **the reduction**: `Class2OwnershipPacking ⟹
  Class2AreaPacking`, discharging `hsub`/`hdisj` structurally and `hconst` via the wave-13
  `areaPacking_hconst_of_Luniform`.
* `Class2OwnershipPacking.htowerSubMass` + `buildTowerRunSeedClosureFromOwnershipPacking` — the
  ownership residual feeds Tower Core 3 and the full `TowerRunSeedClosureData` end-to-end, exactly
  through the wave-13 `Class2AreaPacking` ⟹ frontier chain.

## Honest status

`Class2AreaPacking` is **NOT** constructed unconditionally: the per-start ownership floor
`(K.1.3★)` is the genuine open K.1.3 input (the semiperiodic "no large run" recurrence forcing each
descent window to carry `≥ ρ_D L` of its own support hits, together with the disjoint selection).
We do not fabricate it.  We DISCHARGE the remaining three sides (subset, disjointness — structurally;
the constant — `L`-uniformly) so the residual is *exactly* the one scalar family `(K.1.3★)`, in its
tightest, multiplicity-one form.

No `sorry`, `axiom`, `admit`, or `native_decide`.  No degenerate/empty/zero-floor shortcut: the
floor is `ρ_D·L > 0` (genuine positive per-hit floor), the windows live in the real class-2 fibre of
the genuine route, and disjointness is the genuine single-owner property of the shell support.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 1.  The ownership (descent-retraction) window — subset & disjointness are FREE

The descent-shift endpoint structure of K.1.3 is an *ownership map* `ownerOf : ℕ → ℕ` retracting each
shell support position to the class-2 start owning it.  The window of `k` is its owned support; the
two geometric obligations of `Class2AreaPacking` then hold *by construction*. -/

/-- **The ownership window** of a start `k`: the shell support positions whose owner (under the
descent-shift retraction `ownerOf`) is `k`.  This is the descent-window-hit set in its
endpoint-indexed form. -/
def ownWindow (d : ℕ → ℕ) (X : ℕ) (ownerOf : ℕ → ℕ) (k : ℕ) : Finset ℕ :=
  (supportShell d X).filter (fun m => ownerOf m = k)

@[simp] theorem mem_ownWindow (d : ℕ → ℕ) (X : ℕ) (ownerOf : ℕ → ℕ) (k m : ℕ) :
    m ∈ ownWindow d X ownerOf k ↔ m ∈ supportShell d X ∧ ownerOf m = k := by
  simp [ownWindow, Finset.mem_filter]

/-- **`hsub` is FREE.**  Each ownership window lies in the shell support (it is a filter of it). -/
theorem ownWindow_subset (d : ℕ → ℕ) (X : ℕ) (ownerOf : ℕ → ℕ) (k : ℕ) :
    ownWindow d X ownerOf k ⊆ supportShell d X :=
  Finset.filter_subset _ _

/-- **`hdisj` is FREE (multiplicity one).**  Distinct owners give disjoint windows: a support
position has exactly one owner, so it cannot lie in two ownership windows.  This is the genuine
endpoint/descent-shift disjointness, made structural. -/
theorem ownWindow_disjoint (d : ℕ → ℕ) (X : ℕ) (ownerOf : ℕ → ℕ) {j k : ℕ} (h : j ≠ k) :
    Disjoint (ownWindow d X ownerOf j) (ownWindow d X ownerOf k) := by
  rw [Finset.disjoint_left]
  intro m hmj hmk
  rw [mem_ownWindow] at hmj hmk
  exact h (hmj.2.symm.trans hmk.2)

/-! ## 2.  The sharp K.1.3 residual: the per-start ownership floor

`Class2OwnershipPacking` is the corrected *existence* shape of the I.4.1/K.1.3 dense-marker input.
It is `Class2AreaPacking` after retiring `window`, `hsub`, `hdisj` (now structural via `ownWindow`)
and `hconst` (now `L`-uniform via the two scalar fields), leaving the **single** genuine geometric
obligation `hfloor` — the K.1.3 maximal-disjoint-selection + per-hit floor. -/

/-- **The sharp K.1.3 endpoint-disjoint window-packing residual.**

* `ownerOf` — the descent-shift retraction assigning each shell support position to its owning
  class-2 start (the K.1.3 endpoint structure);
* `rhoD`, `eps`, `L` — the manuscript constants `ρ_D`, `ε`, and the dyadic scale `L`, with
  `rhoD, L > 0` (genuine, non-degenerate);
* `hYnn`, `hcalib` — the active floor is nonnegative and `≤ 2εL` (the I.3 calibration `Y ≍ εL`);
* `huniform` — the `L`-FREE constant inequality `2·c₀·ε ≤ (ξ/6)·ρ_D` (the wave-13 resolution of the
  deep-shell obstruction; drives `hconst` through `areaPacking_hconst_of_Luniform`);
* `hbdry` — the boundary start `0` is not class-2 routed;
* `hfloor` — **`(K.1.3★)`** : every class-2 start owns at least `ρ_D·L` of its own (pairwise-disjoint)
  shell support hits.  This is the **only** geometric residual; subset and disjointness are free. -/
structure Class2OwnershipPacking (ctx : ActualFailureContext) where
  /-- The descent-shift retraction (ownership of shell support positions by class-2 starts). -/
  ownerOf : ℕ → ℕ
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
  /-- **`(K.1.3★)` — the per-start ownership floor.**  Each class-2 start owns at least `ρ_D·L`
  support positions of the shell.  THE sharp residual. -/
  hfloor : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
      rhoD * L ≤ ((ownWindow ctx.d ctx.X ownerOf k).card : ℝ)

/-! ## 3.  The reduction: the ownership floor inhabits `Class2AreaPacking`

`hsub` and `hdisj` are discharged by `ownWindow_subset` / `ownWindow_disjoint` (structural, free);
`hconst` by the wave-13 `areaPacking_hconst_of_Luniform` from the `L`-free scalar data; `hcard` is
exactly `hfloor`.  So the only thing the caller must supply is `(K.1.3★)`. -/

/-- **`Class2OwnershipPacking ⟹ Class2AreaPacking`** — the K.1.3 existence reduction.

Builds the wave-13 area packing from the ownership residual: window `:= ownWindow`, floor
`:= ρ_D·L`, with `hsub`/`hdisj` proved structurally (multiplicity one) and `hconst` proved
`L`-uniformly.  The class-2 area packing — and hence Tower Core 3 — now hinges on the **single**
geometric fact `(K.1.3★)`. -/
def Class2AreaPacking.ofOwnershipPacking {ctx : ActualFailureContext}
    (P : Class2OwnershipPacking ctx) : Class2AreaPacking ctx where
  floor := P.rhoD * P.L
  hfloor_pos := mul_pos P.hrhoD_pos P.hL_pos
  window := fun k => ownWindow ctx.d ctx.X P.ownerOf k
  hbdry := P.hbdry
  hsub := fun k _ => ownWindow_subset ctx.d ctx.X P.ownerOf k
  hdisj := fun _ _ _ _ hjk => ownWindow_disjoint ctx.d ctx.X P.ownerOf hjk
  hcard := P.hfloor
  hconst :=
    areaPacking_hconst_of_Luniform erdos260Constants.c0_pos.le P.hL_pos.le P.hYnn P.hcalib P.huniform

/-! ## 4.  End-to-end: the ownership residual discharges Tower Core 3 and feeds the frontier -/

/-- **Tower Core 3 from the ownership residual** (`routedClassMassOf … 2 ≤ ξ·X/6`), via the wave-13
`Class2AreaPacking` ⟹ Core 3 chain. -/
theorem Class2OwnershipPacking.htowerSubMass {ctx : ActualFailureContext}
    (P : Class2OwnershipPacking ctx) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
      ≤ erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  (Class2AreaPacking.ofOwnershipPacking P).htowerSubMass

/-- **The explicit `Θ(X/Y)` sparsity from the ownership residual** — `#fibre₂ ≤ c₀·X/(ρ_D·L)`. -/
theorem Class2OwnershipPacking.class2_card_le {ctx : ActualFailureContext}
    (P : Class2OwnershipPacking ctx) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).card : ℝ)
      ≤ erdos260Constants.c0 * (ctx.shell.X : ℝ) / (P.rhoD * P.L) :=
  class2_card_le_of_areaPacking ctx (Class2AreaPacking.ofOwnershipPacking P)

/-- **Build the full Tower+Run seed closure from the ownership residual + run chain.**  Pre-composes
the K.1.3 existence reduction with the wave-13 `buildTowerRunSeedClosureFromAreaPacking`, so an
ownership residual for every shell feeds `erdos260_of_minimalResidual` end-to-end (Core 3 via the
multiplicity-one area packing, Cores 4+5 via the run stage chain). -/
def buildTowerRunSeedClosureFromOwnershipPacking
    (pack : ∀ ctx : ActualFailureContext, Class2OwnershipPacking ctx)
    (chain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx) :
    TowerRunSeedClosureData :=
  buildTowerRunSeedClosureFromAreaPacking
    (fun ctx => Class2AreaPacking.ofOwnershipPacking (pack ctx)) chain

/-! ## 5.  Honest residual inventory -/

/-- The precise status of Lemma K.1.3 (the `Class2AreaPacking` existence side) after this module. -/
def towerK13PackingExistenceResiduals : List String :=
  [ "REFORMULATION (endpoint = ownership/retraction) — ownWindow d X ownerOf k := " ++
      "(supportShell d X).filter (ownerOf · = k): the K.1.3 carry descent-shift endpoint structure " ++
      "as an ownership map ℕ→ℕ retracting each shell support hit to its owning class-2 start. The " ++
      "free window + the two geometric constraints hsub/hdisj of Class2AreaPacking become " ++
      "STRUCTURAL.",
    "hsub PROVED (FREE) — ownWindow_subset: ownWindow … k ⊆ supportShell d X is Finset.filter_subset.",
    "hdisj PROVED (FREE, multiplicity one) — ownWindow_disjoint: distinct owners give disjoint " ++
      "windows (a support position has exactly ONE owner). The genuine endpoint/descent-shift " ++
      "disjointness, made structural — no maximal-selection step is assumed at the window level; it " ++
      "is absorbed into the single floor residual below.",
    "hconst PROVED (L-UNIFORM) — discharged by the wave-13 areaPacking_hconst_of_Luniform from the " ++
      "two L-FREE scalar fields hcalib (2Y ≤ 2εL) and huniform (2c₀ε ≤ (ξ/6)ρ_D). The deep-shell " ++
      "obstruction is gone: ρ_D L sits in the numerator balancing 2Y ≍ 2εL.",
    "SHARP RESIDUAL (K.1.3★, the ONLY geometric obligation) — Class2OwnershipPacking.hfloor: " ++
      "∀ k ∈ fibre₂, ρ_D·L ≤ #{ m ∈ supportShell d X : ownerOf m = k }. I.e. every class-2 start " ++
      "owns ≥ ρ_D L of its own PAIRWISE-DISJOINT shell support hits — a system of distinct " ++
      "representatives at density ρ_D L for the class-2 fibre. This is the K.1.3 " ++
      "maximal-disjoint-selection + per-hit floor combined into one multiplicity-one scalar family, " ++
      "the irreducible open input (the semiperiodic no-large-run recurrence + disjoint selection). " ++
      "It is NOT fabricated here.",
    "REDUCTION (PROVED) — Class2AreaPacking.ofOwnershipPacking: Class2OwnershipPacking ⟹ " ++
      "Class2AreaPacking, with floor = ρ_D·L > 0 (genuine, non-degenerate). Hence Tower Core 3 " ++
      "(Class2OwnershipPacking.htowerSubMass: routedClassMassOf … 2 ≤ ξ·X/6) and the Θ(X/Y) sparsity " ++
      "(class2_card_le: #fibre₂ ≤ c₀X/(ρ_D L)) follow.",
    "ASSEMBLED — buildTowerRunSeedClosureFromOwnershipPacking: a full TowerRunSeedClosureData from " ++
      "the ownership residual (Core 3) + RunClass5StageChain (Cores 4+5), feeding " ++
      "erdos260_of_minimalResidual through the wave-13 area packing.",
    "VERDICT — Class2AreaPacking is NOT constructed unconditionally; it is reduced to the single " ++
      "bare residual (K.1.3★). The other three sides (subset, disjointness, constant) are fully " ++
      "discharged. No degenerate/empty/zero-floor shortcut: floor = ρ_D L > 0 over the real class-2 " ++
      "fibre of the genuine route." ]

theorem towerK13PackingExistenceResiduals_nonempty :
    towerK13PackingExistenceResiduals ≠ [] := by
  simp [towerK13PackingExistenceResiduals]

/-! ## 6.  Axiom-cleanliness audit -/

#print axioms ownWindow_subset
#print axioms ownWindow_disjoint
#print axioms Class2AreaPacking.ofOwnershipPacking
#print axioms Class2OwnershipPacking.htowerSubMass
#print axioms Class2OwnershipPacking.class2_card_le
#print axioms buildTowerRunSeedClosureFromOwnershipPacking

end

end Erdos260
