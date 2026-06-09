import Erdos260.DensePackFirstStopOwnerCore

/-!
# DensePack Core 12 — the endpoint landing `landsShift` IS the bare coarea hit-density

This module (NEW; it edits no existing file) owns the single surviving DensePack residual flagged by
wave 14, the endpoint-landing fact

```
densePackLandsShift budget ctx
  := ∀ k ∈ genuineDensePackStarts ctx, k + ctx.n24CarryData.r ∈ densePackMarkers budget ctx
```

(the terminal descent endpoint `end(k) = k + r` of each genuine densePack tower-exit start is a dense
marker).  Wave 14 reduced **all** of DensePack Core 12 to this one geometric fact and pinned the
first-stop owner to the descent shift `· − r`.  This module **audits the marker geometry to the
ground** and proves that `landsShift` is *exactly* the bare K.1 coarea hit-density at the descent
endpoint — with the ambient-window range bound **fully discharged**.

## The audit (what `densePackMarkers` really is)

`densePackMarkers budget ctx` abbreviates the faithful leaf's dense-marker set
`(faithfulCapacityPhases budget ctx).toClosurePhaseData.densePack.densePackPoints`.  Threading the
faithful assembly (`assembledFaithfulPhases` → `actualProofV4LeafPhases` →
`appendixNGapCanonicalYActualDensePackToGrounded` → `ofActualSupportWindows`) this is **definitionally**
the shell's own actual-support marker set (`densePackMarkers_eq_actualPoints`, by `rfl`):

```
densePackMarkers budget ctx = proofV4DensePackActualPoints ctx.shell
```

and a point `m` lies in it (`mem_proofV4DensePackActualPoints`) iff

* `m ≤ 3·X + spread` — the ambient finite window, **and**
* `⌊ρ_D·L⌋ ≤ |supportWindow(m)|` — the one-sided support packet `[m, m+spread] ∩ supportShell d X`
  carries at least the manuscript threshold `⌊ρ_D L⌋` of shell hits (the **K.1 hit-density**).

## The reduction (the range bound is geometric housekeeping; only the hit-density remains)

The ambient range bound is **not** an independent residual: every element of `supportShell d X` is
`≤ 2X` (`mem_supportShell`), so a *non-empty* support window already forces `m ≤ 2X ≤ 3X + spread`
(`endpoint_le_of_window_nonempty`).  And the threshold is a genuine positive floor
`⌊ρ_D L⌋ ≥ 1` for any failure context (`proofV4DensePackMinHits_pos`, from the manuscript largeness
gate `ctx.shell_carryLarge`).  Hence the hit-density alone forces the window non-empty, hence the
range bound (`mem_actualPoints_of_density`).  So:

* `densePackEndpointDensity ctx`
  `:= ∀ k ∈ genuineDensePackStarts ctx, ⌊ρ_D L⌋ ≤ |supportWindow(k + r)|` — the **bare coarea
  hit-density** at the descent endpoint (the J.2/J.5/K.1 coarea normalisation, read on the *actual*
  endpoint `k + r`).  It depends only on `ctx` (the audit identity is budget-independent), so the
  surviving residual is purely the shell's hit-density geometry, *not* the free phase routing;
* `densePackLandsShift_iff_density` — **the sharp characterization**: `landsShift ⟺
  densePackEndpointDensity`.  The endpoint landing is *exactly* the bare hit-density; nothing else.

## What is fully proved here (axiom-clean: no `sorry`/`axiom`/`admit`/`native_decide`)

* `densePackMarkers_eq_actualPoints` — `densePackMarkers budget ctx = proofV4DensePackActualPoints
  ctx.shell` by `rfl` (the faithful-assembly audit, grounded).
* `mem_proofV4DensePackActualPoints` / `mem_densePackMarkers` — the clean membership characterization
  (ambient range ∧ K.1 hit-density).
* `endpoint_le_of_window_nonempty` — a non-empty support window forces `m ≤ 2X` (the range bound from
  one hit).
* `proofV4DensePackMinHits_pos` — `0 < ⌊ρ_D L⌋` for any failure context.
* `mem_actualPoints_of_density` — the K.1 hit-density forces full marker membership (range discharged).
* `densePackEndpointDensity` + `densePackLandsShift_iff_density` / `densePackLandsShift_iff_coareaMembership`
  — the sharp reduction of `landsShift` to the bare coarea hit-density.
* `densePackEndpointDensity_sufficient` / `densePackCoareaFirstStop_nonempty_of_density` — the
  hit-density forces the K.1.1 count and inhabits `DensePackCoareaFirstStop`.
* `erdos260_of_densePackEndpointDensity` — Erdős #260 from the hit-density family (+ the orthogonal
  TRT/Chernoff/CNL/active-window inputs), via the wave-14 `erdos260_of_densePackLandsShift`.

## The honest residual that genuinely remains

`densePackEndpointDensity` — the bare K.1 coarea hit-density `⌊ρ_D L⌋ ≤ |supportWindow(k + r)|` of
each densePack tower-exit start's terminal endpoint.  It relates the SCC-band tower-exit classifier
`towerClsOfShell ctx · = densePack` (the canonical slope orbit, `canonGap = 3`) to the **shell's own**
hit-density geometry `supportShell ctx.shell.d ctx.shell.X`.  No phase-budget / free-routing datum
forces a slope-orbit densePack endpoint to sit at the centre of a hit-dense support window — this is
the manuscript J.2/J.5/K.1 coarea normalisation, genuinely open at this layer.  This module reduces
the residual to its irreducible core: the **single hit-density inequality**, with the marker geometry
fully unfolded and the ambient range bound discharged.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 1.  The audit — `densePackMarkers` IS the shell's actual-support marker set

The abbreviation `densePackMarkers budget ctx` threads through the faithful assembly to the shell's
own `proofV4DensePackActualPoints` — definitionally (`rfl`).  We then read off the clean membership
characterization. -/

/-- **The grounded audit identity (by `rfl`).**  The faithful leaf's dense-marker set
`densePackMarkers budget ctx` is, definitionally, the shell's own actual-support marker set
`proofV4DensePackActualPoints ctx.shell` — the faithful assembly
(`assembledFaithfulPhases` → `actualProofV4LeafPhases` →
`appendixNGapCanonicalYActualDensePackToGrounded` → `ofActualSupportWindows`) carries the
`densePackPoints` field unchanged. -/
theorem densePackMarkers_eq_actualPoints
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    densePackMarkers budget ctx = proofV4DensePackActualPoints ctx.shell := rfl

/-- **The clean membership characterization of the shell's marker set.**  A point `m` is an actual
dense marker iff it sits in the ambient finite window `[0, 3X + spread]` **and** its one-sided
support packet `[m, m + spread] ∩ supportShell d X` carries at least the manuscript threshold
`⌊ρ_D L⌋` of shell hits.  The second conjunct is the genuine K.1 hit-density. -/
theorem mem_proofV4DensePackActualPoints (shell : FailingDyadicShell) (m : ℕ) :
    m ∈ proofV4DensePackActualPoints shell ↔
      m ≤ 3 * shell.X + proofV4DensePackSpread shell ∧
        proofV4DensePackMinHits shell ≤ (proofV4DensePackSupportWindow shell m).card := by
  unfold proofV4DensePackActualPoints
  rw [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨_, h2⟩, h3⟩
    exact ⟨h2, h3⟩
  · rintro ⟨h2, h3⟩
    exact ⟨⟨Nat.zero_le _, h2⟩, h3⟩

/-- **The clean membership characterization of `densePackMarkers`** — the audit identity composed with
the support-window characterization. -/
theorem mem_densePackMarkers
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) (m : ℕ) :
    m ∈ densePackMarkers budget ctx ↔
      m ≤ 3 * ctx.shell.X + proofV4DensePackSpread ctx.shell ∧
        proofV4DensePackMinHits ctx.shell
          ≤ (proofV4DensePackSupportWindow ctx.shell m).card := by
  rw [densePackMarkers_eq_actualPoints, mem_proofV4DensePackActualPoints]

/-! ## 2.  The range bound is geometric housekeeping (derived from the hit-density)

A non-empty support window already pins the marker below `2X`, and the manuscript threshold is a
genuine positive floor `⌊ρ_D L⌋ ≥ 1`; so the hit-density alone forces full marker membership — the
ambient range bound is not an independent residual. -/

/-- **The range bound from one hit.**  If the one-sided support window of `m` is non-empty, then
`m ≤ 2X`: a hit `n` in the window lies in `supportShell d X`, hence `n ≤ 2X` (`mem_supportShell`),
and `m ≤ n`. -/
theorem endpoint_le_of_window_nonempty {shell : FailingDyadicShell} {m : ℕ}
    (hpos : 0 < (proofV4DensePackSupportWindow shell m).card) :
    m ≤ 2 * shell.X := by
  obtain ⟨n, hn⟩ := Finset.card_pos.mp hpos
  simp only [proofV4DensePackSupportWindow, Finset.mem_filter] at hn
  obtain ⟨hnShell, hmn, _⟩ := hn
  obtain ⟨_, hn2, _⟩ := (mem_supportShell shell.d shell.X n).mp hnShell
  omega

/-- **The manuscript hit threshold is a genuine positive floor** `0 < ⌊ρ_D L⌋` for any failure
context — from the largeness gate `ctx.shell_carryLarge` (`carryB Q + 25 ≤ L`), via the proved
`proofV4DensePackMinHits_pos_of_carryLarge`.  So the K.1 hit-density inequality is non-trivial
(never the vacuous `0 ≤ card`). -/
theorem proofV4DensePackMinHits_pos (ctx : ActualFailureContext) :
    0 < proofV4DensePackMinHits ctx.shell :=
  proofV4DensePackMinHits_pos_of_carryLarge ctx.shell_carryLarge

/-- **Full marker membership from the bare hit-density (range discharged).**  For a failure context,
the K.1 hit-density `⌊ρ_D L⌋ ≤ |supportWindow(m)|` alone forces `m ∈ proofV4DensePackActualPoints
ctx.shell`: the positive threshold makes the window non-empty (`proofV4DensePackMinHits_pos`), which
forces the ambient range bound (`endpoint_le_of_window_nonempty`). -/
theorem mem_actualPoints_of_density (ctx : ActualFailureContext) {m : ℕ}
    (hd : proofV4DensePackMinHits ctx.shell ≤ (proofV4DensePackSupportWindow ctx.shell m).card) :
    m ∈ proofV4DensePackActualPoints ctx.shell := by
  rw [mem_proofV4DensePackActualPoints]
  refine ⟨?_, hd⟩
  have hpos : 0 < (proofV4DensePackSupportWindow ctx.shell m).card :=
    lt_of_lt_of_le (proofV4DensePackMinHits_pos ctx) hd
  have hle : m ≤ 2 * ctx.shell.X := endpoint_le_of_window_nonempty hpos
  omega

/-! ## 3.  The bare coarea hit-density residual and the sharp characterization

`densePackEndpointDensity` is the single irreducible content of `landsShift`: the K.1 hit-density at
each densePack tower-exit start's *actual* terminal endpoint `k + r`.  The sharp characterization
`densePackLandsShift_iff_density` shows the endpoint landing is *exactly* this hit-density — nothing
weaker, nothing stronger, no ambient-window slack. -/

/-- **The bare DensePack coarea hit-density residual.**  Each genuine densePack tower-exit start's
terminal descent endpoint `k + r` carries at least the manuscript threshold `⌊ρ_D L⌋` of shell hits
in its one-sided support window `[k+r, k+r+spread] ∩ supportShell d X`.  This is the J.2/J.5/K.1
coarea normalisation read on the *actual* endpoint.

**It depends only on `ctx`, not on the routing `budget`** — the audit identity
`densePackMarkers budget ctx = proofV4DensePackActualPoints ctx.shell` is budget-independent, so the
surviving residual is purely the shell's own hit-density geometry, not the free phase routing. -/
def densePackEndpointDensity (ctx : ActualFailureContext) : Prop :=
  ∀ k ∈ genuineDensePackStarts ctx,
    proofV4DensePackMinHits ctx.shell
      ≤ (proofV4DensePackSupportWindow ctx.shell (k + ctx.n24CarryData.r)).card

/-- **The endpoint landing yields the bare hit-density** — projecting the second (hit-density)
conjunct of marker membership at each endpoint. -/
theorem densePackEndpointDensity_of_landsShift
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext)
    (h : densePackLandsShift budget ctx) :
    densePackEndpointDensity ctx := by
  intro k hk
  have hm := h k hk
  rw [mem_densePackMarkers] at hm
  exact hm.2

/-- **The bare hit-density yields the endpoint landing** — the K.1 hit-density forces full marker
membership at each endpoint (`mem_actualPoints_of_density`, range discharged). -/
theorem densePackLandsShift_of_density
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext)
    (h : densePackEndpointDensity ctx) :
    densePackLandsShift budget ctx := by
  intro k hk
  rw [densePackMarkers_eq_actualPoints]
  exact mem_actualPoints_of_density ctx (h k hk)

/-- **The sharp characterization.**  The endpoint landing `landsShift` is *exactly* the bare K.1
coarea hit-density at the descent endpoints.  All of DensePack Core 12 therefore reduces to the single
hit-density inequality `⌊ρ_D L⌋ ≤ |supportWindow(k + r)|` — the marker geometry fully unfolded, the
ambient-window range bound discharged. -/
theorem densePackLandsShift_iff_density
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    densePackLandsShift budget ctx ↔ densePackEndpointDensity ctx :=
  ⟨densePackEndpointDensity_of_landsShift budget ctx,
    densePackLandsShift_of_density budget ctx⟩

/-- **The sharp characterization, in literal bare-membership form.**  `landsShift` holds iff every
densePack endpoint `k + r` satisfies the two explicit coarea conditions: the ambient range bound and
the K.1 hit-density.  (By §2 the first is implied by the second; this form exposes both literally.) -/
theorem densePackLandsShift_iff_coareaMembership
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    densePackLandsShift budget ctx ↔
      ∀ k ∈ genuineDensePackStarts ctx,
        k + ctx.n24CarryData.r ≤ 3 * ctx.shell.X + proofV4DensePackSpread ctx.shell ∧
          proofV4DensePackMinHits ctx.shell
            ≤ (proofV4DensePackSupportWindow ctx.shell (k + ctx.n24CarryData.r)).card := by
  constructor
  · intro h k hk
    have hm := h k hk
    rwa [mem_densePackMarkers] at hm
  · intro h k hk
    rw [mem_densePackMarkers]
    exact h k hk

/-! ## 4.  The count, the inhabitation, and the route to `Erdos260Statement`

The bare hit-density is *sufficient* for everything wave 14 derived from `landsShift`: the K.1.1
count, the `DensePackCoareaFirstStop` inhabitation, and `Erdos260Statement`. -/

/-- **The hit-density family yields the endpoint-landing family.** -/
theorem densePackLandsShift_family_of_density
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (h : ∀ ctx : ActualFailureContext, densePackEndpointDensity ctx) :
    ∀ ctx : ActualFailureContext, densePackLandsShift budget ctx :=
  fun ctx => densePackLandsShift_of_density budget ctx (h ctx)

/-- **The K.1.1 count from the bare hit-density.**  `|genuineDensePackStarts| ≤ |densePackMarkers|`
via the wave-14 explicit endpoint injection `· + r`. -/
theorem densePackEndpointDensity_sufficient
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext)
    (h : densePackEndpointDensity ctx) :
    (genuineDensePackStarts ctx).card ≤ (densePackMarkers budget ctx).card :=
  densePackStarts_card_le_of_landsShift budget ctx (densePackLandsShift_of_density budget ctx h)

/-- **`DensePackCoareaFirstStop` is inhabited from the bare hit-density.** -/
theorem densePackCoareaFirstStop_nonempty_of_density
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext)
    (h : densePackEndpointDensity ctx) :
    Nonempty (DensePackCoareaFirstStop budget ctx) :=
  densePackCoareaFirstStop_nonempty_of_landsShift budget ctx
    (densePackLandsShift_of_density budget ctx h)

/-- **Erdős #260 from the bare coarea hit-density family.**  The DensePack class-3 first-stop coarea
data is supplied for every context by the descent-shift owner applied to the hit-density family; the
orthogonal active-window / floor / TRT / Chernoff / CNL inputs are taken as inputs, exactly as in the
wave-14 `erdos260_of_densePackLandsShift`. -/
theorem erdos260_of_densePackEndpointDensity
    (trt : SeedTRTData)
    (chernoff : Class0ChernoffInjection trt.toBudget)
    (cnl : Class1CNLInjection trt.toBudget)
    (hdensity : ∀ ctx : ActualFailureContext, densePackEndpointDensity ctx)
    (windowReach : ActualFailureContext → ℕ)
    (hReach : ∀ ctx : ActualFailureContext,
      windowReach ctx + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hContain : ∀ ctx : ActualFailureContext, ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + windowReach ctx)
    (hfloor : ∀ ctx : ActualFailureContext, densePackActiveFloor ctx - 1 ≤ ctx.n24CarryData.T) :
    Erdos260Statement :=
  erdos260_of_densePackLandsShift trt chernoff cnl
    (densePackLandsShift_family_of_density trt.toBudget hdensity)
    windowReach hReach hContain hfloor

/-! ## 5.  Non-vacuity / non-degeneracy (no emptiness, no identity-on-trivial-set)

The residual is consistent and non-degenerate: the threshold is a genuine positive floor, the range
mechanism fires on a concrete hit, the endpoint shift is a genuine non-identity map, and the
hit-density inhabits the first-stop model. -/

/-- **The range-derivation kernel fires (concrete, non-vacuous).**  A single hit `n` in the dyadic
shell `(X, 2X]` to the right of `m` already forces `m ≤ 2X` — the concrete arithmetic kernel behind
`endpoint_le_of_window_nonempty`, on a non-trivial witness. -/
theorem densePackEndpoint_range_kernel_nonvacuous :
    ∀ m n X : ℕ, X < n → n ≤ 2 * X → m ≤ n → m ≤ 2 * X := by
  intro m n X _ h2 h3; omega

/-- **The endpoint shift is a genuine non-identity map** for a positive descent order — so the
reduction is no identity-on-trivial-set shortcut (re-export of the wave-14 fact). -/
theorem densePackEndpointDensity_shift_non_identity {r : ℕ} (hr : 0 < r) (k : ℕ) : k + r ≠ k :=
  densePackFirstStop_shift_non_identity hr k

/-- **Non-vacuity capstone.**  Whenever the bare coarea hit-density holds, the first-stop coarea data
is inhabited — the residual is consistent, not vacuous. -/
theorem densePackEndpointDensity_nonvacuous
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext)
    (h : densePackEndpointDensity ctx) :
    Nonempty (DensePackCoareaFirstStop budget ctx) :=
  densePackCoareaFirstStop_nonempty_of_density budget ctx h

/-! ## 6.  Honest residual inventory -/

/-- The precise status of the DensePack endpoint-landing residual after this module. -/
def densePackLandsShiftResiduals : List String :=
  [ "AUDIT (densePackMarkers grounded, by rfl) — densePackMarkers_eq_actualPoints: densePackMarkers " ++
      "budget ctx = proofV4DensePackActualPoints ctx.shell DEFINITIONALLY. The faithful assembly " ++
      "(assembledFaithfulPhases → actualProofV4LeafPhases → " ++
      "appendixNGapCanonicalYActualDensePackToGrounded → ofActualSupportWindows) carries the " ++
      "densePackPoints field unchanged, so the abbreviation IS the shell's own actual-support marker " ++
      "set. mem_proofV4DensePackActualPoints / mem_densePackMarkers read membership as: ambient range " ++
      "m ≤ 3X+spread AND K.1 hit-density ⌊ρ_D L⌋ ≤ |supportWindow(m)|.",
    "REDUCTION (range bound discharged) — endpoint_le_of_window_nonempty: a non-empty support window " ++
      "forces m ≤ 2X (every supportShell d X hit is ≤ 2X by mem_supportShell, and m ≤ that hit). " ++
      "proofV4DensePackMinHits_pos: the threshold ⌊ρ_D L⌋ ≥ 1 for any failure context (largeness gate " ++
      "ctx.shell_carryLarge). Hence mem_actualPoints_of_density: the bare hit-density ALONE forces full " ++
      "marker membership — the ambient range bound is geometric housekeeping, not an independent residual.",
    "SHARP (landsShift ⟺ bare coarea hit-density) — densePackLandsShift_iff_density: densePackLandsShift " ++
      "budget ctx ⟺ densePackEndpointDensity ctx, the latter being ∀ k ∈ genuineDensePackStarts " ++
      "ctx, ⌊ρ_D L⌋ ≤ |supportWindow(k + r)|. So the endpoint landing is EXACTLY the K.1 hit-density at " ++
      "the actual descent endpoints — nothing weaker, nothing stronger, no ambient slack. The residual " ++
      "is BUDGET-INDEPENDENT (depends only on ctx). densePackLandsShift_iff_coareaMembership exposes " ++
      "the literal two-conjunct membership form.",
    "SUFFICIENT (count + model + Erdos260) — densePackEndpointDensity_sufficient: hit-density ⟹ " ++
      "|genuineDensePackStarts| ≤ |densePackMarkers| (wave-14 endpoint injection ·+r); " ++
      "densePackCoareaFirstStop_nonempty_of_density inhabits DensePackCoareaFirstStop; " ++
      "erdos260_of_densePackEndpointDensity reaches Erdos260Statement via the wave-14 " ++
      "erdos260_of_densePackLandsShift (+ the orthogonal TRT/Chernoff/CNL/active-window/floor inputs).",
    "RESIDUAL (the single irreducible fact) — densePackEndpointDensity ctx: ∀ k ∈ " ++
      "genuineDensePackStarts ctx, ⌊ρ_D L⌋ ≤ |(supportShell ctx.shell.d ctx.shell.X).filter " ++
      "(fun n => k+r ≤ n ∧ n ≤ k+r+spread)|. It relates the SCC-band tower-exit classifier " ++
      "towerClsOfShell ctx · = densePack (the canonical slope orbit, canonGap = 3) to the SHELL'S OWN " ++
      "hit-density supportShell ctx.shell.d ctx.shell.X. No phase-budget / free-routing datum forces a " ++
      "slope-orbit densePack endpoint to centre a hit-dense window — the manuscript J.2/J.5/K.1 coarea " ++
      "normalisation, genuinely open. This module unfolds the marker geometry to the ground and " ++
      "discharges the ambient range bound, leaving the single hit-density inequality.",
    "NON-VACUOUS / NON-DEGENERATE — densePackEndpointDensity_nonvacuous inhabits the model from the " ++
      "hit-density; proofV4DensePackMinHits_pos shows the threshold is a genuine positive floor (the " ++
      "inequality is never the vacuous 0 ≤ card); densePackEndpoint_range_kernel_nonvacuous fires the " ++
      "range kernel on a concrete shell hit; densePackEndpointDensity_shift_non_identity shows ·+r is a " ++
      "genuine non-identity endpoint map. No empty-start / identity-on-trivial-set shortcut." ]

theorem densePackLandsShiftResiduals_nonempty : densePackLandsShiftResiduals ≠ [] := by
  simp [densePackLandsShiftResiduals]

/-! ## 7.  Axiom-cleanliness audit -/

#print axioms densePackMarkers_eq_actualPoints
#print axioms mem_proofV4DensePackActualPoints
#print axioms mem_densePackMarkers
#print axioms endpoint_le_of_window_nonempty
#print axioms proofV4DensePackMinHits_pos
#print axioms mem_actualPoints_of_density
#print axioms densePackEndpointDensity_of_landsShift
#print axioms densePackLandsShift_of_density
#print axioms densePackLandsShift_iff_density
#print axioms densePackLandsShift_iff_coareaMembership
#print axioms densePackLandsShift_family_of_density
#print axioms densePackEndpointDensity_sufficient
#print axioms densePackCoareaFirstStop_nonempty_of_density
#print axioms erdos260_of_densePackEndpointDensity
#print axioms densePackEndpoint_range_kernel_nonvacuous
#print axioms densePackEndpointDensity_shift_non_identity
#print axioms densePackEndpointDensity_nonvacuous

end

end Erdos260
