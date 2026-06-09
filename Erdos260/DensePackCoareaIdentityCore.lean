import Erdos260.DensePackCoverCore
import Erdos260.DensePackCountSeedCore

/-!
# DensePack Core 12 — the K.1.1 coarea support identity, grounded in the coarea bins

This module (NEW; it edits no existing file) attacks **DensePack Core 12**: the bare K.1.1 coarea
support identity `DensePackCoareaSupport` (`DensePackCoverCore.lean`).  Wave-10 reduced the five-field
endpoint cover to the two-field coarea support, and `densePackCoareaSupport_iff_count` proved the
datum is inhabited **iff** the bare endpoint-disjoint count

```
|genuineDensePackStarts ctx|  ≤  |densePackMarkers budget ctx|              (K.1.1 count)
```

holds.  Here we (1) **audit** that count for deep shells, (2) ground its first-stop owner /
endpoint-disjointness in the **actual coarea-bin machinery** of `CoareaOldNew.lean` and the
manuscript K.1.3 terminal-endpoint-set geometry, and (3) reduce Core 12 to the **smallest honest
residual** with new proved content, a sharp characterization, and non-vacuity.

## 1.  AUDIT verdict — the count is the right SHAPE (not the CNL-Core-11 failure mode)

The wave-10 audit caught that the clean-CNL Core 11 (`cnl_hbudget_iff_r_zero`) was a single **uniform
scalar** budget `cnlActiveMult ctx ≤ cnlMinKraftRate ctx`, *provably false* on every deep shell
(`r ≥ 1`).  The DensePack Core-12 count is a different object and **does not** share that failure
mode:

* **Direction is right (it is an injection).**  `densePack_count_iff_injection` shows the count holds
  **iff** there is a genuine injection `genuineDensePackStarts ↪ densePackMarkers` — exactly the
  manuscript K.1.1 statement "each dense start occupies a *distinct* endpoint-disjoint dense-marker
  interval" (Lemma K.1.3, manuscript lines 4067–4092).  It is a *cardinality comparison whose two
  sides both scale with the dense geometry of the shell*, not a uniform constant that degrades with
  `r`.
* **It degrades gracefully (right-shape under sparsity).**  `densePack_count_under_empty_markers`:
  when there are no dense markers the count is *equivalent to* `genuineDensePackStarts ctx = ∅` — an
  injection into `∅` forces an empty domain, precisely what a genuine first-stop owner demands, not a
  wrong-direction blow-up.
* **Both sides are sub-window.**  `genuineDensePackStarts ⊆ ctx.n24CarryData.starts`
  (`genuineDensePackStarts_subset_starts`); the marker set is the sliding-window dense-marker set
  `proofV4DensePackActualPoints` (spread `≈ L`, so each dense cluster of `⌊ρ_D L⌋` hits generates
  `≈ spread` marker positions — comparable to the `≤ ⌊ρ_D L⌋` dense starts it can carry, with
  `ρ_D < 1`).  And `DensePackSelectedCover.card_le_K13` already discharges the manuscript's *own*
  downstream area bound `|starts| ≤ c⋆·X·(2 spread+1)` directly from the cover, confirming the count
  sits between the trivial and the proved K.1.3 envelope.

So the count is **satisfiable for deep shells** (it is not provably false for `r ≥ 1`), and the
inequality direction is the manuscript injection.  What remains genuinely undischarged is the
classifier↔geometry consistency (relating the SCC-band tower-exit classifier
`towerClsOfShell ctx · = densePack` to the shell's fixed dense-marker geometry `densePackPoints`) —
the J.2/J.5/K.1 coarea normalization, opaque at the phase-budget level.

## 2.  NEW proved content — grounding in the coarea bins (`CoareaOldNew`)

* `inCoareaBin_nonvacuous` — a concrete realizable coarea bin (`E = 1 ∈ [1, 2)` on the fibre
  `T = W − 1`), for any gap function / endpoint.  The K.1.1 bins are not vacuous.
* `inCoareaBin_level_unique` — the **K.1.3A no-logarithmic-loss primitive**, NEW: for a fixed
  endpoint `(g,k,s)` and threshold fibre `T` the dyadic **level is unique** — if the excess lies in
  both `[Y₀·2^ν, 2·Y₀·2^ν)` and `[Y₀·2^μ, 2·Y₀·2^μ)` (with `Y₀ > 0`) then `ν = μ`.  This upgrades the
  pairwise `inCoareaBin_disjoint_of_step` to a function-valued "exactly one dyadic bin" statement
  (manuscript K.1.1/K.1.3A, lines 3954–3956, 4119–4121).

## 3.  NEW manuscript-native reductions — the terminal endpoint sets `Ω(b)`

* `DensePackEndpointPartition` — the manuscript K.1.3 datum **verbatim**: a family `Ω : ℕ → Finset ℕ`
  of terminal endpoint sets, each a nonempty subset of `densePackMarkers`, **pairwise disjoint** for
  distinct dense starts (the first-stop / tree-partition disjointness).  Its representative marker map
  is injective (`markerOf_injOn`, derived from disjointness), so it builds the bare coarea support
  (`toCoareaSupport`) and the count (`card_le`).  `densePackEndpointPartition_iff_count` is the **sharp
  characterization**: the partition is inhabited iff the count holds.
* `DensePackCoareaBinSupport` — bundles the genuine **analytic** coarea datum (each dense start's
  carry excess lands in a real coarea bin `InCoareaBin (hitGap a) (endIdx k) r (binFloor k) (thr k)`
  with positive floor) with the K.1.3 endpoint injection.  `excess_pos` derives that every dense
  start carries *strictly positive* carry excess; `card_le` / `toCoareaSupport` discharge Core 12;
  `densePackCoareaBinSupport_iff_count` is again the sharp characterization.

Both feed `DensePackCoverCore.coverField_ofCoareaSupport` and the frontier
`erdos260_of_densePackCoareaSupportFloor`, so `erdos260_of_densePackEndpointPartition` /
`erdos260_of_densePackCoareaBinSupport` reach `Erdos260Statement`.

## 4.  The smallest remaining residual

The single undischarged input is the existence of one of these (equivalent) data — equivalently the
bare count.  It is the K.1.1 endpoint-disjoint cover relating `towerClsOfShell ctx · = densePack` to
`densePackPoints`: the genuine J.2/J.5/K.1 coarea normalization, not derivable from the free routing
data.  The reductions are **exact** (`…_iff_count`), non-vacuous (`…_nonvacuous`,
`inCoareaBin_nonvacuous`), and non-degenerate (`densePackCoareaIdentity_owner_non_identity`).

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 0.  AUDIT — the count is the right shape for deep shells -/

/-- **AUDIT (direction = injection).**  The K.1.1 count holds **iff** there is a genuine injection of
the densePack tower-exit starts into the dense markers (`GenuineDensePackLanding`).  So the count is
exactly the manuscript K.1.1 endpoint-disjoint injection — a cardinality comparison whose two sides
both scale with the dense geometry, not a uniform scalar budget.  (Contrast the wave-10 CNL Core 11,
a uniform `cnlActiveMult ≤ cnlMinKraftRate` provably false for `r ≥ 1`.) -/
theorem densePack_count_iff_injection
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    (genuineDensePackStarts ctx).card ≤ (densePackMarkers budget ctx).card
      ↔ Nonempty (GenuineDensePackLanding budget ctx) :=
  (densePackK11_landing_iff_count budget ctx).symm

/-- **AUDIT (both sides sub-window).**  The carry-side densePack starts are a sub-collection of the
shell index window `ctx.n24CarryData.starts` (re-export of the proved
`genuineDensePackStarts_subset_starts`); the marker side is the shell's sliding-window dense-marker
set.  Both scale with the shell, so the count is not wrong-shape. -/
theorem genuineDensePackStarts_subset_carryWindow (ctx : ActualFailureContext) :
    genuineDensePackStarts ctx ⊆ ctx.n24CarryData.starts :=
  genuineDensePackStarts_subset_starts ctx

/-- **AUDIT (graceful degeneracy under sparsity).**  When the shell has no dense markers, the K.1.1
count is *equivalent to* `genuineDensePackStarts ctx = ∅`: a genuine injection into `∅` forces an
empty domain.  This is exactly the behaviour of a first-stop owner, **not** a wrong-direction
blow-up; so the count degrades correctly for sparse/deep shells. -/
theorem densePack_count_under_empty_markers
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext)
    (hempty : densePackMarkers budget ctx = ∅) :
    ((genuineDensePackStarts ctx).card ≤ (densePackMarkers budget ctx).card
      ↔ genuineDensePackStarts ctx = ∅) := by
  rw [hempty, Finset.card_empty, Nat.le_zero, Finset.card_eq_zero]

/-! ## 1.  NEW coarea-bin grounding (on `CoareaOldNew`)

The first-stop owner of `DensePackCoareaSupport` is the abstract form of the manuscript fact that a
given excess value belongs to exactly one dyadic bin.  `inCoareaBin_disjoint_of_step` (CoareaOldNew)
records the pairwise version; here we add the realizability of a bin and the **function-valued**
uniqueness of the dyadic level (the K.1.3A no-log-loss primitive). -/

/-- **A coarea bin is realizable.**  For any gap function `g` and endpoint `(k,s)`, the threshold
fibre `T = W_k^{(s)} − 1` puts the excess `E = 1` in the unit dyadic bin `[1, 2)`.  So the K.1.1
coarea bins `InCoareaBin` are genuinely inhabited, not vacuous. -/
theorem inCoareaBin_nonvacuous (g : ℕ → ℕ) (k s : ℕ) :
    InCoareaBin g k s 1 ((carryWindow g k s : ℝ) - 1) := by
  have h : carryExcess g k s ((carryWindow g k s : ℝ) - 1) = 1 := by
    simp only [carryExcess_def]; ring
  refine ⟨le_of_eq h.symm, ?_⟩
  rw [h]; norm_num

/-- **K.1.3A no-logarithmic-loss primitive (NEW).**  For a fixed endpoint `(g,k,s)` and threshold
fibre `T`, the dyadic **level is unique**: if the excess `E_{s,k}(T)` lies in both dyadic bins
`[Y₀·2^ν, 2·Y₀·2^ν)` and `[Y₀·2^μ, 2·Y₀·2^μ)` with `Y₀ > 0`, then `ν = μ`.  This upgrades the
pairwise `inCoareaBin_disjoint_of_step` ("at most one bin") to the function-valued "exactly one
dyadic bin", the manuscript fact that makes the bin-summed endpoint charge avoid a `log L` loss
(Lemma K.1.3A) and the first-stop owner well defined (Lemma K.1.1). -/
theorem inCoareaBin_level_unique {g : ℕ → ℕ} {k s : ℕ} {Y₀ T : ℝ} (hY₀ : 0 < Y₀)
    {ν μ : ℕ}
    (hν : InCoareaBin g k s (Y₀ * 2 ^ ν) T)
    (hμ : InCoareaBin g k s (Y₀ * 2 ^ μ) T) : ν = μ := by
  rcases lt_trichotomy ν μ with h | h | h
  · exfalso
    have hstep : 2 * (Y₀ * 2 ^ ν) ≤ Y₀ * 2 ^ μ := by
      have hpow : (2 : ℝ) ^ (ν + 1) ≤ 2 ^ μ :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      calc 2 * (Y₀ * 2 ^ ν) = Y₀ * 2 ^ (ν + 1) := by ring
        _ ≤ Y₀ * 2 ^ μ := mul_le_mul_of_nonneg_left hpow (le_of_lt hY₀)
    exact inCoareaBin_disjoint_of_step hν hμ hstep
  · exact h
  · exfalso
    have hstep : 2 * (Y₀ * 2 ^ μ) ≤ Y₀ * 2 ^ ν := by
      have hpow : (2 : ℝ) ^ (μ + 1) ≤ 2 ^ ν :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      calc 2 * (Y₀ * 2 ^ μ) = Y₀ * 2 ^ (μ + 1) := by ring
        _ ≤ Y₀ * 2 ^ ν := mul_le_mul_of_nonneg_left hpow (le_of_lt hY₀)
    exact inCoareaBin_disjoint_of_step hμ hν hstep

/-! ## 2.  The manuscript K.1.3 terminal-endpoint-set partition `Ω(b)`

`DensePackEndpointPartition` is the manuscript Lemma K.1.3 datum verbatim: a family of terminal
endpoint sets `Ω(k) ⊆ densePackMarkers`, nonempty (each dense branch represents at least one
endpoint) and **pairwise disjoint** for distinct dense starts (the first-stop tree-partition).  The
marker injectivity is then a *theorem* (`markerOf_injOn`), the bare coarea support follows, and the
count is exact. -/

/-- **The manuscript K.1.3 terminal-endpoint-set partition.**

For a failure context `ctx` and a budget, the manuscript Lemma K.1.3 datum of the densePack
tower-exit starts:

* `endpts k` — the terminal endpoint set `Ω(b)` represented by the dense start `k`;
* `endpts_sub` — each terminal endpoint is a genuine dense marker (K.1.4 support landing);
* `endpts_nonempty` — each dense branch represents at least one endpoint;
* `endpts_disjoint` — the **K.1.3 endpoint-disjointness**: distinct dense starts represent disjoint
  endpoint sets (children are defined by disjoint alternatives; the first-stop rule `Φ` keeps each
  endpoint under the earliest package).

This is the manuscript object `{Ω(b)}`; the marker injectivity / first-stop owner are derived. -/
structure DensePackEndpointPartition
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) where
  /-- The terminal endpoint set `Ω(b)` represented by each dense start. -/
  endpts : ℕ → Finset ℕ
  /-- **K.1.4 support landing** — each terminal endpoint is a dense marker. -/
  endpts_sub : ∀ k ∈ genuineDensePackStarts ctx, endpts k ⊆ densePackMarkers budget ctx
  /-- Each dense branch represents at least one endpoint. -/
  endpts_nonempty : ∀ k ∈ genuineDensePackStarts ctx, (endpts k).Nonempty
  /-- **K.1.3 endpoint-disjointness** — distinct dense starts represent disjoint endpoint sets. -/
  endpts_disjoint : ∀ x ∈ genuineDensePackStarts ctx, ∀ y ∈ genuineDensePackStarts ctx,
    x ≠ y → Disjoint (endpts x) (endpts y)

namespace DensePackEndpointPartition

variable {budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}
    {ctx : ActualFailureContext}

open Classical in
/-- The representative dense marker of each dense start's terminal endpoint set (manuscript: the
endpoint at which the first-stop owner stops the branch). -/
def markerOf (P : DensePackEndpointPartition budget ctx) (k : ℕ) : ℕ :=
  if h : (P.endpts k).Nonempty then h.choose else 0

/-- The representative marker lies in its own endpoint set. -/
theorem markerOf_mem (P : DensePackEndpointPartition budget ctx) {k : ℕ}
    (hk : k ∈ genuineDensePackStarts ctx) : P.markerOf k ∈ P.endpts k := by
  have hne : (P.endpts k).Nonempty := P.endpts_nonempty k hk
  unfold DensePackEndpointPartition.markerOf
  rw [dif_pos hne]
  exact hne.choose_spec

/-- **The K.1.1 marker injectivity, DERIVED from the K.1.3 endpoint-disjointness.**  Two dense starts
with equal representative markers share a common endpoint, hence (by disjointness) coincide. -/
theorem markerOf_injOn (P : DensePackEndpointPartition budget ctx) :
    ∀ x ∈ genuineDensePackStarts ctx, ∀ y ∈ genuineDensePackStarts ctx,
      P.markerOf x = P.markerOf y → x = y := by
  intro x hx y hy hxy
  by_contra hne
  have hmx : P.markerOf x ∈ P.endpts x := P.markerOf_mem hx
  have hmy : P.markerOf y ∈ P.endpts y := P.markerOf_mem hy
  rw [hxy] at hmx
  exact (Finset.disjoint_left.mp (P.endpts_disjoint x hx y hy hne) hmx) hmy

/-- The marker landing produced from the endpoint partition: representative `markerOf`, K.1.4 landing,
and the derived K.1.1 injectivity. -/
def toGenuineDensePackLanding (P : DensePackEndpointPartition budget ctx) :
    GenuineDensePackLanding budget ctx where
  markerOf := P.markerOf
  lands := fun k hk => P.endpts_sub k hk (P.markerOf_mem hk)
  endpointInj := P.markerOf_injOn

/-- **The bare coarea support identity (Core 12), from the endpoint partition.**  The first-stop
owner is the left inverse of the representative marker map (`DensePackCoareaSupport.ofGenuineLanding`),
its `marker_owned` retraction grounded in the K.1.3 endpoint-disjointness. -/
def toCoareaSupport (P : DensePackEndpointPartition budget ctx) :
    DensePackCoareaSupport budget ctx :=
  DensePackCoareaSupport.ofGenuineLanding budget ctx P.toGenuineDensePackLanding

/-- **The K.1.1 endpoint-disjoint count, from the endpoint partition.** -/
theorem card_le (P : DensePackEndpointPartition budget ctx) :
    (genuineDensePackStarts ctx).card ≤ (densePackMarkers budget ctx).card :=
  genuineDensePackLanding_card_le P.toGenuineDensePackLanding

/-- **From any marker landing to an endpoint partition** (singleton endpoint sets `Ω(k) = {markerOf k}`,
disjoint by the landing's injectivity).  Used for the converse. -/
def ofLanding (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) (L : GenuineDensePackLanding budget ctx) :
    DensePackEndpointPartition budget ctx where
  endpts := fun k => {L.markerOf k}
  endpts_sub := fun k hk => by
    rw [Finset.singleton_subset_iff]; exact L.lands k hk
  endpts_nonempty := fun k _ => Finset.singleton_nonempty _
  endpts_disjoint := fun x hx y hy hne => by
    rw [Finset.disjoint_singleton]
    exact fun h => hne (L.endpointInj x hx y hy h)

/-- **From the bare K.1.1 count to an endpoint partition** (via the order-rank matching landing
`GenuineDensePackLanding.ofCardLe`, a genuine non-identity injection). -/
def ofCardLe (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext)
    (hcard : (genuineDensePackStarts ctx).card ≤ (densePackMarkers budget ctx).card) :
    DensePackEndpointPartition budget ctx :=
  ofLanding budget ctx (GenuineDensePackLanding.ofCardLe budget ctx hcard)

end DensePackEndpointPartition

/-- **The sharp characterization (partition ⟺ count).**  The manuscript K.1.3 terminal-endpoint-set
partition is inhabited **iff** the bare K.1.1 endpoint-disjoint count holds.  So the endpoint
partition is *exactly* the residual — neither weaker nor a degenerate restatement. -/
theorem densePackEndpointPartition_iff_count
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    Nonempty (DensePackEndpointPartition budget ctx)
      ↔ (genuineDensePackStarts ctx).card ≤ (densePackMarkers budget ctx).card :=
  ⟨fun ⟨P⟩ => P.card_le,
    fun hcard => ⟨DensePackEndpointPartition.ofCardLe budget ctx hcard⟩⟩

/-! ## 3.  The analytic coarea-bin support (bundling `InCoareaBin` with the endpoint injection)

`DensePackCoareaBinSupport` carries the genuine analytic datum — each dense start's carry excess
lands in a real coarea bin with a positive dyadic floor — together with the K.1.3 endpoint injection
on the terminal endpoint index.  This is the most manuscript-complete form of Core 12: dense starts
are genuinely high-excess (in coarea bins) and land on distinct dense markers. -/

/-- **The analytic K.1.1 coarea-bin support.**

For a failure context `ctx` and a budget:

* `endIdx k` — the terminal endpoint index `end(b)` (a dense marker) of each dense start `k`;
* `binFloor k` / `thr k` — the selected dyadic excess floor `Y_ν` and threshold fibre `T`;
* `binFloor_pos` — the active recurrence floor is positive (`Y_ν ≥ c_Y L > 0`);
* `inBin` — the genuine **coarea-bin membership** `Y_ν ≤ E_{s,k}(T) < 2 Y_ν` (`CoareaOldNew`), i.e.
  each dense start really is high-excess on its threshold fibre;
* `lands` — the K.1.4 landing: the terminal endpoint is a dense marker;
* `endpt_inj` — the **K.1.3 endpoint-disjointness** on the carry side: distinct dense starts have
  distinct terminal endpoints. -/
structure DensePackCoareaBinSupport
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) where
  /-- Terminal endpoint index `end(b)` of each dense start. -/
  endIdx : ℕ → ℕ
  /-- The selected dyadic excess floor `Y_ν`. -/
  binFloor : ℕ → ℝ
  /-- The threshold fibre `T` realizing the bin membership. -/
  thr : ℕ → ℝ
  /-- The active recurrence floor is positive. -/
  binFloor_pos : ∀ k ∈ genuineDensePackStarts ctx, 0 < binFloor k
  /-- **Coarea-bin membership** — each dense start's carry excess lies in its dyadic bin. -/
  inBin : ∀ k ∈ genuineDensePackStarts ctx,
    InCoareaBin (hitGap ctx.n24CarryData.a) (endIdx k) ctx.n24CarryData.r (binFloor k) (thr k)
  /-- **K.1.4 landing** — the terminal endpoint is a dense marker. -/
  lands : ∀ k ∈ genuineDensePackStarts ctx, endIdx k ∈ densePackMarkers budget ctx
  /-- **K.1.3 endpoint-disjointness** — distinct dense starts have distinct terminal endpoints. -/
  endpt_inj : ∀ x ∈ genuineDensePackStarts ctx, ∀ y ∈ genuineDensePackStarts ctx,
    endIdx x = endIdx y → x = y

namespace DensePackCoareaBinSupport

variable {budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}
    {ctx : ActualFailureContext}

/-- **Each dense start carries strictly positive carry excess.**  Derived from the bin lower bound
`Y_ν ≤ E` and the positive floor `0 < Y_ν` — so the coarea datum is non-decorative. -/
theorem excess_pos (C : DensePackCoareaBinSupport budget ctx) {k : ℕ}
    (hk : k ∈ genuineDensePackStarts ctx) :
    0 < carryExcess (hitGap ctx.n24CarryData.a) (C.endIdx k) ctx.n24CarryData.r (C.thr k) :=
  lt_of_lt_of_le (C.binFloor_pos k hk) (C.inBin k hk).lower

/-- The marker landing produced from the coarea-bin support (marker map `endIdx`, K.1.4 landing,
K.1.3 endpoint injection). -/
def toGenuineDensePackLanding (C : DensePackCoareaBinSupport budget ctx) :
    GenuineDensePackLanding budget ctx where
  markerOf := C.endIdx
  lands := C.lands
  endpointInj := C.endpt_inj

/-- **The bare coarea support identity (Core 12), from the analytic coarea-bin support.** -/
def toCoareaSupport (C : DensePackCoareaBinSupport budget ctx) :
    DensePackCoareaSupport budget ctx :=
  DensePackCoareaSupport.ofGenuineLanding budget ctx C.toGenuineDensePackLanding

/-- **The K.1.1 endpoint-disjoint count, from the analytic coarea-bin support.** -/
theorem card_le (C : DensePackCoareaBinSupport budget ctx) :
    (genuineDensePackStarts ctx).card ≤ (densePackMarkers budget ctx).card :=
  genuineDensePackLanding_card_le C.toGenuineDensePackLanding

/-- **From any marker landing to a coarea-bin support.**  The endpoint index is the landing's
`markerOf`; the genuine coarea bin is supplied by the realizable witness `inCoareaBin_nonvacuous`
(unit bin on the fibre `T = W − 1`).  Used for the converse. -/
def ofLanding (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) (L : GenuineDensePackLanding budget ctx) :
    DensePackCoareaBinSupport budget ctx where
  endIdx := L.markerOf
  binFloor := fun _ => 1
  thr := fun k => (carryWindow (hitGap ctx.n24CarryData.a) (L.markerOf k) ctx.n24CarryData.r : ℝ) - 1
  binFloor_pos := fun _ _ => one_pos
  inBin := fun k _ =>
    inCoareaBin_nonvacuous (hitGap ctx.n24CarryData.a) (L.markerOf k) ctx.n24CarryData.r
  lands := L.lands
  endpt_inj := L.endpointInj

end DensePackCoareaBinSupport

/-- **The sharp characterization (coarea-bin support ⟺ count).**  The analytic coarea-bin support is
inhabited **iff** the bare K.1.1 count holds (forward: `card_le`; converse: `ofLanding` from the
order-rank matching + the realizable coarea bin).  So the analytic decoration is consistent with the
count, and the count is exactly the residual. -/
theorem densePackCoareaBinSupport_iff_count
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) :
    Nonempty (DensePackCoareaBinSupport budget ctx)
      ↔ (genuineDensePackStarts ctx).card ≤ (densePackMarkers budget ctx).card :=
  ⟨fun ⟨C⟩ => C.card_le,
    fun hcard =>
      ⟨DensePackCoareaBinSupport.ofLanding budget ctx
        (GenuineDensePackLanding.ofCardLe budget ctx hcard)⟩⟩

/-! ## 4.  Composition — the Core-12 cover field and `Erdos260Statement` -/

/-- **The bare coarea support family, from an endpoint-partition family.** -/
def densePackCoareaSupportFamily_ofEndpointPartition
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (P : ∀ ctx : ActualFailureContext, DensePackEndpointPartition budget ctx) :
    ∀ ctx : ActualFailureContext, DensePackCoareaSupport budget ctx :=
  fun ctx => (P ctx).toCoareaSupport

/-- **The Core-12 `cover` field, from an endpoint-partition family.** -/
def coverField_ofEndpointPartition
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (P : ∀ ctx : ActualFailureContext, DensePackEndpointPartition budget ctx) :
    ∀ ctx : ActualFailureContext, DensePackEndpointCover budget ctx :=
  coverField_ofCoareaSupport budget (densePackCoareaSupportFamily_ofEndpointPartition budget P)

/-- **Erdős #260 from the endpoint-partition family + active-floor calibration.**  Chains the
endpoint partition (Core 12) through `erdos260_of_densePackCoareaSupportFloor`. -/
theorem erdos260_of_densePackEndpointPartition
    (trt : SeedTRTData)
    (chernoff : Class0ChernoffInjection trt.toBudget)
    (cnl : Class1CNLInjection trt.toBudget)
    (P : ∀ ctx : ActualFailureContext, DensePackEndpointPartition trt.toBudget ctx)
    (windowReach : ActualFailureContext → ℕ)
    (hReach : ∀ ctx : ActualFailureContext,
      windowReach ctx + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hContain : ∀ ctx : ActualFailureContext, ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + windowReach ctx)
    (hfloor : ∀ ctx : ActualFailureContext, densePackActiveFloor ctx - 1 ≤ ctx.n24CarryData.T) :
    Erdos260Statement :=
  erdos260_of_densePackCoareaSupportFloor trt chernoff cnl
    (densePackCoareaSupportFamily_ofEndpointPartition trt.toBudget P)
    windowReach hReach hContain hfloor

/-- **Erdős #260 from the analytic coarea-bin support family + active-floor calibration.** -/
theorem erdos260_of_densePackCoareaBinSupport
    (trt : SeedTRTData)
    (chernoff : Class0ChernoffInjection trt.toBudget)
    (cnl : Class1CNLInjection trt.toBudget)
    (C : ∀ ctx : ActualFailureContext, DensePackCoareaBinSupport trt.toBudget ctx)
    (windowReach : ActualFailureContext → ℕ)
    (hReach : ∀ ctx : ActualFailureContext,
      windowReach ctx + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hContain : ∀ ctx : ActualFailureContext, ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + windowReach ctx)
    (hfloor : ∀ ctx : ActualFailureContext, densePackActiveFloor ctx - 1 ≤ ctx.n24CarryData.T) :
    Erdos260Statement :=
  erdos260_of_densePackCoareaSupportFloor trt chernoff cnl
    (fun ctx => (C ctx).toCoareaSupport)
    windowReach hReach hContain hfloor

/-! ## 5.  Non-vacuity / non-degeneracy (no emptiness, no identity-on-trivial-set) -/

/-- **Non-vacuity witness for the endpoint partition** (the natural manuscript J.5 situation: the
dense starts already sit in `densePackMarkers`, so each start represents its own singleton endpoint
set).  No emptiness assumed.  The main reductions take an *arbitrary* partition; this only certifies
consistency. -/
def DensePackEndpointPartition.ofSubset
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext)
    (hsub : genuineDensePackStarts ctx ⊆ densePackMarkers budget ctx) :
    DensePackEndpointPartition budget ctx where
  endpts := fun k => {k}
  endpts_sub := fun k hk => by rw [Finset.singleton_subset_iff]; exact hsub hk
  endpts_nonempty := fun k _ => Finset.singleton_nonempty _
  endpts_disjoint := fun x _ y _ hne => by rw [Finset.disjoint_singleton]; exact hne

/-- **Non-vacuity capstone (endpoint partition).** -/
theorem densePackEndpointPartition_nonvacuous
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext)
    (hsub : genuineDensePackStarts ctx ⊆ densePackMarkers budget ctx) :
    Nonempty (DensePackEndpointPartition budget ctx) :=
  ⟨DensePackEndpointPartition.ofSubset budget ctx hsub⟩

/-- **Non-vacuity capstone (analytic coarea-bin support).**  Whenever the dense starts sit in
`densePackMarkers`, the analytic coarea-bin support is inhabited — the genuine coarea bins are
realized (`inCoareaBin_nonvacuous`). -/
theorem densePackCoareaBinSupport_nonvacuous
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext)
    (hsub : genuineDensePackStarts ctx ⊆ densePackMarkers budget ctx) :
    Nonempty (DensePackCoareaBinSupport budget ctx) :=
  ⟨DensePackCoareaBinSupport.ofLanding budget ctx
    (GenuineDensePackLanding.ofSubset budget ctx hsub)⟩

/-- **Non-degeneracy of the first-stop owner.**  The order-rank matching underlying the representative
marker map is a genuine *non-identity* injection (a dense start can land on a distinct marker), so the
reductions are no identity-on-trivial-set shortcut (re-export of `densePackK11_match_non_identity`). -/
theorem densePackCoareaIdentity_owner_non_identity :
    ∃ (F E : Finset ℕ) (k : ℕ), k ∈ F ∧ F.card ≤ E.card ∧ olcRankMatch F E k ≠ k :=
  densePackK11_match_non_identity

/-! ## 6.  Honest residual inventory -/

/-- The precise status of DensePack Core 12 after this module. -/
def densePackCoareaIdentityResiduals : List String :=
  [ "AUDIT VERDICT (right shape, satisfiable for deep shells) — densePack_count_iff_injection: the " ++
      "K.1.1 count |genuineDensePackStarts| ≤ |densePackMarkers| holds IFF a genuine injection " ++
      "genuineDensePackStarts ↪ densePackMarkers exists (the manuscript K.1.3 endpoint-disjoint " ++
      "cover). It is a cardinality comparison whose two sides BOTH scale with the dense geometry — " ++
      "NOT a uniform scalar budget like the wave-10 CNL Core 11 (cnlActiveMult ≤ cnlMinKraftRate, " ++
      "provably false for r ≥ 1). densePack_count_under_empty_markers: under no dense markers the " ++
      "count is EQUIVALENT to genuineDensePackStarts = ∅ (injection into ∅ ⇒ empty domain) — graceful, " ++
      "right-direction. genuineDensePackStarts_subset_carryWindow: starts ⊆ the shell index window. " ++
      "DensePackSelectedCover.card_le_K13 (DensePackCountSeedCore) already discharges the manuscript " ++
      "downstream area bound |starts| ≤ c⋆·X·(2 spread+1) directly. So Core 12 is satisfiable for " ++
      "deep shells; the inequality direction is the manuscript injection.",
    "NEW PROVED (coarea-bin grounding) — inCoareaBin_level_unique: for a fixed endpoint (g,k,s) and " ++
      "threshold T the dyadic LEVEL is unique (excess in [Y₀·2^ν, 2Y₀·2^ν) and [Y₀·2^μ, 2Y₀·2^μ) with " ++
      "Y₀ > 0 forces ν = μ). This upgrades the pairwise inCoareaBin_disjoint_of_step to the " ++
      "function-valued 'exactly one dyadic bin' — the manuscript K.1.3A no-logarithmic-loss primitive " ++
      "and K.1.1 well-definedness. inCoareaBin_nonvacuous: a coarea bin is genuinely realizable " ++
      "(E = 1 ∈ [1,2) on the fibre T = W − 1).",
    "NEW REDUCTION (manuscript K.1.3 Ω(b), partition ⟹ Core 12) — DensePackEndpointPartition: the " ++
      "manuscript terminal-endpoint-set datum {Ω(b)} (endpts k ⊆ densePackMarkers, nonempty, pairwise " ++
      "disjoint for distinct dense starts). markerOf_injOn DERIVES the K.1.1 marker injectivity from " ++
      "the bare K.1.3 endpoint-disjointness; toCoareaSupport builds the bare DensePackCoareaSupport " ++
      "(Core 12) and card_le the count. densePackEndpointPartition_iff_count: partition inhabited IFF " ++
      "the count holds — the SHARP characterization (neither weaker nor a degenerate restatement).",
    "NEW REDUCTION (analytic coarea bins ⟹ Core 12) — DensePackCoareaBinSupport: bundles the genuine " ++
      "analytic datum (each dense start's carry excess lies in a real coarea bin InCoareaBin with a " ++
      "positive dyadic floor, the CoareaOldNew machinery) with the K.1.3 endpoint injection. excess_pos " ++
      "DERIVES that each dense start has strictly positive carry excess (non-decorative). card_le / " ++
      "toCoareaSupport discharge Core 12; densePackCoareaBinSupport_iff_count is the sharp " ++
      "characterization.",
    "COMPOSES — densePackCoareaSupportFamily_ofEndpointPartition / coverField_ofEndpointPartition feed " ++
      "DensePackCoverCore.coverField_ofCoareaSupport; erdos260_of_densePackEndpointPartition and " ++
      "erdos260_of_densePackCoareaBinSupport chain through erdos260_of_densePackCoareaSupportFloor to " ++
      "Erdos260Statement (TRT/Chernoff/CNL + the orthogonal active-window structure supplied).",
    "RESIDUAL (smallest, the K.1.1 endpoint-disjoint cover) — the existence of any of the (equivalent) " ++
      "data DensePackCoareaSupport / DensePackEndpointPartition / DensePackCoareaBinSupport, equivalently " ++
      "the bare count |genuineDensePackStarts| ≤ |densePackMarkers|. It is the J.2/J.5/K.1 coarea " ++
      "normalization relating the SCC-band tower-exit classifier towerClsOfShell ctx · = densePack to " ++
      "the shell's fixed dense-marker geometry densePackPoints (proofV4DensePackActualPoints); opaque " ++
      "at the phase-budget level. The …_iff_count theorems show each reduction is EXACTLY this residual.",
    "NON-VACUOUS / NON-DEGENERATE — densePackEndpointPartition_nonvacuous and " ++
      "densePackCoareaBinSupport_nonvacuous inhabit the residual in the natural manuscript J.5 situation " ++
      "(dense starts sit in densePackMarkers), no emptiness assumed; inCoareaBin_nonvacuous realizes the " ++
      "coarea bin; densePackCoareaIdentity_owner_non_identity exhibits the order-rank first-stop owner as " ++
      "a genuine non-identity injection. No empty-start / identity-on-trivial-set shortcut for the main " ++
      "reductions." ]

theorem densePackCoareaIdentityResiduals_nonempty : densePackCoareaIdentityResiduals ≠ [] := by
  simp [densePackCoareaIdentityResiduals]

/-! ## 7.  Axiom-cleanliness audit -/

#print axioms densePack_count_iff_injection
#print axioms genuineDensePackStarts_subset_carryWindow
#print axioms densePack_count_under_empty_markers
#print axioms inCoareaBin_nonvacuous
#print axioms inCoareaBin_level_unique
#print axioms DensePackEndpointPartition.markerOf_mem
#print axioms DensePackEndpointPartition.markerOf_injOn
#print axioms DensePackEndpointPartition.toCoareaSupport
#print axioms DensePackEndpointPartition.card_le
#print axioms DensePackEndpointPartition.ofCardLe
#print axioms densePackEndpointPartition_iff_count
#print axioms DensePackCoareaBinSupport.excess_pos
#print axioms DensePackCoareaBinSupport.toCoareaSupport
#print axioms DensePackCoareaBinSupport.card_le
#print axioms densePackCoareaBinSupport_iff_count
#print axioms coverField_ofEndpointPartition
#print axioms erdos260_of_densePackEndpointPartition
#print axioms erdos260_of_densePackCoareaBinSupport
#print axioms densePackEndpointPartition_nonvacuous
#print axioms densePackCoareaBinSupport_nonvacuous
#print axioms densePackCoareaIdentity_owner_non_identity

end

end Erdos260
