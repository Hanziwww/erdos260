import Erdos260.TowerShallowDeepUnconditional
import Erdos260.ReturnAnchoredUnconditional

/-!
# Tower / Class 2 — the class-2 routing pin and the SHARP deep-shell count-bound reduction

This module (NEW; it edits no existing file) settles the class-2 routing pin and reduces the
deep-shell Tower residual `Class2DeepShellResidual` (of `TowerShallowDeepUnconditional.lean`)
to its EXACT combinatorial frontier — a single `ℕ` counting inequality per deep shell — with
proved bridges in BOTH directions.

## 1.  The class-2 routing pin (`mem_class2Fibre_iff`), settled

Mirroring the proved class-1 (`mem_class1Fibre_iff`, gap-window EQUALITY `64·gW = 129L + 64`,
band `canonGap = 4`) and class-4 (`mem_class4Fibre_iff`, floor `129L + 64 ≤ 64·gW`, band
`canonGap = 2`) characterizations: the genuine route reaches class `2` exactly through the
`cnlTail` catch-all (`canonGap q K_k = 4`) with a semiperiodic-band window excess
(`returnCls = 1`, no large run).  With the pinned `T = 2L + 1`, `Y = L/64` this is the
**strict two-sided gap-window band** (an inequality band, NOT an equality):

`k ∈ fibre₂  ⟺  k ∈ starts  ∧  129L + 64 < 64·gapWindow(k) < 130L + 64  ∧  canonGap q K_k = 4`.

(Class 1 sits at the LEFT endpoint `64·gW = 129L+64`; class 4 fills `64·gW ≥ 130L+64` after the
band-2 exit; class 2 is exactly the open band between them.)  Telescoped hit-position form:
`129L + 64 < 64·(a(k+r+1) − a(k)) < 130L + 64` (`class2Fibre_hitPosition_band`).

## 2.  The deep-shell residual IS a counting inequality (both directions proved)

`Class2DeepShellWindowData ctx` (windows + landing + Hall marginal at block size
`m₀ = towerSparsityBlock`) is **inhabited iff**

`m₀ · #fibre₂ ≤ K = |supportShell d X|`   (`class2DeepShellWindowData_iff_countBound`).

* (⇐) **the rank-block construction** (`class2DeepShellWindowData_ofCountBound`): sort the
  genuine fibre and give its `j`-th element the hit-index block
  `[i₀ + j·m₀, i₀ + (j+1)·m₀)`.  The blocks are pairwise disjoint with card `m₀`, so the Hall
  marginal holds with EQUALITY for every `S` (`card_biUnion`), and the count bound puts every
  block inside the genuine start window, where the closed landing lemma `towerSD_window_lands`
  (via `ofRangeWindows`) discharges `hlands`.
* (⇒) **necessity** (`countBound_of_class2DeepShellWindowData`): any window family's landing
  forces `⋃ W ⊆ [i₀, i₀+K)` — a hit index landing in the shell must lie in the start window
  (`hitIndex_mem_window_of_mem_supportShell`, from `lt_firstIndexAbove` +
  `a_firstIndexAbove_add_card_gt`) — so Hall at `S = fibre₂` gives `m₀·#fibre₂ ≤ K`.

Hence the capstone field is EQUIVALENT to the named `Prop`

`Class2DeepShellCountBound : ∀ ctx, 328965 < L → m₀ · #fibre₂ ≤ K`

(`towerDeepResidual_ofCountBound` / `countBound_ofTowerDeepResidual`), and
`p9V3TowerCount_ofCountBound` feeds the exact `P9V3RunResidual.towerCount` /
`Erdos260SixAtomResidual.towerDeep` shape from the counting inequality alone.

This reduction is STRICTLY SHARPER than a start-spacing residual: spacing `≥ m₀` between
consecutive class-2 starts does NOT suffice for the Hall data (e.g. `K = 3`, `m₀ = 2`, starts
`{i₀, i₀+2}`: spacing 2 but `m₀·t = 4 > 3 = K`, so no landing window family can satisfy the
marginal) — the count bound is the exact obstruction, and it is what the rank-block
construction consumes.

## 3.  Unconditional subregime closures (genuine, non-fabricated)

* `class2Fibre_empty_of_modulus_lt_nine` → `class2DeepShellWindowData_of_modulus_lt_nine`:
  on every shell with AP-subfibre modulus `q < 9` the band-4 window `8K ≤ q < 16K` is
  unsatisfiable, the fibre is PROVABLY empty, and the full deep window datum follows.
* `class2DeepShellWindowData_of_card_le_one`: `m₀ ≤ r + 1 ≤ K` always
  (`towerSparsityBlock_le_shellWidth`), so any shell with `#fibre₂ ≤ 1` is closed.
* **The orbit run rigidity** (`band4_run_forces_pow_lt` / `class2Fibre_run_forces_pow_lt`):
  a run `k, k+1, …, k+s` of class-2 starts forces `15·K_k = q` (the exact `1/15` fixed point
  of the band-4 step `K ↦ 16K − q`, possible only when `15 ∣ q`) **or** `16^s < q`.  So on
  every shell with `15 ∤ q` (in fact whenever the orbit is off the fixed point) class-2 runs
  have length `≤ log₁₆ q`, and consecutive pairs are pinned into the 16×-narrower band
  `17q < 256·K_k ≤ …` (`class2Fibre_pair_orbit_band`).

## 4.  Honesty — why the count bound itself is NOT closed here

The two pins are mutually unconstrained in the formalization: the gap-window band constrains
the HIT sequence `a`, the band-4 pin constrains the slope ORBIT, and no unconditional bridge
ties `hitGap a` to `canonGap` along the orbit (the zero-run matching `hzero` of
`carry_tracks_slopeOrbit` is the explicit §25.1/E.2–E.4 residual, never faked).  Within the
formal model: (i) `15 ∣ q` shells admit unbounded band-4 runs (the `1/15` fixed point), and
(ii) the band, an OPEN interval of length `L` in `64·gapWindow`, is satisfiable on arbitrarily
long blocks of consecutive starts by locally `≈ 2L/(r+1)`-dense hit patterns inside a globally
`< c₀X`-sparse shell.  Interval counting cannot beat this: disjointifying descent windows
yields only `#fibre₂ ≲ (r+1)·X/(2L) ≈ (3κL/2)·(K/m₀)/K · …` — a factor `≈ 3κL/2 ≈ 32` above
the demanded `K/m₀` at the failure cap `K < c₀X = κX/64`.  The genuinely missing input is the
manuscript's per-start ownership (§25.1 semiperiodic matching + K.2 Fine–Wilf), exactly as the
`TowerShallowDeepUnconditional` audit records.  No degenerate witness is fabricated.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

namespace Erdos260

open Finset

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 1.  The strict window-excess band in exact `ℕ` form

With the pinned `T = 2L + 1` (`cnlMulti_n24_T_eq`) and `Y = L/64` (`n24CarryData_Y_eq_div`),
the strict high-excess floor and the strict `2Y` ceiling become the two-sided `ℕ` band
`129L + 64 < 64·gapWindow < 130L + 64`. -/

/-- **The strict high-excess floor in `ℕ` form**: `Y < windowExcess ⟺ 129L + 64 < 64·gapWindow`
(the strict twin of the proved `Y_le_windowExcess_iff_gapWindow`). -/
theorem class2_Y_lt_windowExcess_iff_gapWindow (ctx : ActualFailureContext) (k : ℕ) :
    ctx.n24CarryData.Y
        < windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
      ↔ 129 * shellLadderDepth ctx + 64
          < 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r := by
  rw [cnlMulti_n24_T_eq, n24CarryData_Y_eq_div]
  have hL : (28 : ℝ) ≤ ((shellLadderDepth ctx : ℕ) : ℝ) := by
    exact_mod_cast shellLadderDepth_ge ctx
  unfold windowExcess positivePart
  constructor
  · intro h
    by_cases hle : ((gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r : ℕ) : ℝ)
        - (2 * ((shellLadderDepth ctx : ℕ) : ℝ) + 1) ≤ 0
    · rw [max_eq_right hle] at h
      linarith
    · rw [max_eq_left (not_le.mp hle).le] at h
      have hreal : (129 : ℝ) * ((shellLadderDepth ctx : ℕ) : ℝ) + 64
          < 64 * ((gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r : ℕ) : ℝ) := by
        linarith
      exact_mod_cast hreal
  · intro h
    have hreal : (129 : ℝ) * ((shellLadderDepth ctx : ℕ) : ℝ) + 64
        < 64 * ((gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r : ℕ) : ℝ) := by
      exact_mod_cast h
    rw [max_eq_left (by linarith)]
    linarith

/-- **The strict `2Y` ceiling in `ℕ` form**: `windowExcess < 2Y ⟺ 64·gapWindow < 130L + 64`. -/
theorem class2_windowExcess_lt_twoY_iff_gapWindow (ctx : ActualFailureContext) (k : ℕ) :
    windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
        < 2 * ctx.n24CarryData.Y
      ↔ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
          < 130 * shellLadderDepth ctx + 64 := by
  rw [cnlMulti_n24_T_eq, n24CarryData_Y_eq_div]
  have hL : (28 : ℝ) ≤ ((shellLadderDepth ctx : ℕ) : ℝ) := by
    exact_mod_cast shellLadderDepth_ge ctx
  unfold windowExcess positivePart
  constructor
  · intro h
    by_cases hle : ((gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r : ℕ) : ℝ)
        - (2 * ((shellLadderDepth ctx : ℕ) : ℝ) + 1) ≤ 0
    · have hreal : 64 * ((gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r : ℕ) : ℝ)
          < 130 * ((shellLadderDepth ctx : ℕ) : ℝ) + 64 := by
        linarith
      exact_mod_cast hreal
    · rw [max_eq_left (not_le.mp hle).le] at h
      have hreal : 64 * ((gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r : ℕ) : ℝ)
          < 130 * ((shellLadderDepth ctx : ℕ) : ℝ) + 64 := by
        linarith
      exact_mod_cast hreal
  · intro h
    have hreal : 64 * ((gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r : ℕ) : ℝ)
        < 130 * ((shellLadderDepth ctx : ℕ) : ℝ) + 64 := by
      exact_mod_cast h
    by_cases hle : ((gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r : ℕ) : ℝ)
        - (2 * ((shellLadderDepth ctx : ℕ) : ℝ) + 1) ≤ 0
    · rw [max_eq_right hle]
      linarith
    · rw [max_eq_left (not_le.mp hle).le]
      linarith

/-- **The K.4 return band classifier hits `1` exactly on the open-closed band
`Y < windowExcess ≤ 2Y`** (the semiperiodic-recurrence band; the `returnCls = 0` twin is the
proved `returnCls_eq_zero_iff`). -/
theorem returnCls_eq_one_iff (ctx : ActualFailureContext) (k : ℕ) :
    returnCls ctx k = 1
      ↔ ctx.n24CarryData.Y
            < windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
          ∧ windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
            ≤ 2 * ctx.n24CarryData.Y := by
  unfold returnCls
  split_ifs with h1 h2
  · exact iff_of_false (by decide) (fun hc => absurd h1 (not_le.mpr hc.1))
  · exact iff_of_true rfl ⟨not_le.mp h1, h2⟩
  · exact iff_of_false (by decide) (fun hc => h2 hc.2)

/-! ## Part 2.  The sharp class-2 membership characterization (the routing pin) -/

/-- **The sharp class-2 membership characterization** (the class-2 analogue of
`mem_class1Fibre_iff` / `mem_class4Fibre_iff`): `k ∈ fibre₂` iff `k` is a carry-window start
whose gap window sits in the OPEN band `129L + 64 < 64·gapWindow < 130L + 64` (the strict
high-excess floor and the strict no-large-run ceiling) and whose slope-orbit canonical-gap
band index is EXACTLY `4` (the `cnlTail` window).  Class 1 is the left endpoint
(`64·gW = 129L + 64`); class 4 (band 2) carries `64·gW ≥ 129L + 64` with no upper bound. -/
theorem mem_class2Fibre_iff (ctx : ActualFailureContext) (k : ℕ) :
    k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2
      ↔ k ∈ ctx.n24CarryData.starts
        ∧ 129 * shellLadderDepth ctx + 64
            < 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
            < 130 * shellLadderDepth ctx + 64
        ∧ canonGap (class1SlopeDatum ctx).q
            (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 4 := by
  constructor
  · intro hk
    have hhigh := mem_highExcessStarts.mp (Finset.mem_filter.mp hk).1
    have hroute : genuineChargeRoute ctx k = 2 := (Finset.mem_filter.mp hk).2
    obtain ⟨htower, hrun, hret⟩ := (genuineChargeRoute_eq_two_iff ctx k).mp hroute
    have hband : canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 4 := by
      rw [towerClsOfShell_eq_band] at htower
      exact (towerExitClassOfGap_eq_cnlTail_iff _).mp htower
    have hk0 : k ≠ 0 := fun h0 => zero_notMem_n24Starts ctx (h0 ▸ hhigh.1)
    have hYlt : ctx.n24CarryData.Y
        < windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T :=
      ((returnCls_eq_one_iff ctx k).mp hret).1
    have hlt2Y : windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ctx.n24CarryData.T < 2 * ctx.n24CarryData.Y := by
      by_contra hcon
      rw [not_lt] at hcon
      exact hrun (by unfold runClsOfShell; rw [if_neg hk0, if_pos hcon])
    exact ⟨hhigh.1, (class2_Y_lt_windowExcess_iff_gapWindow ctx k).mp hYlt,
      (class2_windowExcess_lt_twoY_iff_gapWindow ctx k).mp hlt2Y, hband⟩
  · rintro ⟨hstart, hgw1, hgw2, hband⟩
    have hYlt := (class2_Y_lt_windowExcess_iff_gapWindow ctx k).mpr hgw1
    have hlt2Y := (class2_windowExcess_lt_twoY_iff_gapWindow ctx k).mpr hgw2
    have hk0 : k ≠ 0 := fun h0 => zero_notMem_n24Starts ctx (h0 ▸ hstart)
    have htower : towerClsOfShell ctx k = TowerExitClass.cnlTail := by
      rw [towerClsOfShell_eq_band, hband]
      rfl
    have hrun : runClsOfShell ctx k ≠ 1 := by
      unfold runClsOfShell
      rw [if_neg hk0, if_neg (not_le.mpr hlt2Y)]
      decide
    have hret : returnCls ctx k = 1 :=
      (returnCls_eq_one_iff ctx k).mpr ⟨hYlt, hlt2Y.le⟩
    exact Finset.mem_filter.mpr
      ⟨mem_highExcessStarts.mpr ⟨hstart, hYlt.le⟩,
        (genuineChargeRoute_eq_two_iff ctx k).mpr ⟨htower, hrun, hret⟩⟩

/-- **The class-2 fibre IS the doubly-pinned window filter** (irreducible arithmetic form). -/
theorem class2Fibre_eq_pinnedFilter (ctx : ActualFailureContext) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2
      = ctx.n24CarryData.starts.filter (fun k =>
          (129 * shellLadderDepth ctx + 64
              < 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
            ∧ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
              < 130 * shellLadderDepth ctx + 64)
            ∧ canonGap (class1SlopeDatum ctx).q
                (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 4) := by
  ext k
  rw [Finset.mem_filter, mem_class2Fibre_iff]
  tauto

/-- **The class-2 gap-window band pin** (forward form): every class-2 routed start has its
`(r+1)`-step gap window in the open band `(129L + 64)/64 < gapWindow < (130L + 64)/64`. -/
theorem class2Fibre_gapWindow_band (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2) :
    129 * shellLadderDepth ctx + 64
        < 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
      ∧ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        < 130 * shellLadderDepth ctx + 64 :=
  ⟨((mem_class2Fibre_iff ctx k).mp hk).2.1, ((mem_class2Fibre_iff ctx k).mp hk).2.2.1⟩

/-- **The hit-position band** (the telescoped form of the class-2 pin): every class-2 start has
its `(r+1)`-st following hit strictly between `(129L+64)/64` and `(130L+64)/64` above its own
hit position. -/
theorem class2Fibre_hitPosition_band (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2) :
    129 * shellLadderDepth ctx + 64
        < 64 * (ctx.n24CarryData.a (k + ctx.n24CarryData.r + 1) - ctx.n24CarryData.a k)
      ∧ 64 * (ctx.n24CarryData.a (k + ctx.n24CarryData.r + 1) - ctx.n24CarryData.a k)
        < 130 * shellLadderDepth ctx + 64 := by
  have h := class2Fibre_gapWindow_band ctx hk
  rwa [ctx.n24CarryData.carry.hits.gapWindow_hitGap_eq] at h

/-- **The class-2 band pin**: every class-2 routed start of the genuine route has its
slope-orbit canonical-gap band index EXACTLY `4` (the same E.13 band as class 1 — the two
classes are separated by the window excess, not the orbit band). -/
theorem class2Fibre_canonGap_eq (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2) :
    canonGap (class1SlopeDatum ctx).q
      (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 4 :=
  ((mem_class2Fibre_iff ctx k).mp hk).2.2.2

/-- **The class-2 orbit-band pin**: the slope-orbit numerator at every class-2 start sits in
the dyadic band `8·K_k ≤ q < 16·K_k`, i.e. `q/16 < K_k ≤ q/8`. -/
theorem class2Fibre_orbit_band (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2) :
    8 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
        ≤ (class1SlopeDatum ctx).q
      ∧ (class1SlopeDatum ctx).q
        < 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k := by
  have hband := class2Fibre_canonGap_eq ctx hk
  have horb := slopeOrbit_mem (class1SlopeDatum ctx).hq_odd (class1SlopeDatum ctx).hK₀_pos
    (class1SlopeDatum ctx).hK₀_lt k
  exact (canonGap_eq_four_iff horb.1).mp hband

/-- **The class-2 orbit-step pin**: at every class-2 start the E.12/E.13 successor numerator
is EXACTLY `16·K_k − q` (the band-4 carry-doubling step). -/
theorem class2Fibre_orbit_step (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2) :
    slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (k + 1)
      = 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
        - (class1SlopeDatum ctx).q := by
  have hband := class2Fibre_canonGap_eq ctx hk
  have hstep : slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (k + 1)
      = boundedSlopeStep (class1SlopeDatum ctx).q
          (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) := rfl
  rw [hstep]
  unfold boundedSlopeStep
  rw [hband]
  norm_num

/-- **A nonempty class-2 fibre forces a large AP-subfibre modulus**: `q ≥ 9` (the band
`8K ≤ q` needs `q ≥ 8`, and `q` is odd). -/
theorem modulus_ge_nine_of_class2Fibre_nonempty (ctx : ActualFailureContext)
    (h : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).Nonempty) :
    9 ≤ (class1SlopeDatum ctx).q := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨h8, h16⟩ := class2Fibre_orbit_band ctx hk
  have horb := slopeOrbit_mem (class1SlopeDatum ctx).hq_odd (class1SlopeDatum ctx).hK₀_pos
    (class1SlopeDatum ctx).hK₀_lt k
  obtain ⟨m, hm⟩ := (class1SlopeDatum ctx).hq_odd
  have h1 := horb.1
  omega

/-- **Small-modulus closure**: the class-2 routed fibre of the genuine route is PROVABLY EMPTY
on every shell whose closed AP-subfibre modulus is `< 9` (`q ∈ {3, 5, 7}`) — the E.13 band-4
window `8K ≤ q < 16K` is unsatisfiable below `q = 9`.  (Mirrors the class-1
`class1Fibre_empty_of_modulus_lt_nine`; this is a PROVED emptiness on a genuine subfamily,
not a fabricated witness — on `q ≥ 9` shells the fibre stays genuinely live.) -/
theorem class2Fibre_empty_of_modulus_lt_nine (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q < 9) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2 = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro k hk
  have h9 := modulus_ge_nine_of_class2Fibre_nonempty ctx ⟨k, hk⟩
  omega

/-! ## Part 3.  Orbit run rigidity — the spacing-side structure of the class-2 pin

The band-4 step is `K ↦ 16K − q` on the band `(q/16, q/8]`.  Its unique fixed point is
`K = q/15` (so band-4 runs of unbounded length exist EXACTLY on the `15 ∣ q` orbits sitting at
the fixed point); off the fixed point the distance `|15K − q|` grows by the factor `16` each
step while staying `< q`, so a run of `s + 1` consecutive band-4 positions forces `16^s < q`.
This is the precise formal content of "the class-2 pin forces start spacing": it does — at
scale `log₁₆ q` along the orbit — UNLESS the shell's orbit is the exact `1/15` cycle, which the
formalized band conditions cannot exclude.  (This is why the deep closure below is keyed to the
COUNT bound, not to spacing.) -/

/-- **Band-4 run rigidity for the bounded-slope orbit**: if the canonical-gap band index is `4`
at `s + 1` consecutive orbit positions `k, k+1, …, k+s`, then either the orbit sits at the
exact `1/15` fixed point (`15·K_k = q`, forcing `15 ∣ q`) or `16^s < q`. -/
theorem band4_run_forces_pow_lt {q K₀ : ℕ} (hq : Odd q) (hK1 : 1 ≤ K₀) (hKq : K₀ < q)
    {k s : ℕ}
    (hband : ∀ i, i ≤ s → canonGap q (slopeOrbit q K₀ (k + i)) = 4) :
    15 * slopeOrbit q K₀ k = q ∨ 16 ^ s < q := by
  have horb : ∀ j, 1 ≤ slopeOrbit q K₀ j ∧ slopeOrbit q K₀ j < q :=
    slopeOrbit_mem hq hK1 hKq
  have hb : ∀ i, i ≤ s →
      8 * slopeOrbit q K₀ (k + i) ≤ q ∧ q < 16 * slopeOrbit q K₀ (k + i) :=
    fun i hi => (canonGap_eq_four_iff (horb (k + i)).1).mp (hband i hi)
  have hstep : ∀ i, i < s →
      slopeOrbit q K₀ (k + i + 1) = 16 * slopeOrbit q K₀ (k + i) - q := by
    intro i hi
    have h4 := hband i (Nat.le_of_lt hi)
    have hrfl : slopeOrbit q K₀ (k + i + 1)
        = boundedSlopeStep q (slopeOrbit q K₀ (k + i)) := rfl
    rw [hrfl]
    unfold boundedSlopeStep
    rw [h4]
    norm_num
  rcases Nat.lt_trichotomy (15 * slopeOrbit q K₀ k) q with hlt | heq | hgt
  · refine Or.inr ?_
    have key : ∀ i, i ≤ s →
        15 * slopeOrbit q K₀ (k + i) < q
          ∧ q - 15 * slopeOrbit q K₀ (k + i)
              = 16 ^ i * (q - 15 * slopeOrbit q K₀ k) := by
      intro i
      induction i with
      | zero =>
          intro _
          constructor
          · simpa using hlt
          · simp
      | succ n ih =>
          intro hns
          obtain ⟨ihlt, iheq⟩ := ih (by omega)
          have hstepn := hstep n (by omega)
          have hbn := hb n (by omega)
          have hadd : k + (n + 1) = k + n + 1 := rfl
          rw [hadd]
          constructor
          · omega
          · have hq16 : q - 15 * slopeOrbit q K₀ (k + n + 1)
                = 16 * (q - 15 * slopeOrbit q K₀ (k + n)) := by omega
            rw [hq16, iheq, pow_succ]
            ring
    obtain ⟨hlast, hpow⟩ := key s le_rfl
    have hx1 : 1 ≤ slopeOrbit q K₀ (k + s) := (horb (k + s)).1
    have hge1 : 1 ≤ q - 15 * slopeOrbit q K₀ k := by omega
    have h16 : 16 ^ s * 1 ≤ 16 ^ s * (q - 15 * slopeOrbit q K₀ k) :=
      Nat.mul_le_mul_left _ hge1
    have hfin : 16 ^ s ≤ q - 15 * slopeOrbit q K₀ (k + s) := by
      rw [hpow]
      omega
    omega
  · exact Or.inl heq
  · refine Or.inr ?_
    have key : ∀ i, i ≤ s →
        q < 15 * slopeOrbit q K₀ (k + i)
          ∧ 15 * slopeOrbit q K₀ (k + i) - q
              = 16 ^ i * (15 * slopeOrbit q K₀ k - q) := by
      intro i
      induction i with
      | zero =>
          intro _
          constructor
          · simpa using hgt
          · simp
      | succ n ih =>
          intro hns
          obtain ⟨ihgt, iheq⟩ := ih (by omega)
          have hstepn := hstep n (by omega)
          have hbn := hb n (by omega)
          have hadd : k + (n + 1) = k + n + 1 := rfl
          rw [hadd]
          constructor
          · omega
          · have hq16 : 15 * slopeOrbit q K₀ (k + n + 1) - q
                = 16 * (15 * slopeOrbit q K₀ (k + n) - q) := by omega
            rw [hq16, iheq, pow_succ]
            ring
    obtain ⟨hgtlast, hpow⟩ := key s le_rfl
    have hbs := hb s le_rfl
    have hge1 : 1 ≤ 15 * slopeOrbit q K₀ k - q := by omega
    have h16 : 16 ^ s * 1 ≤ 16 ^ s * (15 * slopeOrbit q K₀ k - q) :=
      Nat.mul_le_mul_left _ hge1
    have hfin : 16 ^ s ≤ 15 * slopeOrbit q K₀ (k + s) - q := by
      rw [hpow]
      omega
    omega

/-- **Class-2 run rigidity**: a run `k, k+1, …, k+s` of class-2 routed starts forces either
the exact `1/15` orbit fixed point `15·K_k = q` or `16^s < q`.  In particular class-2 runs are
`≤ log₁₆ q` long on every shell whose orbit is off the fixed point. -/
theorem class2Fibre_run_forces_pow_lt (ctx : ActualFailureContext) {k s : ℕ}
    (hrun : ∀ i, i ≤ s →
      k + i ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2) :
    15 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
        = (class1SlopeDatum ctx).q
      ∨ 16 ^ s < (class1SlopeDatum ctx).q :=
  band4_run_forces_pow_lt (class1SlopeDatum ctx).hq_odd (class1SlopeDatum ctx).hK₀_pos
    (class1SlopeDatum ctx).hK₀_lt
    (fun i hi => class2Fibre_canonGap_eq ctx (hrun i hi))

/-- **The consecutive-pair pin**: two adjacent class-2 starts pin the orbit numerator into the
16×-narrower band `17q < 256·K_k` and `128·K_k ≤ 9q` (i.e. `K_k ∈ (17q/256, 9q/128]`). -/
theorem class2Fibre_pair_orbit_band (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2)
    (hk1 : k + 1 ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2) :
    17 * (class1SlopeDatum ctx).q
        < 256 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
      ∧ 128 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
        ≤ 9 * (class1SlopeDatum ctx).q := by
  have hb0 := class2Fibre_orbit_band ctx hk
  have hb1 := class2Fibre_orbit_band ctx hk1
  have hstep := class2Fibre_orbit_step ctx hk
  omega

/-! ## Part 4.  Hit-index window geometry — landing forces the start window

The converse of the closed landing lemma `towerSD_window_lands`: a hit index whose hit lands
in the dyadic shell support MUST lie in the genuine start window `[i₀, i₀ + K)`.  This is what
makes the count bound `m₀·#fibre₂ ≤ K` NECESSARY for any Hall window family. -/

/-- **Landing forces the window**: if the `j`-th hit lands in `supportShell d X`, then
`firstIndexAbove X ≤ j < firstIndexAbove X + |supportShell d X|`. -/
theorem hitIndex_mem_window_of_mem_supportShell (ctx : ActualFailureContext) {j : ℕ}
    (hj : ctx.n24CarryData.a j ∈ supportShell ctx.d ctx.X) :
    shellStart ctx ≤ j ∧ j < shellStart ctx + shellWidth ctx := by
  rw [mem_supportShell] at hj
  obtain ⟨hlo, hhi, _⟩ := hj
  constructor
  · by_contra hcon
    rw [not_le] at hcon
    have hle : ctx.n24CarryData.a j ≤ ctx.shell.X :=
      ctx.n24CarryData.carry.hits.lt_firstIndexAbove ctx.shell.X hcon
    rw [ActualFailureContext.shell_X] at hle
    omega
  · by_contra hcon
    rw [not_lt] at hcon
    have hgt : 2 * ctx.shell.X
        < ctx.n24CarryData.a (shellStart ctx + shellWidth ctx) :=
      ctx.n24CarryData.carry.hits.a_firstIndexAbove_add_card_gt ctx.shell.X
    have hmono : ctx.n24CarryData.a (shellStart ctx + shellWidth ctx)
        ≤ ctx.n24CarryData.a j :=
      ctx.n24CarryData.carry.hits.strict.monotone hcon
    rw [ActualFailureContext.shell_X] at hgt
    omega

/-! ## Part 5.  The rank-block window construction and the count-bound equivalence -/

/-- **The class-2 fibre rank**: the number of class-2 routed starts strictly below `k`. -/
def class2Rank (ctx : ActualFailureContext) (k : ℕ) : ℕ :=
  ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).filter (fun x => x < k)).card

/-- The rank of a fibre member is strictly below the fibre cardinality. -/
theorem class2Rank_lt_card (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2) :
    class2Rank ctx k
      < (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).card := by
  have hsub : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).filter
        (fun x => x < k)
      ⊆ (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).erase k := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_erase.mpr ⟨Nat.ne_of_lt hx2, hx1⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hk] at hcard
  have hpos : 0 < (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).card :=
    Finset.card_pos.mpr ⟨k, hk⟩
  unfold class2Rank
  omega

/-- The rank is strictly monotone on fibre members. -/
theorem class2Rank_lt_of_mem_lt (ctx : ActualFailureContext) {k k' : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2)
    (hlt : k < k') :
    class2Rank ctx k < class2Rank ctx k' := by
  have hsub : insert k
        ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).filter (fun x => x < k))
      ⊆ (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).filter
          (fun x => x < k') := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_filter.mpr ⟨hk, hlt⟩
    · obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨hx1, by omega⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simp [Finset.mem_filter])] at hcard
  unfold class2Rank
  omega

/-- The rank is injective on fibre members. -/
theorem class2Rank_ne_of_mem_ne (ctx : ActualFailureContext) {k k' : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2)
    (hk' : k' ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2)
    (hne : k ≠ k') :
    class2Rank ctx k ≠ class2Rank ctx k' := by
  rcases Nat.lt_or_ge k k' with h | h
  · exact Nat.ne_of_lt (class2Rank_lt_of_mem_lt ctx hk h)
  · have hlt : k' < k := by omega
    exact (Nat.ne_of_lt (class2Rank_lt_of_mem_lt ctx hk' hlt)).symm

/-- **The rank-block window**: the `j`-th class-2 start (in increasing order) owns the
hit-index block `[i₀ + j·m₀, i₀ + (j+1)·m₀)` of the genuine start window. -/
def class2BlockWindow (ctx : ActualFailureContext) (k : ℕ) : Finset ℕ :=
  Finset.Ico (shellStart ctx + class2Rank ctx k * towerSparsityBlock ctx)
    (shellStart ctx + class2Rank ctx k * towerSparsityBlock ctx + towerSparsityBlock ctx)

/-- Each rank block has exactly `m₀` hit indices. -/
theorem class2BlockWindow_card (ctx : ActualFailureContext) (k : ℕ) :
    (class2BlockWindow ctx k).card = towerSparsityBlock ctx := by
  unfold class2BlockWindow
  rw [Nat.card_Ico]
  omega

/-- Rank blocks of distinct fibre members are pairwise disjoint. -/
theorem class2BlockWindow_disjoint (ctx : ActualFailureContext) {k k' : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2)
    (hk' : k' ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2)
    (hne : k ≠ k') :
    Disjoint (class2BlockWindow ctx k) (class2BlockWindow ctx k') := by
  have key : ∀ x y : ℕ, class2Rank ctx x < class2Rank ctx y →
      Disjoint (class2BlockWindow ctx x) (class2BlockWindow ctx y) := by
    intro x y hr
    rw [Finset.disjoint_left]
    intro n hnx hny
    simp only [class2BlockWindow, Finset.mem_Ico] at hnx hny
    have hmul : class2Rank ctx x * towerSparsityBlock ctx + towerSparsityBlock ctx
        ≤ class2Rank ctx y * towerSparsityBlock ctx := by
      calc class2Rank ctx x * towerSparsityBlock ctx + towerSparsityBlock ctx
          = (class2Rank ctx x + 1) * towerSparsityBlock ctx := by ring
        _ ≤ class2Rank ctx y * towerSparsityBlock ctx :=
            Nat.mul_le_mul_right _ hr
    omega
  rcases Nat.lt_or_ge (class2Rank ctx k) (class2Rank ctx k') with h | h
  · exact key k k' h
  · have hlt : class2Rank ctx k' < class2Rank ctx k := by
      have hne' := class2Rank_ne_of_mem_ne ctx hk hk' hne
      omega
    exact (key k' k hlt).symm

/-- **Under the count bound `m₀·#fibre₂ ≤ K`, every rank block sits inside the genuine start
window** — the landing obligation is then discharged by the closed `towerSD_window_lands`. -/
theorem class2BlockWindow_subset_window (ctx : ActualFailureContext)
    (hcount : towerSparsityBlock ctx
        * (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).card
      ≤ shellWidth ctx)
    {k : ℕ} (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2) :
    class2BlockWindow ctx k
      ⊆ Finset.Ico (shellStart ctx) (shellStart ctx + shellWidth ctx) := by
  intro n hn
  simp only [class2BlockWindow, Finset.mem_Ico] at hn
  rw [Finset.mem_Ico]
  have hrank := class2Rank_lt_card ctx hk
  have hmul : class2Rank ctx k * towerSparsityBlock ctx + towerSparsityBlock ctx
      ≤ towerSparsityBlock ctx
          * (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).card := by
    calc class2Rank ctx k * towerSparsityBlock ctx + towerSparsityBlock ctx
        = (class2Rank ctx k + 1) * towerSparsityBlock ctx := by ring
      _ ≤ (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).card
            * towerSparsityBlock ctx :=
          Nat.mul_le_mul_right _ (by omega)
      _ = towerSparsityBlock ctx
            * (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).card :=
          Nat.mul_comm _ _
  omega

/-- **The deep-shell window data from the count bound** (any shell, no depth hypothesis): the
rank-block family is pairwise disjoint with per-block card `m₀`, so the Hall marginal holds
with EQUALITY for every subfamily, and the count bound keeps every block inside the genuine
start window. -/
def class2DeepShellWindowData_ofCountBound (ctx : ActualFailureContext)
    (hcount : towerSparsityBlock ctx
        * (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).card
      ≤ shellWidth ctx) :
    Class2DeepShellWindowData ctx :=
  Class2DeepShellWindowData.ofRangeWindows ctx (class2BlockWindow ctx)
    (fun k hk => class2BlockWindow_subset_window ctx hcount hk)
    (fun S hS => by
      have hdisj : ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
          Disjoint (class2BlockWindow ctx x) (class2BlockWindow ctx y) :=
        fun x hx y hy hxy => class2BlockWindow_disjoint ctx (hS hx) (hS hy) hxy
      calc towerSparsityBlock ctx * S.card
          = ∑ _k ∈ S, towerSparsityBlock ctx := by
            rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
        _ = ∑ k ∈ S, (class2BlockWindow ctx k).card :=
            Finset.sum_congr rfl (fun k _ => (class2BlockWindow_card ctx k).symm)
        _ = (S.biUnion (class2BlockWindow ctx)).card :=
            (Finset.card_biUnion hdisj).symm
        _ ≤ (S.biUnion (class2BlockWindow ctx)).card := le_rfl)

/-- **The count bound is NECESSARY**: any deep-shell window datum forces
`m₀·#fibre₂ ≤ |supportShell|` — its windows land in the shell, so they live inside the start
window, and the Hall marginal at `S = fibre₂` caps the count. -/
theorem countBound_of_class2DeepShellWindowData {ctx : ActualFailureContext}
    (D : Class2DeepShellWindowData ctx) :
    towerSparsityBlock ctx
        * (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).card
      ≤ shellWidth ctx := by
  have hmarg := D.hmarg (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2)
    (Finset.Subset.refl _)
  have hsub : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).biUnion D.W
      ⊆ Finset.Ico (shellStart ctx) (shellStart ctx + shellWidth ctx) := by
    intro j hj
    rw [Finset.mem_biUnion] at hj
    obtain ⟨k, hk, hjk⟩ := hj
    have hwin := hitIndex_mem_window_of_mem_supportShell ctx (D.hlands k hk j hjk)
    rw [Finset.mem_Ico]
    exact hwin
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Ico] at hcard
  omega

/-- **The exact frontier**: the deep-shell window datum is inhabited IFF the counting
inequality `m₀·#fibre₂ ≤ |supportShell|` holds.  The Tower deep-shell residual IS a counting
problem. -/
theorem class2DeepShellWindowData_iff_countBound (ctx : ActualFailureContext) :
    Nonempty (Class2DeepShellWindowData ctx)
      ↔ towerSparsityBlock ctx
            * (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).card
          ≤ shellWidth ctx :=
  ⟨fun ⟨D⟩ => countBound_of_class2DeepShellWindowData D,
   fun h => ⟨class2DeepShellWindowData_ofCountBound ctx h⟩⟩

/-! ## Part 6.  The strictly smaller deep residual and its bridges -/

/-- **The sharp deep-shell residual, as a single named `Prop`**: on every genuinely deep shell
(`L ≥ 328966`, equivalently `r ≥ 21`), the class-2 fibre count obeys
`m₀ · #fibre₂ ≤ |supportShell|`.  By `class2DeepShellWindowData_iff_countBound` this is
EQUIVALENT to (not merely sufficient for) the capstone's `Class2DeepShellResidual`, and it is
strictly smaller data: one `ℕ` inequality per deep shell, no window family, no Hall marginal,
no landing geometry. -/
abbrev Class2DeepShellCountBound : Prop :=
  ∀ ctx : ActualFailureContext, towerShallowDepthBound < shellLadderDepth ctx →
    towerSparsityBlock ctx
        * (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).card
      ≤ shellWidth ctx

/-- **The bridge**: the counting inequality alone discharges the full deep-shell Tower
residual consumed by `Erdos260SixAtomResidual.towerDeep`. -/
def towerDeepResidual_ofCountBound (h : Class2DeepShellCountBound) :
    Class2DeepShellResidual :=
  fun ctx hdeep => class2DeepShellWindowData_ofCountBound ctx (h ctx hdeep)

/-- **The converse bridge**: any deep-shell residual yields the counting inequality — the
reduction loses nothing. -/
theorem countBound_ofTowerDeepResidual (R : Class2DeepShellResidual) :
    Class2DeepShellCountBound :=
  fun ctx hdeep => countBound_of_class2DeepShellWindowData (R ctx hdeep)

/-- **The lossless-reduction equivalence at the residual level**: the capstone's deep-shell
Tower surface is inhabited IFF the counting inequality holds on every deep shell. -/
theorem towerDeepResidual_iff_countBound :
    Nonempty Class2DeepShellResidual ↔ Class2DeepShellCountBound :=
  ⟨fun ⟨R⟩ => countBound_ofTowerDeepResidual R,
   fun h => ⟨towerDeepResidual_ofCountBound h⟩⟩

/-- **The full V3/P9 Tower field from the counting inequality alone**: shallow shells through
the unconditional direct closure, deep shells through the rank-block Hall data. -/
def p9V3TowerCount_ofCountBound (h : Class2DeepShellCountBound) :
    ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx :=
  p9V3TowerCount_ofShallowDeep (towerDeepResidual_ofCountBound h)

/-- The routed class-2 Tower sub-mass slot from the counting inequality:
`routedClassMassOf … 2 ≤ ξ·X/6` on every failing shell. -/
theorem class2TowerSubMass_ofCountBound (h : Class2DeepShellCountBound)
    (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
      ≤ erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  class2TowerSubMass_ofShallowDeep (towerDeepResidual_ofCountBound h) ctx

/-! ## Part 7.  Unconditional per-shell closures of the count bound -/

/-- **The block always fits once**: `m₀ ≤ r + 1 ≤ K` (ceiling division `⌈3(r+1)/64⌉ ≤ r + 1`
and the stored window fit `r + 1 ≤ |supportShell|`). -/
theorem towerSparsityBlock_le_shellWidth (ctx : ActualFailureContext) :
    towerSparsityBlock ctx ≤ shellWidth ctx := by
  have hr := r_add_one_le_width ctx
  have hm : towerSparsityBlock ctx ≤ ctx.n24CarryData.r + 1 := by
    unfold towerSparsityBlock
    omega
  omega

/-- **Closure on `q < 9` shells**: the fibre is provably empty there, so the count bound — and
hence the FULL deep window datum — holds outright. -/
def class2DeepShellWindowData_of_modulus_lt_nine (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q < 9) :
    Class2DeepShellWindowData ctx :=
  class2DeepShellWindowData_ofCountBound ctx (by
    rw [class2Fibre_empty_of_modulus_lt_nine ctx hq]
    simp)

/-- **Closure on `#fibre₂ ≤ 1` shells**: a single class-2 start always owns a full block
(`m₀ ≤ r + 1 ≤ K`), so the count bound — and the full deep window datum — holds outright. -/
def class2DeepShellWindowData_of_card_le_one (ctx : ActualFailureContext)
    (hcard : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).card ≤ 1) :
    Class2DeepShellWindowData ctx :=
  class2DeepShellWindowData_ofCountBound ctx (by
    calc towerSparsityBlock ctx
          * (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).card
        ≤ towerSparsityBlock ctx * 1 := Nat.mul_le_mul_left _ hcard
      _ = towerSparsityBlock ctx := Nat.mul_one _
      _ ≤ shellWidth ctx := towerSparsityBlock_le_shellWidth ctx)

/-! ## Part 8.  Honest machine-readable status -/

/-- The precise status of the Tower / Class 2 deep-shell closure after this module. -/
def towerDeepWindowClosureStatus : List String :=
  [ "CLOSED (the class-2 routing pin, settled) — mem_class2Fibre_iff / " ++
      "class2Fibre_eq_pinnedFilter: k ∈ fibre₂ ⟺ k ∈ starts ∧ 129L+64 < 64·gapWindow < " ++
      "130L+64 ∧ canonGap q K_k = 4. An OPEN inequality band (width L in 64·gapWindow), not " ++
      "an equality: class 1 is the left endpoint 64·gW = 129L+64, class 4 (band 2) is the " ++
      "unbounded floor 64·gW ≥ 129L+64; class 2 is exactly the open strip between the strict " ++
      "high-excess floor (returnCls = 1) and the strict no-large-run ceiling (runCls ≠ 1). " ++
      "Strict ℕ forms: class2_Y_lt_windowExcess_iff_gapWindow, " ++
      "class2_windowExcess_lt_twoY_iff_gapWindow, returnCls_eq_one_iff. Telescoped " ++
      "hit-position band: class2Fibre_hitPosition_band.",
    "CLOSED (the deep residual IS a counting inequality, BOTH directions) — " ++
      "class2DeepShellWindowData_iff_countBound: Nonempty (Class2DeepShellWindowData ctx) ⟺ " ++
      "towerSparsityBlock·#fibre₂ ≤ |supportShell|. Sufficiency: the rank-block construction " ++
      "(class2Rank / class2BlockWindow) gives pairwise-disjoint m₀-blocks inside the start " ++
      "window with Hall marginal EQUALITY (card_biUnion); landing via the closed " ++
      "towerSD_window_lands through ofRangeWindows. Necessity: landing forces windows into " ++
      "[i₀, i₀+K) (hitIndex_mem_window_of_mem_supportShell, from lt_firstIndexAbove + " ++
      "a_firstIndexAbove_add_card_gt), so Hall at S = fibre₂ caps the count.",
    "REDUCED (the strictly smaller deep residual + proved bridges) — " ++
      "Class2DeepShellCountBound : ∀ ctx, 328965 < L → m₀·#fibre₂ ≤ K, a single ℕ inequality " ++
      "per deep shell (a Prop; no window family, no Hall data, no landing geometry). " ++
      "towerDeepResidual_ofCountBound : Class2DeepShellCountBound → Class2DeepShellResidual " ++
      "(the exact capstone field of Erdos260SixAtomResidual.towerDeep); " ++
      "countBound_ofTowerDeepResidual is the converse, so the reduction is LOSSLESS. " ++
      "p9V3TowerCount_ofCountBound / class2TowerSubMass_ofCountBound feed the full V3/P9 " ++
      "Tower field and the ξX/6 slot from the counting inequality alone.",
    "SHARPER THAN SPACING — a start-spacing fact (consecutive class-2 starts ≥ m₀ apart) " ++
      "does NOT imply the residual: with K = 3, m₀ = 2 and starts {i₀, i₀+2} the spacing is " ++
      "m₀ but m₀·t = 4 > 3 = K, so no landing window family satisfies the marginal. The " ++
      "count bound is the exact obstruction and the exact deliverable.",
    "CLOSED UNCONDITIONALLY (q < 9 deep shells) — class2Fibre_empty_of_modulus_lt_nine / " ++
      "modulus_ge_nine_of_class2Fibre_nonempty: the E.13 band-4 window 8K ≤ q < 16K is " ++
      "unsatisfiable for q ∈ {3,5,7}, the fibre is PROVABLY empty, and " ++
      "class2DeepShellWindowData_of_modulus_lt_nine delivers the full window datum. This is " ++
      "a proved emptiness on a genuine subfamily (mirror of the class-1/class-4 closures), " ++
      "NOT a fabricated witness; on q ≥ 9 shells the fibre stays genuinely live and carries " ++
      "the pressure mass.",
    "CLOSED UNCONDITIONALLY (single-start shells) — class2DeepShellWindowData_of_card_le_one " ++
      "via towerSparsityBlock_le_shellWidth (m₀ ≤ r+1 ≤ K): any shell with #fibre₂ ≤ 1 " ++
      "carries the full deep window datum.",
    "CLOSED (orbit run rigidity — the genuine spacing-side content) — " ++
      "band4_run_forces_pow_lt / class2Fibre_run_forces_pow_lt: a run k..k+s of class-2 " ++
      "starts forces 15·K_k = q (the exact 1/15 fixed point of the band-4 step K ↦ 16K − q, " ++
      "possible only when 15 ∣ q) OR 16^s < q. So class-2 runs are ≤ log₁₆ q off the fixed " ++
      "point; class2Fibre_pair_orbit_band pins consecutive pairs into the 16×-narrower band " ++
      "17q < 256·K_k ∧ 128·K_k ≤ 9q. The fixed-point escape is GENUINE: 15 ∣ q orbits admit " ++
      "unbounded band-4 runs, which is one of the two reasons the count bound is not a " ++
      "theorem of the formalized pins.",
    "HONESTLY NOT CLOSED (the count bound itself) — m₀·#fibre₂ ≤ K on deep shells. The " ++
      "gap-window band constrains the hit sequence a; the band-4 pin constrains the slope " ++
      "orbit; NO unconditional bridge ties hitGap a to canonGap along the orbit (the " ++
      "zero-run matching hzero of carry_tracks_slopeOrbit is the explicit §25.1/E.2-E.4 " ++
      "residual). Within the formal model, 15 ∣ q orbits sit at the band-4 fixed point and " ++
      "an L-wide open band admits locally ≈ 2L/(r+1)-dense hit blocks inside a globally " ++
      "< c₀X-sparse shell, so consecutive class-2 runs of unbounded length are not " ++
      "refutable. Interval counting tops out at #fibre₂ ≲ (r+1)·X/(2L+2) (disjointified " ++
      "descent windows of span > 2L inside the ≤ X position span), which exceeds the " ++
      "demanded K/m₀ by the factor ≈ 3κL/2 ≈ 32 at the failure cap K < c₀X = κX/64 — the " ++
      "missing input is the manuscript's PER-START ownership (§25.1 semiperiodic matching + " ++
      "K.2 Fine-Wilf), exactly as recorded in the TowerShallowDeepUnconditional audit. No " ++
      "degenerate witness is fabricated.",
    "NON-DEGENERATE — every construction runs over the genuine routed class-2 fibre of " ++
      "genuineChargeRoute with the genuine carry data (real hit enumeration, real start " ++
      "window, real failure cap); the rank-block windows are real owned hit-index blocks " ++
      "with positive density m₀/K; the Hall marginal is proved with equality, not " ++
      "weakened; the subregime closures are proved emptiness/cardinality facts, not " ++
      "fabricated data." ]

theorem towerDeepWindowClosureStatus_nonempty : towerDeepWindowClosureStatus ≠ [] := by
  simp [towerDeepWindowClosureStatus]

/-! ## Part 9.  Axiom-cleanliness audit -/

#print axioms class2_Y_lt_windowExcess_iff_gapWindow
#print axioms class2_windowExcess_lt_twoY_iff_gapWindow
#print axioms returnCls_eq_one_iff
#print axioms mem_class2Fibre_iff
#print axioms class2Fibre_eq_pinnedFilter
#print axioms class2Fibre_gapWindow_band
#print axioms class2Fibre_hitPosition_band
#print axioms class2Fibre_canonGap_eq
#print axioms class2Fibre_orbit_band
#print axioms class2Fibre_orbit_step
#print axioms modulus_ge_nine_of_class2Fibre_nonempty
#print axioms class2Fibre_empty_of_modulus_lt_nine
#print axioms band4_run_forces_pow_lt
#print axioms class2Fibre_run_forces_pow_lt
#print axioms class2Fibre_pair_orbit_band
#print axioms hitIndex_mem_window_of_mem_supportShell
#print axioms class2Rank_lt_card
#print axioms class2Rank_lt_of_mem_lt
#print axioms class2Rank_ne_of_mem_ne
#print axioms class2BlockWindow_card
#print axioms class2BlockWindow_disjoint
#print axioms class2BlockWindow_subset_window
#print axioms class2DeepShellWindowData_ofCountBound
#print axioms countBound_of_class2DeepShellWindowData
#print axioms class2DeepShellWindowData_iff_countBound
#print axioms towerDeepResidual_ofCountBound
#print axioms countBound_ofTowerDeepResidual
#print axioms towerDeepResidual_iff_countBound
#print axioms p9V3TowerCount_ofCountBound
#print axioms class2TowerSubMass_ofCountBound
#print axioms towerSparsityBlock_le_shellWidth
#print axioms class2DeepShellWindowData_of_modulus_lt_nine
#print axioms class2DeepShellWindowData_of_card_le_one
#print axioms towerDeepWindowClosureStatus_nonempty

end

end Erdos260
