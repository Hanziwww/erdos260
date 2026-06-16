import Erdos260.HitToHitCarry
import Erdos260.TowerDeepWindowClosure
import Erdos260.RunClass5Routing

/-!
# SCC recurrence-persistence at the fixed families: pressure vs persistence
(`SCCPersistence`)

This module (NEW; it edits no existing file) formalizes the manuscript's I.3/E.8/L.3/M.5
recurrence-persistence mechanism for the five fixed families at the exact granularity the
in-tree machinery supports, and works the brief's counting route honestly.  Three genuinely
new mechanisms are PROVED; the unproved link is named precisely.

## Part 1 — the counting-route verdict (PROVED, and it REVERSES the expected outcome)

The brief conjectured that at a fixed datum the pressure mass MUST sit in class 2 and asked
whether the pressure-forced `#fibre₂` exceeds the sliding-window cap.  The honest verdict is
sharper and goes the other way: the failure hypothesis ITSELF caps the class-1/2 masses far
below the pressure floor, because classes 1 and 2 carry PER-START excess caps (`Y` and `2Y`)
while their cardinalities are capped by `|starts| = |supportShell| < c₀·X`:

  `mass₁ + mass₂ ≤ |supportShell|·3Y < (κ/64)·X·(3L/64) = (3/8)·κXL/64·…`,

while the PROVED Lemma 21.1 floor gives `total ≥ cPr·X·(r+1) > (1/2)·X·κL`.  Numerically
`512·(mass₁+mass₂) ≤ cPr·X·(r+1)` (`scc_class12_deficit`): classes 1∪2 carry less than
`1/512` of the pressure.  No sliding-window engine is even needed — the count cap from
`hfailure` supersedes it (the sliding cap `(r+1)·64X/(129L)` is far LOOSER than `c₀X`).

## Part 2 — the per-datum routing collapse and the pressure relocation (PROVED)

At each fixed datum the slope orbit is eventually CONSTANT (fixed point), so the L.3.1
classifier `towerClsOfShell` is constant on `k ≥ 1` (`OrbitBandPinned`,
`fixedFamilyHit_orbitBandPinned`).  Consequences (`fixedFamilyHit_pressure_relocation`):

* `(3,1)` (band 2): EVERY start routes to class 4 (returnPkg) — `floor ≤ mass₄`;
* `(21,3)` (band 3): EVERY start routes to class 3 (densePack) — `floor ≤ mass₃`;
* `(15,1)`, `(15,2)`, `(105,7)` (band 4): classes 0/3/4/6 are EMPTY, classes 1/2 are
  starved (Part 1), so `(511/512)·floor ≤ mass₅` — **the pressure mass sits in class 5**
  (the heavy class `windowExcess ≥ 2Y`), NOT in class 2.  The class-2 fibre (the
  `Y < windowExcess < 2Y` band) can never host the recurrent mass.

## Part 3 — persistence KILLS the pressure (the formal L.3 alternative, PROVED)

While the trajectory persists (all hit gaps equal the recurrent band ≤ 4), every gap window
is LIGHT: `gapWindow = (r+1)·band ≤ 4(κL+1) < 2L+1 = T`, so `windowExcess = 0`
(`scc_windowExcess_zero_of_band_window`).  Hence a persistence onset at or below the start
window (`FixedFamilyIndexPersistence`: onset index `≤ firstIndexAbove X`) EMPTIES
`highExcessStarts`, contradicting the proved pressure floor `cPr·X·(r+1) ≤ highExcessMass`:
`fixedFamilyIndexPersistence_void`.  Corollaries — a SECOND, bootstrap-free, every-scale
voiding of the clean continuation and of the carry linearity:
`fixedFamilyCleanContinuation_pressure_void`, `fixedFamilyCarryLinear_pressure_void`
(the wave-7 route needed the window-periodicity bootstrap; this one needs only Lemma 21.1).
Dual reading (PROVED): every high-excess start's window CONTAINS an exit — a non-band gap
(`scc_exit_in_window_of_highExcess`) — the trajectory is FORCED to keep making transient
excursions while the failure persists; recurrence and persistence are INCOMPATIBLE inside
the shell.

## Part 4 — the widened persistence target (NEW supply atom, payoff PROVED)

`FixedFamilyShellPersistence ctx`: some `k₁` with onset POSITION `512·a k₁ ≤ 1023·X`
(i.e. `a k₁ ≤ 2X − X/512` — almost the WHOLE shell, vs the old `a k₀ ≤ X`) has all later
hit gaps equal to the band.  PROVED: this voids the context outright
(`fixedFamilyShellPersistence_void`) by raw support counting — the hits form an arithmetic
progression of step `band ≤ 4`, sweeping `≥ X/4096 − 1` support points into `(X, 2X]`,
overwhelming `hfailure`'s cap `c₀·X = 17X/2²⁴` (margin `2¹²/17`).  The old clean
continuation IMPLIES it (`fixedFamilyCleanContinuation_shellPersistence`), so the supply
burden strictly drops: the deep form is equivalent to the deep voiding and to the carry
linearity (`deepFixedFamilyShellPersistence_iff_void`, `…_iff_carryLinear`) — the honest
no-free-lunch pattern — but as a TARGET the onset window has widened from `(0, X]` to
`(0, 2X − X/512]`.

## Part 5 — the excursion/block combinatorics (PROVED) and the named residual

* `scc_bandRun_of_exits_le` — the pigeonhole engine: `≤ e` exits (non-band gaps) in an
  index window of length `m` leave a contiguous band-run of length `len` with
  `m ≤ e + (e+1)·len` — few exits force a long persistent block.
* `FixedFamilyWindowExitBound ctx E` — the named count atom (the formalizable shadow of the
  I.3 first-entry/first-exit accounting): at most `E` exits in the start window.  PROVED
  consequence: a band-run of length `≥ (W−E)/(E+1)` inside the window
  (`fixedFamily_bandRun_of_windowExitBound`).
* HONEST LIMIT (recorded, not claimed): a finite in-window block does NOT void — the
  bootstrap's `WindowPeriodic` (DensityBootstrap) demands the FULL tail (`∀ n > x`), and a
  count bound alone cannot void by mass accounting either: a SINGLE giant gap (one exit)
  can pay the entire pressure floor, so exit COUNTS without exit-SIZE control prove
  nothing about the mass.  The manuscript's M.5/L.3 step bounds exit MASS, not exit count;
  no in-tree atom does either.  The closing link therefore remains exactly:
  supply `FixedFamilyShellPersistence` (weakest known: onset anywhere in the first
  `1023/1024` of the doubled shell) — equivalently the clean continuation / carry
  linearity at deep scales.

No `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Part 0.  Scale and parameter helpers -/

/-- The dyadic scale identity `X = 2^L` at the canonical ladder depth. -/
theorem scc_X_pow (ctx : ActualFailureContext) :
    ctx.shell.X = 2 ^ shellLadderDepth ctx :=
  Classical.choose_spec ctx.shell.hXdyadic

/-- `X ≥ 2^28` on every actual failure context (from the proved `L ≥ 28`). -/
theorem scc_X_ge (ctx : ActualFailureContext) : 268435456 ≤ ctx.shell.X := by
  rw [scc_X_pow ctx]
  calc (268435456 : ℕ) = 2 ^ 28 := by norm_num
    _ ≤ 2 ^ shellLadderDepth ctx :=
        Nat.pow_le_pow_right (by norm_num) (shellLadderDepth_ge ctx)

/-- The canonical descent order is the manuscript floor `r = ⌊κ·L⌋`. -/
theorem scc_r_eq_floor (ctx : ActualFailureContext) :
    ctx.n24CarryData.r
      = Nat.floor (manuscriptKappa * ((shellLadderDepth ctx : ℕ) : ℝ)) := by
  rw [cnlMulti_n24_r_eq]
  rfl

/-- `r ≤ κ·L` in real form. -/
theorem scc_r_le_kappaL (ctx : ActualFailureContext) :
    (ctx.n24CarryData.r : ℝ) ≤ manuscriptKappa * ((shellLadderDepth ctx : ℕ) : ℝ) := by
  rw [scc_r_eq_floor]
  exact Nat.floor_le (mul_nonneg manuscriptKappa_pos.le (Nat.cast_nonneg _))

/-- `κ·L < r + 1` in real form (the floor's defining upper bound). -/
theorem scc_kappaL_lt_r_succ (ctx : ActualFailureContext) :
    manuscriptKappa * ((shellLadderDepth ctx : ℕ) : ℝ) < (ctx.n24CarryData.r : ℝ) + 1 := by
  have h : ctx.n24CarryData.r
      = Nat.floor (manuscriptKappa * ((shellLadderDepth ctx : ℕ) : ℝ)) :=
    scc_r_eq_floor ctx
  rw [h]
  exact Nat.lt_floor_add_one _

/-- The start window has exactly `|supportShell|` indices. -/
theorem scc_starts_card (ctx : ActualFailureContext) :
    ctx.n24CarryData.starts.card = (supportShell ctx.shell.d ctx.shell.X).card := by
  rw [cnlMulti_starts_eq_window, Nat.card_Ico]
  omega

/-- Every carry-window start sits at or above the first in-shell hit index. -/
theorem scc_starts_mem_ge (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ ctx.n24CarryData.starts) :
    ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X ≤ k := by
  rw [cnlMulti_starts_eq_window, Finset.mem_Ico] at hk
  exact hk.1

/-- **The failure cap in numeric form**: `|supportShell| < (17/2^24)·X` (the pinned
`c₀ = κ/64 = 17/16777216`). -/
theorem scc_supportShell_lt (ctx : ActualFailureContext) :
    ((supportShell ctx.shell.d ctx.shell.X).card : ℝ)
      < 17 / 16777216 * (ctx.shell.X : ℝ) := by
  have h := ctx.hfailure
  have hc : erdos260Constants.c0 = manuscriptKappa / 64 := rfl
  rw [hc, towerKappa_eq] at h
  have he : (17 : ℝ) / 262144 / 64 * (ctx.X : ℝ) = 17 / 16777216 * (ctx.X : ℝ) := by
    norm_num
  rw [he] at h
  rw [ActualFailureContext.shell_d, ActualFailureContext.shell_X]
  exact h

/-! ## Part 1.  The counting-route verdict: classes 1 and 2 are starved

Class-1 members have `windowExcess = Y` EXACTLY; class-2 members have
`Y < windowExcess ≤ 2Y` (the `returnCls = 1` branch).  Their counts are capped by the
failure hypothesis itself: `|fibre_i| ≤ |starts| = |supportShell| < c₀·X`.  Both per-start
caps multiplied by the count cap fall a factor `> 512` below the pressure floor. -/

/-- **The class-2 per-start excess cap** `windowExcess ≤ 2Y` (the `returnCls = 1` pin). -/
theorem scc_class2_excess_le (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2) :
    windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
      ≤ 2 * ctx.n24CarryData.Y := by
  have hroute : genuineChargeRoute ctx k = 2 := (Finset.mem_filter.mp hk).2
  obtain ⟨_, _, hret⟩ := (genuineChargeRoute_eq_two_iff ctx k).mp hroute
  exact ((returnCls_eq_one_iff ctx k).mp hret).2

/-- Every routed class fibre is at most the support-shell count. -/
theorem scc_fibre_card_le (ctx : ActualFailureContext) (i : Fin 7) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i).card
      ≤ (supportShell ctx.shell.d ctx.shell.X).card := by
  rw [← scc_starts_card ctx]
  apply Finset.card_le_card
  intro k hk
  exact (mem_highExcessStarts.mp (Finset.mem_filter.mp hk).1).1

/-- The class-1 routed mass is at most `|supportShell|·Y`. -/
theorem scc_class1Mass_le (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 1
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card : ℝ) * ctx.n24CarryData.Y := by
  rw [routedClassMass_one_eq_card_mul_Y]
  apply mul_le_mul_of_nonneg_right _ (n24CarryData_Y_pos ctx).le
  exact_mod_cast scc_fibre_card_le ctx 1

/-- The class-2 routed mass is at most `|supportShell|·2Y`. -/
theorem scc_class2Mass_le (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card : ℝ)
          * (2 * ctx.n24CarryData.Y) := by
  rw [routedClassMassOf_eq_sum_fibre]
  have hY2 : (0 : ℝ) ≤ 2 * ctx.n24CarryData.Y := by
    have := n24CarryData_Y_pos ctx
    linarith
  calc ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
        windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
      ≤ ∑ _k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
          2 * ctx.n24CarryData.Y :=
        Finset.sum_le_sum (fun k hk => scc_class2_excess_le ctx hk)
    _ = ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).card : ℝ)
          * (2 * ctx.n24CarryData.Y) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((supportShell ctx.shell.d ctx.shell.X).card : ℝ)
          * (2 * ctx.n24CarryData.Y) := by
        apply mul_le_mul_of_nonneg_right _ hY2
        exact_mod_cast scc_fibre_card_le ctx 2

/-- Every routed class mass is nonnegative. -/
theorem scc_mass_nonneg (ctx : ActualFailureContext) (i : Fin 7) :
    0 ≤ routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) i := by
  rw [routedClassMassOf_eq_sum_fibre]
  exact Finset.sum_nonneg (fun k _ => windowExcess_nonneg _ _ _ _)

/-- **The proved Lemma 21.1 pressure floor against the seven-class partition**:
`cPr·X·(r+1) ≤ Σ_i mass_i`. -/
theorem scc_pressure_floor (ctx : ActualFailureContext) :
    erdos260Constants.cPr * (ctx.shell.X : ℝ) * ((ctx.n24CarryData.r : ℝ) + 1)
      ≤ ∑ i : Fin 7, routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) i := by
  rw [← highExcessMass_eq_sum_routedClassMassOf]
  exact ctx.n24CarryData.highExcessMass_lower

/-- **THE CLASS-1∪2 MASS DEFICIT (the counting-route verdict)**: the combined class-1 and
class-2 routed masses are at most `1/512` of the pressure floor — the pressure can NEVER
sit in the thin classes.  Pure counting: `mass₁+mass₂ ≤ |supportShell|·3Y < c₀X·(3L/64)`
vs `floor > (1/2)X·κL`, with `c₀ = κ/64`. -/
theorem scc_class12_deficit (ctx : ActualFailureContext) :
    512 * (routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 1
        + routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2)
      ≤ erdos260Constants.cPr * (ctx.shell.X : ℝ) * ((ctx.n24CarryData.r : ℝ) + 1) := by
  have hm1 := scc_class1Mass_le ctx
  have hm2 := scc_class2Mass_le ctx
  rw [n24CarryData_Y_eq_div] at hm1 hm2
  have hKc := (scc_supportShell_lt ctx).le
  have hrk := (scc_kappaL_lt_r_succ ctx).le
  rw [towerKappa_eq] at hrk
  have hLnn : (0 : ℝ) ≤ ((shellLadderDepth ctx : ℕ) : ℝ) := Nat.cast_nonneg _
  have hXnn : (0 : ℝ) ≤ (ctx.shell.X : ℝ) := Nat.cast_nonneg _
  have hKL : ((supportShell ctx.shell.d ctx.shell.X).card : ℝ)
        * ((shellLadderDepth ctx : ℕ) : ℝ)
      ≤ 17 / 16777216 * (ctx.shell.X : ℝ) * ((shellLadderDepth ctx : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_right hKc hLnn
  have hXr : (ctx.shell.X : ℝ) * (17 / 262144 * ((shellLadderDepth ctx : ℕ) : ℝ))
      ≤ (ctx.shell.X : ℝ) * ((ctx.n24CarryData.r : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hrk hXnn
  -- `erdos260Constants.cPr = 1/2` definitionally; `show` avoids the dependent-type rewrite
  show 512 * (routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 1
      + routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2)
    ≤ 1 / 2 * (ctx.shell.X : ℝ) * ((ctx.n24CarryData.r : ℝ) + 1)
  nlinarith [hm1, hm2, hKL, hXr]

/-- The class-2 mass alone is at most `1/512` of the pressure floor (corollary). -/
theorem scc_class2_deficit (ctx : ActualFailureContext) :
    512 * routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
      ≤ erdos260Constants.cPr * (ctx.shell.X : ℝ) * ((ctx.n24CarryData.r : ℝ) + 1) := by
  have h := scc_class12_deficit ctx
  have h1 := scc_mass_nonneg ctx 1
  linarith

/-! ## Part 2.  The per-datum band pins and the pressure relocation -/

/-- The orbit-band pin: from index `1` on, the recurrent slope orbit reads band `b`. -/
def OrbitBandPinned (ctx : ActualFailureContext) (b : ℕ) : Prop :=
  ∀ k, 1 ≤ k →
    canonGap (class1SlopeDatum ctx).q
      (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = b

/-- `(3,1)` pins band `2` everywhere (constant orbit at the fixed point `1`). -/
theorem orbitBandPinned_3_1 (ctx : ActualFailureContext)
    (h : (class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1) :
    OrbitBandPinned ctx 2 := by
  intro k _
  rw [h.1, h.2, slopeOrbit_three_one_const k]
  exact fixedCycleGap_3_1

/-- `(21,3)` pins band `3` everywhere (constant orbit at the fixed point `3`). -/
theorem orbitBandPinned_21_3 (ctx : ActualFailureContext)
    (h : (class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3) :
    OrbitBandPinned ctx 3 := by
  intro k _
  rw [h.1, h.2, slopeOrbit_twentyone_three_const k]
  exact fixedCycleGap_21_3

/-- `(15,1)` pins band `4` everywhere (constant orbit at the fixed point `1`). -/
theorem orbitBandPinned_15_1 (ctx : ActualFailureContext)
    (h : (class1SlopeDatum ctx).q = 15 ∧ (class1SlopeDatum ctx).K₀ = 1) :
    OrbitBandPinned ctx 4 := by
  intro k _
  rw [h.1, h.2, slopeOrbit_fifteen_one_const k]
  exact fixedCycleGap_15_1

/-- `(15,2)` pins band `4` from index `1` (one-step pre-period `2 → 1`). -/
theorem orbitBandPinned_15_2 (ctx : ActualFailureContext)
    (h : (class1SlopeDatum ctx).q = 15 ∧ (class1SlopeDatum ctx).K₀ = 2) :
    OrbitBandPinned ctx 4 := by
  intro k hk
  rw [h.1, h.2]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [slopeOrbit_fifteen_two_tail j]
  exact fixedCycleGap_15_1

/-- `(105,7)` pins band `4` everywhere (constant orbit at the fixed point `7`). -/
theorem orbitBandPinned_105_7 (ctx : ActualFailureContext)
    (h : (class1SlopeDatum ctx).q = 105 ∧ (class1SlopeDatum ctx).K₀ = 7) :
    OrbitBandPinned ctx 4 := by
  intro k _
  rw [h.1, h.2, slopeOrbit_oneOhFive_seven_const k]
  exact fixedCycleGap_105_7

/-- **At every fixed-family hit the orbit band is pinned to the recurrent band from
index `1` on** — the eventual constancy of the L.3.1 classifier at the five data. -/
theorem fixedFamilyHit_orbitBandPinned (ctx : ActualFailureContext)
    (hhit : FixedFamilyHit ctx) :
    OrbitBandPinned ctx (fixedFamilyRecurrentBand ctx) := by
  rcases hhit with ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩
  · have hb : fixedFamilyRecurrentBand ctx = 2 := by
      unfold fixedFamilyRecurrentBand
      rw [hq, hK]
      exact fixedFamilyBand_3_1
    rw [hb]
    exact orbitBandPinned_3_1 ctx ⟨hq, hK⟩
  · have hb : fixedFamilyRecurrentBand ctx = 3 := by
      unfold fixedFamilyRecurrentBand
      rw [hq, hK]
      exact fixedFamilyBand_21_3
    rw [hb]
    exact orbitBandPinned_21_3 ctx ⟨hq, hK⟩
  · have hb : fixedFamilyRecurrentBand ctx = 4 := by
      unfold fixedFamilyRecurrentBand
      rw [hq, hK]
      exact fixedFamilyBand_15_1
    rw [hb]
    exact orbitBandPinned_15_1 ctx ⟨hq, hK⟩
  · have hb : fixedFamilyRecurrentBand ctx = 4 := by
      unfold fixedFamilyRecurrentBand
      rw [hq, hK]
      exact fixedFamilyBand_15_2
    rw [hb]
    exact orbitBandPinned_15_2 ctx ⟨hq, hK⟩
  · have hb : fixedFamilyRecurrentBand ctx = 4 := by
      unfold fixedFamilyRecurrentBand
      rw [hq, hK]
      exact fixedFamilyBand_105_7
    rw [hb]
    exact orbitBandPinned_105_7 ctx ⟨hq, hK⟩

/-- The L.3.1 classifier under the band-2 pin: `returnPkg` at every `k ≥ 1`. -/
theorem scc_towerCls_of_pinned2 (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 2) {k : ℕ} (hk : 1 ≤ k) :
    towerClsOfShell ctx k = TowerExitClass.returnPkg := by
  rw [towerClsOfShell_eq_band, hpin k hk]
  rfl

/-- The L.3.1 classifier under the band-3 pin: `densePack` at every `k ≥ 1`. -/
theorem scc_towerCls_of_pinned3 (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 3) {k : ℕ} (hk : 1 ≤ k) :
    towerClsOfShell ctx k = TowerExitClass.densePack := by
  rw [towerClsOfShell_eq_band, hpin k hk]
  rfl

/-- The L.3.1 classifier under the band-4 pin: `cnlTail` at every `k ≥ 1`. -/
theorem scc_towerCls_of_pinned4 (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 4) {k : ℕ} (hk : 1 ≤ k) :
    towerClsOfShell ctx k = TowerExitClass.cnlTail := by
  rw [towerClsOfShell_eq_band, hpin k hk]
  rfl

/-- Fibre-emptiness engine: a route value excluded on every start empties the fibre. -/
theorem scc_fibre_empty_of_route_ne (ctx : ActualFailureContext) (i : Fin 7)
    (h : ∀ k, k ∈ ctx.n24CarryData.starts → genuineChargeRoute ctx k ≠ i) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro k hk
  have hmem := Finset.mem_filter.mp hk
  exact h k (mem_highExcessStarts.mp hmem.1).1 hmem.2

/-- An empty fibre carries zero routed mass. -/
theorem scc_mass_of_empty (ctx : ActualFailureContext) {i : Fin 7}
    (h : routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) i = 0 := by
  rw [routedClassMassOf_eq_sum_fibre, h, Finset.sum_empty]

/-- Window starts are positive (`0 ∉ starts`). -/
theorem scc_starts_pos (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ ctx.n24CarryData.starts) : 1 ≤ k := by
  rcases Nat.eq_zero_or_pos k with h | h
  · exact absurd (h ▸ hk) (zero_notMem_n24Starts ctx)
  · exact h

/-- Under the band-2 pin EVERY start routes to class 4 (the `returnPkg` branch). -/
theorem scc_route_of_pinned2 (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 2) {k : ℕ} (hk : 1 ≤ k) :
    genuineChargeRoute ctx k = 4 :=
  (genuineChargeRoute_eq_four_iff ctx k).mpr
    (Or.inl (scc_towerCls_of_pinned2 ctx hpin hk))

/-- Under the band-3 pin EVERY start routes to class 3 (the `densePack` branch). -/
theorem scc_route_of_pinned3 (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 3) {k : ℕ} (hk : 1 ≤ k) :
    genuineChargeRoute ctx k = 3 :=
  (genuineChargeRoute_eq_three_iff ctx k).mpr
    (scc_towerCls_of_pinned3 ctx hpin hk)

/-- Under the band-2 pin every fibre other than class 4 is EMPTY. -/
theorem band2_fibre_empty (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 2) (i : Fin 7) (hi : i ≠ 4) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ := by
  apply scc_fibre_empty_of_route_ne
  intro k hk hroute
  rw [scc_route_of_pinned2 ctx hpin (scc_starts_pos ctx hk)] at hroute
  exact hi hroute.symm

/-- Under the band-3 pin every fibre other than class 3 is EMPTY. -/
theorem band3_fibre_empty (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 3) (i : Fin 7) (hi : i ≠ 3) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ := by
  apply scc_fibre_empty_of_route_ne
  intro k hk hroute
  rw [scc_route_of_pinned3 ctx hpin (scc_starts_pos ctx hk)] at hroute
  exact hi hroute.symm

/-- Under the band-4 pin the class-0 (Chernoff) fibre is EMPTY. -/
theorem band4_fibre0_empty (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 4) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0 = ∅ := by
  apply scc_fibre_empty_of_route_ne
  intro k hk hroute
  have ht := (genuineChargeRoute_eq_zero_iff ctx k).mp hroute
  rw [scc_towerCls_of_pinned4 ctx hpin (scc_starts_pos ctx hk)] at ht
  exact TowerExitClass.noConfusion ht

/-- Under the band-4 pin the class-3 (DensePack) fibre is EMPTY. -/
theorem band4_fibre3_empty (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 4) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 3 = ∅ := by
  apply scc_fibre_empty_of_route_ne
  intro k hk hroute
  have ht := (genuineChargeRoute_eq_three_iff ctx k).mp hroute
  rw [scc_towerCls_of_pinned4 ctx hpin (scc_starts_pos ctx hk)] at ht
  exact TowerExitClass.noConfusion ht

/-- Under the band-4 pin the class-4 (Return) fibre is EMPTY: the `returnPkg` branch is
band-blocked, and the `cnlTail ∧ returnCls = 2` branch contradicts `runCls ≠ 1`. -/
theorem band4_fibre4_empty (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 4) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4 = ∅ := by
  apply scc_fibre_empty_of_route_ne
  intro k hk hroute
  have hk1 := scc_starts_pos ctx hk
  rcases (genuineChargeRoute_eq_four_iff ctx k).mp hroute with ht | ⟨_, hrun, hret⟩
  · rw [scc_towerCls_of_pinned4 ctx hpin hk1] at ht
    exact TowerExitClass.noConfusion ht
  · have hwlt : windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ctx.n24CarryData.T < 2 * ctx.n24CarryData.Y := by
      by_contra hge
      exact hrun ((runClsOfShell_eq_one_iff ctx k).mpr ⟨by omega, not_lt.mp hge⟩)
    by_cases hle : windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ctx.n24CarryData.T ≤ ctx.n24CarryData.Y
    · have h0 := (returnCls_eq_zero_iff ctx k).mpr hle
      rw [h0] at hret
      exact absurd hret (by decide)
    · have h1 := (returnCls_eq_one_iff ctx k).mpr ⟨lt_of_not_ge hle, hwlt.le⟩
      rw [h1] at hret
      exact absurd hret (by decide)

/-- **Band-2 relocation `(3,1)`**: the WHOLE pressure floor sits in class 4. -/
theorem band2_pressure_in_class4 (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 2) :
    erdos260Constants.cPr * (ctx.shell.X : ℝ) * ((ctx.n24CarryData.r : ℝ) + 1)
      ≤ routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 4 := by
  have hsum := scc_pressure_floor ctx
  rw [Fin.sum_univ_seven] at hsum
  have h0 := scc_mass_of_empty ctx (band2_fibre_empty ctx hpin 0 (by decide))
  have h1 := scc_mass_of_empty ctx (band2_fibre_empty ctx hpin 1 (by decide))
  have h2 := scc_mass_of_empty ctx (band2_fibre_empty ctx hpin 2 (by decide))
  have h3 := scc_mass_of_empty ctx (band2_fibre_empty ctx hpin 3 (by decide))
  have h5 := scc_mass_of_empty ctx (band2_fibre_empty ctx hpin 5 (by decide))
  have h6 := scc_mass_of_empty ctx (band2_fibre_empty ctx hpin 6 (by decide))
  linarith

/-- **Band-3 relocation `(21,3)`**: the WHOLE pressure floor sits in class 3. -/
theorem band3_pressure_in_class3 (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 3) :
    erdos260Constants.cPr * (ctx.shell.X : ℝ) * ((ctx.n24CarryData.r : ℝ) + 1)
      ≤ routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 3 := by
  have hsum := scc_pressure_floor ctx
  rw [Fin.sum_univ_seven] at hsum
  have h0 := scc_mass_of_empty ctx (band3_fibre_empty ctx hpin 0 (by decide))
  have h1 := scc_mass_of_empty ctx (band3_fibre_empty ctx hpin 1 (by decide))
  have h2 := scc_mass_of_empty ctx (band3_fibre_empty ctx hpin 2 (by decide))
  have h4 := scc_mass_of_empty ctx (band3_fibre_empty ctx hpin 4 (by decide))
  have h5 := scc_mass_of_empty ctx (band3_fibre_empty ctx hpin 5 (by decide))
  have h6 := scc_mass_of_empty ctx (band3_fibre_empty ctx hpin 6 (by decide))
  linarith

/-- **Band-4 relocation `(15,1)/(15,2)/(105,7)` — THE REVERSAL**: at least `511/512` of
the pressure floor sits in CLASS 5 (the heavy class `windowExcess ≥ 2Y`), NOT in class 2:
classes 0/3/4/6 are empty and classes 1∪2 are starved by the counting deficit. -/
theorem band4_pressure_in_class5 (ctx : ActualFailureContext)
    (hpin : OrbitBandPinned ctx 4) :
    511 / 512 * (erdos260Constants.cPr * (ctx.shell.X : ℝ)
        * ((ctx.n24CarryData.r : ℝ) + 1))
      ≤ routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5 := by
  have hsum := scc_pressure_floor ctx
  rw [Fin.sum_univ_seven] at hsum
  have h0 := scc_mass_of_empty ctx (band4_fibre0_empty ctx hpin)
  have h3 := scc_mass_of_empty ctx (band4_fibre3_empty ctx hpin)
  have h4 := scc_mass_of_empty ctx (band4_fibre4_empty ctx hpin)
  have h6 := genuineChargeRoute_routed6_zero ctx
  have h12 := scc_class12_deficit ctx
  linarith

/-- **The pressure-relocation verdict at every fixed-family hit** (the honest answer to
the brief's "the pressure mass MUST sit in class 2"): it never does — it sits in class 4
at `(3,1)`, class 3 at `(21,3)`, and (up to `1/512`) class 5 at the band-4 data. -/
theorem fixedFamilyHit_pressure_relocation (ctx : ActualFailureContext)
    (hhit : FixedFamilyHit ctx) :
    erdos260Constants.cPr * (ctx.shell.X : ℝ) * ((ctx.n24CarryData.r : ℝ) + 1)
        ≤ routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 4
      ∨ erdos260Constants.cPr * (ctx.shell.X : ℝ) * ((ctx.n24CarryData.r : ℝ) + 1)
          ≤ routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 3
      ∨ 511 / 512 * (erdos260Constants.cPr * (ctx.shell.X : ℝ)
            * ((ctx.n24CarryData.r : ℝ) + 1))
          ≤ routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5 := by
  rcases hhit with h | h | h | h | h
  · exact Or.inl (band2_pressure_in_class4 ctx (orbitBandPinned_3_1 ctx h))
  · exact Or.inr (Or.inl (band3_pressure_in_class3 ctx (orbitBandPinned_21_3 ctx h)))
  · exact Or.inr (Or.inr (band4_pressure_in_class5 ctx (orbitBandPinned_15_1 ctx h)))
  · exact Or.inr (Or.inr (band4_pressure_in_class5 ctx (orbitBandPinned_15_2 ctx h)))
  · exact Or.inr (Or.inr (band4_pressure_in_class5 ctx (orbitBandPinned_105_7 ctx h)))

/-! ## Part 3.  Persistence kills the pressure (the formal L.3 alternative) -/

/-- A constant-gap window sums exactly: `gapWindow = (r+1)·g`. -/
theorem scc_gapWindow_const {a : ℕ → ℕ} {k r g : ℕ}
    (h : ∀ i, i ≤ r → hitGap a (k + i) = g) :
    gapWindow (hitGap a) k r = (r + 1) * g := by
  unfold gapWindow
  rw [Finset.sum_congr rfl (fun i hi => h i (by
    rw [Finset.mem_range] at hi
    omega))]
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- **Persistent windows are LIGHT**: if all `r+1` gaps of `k`'s window equal the
recurrent band (`≤ 4`), the window excess VANISHES — `(r+1)·band ≤ 4(κL+1) < 2L+1 = T`. -/
theorem scc_windowExcess_zero_of_band_window (ctx : ActualFailureContext)
    (hhit : FixedFamilyHit ctx) {k : ℕ}
    (h : ∀ i, i ≤ ctx.n24CarryData.r →
      hitGap ctx.n24CarryData.a (k + i) = fixedFamilyRecurrentBand ctx) :
    windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
      = 0 := by
  have hb4 : fixedFamilyRecurrentBand ctx ≤ 4 :=
    (fixedFamilyRecurrentBand_bounds ctx hhit).2
  have hgw : gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
      = (ctx.n24CarryData.r + 1) * fixedFamilyRecurrentBand ctx :=
    scc_gapWindow_const h
  apply windowExcess_eq_zero_of_gapWindow_le
  rw [hgw, cnlMulti_n24_T_eq]
  have hr := scc_r_le_kappaL ctx
  rw [towerKappa_eq] at hr
  have hL28 : (28 : ℝ) ≤ ((shellLadderDepth ctx : ℕ) : ℝ) := by
    exact_mod_cast shellLadderDepth_ge ctx
  have hb4' : ((fixedFamilyRecurrentBand ctx : ℕ) : ℝ) ≤ 4 := by
    exact_mod_cast hb4
  have hrnn : (0 : ℝ) ≤ (ctx.n24CarryData.r : ℝ) := Nat.cast_nonneg _
  push_cast
  have hprod : ((ctx.n24CarryData.r : ℝ) + 1) * ((fixedFamilyRecurrentBand ctx : ℕ) : ℝ)
      ≤ ((ctx.n24CarryData.r : ℝ) + 1) * 4 :=
    mul_le_mul_of_nonneg_left hb4' (by linarith)
  linarith

/-- **The dual exit forcing (PROVED)**: every high-excess start's window CONTAINS an exit
(a non-band hit gap) — the trajectory cannot persist anywhere it pays pressure mass. -/
theorem scc_exit_in_window_of_highExcess (ctx : ActualFailureContext)
    (hhit : FixedFamilyHit ctx) {k : ℕ}
    (hk : k ∈ highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
        ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y) :
    ∃ i, i ≤ ctx.n24CarryData.r ∧
      hitGap ctx.n24CarryData.a (k + i) ≠ fixedFamilyRecurrentBand ctx := by
  by_contra hcon
  have hall : ∀ i, i ≤ ctx.n24CarryData.r →
      hitGap ctx.n24CarryData.a (k + i) = fixedFamilyRecurrentBand ctx := by
    intro i hi
    by_contra hne
    exact hcon ⟨i, hi, hne⟩
  have hzero := scc_windowExcess_zero_of_band_window ctx hhit hall
  have hY := (mem_highExcessStarts.mp hk).2
  have hYpos := n24CarryData_Y_pos ctx
  rw [hzero] at hY
  linarith

/-- **The index-persistence atom**: some onset index at or below the start window from
which ALL hit gaps equal the recurrent band. -/
def FixedFamilyIndexPersistence (ctx : ActualFailureContext) : Prop :=
  ∃ k₁, k₁ ≤ ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X ∧
    ∀ k, k₁ ≤ k → hitGap ctx.n24CarryData.a k = fixedFamilyRecurrentBand ctx

/-- Index persistence EMPTIES the high-excess start set. -/
theorem highExcessStarts_empty_of_indexPersistence (ctx : ActualFailureContext)
    (hhit : FixedFamilyHit ctx) (hp : FixedFamilyIndexPersistence ctx) :
    highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
      ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y = ∅ := by
  obtain ⟨k₁, hk₁, hg⟩ := hp
  rw [Finset.eq_empty_iff_forall_notMem]
  intro k hk
  obtain ⟨hstart, hY⟩ := mem_highExcessStarts.mp hk
  have hge : k₁ ≤ k := le_trans hk₁ (scc_starts_mem_ge ctx hstart)
  have hzero := scc_windowExcess_zero_of_band_window ctx hhit
    (k := k) (fun i _ => hg (k + i) (by omega))
  have hYpos := n24CarryData_Y_pos ctx
  rw [hzero] at hY
  linarith

/-- **PERSISTENCE CONTRADICTS THE PRESSURE FLOOR (the formal L.3 alternative)**: a
fixed-family context admits NO persistence onset at or below the start window — the
proved Lemma 21.1 floor `cPr·X·(r+1) > 0` cannot live on an empty high-excess set.
This holds at EVERY scale, with no bootstrap and no window-periodicity machinery. -/
theorem fixedFamilyIndexPersistence_void (ctx : ActualFailureContext)
    (hhit : FixedFamilyHit ctx) (hp : FixedFamilyIndexPersistence ctx) : False := by
  have hempty := highExcessStarts_empty_of_indexPersistence ctx hhit hp
  have hfloor := ctx.n24CarryData.highExcessMass_lower
  rw [hempty, highExcessMass_empty] at hfloor
  -- `erdos260Constants.cPr = 1/2` definitionally; retype to avoid the dependent rewrite
  have hfloor2 : (1 / 2 : ℝ) * (ctx.shell.X : ℝ) * ((ctx.n24CarryData.r : ℝ) + 1) ≤ 0 :=
    hfloor
  have hX := ctx.shell.X_pos_real
  have hr1 : (0 : ℝ) < (ctx.n24CarryData.r : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (ctx.n24CarryData.r : ℝ) := Nat.cast_nonneg _
    linarith
  nlinarith [mul_pos hX hr1, hfloor2]

/-- The clean continuation yields index persistence (`a k₀ ≤ X` forces
`k₀ < firstIndexAbove X`). -/
theorem fixedFamilyCleanContinuation_indexPersistence (ctx : ActualFailureContext)
    (hcc : FixedFamilyCleanContinuation ctx) : FixedFamilyIndexPersistence ctx := by
  obtain ⟨k₀, honset, hg⟩ := hcc
  refine ⟨k₀, ?_, hg⟩
  rcases Nat.lt_or_ge (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X) k₀
    with hcon | hle
  · exfalso
    have hspec := ctx.n24CarryData.carry.hits.firstIndexAbove_spec ctx.shell.X
    have hmono : ctx.n24CarryData.a
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X)
        ≤ ctx.n24CarryData.a k₀ :=
      ctx.n24CarryData.carry.hits.strict.monotone hcon.le
    -- `ctx.shell.X = ctx.X` definitionally; retype the onset to avoid the dependent rewrite
    have honset' : ctx.n24CarryData.a k₀ ≤ ctx.shell.X := honset
    omega
  · exact hle

/-- **The second, bootstrap-free voiding of the clean continuation** (per context, EVERY
scale): the E.6/E.7 clean continuation contradicts the pressure floor outright. -/
theorem fixedFamilyCleanContinuation_pressure_void (ctx : ActualFailureContext)
    (hhit : FixedFamilyHit ctx) (hcc : FixedFamilyCleanContinuation ctx) : False :=
  fixedFamilyIndexPersistence_void ctx hhit
    (fixedFamilyCleanContinuation_indexPersistence ctx hcc)

/-- The carry linearity is likewise pressure-void at every fixed-family hit (via the
proved E.14 bridge `fixedFamilyCleanContinuation_of_carryLinear`). -/
theorem fixedFamilyCarryLinear_pressure_void (ctx : ActualFailureContext)
    (hhit : FixedFamilyHit ctx) (hcl : FixedFamilyCarryLinear ctx) : False :=
  fixedFamilyCleanContinuation_pressure_void ctx hhit
    (fixedFamilyCleanContinuation_of_carryLinear ctx hhit hcl)

/-! ## Part 4.  The widened persistence target: shell persistence

The clean continuation demands the onset POSITION `a k₀ ≤ X`.  The support-count
mechanism below voids any onset position up to `(1023/512)·X = 2X − X/512`: once the
gaps are constant `= band ≤ 4` from `k₁`, the hits sweep an arithmetic progression of
step `≤ 4` through `(X, 2X]`, planting `≥ X/4096 − 1` support points — overwhelming the
failure cap `c₀·X = 17X/2²⁴` by a factor `≈ 2¹²/17`. -/

/-- AP-entry helper: a step-`b` progression starting at or below `X` enters `(X, X+b]`. -/
theorem scc_ap_enters (b X : ℕ) (hb : 0 < b) :
    ∀ t A, X ≤ A + t → A ≤ X →
      ∃ j, X < A + j * b ∧ A + j * b ≤ X + b := by
  intro t
  induction t with
  | zero =>
      intro A h1 h2
      exact ⟨1, by omega, by omega⟩
  | succ t ih =>
      intro A h1 h2
      by_cases hc : X < A + b
      · exact ⟨1, by omega, by omega⟩
      · obtain ⟨j, hj1, hj2⟩ := ih (A + b) (by omega) (by omega)
        refine ⟨1 + j, ?_, ?_⟩
        · have he : A + (1 + j) * b = A + b + j * b := by ring
          rw [he]
          exact hj1
        · have he : A + (1 + j) * b = A + b + j * b := by ring
          rw [he]
          exact hj2

/-- **The shell-persistence atom (the NEW, WIDER supply target)**: some onset `k₁` with
position `512·a k₁ ≤ 1023·X` (anywhere in the first `1023/1024` of the doubled shell)
from which ALL hit gaps equal the recurrent band. -/
def FixedFamilyShellPersistence (ctx : ActualFailureContext) : Prop :=
  ∃ k₁, 512 * ctx.n24CarryData.a k₁ ≤ 1023 * ctx.shell.X ∧
    ∀ k, k₁ ≤ k → hitGap ctx.n24CarryData.a k = fixedFamilyRecurrentBand ctx

/-- **SHELL PERSISTENCE IS VOID (PROVED, every scale)**: the band-stepped hit progression
floods the dyadic shell with `≥ X/4096 − 1 > c₀·X` support points, contradicting
`hfailure`. -/
theorem fixedFamilyShellPersistence_void (ctx : ActualFailureContext)
    (hhit : FixedFamilyHit ctx) (hp : FixedFamilyShellPersistence ctx) : False := by
  obtain ⟨k₁, honset, hg⟩ := hp
  obtain ⟨hb2, hb4⟩ := fixedFamilyRecurrentBand_bounds ctx hhit
  have hAP : ∀ m, ctx.n24CarryData.a (k₁ + m)
      = ctx.n24CarryData.a k₁ + m * fixedFamilyRecurrentBand ctx :=
    hitSequence_AP_of_const_gaps ctx.n24CarryData.carry.hits hg
  have hX28 : 268435456 ≤ ctx.shell.X := scc_X_ge ctx
  -- the entry index: the first AP point above `X`, with the unified 512-scaled bound
  obtain ⟨j, hj1, hj2⟩ :
      ∃ j, ctx.shell.X < ctx.n24CarryData.a k₁ + j * fixedFamilyRecurrentBand ctx
        ∧ 512 * (ctx.n24CarryData.a k₁ + j * fixedFamilyRecurrentBand ctx)
            ≤ 1023 * ctx.shell.X + 512 * fixedFamilyRecurrentBand ctx := by
    by_cases hXA : ctx.shell.X < ctx.n24CarryData.a k₁
    · exact ⟨0, by omega, by omega⟩
    · obtain ⟨j, hj1, hj2⟩ := scc_ap_enters (fixedFamilyRecurrentBand ctx) ctx.shell.X
        (by omega) ctx.shell.X (ctx.n24CarryData.a k₁) (by omega) (by omega)
      refine ⟨j, hj1, ?_⟩
      have h := Nat.mul_le_mul (le_refl 512) hj2
      generalize hP : ctx.n24CarryData.a k₁ + j * fixedFamilyRecurrentBand ctx = P at h ⊢
      omega
  -- the sweep stays inside `(X, 2X]` for `X/4096` steps
  have hlow : ∀ m, ctx.shell.X < ctx.n24CarryData.a (k₁ + (j + m)) := by
    intro m
    rw [hAP]
    have hmono : j * fixedFamilyRecurrentBand ctx
        ≤ (j + m) * fixedFamilyRecurrentBand ctx :=
      Nat.mul_le_mul (Nat.le_add_right j m) (le_refl _)
    generalize hP : (j + m) * fixedFamilyRecurrentBand ctx = P at hmono ⊢
    generalize hQ : j * fixedFamilyRecurrentBand ctx = Q at hmono hj1
    omega
  have hupper : ∀ m, m < ctx.shell.X / 4096 →
      ctx.n24CarryData.a (k₁ + (j + m)) ≤ 2 * ctx.shell.X := by
    intro m hm
    rw [hAP]
    have hexp : 512 * (ctx.n24CarryData.a k₁
          + (j + m) * fixedFamilyRecurrentBand ctx)
        = 512 * (ctx.n24CarryData.a k₁ + j * fixedFamilyRecurrentBand ctx)
          + 512 * (m * fixedFamilyRecurrentBand ctx) := by
      ring
    have hmb : 512 * (m * fixedFamilyRecurrentBand ctx) ≤ 512 * (m * 4) :=
      Nat.mul_le_mul (le_refl 512) (Nat.mul_le_mul (le_refl m) hb4)
    have h512 : 512 * (ctx.n24CarryData.a k₁
          + (j + m) * fixedFamilyRecurrentBand ctx)
        ≤ 1023 * ctx.shell.X + 512 * fixedFamilyRecurrentBand ctx + 512 * (m * 4) := by
      rw [hexp]
      exact Nat.add_le_add hj2 hmb
    generalize hP : ctx.n24CarryData.a k₁
        + (j + m) * fixedFamilyRecurrentBand ctx = P at h512 ⊢
    omega
  -- the swept hits are distinct support-shell members
  have hmem : ∀ m, m < ctx.shell.X / 4096 →
      ctx.n24CarryData.a (k₁ + (j + m)) ∈ supportShell ctx.shell.d ctx.shell.X := by
    intro m hm
    exact ctx.n24CarryData.carry.hits.hit_mem_supportShell (hlow m) (hupper m hm)
  have hcard : ctx.shell.X / 4096 ≤ (supportShell ctx.shell.d ctx.shell.X).card := by
    have hinj : Function.Injective
        (fun m => ctx.n24CarryData.a (k₁ + (j + m))) := by
      intro m₁ m₂ h
      have := ctx.n24CarryData.carry.hits.strict.injective h
      omega
    have hsub : (Finset.range (ctx.shell.X / 4096)).image
          (fun m => ctx.n24CarryData.a (k₁ + (j + m)))
        ⊆ supportShell ctx.shell.d ctx.shell.X := by
      intro x hx
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
      exact hmem m (Finset.mem_range.mp hm)
    calc ctx.shell.X / 4096
        = ((Finset.range (ctx.shell.X / 4096)).image
            (fun m => ctx.n24CarryData.a (k₁ + (j + m)))).card := by
          rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
      _ ≤ (supportShell ctx.shell.d ctx.shell.X).card := Finset.card_le_card hsub
  -- the count overwhelms the failure cap
  have hfail := scc_supportShell_lt ctx
  have hcardR : ((ctx.shell.X / 4096 : ℕ) : ℝ)
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card : ℝ) := by
    exact_mod_cast hcard
  have hnX : ctx.shell.X ≤ 4096 * (ctx.shell.X / 4096) + 4095 := by omega
  have hnXR : (ctx.shell.X : ℝ) ≤ 4096 * ((ctx.shell.X / 4096 : ℕ) : ℝ) + 4095 := by
    exact_mod_cast hnX
  have hXR : (268435456 : ℝ) ≤ (ctx.shell.X : ℝ) := by exact_mod_cast hX28
  linarith

/-- The clean continuation supplies shell persistence (`a k₀ ≤ X ⟹ 512·a k₀ ≤ 1023·X`):
the new atom is weaker-or-equal as a TARGET. -/
theorem fixedFamilyCleanContinuation_shellPersistence (ctx : ActualFailureContext)
    (hcc : FixedFamilyCleanContinuation ctx) : FixedFamilyShellPersistence ctx := by
  obtain ⟨k₀, honset, hg⟩ := hcc
  refine ⟨k₀, ?_, hg⟩
  rw [ActualFailureContext.shell_X]
  omega

/-! ## Part 5.  Excursion blocks and exits: the proved combinatorics and the named atom -/

/-- **The pigeonhole block engine**: `≤ e` exits (non-`g` gaps) in `[lo, lo+m)` leave a
contiguous `g`-run of length `len` with `m ≤ e + (e+1)·len` — few exits force a long
persistent block. -/
theorem scc_bandRun_of_exits_le (a : ℕ → ℕ) (g : ℕ) :
    ∀ e lo m : ℕ,
      ((Finset.Ico lo (lo + m)).filter (fun k => hitGap a k ≠ g)).card ≤ e →
      ∃ k₀ len, lo ≤ k₀ ∧ k₀ + len ≤ lo + m ∧
        (∀ i, i < len → hitGap a (k₀ + i) = g) ∧ m ≤ e + (e + 1) * len := by
  intro e
  induction e with
  | zero =>
      intro lo m hcard
      refine ⟨lo, m, le_rfl, le_rfl, ?_, by omega⟩
      intro i hi
      by_contra hne
      have hmem : lo + i ∈ (Finset.Ico lo (lo + m)).filter
          (fun k => hitGap a k ≠ g) :=
        Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hne⟩
      have := Finset.card_pos.mpr ⟨lo + i, hmem⟩
      omega
  | succ e ih =>
      intro lo m hcard
      by_cases hempty :
          (Finset.Ico lo (lo + m)).filter (fun k => hitGap a k ≠ g) = ∅
      · refine ⟨lo, m, le_rfl, le_rfl, ?_, ?_⟩
        · intro i hi
          by_contra hne
          have hmem : lo + i ∈ (Finset.Ico lo (lo + m)).filter
              (fun k => hitGap a k ≠ g) :=
            Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hne⟩
          rw [hempty] at hmem
          exact absurd hmem (Finset.notMem_empty _)
        · exact le_trans (Nat.le_mul_of_pos_left m (by omega))
            (Nat.le_add_left _ _)
      · have hne : ((Finset.Ico lo (lo + m)).filter
            (fun k => hitGap a k ≠ g)).Nonempty :=
          Finset.nonempty_of_ne_empty hempty
        have hpmem := Finset.min'_mem _ hne
        set p := ((Finset.Ico lo (lo + m)).filter
          (fun k => hitGap a k ≠ g)).min' hne with hpdef
        have hpIco := (Finset.mem_filter.mp hpmem).1
        rw [Finset.mem_Ico] at hpIco
        have hprefix : ∀ i, i < p - lo → hitGap a (lo + i) = g := by
          intro i hi
          by_contra hne'
          have hmem : lo + i ∈ (Finset.Ico lo (lo + m)).filter
              (fun k => hitGap a k ≠ g) :=
            Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hne'⟩
          have := Finset.min'_le _ _ hmem
          omega
        have htail_card : ((Finset.Ico (p + 1) (lo + m)).filter
            (fun k => hitGap a k ≠ g)).card ≤ e := by
          have hsub : (Finset.Ico (p + 1) (lo + m)).filter
                (fun k => hitGap a k ≠ g)
              ⊆ ((Finset.Ico lo (lo + m)).filter
                (fun k => hitGap a k ≠ g)).erase p := by
            intro x hx
            have hx' := Finset.mem_filter.mp hx
            rw [Finset.mem_Ico] at hx'
            refine Finset.mem_erase.mpr ⟨by omega, ?_⟩
            exact Finset.mem_filter.mpr
              ⟨Finset.mem_Ico.mpr ⟨by omega, hx'.1.2⟩, hx'.2⟩
          calc ((Finset.Ico (p + 1) (lo + m)).filter
                (fun k => hitGap a k ≠ g)).card
              ≤ (((Finset.Ico lo (lo + m)).filter
                  (fun k => hitGap a k ≠ g)).erase p).card :=
                Finset.card_le_card hsub
            _ = ((Finset.Ico lo (lo + m)).filter
                  (fun k => hitGap a k ≠ g)).card - 1 :=
                Finset.card_erase_of_mem hpmem
            _ ≤ e := by omega
        obtain ⟨k₀', len', hk1', hk2', hrun', hcount'⟩ :=
          ih (p + 1) (lo + m - (p + 1)) (by
            have hrw : p + 1 + (lo + m - (p + 1)) = lo + m := by omega
            rw [hrw]
            exact htail_card)
        by_cases hwhich : p - lo ≤ len'
        · refine ⟨k₀', len', by omega, by omega, hrun', ?_⟩
          have hexp : (e + 1 + 1) * len' = len' + (e + 1) * len' := by ring
          rw [hexp]
          generalize hT : (e + 1) * len' = T at hcount' ⊢
          omega
        · refine ⟨lo, p - lo, le_rfl, by omega, hprefix, ?_⟩
          have hexp : (e + 1 + 1) * (p - lo) = (p - lo) + (e + 1) * (p - lo) := by
            ring
          rw [hexp]
          have hmono : (e + 1) * len' ≤ (e + 1) * (p - lo) :=
            Nat.mul_le_mul (le_refl (e + 1)) (by omega)
          generalize hT1 : (e + 1) * len' = T1 at hcount' hmono
          generalize hT2 : (e + 1) * (p - lo) = T2 at hmono ⊢
          omega

/-- **The named count atom** (the formalizable shadow of the I.3 first-entry/first-exit
accounting): at most `E` exits (non-band hit gaps) in the carry start window. -/
def FixedFamilyWindowExitBound (ctx : ActualFailureContext) (E : ℕ) : Prop :=
  ((Finset.Ico (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X)
      (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
        + (supportShell ctx.shell.d ctx.shell.X).card)).filter
    (fun k => hitGap ctx.n24CarryData.a k ≠ fixedFamilyRecurrentBand ctx)).card ≤ E

/-- **PROVED chain link**: an exit-count bound forces a contiguous in-window band-run of
pigeonhole length: `W ≤ E + (E+1)·len`. -/
theorem fixedFamily_bandRun_of_windowExitBound (ctx : ActualFailureContext) {E : ℕ}
    (h : FixedFamilyWindowExitBound ctx E) :
    ∃ k₀ len,
      ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X ≤ k₀ ∧
      k₀ + len ≤ ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
        + (supportShell ctx.shell.d ctx.shell.X).card ∧
      (∀ i, i < len →
        hitGap ctx.n24CarryData.a (k₀ + i) = fixedFamilyRecurrentBand ctx) ∧
      (supportShell ctx.shell.d ctx.shell.X).card ≤ E + (E + 1) * len :=
  scc_bandRun_of_exits_le ctx.n24CarryData.a (fixedFamilyRecurrentBand ctx) E
    (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X)
    (supportShell ctx.shell.d ctx.shell.X).card h

/-! ## Part 6.  Deep forms, equivalences, and consumer wiring (additive) -/

/-- The deep shell-persistence supply Prop (demanded only at `X > 2^493443`). -/
def DeepFixedFamilyShellPersistence : Prop :=
  ∀ ctx : ActualFailureContext, 2 ^ 493443 < ctx.X → FixedFamilyHit ctx →
    FixedFamilyShellPersistence ctx

/-- Shell persistence discharges the deep family voiding. -/
theorem deepFixedFamilyVoid_of_shellPersistence
    (h : DeepFixedFamilyShellPersistence) : DeepFixedFamilyVoid :=
  fun ctx hX hhit => fixedFamilyShellPersistence_void ctx hhit (h ctx hX hhit)

/-- The honest no-free-lunch equivalence: the deep shell-persistence supply IS the deep
voiding (forward: the support-count contradiction; backward: vacuity). -/
theorem deepFixedFamilyShellPersistence_iff_void :
    DeepFixedFamilyShellPersistence ↔ DeepFixedFamilyVoid := by
  constructor
  · exact deepFixedFamilyVoid_of_shellPersistence
  · intro h ctx hX hhit
    exact absurd hhit (h ctx hX)

/-- Shell persistence has exactly the strength of the carry linearity (both equal the
deep voiding). -/
theorem deepFixedFamilyShellPersistence_iff_carryLinear :
    DeepFixedFamilyShellPersistence ↔ DeepFixedFamilyCarryLinear :=
  deepFixedFamilyShellPersistence_iff_void.trans
    deepFixedFamilyCarryLinear_iff_void.symm

/-- The clean continuation supplies the deep shell persistence (the supply burden
strictly drops: onset window `(0, X]` widens to `(0, 2X − X/512]`). -/
theorem deepFixedFamilyShellPersistence_of_cleanContinuation
    (h : DeepFixedFamilyCleanContinuation) : DeepFixedFamilyShellPersistence :=
  fun ctx hX hhit =>
    fixedFamilyCleanContinuation_shellPersistence ctx (h ctx hX hhit)

/-- The carry linearity supplies the deep shell persistence. -/
theorem deepFixedFamilyShellPersistence_of_carryLinear
    (h : DeepFixedFamilyCarryLinear) : DeepFixedFamilyShellPersistence :=
  fun ctx hX hhit =>
    fixedFamilyCleanContinuation_shellPersistence ctx
      (fixedFamilyCleanContinuation_of_carryLinear ctx hhit (h ctx hX hhit))

/-- **ALL FIVE families void at every scale under the shell-persistence supply.** -/
theorem fixedFamilyHit_void_of_shellPersistence
    (h : DeepFixedFamilyShellPersistence) (ctx : ActualFailureContext) :
    ¬ FixedFamilyHit ctx :=
  fixedFamilyHit_void_of_deepScale (deepFixedFamilyVoid_of_shellPersistence h) ctx

/-- Band-2 `(3,1)` void under the shell persistence. -/
theorem returnFixedFamily_void_of_shellPersistence
    (h : DeepFixedFamilyShellPersistence) (ctx : ActualFailureContext) :
    ¬((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1) :=
  fun hh => fixedFamilyHit_void_of_shellPersistence h ctx (Or.inl hh)

/-- Band-3 `(21,3)` void under the shell persistence. -/
theorem densePackFixedFamily_void_of_shellPersistence
    (h : DeepFixedFamilyShellPersistence) (ctx : ActualFailureContext) :
    ¬((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3) :=
  fun hh => fixedFamilyHit_void_of_shellPersistence h ctx (Or.inr (Or.inl hh))

/-- Band-4 `(15,1)` void under the shell persistence. -/
theorem towerFP15_1Family_void_of_shellPersistence
    (h : DeepFixedFamilyShellPersistence) (ctx : ActualFailureContext) :
    ¬((class1SlopeDatum ctx).q = 15 ∧ (class1SlopeDatum ctx).K₀ = 1) :=
  fun hh =>
    fixedFamilyHit_void_of_shellPersistence h ctx (Or.inr (Or.inr (Or.inl hh)))

/-- Band-4 `(15,2)` void under the shell persistence. -/
theorem towerFP15_2Family_void_of_shellPersistence
    (h : DeepFixedFamilyShellPersistence) (ctx : ActualFailureContext) :
    ¬((class1SlopeDatum ctx).q = 15 ∧ (class1SlopeDatum ctx).K₀ = 2) :=
  fun hh =>
    fixedFamilyHit_void_of_shellPersistence h ctx
      (Or.inr (Or.inr (Or.inr (Or.inl hh))))

/-- Band-4 `(105,7)` void under the shell persistence. -/
theorem towerFP105Family_void_of_shellPersistence
    (h : DeepFixedFamilyShellPersistence) (ctx : ActualFailureContext) :
    ¬((class1SlopeDatum ctx).q = 105 ∧ (class1SlopeDatum ctx).K₀ = 7) :=
  fun hh =>
    fixedFamilyHit_void_of_shellPersistence h ctx
      (Or.inr (Or.inr (Or.inr (Or.inr hh))))

/-- The collapsed tower escape surface under the shell persistence. -/
theorem towerEscapeLever_of_shellPersistence
    (h : DeepFixedFamilyShellPersistence) (ctx : ActualFailureContext)
    (hesc : TowerEscape ctx) : TowerEscapeLever ctx :=
  towerEscapeLever_of_towerEscape_deepFamilies
    (deepFixedFamilyVoid_of_shellPersistence h) ctx hesc

/-- The tower capstone field bridge under the shell persistence. -/
theorem towerFixedPointResidual_of_shellPersistence
    (h : DeepFixedFamilyShellPersistence) (hres : TowerLeverResidual) :
    TowerFixedPointResidual :=
  towerFixedPointResidual_of_deepFamilies
    (deepFixedFamilyVoid_of_shellPersistence h) hres

/-! ## Part 7.  Honest machine-readable status -/

/-- The precise status of the SCC recurrence-persistence pass. -/
def sccPersistenceStatus : List String :=
  [ "COUNTING-ROUTE VERDICT (PROVED, REVERSES the brief's expectation): the pressure " ++
      "mass can NEVER sit in class 2.  Classes 1 and 2 carry per-start excess caps " ++
      "(windowExcess = Y exactly on class 1; Y < windowExcess <= 2Y on class 2, " ++
      "scc_class2_excess_le) and their counts are capped by the failure hypothesis " ++
      "itself: |fibre_i| <= |starts| = |supportShell| < c0*X = 17X/2^24 " ++
      "(scc_fibre_card_le, scc_starts_card, scc_supportShell_lt).  Hence " ++
      "512*(mass1+mass2) <= cPr*X*(r+1) (scc_class12_deficit; scc_class2_deficit): " ++
      "classes 1 and 2 together absorb < 1/512 of the proved Lemma 21.1 floor.  The " ++
      "sliding-window engine is NOT needed: the c0*X count cap supersedes the " ++
      "(r+1)*64X/(129L) sliding cap.  The brief's own arithmetic (pressure floor " ++
      "below the sliding cap, ratio ~1/(128(r+1)^2)) is confirmed moot: counting " ++
      "alone does not void the context, but it DOES void the pressure-in-class-2 " ++
      "scenario outright.",
    "PRESSURE RELOCATION AT THE FIXED DATA (PROVED): the slope orbit is constant at " ++
      "each datum from index 1 (OrbitBandPinned, fixedFamilyHit_orbitBandPinned, via " ++
      "the in-tree fixed-point lemmas slopeOrbit_*_const/_tail), so towerClsOfShell " ++
      "is constant and the genuine route collapses: at (3,1) (band 2) EVERY start " ++
      "routes to class 4 - floor <= mass4 (band2_pressure_in_class4); at (21,3) " ++
      "(band 3) EVERY start routes to class 3 - floor <= mass3 " ++
      "(band3_pressure_in_class3); at (15,1)/(15,2)/(105,7) (band 4) classes 0/3/4/6 " ++
      "are EMPTY (band4_fibre*_empty) and (511/512)*floor <= mass5 " ++
      "(band4_pressure_in_class5): the recurrent pressure sits in the HEAVY class 5 " ++
      "(windowExcess >= 2Y), not in class 2.  Dispatcher: " ++
      "fixedFamilyHit_pressure_relocation.",
    "PERSISTENCE KILLS THE PRESSURE (PROVED - the formal content of the L.3 " ++
      "transient/persistent alternative): while the gaps follow the band (<= 4), " ++
      "every gap window is LIGHT - gapWindow = (r+1)*band <= 4(kappa*L+1) < 2L+1 = T, " ++
      "so windowExcess = 0 (scc_windowExcess_zero_of_band_window).  An onset index " ++
      "<= firstIndexAbove X (FixedFamilyIndexPersistence) therefore EMPTIES " ++
      "highExcessStarts and contradicts the PROVED pressure floor cPr*X*(r+1) > 0 " ++
      "(fixedFamilyIndexPersistence_void) - at EVERY scale, with no bootstrap.  " ++
      "Corollaries: the clean continuation and the carry linearity are pressure-void " ++
      "per context (fixedFamilyCleanContinuation_pressure_void, " ++
      "fixedFamilyCarryLinear_pressure_void) - a SECOND, independent voiding " ++
      "mechanism beside the wave-7 window-periodicity bootstrap.  Dual reading " ++
      "(PROVED): every high-excess start's window CONTAINS a non-band gap " ++
      "(scc_exit_in_window_of_highExcess) - recurrence forces transient excursions; " ++
      "the trajectory can never STAY while the failure persists.",
    "THE WIDENED SUPPLY TARGET (NEW; payoff PROVED): FixedFamilyShellPersistence - " ++
      "onset POSITION anywhere with 512*a(k1) <= 1023*X (i.e. a(k1) <= 2X - X/512, " ++
      "vs the old clean-continuation demand a(k0) <= X) plus band-constant tail.  " ++
      "VOID at every scale by raw support counting: the hits sweep an AP of step " ++
      "band in {2,3,4} through (X, 2X], planting >= X/4096 - 1 support points " ++
      "(scc_ap_enters, hitSequence_AP_of_const_gaps, hit_mem_supportShell), " ++
      "overwhelming hfailure's cap 17X/2^24 by a factor ~2^12/17 " ++
      "(fixedFamilyShellPersistence_void).  The clean continuation IMPLIES it " ++
      "(fixedFamilyCleanContinuation_shellPersistence), so the supply burden " ++
      "strictly drops.  No free lunch (PROVED): " ++
      "deepFixedFamilyShellPersistence_iff_void and _iff_carryLinear - the deep " ++
      "form has exactly the strength of the deep voiding / carry linearity.",
    "EXCURSION/BLOCK COMBINATORICS (PROVED): scc_bandRun_of_exits_le - <= e exits " ++
      "in an index window of length m leave a contiguous band-run of length len " ++
      "with m <= e + (e+1)*len (pigeonhole on the first exit, induction on e).  " ++
      "Named count atom FixedFamilyWindowExitBound ctx E (the formalizable shadow " ++
      "of the I.3 first-entry/first-exit accounting); proved consequence " ++
      "fixedFamily_bandRun_of_windowExitBound: a band-run of pigeonhole length " ++
      "inside the start window.",
    "HONEST LIMITS (recorded): (a) the bootstrap's WindowPeriodic " ++
      "(DensityBootstrap) demands the FULL tail (for all n > x, d(n+p) = d(n)) " ++
      "with onset x <= X and period 2p <= X - a finite in-window block does NOT " ++
      "void; (b) an exit COUNT bound alone cannot void by mass accounting: a " ++
      "single giant gap (ONE exit) pays the entire pressure floor, since the " ++
      "(r+1) window starts covering it each collect windowExcess ~ that gap - the " ++
      "manuscript's M.5/L.3 step controls exit MASS, not exit count, and no " ++
      "in-tree atom bounds either; (c) the index/shell persistence onsets are " ++
      "incomparable (firstIndexAbove X can sit at position up to 2X or beyond on " ++
      "thin shells), so both voidings are kept; (d) the onset-free eventual " ++
      "continuation (FixedFamilyEventualCleanContinuation) is NOT voided here: an " ++
      "onset beyond 2X - X/512 escapes both mechanisms at scale X - the onset " ++
      "placement remains the exact gap, consistent with HitToHitCarry.",
    "WHAT REMAINS (the named link): supply FixedFamilyShellPersistence at deep " ++
      "fixed-family contexts (equivalently DeepFixedFamilyCleanContinuation / " ++
      "DeepFixedFamilyCarryLinear; the shell form is the weakest known).  The " ++
      "manuscript's mechanism for it is the I.3.1 refined recurrent tower classes " ++
      "+ E.8 propagation + M.5 low-transient-exit mass accounting: recurrent " ++
      "states visited infinitely often with bounded exit MASS force the " ++
      "trajectory's gaps onto the band with onset inside the shell - none of " ++
      "which is formalized in-tree (the formalized tower atoms carry landing/" ++
      "count/window-match data only; no atom constrains exit mass or carry " ++
      "magnitude - HitToHitCarry's verdict, unchanged).",
    "CONSUMERS WIRED (additive): deepFixedFamilyVoid_of_shellPersistence, " ++
      "fixedFamilyHit_void_of_shellPersistence (all five families at every " ++
      "scale), the five per-family voidings *_void_of_shellPersistence, " ++
      "towerEscapeLever_of_shellPersistence, " ++
      "towerFixedPointResidual_of_shellPersistence, " ++
      "deepFixedFamilyShellPersistence_of_cleanContinuation / _of_carryLinear." ]

theorem sccPersistenceStatus_nonempty : sccPersistenceStatus ≠ [] := by
  simp [sccPersistenceStatus]

/-! ## Part 8.  Axiom-cleanliness audit -/

#print axioms scc_X_pow
#print axioms scc_X_ge
#print axioms scc_r_eq_floor
#print axioms scc_r_le_kappaL
#print axioms scc_kappaL_lt_r_succ
#print axioms scc_starts_card
#print axioms scc_starts_mem_ge
#print axioms scc_supportShell_lt
#print axioms scc_class2_excess_le
#print axioms scc_fibre_card_le
#print axioms scc_class1Mass_le
#print axioms scc_class2Mass_le
#print axioms scc_mass_nonneg
#print axioms scc_pressure_floor
#print axioms scc_class12_deficit
#print axioms scc_class2_deficit
#print axioms orbitBandPinned_3_1
#print axioms orbitBandPinned_21_3
#print axioms orbitBandPinned_15_1
#print axioms orbitBandPinned_15_2
#print axioms orbitBandPinned_105_7
#print axioms fixedFamilyHit_orbitBandPinned
#print axioms scc_fibre_empty_of_route_ne
#print axioms scc_mass_of_empty
#print axioms scc_route_of_pinned2
#print axioms scc_route_of_pinned3
#print axioms band2_fibre_empty
#print axioms band3_fibre_empty
#print axioms band4_fibre0_empty
#print axioms band4_fibre3_empty
#print axioms band4_fibre4_empty
#print axioms band2_pressure_in_class4
#print axioms band3_pressure_in_class3
#print axioms band4_pressure_in_class5
#print axioms fixedFamilyHit_pressure_relocation
#print axioms scc_gapWindow_const
#print axioms scc_windowExcess_zero_of_band_window
#print axioms scc_exit_in_window_of_highExcess
#print axioms highExcessStarts_empty_of_indexPersistence
#print axioms fixedFamilyIndexPersistence_void
#print axioms fixedFamilyCleanContinuation_indexPersistence
#print axioms fixedFamilyCleanContinuation_pressure_void
#print axioms fixedFamilyCarryLinear_pressure_void
#print axioms scc_ap_enters
#print axioms fixedFamilyShellPersistence_void
#print axioms fixedFamilyCleanContinuation_shellPersistence
#print axioms scc_bandRun_of_exits_le
#print axioms fixedFamily_bandRun_of_windowExitBound
#print axioms deepFixedFamilyVoid_of_shellPersistence
#print axioms deepFixedFamilyShellPersistence_iff_void
#print axioms deepFixedFamilyShellPersistence_iff_carryLinear
#print axioms deepFixedFamilyShellPersistence_of_cleanContinuation
#print axioms deepFixedFamilyShellPersistence_of_carryLinear
#print axioms fixedFamilyHit_void_of_shellPersistence
#print axioms returnFixedFamily_void_of_shellPersistence
#print axioms densePackFixedFamily_void_of_shellPersistence
#print axioms towerFP15_1Family_void_of_shellPersistence
#print axioms towerFP15_2Family_void_of_shellPersistence
#print axioms towerFP105Family_void_of_shellPersistence
#print axioms towerEscapeLever_of_shellPersistence
#print axioms towerFixedPointResidual_of_shellPersistence
#print axioms sccPersistenceStatus_nonempty

end

end Erdos260
