import Erdos260.Erdos260SharpCapstone

/-!
# DensePack class-3 cycle closure — wave 3: band-3 cycle checks, the `q = 7` fixed family,
and the budget-free cycle-split residual

This module (NEW; it edits no existing file) attacks the wave-2 capstone field
`densePackSplit : DensePackRegimeSplitResidual (sharpAtomBudget …)` with the orbit-cycle
machinery of `CNLClass1Closure`, mirrored onto the class-3 (band-3) pin of
`DensePackCorrectedClosure`.  Everything is proved from the routing/orbit arithmetic of the
canonical objects — no fabricated witnesses, no new axioms.

## What is newly closed here (all unconditional)

* **The class-3 parity pins** (`densePackStarts_start_pos`, `densePackStarts_orbit_odd`):
  every genuine dense start sits at a positive window index, so its orbit numerator is ODD.
* **The odd band-3 modulus window** (`band_three_odd_modulus_window`,
  `modulus_window_of_densePackStarts_nonempty`): an odd `K` with `4K ≤ q < 8K` forces
  `q ∈ {5, 7} ∪ {13, 15, …}`; hence the **NEW modulus closure**
  `densePackStarts_empty_of_modulus_window`: the dense start set is PROVABLY EMPTY on every
  shell with `8 ≤ q < 13` (`q ∈ {9, 11}`) — beyond the wave-2 `q < 5` closure.  On `q ≤ 7`
  the orbit numerator is pinned to `K_k = 1` exactly
  (`densePackStarts_orbit_eq_one_of_modulus_le_seven`).
* **The mod-period reduction** (`slopeOrbit_eq_mod_period`): with any period `c` valid from
  index `1`, `K_k = K_{1 + (k−1) mod c}` — every orbit reading happens at one of the `c`
  canonical cycle indices.
* **The finite band-3 cycle-check closures** (`densePackStarts_empty_of_orbit_band3_free`,
  `densePackStarts_empty_of_cycle_band3_free`, the named per-ctx Prop
  `Class3CycleBand3Free` with `densePackStarts_empty_of_cycleBand3Free`): a band-3-free
  period empties the dense start set — the exact class-3 mirror of
  `class1Fibre_empty_of_cycle_band_free`.  Instantiated families:
  `class3CycleBand3Free_of_modulus_lt_five`, `class3CycleBand3Free_of_modulus_window`
  (`q ∈ {9, 11}`), `class3CycleBand3Free_of_q7_unfixed`.
* **The top-band residue closers** (`Class3TopBandCycleFree`,
  `class3Interior_of_topBandCycleFree`, `densePackStarts_empty_of_gate_topBandCycleFree`):
  if the ≤ `r + 1` top-band window positions read non-band-3 cycle residues, the K.1
  interior holds on ALL shells (gated or not), and gated shells are empty outright.
* **The cycle-density count bound** (`cycleBand3Residues`,
  `densePackStarts_card_le_cycle_density`, existential form
  `densePackStarts_card_le_cycle_density_exists`):
  `|starts₃| ≤ b₃ · (⌊(K−1)/c⌋ + 2)` with `b₃` the per-cycle band-3 residue count — the
  class-3 cycle-density analogue of the width count `|starts₃| ≤ K`.  Concrete halving at
  `q = 5` (`densePackStarts_card_le_of_q5`: `b₃ ≤ 1` on the period-2 cycle `1 → 3`).
* **The `q = 7` dichotomy** (`densePackStarts_q7_dichotomy`): either the orbit enters the
  swap cycle `3 ↔ 5` (bands `2, 1`) and the start set is empty
  (`densePackStarts_empty_of_q7_unfixed`), or it is the all-ones band-3 FIXED POINT and the
  start set IS the bare gap-floor filter (`densePackStarts_eq_floorFilter_of_q7_fixed`).
  The fixed family genuinely defeats every cycle check
  (`not_class3CycleBand3Free_of_q7_fixed`) — there the count bounds must come from the
  gap-window pin, as wave 2 proved.
* **The gated characterization** (`densePackStarts_empty_iff_topBand_of_gate`, the q-7-fixed
  numeral form `densePackStarts_empty_iff_topBand_floor_of_gate_q7_fixed`,
  `densePackStarts_card_le_two_of_gate`): on gated shells emptiness IS the refutation of the
  two pins at the ≤ `r + 1 ≤ 2` top-band starts; at the `q = 7` fixed point the band pin is
  automatic, so gated emptiness is exactly ≤ 2 gap-floor refutations per shell.
* **The escape-gap blow-up** (`densePackStarts_escapeGap_of_gate_least`,
  `densePackStarts_escapeGap_of_r_eq_zero`): on a gated shell, a dense start whose window
  exactly reaches the shell-window top forces the single escape gap
  `hitGap a (i+K−1) > L + B + 1` — the quantified form of the wave-2 top-gap obstruction
  (the floor is NOT unrealizable at gated `r = 1` shells; it is realizable only through the
  model-unconstrained escape gap).
* **The cycle-density Nat cover** (`amortizedCover_of_cycle_density`): on `r ≥ 1` shells the
  corrected K.1.2 cover follows from the per-ctx Nat check
  `b₃ · (⌊(K−1)/c⌋ + 2) · ((r+1)(L+B+1) − (2L+1)) ≤ |proofV4DensePackActualPoints|` — the
  cycle-density sharpening of the wave-2 width form `amortizedCover_of_width_arith`.

## The wave-3 surface: `DensePackCycleSplitResidual`

A BUDGET-FREE structure whose four fields are the wave-2 regime-split fields guarded by the
failure of the corresponding cycle check (`¬ Class3TopBandCycleFree` for gated emptiness and
the interior, `¬ Class3CycleBand3Free` for density and the cover), with the cover stated in
exact `ℕ` form against the faithful marker count.  Bridges:

* `DensePackCycleSplitResidual.toRegimeSplit` — produces `DensePackRegimeSplitResidual
  budget` for EVERY budget (the capstone instantiates at `sharpAtomBudget`);
* `DensePackRegimeSplitResidual.toCycleSplit` — the converse weakening, so
  `nonempty_cycleSplit_iff_regimeSplit`: the two surfaces are EQUIVALENT — the wave-3
  presentation hides no strength and demands nothing on cycle-closed shells;
* `erdos260SharpResidualOfCycleSplit` / `erdos260_of_cycleSplit` — the drop-in capstone
  assembly with the class-3 slot carried by the cycle-split residual.

## The honest residual after this module

(a) Gated shells (`r ≤ 1`) whose top-band cycle residues contain band 3 (e.g. the `q = 7`
fixed point): the ≤ `r + 1 ≤ 2` gap-floor refutations — the floor lives on the
model-unconstrained escape gap, so it is not refutable at this layer.  (b) Ungated shells
(part of `r = 1`, all `r ≥ 2`) whose cycle contains band 3: the K.1.1 endpoint density, the
K.1 interior (only when the top-band residues meet band 3), and the corrected K.1.2 Nat
cover (now with the cycle-density count available against the faithful marker count).

No `sorry`, `admit`, new `axiom`, or `native_decide`.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 1.  The class-3 positivity/parity pins and the odd band-3 modulus window -/

/-- **Every genuine dense start sits at a positive window index** (the class-3 mirror of
`class1Fibre_start_pos`). -/
theorem densePackStarts_start_pos (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ genuineDensePackStarts ctx) : 1 ≤ k :=
  n24_starts_pos ctx (genuineDensePackStarts_subset_starts ctx hk)

/-- **The class-3 odd-numerator pin**: every genuine dense start has an ODD slope-orbit
numerator `K_k` (it sits at index `k ≥ 1` of the orbit). -/
theorem densePackStarts_orbit_odd (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ genuineDensePackStarts ctx) :
    Odd (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) :=
  slopeOrbit_odd (class1SlopeDatum ctx).hq_odd (class1SlopeDatum ctx).hK₀_pos
    (class1SlopeDatum ctx).hK₀_lt k (densePackStarts_start_pos ctx hk)

/-- **The odd band-3 modulus window**: an odd `K` in the E.13 band-3 window `4K ≤ q < 8K`
of an odd modulus forces `q ∈ {5, 7} ∪ {13, 15, …}` (the class-3 mirror of
`band_four_odd_modulus_window`). -/
theorem band_three_odd_modulus_window {q K : ℕ} (hq : Odd q) (hK : Odd K)
    (h4 : 4 * K ≤ q) (h8 : q < 8 * K) :
    5 ≤ q ∧ (q ≤ 7 ∨ 13 ≤ q) := by
  obtain ⟨m, hm⟩ := hq
  obtain ⟨n, hn⟩ := hK
  omega

/-- **The two-sided modulus window of a nonempty dense start set** (sharpens the wave-2
`modulus_ge_five_of_densePackStarts_nonempty`): the parity pin excludes the whole band
`8 ≤ q < 13`. -/
theorem modulus_window_of_densePackStarts_nonempty (ctx : ActualFailureContext)
    (h : (genuineDensePackStarts ctx).Nonempty) :
    5 ≤ (class1SlopeDatum ctx).q
      ∧ ((class1SlopeDatum ctx).q ≤ 7 ∨ 13 ≤ (class1SlopeDatum ctx).q) := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨h4, h8⟩ := densePackStarts_orbit_band ctx hk
  exact band_three_odd_modulus_window (class1SlopeDatum ctx).hq_odd
    (densePackStarts_orbit_odd ctx hk) h4 h8

/-- **NEW modulus-window closure**: the dense start set is PROVABLY EMPTY on every shell
whose closed AP-subfibre modulus lies in the band `8 ≤ q < 13` (`q ∈ {9, 11}`) — the only
band-3 numerator there is the even `K = 2`, while every window start carries an odd orbit
numerator. -/
theorem densePackStarts_empty_of_modulus_window (ctx : ActualFailureContext)
    (h8 : 8 ≤ (class1SlopeDatum ctx).q) (h13 : (class1SlopeDatum ctx).q < 13) :
    genuineDensePackStarts ctx = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro k hk
  obtain ⟨h5, hwin⟩ := modulus_window_of_densePackStarts_nonempty ctx ⟨k, hk⟩
  omega

/-- **The low-modulus orbit pin**: on every shell with `q ≤ 7` (so `q ∈ {5, 7}` after the
window closure), each dense start has its orbit numerator pinned to `K_k = 1` EXACTLY. -/
theorem densePackStarts_orbit_eq_one_of_modulus_le_seven (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q ≤ 7) {k : ℕ}
    (hk : k ∈ genuineDensePackStarts ctx) :
    slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k = 1 := by
  obtain ⟨h4, h8⟩ := densePackStarts_orbit_band ctx hk
  omega

/-- **The sharp class-3 membership characterization, wave 3**: the wave-2 form upgraded with
the two derived pins `1 ≤ k` and `Odd K_k` — still necessary AND sufficient. -/
theorem mem_densePackStarts_iff_sharp (ctx : ActualFailureContext) (k : ℕ) :
    k ∈ genuineDensePackStarts ctx
      ↔ k ∈ ctx.n24CarryData.starts
        ∧ 1 ≤ k
        ∧ Odd (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k)
        ∧ 129 * shellLadderDepth ctx + 64
            ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ canonGap (class1SlopeDatum ctx).q
            (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 3 := by
  constructor
  · intro hk
    obtain ⟨hstart, hgw, hband⟩ := (mem_densePackStarts_iff ctx k).mp hk
    exact ⟨hstart, densePackStarts_start_pos ctx hk, densePackStarts_orbit_odd ctx hk,
      hgw, hband⟩
  · rintro ⟨hstart, _, _, hgw, hband⟩
    exact (mem_densePackStarts_iff ctx k).mpr ⟨hstart, hgw, hband⟩

/-! ## Part 2.  The mod-period reduction

With any period `c` valid from index `1`, the orbit at `k ≥ 1` is its reading at the
canonical cycle index `1 + (k − 1) mod c ∈ [1, c]`.  This turns every orbit pin at a window
start into a pin at one of `c` checkable cycle indices. -/

private theorem slopeOrbit_mod_period_aux {q K₀ c : ℕ} (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m → slopeOrbit q K₀ (m + c) = slopeOrbit q K₀ m) :
    ∀ n k, 1 ≤ k → k ≤ c * (n + 1) →
      slopeOrbit q K₀ k = slopeOrbit q K₀ (1 + (k - 1) % c) := by
  intro n
  induction n with
  | zero =>
      intro k h1 hle
      have he0 : c * (0 + 1) = c := by ring
      have hmod : (k - 1) % c = k - 1 := Nat.mod_eq_of_lt (by omega)
      have he : 1 + (k - 1) % c = k := by omega
      rw [he]
  | succ n ih =>
      intro k h1 hle
      by_cases hle' : k ≤ c * (n + 1)
      · exact ih k h1 hle'
      · have hsplit : c * (n + 1 + 1) = c * (n + 1) + c := by ring
        have hcA : c ≤ c * (n + 1) := Nat.le_mul_of_pos_right c (by omega)
        have hck : c < k := by omega
        have hk1 : 1 ≤ k - c := by omega
        have hstep : slopeOrbit q K₀ k = slopeOrbit q K₀ (k - c) := by
          have h := hper (k - c) hk1
          rwa [Nat.sub_add_cancel (by omega : c ≤ k)] at h
        have hmod : (k - c - 1) % c = (k - 1) % c := by
          have he : k - 1 = (k - c - 1) + c := by omega
          rw [he, Nat.add_mod_right]
        rw [hstep, ih (k - c) hk1 (by omega), hmod]

/-- **The mod-period reduction**: with a period `c ≥ 1` valid from index `1`, the orbit
reading at any `k ≥ 1` is its reading at the canonical cycle index `1 + (k − 1) % c`. -/
theorem slopeOrbit_eq_mod_period {q K₀ c : ℕ} (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m → slopeOrbit q K₀ (m + c) = slopeOrbit q K₀ m)
    {k : ℕ} (hk : 1 ≤ k) :
    slopeOrbit q K₀ k = slopeOrbit q K₀ (1 + (k - 1) % c) :=
  slopeOrbit_mod_period_aux hc hper k k hk
    (le_trans (Nat.le_succ k) (Nat.le_mul_of_pos_left (k + 1) (by omega)))

/-! ## Part 3.  The finite band-3 cycle-check closures -/

/-- **Band-3-free-orbit closure**: if the orbit never reads band 3 at any positive index,
the dense start set is empty (the class-3 mirror of `class1Fibre_empty_of_orbit_band_free`). -/
theorem densePackStarts_empty_of_orbit_band3_free (ctx : ActualFailureContext)
    (h : ∀ j, 1 ≤ j → canonGap (class1SlopeDatum ctx).q
      (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) ≠ 3) :
    genuineDensePackStarts ctx = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro k hk
  exact h k (densePackStarts_start_pos ctx hk) (densePackStarts_canonGap_eq ctx hk)

/-- **The finite band-3 cycle-check closure**: if SOME period `c ≥ 1` of the orbit (valid
from index `1`) has all `c` of its band readings `≠ 3`, the dense start set is empty.
Combined with `class1Fibre_orbit_period_exists` (`c ≤ q`), the orbit side of the class-3
residual is decided by at most `q` canonical-gap evaluations per context — the exact mirror
of `class1Fibre_empty_of_cycle_band_free`. -/
theorem densePackStarts_empty_of_cycle_band3_free (ctx : ActualFailureContext) {c : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hband : ∀ j, 1 ≤ j → j ≤ c → canonGap (class1SlopeDatum ctx).q
      (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) ≠ 3) :
    genuineDensePackStarts ctx = ∅ := by
  apply densePackStarts_empty_of_orbit_band3_free ctx
  intro j hj
  rw [slopeOrbit_eq_mod_period hc hper hj]
  refine hband (1 + (j - 1) % c) (by omega) ?_
  have := Nat.mod_lt (j - 1) (show 0 < c by omega)
  omega

/-- **The named per-ctx band-3 cycle check**: some period of the recurrent orbit is
band-3-free.  A finite check (≤ `q` canonical-gap evaluations). -/
def Class3CycleBand3Free (ctx : ActualFailureContext) : Prop :=
  ∃ c, 1 ≤ c
    ∧ (∀ m, 1 ≤ m →
        slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
          = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    ∧ ∀ j, 1 ≤ j → j ≤ c → canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) ≠ 3

/-- The band-3 cycle check empties the dense start set. -/
theorem densePackStarts_empty_of_cycleBand3Free (ctx : ActualFailureContext)
    (h : Class3CycleBand3Free ctx) :
    genuineDensePackStarts ctx = ∅ := by
  obtain ⟨c, hc, hper, hband⟩ := h
  exact densePackStarts_empty_of_cycle_band3_free ctx hc hper hband

/-- A globally band-3-free cycle family closes the whole named emptiness atom
`Class3StartsEmpty` (hence the ENTIRE corrected class-3 atom, every budget). -/
theorem class3StartsEmpty_of_cycleBand3Free_all
    (h : ∀ ctx : ActualFailureContext, Class3CycleBand3Free ctx) :
    Class3StartsEmpty :=
  fun ctx => densePackStarts_empty_of_cycleBand3Free ctx (h ctx)

/-- **The named per-ctx TOP-BAND cycle check**: some period's cycle residues read non-band-3
at every top-band window position (`i + K ≤ k + r + 1`, `k < i + K`) — at most `r + 1`
residue evaluations. -/
def Class3TopBandCycleFree (ctx : ActualFailureContext) : Prop :=
  ∃ c, 1 ≤ c
    ∧ (∀ m, 1 ≤ m →
        slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
          = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    ∧ ∀ k, 1 ≤ k →
        ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card ≤ k + ctx.n24CarryData.r + 1 →
        k < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card →
        canonGap (class1SlopeDatum ctx).q
          (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀
            (1 + (k - 1) % c)) ≠ 3

/-- A band-3-free cycle is in particular top-band free. -/
theorem class3TopBandCycleFree_of_cycleBand3Free (ctx : ActualFailureContext)
    (h : Class3CycleBand3Free ctx) : Class3TopBandCycleFree ctx := by
  obtain ⟨c, hc, hper, hband⟩ := h
  refine ⟨c, hc, hper, fun k hk _ _ => hband (1 + (k - 1) % c) (by omega) ?_⟩
  have := Nat.mod_lt (k - 1) (show 0 < c by omega)
  omega

/-- **The K.1 interior from the top-band cycle check, on ALL shells** (gated or not): if the
top-band residues avoid band 3 on the cycle, every dense start is window-interior. -/
theorem class3Interior_of_topBandCycleFree (ctx : ActualFailureContext)
    (h : Class3TopBandCycleFree ctx) :
    ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r + 1
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card := by
  obtain ⟨c, hc, hper, hfree⟩ := h
  intro k hk
  by_contra hge
  rw [not_lt] at hge
  have h1 := densePackStarts_start_pos ctx hk
  have hwin := densePackStarts_mem_window ctx hk
  have hband := densePackStarts_canonGap_eq ctx hk
  rw [slopeOrbit_eq_mod_period hc hper h1] at hband
  exact hfree k h1 hge hwin.2 hband

/-- **Gated emptiness from the top-band cycle check** (via the wave-2 gate dichotomy). -/
theorem densePackStarts_empty_of_gate_topBandCycleFree (ctx : ActualFailureContext)
    (hg : class3Gate ctx) (h : Class3TopBandCycleFree ctx) :
    genuineDensePackStarts ctx = ∅ :=
  (class3Interior_iff_densePackStarts_empty ctx hg).mp
    (class3Interior_of_topBandCycleFree ctx h)

/-! ### Closed cycle families -/

/-- `q < 5`: the cycle check holds (band 3 is unreachable below `q = 5`). -/
theorem class3CycleBand3Free_of_modulus_lt_five (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q < 5) : Class3CycleBand3Free ctx := by
  obtain ⟨c, hc1, hcq, hper⟩ := class1Fibre_orbit_period_exists ctx
  refine ⟨c, hc1, hper, fun j hj1 hjc hband => ?_⟩
  have horb := slopeOrbit_mem (class1SlopeDatum ctx).hq_odd (class1SlopeDatum ctx).hK₀_pos
    (class1SlopeDatum ctx).hK₀_lt j
  obtain ⟨h4, h8⟩ := (canonGap_eq_three_iff horb.1).mp hband
  obtain ⟨m, hm⟩ := (class1SlopeDatum ctx).hq_odd
  omega

/-- `8 ≤ q < 13` (`q ∈ {9, 11}`): the cycle check holds — odd orbit values cannot read
band 3 there. -/
theorem class3CycleBand3Free_of_modulus_window (ctx : ActualFailureContext)
    (h8 : 8 ≤ (class1SlopeDatum ctx).q) (h13 : (class1SlopeDatum ctx).q < 13) :
    Class3CycleBand3Free ctx := by
  obtain ⟨c, hc1, hcq, hper⟩ := class1Fibre_orbit_period_exists ctx
  refine ⟨c, hc1, hper, fun j hj1 hjc hband => ?_⟩
  have horb := slopeOrbit_mem (class1SlopeDatum ctx).hq_odd (class1SlopeDatum ctx).hK₀_pos
    (class1SlopeDatum ctx).hK₀_lt j
  have hodd := slopeOrbit_odd (class1SlopeDatum ctx).hq_odd (class1SlopeDatum ctx).hK₀_pos
    (class1SlopeDatum ctx).hK₀_lt j hj1
  obtain ⟨h4, h8'⟩ := (canonGap_eq_three_iff horb.1).mp hband
  obtain ⟨hw1, hw2⟩ := band_three_odd_modulus_window (class1SlopeDatum ctx).hq_odd
    hodd h4 h8'
  omega

/-! ## Part 4.  The band-3 cycle residues and the cycle-density count bound -/

/-- **The band-3 residue set of one cycle period**: the residues `t ∈ [0, c)` whose cycle
index `1 + t` reads band 3. -/
def cycleBand3Residues (ctx : ActualFailureContext) (c : ℕ) : Finset ℕ :=
  (Finset.range c).filter (fun t => canonGap (class1SlopeDatum ctx).q
    (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (1 + t)) = 3)

/-- Membership in the band-3 residue set. -/
theorem mem_cycleBand3Residues (ctx : ActualFailureContext) (c t : ℕ) :
    t ∈ cycleBand3Residues ctx c
      ↔ t < c ∧ canonGap (class1SlopeDatum ctx).q
          (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (1 + t)) = 3 := by
  unfold cycleBand3Residues
  rw [Finset.mem_filter, Finset.mem_range]

/-- Every dense start's residue `(k − 1) % c` lies in the band-3 residue set. -/
theorem densePackStarts_residue_mem (ctx : ActualFailureContext) {c k : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hk : k ∈ genuineDensePackStarts ctx) :
    (k - 1) % c ∈ cycleBand3Residues ctx c := by
  have h1 := densePackStarts_start_pos ctx hk
  have hband := densePackStarts_canonGap_eq ctx hk
  rw [slopeOrbit_eq_mod_period hc hper h1] at hband
  rw [mem_cycleBand3Residues]
  exact ⟨Nat.mod_lt _ (by omega), hband⟩

private theorem nat_add_div_le_add_div_succ {a b c : ℕ} (hc : 0 < c) :
    (a + b) / c ≤ a / c + b / c + 1 := by
  have hkey : a + b < (a / c + b / c + 2) * c := by
    have ha := Nat.div_add_mod a c
    have hb := Nat.div_add_mod b c
    have ham : a % c < c := Nat.mod_lt _ hc
    have hbm : b % c < c := Nat.mod_lt _ hc
    calc a + b = c * (a / c) + a % c + (c * (b / c) + b % c) := by omega
      _ < c * (a / c) + c * (b / c) + 2 * c := by omega
      _ = (a / c + b / c + 2) * c := by ring
  have := (Nat.div_lt_iff_lt_mul hc).mpr hkey
  omega

/-- **The cycle-density count bound**: with a period `c` valid from index `1`, the dense
start set has at most `b₃ · (⌊(K−1)/c⌋ + 2)` elements, `b₃ = |cycleBand3Residues|` and
`K = |supportShell|` the window width — each band-3 residue class meets the window in at
most `⌊(K−1)/c⌋ + 2` starts. -/
theorem densePackStarts_card_le_cycle_density (ctx : ActualFailureContext) {c : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m) :
    (genuineDensePackStarts ctx).card
      ≤ (cycleBand3Residues ctx c).card
        * (((supportShell ctx.shell.d ctx.shell.X).card - 1) / c + 2) := by
  classical
  have hipos := n24_firstIndexAbove_pos ctx
  have hmain : (genuineDensePackStarts ctx).card
      ≤ ((cycleBand3Residues ctx c) ×ˢ
          Finset.range (((supportShell ctx.shell.d ctx.shell.X).card - 1) / c + 2)).card := by
    apply Finset.card_le_card_of_injOn (fun k =>
      ((k - 1) % c,
        (k - 1) / c
          - (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X - 1) / c))
    · intro k hk
      have h1 := densePackStarts_start_pos ctx hk
      have hwin := densePackStarts_mem_window ctx hk
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe]
      refine ⟨densePackStarts_residue_mem ctx hc hper hk, ?_⟩
      rw [Finset.mem_range]
      have hk_le : k - 1
          ≤ (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X - 1)
            + ((supportShell ctx.shell.d ctx.shell.X).card - 1) := by omega
      have hdiv : (k - 1) / c
          ≤ ((ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X - 1)
            + ((supportShell ctx.shell.d ctx.shell.X).card - 1)) / c :=
        Nat.div_le_div_right hk_le
      have hsplit : ((ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X - 1)
            + ((supportShell ctx.shell.d ctx.shell.X).card - 1)) / c
          ≤ (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X - 1) / c
            + ((supportShell ctx.shell.d ctx.shell.X).card - 1) / c + 1 :=
        nat_add_div_le_add_div_succ (by omega)
      have hmono : (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X - 1) / c
          ≤ (k - 1) / c := Nat.div_le_div_right (by omega)
      omega
    · intro k1 hk1 k2 hk2 heq
      have hk1' : k1 ∈ genuineDensePackStarts ctx := hk1
      have hk2' : k2 ∈ genuineDensePackStarts ctx := hk2
      have h11 := densePackStarts_start_pos ctx hk1'
      have h12 := densePackStarts_start_pos ctx hk2'
      have hw1 := densePackStarts_mem_window ctx hk1'
      have hw2 := densePackStarts_mem_window ctx hk2'
      have hmod : (k1 - 1) % c = (k2 - 1) % c := congrArg Prod.fst heq
      have hsub : (k1 - 1) / c
            - (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X - 1) / c
          = (k2 - 1) / c
            - (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X - 1) / c :=
        congrArg Prod.snd heq
      have hd1 : (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X - 1) / c
          ≤ (k1 - 1) / c := Nat.div_le_div_right (by omega)
      have hd2 : (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X - 1) / c
          ≤ (k2 - 1) / c := Nat.div_le_div_right (by omega)
      have hdiv : (k1 - 1) / c = (k2 - 1) / c := by omega
      have e1 := Nat.div_add_mod (k1 - 1) c
      have e2 := Nat.div_add_mod (k2 - 1) c
      rw [hdiv] at e1
      omega
  calc (genuineDensePackStarts ctx).card
      ≤ ((cycleBand3Residues ctx c) ×ˢ
          Finset.range (((supportShell ctx.shell.d ctx.shell.X).card - 1) / c + 2)).card :=
        hmain
    _ = (cycleBand3Residues ctx c).card
        * (((supportShell ctx.shell.d ctx.shell.X).card - 1) / c + 2) := by
        rw [Finset.card_product, Finset.card_range]

/-- **The unconditional cycle-density count** (no hypotheses): SOME period `1 ≤ c ≤ q`
carries the bound. -/
theorem densePackStarts_card_le_cycle_density_exists (ctx : ActualFailureContext) :
    ∃ c, 1 ≤ c ∧ c ≤ (class1SlopeDatum ctx).q
      ∧ (genuineDensePackStarts ctx).card
        ≤ (cycleBand3Residues ctx c).card
          * (((supportShell ctx.shell.d ctx.shell.X).card - 1) / c + 2) := by
  obtain ⟨c, hc1, hcq, hper⟩ := class1Fibre_orbit_period_exists ctx
  exact ⟨c, hc1, hcq, densePackStarts_card_le_cycle_density ctx hc1 hper⟩

/-! ### The `q = 5` showcase: period 2, at most ONE band-3 residue — the count is halved -/

/-- `canonGap 5 1 = 3` (the band-3 window `4 ≤ 5 < 8` at `K = 1`). -/
theorem canonGap_five_one : canonGap 5 1 = 3 := by
  unfold canonGap
  rw [Nat.div_one]
  have hlog : Nat.log 2 5 = 2 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  omega

/-- `canonGap 5 3 = 1` (band 1: `5 < 2·3`). -/
theorem canonGap_five_three : canonGap 5 3 = 1 := by
  unfold canonGap
  rw [show (5 : ℕ) / 3 = 1 from by norm_num]
  rw [Nat.log_one_right]

/-- The E.13 step at `q = 5` sends `1 ↦ 3` (`2³·1 − 5 = 3`). -/
theorem boundedSlopeStep_five_one : boundedSlopeStep 5 1 = 3 := by
  unfold boundedSlopeStep
  rw [canonGap_five_one]
  norm_num

/-- The E.13 step at `q = 5` sends `3 ↦ 1` (`2·3 − 5 = 1`). -/
theorem boundedSlopeStep_five_three : boundedSlopeStep 5 3 = 1 := by
  unfold boundedSlopeStep
  rw [canonGap_five_three]
  norm_num

/-- At `q = 5` the orbit has period `2` from index `1` (the swap cycle `1 ↔ 3`). -/
theorem slopeOrbit_five_period_two {K₀ : ℕ} (hK1 : 1 ≤ K₀) (hKq : K₀ < 5) :
    ∀ m, 1 ≤ m → slopeOrbit 5 K₀ (m + 2) = slopeOrbit 5 K₀ m := by
  have h5 : Odd 5 := Nat.odd_iff.mpr (by norm_num)
  intro m hm
  have hmem := slopeOrbit_mem h5 hK1 hKq m
  have hodd := slopeOrbit_odd h5 hK1 hKq m hm
  have hcase : slopeOrbit 5 K₀ m = 1 ∨ slopeOrbit 5 K₀ m = 3 := by
    obtain ⟨t, ht⟩ := hodd
    omega
  have hs1 : slopeOrbit 5 K₀ (m + 1) = boundedSlopeStep 5 (slopeOrbit 5 K₀ m) := rfl
  have hs2 : slopeOrbit 5 K₀ (m + 2) = boundedSlopeStep 5 (slopeOrbit 5 K₀ (m + 1)) := rfl
  rcases hcase with h | h
  · rw [hs2, hs1, h, boundedSlopeStep_five_one, boundedSlopeStep_five_three]
  · rw [hs2, hs1, h, boundedSlopeStep_five_three, boundedSlopeStep_five_one]

/-- **The `q = 5` halving**: the period-2 cycle `1 ↔ 3` reads band 3 at exactly one residue,
so `|starts₃| ≤ ⌊(K−1)/2⌋ + 2` — the cycle-density count strictly beats the width count for
`K ≥ 7`. -/
theorem densePackStarts_card_le_of_q5 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 5) :
    (genuineDensePackStarts ctx).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card - 1) / 2 + 2 := by
  have hKq : (class1SlopeDatum ctx).K₀ < 5 := by
    have := (class1SlopeDatum ctx).hK₀_lt
    omega
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 2)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq]
    exact slopeOrbit_five_period_two (class1SlopeDatum ctx).hK₀_pos hKq
  have hcount := densePackStarts_card_le_cycle_density ctx (by norm_num) hper
  have hres : (cycleBand3Residues ctx 2).card ≤ 1 := by
    by_contra hgt
    rw [not_le] at hgt
    have hsub : cycleBand3Residues ctx 2 ⊆ Finset.range 2 :=
      Finset.filter_subset _ _
    have hcard2 : (Finset.range 2).card ≤ (cycleBand3Residues ctx 2).card := by
      rw [Finset.card_range]
      omega
    have heq : cycleBand3Residues ctx 2 = Finset.range 2 :=
      Finset.eq_of_subset_of_card_le hsub hcard2
    have h0 : (0 : ℕ) ∈ cycleBand3Residues ctx 2 := by
      rw [heq]
      exact Finset.mem_range.mpr (by norm_num)
    have h1 : (1 : ℕ) ∈ cycleBand3Residues ctx 2 := by
      rw [heq]
      exact Finset.mem_range.mpr (by norm_num)
    rw [mem_cycleBand3Residues] at h0 h1
    have h0' : canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 1) = 3 := h0.2
    have h1' : canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 2) = 3 := h1.2
    have hmem1 := slopeOrbit_mem (class1SlopeDatum ctx).hq_odd
      (class1SlopeDatum ctx).hK₀_pos (class1SlopeDatum ctx).hK₀_lt 1
    have hodd1 := slopeOrbit_odd (class1SlopeDatum ctx).hq_odd
      (class1SlopeDatum ctx).hK₀_pos (class1SlopeDatum ctx).hK₀_lt 1 le_rfl
    have hlt5 : slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 1 < 5 := by
      have := hmem1.2
      omega
    have hcase : slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 1 = 1
        ∨ slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 1 = 3 := by
      obtain ⟨t, ht⟩ := hodd1
      have := hmem1.1
      omega
    have hs2 : slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 2
        = boundedSlopeStep (class1SlopeDatum ctx).q
            (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 1) := rfl
    rcases hcase with hone | hthree
    · have horb2 : slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 2 = 3 := by
        rw [hs2, hone, hq]
        exact boundedSlopeStep_five_one
      rw [horb2, hq, canonGap_five_three] at h1'
      omega
    · rw [hthree, hq, canonGap_five_three] at h0'
      omega
  calc (genuineDensePackStarts ctx).card
      ≤ (cycleBand3Residues ctx 2).card
        * (((supportShell ctx.shell.d ctx.shell.X).card - 1) / 2 + 2) := hcount
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card - 1) / 2 + 2) :=
        Nat.mul_le_mul_right _ hres
    _ = ((supportShell ctx.shell.d ctx.shell.X).card - 1) / 2 + 2 := one_mul _

/-! ## Part 5.  The `q = 7` family: the swap cycle closes, the fixed point is characterized -/

/-- `canonGap 7 3 = 2` (band 2: `2·3 ≤ 7 < 4·3`). -/
theorem canonGap_seven_three : canonGap 7 3 = 2 := by
  unfold canonGap
  rw [show (7 : ℕ) / 3 = 2 from by norm_num]
  have hlog : Nat.log 2 2 = 1 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  omega

/-- `canonGap 7 5 = 1` (band 1: `7 < 2·5`). -/
theorem canonGap_seven_five : canonGap 7 5 = 1 := by
  unfold canonGap
  rw [show (7 : ℕ) / 5 = 1 from by norm_num]
  rw [Nat.log_one_right]

/-- The E.13 step at `q = 7` sends `3 ↦ 5` (`4·3 − 7 = 5`). -/
theorem boundedSlopeStep_seven_three : boundedSlopeStep 7 3 = 5 := by
  unfold boundedSlopeStep
  rw [canonGap_seven_three]
  norm_num

/-- The E.13 step at `q = 7` sends `5 ↦ 3` (`2·5 − 7 = 3`). -/
theorem boundedSlopeStep_seven_five : boundedSlopeStep 7 5 = 3 := by
  unfold boundedSlopeStep
  rw [canonGap_seven_five]
  norm_num

/-- **The unfixed `q = 7` orbit is band-3-free**: if `K₁ ≠ 1` the orbit lives on the swap
cycle `3 ↔ 5` (bands `2, 1`) from index `1` on. -/
theorem slopeOrbit_seven_band3_free_of_unfixed {K₀ : ℕ} (hK1 : 1 ≤ K₀) (hKq : K₀ < 7)
    (h1 : slopeOrbit 7 K₀ 1 ≠ 1) :
    ∀ j, 1 ≤ j → canonGap 7 (slopeOrbit 7 K₀ j) ≠ 3 := by
  have h7 : Odd 7 := Nat.odd_iff.mpr (by norm_num)
  have key : ∀ j, 1 ≤ j → slopeOrbit 7 K₀ j = 3 ∨ slopeOrbit 7 K₀ j = 5 := by
    intro j
    induction j with
    | zero =>
        intro h
        omega
    | succ j ih =>
        intro _
        by_cases hj0 : 1 ≤ j
        · rcases ih hj0 with h3 | h5
          · right
            show boundedSlopeStep 7 (slopeOrbit 7 K₀ j) = 5
            rw [h3]
            exact boundedSlopeStep_seven_three
          · left
            show boundedSlopeStep 7 (slopeOrbit 7 K₀ j) = 3
            rw [h5]
            exact boundedSlopeStep_seven_five
        · have hj' : j = 0 := by omega
          subst hj'
          show slopeOrbit 7 K₀ 1 = 3 ∨ slopeOrbit 7 K₀ 1 = 5
          have hmem := slopeOrbit_mem h7 hK1 hKq 1
          have hodd := slopeOrbit_odd h7 hK1 hKq 1 le_rfl
          obtain ⟨t, ht⟩ := hodd
          have hub := hmem.2
          have hlb := hmem.1
          omega
  intro j hj
  rcases key j hj with h3 | h5
  · rw [h3, canonGap_seven_three]
    omega
  · rw [h5, canonGap_seven_five]
    omega

/-- **The fixed `q = 7` orbit is all-ones**: if `K₁ = 1` then `K_j = 1` at every `j ≥ 1`
(the band-3 fixed point of `boundedSlopeStep_seven_one`). -/
theorem slopeOrbit_seven_fixed_of_one {K₀ : ℕ} (hK1 : 1 ≤ K₀) (hKq : K₀ < 7)
    (h1 : slopeOrbit 7 K₀ 1 = 1) :
    ∀ j, 1 ≤ j → slopeOrbit 7 K₀ j = 1 := by
  intro j
  induction j with
  | zero =>
      intro h
      omega
  | succ j ih =>
      intro _
      by_cases hj0 : 1 ≤ j
      · have hjv := ih hj0
        show boundedSlopeStep 7 (slopeOrbit 7 K₀ j) = 1
        rw [hjv]
        exact boundedSlopeStep_seven_one
      · have hj' : j = 0 := by omega
        subst hj'
        exact h1

/-- **`q = 7`, unfixed: the dense start set is empty** (the swap cycle never reads band 3). -/
theorem densePackStarts_empty_of_q7_unfixed (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 7)
    (h1 : slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 1 ≠ 1) :
    genuineDensePackStarts ctx = ∅ := by
  apply densePackStarts_empty_of_orbit_band3_free ctx
  have hKq : (class1SlopeDatum ctx).K₀ < 7 := by
    have := (class1SlopeDatum ctx).hK₀_lt
    omega
  rw [hq] at h1 ⊢
  exact slopeOrbit_seven_band3_free_of_unfixed (class1SlopeDatum ctx).hK₀_pos hKq h1

/-- `q = 7`, unfixed: the band-3 cycle check holds. -/
theorem class3CycleBand3Free_of_q7_unfixed (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 7)
    (h1 : slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 1 ≠ 1) :
    Class3CycleBand3Free ctx := by
  obtain ⟨c, hc1, hcq, hper⟩ := class1Fibre_orbit_period_exists ctx
  refine ⟨c, hc1, hper, fun j hj1 hjc => ?_⟩
  have hKq : (class1SlopeDatum ctx).K₀ < 7 := by
    have := (class1SlopeDatum ctx).hK₀_lt
    omega
  rw [hq] at h1 ⊢
  exact slopeOrbit_seven_band3_free_of_unfixed (class1SlopeDatum ctx).hK₀_pos hKq h1 j hj1

/-- **The `q = 7` fixed point genuinely DEFEATS every cycle check**: every period reads
band 3 at its first index — the honest obstruction (count bounds there must come from the
gap-window pin, `band3_pin_all_indices_q7`). -/
theorem not_class3CycleBand3Free_of_q7_fixed (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 7)
    (h1 : slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 1 = 1) :
    ¬ Class3CycleBand3Free ctx := by
  rintro ⟨c, hc1, hper, hband⟩
  refine hband 1 le_rfl hc1 ?_
  rw [hq] at h1 ⊢
  rw [h1]
  exact canonGap_seven_one

/-- **`q = 7`, fixed: the dense start set IS the bare gap-floor filter** (the band pin holds
at EVERY window start, so only the high-excess floor selects). -/
theorem densePackStarts_eq_floorFilter_of_q7_fixed (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 7)
    (h1 : slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 1 = 1) :
    genuineDensePackStarts ctx
      = ctx.n24CarryData.starts.filter (fun k =>
          129 * shellLadderDepth ctx + 64
            ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r) := by
  have hKq : (class1SlopeDatum ctx).K₀ < 7 := by
    have := (class1SlopeDatum ctx).hK₀_lt
    omega
  have hfix : ∀ j, 1 ≤ j →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j = 1 := by
    rw [hq] at h1 ⊢
    exact slopeOrbit_seven_fixed_of_one (class1SlopeDatum ctx).hK₀_pos hKq h1
  ext k
  rw [mem_densePackStarts_iff, Finset.mem_filter]
  constructor
  · rintro ⟨hstart, hgw, _⟩
    exact ⟨hstart, hgw⟩
  · rintro ⟨hstart, hgw⟩
    refine ⟨hstart, hgw, ?_⟩
    rw [hfix k (n24_starts_pos ctx hstart), hq]
    exact canonGap_seven_one

/-- **The `q = 7` dichotomy**: the dense start set is empty outright, OR the orbit is the
all-ones band-3 fixed point and the start set is exactly the gap-floor filter. -/
theorem densePackStarts_q7_dichotomy (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 7) :
    genuineDensePackStarts ctx = ∅
      ∨ (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 1 = 1
          ∧ genuineDensePackStarts ctx
            = ctx.n24CarryData.starts.filter (fun k =>
                129 * shellLadderDepth ctx + 64
                  ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r)) := by
  by_cases h1 : slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 1 = 1
  · exact Or.inr ⟨h1, densePackStarts_eq_floorFilter_of_q7_fixed ctx hq h1⟩
  · exact Or.inl (densePackStarts_empty_of_q7_unfixed ctx hq h1)

/-! ## Part 6.  The gated regime: top-band characterization and the escape-gap blow-up -/

/-- Gated shells carry at most TWO dense starts (`card ≤ r + 1` with the gate pin
`r ≤ 1`). -/
theorem densePackStarts_card_le_two_of_gate (ctx : ActualFailureContext)
    (hg : class3Gate ctx) :
    (genuineDensePackStarts ctx).card ≤ 2 := by
  have h := densePackStarts_card_le_of_gapCeiling ctx hg
  have hr := class3Gate_r_le_one ctx hg
  omega

/-- **Gated emptiness IS the top-band pin refutation**: on a gated shell the dense start set
is empty iff no top-band window start (`i + K ≤ k + r + 1`) carries the gap floor AND the
band-3 pin simultaneously — at most `r + 1 ≤ 2` checks per shell. -/
theorem densePackStarts_empty_iff_topBand_of_gate (ctx : ActualFailureContext)
    (hg : class3Gate ctx) :
    genuineDensePackStarts ctx = ∅
      ↔ ∀ k ∈ ctx.n24CarryData.starts,
          ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card ≤ k + ctx.n24CarryData.r + 1 →
          ¬(129 * shellLadderDepth ctx + 64
                ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
            ∧ canonGap (class1SlopeDatum ctx).q
                (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 3) := by
  constructor
  · intro hempty k hstart htop hpins
    have hmem : k ∈ genuineDensePackStarts ctx :=
      (mem_densePackStarts_iff ctx k).mpr ⟨hstart, hpins.1, hpins.2⟩
    rw [hempty] at hmem
    exact Finset.notMem_empty k hmem
  · intro h
    rw [Finset.eq_empty_iff_forall_notMem]
    intro k hk
    have hmem := (mem_densePackStarts_iff ctx k).mp hk
    exact h k hmem.1 (densePackStarts_window_overrun ctx hk hg) ⟨hmem.2.1, hmem.2.2⟩

/-- **The gated `q = 7` fixed family characterized**: emptiness is EXACTLY the gap-floor
refutation at the ≤ `r + 1 ≤ 2` top-band window starts (the band pin is automatic on the
fixed orbit) — the minimal honest residual of the known hard family. -/
theorem densePackStarts_empty_iff_topBand_floor_of_gate_q7_fixed (ctx : ActualFailureContext)
    (hg : class3Gate ctx)
    (hq : (class1SlopeDatum ctx).q = 7)
    (h1 : slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 1 = 1) :
    genuineDensePackStarts ctx = ∅
      ↔ ∀ k ∈ ctx.n24CarryData.starts,
          ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card ≤ k + ctx.n24CarryData.r + 1 →
          ¬(129 * shellLadderDepth ctx + 64
              ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r) := by
  have hKq : (class1SlopeDatum ctx).K₀ < 7 := by
    have := (class1SlopeDatum ctx).hK₀_lt
    omega
  have hfix : ∀ j, 1 ≤ j →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j = 1 := by
    rw [hq] at h1 ⊢
    exact slopeOrbit_seven_fixed_of_one (class1SlopeDatum ctx).hK₀_pos hKq h1
  rw [densePackStarts_empty_iff_topBand_of_gate ctx hg]
  constructor
  · intro h k hstart htop hfloor
    refine h k hstart htop ⟨hfloor, ?_⟩
    rw [hfix k (n24_starts_pos ctx hstart), hq]
    exact canonGap_seven_one
  · intro h k hstart htop hpins
    exact h k hstart htop hpins.1

/-- **The escape-gap blow-up at the least top-band position**: on a gated shell, a dense
start whose descent window EXACTLY reaches the shell-window top must carry an escape gap
`hitGap a (k + r) = hitGap a (i + K − 1)` STRICTLY above the proved dyadic ceiling
`L + B + 1` — the gap floor is realizable only through the model-unconstrained first gap
after the shell. -/
theorem densePackStarts_escapeGap_of_gate_least (ctx : ActualFailureContext)
    (hg : class3Gate ctx) {k : ℕ} (hk : k ∈ genuineDensePackStarts ctx)
    (htop : k + ctx.n24CarryData.r + 1
        = ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + (supportShell ctx.shell.d ctx.shell.X).card) :
    shellLadderDepth ctx + carryB ctx.shell.Q + 1
      < hitGap ctx.n24CarryData.a (k + ctx.n24CarryData.r) := by
  by_contra hle
  rw [not_lt] at hle
  have hgap : ∀ m ∈ Finset.range (ctx.n24CarryData.r + 1),
      hitGap ctx.n24CarryData.a (k + m)
        ≤ shellLadderDepth ctx + carryB ctx.shell.Q + 1 := by
    intro m hm
    rw [Finset.mem_range] at hm
    by_cases hmr : m = ctx.n24CarryData.r
    · subst hmr
      exact hle
    · exact n24_hitGap_le_window ctx (by omega)
  have hsum : gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
      ≤ (ctx.n24CarryData.r + 1) * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) := by
    unfold gapWindow
    calc ∑ m ∈ Finset.range (ctx.n24CarryData.r + 1), hitGap ctx.n24CarryData.a (k + m)
        ≤ ∑ _m ∈ Finset.range (ctx.n24CarryData.r + 1),
            (shellLadderDepth ctx + carryB ctx.shell.Q + 1) := Finset.sum_le_sum hgap
      _ = (ctx.n24CarryData.r + 1) * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hfloor := ((mem_densePackStarts_iff ctx k).mp hk).2.1
  unfold class3Gate at hg
  have h64 : 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
      ≤ 64 * ((ctx.n24CarryData.r + 1)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) :=
    Nat.mul_le_mul_left 64 hsum
  omega

/-- **The `r = 0` escape-gap numeral form**: the (unique possible) dense start of an `r = 0`
shell carries a single gap STRICTLY above the dyadic ceiling `L + B + 1`. -/
theorem densePackStarts_escapeGap_of_r_eq_zero (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0) {k : ℕ} (hk : k ∈ genuineDensePackStarts ctx) :
    shellLadderDepth ctx + carryB ctx.shell.Q + 1 < hitGap ctx.n24CarryData.a k := by
  have htop := densePackStarts_top_of_r_eq_zero ctx hr hk
  have hmain := densePackStarts_escapeGap_of_gate_least ctx
    (class3Gate_of_r_eq_zero ctx hr) hk (by omega)
  rw [hr] at hmain
  simpa using hmain

/-! ## Part 7.  The cycle-density Nat cover -/

/-- **The deep-cover cycle-density sufficient form**: on `r ≥ 1` shells (any budget), the
corrected K.1.2 amortized cover follows from the per-ctx `ℕ` check
`b₃ · (⌊(K−1)/c⌋ + 2) · ((r+1)(L+B+1) − (2L+1)) ≤ |proofV4DensePackActualPoints|` — the
cycle-density sharpening of `amortizedCover_of_width_arith` against the faithful marker
count. -/
theorem amortizedCover_of_cycle_density
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (ctx : ActualFailureContext) (hr : 1 ≤ ctx.n24CarryData.r) {c : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (h : (cycleBand3Residues ctx c).card
          * (((supportShell ctx.shell.d ctx.shell.X).card - 1) / c + 2)
          * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
              - (2 * shellLadderDepth ctx + 1))
        ≤ (proofV4DensePackActualPoints ctx.shell).card) :
    ((genuineDensePackStarts ctx).card : ℝ) * densePackCorrectedMult ctx
      ≤ termDensePack (faithfulCapacityPhases budget ctx).toClosurePhaseData := by
  rw [amortizedCover_iff_nat_of_r_ge_one budget ctx hr]
  calc (genuineDensePackStarts ctx).card
        * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
            - (2 * shellLadderDepth ctx + 1))
      ≤ (cycleBand3Residues ctx c).card
          * (((supportShell ctx.shell.d ctx.shell.X).card - 1) / c + 2)
          * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
              - (2 * shellLadderDepth ctx + 1)) :=
        Nat.mul_le_mul_right _ (densePackStarts_card_le_cycle_density ctx hc hper)
    _ ≤ (proofV4DensePackActualPoints ctx.shell).card := h

/-! ## Part 8.  The wave-3 budget-free cycle-split residual and its bridges -/

/-- Ungated shells have descent order `r ≥ 1` (the gate is automatic at `r = 0`). -/
theorem n24_r_pos_of_not_class3Gate (ctx : ActualFailureContext)
    (hg : ¬ class3Gate ctx) : 1 ≤ ctx.n24CarryData.r := by
  by_contra h
  exact hg (class3Gate_of_r_eq_zero ctx (by omega))

/-- **The wave-3 cycle-split residual** — BUDGET-FREE, strictly smaller in presentation than
the wave-2 `DensePackRegimeSplitResidual`: each field is guarded by the FAILURE of the
corresponding proved cycle check (nothing is demanded on cycle-closed shells), and the cover
is the exact `ℕ` inequality against the faithful marker count.  Equivalent to the wave-2
surface at every budget (`nonempty_cycleSplit_iff_regimeSplit`). -/
structure DensePackCycleSplitResidual where
  /-- Gated shells whose top-band cycle residues meet band 3 (e.g. the `q = 7` fixed
  point): the dense start set is empty — equivalently the ≤ `r + 1 ≤ 2` top-band pin
  refutations (`densePackStarts_empty_iff_topBand_of_gate`). -/
  gatedEmpty : ∀ ctx : ActualFailureContext, class3Gate ctx →
    ¬ Class3TopBandCycleFree ctx → genuineDensePackStarts ctx = ∅
  /-- Ungated shells whose cycle meets band 3: the K.1.1 coarea hit-density at the descent
  endpoints. -/
  ungatedDensity : ∀ ctx : ActualFailureContext, ¬ class3Gate ctx →
    ¬ Class3CycleBand3Free ctx → densePackEndpointDensity ctx
  /-- Ungated shells whose top-band cycle residues meet band 3: the K.1 active-window
  interior containment. -/
  ungatedInterior : ∀ ctx : ActualFailureContext, ¬ class3Gate ctx →
    ¬ Class3TopBandCycleFree ctx →
    ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r + 1
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card
  /-- Ungated shells whose cycle meets band 3: the corrected K.1.2 cover in exact `ℕ` form
  against the faithful marker count (the cycle-density count bound is available against
  it, `amortizedCover_of_cycle_density`). -/
  ungatedCoverNat : ∀ ctx : ActualFailureContext, ¬ class3Gate ctx →
    ¬ Class3CycleBand3Free ctx →
    (genuineDensePackStarts ctx).card
        * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
            - (2 * shellLadderDepth ctx + 1))
      ≤ (proofV4DensePackActualPoints ctx.shell).card

namespace DensePackCycleSplitResidual

/-- **The bridge into the wave-2 capstone surface, at EVERY budget**: cycle-closed shells
discharge their fields through the proved cycle checks; the rest use the residual data.  The
cover converts through the faithful `ℕ` evaluation (`amortizedCover_iff_nat_of_r_ge_one`,
`r ≥ 1` on ungated shells). -/
def toRegimeSplit (R : DensePackCycleSplitResidual)
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx) :
    DensePackRegimeSplitResidual budget where
  gatedEmpty := fun ctx hg => by
    by_cases hfree : Class3TopBandCycleFree ctx
    · exact densePackStarts_empty_of_gate_topBandCycleFree ctx hg hfree
    · exact R.gatedEmpty ctx hg hfree
  ungatedDensity := fun ctx hg => by
    by_cases hfree : Class3CycleBand3Free ctx
    · exact densePackEndpointDensity_of_empty ctx
        (densePackStarts_empty_of_cycleBand3Free ctx hfree)
    · exact R.ungatedDensity ctx hg hfree
  ungatedInterior := fun ctx hg => by
    by_cases hfree : Class3TopBandCycleFree ctx
    · exact class3Interior_of_topBandCycleFree ctx hfree
    · exact R.ungatedInterior ctx hg hfree
  ungatedCover := fun ctx hg => by
    rw [amortizedCover_iff_nat_of_r_ge_one budget ctx (n24_r_pos_of_not_class3Gate ctx hg)]
    by_cases hfree : Class3CycleBand3Free ctx
    · rw [densePackStarts_empty_of_cycleBand3Free ctx hfree]
      simp
    · exact R.ungatedCoverNat ctx hg hfree

end DensePackCycleSplitResidual

/-- **The converse weakening**: any wave-2 regime-split provider (at any budget) restricts to
the wave-3 cycle-split surface — so the new surface hides no strength. -/
def DensePackRegimeSplitResidual.toCycleSplit
    {budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx}
    (R : DensePackRegimeSplitResidual budget) : DensePackCycleSplitResidual where
  gatedEmpty := fun ctx hg _ => R.gatedEmpty ctx hg
  ungatedDensity := fun ctx hg _ => R.ungatedDensity ctx hg
  ungatedInterior := fun ctx hg _ => R.ungatedInterior ctx hg
  ungatedCoverNat := fun ctx hg _ => by
    rw [← amortizedCover_iff_nat_of_r_ge_one budget ctx
      (n24_r_pos_of_not_class3Gate ctx hg)]
    exact R.ungatedCover ctx hg

/-- **The two surfaces are EQUIVALENT at every budget** — the wave-3 cycle-split residual is
exactly the wave-2 regime split with the proved cycle checks folded in. -/
theorem nonempty_cycleSplit_iff_regimeSplit
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx) :
    Nonempty DensePackCycleSplitResidual
      ↔ Nonempty (DensePackRegimeSplitResidual budget) :=
  ⟨fun ⟨R⟩ => ⟨R.toRegimeSplit budget⟩, fun ⟨S⟩ => ⟨S.toCycleSplit⟩⟩

/-! ## Part 9.  The capstone drop-in -/

/-- **The sharp capstone residual with the class-3 slot carried by the wave-3 cycle-split
residual** — the other six fields verbatim; `densePackSplit` is rebuilt through
`toRegimeSplit` at the canonical `sharpAtomBudget`. -/
def erdos260SharpResidualOfCycleSplit
    (towerCount : Class2DeepShellCountBound)
    (runSplit : ∀ ctx : ActualFailureContext, RunClass5SplitBoundary ctx)
    (returnSmall : Class4FibreSmall)
    (returnDigit : ∀ ctx : ActualFailureContext, ReturnClass4DigitResidual ctx)
    (class0Pinned : ∀ ctx : ActualFailureContext, ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q))
    (class1Pinned : ∀ ctx : ActualFailureContext, ∀ k ∈ ctx.n24CarryData.starts,
      1 ≤ k →
      64 ∣ shellLadderDepth ctx →
      9 ≤ (class1SlopeDatum ctx).q →
      ((class1SlopeDatum ctx).q ≤ 15 ∨ 25 ≤ (class1SlopeDatum ctx).q) →
      Odd (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) →
      64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
          = 129 * shellLadderDepth ctx + 64 →
      canonGap (class1SlopeDatum ctx).q
          (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) ≠ 4)
    (cycle : DensePackCycleSplitResidual) :
    Erdos260SharpResidual where
  towerCount := towerCount
  runSplit := runSplit
  returnSmall := returnSmall
  returnDigit := returnDigit
  class0Pinned := class0Pinned
  class1Pinned := class1Pinned
  densePackSplit := cycle.toRegimeSplit
    (sharpAtomBudget towerCount runSplit returnSmall returnDigit)

/-- **The final endpoint with the class-3 slot at the wave-3 cycle surface**:
`Erdos260Statement` from the six other sharp fields plus the budget-free cycle-split
residual. -/
theorem erdos260_of_cycleSplit
    (towerCount : Class2DeepShellCountBound)
    (runSplit : ∀ ctx : ActualFailureContext, RunClass5SplitBoundary ctx)
    (returnSmall : Class4FibreSmall)
    (returnDigit : ∀ ctx : ActualFailureContext, ReturnClass4DigitResidual ctx)
    (class0Pinned : ∀ ctx : ActualFailureContext, ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q))
    (class1Pinned : ∀ ctx : ActualFailureContext, ∀ k ∈ ctx.n24CarryData.starts,
      1 ≤ k →
      64 ∣ shellLadderDepth ctx →
      9 ≤ (class1SlopeDatum ctx).q →
      ((class1SlopeDatum ctx).q ≤ 15 ∨ 25 ≤ (class1SlopeDatum ctx).q) →
      Odd (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) →
      64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
          = 129 * shellLadderDepth ctx + 64 →
      canonGap (class1SlopeDatum ctx).q
          (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) ≠ 4)
    (cycle : DensePackCycleSplitResidual) :
    Erdos260Statement :=
  erdos260_of_sharpResidual (erdos260SharpResidualOfCycleSplit towerCount runSplit
    returnSmall returnDigit class0Pinned class1Pinned cycle)

/-! ## Part 10.  Machine-readable status (honest) -/

/-- Honest machine-readable status of the wave-3 class-3 cycle closure. -/
def densePackClass3CycleClosureStatus : List String :=
  [ "CLOSED (parity pins, NEW): every genuine dense start has k >= 1 " ++
      "(densePackStarts_start_pos) and an ODD orbit numerator K_k " ++
      "(densePackStarts_orbit_odd).",
    "CLOSED (odd band-3 modulus window, NEW): an odd K with 4K <= q < 8K forces " ++
      "q in {5,7} u {13,15,...} (band_three_odd_modulus_window, " ++
      "modulus_window_of_densePackStarts_nonempty); the dense start set is PROVABLY EMPTY " ++
      "on every shell with 8 <= q < 13, i.e. q in {9,11} " ++
      "(densePackStarts_empty_of_modulus_window) - a NEW closed modulus family beyond the " ++
      "wave-2 q < 5 closure. On q <= 7 the orbit numerator is pinned to K_k = 1 " ++
      "(densePackStarts_orbit_eq_one_of_modulus_le_seven). Sharp membership with both " ++
      "derived pins: mem_densePackStarts_iff_sharp.",
    "CLOSED (mod-period reduction, NEW): slopeOrbit_eq_mod_period - with any period c " ++
      "valid from index 1, K_k = K_{1 + (k-1) mod c}; every orbit pin at a window start " ++
      "is a pin at one of c checkable cycle indices.",
    "CLOSED (finite band-3 cycle checks, NEW - the class-3 mirror of " ++
      "class1Fibre_empty_of_cycle_band_free): a band-3-free period empties the dense " ++
      "start set (densePackStarts_empty_of_orbit_band3_free, " ++
      "densePackStarts_empty_of_cycle_band3_free, named Prop Class3CycleBand3Free with " ++
      "densePackStarts_empty_of_cycleBand3Free, global form " ++
      "class3StartsEmpty_of_cycleBand3Free_all). Closed families: q < 5 " ++
      "(class3CycleBand3Free_of_modulus_lt_five), q in {9,11} " ++
      "(class3CycleBand3Free_of_modulus_window), q = 7 with unfixed orbit " ++
      "(class3CycleBand3Free_of_q7_unfixed).",
    "CLOSED (top-band residue closers, NEW): Class3TopBandCycleFree (<= r+1 residue " ++
      "evaluations per ctx) gives the K.1 interior on ALL shells " ++
      "(class3Interior_of_topBandCycleFree) and gated emptiness " ++
      "(densePackStarts_empty_of_gate_topBandCycleFree); a band-3-free cycle is top-band " ++
      "free (class3TopBandCycleFree_of_cycleBand3Free).",
    "CLOSED (cycle-density count, NEW): |starts3| <= b3 * ((K-1)/c + 2) with b3 = " ++
      "|cycleBand3Residues ctx c| (densePackStarts_card_le_cycle_density; unconditional " ++
      "existential form densePackStarts_card_le_cycle_density_exists with c <= q). " ++
      "Concrete halving at q = 5: the period-2 swap cycle 1 <-> 3 has b3 <= 1, so " ++
      "|starts3| <= (K-1)/2 + 2 (densePackStarts_card_le_of_q5) - strictly beats the " ++
      "width count for K >= 7.",
    "CLOSED (the q = 7 dichotomy, NEW): densePackStarts_q7_dichotomy - either the orbit " ++
      "enters the swap cycle 3 <-> 5 (bands 2,1) and the start set is EMPTY " ++
      "(densePackStarts_empty_of_q7_unfixed, slopeOrbit_seven_band3_free_of_unfixed), or " ++
      "it is the all-ones band-3 fixed point (slopeOrbit_seven_fixed_of_one) and the " ++
      "start set IS the bare gap-floor filter " ++
      "(densePackStarts_eq_floorFilter_of_q7_fixed). The fixed family genuinely defeats " ++
      "every cycle check (not_class3CycleBand3Free_of_q7_fixed) - count bounds there " ++
      "must come from the gap-window pin, as wave 2 proved.",
    "CLOSED (gated characterization): on gated shells emptiness IS the refutation of the " ++
      "two pins at the <= r+1 <= 2 top-band starts " ++
      "(densePackStarts_empty_iff_topBand_of_gate, densePackStarts_card_le_two_of_gate); " ++
      "at the q = 7 fixed point the band pin is automatic, so gated emptiness is exactly " ++
      "<= 2 gap-floor refutations (densePackStarts_empty_iff_topBand_floor_of_gate_" ++
      "q7_fixed).",
    "OBSTRUCTION QUANTIFIED (the gate does NOT make the floor unrealizable at gated " ++
      "r = 1 shells): a dense start whose window exactly reaches the shell-window top " ++
      "must carry an escape gap hitGap a (i+K-1) STRICTLY above the dyadic ceiling " ++
      "L+B+1 (densePackStarts_escapeGap_of_gate_least; r = 0 numeral form " ++
      "densePackStarts_escapeGap_of_r_eq_zero). The first gap after the dyadic shell is " ++
      "model-unconstrained (wave-2 top-gap escape), so the floor remains realizable " ++
      "exactly there; gated emptiness is NOT closable at this layer and stays as the " ++
      "<= 2 per-shell floor checks.",
    "CLOSED (cycle-density Nat cover, NEW): on r >= 1 shells the corrected K.1.2 cover " ++
      "follows from b3 * ((K-1)/c + 2) * ((r+1)(L+B+1) - (2L+1)) <= " ++
      "|proofV4DensePackActualPoints| (amortizedCover_of_cycle_density) - the " ++
      "cycle-density sharpening of amortizedCover_of_width_arith against the faithful " ++
      "termDensePack value (termDensePack_faithful_eq).",
    "SURFACE (the wave-3 residual, budget-free): DensePackCycleSplitResidual - gatedEmpty/" ++
      "ungatedDensity/ungatedInterior/ungatedCoverNat, each guarded by the FAILURE of the " ++
      "matching proved cycle check (notTopBandCycleFree for gated emptiness and interior, " ++
      "not CycleBand3Free for density and cover), the cover in exact Nat form. Bridges: " ++
      "DensePackCycleSplitResidual.toRegimeSplit (produces DensePackRegimeSplitResidual " ++
      "budget for EVERY budget; ungated r >= 1 via n24_r_pos_of_not_class3Gate), " ++
      "DensePackRegimeSplitResidual.toCycleSplit (converse weakening), " ++
      "nonempty_cycleSplit_iff_regimeSplit (EQUIVALENT surfaces at every budget).",
    "CAPSTONE DROP-IN: erdos260SharpResidualOfCycleSplit / erdos260_of_cycleSplit - the " ++
      "sharp capstone with densePackSplit rebuilt from the budget-free cycle-split " ++
      "residual at sharpAtomBudget; the other six fields verbatim.",
    "RESIDUAL (honest, what remains open): (a) gated shells (r <= 1) whose top-band " ++
      "cycle residues contain band 3 (e.g. the q = 7 all-ones fixed point, reached iff " ++
      "K_1 = 1): the <= r+1 <= 2 per-shell gap-floor refutations - the floor lives on " ++
      "the model-unconstrained escape gap; (b) ungated shells (part of r = 1, all " ++
      "r >= 2) whose cycle contains band 3: the K.1.1 endpoint density, the K.1 " ++
      "interior (only when top-band residues meet band 3), and the corrected K.1.2 Nat " ++
      "cover (with the cycle-density count now available against the faithful marker " ++
      "count). No formalized bridge ties the digit-side floor to the orbit-side band " ++
      "beyond the shared index k; we do NOT claim unconditional closure of the atom." ]

theorem densePackClass3CycleClosureStatus_nonempty :
    densePackClass3CycleClosureStatus ≠ [] := by
  simp [densePackClass3CycleClosureStatus]

/-! ## Part 11.  Axiom-cleanliness audit -/

#print axioms densePackStarts_start_pos
#print axioms densePackStarts_orbit_odd
#print axioms band_three_odd_modulus_window
#print axioms modulus_window_of_densePackStarts_nonempty
#print axioms densePackStarts_empty_of_modulus_window
#print axioms densePackStarts_orbit_eq_one_of_modulus_le_seven
#print axioms mem_densePackStarts_iff_sharp
#print axioms slopeOrbit_eq_mod_period
#print axioms densePackStarts_empty_of_orbit_band3_free
#print axioms densePackStarts_empty_of_cycle_band3_free
#print axioms densePackStarts_empty_of_cycleBand3Free
#print axioms class3StartsEmpty_of_cycleBand3Free_all
#print axioms class3TopBandCycleFree_of_cycleBand3Free
#print axioms class3Interior_of_topBandCycleFree
#print axioms densePackStarts_empty_of_gate_topBandCycleFree
#print axioms class3CycleBand3Free_of_modulus_lt_five
#print axioms class3CycleBand3Free_of_modulus_window
#print axioms mem_cycleBand3Residues
#print axioms densePackStarts_residue_mem
#print axioms densePackStarts_card_le_cycle_density
#print axioms densePackStarts_card_le_cycle_density_exists
#print axioms canonGap_five_one
#print axioms canonGap_five_three
#print axioms boundedSlopeStep_five_one
#print axioms boundedSlopeStep_five_three
#print axioms slopeOrbit_five_period_two
#print axioms densePackStarts_card_le_of_q5
#print axioms canonGap_seven_three
#print axioms canonGap_seven_five
#print axioms boundedSlopeStep_seven_three
#print axioms boundedSlopeStep_seven_five
#print axioms slopeOrbit_seven_band3_free_of_unfixed
#print axioms slopeOrbit_seven_fixed_of_one
#print axioms densePackStarts_empty_of_q7_unfixed
#print axioms class3CycleBand3Free_of_q7_unfixed
#print axioms not_class3CycleBand3Free_of_q7_fixed
#print axioms densePackStarts_eq_floorFilter_of_q7_fixed
#print axioms densePackStarts_q7_dichotomy
#print axioms densePackStarts_card_le_two_of_gate
#print axioms densePackStarts_empty_iff_topBand_of_gate
#print axioms densePackStarts_empty_iff_topBand_floor_of_gate_q7_fixed
#print axioms densePackStarts_escapeGap_of_gate_least
#print axioms densePackStarts_escapeGap_of_r_eq_zero
#print axioms amortizedCover_of_cycle_density
#print axioms n24_r_pos_of_not_class3Gate
#print axioms DensePackCycleSplitResidual.toRegimeSplit
#print axioms DensePackRegimeSplitResidual.toCycleSplit
#print axioms nonempty_cycleSplit_iff_regimeSplit
#print axioms erdos260SharpResidualOfCycleSplit
#print axioms erdos260_of_cycleSplit
#print axioms densePackClass3CycleClosureStatus_nonempty

end

end Erdos260
