import Erdos260.ChernoffAreaUnconditional
import Erdos260.ReturnAnchoredUnconditional

/-!
# Erdős #260 — the class-0 (Chernoff) routed fibre of the genuine route, settled

This module (NEW; it edits no existing file) settles the routing arithmetic of the class-0
atom — the field `class0Empty : ∀ ctx, routedFibre ctx.n24CarryData ((sixAtomBudget …) ctx).route
0 = ∅` of `Erdos260SixAtomResidual` — to the same sharpness as the proved class-1
(`mem_class1Fibre_iff`, `CNLMultiChargeUnconditional`) and class-4 (`mem_class4Fibre_iff`,
`ReturnAnchoredUnconditional`) analyses, and strictly beyond them on `r = 0` shells.

## The route readout (CLOSED)

The genuine first-obstruction route reaches class `0` through EXACTLY ONE branch:
`towerClsOfShell ctx k = .other` (`genuineChargeRoute_eq_zero_iff`, proved upstream) — unlike
classes 1/2/4/5 there is NO exceptional `cnlTail` refinement branch.  The L.3.1 classifier is the
band readout of the closed AP-subfibre slope orbit (`towerClsOfShell_eq_band`), and
`towerExitClassOfGap g = .other ⟺ g = 0 ∨ g ≥ 5` (`towerExitClassOfGap_eq_other_iff`).  Since
`canonGap = log₂(q/K) + 1 ≥ 1` is NEVER `0` (`canonGap_ne_zero`), class 0 is exactly the DEEP
E.13 band `canonGap q K_k ≥ 5`, i.e. `16·K_k ≤ q` (`canonGap_ge_five_iff`,
`genuineChargeRoute_eq_zero_iff_canonGap` / `…_orbitBand`): the class-0 atom is the Chernoff
progress-endpoint band where the recurrent slope numerator has fallen to `K_k ≤ q/16`.

## The sharp membership characterization (CLOSED — the brief's target)

`mem_class0Fibre_iff` / `mem_class0Fibre_iff_orbitBand` / `class0Fibre_eq_pinnedFilter`:

  `k ∈ fibre₀ ⟺ k ∈ starts ∧ 129·L + 64 ≤ 64·gapWindow(k) ∧ canonGap q K_k ≥ 5 (⟺ 16·K_k ≤ q)`

— the exact class-0 analogue of `mem_class1Fibre_iff` (class 1 pins `64·gapWindow = 129L + 64`
EXACTLY and band `= 4`; class 4 pins the floor and band `= 2`; class 0 pins the floor and the
deep band `≥ 5`).  Hence `class0Fibre_empty_iff_pinned` and, for every v3-shaped budget
(`(budget ctx).route = genuineChargeRoute ctx` by `rfl`, including the capstone's
`sixAtomBudget`), `v3_class0FibreEmpty_iff_pinned`: the capstone field is EQUIVALENT to the
pinned arithmetic statement that no carry-window start realizes the high-excess gap-window floor
and the deep band simultaneously.

## Unconditional subfamily closures (CLOSED)

* **Small modulus**: a class-0 start needs `16·K_k ≤ q` with `K_k ≥ 1` and `q` odd, so `q ≥ 17`
  (`modulus_ge_seventeen_of_class0Fibre_nonempty`); the fibre is PROVABLY EMPTY on every shell
  with closed AP-subfibre modulus `< 17` (`class0Fibre_empty_of_modulus_lt_seventeen`,
  `v3_class0Fibre_empty_of_modulus_lt_seventeen`) — the class-0 mirror of the class-1 `q < 9`
  closure, with the strictly larger threshold of the deeper band.
* **Window confinement**: every HIGH-EXCESS start (hence every routed start of EVERY class)
  overruns the shell-window top under the numeric gate `64(r+1)(L+B+1) < 129L + 64`
  (`n24_highExcess_window_overrun`, the route-free generalization of the class-1/class-4
  overruns), so `|fibre₀| ≤ r + 1` under the gate (`class0Fibre_card_le_of_gapCeiling`) and
  `|fibre₀| ≤ 1` on every `r = ⌊κL⌋ = 0` shell — ALL `L ≤ 15420`
  (`class0Fibre_card_le_one_of_r_eq_zero`, `class0Fibre_card_le_one_of_L_le`).

## The `r = 0` EXACT closure (NEW — strictly sharper than the class-1/class-4 state)

On `r = 0` shells the pressure floor REMOVES the hit-gap pin from the residual: the proved
Lemma 21.1 floor makes `highExcessStarts` nonempty (`chernoffClass0_highExcessStarts_nonempty`),
and under the (automatic) gate every high-excess start is the SINGLE topmost window start, so

  `highExcessStarts = {top}`  (`highExcessStarts_eq_top_of_r_eq_zero`, `top = class0TopStart`).

Consequently the class-0 fibre on an `r = 0` shell is COMPLETELY DECIDED by the orbit band at
`top`:  `fibre₀ = ∅ ⟺ q < 16·K_top` and `fibre₀ = {top} ⟺ 16·K_top ≤ q`
(`class0Fibre_empty_iff_of_r_eq_zero`, `class0Fibre_eq_singleton_top_iff_of_r_eq_zero`,
numeral form `class0Fibre_empty_iff_of_L_le`).  The residual on the whole `L ≤ 15420` family is
the SINGLE arithmetic statement `q < 16·K_top` per shell — no gap-window input survives.
Cross-atom exclusions on `r = 0` shells: a nonempty class-1 OR class-4 fibre forces the class-0
fibre EMPTY (`class0Fibre_empty_of_class1Fibre_nonempty_of_r_eq_zero`,
`class0Fibre_empty_of_class4Fibre_nonempty_of_r_eq_zero`) — at most one top-band atom fires.

## Why NO unconditional emptiness theorem is claimed (honest boundary)

Full closure would need `q < 16·K_k` along the whole carry window on every shell.  The deep band
is genuinely reachable by the E.13 orbit (e.g. `q = 17`: the orbit `1 → 15 → 13 → 9 → 1` visits
`K = 1 ≤ q/16` every fourth step), and the formalization carries NO bridge between the hit
sequence (`hitGap`) and the slope orbit (`canonGap`) at the actual ctx — the same honest
obstruction recorded for class 1.  The pinned `iff` is therefore the exact boundary; by
`genuineAreaSeed_iff_class0FibreEmpty` no weaker class-0 input can exist.

## Consumers

`Class0FibreEmpty budget` names the capstone-shaped Prop; `class0FibreEmpty_of_genuineRoute_pinned`
(any budget routing through the genuine route), `class0FibreEmpty_of_pinned_arithmetic` (proved
obstructions folded in), the subfamily splits `class0FibreEmpty_of_modulus_ge_seventeen_case` /
`class0FibreEmpty_of_r_pos_case` (the `r = 0` half discharged by the band statement), the §22
surface equivalences `v3_genuineAreaSeed_iff_pinned` / `v3_chernoffKraftSmall_iff_pinned`, and
the P9 endpoint `erdos260_p9V3_of_class0PinnedArithmetic` feed the existing
`erdos260_p9V3_of_chernoffClass0Empty` / capstone consumers.

No `sorry`, `axiom`, `admit`, or `native_decide`; no fabricated witnesses — every emptiness
statement here is a THEOREM about the canonical routing arithmetic.
-/

namespace Erdos260

open Finset

set_option linter.unusedVariables false

noncomputable section

/-! ## 1.  The band readout: class 0 is the deep E.13 band `canonGap ≥ 5` -/

/-- The canonical-gap band index is never `0` (it is `log₂(q/K) + 1 ≥ 1`).  Hence the `g = 0`
case of the `.other` branch of `towerExitClassOfGap` is unreachable on slope orbits. -/
theorem canonGap_ne_zero (q K : ℕ) : canonGap q K ≠ 0 := by
  unfold canonGap
  omega

/-- The L.3.1 band classifier hits `.other` exactly on band index `0` or `≥ 5`. -/
theorem towerExitClassOfGap_eq_other_iff (g : ℕ) :
    towerExitClassOfGap g = TowerExitClass.other ↔ g = 0 ∨ 5 ≤ g := by
  constructor
  · intro h
    rcases g with _ | _ | _ | _ | _ | n
    · exact Or.inl rfl
    · cases h
    · cases h
    · cases h
    · cases h
    · exact Or.inr (by omega)
  · intro h
    rcases g with _ | _ | _ | _ | _ | n
    · rfl
    · exact absurd h (by omega)
    · exact absurd h (by omega)
    · exact absurd h (by omega)
    · exact absurd h (by omega)
    · rfl

/-- **The deep E.13 band window**: `canonGap q K ≥ 5` iff `16·K ≤ q` (for `K ≥ 1`) — the class-0
mirror of `canonGap_eq_four_iff` (class 1) and `canonGap_eq_two_iff` (class 4). -/
theorem canonGap_ge_five_iff {q K : ℕ} (hK : 1 ≤ K) :
    5 ≤ canonGap q K ↔ 16 * K ≤ q := by
  unfold canonGap
  constructor
  · intro h
    have hlog : 4 ≤ Nat.log 2 (q / K) := by omega
    have hne : q / K ≠ 0 := by
      intro h0
      rw [h0, Nat.log_zero_right] at hlog
      omega
    have h16 : 16 ≤ q / K := by
      have hpow := Nat.pow_log_le_self 2 hne
      have hmono : 2 ^ 4 ≤ 2 ^ Nat.log 2 (q / K) :=
        Nat.pow_le_pow_right (by norm_num) hlog
      have h24 : (2 : ℕ) ^ 4 = 16 := by norm_num
      omega
    exact (Nat.le_div_iff_mul_le hK).mp h16
  · intro h
    have h16 : 16 ≤ q / K := (Nat.le_div_iff_mul_le hK).mpr h
    have hlt := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (q / K)
    by_contra hcon
    have hle : Nat.log 2 (q / K) + 1 ≤ 4 := by omega
    have hmono : 2 ^ (Nat.log 2 (q / K) + 1) ≤ 2 ^ 4 :=
      Nat.pow_le_pow_right (by norm_num) hle
    have h24 : (2 : ℕ) ^ 4 = 16 := by norm_num
    omega

/-- **The class-0 route test IS the deep-band test (canonGap form).**  The genuine route assigns
`k` to class `0` iff the slope-orbit band index at `k` is `≥ 5`.  Class 0 has NO exceptional
route branch: the `g = 0` alternative of the `.other` readout is killed by `canonGap_ne_zero`. -/
theorem genuineChargeRoute_eq_zero_iff_canonGap (ctx : ActualFailureContext) (k : ℕ) :
    genuineChargeRoute ctx k = 0
      ↔ 5 ≤ canonGap (class1SlopeDatum ctx).q
          (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) := by
  rw [genuineChargeRoute_eq_zero_iff, towerClsOfShell_eq_band,
    towerExitClassOfGap_eq_other_iff]
  constructor
  · rintro (h0 | h5)
    · exact absurd h0 (canonGap_ne_zero _ _)
    · exact h5
  · exact fun h5 => Or.inr h5

/-- **The class-0 route test IS the deep-band test (orbit-band ℕ form)**: `route k = 0` iff
`16·K_k ≤ q`. -/
theorem genuineChargeRoute_eq_zero_iff_orbitBand (ctx : ActualFailureContext) (k : ℕ) :
    genuineChargeRoute ctx k = 0
      ↔ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
          ≤ (class1SlopeDatum ctx).q := by
  rw [genuineChargeRoute_eq_zero_iff_canonGap]
  have horb := slopeOrbit_mem (class1SlopeDatum ctx).hq_odd (class1SlopeDatum ctx).hK₀_pos
    (class1SlopeDatum ctx).hK₀_lt k
  exact canonGap_ge_five_iff horb.1

/-! ## 2.  The sharp class-0 membership characterization -/

/-- The class-0 routed fibre is definitionally the route-0 filter of the high-excess starts. -/
theorem class0Fibre_eq_highExcess_filter (ctx : ActualFailureContext) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0
      = (highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
          ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y).filter
            (fun k => genuineChargeRoute ctx k = 0) := rfl

/-- **The class-0 band pin**: every class-0 routed start of the genuine route has its slope-orbit
canonical-gap band index `≥ 5` (the deep Chernoff exit band). -/
theorem class0Fibre_canonGap_ge (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0) :
    5 ≤ canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) :=
  (genuineChargeRoute_eq_zero_iff_canonGap ctx k).mp (Finset.mem_filter.mp hk).2

/-- **The sharp class-0 membership characterization** (the class-0 analogue of
`mem_class1Fibre_iff` / `mem_class4Fibre_iff`): `k ∈ fibre₀` iff `k` is a carry-window start with
the high-excess gap-window floor `129L + 64 ≤ 64·gapWindow` and the deep E.13 band pin
`canonGap q K_k ≥ 5`. -/
theorem mem_class0Fibre_iff (ctx : ActualFailureContext) (k : ℕ) :
    k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0
      ↔ k ∈ ctx.n24CarryData.starts
        ∧ 129 * shellLadderDepth ctx + 64
            ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 5 ≤ canonGap (class1SlopeDatum ctx).q
            (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) := by
  constructor
  · intro hk
    have hhigh := mem_highExcessStarts.mp (Finset.mem_filter.mp hk).1
    exact ⟨hhigh.1, (Y_le_windowExcess_iff_gapWindow ctx k).mp hhigh.2,
      class0Fibre_canonGap_ge ctx hk⟩
  · rintro ⟨hstart, hgw, hband⟩
    exact Finset.mem_filter.mpr
      ⟨mem_highExcessStarts.mpr ⟨hstart, (Y_le_windowExcess_iff_gapWindow ctx k).mpr hgw⟩,
        (genuineChargeRoute_eq_zero_iff_canonGap ctx k).mpr hband⟩

/-- The membership characterization in pure orbit-band ℕ arithmetic: `k ∈ fibre₀` iff `k` is a
window start with `129L + 64 ≤ 64·gapWindow(k)` and `16·K_k ≤ q`. -/
theorem mem_class0Fibre_iff_orbitBand (ctx : ActualFailureContext) (k : ℕ) :
    k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0
      ↔ k ∈ ctx.n24CarryData.starts
        ∧ 129 * shellLadderDepth ctx + 64
            ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q := by
  rw [mem_class0Fibre_iff]
  have horb := slopeOrbit_mem (class1SlopeDatum ctx).hq_odd (class1SlopeDatum ctx).hK₀_pos
    (class1SlopeDatum ctx).hK₀_lt k
  rw [canonGap_ge_five_iff horb.1]

/-- **The class-0 fibre IS the doubly-pinned window filter** (irreducible arithmetic form). -/
theorem class0Fibre_eq_pinnedFilter (ctx : ActualFailureContext) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0
      = ctx.n24CarryData.starts.filter (fun k =>
          129 * shellLadderDepth ctx + 64
              ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
            ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
                ≤ (class1SlopeDatum ctx).q) := by
  ext k
  rw [Finset.mem_filter, mem_class0Fibre_iff_orbitBand]

/-! ## 3.  Orbit-band corollaries and the small-modulus closure -/

/-- **The class-0 orbit-band pin**: the slope-orbit numerator at every class-0 start has fallen
into the deep band `16·K_k ≤ q`, i.e. `K_k ≤ q/16`. -/
theorem class0Fibre_orbit_band (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0) :
    16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
      ≤ (class1SlopeDatum ctx).q :=
  (genuineChargeRoute_eq_zero_iff_orbitBand ctx k).mp (Finset.mem_filter.mp hk).2

/-- **A nonempty class-0 fibre forces a large AP-subfibre modulus**: `q ≥ 17` (the deep band
`16K ≤ q` needs `q ≥ 16`, and `q` is odd).  Mirror of the class-1 `q ≥ 9` obstruction, with the
strictly larger threshold of the deeper band. -/
theorem modulus_ge_seventeen_of_class0Fibre_nonempty (ctx : ActualFailureContext)
    (h : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).Nonempty) :
    17 ≤ (class1SlopeDatum ctx).q := by
  obtain ⟨k, hk⟩ := h
  have h16 := class0Fibre_orbit_band ctx hk
  have horb := slopeOrbit_mem (class1SlopeDatum ctx).hq_odd (class1SlopeDatum ctx).hK₀_pos
    (class1SlopeDatum ctx).hK₀_lt k
  obtain ⟨m, hm⟩ := (class1SlopeDatum ctx).hq_odd
  have h1 := horb.1
  omega

/-- **Small-modulus closure**: the class-0 routed fibre of the genuine route is PROVABLY EMPTY on
every shell whose closed AP-subfibre modulus is `< 17` (`q ∈ {3, 5, …, 15}`) — the deep band
`16K ≤ q` is unsatisfiable below `q = 17`. -/
theorem class0Fibre_empty_of_modulus_lt_seventeen (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q < 17) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0 = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro k hk
  have h17 := modulus_ge_seventeen_of_class0Fibre_nonempty ctx ⟨k, hk⟩
  omega

/-- The v3 seed budget routes through the genuine route, so the small-modulus closure applies. -/
theorem v3_class0Fibre_empty_of_modulus_lt_seventeen
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runChain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q < 17) :
    routedFibre ctx.n24CarryData
      ((v3Budget towerCount runChain returnCharge) ctx).route 0 = ∅ :=
  class0Fibre_empty_of_modulus_lt_seventeen ctx hq

/-! ## 4.  The routed class-0 mass: floor and vanishing characterization -/

/-- **The class-0 mass floor**: the routed class-0 mass dominates `|fibre₀|·Y` (every routed
start clears the active floor).  Class 1 has the exact identity `mass₁ = |fibre₁|·Y`
(razor-thin level set); class 0 keeps only the floor — its excesses are unbounded above. -/
theorem card_mul_Y_le_routedClassMass_zero (ctx : ActualFailureContext) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 0 := by
  rw [routedClassMassOf_eq_sum_fibre]
  calc ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card : ℝ)
        * ctx.n24CarryData.Y
      = ∑ _k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0,
          ctx.n24CarryData.Y := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0,
          windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
            ctx.n24CarryData.T :=
        Finset.sum_le_sum (fun k hk =>
          Y_le_windowExcess_of_mem_routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0 hk)

/-- **The class-0 routed mass vanishes IFF the class-0 fibre is empty** (the ledger-level form of
the routing statement; `Y ≥ 7/16 > 0` separates the two). -/
theorem routedClassMass_zero_eq_zero_iff (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 0 = 0
      ↔ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0 = ∅ := by
  constructor
  · intro h
    by_contra hne
    have hpos : 0 < (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card :=
      Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
    have hYpos := n24CarryData_Y_pos ctx
    have hge := card_mul_Y_le_routedClassMass_zero ctx
    rw [h] at hge
    have hcard1 : (1 : ℝ)
        ≤ ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card : ℝ) := by
      exact_mod_cast hpos
    have h1Y : (1 : ℝ) * ctx.n24CarryData.Y
        ≤ ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card : ℝ)
            * ctx.n24CarryData.Y :=
      mul_le_mul_of_nonneg_right hcard1 hYpos.le
    rw [one_mul] at h1Y
    linarith
  · intro h
    rw [routedClassMassOf_eq_sum_fibre, h, Finset.sum_empty]

/-! ## 5.  Window confinement: the route-free high-excess overrun and the boundary band

The overrun argument of classes 1 and 4 uses ONLY the high-excess floor `Y ≤ windowExcess`,
which holds for EVERY high-excess start — no class pin is needed.  We prove it once,
route-free, and specialize.  This is what later makes the `r = 0` closure exact: the floor
confines the WHOLE high-excess set, and the pressure floor makes that set nonempty. -/

/-- **The route-free high-excess window overrun.**  Under the numeric gate
`64·(r+1)·(L+B+1) < 129·L + 64`, EVERY high-excess start's descent window overruns the shell
window: `firstIndexAbove X + |supportShell d X| ≤ k + r + 1`. -/
theorem n24_highExcess_window_overrun (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
      ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y)
    (hnum : 64 * ((ctx.n24CarryData.r + 1)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
        < 129 * shellLadderDepth ctx + 64) :
    ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
        + (supportShell ctx.shell.d ctx.shell.X).card
      ≤ k + ctx.n24CarryData.r + 1 := by
  by_contra hint
  have hint' : k + ctx.n24CarryData.r + 1
      < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
        + (supportShell ctx.shell.d ctx.shell.X).card := Nat.lt_of_not_le hint
  have hgap : ∀ m ∈ Finset.range (ctx.n24CarryData.r + 1),
      hitGap ctx.n24CarryData.a (k + m)
        ≤ shellLadderDepth ctx + carryB ctx.shell.Q + 1 := by
    intro m hm
    rw [Finset.mem_range] at hm
    exact n24_hitGap_le_window ctx (by omega)
  have hsum : gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
      ≤ (ctx.n24CarryData.r + 1) * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) := by
    unfold gapWindow
    calc ∑ m ∈ Finset.range (ctx.n24CarryData.r + 1), hitGap ctx.n24CarryData.a (k + m)
        ≤ ∑ _m ∈ Finset.range (ctx.n24CarryData.r + 1),
            (shellLadderDepth ctx + carryB ctx.shell.Q + 1) := Finset.sum_le_sum hgap
      _ = (ctx.n24CarryData.r + 1) * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hY : ctx.n24CarryData.Y
      ≤ windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T :=
    (mem_highExcessStarts.mp hk).2
  have hpin := (Y_le_windowExcess_iff_gapWindow ctx k).mp hY
  have h64 : 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
      ≤ 64 * ((ctx.n24CarryData.r + 1)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) :=
    Nat.mul_le_mul_left 64 hsum
  omega

/-- Every class-0 routed start lies in the dyadic shell index window `i ≤ k < i + K`. -/
theorem class0Fibre_mem_window (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0) :
    ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X ≤ k
      ∧ k < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + (supportShell ctx.shell.d ctx.shell.X).card := by
  have hstart : k ∈ ctx.n24CarryData.starts :=
    (mem_highExcessStarts.mp (Finset.mem_filter.mp hk).1).1
  rw [cnlMulti_starts_eq_window, Finset.mem_Ico] at hstart
  exact hstart

/-- **The class-0 window-overrun pin** (specialization of the route-free overrun). -/
theorem class0Fibre_window_overrun (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0)
    (hnum : 64 * ((ctx.n24CarryData.r + 1)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
        < 129 * shellLadderDepth ctx + 64) :
    ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
        + (supportShell ctx.shell.d ctx.shell.X).card
      ≤ k + ctx.n24CarryData.r + 1 :=
  n24_highExcess_window_overrun ctx (Finset.mem_filter.mp hk).1 hnum

/-- **The boundary-band cardinality bound**: under the numeric gate the class-0 fibre has at most
`r + 1` elements (it sits inside the top `r + 1` positions of the shell window). -/
theorem class0Fibre_card_le_of_gapCeiling (ctx : ActualFailureContext)
    (hnum : 64 * ((ctx.n24CarryData.r + 1)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
        < 129 * shellLadderDepth ctx + 64) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card
      ≤ ctx.n24CarryData.r + 1 := by
  have hsub : routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0
      ⊆ Finset.Ico
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card - (ctx.n24CarryData.r + 1))
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card) := by
    intro k hk
    have hover := class0Fibre_window_overrun ctx hk hnum
    have hwin := class0Fibre_mem_window ctx hk
    rw [Finset.mem_Ico]
    omega
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card
      ≤ (Finset.Ico
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card - (ctx.n24CarryData.r + 1))
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card)).card :=
        Finset.card_le_card hsub
    _ ≤ ctx.n24CarryData.r + 1 := by
        rw [Nat.card_Ico]
        omega

/-! ## 6.  The `r = 0` EXACT closure: the pressure floor absorbs the hit-gap pin

On `r = 0` shells (ALL `L ≤ 15420`) the gate holds automatically and the route-free overrun
confines the WHOLE high-excess set to the single topmost window start; the Lemma 21.1 pressure
floor makes the set nonempty, so it EQUALS `{top}`.  The class-0 fibre is then decided purely by
the orbit band at `top` — the gap-window pin disappears from the `r = 0` residual. -/

/-- The topmost carry-window start `top = firstIndexAbove X + |supportShell d X| − 1`. -/
def class0TopStart (ctx : ActualFailureContext) : ℕ :=
  ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
    + (supportShell ctx.shell.d ctx.shell.X).card - 1

/-- The topmost window start is a genuine carry-window start (the window is nonempty:
`r + 1 ≤ |supportShell d X|`). -/
theorem class0TopStart_mem_starts (ctx : ActualFailureContext) :
    class0TopStart ctx ∈ ctx.n24CarryData.starts := by
  have hwidth := cnlMulti_r_add_one_le_width ctx
  rw [cnlMulti_starts_eq_window, Finset.mem_Ico]
  unfold class0TopStart
  omega

/-- **`r = 0` shells: the high-excess start set IS the topmost-start singleton.**  Confinement:
the route-free overrun under the automatic gate pins every member to `top`; nonemptiness: the
proved Lemma 21.1 pressure floor (`chernoffClass0_highExcessStarts_nonempty`). -/
theorem highExcessStarts_eq_top_of_r_eq_zero (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0) :
    highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
        ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y
      = {class0TopStart ctx} := by
  have hgate := class4_gate_of_r_eq_zero ctx hr
  have htop : ∀ k ∈ highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
      ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y,
      k = class0TopStart ctx := by
    intro k hk
    have hover := n24_highExcess_window_overrun ctx hk hgate
    have hstart := (mem_highExcessStarts.mp hk).1
    rw [cnlMulti_starts_eq_window, Finset.mem_Ico] at hstart
    unfold class0TopStart
    omega
  obtain ⟨k₀, hk₀⟩ := chernoffClass0_highExcessStarts_nonempty ctx
  ext k
  rw [Finset.mem_singleton]
  constructor
  · exact htop k
  · intro hk
    subst hk
    have hk₀top := htop k₀ hk₀
    rwa [hk₀top] at hk₀

/-- **`r = 0` shells: the topmost window start is high-excess** — the pressure floor lands its
mass exactly at `top`, so the hit-gap floor `129L + 64 ≤ 64·gapWindow(top)` holds FOR FREE. -/
theorem class0Top_highExcess_of_r_eq_zero (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0) :
    class0TopStart ctx ∈ highExcessStarts ctx.n24CarryData.starts
      (hitGap ctx.n24CarryData.a) ctx.n24CarryData.r ctx.n24CarryData.T
      ctx.n24CarryData.Y := by
  rw [highExcessStarts_eq_top_of_r_eq_zero ctx hr]
  exact Finset.mem_singleton_self _

/-- **`r = 0` shells: the class-0 fibre is pinned to the SINGLE topmost window start.** -/
theorem class0Fibre_top_of_r_eq_zero (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0) :
    k + 1 = ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
        + (supportShell ctx.shell.d ctx.shell.X).card := by
  have hover := class0Fibre_window_overrun ctx hk (class4_gate_of_r_eq_zero ctx hr)
  have hwin := class0Fibre_mem_window ctx hk
  omega

/-- **`r = 0` shells: at most ONE class-0 routed start** (`r = ⌊κL⌋ = 0` covers every shell with
`L ≤ 15420`). -/
theorem class0Fibre_card_le_one_of_r_eq_zero (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card ≤ 1 := by
  have hsub : routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0
      ⊆ {class0TopStart ctx} := by
    rw [class0Fibre_eq_highExcess_filter, highExcessStarts_eq_top_of_r_eq_zero ctx hr]
    exact Finset.filter_subset _ _
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card
      ≤ ({class0TopStart ctx} : Finset ℕ).card := Finset.card_le_card hsub
    _ = 1 := Finset.card_singleton _

/-- **Every shell with `L ≤ 15420` has at most ONE class-0 routed start** (the explicit-numeral
form of the `r = 0` boundary pinning). -/
theorem class0Fibre_card_le_one_of_L_le (ctx : ActualFailureContext)
    (hL : shellLadderDepth ctx ≤ 15420) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card ≤ 1 :=
  class0Fibre_card_le_one_of_r_eq_zero ctx (n24_r_eq_zero_of_L_le ctx hL)

/-- **The `r = 0` EXACT emptiness characterization**: on every `r = 0` shell the class-0 fibre is
empty IFF the slope orbit at the topmost window start sits ABOVE the deep band,
`q < 16·K_top`.  The hit-gap pin is gone: the pressure floor forces `top` high-excess, so ONLY
the band decides.  (No analogue is available for classes 1/4, whose `r = 0` residuals retain
their gap-window pins.) -/
theorem class0Fibre_empty_iff_of_r_eq_zero (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0 = ∅
      ↔ (class1SlopeDatum ctx).q
          < 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀
              (class0TopStart ctx) := by
  rw [class0Fibre_eq_highExcess_filter, highExcessStarts_eq_top_of_r_eq_zero ctx hr,
    Finset.filter_singleton]
  by_cases hroute : genuineChargeRoute ctx (class0TopStart ctx) = 0
  · rw [if_pos hroute]
    have h16 := (genuineChargeRoute_eq_zero_iff_orbitBand ctx _).mp hroute
    constructor
    · intro h
      exact absurd h (Finset.singleton_ne_empty _)
    · intro hlt
      exfalso
      omega
  · rw [if_neg hroute]
    have h16 : ¬ (16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀
        (class0TopStart ctx) ≤ (class1SlopeDatum ctx).q) :=
      fun hle => hroute ((genuineChargeRoute_eq_zero_iff_orbitBand ctx _).mpr hle)
    constructor
    · intro _
      omega
    · intro _
      rfl

/-- **The `r = 0` EXACT singleton characterization**: on every `r = 0` shell the class-0 fibre is
the topmost-start singleton IFF the orbit at `top` is in the deep band, `16·K_top ≤ q`. -/
theorem class0Fibre_eq_singleton_top_iff_of_r_eq_zero (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0 = {class0TopStart ctx}
      ↔ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀
            (class0TopStart ctx)
          ≤ (class1SlopeDatum ctx).q := by
  rw [class0Fibre_eq_highExcess_filter, highExcessStarts_eq_top_of_r_eq_zero ctx hr,
    Finset.filter_singleton]
  by_cases hroute : genuineChargeRoute ctx (class0TopStart ctx) = 0
  · rw [if_pos hroute]
    exact ⟨fun _ => (genuineChargeRoute_eq_zero_iff_orbitBand ctx _).mp hroute,
      fun _ => rfl⟩
  · rw [if_neg hroute]
    constructor
    · intro h
      exact absurd h.symm (Finset.singleton_ne_empty _)
    · intro h16
      exact absurd ((genuineChargeRoute_eq_zero_iff_orbitBand ctx _).mpr h16) hroute

/-- The `r = 0` exact emptiness characterization on the explicit numeral range `L ≤ 15420`. -/
theorem class0Fibre_empty_iff_of_L_le (ctx : ActualFailureContext)
    (hL : shellLadderDepth ctx ≤ 15420) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0 = ∅
      ↔ (class1SlopeDatum ctx).q
          < 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀
              (class0TopStart ctx) :=
  class0Fibre_empty_iff_of_r_eq_zero ctx (n24_r_eq_zero_of_L_le ctx hL)

/-- **Cross-atom exclusion (`r = 0`, vs class 1)**: a nonempty class-1 fibre EMPTIES the class-0
fibre — both are pinned to the same topmost start, which the route assigns to one class only. -/
theorem class0Fibre_empty_of_class1Fibre_nonempty_of_r_eq_zero (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0)
    (h1 : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).Nonempty) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0 = ∅ := by
  obtain ⟨j, hj⟩ := h1
  rw [Finset.eq_empty_iff_forall_notMem]
  intro k hk
  have hjtop := class1Fibre_top_of_r_eq_zero ctx hr hj
  have hktop := class0Fibre_top_of_r_eq_zero ctx hr hk
  have hjk : j = k := by omega
  have hr1 : genuineChargeRoute ctx j = 1 := (Finset.mem_filter.mp hj).2
  have hr0 : genuineChargeRoute ctx k = 0 := (Finset.mem_filter.mp hk).2
  rw [hjk, hr0] at hr1
  exact absurd hr1 (by decide)

/-- **Cross-atom exclusion (`r = 0`, vs class 4)**: a nonempty class-4 fibre EMPTIES the class-0
fibre. -/
theorem class0Fibre_empty_of_class4Fibre_nonempty_of_r_eq_zero (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0)
    (h4 : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4).Nonempty) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0 = ∅ := by
  obtain ⟨j, hj⟩ := h4
  rw [Finset.eq_empty_iff_forall_notMem]
  intro k hk
  have hjtop := class4Fibre_top_of_r_eq_zero ctx hr hj
  have hktop := class0Fibre_top_of_r_eq_zero ctx hr hk
  have hjk : j = k := by omega
  have hr4 : genuineChargeRoute ctx j = 4 := (Finset.mem_filter.mp hj).2
  have hr0 : genuineChargeRoute ctx k = 0 := (Finset.mem_filter.mp hk).2
  rw [hjk, hr0] at hr4
  exact absurd hr4 (by decide)

/-! ## 7.  The named residual and its sharpest necessary-and-sufficient arithmetic form -/

/-- **THE minimal residual of the class-0 Chernoff atom**: the class-0 routed fibre is empty on
every actual failure context (mirror of `Class1FibreEmpty`).  At `budget := sixAtomBudget …`
(whose route is `genuineChargeRoute` by `rfl`) this is EXACTLY the capstone field
`Erdos260SixAtomResidual.class0Empty`. -/
def Class0FibreEmpty
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx) : Prop :=
  ∀ ctx : ActualFailureContext, routedFibre ctx.n24CarryData (budget ctx).route 0 = ∅

/-- **The per-context pinned form**: the class-0 fibre of the genuine route is empty IFF no
carry-window start realizes the high-excess gap-window floor and the deep band simultaneously. -/
theorem class0Fibre_empty_iff_pinned (ctx : ActualFailureContext) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0 = ∅
      ↔ ∀ k ∈ ctx.n24CarryData.starts,
          ¬(129 * shellLadderDepth ctx + 64
              ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
            ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
                ≤ (class1SlopeDatum ctx).q) := by
  rw [Finset.eq_empty_iff_forall_notMem]
  constructor
  · intro h k hkstart hpins
    exact h k ((mem_class0Fibre_iff_orbitBand ctx k).mpr ⟨hkstart, hpins.1, hpins.2⟩)
  · intro h k hk
    rw [mem_class0Fibre_iff_orbitBand] at hk
    exact h k hk.1 ⟨hk.2.1, hk.2.2⟩

/-- **The residual in its sharpest necessary-and-sufficient arithmetic form**: the v3 class-0
atom `Class0FibreEmpty (v3Budget …)` holds IFF no carry-window start simultaneously realizes the
gap-window floor and the deep-band pin — the class-0 mirror of `v3_class1FibreEmpty_iff_pinned`.
The capstone budget `sixAtomBudget …` IS a `v3Budget`, so this decides its `class0Empty` field. -/
theorem v3_class0FibreEmpty_iff_pinned
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runChain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx) :
    Class0FibreEmpty (v3Budget towerCount runChain returnCharge)
      ↔ ∀ ctx : ActualFailureContext, ∀ k ∈ ctx.n24CarryData.starts,
          ¬(129 * shellLadderDepth ctx + 64
              ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
            ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
                ≤ (class1SlopeDatum ctx).q) := by
  unfold Class0FibreEmpty
  exact forall_congr' fun ctx => by
    rw [v3Budget_route]
    exact class0Fibre_empty_iff_pinned ctx

/-- The pinned arithmetic empties the class-0 fibre of ANY budget routing through the genuine
first-obstruction route (covers `v3Budget` and the capstone `sixAtomBudget` alike). -/
theorem class0FibreEmpty_of_genuineRoute_pinned
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (hroute : ∀ ctx : ActualFailureContext, (budget ctx).route = genuineChargeRoute ctx)
    (h : ∀ ctx : ActualFailureContext, ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q)) :
    Class0FibreEmpty budget := by
  intro ctx
  rw [hroute ctx]
  exact (class0Fibre_empty_iff_pinned ctx).mpr (h ctx)

/-- **The pinned arithmetic SUFFICIENT condition, with all proved obstructions folded in**: to
close the atom it suffices to refute the deep band on the shells surviving every proved closure —
modulus `q ≥ 17`, gap-window floor satisfied — for window starts only (the class-0 mirror of
`class1FibreEmpty_of_pinned_arithmetic`). -/
theorem class0FibreEmpty_of_pinned_arithmetic
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runChain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (h : ∀ ctx : ActualFailureContext, ∀ k ∈ ctx.n24CarryData.starts,
      17 ≤ (class1SlopeDatum ctx).q →
      129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
      ¬(16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
          ≤ (class1SlopeDatum ctx).q)) :
    Class0FibreEmpty (v3Budget towerCount runChain returnCharge) := by
  rw [v3_class0FibreEmpty_iff_pinned]
  intro ctx k hkstart hpins
  obtain ⟨hgw, hband⟩ := hpins
  have hq17 : 17 ≤ (class1SlopeDatum ctx).q := by
    have horb := slopeOrbit_mem (class1SlopeDatum ctx).hq_odd (class1SlopeDatum ctx).hK₀_pos
      (class1SlopeDatum ctx).hK₀_lt k
    obtain ⟨m, hm⟩ := (class1SlopeDatum ctx).hq_odd
    have h1 := horb.1
    omega
  exact h ctx k hkstart hq17 hgw hband

/-- **The residual shrinks to the `q ≥ 17` shell subfamily**: to close `Class0FibreEmpty` for the
v3 budget it suffices to treat the shells whose closed AP-subfibre modulus is at least `17`. -/
theorem class0FibreEmpty_of_modulus_ge_seventeen_case
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runChain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (h : ∀ ctx : ActualFailureContext, 17 ≤ (class1SlopeDatum ctx).q →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0 = ∅) :
    Class0FibreEmpty (v3Budget towerCount runChain returnCharge) := by
  intro ctx
  show routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0 = ∅
  by_cases hq : 17 ≤ (class1SlopeDatum ctx).q
  · exact h ctx hq
  · exact class0Fibre_empty_of_modulus_lt_seventeen ctx (by omega)

/-- **The residual splits along `r`**: the `r = 0` half (ALL `L ≤ 15420`) is carried by the
single top-band statement `q < 16·K_top` per shell (NO gap-window input), and only the deep
shells `r ≥ 1` (`L ≥ 15421`) retain the full pinned form. -/
theorem class0FibreEmpty_of_r_pos_case
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runChain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (hdeep : ∀ ctx : ActualFailureContext, 1 ≤ ctx.n24CarryData.r →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0 = ∅)
    (htop : ∀ ctx : ActualFailureContext, ctx.n24CarryData.r = 0 →
      (class1SlopeDatum ctx).q
        < 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀
            (class0TopStart ctx)) :
    Class0FibreEmpty (v3Budget towerCount runChain returnCharge) := by
  intro ctx
  show routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0 = ∅
  rcases Nat.eq_zero_or_pos ctx.n24CarryData.r with hr | hr
  · exact (class0Fibre_empty_iff_of_r_eq_zero ctx hr).mpr (htop ctx hr)
  · exact hdeep ctx hr

/-! ## 8.  Bridges into the §22 Chernoff surfaces and the P9 endpoint -/

/-- **The genuine §22 area seed over the v3 budget EXISTS iff the pinned arithmetic holds** —
`genuineAreaSeed_iff_class0FibreEmpty` composed with the sharp membership characterization. -/
theorem v3_genuineAreaSeed_iff_pinned
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runChain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx) :
    Nonempty (ChernoffGenuineAreaSeedForBudget (v3Budget towerCount runChain returnCharge))
      ↔ ∀ ctx : ActualFailureContext, ∀ k ∈ ctx.n24CarryData.starts,
          ¬(129 * shellLadderDepth ctx + 64
              ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
            ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
                ≤ (class1SlopeDatum ctx).q) :=
  (genuineAreaSeed_iff_class0FibreEmpty _).trans
    (forall_congr' fun ctx => by
      rw [v3Budget_route]
      exact class0Fibre_empty_iff_pinned ctx)

/-- **The two-field `(kraft, small)` residual over the v3 budget EXISTS iff the pinned arithmetic
holds** — the calibrated 22.1A surface is decided by the routing arithmetic. -/
theorem v3_chernoffKraftSmall_iff_pinned
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runChain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx) :
    Nonempty (ChernoffGenuineAreaKraftSmallResidual
        (v3Budget towerCount runChain returnCharge))
      ↔ ∀ ctx : ActualFailureContext, ∀ k ∈ ctx.n24CarryData.starts,
          ¬(129 * shellLadderDepth ctx + 64
              ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
            ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
                ≤ (class1SlopeDatum ctx).q) :=
  (chernoffKraftSmallResidual_iff_class0FibreEmpty _).trans
    (forall_congr' fun ctx => by
      rw [v3Budget_route]
      exact class0Fibre_empty_iff_pinned ctx)

/-- **The P9/V3 endpoint from the class-0 pinned arithmetic** — the Chernoff slot carried in its
sharpest arithmetic form (refute the simultaneous gap-window-floor/deep-band pins on window
starts); all other atoms as hypotheses, exactly as in `erdos260_p9V3_of_chernoffClass0Empty`. -/
theorem erdos260_p9V3_of_class0PinnedArithmetic
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runResidual : ∀ ctx : ActualFailureContext, RunClass5LeafResidual ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (hpin : ∀ ctx : ActualFailureContext, ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q))
    (cnl : Class1CNLInjection
      (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge))
    (densePackCount : ∀ ctx : ActualFailureContext,
      (genuineDensePackStarts ctx).card
        ≤ (densePackMarkers
          (v3Budget towerCount (p9V3RunChainOfResidual runResidual) returnCharge) ctx).card)
    (windowReach : ActualFailureContext → ℕ)
    (hReach : ∀ ctx : ActualFailureContext,
      windowReach ctx + 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hContain : ∀ ctx : ActualFailureContext, ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + windowReach ctx)
    (hScale : ∀ ctx : ActualFailureContext,
      ((ctx.n24CarryData.r : ℝ) + 1) * (densePackDyadicG0 ctx : ℝ) - ctx.n24CarryData.T ≤ 1) :
    Erdos260Statement :=
  erdos260_p9V3_of_chernoffClass0Empty
    { towerCount := towerCount
      runResidual := runResidual
      returnCharge := returnCharge
      class0Empty := fun ctx => by
        show routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0 = ∅
        exact (class0Fibre_empty_iff_pinned ctx).mpr (hpin ctx)
      cnl := cnl
      densePackCount := densePackCount
      windowReach := windowReach
      hReach := hReach
      hContain := hContain
      hScale := hScale }

/-! ## 9.  Machine-readable status (brutally honest) -/

/-- Honest machine-readable status of the class-0 routing settlement. -/
def chernoffClass0RoutingStatus : List String :=
  [ "CLOSED (route readout): class 0 is reached through EXACTLY ONE branch of the genuine " ++
      "first-obstruction route — towerClsOfShell = .other (genuineChargeRoute_eq_zero_iff), " ++
      "with NO exceptional cnlTail branch (unlike classes 1/2/4/5). The .other band readout is " ++
      "g = 0 or g >= 5 (towerExitClassOfGap_eq_other_iff); canonGap = log2(q/K)+1 >= 1 is never " ++
      "0 (canonGap_ne_zero); so the class-0 route test is EXACTLY the deep E.13 band " ++
      "canonGap q K_k >= 5, equivalently 16*K_k <= q for the orbit numerator " ++
      "(canonGap_ge_five_iff, genuineChargeRoute_eq_zero_iff_canonGap/_orbitBand).",
    "OBSTRUCTION PROVED (the sharp membership characterization, the brief's target): k is in " ++
      "fibre0 IFF k is a carry-window start realizing the high-excess gap-window floor " ++
      "129L + 64 <= 64*gapWindow(k) AND the deep band canonGap q K_k >= 5 (16*K_k <= q) " ++
      "(mem_class0Fibre_iff, mem_class0Fibre_iff_orbitBand, class0Fibre_eq_pinnedFilter) — " ++
      "the exact mirror of mem_class1Fibre_iff (band = 4, excess pinned = Y) and " ++
      "mem_class4Fibre_iff (band = 2, floor): class 0 pins the floor and the deep band.",
    "CLOSED (small-modulus subfamily): a class-0 start forces q >= 17 (16K <= q, K >= 1, " ++
      "q odd: modulus_ge_seventeen_of_class0Fibre_nonempty), so the fibre is PROVABLY EMPTY " ++
      "whenever q < 17 (class0Fibre_empty_of_modulus_lt_seventeen, v3_ form) — the class-0 " ++
      "mirror of the class-1 q < 9 closure at the deeper band's larger threshold.",
    "CLOSED (mass form): routedClassMassOf ... 0 >= |fibre0|*Y " ++
      "(card_mul_Y_le_routedClassMass_zero) and the class-0 routed mass VANISHES iff the fibre " ++
      "is empty (routedClassMass_zero_eq_zero_iff) — the ledger-level form of the atom.",
    "CLOSED (window confinement, route-free): EVERY high-excess start overruns the shell-window " ++
      "top under the gate 64(r+1)(L+B+1) < 129L + 64 (n24_highExcess_window_overrun — only the " ++
      "floor Y <= windowExcess is used, so this generalizes the class-1/class-4 overruns to " ++
      "every class at once); hence |fibre0| <= r + 1 under the gate " ++
      "(class0Fibre_card_le_of_gapCeiling) and |fibre0| <= 1 on r = 0 shells, i.e. ALL " ++
      "L <= 15420 (class0Fibre_card_le_one_of_r_eq_zero/_of_L_le).",
    "CLOSED (the r = 0 EXACT closure — NEW, sharper than the class-1/class-4 state): on r = 0 " ++
      "shells the proved pressure floor (chernoffClass0_highExcessStarts_nonempty) plus the " ++
      "route-free overrun force highExcessStarts = {top} (highExcessStarts_eq_top_of_r_eq_zero, " ++
      "top = class0TopStart = firstIndexAbove X + |supportShell| - 1, a genuine window start, " ++
      "class0TopStart_mem_starts, high-excess for free: class0Top_highExcess_of_r_eq_zero). " ++
      "Hence fibre0 = empty IFF q < 16*K_top and fibre0 = {top} IFF 16*K_top <= q " ++
      "(class0Fibre_empty_iff_of_r_eq_zero, class0Fibre_eq_singleton_top_iff_of_r_eq_zero, " ++
      "numeral form class0Fibre_empty_iff_of_L_le): the hit-gap pin is ABSORBED by the " ++
      "pressure floor — the whole L <= 15420 residual is ONE orbit-band statement per shell.",
    "CLOSED (cross-atom exclusions on r = 0 shells): a nonempty class-1 OR class-4 fibre " ++
      "EMPTIES the class-0 fibre (class0Fibre_empty_of_class1Fibre_nonempty_of_r_eq_zero, " ++
      "class0Fibre_empty_of_class4Fibre_nonempty_of_r_eq_zero) — all top-band atoms compete " ++
      "for the single topmost start.",
    "REDUCED (the minimal residual, necessary AND sufficient): Class0FibreEmpty (v3Budget ...) " ++
      "IFF no carry-window start realizes the floor and the deep band simultaneously " ++
      "(class0Fibre_empty_iff_pinned, v3_class0FibreEmpty_iff_pinned); sufficient forms with " ++
      "proved obstructions folded in (class0FibreEmpty_of_pinned_arithmetic: q >= 17 + floor " ++
      "given), the q-split (class0FibreEmpty_of_modulus_ge_seventeen_case), the r-split with " ++
      "the r = 0 half reduced to the top-band statement (class0FibreEmpty_of_r_pos_case), and " ++
      "the generic genuine-route bridge (class0FibreEmpty_of_genuineRoute_pinned). The " ++
      "capstone sixAtomBudget IS a v3Budget with route = genuineChargeRoute by rfl, so these " ++
      "decide the Erdos260SixAtomResidual.class0Empty field directly.",
    "BRIDGES PROVED: the genuine paragraph-22 area seed and the (kraft, small) residual over " ++
      "the v3 budget EXIST iff the pinned arithmetic holds (v3_genuineAreaSeed_iff_pinned, " ++
      "v3_chernoffKraftSmall_iff_pinned), and the P9 endpoint runs from the pinned form " ++
      "(erdos260_p9V3_of_class0PinnedArithmetic) through erdos260_p9V3_of_chernoffClass0Empty.",
    "HONEST BOUNDARY (no unconditional emptiness claimed): the deep band is genuinely " ++
      "reachable by the E.13 orbit (q = 17: the orbit 1 -> 15 -> 13 -> 9 -> 1 revisits " ++
      "K = 1 <= q/16 every fourth step), and the formalization has NO bridge between hitGap " ++
      "and canonGap at the actual ctx (same obstruction recorded for class 1). The pressure " ++
      "floor does NOT force class-0 mass (class 1 is the route's catch-all; class 0 is a " ++
      "specific band), so emptiness is neither provable nor refutable here; the pinned iff is " ++
      "the exact boundary, and by genuineAreaSeed_iff_class0FibreEmpty no weaker class-0 " ++
      "input exists." ]

theorem chernoffClass0RoutingStatus_nonempty : chernoffClass0RoutingStatus ≠ [] := by
  simp [chernoffClass0RoutingStatus]

/-! ## 10.  Axiom-cleanliness audit -/

#print axioms canonGap_ne_zero
#print axioms towerExitClassOfGap_eq_other_iff
#print axioms canonGap_ge_five_iff
#print axioms genuineChargeRoute_eq_zero_iff_canonGap
#print axioms genuineChargeRoute_eq_zero_iff_orbitBand
#print axioms class0Fibre_eq_highExcess_filter
#print axioms class0Fibre_canonGap_ge
#print axioms mem_class0Fibre_iff
#print axioms mem_class0Fibre_iff_orbitBand
#print axioms class0Fibre_eq_pinnedFilter
#print axioms class0Fibre_orbit_band
#print axioms modulus_ge_seventeen_of_class0Fibre_nonempty
#print axioms class0Fibre_empty_of_modulus_lt_seventeen
#print axioms v3_class0Fibre_empty_of_modulus_lt_seventeen
#print axioms card_mul_Y_le_routedClassMass_zero
#print axioms routedClassMass_zero_eq_zero_iff
#print axioms n24_highExcess_window_overrun
#print axioms class0Fibre_mem_window
#print axioms class0Fibre_window_overrun
#print axioms class0Fibre_card_le_of_gapCeiling
#print axioms class0TopStart
#print axioms class0TopStart_mem_starts
#print axioms highExcessStarts_eq_top_of_r_eq_zero
#print axioms class0Top_highExcess_of_r_eq_zero
#print axioms class0Fibre_top_of_r_eq_zero
#print axioms class0Fibre_card_le_one_of_r_eq_zero
#print axioms class0Fibre_card_le_one_of_L_le
#print axioms class0Fibre_empty_iff_of_r_eq_zero
#print axioms class0Fibre_eq_singleton_top_iff_of_r_eq_zero
#print axioms class0Fibre_empty_iff_of_L_le
#print axioms class0Fibre_empty_of_class1Fibre_nonempty_of_r_eq_zero
#print axioms class0Fibre_empty_of_class4Fibre_nonempty_of_r_eq_zero
#print axioms class0Fibre_empty_iff_pinned
#print axioms v3_class0FibreEmpty_iff_pinned
#print axioms class0FibreEmpty_of_genuineRoute_pinned
#print axioms class0FibreEmpty_of_pinned_arithmetic
#print axioms class0FibreEmpty_of_modulus_ge_seventeen_case
#print axioms class0FibreEmpty_of_r_pos_case
#print axioms v3_genuineAreaSeed_iff_pinned
#print axioms v3_chernoffKraftSmall_iff_pinned
#print axioms erdos260_p9V3_of_class0PinnedArithmetic
#print axioms chernoffClass0RoutingStatus_nonempty

end

end Erdos260
