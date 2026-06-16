import Erdos260.ChernoffClass0Routing
import Erdos260.CNLClass1Closure

/-!
# Class-0 (Chernoff) deep-band cycle closure, wave 3

This module (NEW; it edits no existing file) adapts the wave-2 class-1 orbit-periodicity
machinery (`CNLClass1Closure`) to the DEEP E.13 bands (`canonGap q K_k ≥ 5`, equivalently
`16·K_k ≤ q`) that route the class-0 (Chernoff) atom, and delivers per-context finite
cycle-check closures, modulus-family closures, and the `K = 1` bottleneck criterion for the
capstone field

  `class0Pinned : ∀ ctx, ∀ k ∈ starts, ¬(129L + 64 ≤ 64·gW(k) ∧ 16·K_k ≤ q)`

of `Erdos260SharpResidual` (`Erdos260SharpCapstone.lean`).  Everything is proved from the
routing/orbit arithmetic of the canonical objects — no fabricated witnesses, no new axioms.

## What IS newly closed here (all unconditional theorems)

* **Generic cycle propagation** (`slopeOrbit_pred_of_cycle`): any predicate verified on ONE
  period block `[1, c]` of the slope orbit holds at EVERY positive index — the predicate
  abstraction of the wave-2 band-4 propagation, reusable for every band test at once.
* **The residue reduction** (`cycleRep`, `slopeOrbit_add_mul_period`, `slopeOrbit_cycleRep`):
  for any period `c` valid from index `1`, `K_k = K_{cycleRep c k}` with
  `cycleRep c k ∈ [1, c]` — the orbit readout at an arbitrary window start is decided by its
  residue class mod `c`.
* **The per-ctx finite cycle-check closures** (`class0Pinned_of_orbit_deepBand_free`,
  `class0Pinned_of_cycle_deepBand_free`, `class0Pinned_of_cycleCheck`, fibre forms
  `class0Fibre_empty_of_orbit_deepBand_free` / `class0Fibre_empty_of_cycle_deepBand_free` /
  `v3_class0Fibre_empty_of_cycle_deepBand_free`): if one period of the orbit avoids the deep
  band (`q < 16·K_j` on `[1, c]`), the class-0 pinned arithmetic holds at the ctx and the
  class-0 routed fibre is EMPTY — the exact class-0 mirror of
  `class1Fibre_empty_of_cycle_band_free`, decided by at most `q` orbit readings per ctx.
* **The general bottleneck criterion** (`class0Pinned_of_cycle_floor`): if the SMALLEST cycle
  element exceeds `q/16` (formally: some `m` with `m ≤ K_j` on the cycle and `q < 16·m`), the
  pinned arithmetic holds — the brief's line-2 criterion in its sharpest form.
* **The `K = 1` bottleneck on `q < 32`** (`deepBand_eq_one_of_modulus_lt_32`,
  `cycle_deepBand_iff_one_of_modulus_window`,
  `class0Pinned_of_orbit_avoids_one_of_modulus_lt_32`,
  `class0Pinned_of_cycle_avoids_one_of_modulus_lt_32`): on `16 ≤ q < 32` the deep band fires
  ONLY at the orbit value `K = 1` (`16K ≤ q < 32` forces `K = 1`), so deep-band presence on
  the cycle is EQUIVALENT to `1` being on the cycle, and the whole modulus family
  `17 ≤ q ≤ 31` closes whenever the cycle avoids `1` — one equality test per cycle element.
* **The divisor/gcd persistence families** (`slopeOrbit_dvd_of_dvd_from`,
  `slopeOrbit_dvd_of_dvd`, `slopeOrbit_dvd_of_cycle_dvd`, `class0Pinned_of_dvd_floor`,
  `class0Pinned_of_gcd_floor`, `class0Pinned_of_base_dvd_modulus`,
  `class0Pinned_of_cycle_dvd_floor`): the E.13 step `K ↦ 2^g·K − q` preserves every common
  divisor `d` of `q` and the state, so every orbit value is `≥ d`; hence
  `q < 16·gcd(q, K₀)` closes the ctx OUTRIGHT — no cycle computation at all.  Instantiation:
  every shell whose base numerator divides its modulus with quotient `< 16` (`K₀ ∣ q`,
  `q < 16·K₀` — e.g. the whole `q = 3·K₀` family of the class-4 fixed point, `q = 5·K₀`, …,
  `q = 15·K₀`) is class-0-pinned unconditionally.
* **The window-residue refinement, necessary AND sufficient**
  (`class0Pinned_of_window_residues`, `class0Pinned_iff_window_residues`,
  `Class0WindowCycleCheck`, `class0Pinned_iff_windowCycleCheck`,
  `class0Pinned_field_iff_windowCycleCheck`): only window starts `k` realizing the gap-window
  floor matter, and each contributes exactly its residue `cycleRep c k`; the windowed finite
  check is EQUIVALENT to the capstone pinned field, per ctx and globally — the exact
  surviving surface of the atom in finite-check form (`≤ q` orbit readings + `≤ |starts|`
  comparisons per ctx).
* **The modulus-split field assemblies** (`class0Pinned_of_modulus_lt_seventeen`,
  `class0Pinned_field_of_modulus_split`, `class0Pinned_field_of_bottleneck_split`,
  `class0FibreEmpty_of_windowCycleCheck`, `v3_class0FibreEmpty_of_modulus_split_check`):
  `q < 17` is closed outright inside the split (the deep band needs `16·K ≤ q`, `K ≥ 1`,
  `q` odd), `17 ≤ q < 32` reduces to the avoid-`1` cycle check, and only `q ≥ 32` retains the
  general windowed check; the assemblies land on EXACTLY the capstone field shape and on the
  wave-2 `Class0FibreEmpty` residual for every genuine-route budget.

## Honest obstruction PROVED (why the cycle-only check cannot always fire)

`slopeOrbit_period_closes_at_base` / `cycle_deepBand_of_odd_small_base` /
`not_class0CycleDeepBandFree_of_odd_small_base`: for an ODD base numerator `K₀`, every period
of the orbit closes at the base (`K_c = K₀` by backward determinism on odd states), so when
additionally `16·K₀ ≤ q` the deep band sits ON every cycle and the window-free cycle check
`Class0CycleDeepBandFree` is PROVABLY FALSE.  On such shells only the windowed check (floor
coupling + residue miss) can close the atom.  The deep band is genuinely reachable (the brief
records `q = 17`: `1 → 15 → 13 → 9 → 1` revisits `K = 1` every fourth step), and the
formalization carries no `hitGap ↔ canonGap` bridge at the actual ctx — so NO unconditional
emptiness theorem is claimed: the windowed check equivalence is the exact boundary.

No `sorry`, `admit`, `axiom`, or `native_decide`.
-/

namespace Erdos260

open Finset

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 1.  Generic cycle propagation and the residue reduction

The wave-2 propagation (`orbit_band_free_of_cycle_aux`) is specific to the band-4 test.  We
abstract it to an arbitrary predicate on orbit VALUES, then add the residue reduction: a
period valid from index `1` decides the orbit at every positive index by its representative
in `[1, c]`. -/

private theorem slopeOrbit_pred_of_cycle_aux {q K₀ c : ℕ} {P : ℕ → Prop} (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m → slopeOrbit q K₀ (m + c) = slopeOrbit q K₀ m)
    (hP : ∀ j, 1 ≤ j → j ≤ c → P (slopeOrbit q K₀ j)) :
    ∀ n j, 1 ≤ j → j ≤ c * (n + 1) → P (slopeOrbit q K₀ j) := by
  intro n
  induction n with
  | zero =>
      intro j h1 hle
      exact hP j h1 (by omega)
  | succ n ih =>
      intro j h1 hle
      by_cases hle' : j ≤ c * (n + 1)
      · exact ih j h1 hle'
      · have hcA : c ≤ c * (n + 1) := Nat.le_mul_of_pos_right c (by omega)
        have hcj : c ≤ j := by omega
        have hj1 : 1 ≤ j - c := by omega
        have heq : slopeOrbit q K₀ j = slopeOrbit q K₀ (j - c) := by
          have h := hper (j - c) hj1
          rwa [Nat.sub_add_cancel hcj] at h
        rw [heq]
        refine ih (j - c) hj1 ?_
        have hsplit : c * (n + 1 + 1) = c * (n + 1) + c := by ring
        omega

/-- **Generic cycle propagation**: a predicate on orbit values verified on one period block
`[1, c]` holds at every positive index (predicate abstraction of the wave-2 band-4
propagation; instantiated below with the deep-band miss `q < 16·K`, the value test `K ≠ 1`,
and the floor test `m ≤ K`). -/
theorem slopeOrbit_pred_of_cycle {q K₀ c : ℕ} {P : ℕ → Prop} (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m → slopeOrbit q K₀ (m + c) = slopeOrbit q K₀ m)
    (hP : ∀ j, 1 ≤ j → j ≤ c → P (slopeOrbit q K₀ j)) :
    ∀ j, 1 ≤ j → P (slopeOrbit q K₀ j) := by
  intro j hj
  refine slopeOrbit_pred_of_cycle_aux hc hper hP j j hj ?_
  calc j ≤ j + 1 := by omega
    _ ≤ c * (j + 1) := Nat.le_mul_of_pos_left (j + 1) (by omega)

/-- Period iteration: a period `c` valid from index `1` iterates to every multiple `t·c`. -/
theorem slopeOrbit_add_mul_period {q K₀ c : ℕ}
    (hper : ∀ m, 1 ≤ m → slopeOrbit q K₀ (m + c) = slopeOrbit q K₀ m) :
    ∀ t m, 1 ≤ m → slopeOrbit q K₀ (m + t * c) = slopeOrbit q K₀ m := by
  intro t
  induction t with
  | zero =>
      intro m hm
      rw [Nat.zero_mul, Nat.add_zero]
  | succ t ih =>
      intro m hm
      have h1 : m + (t + 1) * c = m + t * c + c := by ring
      rw [h1, hper (m + t * c) (by omega), ih m hm]

/-- **The cycle representative** of an index `k` for a period `c`: the unique element of
`[1, c]` congruent to `k` mod `c` (the class of `0` is represented by `c` itself, matching
pure periodicity FROM index `1`). -/
def cycleRep (c k : ℕ) : ℕ := if k % c = 0 then c else k % c

/-- The cycle representative is positive. -/
theorem cycleRep_pos {c : ℕ} (hc : 1 ≤ c) (k : ℕ) : 1 ≤ cycleRep c k := by
  unfold cycleRep
  split
  · exact hc
  · next h => exact Nat.pos_of_ne_zero h

/-- The cycle representative lies in the period block: `cycleRep c k ≤ c`. -/
theorem cycleRep_le {c : ℕ} (hc : 1 ≤ c) (k : ℕ) : cycleRep c k ≤ c := by
  unfold cycleRep
  split
  · exact le_rfl
  · exact Nat.le_of_lt (Nat.mod_lt k hc)

/-- **The residue reduction**: under a period `c` valid from index `1`, the orbit value at
ANY positive index equals the value at its cycle representative — the orbit readout at a
window start is decided by `k mod c`. -/
theorem slopeOrbit_cycleRep {q K₀ c : ℕ} (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m → slopeOrbit q K₀ (m + c) = slopeOrbit q K₀ m)
    {k : ℕ} (hk : 1 ≤ k) :
    slopeOrbit q K₀ k = slopeOrbit q K₀ (cycleRep c k) := by
  unfold cycleRep
  by_cases h0 : k % c = 0
  · rw [if_pos h0]
    have hdvd : c ∣ k := Nat.dvd_of_mod_eq_zero h0
    have hck : c ≤ k := Nat.le_of_dvd hk hdvd
    have hpos : 0 < k / c := Nat.div_pos hck hc
    obtain ⟨t, ht⟩ : ∃ t, k / c = t + 1 :=
      ⟨k / c - 1, (Nat.succ_pred_eq_of_pos hpos).symm⟩
    have hmul : k / c * c = k := Nat.div_mul_cancel hdvd
    rw [ht] at hmul
    have hke : k = c + t * c := by
      rw [← hmul]
      ring
    calc slopeOrbit q K₀ k = slopeOrbit q K₀ (c + t * c) := by rw [← hke]
      _ = slopeOrbit q K₀ c := slopeOrbit_add_mul_period hper t c hc
  · rw [if_neg h0]
    have hr1 : 1 ≤ k % c := Nat.pos_of_ne_zero h0
    have hke : k = k % c + k / c * c := (Nat.mod_add_div' k c).symm
    calc slopeOrbit q K₀ k = slopeOrbit q K₀ (k % c + k / c * c) := by rw [← hke]
      _ = slopeOrbit q K₀ (k % c) := slopeOrbit_add_mul_period hper (k / c) (k % c) hr1

/-! ## Part 2.  Divisor persistence along the orbit

The E.13 step `K ↦ 2^g·K − q` preserves every common divisor of `q` and the state (the
subtraction is `Nat.dvd_sub`-safe), so divisors of the base — in particular
`gcd(q, K₀)` — floor the WHOLE orbit.  With a period, a divisor of any one positive-index
value floors the whole cycle. -/

/-- Divisor persistence from an arbitrary anchor: a common divisor of `q` and the orbit value
at `j₀` divides every later orbit value. -/
theorem slopeOrbit_dvd_of_dvd_from {q K₀ d j₀ : ℕ} (hdq : d ∣ q)
    (hd : d ∣ slopeOrbit q K₀ j₀) :
    ∀ j, j₀ ≤ j → d ∣ slopeOrbit q K₀ j := by
  have haux : ∀ t, d ∣ slopeOrbit q K₀ (j₀ + t) := by
    intro t
    induction t with
    | zero => exact hd
    | succ t ih =>
        have hstep : slopeOrbit q K₀ (j₀ + (t + 1))
            = boundedSlopeStep q (slopeOrbit q K₀ (j₀ + t)) := rfl
        rw [hstep]
        unfold boundedSlopeStep
        exact Nat.dvd_sub (ih.mul_left _) hdq
  intro j hj
  have h := haux (j - j₀)
  rwa [Nat.add_sub_cancel' hj] at h

/-- **Base divisor persistence**: a common divisor of `q` and `K₀` divides EVERY orbit
value. -/
theorem slopeOrbit_dvd_of_dvd {q K₀ d : ℕ} (hdq : d ∣ q) (hdK : d ∣ K₀) :
    ∀ j, d ∣ slopeOrbit q K₀ j := fun j =>
  slopeOrbit_dvd_of_dvd_from (j₀ := 0) hdq hdK j (Nat.zero_le j)

/-- **Cycle divisor persistence**: under a period `c`, a common divisor of `q` and the orbit
value at ANY positive index divides every positive-index orbit value (forward persistence
wraps around the cycle). -/
theorem slopeOrbit_dvd_of_cycle_dvd {q K₀ c d j₀ : ℕ} (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m → slopeOrbit q K₀ (m + c) = slopeOrbit q K₀ m)
    (hj₀ : 1 ≤ j₀) (hdq : d ∣ q) (hd : d ∣ slopeOrbit q K₀ j₀) :
    ∀ j, 1 ≤ j → d ∣ slopeOrbit q K₀ j := by
  intro j hj
  have hle : j₀ ≤ j + j₀ * c := by
    have h1 : j₀ ≤ j₀ * c := Nat.le_mul_of_pos_right j₀ (by omega)
    omega
  have hdvd := slopeOrbit_dvd_of_dvd_from hdq hd (j + j₀ * c) hle
  rwa [slopeOrbit_add_mul_period hper j₀ j hj] at hdvd

/-! ## Part 3.  The per-ctx deep-band cycle-check closures (the capstone field shape)

Every theorem in this part concludes EXACTLY the per-ctx body of the capstone field
`Erdos260SharpResidual.class0Pinned`: no carry-window start realizes the gap-window floor
`129L + 64 ≤ 64·gW` and the deep band `16·K_k ≤ q` simultaneously. -/

/-- **Orbit deep-band-free closure**: if the orbit misses the deep band at every positive
index, the class-0 pinned arithmetic holds at the ctx (every window start has `k ≥ 1`). -/
theorem class0Pinned_of_orbit_deepBand_free (ctx : ActualFailureContext)
    (h : ∀ j, 1 ≤ j →
      (class1SlopeDatum ctx).q
        < 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) :
    ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q) := by
  intro k hk hpins
  have h1 := h k (n24_starts_pos ctx hk)
  have h2 := hpins.2
  omega

/-- **The finite cycle-check closure** (the class-0 mirror of
`class1Fibre_empty_of_cycle_band_free`): if SOME period `c ≥ 1` of the orbit (valid from
index `1`) misses the deep band on one full block `[1, c]`, the class-0 pinned arithmetic
holds at the ctx.  With `class1Fibre_orbit_period_exists` (`c ≤ q`) this is decided by at
most `q` orbit readings per ctx. -/
theorem class0Pinned_of_cycle_deepBand_free (ctx : ActualFailureContext) {c : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hband : ∀ j, 1 ≤ j → j ≤ c →
      (class1SlopeDatum ctx).q
        < 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) :
    ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q) :=
  class0Pinned_of_orbit_deepBand_free ctx
    (slopeOrbit_pred_of_cycle
      (P := fun K => (class1SlopeDatum ctx).q < 16 * K) hc hper hband)

/-- **The general bottleneck criterion** (the brief's line 2): if the smallest cycle element
exceeds `q/16` — formally, some floor `m` with `m ≤ K_j` across one period and `q < 16·m` —
the class-0 pinned arithmetic holds at the ctx. -/
theorem class0Pinned_of_cycle_floor (ctx : ActualFailureContext) {c m : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m', 1 ≤ m' →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m' + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m')
    (hfloor : ∀ j, 1 ≤ j → j ≤ c →
      m ≤ slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j)
    (hq : (class1SlopeDatum ctx).q < 16 * m) :
    ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q) := by
  apply class0Pinned_of_cycle_deepBand_free ctx hc hper
  intro j hj1 hjc
  have h := hfloor j hj1 hjc
  omega

/-- **The small-modulus family in pinned form**: on `q < 17` the deep band `16·K ≤ q` is
unsatisfiable (`K ≥ 1`, `q` odd), so the class-0 pinned arithmetic holds OUTRIGHT — the
pinned-field form of the wave-2 `class0Fibre_empty_of_modulus_lt_seventeen`. -/
theorem class0Pinned_of_modulus_lt_seventeen (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q < 17) :
    ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q) := by
  intro k hk hpins
  have horb := slopeOrbit_mem (class1SlopeDatum ctx).hq_odd (class1SlopeDatum ctx).hK₀_pos
    (class1SlopeDatum ctx).hK₀_lt k
  obtain ⟨m, hm⟩ := (class1SlopeDatum ctx).hq_odd
  have h1 := horb.1
  have h2 := hpins.2
  omega

/-! ## Part 4.  The `K = 1` bottleneck: the modulus window `16 ≤ q < 32`

On `q < 32` the deep band `16·K ≤ q` admits ONLY the orbit value `K = 1`, so deep-band
presence on the cycle is EQUIVALENT to `1` lying on the cycle, and the whole odd modulus
family `17 ≤ q ≤ 31` closes by one equality test per cycle element. -/

/-- **The deep band forces `K = 1` below modulus `32`**. -/
theorem deepBand_eq_one_of_modulus_lt_32 {q K : ℕ} (hq32 : q < 32) (hK : 1 ≤ K)
    (h16 : 16 * K ≤ q) : K = 1 := by omega

/-- **The `K = 1` bottleneck, iff form**: on the modulus window `16 ≤ q < 32` the cycle
contains a deep-band element IFF it contains the value `1`. -/
theorem cycle_deepBand_iff_one_of_modulus_window (ctx : ActualFailureContext)
    (hq16 : 16 ≤ (class1SlopeDatum ctx).q) (hq32 : (class1SlopeDatum ctx).q < 32)
    (c : ℕ) :
    (∃ j, 1 ≤ j ∧ j ≤ c
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j
            ≤ (class1SlopeDatum ctx).q)
      ↔ ∃ j, 1 ≤ j ∧ j ≤ c
          ∧ slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j = 1 := by
  constructor
  · rintro ⟨j, hj1, hjc, h16⟩
    have horb := slopeOrbit_mem (class1SlopeDatum ctx).hq_odd (class1SlopeDatum ctx).hK₀_pos
      (class1SlopeDatum ctx).hK₀_lt j
    have h1 := horb.1
    exact ⟨j, hj1, hjc, by omega⟩
  · rintro ⟨j, hj1, hjc, h1⟩
    refine ⟨j, hj1, hjc, ?_⟩
    rw [h1]
    omega

/-- **The avoid-`1` orbit closure on `q < 32`**: if the orbit never takes the value `1` at a
positive index, the class-0 pinned arithmetic holds at every ctx with `q < 32`. -/
theorem class0Pinned_of_orbit_avoids_one_of_modulus_lt_32 (ctx : ActualFailureContext)
    (hq32 : (class1SlopeDatum ctx).q < 32)
    (h1 : ∀ j, 1 ≤ j →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j ≠ 1) :
    ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q) := by
  apply class0Pinned_of_orbit_deepBand_free ctx
  intro j hj
  have horb := slopeOrbit_mem (class1SlopeDatum ctx).hq_odd (class1SlopeDatum ctx).hK₀_pos
    (class1SlopeDatum ctx).hK₀_lt j
  have hne := h1 j hj
  have hpos := horb.1
  omega

/-- **The avoid-`1` cycle closure on `q < 32`** (the `K = 1` bottleneck criterion, finite
form): if one period block `[1, c]` of the orbit avoids the value `1`, the class-0 pinned
arithmetic holds at every ctx with `q < 32` — closing the whole odd modulus family
`17 ≤ q ≤ 31` per cycle check (`q < 17` needs no orbit input at all). -/
theorem class0Pinned_of_cycle_avoids_one_of_modulus_lt_32 (ctx : ActualFailureContext)
    (hq32 : (class1SlopeDatum ctx).q < 32) {c : ℕ} (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (h1 : ∀ j, 1 ≤ j → j ≤ c →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j ≠ 1) :
    ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q) :=
  class0Pinned_of_orbit_avoids_one_of_modulus_lt_32 ctx hq32
    (slopeOrbit_pred_of_cycle (P := fun K => K ≠ 1) hc hper h1)

/-! ## Part 5.  The divisor/gcd modulus-family closures (no cycle computation)

Divisor persistence floors the whole orbit by `gcd(q, K₀)`, so `q < 16·gcd(q, K₀)` closes
the ctx outright — a brand-new unconditional family in pure `(q, K₀)` arithmetic, fed by the
closed-datum pins `q = oddpart(Q·(2|P|+1))`, `K₀ = |P|` of `CNLClass1Closure`. -/

/-- **The divisor-floor closure**: a common divisor `d` of `q` and `K₀` with `q < 16·d`
closes the class-0 pinned arithmetic at the ctx (every orbit value is a positive multiple of
`d`, hence `≥ d > q/16`). -/
theorem class0Pinned_of_dvd_floor (ctx : ActualFailureContext) {d : ℕ}
    (hdq : d ∣ (class1SlopeDatum ctx).q) (hdK : d ∣ (class1SlopeDatum ctx).K₀)
    (hq : (class1SlopeDatum ctx).q < 16 * d) :
    ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q) := by
  apply class0Pinned_of_orbit_deepBand_free ctx
  intro j hj
  have horb := slopeOrbit_mem (class1SlopeDatum ctx).hq_odd (class1SlopeDatum ctx).hK₀_pos
    (class1SlopeDatum ctx).hK₀_lt j
  have hdvd := slopeOrbit_dvd_of_dvd hdq hdK j
  have hle : d ≤ slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j :=
    Nat.le_of_dvd horb.1 hdvd
  omega

/-- **The gcd-floor closure** (unconditional modulus family): `q < 16·gcd(q, K₀)` closes the
class-0 pinned arithmetic at the ctx with NO cycle computation. -/
theorem class0Pinned_of_gcd_floor (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q
        < 16 * Nat.gcd (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀) :
    ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q) :=
  class0Pinned_of_dvd_floor ctx (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _) hq

/-- **The dividing-base family**: every shell whose base numerator divides its modulus with
quotient below `16` (`K₀ ∣ q`, `q < 16·K₀` — e.g. the whole `q = 3·K₀` family of the class-4
fixed point, `q = 5·K₀`, …, `q = 15·K₀`) is class-0-pinned unconditionally. -/
theorem class0Pinned_of_base_dvd_modulus (ctx : ActualFailureContext)
    (hdvd : (class1SlopeDatum ctx).K₀ ∣ (class1SlopeDatum ctx).q)
    (hq : (class1SlopeDatum ctx).q < 16 * (class1SlopeDatum ctx).K₀) :
    ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q) :=
  class0Pinned_of_dvd_floor ctx hdvd dvd_rfl hq

/-- **The cycle divisor-floor closure**: a common divisor `d` of `q` and the orbit value at
ANY positive anchor `j₀`, with `q < 16·d` and a period in hand, closes the class-0 pinned
arithmetic at the ctx (covers even `K₀` whose first step gains the factor). -/
theorem class0Pinned_of_cycle_dvd_floor (ctx : ActualFailureContext) {c d j₀ : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hj₀ : 1 ≤ j₀) (hdq : d ∣ (class1SlopeDatum ctx).q)
    (hd : d ∣ slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j₀)
    (hq : (class1SlopeDatum ctx).q < 16 * d) :
    ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q) := by
  apply class0Pinned_of_orbit_deepBand_free ctx
  intro j hj
  have horb := slopeOrbit_mem (class1SlopeDatum ctx).hq_odd (class1SlopeDatum ctx).hK₀_pos
    (class1SlopeDatum ctx).hK₀_lt j
  have hdvd := slopeOrbit_dvd_of_cycle_dvd hc hper hj₀ hdq hd j hj
  have hle : d ≤ slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j :=
    Nat.le_of_dvd horb.1 hdvd
  omega

/-! ## Part 6.  The window-residue refinement: the EXACT finite-check surface

Only window starts realizing the gap-window floor matter, and each reads the orbit at its
residue `cycleRep c k` — given ANY period, the windowed check is necessary AND sufficient
for the per-ctx pinned arithmetic.  The existential packaging `Class0WindowCycleCheck` is
therefore EQUIVALENT to the capstone field, per ctx and globally. -/

/-- **The window-residue closure**: if every floor-realizing window start has its cycle
representative outside the deep band, the class-0 pinned arithmetic holds at the ctx (the
window may miss all deep residues, e.g. when `|starts| < c`). -/
theorem class0Pinned_of_window_residues (ctx : ActualFailureContext) {c : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (h : ∀ k ∈ ctx.n24CarryData.starts,
      129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
      (class1SlopeDatum ctx).q
        < 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀
            (cycleRep c k)) :
    ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q) := by
  intro k hk hpins
  have h1 : 1 ≤ k := n24_starts_pos ctx hk
  have hrep := slopeOrbit_cycleRep hc hper h1
  have hlt := h k hk hpins.1
  rw [← hrep] at hlt
  have h2 := hpins.2
  omega

/-- **The window-residue check is EXACT**: given any period `c` valid from index `1`, the
per-ctx pinned arithmetic holds IFF every floor-realizing window start has its cycle
representative outside the deep band — the sharpest per-ctx finite check (`≤ q` orbit
readings + `≤ |starts|` comparisons). -/
theorem class0Pinned_iff_window_residues (ctx : ActualFailureContext) {c : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m) :
    (∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q))
      ↔ ∀ k ∈ ctx.n24CarryData.starts,
          129 * shellLadderDepth ctx + 64
              ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
          (class1SlopeDatum ctx).q
            < 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀
                (cycleRep c k) := by
  constructor
  · intro h k hk hgw
    have h1 : 1 ≤ k := n24_starts_pos ctx hk
    have hrep := slopeOrbit_cycleRep hc hper h1
    rcases Nat.lt_or_ge (class1SlopeDatum ctx).q
        (16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀
          (cycleRep c k)) with hlt | hge
    · exact hlt
    · exfalso
      refine h k hk ⟨hgw, ?_⟩
      rw [hrep]
      exact hge
  · intro h
    exact class0Pinned_of_window_residues ctx hc hper h

/-- **The per-ctx finite cycle check** (sufficient, window-free): SOME period of the slope
orbit is deep-band-free over one full block `[1, c]`.  Decided by at most `q` orbit
readings. -/
def Class0CycleDeepBandFree (ctx : ActualFailureContext) : Prop :=
  ∃ c, 1 ≤ c ∧ c ≤ (class1SlopeDatum ctx).q
    ∧ (∀ m, 1 ≤ m →
        slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
          = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    ∧ ∀ j, 1 ≤ j → j ≤ c →
        (class1SlopeDatum ctx).q
          < 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j

/-- **The per-ctx windowed finite check** (necessary AND sufficient): SOME period such that
every floor-realizing window start reads the orbit outside the deep band at its residue. -/
def Class0WindowCycleCheck (ctx : ActualFailureContext) : Prop :=
  ∃ c, 1 ≤ c ∧ c ≤ (class1SlopeDatum ctx).q
    ∧ (∀ m, 1 ≤ m →
        slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
          = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    ∧ ∀ k ∈ ctx.n24CarryData.starts,
        129 * shellLadderDepth ctx + 64
            ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
        (class1SlopeDatum ctx).q
          < 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀
              (cycleRep c k)

/-- The window-free cycle check implies the windowed one (drop the floor input and read the
representative through `cycleRep_pos` / `cycleRep_le`). -/
theorem Class0CycleDeepBandFree.toWindowCheck {ctx : ActualFailureContext}
    (h : Class0CycleDeepBandFree ctx) : Class0WindowCycleCheck ctx := by
  obtain ⟨c, hc1, hcq, hper, hband⟩ := h
  exact ⟨c, hc1, hcq, hper, fun k hk _ =>
    hband (cycleRep c k) (cycleRep_pos hc1 k) (cycleRep_le hc1 k)⟩

/-- The window-free finite cycle check closes the per-ctx pinned arithmetic. -/
theorem class0Pinned_of_cycleCheck (ctx : ActualFailureContext)
    (h : Class0CycleDeepBandFree ctx) :
    ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q) := by
  obtain ⟨c, hc1, hcq, hper, hband⟩ := h
  exact class0Pinned_of_cycle_deepBand_free ctx hc1 hper hband

/-- The windowed finite check closes the per-ctx pinned arithmetic. -/
theorem class0Pinned_of_windowCycleCheck (ctx : ActualFailureContext)
    (h : Class0WindowCycleCheck ctx) :
    ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q) := by
  obtain ⟨c, hc1, hcq, hper, hcheck⟩ := h
  exact class0Pinned_of_window_residues ctx hc1 hper hcheck

/-- **The per-ctx pinned arithmetic IS the windowed finite check** (necessary and
sufficient; the canonical period `1 ≤ c ≤ q` of `class1Fibre_orbit_period_exists` witnesses
the forward direction). -/
theorem class0Pinned_iff_windowCycleCheck (ctx : ActualFailureContext) :
    (∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q))
      ↔ Class0WindowCycleCheck ctx := by
  constructor
  · intro h
    obtain ⟨c, hc1, hcq, hper⟩ := class1Fibre_orbit_period_exists ctx
    exact ⟨c, hc1, hcq, hper,
      (class0Pinned_iff_window_residues ctx hc1 hper).mp h⟩
  · exact class0Pinned_of_windowCycleCheck ctx

/-! ## Part 7.  Honest obstruction: an odd small base puts the deep band ON every cycle

Backward determinism on odd states closes every period at the base: `K_c = K₀` for odd `K₀`.
So when `16·K₀ ≤ q`, EVERY cycle contains a deep-band element and the window-free check
`Class0CycleDeepBandFree` is provably FALSE — on such shells only the windowed check can
close the atom.  This is a proved boundary, not a conjecture. -/

/-- **Every period closes at an odd base**: for odd `K₀`, any period `c ≥ 1` valid from
index `1` satisfies `K_c = K₀` (peel one step by injectivity on odd states). -/
theorem slopeOrbit_period_closes_at_base {q K₀ c : ℕ} (hq : Odd q) (hK1 : 1 ≤ K₀)
    (hKq : K₀ < q) (hodd : Odd K₀) (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m → slopeOrbit q K₀ (m + c) = slopeOrbit q K₀ m) :
    slopeOrbit q K₀ c = K₀ := by
  have h1 := hper 1 le_rfl
  have e1 : 1 + c = c + 1 := Nat.add_comm 1 c
  rw [e1] at h1
  have hstepc : slopeOrbit q K₀ (c + 1) = boundedSlopeStep q (slopeOrbit q K₀ c) := rfl
  have hstep0 : slopeOrbit q K₀ 1 = boundedSlopeStep q K₀ := rfl
  rw [hstepc, hstep0] at h1
  have hmemc := slopeOrbit_mem hq hK1 hKq c
  exact boundedSlopeStep_inj_of_odd hq hmemc.1 hmemc.2 hK1 hKq
    (slopeOrbit_odd hq hK1 hKq c hc) hodd h1

/-- **The deep band sits on every cycle of an odd small base**: odd `K₀` with `16·K₀ ≤ q`
forces a deep-band element on every period block `[1, c]`. -/
theorem cycle_deepBand_of_odd_small_base {q K₀ c : ℕ} (hq : Odd q) (hK1 : 1 ≤ K₀)
    (hKq : K₀ < q) (hodd : Odd K₀) (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m → slopeOrbit q K₀ (m + c) = slopeOrbit q K₀ m)
    (hsmall : 16 * K₀ ≤ q) :
    ∃ j, 1 ≤ j ∧ j ≤ c ∧ 16 * slopeOrbit q K₀ j ≤ q := by
  refine ⟨c, hc, le_rfl, ?_⟩
  rw [slopeOrbit_period_closes_at_base hq hK1 hKq hodd hc hper]
  exact hsmall

/-- **The window-free cycle check is provably FALSE on odd small bases**: `Odd K₀` and
`16·K₀ ≤ q` refute `Class0CycleDeepBandFree ctx`.  On such shells the windowed check
(`Class0WindowCycleCheck`, the exact surface) is the ONLY remaining closure route. -/
theorem not_class0CycleDeepBandFree_of_odd_small_base (ctx : ActualFailureContext)
    (hodd : Odd (class1SlopeDatum ctx).K₀)
    (hsmall : 16 * (class1SlopeDatum ctx).K₀ ≤ (class1SlopeDatum ctx).q) :
    ¬ Class0CycleDeepBandFree ctx := by
  rintro ⟨c, hc1, hcq, hper, hband⟩
  have hbase := slopeOrbit_period_closes_at_base (class1SlopeDatum ctx).hq_odd
    (class1SlopeDatum ctx).hK₀_pos (class1SlopeDatum ctx).hK₀_lt hodd hc1 hper
  have hlt := hband c hc1 le_rfl
  rw [hbase] at hlt
  omega

/-! ## Part 8.  Fibre-level mirrors and the field-level assemblies

The per-ctx closures land on the wave-2 emptiness surfaces through
`class0Fibre_empty_iff_pinned`, and assemble into EXACTLY the capstone field shape of
`Erdos260SharpResidual.class0Pinned`. -/

/-- **Fibre-level orbit closure**: a deep-band-free orbit empties the class-0 routed fibre
of the genuine route. -/
theorem class0Fibre_empty_of_orbit_deepBand_free (ctx : ActualFailureContext)
    (h : ∀ j, 1 ≤ j →
      (class1SlopeDatum ctx).q
        < 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0 = ∅ :=
  (class0Fibre_empty_iff_pinned ctx).mpr (class0Pinned_of_orbit_deepBand_free ctx h)

/-- **Fibre-level finite cycle-check closure** (the class-0 mirror of
`class1Fibre_empty_of_cycle_band_free`): a deep-band-free period empties the class-0 routed
fibre of the genuine route. -/
theorem class0Fibre_empty_of_cycle_deepBand_free (ctx : ActualFailureContext) {c : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hband : ∀ j, 1 ≤ j → j ≤ c →
      (class1SlopeDatum ctx).q
        < 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0 = ∅ :=
  (class0Fibre_empty_iff_pinned ctx).mpr
    (class0Pinned_of_cycle_deepBand_free ctx hc hper hband)

/-- The v3 seed budget routes through the genuine route, so the cycle-check closure applies
to it verbatim (the class-0 mirror of `v3_class1Fibre_empty_of_cycle_band_free`). -/
theorem v3_class0Fibre_empty_of_cycle_deepBand_free
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runChain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (ctx : ActualFailureContext) {c : ℕ} (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hband : ∀ j, 1 ≤ j → j ≤ c →
      (class1SlopeDatum ctx).q
        < 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) :
    routedFibre ctx.n24CarryData
      ((v3Budget towerCount runChain returnCharge) ctx).route 0 = ∅ :=
  class0Fibre_empty_of_cycle_deepBand_free ctx hc hper hband

/-- **The capstone field IS the per-ctx windowed finite check, globally** (necessary and
sufficient): the LHS is verbatim the `class0Pinned` field of `Erdos260SharpResidual`. -/
theorem class0Pinned_field_iff_windowCycleCheck :
    (∀ ctx : ActualFailureContext, ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q))
      ↔ ∀ ctx : ActualFailureContext, Class0WindowCycleCheck ctx :=
  forall_congr' fun ctx => class0Pinned_iff_windowCycleCheck ctx

/-- **The field-level modulus split**: `q < 17` shells need NO input (closed outright);
delivering the windowed check on `q ≥ 17` shells yields the capstone `class0Pinned` field
verbatim. -/
theorem class0Pinned_field_of_modulus_split
    (h : ∀ ctx : ActualFailureContext, 17 ≤ (class1SlopeDatum ctx).q →
      Class0WindowCycleCheck ctx) :
    ∀ ctx : ActualFailureContext, ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q) := by
  intro ctx
  rcases Nat.lt_or_ge (class1SlopeDatum ctx).q 17 with hq | hq
  · exact class0Pinned_of_modulus_lt_seventeen ctx hq
  · exact class0Pinned_of_windowCycleCheck ctx (h ctx hq)

/-- **The field-level bottleneck split**: `q < 17` closed outright; `17 ≤ q < 32` carried by
the avoid-`1` cycle data (the `K = 1` bottleneck); only `q ≥ 32` retains the general
windowed check.  The conclusion is the capstone `class0Pinned` field verbatim. -/
theorem class0Pinned_field_of_bottleneck_split
    (hmid : ∀ ctx : ActualFailureContext,
      17 ≤ (class1SlopeDatum ctx).q → (class1SlopeDatum ctx).q < 32 →
      ∃ c, 1 ≤ c
        ∧ (∀ m, 1 ≤ m →
            slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
              = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
        ∧ ∀ j, 1 ≤ j → j ≤ c →
            slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j ≠ 1)
    (hbig : ∀ ctx : ActualFailureContext, 32 ≤ (class1SlopeDatum ctx).q →
      Class0WindowCycleCheck ctx) :
    ∀ ctx : ActualFailureContext, ∀ k ∈ ctx.n24CarryData.starts,
      ¬(129 * shellLadderDepth ctx + 64
          ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ∧ 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
            ≤ (class1SlopeDatum ctx).q) := by
  intro ctx
  rcases Nat.lt_or_ge (class1SlopeDatum ctx).q 17 with hq17 | hq17
  · exact class0Pinned_of_modulus_lt_seventeen ctx hq17
  · rcases Nat.lt_or_ge (class1SlopeDatum ctx).q 32 with hq32 | hq32
    · obtain ⟨c, hc1, hper, h1⟩ := hmid ctx hq17 hq32
      exact class0Pinned_of_cycle_avoids_one_of_modulus_lt_32 ctx hq32 hc1 hper h1
    · exact class0Pinned_of_windowCycleCheck ctx (hbig ctx hq32)

/-- **The wave-2 residual from the windowed checks**: the per-ctx windowed finite checks
discharge `Class0FibreEmpty` for EVERY budget routing through the genuine route (covers
`v3Budget` and the capstone `sixAtomBudget`/`sharpAtomBudget` alike). -/
theorem class0FibreEmpty_of_windowCycleCheck
    (budget : ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx)
    (hroute : ∀ ctx : ActualFailureContext, (budget ctx).route = genuineChargeRoute ctx)
    (h : ∀ ctx : ActualFailureContext, Class0WindowCycleCheck ctx) :
    Class0FibreEmpty budget :=
  class0FibreEmpty_of_genuineRoute_pinned budget hroute
    (fun ctx => (class0Pinned_iff_windowCycleCheck ctx).mpr (h ctx))

/-- **The v3 atom from the split surface**: windowed checks on `q ≥ 17` shells only (the
`q < 17` half is a theorem) discharge the wave-1/wave-2 class-0 atom for the v3 budget. -/
theorem v3_class0FibreEmpty_of_modulus_split_check
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runChain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (h : ∀ ctx : ActualFailureContext, 17 ≤ (class1SlopeDatum ctx).q →
      Class0WindowCycleCheck ctx) :
    Class0FibreEmpty (v3Budget towerCount runChain returnCharge) :=
  class0FibreEmpty_of_genuineRoute_pinned _ (fun _ => rfl)
    (class0Pinned_field_of_modulus_split h)

/-! ## Part 9.  Machine-readable status (brutally honest) -/

/-- Honest machine-readable status of the wave-3 class-0 deep-band cycle closure. -/
def chernoffClass0CycleClosureStatus : List String :=
  [ "TARGET (capstone field): Erdos260SharpResidual.class0Pinned - forall ctx, forall k in " ++
      "starts, NOT (129L+64 <= 64*gW(k) AND 16*K_k <= q).  Every per-ctx closure below " ++
      "concludes EXACTLY this body; the field-level assemblies conclude the field verbatim.",
    "CLOSED (generic cycle propagation, NEW): any predicate verified on one period block " ++
      "[1,c] of the slope orbit holds at every positive index (slopeOrbit_pred_of_cycle) - " ++
      "the predicate abstraction of the wave-2 band-4 propagation, instantiated here with " ++
      "the deep-band miss q < 16K, the value test K <> 1, and the floor test m <= K.",
    "CLOSED (residue reduction, NEW): for any period c valid from index 1, K_k = " ++
      "K_{cycleRep c k} with cycleRep c k in [1,c] (cycleRep, cycleRep_pos, cycleRep_le, " ++
      "slopeOrbit_add_mul_period, slopeOrbit_cycleRep) - window starts read the orbit at " ++
      "their residue class mod c.",
    "CLOSED (per-ctx finite cycle-check closures, NEW - the class-0 mirror of " ++
      "class1Fibre_empty_of_cycle_band_free): a deep-band-free orbit or period closes the " ++
      "pinned arithmetic (class0Pinned_of_orbit_deepBand_free, " ++
      "class0Pinned_of_cycle_deepBand_free, class0Pinned_of_cycleCheck) and empties the " ++
      "class-0 routed fibre (class0Fibre_empty_of_orbit_deepBand_free, " ++
      "class0Fibre_empty_of_cycle_deepBand_free, v3_class0Fibre_empty_of_cycle_deepBand_free)" ++
      " - at most q orbit readings per ctx (class1Fibre_orbit_period_exists gives c <= q).",
    "CLOSED (general bottleneck criterion, NEW - the brief's line 2): smallest cycle " ++
      "element > q/16 closes the ctx (class0Pinned_of_cycle_floor: any floor m <= K_j on " ++
      "[1,c] with q < 16m).",
    "CLOSED (K = 1 bottleneck on q < 32, NEW): the deep band 16K <= q < 32 forces K = 1 " ++
      "(deepBand_eq_one_of_modulus_lt_32), so cycle deep-band presence IS 1-membership " ++
      "(cycle_deepBand_iff_one_of_modulus_window) and the whole odd family 17 <= q <= 31 " ++
      "closes whenever the cycle avoids 1 (class0Pinned_of_orbit_avoids_one_of_modulus_lt_32," ++
      " class0Pinned_of_cycle_avoids_one_of_modulus_lt_32) - one equality test per cycle " ++
      "element.  Example landscape (manuscript arithmetic, not formalized per-value): q = 17" ++
      " has the deep cycle 1->15->13->9 AND the clean cycle 3->7->11->5; q = 21 has clean " ++
      "cycles {3}, {7}, {9,15}, {5,19,17,13} and only {1,11} deep.",
    "CLOSED (divisor/gcd persistence families, NEW - no cycle computation): the E.13 step " ++
      "preserves common divisors of q and the state (slopeOrbit_dvd_of_dvd_from, " ++
      "slopeOrbit_dvd_of_dvd, slopeOrbit_dvd_of_cycle_dvd), so q < 16*gcd(q,K0) closes the " ++
      "ctx outright (class0Pinned_of_gcd_floor, class0Pinned_of_dvd_floor, " ++
      "class0Pinned_of_cycle_dvd_floor) - instantiation: every shell with K0 | q and " ++
      "q < 16*K0 (class0Pinned_of_base_dvd_modulus), e.g. the whole q = 3*K0 family of the " ++
      "class-4 fixed point and q = 5*K0, ..., q = 15*K0.",
    "CLOSED (small-modulus family in pinned form): q < 17 closes outright " ++
      "(class0Pinned_of_modulus_lt_seventeen; 16K <= q needs K >= 1 and q odd) - the " ++
      "pinned-field form of the wave-2 fibre closure, consumed by the field splits.",
    "CLOSED (window-residue refinement, NEW - the EXACT surface): only floor-realizing " ++
      "window starts matter, each at its residue cycleRep c k " ++
      "(class0Pinned_of_window_residues); given ANY period the windowed check is necessary " ++
      "AND sufficient (class0Pinned_iff_window_residues), packaged existentially as " ++
      "Class0WindowCycleCheck with the per-ctx iff class0Pinned_iff_windowCycleCheck and " ++
      "the field-level iff class0Pinned_field_iff_windowCycleCheck.  The window-free check " ++
      "Class0CycleDeepBandFree implies it (Class0CycleDeepBandFree.toWindowCheck).",
    "CLOSED (field assemblies, NEW): class0Pinned_field_of_modulus_split (q < 17 free; " ++
      "windowed checks only on q >= 17) and class0Pinned_field_of_bottleneck_split (q < 17 " ++
      "free; 17 <= q < 32 via avoid-1 cycle data; q >= 32 via windowed checks) conclude the " ++
      "capstone field verbatim; class0FibreEmpty_of_windowCycleCheck and " ++
      "v3_class0FibreEmpty_of_modulus_split_check land on the wave-2 Class0FibreEmpty for " ++
      "every genuine-route budget.",
    "OBSTRUCTION PROVED (the honest boundary of cycle-only checks): every period closes at " ++
      "an ODD base, K_c = K0 (slopeOrbit_period_closes_at_base, by backward determinism on " ++
      "odd states), so Odd K0 with 16*K0 <= q puts the deep band ON every cycle " ++
      "(cycle_deepBand_of_odd_small_base) and Class0CycleDeepBandFree is provably FALSE " ++
      "(not_class0CycleDeepBandFree_of_odd_small_base) - on such shells ONLY the windowed " ++
      "check can close the atom.",
    "NOT CLOSED (the honest wave-3 residual): the atom itself.  The deep band is genuinely " ++
      "reachable (q = 17: the orbit 1 -> 15 -> 13 -> 9 -> 1 revisits K = 1 every fourth " ++
      "step), the formalization carries no hitGap <-> canonGap bridge at the actual ctx " ++
      "(same obstruction as classes 1/4), and the pressure floor forbids proving all " ++
      "classes empty.  The exact remaining surface is: per ctx with q >= 17, the windowed " ++
      "finite check Class0WindowCycleCheck (equivalently the original pinned field, by the " ++
      "proved iff) - i.e. shells whose orbit cycle meets the deep band at a floor-realizing " ++
      "window residue.  We do NOT claim unconditional closure of the atom." ]

theorem chernoffClass0CycleClosureStatus_nonempty :
    chernoffClass0CycleClosureStatus ≠ [] := by
  simp [chernoffClass0CycleClosureStatus]

/-! ## Part 10.  Axiom-cleanliness audit -/

#print axioms slopeOrbit_pred_of_cycle
#print axioms slopeOrbit_add_mul_period
#print axioms cycleRep_pos
#print axioms cycleRep_le
#print axioms slopeOrbit_cycleRep
#print axioms slopeOrbit_dvd_of_dvd_from
#print axioms slopeOrbit_dvd_of_dvd
#print axioms slopeOrbit_dvd_of_cycle_dvd
#print axioms class0Pinned_of_orbit_deepBand_free
#print axioms class0Pinned_of_cycle_deepBand_free
#print axioms class0Pinned_of_cycle_floor
#print axioms class0Pinned_of_modulus_lt_seventeen
#print axioms deepBand_eq_one_of_modulus_lt_32
#print axioms cycle_deepBand_iff_one_of_modulus_window
#print axioms class0Pinned_of_orbit_avoids_one_of_modulus_lt_32
#print axioms class0Pinned_of_cycle_avoids_one_of_modulus_lt_32
#print axioms class0Pinned_of_dvd_floor
#print axioms class0Pinned_of_gcd_floor
#print axioms class0Pinned_of_base_dvd_modulus
#print axioms class0Pinned_of_cycle_dvd_floor
#print axioms class0Pinned_of_window_residues
#print axioms class0Pinned_iff_window_residues
#print axioms Class0CycleDeepBandFree.toWindowCheck
#print axioms class0Pinned_of_cycleCheck
#print axioms class0Pinned_of_windowCycleCheck
#print axioms class0Pinned_iff_windowCycleCheck
#print axioms slopeOrbit_period_closes_at_base
#print axioms cycle_deepBand_of_odd_small_base
#print axioms not_class0CycleDeepBandFree_of_odd_small_base
#print axioms class0Fibre_empty_of_orbit_deepBand_free
#print axioms class0Fibre_empty_of_cycle_deepBand_free
#print axioms v3_class0Fibre_empty_of_cycle_deepBand_free
#print axioms class0Pinned_field_iff_windowCycleCheck
#print axioms class0Pinned_field_of_modulus_split
#print axioms class0Pinned_field_of_bottleneck_split
#print axioms class0FibreEmpty_of_windowCycleCheck
#print axioms v3_class0FibreEmpty_of_modulus_split_check
#print axioms chernoffClass0CycleClosureStatus_nonempty

end

end Erdos260
