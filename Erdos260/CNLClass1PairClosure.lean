import Erdos260.Erdos260DatumCapstone

/-!
# Erdős 260 — CNL / class-1 pair closure: band-4 residue congruences, per-residue-window
# count bounds, the `r = 0` top-residue dichotomy, gcd-window criteria, and the strictly
# smaller successor of `Class1DatumResidual`

The consumer is `Class1DatumResidual` (`CNLClass1DatumClosure.lean`): its open data are
exactly the divisor-pin pairs `(q, K₀)` whose recurrent orbit READS band 4
(`canonGap = 4`, the window `8K ≤ q < 16K`) — `q = 25 @ {2,12}`, `29 @ 14`, `37 @ 18`,
`41 @ 20`, `47 @ 23`, `49 @ {3,24}`, the in-modulus leftovers `35 @ {3,17}`, `39 @ 6`,
`55 @ 5`, `57 @ {1,28}`, `63 @ 10`, `69 @ {11,34}`, `75 @ {7,12,37}`, `87 @ {1,14}`,
`99 @ 5` (twenty-three pairs), plus the un-enumerated `q ≥ 101`.  This module proves,
without closing any of them dishonestly:

1. **Per-pair band-4 residue congruences** (`class1Fibre_residue_of_datum_*`):
   twenty-one of the twenty-three cycles carry EXACTLY ONE band-4 residue `j₄ ∈ [1, c]`,
   so every class-1 start at such a datum satisfies the explicit congruence
   `k % c = j₄ % c` AND the orbit-value pin `K_k = v₄`; the two `q = 69` cycles carry
   exactly TWO band-4 residues, giving the explicit two-class disjunction.  Everything
   is transported along the certified period through `slopeOrbit_eq_residue` (the
   `class1Fibre_residue_pin` pattern, with the minimality input replaced by the
   certified residue table).
2. **Per-residue-window count bounds** (`class1Band4CycleBand`,
   `class1Fibre_card_le_cycleDensity`, `class1Fibre_card_le_of_datum_*`): the class-1
   fibre injects into (band-4 cycle residues) × (window blocks), so on every open pair
   `#fibre₁ ≤ b₄·⌈W/c⌉` with `b₄ ∈ {1, 2}` — AT MOST ONE member per band-4 residue per
   window.  Combined with the proved rigidity lemmas
   (`class1Fibre_pair_rigidity_of_datum_*`): two members (same residue class when
   `b₄ = 2`) carry equal orbit numerators, satisfy the concrete hit-gap repeat equation
   `a(k+r+1) + a(k') = a(k'+r+1) + a(k)` (`class1Fibre_span_rigidity`), and their
   spacing is a full orbit period (`class1Fibre_spacing_period`).
3. **The `r = 0` top-start dichotomy** (`class1Fibre_top_notMem_of_residue_*`,
   `class1_r0_top_verdict_of_datum_*`): if the computable top residue
   `cnlWindowTopStart ctx % c` misses the band-4 class(es), the top start is NOT
   class-1 (for every `r`, in particular `r = 0`); otherwise the `r = 0` demand reduces
   to ONE explicit hit-gap disequality `64·hitGap(top) ≠ 129L + 64`
   (`class1Fibre_r0_top_notMem_of_hitGap` via `class1Fibre_r0_hitGap_pin`).
4. **General `q ≥ 101` sufficient criteria** (the gcd suite, mirroring
   `datum_gcd_floor_forces_K_le_seven`): `gcd(q, K₀)` divides EVERY orbit value
   (`slopeOrbit_gcd_dvd`), so a band-4 window free of `gcd`-multiples empties the fibre
   (`Class1GcdWindowMiss`, `class1Fibre_empty_of_gcd_window_miss`); numeric form
   `q < 8·gcd` (`class1Fibre_empty_of_eight_mul_gcd_gt`); at `q < 16·gcd` the orbit
   value is pinned to `gcd` itself (`class1Fibre_orbit_eq_gcd_of_window`) and the lever
   is confined to `K₀ ≤ 7` (`class1_gcd_window_K₀_le_seven`).
5. **The strictly smaller successor** `Class1PairResidual`: the same two fields as
   `Class1DatumResidual`, each additionally relieved of the gcd-window-miss shells, and
   the `r = 0` field additionally relieved of the top-residue-miss shells
   (`Class1PairTopMiss`).  Bridges: `class1DatumResidual_of_pairResidual` (additive),
   `class1DeepResidual_of_pairResidual` (through `class1DeepResidual_of_datumResidual`),
   the capstone discharges `class1Pinned_of_pairResidual` /
   `class1FibreEmpty_of_pairResidual`, and the weakening witness
   `class1PairResidual_of_datumResidual`.

No `sorry`, `admit`, new `axiom`, or `native_decide`.
-/

namespace Erdos260

open Finset

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 1.  The band-4 cycle band and the cycle-density count engine -/

/-- **The band-4 cycle band**: the residue indices `j ∈ [1, c]` of one orbit period whose
band is `4` (the class-1 window `8K ≤ q < 16K`) — the class-1 mirror of the proved
class-5 `class5CycleBand` and class-2 `towerBand4CycleCount`. -/
def class1Band4CycleBand (ctx : ActualFailureContext) (c : ℕ) : Finset ℕ :=
  (Finset.Icc 1 c).filter (fun j =>
    canonGap (class1SlopeDatum ctx).q
      (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) = 4)

theorem mem_class1Band4CycleBand (ctx : ActualFailureContext) {c j : ℕ} :
    j ∈ class1Band4CycleBand ctx c
      ↔ (1 ≤ j ∧ j ≤ c)
        ∧ canonGap (class1SlopeDatum ctx).q
            (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) = 4 := by
  unfold class1Band4CycleBand
  rw [Finset.mem_filter, Finset.mem_Icc]

/-- Datum substitution for the band-4 cycle band (the per-pair tables are pure
`(q, K₀)` statements). -/
theorem class1Band4CycleBand_congr (ctx : ActualFailureContext) {qv Kv : ℕ}
    (hq : (class1SlopeDatum ctx).q = qv) (hK : (class1SlopeDatum ctx).K₀ = Kv)
    (c : ℕ) :
    class1Band4CycleBand ctx c
      = (Finset.Icc 1 c).filter (fun j => canonGap qv (slopeOrbit qv Kv j) = 4) := by
  unfold class1Band4CycleBand
  rw [hq, hK]

private theorem cnl_window_residue_block_inj {c F k₁ k₂ : ℕ} (hc : 1 ≤ c)
    (h₁1 : 1 ≤ k₁) (h₁F : F ≤ k₁) (h₂F : F ≤ k₂) (hle : k₁ ≤ k₂)
    (hmod : (k₁ - 1) % c = (k₂ - 1) % c)
    (hdiv : (k₁ - F) / c = (k₂ - F) / c) :
    k₁ = k₂ := by
  have hdvd : c ∣ (k₂ - 1) - (k₁ - 1) := (Nat.modEq_iff_dvd' (by omega)).mp hmod
  obtain ⟨t, ht⟩ := hdvd
  have hk2F : k₂ - F = k₁ - F + c * t := by omega
  rw [hk2F, Nat.add_mul_div_left _ _ (show 0 < c by omega)] at hdiv
  have ht0 : t = 0 := by omega
  subst ht0
  rw [Nat.mul_zero] at ht
  omega

/-- **The class-1 cycle-density count bound**: for any orbit period `c` valid from index
`1`, the class-1 fibre injects into (band-4 cycle residues) × (window blocks):
`#fibre₁ ≤ #class1Band4CycleBand · ⌈W/c⌉` — at most one member per band-4 residue per
window block. -/
theorem class1Fibre_card_le_cycleDensity (ctx : ActualFailureContext) {c : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx c).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c) := by
  classical
  have hW1 : 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card :=
    le_trans (Nat.le_add_left 1 ctx.n24CarryData.r) (cnlMulti_r_add_one_le_width ctx)
  have hmaps : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1,
      ((k - 1) % c + 1,
        (k - ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X) / c)
        ∈ (class1Band4CycleBand ctx c) ×ˢ
            Finset.range
              (((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c) := by
    intro k hk
    have hk1 : 1 ≤ k := class1Fibre_start_pos ctx hk
    have hwin := class1Fibre_mem_window ctx hk
    rw [Finset.mem_product]
    constructor
    · rw [mem_class1Band4CycleBand]
      have hmodlt : (k - 1) % c < c := Nat.mod_lt _ (by omega)
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      have heq := slopeOrbit_eq_residue hc hper hk1
      rw [← heq]
      exact class1Fibre_canonGap_eq ctx hk
    · rw [Finset.mem_range]
      have hdle : (k - ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X) / c
          ≤ ((supportShell ctx.shell.d ctx.shell.X).card - 1) / c :=
        Nat.div_le_div_right (by omega)
      have hceil : ((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c
          = ((supportShell ctx.shell.d ctx.shell.X).card - 1) / c + 1 := by
        have he : (supportShell ctx.shell.d ctx.shell.X).card + c - 1
            = ((supportShell ctx.shell.d ctx.shell.X).card - 1) + c := by omega
        rw [he, Nat.add_div_right _ (by omega)]
      omega
  have hinj : Set.InjOn (fun k : ℕ =>
      ((k - 1) % c + 1,
        (k - ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X) / c))
      (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1) := by
    intro k₁ hk₁ k₂ hk₂ heq
    have hk₁' := Finset.mem_coe.mp hk₁
    have hk₂' := Finset.mem_coe.mp hk₂
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hmod1, hdiv⟩ := heq
    have hmod : (k₁ - 1) % c = (k₂ - 1) % c := by omega
    have h1F := (class1Fibre_mem_window ctx hk₁').1
    have h2F := (class1Fibre_mem_window ctx hk₂').1
    have h11 : 1 ≤ k₁ := class1Fibre_start_pos ctx hk₁'
    have h21 : 1 ≤ k₂ := class1Fibre_start_pos ctx hk₂'
    rcases le_total k₁ k₂ with hle | hle
    · exact cnl_window_residue_block_inj hc h11 h1F h2F hle hmod hdiv
    · exact (cnl_window_residue_block_inj hc h21 h2F h1F hle hmod.symm hdiv.symm).symm
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ ((class1Band4CycleBand ctx c) ×ˢ
          Finset.range
            (((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c)).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ = (class1Band4CycleBand ctx c).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c) := by
        rw [Finset.card_product, Finset.card_range]

/-- The cycle-density bound at SOME period `c ≤ q` — unconditional existence via
`class1Fibre_orbit_period_exists`. -/
theorem class1Fibre_card_le_cycleDensity_exists (ctx : ActualFailureContext) :
    ∃ c : ℕ, 1 ≤ c ∧ c ≤ (class1SlopeDatum ctx).q ∧
      (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
        ≤ (class1Band4CycleBand ctx c).card
          * (((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c) := by
  obtain ⟨c, hc1, hcq, hper⟩ := class1Fibre_orbit_period_exists ctx
  exact ⟨c, hc1, hcq, class1Fibre_card_le_cycleDensity ctx hc1 hper⟩

/-- A certified residue table bounds the band-4 cycle band through an explicit
superset. -/
theorem band4_cycle_card_le_of_subset {q K c b : ℕ} {B : Finset ℕ}
    (h : ∀ j, 1 ≤ j → j ≤ c → canonGap q (slopeOrbit q K j) = 4 → j ∈ B)
    (hB : B.card ≤ b) :
    ((Finset.Icc 1 c).filter
      (fun j => canonGap q (slopeOrbit q K j) = 4)).card ≤ b := by
  refine le_trans (Finset.card_le_card ?_) hB
  intro j hj
  rw [Finset.mem_filter, Finset.mem_Icc] at hj
  exact h j hj.1.1 hj.1.2 hj.2

/-! ## Part 2.  The gcd-window criteria (the general `q ≥ 101` levers)

`gcd(q, K₀)` is invariant under the E.13 step (`2^g·K − q` keeps every common divisor of
`q` and `K`), so it divides EVERY orbit value.  A band-4 window `(q/16, q/8]` free of
`gcd`-multiples therefore empties the class-1 fibre — for every modulus, in particular
the un-enumerated `q ≥ 101`.  This mirrors the class-0 gcd-floor suite
(`datum_gcd_floor_forces_K_le_seven`). -/

/-- **The orbit gcd invariance**: `gcd(q, K₀)` divides every orbit value. -/
theorem slopeOrbit_gcd_dvd (q K₀ : ℕ) (j : ℕ) :
    Nat.gcd q K₀ ∣ slopeOrbit q K₀ j := by
  induction j with
  | zero => exact Nat.gcd_dvd_right q K₀
  | succ j ih =>
      have hstep : slopeOrbit q K₀ (j + 1)
          = boundedSlopeStep q (slopeOrbit q K₀ j) := rfl
      rw [hstep]
      unfold boundedSlopeStep
      exact Nat.dvd_sub (ih.mul_left _) (Nat.gcd_dvd_left q K₀)

/-- **The gcd-window-miss criterion**: no multiple of `gcd(q, K₀)` lies in the band-4
window `8v ≤ q < 16v`. -/
def Class1GcdWindowMiss (ctx : ActualFailureContext) : Prop :=
  ∀ v : ℕ, Nat.gcd (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ ∣ v →
    ¬(8 * v ≤ (class1SlopeDatum ctx).q ∧ (class1SlopeDatum ctx).q < 16 * v)

/-- **Gcd-window-miss empties the class-1 fibre** — for EVERY modulus (the general
`q ≥ 101` sufficient criterion): a class-1 start needs a band-4 orbit value, which is a
`gcd`-multiple inside the window. -/
theorem class1Fibre_empty_of_gcd_window_miss (ctx : ActualFailureContext)
    (h : Class1GcdWindowMiss ctx) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro k hk
  have hband := class1Fibre_canonGap_eq ctx hk
  have horb := slopeOrbit_mem (class1SlopeDatum ctx).hq_odd
    (class1SlopeDatum ctx).hK₀_pos (class1SlopeDatum ctx).hK₀_lt k
  exact h _ (slopeOrbit_gcd_dvd _ _ k) ((canonGap_eq_four_iff horb.1).mp hband)

/-- **The numeric gcd closure**: `q < 8·gcd(q, K₀)` empties the class-1 fibre (every
positive `gcd`-multiple already overshoots the window). -/
theorem class1Fibre_empty_of_eight_mul_gcd_gt (ctx : ActualFailureContext)
    (h8 : (class1SlopeDatum ctx).q
      < 8 * Nat.gcd (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ := by
  refine class1Fibre_empty_of_gcd_window_miss ctx ?_
  intro v hv hcon
  rcases Nat.eq_zero_or_pos v with rfl | hvpos
  · omega
  · have hgv : Nat.gcd (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ ≤ v :=
      Nat.le_of_dvd hvpos hv
    omega

/-- **The gcd value pin**: at `q < 16·gcd(q, K₀)` the only window candidate is the gcd
itself, so every class-1 start has its orbit value EQUAL to `gcd(q, K₀)`. -/
theorem class1Fibre_orbit_eq_gcd_of_window (ctx : ActualFailureContext)
    (h16 : (class1SlopeDatum ctx).q
      < 16 * Nat.gcd (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀)
    {k : ℕ} (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1) :
    slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
      = Nat.gcd (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ := by
  have hband := class1Fibre_canonGap_eq ctx hk
  have horb := slopeOrbit_mem (class1SlopeDatum ctx).hq_odd
    (class1SlopeDatum ctx).hK₀_pos (class1SlopeDatum ctx).hK₀_lt k
  have hwin := (canonGap_eq_four_iff horb.1).mp hband
  obtain ⟨m, hm⟩ := slopeOrbit_gcd_dvd (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · interval_cases m
    · have h1 := horb.1
      rw [hm] at h1
      omega
    · rw [hm]
      exact Nat.mul_one _
  · exfalso
    have h2 : Nat.gcd (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ * 2
        ≤ Nat.gcd (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ * m :=
      Nat.mul_le_mul_left _ hm2
    rw [hm] at hwin
    have h16' : 16 * Nat.gcd (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀
        ≤ 8 * (Nat.gcd (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ * m) := by
      calc 16 * Nat.gcd (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀
          = 8 * (Nat.gcd (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ * 2) := by
            ring
        _ ≤ 8 * (Nat.gcd (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ * m) :=
            Nat.mul_le_mul_left 8 h2
    omega

/-- **The gcd-window lever is confined to small bases** — the class-1 face of
`datum_gcd_floor_forces_K_le_seven`: under the divisor pin, `q < 16·gcd(q, K₀)` forces
`K₀ ≤ 7`. -/
theorem class1_gcd_window_K₀_le_seven (ctx : ActualFailureContext)
    (hfl : (class1SlopeDatum ctx).q
      < 16 * Nat.gcd (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀) :
    (class1SlopeDatum ctx).K₀ ≤ 7 :=
  class0_datum_gcd_floor_K₀_le_seven ctx hfl

/-! ## Part 3.  The generic `r = 0` hit-gap closer -/

/-- On `r = 0` shells, a single explicit hit-gap disequality at the top start excludes
it from the class-1 fibre (the contrapositive of `class1Fibre_r0_hitGap_pin`). -/
theorem class1Fibre_r0_top_notMem_of_hitGap (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0)
    (hgap : 64 * hitGap ctx.n24CarryData.a (cnlWindowTopStart ctx)
      ≠ 129 * shellLadderDepth ctx + 64) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 :=
  fun hk => hgap (class1Fibre_r0_hitGap_pin ctx hr hk)

/-! ## Part 4.  The per-pair tables: the band-4 residues of each open cycle

Each `cnlPairCycle_q_K₀` certifies, by pure numeral arithmetic through
`slopeOrbit_step_eval` (no `Nat.log` computation), that the `(q, K₀)` orbit is purely
periodic with the stated period `c`, records the band-4 cycle value(s), and proves that
EVERY band-4 reading lands in the certified residue set. -/

/-- `(q, K₀) = (25, 2)`: period `10`, cycle `7 → 3 → 23 → 21 → 17 → 9 → 11 → 19 → 13 → 1`, bands `2, 4, 1, 1, 1, 2, 2, 1, 1, 5` — band-4 residue set `{2}` (values `3`), congruence class(es) `k % 10 ∈ {2}`. -/
private theorem cnlPairCycle_25_2 :
    slopeOrbit 25 2 (1 + 10) = slopeOrbit 25 2 1
      ∧ slopeOrbit 25 2 2 = 3
      ∧ ∀ j, 1 ≤ j → j ≤ 10 →
          canonGap 25 (slopeOrbit 25 2 j) = 4 → j ∈ ({2} : Finset ℕ) := by
  have e0 : slopeOrbit 25 2 0 = 2 := rfl
  have e1 : slopeOrbit 25 2 1 = 7 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 25 2 2 = 3 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 25 2 3 = 23 :=
    slopeOrbit_step_eval 2 3 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 25 2 4 = 21 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 25 2 5 = 17 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 25 2 6 = 9 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 25 2 7 = 11 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 25 2 8 = 19 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 25 2 9 = 13 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 25 2 10 = 1 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 25 2 11 = 7 :=
    slopeOrbit_step_eval 10 4 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, e2, ?_⟩
  · show slopeOrbit 25 2 11 = slopeOrbit 25 2 1
    rw [e11, e1]
  · intro j hj1 hjc hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

private theorem cnlPairResidue_25_2 {k : ℕ} (hk1 : 1 ≤ k)
    (hband : canonGap 25 (slopeOrbit 25 2 k) = 4) :
    k % 10 = 2 ∧ slopeOrbit 25 2 k = 3 := by
  have hper := slopeOrbit_period_of_return cnlPairCycle_25_2.1
  have hres := slopeOrbit_eq_residue (by norm_num) hper hk1
  have hmod : (k - 1) % 10 < 10 := Nat.mod_lt _ (by norm_num)
  have hmem := cnlPairCycle_25_2.2.2 ((k - 1) % 10 + 1) (by omega) (by omega)
    (by rw [← hres]; exact hband)
  have hj4 := Finset.mem_singleton.mp hmem
  refine ⟨by omega, ?_⟩
  rw [hres, hj4]
  exact cnlPairCycle_25_2.2.1

/-- `(q, K₀) = (25, 2)`: every class-1 start satisfies the explicit congruence `k % 10 = 2`
and carries the unique band-4 orbit value `3`. -/
theorem class1Fibre_residue_of_datum_25_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 25) (hK : (class1SlopeDatum ctx).K₀ = 2)
    {k : ℕ} (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1) :
    k % 10 = 2
      ∧ slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k = 3 := by
  have hband := class1Fibre_canonGap_eq ctx hk
  have hk1 := class1Fibre_start_pos ctx hk
  rw [hq, hK] at hband
  have h := cnlPairResidue_25_2 hk1 hband
  refine ⟨h.1, ?_⟩
  rw [hq, hK]
  exact h.2

/-- `(q, K₀) = (25, 2)`: AT MOST ONE class-1 member per residue window — `#fibre₁ ≤ ⌈W/10⌉`. -/
theorem class1Fibre_card_le_of_datum_25_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 25) (hK : (class1SlopeDatum ctx).K₀ = 2) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card + 10 - 1) / 10 := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 10)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return cnlPairCycle_25_2.1
  have hcount : (class1Band4CycleBand ctx 10).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset cnlPairCycle_25_2.2.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 10).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 10 - 1) / 10) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 10 - 1) / 10) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)
    _ = ((supportShell ctx.shell.d ctx.shell.X).card + 10 - 1) / 10 :=
        Nat.one_mul _

/-- `(q, K₀) = (25, 2)`: any two class-1 members are congruent mod `10`, satisfy the concrete
hit-gap repeat equation, and their spacing is a full orbit period. -/
theorem class1Fibre_pair_rigidity_of_datum_25_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 25) (hK : (class1SlopeDatum ctx).K₀ = 2)
    {k k' : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hk' : k' ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hlt : k < k') :
    k % 10 = k' % 10
      ∧ ctx.n24CarryData.a (k + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k'
          = ctx.n24CarryData.a (k' + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k
      ∧ (∀ m, 1 ≤ m →
          slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + (k' - k))
            = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m) := by
  have h1 := class1Fibre_residue_of_datum_25_2 ctx hq hK hk
  have h2 := class1Fibre_residue_of_datum_25_2 ctx hq hK hk'
  exact ⟨by omega, class1Fibre_span_rigidity ctx hk hk',
    class1Fibre_spacing_period ctx hk hk' hlt (h1.2.trans h2.2.symm)⟩

/-- `(q, K₀) = (25, 2)`: a top start whose residue misses `2` mod `10` is NOT class-1
(every `r`, in particular `r = 0`). -/
theorem class1Fibre_top_notMem_of_residue_25_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 25) (hK : (class1SlopeDatum ctx).K₀ = 2)
    (hres : cnlWindowTopStart ctx % 10 ≠ 2) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 :=
  fun hk => hres (class1Fibre_residue_of_datum_25_2 ctx hq hK hk).1

/-- `(q, K₀) = (25, 2)`, `r = 0`: the top start is not class-1 OR the two explicit pins hold
(residue hit `% 10 = 2` + the single hit-gap equation). -/
theorem class1_r0_top_verdict_of_datum_25_2 (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0)
    (hq : (class1SlopeDatum ctx).q = 25) (hK : (class1SlopeDatum ctx).K₀ = 2) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
      ∨ (cnlWindowTopStart ctx % 10 = 2
          ∧ 64 * hitGap ctx.n24CarryData.a (cnlWindowTopStart ctx)
              = 129 * shellLadderDepth ctx + 64) := by
  by_cases hk : cnlWindowTopStart ctx
      ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
  · exact Or.inr ⟨(class1Fibre_residue_of_datum_25_2 ctx hq hK hk).1,
      class1Fibre_r0_hitGap_pin ctx hr hk⟩
  · exact Or.inl hk

/-- `(q, K₀) = (25, 12)`: period `10`, cycle `23 → 21 → 17 → 9 → 11 → 19 → 13 → 1 → 7 → 3`, bands `1, 1, 1, 2, 2, 1, 1, 5, 2, 4` — band-4 residue set `{10}` (values `3`), congruence class(es) `k % 10 ∈ {0}`. -/
private theorem cnlPairCycle_25_12 :
    slopeOrbit 25 12 (1 + 10) = slopeOrbit 25 12 1
      ∧ slopeOrbit 25 12 10 = 3
      ∧ ∀ j, 1 ≤ j → j ≤ 10 →
          canonGap 25 (slopeOrbit 25 12 j) = 4 → j ∈ ({10} : Finset ℕ) := by
  have e0 : slopeOrbit 25 12 0 = 12 := rfl
  have e1 : slopeOrbit 25 12 1 = 23 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 25 12 2 = 21 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 25 12 3 = 17 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 25 12 4 = 9 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 25 12 5 = 11 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 25 12 6 = 19 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 25 12 7 = 13 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 25 12 8 = 1 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 25 12 9 = 7 :=
    slopeOrbit_step_eval 8 4 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 25 12 10 = 3 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 25 12 11 = 23 :=
    slopeOrbit_step_eval 10 3 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, e10, ?_⟩
  · show slopeOrbit 25 12 11 = slopeOrbit 25 12 1
    rw [e11, e1]
  · intro j hj1 hjc hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide

private theorem cnlPairResidue_25_12 {k : ℕ} (hk1 : 1 ≤ k)
    (hband : canonGap 25 (slopeOrbit 25 12 k) = 4) :
    k % 10 = 0 ∧ slopeOrbit 25 12 k = 3 := by
  have hper := slopeOrbit_period_of_return cnlPairCycle_25_12.1
  have hres := slopeOrbit_eq_residue (by norm_num) hper hk1
  have hmod : (k - 1) % 10 < 10 := Nat.mod_lt _ (by norm_num)
  have hmem := cnlPairCycle_25_12.2.2 ((k - 1) % 10 + 1) (by omega) (by omega)
    (by rw [← hres]; exact hband)
  have hj4 := Finset.mem_singleton.mp hmem
  refine ⟨by omega, ?_⟩
  rw [hres, hj4]
  exact cnlPairCycle_25_12.2.1

/-- `(q, K₀) = (25, 12)`: every class-1 start satisfies the explicit congruence `k % 10 = 0`
and carries the unique band-4 orbit value `3`. -/
theorem class1Fibre_residue_of_datum_25_12 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 25) (hK : (class1SlopeDatum ctx).K₀ = 12)
    {k : ℕ} (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1) :
    k % 10 = 0
      ∧ slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k = 3 := by
  have hband := class1Fibre_canonGap_eq ctx hk
  have hk1 := class1Fibre_start_pos ctx hk
  rw [hq, hK] at hband
  have h := cnlPairResidue_25_12 hk1 hband
  refine ⟨h.1, ?_⟩
  rw [hq, hK]
  exact h.2

/-- `(q, K₀) = (25, 12)`: AT MOST ONE class-1 member per residue window — `#fibre₁ ≤ ⌈W/10⌉`. -/
theorem class1Fibre_card_le_of_datum_25_12 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 25) (hK : (class1SlopeDatum ctx).K₀ = 12) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card + 10 - 1) / 10 := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 10)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return cnlPairCycle_25_12.1
  have hcount : (class1Band4CycleBand ctx 10).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset cnlPairCycle_25_12.2.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 10).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 10 - 1) / 10) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 10 - 1) / 10) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)
    _ = ((supportShell ctx.shell.d ctx.shell.X).card + 10 - 1) / 10 :=
        Nat.one_mul _

/-- `(q, K₀) = (25, 12)`: any two class-1 members are congruent mod `10`, satisfy the concrete
hit-gap repeat equation, and their spacing is a full orbit period. -/
theorem class1Fibre_pair_rigidity_of_datum_25_12 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 25) (hK : (class1SlopeDatum ctx).K₀ = 12)
    {k k' : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hk' : k' ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hlt : k < k') :
    k % 10 = k' % 10
      ∧ ctx.n24CarryData.a (k + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k'
          = ctx.n24CarryData.a (k' + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k
      ∧ (∀ m, 1 ≤ m →
          slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + (k' - k))
            = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m) := by
  have h1 := class1Fibre_residue_of_datum_25_12 ctx hq hK hk
  have h2 := class1Fibre_residue_of_datum_25_12 ctx hq hK hk'
  exact ⟨by omega, class1Fibre_span_rigidity ctx hk hk',
    class1Fibre_spacing_period ctx hk hk' hlt (h1.2.trans h2.2.symm)⟩

/-- `(q, K₀) = (25, 12)`: a top start whose residue misses `0` mod `10` is NOT class-1
(every `r`, in particular `r = 0`). -/
theorem class1Fibre_top_notMem_of_residue_25_12 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 25) (hK : (class1SlopeDatum ctx).K₀ = 12)
    (hres : cnlWindowTopStart ctx % 10 ≠ 0) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 :=
  fun hk => hres (class1Fibre_residue_of_datum_25_12 ctx hq hK hk).1

/-- `(q, K₀) = (25, 12)`, `r = 0`: the top start is not class-1 OR the two explicit pins hold
(residue hit `% 10 = 0` + the single hit-gap equation). -/
theorem class1_r0_top_verdict_of_datum_25_12 (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0)
    (hq : (class1SlopeDatum ctx).q = 25) (hK : (class1SlopeDatum ctx).K₀ = 12) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
      ∨ (cnlWindowTopStart ctx % 10 = 0
          ∧ 64 * hitGap ctx.n24CarryData.a (cnlWindowTopStart ctx)
              = 129 * shellLadderDepth ctx + 64) := by
  by_cases hk : cnlWindowTopStart ctx
      ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
  · exact Or.inr ⟨(class1Fibre_residue_of_datum_25_12 ctx hq hK hk).1,
      class1Fibre_r0_hitGap_pin ctx hr hk⟩
  · exact Or.inl hk

/-- `(q, K₀) = (29, 14)`: period `14`, cycle `27 → 25 → 21 → 13 → 23 → 17 → 5 → 11 → 15 → 1 → 3 → 19 → 9 → 7`, bands `1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 4, 1, 2, 3` — band-4 residue set `{11}` (values `3`), congruence class(es) `k % 14 ∈ {11}`. -/
private theorem cnlPairCycle_29_14 :
    slopeOrbit 29 14 (1 + 14) = slopeOrbit 29 14 1
      ∧ slopeOrbit 29 14 11 = 3
      ∧ ∀ j, 1 ≤ j → j ≤ 14 →
          canonGap 29 (slopeOrbit 29 14 j) = 4 → j ∈ ({11} : Finset ℕ) := by
  have e0 : slopeOrbit 29 14 0 = 14 := rfl
  have e1 : slopeOrbit 29 14 1 = 27 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 29 14 2 = 25 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 29 14 3 = 21 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 29 14 4 = 13 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 29 14 5 = 23 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 29 14 6 = 17 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 29 14 7 = 5 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 29 14 8 = 11 :=
    slopeOrbit_step_eval 7 2 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 29 14 9 = 15 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 29 14 10 = 1 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 29 14 11 = 3 :=
    slopeOrbit_step_eval 10 4 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 29 14 12 = 19 :=
    slopeOrbit_step_eval 11 3 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 29 14 13 = 9 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 29 14 14 = 7 :=
    slopeOrbit_step_eval 13 1 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 29 14 15 = 27 :=
    slopeOrbit_step_eval 14 2 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, e11, ?_⟩
  · show slopeOrbit 29 14 15 = slopeOrbit 29 14 1
    rw [e15, e1]
  · intro j hj1 hjc hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · decide
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))

private theorem cnlPairResidue_29_14 {k : ℕ} (hk1 : 1 ≤ k)
    (hband : canonGap 29 (slopeOrbit 29 14 k) = 4) :
    k % 14 = 11 ∧ slopeOrbit 29 14 k = 3 := by
  have hper := slopeOrbit_period_of_return cnlPairCycle_29_14.1
  have hres := slopeOrbit_eq_residue (by norm_num) hper hk1
  have hmod : (k - 1) % 14 < 14 := Nat.mod_lt _ (by norm_num)
  have hmem := cnlPairCycle_29_14.2.2 ((k - 1) % 14 + 1) (by omega) (by omega)
    (by rw [← hres]; exact hband)
  have hj4 := Finset.mem_singleton.mp hmem
  refine ⟨by omega, ?_⟩
  rw [hres, hj4]
  exact cnlPairCycle_29_14.2.1

/-- `(q, K₀) = (29, 14)`: every class-1 start satisfies the explicit congruence `k % 14 = 11`
and carries the unique band-4 orbit value `3`. -/
theorem class1Fibre_residue_of_datum_29_14 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 29) (hK : (class1SlopeDatum ctx).K₀ = 14)
    {k : ℕ} (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1) :
    k % 14 = 11
      ∧ slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k = 3 := by
  have hband := class1Fibre_canonGap_eq ctx hk
  have hk1 := class1Fibre_start_pos ctx hk
  rw [hq, hK] at hband
  have h := cnlPairResidue_29_14 hk1 hband
  refine ⟨h.1, ?_⟩
  rw [hq, hK]
  exact h.2

/-- `(q, K₀) = (29, 14)`: AT MOST ONE class-1 member per residue window — `#fibre₁ ≤ ⌈W/14⌉`. -/
theorem class1Fibre_card_le_of_datum_29_14 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 29) (hK : (class1SlopeDatum ctx).K₀ = 14) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card + 14 - 1) / 14 := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 14)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return cnlPairCycle_29_14.1
  have hcount : (class1Band4CycleBand ctx 14).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset cnlPairCycle_29_14.2.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 14).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 14 - 1) / 14) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 14 - 1) / 14) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)
    _ = ((supportShell ctx.shell.d ctx.shell.X).card + 14 - 1) / 14 :=
        Nat.one_mul _

/-- `(q, K₀) = (29, 14)`: any two class-1 members are congruent mod `14`, satisfy the concrete
hit-gap repeat equation, and their spacing is a full orbit period. -/
theorem class1Fibre_pair_rigidity_of_datum_29_14 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 29) (hK : (class1SlopeDatum ctx).K₀ = 14)
    {k k' : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hk' : k' ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hlt : k < k') :
    k % 14 = k' % 14
      ∧ ctx.n24CarryData.a (k + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k'
          = ctx.n24CarryData.a (k' + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k
      ∧ (∀ m, 1 ≤ m →
          slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + (k' - k))
            = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m) := by
  have h1 := class1Fibre_residue_of_datum_29_14 ctx hq hK hk
  have h2 := class1Fibre_residue_of_datum_29_14 ctx hq hK hk'
  exact ⟨by omega, class1Fibre_span_rigidity ctx hk hk',
    class1Fibre_spacing_period ctx hk hk' hlt (h1.2.trans h2.2.symm)⟩

/-- `(q, K₀) = (29, 14)`: a top start whose residue misses `11` mod `14` is NOT class-1
(every `r`, in particular `r = 0`). -/
theorem class1Fibre_top_notMem_of_residue_29_14 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 29) (hK : (class1SlopeDatum ctx).K₀ = 14)
    (hres : cnlWindowTopStart ctx % 14 ≠ 11) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 :=
  fun hk => hres (class1Fibre_residue_of_datum_29_14 ctx hq hK hk).1

/-- `(q, K₀) = (29, 14)`, `r = 0`: the top start is not class-1 OR the two explicit pins hold
(residue hit `% 14 = 11` + the single hit-gap equation). -/
theorem class1_r0_top_verdict_of_datum_29_14 (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0)
    (hq : (class1SlopeDatum ctx).q = 29) (hK : (class1SlopeDatum ctx).K₀ = 14) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
      ∨ (cnlWindowTopStart ctx % 14 = 11
          ∧ 64 * hitGap ctx.n24CarryData.a (cnlWindowTopStart ctx)
              = 129 * shellLadderDepth ctx + 64) := by
  by_cases hk : cnlWindowTopStart ctx
      ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
  · exact Or.inr ⟨(class1Fibre_residue_of_datum_29_14 ctx hq hK hk).1,
      class1Fibre_r0_hitGap_pin ctx hr hk⟩
  · exact Or.inl hk

/-- `(q, K₀) = (35, 3)`: period `7`, cycle `13 → 17 → 33 → 31 → 27 → 19 → 3`, bands `2, 2, 1, 1, 1, 1, 4` — band-4 residue set `{7}` (values `3`), congruence class(es) `k % 7 ∈ {0}`. -/
private theorem cnlPairCycle_35_3 :
    slopeOrbit 35 3 (1 + 7) = slopeOrbit 35 3 1
      ∧ slopeOrbit 35 3 7 = 3
      ∧ ∀ j, 1 ≤ j → j ≤ 7 →
          canonGap 35 (slopeOrbit 35 3 j) = 4 → j ∈ ({7} : Finset ℕ) := by
  have e0 : slopeOrbit 35 3 0 = 3 := rfl
  have e1 : slopeOrbit 35 3 1 = 13 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 35 3 2 = 17 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 35 3 3 = 33 :=
    slopeOrbit_step_eval 2 1 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 35 3 4 = 31 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 35 3 5 = 27 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 35 3 6 = 19 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 35 3 7 = 3 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 35 3 8 = 13 :=
    slopeOrbit_step_eval 7 3 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, e7, ?_⟩
  · show slopeOrbit 35 3 8 = slopeOrbit 35 3 1
    rw [e8, e1]
  · intro j hj1 hjc hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide

private theorem cnlPairResidue_35_3 {k : ℕ} (hk1 : 1 ≤ k)
    (hband : canonGap 35 (slopeOrbit 35 3 k) = 4) :
    k % 7 = 0 ∧ slopeOrbit 35 3 k = 3 := by
  have hper := slopeOrbit_period_of_return cnlPairCycle_35_3.1
  have hres := slopeOrbit_eq_residue (by norm_num) hper hk1
  have hmod : (k - 1) % 7 < 7 := Nat.mod_lt _ (by norm_num)
  have hmem := cnlPairCycle_35_3.2.2 ((k - 1) % 7 + 1) (by omega) (by omega)
    (by rw [← hres]; exact hband)
  have hj4 := Finset.mem_singleton.mp hmem
  refine ⟨by omega, ?_⟩
  rw [hres, hj4]
  exact cnlPairCycle_35_3.2.1

/-- `(q, K₀) = (35, 3)`: every class-1 start satisfies the explicit congruence `k % 7 = 0`
and carries the unique band-4 orbit value `3`. -/
theorem class1Fibre_residue_of_datum_35_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 35) (hK : (class1SlopeDatum ctx).K₀ = 3)
    {k : ℕ} (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1) :
    k % 7 = 0
      ∧ slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k = 3 := by
  have hband := class1Fibre_canonGap_eq ctx hk
  have hk1 := class1Fibre_start_pos ctx hk
  rw [hq, hK] at hband
  have h := cnlPairResidue_35_3 hk1 hband
  refine ⟨h.1, ?_⟩
  rw [hq, hK]
  exact h.2

/-- `(q, K₀) = (35, 3)`: AT MOST ONE class-1 member per residue window — `#fibre₁ ≤ ⌈W/7⌉`. -/
theorem class1Fibre_card_le_of_datum_35_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 35) (hK : (class1SlopeDatum ctx).K₀ = 3) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card + 7 - 1) / 7 := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 7)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return cnlPairCycle_35_3.1
  have hcount : (class1Band4CycleBand ctx 7).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset cnlPairCycle_35_3.2.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 7).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 7 - 1) / 7) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 7 - 1) / 7) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)
    _ = ((supportShell ctx.shell.d ctx.shell.X).card + 7 - 1) / 7 :=
        Nat.one_mul _

/-- `(q, K₀) = (35, 3)`: any two class-1 members are congruent mod `7`, satisfy the concrete
hit-gap repeat equation, and their spacing is a full orbit period. -/
theorem class1Fibre_pair_rigidity_of_datum_35_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 35) (hK : (class1SlopeDatum ctx).K₀ = 3)
    {k k' : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hk' : k' ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hlt : k < k') :
    k % 7 = k' % 7
      ∧ ctx.n24CarryData.a (k + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k'
          = ctx.n24CarryData.a (k' + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k
      ∧ (∀ m, 1 ≤ m →
          slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + (k' - k))
            = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m) := by
  have h1 := class1Fibre_residue_of_datum_35_3 ctx hq hK hk
  have h2 := class1Fibre_residue_of_datum_35_3 ctx hq hK hk'
  exact ⟨by omega, class1Fibre_span_rigidity ctx hk hk',
    class1Fibre_spacing_period ctx hk hk' hlt (h1.2.trans h2.2.symm)⟩

/-- `(q, K₀) = (35, 3)`: a top start whose residue misses `0` mod `7` is NOT class-1
(every `r`, in particular `r = 0`). -/
theorem class1Fibre_top_notMem_of_residue_35_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 35) (hK : (class1SlopeDatum ctx).K₀ = 3)
    (hres : cnlWindowTopStart ctx % 7 ≠ 0) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 :=
  fun hk => hres (class1Fibre_residue_of_datum_35_3 ctx hq hK hk).1

/-- `(q, K₀) = (35, 3)`, `r = 0`: the top start is not class-1 OR the two explicit pins hold
(residue hit `% 7 = 0` + the single hit-gap equation). -/
theorem class1_r0_top_verdict_of_datum_35_3 (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0)
    (hq : (class1SlopeDatum ctx).q = 35) (hK : (class1SlopeDatum ctx).K₀ = 3) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
      ∨ (cnlWindowTopStart ctx % 7 = 0
          ∧ 64 * hitGap ctx.n24CarryData.a (cnlWindowTopStart ctx)
              = 129 * shellLadderDepth ctx + 64) := by
  by_cases hk : cnlWindowTopStart ctx
      ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
  · exact Or.inr ⟨(class1Fibre_residue_of_datum_35_3 ctx hq hK hk).1,
      class1Fibre_r0_hitGap_pin ctx hr hk⟩
  · exact Or.inl hk

/-- `(q, K₀) = (35, 17)`: period `7`, cycle `33 → 31 → 27 → 19 → 3 → 13 → 17`, bands `1, 1, 1, 1, 4, 2, 2` — band-4 residue set `{5}` (values `3`), congruence class(es) `k % 7 ∈ {5}`. -/
private theorem cnlPairCycle_35_17 :
    slopeOrbit 35 17 (1 + 7) = slopeOrbit 35 17 1
      ∧ slopeOrbit 35 17 5 = 3
      ∧ ∀ j, 1 ≤ j → j ≤ 7 →
          canonGap 35 (slopeOrbit 35 17 j) = 4 → j ∈ ({5} : Finset ℕ) := by
  have e0 : slopeOrbit 35 17 0 = 17 := rfl
  have e1 : slopeOrbit 35 17 1 = 33 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 35 17 2 = 31 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 35 17 3 = 27 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 35 17 4 = 19 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 35 17 5 = 3 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 35 17 6 = 13 :=
    slopeOrbit_step_eval 5 3 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 35 17 7 = 17 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 35 17 8 = 33 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, e5, ?_⟩
  · show slopeOrbit 35 17 8 = slopeOrbit 35 17 1
    rw [e8, e1]
  · intro j hj1 hjc hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))

private theorem cnlPairResidue_35_17 {k : ℕ} (hk1 : 1 ≤ k)
    (hband : canonGap 35 (slopeOrbit 35 17 k) = 4) :
    k % 7 = 5 ∧ slopeOrbit 35 17 k = 3 := by
  have hper := slopeOrbit_period_of_return cnlPairCycle_35_17.1
  have hres := slopeOrbit_eq_residue (by norm_num) hper hk1
  have hmod : (k - 1) % 7 < 7 := Nat.mod_lt _ (by norm_num)
  have hmem := cnlPairCycle_35_17.2.2 ((k - 1) % 7 + 1) (by omega) (by omega)
    (by rw [← hres]; exact hband)
  have hj4 := Finset.mem_singleton.mp hmem
  refine ⟨by omega, ?_⟩
  rw [hres, hj4]
  exact cnlPairCycle_35_17.2.1

/-- `(q, K₀) = (35, 17)`: every class-1 start satisfies the explicit congruence `k % 7 = 5`
and carries the unique band-4 orbit value `3`. -/
theorem class1Fibre_residue_of_datum_35_17 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 35) (hK : (class1SlopeDatum ctx).K₀ = 17)
    {k : ℕ} (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1) :
    k % 7 = 5
      ∧ slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k = 3 := by
  have hband := class1Fibre_canonGap_eq ctx hk
  have hk1 := class1Fibre_start_pos ctx hk
  rw [hq, hK] at hband
  have h := cnlPairResidue_35_17 hk1 hband
  refine ⟨h.1, ?_⟩
  rw [hq, hK]
  exact h.2

/-- `(q, K₀) = (35, 17)`: AT MOST ONE class-1 member per residue window — `#fibre₁ ≤ ⌈W/7⌉`. -/
theorem class1Fibre_card_le_of_datum_35_17 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 35) (hK : (class1SlopeDatum ctx).K₀ = 17) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card + 7 - 1) / 7 := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 7)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return cnlPairCycle_35_17.1
  have hcount : (class1Band4CycleBand ctx 7).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset cnlPairCycle_35_17.2.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 7).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 7 - 1) / 7) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 7 - 1) / 7) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)
    _ = ((supportShell ctx.shell.d ctx.shell.X).card + 7 - 1) / 7 :=
        Nat.one_mul _

/-- `(q, K₀) = (35, 17)`: any two class-1 members are congruent mod `7`, satisfy the concrete
hit-gap repeat equation, and their spacing is a full orbit period. -/
theorem class1Fibre_pair_rigidity_of_datum_35_17 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 35) (hK : (class1SlopeDatum ctx).K₀ = 17)
    {k k' : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hk' : k' ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hlt : k < k') :
    k % 7 = k' % 7
      ∧ ctx.n24CarryData.a (k + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k'
          = ctx.n24CarryData.a (k' + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k
      ∧ (∀ m, 1 ≤ m →
          slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + (k' - k))
            = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m) := by
  have h1 := class1Fibre_residue_of_datum_35_17 ctx hq hK hk
  have h2 := class1Fibre_residue_of_datum_35_17 ctx hq hK hk'
  exact ⟨by omega, class1Fibre_span_rigidity ctx hk hk',
    class1Fibre_spacing_period ctx hk hk' hlt (h1.2.trans h2.2.symm)⟩

/-- `(q, K₀) = (35, 17)`: a top start whose residue misses `5` mod `7` is NOT class-1
(every `r`, in particular `r = 0`). -/
theorem class1Fibre_top_notMem_of_residue_35_17 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 35) (hK : (class1SlopeDatum ctx).K₀ = 17)
    (hres : cnlWindowTopStart ctx % 7 ≠ 5) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 :=
  fun hk => hres (class1Fibre_residue_of_datum_35_17 ctx hq hK hk).1

/-- `(q, K₀) = (35, 17)`, `r = 0`: the top start is not class-1 OR the two explicit pins hold
(residue hit `% 7 = 5` + the single hit-gap equation). -/
theorem class1_r0_top_verdict_of_datum_35_17 (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0)
    (hq : (class1SlopeDatum ctx).q = 35) (hK : (class1SlopeDatum ctx).K₀ = 17) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
      ∨ (cnlWindowTopStart ctx % 7 = 5
          ∧ 64 * hitGap ctx.n24CarryData.a (cnlWindowTopStart ctx)
              = 129 * shellLadderDepth ctx + 64) := by
  by_cases hk : cnlWindowTopStart ctx
      ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
  · exact Or.inr ⟨(class1Fibre_residue_of_datum_35_17 ctx hq hK hk).1,
      class1Fibre_r0_hitGap_pin ctx hr hk⟩
  · exact Or.inl hk

/-- `(q, K₀) = (37, 18)`: period `18`, cycle `35 → 33 → 29 → 21 → 5 → 3 → 11 → 7 → 19 → 1 → 27 → 17 → 31 → 25 → 13 → 15 → 23 → 9`, bands `1, 1, 1, 1, 3, 4, 2, 3, 1, 6, 1, 2, 1, 1, 2, 2, 1, 3` — band-4 residue set `{6}` (values `3`), congruence class(es) `k % 18 ∈ {6}`. -/
private theorem cnlPairCycle_37_18 :
    slopeOrbit 37 18 (1 + 18) = slopeOrbit 37 18 1
      ∧ slopeOrbit 37 18 6 = 3
      ∧ ∀ j, 1 ≤ j → j ≤ 18 →
          canonGap 37 (slopeOrbit 37 18 j) = 4 → j ∈ ({6} : Finset ℕ) := by
  have e0 : slopeOrbit 37 18 0 = 18 := rfl
  have e1 : slopeOrbit 37 18 1 = 35 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 37 18 2 = 33 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 37 18 3 = 29 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 37 18 4 = 21 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 37 18 5 = 5 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 37 18 6 = 3 :=
    slopeOrbit_step_eval 5 2 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 37 18 7 = 11 :=
    slopeOrbit_step_eval 6 3 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 37 18 8 = 7 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 37 18 9 = 19 :=
    slopeOrbit_step_eval 8 2 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 37 18 10 = 1 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 37 18 11 = 27 :=
    slopeOrbit_step_eval 10 5 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 37 18 12 = 17 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 37 18 13 = 31 :=
    slopeOrbit_step_eval 12 1 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 37 18 14 = 25 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 37 18 15 = 13 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 37 18 16 = 15 :=
    slopeOrbit_step_eval 15 1 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 37 18 17 = 23 :=
    slopeOrbit_step_eval 16 1 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 37 18 18 = 9 :=
    slopeOrbit_step_eval 17 0 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 37 18 19 = 35 :=
    slopeOrbit_step_eval 18 2 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, e6, ?_⟩
  · show slopeOrbit 37 18 19 = slopeOrbit 37 18 1
    rw [e19, e1]
  · intro j hj1 hjc hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))

private theorem cnlPairResidue_37_18 {k : ℕ} (hk1 : 1 ≤ k)
    (hband : canonGap 37 (slopeOrbit 37 18 k) = 4) :
    k % 18 = 6 ∧ slopeOrbit 37 18 k = 3 := by
  have hper := slopeOrbit_period_of_return cnlPairCycle_37_18.1
  have hres := slopeOrbit_eq_residue (by norm_num) hper hk1
  have hmod : (k - 1) % 18 < 18 := Nat.mod_lt _ (by norm_num)
  have hmem := cnlPairCycle_37_18.2.2 ((k - 1) % 18 + 1) (by omega) (by omega)
    (by rw [← hres]; exact hband)
  have hj4 := Finset.mem_singleton.mp hmem
  refine ⟨by omega, ?_⟩
  rw [hres, hj4]
  exact cnlPairCycle_37_18.2.1

/-- `(q, K₀) = (37, 18)`: every class-1 start satisfies the explicit congruence `k % 18 = 6`
and carries the unique band-4 orbit value `3`. -/
theorem class1Fibre_residue_of_datum_37_18 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 37) (hK : (class1SlopeDatum ctx).K₀ = 18)
    {k : ℕ} (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1) :
    k % 18 = 6
      ∧ slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k = 3 := by
  have hband := class1Fibre_canonGap_eq ctx hk
  have hk1 := class1Fibre_start_pos ctx hk
  rw [hq, hK] at hband
  have h := cnlPairResidue_37_18 hk1 hband
  refine ⟨h.1, ?_⟩
  rw [hq, hK]
  exact h.2

/-- `(q, K₀) = (37, 18)`: AT MOST ONE class-1 member per residue window — `#fibre₁ ≤ ⌈W/18⌉`. -/
theorem class1Fibre_card_le_of_datum_37_18 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 37) (hK : (class1SlopeDatum ctx).K₀ = 18) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card + 18 - 1) / 18 := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 18)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return cnlPairCycle_37_18.1
  have hcount : (class1Band4CycleBand ctx 18).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset cnlPairCycle_37_18.2.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 18).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 18 - 1) / 18) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 18 - 1) / 18) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)
    _ = ((supportShell ctx.shell.d ctx.shell.X).card + 18 - 1) / 18 :=
        Nat.one_mul _

/-- `(q, K₀) = (37, 18)`: any two class-1 members are congruent mod `18`, satisfy the concrete
hit-gap repeat equation, and their spacing is a full orbit period. -/
theorem class1Fibre_pair_rigidity_of_datum_37_18 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 37) (hK : (class1SlopeDatum ctx).K₀ = 18)
    {k k' : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hk' : k' ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hlt : k < k') :
    k % 18 = k' % 18
      ∧ ctx.n24CarryData.a (k + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k'
          = ctx.n24CarryData.a (k' + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k
      ∧ (∀ m, 1 ≤ m →
          slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + (k' - k))
            = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m) := by
  have h1 := class1Fibre_residue_of_datum_37_18 ctx hq hK hk
  have h2 := class1Fibre_residue_of_datum_37_18 ctx hq hK hk'
  exact ⟨by omega, class1Fibre_span_rigidity ctx hk hk',
    class1Fibre_spacing_period ctx hk hk' hlt (h1.2.trans h2.2.symm)⟩

/-- `(q, K₀) = (37, 18)`: a top start whose residue misses `6` mod `18` is NOT class-1
(every `r`, in particular `r = 0`). -/
theorem class1Fibre_top_notMem_of_residue_37_18 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 37) (hK : (class1SlopeDatum ctx).K₀ = 18)
    (hres : cnlWindowTopStart ctx % 18 ≠ 6) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 :=
  fun hk => hres (class1Fibre_residue_of_datum_37_18 ctx hq hK hk).1

/-- `(q, K₀) = (37, 18)`, `r = 0`: the top start is not class-1 OR the two explicit pins hold
(residue hit `% 18 = 6` + the single hit-gap equation). -/
theorem class1_r0_top_verdict_of_datum_37_18 (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0)
    (hq : (class1SlopeDatum ctx).q = 37) (hK : (class1SlopeDatum ctx).K₀ = 18) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
      ∨ (cnlWindowTopStart ctx % 18 = 6
          ∧ 64 * hitGap ctx.n24CarryData.a (cnlWindowTopStart ctx)
              = 129 * shellLadderDepth ctx + 64) := by
  by_cases hk : cnlWindowTopStart ctx
      ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
  · exact Or.inr ⟨(class1Fibre_residue_of_datum_37_18 ctx hq hK hk).1,
      class1Fibre_r0_hitGap_pin ctx hr hk⟩
  · exact Or.inl hk

/-- `(q, K₀) = (39, 6)`: period `6`, cycle `9 → 33 → 27 → 15 → 21 → 3`, bands `3, 1, 1, 2, 1, 4` — band-4 residue set `{6}` (values `3`), congruence class(es) `k % 6 ∈ {0}`. -/
private theorem cnlPairCycle_39_6 :
    slopeOrbit 39 6 (1 + 6) = slopeOrbit 39 6 1
      ∧ slopeOrbit 39 6 6 = 3
      ∧ ∀ j, 1 ≤ j → j ≤ 6 →
          canonGap 39 (slopeOrbit 39 6 j) = 4 → j ∈ ({6} : Finset ℕ) := by
  have e0 : slopeOrbit 39 6 0 = 6 := rfl
  have e1 : slopeOrbit 39 6 1 = 9 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 39 6 2 = 33 :=
    slopeOrbit_step_eval 1 2 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 39 6 3 = 27 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 39 6 4 = 15 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 39 6 5 = 21 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 39 6 6 = 3 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 39 6 7 = 9 :=
    slopeOrbit_step_eval 6 3 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, e6, ?_⟩
  · show slopeOrbit 39 6 7 = slopeOrbit 39 6 1
    rw [e7, e1]
  · intro j hj1 hjc hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide

private theorem cnlPairResidue_39_6 {k : ℕ} (hk1 : 1 ≤ k)
    (hband : canonGap 39 (slopeOrbit 39 6 k) = 4) :
    k % 6 = 0 ∧ slopeOrbit 39 6 k = 3 := by
  have hper := slopeOrbit_period_of_return cnlPairCycle_39_6.1
  have hres := slopeOrbit_eq_residue (by norm_num) hper hk1
  have hmod : (k - 1) % 6 < 6 := Nat.mod_lt _ (by norm_num)
  have hmem := cnlPairCycle_39_6.2.2 ((k - 1) % 6 + 1) (by omega) (by omega)
    (by rw [← hres]; exact hband)
  have hj4 := Finset.mem_singleton.mp hmem
  refine ⟨by omega, ?_⟩
  rw [hres, hj4]
  exact cnlPairCycle_39_6.2.1

/-- `(q, K₀) = (39, 6)`: every class-1 start satisfies the explicit congruence `k % 6 = 0`
and carries the unique band-4 orbit value `3`. -/
theorem class1Fibre_residue_of_datum_39_6 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 39) (hK : (class1SlopeDatum ctx).K₀ = 6)
    {k : ℕ} (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1) :
    k % 6 = 0
      ∧ slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k = 3 := by
  have hband := class1Fibre_canonGap_eq ctx hk
  have hk1 := class1Fibre_start_pos ctx hk
  rw [hq, hK] at hband
  have h := cnlPairResidue_39_6 hk1 hband
  refine ⟨h.1, ?_⟩
  rw [hq, hK]
  exact h.2

/-- `(q, K₀) = (39, 6)`: AT MOST ONE class-1 member per residue window — `#fibre₁ ≤ ⌈W/6⌉`. -/
theorem class1Fibre_card_le_of_datum_39_6 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 39) (hK : (class1SlopeDatum ctx).K₀ = 6) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card + 6 - 1) / 6 := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 6)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return cnlPairCycle_39_6.1
  have hcount : (class1Band4CycleBand ctx 6).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset cnlPairCycle_39_6.2.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 6).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 6 - 1) / 6) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 6 - 1) / 6) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)
    _ = ((supportShell ctx.shell.d ctx.shell.X).card + 6 - 1) / 6 :=
        Nat.one_mul _

/-- `(q, K₀) = (39, 6)`: any two class-1 members are congruent mod `6`, satisfy the concrete
hit-gap repeat equation, and their spacing is a full orbit period. -/
theorem class1Fibre_pair_rigidity_of_datum_39_6 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 39) (hK : (class1SlopeDatum ctx).K₀ = 6)
    {k k' : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hk' : k' ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hlt : k < k') :
    k % 6 = k' % 6
      ∧ ctx.n24CarryData.a (k + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k'
          = ctx.n24CarryData.a (k' + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k
      ∧ (∀ m, 1 ≤ m →
          slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + (k' - k))
            = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m) := by
  have h1 := class1Fibre_residue_of_datum_39_6 ctx hq hK hk
  have h2 := class1Fibre_residue_of_datum_39_6 ctx hq hK hk'
  exact ⟨by omega, class1Fibre_span_rigidity ctx hk hk',
    class1Fibre_spacing_period ctx hk hk' hlt (h1.2.trans h2.2.symm)⟩

/-- `(q, K₀) = (39, 6)`: a top start whose residue misses `0` mod `6` is NOT class-1
(every `r`, in particular `r = 0`). -/
theorem class1Fibre_top_notMem_of_residue_39_6 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 39) (hK : (class1SlopeDatum ctx).K₀ = 6)
    (hres : cnlWindowTopStart ctx % 6 ≠ 0) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 :=
  fun hk => hres (class1Fibre_residue_of_datum_39_6 ctx hq hK hk).1

/-- `(q, K₀) = (39, 6)`, `r = 0`: the top start is not class-1 OR the two explicit pins hold
(residue hit `% 6 = 0` + the single hit-gap equation). -/
theorem class1_r0_top_verdict_of_datum_39_6 (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0)
    (hq : (class1SlopeDatum ctx).q = 39) (hK : (class1SlopeDatum ctx).K₀ = 6) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
      ∨ (cnlWindowTopStart ctx % 6 = 0
          ∧ 64 * hitGap ctx.n24CarryData.a (cnlWindowTopStart ctx)
              = 129 * shellLadderDepth ctx + 64) := by
  by_cases hk : cnlWindowTopStart ctx
      ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
  · exact Or.inr ⟨(class1Fibre_residue_of_datum_39_6 ctx hq hK hk).1,
      class1Fibre_r0_hitGap_pin ctx hr hk⟩
  · exact Or.inl hk

/-- `(q, K₀) = (41, 20)`: period `10`, cycle `39 → 37 → 33 → 25 → 9 → 31 → 21 → 1 → 23 → 5`, bands `1, 1, 1, 1, 3, 1, 1, 6, 1, 4` — band-4 residue set `{10}` (values `5`), congruence class(es) `k % 10 ∈ {0}`. -/
private theorem cnlPairCycle_41_20 :
    slopeOrbit 41 20 (1 + 10) = slopeOrbit 41 20 1
      ∧ slopeOrbit 41 20 10 = 5
      ∧ ∀ j, 1 ≤ j → j ≤ 10 →
          canonGap 41 (slopeOrbit 41 20 j) = 4 → j ∈ ({10} : Finset ℕ) := by
  have e0 : slopeOrbit 41 20 0 = 20 := rfl
  have e1 : slopeOrbit 41 20 1 = 39 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 41 20 2 = 37 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 41 20 3 = 33 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 41 20 4 = 25 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 41 20 5 = 9 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 41 20 6 = 31 :=
    slopeOrbit_step_eval 5 2 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 41 20 7 = 21 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 41 20 8 = 1 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 41 20 9 = 23 :=
    slopeOrbit_step_eval 8 5 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 41 20 10 = 5 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 41 20 11 = 39 :=
    slopeOrbit_step_eval 10 3 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, e10, ?_⟩
  · show slopeOrbit 41 20 11 = slopeOrbit 41 20 1
    rw [e11, e1]
  · intro j hj1 hjc hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide

private theorem cnlPairResidue_41_20 {k : ℕ} (hk1 : 1 ≤ k)
    (hband : canonGap 41 (slopeOrbit 41 20 k) = 4) :
    k % 10 = 0 ∧ slopeOrbit 41 20 k = 5 := by
  have hper := slopeOrbit_period_of_return cnlPairCycle_41_20.1
  have hres := slopeOrbit_eq_residue (by norm_num) hper hk1
  have hmod : (k - 1) % 10 < 10 := Nat.mod_lt _ (by norm_num)
  have hmem := cnlPairCycle_41_20.2.2 ((k - 1) % 10 + 1) (by omega) (by omega)
    (by rw [← hres]; exact hband)
  have hj4 := Finset.mem_singleton.mp hmem
  refine ⟨by omega, ?_⟩
  rw [hres, hj4]
  exact cnlPairCycle_41_20.2.1

/-- `(q, K₀) = (41, 20)`: every class-1 start satisfies the explicit congruence `k % 10 = 0`
and carries the unique band-4 orbit value `5`. -/
theorem class1Fibre_residue_of_datum_41_20 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 41) (hK : (class1SlopeDatum ctx).K₀ = 20)
    {k : ℕ} (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1) :
    k % 10 = 0
      ∧ slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k = 5 := by
  have hband := class1Fibre_canonGap_eq ctx hk
  have hk1 := class1Fibre_start_pos ctx hk
  rw [hq, hK] at hband
  have h := cnlPairResidue_41_20 hk1 hband
  refine ⟨h.1, ?_⟩
  rw [hq, hK]
  exact h.2

/-- `(q, K₀) = (41, 20)`: AT MOST ONE class-1 member per residue window — `#fibre₁ ≤ ⌈W/10⌉`. -/
theorem class1Fibre_card_le_of_datum_41_20 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 41) (hK : (class1SlopeDatum ctx).K₀ = 20) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card + 10 - 1) / 10 := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 10)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return cnlPairCycle_41_20.1
  have hcount : (class1Band4CycleBand ctx 10).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset cnlPairCycle_41_20.2.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 10).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 10 - 1) / 10) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 10 - 1) / 10) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)
    _ = ((supportShell ctx.shell.d ctx.shell.X).card + 10 - 1) / 10 :=
        Nat.one_mul _

/-- `(q, K₀) = (41, 20)`: any two class-1 members are congruent mod `10`, satisfy the concrete
hit-gap repeat equation, and their spacing is a full orbit period. -/
theorem class1Fibre_pair_rigidity_of_datum_41_20 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 41) (hK : (class1SlopeDatum ctx).K₀ = 20)
    {k k' : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hk' : k' ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hlt : k < k') :
    k % 10 = k' % 10
      ∧ ctx.n24CarryData.a (k + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k'
          = ctx.n24CarryData.a (k' + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k
      ∧ (∀ m, 1 ≤ m →
          slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + (k' - k))
            = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m) := by
  have h1 := class1Fibre_residue_of_datum_41_20 ctx hq hK hk
  have h2 := class1Fibre_residue_of_datum_41_20 ctx hq hK hk'
  exact ⟨by omega, class1Fibre_span_rigidity ctx hk hk',
    class1Fibre_spacing_period ctx hk hk' hlt (h1.2.trans h2.2.symm)⟩

/-- `(q, K₀) = (41, 20)`: a top start whose residue misses `0` mod `10` is NOT class-1
(every `r`, in particular `r = 0`). -/
theorem class1Fibre_top_notMem_of_residue_41_20 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 41) (hK : (class1SlopeDatum ctx).K₀ = 20)
    (hres : cnlWindowTopStart ctx % 10 ≠ 0) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 :=
  fun hk => hres (class1Fibre_residue_of_datum_41_20 ctx hq hK hk).1

/-- `(q, K₀) = (41, 20)`, `r = 0`: the top start is not class-1 OR the two explicit pins hold
(residue hit `% 10 = 0` + the single hit-gap equation). -/
theorem class1_r0_top_verdict_of_datum_41_20 (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0)
    (hq : (class1SlopeDatum ctx).q = 41) (hK : (class1SlopeDatum ctx).K₀ = 20) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
      ∨ (cnlWindowTopStart ctx % 10 = 0
          ∧ 64 * hitGap ctx.n24CarryData.a (cnlWindowTopStart ctx)
              = 129 * shellLadderDepth ctx + 64) := by
  by_cases hk : cnlWindowTopStart ctx
      ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
  · exact Or.inr ⟨(class1Fibre_residue_of_datum_41_20 ctx hq hK hk).1,
      class1Fibre_r0_hitGap_pin ctx hr hk⟩
  · exact Or.inl hk

/-- `(q, K₀) = (47, 23)`: period `14`, cycle `45 → 43 → 39 → 31 → 15 → 13 → 5 → 33 → 19 → 29 → 11 → 41 → 35 → 23`, bands `1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 1, 2` — band-4 residue set `{7}` (values `5`), congruence class(es) `k % 14 ∈ {7}`. -/
private theorem cnlPairCycle_47_23 :
    slopeOrbit 47 23 (1 + 14) = slopeOrbit 47 23 1
      ∧ slopeOrbit 47 23 7 = 5
      ∧ ∀ j, 1 ≤ j → j ≤ 14 →
          canonGap 47 (slopeOrbit 47 23 j) = 4 → j ∈ ({7} : Finset ℕ) := by
  have e0 : slopeOrbit 47 23 0 = 23 := rfl
  have e1 : slopeOrbit 47 23 1 = 45 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 47 23 2 = 43 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 47 23 3 = 39 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 47 23 4 = 31 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 47 23 5 = 15 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 47 23 6 = 13 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 47 23 7 = 5 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 47 23 8 = 33 :=
    slopeOrbit_step_eval 7 3 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 47 23 9 = 19 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 47 23 10 = 29 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 47 23 11 = 11 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 47 23 12 = 41 :=
    slopeOrbit_step_eval 11 2 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 47 23 13 = 35 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 47 23 14 = 23 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 47 23 15 = 45 :=
    slopeOrbit_step_eval 14 1 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, e7, ?_⟩
  · show slopeOrbit 47 23 15 = slopeOrbit 47 23 1
    rw [e15, e1]
  · intro j hj1 hjc hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))

private theorem cnlPairResidue_47_23 {k : ℕ} (hk1 : 1 ≤ k)
    (hband : canonGap 47 (slopeOrbit 47 23 k) = 4) :
    k % 14 = 7 ∧ slopeOrbit 47 23 k = 5 := by
  have hper := slopeOrbit_period_of_return cnlPairCycle_47_23.1
  have hres := slopeOrbit_eq_residue (by norm_num) hper hk1
  have hmod : (k - 1) % 14 < 14 := Nat.mod_lt _ (by norm_num)
  have hmem := cnlPairCycle_47_23.2.2 ((k - 1) % 14 + 1) (by omega) (by omega)
    (by rw [← hres]; exact hband)
  have hj4 := Finset.mem_singleton.mp hmem
  refine ⟨by omega, ?_⟩
  rw [hres, hj4]
  exact cnlPairCycle_47_23.2.1

/-- `(q, K₀) = (47, 23)`: every class-1 start satisfies the explicit congruence `k % 14 = 7`
and carries the unique band-4 orbit value `5`. -/
theorem class1Fibre_residue_of_datum_47_23 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 47) (hK : (class1SlopeDatum ctx).K₀ = 23)
    {k : ℕ} (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1) :
    k % 14 = 7
      ∧ slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k = 5 := by
  have hband := class1Fibre_canonGap_eq ctx hk
  have hk1 := class1Fibre_start_pos ctx hk
  rw [hq, hK] at hband
  have h := cnlPairResidue_47_23 hk1 hband
  refine ⟨h.1, ?_⟩
  rw [hq, hK]
  exact h.2

/-- `(q, K₀) = (47, 23)`: AT MOST ONE class-1 member per residue window — `#fibre₁ ≤ ⌈W/14⌉`. -/
theorem class1Fibre_card_le_of_datum_47_23 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 47) (hK : (class1SlopeDatum ctx).K₀ = 23) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card + 14 - 1) / 14 := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 14)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return cnlPairCycle_47_23.1
  have hcount : (class1Band4CycleBand ctx 14).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset cnlPairCycle_47_23.2.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 14).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 14 - 1) / 14) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 14 - 1) / 14) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)
    _ = ((supportShell ctx.shell.d ctx.shell.X).card + 14 - 1) / 14 :=
        Nat.one_mul _

/-- `(q, K₀) = (47, 23)`: any two class-1 members are congruent mod `14`, satisfy the concrete
hit-gap repeat equation, and their spacing is a full orbit period. -/
theorem class1Fibre_pair_rigidity_of_datum_47_23 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 47) (hK : (class1SlopeDatum ctx).K₀ = 23)
    {k k' : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hk' : k' ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hlt : k < k') :
    k % 14 = k' % 14
      ∧ ctx.n24CarryData.a (k + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k'
          = ctx.n24CarryData.a (k' + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k
      ∧ (∀ m, 1 ≤ m →
          slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + (k' - k))
            = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m) := by
  have h1 := class1Fibre_residue_of_datum_47_23 ctx hq hK hk
  have h2 := class1Fibre_residue_of_datum_47_23 ctx hq hK hk'
  exact ⟨by omega, class1Fibre_span_rigidity ctx hk hk',
    class1Fibre_spacing_period ctx hk hk' hlt (h1.2.trans h2.2.symm)⟩

/-- `(q, K₀) = (47, 23)`: a top start whose residue misses `7` mod `14` is NOT class-1
(every `r`, in particular `r = 0`). -/
theorem class1Fibre_top_notMem_of_residue_47_23 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 47) (hK : (class1SlopeDatum ctx).K₀ = 23)
    (hres : cnlWindowTopStart ctx % 14 ≠ 7) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 :=
  fun hk => hres (class1Fibre_residue_of_datum_47_23 ctx hq hK hk).1

/-- `(q, K₀) = (47, 23)`, `r = 0`: the top start is not class-1 OR the two explicit pins hold
(residue hit `% 14 = 7` + the single hit-gap equation). -/
theorem class1_r0_top_verdict_of_datum_47_23 (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0)
    (hq : (class1SlopeDatum ctx).q = 47) (hK : (class1SlopeDatum ctx).K₀ = 23) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
      ∨ (cnlWindowTopStart ctx % 14 = 7
          ∧ 64 * hitGap ctx.n24CarryData.a (cnlWindowTopStart ctx)
              = 129 * shellLadderDepth ctx + 64) := by
  by_cases hk : cnlWindowTopStart ctx
      ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
  · exact Or.inr ⟨(class1Fibre_residue_of_datum_47_23 ctx hq hK hk).1,
      class1Fibre_r0_hitGap_pin ctx hr hk⟩
  · exact Or.inl hk

/-- `(q, K₀) = (49, 3)`: period `11`, cycle `47 → 45 → 41 → 33 → 17 → 19 → 27 → 5 → 31 → 13 → 3`, bands `1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 5` — band-4 residue set `{8}` (values `5`), congruence class(es) `k % 11 ∈ {8}`. -/
private theorem cnlPairCycle_49_3 :
    slopeOrbit 49 3 (1 + 11) = slopeOrbit 49 3 1
      ∧ slopeOrbit 49 3 8 = 5
      ∧ ∀ j, 1 ≤ j → j ≤ 11 →
          canonGap 49 (slopeOrbit 49 3 j) = 4 → j ∈ ({8} : Finset ℕ) := by
  have e0 : slopeOrbit 49 3 0 = 3 := rfl
  have e1 : slopeOrbit 49 3 1 = 47 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 49 3 2 = 45 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 49 3 3 = 41 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 49 3 4 = 33 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 49 3 5 = 17 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 49 3 6 = 19 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 49 3 7 = 27 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 49 3 8 = 5 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 49 3 9 = 31 :=
    slopeOrbit_step_eval 8 3 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 49 3 10 = 13 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 49 3 11 = 3 :=
    slopeOrbit_step_eval 10 1 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 49 3 12 = 47 :=
    slopeOrbit_step_eval 11 4 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, e8, ?_⟩
  · show slopeOrbit 49 3 12 = slopeOrbit 49 3 1
    rw [e12, e1]
  · intro j hj1 hjc hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

private theorem cnlPairResidue_49_3 {k : ℕ} (hk1 : 1 ≤ k)
    (hband : canonGap 49 (slopeOrbit 49 3 k) = 4) :
    k % 11 = 8 ∧ slopeOrbit 49 3 k = 5 := by
  have hper := slopeOrbit_period_of_return cnlPairCycle_49_3.1
  have hres := slopeOrbit_eq_residue (by norm_num) hper hk1
  have hmod : (k - 1) % 11 < 11 := Nat.mod_lt _ (by norm_num)
  have hmem := cnlPairCycle_49_3.2.2 ((k - 1) % 11 + 1) (by omega) (by omega)
    (by rw [← hres]; exact hband)
  have hj4 := Finset.mem_singleton.mp hmem
  refine ⟨by omega, ?_⟩
  rw [hres, hj4]
  exact cnlPairCycle_49_3.2.1

/-- `(q, K₀) = (49, 3)`: every class-1 start satisfies the explicit congruence `k % 11 = 8`
and carries the unique band-4 orbit value `5`. -/
theorem class1Fibre_residue_of_datum_49_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 49) (hK : (class1SlopeDatum ctx).K₀ = 3)
    {k : ℕ} (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1) :
    k % 11 = 8
      ∧ slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k = 5 := by
  have hband := class1Fibre_canonGap_eq ctx hk
  have hk1 := class1Fibre_start_pos ctx hk
  rw [hq, hK] at hband
  have h := cnlPairResidue_49_3 hk1 hband
  refine ⟨h.1, ?_⟩
  rw [hq, hK]
  exact h.2

/-- `(q, K₀) = (49, 3)`: AT MOST ONE class-1 member per residue window — `#fibre₁ ≤ ⌈W/11⌉`. -/
theorem class1Fibre_card_le_of_datum_49_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 49) (hK : (class1SlopeDatum ctx).K₀ = 3) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card + 11 - 1) / 11 := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 11)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return cnlPairCycle_49_3.1
  have hcount : (class1Band4CycleBand ctx 11).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset cnlPairCycle_49_3.2.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 11).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 11 - 1) / 11) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 11 - 1) / 11) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)
    _ = ((supportShell ctx.shell.d ctx.shell.X).card + 11 - 1) / 11 :=
        Nat.one_mul _

/-- `(q, K₀) = (49, 3)`: any two class-1 members are congruent mod `11`, satisfy the concrete
hit-gap repeat equation, and their spacing is a full orbit period. -/
theorem class1Fibre_pair_rigidity_of_datum_49_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 49) (hK : (class1SlopeDatum ctx).K₀ = 3)
    {k k' : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hk' : k' ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hlt : k < k') :
    k % 11 = k' % 11
      ∧ ctx.n24CarryData.a (k + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k'
          = ctx.n24CarryData.a (k' + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k
      ∧ (∀ m, 1 ≤ m →
          slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + (k' - k))
            = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m) := by
  have h1 := class1Fibre_residue_of_datum_49_3 ctx hq hK hk
  have h2 := class1Fibre_residue_of_datum_49_3 ctx hq hK hk'
  exact ⟨by omega, class1Fibre_span_rigidity ctx hk hk',
    class1Fibre_spacing_period ctx hk hk' hlt (h1.2.trans h2.2.symm)⟩

/-- `(q, K₀) = (49, 3)`: a top start whose residue misses `8` mod `11` is NOT class-1
(every `r`, in particular `r = 0`). -/
theorem class1Fibre_top_notMem_of_residue_49_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 49) (hK : (class1SlopeDatum ctx).K₀ = 3)
    (hres : cnlWindowTopStart ctx % 11 ≠ 8) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 :=
  fun hk => hres (class1Fibre_residue_of_datum_49_3 ctx hq hK hk).1

/-- `(q, K₀) = (49, 3)`, `r = 0`: the top start is not class-1 OR the two explicit pins hold
(residue hit `% 11 = 8` + the single hit-gap equation). -/
theorem class1_r0_top_verdict_of_datum_49_3 (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0)
    (hq : (class1SlopeDatum ctx).q = 49) (hK : (class1SlopeDatum ctx).K₀ = 3) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
      ∨ (cnlWindowTopStart ctx % 11 = 8
          ∧ 64 * hitGap ctx.n24CarryData.a (cnlWindowTopStart ctx)
              = 129 * shellLadderDepth ctx + 64) := by
  by_cases hk : cnlWindowTopStart ctx
      ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
  · exact Or.inr ⟨(class1Fibre_residue_of_datum_49_3 ctx hq hK hk).1,
      class1Fibre_r0_hitGap_pin ctx hr hk⟩
  · exact Or.inl hk

/-- `(q, K₀) = (49, 24)`: period `11`, cycle `47 → 45 → 41 → 33 → 17 → 19 → 27 → 5 → 31 → 13 → 3`, bands `1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 5` — band-4 residue set `{8}` (values `5`), congruence class(es) `k % 11 ∈ {8}`. -/
private theorem cnlPairCycle_49_24 :
    slopeOrbit 49 24 (1 + 11) = slopeOrbit 49 24 1
      ∧ slopeOrbit 49 24 8 = 5
      ∧ ∀ j, 1 ≤ j → j ≤ 11 →
          canonGap 49 (slopeOrbit 49 24 j) = 4 → j ∈ ({8} : Finset ℕ) := by
  have e0 : slopeOrbit 49 24 0 = 24 := rfl
  have e1 : slopeOrbit 49 24 1 = 47 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 49 24 2 = 45 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 49 24 3 = 41 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 49 24 4 = 33 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 49 24 5 = 17 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 49 24 6 = 19 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 49 24 7 = 27 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 49 24 8 = 5 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 49 24 9 = 31 :=
    slopeOrbit_step_eval 8 3 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 49 24 10 = 13 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 49 24 11 = 3 :=
    slopeOrbit_step_eval 10 1 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 49 24 12 = 47 :=
    slopeOrbit_step_eval 11 4 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, e8, ?_⟩
  · show slopeOrbit 49 24 12 = slopeOrbit 49 24 1
    rw [e12, e1]
  · intro j hj1 hjc hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

private theorem cnlPairResidue_49_24 {k : ℕ} (hk1 : 1 ≤ k)
    (hband : canonGap 49 (slopeOrbit 49 24 k) = 4) :
    k % 11 = 8 ∧ slopeOrbit 49 24 k = 5 := by
  have hper := slopeOrbit_period_of_return cnlPairCycle_49_24.1
  have hres := slopeOrbit_eq_residue (by norm_num) hper hk1
  have hmod : (k - 1) % 11 < 11 := Nat.mod_lt _ (by norm_num)
  have hmem := cnlPairCycle_49_24.2.2 ((k - 1) % 11 + 1) (by omega) (by omega)
    (by rw [← hres]; exact hband)
  have hj4 := Finset.mem_singleton.mp hmem
  refine ⟨by omega, ?_⟩
  rw [hres, hj4]
  exact cnlPairCycle_49_24.2.1

/-- `(q, K₀) = (49, 24)`: every class-1 start satisfies the explicit congruence `k % 11 = 8`
and carries the unique band-4 orbit value `5`. -/
theorem class1Fibre_residue_of_datum_49_24 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 49) (hK : (class1SlopeDatum ctx).K₀ = 24)
    {k : ℕ} (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1) :
    k % 11 = 8
      ∧ slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k = 5 := by
  have hband := class1Fibre_canonGap_eq ctx hk
  have hk1 := class1Fibre_start_pos ctx hk
  rw [hq, hK] at hband
  have h := cnlPairResidue_49_24 hk1 hband
  refine ⟨h.1, ?_⟩
  rw [hq, hK]
  exact h.2

/-- `(q, K₀) = (49, 24)`: AT MOST ONE class-1 member per residue window — `#fibre₁ ≤ ⌈W/11⌉`. -/
theorem class1Fibre_card_le_of_datum_49_24 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 49) (hK : (class1SlopeDatum ctx).K₀ = 24) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card + 11 - 1) / 11 := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 11)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return cnlPairCycle_49_24.1
  have hcount : (class1Band4CycleBand ctx 11).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset cnlPairCycle_49_24.2.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 11).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 11 - 1) / 11) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 11 - 1) / 11) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)
    _ = ((supportShell ctx.shell.d ctx.shell.X).card + 11 - 1) / 11 :=
        Nat.one_mul _

/-- `(q, K₀) = (49, 24)`: any two class-1 members are congruent mod `11`, satisfy the concrete
hit-gap repeat equation, and their spacing is a full orbit period. -/
theorem class1Fibre_pair_rigidity_of_datum_49_24 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 49) (hK : (class1SlopeDatum ctx).K₀ = 24)
    {k k' : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hk' : k' ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hlt : k < k') :
    k % 11 = k' % 11
      ∧ ctx.n24CarryData.a (k + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k'
          = ctx.n24CarryData.a (k' + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k
      ∧ (∀ m, 1 ≤ m →
          slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + (k' - k))
            = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m) := by
  have h1 := class1Fibre_residue_of_datum_49_24 ctx hq hK hk
  have h2 := class1Fibre_residue_of_datum_49_24 ctx hq hK hk'
  exact ⟨by omega, class1Fibre_span_rigidity ctx hk hk',
    class1Fibre_spacing_period ctx hk hk' hlt (h1.2.trans h2.2.symm)⟩

/-- `(q, K₀) = (49, 24)`: a top start whose residue misses `8` mod `11` is NOT class-1
(every `r`, in particular `r = 0`). -/
theorem class1Fibre_top_notMem_of_residue_49_24 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 49) (hK : (class1SlopeDatum ctx).K₀ = 24)
    (hres : cnlWindowTopStart ctx % 11 ≠ 8) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 :=
  fun hk => hres (class1Fibre_residue_of_datum_49_24 ctx hq hK hk).1

/-- `(q, K₀) = (49, 24)`, `r = 0`: the top start is not class-1 OR the two explicit pins hold
(residue hit `% 11 = 8` + the single hit-gap equation). -/
theorem class1_r0_top_verdict_of_datum_49_24 (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0)
    (hq : (class1SlopeDatum ctx).q = 49) (hK : (class1SlopeDatum ctx).K₀ = 24) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
      ∨ (cnlWindowTopStart ctx % 11 = 8
          ∧ 64 * hitGap ctx.n24CarryData.a (cnlWindowTopStart ctx)
              = 129 * shellLadderDepth ctx + 64) := by
  by_cases hk : cnlWindowTopStart ctx
      ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
  · exact Or.inr ⟨(class1Fibre_residue_of_datum_49_24 ctx hq hK hk).1,
      class1Fibre_r0_hitGap_pin ctx hr hk⟩
  · exact Or.inl hk

/-- `(q, K₀) = (55, 5)`: period `5`, cycle `25 → 45 → 35 → 15 → 5`, bands `2, 1, 1, 2, 4` — band-4 residue set `{5}` (values `5`), congruence class(es) `k % 5 ∈ {0}`. -/
private theorem cnlPairCycle_55_5 :
    slopeOrbit 55 5 (1 + 5) = slopeOrbit 55 5 1
      ∧ slopeOrbit 55 5 5 = 5
      ∧ ∀ j, 1 ≤ j → j ≤ 5 →
          canonGap 55 (slopeOrbit 55 5 j) = 4 → j ∈ ({5} : Finset ℕ) := by
  have e0 : slopeOrbit 55 5 0 = 5 := rfl
  have e1 : slopeOrbit 55 5 1 = 25 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 55 5 2 = 45 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 55 5 3 = 35 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 55 5 4 = 15 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 55 5 5 = 5 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 55 5 6 = 25 :=
    slopeOrbit_step_eval 5 3 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, e5, ?_⟩
  · show slopeOrbit 55 5 6 = slopeOrbit 55 5 1
    rw [e6, e1]
  · intro j hj1 hjc hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide

private theorem cnlPairResidue_55_5 {k : ℕ} (hk1 : 1 ≤ k)
    (hband : canonGap 55 (slopeOrbit 55 5 k) = 4) :
    k % 5 = 0 ∧ slopeOrbit 55 5 k = 5 := by
  have hper := slopeOrbit_period_of_return cnlPairCycle_55_5.1
  have hres := slopeOrbit_eq_residue (by norm_num) hper hk1
  have hmod : (k - 1) % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have hmem := cnlPairCycle_55_5.2.2 ((k - 1) % 5 + 1) (by omega) (by omega)
    (by rw [← hres]; exact hband)
  have hj4 := Finset.mem_singleton.mp hmem
  refine ⟨by omega, ?_⟩
  rw [hres, hj4]
  exact cnlPairCycle_55_5.2.1

/-- `(q, K₀) = (55, 5)`: every class-1 start satisfies the explicit congruence `k % 5 = 0`
and carries the unique band-4 orbit value `5`. -/
theorem class1Fibre_residue_of_datum_55_5 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 55) (hK : (class1SlopeDatum ctx).K₀ = 5)
    {k : ℕ} (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1) :
    k % 5 = 0
      ∧ slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k = 5 := by
  have hband := class1Fibre_canonGap_eq ctx hk
  have hk1 := class1Fibre_start_pos ctx hk
  rw [hq, hK] at hband
  have h := cnlPairResidue_55_5 hk1 hband
  refine ⟨h.1, ?_⟩
  rw [hq, hK]
  exact h.2

/-- `(q, K₀) = (55, 5)`: AT MOST ONE class-1 member per residue window — `#fibre₁ ≤ ⌈W/5⌉`. -/
theorem class1Fibre_card_le_of_datum_55_5 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 55) (hK : (class1SlopeDatum ctx).K₀ = 5) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card + 5 - 1) / 5 := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 5)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return cnlPairCycle_55_5.1
  have hcount : (class1Band4CycleBand ctx 5).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset cnlPairCycle_55_5.2.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 5).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 5 - 1) / 5) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 5 - 1) / 5) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)
    _ = ((supportShell ctx.shell.d ctx.shell.X).card + 5 - 1) / 5 :=
        Nat.one_mul _

/-- `(q, K₀) = (55, 5)`: any two class-1 members are congruent mod `5`, satisfy the concrete
hit-gap repeat equation, and their spacing is a full orbit period. -/
theorem class1Fibre_pair_rigidity_of_datum_55_5 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 55) (hK : (class1SlopeDatum ctx).K₀ = 5)
    {k k' : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hk' : k' ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hlt : k < k') :
    k % 5 = k' % 5
      ∧ ctx.n24CarryData.a (k + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k'
          = ctx.n24CarryData.a (k' + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k
      ∧ (∀ m, 1 ≤ m →
          slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + (k' - k))
            = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m) := by
  have h1 := class1Fibre_residue_of_datum_55_5 ctx hq hK hk
  have h2 := class1Fibre_residue_of_datum_55_5 ctx hq hK hk'
  exact ⟨by omega, class1Fibre_span_rigidity ctx hk hk',
    class1Fibre_spacing_period ctx hk hk' hlt (h1.2.trans h2.2.symm)⟩

/-- `(q, K₀) = (55, 5)`: a top start whose residue misses `0` mod `5` is NOT class-1
(every `r`, in particular `r = 0`). -/
theorem class1Fibre_top_notMem_of_residue_55_5 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 55) (hK : (class1SlopeDatum ctx).K₀ = 5)
    (hres : cnlWindowTopStart ctx % 5 ≠ 0) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 :=
  fun hk => hres (class1Fibre_residue_of_datum_55_5 ctx hq hK hk).1

/-- `(q, K₀) = (55, 5)`, `r = 0`: the top start is not class-1 OR the two explicit pins hold
(residue hit `% 5 = 0` + the single hit-gap equation). -/
theorem class1_r0_top_verdict_of_datum_55_5 (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0)
    (hq : (class1SlopeDatum ctx).q = 55) (hK : (class1SlopeDatum ctx).K₀ = 5) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
      ∨ (cnlWindowTopStart ctx % 5 = 0
          ∧ 64 * hitGap ctx.n24CarryData.a (cnlWindowTopStart ctx)
              = 129 * shellLadderDepth ctx + 64) := by
  by_cases hk : cnlWindowTopStart ctx
      ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
  · exact Or.inr ⟨(class1Fibre_residue_of_datum_55_5 ctx hq hK hk).1,
      class1Fibre_r0_hitGap_pin ctx hr hk⟩
  · exact Or.inl hk

/-- `(q, K₀) = (57, 1)`: period `9`, cycle `7 → 55 → 53 → 49 → 41 → 25 → 43 → 29 → 1`, bands `4, 1, 1, 1, 1, 2, 1, 1, 6` — band-4 residue set `{1}` (values `7`), congruence class(es) `k % 9 ∈ {1}`. -/
private theorem cnlPairCycle_57_1 :
    slopeOrbit 57 1 (1 + 9) = slopeOrbit 57 1 1
      ∧ slopeOrbit 57 1 1 = 7
      ∧ ∀ j, 1 ≤ j → j ≤ 9 →
          canonGap 57 (slopeOrbit 57 1 j) = 4 → j ∈ ({1} : Finset ℕ) := by
  have e0 : slopeOrbit 57 1 0 = 1 := rfl
  have e1 : slopeOrbit 57 1 1 = 7 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 57 1 2 = 55 :=
    slopeOrbit_step_eval 1 3 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 57 1 3 = 53 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 57 1 4 = 49 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 57 1 5 = 41 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 57 1 6 = 25 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 57 1 7 = 43 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 57 1 8 = 29 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 57 1 9 = 1 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 57 1 10 = 7 :=
    slopeOrbit_step_eval 9 5 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, e1, ?_⟩
  · show slopeOrbit 57 1 10 = slopeOrbit 57 1 1
    rw [e10, e1]
  · intro j hj1 hjc hband
    interval_cases j
    · decide
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

private theorem cnlPairResidue_57_1 {k : ℕ} (hk1 : 1 ≤ k)
    (hband : canonGap 57 (slopeOrbit 57 1 k) = 4) :
    k % 9 = 1 ∧ slopeOrbit 57 1 k = 7 := by
  have hper := slopeOrbit_period_of_return cnlPairCycle_57_1.1
  have hres := slopeOrbit_eq_residue (by norm_num) hper hk1
  have hmod : (k - 1) % 9 < 9 := Nat.mod_lt _ (by norm_num)
  have hmem := cnlPairCycle_57_1.2.2 ((k - 1) % 9 + 1) (by omega) (by omega)
    (by rw [← hres]; exact hband)
  have hj4 := Finset.mem_singleton.mp hmem
  refine ⟨by omega, ?_⟩
  rw [hres, hj4]
  exact cnlPairCycle_57_1.2.1

/-- `(q, K₀) = (57, 1)`: every class-1 start satisfies the explicit congruence `k % 9 = 1`
and carries the unique band-4 orbit value `7`. -/
theorem class1Fibre_residue_of_datum_57_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 57) (hK : (class1SlopeDatum ctx).K₀ = 1)
    {k : ℕ} (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1) :
    k % 9 = 1
      ∧ slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k = 7 := by
  have hband := class1Fibre_canonGap_eq ctx hk
  have hk1 := class1Fibre_start_pos ctx hk
  rw [hq, hK] at hband
  have h := cnlPairResidue_57_1 hk1 hband
  refine ⟨h.1, ?_⟩
  rw [hq, hK]
  exact h.2

/-- `(q, K₀) = (57, 1)`: AT MOST ONE class-1 member per residue window — `#fibre₁ ≤ ⌈W/9⌉`. -/
theorem class1Fibre_card_le_of_datum_57_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 57) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card + 9 - 1) / 9 := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 9)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return cnlPairCycle_57_1.1
  have hcount : (class1Band4CycleBand ctx 9).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset cnlPairCycle_57_1.2.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 9).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 9 - 1) / 9) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 9 - 1) / 9) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)
    _ = ((supportShell ctx.shell.d ctx.shell.X).card + 9 - 1) / 9 :=
        Nat.one_mul _

/-- `(q, K₀) = (57, 1)`: any two class-1 members are congruent mod `9`, satisfy the concrete
hit-gap repeat equation, and their spacing is a full orbit period. -/
theorem class1Fibre_pair_rigidity_of_datum_57_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 57) (hK : (class1SlopeDatum ctx).K₀ = 1)
    {k k' : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hk' : k' ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hlt : k < k') :
    k % 9 = k' % 9
      ∧ ctx.n24CarryData.a (k + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k'
          = ctx.n24CarryData.a (k' + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k
      ∧ (∀ m, 1 ≤ m →
          slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + (k' - k))
            = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m) := by
  have h1 := class1Fibre_residue_of_datum_57_1 ctx hq hK hk
  have h2 := class1Fibre_residue_of_datum_57_1 ctx hq hK hk'
  exact ⟨by omega, class1Fibre_span_rigidity ctx hk hk',
    class1Fibre_spacing_period ctx hk hk' hlt (h1.2.trans h2.2.symm)⟩

/-- `(q, K₀) = (57, 1)`: a top start whose residue misses `1` mod `9` is NOT class-1
(every `r`, in particular `r = 0`). -/
theorem class1Fibre_top_notMem_of_residue_57_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 57) (hK : (class1SlopeDatum ctx).K₀ = 1)
    (hres : cnlWindowTopStart ctx % 9 ≠ 1) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 :=
  fun hk => hres (class1Fibre_residue_of_datum_57_1 ctx hq hK hk).1

/-- `(q, K₀) = (57, 1)`, `r = 0`: the top start is not class-1 OR the two explicit pins hold
(residue hit `% 9 = 1` + the single hit-gap equation). -/
theorem class1_r0_top_verdict_of_datum_57_1 (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0)
    (hq : (class1SlopeDatum ctx).q = 57) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
      ∨ (cnlWindowTopStart ctx % 9 = 1
          ∧ 64 * hitGap ctx.n24CarryData.a (cnlWindowTopStart ctx)
              = 129 * shellLadderDepth ctx + 64) := by
  by_cases hk : cnlWindowTopStart ctx
      ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
  · exact Or.inr ⟨(class1Fibre_residue_of_datum_57_1 ctx hq hK hk).1,
      class1Fibre_r0_hitGap_pin ctx hr hk⟩
  · exact Or.inl hk

/-- `(q, K₀) = (57, 28)`: period `9`, cycle `55 → 53 → 49 → 41 → 25 → 43 → 29 → 1 → 7`, bands `1, 1, 1, 1, 2, 1, 1, 6, 4` — band-4 residue set `{9}` (values `7`), congruence class(es) `k % 9 ∈ {0}`. -/
private theorem cnlPairCycle_57_28 :
    slopeOrbit 57 28 (1 + 9) = slopeOrbit 57 28 1
      ∧ slopeOrbit 57 28 9 = 7
      ∧ ∀ j, 1 ≤ j → j ≤ 9 →
          canonGap 57 (slopeOrbit 57 28 j) = 4 → j ∈ ({9} : Finset ℕ) := by
  have e0 : slopeOrbit 57 28 0 = 28 := rfl
  have e1 : slopeOrbit 57 28 1 = 55 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 57 28 2 = 53 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 57 28 3 = 49 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 57 28 4 = 41 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 57 28 5 = 25 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 57 28 6 = 43 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 57 28 7 = 29 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 57 28 8 = 1 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 57 28 9 = 7 :=
    slopeOrbit_step_eval 8 5 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 57 28 10 = 55 :=
    slopeOrbit_step_eval 9 3 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, e9, ?_⟩
  · show slopeOrbit 57 28 10 = slopeOrbit 57 28 1
    rw [e10, e1]
  · intro j hj1 hjc hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · decide

private theorem cnlPairResidue_57_28 {k : ℕ} (hk1 : 1 ≤ k)
    (hband : canonGap 57 (slopeOrbit 57 28 k) = 4) :
    k % 9 = 0 ∧ slopeOrbit 57 28 k = 7 := by
  have hper := slopeOrbit_period_of_return cnlPairCycle_57_28.1
  have hres := slopeOrbit_eq_residue (by norm_num) hper hk1
  have hmod : (k - 1) % 9 < 9 := Nat.mod_lt _ (by norm_num)
  have hmem := cnlPairCycle_57_28.2.2 ((k - 1) % 9 + 1) (by omega) (by omega)
    (by rw [← hres]; exact hband)
  have hj4 := Finset.mem_singleton.mp hmem
  refine ⟨by omega, ?_⟩
  rw [hres, hj4]
  exact cnlPairCycle_57_28.2.1

/-- `(q, K₀) = (57, 28)`: every class-1 start satisfies the explicit congruence `k % 9 = 0`
and carries the unique band-4 orbit value `7`. -/
theorem class1Fibre_residue_of_datum_57_28 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 57) (hK : (class1SlopeDatum ctx).K₀ = 28)
    {k : ℕ} (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1) :
    k % 9 = 0
      ∧ slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k = 7 := by
  have hband := class1Fibre_canonGap_eq ctx hk
  have hk1 := class1Fibre_start_pos ctx hk
  rw [hq, hK] at hband
  have h := cnlPairResidue_57_28 hk1 hband
  refine ⟨h.1, ?_⟩
  rw [hq, hK]
  exact h.2

/-- `(q, K₀) = (57, 28)`: AT MOST ONE class-1 member per residue window — `#fibre₁ ≤ ⌈W/9⌉`. -/
theorem class1Fibre_card_le_of_datum_57_28 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 57) (hK : (class1SlopeDatum ctx).K₀ = 28) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card + 9 - 1) / 9 := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 9)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return cnlPairCycle_57_28.1
  have hcount : (class1Band4CycleBand ctx 9).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset cnlPairCycle_57_28.2.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 9).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 9 - 1) / 9) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 9 - 1) / 9) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)
    _ = ((supportShell ctx.shell.d ctx.shell.X).card + 9 - 1) / 9 :=
        Nat.one_mul _

/-- `(q, K₀) = (57, 28)`: any two class-1 members are congruent mod `9`, satisfy the concrete
hit-gap repeat equation, and their spacing is a full orbit period. -/
theorem class1Fibre_pair_rigidity_of_datum_57_28 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 57) (hK : (class1SlopeDatum ctx).K₀ = 28)
    {k k' : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hk' : k' ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hlt : k < k') :
    k % 9 = k' % 9
      ∧ ctx.n24CarryData.a (k + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k'
          = ctx.n24CarryData.a (k' + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k
      ∧ (∀ m, 1 ≤ m →
          slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + (k' - k))
            = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m) := by
  have h1 := class1Fibre_residue_of_datum_57_28 ctx hq hK hk
  have h2 := class1Fibre_residue_of_datum_57_28 ctx hq hK hk'
  exact ⟨by omega, class1Fibre_span_rigidity ctx hk hk',
    class1Fibre_spacing_period ctx hk hk' hlt (h1.2.trans h2.2.symm)⟩

/-- `(q, K₀) = (57, 28)`: a top start whose residue misses `0` mod `9` is NOT class-1
(every `r`, in particular `r = 0`). -/
theorem class1Fibre_top_notMem_of_residue_57_28 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 57) (hK : (class1SlopeDatum ctx).K₀ = 28)
    (hres : cnlWindowTopStart ctx % 9 ≠ 0) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 :=
  fun hk => hres (class1Fibre_residue_of_datum_57_28 ctx hq hK hk).1

/-- `(q, K₀) = (57, 28)`, `r = 0`: the top start is not class-1 OR the two explicit pins hold
(residue hit `% 9 = 0` + the single hit-gap equation). -/
theorem class1_r0_top_verdict_of_datum_57_28 (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0)
    (hq : (class1SlopeDatum ctx).q = 57) (hK : (class1SlopeDatum ctx).K₀ = 28) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
      ∨ (cnlWindowTopStart ctx % 9 = 0
          ∧ 64 * hitGap ctx.n24CarryData.a (cnlWindowTopStart ctx)
              = 129 * shellLadderDepth ctx + 64) := by
  by_cases hk : cnlWindowTopStart ctx
      ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
  · exact Or.inr ⟨(class1Fibre_residue_of_datum_57_28 ctx hq hK hk).1,
      class1Fibre_r0_hitGap_pin ctx hr hk⟩
  · exact Or.inl hk

/-- `(q, K₀) = (63, 10)`: period `2`, cycle `17 → 5`, bands `2, 4` — band-4 residue set `{2}` (values `5`), congruence class(es) `k % 2 ∈ {0}`. -/
private theorem cnlPairCycle_63_10 :
    slopeOrbit 63 10 (1 + 2) = slopeOrbit 63 10 1
      ∧ slopeOrbit 63 10 2 = 5
      ∧ ∀ j, 1 ≤ j → j ≤ 2 →
          canonGap 63 (slopeOrbit 63 10 j) = 4 → j ∈ ({2} : Finset ℕ) := by
  have e0 : slopeOrbit 63 10 0 = 10 := rfl
  have e1 : slopeOrbit 63 10 1 = 17 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 63 10 2 = 5 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 63 10 3 = 17 :=
    slopeOrbit_step_eval 2 3 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, e2, ?_⟩
  · show slopeOrbit 63 10 3 = slopeOrbit 63 10 1
    rw [e3, e1]
  · intro j hj1 hjc hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide

private theorem cnlPairResidue_63_10 {k : ℕ} (hk1 : 1 ≤ k)
    (hband : canonGap 63 (slopeOrbit 63 10 k) = 4) :
    k % 2 = 0 ∧ slopeOrbit 63 10 k = 5 := by
  have hper := slopeOrbit_period_of_return cnlPairCycle_63_10.1
  have hres := slopeOrbit_eq_residue (by norm_num) hper hk1
  have hmod : (k - 1) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hmem := cnlPairCycle_63_10.2.2 ((k - 1) % 2 + 1) (by omega) (by omega)
    (by rw [← hres]; exact hband)
  have hj4 := Finset.mem_singleton.mp hmem
  refine ⟨by omega, ?_⟩
  rw [hres, hj4]
  exact cnlPairCycle_63_10.2.1

/-- `(q, K₀) = (63, 10)`: every class-1 start satisfies the explicit congruence `k % 2 = 0`
and carries the unique band-4 orbit value `5`. -/
theorem class1Fibre_residue_of_datum_63_10 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) (hK : (class1SlopeDatum ctx).K₀ = 10)
    {k : ℕ} (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1) :
    k % 2 = 0
      ∧ slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k = 5 := by
  have hband := class1Fibre_canonGap_eq ctx hk
  have hk1 := class1Fibre_start_pos ctx hk
  rw [hq, hK] at hband
  have h := cnlPairResidue_63_10 hk1 hband
  refine ⟨h.1, ?_⟩
  rw [hq, hK]
  exact h.2

/-- `(q, K₀) = (63, 10)`: AT MOST ONE class-1 member per residue window — `#fibre₁ ≤ ⌈W/2⌉`. -/
theorem class1Fibre_card_le_of_datum_63_10 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) (hK : (class1SlopeDatum ctx).K₀ = 10) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card + 2 - 1) / 2 := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 2)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return cnlPairCycle_63_10.1
  have hcount : (class1Band4CycleBand ctx 2).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset cnlPairCycle_63_10.2.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 2).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 2 - 1) / 2) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 2 - 1) / 2) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)
    _ = ((supportShell ctx.shell.d ctx.shell.X).card + 2 - 1) / 2 :=
        Nat.one_mul _

/-- `(q, K₀) = (63, 10)`: any two class-1 members are congruent mod `2`, satisfy the concrete
hit-gap repeat equation, and their spacing is a full orbit period. -/
theorem class1Fibre_pair_rigidity_of_datum_63_10 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) (hK : (class1SlopeDatum ctx).K₀ = 10)
    {k k' : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hk' : k' ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hlt : k < k') :
    k % 2 = k' % 2
      ∧ ctx.n24CarryData.a (k + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k'
          = ctx.n24CarryData.a (k' + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k
      ∧ (∀ m, 1 ≤ m →
          slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + (k' - k))
            = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m) := by
  have h1 := class1Fibre_residue_of_datum_63_10 ctx hq hK hk
  have h2 := class1Fibre_residue_of_datum_63_10 ctx hq hK hk'
  exact ⟨by omega, class1Fibre_span_rigidity ctx hk hk',
    class1Fibre_spacing_period ctx hk hk' hlt (h1.2.trans h2.2.symm)⟩

/-- `(q, K₀) = (63, 10)`: a top start whose residue misses `0` mod `2` is NOT class-1
(every `r`, in particular `r = 0`). -/
theorem class1Fibre_top_notMem_of_residue_63_10 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) (hK : (class1SlopeDatum ctx).K₀ = 10)
    (hres : cnlWindowTopStart ctx % 2 ≠ 0) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 :=
  fun hk => hres (class1Fibre_residue_of_datum_63_10 ctx hq hK hk).1

/-- `(q, K₀) = (63, 10)`, `r = 0`: the top start is not class-1 OR the two explicit pins hold
(residue hit `% 2 = 0` + the single hit-gap equation). -/
theorem class1_r0_top_verdict_of_datum_63_10 (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0)
    (hq : (class1SlopeDatum ctx).q = 63) (hK : (class1SlopeDatum ctx).K₀ = 10) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
      ∨ (cnlWindowTopStart ctx % 2 = 0
          ∧ 64 * hitGap ctx.n24CarryData.a (cnlWindowTopStart ctx)
              = 129 * shellLadderDepth ctx + 64) := by
  by_cases hk : cnlWindowTopStart ctx
      ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
  · exact Or.inr ⟨(class1Fibre_residue_of_datum_63_10 ctx hq hK hk).1,
      class1Fibre_r0_hitGap_pin ctx hr hk⟩
  · exact Or.inl hk

/-- `(q, K₀) = (69, 11)`: period `11`, cycle `19 → 7 → 43 → 17 → 67 → 65 → 61 → 53 → 37 → 5 → 11`, bands `2, 4, 1, 3, 1, 1, 1, 1, 1, 4, 3` — band-4 residue set `{2, 10}` (values `7, 5`), congruence class(es) `k % 11 ∈ {2, 10}`. -/
private theorem cnlPairCycle_69_11 :
    slopeOrbit 69 11 (1 + 11) = slopeOrbit 69 11 1
      ∧ slopeOrbit 69 11 2 = 7
      ∧ slopeOrbit 69 11 10 = 5
      ∧ ∀ j, 1 ≤ j → j ≤ 11 →
          canonGap 69 (slopeOrbit 69 11 j) = 4 → j ∈ ({2, 10} : Finset ℕ) := by
  have e0 : slopeOrbit 69 11 0 = 11 := rfl
  have e1 : slopeOrbit 69 11 1 = 19 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 69 11 2 = 7 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 69 11 3 = 43 :=
    slopeOrbit_step_eval 2 3 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 69 11 4 = 17 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 69 11 5 = 67 :=
    slopeOrbit_step_eval 4 2 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 69 11 6 = 65 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 69 11 7 = 61 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 69 11 8 = 53 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 69 11 9 = 37 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 69 11 10 = 5 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 69 11 11 = 11 :=
    slopeOrbit_step_eval 10 3 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 69 11 12 = 19 :=
    slopeOrbit_step_eval 11 2 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, e2, e10, ?_⟩
  · show slopeOrbit 69 11 12 = slopeOrbit 69 11 1
    rw [e12, e1]
  · intro j hj1 hjc hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))

private theorem cnlPairResidue_69_11 {k : ℕ} (hk1 : 1 ≤ k)
    (hband : canonGap 69 (slopeOrbit 69 11 k) = 4) :
    (k % 11 = 2 ∧ slopeOrbit 69 11 k = 7)
      ∨ (k % 11 = 10 ∧ slopeOrbit 69 11 k = 5) := by
  have hper := slopeOrbit_period_of_return cnlPairCycle_69_11.1
  have hres := slopeOrbit_eq_residue (by norm_num) hper hk1
  have hmod : (k - 1) % 11 < 11 := Nat.mod_lt _ (by norm_num)
  have hmem := cnlPairCycle_69_11.2.2.2 ((k - 1) % 11 + 1) (by omega) (by omega)
    (by rw [← hres]; exact hband)
  rcases Finset.mem_insert.mp hmem with hj | hj
  · refine Or.inl ⟨by omega, ?_⟩
    rw [hres, hj]
    exact cnlPairCycle_69_11.2.1
  · have hj' := Finset.mem_singleton.mp hj
    refine Or.inr ⟨by omega, ?_⟩
    rw [hres, hj']
    exact cnlPairCycle_69_11.2.2.1

/-- `(q, K₀) = (69, 11)`: every class-1 start lies in one of the TWO explicit congruence
classes `k % 11 ∈ {2, 10}`, with the matching band-4 orbit value (`7` resp. `5`). -/
theorem class1Fibre_residue_of_datum_69_11 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 69) (hK : (class1SlopeDatum ctx).K₀ = 11)
    {k : ℕ} (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1) :
    (k % 11 = 2
        ∧ slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k = 7)
      ∨ (k % 11 = 10
        ∧ slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k = 5) := by
  have hband := class1Fibre_canonGap_eq ctx hk
  have hk1 := class1Fibre_start_pos ctx hk
  rw [hq, hK] at hband
  rcases cnlPairResidue_69_11 hk1 hband with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine Or.inl ⟨h1, ?_⟩
    rw [hq, hK]
    exact h2
  · refine Or.inr ⟨h1, ?_⟩
    rw [hq, hK]
    exact h2

/-- `(q, K₀) = (69, 11)`: at most TWO class-1 members per residue window — `#fibre₁ ≤ 2·⌈W/11⌉`. -/
theorem class1Fibre_card_le_of_datum_69_11 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 69) (hK : (class1SlopeDatum ctx).K₀ = 11) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 11 - 1) / 11) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 11)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return cnlPairCycle_69_11.1
  have hcount : (class1Band4CycleBand ctx 11).card ≤ 2 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset cnlPairCycle_69_11.2.2.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 11).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 11 - 1) / 11) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 11 - 1) / 11) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(q, K₀) = (69, 11)`: two class-1 members in the SAME residue class mod `11` carry equal
orbit numerators, satisfy the concrete hit-gap repeat equation, and their spacing is a
full orbit period. -/
theorem class1Fibre_pair_rigidity_of_datum_69_11 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 69) (hK : (class1SlopeDatum ctx).K₀ = 11)
    {k k' : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hk' : k' ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hlt : k < k') (hmod : k % 11 = k' % 11) :
    ctx.n24CarryData.a (k + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k'
        = ctx.n24CarryData.a (k' + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k
      ∧ (∀ m, 1 ≤ m →
          slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + (k' - k))
            = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m) := by
  have h1 := class1Fibre_residue_of_datum_69_11 ctx hq hK hk
  have h2 := class1Fibre_residue_of_datum_69_11 ctx hq hK hk'
  have horb : slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
      = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k' := by
    rcases h1 with ⟨hr1, hv1⟩ | ⟨hr1, hv1⟩ <;>
      rcases h2 with ⟨hr2, hv2⟩ | ⟨hr2, hv2⟩
    · rw [hv1, hv2]
    · omega
    · omega
    · rw [hv1, hv2]
  exact ⟨class1Fibre_span_rigidity ctx hk hk',
    class1Fibre_spacing_period ctx hk hk' hlt horb⟩

/-- `(q, K₀) = (69, 11)`: a top start whose residue misses BOTH classes `2` and `10` mod `11`
is NOT class-1 (every `r`, in particular `r = 0`). -/
theorem class1Fibre_top_notMem_of_residue_69_11 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 69) (hK : (class1SlopeDatum ctx).K₀ = 11)
    (hres1 : cnlWindowTopStart ctx % 11 ≠ 2)
    (hres2 : cnlWindowTopStart ctx % 11 ≠ 10) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 := by
  intro hk
  rcases class1Fibre_residue_of_datum_69_11 ctx hq hK hk with ⟨h, _⟩ | ⟨h, _⟩
  · exact hres1 h
  · exact hres2 h

/-- `(q, K₀) = (69, 11)`, `r = 0`: the top start is not class-1 OR the residue hits one of the
two classes AND the single hit-gap equation holds. -/
theorem class1_r0_top_verdict_of_datum_69_11 (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0)
    (hq : (class1SlopeDatum ctx).q = 69) (hK : (class1SlopeDatum ctx).K₀ = 11) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
      ∨ ((cnlWindowTopStart ctx % 11 = 2 ∨ cnlWindowTopStart ctx % 11 = 10)
          ∧ 64 * hitGap ctx.n24CarryData.a (cnlWindowTopStart ctx)
              = 129 * shellLadderDepth ctx + 64) := by
  by_cases hk : cnlWindowTopStart ctx
      ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
  · rcases class1Fibre_residue_of_datum_69_11 ctx hq hK hk with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inr ⟨Or.inl h, class1Fibre_r0_hitGap_pin ctx hr hk⟩
    · exact Or.inr ⟨Or.inr h, class1Fibre_r0_hitGap_pin ctx hr hk⟩
  · exact Or.inl hk

/-- `(q, K₀) = (69, 34)`: period `11`, cycle `67 → 65 → 61 → 53 → 37 → 5 → 11 → 19 → 7 → 43 → 17`, bands `1, 1, 1, 1, 1, 4, 3, 2, 4, 1, 3` — band-4 residue set `{6, 9}` (values `5, 7`), congruence class(es) `k % 11 ∈ {6, 9}`. -/
private theorem cnlPairCycle_69_34 :
    slopeOrbit 69 34 (1 + 11) = slopeOrbit 69 34 1
      ∧ slopeOrbit 69 34 6 = 5
      ∧ slopeOrbit 69 34 9 = 7
      ∧ ∀ j, 1 ≤ j → j ≤ 11 →
          canonGap 69 (slopeOrbit 69 34 j) = 4 → j ∈ ({6, 9} : Finset ℕ) := by
  have e0 : slopeOrbit 69 34 0 = 34 := rfl
  have e1 : slopeOrbit 69 34 1 = 67 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 69 34 2 = 65 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 69 34 3 = 61 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 69 34 4 = 53 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 69 34 5 = 37 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 69 34 6 = 5 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 69 34 7 = 11 :=
    slopeOrbit_step_eval 6 3 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 69 34 8 = 19 :=
    slopeOrbit_step_eval 7 2 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 69 34 9 = 7 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 69 34 10 = 43 :=
    slopeOrbit_step_eval 9 3 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 69 34 11 = 17 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 69 34 12 = 67 :=
    slopeOrbit_step_eval 11 2 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, e6, e9, ?_⟩
  · show slopeOrbit 69 34 12 = slopeOrbit 69 34 1
    rw [e12, e1]
  · intro j hj1 hjc hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))

private theorem cnlPairResidue_69_34 {k : ℕ} (hk1 : 1 ≤ k)
    (hband : canonGap 69 (slopeOrbit 69 34 k) = 4) :
    (k % 11 = 6 ∧ slopeOrbit 69 34 k = 5)
      ∨ (k % 11 = 9 ∧ slopeOrbit 69 34 k = 7) := by
  have hper := slopeOrbit_period_of_return cnlPairCycle_69_34.1
  have hres := slopeOrbit_eq_residue (by norm_num) hper hk1
  have hmod : (k - 1) % 11 < 11 := Nat.mod_lt _ (by norm_num)
  have hmem := cnlPairCycle_69_34.2.2.2 ((k - 1) % 11 + 1) (by omega) (by omega)
    (by rw [← hres]; exact hband)
  rcases Finset.mem_insert.mp hmem with hj | hj
  · refine Or.inl ⟨by omega, ?_⟩
    rw [hres, hj]
    exact cnlPairCycle_69_34.2.1
  · have hj' := Finset.mem_singleton.mp hj
    refine Or.inr ⟨by omega, ?_⟩
    rw [hres, hj']
    exact cnlPairCycle_69_34.2.2.1

/-- `(q, K₀) = (69, 34)`: every class-1 start lies in one of the TWO explicit congruence
classes `k % 11 ∈ {6, 9}`, with the matching band-4 orbit value (`5` resp. `7`). -/
theorem class1Fibre_residue_of_datum_69_34 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 69) (hK : (class1SlopeDatum ctx).K₀ = 34)
    {k : ℕ} (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1) :
    (k % 11 = 6
        ∧ slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k = 5)
      ∨ (k % 11 = 9
        ∧ slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k = 7) := by
  have hband := class1Fibre_canonGap_eq ctx hk
  have hk1 := class1Fibre_start_pos ctx hk
  rw [hq, hK] at hband
  rcases cnlPairResidue_69_34 hk1 hband with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine Or.inl ⟨h1, ?_⟩
    rw [hq, hK]
    exact h2
  · refine Or.inr ⟨h1, ?_⟩
    rw [hq, hK]
    exact h2

/-- `(q, K₀) = (69, 34)`: at most TWO class-1 members per residue window — `#fibre₁ ≤ 2·⌈W/11⌉`. -/
theorem class1Fibre_card_le_of_datum_69_34 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 69) (hK : (class1SlopeDatum ctx).K₀ = 34) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 11 - 1) / 11) := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 11)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return cnlPairCycle_69_34.1
  have hcount : (class1Band4CycleBand ctx 11).card ≤ 2 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset cnlPairCycle_69_34.2.2.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 11).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 11 - 1) / 11) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 2 * (((supportShell ctx.shell.d ctx.shell.X).card + 11 - 1) / 11) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)

/-- `(q, K₀) = (69, 34)`: two class-1 members in the SAME residue class mod `11` carry equal
orbit numerators, satisfy the concrete hit-gap repeat equation, and their spacing is a
full orbit period. -/
theorem class1Fibre_pair_rigidity_of_datum_69_34 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 69) (hK : (class1SlopeDatum ctx).K₀ = 34)
    {k k' : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hk' : k' ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hlt : k < k') (hmod : k % 11 = k' % 11) :
    ctx.n24CarryData.a (k + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k'
        = ctx.n24CarryData.a (k' + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k
      ∧ (∀ m, 1 ≤ m →
          slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + (k' - k))
            = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m) := by
  have h1 := class1Fibre_residue_of_datum_69_34 ctx hq hK hk
  have h2 := class1Fibre_residue_of_datum_69_34 ctx hq hK hk'
  have horb : slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k
      = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k' := by
    rcases h1 with ⟨hr1, hv1⟩ | ⟨hr1, hv1⟩ <;>
      rcases h2 with ⟨hr2, hv2⟩ | ⟨hr2, hv2⟩
    · rw [hv1, hv2]
    · omega
    · omega
    · rw [hv1, hv2]
  exact ⟨class1Fibre_span_rigidity ctx hk hk',
    class1Fibre_spacing_period ctx hk hk' hlt horb⟩

/-- `(q, K₀) = (69, 34)`: a top start whose residue misses BOTH classes `6` and `9` mod `11`
is NOT class-1 (every `r`, in particular `r = 0`). -/
theorem class1Fibre_top_notMem_of_residue_69_34 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 69) (hK : (class1SlopeDatum ctx).K₀ = 34)
    (hres1 : cnlWindowTopStart ctx % 11 ≠ 6)
    (hres2 : cnlWindowTopStart ctx % 11 ≠ 9) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 := by
  intro hk
  rcases class1Fibre_residue_of_datum_69_34 ctx hq hK hk with ⟨h, _⟩ | ⟨h, _⟩
  · exact hres1 h
  · exact hres2 h

/-- `(q, K₀) = (69, 34)`, `r = 0`: the top start is not class-1 OR the residue hits one of the
two classes AND the single hit-gap equation holds. -/
theorem class1_r0_top_verdict_of_datum_69_34 (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0)
    (hq : (class1SlopeDatum ctx).q = 69) (hK : (class1SlopeDatum ctx).K₀ = 34) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
      ∨ ((cnlWindowTopStart ctx % 11 = 6 ∨ cnlWindowTopStart ctx % 11 = 9)
          ∧ 64 * hitGap ctx.n24CarryData.a (cnlWindowTopStart ctx)
              = 129 * shellLadderDepth ctx + 64) := by
  by_cases hk : cnlWindowTopStart ctx
      ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
  · rcases class1Fibre_residue_of_datum_69_34 ctx hq hK hk with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inr ⟨Or.inl h, class1Fibre_r0_hitGap_pin ctx hr hk⟩
    · exact Or.inr ⟨Or.inr h, class1Fibre_r0_hitGap_pin ctx hr hk⟩
  · exact Or.inl hk

/-- `(q, K₀) = (75, 7)`: period `11`, cycle `37 → 73 → 71 → 67 → 59 → 43 → 11 → 13 → 29 → 41 → 7`, bands `2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4` — band-4 residue set `{11}` (values `7`), congruence class(es) `k % 11 ∈ {0}`. -/
private theorem cnlPairCycle_75_7 :
    slopeOrbit 75 7 (1 + 11) = slopeOrbit 75 7 1
      ∧ slopeOrbit 75 7 11 = 7
      ∧ ∀ j, 1 ≤ j → j ≤ 11 →
          canonGap 75 (slopeOrbit 75 7 j) = 4 → j ∈ ({11} : Finset ℕ) := by
  have e0 : slopeOrbit 75 7 0 = 7 := rfl
  have e1 : slopeOrbit 75 7 1 = 37 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 75 7 2 = 73 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 75 7 3 = 71 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 75 7 4 = 67 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 75 7 5 = 59 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 75 7 6 = 43 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 75 7 7 = 11 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 75 7 8 = 13 :=
    slopeOrbit_step_eval 7 2 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 75 7 9 = 29 :=
    slopeOrbit_step_eval 8 2 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 75 7 10 = 41 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 75 7 11 = 7 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 75 7 12 = 37 :=
    slopeOrbit_step_eval 11 3 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, e11, ?_⟩
  · show slopeOrbit 75 7 12 = slopeOrbit 75 7 1
    rw [e12, e1]
  · intro j hj1 hjc hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide

private theorem cnlPairResidue_75_7 {k : ℕ} (hk1 : 1 ≤ k)
    (hband : canonGap 75 (slopeOrbit 75 7 k) = 4) :
    k % 11 = 0 ∧ slopeOrbit 75 7 k = 7 := by
  have hper := slopeOrbit_period_of_return cnlPairCycle_75_7.1
  have hres := slopeOrbit_eq_residue (by norm_num) hper hk1
  have hmod : (k - 1) % 11 < 11 := Nat.mod_lt _ (by norm_num)
  have hmem := cnlPairCycle_75_7.2.2 ((k - 1) % 11 + 1) (by omega) (by omega)
    (by rw [← hres]; exact hband)
  have hj4 := Finset.mem_singleton.mp hmem
  refine ⟨by omega, ?_⟩
  rw [hres, hj4]
  exact cnlPairCycle_75_7.2.1

/-- `(q, K₀) = (75, 7)`: every class-1 start satisfies the explicit congruence `k % 11 = 0`
and carries the unique band-4 orbit value `7`. -/
theorem class1Fibre_residue_of_datum_75_7 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 75) (hK : (class1SlopeDatum ctx).K₀ = 7)
    {k : ℕ} (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1) :
    k % 11 = 0
      ∧ slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k = 7 := by
  have hband := class1Fibre_canonGap_eq ctx hk
  have hk1 := class1Fibre_start_pos ctx hk
  rw [hq, hK] at hband
  have h := cnlPairResidue_75_7 hk1 hband
  refine ⟨h.1, ?_⟩
  rw [hq, hK]
  exact h.2

/-- `(q, K₀) = (75, 7)`: AT MOST ONE class-1 member per residue window — `#fibre₁ ≤ ⌈W/11⌉`. -/
theorem class1Fibre_card_le_of_datum_75_7 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 75) (hK : (class1SlopeDatum ctx).K₀ = 7) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card + 11 - 1) / 11 := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 11)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return cnlPairCycle_75_7.1
  have hcount : (class1Band4CycleBand ctx 11).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset cnlPairCycle_75_7.2.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 11).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 11 - 1) / 11) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 11 - 1) / 11) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)
    _ = ((supportShell ctx.shell.d ctx.shell.X).card + 11 - 1) / 11 :=
        Nat.one_mul _

/-- `(q, K₀) = (75, 7)`: any two class-1 members are congruent mod `11`, satisfy the concrete
hit-gap repeat equation, and their spacing is a full orbit period. -/
theorem class1Fibre_pair_rigidity_of_datum_75_7 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 75) (hK : (class1SlopeDatum ctx).K₀ = 7)
    {k k' : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hk' : k' ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hlt : k < k') :
    k % 11 = k' % 11
      ∧ ctx.n24CarryData.a (k + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k'
          = ctx.n24CarryData.a (k' + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k
      ∧ (∀ m, 1 ≤ m →
          slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + (k' - k))
            = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m) := by
  have h1 := class1Fibre_residue_of_datum_75_7 ctx hq hK hk
  have h2 := class1Fibre_residue_of_datum_75_7 ctx hq hK hk'
  exact ⟨by omega, class1Fibre_span_rigidity ctx hk hk',
    class1Fibre_spacing_period ctx hk hk' hlt (h1.2.trans h2.2.symm)⟩

/-- `(q, K₀) = (75, 7)`: a top start whose residue misses `0` mod `11` is NOT class-1
(every `r`, in particular `r = 0`). -/
theorem class1Fibre_top_notMem_of_residue_75_7 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 75) (hK : (class1SlopeDatum ctx).K₀ = 7)
    (hres : cnlWindowTopStart ctx % 11 ≠ 0) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 :=
  fun hk => hres (class1Fibre_residue_of_datum_75_7 ctx hq hK hk).1

/-- `(q, K₀) = (75, 7)`, `r = 0`: the top start is not class-1 OR the two explicit pins hold
(residue hit `% 11 = 0` + the single hit-gap equation). -/
theorem class1_r0_top_verdict_of_datum_75_7 (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0)
    (hq : (class1SlopeDatum ctx).q = 75) (hK : (class1SlopeDatum ctx).K₀ = 7) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
      ∨ (cnlWindowTopStart ctx % 11 = 0
          ∧ 64 * hitGap ctx.n24CarryData.a (cnlWindowTopStart ctx)
              = 129 * shellLadderDepth ctx + 64) := by
  by_cases hk : cnlWindowTopStart ctx
      ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
  · exact Or.inr ⟨(class1Fibre_residue_of_datum_75_7 ctx hq hK hk).1,
      class1Fibre_r0_hitGap_pin ctx hr hk⟩
  · exact Or.inl hk

/-- `(q, K₀) = (75, 12)`: period `10`, cycle `21 → 9 → 69 → 63 → 51 → 27 → 33 → 57 → 39 → 3`, bands `2, 4, 1, 1, 1, 2, 2, 1, 1, 5` — band-4 residue set `{2}` (values `9`), congruence class(es) `k % 10 ∈ {2}`. -/
private theorem cnlPairCycle_75_12 :
    slopeOrbit 75 12 (1 + 10) = slopeOrbit 75 12 1
      ∧ slopeOrbit 75 12 2 = 9
      ∧ ∀ j, 1 ≤ j → j ≤ 10 →
          canonGap 75 (slopeOrbit 75 12 j) = 4 → j ∈ ({2} : Finset ℕ) := by
  have e0 : slopeOrbit 75 12 0 = 12 := rfl
  have e1 : slopeOrbit 75 12 1 = 21 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 75 12 2 = 9 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 75 12 3 = 69 :=
    slopeOrbit_step_eval 2 3 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 75 12 4 = 63 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 75 12 5 = 51 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 75 12 6 = 27 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 75 12 7 = 33 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 75 12 8 = 57 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 75 12 9 = 39 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 75 12 10 = 3 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 75 12 11 = 21 :=
    slopeOrbit_step_eval 10 4 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, e2, ?_⟩
  · show slopeOrbit 75 12 11 = slopeOrbit 75 12 1
    rw [e11, e1]
  · intro j hj1 hjc hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

private theorem cnlPairResidue_75_12 {k : ℕ} (hk1 : 1 ≤ k)
    (hband : canonGap 75 (slopeOrbit 75 12 k) = 4) :
    k % 10 = 2 ∧ slopeOrbit 75 12 k = 9 := by
  have hper := slopeOrbit_period_of_return cnlPairCycle_75_12.1
  have hres := slopeOrbit_eq_residue (by norm_num) hper hk1
  have hmod : (k - 1) % 10 < 10 := Nat.mod_lt _ (by norm_num)
  have hmem := cnlPairCycle_75_12.2.2 ((k - 1) % 10 + 1) (by omega) (by omega)
    (by rw [← hres]; exact hband)
  have hj4 := Finset.mem_singleton.mp hmem
  refine ⟨by omega, ?_⟩
  rw [hres, hj4]
  exact cnlPairCycle_75_12.2.1

/-- `(q, K₀) = (75, 12)`: every class-1 start satisfies the explicit congruence `k % 10 = 2`
and carries the unique band-4 orbit value `9`. -/
theorem class1Fibre_residue_of_datum_75_12 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 75) (hK : (class1SlopeDatum ctx).K₀ = 12)
    {k : ℕ} (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1) :
    k % 10 = 2
      ∧ slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k = 9 := by
  have hband := class1Fibre_canonGap_eq ctx hk
  have hk1 := class1Fibre_start_pos ctx hk
  rw [hq, hK] at hband
  have h := cnlPairResidue_75_12 hk1 hband
  refine ⟨h.1, ?_⟩
  rw [hq, hK]
  exact h.2

/-- `(q, K₀) = (75, 12)`: AT MOST ONE class-1 member per residue window — `#fibre₁ ≤ ⌈W/10⌉`. -/
theorem class1Fibre_card_le_of_datum_75_12 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 75) (hK : (class1SlopeDatum ctx).K₀ = 12) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card + 10 - 1) / 10 := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 10)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return cnlPairCycle_75_12.1
  have hcount : (class1Band4CycleBand ctx 10).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset cnlPairCycle_75_12.2.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 10).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 10 - 1) / 10) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 10 - 1) / 10) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)
    _ = ((supportShell ctx.shell.d ctx.shell.X).card + 10 - 1) / 10 :=
        Nat.one_mul _

/-- `(q, K₀) = (75, 12)`: any two class-1 members are congruent mod `10`, satisfy the concrete
hit-gap repeat equation, and their spacing is a full orbit period. -/
theorem class1Fibre_pair_rigidity_of_datum_75_12 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 75) (hK : (class1SlopeDatum ctx).K₀ = 12)
    {k k' : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hk' : k' ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hlt : k < k') :
    k % 10 = k' % 10
      ∧ ctx.n24CarryData.a (k + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k'
          = ctx.n24CarryData.a (k' + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k
      ∧ (∀ m, 1 ≤ m →
          slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + (k' - k))
            = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m) := by
  have h1 := class1Fibre_residue_of_datum_75_12 ctx hq hK hk
  have h2 := class1Fibre_residue_of_datum_75_12 ctx hq hK hk'
  exact ⟨by omega, class1Fibre_span_rigidity ctx hk hk',
    class1Fibre_spacing_period ctx hk hk' hlt (h1.2.trans h2.2.symm)⟩

/-- `(q, K₀) = (75, 12)`: a top start whose residue misses `2` mod `10` is NOT class-1
(every `r`, in particular `r = 0`). -/
theorem class1Fibre_top_notMem_of_residue_75_12 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 75) (hK : (class1SlopeDatum ctx).K₀ = 12)
    (hres : cnlWindowTopStart ctx % 10 ≠ 2) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 :=
  fun hk => hres (class1Fibre_residue_of_datum_75_12 ctx hq hK hk).1

/-- `(q, K₀) = (75, 12)`, `r = 0`: the top start is not class-1 OR the two explicit pins hold
(residue hit `% 10 = 2` + the single hit-gap equation). -/
theorem class1_r0_top_verdict_of_datum_75_12 (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0)
    (hq : (class1SlopeDatum ctx).q = 75) (hK : (class1SlopeDatum ctx).K₀ = 12) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
      ∨ (cnlWindowTopStart ctx % 10 = 2
          ∧ 64 * hitGap ctx.n24CarryData.a (cnlWindowTopStart ctx)
              = 129 * shellLadderDepth ctx + 64) := by
  by_cases hk : cnlWindowTopStart ctx
      ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
  · exact Or.inr ⟨(class1Fibre_residue_of_datum_75_12 ctx hq hK hk).1,
      class1Fibre_r0_hitGap_pin ctx hr hk⟩
  · exact Or.inl hk

/-- `(q, K₀) = (75, 37)`: period `11`, cycle `73 → 71 → 67 → 59 → 43 → 11 → 13 → 29 → 41 → 7 → 37`, bands `1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 2` — band-4 residue set `{10}` (values `7`), congruence class(es) `k % 11 ∈ {10}`. -/
private theorem cnlPairCycle_75_37 :
    slopeOrbit 75 37 (1 + 11) = slopeOrbit 75 37 1
      ∧ slopeOrbit 75 37 10 = 7
      ∧ ∀ j, 1 ≤ j → j ≤ 11 →
          canonGap 75 (slopeOrbit 75 37 j) = 4 → j ∈ ({10} : Finset ℕ) := by
  have e0 : slopeOrbit 75 37 0 = 37 := rfl
  have e1 : slopeOrbit 75 37 1 = 73 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 75 37 2 = 71 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 75 37 3 = 67 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 75 37 4 = 59 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 75 37 5 = 43 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 75 37 6 = 11 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 75 37 7 = 13 :=
    slopeOrbit_step_eval 6 2 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 75 37 8 = 29 :=
    slopeOrbit_step_eval 7 2 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 75 37 9 = 41 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 75 37 10 = 7 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 75 37 11 = 37 :=
    slopeOrbit_step_eval 10 3 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 75 37 12 = 73 :=
    slopeOrbit_step_eval 11 1 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, e10, ?_⟩
  · show slopeOrbit 75 37 12 = slopeOrbit 75 37 1
    rw [e12, e1]
  · intro j hj1 hjc hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))

private theorem cnlPairResidue_75_37 {k : ℕ} (hk1 : 1 ≤ k)
    (hband : canonGap 75 (slopeOrbit 75 37 k) = 4) :
    k % 11 = 10 ∧ slopeOrbit 75 37 k = 7 := by
  have hper := slopeOrbit_period_of_return cnlPairCycle_75_37.1
  have hres := slopeOrbit_eq_residue (by norm_num) hper hk1
  have hmod : (k - 1) % 11 < 11 := Nat.mod_lt _ (by norm_num)
  have hmem := cnlPairCycle_75_37.2.2 ((k - 1) % 11 + 1) (by omega) (by omega)
    (by rw [← hres]; exact hband)
  have hj4 := Finset.mem_singleton.mp hmem
  refine ⟨by omega, ?_⟩
  rw [hres, hj4]
  exact cnlPairCycle_75_37.2.1

/-- `(q, K₀) = (75, 37)`: every class-1 start satisfies the explicit congruence `k % 11 = 10`
and carries the unique band-4 orbit value `7`. -/
theorem class1Fibre_residue_of_datum_75_37 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 75) (hK : (class1SlopeDatum ctx).K₀ = 37)
    {k : ℕ} (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1) :
    k % 11 = 10
      ∧ slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k = 7 := by
  have hband := class1Fibre_canonGap_eq ctx hk
  have hk1 := class1Fibre_start_pos ctx hk
  rw [hq, hK] at hband
  have h := cnlPairResidue_75_37 hk1 hband
  refine ⟨h.1, ?_⟩
  rw [hq, hK]
  exact h.2

/-- `(q, K₀) = (75, 37)`: AT MOST ONE class-1 member per residue window — `#fibre₁ ≤ ⌈W/11⌉`. -/
theorem class1Fibre_card_le_of_datum_75_37 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 75) (hK : (class1SlopeDatum ctx).K₀ = 37) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card + 11 - 1) / 11 := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 11)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return cnlPairCycle_75_37.1
  have hcount : (class1Band4CycleBand ctx 11).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset cnlPairCycle_75_37.2.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 11).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 11 - 1) / 11) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 11 - 1) / 11) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)
    _ = ((supportShell ctx.shell.d ctx.shell.X).card + 11 - 1) / 11 :=
        Nat.one_mul _

/-- `(q, K₀) = (75, 37)`: any two class-1 members are congruent mod `11`, satisfy the concrete
hit-gap repeat equation, and their spacing is a full orbit period. -/
theorem class1Fibre_pair_rigidity_of_datum_75_37 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 75) (hK : (class1SlopeDatum ctx).K₀ = 37)
    {k k' : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hk' : k' ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hlt : k < k') :
    k % 11 = k' % 11
      ∧ ctx.n24CarryData.a (k + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k'
          = ctx.n24CarryData.a (k' + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k
      ∧ (∀ m, 1 ≤ m →
          slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + (k' - k))
            = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m) := by
  have h1 := class1Fibre_residue_of_datum_75_37 ctx hq hK hk
  have h2 := class1Fibre_residue_of_datum_75_37 ctx hq hK hk'
  exact ⟨by omega, class1Fibre_span_rigidity ctx hk hk',
    class1Fibre_spacing_period ctx hk hk' hlt (h1.2.trans h2.2.symm)⟩

/-- `(q, K₀) = (75, 37)`: a top start whose residue misses `10` mod `11` is NOT class-1
(every `r`, in particular `r = 0`). -/
theorem class1Fibre_top_notMem_of_residue_75_37 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 75) (hK : (class1SlopeDatum ctx).K₀ = 37)
    (hres : cnlWindowTopStart ctx % 11 ≠ 10) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 :=
  fun hk => hres (class1Fibre_residue_of_datum_75_37 ctx hq hK hk).1

/-- `(q, K₀) = (75, 37)`, `r = 0`: the top start is not class-1 OR the two explicit pins hold
(residue hit `% 11 = 10` + the single hit-gap equation). -/
theorem class1_r0_top_verdict_of_datum_75_37 (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0)
    (hq : (class1SlopeDatum ctx).q = 75) (hK : (class1SlopeDatum ctx).K₀ = 37) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
      ∨ (cnlWindowTopStart ctx % 11 = 10
          ∧ 64 * hitGap ctx.n24CarryData.a (cnlWindowTopStart ctx)
              = 129 * shellLadderDepth ctx + 64) := by
  by_cases hk : cnlWindowTopStart ctx
      ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
  · exact Or.inr ⟨(class1Fibre_residue_of_datum_75_37 ctx hq hK hk).1,
      class1Fibre_r0_hitGap_pin ctx hr hk⟩
  · exact Or.inl hk

/-- `(q, K₀) = (87, 1)`: period `11`, cycle `41 → 77 → 67 → 47 → 7 → 25 → 13 → 17 → 49 → 11 → 1`, bands `2, 1, 1, 1, 4, 2, 3, 3, 1, 3, 7` — band-4 residue set `{5}` (values `7`), congruence class(es) `k % 11 ∈ {5}`. -/
private theorem cnlPairCycle_87_1 :
    slopeOrbit 87 1 (1 + 11) = slopeOrbit 87 1 1
      ∧ slopeOrbit 87 1 5 = 7
      ∧ ∀ j, 1 ≤ j → j ≤ 11 →
          canonGap 87 (slopeOrbit 87 1 j) = 4 → j ∈ ({5} : Finset ℕ) := by
  have e0 : slopeOrbit 87 1 0 = 1 := rfl
  have e1 : slopeOrbit 87 1 1 = 41 :=
    slopeOrbit_step_eval 0 6 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 87 1 2 = 77 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 87 1 3 = 67 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 87 1 4 = 47 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 87 1 5 = 7 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 87 1 6 = 25 :=
    slopeOrbit_step_eval 5 3 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 87 1 7 = 13 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 87 1 8 = 17 :=
    slopeOrbit_step_eval 7 2 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 87 1 9 = 49 :=
    slopeOrbit_step_eval 8 2 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 87 1 10 = 11 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 87 1 11 = 1 :=
    slopeOrbit_step_eval 10 2 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 87 1 12 = 41 :=
    slopeOrbit_step_eval 11 6 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, e5, ?_⟩
  · show slopeOrbit 87 1 12 = slopeOrbit 87 1 1
    rw [e12, e1]
  · intro j hj1 hjc hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

private theorem cnlPairResidue_87_1 {k : ℕ} (hk1 : 1 ≤ k)
    (hband : canonGap 87 (slopeOrbit 87 1 k) = 4) :
    k % 11 = 5 ∧ slopeOrbit 87 1 k = 7 := by
  have hper := slopeOrbit_period_of_return cnlPairCycle_87_1.1
  have hres := slopeOrbit_eq_residue (by norm_num) hper hk1
  have hmod : (k - 1) % 11 < 11 := Nat.mod_lt _ (by norm_num)
  have hmem := cnlPairCycle_87_1.2.2 ((k - 1) % 11 + 1) (by omega) (by omega)
    (by rw [← hres]; exact hband)
  have hj4 := Finset.mem_singleton.mp hmem
  refine ⟨by omega, ?_⟩
  rw [hres, hj4]
  exact cnlPairCycle_87_1.2.1

/-- `(q, K₀) = (87, 1)`: every class-1 start satisfies the explicit congruence `k % 11 = 5`
and carries the unique band-4 orbit value `7`. -/
theorem class1Fibre_residue_of_datum_87_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 87) (hK : (class1SlopeDatum ctx).K₀ = 1)
    {k : ℕ} (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1) :
    k % 11 = 5
      ∧ slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k = 7 := by
  have hband := class1Fibre_canonGap_eq ctx hk
  have hk1 := class1Fibre_start_pos ctx hk
  rw [hq, hK] at hband
  have h := cnlPairResidue_87_1 hk1 hband
  refine ⟨h.1, ?_⟩
  rw [hq, hK]
  exact h.2

/-- `(q, K₀) = (87, 1)`: AT MOST ONE class-1 member per residue window — `#fibre₁ ≤ ⌈W/11⌉`. -/
theorem class1Fibre_card_le_of_datum_87_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 87) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card + 11 - 1) / 11 := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 11)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return cnlPairCycle_87_1.1
  have hcount : (class1Band4CycleBand ctx 11).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset cnlPairCycle_87_1.2.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 11).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 11 - 1) / 11) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 11 - 1) / 11) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)
    _ = ((supportShell ctx.shell.d ctx.shell.X).card + 11 - 1) / 11 :=
        Nat.one_mul _

/-- `(q, K₀) = (87, 1)`: any two class-1 members are congruent mod `11`, satisfy the concrete
hit-gap repeat equation, and their spacing is a full orbit period. -/
theorem class1Fibre_pair_rigidity_of_datum_87_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 87) (hK : (class1SlopeDatum ctx).K₀ = 1)
    {k k' : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hk' : k' ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hlt : k < k') :
    k % 11 = k' % 11
      ∧ ctx.n24CarryData.a (k + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k'
          = ctx.n24CarryData.a (k' + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k
      ∧ (∀ m, 1 ≤ m →
          slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + (k' - k))
            = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m) := by
  have h1 := class1Fibre_residue_of_datum_87_1 ctx hq hK hk
  have h2 := class1Fibre_residue_of_datum_87_1 ctx hq hK hk'
  exact ⟨by omega, class1Fibre_span_rigidity ctx hk hk',
    class1Fibre_spacing_period ctx hk hk' hlt (h1.2.trans h2.2.symm)⟩

/-- `(q, K₀) = (87, 1)`: a top start whose residue misses `5` mod `11` is NOT class-1
(every `r`, in particular `r = 0`). -/
theorem class1Fibre_top_notMem_of_residue_87_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 87) (hK : (class1SlopeDatum ctx).K₀ = 1)
    (hres : cnlWindowTopStart ctx % 11 ≠ 5) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 :=
  fun hk => hres (class1Fibre_residue_of_datum_87_1 ctx hq hK hk).1

/-- `(q, K₀) = (87, 1)`, `r = 0`: the top start is not class-1 OR the two explicit pins hold
(residue hit `% 11 = 5` + the single hit-gap equation). -/
theorem class1_r0_top_verdict_of_datum_87_1 (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0)
    (hq : (class1SlopeDatum ctx).q = 87) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
      ∨ (cnlWindowTopStart ctx % 11 = 5
          ∧ 64 * hitGap ctx.n24CarryData.a (cnlWindowTopStart ctx)
              = 129 * shellLadderDepth ctx + 64) := by
  by_cases hk : cnlWindowTopStart ctx
      ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
  · exact Or.inr ⟨(class1Fibre_residue_of_datum_87_1 ctx hq hK hk).1,
      class1Fibre_r0_hitGap_pin ctx hr hk⟩
  · exact Or.inl hk

/-- `(q, K₀) = (87, 14)`: period `11`, cycle `25 → 13 → 17 → 49 → 11 → 1 → 41 → 77 → 67 → 47 → 7`, bands `2, 3, 3, 1, 3, 7, 2, 1, 1, 1, 4` — band-4 residue set `{11}` (values `7`), congruence class(es) `k % 11 ∈ {0}`. -/
private theorem cnlPairCycle_87_14 :
    slopeOrbit 87 14 (1 + 11) = slopeOrbit 87 14 1
      ∧ slopeOrbit 87 14 11 = 7
      ∧ ∀ j, 1 ≤ j → j ≤ 11 →
          canonGap 87 (slopeOrbit 87 14 j) = 4 → j ∈ ({11} : Finset ℕ) := by
  have e0 : slopeOrbit 87 14 0 = 14 := rfl
  have e1 : slopeOrbit 87 14 1 = 25 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 87 14 2 = 13 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 87 14 3 = 17 :=
    slopeOrbit_step_eval 2 2 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 87 14 4 = 49 :=
    slopeOrbit_step_eval 3 2 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 87 14 5 = 11 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 87 14 6 = 1 :=
    slopeOrbit_step_eval 5 2 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 87 14 7 = 41 :=
    slopeOrbit_step_eval 6 6 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 87 14 8 = 77 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 87 14 9 = 67 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 87 14 10 = 47 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 87 14 11 = 7 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 87 14 12 = 25 :=
    slopeOrbit_step_eval 11 3 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, e11, ?_⟩
  · show slopeOrbit 87 14 12 = slopeOrbit 87 14 1
    rw [e12, e1]
  · intro j hj1 hjc hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide

private theorem cnlPairResidue_87_14 {k : ℕ} (hk1 : 1 ≤ k)
    (hband : canonGap 87 (slopeOrbit 87 14 k) = 4) :
    k % 11 = 0 ∧ slopeOrbit 87 14 k = 7 := by
  have hper := slopeOrbit_period_of_return cnlPairCycle_87_14.1
  have hres := slopeOrbit_eq_residue (by norm_num) hper hk1
  have hmod : (k - 1) % 11 < 11 := Nat.mod_lt _ (by norm_num)
  have hmem := cnlPairCycle_87_14.2.2 ((k - 1) % 11 + 1) (by omega) (by omega)
    (by rw [← hres]; exact hband)
  have hj4 := Finset.mem_singleton.mp hmem
  refine ⟨by omega, ?_⟩
  rw [hres, hj4]
  exact cnlPairCycle_87_14.2.1

/-- `(q, K₀) = (87, 14)`: every class-1 start satisfies the explicit congruence `k % 11 = 0`
and carries the unique band-4 orbit value `7`. -/
theorem class1Fibre_residue_of_datum_87_14 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 87) (hK : (class1SlopeDatum ctx).K₀ = 14)
    {k : ℕ} (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1) :
    k % 11 = 0
      ∧ slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k = 7 := by
  have hband := class1Fibre_canonGap_eq ctx hk
  have hk1 := class1Fibre_start_pos ctx hk
  rw [hq, hK] at hband
  have h := cnlPairResidue_87_14 hk1 hband
  refine ⟨h.1, ?_⟩
  rw [hq, hK]
  exact h.2

/-- `(q, K₀) = (87, 14)`: AT MOST ONE class-1 member per residue window — `#fibre₁ ≤ ⌈W/11⌉`. -/
theorem class1Fibre_card_le_of_datum_87_14 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 87) (hK : (class1SlopeDatum ctx).K₀ = 14) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card + 11 - 1) / 11 := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 11)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return cnlPairCycle_87_14.1
  have hcount : (class1Band4CycleBand ctx 11).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset cnlPairCycle_87_14.2.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 11).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 11 - 1) / 11) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 11 - 1) / 11) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)
    _ = ((supportShell ctx.shell.d ctx.shell.X).card + 11 - 1) / 11 :=
        Nat.one_mul _

/-- `(q, K₀) = (87, 14)`: any two class-1 members are congruent mod `11`, satisfy the concrete
hit-gap repeat equation, and their spacing is a full orbit period. -/
theorem class1Fibre_pair_rigidity_of_datum_87_14 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 87) (hK : (class1SlopeDatum ctx).K₀ = 14)
    {k k' : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hk' : k' ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hlt : k < k') :
    k % 11 = k' % 11
      ∧ ctx.n24CarryData.a (k + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k'
          = ctx.n24CarryData.a (k' + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k
      ∧ (∀ m, 1 ≤ m →
          slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + (k' - k))
            = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m) := by
  have h1 := class1Fibre_residue_of_datum_87_14 ctx hq hK hk
  have h2 := class1Fibre_residue_of_datum_87_14 ctx hq hK hk'
  exact ⟨by omega, class1Fibre_span_rigidity ctx hk hk',
    class1Fibre_spacing_period ctx hk hk' hlt (h1.2.trans h2.2.symm)⟩

/-- `(q, K₀) = (87, 14)`: a top start whose residue misses `0` mod `11` is NOT class-1
(every `r`, in particular `r = 0`). -/
theorem class1Fibre_top_notMem_of_residue_87_14 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 87) (hK : (class1SlopeDatum ctx).K₀ = 14)
    (hres : cnlWindowTopStart ctx % 11 ≠ 0) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 :=
  fun hk => hres (class1Fibre_residue_of_datum_87_14 ctx hq hK hk).1

/-- `(q, K₀) = (87, 14)`, `r = 0`: the top start is not class-1 OR the two explicit pins hold
(residue hit `% 11 = 0` + the single hit-gap equation). -/
theorem class1_r0_top_verdict_of_datum_87_14 (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0)
    (hq : (class1SlopeDatum ctx).q = 87) (hK : (class1SlopeDatum ctx).K₀ = 14) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
      ∨ (cnlWindowTopStart ctx % 11 = 0
          ∧ 64 * hitGap ctx.n24CarryData.a (cnlWindowTopStart ctx)
              = 129 * shellLadderDepth ctx + 64) := by
  by_cases hk : cnlWindowTopStart ctx
      ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
  · exact Or.inr ⟨(class1Fibre_residue_of_datum_87_14 ctx hq hK hk).1,
      class1Fibre_r0_hitGap_pin ctx hr hk⟩
  · exact Or.inl hk

/-- `(q, K₀) = (99, 5)`: period `15`, cycle `61 → 23 → 85 → 71 → 43 → 73 → 47 → 89 → 79 → 59 → 19 → 53 → 7 → 13 → 5`, bands `1, 3, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 4, 3, 5` — band-4 residue set `{13}` (values `7`), congruence class(es) `k % 15 ∈ {13}`. -/
private theorem cnlPairCycle_99_5 :
    slopeOrbit 99 5 (1 + 15) = slopeOrbit 99 5 1
      ∧ slopeOrbit 99 5 13 = 7
      ∧ ∀ j, 1 ≤ j → j ≤ 15 →
          canonGap 99 (slopeOrbit 99 5 j) = 4 → j ∈ ({13} : Finset ℕ) := by
  have e0 : slopeOrbit 99 5 0 = 5 := rfl
  have e1 : slopeOrbit 99 5 1 = 61 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 99 5 2 = 23 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 99 5 3 = 85 :=
    slopeOrbit_step_eval 2 2 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 99 5 4 = 71 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 99 5 5 = 43 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 99 5 6 = 73 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 99 5 7 = 47 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 99 5 8 = 89 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 99 5 9 = 79 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 99 5 10 = 59 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 99 5 11 = 19 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 99 5 12 = 53 :=
    slopeOrbit_step_eval 11 2 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 99 5 13 = 7 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 99 5 14 = 13 :=
    slopeOrbit_step_eval 13 3 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 99 5 15 = 5 :=
    slopeOrbit_step_eval 14 2 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 99 5 16 = 61 :=
    slopeOrbit_step_eval 15 4 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, e13, ?_⟩
  · show slopeOrbit 99 5 16 = slopeOrbit 99 5 1
    rw [e16, e1]
  · intro j hj1 hjc hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · decide
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

private theorem cnlPairResidue_99_5 {k : ℕ} (hk1 : 1 ≤ k)
    (hband : canonGap 99 (slopeOrbit 99 5 k) = 4) :
    k % 15 = 13 ∧ slopeOrbit 99 5 k = 7 := by
  have hper := slopeOrbit_period_of_return cnlPairCycle_99_5.1
  have hres := slopeOrbit_eq_residue (by norm_num) hper hk1
  have hmod : (k - 1) % 15 < 15 := Nat.mod_lt _ (by norm_num)
  have hmem := cnlPairCycle_99_5.2.2 ((k - 1) % 15 + 1) (by omega) (by omega)
    (by rw [← hres]; exact hband)
  have hj4 := Finset.mem_singleton.mp hmem
  refine ⟨by omega, ?_⟩
  rw [hres, hj4]
  exact cnlPairCycle_99_5.2.1

/-- `(q, K₀) = (99, 5)`: every class-1 start satisfies the explicit congruence `k % 15 = 13`
and carries the unique band-4 orbit value `7`. -/
theorem class1Fibre_residue_of_datum_99_5 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 99) (hK : (class1SlopeDatum ctx).K₀ = 5)
    {k : ℕ} (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1) :
    k % 15 = 13
      ∧ slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k = 7 := by
  have hband := class1Fibre_canonGap_eq ctx hk
  have hk1 := class1Fibre_start_pos ctx hk
  rw [hq, hK] at hband
  have h := cnlPairResidue_99_5 hk1 hband
  refine ⟨h.1, ?_⟩
  rw [hq, hK]
  exact h.2

/-- `(q, K₀) = (99, 5)`: AT MOST ONE class-1 member per residue window — `#fibre₁ ≤ ⌈W/15⌉`. -/
theorem class1Fibre_card_le_of_datum_99_5 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 99) (hK : (class1SlopeDatum ctx).K₀ = 5) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card + 15 - 1) / 15 := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 15)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return cnlPairCycle_99_5.1
  have hcount : (class1Band4CycleBand ctx 15).card ≤ 1 := by
    rw [class1Band4CycleBand_congr ctx hq hK]
    exact band4_cycle_card_le_of_subset cnlPairCycle_99_5.2.2 (by decide)
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx 15).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + 15 - 1) / 15) :=
        class1Fibre_card_le_cycleDensity ctx (by norm_num) hper
    _ ≤ 1 * (((supportShell ctx.shell.d ctx.shell.X).card + 15 - 1) / 15) :=
        Nat.mul_le_mul hcount (Nat.le_refl _)
    _ = ((supportShell ctx.shell.d ctx.shell.X).card + 15 - 1) / 15 :=
        Nat.one_mul _

/-- `(q, K₀) = (99, 5)`: any two class-1 members are congruent mod `15`, satisfy the concrete
hit-gap repeat equation, and their spacing is a full orbit period. -/
theorem class1Fibre_pair_rigidity_of_datum_99_5 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 99) (hK : (class1SlopeDatum ctx).K₀ = 5)
    {k k' : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hk' : k' ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hlt : k < k') :
    k % 15 = k' % 15
      ∧ ctx.n24CarryData.a (k + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k'
          = ctx.n24CarryData.a (k' + ctx.n24CarryData.r + 1) + ctx.n24CarryData.a k
      ∧ (∀ m, 1 ≤ m →
          slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + (k' - k))
            = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m) := by
  have h1 := class1Fibre_residue_of_datum_99_5 ctx hq hK hk
  have h2 := class1Fibre_residue_of_datum_99_5 ctx hq hK hk'
  exact ⟨by omega, class1Fibre_span_rigidity ctx hk hk',
    class1Fibre_spacing_period ctx hk hk' hlt (h1.2.trans h2.2.symm)⟩

/-- `(q, K₀) = (99, 5)`: a top start whose residue misses `13` mod `15` is NOT class-1
(every `r`, in particular `r = 0`). -/
theorem class1Fibre_top_notMem_of_residue_99_5 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 99) (hK : (class1SlopeDatum ctx).K₀ = 5)
    (hres : cnlWindowTopStart ctx % 15 ≠ 13) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 :=
  fun hk => hres (class1Fibre_residue_of_datum_99_5 ctx hq hK hk).1

/-- `(q, K₀) = (99, 5)`, `r = 0`: the top start is not class-1 OR the two explicit pins hold
(residue hit `% 15 = 13` + the single hit-gap equation). -/
theorem class1_r0_top_verdict_of_datum_99_5 (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0)
    (hq : (class1SlopeDatum ctx).q = 99) (hK : (class1SlopeDatum ctx).K₀ = 5) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
      ∨ (cnlWindowTopStart ctx % 15 = 13
          ∧ 64 * hitGap ctx.n24CarryData.a (cnlWindowTopStart ctx)
              = 129 * shellLadderDepth ctx + 64) := by
  by_cases hk : cnlWindowTopStart ctx
      ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
  · exact Or.inr ⟨(class1Fibre_residue_of_datum_99_5 ctx hq hK hk).1,
      class1Fibre_r0_hitGap_pin ctx hr hk⟩
  · exact Or.inl hk

/-! ## Part 5.  The aggregate top-residue-miss predicate and the successor residual -/

/-- **The top-residue-miss predicate**: the datum is one of the twenty-three open
band-4 pairs AND the computable top residue misses the pair's band-4 congruence
class(es) — an explicitly checkable per-shell condition that excludes the top
start from the class-1 fibre. -/
def Class1PairTopMiss (ctx : ActualFailureContext) : Prop :=
  ((class1SlopeDatum ctx).q = 25 ∧ (class1SlopeDatum ctx).K₀ = 2
        ∧ cnlWindowTopStart ctx % 10 ≠ 2)
    ∨ ((class1SlopeDatum ctx).q = 25 ∧ (class1SlopeDatum ctx).K₀ = 12
        ∧ cnlWindowTopStart ctx % 10 ≠ 0)
    ∨ ((class1SlopeDatum ctx).q = 29 ∧ (class1SlopeDatum ctx).K₀ = 14
        ∧ cnlWindowTopStart ctx % 14 ≠ 11)
    ∨ ((class1SlopeDatum ctx).q = 35 ∧ (class1SlopeDatum ctx).K₀ = 3
        ∧ cnlWindowTopStart ctx % 7 ≠ 0)
    ∨ ((class1SlopeDatum ctx).q = 35 ∧ (class1SlopeDatum ctx).K₀ = 17
        ∧ cnlWindowTopStart ctx % 7 ≠ 5)
    ∨ ((class1SlopeDatum ctx).q = 37 ∧ (class1SlopeDatum ctx).K₀ = 18
        ∧ cnlWindowTopStart ctx % 18 ≠ 6)
    ∨ ((class1SlopeDatum ctx).q = 39 ∧ (class1SlopeDatum ctx).K₀ = 6
        ∧ cnlWindowTopStart ctx % 6 ≠ 0)
    ∨ ((class1SlopeDatum ctx).q = 41 ∧ (class1SlopeDatum ctx).K₀ = 20
        ∧ cnlWindowTopStart ctx % 10 ≠ 0)
    ∨ ((class1SlopeDatum ctx).q = 47 ∧ (class1SlopeDatum ctx).K₀ = 23
        ∧ cnlWindowTopStart ctx % 14 ≠ 7)
    ∨ ((class1SlopeDatum ctx).q = 49 ∧ (class1SlopeDatum ctx).K₀ = 3
        ∧ cnlWindowTopStart ctx % 11 ≠ 8)
    ∨ ((class1SlopeDatum ctx).q = 49 ∧ (class1SlopeDatum ctx).K₀ = 24
        ∧ cnlWindowTopStart ctx % 11 ≠ 8)
    ∨ ((class1SlopeDatum ctx).q = 55 ∧ (class1SlopeDatum ctx).K₀ = 5
        ∧ cnlWindowTopStart ctx % 5 ≠ 0)
    ∨ ((class1SlopeDatum ctx).q = 57 ∧ (class1SlopeDatum ctx).K₀ = 1
        ∧ cnlWindowTopStart ctx % 9 ≠ 1)
    ∨ ((class1SlopeDatum ctx).q = 57 ∧ (class1SlopeDatum ctx).K₀ = 28
        ∧ cnlWindowTopStart ctx % 9 ≠ 0)
    ∨ ((class1SlopeDatum ctx).q = 63 ∧ (class1SlopeDatum ctx).K₀ = 10
        ∧ cnlWindowTopStart ctx % 2 ≠ 0)
    ∨ ((class1SlopeDatum ctx).q = 69 ∧ (class1SlopeDatum ctx).K₀ = 11
        ∧ cnlWindowTopStart ctx % 11 ≠ 2 ∧ cnlWindowTopStart ctx % 11 ≠ 10)
    ∨ ((class1SlopeDatum ctx).q = 69 ∧ (class1SlopeDatum ctx).K₀ = 34
        ∧ cnlWindowTopStart ctx % 11 ≠ 6 ∧ cnlWindowTopStart ctx % 11 ≠ 9)
    ∨ ((class1SlopeDatum ctx).q = 75 ∧ (class1SlopeDatum ctx).K₀ = 7
        ∧ cnlWindowTopStart ctx % 11 ≠ 0)
    ∨ ((class1SlopeDatum ctx).q = 75 ∧ (class1SlopeDatum ctx).K₀ = 12
        ∧ cnlWindowTopStart ctx % 10 ≠ 2)
    ∨ ((class1SlopeDatum ctx).q = 75 ∧ (class1SlopeDatum ctx).K₀ = 37
        ∧ cnlWindowTopStart ctx % 11 ≠ 10)
    ∨ ((class1SlopeDatum ctx).q = 87 ∧ (class1SlopeDatum ctx).K₀ = 1
        ∧ cnlWindowTopStart ctx % 11 ≠ 5)
    ∨ ((class1SlopeDatum ctx).q = 87 ∧ (class1SlopeDatum ctx).K₀ = 14
        ∧ cnlWindowTopStart ctx % 11 ≠ 0)
    ∨ ((class1SlopeDatum ctx).q = 99 ∧ (class1SlopeDatum ctx).K₀ = 5
        ∧ cnlWindowTopStart ctx % 15 ≠ 13)

/-- Top-residue-miss excludes the top start (dispatching the twenty-three per-pair
residue closers). -/
theorem class1Fibre_top_notMem_of_pairTopMiss (ctx : ActualFailureContext)
    (h : Class1PairTopMiss ctx) :
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 := by
  rcases h with ⟨hq, hK, hres⟩ | ⟨hq, hK, hres⟩ | ⟨hq, hK, hres⟩ | ⟨hq, hK, hres⟩ | ⟨hq, hK, hres⟩ | ⟨hq, hK, hres⟩ | ⟨hq, hK, hres⟩ | ⟨hq, hK, hres⟩ | ⟨hq, hK, hres⟩ | ⟨hq, hK, hres⟩ | ⟨hq, hK, hres⟩ | ⟨hq, hK, hres⟩ | ⟨hq, hK, hres⟩ | ⟨hq, hK, hres⟩ | ⟨hq, hK, hres⟩ | ⟨hq, hK, hres1, hres2⟩ | ⟨hq, hK, hres1, hres2⟩ | ⟨hq, hK, hres⟩ | ⟨hq, hK, hres⟩ | ⟨hq, hK, hres⟩ | ⟨hq, hK, hres⟩ | ⟨hq, hK, hres⟩ | ⟨hq, hK, hres⟩
  · exact class1Fibre_top_notMem_of_residue_25_2 ctx hq hK hres
  · exact class1Fibre_top_notMem_of_residue_25_12 ctx hq hK hres
  · exact class1Fibre_top_notMem_of_residue_29_14 ctx hq hK hres
  · exact class1Fibre_top_notMem_of_residue_35_3 ctx hq hK hres
  · exact class1Fibre_top_notMem_of_residue_35_17 ctx hq hK hres
  · exact class1Fibre_top_notMem_of_residue_37_18 ctx hq hK hres
  · exact class1Fibre_top_notMem_of_residue_39_6 ctx hq hK hres
  · exact class1Fibre_top_notMem_of_residue_41_20 ctx hq hK hres
  · exact class1Fibre_top_notMem_of_residue_47_23 ctx hq hK hres
  · exact class1Fibre_top_notMem_of_residue_49_3 ctx hq hK hres
  · exact class1Fibre_top_notMem_of_residue_49_24 ctx hq hK hres
  · exact class1Fibre_top_notMem_of_residue_55_5 ctx hq hK hres
  · exact class1Fibre_top_notMem_of_residue_57_1 ctx hq hK hres
  · exact class1Fibre_top_notMem_of_residue_57_28 ctx hq hK hres
  · exact class1Fibre_top_notMem_of_residue_63_10 ctx hq hK hres
  · exact class1Fibre_top_notMem_of_residue_69_11 ctx hq hK hres1 hres2
  · exact class1Fibre_top_notMem_of_residue_69_34 ctx hq hK hres1 hres2
  · exact class1Fibre_top_notMem_of_residue_75_7 ctx hq hK hres
  · exact class1Fibre_top_notMem_of_residue_75_12 ctx hq hK hres
  · exact class1Fibre_top_notMem_of_residue_75_37 ctx hq hK hres
  · exact class1Fibre_top_notMem_of_residue_87_1 ctx hq hK hres
  · exact class1Fibre_top_notMem_of_residue_87_14 ctx hq hK hres
  · exact class1Fibre_top_notMem_of_residue_99_5 ctx hq hK hres

/-- **The strictly smaller class-1 pair residual.**  The SAME two fields as
`Class1DatumResidual`, each additionally relieved of the gcd-window-miss shells (closed
by `class1Fibre_empty_of_gcd_window_miss`), and the `r = 0` field additionally relieved
of the top-residue-miss shells (closed by `class1Fibre_top_notMem_of_pairTopMiss`).
Hence `Class1PairResidual` demands strictly less than `Class1DatumResidual`. -/
structure Class1PairResidual : Prop where
  /-- `r = 0` shells with a not-yet-closed datum, top residue ON the band-4 congruence
  class(es), and a gcd-reachable band-4 window: the top window start is not class-1. -/
  topStart : ∀ ctx : ActualFailureContext,
    ctx.n24CarryData.r = 0 →
    64 ∣ shellLadderDepth ctx →
    9 ≤ (class1SlopeDatum ctx).q →
    ((class1SlopeDatum ctx).q ≤ 15 ∨ 25 ≤ (class1SlopeDatum ctx).q) →
    (class1SlopeDatum ctx).q ∉ class1ClosedModuli →
    ¬ Class1DatumClosed ctx →
    ¬ Class1PairTopMiss ctx →
    ¬ Class1GcdWindowMiss ctx →
    cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1
  /-- Deep shells (`r ≥ 1`) with a not-yet-closed datum and a gcd-reachable band-4
  window: emptiness on the survivors. -/
  deep : ∀ ctx : ActualFailureContext,
    1 ≤ ctx.n24CarryData.r →
    64 ∣ shellLadderDepth ctx →
    9 ≤ (class1SlopeDatum ctx).q →
    ((class1SlopeDatum ctx).q ≤ 15 ∨ 25 ≤ (class1SlopeDatum ctx).q) →
    (class1SlopeDatum ctx).q ∉ class1ClosedModuli →
    ¬ Class1DatumClosed ctx →
    ¬ Class1GcdWindowMiss ctx →
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅

/-- **The bridge (additive)**: the pair residual rebuilds `Class1DatumResidual` — the
gcd-window-miss shells and the top-residue-miss shells are filled in unconditionally,
the rest is exactly the residual hypothesis. -/
theorem class1DatumResidual_of_pairResidual (R : Class1PairResidual) :
    Class1DatumResidual := by
  refine ⟨fun ctx hr hdvd h9 hwin hcl hdc => ?_, fun ctx hr hdvd h9 hwin hcl hdc => ?_⟩
  · by_cases hgcd : Class1GcdWindowMiss ctx
    · rw [class1Fibre_empty_of_gcd_window_miss ctx hgcd]
      exact Finset.notMem_empty _
    · by_cases htm : Class1PairTopMiss ctx
      · exact class1Fibre_top_notMem_of_pairTopMiss ctx htm
      · exact R.topStart ctx hr hdvd h9 hwin hcl hdc htm hgcd
  · by_cases hgcd : Class1GcdWindowMiss ctx
    · exact class1Fibre_empty_of_gcd_window_miss ctx hgcd
    · exact R.deep ctx hr hdvd h9 hwin hcl hdc hgcd

/-- The datum residual trivially provides the pair residual (the extra hypotheses are
dropped), so `Class1PairResidual` is logically no stronger — and strictly weaker,
witnessed by the gcd-window and top-residue-miss closures. -/
theorem class1PairResidual_of_datumResidual (R : Class1DatumResidual) :
    Class1PairResidual :=
  ⟨fun ctx hr hdvd h9 hwin hcl hdc _ _ => R.topStart ctx hr hdvd h9 hwin hcl hdc,
   fun ctx hr hdvd h9 hwin hcl hdc _ => R.deep ctx hr hdvd h9 hwin hcl hdc⟩

/-- **The wave-3 bridge, through `class1DeepResidual_of_datumResidual`**: the pair
residual rebuilds the full `Class1DeepResidual`. -/
theorem class1DeepResidual_of_pairResidual (R : Class1PairResidual) :
    Class1DeepResidual :=
  class1DeepResidual_of_datumResidual (class1DatumResidual_of_pairResidual R)

/-- **The capstone discharge**: the pair residual produces EXACTLY the capstone field
`class1Pinned` (same statement, same hypotheses). -/
theorem class1Pinned_of_pairResidual (R : Class1PairResidual) :
    ∀ ctx : ActualFailureContext, ∀ k ∈ ctx.n24CarryData.starts,
      1 ≤ k →
      64 ∣ shellLadderDepth ctx →
      9 ≤ (class1SlopeDatum ctx).q →
      ((class1SlopeDatum ctx).q ≤ 15 ∨ 25 ≤ (class1SlopeDatum ctx).q) →
      Odd (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) →
      64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
          = 129 * shellLadderDepth ctx + 64 →
      canonGap (class1SlopeDatum ctx).q
          (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) ≠ 4 :=
  class1Pinned_of_datumResidual (class1DatumResidual_of_pairResidual R)

/-- **The full-chain entry**: the pair residual closes the v3 clean-CNL atom through the
existing wave-2 sharp pinned-arithmetic bridge. -/
theorem class1FibreEmpty_of_pairResidual
    (towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (runChain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx)
    (returnCharge : ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx)
    (R : Class1PairResidual) :
    Class1FibreEmpty (v3Budget towerCount runChain returnCharge) :=
  class1FibreEmpty_of_datumResidual towerCount runChain returnCharge
    (class1DatumResidual_of_pairResidual R)

/-! ## Part 6.  Honest status -/

/-- Machine-readable status of the CNL / class-1 pair closure. -/
def cnlClass1PairClosureStatus : List String :=
  [ "TARGET (consumer): Class1DatumResidual (CNLClass1DatumClosure) - its open data " ++
      "are the divisor-pin pairs whose orbits READ band 4 (canonGap = 4, the window " ++
      "8K <= q < 16K): 25@{2,12}, 29@14, 37@18, 41@20, 47@23, 49@{3,24}, 35@{3,17}, " ++
      "39@6, 55@5, 57@{1,28}, 63@10, 69@{11,34}, 75@{7,12,37}, 87@{1,14}, 99@5 " ++
      "(twenty-three pairs), plus the un-enumerated q >= 101.",
    "ENGINE (cycle-density count, NEW): class1Band4CycleBand (band-4 residues of one " ++
      "period) and class1Fibre_card_le_cycleDensity - #fibre1 <= #band4residues * " ++
      "ceil(W/c) by the residue x block injection (the class-1 mirror of the proved " ++
      "class-5/class-2 counts); existential form at some c <= q " ++
      "(class1Fibre_card_le_cycleDensity_exists).",
    "PER-PAIR RESIDUE CONGRUENCES (23 pairs, NEW): twenty-one cycles carry EXACTLY " ++
      "ONE band-4 residue j4, so class-1 membership forces the explicit congruence " ++
      "k % c = j4 % c AND the orbit-value pin K_k = v4; the two q = 69 cycles carry " ++
      "exactly TWO residues, giving the explicit two-class disjunction " ++
      "(class1Fibre_residue_of_datum_*, transported by slopeOrbit_eq_residue along " ++
      "the certified period - the class1Fibre_residue_pin pattern with minimality " ++
      "replaced by the certified residue table). Table: (25,2) c=10 rho=2 v4=3; " ++
      "(25,12) c=10 rho=0 v4=3; (29,14) c=14 rho=11 v4=3; (35,3) c=7 rho=0 v4=3; " ++
      "(35,17) c=7 rho=5 v4=3; (37,18) c=18 rho=6 v4=3; (39,6) c=6 rho=0 v4=3; " ++
      "(41,20) c=10 rho=0 v4=5; (47,23) c=14 rho=7 v4=5; (49,3) c=11 rho=8 v4=5; " ++
      "(49,24) c=11 rho=8 v4=5; (55,5) c=5 rho=0 v4=5; (57,1) c=9 rho=1 v4=7; " ++
      "(57,28) c=9 rho=0 v4=7; (63,10) c=2 rho=0 v4=5; (69,11) c=11 rho=2/10 " ++
      "v4=7/5; (69,34) c=11 rho=6/9 v4=5/7; (75,7) c=11 rho=0 v4=7; (75,12) c=10 " ++
      "rho=2 v4=9; (75,37) c=11 rho=10 v4=7; (87,1) c=11 rho=5 v4=7; (87,14) c=11 " ++
      "rho=0 v4=7; (99,5) c=15 rho=13 v4=7.",
    "PER-PAIR COUNT BOUNDS (23 pairs, NEW): #fibre1 <= ceil(W/c) on the twenty-one " ++
      "one-residue pairs and <= 2*ceil(W/c) on the q = 69 pairs - AT MOST ONE member " ++
      "per band-4 residue per window (class1Fibre_card_le_of_datum_*, via " ++
      "band4_cycle_card_le_of_subset).",
    "PER-PAIR RIGIDITY (23 pairs, NEW): two class-1 members (same residue class when " ++
      "b4 = 2) carry EQUAL orbit numerators, satisfy the concrete hit-gap repeat " ++
      "equation a(k+r+1) + a(k') = a(k'+r+1) + a(k) (class1Fibre_span_rigidity), and " ++
      "their spacing is a FULL orbit period (class1Fibre_spacing_period) " ++
      "(class1Fibre_pair_rigidity_of_datum_*).",
    "R = 0 TOP-START DICHOTOMY (23 pairs, NEW): top residue misses the band-4 " ++
      "class(es) => top start NOT class-1, for EVERY r " ++
      "(class1Fibre_top_notMem_of_residue_*, aggregated by Class1PairTopMiss / " ++
      "class1Fibre_top_notMem_of_pairTopMiss); otherwise the r = 0 demand is ONE " ++
      "explicit hit-gap disequality 64*hitGap(top) != 129L+64 " ++
      "(class1_r0_top_verdict_of_datum_*, class1Fibre_r0_top_notMem_of_hitGap via " ++
      "class1Fibre_r0_hitGap_pin / class1Fibre_r0_top_band4).",
    "GENERAL q >= 101 CRITERIA (gcd suite, NEW - mirrors " ++
      "datum_gcd_floor_forces_K_le_seven): gcd(q,K0) divides every orbit value " ++
      "(slopeOrbit_gcd_dvd, E.13-step invariance); a gcd-multiple-free band-4 window " ++
      "empties the fibre (Class1GcdWindowMiss, class1Fibre_empty_of_gcd_window_miss) " ++
      "- valid for EVERY modulus; numeric form q < 8*gcd " ++
      "(class1Fibre_empty_of_eight_mul_gcd_gt); at q < 16*gcd the orbit value is " ++
      "pinned to gcd itself (class1Fibre_orbit_eq_gcd_of_window) and the lever is " ++
      "confined to K0 <= 7 (class1_gcd_window_K0_le_seven).",
    "SUCCESSOR (strictly smaller, NEW): Class1PairResidual - the Class1DatumResidual " ++
      "fields additionally relieved of gcd-window-miss shells (both fields) and " ++
      "top-residue-miss shells (r = 0 field). Bridges: " ++
      "class1DatumResidual_of_pairResidual (additive), " ++
      "class1DeepResidual_of_pairResidual (through " ++
      "class1DeepResidual_of_datumResidual), capstone discharges " ++
      "class1Pinned_of_pairResidual / class1FibreEmpty_of_pairResidual; weakening " ++
      "witness class1PairResidual_of_datumResidual.",
    "HONEST RESIDUAL: no open pair is closed outright - each cycle DOES read band 4, " ++
      "so the orbit side cannot refute membership; what remains per pair is the " ++
      "digit-side question at the certified congruence class(es) mod c (deep) and " ++
      "ONE hit-gap equation (r = 0). The gcd criteria fire only off the 23 pairs " ++
      "(their gcds are 1 or small with q >= 8*gcd). No degenerate witness is " ++
      "fabricated.",
    "NO sorry / admit / new axiom / native_decide; per-pair tables are pure numeral " ++
      "arithmetic (slopeOrbit_step_eval, no Nat.log evaluation); audit block at file " ++
      "end." ]

theorem cnlClass1PairClosureStatus_nonempty : cnlClass1PairClosureStatus ≠ [] := by
  simp [cnlClass1PairClosureStatus]

/-! ## Part 7.  Axiom audit -/

#print axioms class1Band4CycleBand
#print axioms mem_class1Band4CycleBand
#print axioms class1Band4CycleBand_congr
#print axioms class1Fibre_card_le_cycleDensity
#print axioms class1Fibre_card_le_cycleDensity_exists
#print axioms band4_cycle_card_le_of_subset
#print axioms slopeOrbit_gcd_dvd
#print axioms Class1GcdWindowMiss
#print axioms class1Fibre_empty_of_gcd_window_miss
#print axioms class1Fibre_empty_of_eight_mul_gcd_gt
#print axioms class1Fibre_orbit_eq_gcd_of_window
#print axioms class1_gcd_window_K₀_le_seven
#print axioms class1Fibre_r0_top_notMem_of_hitGap
#print axioms Class1PairTopMiss
#print axioms class1Fibre_top_notMem_of_pairTopMiss
#print axioms Class1PairResidual
#print axioms class1DatumResidual_of_pairResidual
#print axioms class1PairResidual_of_datumResidual
#print axioms class1DeepResidual_of_pairResidual
#print axioms class1Pinned_of_pairResidual
#print axioms class1FibreEmpty_of_pairResidual
#print axioms cnlClass1PairClosureStatus_nonempty
#print axioms class1Fibre_residue_of_datum_25_2
#print axioms class1Fibre_card_le_of_datum_25_2
#print axioms class1Fibre_pair_rigidity_of_datum_25_2
#print axioms class1Fibre_top_notMem_of_residue_25_2
#print axioms class1_r0_top_verdict_of_datum_25_2
#print axioms class1Fibre_residue_of_datum_25_12
#print axioms class1Fibre_card_le_of_datum_25_12
#print axioms class1Fibre_pair_rigidity_of_datum_25_12
#print axioms class1Fibre_top_notMem_of_residue_25_12
#print axioms class1_r0_top_verdict_of_datum_25_12
#print axioms class1Fibre_residue_of_datum_29_14
#print axioms class1Fibre_card_le_of_datum_29_14
#print axioms class1Fibre_pair_rigidity_of_datum_29_14
#print axioms class1Fibre_top_notMem_of_residue_29_14
#print axioms class1_r0_top_verdict_of_datum_29_14
#print axioms class1Fibre_residue_of_datum_35_3
#print axioms class1Fibre_card_le_of_datum_35_3
#print axioms class1Fibre_pair_rigidity_of_datum_35_3
#print axioms class1Fibre_top_notMem_of_residue_35_3
#print axioms class1_r0_top_verdict_of_datum_35_3
#print axioms class1Fibre_residue_of_datum_35_17
#print axioms class1Fibre_card_le_of_datum_35_17
#print axioms class1Fibre_pair_rigidity_of_datum_35_17
#print axioms class1Fibre_top_notMem_of_residue_35_17
#print axioms class1_r0_top_verdict_of_datum_35_17
#print axioms class1Fibre_residue_of_datum_37_18
#print axioms class1Fibre_card_le_of_datum_37_18
#print axioms class1Fibre_pair_rigidity_of_datum_37_18
#print axioms class1Fibre_top_notMem_of_residue_37_18
#print axioms class1_r0_top_verdict_of_datum_37_18
#print axioms class1Fibre_residue_of_datum_39_6
#print axioms class1Fibre_card_le_of_datum_39_6
#print axioms class1Fibre_pair_rigidity_of_datum_39_6
#print axioms class1Fibre_top_notMem_of_residue_39_6
#print axioms class1_r0_top_verdict_of_datum_39_6
#print axioms class1Fibre_residue_of_datum_41_20
#print axioms class1Fibre_card_le_of_datum_41_20
#print axioms class1Fibre_pair_rigidity_of_datum_41_20
#print axioms class1Fibre_top_notMem_of_residue_41_20
#print axioms class1_r0_top_verdict_of_datum_41_20
#print axioms class1Fibre_residue_of_datum_47_23
#print axioms class1Fibre_card_le_of_datum_47_23
#print axioms class1Fibre_pair_rigidity_of_datum_47_23
#print axioms class1Fibre_top_notMem_of_residue_47_23
#print axioms class1_r0_top_verdict_of_datum_47_23
#print axioms class1Fibre_residue_of_datum_49_3
#print axioms class1Fibre_card_le_of_datum_49_3
#print axioms class1Fibre_pair_rigidity_of_datum_49_3
#print axioms class1Fibre_top_notMem_of_residue_49_3
#print axioms class1_r0_top_verdict_of_datum_49_3
#print axioms class1Fibre_residue_of_datum_49_24
#print axioms class1Fibre_card_le_of_datum_49_24
#print axioms class1Fibre_pair_rigidity_of_datum_49_24
#print axioms class1Fibre_top_notMem_of_residue_49_24
#print axioms class1_r0_top_verdict_of_datum_49_24
#print axioms class1Fibre_residue_of_datum_55_5
#print axioms class1Fibre_card_le_of_datum_55_5
#print axioms class1Fibre_pair_rigidity_of_datum_55_5
#print axioms class1Fibre_top_notMem_of_residue_55_5
#print axioms class1_r0_top_verdict_of_datum_55_5
#print axioms class1Fibre_residue_of_datum_57_1
#print axioms class1Fibre_card_le_of_datum_57_1
#print axioms class1Fibre_pair_rigidity_of_datum_57_1
#print axioms class1Fibre_top_notMem_of_residue_57_1
#print axioms class1_r0_top_verdict_of_datum_57_1
#print axioms class1Fibre_residue_of_datum_57_28
#print axioms class1Fibre_card_le_of_datum_57_28
#print axioms class1Fibre_pair_rigidity_of_datum_57_28
#print axioms class1Fibre_top_notMem_of_residue_57_28
#print axioms class1_r0_top_verdict_of_datum_57_28
#print axioms class1Fibre_residue_of_datum_63_10
#print axioms class1Fibre_card_le_of_datum_63_10
#print axioms class1Fibre_pair_rigidity_of_datum_63_10
#print axioms class1Fibre_top_notMem_of_residue_63_10
#print axioms class1_r0_top_verdict_of_datum_63_10
#print axioms class1Fibre_residue_of_datum_69_11
#print axioms class1Fibre_card_le_of_datum_69_11
#print axioms class1Fibre_pair_rigidity_of_datum_69_11
#print axioms class1Fibre_top_notMem_of_residue_69_11
#print axioms class1_r0_top_verdict_of_datum_69_11
#print axioms class1Fibre_residue_of_datum_69_34
#print axioms class1Fibre_card_le_of_datum_69_34
#print axioms class1Fibre_pair_rigidity_of_datum_69_34
#print axioms class1Fibre_top_notMem_of_residue_69_34
#print axioms class1_r0_top_verdict_of_datum_69_34
#print axioms class1Fibre_residue_of_datum_75_7
#print axioms class1Fibre_card_le_of_datum_75_7
#print axioms class1Fibre_pair_rigidity_of_datum_75_7
#print axioms class1Fibre_top_notMem_of_residue_75_7
#print axioms class1_r0_top_verdict_of_datum_75_7
#print axioms class1Fibre_residue_of_datum_75_12
#print axioms class1Fibre_card_le_of_datum_75_12
#print axioms class1Fibre_pair_rigidity_of_datum_75_12
#print axioms class1Fibre_top_notMem_of_residue_75_12
#print axioms class1_r0_top_verdict_of_datum_75_12
#print axioms class1Fibre_residue_of_datum_75_37
#print axioms class1Fibre_card_le_of_datum_75_37
#print axioms class1Fibre_pair_rigidity_of_datum_75_37
#print axioms class1Fibre_top_notMem_of_residue_75_37
#print axioms class1_r0_top_verdict_of_datum_75_37
#print axioms class1Fibre_residue_of_datum_87_1
#print axioms class1Fibre_card_le_of_datum_87_1
#print axioms class1Fibre_pair_rigidity_of_datum_87_1
#print axioms class1Fibre_top_notMem_of_residue_87_1
#print axioms class1_r0_top_verdict_of_datum_87_1
#print axioms class1Fibre_residue_of_datum_87_14
#print axioms class1Fibre_card_le_of_datum_87_14
#print axioms class1Fibre_pair_rigidity_of_datum_87_14
#print axioms class1Fibre_top_notMem_of_residue_87_14
#print axioms class1_r0_top_verdict_of_datum_87_14
#print axioms class1Fibre_residue_of_datum_99_5
#print axioms class1Fibre_card_le_of_datum_99_5
#print axioms class1Fibre_pair_rigidity_of_datum_99_5
#print axioms class1Fibre_top_notMem_of_residue_99_5
#print axioms class1_r0_top_verdict_of_datum_99_5

end

end Erdos260
