import Erdos260.Erdos260SplitCapstone
import Erdos260.CNLClass1PairClosure

/-!
# Parity-residue closure — member parity from the band-2 cycle pins

This module (NEW; it edits no existing file) closes parts of the wave-11 digit-core
counting clauses (`QOddResetClosure.lean`) via POSITION PARITY of the class-4 fibre
members, read off the band-2 residue tables of `ReturnSpanGateClosure.lean`.

## 1.  The parity transfer (goal 1)

Every class-4 fibre member `k` reads band 2 at its cycle representative
(`olcFibre_cycleRep_band2`), i.e. `cycleRep c k` lies in the band-2 residue set of
one orbit period.  Since `cycleRep c k ≡ k (mod c)`, an EVEN period `c` transfers
residue parity to member parity: if every band-2 residue `j ∈ [1, c]` has
`j % 2 = p`, then every member has `k % 2 = p`
(`olcFibre_parity_of_band2_parity`).  An ODD period transfers NOTHING: `k mod c`
never pins `k mod 2` (`oddPeriod_residue_parity_free` — `k` and `k + c` share the
residue and differ in parity).

Crossing the recorded 45 band-2 residue tables (17 `b₂ = 1` + 28 `b₂ ≥ 2`,
re-verified by `tools_parity_residue_gen.py`) with period parity gives exactly TEN
parity-pinned pairs:

* **members EVEN** (6): `(7,3)c2{2} (31,15)c4{4} (39,1)c4{2} (39,6)c6{4}
  (55,2)c8{2} (39,19)c8{6,8}`;
* **members ODD** (4): `(13,6)c6{3} (51,1)c2{1} (51,8)c2{1} (63,10)c2{1}`;
* 26 pairs have odd `c` (parity free) and 9 have even `c` with mixed residues
  (parity free).

## 2.  Per-datum closures (goal 2)

At Q odd a val-0 fibre member is an ODD raw hit (`olcFibre_val0_odd_hit_of_Q_odd`).
Hence on the six member-EVEN data: (a) the val-0 set is EMPTY
(`olcFibre_val0_filter_eq_empty_of_memberEven`) — `QOddVal0AtMostOne` holds FREE and
`ReturnZeroBody` reduces to `QOddValPosZeroRun` ALONE
(`returnZeroBody_iff_valPosZeroRun_of_memberEven`); (b) every member `k` is even, so
`k + 1` is ODD — the even-`(k+1)` doubling branch of `QOddMaxCleanSplit` is EMPTY
and `ReturnMaxCleanBody` reduces to the pure carry-parity branch
(`returnMaxCleanBody_iff_carryParity_of_memberEven`).  On the four member-ODD data
the mirror holds: the carry-parity branch is vacuous (and its content is automatic,
`carryOf_emod_two_eq_zero_at_even_succ`), so `ReturnMaxCleanBody` reduces to the
pure doubling branch (`returnMaxCleanBody_iff_doubling_of_memberOdd`); the val-0
clause keeps full content there (every member is a val-0 candidate) — recorded
honestly.

## 3.  The `63 @ 10` instance (goal 3) — BOTH lanes, honest

The CLASS-1 lane carries the proved congruence `k % 2 = 0` (members EVEN,
`class1Fibre_residue_of_datum_63_10`: band-4 residue set `{2}`, period 2).  The
CLASS-4 lane (where the digit clauses live) carries the OPPOSITE pin: band-2
residue set `{1}`, period 2, members ODD (`olcFibre_odd_of_datum_63_10`).  Both are
recorded (`datum_63_10_dual_parity`); the class-4 closure delivered at `63 @ 10` is
the member-ODD mirror — `returnMaxClean` reduces to pure doubling and the successor
carry parity is automatic (`datum_63_10_succ_carry_even`) — NOT the val-0 emptiness
(which attaches to member-EVEN data only).

## 4.  The generic odd-`c` case (goal 4) — count bounds, not emptiness

For odd `c` member parity is FREE; the honest deliverable is counting.  On a
`b₂ = 1` cycle the fibre is `c`-spaced (`olcFibre_pair_mod_eq_of_band2_unique`), so
its ODD members are `2c`-spaced (`two_mul_dvd_of_dvd_of_odd`) inside one window:
`#odd ≤ ⌈W/(2c)⌉` (`olcFibre_odd_card_le_of_band2_unique_oddc`), hence
`#val-0 ≤ ⌈W/(2c)⌉` at Q odd (`olcFibre_val0_card_le_of_band2_unique_oddc`), and on
`W ≤ 2c` shells `QOddVal0AtMostOne` holds FREE
(`qOddVal0AtMostOne_of_band2_unique_oddc`) — DOUBLE the spaced-singleton regime
`W ≤ c` of wave 5.  Instance: `(63,31)` gets the val-0 clause on `W ≤ 10`
(`qOddVal0AtMostOne_of_datum_63_31`).  Generic micro-lever: `W ≤ 2` closes the
val-0 clause at EVERY Q-odd context (`qOddVal0AtMostOne_of_width_le_two`) — this is
also exactly what the lever yields at the confined `(3,1)` fixed point (`c = 1`).

## 5.  Capstone bridges (goal 5, additive only)

`ReturnZeroQOddParityReducedField` / `ReturnMaxCleanQOddParityReducedField` are the
wave-11 split fields with the parity-pinned data RELIEVED (val-0 clause demanded
only off the member-EVEN data; per-parity branch demanded per datum class); they
rebuild the verbatim split fields (`returnZeroQOddSplitField_of_parityReduced`,
`returnMaxCleanQOddSplitField_of_parityReduced`), override the wave-11 surface
(`splitResidual_withParityReduced`), and land on the endpoint
(`erdos260_of_parityReducedSplit`).  The converse witnesses
(`parityReducedFields_of_split`) show the reduced fields are weakenings — nothing
is smuggled.

No `sorry`, no `admit`, no new `axiom`, no `native_decide` (`decide` only on small
closed orbit arithmetic); additive only.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 0.  The parity transfer through the cycle representative -/

/-- **Odd periods pin no parity**: `k` and `k + c` share the residue mod `c` and
differ mod 2 — the cycle residue class of an odd period contains both parities. -/
theorem oddPeriod_residue_parity_free {c : ℕ} (hcodd : c % 2 = 1) (k : ℕ) :
    (k + c) % c = k % c ∧ ¬((k + c) % 2 = k % 2) :=
  ⟨Nat.add_mod_right k c, by omega⟩

/-- **The parity transfer**: an EVEN period `c` whose band-2 residues all have parity
`p` forces every class-4 fibre member to parity `p` — `cycleRep c k ≡ k (mod c)` and
`2 ∣ c` transfer the residue parity to the raw position. -/
theorem olcFibre_parity_of_band2_parity (ctx : ActualFailureContext) {c p : ℕ}
    (hc : 1 ≤ c) (hceven : c % 2 = 0)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hpar : ∀ j, 1 ≤ j → j ≤ c →
      canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) = 2 →
        j % 2 = p)
    {k : ℕ} (hk : k ∈ olcFibre ctx) : k % 2 = p := by
  have hband := olcFibre_cycleRep_band2 ctx hc hper hk
  have hj := hpar (cycleRep c k) (cycleRep_pos hc k) (cycleRep_le hc k) hband
  have h2c : (2 : ℕ) ∣ c := Nat.dvd_of_mod_eq_zero hceven
  have hmm : k % c % 2 = k % 2 := Nat.mod_mod_of_dvd k h2c
  unfold cycleRep at hj
  by_cases h0 : k % c = 0
  · rw [if_pos h0] at hj
    omega
  · rw [if_neg h0] at hj
    omega

/-- The datum-level wrapper: transport the parity transfer along `(q, K₀)` pins. -/
theorem olcFibre_parity_of_datum_cycle (ctx : ActualFailureContext)
    {qv Kv c p : ℕ}
    (hq : (class1SlopeDatum ctx).q = qv) (hK : (class1SlopeDatum ctx).K₀ = Kv)
    (hc : 1 ≤ c) (hceven : c % 2 = 0)
    (hcyc : slopeOrbit qv Kv (1 + c) = slopeOrbit qv Kv 1)
    (hpar : ∀ j, 1 ≤ j → j ≤ c → canonGap qv (slopeOrbit qv Kv j) = 2 → j % 2 = p)
    {k : ℕ} (hk : k ∈ olcFibre ctx) : k % 2 = p := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return hcyc
  have hpar' : ∀ j, 1 ≤ j → j ≤ c →
      canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) = 2 →
        j % 2 = p := by
    rw [hq, hK]
    exact hpar
  exact olcFibre_parity_of_band2_parity ctx hc hceven hper hpar' hk

/-! ## Part 1.  The ten parity-pinned pairs (certified cycle tables)

Each pair gets the period return equation and the bounded band-2 parity table,
both decided on the concrete orbit (values < 64, periods ≤ 8). -/

/- ### The six member-EVEN pairs -/

private theorem parityCycle_7_3 : slopeOrbit 7 3 (1 + 2) = slopeOrbit 7 3 1 := by
  decide

private theorem parityTable_7_3 :
    ∀ j, 1 ≤ j → j ≤ 2 → canonGap 7 (slopeOrbit 7 3 j) = 2 → j % 2 = 0 := by
  intro j h1 h2
  interval_cases j <;> decide

/-- `(7, 3)`: cycle `[5, 3]`, band-2 residues `{2}` — members EVEN. -/
theorem olcFibre_even_of_datum_7_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 7) (hK : (class1SlopeDatum ctx).K₀ = 3) :
    ∀ k ∈ olcFibre ctx, k % 2 = 0 := fun k hk =>
  olcFibre_parity_of_datum_cycle ctx hq hK (by norm_num) (by norm_num)
    parityCycle_7_3 parityTable_7_3 hk

private theorem parityCycle_31_15 :
    slopeOrbit 31 15 (1 + 4) = slopeOrbit 31 15 1 := by decide

private theorem parityTable_31_15 :
    ∀ j, 1 ≤ j → j ≤ 4 → canonGap 31 (slopeOrbit 31 15 j) = 2 → j % 2 = 0 := by
  intro j h1 h2
  interval_cases j <;> decide

/-- `(31, 15)`: cycle `[29, 27, 23, 15]`, band-2 residues `{4}` — members EVEN. -/
theorem olcFibre_even_of_datum_31_15 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 31) (hK : (class1SlopeDatum ctx).K₀ = 15) :
    ∀ k ∈ olcFibre ctx, k % 2 = 0 := fun k hk =>
  olcFibre_parity_of_datum_cycle ctx hq hK (by norm_num) (by norm_num)
    parityCycle_31_15 parityTable_31_15 hk

private theorem parityCycle_39_1 : slopeOrbit 39 1 (1 + 4) = slopeOrbit 39 1 1 := by
  decide

private theorem parityTable_39_1 :
    ∀ j, 1 ≤ j → j ≤ 4 → canonGap 39 (slopeOrbit 39 1 j) = 2 → j % 2 = 0 := by
  intro j h1 h2
  interval_cases j <;> decide

/-- `(39, 1)`: cycle `[25, 11, 5, 1]`, band-2 residues `{2}` — members EVEN. -/
theorem olcFibre_even_of_datum_39_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 39) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    ∀ k ∈ olcFibre ctx, k % 2 = 0 := fun k hk =>
  olcFibre_parity_of_datum_cycle ctx hq hK (by norm_num) (by norm_num)
    parityCycle_39_1 parityTable_39_1 hk

private theorem parityCycle_39_6 : slopeOrbit 39 6 (1 + 6) = slopeOrbit 39 6 1 := by
  decide

private theorem parityTable_39_6 :
    ∀ j, 1 ≤ j → j ≤ 6 → canonGap 39 (slopeOrbit 39 6 j) = 2 → j % 2 = 0 := by
  intro j h1 h2
  interval_cases j <;> decide

/-- `(39, 6)`: cycle `[9, 33, 27, 15, 21, 3]`, band-2 residues `{4}` — members EVEN. -/
theorem olcFibre_even_of_datum_39_6 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 39) (hK : (class1SlopeDatum ctx).K₀ = 6) :
    ∀ k ∈ olcFibre ctx, k % 2 = 0 := fun k hk =>
  olcFibre_parity_of_datum_cycle ctx hq hK (by norm_num) (by norm_num)
    parityCycle_39_6 parityTable_39_6 hk

private theorem parityCycle_55_2 : slopeOrbit 55 2 (1 + 8) = slopeOrbit 55 2 1 := by
  decide

private theorem parityTable_55_2 :
    ∀ j, 1 ≤ j → j ≤ 8 → canonGap 55 (slopeOrbit 55 2 j) = 2 → j % 2 = 0 := by
  intro j h1 h2
  interval_cases j <;> decide

/-- `(55, 2)`: cycle `[9, 17, 13, 49, 43, 31, 7, 1]`, band-2 residues `{2}` —
members EVEN. -/
theorem olcFibre_even_of_datum_55_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 55) (hK : (class1SlopeDatum ctx).K₀ = 2) :
    ∀ k ∈ olcFibre ctx, k % 2 = 0 := fun k hk =>
  olcFibre_parity_of_datum_cycle ctx hq hK (by norm_num) (by norm_num)
    parityCycle_55_2 parityTable_55_2 hk

private theorem parityCycle_39_19 :
    slopeOrbit 39 19 (1 + 8) = slopeOrbit 39 19 1 := by decide

private theorem parityTable_39_19 :
    ∀ j, 1 ≤ j → j ≤ 8 → canonGap 39 (slopeOrbit 39 19 j) = 2 → j % 2 = 0 := by
  intro j h1 h2
  interval_cases j <;> decide

/-- `(39, 19)`: cycle `[37, 35, 31, 23, 7, 17, 29, 19]`, band-2 residues `{6, 8}` —
the FIRST parity pin on a `b₂ ≥ 2` pair: both residues even, members EVEN. -/
theorem olcFibre_even_of_datum_39_19 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 39) (hK : (class1SlopeDatum ctx).K₀ = 19) :
    ∀ k ∈ olcFibre ctx, k % 2 = 0 := fun k hk =>
  olcFibre_parity_of_datum_cycle ctx hq hK (by norm_num) (by norm_num)
    parityCycle_39_19 parityTable_39_19 hk

/- ### The four member-ODD pairs -/

private theorem parityCycle_13_6 : slopeOrbit 13 6 (1 + 6) = slopeOrbit 13 6 1 := by
  decide

private theorem parityTable_13_6 :
    ∀ j, 1 ≤ j → j ≤ 6 → canonGap 13 (slopeOrbit 13 6 j) = 2 → j % 2 = 1 := by
  intro j h1 h2
  interval_cases j <;> decide

/-- `(13, 6)`: cycle `[11, 9, 5, 7, 1, 3]`, band-2 residues `{3}` — members ODD. -/
theorem olcFibre_odd_of_datum_13_6 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 13) (hK : (class1SlopeDatum ctx).K₀ = 6) :
    ∀ k ∈ olcFibre ctx, k % 2 = 1 := fun k hk =>
  olcFibre_parity_of_datum_cycle ctx hq hK (by norm_num) (by norm_num)
    parityCycle_13_6 parityTable_13_6 hk

private theorem parityCycle_51_1 : slopeOrbit 51 1 (1 + 2) = slopeOrbit 51 1 1 := by
  decide

private theorem parityTable_51_1 :
    ∀ j, 1 ≤ j → j ≤ 2 → canonGap 51 (slopeOrbit 51 1 j) = 2 → j % 2 = 1 := by
  intro j h1 h2
  interval_cases j <;> decide

/-- `(51, 1)`: cycle `[13, 1]`, band-2 residues `{1}` — members ODD. -/
theorem olcFibre_odd_of_datum_51_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 51) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    ∀ k ∈ olcFibre ctx, k % 2 = 1 := fun k hk =>
  olcFibre_parity_of_datum_cycle ctx hq hK (by norm_num) (by norm_num)
    parityCycle_51_1 parityTable_51_1 hk

private theorem parityCycle_51_8 : slopeOrbit 51 8 (1 + 2) = slopeOrbit 51 8 1 := by
  decide

private theorem parityTable_51_8 :
    ∀ j, 1 ≤ j → j ≤ 2 → canonGap 51 (slopeOrbit 51 8 j) = 2 → j % 2 = 1 := by
  intro j h1 h2
  interval_cases j <;> decide

/-- `(51, 8)`: enters `[13, 1]` after one step, band-2 residues `{1}` — members ODD. -/
theorem olcFibre_odd_of_datum_51_8 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 51) (hK : (class1SlopeDatum ctx).K₀ = 8) :
    ∀ k ∈ olcFibre ctx, k % 2 = 1 := fun k hk =>
  olcFibre_parity_of_datum_cycle ctx hq hK (by norm_num) (by norm_num)
    parityCycle_51_8 parityTable_51_8 hk

private theorem parityCycle_63_10 :
    slopeOrbit 63 10 (1 + 2) = slopeOrbit 63 10 1 := by decide

private theorem parityTable_63_10 :
    ∀ j, 1 ≤ j → j ≤ 2 → canonGap 63 (slopeOrbit 63 10 j) = 2 → j % 2 = 1 := by
  intro j h1 h2
  interval_cases j <;> decide

/-- `(63, 10)`: cycle `[17, 5]`, band-2 residues `{1}` — CLASS-4 members ODD (the
mirror of the class-1 even congruence at the same pair). -/
theorem olcFibre_odd_of_datum_63_10 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) (hK : (class1SlopeDatum ctx).K₀ = 10) :
    ∀ k ∈ olcFibre ctx, k % 2 = 1 := fun k hk =>
  olcFibre_parity_of_datum_cycle ctx hq hK (by norm_num) (by norm_num)
    parityCycle_63_10 parityTable_63_10 hk

/- ### The aggregate datum predicates -/

/-- **The member-EVEN data**: even period, band-2 residue set parity-pure EVEN —
exactly six of the 45 enumerated `b₂ ≥ 1` pairs. -/
def ReturnB2ParityEvenDatum (ctx : ActualFailureContext) : Prop :=
  ((class1SlopeDatum ctx).q = 7 ∧ (class1SlopeDatum ctx).K₀ = 3)
  ∨ ((class1SlopeDatum ctx).q = 31 ∧ (class1SlopeDatum ctx).K₀ = 15)
  ∨ ((class1SlopeDatum ctx).q = 39 ∧ (class1SlopeDatum ctx).K₀ = 1)
  ∨ ((class1SlopeDatum ctx).q = 39 ∧ (class1SlopeDatum ctx).K₀ = 6)
  ∨ ((class1SlopeDatum ctx).q = 39 ∧ (class1SlopeDatum ctx).K₀ = 19)
  ∨ ((class1SlopeDatum ctx).q = 55 ∧ (class1SlopeDatum ctx).K₀ = 2)

/-- **The member-ODD data**: even period, band-2 residue set parity-pure ODD —
exactly four of the 45 enumerated `b₂ ≥ 1` pairs. -/
def ReturnB2ParityOddDatum (ctx : ActualFailureContext) : Prop :=
  ((class1SlopeDatum ctx).q = 13 ∧ (class1SlopeDatum ctx).K₀ = 6)
  ∨ ((class1SlopeDatum ctx).q = 51 ∧ (class1SlopeDatum ctx).K₀ = 1)
  ∨ ((class1SlopeDatum ctx).q = 51 ∧ (class1SlopeDatum ctx).K₀ = 8)
  ∨ ((class1SlopeDatum ctx).q = 63 ∧ (class1SlopeDatum ctx).K₀ = 10)

/-- Every member-EVEN datum pins all class-4 fibre members to even raw positions. -/
theorem olcFibre_even_of_parityEvenDatum (ctx : ActualFailureContext)
    (h : ReturnB2ParityEvenDatum ctx) : ∀ k ∈ olcFibre ctx, k % 2 = 0 := by
  rcases h with ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩
  · exact olcFibre_even_of_datum_7_3 ctx hq hK
  · exact olcFibre_even_of_datum_31_15 ctx hq hK
  · exact olcFibre_even_of_datum_39_1 ctx hq hK
  · exact olcFibre_even_of_datum_39_6 ctx hq hK
  · exact olcFibre_even_of_datum_39_19 ctx hq hK
  · exact olcFibre_even_of_datum_55_2 ctx hq hK

/-- Every member-ODD datum pins all class-4 fibre members to odd raw positions. -/
theorem olcFibre_odd_of_parityOddDatum (ctx : ActualFailureContext)
    (h : ReturnB2ParityOddDatum ctx) : ∀ k ∈ olcFibre ctx, k % 2 = 1 := by
  rcases h with ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩
  · exact olcFibre_odd_of_datum_13_6 ctx hq hK
  · exact olcFibre_odd_of_datum_51_1 ctx hq hK
  · exact olcFibre_odd_of_datum_51_8 ctx hq hK
  · exact olcFibre_odd_of_datum_63_10 ctx hq hK

/-! ## Part 2.  The member-parity closures of the digit clauses (Q odd) -/

/-- **(a) Member-EVEN kills the val-0 set**: at Q odd a val-0 member is an odd raw
hit, but every member is even — the val-0 part of the fibre is EMPTY. -/
theorem olcFibre_val0_filter_eq_empty_of_memberEven (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) (heven : ∀ k ∈ olcFibre ctx, k % 2 = 0) :
    (olcFibre ctx).filter (fun k => carryVal2 ctx k = 0) = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  intro k hk h0
  have hodd := (olcFibre_val0_odd_hit_of_Q_odd ctx hQodd hk h0).1
  have := heven k hk
  omega

/-- **(a) `QOddVal0AtMostOne` holds FREE on member-EVEN data**: the clause counts an
empty set. -/
theorem qOddVal0AtMostOne_of_memberEven (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) (heven : ∀ k ∈ olcFibre ctx, k % 2 = 0) :
    QOddVal0AtMostOne ctx := by
  intro x hx z hz h0x h0z
  have hodd := (olcFibre_val0_odd_hit_of_Q_odd ctx hQodd hx h0x).1
  have := heven x hx
  omega

/-- The valuation floor on member-EVEN data: every member has `carryVal2 ≥ 1`. -/
theorem carryVal2_pos_of_memberEven (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) (heven : ∀ k ∈ olcFibre ctx, k % 2 = 0) :
    ∀ k ∈ olcFibre ctx, 1 ≤ carryVal2 ctx k := by
  intro k hk
  rcases Nat.eq_zero_or_pos (carryVal2 ctx k) with h0 | hpos
  · have hodd := (olcFibre_val0_odd_hit_of_Q_odd ctx hQodd hk h0).1
    have := heven k hk
    omega
  · exact hpos

/-- **`returnZero` reduces to the val-positive zero-run clause ALONE on member-EVEN
data**: the val-0 counting clause of the wave-11 split is free. -/
theorem returnZeroBody_iff_valPosZeroRun_of_memberEven (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) (heven : ∀ k ∈ olcFibre ctx, k % 2 = 0) :
    ReturnZeroBody ctx ↔ QOddValPosZeroRun ctx := by
  rw [returnZeroBody_iff_qOddSplit ctx hQodd]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨qOddVal0AtMostOne_of_memberEven ctx hQodd heven, h⟩

/-- **(b) Member-EVEN empties the doubling branch**: `QOddMaxCleanSplit` collapses to
the pure carry-parity branch — every member `k` is even, so `k + 1` is odd and the
even-`(k+1)` doubling clause is vacuous while the parity guard is automatic. -/
theorem qOddMaxCleanSplit_iff_carryParity_of_memberEven (ctx : ActualFailureContext)
    (heven : ∀ k ∈ olcFibre ctx, k % 2 = 0) :
    QOddMaxCleanSplit ctx ↔
      ∀ k ∈ olcFibre ctx,
        (∀ z ∈ olcFibre ctx, returnSelfRefKey ctx z = returnSelfRefKey ctx k → z ≤ k) →
        carryOf ctx (k + 1) % 2 = 0 := by
  constructor
  · intro H k hk hmax
    exact (H k hk hmax).1 (heven k hk)
  · intro H k hk hmax
    refine ⟨fun _ => H k hk hmax, fun hodd => ?_⟩
    have := heven k hk
    omega

/-- The member-ODD mirror: `QOddMaxCleanSplit` collapses to the pure doubling
branch — every member `k` is odd, so `k + 1` is even and the carry-parity clause is
vacuous. -/
theorem qOddMaxCleanSplit_iff_doubling_of_memberOdd (ctx : ActualFailureContext)
    (hodd : ∀ k ∈ olcFibre ctx, k % 2 = 1) :
    QOddMaxCleanSplit ctx ↔
      ∀ k ∈ olcFibre ctx,
        (∀ z ∈ olcFibre ctx, returnSelfRefKey ctx z = returnSelfRefKey ctx k → z ≤ k) →
        carryOf ctx (k + 1) = 2 * carryOf ctx k := by
  constructor
  · intro H k hk hmax
    exact (H k hk hmax).2 (hodd k hk)
  · intro H k hk hmax
    refine ⟨fun heven => ?_, fun _ => H k hk hmax⟩
    have := hodd k hk
    omega

/-- **`returnMaxClean` reduces to the carry-parity branch ALONE on member-EVEN data
(Q odd)** — the verbatim digit demand becomes a pure carry-parity fact at every
per-slice maximum. -/
theorem returnMaxCleanBody_iff_carryParity_of_memberEven (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) (heven : ∀ k ∈ olcFibre ctx, k % 2 = 0) :
    ReturnMaxCleanBody ctx ↔
      ∀ k ∈ olcFibre ctx,
        (∀ z ∈ olcFibre ctx, returnSelfRefKey ctx z = returnSelfRefKey ctx k → z ≤ k) →
        carryOf ctx (k + 1) % 2 = 0 :=
  (returnMaxCleanBody_iff_qOddSplit ctx hQodd).trans
    (qOddMaxCleanSplit_iff_carryParity_of_memberEven ctx heven)

/-- **`returnMaxClean` reduces to the doubling branch ALONE on member-ODD data
(Q odd)** — the parity route is empty there (and its content automatic). -/
theorem returnMaxCleanBody_iff_doubling_of_memberOdd (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) (hodd : ∀ k ∈ olcFibre ctx, k % 2 = 1) :
    ReturnMaxCleanBody ctx ↔
      ∀ k ∈ olcFibre ctx,
        (∀ z ∈ olcFibre ctx, returnSelfRefKey ctx z = returnSelfRefKey ctx k → z ≤ k) →
        carryOf ctx (k + 1) = 2 * carryOf ctx k :=
  (returnMaxCleanBody_iff_qOddSplit ctx hQodd).trans
    (qOddMaxCleanSplit_iff_doubling_of_memberOdd ctx hodd)

/-- On member-ODD data the successor carry parity is AUTOMATIC (any `Q`): every
`k + 1` is even and the parity dictionary forces `carryOf (k+1) ≡ 0 (mod 2)`. -/
theorem succ_carry_even_of_memberOdd (ctx : ActualFailureContext)
    (hodd : ∀ k ∈ olcFibre ctx, k % 2 = 1) :
    ∀ k ∈ olcFibre ctx, carryOf ctx (k + 1) % 2 = 0 := fun k hk =>
  carryOf_emod_two_eq_zero_at_even_succ ctx (hodd k hk)

/- ### The per-datum digit-field closures -/

/-- **The member-EVEN per-datum closure of `returnZero` (Q odd)**: on the six
parity-even data the val-0 clause is FREE and the field reduces to the val-positive
zero-run clause alone. -/
theorem returnZero_reduces_of_parityEvenDatum (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) (h : ReturnB2ParityEvenDatum ctx) :
    QOddVal0AtMostOne ctx ∧ (ReturnZeroBody ctx ↔ QOddValPosZeroRun ctx) :=
  ⟨qOddVal0AtMostOne_of_memberEven ctx hQodd (olcFibre_even_of_parityEvenDatum ctx h),
   returnZeroBody_iff_valPosZeroRun_of_memberEven ctx hQodd
     (olcFibre_even_of_parityEvenDatum ctx h)⟩

/-- **The member-EVEN per-datum closure of `returnMaxClean` (Q odd)**: on the six
parity-even data the doubling branch is EMPTY and the field reduces to the pure
carry-parity branch. -/
theorem returnMaxClean_reduces_of_parityEvenDatum (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) (h : ReturnB2ParityEvenDatum ctx) :
    ReturnMaxCleanBody ctx ↔
      ∀ k ∈ olcFibre ctx,
        (∀ z ∈ olcFibre ctx, returnSelfRefKey ctx z = returnSelfRefKey ctx k → z ≤ k) →
        carryOf ctx (k + 1) % 2 = 0 :=
  returnMaxCleanBody_iff_carryParity_of_memberEven ctx hQodd
    (olcFibre_even_of_parityEvenDatum ctx h)

/-- **The member-ODD per-datum closure of `returnMaxClean` (Q odd)**: on the four
parity-odd data the carry-parity branch is EMPTY and the field reduces to the pure
doubling branch. -/
theorem returnMaxClean_reduces_of_parityOddDatum (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1) (h : ReturnB2ParityOddDatum ctx) :
    ReturnMaxCleanBody ctx ↔
      ∀ k ∈ olcFibre ctx,
        (∀ z ∈ olcFibre ctx, returnSelfRefKey ctx z = returnSelfRefKey ctx k → z ≤ k) →
        carryOf ctx (k + 1) = 2 * carryOf ctx k :=
  returnMaxCleanBody_iff_doubling_of_memberOdd ctx hQodd
    (olcFibre_odd_of_parityOddDatum ctx h)

/-! ## Part 3.  The `63 @ 10` instance — both lanes recorded honestly -/

/-- **The `63 @ 10` dual parity**: the CLASS-1 fibre members are EVEN (the proved
band-4 congruence `k % 2 = 0` of `CNLClass1PairClosure`) while the CLASS-4 fibre
members are ODD (band-2 residue `{1}` mod 2).  The two lanes carry OPPOSITE pins at
the same pair — the val-0 emptiness lever (member-EVEN) does NOT attach to the
class-4 lane here; the doubling reduction does. -/
theorem datum_63_10_dual_parity (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) (hK : (class1SlopeDatum ctx).K₀ = 10) :
    (∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1, k % 2 = 0)
      ∧ (∀ k ∈ olcFibre ctx, k % 2 = 1) :=
  ⟨fun k hk => (class1Fibre_residue_of_datum_63_10 ctx hq hK hk).1,
   olcFibre_odd_of_datum_63_10 ctx hq hK⟩

/-- At `63 @ 10` the successor carry parity is automatic at every class-4 member
(any `Q`). -/
theorem datum_63_10_succ_carry_even (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) (hK : (class1SlopeDatum ctx).K₀ = 10) :
    ∀ k ∈ olcFibre ctx, carryOf ctx (k + 1) % 2 = 0 :=
  succ_carry_even_of_memberOdd ctx (olcFibre_odd_of_datum_63_10 ctx hq hK)

/-- **The sharpened `63 @ 10` instance (Q odd)**: `returnMaxClean` IS the pure
doubling demand at the per-slice maxima — the carry-parity branch is empty. -/
theorem returnMaxClean_doubling_of_datum_63_10 (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1)
    (hq : (class1SlopeDatum ctx).q = 63) (hK : (class1SlopeDatum ctx).K₀ = 10) :
    ReturnMaxCleanBody ctx ↔
      ∀ k ∈ olcFibre ctx,
        (∀ z ∈ olcFibre ctx, returnSelfRefKey ctx z = returnSelfRefKey ctx k → z ≤ k) →
        carryOf ctx (k + 1) = 2 * carryOf ctx k :=
  returnMaxCleanBody_iff_doubling_of_memberOdd ctx hQodd
    (olcFibre_odd_of_datum_63_10 ctx hq hK)

/-! ## Part 4.  The generic odd-`c` case — count bounds, honestly no emptiness -/

/-- Coprimality-free gluing: `c` odd, `c ∣ d`, `2 ∣ d` force `2c ∣ d`. -/
theorem two_mul_dvd_of_dvd_of_odd {c d : ℕ} (hcodd : c % 2 = 1) (hcd : c ∣ d)
    (h2d : 2 ∣ d) : 2 * c ∣ d := by
  obtain ⟨t, rfl⟩ := hcd
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2d with h2c | h2t
  · exact absurd h2c (by omega)
  · obtain ⟨s, rfl⟩ := h2t
    exact ⟨s, by ring⟩

/-- **The spaced-set count**: a finite set of naturals whose pairwise differences are
positive multiples of `c` and bounded by `W` has at most `⌈W/c⌉` elements. -/
theorem spaced_finset_card_le {S : Finset ℕ} {c W : ℕ} (hc : 1 ≤ c) (hW : 1 ≤ W)
    (hspace : ∀ x ∈ S, ∀ z ∈ S, x < z → c ∣ z - x)
    (hdist : ∀ x ∈ S, ∀ z ∈ S, x < z → z - x < W) :
    S.card ≤ (W + c - 1) / c := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  · have hmS : S.min' hne ∈ S := S.min'_mem hne
    set m := S.min' hne with hm
    have hdvd : ∀ k ∈ S, c ∣ k - m := by
      intro k hk
      rcases eq_or_lt_of_le (S.min'_le k hk) with heq | hlt
      · have hk0 : k - m = 0 := by omega
        rw [hk0]
        exact dvd_zero c
      · exact hspace m hmS k hk hlt
    have hlt : ∀ k ∈ S, k - m < W := by
      intro k hk
      rcases eq_or_lt_of_le (S.min'_le k hk) with heq | hlt
      · rw [← heq]
        omega
      · exact hdist m hmS k hk hlt
    have hmap : ∀ k ∈ S, (k - m) / c ∈ Finset.range ((W + c - 1) / c) := by
      intro k hk
      rw [Finset.mem_range]
      have h1 : k - m ≤ W - 1 := by
        have := hlt k hk
        omega
      have h2 : (k - m) / c ≤ (W - 1) / c := Nat.div_le_div_right h1
      have h3 : (W + c - 1) / c = (W - 1) / c + 1 := by
        have he : W + c - 1 = (W - 1) + c := by omega
        rw [he, Nat.add_div_right _ hc]
      omega
    have hinj : ∀ x ∈ S, ∀ z ∈ S, (x - m) / c = (z - m) / c → x = z := by
      intro x hx z hz hf
      have ex : (x - m) / c * c = x - m := Nat.div_mul_cancel (hdvd x hx)
      have ez : (z - m) / c * c = z - m := Nat.div_mul_cancel (hdvd z hz)
      have hmx := S.min'_le x hx
      have hmz := S.min'_le z hz
      have hxz : x - m = z - m := by
        rw [← ex, ← ez, hf]
      omega
    calc S.card ≤ (Finset.range ((W + c - 1) / c)).card :=
          Finset.card_le_card_of_injOn (fun k => (k - m) / c) hmap
            (fun x hx z hz hf =>
              hinj x (Finset.mem_coe.mp hx) z (Finset.mem_coe.mp hz) hf)
      _ = (W + c - 1) / c := Finset.card_range _

/-- **Odd members of a `b₂ = 1` odd-period fibre are `2c`-spaced**: the `c`-spacing
congruence plus shared parity glue to a `2c` step (`c` odd). -/
theorem olcFibre_odd_pair_two_mul_dvd_of_band2_unique_oddc
    (ctx : ActualFailureContext) {c j₀ : ℕ} (hc : 1 ≤ c) (hcodd : c % 2 = 1)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (huniq : ∀ j, 1 ≤ j → j ≤ c →
      canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) = 2 → j = j₀)
    {x z : ℕ} (hx : x ∈ olcFibre ctx) (hz : z ∈ olcFibre ctx)
    (hxp : x % 2 = 1) (hzp : z % 2 = 1) (hlt : x < z) : 2 * c ∣ z - x := by
  have hmod := olcFibre_pair_mod_eq_of_band2_unique ctx hc hper huniq hx hz
  have hcd : c ∣ z - x := (Nat.modEq_iff_dvd' (le_of_lt hlt)).mp hmod
  have h2d : (2 : ℕ) ∣ z - x := by omega
  exact two_mul_dvd_of_dvd_of_odd hcodd hcd h2d

/-- **The odd-member count bound (odd period, `b₂ = 1`)**: `#odd ≤ ⌈W/(2c)⌉` — the
honest odd-`c` replacement for emptiness. -/
theorem olcFibre_odd_card_le_of_band2_unique_oddc (ctx : ActualFailureContext)
    {c j₀ : ℕ} (hc : 1 ≤ c) (hcodd : c % 2 = 1)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (huniq : ∀ j, 1 ≤ j → j ≤ c →
      canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) = 2 → j = j₀) :
    ((olcFibre ctx).filter (fun k => k % 2 = 1)).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card + 2 * c - 1) / (2 * c) := by
  rcases ((olcFibre ctx).filter (fun k => k % 2 = 1)).eq_empty_or_nonempty with
    he | hne
  · rw [he]
    simp
  · obtain ⟨k₀, hk₀⟩ := hne
    have hk₀f : k₀ ∈ olcFibre ctx := (Finset.mem_filter.mp hk₀).1
    have hw := olcFibre_mem_window ctx hk₀f
    have hW1 : 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card := by omega
    refine spaced_finset_card_le (by omega) hW1 ?_ ?_
    · intro x hx z hz hlt
      obtain ⟨hxf, hxp⟩ := Finset.mem_filter.mp hx
      obtain ⟨hzf, hzp⟩ := Finset.mem_filter.mp hz
      exact olcFibre_odd_pair_two_mul_dvd_of_band2_unique_oddc ctx hc hcodd hper
        huniq hxf hzf hxp hzp hlt
    · intro x hx z hz hlt
      exact olcFibre_pair_dist_lt_width ctx (Finset.mem_filter.mp hx).1
        (Finset.mem_filter.mp hz).1

/-- **The val-0 count bound (odd period, `b₂ = 1`, Q odd)**: the val-0 members are
odd, so `#val-0 ≤ ⌈W/(2c)⌉` — a COUNT bound, not emptiness. -/
theorem olcFibre_val0_card_le_of_band2_unique_oddc (ctx : ActualFailureContext)
    {c j₀ : ℕ} (hQodd : ctx.Q % 2 = 1) (hc : 1 ≤ c) (hcodd : c % 2 = 1)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (huniq : ∀ j, 1 ≤ j → j ≤ c →
      canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) = 2 → j = j₀) :
    ((olcFibre ctx).filter (fun k => carryVal2 ctx k = 0)).card
      ≤ ((supportShell ctx.shell.d ctx.shell.X).card + 2 * c - 1) / (2 * c) := by
  refine le_trans (Finset.card_le_card ?_)
    (olcFibre_odd_card_le_of_band2_unique_oddc ctx hc hcodd hper huniq)
  intro k hk
  obtain ⟨hkf, hk0⟩ := Finset.mem_filter.mp hk
  exact Finset.mem_filter.mpr
    ⟨hkf, (olcFibre_val0_odd_hit_of_Q_odd ctx hQodd hkf hk0).1⟩

/-- **The generic width-2 micro-lever (Q odd, ANY datum)**: two val-0 members are
both odd, so they differ by at least 2 — on `W ≤ 2` shells the val-0 clause holds
free.  (At the confined `(3,1)` fixed point `c = 1`, this IS the `W ≤ 2c` regime.) -/
theorem qOddVal0AtMostOne_of_width_le_two (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1)
    (hW : (supportShell ctx.shell.d ctx.shell.X).card ≤ 2) :
    QOddVal0AtMostOne ctx := by
  intro x hx z hz h0x h0z
  have hxp := (olcFibre_val0_odd_hit_of_Q_odd ctx hQodd hx h0x).1
  have hzp := (olcFibre_val0_odd_hit_of_Q_odd ctx hQodd hz h0z).1
  rcases Nat.lt_trichotomy x z with hlt | heq | hgt
  · have hwd := olcFibre_pair_dist_lt_width ctx hx hz
    omega
  · exact heq
  · have hwd := olcFibre_pair_dist_lt_width ctx hz hx
    omega

/-- **The `W ≤ 2c` val-0 closure (odd period, `b₂ = 1`, Q odd)**: two val-0 members
would be `2c`-spaced inside a window of width `W ≤ 2c` — `QOddVal0AtMostOne` holds
FREE on a regime DOUBLE the wave-5 spaced-singleton regime `W ≤ c`. -/
theorem qOddVal0AtMostOne_of_band2_unique_oddc (ctx : ActualFailureContext)
    {c j₀ : ℕ} (hQodd : ctx.Q % 2 = 1) (hc : 1 ≤ c) (hcodd : c % 2 = 1)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (huniq : ∀ j, 1 ≤ j → j ≤ c →
      canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) = 2 → j = j₀)
    (hW : (supportShell ctx.shell.d ctx.shell.X).card ≤ 2 * c) :
    QOddVal0AtMostOne ctx := by
  have key : ∀ x ∈ olcFibre ctx, ∀ z ∈ olcFibre ctx,
      carryVal2 ctx x = 0 → carryVal2 ctx z = 0 → x < z → False := by
    intro x hx z hz h0x h0z hlt
    have hxp := (olcFibre_val0_odd_hit_of_Q_odd ctx hQodd hx h0x).1
    have hzp := (olcFibre_val0_odd_hit_of_Q_odd ctx hQodd hz h0z).1
    have h2cd := olcFibre_odd_pair_two_mul_dvd_of_band2_unique_oddc ctx hc hcodd
      hper huniq hx hz hxp hzp hlt
    have hwd := olcFibre_pair_dist_lt_width ctx hx hz
    have hle : 2 * c ≤ z - x := Nat.le_of_dvd (by omega) h2cd
    omega
  intro x hx z hz h0x h0z
  rcases Nat.lt_trichotomy x z with hlt | heq | hgt
  · exact (key x hx z hz h0x h0z hlt).elim
  · exact heq
  · exact (key z hz x hx h0z h0x hgt).elim

/- ### The `(63, 31)` instance of the odd-`c` lever -/

private theorem parityCycle_63_31 :
    slopeOrbit 63 31 (1 + 5) = slopeOrbit 63 31 1 := by decide

private theorem parityTable_63_31 :
    ∀ j, 1 ≤ j → j ≤ 5 → canonGap 63 (slopeOrbit 63 31 j) = 2 → j = 5 := by
  intro j h1 h2
  interval_cases j <;> decide

/-- `(63, 31)` (cycle `[61, 59, 55, 47, 31]`, unique band-2 residue `j₀ = 5`, period
5 ODD): the val-0 clause closes on `W ≤ 10` shells — DOUBLE the wave-5 `W ≤ 5`
singleton regime. -/
theorem qOddVal0AtMostOne_of_datum_63_31 (ctx : ActualFailureContext)
    (hQodd : ctx.Q % 2 = 1)
    (hq : (class1SlopeDatum ctx).q = 63) (hK : (class1SlopeDatum ctx).K₀ = 31)
    (hW : (supportShell ctx.shell.d ctx.shell.X).card ≤ 10) :
    QOddVal0AtMostOne ctx := by
  have hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + 5)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m := by
    rw [hq, hK]
    exact slopeOrbit_period_of_return parityCycle_63_31
  have huniq : ∀ j, 1 ≤ j → j ≤ 5 →
      canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) = 2 →
        j = 5 := by
    rw [hq, hK]
    exact parityTable_63_31
  exact qOddVal0AtMostOne_of_band2_unique_oddc ctx hQodd (by norm_num) (by norm_num)
    hper huniq (by omega)

/-! ## Part 5.  Capstone bridges — the parity-reduced successor fields -/

/-- **The parity-reduced `returnZero` Q-odd field**: under the verbatim wave-11
guards, the val-positive zero-run clause everywhere, but the val-0 counting clause
demanded only OFF the six member-EVEN data (where it is proved free). -/
def ReturnZeroQOddParityReducedField : Prop :=
  ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    (∃ k ∈ olcFibre ctx,
      2 ^ carryVal2 ctx k < (supportShell ctx.shell.d ctx.shell.X).card) →
    ¬ ReturnIndexWindowClean ctx →
    ctx.Q % 2 = 1 →
    QOddValPosZeroRun ctx ∧ (¬ ReturnB2ParityEvenDatum ctx → QOddVal0AtMostOne ctx)

/-- **The parity-reduced `returnMaxClean` Q-odd field**: per datum class, only the
LIVE branch is demanded — carry parity on member-EVEN data, doubling on member-ODD
data, the full split off the ten pinned pairs. -/
def ReturnMaxCleanQOddParityReducedField : Prop :=
  ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnIndexWindowClean ctx →
    ctx.Q % 2 = 1 →
    (ReturnB2ParityEvenDatum ctx →
      ∀ k ∈ olcFibre ctx,
        (∀ z ∈ olcFibre ctx, returnSelfRefKey ctx z = returnSelfRefKey ctx k → z ≤ k) →
        carryOf ctx (k + 1) % 2 = 0)
    ∧ (ReturnB2ParityOddDatum ctx →
      ∀ k ∈ olcFibre ctx,
        (∀ z ∈ olcFibre ctx, returnSelfRefKey ctx z = returnSelfRefKey ctx k → z ≤ k) →
        carryOf ctx (k + 1) = 2 * carryOf ctx k)
    ∧ (¬ ReturnB2ParityEvenDatum ctx → ¬ ReturnB2ParityOddDatum ctx →
        QOddMaxCleanSplit ctx)

/-- **The `returnZero` rebuild**: the parity-reduced field rebuilds the verbatim
wave-11 split field — on member-EVEN data the val-0 clause is proved free. -/
theorem returnZeroQOddSplitField_of_parityReduced
    (h : ReturnZeroQOddParityReducedField) : ReturnZeroQOddSplitField := by
  intro ctx hA hB hC hD hQ
  obtain ⟨hrun, hoff⟩ := h ctx hA hB hC hD hQ
  by_cases hpe : ReturnB2ParityEvenDatum ctx
  · exact ⟨qOddVal0AtMostOne_of_memberEven ctx hQ
      (olcFibre_even_of_parityEvenDatum ctx hpe), hrun⟩
  · exact ⟨hoff hpe, hrun⟩

/-- **The `returnMaxClean` rebuild**: the parity-reduced field rebuilds the verbatim
wave-11 split field — per datum class the dead branch is restored for free. -/
theorem returnMaxCleanQOddSplitField_of_parityReduced
    (h : ReturnMaxCleanQOddParityReducedField) : ReturnMaxCleanQOddSplitField := by
  intro ctx hA hD hQ
  obtain ⟨he, ho, hoff⟩ := h ctx hA hD hQ
  by_cases hpe : ReturnB2ParityEvenDatum ctx
  · exact (qOddMaxCleanSplit_iff_carryParity_of_memberEven ctx
      (olcFibre_even_of_parityEvenDatum ctx hpe)).mpr (he hpe)
  · by_cases hpo : ReturnB2ParityOddDatum ctx
    · exact (qOddMaxCleanSplit_iff_doubling_of_memberOdd ctx
        (olcFibre_odd_of_parityOddDatum ctx hpo)).mpr (ho hpo)
    · exact hoff hpe hpo

/-- **The converse witnesses** (weakening accounting, nothing smuggled): any wave-11
split surface provides both parity-reduced fields. -/
theorem parityReducedFields_of_split (R : Erdos260SplitResidual) :
    ReturnZeroQOddParityReducedField ∧ ReturnMaxCleanQOddParityReducedField := by
  constructor
  · intro ctx hA hB hC hD hQ
    obtain ⟨h1, h2⟩ := R.returnZeroQOddSplit ctx hA hB hC hD hQ
    exact ⟨h2, fun _ => h1⟩
  · intro ctx hA hD hQ
    have H := R.returnMaxCleanQOddSplit ctx hA hD hQ
    refine ⟨fun hpe k hk hmax => ?_, fun hpo k hk hmax => ?_, fun _ _ => H⟩
    · exact (H k hk hmax).1 (olcFibre_even_of_parityEvenDatum ctx hpe k hk)
    · exact (H k hk hmax).2 (olcFibre_odd_of_parityOddDatum ctx hpo k hk)

/-- **The surface override**: replace the two Q-odd digit fields of any wave-11
split surface by their parity-reduced forms — the result is again a full
`Erdos260SplitResidual`. -/
def splitResidual_withParityReduced (R : Erdos260SplitResidual)
    (hz : ReturnZeroQOddParityReducedField)
    (hm : ReturnMaxCleanQOddParityReducedField) : Erdos260SplitResidual :=
  { R with
    returnZeroQOddSplit := returnZeroQOddSplitField_of_parityReduced hz
    returnMaxCleanQOddSplit := returnMaxCleanQOddSplitField_of_parityReduced hm }

/-- **Endpoint**: `Erdos260Statement` from a wave-11 split surface whose two Q-odd
digit fields are supplied in parity-reduced form. -/
theorem erdos260_of_parityReducedSplit (R : Erdos260SplitResidual)
    (hz : ReturnZeroQOddParityReducedField)
    (hm : ReturnMaxCleanQOddParityReducedField) : Erdos260Statement :=
  erdos260_of_splitResidual (splitResidual_withParityReduced R hz hm)

/-! ## Part 6.  Machine-readable status (honest) -/

/-- Honest machine-readable status of the parity-residue closure module. -/
def parityResidueClosureStatus : List String :=
  [ "PARITY TRANSFER (goal 1, proved): every class-4 fibre member k reads band 2 " ++
      "at its cycle representative (olcFibre_cycleRep_band2), and cycleRep c k = k " ++
      "mod c (with c for 0), so an EVEN period c with a parity-pure band-2 residue " ++
      "set pins k % 2 (olcFibre_parity_of_band2_parity / " ++
      "olcFibre_parity_of_datum_cycle).  An ODD period pins NOTHING: k and k + c " ++
      "share the residue and differ in parity (oddPeriod_residue_parity_free).",
    "THE PARITY-PURE DATA (exact, certified by decided cycle tables, re-verified " ++
      "by tools_parity_residue_gen.py against the recorded ReturnSpanGateClosure " ++
      "tables): members EVEN - (7,3)c2{2} (31,15)c4{4} (39,1)c4{2} (39,6)c6{4} " ++
      "(55,2)c8{2} (39,19)c8{6,8} (olcFibre_even_of_datum_*, aggregate " ++
      "ReturnB2ParityEvenDatum / olcFibre_even_of_parityEvenDatum); members ODD - " ++
      "(13,6)c6{3} (51,1)c2{1} (51,8)c2{1} (63,10)c2{1} (olcFibre_odd_of_datum_*, " ++
      "aggregate ReturnB2ParityOddDatum / olcFibre_odd_of_parityOddDatum).  " ++
      "(39,19) is the first parity pin on a b2 >= 2 pair.  The other 35 enumerated " ++
      "pairs are parity-FREE: 26 have odd period, 9 have even period with mixed " ++
      "residues - honestly out of reach of this lever.",
    "PER-DATUM CLOSURES (goal 2, proved, Q odd): on the SIX member-EVEN data - " ++
      "(a) the val-0 fibre part is EMPTY (olcFibre_val0_filter_eq_empty_of_" ++
      "memberEven; a val-0 member is an odd raw hit by the wave-10 reset law, but " ++
      "members are even), so QOddVal0AtMostOne holds FREE (qOddVal0AtMostOne_of_" ++
      "memberEven) and every member has carryVal2 >= 1 (carryVal2_pos_of_" ++
      "memberEven); returnZero reduces to QOddValPosZeroRun ALONE " ++
      "(returnZeroBody_iff_valPosZeroRun_of_memberEven, datum form " ++
      "returnZero_reduces_of_parityEvenDatum).  (b) every k+1 is ODD, the doubling " ++
      "branch of QOddMaxCleanSplit is EMPTY, and returnMaxClean reduces to the " ++
      "pure carry-parity branch (returnMaxCleanBody_iff_carryParity_of_memberEven, " ++
      "datum form returnMaxClean_reduces_of_parityEvenDatum).  On the FOUR " ++
      "member-ODD data the mirror: the carry-parity branch is empty (its content " ++
      "automatic, succ_carry_even_of_memberOdd via carryOf_emod_two_eq_zero_at_" ++
      "even_succ) and returnMaxClean reduces to pure doubling " ++
      "(returnMaxCleanBody_iff_doubling_of_memberOdd, datum form " ++
      "returnMaxClean_reduces_of_parityOddDatum); the val-0 clause keeps FULL " ++
      "content there - every member is a val-0 candidate.  HONEST: no clause is " ++
      "closed outright on parity-free data; QOddValPosZeroRun stays open " ++
      "everywhere; the doubling demand stays open on member-ODD data.",
    "THE 63@10 INSTANCE (goal 3, both lanes, honest): the CLASS-1 fibre carries " ++
      "the proved EVEN congruence k % 2 = 0 (class1Fibre_residue_of_datum_63_10, " ++
      "band-4 residue {2} of the period-2 cycle 17 -> 5); the CLASS-4 fibre " ++
      "carries the OPPOSITE pin k % 2 = 1 (olcFibre_odd_of_datum_63_10, band-2 " ++
      "residue {1} of the SAME cycle - index 1 reads band 2 at value 17, index 2 " ++
      "reads band 4 at value 5).  Dual record datum_63_10_dual_parity.  " ++
      "CONSEQUENCE: at 63@10 the digit-side closure delivered is the member-ODD " ++
      "mirror - returnMaxClean IS pure doubling (returnMaxClean_doubling_of_" ++
      "datum_63_10) and the successor carry parity is automatic " ++
      "(datum_63_10_succ_carry_even); the val-0-emptiness lever does NOT attach " ++
      "to the class-4 lane at this pair (it would need member-EVEN).",
    "ODD-c CHARACTERIZATION (goal 4, honest): for c odd, k mod c NEVER determines " ++
      "k mod 2 (oddPeriod_residue_parity_free) - no emptiness is claimed.  " ++
      "Delivered counts: on a b2 = 1 odd-period datum the fibre is c-spaced, its " ++
      "odd members are 2c-spaced (two_mul_dvd_of_dvd_of_odd, " ++
      "olcFibre_odd_pair_two_mul_dvd_of_band2_unique_oddc), so #odd <= " ++
      "ceil(W/(2c)) (olcFibre_odd_card_le_of_band2_unique_oddc via the generic " ++
      "spaced_finset_card_le) and #val-0 <= ceil(W/(2c)) at Q odd " ++
      "(olcFibre_val0_card_le_of_band2_unique_oddc).  Closure regimes: W <= 2c " ++
      "gives QOddVal0AtMostOne FREE (qOddVal0AtMostOne_of_band2_unique_oddc) - " ++
      "DOUBLE the wave-5 spaced-singleton regime W <= c; instance (63,31) on " ++
      "W <= 10 (qOddVal0AtMostOne_of_datum_63_31); generic W <= 2 micro-lever at " ++
      "EVERY Q-odd context (qOddVal0AtMostOne_of_width_le_two), which at the " ++
      "confined (3,1) fixed point (c = 1) is exactly the W <= 2c regime.",
    "CAPSTONE BRIDGES (goal 5, additive): ReturnZeroQOddParityReducedField (val-0 " ++
      "clause demanded only OFF the six member-EVEN data) and " ++
      "ReturnMaxCleanQOddParityReducedField (only the LIVE branch demanded per " ++
      "datum class) rebuild the verbatim wave-11 split fields " ++
      "(returnZeroQOddSplitField_of_parityReduced / " ++
      "returnMaxCleanQOddSplitField_of_parityReduced); converse witnesses " ++
      "parityReducedFields_of_split (the reduced fields are weakenings); surface " ++
      "override splitResidual_withParityReduced : Erdos260SplitResidual; endpoint " ++
      "erdos260_of_parityReducedSplit : Erdos260Statement.  Strictly-weaker-to-" ++
      "provide accounting: the Q-odd returnZero obligation drops the val-0 clause " ++
      "on six pairs; the Q-odd returnMaxClean obligation drops one branch on ten " ++
      "pairs.",
    "HYGIENE: additive only; no upstream module touched; no sorry / admit / new " ++
      "axiom / native_decide (decide only on closed orbit arithmetic with values " ++
      "< 64 and periods <= 8); all #print axioms in [propext, Classical.choice, " ++
      "Quot.sound]." ]

theorem parityResidueClosureStatus_nonempty : parityResidueClosureStatus ≠ [] := by
  simp [parityResidueClosureStatus]

/-! ## Part 7.  Axiom-cleanliness audit -/

#print axioms oddPeriod_residue_parity_free
#print axioms olcFibre_parity_of_band2_parity
#print axioms olcFibre_parity_of_datum_cycle
#print axioms olcFibre_even_of_datum_7_3
#print axioms olcFibre_even_of_datum_31_15
#print axioms olcFibre_even_of_datum_39_1
#print axioms olcFibre_even_of_datum_39_6
#print axioms olcFibre_even_of_datum_55_2
#print axioms olcFibre_even_of_datum_39_19
#print axioms olcFibre_odd_of_datum_13_6
#print axioms olcFibre_odd_of_datum_51_1
#print axioms olcFibre_odd_of_datum_51_8
#print axioms olcFibre_odd_of_datum_63_10
#print axioms olcFibre_even_of_parityEvenDatum
#print axioms olcFibre_odd_of_parityOddDatum
#print axioms olcFibre_val0_filter_eq_empty_of_memberEven
#print axioms qOddVal0AtMostOne_of_memberEven
#print axioms carryVal2_pos_of_memberEven
#print axioms returnZeroBody_iff_valPosZeroRun_of_memberEven
#print axioms qOddMaxCleanSplit_iff_carryParity_of_memberEven
#print axioms qOddMaxCleanSplit_iff_doubling_of_memberOdd
#print axioms returnMaxCleanBody_iff_carryParity_of_memberEven
#print axioms returnMaxCleanBody_iff_doubling_of_memberOdd
#print axioms succ_carry_even_of_memberOdd
#print axioms returnZero_reduces_of_parityEvenDatum
#print axioms returnMaxClean_reduces_of_parityEvenDatum
#print axioms returnMaxClean_reduces_of_parityOddDatum
#print axioms datum_63_10_dual_parity
#print axioms datum_63_10_succ_carry_even
#print axioms returnMaxClean_doubling_of_datum_63_10
#print axioms two_mul_dvd_of_dvd_of_odd
#print axioms spaced_finset_card_le
#print axioms olcFibre_odd_pair_two_mul_dvd_of_band2_unique_oddc
#print axioms olcFibre_odd_card_le_of_band2_unique_oddc
#print axioms olcFibre_val0_card_le_of_band2_unique_oddc
#print axioms qOddVal0AtMostOne_of_width_le_two
#print axioms qOddVal0AtMostOne_of_band2_unique_oddc
#print axioms qOddVal0AtMostOne_of_datum_63_31
#print axioms returnZeroQOddSplitField_of_parityReduced
#print axioms returnMaxCleanQOddSplitField_of_parityReduced
#print axioms parityReducedFields_of_split
#print axioms splitResidual_withParityReduced
#print axioms erdos260_of_parityReducedSplit
#print axioms parityResidueClosureStatus_nonempty

end

end Erdos260
