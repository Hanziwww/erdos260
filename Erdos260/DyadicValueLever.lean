import Erdos260.Erdos260DatumCapstone

/-!
# The dyadic-value lever — the complete `Q`/value arithmetic of the surviving fixed families

This module (NEW; it edits no existing file) settles the wave-5 flag raised at the end of
`Erdos260DatumCapstone.lean`: it determines EXACTLY what the model proves about the shell
denominator `Q` and the Erdős weighted value `Σ n·dₙ/2ⁿ` at a failing shell, consolidates the
per-family value pins (adding the THREE missing tower-pair value pins), and wires the single
voiding fact into every consuming surface in conditional form.

## Goal 1 — what the model proves about `Q` and the value (all per-ctx, unconditional)

* `shell_carry_choose_pos` / `shell_carry_choose_eq_K₀`: the chosen carry numerator is positive
  and equals the orbit base numerator, `P = K₀ > 0`.
* `shell_value_eq_K₀_div_Q` / `shell_value_pos`: the weighted value is EXACTLY `K₀ / Q > 0`.
* `datum_q_eq_oddpartQ_mul` — **the master pin**: `q = oddpart(Q) · (2K₀ + 1)`; every
  per-family `oddpart(Q)` pin of waves 4 is a one-line corollary.
* `shell_Q_scale_bound`: `2²⁷ · Q < X` (the only size constraint: `Q` is scale-bounded above).
* **The model does NOT pin the parity of `Q`**: the shell carries only `0 < Q` (the rationality
  witness denominator is arbitrary — `value = P/Q` is closed under `(P,Q) ↦ (2P,2Q)`), and the
  §25.1 canonical residual center (`runFOfShell`) is deliberately built from `Q/(2Q+1)`, NOT
  from `P/Q`, exactly so that its non-dyadicity (`ResidualCenter.hnondyadic`, `q₀ > 1`) holds
  REGARDLESS of whether `P/Q` is dyadic.  No lemma of the model excludes `Q = 2^t` or `Q = 1`.

## Goal 2 — the five fixed families and their forced values

With `value = K₀/Q` and the master pin, each surviving fixed pair forces the value exactly:

| family | `(q, K₀)` | `oddpart(Q)` | `Q` | value |
|--------|-----------|--------------|-----|-------|
| band 2 (Return)    | `(3, 1)`   | `1` | `2^t`   | `1/2^t`  (dyadic) |
| band 3 (DensePack) | `(21, 3)`  | `3` | `3·2^t` | `1/2^t`  (dyadic) |
| band 4 (Tower)     | `(15, 1)`  | `5` | `5·2^t` | `1/(5·2^t)` |
| band 4 (Tower)     | `(15, 2)`  | `3` | `3·2^t` | `2/(3·2^t)` |
| band 4 (Tower)     | `(105, 7)` | `7` | `7·2^t` | `1/2^t`  (dyadic) |

The band-2/band-3 value pins are wave-4 (`return_datum_value_eq`, `densePack_datum_value_eq`);
the three tower value pins are NEW here (`towerFP15_1_value_eq`, `towerFP15_2_value_eq`,
`towerFP105_7_value_eq` — note `(105, 7)` is ALSO exactly dyadic, `7/(7·2^t) = 1/2^t`).
`fixedFamilyHit_value_pinned` consolidates: ANY fixed-family hit forces
`oddpart(Q) ∈ {1, 3, 5, 7}` and `value = K₀/(oddpart(Q)·2^t)`.

**The model cannot refute these families**, and this module PROVES why at the data level:
`dyadicWitnessDigits` (`dₙ = 1` for `n ≥ 3`) is a genuine binary non-terminating sequence with
weighted value EXACTLY `1` (`dyadicWitnessDigits_value`, from `Σ_{n≥3} n/2ⁿ = 1`), so the
`(Q, d)`-level data of all three dyadic-value families is consistent
(`dyadicValue_family_data_consistent`: `Q ∈ {1, 3, 7}`, `P = Q`, `t = 0`).  Any voiding proof
must therefore use the LARGENESS/FAILURE fields (`hlarge`, `hfailure`, `hXdyadic`) — it cannot
come from `{0 < Q, BinaryDigits, ¬EventuallyZero, value = P/Q}` alone.

## Goal 3 — the lever and the conditional wiring (additive)

`DyadicValueLever` is the SINGLE fact `∀ ctx, ¬∃ t, value = 1/2^t`.  Under it:

* `returnFixedFamily_void` / `densePackFixedFamily_void` / `towerFP105Family_void` — the band-2,
  band-3 and `(105,7)` band-4 families are VOID (no ctx realizes them); hit forms
  `returnClass4FixedHit_void`, `class3FixedHit_void`.
* `datum_band2CycleCount_lt_of_lever` — `b₂ < c` on EVERY period of EVERY ctx (the off-`(3,1)`
  guard of `datum_band2CycleCount_lt_of_offFixed` discharged); fibre form
  `olcFibre_card_le_of_lever`.
* `cycleBand3Residues_card_lt_of_lever` — `b₃ < c` on EVERY period of EVERY ctx; density form
  `densePackStarts_card_le_of_lever_density`.
* `towerFixedPoint_datum_confined_of_lever` — a band-4 fixed hit forces `q = 15, K₀ ≤ 2`;
  `towerBand4CycleCount_lt_of_lever` needs only `q ≠ 15` (the `q ≠ 105` guard discharged).
* The capstone wiring: `TowerEscapeLever` (the wave-4 `TowerEscape` minus the `(105, 7)`
  branch), `Erdos260DyadicLeverResidual` (the wave-4 datum residual with the lever as a field,
  the tower escape shrunk, and the four Return fields plus all four DensePack fields each
  relieved of their surviving fixed family), and the endpoint
  `erdos260_of_dyadicValueLever : Erdos260DyadicLeverResidual → Erdos260Statement`.

The `(15, 1)` / `(15, 2)` pairs are NOT voided by the dyadic lever (their values are the
non-dyadic `1/(5·2^t)`, `2/(3·2^t)`); their exact voiding facts are recorded as
`TowerFifthValueLever` / `TowerThirdsValueLever` (`towerFP15_1Family_void`,
`towerFP15_2Family_void`), and the Q-side alternative for all five families is
`fixedFamilyHit_void_of_oddpartQ` (`oddpart(Q) ∉ {1,3,5,7}`).

## Goal 4 — the honest finding

The model does NOT prove `DyadicValueLever` (nor `Odd Q`, nor `1 < Q`, nor `gcd(P,Q) = 1`),
and `dyadicValue_family_data_consistent` shows it CANNOT be proved from the value data alone.
Everything conditional below is stated as such.  No context is claimed empty.

No `sorry`, `admit`, new `axiom`, or `native_decide`.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 1.  The unconditional `Q`/value inventory of a failing shell -/

/-- The chosen carry numerator of the actual shell is positive (re-export of the wave-3
`failingShell_carry_pos` at the `Classical.choose` witness). -/
theorem shell_carry_choose_pos (ctx : ActualFailureContext) :
    0 < ctx.shell.hrational.choose :=
  failingShell_carry_pos ctx.shell _ ctx.shell.hrational.choose_spec

/-- **The carry numerator IS the orbit base numerator**: `P = K₀` (as integers; `K₀ = |P|`
with `P > 0`).  Every datum statement about `K₀` is a statement about the actual `P`. -/
theorem shell_carry_choose_eq_K₀ (ctx : ActualFailureContext) :
    ctx.shell.hrational.choose = ((class1SlopeDatum ctx).K₀ : ℤ) := by
  have hK := class1SlopeDatum_K₀_eq ctx
  have hpos := shell_carry_choose_pos ctx
  have habs : (ctx.shell.hrational.choose.natAbs : ℤ) = ctx.shell.hrational.choose :=
    Int.natAbs_of_nonneg hpos.le
  rw [hK]
  exact habs.symm

/-- **The weighted value of the actual shell is EXACTLY `K₀ / Q`** — the complete value
identity (the numerator is the orbit base numerator, the denominator the shell field). -/
theorem shell_value_eq_K₀_div_Q (ctx : ActualFailureContext) :
    realWeightedValue (natBinaryAsReal ctx.shell.d)
      = ((class1SlopeDatum ctx).K₀ : ℝ) / (ctx.shell.Q : ℝ) := by
  have hcast : (ctx.shell.hrational.choose : ℝ) = ((class1SlopeDatum ctx).K₀ : ℝ) :=
    (congrArg (fun z : ℤ => (z : ℝ)) (shell_carry_choose_eq_K₀ ctx)).trans
      (Int.cast_natCast _)
  exact ctx.shell.hrational.choose_spec.trans
    (congrArg (fun x : ℝ => x / (ctx.shell.Q : ℝ)) hcast)

/-- The weighted value of a failing shell is strictly positive. -/
theorem shell_value_pos (ctx : ActualFailureContext) :
    0 < realWeightedValue (natBinaryAsReal ctx.shell.d) := by
  rw [shell_value_eq_K₀_div_Q ctx]
  apply div_pos
  · exact_mod_cast (class1SlopeDatum ctx).hK₀_pos
  · exact_mod_cast ctx.shell.hQ

/-- **THE MASTER `Q`-PIN** (unconditional, per ctx): the orbit modulus factors EXACTLY as
`q = oddpart(Q) · (2K₀ + 1)`.  Every wave-4 per-family `oddpart(Q)` pin
(`return_datum_Q_oddPart`, `densePack_datum_Q_oddPart`, `towerFP15_1_oddpartQ`,
`towerFP15_2_oddpartQ`, `towerFP105_7_oddpartQ`) is a one-line corollary. -/
theorem datum_q_eq_oddpartQ_mul (ctx : ActualFailureContext) :
    (class1SlopeDatum ctx).q
      = ordCompl[2] ctx.shell.Q * (2 * (class1SlopeDatum ctx).K₀ + 1) := by
  have hqe := class1SlopeDatum_q_eq ctx
  rw [← class1SlopeDatum_K₀_eq ctx] at hqe
  rw [hqe]
  show ordCompl[2] (ctx.shell.Q * (2 * (class1SlopeDatum ctx).K₀ + 1)) = _
  exact ordCompl_two_mul_odd ctx.shell.hQ.ne' ⟨(class1SlopeDatum ctx).K₀, rfl⟩

/-- The 2-adic split of the shell denominator: `Q = oddpart(Q) · 2^t` with
`t = ν₂(Q)` (true of every positive natural; recorded in the shell's terms). -/
theorem shell_Q_eq_oddpart_mul_pow (ctx : ActualFailureContext) :
    ctx.shell.Q = ordCompl[2] ctx.shell.Q * 2 ^ ctx.shell.Q.factorization 2 := by
  conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self ctx.shell.Q 2]
  exact Nat.mul_comm _ _

/-- **The only size constraint the model puts on `Q`**: the shell denominator is
scale-bounded, `2²⁷ · Q < X` (from the carry-largeness gate `carryB Q + 25 ≤ L`,
`X = 2^L`).  There is NO lower bound beyond `0 < Q` and NO parity constraint. -/
theorem shell_Q_scale_bound (ctx : ActualFailureContext) :
    2 ^ 27 * ctx.shell.Q < ctx.shell.X := by
  have hL : carryB ctx.shell.Q + 25 ≤ Classical.choose ctx.shell.hXdyadic :=
    ctx.shell_carryLarge
  have hX : ctx.shell.X = 2 ^ Classical.choose ctx.shell.hXdyadic :=
    Classical.choose_spec ctx.shell.hXdyadic
  have hlog : ctx.shell.Q * 4 < 2 ^ carryB ctx.shell.Q := by
    unfold carryB
    exact Nat.lt_pow_succ_log_self (by norm_num) _
  have hmono : 2 ^ (carryB ctx.shell.Q + 25)
      ≤ 2 ^ Classical.choose ctx.shell.hXdyadic :=
    Nat.pow_le_pow_right (by norm_num) hL
  calc 2 ^ 27 * ctx.shell.Q = (ctx.shell.Q * 4) * 2 ^ 25 := by ring
    _ < 2 ^ carryB ctx.shell.Q * 2 ^ 25 :=
        mul_lt_mul_of_pos_right hlog (by positivity)
    _ = 2 ^ (carryB ctx.shell.Q + 25) := (pow_add 2 _ 25).symm
    _ ≤ 2 ^ Classical.choose ctx.shell.hXdyadic := hmono
    _ = ctx.shell.X := hX.symm

/-- **The complete unconditional `Q`-surface of the model, consolidated**: positivity of `Q`,
positivity of the carry numerator, the exact value identity, and the scale bound.  This is
EVERYTHING the model proves about `Q` at a failing shell — in particular nothing pins the
parity of `Q`. -/
theorem shell_Q_constraints (ctx : ActualFailureContext) :
    0 < ctx.shell.Q
    ∧ 0 < ctx.shell.hrational.choose
    ∧ realWeightedValue (natBinaryAsReal ctx.shell.d)
        = (ctx.shell.hrational.choose : ℝ) / (ctx.shell.Q : ℝ)
    ∧ 2 ^ 27 * ctx.shell.Q < ctx.shell.X :=
  ⟨ctx.shell.hQ, shell_carry_choose_pos ctx, ctx.shell.hrational.choose_spec,
    shell_Q_scale_bound ctx⟩

/-! ## Part 2.  The value rigidity of the fixed families — the three NEW tower value pins -/

/-- **The value-rigidity engine**: any pin `oddpart(Q) = u` forces `Q = u · 2^t` and
`value = K₀ / (u · 2^t)` — the complete shape of the weighted value from the odd part. -/
theorem datum_value_eq_of_oddpartQ (ctx : ActualFailureContext) {u : ℕ}
    (hu : ordCompl[2] ctx.shell.Q = u) :
    ∃ t : ℕ, ctx.shell.Q = u * 2 ^ t
      ∧ realWeightedValue (natBinaryAsReal ctx.shell.d)
          = ((class1SlopeDatum ctx).K₀ : ℝ) / ((u : ℝ) * 2 ^ t) := by
  have hQ : ctx.shell.Q = u * 2 ^ ctx.shell.Q.factorization 2 := by
    have h := shell_Q_eq_oddpart_mul_pow ctx
    rw [hu] at h
    exact h
  refine ⟨ctx.shell.Q.factorization 2, hQ, ?_⟩
  have hcast : (ctx.shell.Q : ℝ) = (u : ℝ) * 2 ^ ctx.shell.Q.factorization 2 := by
    conv_lhs => rw [hQ]
    push_cast
    ring
  exact (shell_value_eq_K₀_div_Q ctx).trans
    (congrArg (fun x : ℝ => ((class1SlopeDatum ctx).K₀ : ℝ) / x) hcast)

/-- **NEW tower value pin at `(15, 1)`**: `Q = 5 · 2^t` and the weighted value is EXACTLY
`1/(5·2^t)` — NOT dyadic (odd part `5`). -/
theorem towerFP15_1_value_eq (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 15) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    ∃ t : ℕ, ctx.shell.Q = 5 * 2 ^ t
      ∧ realWeightedValue (natBinaryAsReal ctx.shell.d) = 1 / (5 * 2 ^ t) := by
  obtain ⟨t, hQ, hval⟩ := datum_value_eq_of_oddpartQ ctx (towerFP15_1_oddpartQ ctx hq hK)
  refine ⟨t, hQ, ?_⟩
  rw [hval, hK]
  norm_num

/-- **NEW tower value pin at `(15, 2)`**: `Q = 3 · 2^t` and the weighted value is EXACTLY
`2/(3·2^t)` — NOT dyadic (odd part `3`). -/
theorem towerFP15_2_value_eq (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 15) (hK : (class1SlopeDatum ctx).K₀ = 2) :
    ∃ t : ℕ, ctx.shell.Q = 3 * 2 ^ t
      ∧ realWeightedValue (natBinaryAsReal ctx.shell.d) = 2 / (3 * 2 ^ t) := by
  obtain ⟨t, hQ, hval⟩ := datum_value_eq_of_oddpartQ ctx (towerFP15_2_oddpartQ ctx hq hK)
  refine ⟨t, hQ, ?_⟩
  rw [hval, hK]
  norm_num

/-- **NEW tower value pin at `(105, 7)`**: `Q = 7 · 2^t` and the weighted value is EXACTLY
the dyadic reciprocal `7/(7·2^t) = 1/2^t` — the THIRD exactly-dyadic family, alongside the
band-2 `(3,1)` and band-3 `(21,3)` survivors. -/
theorem towerFP105_7_value_eq (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 105) (hK : (class1SlopeDatum ctx).K₀ = 7) :
    ∃ t : ℕ, ctx.shell.Q = 7 * 2 ^ t
      ∧ realWeightedValue (natBinaryAsReal ctx.shell.d) = 1 / 2 ^ t := by
  obtain ⟨t, hQ, hval⟩ := datum_value_eq_of_oddpartQ ctx (towerFP105_7_oddpartQ ctx hq hK)
  refine ⟨t, hQ, ?_⟩
  rw [hval, hK]
  rw [div_eq_div_iff (by positivity) (by positivity)]
  push_cast
  ring

/-- **The five surviving fixed pairs**, across bands 2, 3 and 4 (the complete fixed-point
escape set of the wave-4 datum confinements). -/
def FixedFamilyHit (ctx : ActualFailureContext) : Prop :=
  ((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1)
  ∨ ((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3)
  ∨ ((class1SlopeDatum ctx).q = 15 ∧ (class1SlopeDatum ctx).K₀ = 1)
  ∨ ((class1SlopeDatum ctx).q = 15 ∧ (class1SlopeDatum ctx).K₀ = 2)
  ∨ ((class1SlopeDatum ctx).q = 105 ∧ (class1SlopeDatum ctx).K₀ = 7)

/-- **Any fixed-family hit confines the odd part of `Q` to `{1, 3, 5, 7}`** — the
consolidated Q-side rigidity of all five surviving pairs (via the master pin). -/
theorem fixedFamilyHit_oddpartQ_mem (ctx : ActualFailureContext) (h : FixedFamilyHit ctx) :
    ordCompl[2] ctx.shell.Q ∈ ({1, 3, 5, 7} : Finset ℕ) := by
  have hpin := datum_q_eq_oddpartQ_mul ctx
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rcases h with ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ <;>
    rw [hq, hK] at hpin <;> omega

/-- **The full value rigidity**: any fixed-family hit forces `oddpart(Q) ∈ {1,3,5,7}`,
`Q = oddpart(Q) · 2^t`, and `value = K₀ / (oddpart(Q) · 2^t)` — the weighted value of every
surviving family is a rational with denominator-odd-part at most `7`. -/
theorem fixedFamilyHit_value_pinned (ctx : ActualFailureContext) (h : FixedFamilyHit ctx) :
    ∃ u t : ℕ, u ∈ ({1, 3, 5, 7} : Finset ℕ)
      ∧ ctx.shell.Q = u * 2 ^ t
      ∧ realWeightedValue (natBinaryAsReal ctx.shell.d)
          = ((class1SlopeDatum ctx).K₀ : ℝ) / ((u : ℝ) * 2 ^ t) := by
  obtain ⟨t, hQ, hval⟩ := datum_value_eq_of_oddpartQ ctx rfl
  exact ⟨ordCompl[2] ctx.shell.Q, t, fixedFamilyHit_oddpartQ_mem ctx h, hQ, hval⟩

/-- The odd part of an odd number is itself. -/
theorem ordCompl_two_of_odd {Q : ℕ} (hodd : Odd Q) : ordCompl[2] Q = Q := by
  have h2 : ¬ (2 ∣ Q) := by
    rcases hodd with ⟨m, rfl⟩
    omega
  show Q / 2 ^ Q.factorization 2 = Q
  rw [Nat.factorization_eq_zero_of_not_dvd h2, pow_zero, Nat.div_one]

/-- **The hypothetical-odd-`Q` confinement** (per ctx, answering the wave-5 question "if `Q`
were odd, where could the fixed families live?"): an odd `Q` on any fixed-family hit lies in
`{1, 3, 5, 7}` EXACTLY — in particular the band-2 family would force the integer-value shell
`Q = 1`, `value = K₀ = 1`.  The model proves NO exclusion of these small odd `Q` values. -/
theorem fixedFamilyHit_Q_mem_of_oddQ (ctx : ActualFailureContext)
    (hodd : Odd ctx.shell.Q) (h : FixedFamilyHit ctx) :
    ctx.shell.Q ∈ ({1, 3, 5, 7} : Finset ℕ) := by
  have hmem := fixedFamilyHit_oddpartQ_mem ctx h
  rwa [ordCompl_two_of_odd hodd] at hmem

/-! ## Part 3.  The dyadic-value predicate and its exact characterization -/

/-- The weighted value of the shell is EXACTLY a dyadic reciprocal `1/2^t` — the shape forced
on the band-2 `(3,1)`, band-3 `(21,3)` and band-4 `(105,7)` surviving families. -/
def ShellValueDyadic (ctx : ActualFailureContext) : Prop :=
  ∃ t : ℕ, realWeightedValue (natBinaryAsReal ctx.shell.d) = 1 / 2 ^ t

/-- **The exact `Q`-side characterization of the dyadic-reciprocal value**:
`value = 1/2^t` for some `t` IFF `Q = K₀ · 2^t` for some `t` (the denominator is the
numerator times a power of two). -/
theorem shellValueDyadic_iff (ctx : ActualFailureContext) :
    ShellValueDyadic ctx
      ↔ ∃ t : ℕ, ctx.shell.Q = (class1SlopeDatum ctx).K₀ * 2 ^ t := by
  have hv := shell_value_eq_K₀_div_Q ctx
  have hQne : (ctx.shell.Q : ℝ) ≠ 0 := by
    have hpos : (0 : ℝ) < (ctx.shell.Q : ℝ) := by exact_mod_cast ctx.shell.hQ
    exact hpos.ne'
  have hK0pos : (0 : ℝ) < ((class1SlopeDatum ctx).K₀ : ℝ) := by
    exact_mod_cast (class1SlopeDatum ctx).hK₀_pos
  constructor
  · rintro ⟨t, hval⟩
    refine ⟨t, ?_⟩
    have heq : ((class1SlopeDatum ctx).K₀ : ℝ) / (ctx.shell.Q : ℝ) = 1 / 2 ^ t :=
      hv.symm.trans hval
    rw [div_eq_div_iff hQne (by positivity : (2 : ℝ) ^ t ≠ 0)] at heq
    rw [one_mul] at heq
    exact_mod_cast heq.symm
  · rintro ⟨t, hQ⟩
    refine ⟨t, ?_⟩
    have hcast : (ctx.shell.Q : ℝ) = ((class1SlopeDatum ctx).K₀ : ℝ) * 2 ^ t := by
      conv_lhs => rw [hQ]
      push_cast
      ring
    refine hv.trans ?_
    calc ((class1SlopeDatum ctx).K₀ : ℝ) / (ctx.shell.Q : ℝ)
        = ((class1SlopeDatum ctx).K₀ : ℝ)
            / (((class1SlopeDatum ctx).K₀ : ℝ) * 2 ^ t) :=
          congrArg (fun x : ℝ => ((class1SlopeDatum ctx).K₀ : ℝ) / x) hcast
      _ = 1 / 2 ^ t := by
          rw [div_eq_div_iff
            (mul_ne_zero hK0pos.ne' (by positivity : (2 : ℝ) ^ t ≠ 0))
            (by positivity : (2 : ℝ) ^ t ≠ 0)]
          ring

/-- The band-2 `(3, 1)` family forces a dyadic value (wave-4 `return_datum_value_eq`). -/
theorem shellValueDyadic_of_return_datum (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 3) (hK : (class1SlopeDatum ctx).K₀ = 1) :
    ShellValueDyadic ctx := by
  obtain ⟨t, _, hval⟩ := return_datum_value_eq ctx hq hK
  exact ⟨t, hval⟩

/-- The band-3 `(21, 3)` family forces a dyadic value (wave-4 `densePack_datum_value_eq`). -/
theorem shellValueDyadic_of_densePack_datum (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 21) (hK : (class1SlopeDatum ctx).K₀ = 3) :
    ShellValueDyadic ctx := by
  obtain ⟨t, _, hval⟩ := densePack_datum_value_eq ctx hq hK
  exact ⟨t, hval⟩

/-- The band-4 `(105, 7)` family forces a dyadic value (NEW, `towerFP105_7_value_eq`). -/
theorem shellValueDyadic_of_towerFP105 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 105) (hK : (class1SlopeDatum ctx).K₀ = 7) :
    ShellValueDyadic ctx := by
  obtain ⟨t, _, hval⟩ := towerFP105_7_value_eq ctx hq hK
  exact ⟨t, hval⟩

/-! ## Part 4.  The witness: the dyadic-value data is CONSISTENT — no refutation can come
from the value side

`dₙ = 1` for `n ≥ 3` is binary, non-terminating, and `Σ_{n≥3} n/2ⁿ = 2 − 1/2 − 1/2 = 1`
EXACTLY: the weighted value is `1 = 1/2⁰`, realizable with denominators `Q ∈ {1, 3, 7}`
(`P = Q`).  Hence the `(Q, d)`-level data of all three dyadic-value families is realizable,
and any voiding of them MUST use the largeness/failure fields of the context. -/

/-- The witness digit sequence: `dₙ = 1` exactly for `n ≥ 3`. -/
def dyadicWitnessDigits : ℕ → ℕ := fun n => if 3 ≤ n then 1 else 0

theorem dyadicWitnessDigits_binary : BinaryDigits dyadicWitnessDigits := by
  intro n
  unfold dyadicWitnessDigits
  by_cases h : 3 ≤ n <;> simp [h]

theorem dyadicWitnessDigits_not_eventuallyZero : ¬ EventuallyZero dyadicWitnessDigits := by
  rintro ⟨N, hN⟩
  have h := hN (N + 3) (by omega)
  unfold dyadicWitnessDigits at h
  rw [if_pos (by omega)] at h
  exact absurd h one_ne_zero

/-- The weighted series of the witness sums EXACTLY to `1`: the full sum
`Σ_{n≥1} n/2ⁿ = 2` minus the two missing terms `1/2 + 2/4 = 1`. -/
theorem dyadicWitnessDigits_hasSum :
    HasSum (realWeightedTerm (natBinaryAsReal dyadicWitnessDigits)) 1 := by
  have h2 : HasSum (fun n : ℕ => (n : ℝ) * (1 / 2 : ℝ) ^ n) 2 := by
    have h0 := hasSum_coe_mul_geometric_of_norm_lt_one
      (r := (1 / 2 : ℝ)) (by norm_num)
    have he : (1 / 2 : ℝ) / (1 - 1 / 2) ^ 2 = 2 := by norm_num
    rwa [he] at h0
  have h3 : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ (n + 1)) 2 := by
    have h := hasSum_nat_tail h2 1
    simpa [Finset.sum_range_one] using h
  have e0 : HasSum (fun i : ℕ => if i = 0 then (1 / 2 : ℝ) else 0) (1 / 2 : ℝ) :=
    hasSum_ite_eq 0 (1 / 2 : ℝ)
  have e1 : HasSum (fun i : ℕ => if i = 1 then (1 / 2 : ℝ) else 0) (1 / 2 : ℝ) :=
    hasSum_ite_eq 1 (1 / 2 : ℝ)
  have hcorr : HasSum (fun i : ℕ =>
      (if i = 0 then (1 / 2 : ℝ) else 0) + (if i = 1 then (1 / 2 : ℝ) else 0)) 1 := by
    have h := e0.add e1
    have hh : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
    rwa [hh] at h
  have hsub := h3.sub hcorr
  have h21 : (2 : ℝ) - 1 = 1 := by norm_num
  rw [h21] at hsub
  have hfun : realWeightedTerm (natBinaryAsReal dyadicWitnessDigits)
      = fun n : ℕ => ((n + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ (n + 1)
          - ((if n = 0 then (1 / 2 : ℝ) else 0) + (if n = 1 then (1 / 2 : ℝ) else 0)) := by
    funext n
    by_cases h0 : n = 0
    · subst h0
      norm_num [realWeightedTerm, natBinaryAsReal, dyadicWitnessDigits]
    · by_cases h1 : n = 1
      · subst h1
        norm_num [realWeightedTerm, natBinaryAsReal, dyadicWitnessDigits]
      · have h3le : 3 ≤ n + 1 := by omega
        simp only [realWeightedTerm, natBinaryAsReal, dyadicWitnessDigits,
          if_pos h3le, if_neg h0, if_neg h1, Nat.cast_one, mul_one, add_zero, sub_zero]
        rw [one_div_pow]
        push_cast
        ring
  rw [hfun]
  exact hsub

/-- **The witness value**: `Σ n·dₙ/2ⁿ = 1` exactly for the witness digits. -/
theorem dyadicWitnessDigits_value :
    realWeightedValue (natBinaryAsReal dyadicWitnessDigits) = 1 := by
  unfold realWeightedValue
  exact dyadicWitnessDigits_hasSum.tsum_eq

/-- **THE CONSISTENCY THEOREM**: a genuine binary non-terminating digit sequence with weighted
value EXACTLY the dyadic reciprocal `1/2⁰ = 1`, realizable with each of the denominators
`Q ∈ {1, 3, 7}` pinned by the three dyadic-value families (carry numerator `P = Q > 0`).
Hence `{0 < Q, BinaryDigits d, ¬EventuallyZero d, value = P/Q}` admits dyadic-value models:
NO refutation of the surviving families can be proved from the value-side data alone — any
voiding proof must use the largeness/failure fields (`hlarge`, `hfailure`, `hXdyadic`). -/
theorem dyadicValue_family_data_consistent :
    ∃ d : ℕ → ℕ, BinaryDigits d ∧ ¬ EventuallyZero d
      ∧ realWeightedValue (natBinaryAsReal d) = 1 / 2 ^ 0
      ∧ ∀ Q : ℕ, Q = 1 ∨ Q = 3 ∨ Q = 7 →
          ∃ P : ℤ, 0 < P ∧ realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ) := by
  refine ⟨dyadicWitnessDigits, dyadicWitnessDigits_binary,
    dyadicWitnessDigits_not_eventuallyZero, ?_, ?_⟩
  · rw [dyadicWitnessDigits_value]
    norm_num
  · intro Q hQ
    refine ⟨(Q : ℤ), ?_, ?_⟩
    · rcases hQ with rfl | rfl | rfl <;> norm_num
    · rw [dyadicWitnessDigits_value]
      rcases hQ with rfl | rfl | rfl <;> norm_num

/-! ## Part 5.  The levers and the family voidings (conditional, stated honestly)

`DyadicValueLever` is the single unproven fact that voids the three dyadic-value families;
`TowerFifthValueLever` / `TowerThirdsValueLever` are the exact analogues for the two
non-dyadic tower pairs.  None of these is proved by the model (Part 4 shows the first cannot
be proved from the value data alone). -/

/-- **The dyadic-value lever** — the single fact that voids the band-2 `(3,1)`, band-3
`(21,3)` and band-4 `(105,7)` families wholesale: no failing shell has weighted value exactly
a dyadic reciprocal. -/
def DyadicValueLever : Prop :=
  ∀ ctx : ActualFailureContext, ¬ ShellValueDyadic ctx

/-- The exact voiding fact for the tower pair `(15, 1)`: no failing shell has value
`1/(5·2^t)`. -/
def TowerFifthValueLever : Prop :=
  ∀ ctx : ActualFailureContext,
    ∀ t : ℕ, realWeightedValue (natBinaryAsReal ctx.shell.d) ≠ 1 / (5 * 2 ^ t)

/-- The exact voiding fact for the tower pair `(15, 2)`: no failing shell has value
`2/(3·2^t)`. -/
def TowerThirdsValueLever : Prop :=
  ∀ ctx : ActualFailureContext,
    ∀ t : ℕ, realWeightedValue (natBinaryAsReal ctx.shell.d) ≠ 2 / (3 * 2 ^ t)

/-- **Under the lever the band-2 fixed family is VOID**: no ctx realizes `(q, K₀) = (3, 1)`. -/
theorem returnFixedFamily_void (h : DyadicValueLever) (ctx : ActualFailureContext) :
    ¬((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1) := by
  rintro ⟨hq, hK⟩
  exact h ctx (shellValueDyadic_of_return_datum ctx hq hK)

/-- **Under the lever the band-3 fixed family is VOID**: no ctx realizes `(q, K₀) = (21, 3)`. -/
theorem densePackFixedFamily_void (h : DyadicValueLever) (ctx : ActualFailureContext) :
    ¬((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3) := by
  rintro ⟨hq, hK⟩
  exact h ctx (shellValueDyadic_of_densePack_datum ctx hq hK)

/-- **Under the lever the band-4 fixed pair `(105, 7)` is VOID** (its value is also exactly
dyadic — the NEW pin of this module). -/
theorem towerFP105Family_void (h : DyadicValueLever) (ctx : ActualFailureContext) :
    ¬((class1SlopeDatum ctx).q = 105 ∧ (class1SlopeDatum ctx).K₀ = 7) := by
  rintro ⟨hq, hK⟩
  exact h ctx (shellValueDyadic_of_towerFP105 ctx hq hK)

/-- Under the fifth-value lever the tower pair `(15, 1)` is void. -/
theorem towerFP15_1Family_void (h : TowerFifthValueLever) (ctx : ActualFailureContext) :
    ¬((class1SlopeDatum ctx).q = 15 ∧ (class1SlopeDatum ctx).K₀ = 1) := by
  rintro ⟨hq, hK⟩
  obtain ⟨t, _, hval⟩ := towerFP15_1_value_eq ctx hq hK
  exact h ctx t hval

/-- Under the thirds-value lever the tower pair `(15, 2)` is void. -/
theorem towerFP15_2Family_void (h : TowerThirdsValueLever) (ctx : ActualFailureContext) :
    ¬((class1SlopeDatum ctx).q = 15 ∧ (class1SlopeDatum ctx).K₀ = 2) := by
  rintro ⟨hq, hK⟩
  obtain ⟨t, _, hval⟩ := towerFP15_2_value_eq ctx hq hK
  exact h ctx t hval

/-- **The Q-side master voiding**: if no failing shell has `oddpart(Q) ∈ {1, 3, 5, 7}`, then
ALL FIVE fixed families are void at once. -/
theorem fixedFamilyHit_void_of_oddpartQ
    (h : ∀ ctx : ActualFailureContext,
      ordCompl[2] ctx.shell.Q ∉ ({1, 3, 5, 7} : Finset ℕ))
    (ctx : ActualFailureContext) :
    ¬ FixedFamilyHit ctx :=
  fun hhit => h ctx (fixedFamilyHit_oddpartQ_mem ctx hhit)

/-- The band-2 voiding from the weaker Q-side fact `oddpart(Q) > 1` ("Q is never a pure
power of two") — the single-family version. -/
theorem returnFixedFamily_void_of_oddpartQ
    (h : ∀ ctx : ActualFailureContext, 1 < ordCompl[2] ctx.shell.Q)
    (ctx : ActualFailureContext) :
    ¬((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1) := by
  rintro ⟨hq, hK⟩
  have h1 := return_datum_Q_oddPart ctx hq hK
  have h2 := h ctx
  omega

/-- Under the lever the band-2 fixed HIT is impossible at every index. -/
theorem returnClass4FixedHit_void (h : DyadicValueLever) (ctx : ActualFailureContext) :
    ¬ ReturnClass4FixedHit ctx :=
  fun hhit => returnFixedFamily_void h ctx (returnClass4FixedHit_datum ctx hhit)

/-- Under the lever the band-3 fixed HIT is impossible at every index. -/
theorem class3FixedHit_void (h : DyadicValueLever) (ctx : ActualFailureContext) :
    ¬ Class3FixedHit ctx :=
  fun hhit => densePackFixedFamily_void h ctx (class3FixedHit_datum ctx hhit)

/-! ## Part 6.  The upgraded cycle-density bounds under the lever -/

/-- **`b₂ < c` on EVERY period of EVERY ctx under the lever** — the off-`(3,1)` guard of
`datum_band2CycleCount_lt_of_offFixed` is discharged: band-2 cycle density `1` is impossible
everywhere. -/
theorem datum_band2CycleCount_lt_of_lever (h : DyadicValueLever)
    (ctx : ActualFailureContext) {c : ℕ} (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m) :
    band2CycleCount (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ c < c :=
  datum_band2CycleCount_lt_of_offFixed ctx (returnFixedFamily_void h ctx) hc hper

/-- The unconditional-under-the-lever class-4 fibre bound: `|fibre₄| ≤ t·b₂` AND `b₂ < c` on
every ctx (the quantitative form of `olcFibre_card_le_offFixed`, guard discharged). -/
theorem olcFibre_card_le_of_lever (h : DyadicValueLever)
    (ctx : ActualFailureContext) {c t : ℕ} (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hcover : (supportShell ctx.shell.d ctx.shell.X).card ≤ t * c) :
    (olcFibre ctx).card
        ≤ t * band2CycleCount (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ c
      ∧ band2CycleCount (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ c < c :=
  olcFibre_card_le_offFixed ctx (returnFixedFamily_void h ctx) hc hper hcover

/-- **`b₃ < c` on EVERY period of EVERY ctx under the lever** — the off-`(21,3)` guard of
`cycleBand3Residues_card_lt_of_offDatum` is discharged. -/
theorem cycleBand3Residues_card_lt_of_lever (h : DyadicValueLever)
    (ctx : ActualFailureContext) {c : ℕ} (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m) :
    (cycleBand3Residues ctx c).card < c :=
  cycleBand3Residues_card_lt_of_offDatum ctx (densePackFixedFamily_void h ctx) hc hper

/-- The unconditional-under-the-lever band-3 density count: SOME period `1 ≤ c ≤ q` carries
both the cover bound and the strict deficit `b₃ < c`, on EVERY ctx. -/
theorem densePackStarts_card_le_of_lever_density (h : DyadicValueLever)
    (ctx : ActualFailureContext) :
    ∃ c, 1 ≤ c ∧ c ≤ (class1SlopeDatum ctx).q
      ∧ (cycleBand3Residues ctx c).card < c
      ∧ (genuineDensePackStarts ctx).card
        ≤ (cycleBand3Residues ctx c).card
          * (((supportShell ctx.shell.d ctx.shell.X).card - 1) / c + 2) :=
  densePackStarts_card_le_offDatum_density ctx (densePackFixedFamily_void h ctx)

/-- **The band-4 fixed-hit confinement under the lever**: a `1/15` fixed hit forces
`q = 15 ∧ K₀ ≤ 2` — the `(105, 7)` branch of `towerFixedPoint_datum_confined` is voided. -/
theorem towerFixedPoint_datum_confined_of_lever (h : DyadicValueLever)
    (ctx : ActualFailureContext)
    (hfix : 15 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 1
        = (class1SlopeDatum ctx).q) :
    (class1SlopeDatum ctx).q = 15 ∧ (class1SlopeDatum ctx).K₀ ≤ 2 := by
  rcases towerFixedPoint_datum_confined ctx hfix with h1 | h2 | h3
  · exact ⟨h1.1, by omega⟩
  · exact ⟨h2.1, by omega⟩
  · exact absurd h3 (towerFP105Family_void h ctx)

/-- **`b₄ < c` needs only `q ≠ 15` under the lever** — the `q ≠ 105` guard of
`towerBand4CycleCount_lt_of_datum_off` is discharged. -/
theorem towerBand4CycleCount_lt_of_lever (h : DyadicValueLever)
    (ctx : ActualFailureContext) {c : ℕ} (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (h15 : (class1SlopeDatum ctx).q ≠ 15) :
    towerBand4CycleCount (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ c < c := by
  refine towerBand4CycleCount_lt_of_not_fixed (class1SlopeDatum ctx).hq_odd
    (class1SlopeDatum ctx).hK₀_pos (class1SlopeDatum ctx).hK₀_lt hc hper ?_
  intro hfix
  exact h15 (towerFixedPoint_datum_confined_of_lever h ctx hfix).1

/-! ## Part 7.  The capstone wiring (additive): the lever-shrunk wave-4 surfaces

The tower escape surface drops its `(105, 7)` branch; the four Return fields and the four
DensePack fields are each relieved of their surviving fixed family.  Everything bridges back
into `Erdos260DatumResidual` losslessly through the voidings. -/

/-- **The lever-shrunk tower escape surface** — `TowerEscape` with the `(105, K₀ = 7)` branch
removed (it is void under the lever); `q = 105` survives only via the counted
`m₀ ≥ 8` configuration. -/
def TowerEscapeLever (ctx : ActualFailureContext) : Prop :=
  ((class1SlopeDatum ctx).q = 9 ∧ 3 ≤ towerSparsityBlock ctx)
  ∨ ((class1SlopeDatum ctx).q = 11 ∧ 5 ≤ towerSparsityBlock ctx)
  ∨ ((class1SlopeDatum ctx).q = 13 ∧ 6 ≤ towerSparsityBlock ctx)
  ∨ ((class1SlopeDatum ctx).q = 15 ∧ (class1SlopeDatum ctx).K₀ ≤ 2)
  ∨ ((class1SlopeDatum ctx).q = 105 ∧ 8 ≤ towerSparsityBlock ctx)
  ∨ (25 ≤ (class1SlopeDatum ctx).q ∧ (class1SlopeDatum ctx).q ≠ 105)

/-- The lever escape surface is contained in the wave-4 one (the new surface demands less). -/
theorem towerEscape_of_towerEscapeLever (ctx : ActualFailureContext)
    (h : TowerEscapeLever ctx) : TowerEscape ctx := by
  rcases h with h1 | h2 | h3 | h4 | ⟨hq, hm⟩ | h6
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hq, Or.inr hm⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h6))))

/-- **Under the lever every wave-4 escape resolves to a lever escape**: the only dropped
branch — `q = 105` with `K₀ = 7` — is void. -/
theorem towerEscapeLever_of_towerEscape (h : DyadicValueLever)
    (ctx : ActualFailureContext) (hesc : TowerEscape ctx) : TowerEscapeLever ctx := by
  rcases hesc with h1 | h2 | h3 | h4 | ⟨hq, hK7 | hm⟩ | h6
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
  · exact absurd ⟨hq, hK7⟩ (towerFP105Family_void h ctx)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hq, hm⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h6))))

/-- **The lever tower residual**: the cycle inequality demanded ONLY on deep shells whose
datum escapes every wave-4 closure AND the lever voiding — strictly smaller than the wave-4
`TowerFixedPointResidual`. -/
def TowerLeverResidual : Prop :=
  ∀ ctx : ActualFailureContext, towerShallowDepthBound < shellLadderDepth ctx →
    TowerEscapeLever ctx → Class2CycleInequality ctx

/-- The wave-4 tower residual discharges the lever residual (weakening witness: the new
surface is no stronger). -/
theorem towerLeverResidual_of_fixedPointResidual (h : TowerFixedPointResidual) :
    TowerLeverResidual :=
  fun ctx hdeep hesc => h ctx hdeep (towerEscape_of_towerEscapeLever ctx hesc)

/-- **The lever bridge for the tower field**: under the lever, the lever residual rebuilds
the full wave-4 `TowerFixedPointResidual` (the dropped `(105, 7)` branch is void). -/
theorem towerFixedPointResidual_of_lever (h : DyadicValueLever)
    (hres : TowerLeverResidual) : TowerFixedPointResidual :=
  fun ctx hdeep hesc => hres ctx hdeep (towerEscapeLever_of_towerEscape h ctx hesc)

/-- **The lever-guarded DensePack residual** — the wave-4 `DensePackDatumSplitResidual` with
every field additionally relieved of the `(21, 3)` fixed family (void under the lever). -/
structure DensePackLeverSplitResidual where
  /-- Gated field, demanded only off `(21, 3)`. -/
  gatedEmpty : ∀ ctx : ActualFailureContext, class3Gate ctx →
    ¬ Class3TopBandCycleFree ctx →
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
    ¬((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3) →
    genuineDensePackStarts ctx = ∅
  /-- Ungated density field, demanded only off `(21, 3)`. -/
  ungatedDensity : ∀ ctx : ActualFailureContext, ¬ class3Gate ctx →
    ¬ Class3CycleBand3Free ctx →
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
    ¬((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3) →
    densePackEndpointDensity ctx
  /-- Ungated interior field, demanded only off `(21, 3)`. -/
  ungatedInterior : ∀ ctx : ActualFailureContext, ¬ class3Gate ctx →
    ¬ Class3TopBandCycleFree ctx →
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
    ¬((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3) →
    ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r + 1
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card
  /-- Ungated Nat-cover field, demanded only off `(21, 3)`. -/
  ungatedCoverNat : ∀ ctx : ActualFailureContext, ¬ class3Gate ctx →
    ¬ Class3CycleBand3Free ctx →
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
    ¬((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3) →
    (genuineDensePackStarts ctx).card
        * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
            - (2 * shellLadderDepth ctx + 1))
      ≤ (proofV4DensePackActualPoints ctx.shell).card

/-- **The lever bridge for the DensePack fields**: under the lever every `(21, 3)` ctx is
void, so the guarded provider rebuilds the wave-4 `DensePackDatumSplitResidual` verbatim. -/
def DensePackLeverSplitResidual.toDatumSplit (R : DensePackLeverSplitResidual)
    (h : DyadicValueLever) : DensePackDatumSplitResidual where
  gatedEmpty := fun ctx hg hfree hmod =>
    R.gatedEmpty ctx hg hfree hmod (densePackFixedFamily_void h ctx)
  ungatedDensity := fun ctx hg hfree hmod =>
    R.ungatedDensity ctx hg hfree hmod (densePackFixedFamily_void h ctx)
  ungatedInterior := fun ctx hg hfree hmod =>
    R.ungatedInterior ctx hg hfree hmod (densePackFixedFamily_void h ctx)
  ungatedCoverNat := fun ctx hg hfree hmod =>
    R.ungatedCoverNat ctx hg hfree hmod (densePackFixedFamily_void h ctx)

/-- Weakening witness: any wave-4 DensePack provider restricts to the lever surface. -/
def DensePackDatumSplitResidual.toLeverSplit (R : DensePackDatumSplitResidual) :
    DensePackLeverSplitResidual where
  gatedEmpty := fun ctx hg hfree hmod _ => R.gatedEmpty ctx hg hfree hmod
  ungatedDensity := fun ctx hg hfree hmod _ => R.ungatedDensity ctx hg hfree hmod
  ungatedInterior := fun ctx hg hfree hmod _ => R.ungatedInterior ctx hg hfree hmod
  ungatedCoverNat := fun ctx hg hfree hmod _ => R.ungatedCoverNat ctx hg hfree hmod

/-- **The wave-5 lever residual.**  The wave-4 `Erdos260DatumResidual` surface with the
dyadic-value lever as an explicit field, the tower escape shrunk by the `(105, 7)` voiding,
the four Return fields relieved of the `(3, 1)` family, and the DensePack fields relieved of
the `(21, 3)` family.  The lever is an UNPROVEN hypothesis — kept honest as a field. -/
structure Erdos260DyadicLeverResidual where
  /-- The dyadic-value lever (unproven; see `dyadicValue_family_data_consistent` for why it
  cannot follow from the value data alone). -/
  lever : DyadicValueLever
  /-- Tower / class 2 on the lever-shrunk escape surface. -/
  towerFixed : TowerLeverResidual
  /-- Run / class 5 (`r ≥ 1` only), carried verbatim from wave 4. -/
  runNumeric : RunNumericSettlementHyp
  /-- Return / class 4 count gates, demanded only off the (void) `(3, 1)` family. -/
  returnGates : ∀ ctx : ActualFailureContext,
    ¬((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1) →
    64 * ((ctx.n24CarryData.r + 1)
        * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
      < 129 * shellLadderDepth ctx + 64
    ∨ 64 * (ctx.n24CarryData.a
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r)
        - ctx.n24CarryData.a
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X))
      < 2 * (129 * shellLadderDepth ctx + 64)
    ∨ 64 * (ctx.n24CarryData.a
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card - 1)
        - ctx.n24CarryData.a
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X))
      < 129 * shellLadderDepth ctx + 64
    ∨ ∃ c t : ℕ, 1 ≤ c
        ∧ (∀ m, 1 ≤ m →
            slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
              = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
        ∧ (supportShell ctx.shell.d ctx.shell.X).card ≤ t * c
        ∧ t * ((Finset.Icc 1 c).filter (fun j =>
            canonGap (class1SlopeDatum ctx).q
              (slopeOrbit (class1SlopeDatum ctx).q
                (class1SlopeDatum ctx).K₀ j) = 2)).card
            ≤ ctx.n24CarryData.r + 1
  /-- Return / class 4 digit Z (small-carry regime), demanded only off `(3, 1)`. -/
  returnZero : ∀ ctx : ActualFailureContext,
    ¬((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1) →
    (∃ k ∈ olcFibre ctx,
      2 ^ carryVal2 ctx k < (supportShell ctx.shell.d ctx.shell.X).card) →
    ∀ y ∈ (olcFibre ctx).image (returnSelfRefKey ctx),
      ∀ x ∈ olcSlice ctx (returnSelfRefKey ctx) y,
        ∀ z ∈ olcSlice ctx (returnSelfRefKey ctx) y,
          x < z → ∀ j, x < j → j ≤ z → ctx.d j = 0
  /-- Return / class 4 digit clean step, demanded only off `(3, 1)`. -/
  returnMaxClean : ∀ ctx : ActualFailureContext,
    ¬((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1) →
    ∀ k ∈ olcFibre ctx,
    (∀ z ∈ olcFibre ctx, returnSelfRefKey ctx z = returnSelfRefKey ctx k → z ≤ k) →
    ctx.d (k + 1) = 0
  /-- Return / class 4 K.1 interior, demanded only off `(3, 1)` (where the wave-4 honest
  obstruction lived: at `(3, 1)` every orbit residue reads band 2 and the top-band cycle
  check cannot fire — that family is now void). -/
  returnInterior : ∀ ctx : ActualFailureContext,
    ¬((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1) →
    ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4,
      k + ctx.n24CarryData.r + 1
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card
  /-- Chernoff / class 0 survivor checks, carried verbatim from wave 4. -/
  class0Survivor : ∀ ctx : ActualFailureContext, Class0DatumSurvivor ctx →
    Class0WindowCycleCheck ctx
  /-- Chernoff / class 0 large moduli, carried verbatim from wave 4. -/
  class0Big : ∀ ctx : ActualFailureContext, 48 ≤ (class1SlopeDatum ctx).q →
    Class0WindowCycleCheck ctx
  /-- CNL / class 1 datum residual, carried verbatim from wave 4. -/
  class1Datum : Class1DatumResidual
  /-- DensePack / class 3 on the lever-guarded surface. -/
  densePackDatum : DensePackLeverSplitResidual

namespace Erdos260DyadicLeverResidual

/-- **The bridge into the wave-4 datum residual**: every guard is discharged by the lever
voidings — at a `(3, 1)` ctx the lever yields `False` outright (the family is void), and the
tower/DensePack fields bridge through their dedicated lemmas. -/
def toDatum (R : Erdos260DyadicLeverResidual) : Erdos260DatumResidual where
  towerFixed := towerFixedPointResidual_of_lever R.lever R.towerFixed
  runNumeric := R.runNumeric
  returnGates := fun ctx => by
    by_cases hoff : (class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1
    · exact absurd (shellValueDyadic_of_return_datum ctx hoff.1 hoff.2) (R.lever ctx)
    · exact R.returnGates ctx hoff
  returnZero := fun ctx => by
    by_cases hoff : (class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1
    · exact absurd (shellValueDyadic_of_return_datum ctx hoff.1 hoff.2) (R.lever ctx)
    · exact R.returnZero ctx hoff
  returnMaxClean := fun ctx => by
    by_cases hoff : (class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1
    · exact absurd (shellValueDyadic_of_return_datum ctx hoff.1 hoff.2) (R.lever ctx)
    · exact R.returnMaxClean ctx hoff
  returnInterior := fun ctx => by
    by_cases hoff : (class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1
    · exact absurd (shellValueDyadic_of_return_datum ctx hoff.1 hoff.2) (R.lever ctx)
    · exact R.returnInterior ctx hoff
  class0Survivor := R.class0Survivor
  class0Big := R.class0Big
  class1Datum := R.class1Datum
  densePackDatum := R.densePackDatum.toDatumSplit R.lever

/-- The final statement from the lever residual, through the wave-4 datum capstone. -/
theorem toStatement (R : Erdos260DyadicLeverResidual) : Erdos260Statement :=
  R.toDatum.toStatement

end Erdos260DyadicLeverResidual

/-- **The wave-5 conditional endpoint.**  `Erdos260Statement` from the dyadic-value lever
plus the lever-shrunk per-atom surfaces, composed through the wave-4 datum capstone. -/
theorem erdos260_of_dyadicValueLever (R : Erdos260DyadicLeverResidual) : Erdos260Statement :=
  R.toStatement

/-! ## Part 8.  Machine-readable status (honest) -/

/-- Honest machine-readable status of the dyadic-value lever module. -/
def dyadicValueLeverStatus : List String :=
  [ "WHAT THE MODEL PROVES ABOUT Q AND THE VALUE (goal 1, all unconditional per ctx): " ++
      "0 < Q (shell field hQ); the carry numerator is P = K0 > 0 " ++
      "(shell_carry_choose_pos, shell_carry_choose_eq_K0); the weighted value is EXACTLY " ++
      "K0/Q (shell_value_eq_K0_div_Q, positive by shell_value_pos); THE MASTER PIN " ++
      "q = oddpart(Q)*(2K0+1) (datum_q_eq_oddpartQ_mul - every wave-4 per-family oddpart " ++
      "pin is a corollary); and the scale bound 2^27*Q < X (shell_Q_scale_bound). " ++
      "Consolidated in shell_Q_constraints.",
    "WHAT THE MODEL DOES NOT PROVE (goal 4, the irreducible finding): NO parity pin on Q, " ++
      "NO lower bound beyond 0 < Q, NO gcd(P,Q) = 1. The rationality witness denominator " ++
      "is arbitrary (value = P/Q is closed under (P,Q) -> (2P,2Q)), and the canonical " ++
      "S25.1 residual center runFOfShell is deliberately built from Q/(2Q+1) - NOT from " ++
      "P/Q - so its non-dyadicity (ResidualCenter.hnondyadic, q0 > 1, runFOfShell_q0_gt_one) " ++
      "holds REGARDLESS of whether P/Q is dyadic. Nothing excludes Q = 2^t or Q = 1.",
    "THE FAMILIES ARE NOT REFUTABLE FROM THE VALUE DATA (proved): dyadicWitnessDigits " ++
      "(d_n = 1 for n >= 3) is binary, non-terminating, with weighted value EXACTLY 1 " ++
      "(dyadicWitnessDigits_value, via sum_{n>=3} n/2^n = 2 - 1/2 - 1/2 = 1); " ++
      "dyadicValue_family_data_consistent realizes the value data of all three dyadic " ++
      "families (Q in {1,3,7}, P = Q, t = 0). Any voiding proof MUST use the largeness/" ++
      "failure fields (hlarge, hfailure, hXdyadic) - they are not used by any value lemma.",
    "VALUE RIGIDITY OF THE FIVE SURVIVING FIXED PAIRS (goal 2): band 2 (3,1): Q = 2^t, " ++
      "value = 1/2^t (wave-4 return_datum_value_eq); band 3 (21,3): Q = 3*2^t, value = " ++
      "1/2^t (wave-4 densePack_datum_value_eq); band 4 (15,1): Q = 5*2^t, value = " ++
      "1/(5*2^t) (NEW towerFP15_1_value_eq); band 4 (15,2): Q = 3*2^t, value = 2/(3*2^t) " ++
      "(NEW towerFP15_2_value_eq); band 4 (105,7): Q = 7*2^t, value = 7/(7*2^t) = 1/2^t " ++
      "EXACTLY DYADIC (NEW towerFP105_7_value_eq) - THREE of the five families are " ++
      "dyadic-value, not two. Consolidated: fixedFamilyHit_value_pinned (oddpart(Q) in " ++
      "{1,3,5,7}, value = K0/(oddpart(Q)*2^t)); exact characterization " ++
      "shellValueDyadic_iff (value = 1/2^t iff Q = K0*2^t); hypothetical-odd-Q confinement " ++
      "fixedFamilyHit_Q_mem_of_oddQ (odd Q on a hit forces Q in {1,3,5,7}).",
    "THE SINGLE VOIDING FACTS (goal 4, recorded exactly): DyadicValueLever (no ctx has " ++
      "value = 1/2^t) voids (3,1) + (21,3) + (105,7) wholesale " ++
      "(returnFixedFamily_void, densePackFixedFamily_void, towerFP105Family_void; hit " ++
      "forms returnClass4FixedHit_void, class3FixedHit_void); TowerFifthValueLever " ++
      "(value != 1/(5*2^t)) voids (15,1) (towerFP15_1Family_void); TowerThirdsValueLever " ++
      "(value != 2/(3*2^t)) voids (15,2) (towerFP15_2Family_void); Q-side alternatives: " ++
      "oddpart(Q) > 1 voids band 2 (returnFixedFamily_void_of_oddpartQ), oddpart(Q) " ++
      "notin {1,3,5,7} voids all five (fixedFamilyHit_void_of_oddpartQ). NONE of these " ++
      "levers is proved; all downstream consequences are stated conditionally.",
    "UPGRADED BOUNDS UNDER THE LEVER (goal 3, additive): b2 < c on EVERY period of EVERY " ++
      "ctx (datum_band2CycleCount_lt_of_lever; fibre form olcFibre_card_le_of_lever); " ++
      "b3 < c likewise (cycleBand3Residues_card_lt_of_lever; density form " ++
      "densePackStarts_card_le_of_lever_density); band-4 fixed hits confined to q = 15, " ++
      "K0 <= 2 (towerFixedPoint_datum_confined_of_lever) so b4 < c needs only q != 15 " ++
      "(towerBand4CycleCount_lt_of_lever - the q != 105 guard discharged).",
    "CAPSTONE WIRING (goal 3, additive): TowerEscapeLever drops the (105, K0 = 7) branch " ++
      "of TowerEscape (towerEscapeLever_of_towerEscape under the lever; weakening witness " ++
      "towerLeverResidual_of_fixedPointResidual); DensePackLeverSplitResidual relieves all " ++
      "four DensePack fields of (21,3) (bridge DensePackLeverSplitResidual.toDatumSplit); " ++
      "Erdos260DyadicLeverResidual carries the lever as an explicit field, shrinks the " ++
      "tower escape, and relieves the four Return fields of (3,1) - where the wave-4 " ++
      "honest obstructions (vacuous gate 4 at b2 = c, unfireable interior top-band check) " ++
      "lived; endpoint erdos260_of_dyadicValueLever : Erdos260DyadicLeverResidual -> " ++
      "Erdos260Statement through Erdos260DatumResidual.toStatement. Nothing re-proved.",
    "HONEST RESIDUAL: the lever itself. It is consistent with the value-side data " ++
      "(dyadicValue_family_data_consistent), so proving it requires tying the digit-side " ++
      "failure structure (support sparsity below c0*X at the dyadic scale X) to the exact " ++
      "dyadic value 1/2^t - e.g. a carry-word rigidity argument on integerCarry Q P d N " ++
      "= 2^N*2^t*(1/2^t - S_N) with Q = 2^t, P = 1. No such bridge is formalized; we do " ++
      "NOT claim any context empty, and the (15,1)/(15,2) pairs are untouched by the " ++
      "dyadic lever (their values 1/(5*2^t), 2/(3*2^t) are non-dyadic)." ]

theorem dyadicValueLeverStatus_nonempty : dyadicValueLeverStatus ≠ [] := by
  simp [dyadicValueLeverStatus]

/-! ## Part 9.  Axiom-cleanliness audit -/

#print axioms shell_carry_choose_pos
#print axioms shell_carry_choose_eq_K₀
#print axioms shell_value_eq_K₀_div_Q
#print axioms shell_value_pos
#print axioms datum_q_eq_oddpartQ_mul
#print axioms shell_Q_eq_oddpart_mul_pow
#print axioms shell_Q_scale_bound
#print axioms shell_Q_constraints
#print axioms datum_value_eq_of_oddpartQ
#print axioms towerFP15_1_value_eq
#print axioms towerFP15_2_value_eq
#print axioms towerFP105_7_value_eq
#print axioms fixedFamilyHit_oddpartQ_mem
#print axioms fixedFamilyHit_value_pinned
#print axioms fixedFamilyHit_Q_mem_of_oddQ
#print axioms shellValueDyadic_iff
#print axioms shellValueDyadic_of_return_datum
#print axioms shellValueDyadic_of_densePack_datum
#print axioms shellValueDyadic_of_towerFP105
#print axioms dyadicWitnessDigits_binary
#print axioms dyadicWitnessDigits_not_eventuallyZero
#print axioms dyadicWitnessDigits_hasSum
#print axioms dyadicWitnessDigits_value
#print axioms dyadicValue_family_data_consistent
#print axioms returnFixedFamily_void
#print axioms densePackFixedFamily_void
#print axioms towerFP105Family_void
#print axioms towerFP15_1Family_void
#print axioms towerFP15_2Family_void
#print axioms fixedFamilyHit_void_of_oddpartQ
#print axioms returnFixedFamily_void_of_oddpartQ
#print axioms returnClass4FixedHit_void
#print axioms class3FixedHit_void
#print axioms datum_band2CycleCount_lt_of_lever
#print axioms olcFibre_card_le_of_lever
#print axioms cycleBand3Residues_card_lt_of_lever
#print axioms densePackStarts_card_le_of_lever_density
#print axioms towerFixedPoint_datum_confined_of_lever
#print axioms towerBand4CycleCount_lt_of_lever
#print axioms towerEscape_of_towerEscapeLever
#print axioms towerEscapeLever_of_towerEscape
#print axioms towerLeverResidual_of_fixedPointResidual
#print axioms towerFixedPointResidual_of_lever
#print axioms DensePackLeverSplitResidual.toDatumSplit
#print axioms DensePackDatumSplitResidual.toLeverSplit
#print axioms Erdos260DyadicLeverResidual.toDatum
#print axioms Erdos260DyadicLeverResidual.toStatement
#print axioms erdos260_of_dyadicValueLever
#print axioms dyadicValueLeverStatus_nonempty

end

end Erdos260
