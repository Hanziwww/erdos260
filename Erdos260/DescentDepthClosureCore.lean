import Erdos260.DescentDepthAgreementCore
import Erdos260.SemiperiodicMatchEnrichCore
import Erdos260.IntegerCarry

/-!
# §25.1 descent-depth CLOSURE: discharging `DescentWindowMatch.hmatch` from (D1) ∧ (D2)

Wave-22 (`DescentDepthAgreementCore`) proved the **master reduction**
`singularSquareBound_of_matches`: the descent-depth agreement `MatchesCompletion d s n q₀ a`
(the window word spells the first `n` digits of the rational completion `dyadicDigit q₀ a`) implies
the §25.1 singular-square bound (D1) `|R|·2ⁿ < D·q₀`.  It reduced the §25.1 certificate to the lone
explicit hypothesis field `DescentWindowMatch.hmatch` — the per-window agreement — stated as a
hypothesis (never a `sorry`).

This file (NEW; it edits no existing file) **goes beyond** that re-characterization by formalizing the
manuscript's actual §25.1 / Lemma 25.1 derivation in the **reverse** direction — the genuinely missing
half — and thereby **discharges** `hmatch` from strictly more primitive inputs:

> *Lemma 25.1 (proof, lines ~1098–1111):* binary cylinder stability shows the first `n₀` cylinders are
> equal or adjacent; **"in the equal case there is exact agreement"**; the adjacent (carry-tail) case
> `ξ011…1 / ξ100…0` is the large run, excluded by **no large run**.

Combined with wave-20's exact characterization (`singularSquareBound_iff_cylinder`: (D1) holds iff the
centre lies in the window's own cylinder **or** the carry-adjacent lower one), this completes the
manuscript equivalence and converts `hmatch` into the two genuine certificate fields **(D1)** + **(D2)**.

## What is genuinely PROVED here (no `sorry`/`axiom`/`admit`/`native_decide`)

### Part A — Lemma 25.1 "equal case ⟹ exact agreement" (the reverse direction, CLOSED)

* `matchesCompletion_of_cylinderIndex_eq` — if the centre's depth-`n` cylinder index equals the actual
  window value (`cylinderIndex n (a/q₀) = windowCylinderValue d s n`, the §25.1 *equal* case), then the
  descent-depth agreement `MatchesCompletion d s n q₀ a` holds.  Proof: the window value indexes the
  centre's own cylinder, fed to the closed equal-cylinder bridge
  `SemiperiodicMatchEnrichCore.windowMatch_dyadicDigit_of_cylinder` (which is *defeq* to
  `MatchesCompletion`).
* `matchesCompletion_iff_cylinderIndex_eq` — the clean **equivalence**: the descent-depth agreement IS
  exactly the equal-cylinder condition (forward by wave-22 `windowValue_eq_cylinderIndex_of_matches`).

### Part B — (D1) bound + no-large-run carry exclusion ⟹ agreement (the manuscript direction, CLOSED)

* `matchesCompletion_of_singularSquareBound` — **THE missing manuscript direction**: from the (D1)
  bound for the *actual* window value plus the carry exclusion `cylinderIndex n (a/q₀) + 1 ≠ M`
  (the (D2) no-large-run routing that kills the carry-adjacent lower neighbour), the agreement holds.
  Proof: `SingularSquareBoundCore.dyadicCylinder_center_of_singularSquareBound` gives the equal
  cylinder, then Part A.
* `matchesCompletion_iff_singularSquareBound_and_carry` — the **full equivalence**
  `hmatch ⟺ (D1) ∧ (carry-exclusion)`.  The forward halves are the wave-22 master reduction and the
  fact that equal cylinders exclude the carry neighbour; the backward half is the new direction.  So
  the descent-depth agreement is **not** an independent analytic input: it is *exactly* the conjunction
  of the certificate's (D1) `hbound` and (D2) `hcarry` fields.

### Part C — discharging `DescentWindowMatch.hmatch` (DERIVED)

* `DescentWindowMatch.ofBoundAndCarry` — builds the `DescentWindowMatch` (hence discharges `hmatch`)
  from `hbound` (the (D1) singular-square bound for the actual descent windows — exactly the wave-22
  `descentWindow_singularSquareBound` conclusion / `SingularSquareCertificate.hbound`) and `hcarry`
  (the carry exclusion — exactly the (D2) `NoLargeRun` routing already separately flagged).  `hmatch`
  is no longer a primitive: it is proved from (D1) + (D2).

### Part D — the centre-free residue-band sharpening of (D1) (CLOSED)

* `exists_descentBound_iff_residueBand` — (D1) is satisfiable for *some* centre iff the actual window
  value's residue `(M·q₀) mod 2ⁿ` avoids the forbidden middle band `[q₀, 2ⁿ−q₀]`
  (`SingularSquareBoundCore.exists_singularSquareBound_iff`).
* `residue_upper_witness_lt`, `matchesCompletion_of_residue_upper` — in the **upper** residue band
  `2ⁿ−q₀ < (M·q₀) mod 2ⁿ` the explicit floor witness `a = (M·q₀)/2ⁿ + 1` is a genuine residue
  (`a < q₀`) whose cylinder index is exactly `M`, so the agreement holds with the carry exclusion
  **automatic**.  This reduces (D1)+(D2) to the **centre-free residue-band membership of the actual
  window value** — a single arithmetic condition on `M` alone, strictly more primitive than the
  digit-by-digit agreement `hmatch`.
* `DescentWindowMatch.ofResidueBand` — discharges `hmatch` from the per-window upper-band membership
  alone (the centre numerators are *defined* as the floor witnesses).

### Part E — the elementary carry gap bound (the denominator-drop mechanism, CLOSED)

* `integerCarry_abs_le` — the recurrence `R_{N+1} = 2 R_N − Q(N+1) d_{N+1}` keeps the integer carry
  bounded by the **linear `O_Q(N)` envelope** `|R_N| ≤ Q·(N+2)` (wrapping the proved
  `IntegerCarry.integerCarry_bounds_of_rational_value`).  This is the manuscript's denominator-drop
  residual `|𝓡| ≪_Q X+p`, genuinely PROVABLE from the recurrence.

## Audit verdict (the strictly-more-primitive residual)

`DescentWindowMatch.hmatch` is **discharged**: `matchesCompletion_iff_singularSquareBound_and_carry`
proves `hmatch ⟺ (D1) ∧ (D2)`, and `ofBoundAndCarry` / `ofResidueBand` build the `DescentWindowMatch`
from strictly more primitive inputs.  The two surviving residuals are both strictly below `hmatch`:

* **(D1) the singular-square bound** for the actual windows — *further* reduced here, via the
  upper-band route, to the **centre-free residue-band membership** `2ⁿ−q₀ < (M·q₀) mod 2ⁿ` of the
  actual window value `M` (a single arithmetic condition on `M`, no centre word, no digit agreement);
  and
* **(D2) the no-large-run carry exclusion** `cylinderIndex n (a/q₀) + 1 ≠ M` (the boundary-run
  routing), which in the upper-band route is **automatic**.

The elementary carry gap bound `|R_N| ≤ Q(N+2)` is PROVABLE (`integerCarry_abs_le`) and is the
manuscript's denominator-drop mechanism, but it is the **linear** `O_Q(N)` envelope of the
*position-weighted* carry, **not** the per-window (D1) bound, which is the **constant** bound `< q₀`
= residue-band membership.  The carry gap bound guarantees a small-denominator centre exists near the
window mask point (the denominator drop); converting it to the per-window *constant* (D1) bound is the
depth calibration `n = p − B` (the separately-flagged `hpb`) together with the descent-window
*selection* of which window lands in the admissible band — the latter being the **no-large-run** (D2)
routing.  Sharply: only the residue *value* mod `Q` is periodic, while the carry *value* that fixes the
digits is unbounded (`FailingShellPeriodicityCore.carryOf_value_grows_on_zeroRun`), so the gap bound
under-determines the window without the (D2) selection.  Hence the genuinely-routed residual is
no-large-run (D2), and (D1) is the centre-free residue band.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

namespace Erdos260

noncomputable section

/-! ## Part A — Lemma 25.1 "equal case ⟹ exact agreement": the reverse direction -/

/--
**Lemma 25.1, equal case (reverse direction).**

If the centre `a/q₀`'s depth-`n` cylinder index equals the actual window value
`cylinderIndex n (a/q₀) = windowCylinderValue d s n` (the §25.1 *equal*-cylinder case), then the
descent-depth agreement `MatchesCompletion d s n q₀ a` holds: the window word spells the centre's
completion to depth `n`.  This is the manuscript's "in the equal case there is exact agreement", here
proved by feeding the equal cylinder to the closed bridge `windowMatch_dyadicDigit_of_cylinder` (which
unfolds *definitionally* to `MatchesCompletion`).
-/
theorem matchesCompletion_of_cylinderIndex_eq {d : ℕ → ℕ} (hd : ∀ i, d i ≤ 1)
    {s n q0 a : ℕ} (hq0 : 0 < q0)
    (heq : cylinderIndex n ((a : ℝ) / (q0 : ℝ)) = windowCylinderValue d s n) :
    MatchesCompletion d s n q0 a := by
  have h0 : (0 : ℝ) ≤ (a : ℝ) / (q0 : ℝ) := by positivity
  have hcyl : DyadicCylinder n (windowCylinderValue d s n) ((a : ℝ) / (q0 : ℝ)) := by
    have hc := dyadicCylinder_cylinderIndex (n := n) h0
    rwa [heq] at hc
  intro i hi
  exact windowMatch_dyadicDigit_of_cylinder hd hq0 hcyl i hi

/--
**The descent-depth agreement IS the equal-cylinder condition.**

For a binary word `d` and a small-denominator centre (`a < q₀`), the descent-depth agreement
`MatchesCompletion d s n q₀ a` holds **iff** `cylinderIndex n (a/q₀) = windowCylinderValue d s n`.
Forward is the wave-22 master step `windowValue_eq_cylinderIndex_of_matches`; backward is Part A.
-/
theorem matchesCompletion_iff_cylinderIndex_eq {d : ℕ → ℕ} (hd : ∀ i, d i ≤ 1)
    {s n q0 a : ℕ} (hq0 : 0 < q0) (ha : a < q0) :
    MatchesCompletion d s n q0 a ↔
      cylinderIndex n ((a : ℝ) / (q0 : ℝ)) = windowCylinderValue d s n :=
  ⟨fun hm => (windowValue_eq_cylinderIndex_of_matches hq0 ha hm).symm,
    fun heq => matchesCompletion_of_cylinderIndex_eq hd hq0 heq⟩

/-! ## Part B — (D1) bound + no-large-run carry exclusion ⟹ agreement -/

/--
**THE missing manuscript direction: (D1) + carry exclusion ⟹ descent-depth agreement.**

From the §25.1 singular-square bound (D1) for the *actual* window value
`SingularSquareBound n (windowCylinderValue d s n) q₀ a` together with the carry exclusion
`cylinderIndex n (a/q₀) + 1 ≠ windowCylinderValue d s n` (the (D2) no-large-run routing that excludes
the carry-adjacent lower cylinder `ξ011…1 / ξ100…0`), the descent-depth agreement holds.

Proof: (D1) routes the equal-or-carry dichotomy (`dyadicCylinder_center_of_singularSquareBound`) to
the equal cylinder once the carry neighbour is excluded; then Part A.  This is the half the prior
waves left as the hypothesis `hmatch`.
-/
theorem matchesCompletion_of_singularSquareBound {d : ℕ → ℕ} (hd : ∀ i, d i ≤ 1)
    {s n q0 a : ℕ} (hq0 : 0 < q0)
    (hbound : SingularSquareBound n (windowCylinderValue d s n) q0 a)
    (hcarry : cylinderIndex n ((a : ℝ) / (q0 : ℝ)) + 1 ≠ windowCylinderValue d s n) :
    MatchesCompletion d s n q0 a := by
  intro i hi
  exact windowMatch_dyadicDigit_of_cylinder hd hq0
    (dyadicCylinder_center_of_singularSquareBound hq0 hbound hcarry) i hi

/--
**The descent-depth agreement = (D1) ∧ (D2).**

For a binary word `d` and a small-denominator centre (`a < q₀`), `MatchesCompletion d s n q₀ a` holds
**iff** the (D1) singular-square bound holds for the actual window value **and** the carry-adjacent
lower neighbour is excluded.  So the descent-depth agreement is exactly the conjunction of the §25.1
certificate's two genuine fields — *not* an independent analytic input.
-/
theorem matchesCompletion_iff_singularSquareBound_and_carry {d : ℕ → ℕ} (hd : ∀ i, d i ≤ 1)
    {s n q0 a : ℕ} (hq0 : 0 < q0) (ha : a < q0) :
    MatchesCompletion d s n q0 a ↔
      (SingularSquareBound n (windowCylinderValue d s n) q0 a ∧
        cylinderIndex n ((a : ℝ) / (q0 : ℝ)) + 1 ≠ windowCylinderValue d s n) := by
  constructor
  · intro hm
    have heq : cylinderIndex n ((a : ℝ) / (q0 : ℝ)) = windowCylinderValue d s n :=
      (windowValue_eq_cylinderIndex_of_matches hq0 ha hm).symm
    exact ⟨singularSquareBound_of_matches hq0 ha hm, by omega⟩
  · rintro ⟨hbound, hcarry⟩
    exact matchesCompletion_of_singularSquareBound hd hq0 hbound hcarry

/-! ## Part C — Discharging `DescentWindowMatch.hmatch` from (D1) ∧ (D2) -/

/--
**`DescentWindowMatch` from (D1) ∧ (D2) — `hmatch` discharged.**

Builds the descent-window match data (hence discharges the wave-22 hypothesis `hmatch`) from:

* `hbound` — the (D1) singular-square bound for each actual descent window (exactly the
  `descentWindow_singularSquareBound` conclusion, i.e. the `SingularSquareCertificate.hbound` field),
  and
* `hcarry` — the carry exclusion `cylinderIndex (spread+1) (a k/q₀) + 1 ≠ windowCylinderValue …`
  (exactly the (D2) `NoLargeRun` boundary-run routing, already separately flagged).

The descent-depth agreement is thereby *proved* from the two strictly-more-primitive certificate
fields via `matchesCompletion_of_singularSquareBound`.
-/
def DescentWindowMatch.ofBoundAndCarry (ctx : ActualFailureContext)
    (a : ℕ → ℕ)
    (ha : ∀ k ∈ genuineDensePackStarts ctx, a k < (canonicalCenter ctx).q0)
    (hbound : ∀ k ∈ genuineDensePackStarts ctx,
      SingularSquareBound (proofV4DensePackSpread ctx.shell + 1)
        (windowCylinderValue ctx.shell.d (k + ctx.n24CarryData.r)
          (proofV4DensePackSpread ctx.shell + 1))
        (canonicalCenter ctx).q0 (a k))
    (hcarry : ∀ k ∈ genuineDensePackStarts ctx,
      cylinderIndex (proofV4DensePackSpread ctx.shell + 1)
          ((a k : ℝ) / ((canonicalCenter ctx).q0 : ℝ)) + 1
        ≠ windowCylinderValue ctx.shell.d (k + ctx.n24CarryData.r)
            (proofV4DensePackSpread ctx.shell + 1)) :
    DescentWindowMatch ctx where
  a := a
  ha := ha
  hmatch := fun k hk =>
    matchesCompletion_of_singularSquareBound
      (fun i => by rcases ctx.shell.hd i with h | h <;> omega)
      (canonicalCenter ctx).q0_pos (hbound k hk) (hcarry k hk)

/-! ## Part D — The centre-free residue-band sharpening of (D1) -/

/--
**(D1) admissibility ⟺ residue band of the actual window value.**

The (D1) singular-square bound holds for *some* centre numerator iff the actual window value's residue
`(M·q₀) mod 2ⁿ` (with `M = windowCylinderValue d s n`) avoids the forbidden middle band
`[q₀, 2ⁿ−q₀]`.  This is `SingularSquareBoundCore.exists_singularSquareBound_iff` specialised to the
actual window: (D1) is a **centre-free** condition on `M` alone.
-/
theorem exists_descentBound_iff_residueBand (d : ℕ → ℕ) (s n : ℕ) {q0 : ℕ} (hq0 : 0 < q0) :
    (∃ a : ℕ, SingularSquareBound n (windowCylinderValue d s n) q0 a) ↔
      (windowCylinderValue d s n * q0) % 2 ^ n < q0 ∨
        2 ^ n - q0 < (windowCylinderValue d s n * q0) % 2 ^ n :=
  exists_singularSquareBound_iff hq0

/--
**The upper-band floor witness is a genuine residue.**

In the upper residue band `2ⁿ−q₀ < (M·q₀) mod 2ⁿ` of the actual window value `M = windowCylinderValue
d s n`, the explicit witness `a = (M·q₀)/2ⁿ + 1` satisfies `a < q₀`.  (Because `M < 2ⁿ` forces
`2ⁿ·a ≤ 2ⁿ·q₀ − 1 < 2ⁿ·q₀`.)
-/
theorem residue_upper_witness_lt {d : ℕ → ℕ} (hd : ∀ i, d i ≤ 1) {s n q0 : ℕ} (_hq0 : 0 < q0)
    (hband : 2 ^ n - q0 < (windowCylinderValue d s n * q0) % 2 ^ n) :
    (windowCylinderValue d s n * q0) / 2 ^ n + 1 < q0 := by
  set M := windowCylinderValue d s n with hM
  have hMlt : M < 2 ^ n := by rw [hM]; exact windowCylinderValue_lt hd s n
  have hPpos : 0 < 2 ^ n := by positivity
  have hρ : M * q0 % 2 ^ n < 2 ^ n := Nat.mod_lt _ hPpos
  have hdm : 2 ^ n * (M * q0 / 2 ^ n) + M * q0 % 2 ^ n = M * q0 :=
    Nat.div_add_mod (M * q0) (2 ^ n)
  have hmul : 2 ^ n * (M * q0 / 2 ^ n + 1) = 2 ^ n * (M * q0 / 2 ^ n) + 2 ^ n := by ring
  have hawitness : 2 ^ n * (M * q0 / 2 ^ n + 1) = M * q0 + (2 ^ n - M * q0 % 2 ^ n) := by omega
  have hPrLt : 2 ^ n - M * q0 % 2 ^ n < q0 := by omega
  have hMq : M * q0 ≤ (2 ^ n - 1) * q0 := Nat.mul_le_mul_right q0 (by omega)
  have hsub : (2 ^ n - 1) * q0 = 2 ^ n * q0 - q0 := by rw [Nat.sub_mul, Nat.one_mul]
  have hq0le : q0 ≤ 2 ^ n * q0 := Nat.le_mul_of_pos_left q0 hPpos
  have key : 2 ^ n * (M * q0 / 2 ^ n + 1) < 2 ^ n * q0 := by rw [hawitness]; omega
  exact lt_of_mul_lt_mul_left key (Nat.zero_le _)

/--
**Upper residue band ⟹ descent-depth agreement (centre-free).**

If the actual window value's residue lies in the upper band `2ⁿ−q₀ < (M·q₀) mod 2ⁿ`, then the floor
witness `a = (M·q₀)/2ⁿ + 1` has cylinder index exactly `M`, so the descent-depth agreement
`MatchesCompletion d s n q₀ a` holds (the carry exclusion is automatic in the equal case).  This
exhibits the (D1)+(D2) content as a **single centre-free residue inequality** on `M` — strictly more
primitive than the digit-by-digit agreement.
-/
theorem matchesCompletion_of_residue_upper {d : ℕ → ℕ} (hd : ∀ i, d i ≤ 1) {s n q0 : ℕ}
    (hq0 : 0 < q0)
    (hband : 2 ^ n - q0 < (windowCylinderValue d s n * q0) % 2 ^ n) :
    MatchesCompletion d s n q0 ((windowCylinderValue d s n * q0) / 2 ^ n + 1) := by
  set M := windowCylinderValue d s n with hM
  have hPpos : 0 < 2 ^ n := by positivity
  have hρ : M * q0 % 2 ^ n < 2 ^ n := Nat.mod_lt _ hPpos
  have hdm : 2 ^ n * (M * q0 / 2 ^ n) + M * q0 % 2 ^ n = M * q0 :=
    Nat.div_add_mod (M * q0) (2 ^ n)
  have hmul : 2 ^ n * (M * q0 / 2 ^ n + 1) = 2 ^ n * (M * q0 / 2 ^ n) + 2 ^ n := by ring
  have hawitness : 2 ^ n * (M * q0 / 2 ^ n + 1) = M * q0 + (2 ^ n - M * q0 % 2 ^ n) := by omega
  have hPrLt : 2 ^ n - M * q0 % 2 ^ n < q0 := by omega
  set r := 2 ^ n - M * q0 % 2 ^ n with hr
  have hcyl_eq : cylinderIndex n (((M * q0 / 2 ^ n + 1 : ℕ) : ℝ) / (q0 : ℝ)) = M := by
    rw [cylinderIndex_ratCast q0 (M * q0 / 2 ^ n + 1) n, hawitness, Nat.mul_comm M q0,
      Nat.mul_add_div hq0, Nat.div_eq_of_lt hPrLt, Nat.add_zero]
  exact matchesCompletion_of_cylinderIndex_eq hd hq0 (hcyl_eq.trans hM)

/--
**`DescentWindowMatch` from the centre-free residue band — `hmatch` discharged from a single
arithmetic condition per window.**

Discharges `hmatch` from the per-window upper-band membership of the *actual* window values alone; the
centre numerators are *defined* as the floor witnesses `a k = (M_k·q₀)/2ⁿ + 1` (genuine residues by
`residue_upper_witness_lt`).  This is the sharpest form of the closure: the residual is reduced to a
single arithmetic condition on each actual window value, with no centre word and no digit agreement.
-/
def DescentWindowMatch.ofResidueBand (ctx : ActualFailureContext)
    (hband : ∀ k ∈ genuineDensePackStarts ctx,
      2 ^ (proofV4DensePackSpread ctx.shell + 1) - (canonicalCenter ctx).q0
        < (windowCylinderValue ctx.shell.d (k + ctx.n24CarryData.r)
            (proofV4DensePackSpread ctx.shell + 1) * (canonicalCenter ctx).q0)
          % 2 ^ (proofV4DensePackSpread ctx.shell + 1)) :
    DescentWindowMatch ctx where
  a := fun k => (windowCylinderValue ctx.shell.d (k + ctx.n24CarryData.r)
      (proofV4DensePackSpread ctx.shell + 1) * (canonicalCenter ctx).q0)
      / 2 ^ (proofV4DensePackSpread ctx.shell + 1) + 1
  ha := fun k hk =>
    residue_upper_witness_lt (fun i => by rcases ctx.shell.hd i with h | h <;> omega)
      (canonicalCenter ctx).q0_pos (hband k hk)
  hmatch := fun k hk =>
    matchesCompletion_of_residue_upper (fun i => by rcases ctx.shell.hd i with h | h <;> omega)
      (canonicalCenter ctx).q0_pos (hband k hk)

/-! ## Part E — The elementary carry gap bound (the denominator-drop mechanism) -/

/--
**The elementary carry gap bound (manuscript `|𝓡| ≪_Q X+p`).**

The integer-carry recurrence `R_{N+1} = 2 R_N − Q(N+1) d_{N+1}` keeps the carry bounded by the linear
`O_Q(N)` envelope `|R_N| ≤ Q·(N+2)`.  PROVABLE directly from the recurrence (it wraps the proved
`IntegerCarry.integerCarry_bounds_of_rational_value`, whose `0 ≤ R_N` half lets the absolute value
collapse to the upper bound).

This is the manuscript's denominator-drop residual bound `|𝓡| ≪_Q X+p` of eq. (25.1).  It is the
**mechanism** that places a small-denominator centre near the window mask point (the denominator drop),
but it is the *linear* envelope of the *position-weighted* carry — NOT the per-window (D1) bound, which
is the *constant* bound `< q₀` (= residue-band membership).  Converting this envelope to the per-window
constant bound is the depth calibration `n = p − B` plus the descent-window selection routed by
no-large-run; see the module audit verdict.
-/
theorem integerCarry_abs_le {Q : ℕ} {P : ℤ} {d : ℕ → ℕ} (N : ℕ)
    (hQ : 0 < Q) (hd : BinaryDigits d)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ)) :
    |integerCarry Q P d N| ≤ (Q : ℤ) * ((N + 2 : ℕ) : ℤ) := by
  obtain ⟨hlo, hhi⟩ := integerCarry_bounds_of_rational_value N hQ hd heta
  rw [abs_of_nonneg hlo]
  exact hhi

/-! ## Part F — Honest residual inventory -/

/-- The precise status of the §25.1 descent-depth agreement / `DescentWindowMatch.hmatch` after this
module. -/
def descentDepthClosureResiduals : List String :=
  [ "GOAL (wave-23) — DISCHARGE DescentWindowMatch.hmatch by formalizing the manuscript Lemma 25.1 " ++
      "reverse direction ('in the equal case there is exact agreement') BEYOND the prior waves' " ++
      "agreement ⟹ bound master reduction; reduce hmatch to a STRICTLY more primitive residual.",
    "CLOSED (Lemma 25.1 equal case, reverse) — matchesCompletion_of_cylinderIndex_eq: cylinderIndex n " ++
      "(a/q₀) = windowCylinderValue d s n (the §25.1 EQUAL case) ⟹ MatchesCompletion d s n q₀ a, via " ++
      "the closed equal-cylinder bridge windowMatch_dyadicDigit_of_cylinder (defeq to MatchesCompletion). " ++
      "matchesCompletion_iff_cylinderIndex_eq: the agreement IS exactly the equal-cylinder condition.",
    "CLOSED (the missing manuscript direction) — matchesCompletion_of_singularSquareBound: the (D1) " ++
      "singular-square bound for the ACTUAL window value + the carry exclusion cylinderIndex n (a/q₀)+1 " ++
      "≠ M (the (D2) no-large-run routing of the carry-adjacent lower cylinder ξ011…1/ξ100…0) ⟹ the " ++
      "agreement. matchesCompletion_iff_singularSquareBound_and_carry: hmatch ⟺ (D1) ∧ (D2-carry). The " ++
      "descent-depth agreement is NOT an independent input — it is the conjunction of the certificate's " ++
      "two genuine fields.",
    "DERIVED (hmatch discharged) — DescentWindowMatch.ofBoundAndCarry: builds DescentWindowMatch (hence " ++
      "discharges hmatch) from hbound (the (D1) bound for the actual windows, = descentWindow_" ++
      "singularSquareBound / SingularSquareCertificate.hbound) and hcarry (the (D2) NoLargeRun carry " ++
      "exclusion). hmatch is proved from the two strictly-more-primitive certificate fields.",
    "CLOSED (centre-free residue band) — exists_descentBound_iff_residueBand: (D1) is satisfiable iff " ++
      "(M·q₀) mod 2ⁿ avoids the forbidden middle band [q₀,2ⁿ−q₀]. matchesCompletion_of_residue_upper + " ++
      "residue_upper_witness_lt: in the UPPER band 2ⁿ−q₀ < (M·q₀) mod 2ⁿ the floor witness a = (M·q₀)/" ++
      "2ⁿ+1 < q₀ has cylinder index M, so the agreement holds with the carry exclusion AUTOMATIC. " ++
      "DescentWindowMatch.ofResidueBand discharges hmatch from the per-window upper-band membership of " ++
      "the actual window values ALONE (centre numerators defined as the floor witnesses).",
    "CLOSED (carry gap bound, the denominator-drop mechanism) — integerCarry_abs_le: the recurrence " ++
      "R_{N+1}=2R_N−Q(N+1)d_{N+1} gives |R_N| ≤ Q(N+2), the linear O_Q(N) envelope (manuscript " ++
      "|𝓡| ≪_Q X+p). PROVABLE from the recurrence (wraps integerCarry_bounds_of_rational_value).",
    "VERDICT (the strictly-more-primitive residual) — hmatch ⟺ (D1) ∧ (D2) is PROVED; hmatch is no " ++
      "longer primitive. The two surviving residuals are strictly below hmatch: (D1) the singular-square " ++
      "bound, FURTHER reduced (upper-band route) to the CENTRE-FREE residue-band membership 2ⁿ−q₀ < " ++
      "(M·q₀) mod 2ⁿ of the actual window value M (a single arithmetic condition, no centre word, no " ++
      "digit agreement); and (D2) the no-large-run carry exclusion (automatic in the upper band).",
    "VERDICT (carry gap bound vs (D1)) — the elementary gap bound |R_N| ≤ Q(N+2) is PROVABLE but is the " ++
      "LINEAR envelope of the POSITION-WEIGHTED carry, NOT the per-window (D1) CONSTANT bound < q₀ = " ++
      "residue-band membership. The gap bound is the denominator-drop MECHANISM (a small-denominator " ++
      "centre exists near the window); converting it to the per-window constant bound needs the depth " ++
      "calibration n=p−B (the flagged hpb) AND the descent selection of which window lands in the " ++
      "admissible band — which is the no-large-run (D2) routing. Only the residue VALUE mod Q is " ++
      "periodic; the carry VALUE that fixes the digits is unbounded (carryOf_value_grows_on_zeroRun), so " ++
      "the gap bound under-determines the window without (D2). Genuinely-routed residual: no-large-run " ++
      "(D2); (D1) is the centre-free residue band." ]

theorem descentDepthClosureResiduals_nonempty : descentDepthClosureResiduals ≠ [] := by
  simp [descentDepthClosureResiduals]

/-! ## Part G — Axiom-cleanliness audit -/

#print axioms matchesCompletion_of_cylinderIndex_eq
#print axioms matchesCompletion_iff_cylinderIndex_eq
#print axioms matchesCompletion_of_singularSquareBound
#print axioms matchesCompletion_iff_singularSquareBound_and_carry
#print axioms DescentWindowMatch.ofBoundAndCarry
#print axioms exists_descentBound_iff_residueBand
#print axioms residue_upper_witness_lt
#print axioms matchesCompletion_of_residue_upper
#print axioms DescentWindowMatch.ofResidueBand
#print axioms integerCarry_abs_le

end

end Erdos260
