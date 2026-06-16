import Erdos260.DescentAllDepths

/-!
# Per-scale upper-band membership: the transition law of the sharpest descent atom

This module (NEW; it edits no existing file) attacks the wave-10 sharpest open atom
(`descentAllDepthsStatus`): per-scale upper-band membership
`2ⁿ − q₀ < (Mₙ·q₀) mod 2ⁿ` of the depth-`n` window value `Mₙ = windowCylinderValue d s n`
at cofinally many depths `n`, at one genuine start with the leftmost-window pinch
`k + r = X + 1` (`onsetBudget_forces_shell_edge`).

## The objects (goal 1, exact)

`Mₙ = ∑_{i<n} d(s+i)·2^{n-1-i}` (MSB-first window value).  Write
`ρₙ := (Mₙ·q₀) mod 2ⁿ` (the *band residue*) and `cₙ := 2ⁿ − ρₙ ∈ [1, 2ⁿ]` (the *band
complement*).  The upper band `2ⁿ − q₀ < ρₙ` says exactly `cₙ < q₀`, i.e.
`q₀·Mₙ + cₙ ≡ 0 (mod 2ⁿ)` with a deficit `0 < cₙ < q₀` — `q₀·Mₙ` sits just below a multiple
of `2ⁿ`: a 2-adic approximation statement about `Mₙ/2ⁿ` vs denominator-`q₀` fractions
(`two_pow_dvd_mul_add_complement`).

## THE TRANSITION LAW (goal 1, the heart — all PROVED)

* `windowCylinderValue_succ` — the dyadic refinement recursion `M_{n+1} = 2·Mₙ + d(s+n)`.
* `bandResidue_succ` — hence `ρ_{n+1} = (2·ρₙ + d(s+n)·q₀) mod 2^{n+1}`: the depth-`(n+1)`
  band residue is determined by the depth-`n` residue and the ONE new digit.
* `band_coupling` — under the band at depth `n+1` (and `q₀ ≤ 2ⁿ`, `d` binary) the exact
  integer Euclidean step holds: `2·cₙ = c_{n+1} + d(s+n)·q₀`.
* `digit_eq_binaryQuotient_of_band_succ` — therefore the new digit is FORCED:
  `d(s+n) = ⌊2cₙ/q₀⌋ = binaryQuotient q₀ cₙ`.
* `band_succ_of_digit` / `upperBandAt_succ_iff_digit` — and conversely (for odd `q₀`), given
  the band at `n`, the band at `n+1` holds IFF the digit takes that value.  In that case
  `c_{n+1} = (2cₙ) mod q₀ = binaryRemainder q₀ cₙ` (`bandComplement_succ_of_band_succ`):
  the complement runs the §25.2 binary-division orbit `2rⱼ = ε_{j+1}q₀ + r_{j+1}`.

## Rigidity and the characterization (goals 1–2, PROVED)

* `upperBandAt_of_succ` / `upperBandAt_of_le` — the band is DOWNWARD CLOSED above the
  threshold `q₀ ≤ 2ⁿ`: band at a deeper scale implies band at every intermediate scale.
  Contrapositive `upperBandAt_persists_not`: ONE wrong digit kills the band at ALL deeper
  scales — no second chances; hence cofinal band = band on a full tail
  (`upperBandAt_forall_of_cofinal`).
* `bandComplement_orbit_residue` / `upperBand_digit_orbit` — under the band on `[n₀,∞)` the
  complement orbit is exactly the §25.2 residue orbit of `c_{n₀}`:
  `c_{n₀+j} = dyadicResidue q₀ c_{n₀} j` and `d(s+n₀+j) = dyadicDigit q₀ c_{n₀} j`.
* `upperBandAt_tail_iff_digits` — **THE EQUIVALENCE CHARACTERIZATION**: given the band at a
  base depth `n₀` with `q₀ ≤ 2^{n₀}` (odd `q₀`), the band holds at ALL depths `≥ n₀` IFF the
  window word beyond position `n₀` IS the binary expansion of `c_{n₀}/q₀`.  Band membership
  at all depths encodes a SPECIFIC digit sequence — the expansion of the band-complement
  fraction.
* `bandComplement_eq_dyadicResidue_witness` — the complement at a banded depth IS the §25.2
  residue `r_n = (2ⁿa) mod q₀` of the in-tree floor-witness centre `a = (Mₙq₀)/2ⁿ + 1`.

## The verdict on forcing (goal 2, PROVED equivalence — no shortcut)

* `upperBandAt_of_matchesCompletion` — conversely, a depth-`n` match at a centre with
  non-vanishing residue (`q₀ ∤ 2ⁿa`) puts the window IN the band at depth `n`.
* `upperBandAt_cofinal_iff_tailMatch` — **cofinal band ⟺ tail match**: at one start, band
  membership at cofinally many scales is EQUIVALENT to `∃ a < q₀, q₀ ∤ a ∧ TailMatch`.
  So the per-scale band data is not an intermediate waypoint: it IS the tail match,
  confirming `canonicalPerScaleSupply_iff_lever` at the single-window level.  The carry
  envelope `|R_N| ≤ Q(N+2)` (`integerCarry_abs_le`, the §25.1 mechanism) is the LINEAR
  envelope of the position-weighted carry and cannot by itself force the CONSTANT deficit
  `cₙ < q₀` at unboundedly many `n`.
* `upperBandAt_completion_model` — non-vacuity: the completion word `dyadicDigit q₀ a`
  (coprime `a`) is in the band at EVERY depth `n ≥ log₂ q₀`; no constant/all-zero shortcut.

## The honest repair (goal 3, NEW constructors — the in-tree ∀-n band is vacuous)

* `not_upperBandAt_zero` — the band is FALSE at depth `0` (for `q₀ ≥ 1`): `ρ₀ = 0`.
* `perScale_residueBand_all_depths_empty` — hence the hypothesis of the wave-10
  `PerScaleDescentWindowMatch.ofResidueBand` (band at ALL `n : ℕ`) is UNSATISFIABLE at any
  genuine start: that constructor is honest but vacuous.  The satisfiable forms are:
* `PerScaleDescentWindowMatch.ofUpperBandCofinal` — the repaired bridge: band at COFINALLY
  many scales per genuine start (the correct atom shape) builds the per-scale match, via the
  scale-generic floor-witness route plus downward restriction.
* `CofinalUpperBandSupply` — the named successor atom: cofinal upper-band membership at
  every genuine start plus the in-tree budgets (genuine start, onset `k+r ≤ X+1`, order
  `2·ord ≤ X`) at deep dyadic contexts.  `canonicalPerScaleSupply_of_cofinalUpperBand` /
  `erdos260_of_cofinalUpperBand` — composition into the wave-10 tower (additive only).
* `SeedUpperBandSupply` — the equivalent seed form: ONE banded base depth `n₀` (with
  `q₀ ≤ 2^{n₀}`) plus the tail expansion of the band complement; via
  `upperBandAt_cofinal_of_seed` it implies the cofinal supply
  (`cofinalUpperBandSupply_of_seed`).
* `cofinalUpperBandSupply_iff_lever` — no free lunch, transported: the successor atom is
  logically EQUIVALENT to `DyadicValueLever`.

## What §25.3 supplies at general depth (goal 2/4, honest)

The formalized §25.3/K.1 density layer (`RhoDQCalibrationCore` → `RhoDQFrontierDischargeCore`
→ `RhoDQFinalConsumerBridgeCore`) derives the density atoms FROM a `DescentWindowMatch` — it
CONSUMES the match; it does not produce band membership.  The manuscript Prop 25.3 produces,
per period scale `p`, ONE match of length `≥ p/2` via Lemma 25.1 case 3 from the carry
envelope (eq. 25.1, formalized as `integerCarry_abs_le`) at the SINGLE calibrated depth
`n₀ = p − B` (in-tree: depth `spread+1` via `hpb`) — never at unboundedly many depths of a
FIXED window.  By `upperBandAt_cofinal_iff_tailMatch` such a supply at one window would BE
the tail match, hence the lever: there is no cheaper intermediate, and nothing in the
manuscript's one-scale §25.3 closes it.

No `sorry`, `admit`, new `axiom`, or `native_decide`.
-/

namespace Erdos260

noncomputable section

/-! ## Part 0.  The per-scale band objects -/

/-- The depth-`n` **band residue** `ρₙ = (Mₙ·q₀) mod 2ⁿ` of the window starting at `s`. -/
def bandResidue (d : ℕ → ℕ) (s q0 n : ℕ) : ℕ :=
  windowCylinderValue d s n * q0 % 2 ^ n

/-- The depth-`n` **band complement** `cₙ = 2ⁿ − ρₙ ∈ [1, 2ⁿ]`: the deficit of `q₀·Mₙ` below
the next multiple of `2ⁿ`. -/
def bandComplement (d : ℕ → ℕ) (s q0 n : ℕ) : ℕ :=
  2 ^ n - bandResidue d s q0 n

/-- **The per-scale upper-band membership** — the exact `hband` shape of the wave-10
`PerScaleDescentWindowMatch.ofResidueBand` route, depth `n` free. -/
def UpperBandAt (d : ℕ → ℕ) (s q0 n : ℕ) : Prop :=
  2 ^ n - q0 < bandResidue d s q0 n

/-- Definitional unfolding (the literal in-tree `hband` inequality). -/
theorem upperBandAt_def (d : ℕ → ℕ) (s q0 n : ℕ) :
    UpperBandAt d s q0 n ↔
      2 ^ n - q0 < windowCylinderValue d s n * q0 % 2 ^ n :=
  Iff.rfl

/-- The band residue is a genuine depth-`n` residue. -/
theorem bandResidue_lt (d : ℕ → ℕ) (s q0 n : ℕ) : bandResidue d s q0 n < 2 ^ n :=
  Nat.mod_lt _ (by positivity)

/-- The band complement is positive: `q₀·Mₙ` is never itself a multiple of `2ⁿ` plus `0`
deficit — `cₙ ≥ 1` always. -/
theorem bandComplement_pos (d : ℕ → ℕ) (s q0 n : ℕ) : 0 < bandComplement d s q0 n := by
  have h := bandResidue_lt d s q0 n
  unfold bandComplement
  omega

/-- In the band the complement is a genuine deficit `cₙ < q₀` (no threshold needed). -/
theorem bandComplement_lt_of_upperBandAt {d : ℕ → ℕ} {s q0 n : ℕ}
    (hband : UpperBandAt d s q0 n) : bandComplement d s q0 n < q0 := by
  have h := bandResidue_lt d s q0 n
  have hb : 2 ^ n - q0 < bandResidue d s q0 n := hband
  unfold bandComplement
  omega

/-- Above the threshold `q₀ ≤ 2ⁿ`, band membership IS the complement bound `cₙ < q₀`. -/
theorem upperBandAt_iff_complement_lt {d : ℕ → ℕ} {s q0 n : ℕ} (hq : q0 ≤ 2 ^ n) :
    UpperBandAt d s q0 n ↔ bandComplement d s q0 n < q0 := by
  have h := bandResidue_lt d s q0 n
  unfold UpperBandAt bandComplement
  omega

/-- **The 2-adic reading**: `2ⁿ ∣ q₀·Mₙ + cₙ` always — the band condition `cₙ < q₀` says
`q₀·Mₙ` is within `q₀` below a multiple of `2ⁿ`, i.e. `Mₙ/2ⁿ` 2-adically approximates a
denominator-`q₀` fraction with deficit `cₙ`. -/
theorem two_pow_dvd_mul_add_complement (d : ℕ → ℕ) (s q0 n : ℕ) :
    2 ^ n ∣ windowCylinderValue d s n * q0 + bandComplement d s q0 n := by
  have h : windowCylinderValue d s n * q0 % 2 ^ n < 2 ^ n := Nat.mod_lt _ (by positivity)
  have hdm : 2 ^ n * (windowCylinderValue d s n * q0 / 2 ^ n)
      + windowCylinderValue d s n * q0 % 2 ^ n = windowCylinderValue d s n * q0 :=
    Nat.div_add_mod _ _
  have hmul : 2 ^ n * (windowCylinderValue d s n * q0 / 2 ^ n + 1)
      = 2 ^ n * (windowCylinderValue d s n * q0 / 2 ^ n) + 2 ^ n := by ring
  refine ⟨windowCylinderValue d s n * q0 / 2 ^ n + 1, ?_⟩
  unfold bandComplement bandResidue
  omega

/-! ## Part 1.  The dyadic refinement recursion -/

/-- **The window-value recursion** (one dyadic refinement step):
`M_{n+1} = 2·Mₙ + d(s+n)` — the depth-`(n+1)` value appends one digit. -/
theorem windowCylinderValue_succ (d : ℕ → ℕ) (s n : ℕ) :
    windowCylinderValue d s (n + 1) = 2 * windowCylinderValue d s n + d (s + n) := by
  unfold windowCylinderValue
  rw [Finset.sum_range_succ, Finset.mul_sum]
  have hlast : n + 1 - 1 - n = 0 := by omega
  rw [hlast, pow_zero, mul_one]
  have hsum : (∑ i ∈ Finset.range n, d (s + i) * 2 ^ (n + 1 - 1 - i))
      = ∑ i ∈ Finset.range n, 2 * (d (s + i) * 2 ^ (n - 1 - i)) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    have hexp : n + 1 - 1 - i = n - 1 - i + 1 := by omega
    rw [hexp, pow_succ]
    ring
  rw [hsum]

/-- Doubling mod a doubled power of two only sees the previous residue. -/
theorem mod_two_pow_succ_step (x e n : ℕ) :
    (2 * x + e) % 2 ^ (n + 1) = (2 * (x % 2 ^ n) + e) % 2 ^ (n + 1) := by
  have hdm : 2 ^ n * (x / 2 ^ n) + x % 2 ^ n = x := Nat.div_add_mod x (2 ^ n)
  have h2 : 2 ^ (n + 1) * (x / 2 ^ n) = 2 * (2 ^ n * (x / 2 ^ n)) := by
    rw [pow_succ]; ring
  have hkey : 2 * x + e = 2 * (x % 2 ^ n) + e + 2 ^ (n + 1) * (x / 2 ^ n) := by omega
  rw [hkey, Nat.add_mul_mod_self_left]

/-- **THE RESIDUE TRANSITION LAW** (the heart): the depth-`(n+1)` band residue is determined
by the depth-`n` residue and the one new digit,
`ρ_{n+1} = (2·ρₙ + d(s+n)·q₀) mod 2^{n+1}`. -/
theorem bandResidue_succ (d : ℕ → ℕ) (s q0 n : ℕ) :
    bandResidue d s q0 (n + 1)
      = (2 * bandResidue d s q0 n + d (s + n) * q0) % 2 ^ (n + 1) := by
  unfold bandResidue
  rw [windowCylinderValue_succ]
  have hexp : (2 * windowCylinderValue d s n + d (s + n)) * q0
      = 2 * (windowCylinderValue d s n * q0) + d (s + n) * q0 := by ring
  rw [hexp, mod_two_pow_succ_step]

/-! ## Part 2.  The coupling identity, digit forcing, and the complement orbit -/

/-- A number below `2m` is its own residue mod `m`, or exceeds `m` by its residue. -/
theorem mod_eq_or_of_lt_two_mul {x m : ℕ} (hx : x < m + m) :
    x % m = x ∨ (m ≤ x ∧ x % m + m = x) := by
  rcases Nat.lt_or_ge x m with h | h
  · exact Or.inl (Nat.mod_eq_of_lt h)
  · refine Or.inr ⟨h, ?_⟩
    have hsub : x % m = (x - m) % m := Nat.mod_eq_sub_mod h
    have hlt : x - m < m := by omega
    rw [hsub, Nat.mod_eq_of_lt hlt]
    omega

/-- **THE COUPLING IDENTITY**: if the band holds at depth `n+1` (with `q₀ ≤ 2ⁿ`, `d` binary)
then the complements couple through the exact integer Euclidean step
`2·cₙ = c_{n+1} + d(s+n)·q₀`. -/
theorem band_coupling {d : ℕ → ℕ} (hd : ∀ i, d i ≤ 1) {s q0 n : ℕ}
    (hq : q0 ≤ 2 ^ n) (hband : UpperBandAt d s q0 (n + 1)) :
    2 * bandComplement d s q0 n = bandComplement d s q0 (n + 1) + d (s + n) * q0 := by
  have hP : 0 < 2 ^ n := by positivity
  have hP1 : 0 < 2 ^ (n + 1) := by positivity
  have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
  have hρ : bandResidue d s q0 n < 2 ^ n := Nat.mod_lt _ hP
  have hρ1 : bandResidue d s q0 (n + 1) < 2 ^ (n + 1) := Nat.mod_lt _ hP1
  have hE : d (s + n) * q0 ≤ q0 := by
    have h1 := hd (s + n)
    calc d (s + n) * q0 ≤ 1 * q0 := Nat.mul_le_mul_right q0 h1
      _ = q0 := one_mul q0
  have hb : 2 ^ (n + 1) - q0 < bandResidue d s q0 (n + 1) := hband
  have hstep := bandResidue_succ d s q0 n
  have hx : 2 * bandResidue d s q0 n + d (s + n) * q0 < 2 ^ (n + 1) + 2 ^ (n + 1) := by
    omega
  rcases mod_eq_or_of_lt_two_mul hx with hcase | ⟨hge, hcase⟩ <;>
    rw [← hstep] at hcase <;> unfold bandComplement <;> omega

/-- **Downward rigidity (one step)**: band at depth `n+1` forces band at depth `n`
(above the threshold `q₀ ≤ 2ⁿ`). -/
theorem upperBandAt_of_succ {d : ℕ → ℕ} (hd : ∀ i, d i ≤ 1) {s q0 n : ℕ}
    (hq : q0 ≤ 2 ^ n) (hband : UpperBandAt d s q0 (n + 1)) :
    UpperBandAt d s q0 n := by
  have hcoup := band_coupling hd hq hband
  have hc1 : bandComplement d s q0 (n + 1) < q0 := bandComplement_lt_of_upperBandAt hband
  have hE : d (s + n) * q0 ≤ q0 := by
    have h1 := hd (s + n)
    calc d (s + n) * q0 ≤ 1 * q0 := Nat.mul_le_mul_right q0 h1
      _ = q0 := one_mul q0
  rw [upperBandAt_iff_complement_lt hq]
  omega

/-- **Downward rigidity (iterated)**: band at any deeper scale restricts to every scale
above the threshold. -/
theorem upperBandAt_of_le {d : ℕ → ℕ} (hd : ∀ i, d i ≤ 1) {s q0 m n : ℕ}
    (hq : q0 ≤ 2 ^ m) (hmn : m ≤ n) (hband : UpperBandAt d s q0 n) :
    UpperBandAt d s q0 m := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = m + j := ⟨n - m, by omega⟩
  clear hmn
  induction j with
  | zero => exact hband
  | succ j ih =>
    have hqj : q0 ≤ 2 ^ (m + j) :=
      le_trans hq (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right m j))
    exact ih (upperBandAt_of_succ hd hqj hband)

/-- **No second chances**: once the band fails at a depth above the threshold, it fails at
EVERY deeper depth — one wrong digit kills the descent forever. -/
theorem upperBandAt_persists_not {d : ℕ → ℕ} (hd : ∀ i, d i ≤ 1) {s q0 n m : ℕ}
    (hq : q0 ≤ 2 ^ n) (hnot : ¬ UpperBandAt d s q0 n) (hm : n ≤ m) :
    ¬ UpperBandAt d s q0 m :=
  fun hband => hnot (upperBandAt_of_le hd hq hm hband)

/-- **Cofinal collapses to a full tail**: band at cofinally many scales gives band at EVERY
scale `≥ n₀` (any threshold depth `q₀ ≤ 2^{n₀}`). -/
theorem upperBandAt_forall_of_cofinal {d : ℕ → ℕ} (hd : ∀ i, d i ≤ 1) {s q0 n0 : ℕ}
    (hq : q0 ≤ 2 ^ n0)
    (hcof : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ UpperBandAt d s q0 n) :
    ∀ m : ℕ, n0 ≤ m → UpperBandAt d s q0 m := by
  intro m hm
  obtain ⟨n, hn, hband⟩ := hcof m
  exact upperBandAt_of_le hd
    (le_trans hq (Nat.pow_le_pow_right (by norm_num) hm)) hn hband

/-- **THE DIGIT IS FORCED**: under the band at depth `n+1`, the new digit equals the
binary-division quotient of the depth-`n` complement, `d(s+n) = ⌊2cₙ/q₀⌋`. -/
theorem digit_eq_binaryQuotient_of_band_succ {d : ℕ → ℕ} (hd : ∀ i, d i ≤ 1) {s q0 n : ℕ}
    (hq : q0 ≤ 2 ^ n) (hband : UpperBandAt d s q0 (n + 1)) :
    d (s + n) = binaryQuotient q0 (bandComplement d s q0 n) := by
  have hcoup := band_coupling hd hq hband
  have hc1lt : bandComplement d s q0 (n + 1) < q0 := bandComplement_lt_of_upperBandAt hband
  have hc1pos : 0 < bandComplement d s q0 (n + 1) := bandComplement_pos d s q0 (n + 1)
  have he := hd (s + n)
  unfold binaryQuotient
  rw [hcoup]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp he with he0 | he1
  · rw [he0]
    simp only [Nat.zero_mul, Nat.add_zero]
    exact (Nat.div_eq_of_lt hc1lt).symm
  · rw [he1, one_mul, Nat.add_div_right _ (by omega : 0 < q0), Nat.div_eq_of_lt hc1lt]

/-- **The band-preserving digit choice succeeds** (converse, odd `q₀`): from the band at
depth `n` with the digit `d(s+n) = ⌊2cₙ/q₀⌋`, the band holds at depth `n+1`. -/
theorem band_succ_of_digit {d : ℕ → ℕ} {s q0 n : ℕ}
    (hodd : Odd q0) (hq : q0 ≤ 2 ^ n)
    (hband : UpperBandAt d s q0 n)
    (hdig : d (s + n) = binaryQuotient q0 (bandComplement d s q0 n)) :
    UpperBandAt d s q0 (n + 1) := by
  have hP : 0 < 2 ^ n := by positivity
  have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
  have hρ : bandResidue d s q0 n < 2 ^ n := Nat.mod_lt _ hP
  have hclt : bandComplement d s q0 n < q0 := bandComplement_lt_of_upperBandAt hband
  have hne : 2 * bandComplement d s q0 n ≠ q0 := by
    intro hcontra
    obtain ⟨t, ht⟩ := hodd
    omega
  have hstep := bandResidue_succ d s q0 n
  have hcdef : bandComplement d s q0 n = 2 ^ n - bandResidue d s q0 n := rfl
  show 2 ^ (n + 1) - q0 < bandResidue d s q0 (n + 1)
  rcases Nat.lt_or_ge (2 * bandComplement d s q0 n) q0 with hlt | hge
  · -- quotient 0: the residue doubles and stays in the band
    have he0 : d (s + n) = 0 := by
      rw [hdig]
      unfold binaryQuotient
      exact Nat.div_eq_of_lt hlt
    rw [he0] at hstep
    have hxlt : 2 * bandResidue d s q0 n + 0 * q0 < 2 ^ (n + 1) := by omega
    rw [Nat.mod_eq_of_lt hxlt] at hstep
    omega
  · -- quotient 1: the residue doubles plus `q₀` and stays in the band
    have hgt : q0 < 2 * bandComplement d s q0 n := by omega
    have he1 : d (s + n) = 1 := by
      rw [hdig]
      show 2 * bandComplement d s q0 n / q0 = 1
      exact Nat.div_eq_of_lt_le (by omega) (by omega)
    rw [he1] at hstep
    have hxlt : 2 * bandResidue d s q0 n + 1 * q0 < 2 ^ (n + 1) := by omega
    rw [Nat.mod_eq_of_lt hxlt] at hstep
    omega

/-- **THE TRANSITION LAW (iff form)**: given the band at depth `n` (odd `q₀`, threshold
`q₀ ≤ 2ⁿ`, `d` binary), the band at depth `n+1` holds IFF the new digit takes the
band-preserving value `⌊2cₙ/q₀⌋`. -/
theorem upperBandAt_succ_iff_digit {d : ℕ → ℕ} (hd : ∀ i, d i ≤ 1) {s q0 n : ℕ}
    (hodd : Odd q0) (hq : q0 ≤ 2 ^ n) (hband : UpperBandAt d s q0 n) :
    UpperBandAt d s q0 (n + 1)
      ↔ d (s + n) = binaryQuotient q0 (bandComplement d s q0 n) :=
  ⟨fun h => digit_eq_binaryQuotient_of_band_succ hd hq h,
    fun h => band_succ_of_digit hodd hq hband h⟩

/-- Under the band at depth `n+1`, the complement performs the §25.2 binary-division step:
`c_{n+1} = (2cₙ) mod q₀`. -/
theorem bandComplement_succ_of_band_succ {d : ℕ → ℕ} (hd : ∀ i, d i ≤ 1) {s q0 n : ℕ}
    (hq : q0 ≤ 2 ^ n) (hband : UpperBandAt d s q0 (n + 1)) :
    bandComplement d s q0 (n + 1) = binaryRemainder q0 (bandComplement d s q0 n) := by
  have hcoup := band_coupling hd hq hband
  have hc1lt : bandComplement d s q0 (n + 1) < q0 := bandComplement_lt_of_upperBandAt hband
  unfold binaryRemainder
  rw [hcoup, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc1lt]

/-! ## Part 3.  The orbit characterization: the band encodes one specific digit word -/

/-- For odd `q₀`, the §25.2 residue orbit of a non-multiple never vanishes
(`q₀ ∤ a ⟹ 1 ≤ rₙ` — strictly weaker than coprimality). -/
theorem dyadicResidue_pos_of_not_dvd {q0 a : ℕ} (hodd : Odd q0)
    (hndvd : ¬ q0 ∣ a) (n : ℕ) : 1 ≤ dyadicResidue q0 a n := by
  by_contra h
  have h0 : (2 ^ n * a) % q0 = 0 := by
    have h0' : dyadicResidue q0 a n = 0 := by omega
    exact h0'
  have hdvd : q0 ∣ 2 ^ n * a := Nat.dvd_of_mod_eq_zero h0
  have hcop : Nat.Coprime q0 (2 ^ n) :=
    Nat.Coprime.pow_right n (Nat.coprime_two_left.mpr hodd).symm
  exact hndvd (hcop.dvd_of_dvd_mul_left hdvd)

/-- **The complement orbit IS the §25.2 residue orbit**: under the band on `[n₀,∞)`,
`c_{n₀+j} = dyadicResidue q₀ c_{n₀} j = (2ʲ·c_{n₀}) mod q₀`. -/
theorem bandComplement_orbit_residue {d : ℕ → ℕ} (hd : ∀ i, d i ≤ 1) {s q0 n0 : ℕ}
    (hq : q0 ≤ 2 ^ n0)
    (hband : ∀ m : ℕ, n0 ≤ m → UpperBandAt d s q0 m) :
    ∀ j : ℕ, bandComplement d s q0 (n0 + j)
      = dyadicResidue q0 (bandComplement d s q0 n0) j := by
  have hclt : bandComplement d s q0 n0 < q0 :=
    bandComplement_lt_of_upperBandAt (hband n0 le_rfl)
  intro j
  induction j with
  | zero =>
    show bandComplement d s q0 (n0 + 0) = (2 ^ 0 * bandComplement d s q0 n0) % q0
    rw [Nat.add_zero, pow_zero, one_mul, Nat.mod_eq_of_lt hclt]
  | succ j ih =>
    have hqj : q0 ≤ 2 ^ (n0 + j) :=
      le_trans hq (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right n0 j))
    have hbsucc : UpperBandAt d s q0 (n0 + j + 1) := hband (n0 + j + 1) (by omega)
    have hstep : bandComplement d s q0 (n0 + j + 1)
        = binaryRemainder q0 (bandComplement d s q0 (n0 + j)) :=
      bandComplement_succ_of_band_succ hd hqj hbsucc
    rw [← Nat.add_assoc, hstep, ih, ← dyadicResidue_step]

/-- **The window digits ARE the expansion of the band-complement fraction**: under the band
on `[n₀,∞)`, `d(s+n₀+j) = dyadicDigit q₀ c_{n₀} j` for every `j`. -/
theorem upperBand_digit_orbit {d : ℕ → ℕ} (hd : ∀ i, d i ≤ 1) {s q0 n0 : ℕ}
    (hq : q0 ≤ 2 ^ n0)
    (hband : ∀ m : ℕ, n0 ≤ m → UpperBandAt d s q0 m) (j : ℕ) :
    d (s + (n0 + j)) = dyadicDigit q0 (bandComplement d s q0 n0) j := by
  have hqj : q0 ≤ 2 ^ (n0 + j) :=
    le_trans hq (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right n0 j))
  have hbsucc : UpperBandAt d s q0 (n0 + j + 1) := hband (n0 + j + 1) (by omega)
  have hdig := digit_eq_binaryQuotient_of_band_succ hd hqj hbsucc
  rw [hdig, bandComplement_orbit_residue hd hq hband j]
  rfl

/-- **THE EQUIVALENCE CHARACTERIZATION** (the formal heart of the atom): given the band at a
base depth `n₀` (odd `q₀`, threshold `q₀ ≤ 2^{n₀}`), band membership at ALL depths `≥ n₀` is
EQUIVALENT to the window word beyond `n₀` being the binary expansion of `c_{n₀}/q₀`.  The
per-scale band encodes exactly one digit sequence — a `q₀`-denominator rational expansion. -/
theorem upperBandAt_tail_iff_digits {d : ℕ → ℕ} (hd : ∀ i, d i ≤ 1) {s q0 n0 : ℕ}
    (hodd : Odd q0) (hq : q0 ≤ 2 ^ n0)
    (hband0 : UpperBandAt d s q0 n0) :
    (∀ m : ℕ, n0 ≤ m → UpperBandAt d s q0 m)
      ↔ ∀ j : ℕ, d (s + (n0 + j)) = dyadicDigit q0 (bandComplement d s q0 n0) j := by
  constructor
  · intro hband j
    exact upperBand_digit_orbit hd hq hband j
  · intro hdig
    have key : ∀ j : ℕ, UpperBandAt d s q0 (n0 + j) ∧
        bandComplement d s q0 (n0 + j)
          = dyadicResidue q0 (bandComplement d s q0 n0) j := by
      intro j
      induction j with
      | zero =>
        refine ⟨hband0, ?_⟩
        show bandComplement d s q0 (n0 + 0) = (2 ^ 0 * bandComplement d s q0 n0) % q0
        rw [Nat.add_zero, pow_zero, one_mul,
          Nat.mod_eq_of_lt (bandComplement_lt_of_upperBandAt hband0)]
      | succ j ih =>
        have hqj : q0 ≤ 2 ^ (n0 + j) :=
          le_trans hq (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right n0 j))
        have hdig' : d (s + (n0 + j))
            = binaryQuotient q0 (bandComplement d s q0 (n0 + j)) := by
          rw [hdig j, ih.2]
          rfl
        have hbsucc : UpperBandAt d s q0 (n0 + j + 1) :=
          band_succ_of_digit hodd hqj ih.1 hdig'
        refine ⟨hbsucc, ?_⟩
        rw [← Nat.add_assoc, bandComplement_succ_of_band_succ hd hqj hbsucc, ih.2,
          ← dyadicResidue_step]
    intro m hm
    have hkey := (key (m - n0)).1
    have heq : n0 + (m - n0) = m := by omega
    rwa [heq] at hkey

/-- The seed form fires cofinally: ONE banded base depth plus the tail expansion of its
complement give band membership at unboundedly many (indeed all deeper) scales. -/
theorem upperBandAt_cofinal_of_seed {d : ℕ → ℕ} (hd : ∀ i, d i ≤ 1) {s q0 n0 : ℕ}
    (hodd : Odd q0) (hq : q0 ≤ 2 ^ n0)
    (hband0 : UpperBandAt d s q0 n0)
    (hdig : ∀ j : ℕ, d (s + (n0 + j)) = dyadicDigit q0 (bandComplement d s q0 n0) j) :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ UpperBandAt d s q0 n := by
  intro N
  have hall := (upperBandAt_tail_iff_digits hd hodd hq hband0).mpr hdig
  exact ⟨max N n0, le_max_left N n0, hall (max N n0) (le_max_right N n0)⟩

/-! ## Part 4.  The witness identification and the tail-match equivalence (no shortcut) -/

/-- The banded complement IS the §25.2 residue of the in-tree floor-witness centre:
`cₙ = (2ⁿ·a) mod q₀` for `a = (Mₙ·q₀)/2ⁿ + 1` — the manuscript's `r_n` of the matched
centre `a/q₀`. -/
theorem bandComplement_eq_dyadicResidue_witness {d : ℕ → ℕ} {s q0 n : ℕ}
    (hband : UpperBandAt d s q0 n) :
    bandComplement d s q0 n
      = dyadicResidue q0 (windowCylinderValue d s n * q0 / 2 ^ n + 1) n := by
  have hρ : windowCylinderValue d s n * q0 % 2 ^ n < 2 ^ n := Nat.mod_lt _ (by positivity)
  have hclt : bandComplement d s q0 n < q0 := bandComplement_lt_of_upperBandAt hband
  have hdm : 2 ^ n * (windowCylinderValue d s n * q0 / 2 ^ n)
      + windowCylinderValue d s n * q0 % 2 ^ n = windowCylinderValue d s n * q0 :=
    Nat.div_add_mod _ _
  have hwit : 2 ^ n * (windowCylinderValue d s n * q0 / 2 ^ n + 1)
      = windowCylinderValue d s n * q0 + bandComplement d s q0 n := by
    have hmul : 2 ^ n * (windowCylinderValue d s n * q0 / 2 ^ n + 1)
        = 2 ^ n * (windowCylinderValue d s n * q0 / 2 ^ n) + 2 ^ n := by ring
    unfold bandComplement bandResidue
    omega
  show bandComplement d s q0 n
      = 2 ^ n * (windowCylinderValue d s n * q0 / 2 ^ n + 1) % q0
  rw [hwit, Nat.add_comm (windowCylinderValue d s n * q0) (bandComplement d s q0 n),
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hclt]

/-- The band supplies a depth-`n` match (the in-tree scale-generic floor-witness route,
existence form). -/
theorem upperBandAt_exists_matchesCompletion {d : ℕ → ℕ} (hd : ∀ i, d i ≤ 1) {s q0 n : ℕ}
    (hq0 : 0 < q0) (hband : UpperBandAt d s q0 n) :
    ∃ a : ℕ, a < q0 ∧ MatchesCompletion d s n q0 a :=
  ⟨windowCylinderValue d s n * q0 / 2 ^ n + 1,
    residue_upper_witness_lt hd hq0 hband,
    matchesCompletion_of_residue_upper hd hq0 hband⟩

/-- **The converse**: a depth-`n` match at a centre whose §25.2 residue does not vanish at
depth `n` (`1 ≤ rₙ`, e.g. `q₀ ∤ a` for odd `q₀`) puts the window IN the upper band at depth
`n` — the band is not just sufficient for the match, it is forced by it. -/
theorem upperBandAt_of_matchesCompletion {d : ℕ → ℕ} {s n q0 a : ℕ}
    (hq0 : 0 < q0) (ha : a < q0) (hq : q0 ≤ 2 ^ n)
    (hr : 1 ≤ dyadicResidue q0 a n)
    (hm : MatchesCompletion d s n q0 a) :
    UpperBandAt d s q0 n := by
  have hM : windowCylinderValue d s n = 2 ^ n * a / q0 := by
    rw [windowValue_eq_cylinderIndex_of_matches hq0 ha hm, cylinderIndex_ratCast]
  have hres : dyadicResidue q0 a n < q0 := dyadicResidue_lt hq0 a n
  have hMq : windowCylinderValue d s n * q0 + dyadicResidue q0 a n = 2 ^ n * a := by
    rw [hM]
    show 2 ^ n * a / q0 * q0 + 2 ^ n * a % q0 = 2 ^ n * a
    rw [Nat.mul_comm (2 ^ n * a / q0) q0]
    exact Nat.div_add_mod (2 ^ n * a) q0
  have hmod0 : (windowCylinderValue d s n * q0 + dyadicResidue q0 a n) % 2 ^ n = 0 := by
    rw [hMq]
    exact Nat.mul_mod_right _ _
  have hmod : (windowCylinderValue d s n * q0 % 2 ^ n + dyadicResidue q0 a n) % 2 ^ n
      = 0 := by
    rw [Nat.mod_add_mod]
    exact hmod0
  have hρlt : windowCylinderValue d s n * q0 % 2 ^ n < 2 ^ n := Nat.mod_lt _ (by positivity)
  have hsum : windowCylinderValue d s n * q0 % 2 ^ n + dyadicResidue q0 a n = 2 ^ n := by
    set S := windowCylinderValue d s n * q0 % 2 ^ n + dyadicResidue q0 a n with hS
    rcases Nat.lt_or_ge S (2 ^ n) with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at hmod
      omega
    · have h1 : S % 2 ^ n = (S - 2 ^ n) % 2 ^ n := Nat.mod_eq_sub_mod hge
      have h2 : (S - 2 ^ n) % 2 ^ n = S - 2 ^ n := Nat.mod_eq_of_lt (by omega)
      rw [h1, h2] at hmod
      omega
  show 2 ^ n - q0 < bandResidue d s q0 n
  have hatom : bandResidue d s q0 n = windowCylinderValue d s n * q0 % 2 ^ n := rfl
  omega

/-- A tail match at a non-degenerate centre (`q₀ ∤ a`, odd `q₀`) puts the window in the
band at EVERY depth above the threshold. -/
theorem upperBandAt_forall_of_tailMatch {d : ℕ → ℕ} {x q0 a : ℕ}
    (hq0 : 0 < q0) (hodd : Odd q0) (ha : a < q0) (hndvd : ¬ q0 ∣ a)
    (htm : TailMatch d x q0 a) :
    ∀ n : ℕ, q0 ≤ 2 ^ n → UpperBandAt d (x + 1) q0 n := by
  intro n hq
  exact upperBandAt_of_matchesCompletion hq0 ha hq
    (dyadicResidue_pos_of_not_dvd hodd hndvd n) (fun i _ => htm i)

/-- **THE NO-SHORTCUT VERDICT (single-window form)**: at one start, upper-band membership at
cofinally many scales is EQUIVALENT to a tail match at a non-degenerate small centre.  The
per-scale band data IS the tail match — there is no cheaper intermediate, exactly as
`canonicalPerScaleSupply_iff_lever` predicts at the supply level. -/
theorem upperBandAt_cofinal_iff_tailMatch {d : ℕ → ℕ} (hd : ∀ i, d i ≤ 1) {x q0 : ℕ}
    (hq0 : 1 < q0) (hodd : Odd q0) :
    (∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ UpperBandAt d (x + 1) q0 n)
      ↔ ∃ a : ℕ, a < q0 ∧ ¬ q0 ∣ a ∧ TailMatch d x q0 a := by
  constructor
  · intro hcof
    have hex : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ a : ℕ, a < q0 ∧
        MatchesCompletion d (x + 1) n q0 a := by
      intro N
      obtain ⟨n, hn, hb⟩ := hcof N
      exact ⟨n, hn,
        upperBandAt_exists_matchesCompletion hd (by omega) hb⟩
    obtain ⟨a, ha, htm⟩ := tailMatch_of_cofinal_fixedDenominator (by omega) hex
    refine ⟨a, ha, ?_, htm⟩
    intro hdvd
    have ha0 : a = 0 := Nat.eq_zero_of_dvd_of_lt hdvd ha
    have hdig0 : ∀ i : ℕ, d (x + 1 + i) = 0 := by
      intro i
      rw [htm i, ha0]
      simp [dyadicDigit, dyadicResidue, binaryQuotient]
    have hM0 : ∀ n : ℕ, windowCylinderValue d (x + 1) n = 0 := by
      intro n
      unfold windowCylinderValue
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [hdig0 i, Nat.zero_mul]
    obtain ⟨n, hn, hb⟩ := hcof q0
    have hb' : 2 ^ n - q0 < windowCylinderValue d (x + 1) n * q0 % 2 ^ n := hb
    rw [hM0 n, Nat.zero_mul, Nat.zero_mod] at hb'
    omega
  · rintro ⟨a, ha, hndvd, htm⟩ N
    have hq : q0 ≤ 2 ^ max N q0 :=
      le_trans (Nat.le_of_lt Nat.lt_two_pow_self)
        (Nat.pow_le_pow_right (by norm_num) (le_max_right N q0))
    exact ⟨max N q0, le_max_left N q0,
      upperBandAt_forall_of_tailMatch (by omega) hodd ha hndvd htm (max N q0) hq⟩

/-- **Non-vacuity**: the completion word `dyadicDigit q₀ a` of a non-degenerate centre is in
the band at EVERY depth above the threshold — the band predicate is genuinely satisfiable at
all deep scales; no constant/all-zero shortcut intervenes. -/
theorem upperBandAt_completion_model {q0 a : ℕ} (hq0 : 1 < q0) (hodd : Odd q0)
    (ha : a < q0) (hndvd : ¬ q0 ∣ a) {n : ℕ} (hq : q0 ≤ 2 ^ n) :
    UpperBandAt (dyadicDigit q0 a) 0 q0 n :=
  upperBandAt_of_matchesCompletion (by omega) ha hq
    (dyadicResidue_pos_of_not_dvd hodd hndvd n)
    (matchesCompletion_self q0 a n)

/-! ## Part 5.  The honest repair: the in-tree ∀-depth band hypothesis is vacuous at `n = 0` -/

/-- The band is FALSE at depth `0` (any `q₀`): `ρ₀ = 0` while `2⁰ − q₀ ≥ 0` in `ℕ`. -/
theorem not_upperBandAt_zero {d : ℕ → ℕ} {s q0 : ℕ} :
    ¬ UpperBandAt d s q0 0 := by
  intro h
  have hb : 2 ^ 0 - q0 < bandResidue d s q0 0 := h
  have h0 : bandResidue d s q0 0 = 0 := by
    show windowCylinderValue d s 0 * q0 % 2 ^ 0 = 0
    rw [pow_zero, Nat.mod_one]
  have hpow : (2 : ℕ) ^ 0 = 1 := pow_zero 2
  omega

/-- **The wave-10 `ofResidueBand` hypothesis is UNSATISFIABLE at any genuine start**: its
`hband` quantifies over ALL `n : ℕ` including `n = 0`, where the band is false.  The honest
satisfiable shapes are the cofinal/seed forms below. -/
theorem perScale_residueBand_all_depths_empty (ctx : ActualFailureContext)
    (hband : ∀ n : ℕ, ∀ k ∈ genuineDensePackStarts ctx,
      2 ^ n - (canonicalCenter ctx).q0
        < (windowCylinderValue ctx.shell.d (k + ctx.n24CarryData.r) n
            * (canonicalCenter ctx).q0) % 2 ^ n) :
    ∀ k, k ∉ genuineDensePackStarts ctx := by
  intro k hk
  exact not_upperBandAt_zero (hband 0 k hk)

/-- **The repaired per-scale bridge** (additive; the in-tree constructors are untouched):
upper-band membership at COFINALLY many scales per genuine start — the satisfiable form of
the atom — builds the wave-10 `PerScaleDescentWindowMatch`, by the scale-generic
floor-witness route at a banded scale plus downward restriction (`matchesCompletion_mono`). -/
def PerScaleDescentWindowMatch.ofUpperBandCofinal (ctx : ActualFailureContext)
    (hband : ∀ k ∈ genuineDensePackStarts ctx, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      UpperBandAt ctx.shell.d (k + ctx.n24CarryData.r) (canonicalCenter ctx).q0 n) :
    PerScaleDescentWindowMatch ctx :=
  PerScaleDescentWindowMatch.ofExists ctx (fun n k hk => by
    obtain ⟨m, hm, hb⟩ := hband k hk n
    obtain ⟨a, ha, hmatch⟩ := upperBandAt_exists_matchesCompletion
      (fun i => by rcases ctx.shell.hd i with h | h <;> omega)
      (canonicalCenter ctx).q0_pos hb
    exact ⟨a, ha, matchesCompletion_mono hm hmatch⟩)

/-! ## Part 6.  The named successor atom and its bridges into the conditional tower -/

/-- **THE SUCCESSOR ATOM (cofinal form)** — the satisfiable sharpening of the wave-10
per-scale supply: at every deep dyadic context, upper-band membership at cofinally many
scales at EVERY genuine start, plus one genuine start carrying the onset budget
`k + r ≤ X + 1` (which `onsetBudget_forces_shell_edge` pins to the leftmost window
`k + r = X + 1` under the §25.3 placement `X < k + r`) and the order budget `2·ord ≤ X`. -/
def CofinalUpperBandSupply : Prop :=
  ∀ ctx : ActualFailureContext, 2 ^ 493443 < ctx.X → ShellValueDyadic ctx →
    (∀ k ∈ genuineDensePackStarts ctx, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
        UpperBandAt ctx.shell.d (k + ctx.n24CarryData.r) (canonicalCenter ctx).q0 n) ∧
    ∃ k ∈ genuineDensePackStarts ctx,
      0 < k + ctx.n24CarryData.r ∧ k + ctx.n24CarryData.r ≤ ctx.X + 1 ∧
      2 * orderOf (2 : ZMod (canonicalCenter ctx).q0) ≤ ctx.X

/-- **The seed form of the successor atom** — by the equivalence characterization, ONE banded
base depth plus the tail expansion of its complement per genuine start: the sharpest
finitely-anchored shape. -/
def SeedUpperBandSupply : Prop :=
  ∀ ctx : ActualFailureContext, 2 ^ 493443 < ctx.X → ShellValueDyadic ctx →
    (∀ k ∈ genuineDensePackStarts ctx, ∃ n0 : ℕ,
        (canonicalCenter ctx).q0 ≤ 2 ^ n0 ∧
        UpperBandAt ctx.shell.d (k + ctx.n24CarryData.r) (canonicalCenter ctx).q0 n0 ∧
        ∀ j : ℕ, ctx.shell.d (k + ctx.n24CarryData.r + (n0 + j))
          = dyadicDigit (canonicalCenter ctx).q0
              (bandComplement ctx.shell.d (k + ctx.n24CarryData.r)
                (canonicalCenter ctx).q0 n0) j) ∧
    ∃ k ∈ genuineDensePackStarts ctx,
      0 < k + ctx.n24CarryData.r ∧ k + ctx.n24CarryData.r ≤ ctx.X + 1 ∧
      2 * orderOf (2 : ZMod (canonicalCenter ctx).q0) ≤ ctx.X

/-- The seed form implies the cofinal form (per-start, via the characterization). -/
theorem cofinalUpperBandSupply_of_seed (h : SeedUpperBandSupply) :
    CofinalUpperBandSupply := by
  intro ctx hX hdy
  obtain ⟨hseed, hk⟩ := h ctx hX hdy
  refine ⟨?_, hk⟩
  intro k hkmem N
  obtain ⟨n0, hq, hband0, hdig⟩ := hseed k hkmem
  exact upperBandAt_cofinal_of_seed
    (fun i => by rcases ctx.shell.hd i with h | h <;> omega)
    (runFOfShell_q0_odd ctx) hq hband0 hdig N

/-- **The bridge into the wave-10 tower**: the cofinal successor atom supplies the canonical
per-scale layer (composition only; nothing existing is edited). -/
theorem canonicalPerScaleSupply_of_cofinalUpperBand (h : CofinalUpperBandSupply) :
    CanonicalPerScaleSupply := by
  intro ctx hX hdy
  obtain ⟨hband, k, hk, hpos, hbudget, hord⟩ := h ctx hX hdy
  exact ⟨PerScaleDescentWindowMatch.ofUpperBandCofinal ctx hband,
    k, hk, hpos, hbudget, hord⟩

/-- **The endpoint** (composition through the wave-10 chain): `Erdos260Statement` from the
cofinal upper-band supply plus the lever-shrunk wave-5 surfaces. -/
theorem erdos260_of_cofinalUpperBand (h : CofinalUpperBandSupply)
    (surfaces : DyadicValueLever → Erdos260DyadicLeverResidual) : Erdos260Statement :=
  erdos260_of_canonicalPerScaleSupply
    (canonicalPerScaleSupply_of_cofinalUpperBand h) surfaces

/-- **No free lunch, transported to the successor atom**: the cofinal upper-band supply is
logically EQUIVALENT to the dyadic-value lever it feeds.  Forward: this module's bridge plus
the wave-10 chain.  Backward: the lever empties the hypothesis class. -/
theorem cofinalUpperBandSupply_iff_lever :
    CofinalUpperBandSupply ↔ DyadicValueLever := by
  constructor
  · intro h
    exact canonicalPerScaleSupply_iff_lever.mp
      (canonicalPerScaleSupply_of_cofinalUpperBand h)
  · intro hlever ctx _ hdy
    exact absurd hdy (hlever ctx)

/-! ## Part 7.  Machine-readable status (honest) -/

/-- Honest machine-readable status of the per-scale upper-band attack. -/
def upperBandPerScaleStatus : List String :=
  [ "OBJECTS (goal 1, exact) - M_n = windowCylinderValue d s n = sum_{i<n} d(s+i) 2^(n-1-i); " ++
      "band residue rho_n = (M_n q0) mod 2^n (bandResidue); band complement c_n = 2^n - rho_n " ++
      "in [1, 2^n] (bandComplement, bandComplement_pos); the in-tree hband shape 2^n - q0 < " ++
      "rho_n IS c_n < q0 above the threshold q0 <= 2^n (UpperBandAt, upperBandAt_iff_" ++
      "complement_lt), i.e. 2^n | q0 M_n + c_n with deficit c_n < q0 (two_pow_dvd_mul_add_" ++
      "complement): a 2-adic approximation statement about M_n/2^n vs denominator-q0 " ++
      "fractions.",
    "TRANSITION LAW (goal 1, THE HEART, PROVED) - windowCylinderValue_succ: M_{n+1} = 2 M_n " ++
      "+ d(s+n) (one dyadic digit appended). bandResidue_succ: rho_{n+1} = (2 rho_n + " ++
      "d(s+n) q0) mod 2^{n+1}. band_coupling (band at n+1, q0 <= 2^n, d binary): the exact " ++
      "integer Euclidean step 2 c_n = c_{n+1} + d(s+n) q0. digit_eq_binaryQuotient_of_band_" ++
      "succ: hence the new digit is FORCED, d(s+n) = floor(2 c_n / q0) = binaryQuotient q0 " ++
      "c_n. band_succ_of_digit (odd q0): conversely the band-preserving choice succeeds. " ++
      "upperBandAt_succ_iff_digit: given band at n, band at n+1 IFF d(s+n) takes that " ++
      "value; then c_{n+1} = (2 c_n) mod q0 = binaryRemainder q0 c_n (bandComplement_succ_" ++
      "of_band_succ) - the s25.2 binary-division orbit 2 r_j = eps_{j+1} q0 + r_{j+1}.",
    "RIGIDITY (PROVED) - upperBandAt_of_succ / upperBandAt_of_le: the band is DOWNWARD " ++
      "CLOSED above the threshold; upperBandAt_persists_not: one wrong digit kills the band " ++
      "at ALL deeper scales (no second chances); upperBandAt_forall_of_cofinal: cofinal " ++
      "band membership collapses to band on a full tail [n0, infinity).",
    "CHARACTERIZATION (goals 1-2, PROVED) - bandComplement_orbit_residue: under the band on " ++
      "[n0,inf) the complement orbit IS the s25.2 residue orbit, c_{n0+j} = dyadicResidue " ++
      "q0 c_{n0} j. upperBand_digit_orbit: the window digits are dyadicDigit q0 c_{n0} j. " ++
      "upperBandAt_tail_iff_digits (THE EQUIVALENCE): band at all depths >= n0 IFF the " ++
      "window word beyond n0 is the binary expansion of c_{n0}/q0. Band membership at all " ++
      "scales encodes ONE specific digit sequence - a q0-denominator rational expansion. " ++
      "bandComplement_eq_dyadicResidue_witness: c_n = (2^n a) mod q0 for the in-tree floor " ++
      "witness a = (M_n q0)/2^n + 1 - the manuscript residue r_n of the matched centre.",
    "FORCING VERDICT (goal 2, PROVED both ways - no shortcut) - upperBandAt_of_matches" ++
      "Completion: a depth-n match at a centre with non-vanishing residue (q0 does not " ++
      "divide a, odd q0: dyadicResidue_pos_of_not_dvd) forces the band at depth n. " ++
      "upperBandAt_cofinal_iff_tailMatch: cofinal band membership at one start is " ++
      "EQUIVALENT to (exists a < q0, q0 ndvd a, TailMatch d x q0 a). The per-scale band IS " ++
      "the tail match - consistent with canonicalPerScaleSupply_iff_lever; the carry " ++
      "envelope |R_N| <= Q(N+2) (integerCarry_abs_le) is the LINEAR envelope of the " ++
      "position-weighted carry and cannot alone force the CONSTANT deficit c_n < q0 at " ++
      "unboundedly many n. upperBandAt_completion_model: non-vacuity - the completion word " ++
      "of a non-degenerate centre is in the band at every depth above threshold.",
    "HONEST REPAIR (goal 3, NEW) - not_upperBandAt_zero: the band is FALSE at depth 0 " ++
      "(rho_0 = 0, 2^0 - q0 = 0 in Nat). perScale_residueBand_all_depths_empty: the " ++
      "wave-10 PerScaleDescentWindowMatch.ofResidueBand hypothesis (band at ALL n : Nat) " ++
      "is therefore UNSATISFIABLE at any genuine start - that route is honest but vacuous. " ++
      "PerScaleDescentWindowMatch.ofUpperBandCofinal: the repaired satisfiable bridge - " ++
      "band at COFINALLY many scales per genuine start builds the per-scale match (floor-" ++
      "witness route at a banded scale + matchesCompletion_mono downward restriction).",
    "SUCCESSOR ATOM (goal 3, named) - CofinalUpperBandSupply: at deep dyadic contexts, " ++
      "cofinal upper-band membership at every genuine start + one genuine start with onset " ++
      "budget k+r <= X+1 (pinned to the leftmost window k+r = X+1 by onsetBudget_forces_" ++
      "shell_edge under the s25.3 placement X < k+r) and order budget 2 ord <= X. " ++
      "SeedUpperBandSupply: the equivalent finitely-anchored seed form (one banded base " ++
      "depth + the tail expansion of its complement); cofinalUpperBandSupply_of_seed. " ++
      "Bridges (additive only): canonicalPerScaleSupply_of_cofinalUpperBand -> " ++
      "CanonicalPerScaleSupply -> erdos260_of_cofinalUpperBand -> Erdos260Statement. " ++
      "No free lunch transported: cofinalUpperBandSupply_iff_lever - the successor atom is " ++
      "EQUIVALENT to DyadicValueLever.",
    "WHAT s25.3 SUPPLIES AT GENERAL DEPTH (goal 2/4, honest) - the formalized s25.3/K.1 " ++
      "density layer (RhoDQCalibrationCore, RhoDQFrontierDischargeCore, RhoDQFinal" ++
      "ConsumerBridgeCore) derives the Q-correct density atoms FROM a DescentWindowMatch: " ++
      "it CONSUMES the match, it does not produce band membership. The manuscript Prop " ++
      "25.3 mechanism - the (25.1) carry envelope (formalized: integerCarry_abs_le) plus " ++
      "Lemma 25.1 cylinder stability - yields ONE match of length >= p/2 per period scale " ++
      "p at the SINGLE calibrated depth n0 = p - B (in-tree: spread+1 via hpb), never at " ++
      "unboundedly many depths of a FIXED window. By upperBandAt_cofinal_iff_tailMatch " ++
      "such a supply at one window would BE the tail match, hence the lever: no part of " ++
      "the one-scale s25.3 argument closes the per-scale atom, and there is no cheaper " ++
      "intermediate.",
    "WHAT RESISTS (goal 4) - the digit-forcing question is now exactly: does the leftmost-" ++
      "window pinch (k+r = X+1) force the actual shell word to follow the band-preserving " ++
      "digit choice d(s+n) = binaryQuotient q0 c_n at every scale beyond the calibrated " ++
      "one? By the equivalence this is the tail match itself; the transition law shows " ++
      "each step costs exactly one digit constraint and a single failure is fatal " ++
      "(upperBandAt_persists_not). The sharpest open successor is CofinalUpperBandSupply " ++
      "(equivalently SeedUpperBandSupply), proved here equivalent to the lever.",
    "HYGIENE - additive only (no existing file edited); no sorry / admit / new axiom / " ++
      "native_decide; all #print axioms in [propext, Classical.choice, Quot.sound]." ]

theorem upperBandPerScaleStatus_nonempty : upperBandPerScaleStatus ≠ [] := by
  simp [upperBandPerScaleStatus]

/-! ## Part 8.  Axiom-cleanliness audit
Every key declaration; expected axioms `[propext, Classical.choice, Quot.sound]` or fewer. -/

#print axioms bandResidue_lt
#print axioms bandComplement_pos
#print axioms bandComplement_lt_of_upperBandAt
#print axioms upperBandAt_iff_complement_lt
#print axioms two_pow_dvd_mul_add_complement
#print axioms windowCylinderValue_succ
#print axioms mod_two_pow_succ_step
#print axioms bandResidue_succ
#print axioms mod_eq_or_of_lt_two_mul
#print axioms band_coupling
#print axioms upperBandAt_of_succ
#print axioms upperBandAt_of_le
#print axioms upperBandAt_persists_not
#print axioms upperBandAt_forall_of_cofinal
#print axioms digit_eq_binaryQuotient_of_band_succ
#print axioms band_succ_of_digit
#print axioms upperBandAt_succ_iff_digit
#print axioms bandComplement_succ_of_band_succ
#print axioms dyadicResidue_pos_of_not_dvd
#print axioms bandComplement_orbit_residue
#print axioms upperBand_digit_orbit
#print axioms upperBandAt_tail_iff_digits
#print axioms upperBandAt_cofinal_of_seed
#print axioms bandComplement_eq_dyadicResidue_witness
#print axioms upperBandAt_exists_matchesCompletion
#print axioms upperBandAt_of_matchesCompletion
#print axioms upperBandAt_forall_of_tailMatch
#print axioms upperBandAt_cofinal_iff_tailMatch
#print axioms upperBandAt_completion_model
#print axioms not_upperBandAt_zero
#print axioms perScale_residueBand_all_depths_empty
#print axioms PerScaleDescentWindowMatch.ofUpperBandCofinal
#print axioms cofinalUpperBandSupply_of_seed
#print axioms canonicalPerScaleSupply_of_cofinalUpperBand
#print axioms erdos260_of_cofinalUpperBand
#print axioms cofinalUpperBandSupply_iff_lever
#print axioms upperBandPerScaleStatus_nonempty

end

end Erdos260
