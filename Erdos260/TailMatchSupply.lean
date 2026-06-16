import Erdos260.NearPeriodicityForcing

/-!
# TailMatch supply: the promotion theorem, the free per-depth supply, and the honest verdict

This module (NEW; it edits no existing file) works the project's #1 frontier: supplying
`TailMatch d x q0 a` (the all-lengths §25.1 match, `NearPeriodicityForcing`), the lone
hypothesis under which ALL pinned-value families are void at every scale
(`erdos260_of_dyadicTailMatch`).

## What is genuinely PROVED here (no `sorry`/`axiom`/`admit`/`native_decide`)

### Part 1 — rational separation pinned to the digit level (the §25.3 kernel, sharpened)

* `dyadicDigit_congr` — equal centres (`a·q0' = a'·q0`) have IDENTICAL completion words: the
  digit function `dyadicDigit q0 a` depends only on the rational `a/q0`.  Proved by pure
  division-algorithm arithmetic (`dyadicResidue_cross`), no real analysis.
* `tailMatch_centre_unique` — two tail matches at one onset have EQUAL centre values
  (separation at depth `q0 + q0' + 1` via the in-tree `descentCentre_unique_of_matches`);
  `tailMatch_numerator_unique` — with equal denominators, equal numerators;
  `tailMatch_digit_unique` — the matched completion word is unique outright.
* `tailMatch_normalize` — a tail match normalizes to a genuine residue numerator `a % q0`.

### Part 2 — THE PROMOTION (the manuscript's iterated 25.1/25.3 descent, formalized)

* `tailMatch_of_perDepth_unique` — the abstract chain argument: per-depth existence of a
  matching centre (any depth `n`, possibly a different centre `c_n`) PLUS depth-`N0`
  uniqueness of the completion word promotes to ONE centre matching at ALL depths.  The
  eventually-constant-centre chain: `c_{N0}` and `c_n` (`n ≥ N0`) both match at depth `N0`,
  so their completions agree; hence the depth-`N0` centre matches every depth.
* `tailMatch_of_perDepth_bounded` — the concrete promotion: if every depth `n` has SOME
  matching centre with denominator `≤ B` (numerator a genuine residue), then ONE such
  centre tail-matches.  Uniqueness is supplied by rational separation at depth `B + B + 1`
  (where `2·q0·q0' ≤ 2^{B+B+1}`), i.e. "once the depth exceeds the denominator scale".
* `tailMatch_of_perDepth_fixedDenominator` — fixed-`q0` form (the shape of the in-tree
  (D1) data: `DescentWindowMatch` carries a FIXED canonical `q0` and per-start numerators).
* `tailMatch_iff_perDepth_bounded` — **the exact characterization of the frontier**:
  `TailMatch` at some centre ⟺ uniformly-BOUNDED-denominator per-depth matches.

### Part 3 — per-depth existence is FREE — but with UNBOUNDED denominators

* `matchesCompletion_exists_perDepth` — UNCONDITIONALLY, every binary word matches a
  small-odd-denominator rational completion to every finite depth `n` — with
  `q0 = 2^{n+2} − 1` (the window padded by two zeros and repeated).  So the EXISTENCE half
  of the per-depth hypothesis costs nothing; the entire content of the frontier is the
  uniform BOUND on the denominator (exactly the manuscript's `q ≤ Qp` denominator drop).
  Proved via a self-contained digit extraction `dyadicDigit_windowCylinderValue`: for a
  binary `m`-periodic word with a zero in every window, the completion of
  `windowCylinderValue w 0 m / (2^m − 1)` IS the word — all digits, by the binary-division
  recurrence `2·V_j = V_{j+1} + (2^m − 1)·w_j`.

### Part 4 — the exact reach of `TailMatch`: eventual periodicity with a tail zero

* `dyadicDigit_exists_zero` — completions of genuine residues have zeros beyond every
  index (an all-ones tail would force the residue negative: `2^k + r_{J+k} ≤ q0` diverges).
* `tailMatch_of_eventuallyPeriodic` — an eventually periodic binary word with a zero in the
  tail tail-matches `q0 = 2^p − 1` (with `ord_{q0}(2) ≤ p`: window-budget-compatible).
* `tailMatch_iff_eventuallyPeriodic` — **the exact equivalence**: a small-odd-denominator
  tail match exists ⟺ the word is eventually periodic AND has a zero in the tail.

### Part 5 — the ctx level: the relaxed successor, and the NO-FREE-LUNCH verdict

* `DeepDyadicPerDepthMatch` — the sharpened successor: per-depth matches with one onset and
  a uniform denominator bound, the NUMERATOR free to vary with depth.  Strictly closer to
  the in-tree (D1) data shape; `deepDyadicTailMatch_of_perDepthMatch` promotes it, the
  endpoint is `erdos260_of_dyadicPerDepthMatch`, and `deepDyadicPerDepthMatch_iff` shows
  the relaxation costs nothing.
* **THE HONEST REFUTATION of the "self-match is free at pinned contexts" route**: the
  pinned value is the WEIGHTED value `∑ n·d_n/2^n` (`realWeightedValue`), NOT the plain
  binary value `∑ d_n/2^n` whose expansion `TailMatch` demands — and decisively, the tree
  itself PROVES no window-compatible tail match exists at any pinned context
  (`pinnedValue_tailMatch_void`, restated here as `shellValueDyadic_tailMatch_void`).  So a
  free supply at pinned contexts is impossible short of voiding them, and indeed:
  `deepDyadicTailMatch_iff_lever : DeepDyadicTailMatch ↔ DyadicValueLever`,
  `deepDyadicTailMatch_iff_windowPeriodicity`, `deepFifthTailMatch_iff_lever`,
  `deepThirdsTailMatch_iff_lever`, `deepFixedFamilyTailMatch_iff_void` — the conditional
  tail-match props are not waypoints: each is logically EQUIVALENT to the voiding it was
  meant to supply (one direction is the in-tree bridge; the other is vacuity, because the
  lever empties the hypothesis class).  Supplying `TailMatch` at pinned contexts IS the
  open problem, exactly.

No `sorry`, `admit`, new `axiom`, or `native_decide`.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 0.  Division-algorithm helpers (self-contained, `omega`-friendly) -/

/-- Uniqueness of the quotient: `Z = q·e + ρ` with `ρ < q` forces `Z / q = e`. -/
theorem divByMulAdd_eq {q e ρ Z : ℕ} (hq : 0 < q) (hρ : ρ < q)
    (hZ : Z = q * e + ρ) : Z / q = e := by
  subst hZ
  rw [Nat.add_comm, Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt hρ, Nat.zero_add]

/-- Uniqueness of the remainder: `Z = q·e + ρ` with `ρ < q` forces `Z % q = ρ`. -/
theorem modByMulAdd_eq {q e ρ Z : ℕ} (hq : 0 < q) (hρ : ρ < q)
    (hZ : Z = q * e + ρ) : Z % q = ρ := by
  subst hZ
  rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hρ]

/-! ## Part 1.  Rational separation pinned to the digit level -/

/-- Equal centre values cross-multiply: `(a:ℝ)/q0 = (a':ℝ)/q0'` gives `a·q0' = a'·q0` in `ℕ`. -/
theorem centre_cross_of_div_eq {q0 q0' a a' : ℕ} (hq0 : 0 < q0) (hq0' : 0 < q0')
    (h : (a : ℝ) / (q0 : ℝ) = (a' : ℝ) / (q0' : ℝ)) : a * q0' = a' * q0 := by
  have hq0R : ((q0 : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hq0R' : ((q0' : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [div_eq_div_iff hq0R hq0R'] at h
  exact_mod_cast h

/-- **The residue congruence**: equal centres have cross-proportional residue orbits,
`r_j·q0' = r'_j·q0` at every index — pure division-algorithm arithmetic. -/
theorem dyadicResidue_cross {q0 q0' a a' : ℕ} (hq0 : 0 < q0) (hq0' : 0 < q0')
    (hcross : a * q0' = a' * q0) (j : ℕ) :
    dyadicResidue q0 a j * q0' = dyadicResidue q0' a' j * q0 := by
  have hqq : 0 < q0 * q0' := Nat.mul_pos hq0 hq0'
  have hr : dyadicResidue q0 a j < q0 := dyadicResidue_lt hq0 a j
  have hr' : dyadicResidue q0' a' j < q0' := dyadicResidue_lt hq0' a' j
  have hd1 : q0 * (2 ^ j * a / q0) + dyadicResidue q0 a j = 2 ^ j * a :=
    Nat.div_add_mod (2 ^ j * a) q0
  have hd2 : q0' * (2 ^ j * a' / q0') + dyadicResidue q0' a' j = 2 ^ j * a' :=
    Nat.div_add_mod (2 ^ j * a') q0'
  have hZ : 2 ^ j * a * q0' = 2 ^ j * a' * q0 := by
    calc 2 ^ j * a * q0' = 2 ^ j * (a * q0') := by ring
      _ = 2 ^ j * (a' * q0) := by rw [hcross]
      _ = 2 ^ j * a' * q0 := by ring
  have h1 : 2 ^ j * a * q0'
      = (q0 * q0') * (2 ^ j * a / q0) + dyadicResidue q0 a j * q0' := by
    calc 2 ^ j * a * q0'
        = (q0 * (2 ^ j * a / q0) + dyadicResidue q0 a j) * q0' := by rw [hd1]
      _ = (q0 * q0') * (2 ^ j * a / q0) + dyadicResidue q0 a j * q0' := by ring
  have h2 : 2 ^ j * a * q0'
      = (q0 * q0') * (2 ^ j * a' / q0') + dyadicResidue q0' a' j * q0 := by
    calc 2 ^ j * a * q0' = 2 ^ j * a' * q0 := hZ
      _ = (q0' * (2 ^ j * a' / q0') + dyadicResidue q0' a' j) * q0 := by rw [hd2]
      _ = (q0 * q0') * (2 ^ j * a' / q0') + dyadicResidue q0' a' j * q0 := by ring
  have hb1 : dyadicResidue q0 a j * q0' < q0 * q0' :=
    mul_lt_mul_of_pos_right hr hq0'
  have hb2 : dyadicResidue q0' a' j * q0 < q0 * q0' := by
    calc dyadicResidue q0' a' j * q0 < q0' * q0 := mul_lt_mul_of_pos_right hr' hq0
      _ = q0 * q0' := Nat.mul_comm q0' q0
  have hm1 := modByMulAdd_eq hqq hb1 h1
  have hm2 := modByMulAdd_eq hqq hb2 h2
  rw [← hm1, ← hm2]

/-- **The digit congruence**: equal centres have IDENTICAL completion words — `dyadicDigit`
depends only on the rational value `a/q0`.  (The `ℕ`-arithmetic heart of "the centre is
determined", needed to transport per-depth matches between equal centres.) -/
theorem dyadicDigit_congr {q0 q0' a a' : ℕ} (hq0 : 0 < q0) (hq0' : 0 < q0')
    (hcross : a * q0' = a' * q0) (j : ℕ) :
    dyadicDigit q0 a j = dyadicDigit q0' a' j := by
  have hqq : 0 < q0 * q0' := Nat.mul_pos hq0 hq0'
  have hres := dyadicResidue_cross hq0 hq0' hcross j
  have hd1 : q0 * (2 * dyadicResidue q0 a j / q0) + 2 * dyadicResidue q0 a j % q0
      = 2 * dyadicResidue q0 a j := Nat.div_add_mod (2 * dyadicResidue q0 a j) q0
  have hd2 : q0' * (2 * dyadicResidue q0' a' j / q0') + 2 * dyadicResidue q0' a' j % q0'
      = 2 * dyadicResidue q0' a' j := Nat.div_add_mod (2 * dyadicResidue q0' a' j) q0'
  have hρ1 : 2 * dyadicResidue q0 a j % q0 < q0 := Nat.mod_lt _ hq0
  have hρ2 : 2 * dyadicResidue q0' a' j % q0' < q0' := Nat.mod_lt _ hq0'
  have h1 : 2 * dyadicResidue q0 a j * q0'
      = (q0 * q0') * (2 * dyadicResidue q0 a j / q0)
        + (2 * dyadicResidue q0 a j % q0) * q0' := by
    calc 2 * dyadicResidue q0 a j * q0'
        = (q0 * (2 * dyadicResidue q0 a j / q0) + 2 * dyadicResidue q0 a j % q0) * q0' := by
          rw [hd1]
      _ = (q0 * q0') * (2 * dyadicResidue q0 a j / q0)
            + (2 * dyadicResidue q0 a j % q0) * q0' := by ring
  have h2 : 2 * dyadicResidue q0 a j * q0'
      = (q0 * q0') * (2 * dyadicResidue q0' a' j / q0')
        + (2 * dyadicResidue q0' a' j % q0') * q0 := by
    calc 2 * dyadicResidue q0 a j * q0'
        = 2 * (dyadicResidue q0 a j * q0') := by ring
      _ = 2 * (dyadicResidue q0' a' j * q0) := by rw [hres]
      _ = 2 * dyadicResidue q0' a' j * q0 := by ring
      _ = (q0' * (2 * dyadicResidue q0' a' j / q0')
            + 2 * dyadicResidue q0' a' j % q0') * q0 := by rw [hd2]
      _ = (q0 * q0') * (2 * dyadicResidue q0' a' j / q0')
            + (2 * dyadicResidue q0' a' j % q0') * q0 := by ring
  have hb1 : (2 * dyadicResidue q0 a j % q0) * q0' < q0 * q0' :=
    mul_lt_mul_of_pos_right hρ1 hq0'
  have hb2 : (2 * dyadicResidue q0' a' j % q0') * q0 < q0 * q0' := by
    calc (2 * dyadicResidue q0' a' j % q0') * q0 < q0' * q0 :=
          mul_lt_mul_of_pos_right hρ2 hq0
      _ = q0 * q0' := Nat.mul_comm q0' q0
  have he1 := divByMulAdd_eq hqq hb1 h1
  have he2 := divByMulAdd_eq hqq hb2 h2
  show binaryQuotient q0 (dyadicResidue q0 a j) = binaryQuotient q0' (dyadicResidue q0' a' j)
  show 2 * dyadicResidue q0 a j / q0 = 2 * dyadicResidue q0' a' j / q0'
  rw [← he1, ← he2]

/-- Reducing the numerator mod `q0` does not change the residue orbit. -/
theorem dyadicResidue_mod_left (q0 a : ℕ) (j : ℕ) :
    dyadicResidue q0 (a % q0) j = dyadicResidue q0 a j :=
  (Nat.ModEq.mul_left (2 ^ j) (Nat.mod_modEq a q0))

/-- Reducing the numerator mod `q0` does not change the completion word. -/
theorem dyadicDigit_mod_left (q0 a : ℕ) (j : ℕ) :
    dyadicDigit q0 (a % q0) j = dyadicDigit q0 a j := by
  unfold dyadicDigit
  rw [dyadicResidue_mod_left]

/-- A tail match normalizes to a genuine residue numerator `a % q0 < q0`. -/
theorem tailMatch_normalize {d : ℕ → ℕ} {x q0 a : ℕ}
    (h : TailMatch d x q0 a) : TailMatch d x q0 (a % q0) :=
  fun i => (h i).trans (dyadicDigit_mod_left q0 a i).symm

/-- The separation depth: `2·q0·q0' ≤ 2^{B+B'+1}` whenever `q0 ≤ B`, `q0' ≤ B'`. -/
theorem two_mul_mul_le_two_pow {q0 q0' B B' : ℕ} (h : q0 ≤ B) (h' : q0' ≤ B') :
    2 * q0 * q0' ≤ 2 ^ (B + B' + 1) := by
  have h1 : q0 ≤ 2 ^ B := le_trans h (Nat.le_of_lt Nat.lt_two_pow_self)
  have h2 : q0' ≤ 2 ^ B' := le_trans h' (Nat.le_of_lt Nat.lt_two_pow_self)
  calc 2 * q0 * q0' ≤ 2 * 2 ^ B * 2 ^ B' :=
        Nat.mul_le_mul (Nat.mul_le_mul (le_refl 2) h1) h2
    _ = 2 ^ (B + B' + 1) := by rw [pow_add, pow_add, pow_one]; ring

/-- **Tail-level centre uniqueness** (manuscript §25.3 / `descentCentre_unique` promoted to
the tail): two tail matches at one onset have equal centre VALUES — separation fires at
depth `q0 + q0' + 1`, beyond both denominator scales. -/
theorem tailMatch_centre_unique {d : ℕ → ℕ} {x q0 q0' a a' : ℕ}
    (hq0 : 0 < q0) (hq0' : 0 < q0') (ha : a < q0) (ha' : a' < q0')
    (h : TailMatch d x q0 a) (h' : TailMatch d x q0' a') :
    (a : ℝ) / (q0 : ℝ) = (a' : ℝ) / (q0' : ℝ) :=
  descentCentre_unique_of_matches hq0 hq0' ha ha'
    (two_mul_mul_le_two_pow (le_refl q0) (le_refl q0'))
    (matchesCompletion_of_tailMatch h (q0 + q0' + 1))
    (matchesCompletion_of_tailMatch h' (q0 + q0' + 1))

/-- Two tail matches at one onset use the SAME completion word (trivially: both equal the
word's tail). -/
theorem tailMatch_digit_unique {d : ℕ → ℕ} {x q0 q0' a a' : ℕ}
    (h : TailMatch d x q0 a) (h' : TailMatch d x q0' a') (i : ℕ) :
    dyadicDigit q0 a i = dyadicDigit q0' a' i :=
  (h i).symm.trans (h' i)

/-- With equal denominators the matched numerator is unique outright. -/
theorem tailMatch_numerator_unique {d : ℕ → ℕ} {x q0 a a' : ℕ}
    (hq0 : 0 < q0) (ha : a < q0) (ha' : a' < q0)
    (h : TailMatch d x q0 a) (h' : TailMatch d x q0 a') : a = a' := by
  have hval := tailMatch_centre_unique hq0 hq0 ha ha' h h'
  have hcross := centre_cross_of_div_eq hq0 hq0 hval
  exact Nat.eq_of_mul_eq_mul_right hq0 hcross

/-! ## Part 2.  THE PROMOTION: per-depth matches with a uniform denominator bound
promote to one centre at all depths -/

/-- Matches restrict to smaller depths (the cylinder refinement, downward). -/
theorem matchesCompletion_mono {d : ℕ → ℕ} {s q0 a : ℕ} {m n : ℕ} (h : m ≤ n)
    (hm : MatchesCompletion d s n q0 a) : MatchesCompletion d s m q0 a :=
  fun i hi => hm i (lt_of_lt_of_le hi h)

/-- **The abstract promotion chain** (the manuscript's iterated 25.1/25.3 descent): if every
depth has a matching centre in a class `P`, and the COMPLETION WORD of a `P`-centre is
determined by its depth-`N0` match (the separation input), then the depth-`N0` centre
matches at EVERY depth.  Chain: the depth-`(N0+i+1)` centre matches at depth `N0` (by
restriction) and at index `i`; uniqueness transports the index-`i` digit to the depth-`N0`
centre. -/
theorem tailMatch_of_perDepth_unique {d : ℕ → ℕ} {x : ℕ} (N0 : ℕ) {P : ℕ → ℕ → Prop}
    (hex : ∀ n : ℕ, ∃ q0 a : ℕ, P q0 a ∧ MatchesCompletion d (x + 1) n q0 a)
    (huniq : ∀ q0 a q0' a', P q0 a → P q0' a' →
      MatchesCompletion d (x + 1) N0 q0 a → MatchesCompletion d (x + 1) N0 q0' a' →
      ∀ i, dyadicDigit q0 a i = dyadicDigit q0' a' i) :
    ∃ q0 a : ℕ, P q0 a ∧ TailMatch d x q0 a := by
  obtain ⟨q0, a, hP, hm⟩ := hex N0
  refine ⟨q0, a, hP, fun i => ?_⟩
  obtain ⟨q0', a', hP', hm'⟩ := hex (N0 + (i + 1))
  have hm'N0 : MatchesCompletion d (x + 1) N0 q0' a' :=
    matchesCompletion_mono (Nat.le_add_right N0 (i + 1)) hm'
  have hmi : d (x + 1 + i) = dyadicDigit q0' a' i := hm' i (by omega)
  rw [hmi]
  exact huniq q0' a' q0 a hP' hP hm'N0 hm i

/-- **THE PROMOTION, bounded form**: per-depth existence of a matching centre with
denominator `≤ B` (numerator a genuine residue) promotes to a single tail-matching centre.
The separation depth is `B + B + 1` — "the depth exceeds the denominator scale". -/
theorem tailMatch_of_perDepth_bounded {d : ℕ → ℕ} {x B : ℕ}
    (hex : ∀ n : ℕ, ∃ q0 a : ℕ, (0 < q0 ∧ q0 ≤ B ∧ a < q0) ∧
      MatchesCompletion d (x + 1) n q0 a) :
    ∃ q0 a : ℕ, (0 < q0 ∧ q0 ≤ B ∧ a < q0) ∧ TailMatch d x q0 a := by
  refine tailMatch_of_perDepth_unique (B + B + 1) hex ?_
  rintro q0 a q0' a' ⟨hq0, hqB, ha⟩ ⟨hq0', hqB', ha'⟩ hm hm' i
  have hsep : 2 * q0 * q0' ≤ 2 ^ (B + B + 1) := two_mul_mul_le_two_pow hqB hqB'
  have hval : (a : ℝ) / (q0 : ℝ) = (a' : ℝ) / (q0' : ℝ) :=
    descentCentre_unique_of_matches hq0 hq0' ha ha' hsep hm hm'
  exact dyadicDigit_congr hq0 hq0' (centre_cross_of_div_eq hq0 hq0' hval) i

/-- **THE PROMOTION, fixed-denominator form** — the exact shape of the in-tree (D1) supply
(`DescentWindowMatch` carries a FIXED canonical `q0` with per-start numerators): per-depth
matches at one `q0` (numerator free per depth) promote to one numerator at all depths. -/
theorem tailMatch_of_perDepth_fixedDenominator {d : ℕ → ℕ} {x q0 : ℕ} (hq0 : 0 < q0)
    (hex : ∀ n : ℕ, ∃ a : ℕ, a < q0 ∧ MatchesCompletion d (x + 1) n q0 a) :
    ∃ a : ℕ, a < q0 ∧ TailMatch d x q0 a := by
  have huniq : ∀ (q a q' a' : ℕ), (q0 = q ∧ a < q0) → (q0 = q' ∧ a' < q0) →
      MatchesCompletion d (x + 1) (q0 + q0 + 1) q a →
      MatchesCompletion d (x + 1) (q0 + q0 + 1) q' a' →
      ∀ i, dyadicDigit q a i = dyadicDigit q' a' i := by
    rintro q a q' a' ⟨rfl, ha⟩ ⟨rfl, ha'⟩ hm hm' i
    have hsep : 2 * q0 * q0 ≤ 2 ^ (q0 + q0 + 1) :=
      two_mul_mul_le_two_pow (le_refl q0) (le_refl q0)
    have hval : (a : ℝ) / (q0 : ℝ) = (a' : ℝ) / (q0 : ℝ) :=
      descentCentre_unique_of_matches hq0 hq0 ha ha' hsep hm hm'
    exact dyadicDigit_congr hq0 hq0 (centre_cross_of_div_eq hq0 hq0 hval) i
  obtain ⟨q, a, ⟨hq, ha⟩, hm⟩ :=
    tailMatch_of_perDepth_unique (q0 + q0 + 1) (P := fun q a => q0 = q ∧ a < q0)
      (fun n => (hex n).elim fun a ha => ⟨q0, a, ⟨rfl, ha.1⟩, ha.2⟩) huniq
  subst hq
  exact ⟨a, ha, hm⟩

/-- **The exact characterization of the frontier**: a tail match at SOME centre exists IFF
the per-depth matches admit a UNIFORM denominator bound.  (Forward: the tail-match centre
works at every depth with `B := q0`.  Backward: the promotion.)  Combined with Part 3
(existence with `q0 = 2^{n+2} − 1` is free), the entire content of `TailMatch` is the
BOUND — the manuscript's `q ≤ Qp` denominator drop, uniform in depth. -/
theorem tailMatch_iff_perDepth_bounded {d : ℕ → ℕ} {x : ℕ} :
    (∃ q0 a : ℕ, 0 < q0 ∧ a < q0 ∧ TailMatch d x q0 a)
      ↔ ∃ B : ℕ, ∀ n : ℕ, ∃ q0 a : ℕ,
          (0 < q0 ∧ q0 ≤ B ∧ a < q0) ∧ MatchesCompletion d (x + 1) n q0 a := by
  constructor
  · rintro ⟨q0, a, hq0, ha, hm⟩
    exact ⟨q0, fun n =>
      ⟨q0, a, ⟨hq0, le_refl q0, ha⟩, matchesCompletion_of_tailMatch hm n⟩⟩
  · rintro ⟨B, hex⟩
    obtain ⟨q0, a, ⟨hq0, _, ha⟩, hm⟩ := tailMatch_of_perDepth_bounded hex
    exact ⟨q0, a, hq0, ha, hm⟩

/-! ## Part 3.  Per-depth existence is FREE — at unbounded denominators -/

/-- The reflected geometric sum `∑_{i<m} 2^{m−1−i} = 2^m − 1`. -/
theorem sum_range_two_pow_reflect (m : ℕ) :
    ∑ i ∈ Finset.range m, 2 ^ (m - 1 - i) = 2 ^ m - 1 := by
  rw [Finset.sum_range_reflect (fun i => 2 ^ i) m]
  exact sum_range_two_pow_eq_periodDen m

/-- **The window-value shift recurrence** for an `(k+1)`-periodic word (additive form, no
`ℕ`-subtraction): `2·V_j + w_j = V_{j+1} + 2^{k+1}·w_j` where `V_j` is the depth-`(k+1)`
window value at start `j`. -/
theorem windowValue_step_of_periodic {w : ℕ → ℕ} {k : ℕ}
    (hper : ∀ j, w (j + (k + 1)) = w j) (j : ℕ) :
    2 * windowCylinderValue w j (k + 1) + w j
      = windowCylinderValue w (j + 1) (k + 1) + 2 ^ (k + 1) * w j := by
  have hcongr1 : ∑ i ∈ Finset.range (k + 1), 2 * (w (j + i) * 2 ^ (k + 1 - 1 - i))
      = ∑ i ∈ Finset.range (k + 1), w (j + i) * 2 ^ (k + 1 - i) :=
    Finset.sum_congr rfl (fun i hi => by
      rw [Finset.mem_range] at hi
      have he : k + 1 - i = (k + 1 - 1 - i) + 1 := by omega
      rw [he, pow_succ]
      ring)
  have hpeel : ∑ i ∈ Finset.range (k + 1), w (j + i) * 2 ^ (k + 1 - i)
      = (∑ i ∈ Finset.range k, w (j + (i + 1)) * 2 ^ (k + 1 - (i + 1)))
        + w (j + 0) * 2 ^ (k + 1 - 0) :=
    Finset.sum_range_succ' (fun i => w (j + i) * 2 ^ (k + 1 - i)) k
  have hcongr2 : ∑ i ∈ Finset.range k, w (j + (i + 1)) * 2 ^ (k + 1 - (i + 1))
      = ∑ i ∈ Finset.range k, w (j + 1 + i) * 2 ^ (k - i) :=
    Finset.sum_congr rfl (fun i hi => by
      rw [Finset.mem_range] at hi
      have he : k + 1 - (i + 1) = k - i := by omega
      have hadd : j + (i + 1) = j + 1 + i := by omega
      rw [he, hadd])
  have hL : 2 * windowCylinderValue w j (k + 1)
      = (∑ i ∈ Finset.range k, w (j + 1 + i) * 2 ^ (k - i)) + 2 ^ (k + 1) * w j := by
    unfold windowCylinderValue
    rw [Finset.mul_sum, hcongr1, hpeel, hcongr2, Nat.add_zero, Nat.sub_zero]
    ring
  have hcongr3 : ∑ i ∈ Finset.range k, w (j + 1 + i) * 2 ^ (k + 1 - 1 - i)
      = ∑ i ∈ Finset.range k, w (j + 1 + i) * 2 ^ (k - i) :=
    Finset.sum_congr rfl (fun i hi => by
      rw [Finset.mem_range] at hi
      have he : k + 1 - 1 - i = k - i := by omega
      rw [he])
  have hR : windowCylinderValue w (j + 1) (k + 1)
      = (∑ i ∈ Finset.range k, w (j + 1 + i) * 2 ^ (k - i)) + w j := by
    unfold windowCylinderValue
    rw [Finset.sum_range_succ, hcongr3]
    have hlast : w (j + 1 + k) * 2 ^ (k + 1 - 1 - k) = w j := by
      have hadd : j + 1 + k = j + (k + 1) := by omega
      have he : k + 1 - 1 - k = 0 := by omega
      rw [hadd, he, pow_zero, mul_one, hper j]
    rw [hlast]
  rw [hL, hR]
  ring

/-- **The strict window bound from one zero**: a binary window containing a zero has value
strictly below `2^m − 1`. -/
theorem windowValue_lt_of_zero {w : ℕ → ℕ} {m : ℕ} (hw : ∀ j, w j ≤ 1)
    {j i0 : ℕ} (hi0 : i0 < m) (h0 : w (j + i0) = 0) :
    windowCylinderValue w j m < 2 ^ m - 1 := by
  have hmem : i0 ∈ Finset.range m := Finset.mem_range.mpr hi0
  have hgeom : ∑ i ∈ Finset.range m, 2 ^ (m - 1 - i) = 2 ^ m - 1 :=
    sum_range_two_pow_reflect m
  have hsplitT : (∑ i ∈ (Finset.range m).erase i0, 2 ^ (m - 1 - i)) + 2 ^ (m - 1 - i0)
      = 2 ^ m - 1 :=
    (Finset.sum_erase_add (Finset.range m) (fun i => 2 ^ (m - 1 - i)) hmem).trans hgeom
  have hsplitR : (∑ i ∈ (Finset.range m).erase i0, w (j + i) * 2 ^ (m - 1 - i))
        + w (j + i0) * 2 ^ (m - 1 - i0)
      = windowCylinderValue w j m :=
    Finset.sum_erase_add (Finset.range m) (fun i => w (j + i) * 2 ^ (m - 1 - i)) hmem
  rw [h0, Nat.zero_mul, Nat.add_zero] at hsplitR
  have hle : ∑ i ∈ (Finset.range m).erase i0, w (j + i) * 2 ^ (m - 1 - i)
      ≤ ∑ i ∈ (Finset.range m).erase i0, 2 ^ (m - 1 - i) :=
    Finset.sum_le_sum (fun i _ => by
      calc w (j + i) * 2 ^ (m - 1 - i) ≤ 1 * 2 ^ (m - 1 - i) :=
            Nat.mul_le_mul (hw (j + i)) (le_refl _)
        _ = 2 ^ (m - 1 - i) := Nat.one_mul _)
  have hone : 1 ≤ 2 ^ (m - 1 - i0) := Nat.one_le_two_pow
  omega

/-- Every residue class is hit inside any length-`p` window: `∃ i < p, (j + i) % p = r0`. -/
theorem exists_shift_mod {p : ℕ} (hp : 0 < p) {r0 : ℕ} (hr0 : r0 < p) (j : ℕ) :
    ∃ i, i < p ∧ (j + i) % p = r0 := by
  have hjp : j % p < p := Nat.mod_lt _ hp
  refine ⟨(r0 + p - j % p) % p, Nat.mod_lt _ hp, ?_⟩
  have c1 : (j + (r0 + p - j % p) % p) % p = (j % p + (r0 + p - j % p)) % p :=
    Nat.ModEq.add (Nat.mod_modEq j p).symm (Nat.mod_modEq (r0 + p - j % p) p)
  have c2 : j % p + (r0 + p - j % p) = r0 + p := by omega
  calc (j + (r0 + p - j % p) % p) % p = (j % p + (r0 + p - j % p)) % p := c1
    _ = (r0 + p) % p := by rw [c2]
    _ = r0 % p := Nat.add_mod_right r0 p
    _ = r0 := Nat.mod_eq_of_lt hr0

/-- **The digit extraction** (the engine of the free supply): for a binary `m`-periodic word
with a zero in every length-`m` window, the rational completion of
`windowCylinderValue w 0 m / (2^m − 1)` IS the word — at EVERY index.  Proof: the residue
orbit of the centre is exactly the window-value orbit `V_j` (induction via the shift
recurrence and remainder uniqueness), and the emitted digit is the quotient `w_j`. -/
theorem dyadicDigit_windowCylinderValue {w : ℕ → ℕ} {m : ℕ} (hm : 0 < m)
    (hw : ∀ j, w j ≤ 1) (hper : ∀ j, w (j + m) = w j)
    (hzero : ∀ j, ∃ i, i < m ∧ w (j + i) = 0) :
    ∀ j, dyadicDigit (2 ^ m - 1) (windowCylinderValue w 0 m) j = w j := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hone : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  have hq0pos : 0 < 2 ^ (k + 1) - 1 := by
    have h2 : 2 ^ 1 ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2' : (2 : ℕ) ^ 1 = 2 := by norm_num
    omega
  have hbound : ∀ j, windowCylinderValue w j (k + 1) < 2 ^ (k + 1) - 1 := by
    intro j
    obtain ⟨i0, hi0, h0⟩ := hzero j
    exact windowValue_lt_of_zero hw hi0 h0
  have hstep : ∀ j, 2 * windowCylinderValue w j (k + 1)
      = windowCylinderValue w (j + 1) (k + 1) + (2 ^ (k + 1) - 1) * w j := by
    intro j
    have h := windowValue_step_of_periodic hper j
    have hw1 := hw j
    rcases (by omega : w j = 0 ∨ w j = 1) with h1 | h1 <;> rw [h1] at h ⊢ <;> omega
  have hres : ∀ j, dyadicResidue (2 ^ (k + 1) - 1) (windowCylinderValue w 0 (k + 1)) j
      = windowCylinderValue w j (k + 1) := by
    intro j
    induction j with
    | zero =>
      show 2 ^ 0 * windowCylinderValue w 0 (k + 1) % (2 ^ (k + 1) - 1)
          = windowCylinderValue w 0 (k + 1)
      rw [pow_zero, Nat.one_mul]
      exact Nat.mod_eq_of_lt (hbound 0)
    | succ i ih =>
      rw [dyadicResidue_step, ih]
      show 2 * windowCylinderValue w i (k + 1) % (2 ^ (k + 1) - 1)
          = windowCylinderValue w (i + 1) (k + 1)
      rw [hstep i]
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (hbound (i + 1))
  intro j
  show binaryQuotient (2 ^ (k + 1) - 1)
      (dyadicResidue (2 ^ (k + 1) - 1) (windowCylinderValue w 0 (k + 1)) j) = w j
  rw [hres j]
  show 2 * windowCylinderValue w j (k + 1) / (2 ^ (k + 1) - 1) = w j
  rw [hstep j, Nat.add_mul_div_left _ _ hq0pos, Nat.div_eq_of_lt (hbound (j + 1)),
    Nat.zero_add]

/-- The depth-`n` padding word: the window digits of `d` on `[s, s+n)`, padded by TWO zeros,
repeated with period `n + 2`. -/
def paddedPeriodicWord (d : ℕ → ℕ) (s n : ℕ) : ℕ → ℕ :=
  fun j => if j % (n + 2) < n then d (s + j % (n + 2)) else 0

theorem paddedPeriodicWord_le_one {d : ℕ → ℕ} (hd : BinaryDigits d) (s n : ℕ) :
    ∀ j, paddedPeriodicWord d s n j ≤ 1 := by
  intro j
  unfold paddedPeriodicWord
  split
  · rcases hd (s + j % (n + 2)) with h | h <;> omega
  · omega

theorem paddedPeriodicWord_periodic (d : ℕ → ℕ) (s n : ℕ) :
    ∀ j, paddedPeriodicWord d s n (j + (n + 2)) = paddedPeriodicWord d s n j := by
  intro j
  unfold paddedPeriodicWord
  rw [Nat.add_mod_right]

theorem paddedPeriodicWord_window_zero (d : ℕ → ℕ) (s n : ℕ) :
    ∀ j, ∃ i, i < n + 2 ∧ paddedPeriodicWord d s n (j + i) = 0 := by
  intro j
  obtain ⟨i, hip, hmod⟩ := exists_shift_mod (p := n + 2) (by omega)
    (r0 := n + 1) (by omega) j
  refine ⟨i, hip, ?_⟩
  unfold paddedPeriodicWord
  rw [hmod, if_neg (by omega)]

theorem paddedPeriodicWord_eq_of_lt (d : ℕ → ℕ) (s : ℕ) {n i : ℕ} (hi : i < n) :
    paddedPeriodicWord d s n i = d (s + i) := by
  unfold paddedPeriodicWord
  rw [Nat.mod_eq_of_lt (by omega : i < n + 2), if_pos hi]

/-- **PER-DEPTH EXISTENCE IS FREE** (the unconditional half of the frontier): every binary
word matches a small-odd-denominator rational completion to EVERY finite depth `n` — with
witness denominator `q0 = 2^{n+2} − 1`, GROWING with the depth.  Combined with
`tailMatch_iff_perDepth_bounded`, the entire content of `TailMatch` is the uniform BOUND
on the denominator across depths; existence costs nothing. -/
theorem matchesCompletion_exists_perDepth {d : ℕ → ℕ} (hd : BinaryDigits d) (s n : ℕ) :
    ∃ q0 a : ℕ, 1 < q0 ∧ Odd q0 ∧ a < q0 ∧ q0 = 2 ^ (n + 2) - 1 ∧
      MatchesCompletion d s n q0 a := by
  have hw := paddedPeriodicWord_le_one hd s n
  have hper := paddedPeriodicWord_periodic d s n
  have hzero := paddedPeriodicWord_window_zero d s n
  have hdig := dyadicDigit_windowCylinderValue (m := n + 2) (by omega) hw hper hzero
  have h4 : 4 ≤ 2 ^ (n + 2) := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hone : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
  have hsplit : 2 ^ (n + 2) = 2 ^ (n + 1) * 2 := by rw [← pow_succ]
  refine ⟨2 ^ (n + 2) - 1, windowCylinderValue (paddedPeriodicWord d s n) 0 (n + 2),
    by omega, ?_, ?_, rfl, ?_⟩
  · rw [Nat.odd_iff]
    omega
  · obtain ⟨i0, hi0, h0⟩ := hzero 0
    exact windowValue_lt_of_zero hw hi0 h0
  · intro i hi
    rw [hdig i, paddedPeriodicWord_eq_of_lt d s hi]

/-- The free per-depth supply, at every actual failure context and every onset. -/
theorem matchesCompletion_exists_perDepth_ctx (ctx : ActualFailureContext) (x : ℕ) :
    ∀ n : ℕ, ∃ q0 a : ℕ, 1 < q0 ∧ Odd q0 ∧ a < q0 ∧
      MatchesCompletion ctx.d (x + 1) n q0 a := by
  intro n
  obtain ⟨q0, a, hq0, hodd, ha, _, hm⟩ := matchesCompletion_exists_perDepth ctx.hd (x + 1) n
  exact ⟨q0, a, hq0, hodd, ha, hm⟩

/-! ## Part 4.  The exact reach of `TailMatch`: eventual periodicity with a tail zero -/

/-- **Completions of genuine residues have zeros beyond every index**: an all-ones tail
would drive `q0 − r` into unbounded doubling (`2^k + r_{J+k} ≤ q0` for all `k`), beating
`q0 < 2^{q0}`. -/
theorem dyadicDigit_exists_zero {q0 a : ℕ} (hq0 : 0 < q0) (ha : a < q0) (J : ℕ) :
    ∃ j : ℕ, J ≤ j ∧ dyadicDigit q0 a j = 0 := by
  by_contra hcon
  push Not at hcon
  have hone : ∀ j, J ≤ j → dyadicDigit q0 a j = 1 := by
    intro j hj
    have h1 : dyadicDigit q0 a j ≤ 1 :=
      binaryQuotient_le_one hq0 (dyadicResidue_lt hq0 a j)
    have h2 := hcon j hj
    omega
  have hstep : ∀ j, J ≤ j →
      2 * dyadicResidue q0 a j = q0 + dyadicResidue q0 a (j + 1) := by
    intro j hj
    have hdm : q0 * (2 * dyadicResidue q0 a j / q0) + 2 * dyadicResidue q0 a j % q0
        = 2 * dyadicResidue q0 a j := Nat.div_add_mod (2 * dyadicResidue q0 a j) q0
    have hq : 2 * dyadicResidue q0 a j / q0 = 1 := hone j hj
    have hr1 : dyadicResidue q0 a (j + 1) = 2 * dyadicResidue q0 a j % q0 :=
      dyadicResidue_step q0 a j
    rw [hq, Nat.mul_one] at hdm
    omega
  have henv : ∀ k : ℕ, 2 ^ k + dyadicResidue q0 a (J + k) ≤ q0 := by
    intro k
    induction k with
    | zero =>
      have h := dyadicResidue_lt hq0 a (J + 0)
      simp only [pow_zero]
      omega
    | succ k ih =>
      have hs := hstep (J + k) (by omega)
      have hlt := dyadicResidue_lt hq0 a (J + k + 1)
      have hJk : J + (k + 1) = J + k + 1 := by omega
      rw [hJk, pow_succ]
      omega
  have hfin := henv q0
  have hbig : q0 < 2 ^ q0 := Nat.lt_two_pow_self
  omega

/-- **The converse bridge**: an eventually periodic binary word (period `p ≥ 2`) with a zero
in the tail tail-matches the centre `windowValue/(2^p − 1)` — with the orbit order bounded
by the period (`ord_{q0}(2) ≤ p`, window-budget-compatible). -/
theorem tailMatch_of_eventuallyPeriodic {d : ℕ → ℕ} (hd : BinaryDigits d) {x p : ℕ}
    (hp : 2 ≤ p) (hper : ∀ n, x < n → d (n + p) = d n)
    (hzero : ∃ j, x < j ∧ d j = 0) :
    ∃ q0 a : ℕ, 1 < q0 ∧ Odd q0 ∧ a < q0 ∧ orderOf (2 : ZMod q0) ≤ p ∧
      TailMatch d x q0 a := by
  have hppos : 0 < p := by omega
  set w : ℕ → ℕ := fun j => d (x + 1 + j) with hwdef
  have hwper : ∀ j, w (j + p) = w j := by
    intro j
    simp only [hwdef]
    rw [show x + 1 + (j + p) = (x + 1 + j) + p from by omega]
    exact hper (x + 1 + j) (by omega)
  have hwperiter : ∀ a t : ℕ, w (a + t * p) = w a := by
    intro a t
    induction t with
    | zero => simp
    | succ k ih =>
      rw [show a + (k + 1) * p = (a + k * p) + p from by ring, hwper, ih]
  have hw : ∀ j, w j ≤ 1 := by
    intro j
    simp only [hwdef]
    rcases hd (x + 1 + j) with h | h <;> omega
  obtain ⟨j0, hj0x, hj00⟩ := hzero
  have hk0 : w (j0 - x - 1) = 0 := by
    simp only [hwdef]
    rw [show x + 1 + (j0 - x - 1) = j0 from by omega]
    exact hj00
  have hr0lt : (j0 - x - 1) % p < p := Nat.mod_lt _ hppos
  have hwr0 : w ((j0 - x - 1) % p) = 0 := by
    have hit : w ((j0 - x - 1) % p + (j0 - x - 1) / p * p) = w ((j0 - x - 1) % p) :=
      hwperiter ((j0 - x - 1) % p) ((j0 - x - 1) / p)
    rw [Nat.mod_add_div'] at hit
    rw [← hit]
    exact hk0
  have hwzero : ∀ j, ∃ i, i < p ∧ w (j + i) = 0 := by
    intro j
    obtain ⟨i, hip, hmod⟩ := exists_shift_mod hppos hr0lt j
    refine ⟨i, hip, ?_⟩
    have hit : w ((j + i) % p + (j + i) / p * p) = w ((j + i) % p) :=
      hwperiter ((j + i) % p) ((j + i) / p)
    rw [Nat.mod_add_div'] at hit
    rw [hit, hmod]
    exact hwr0
  have hdig := dyadicDigit_windowCylinderValue (m := p) hppos hw hwper hwzero
  have h4 : 4 ≤ 2 ^ p := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp
  have honep : 1 ≤ 2 ^ (p - 1) := Nat.one_le_two_pow
  have hsplit : 2 ^ p = 2 ^ (p - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  have hq0big : 1 < 2 ^ p - 1 := by omega
  refine ⟨2 ^ p - 1, windowCylinderValue w 0 p, hq0big, ?_, ?_, ?_, fun i => ?_⟩
  · rw [Nat.odd_iff]
    omega
  · obtain ⟨i0, hi0, h0⟩ := hwzero 0
    exact windowValue_lt_of_zero hw hi0 h0
  · have hpow : (2 : ZMod (2 ^ p - 1)) ^ p = 1 := by
      have hmod : (2 : ℕ) ^ p % (2 ^ p - 1) = 1 % (2 ^ p - 1) := by
        have key : (1 + (2 ^ p - 1)) % (2 ^ p - 1) = 1 % (2 ^ p - 1) :=
          Nat.add_mod_right 1 (2 ^ p - 1)
        have h2 : 1 + (2 ^ p - 1) = 2 ^ p := by omega
        rw [h2] at key
        exact key
      have hcast : ((2 ^ p : ℕ) : ZMod (2 ^ p - 1)) = ((1 : ℕ) : ZMod (2 ^ p - 1)) :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
      push_cast at hcast
      exact hcast
    exact Nat.le_of_dvd hppos (orderOf_dvd_of_pow_eq_one hpow)
  · exact (hdig i).symm

/-- **The exact equivalence** (the honest answer to "what IS `TailMatch`"): a binary word
admits a small-odd-denominator tail match at onset `x` IFF it is eventually periodic past
`x` AND carries a zero past `x`.  Forward: the completion's own period
(`tailMatch_eventually_periodic`) and its guaranteed zeros (`dyadicDigit_exists_zero`).
Backward: `tailMatch_of_eventuallyPeriodic` at the doubled period. -/
theorem tailMatch_iff_eventuallyPeriodic {d : ℕ → ℕ} (hd : BinaryDigits d) (x : ℕ) :
    (∃ q0 a : ℕ, 1 < q0 ∧ Odd q0 ∧ a < q0 ∧ TailMatch d x q0 a)
      ↔ ((∃ p : ℕ, 0 < p ∧ ∀ n, x < n → d (n + p) = d n) ∧ ∃ j, x < j ∧ d j = 0) := by
  constructor
  · rintro ⟨q0, a, hq0, hodd, ha, hm⟩
    constructor
    · exact ⟨orderOf (2 : ZMod q0),
        orderOf_pos_iff.mpr (isOfFinOrder_two_zmod hq0 hodd),
        tailMatch_eventually_periodic hm⟩
    · obtain ⟨i, _, h0⟩ := dyadicDigit_exists_zero (by omega : 0 < q0) ha 0
      exact ⟨x + 1 + i, by omega, (hm i).trans h0⟩
  · rintro ⟨⟨p, hp, hper⟩, hzero⟩
    have hper2 : ∀ n, x < n → d (n + (p + p)) = d n := by
      intro n hn
      have h1 : d (n + p) = d n := hper n hn
      have h2 : d (n + p + p) = d (n + p) := hper (n + p) (by omega)
      rw [show n + (p + p) = n + p + p from by omega, h2, h1]
    obtain ⟨q0, a, hq0, hodd, ha, _, hm⟩ :=
      tailMatch_of_eventuallyPeriodic hd (by omega : 2 ≤ p + p) hper2 hzero
    exact ⟨q0, a, hq0, hodd, ha, hm⟩

/-! ## Part 5.  The ctx level: the relaxed successor and the no-free-lunch verdict -/

/-- **The sharpened successor** (the deliverable shape for future supply waves): per-depth
matches at ONE onset with a UNIFORM denominator bound — the numerator and even the
denominator may vary with the depth.  Strictly closer to the in-tree (D1) data shape
(`DescentWindowMatch`: fixed canonical `q0`, per-start numerators, fixed depth `spread+1`)
than `DeepDyadicTailMatch`'s "one `(q0, a)` for all depths simultaneously". -/
def DeepDyadicPerDepthMatch : Prop :=
  ∀ ctx : ActualFailureContext, 2 ^ 493443 < ctx.X → ShellValueDyadic ctx →
    ∃ x B : ℕ, x ≤ ctx.X ∧
      ∀ n : ℕ, ∃ q0 a : ℕ,
        (1 < q0 ∧ Odd q0 ∧ q0 ≤ B ∧ a < q0 ∧ 2 * orderOf (2 : ZMod q0) ≤ ctx.X)
          ∧ MatchesCompletion ctx.d (x + 1) n q0 a

/-- **The promotion fires at the ctx level**: the relaxed per-depth successor delivers the
full deep tail match (the depth-`(B+B+1)` witness centre is THE centre; all constraints
are inherited from it). -/
theorem deepDyadicTailMatch_of_perDepthMatch (h : DeepDyadicPerDepthMatch) :
    DeepDyadicTailMatch := by
  intro ctx hX hdy
  obtain ⟨x, B, hx, hex⟩ := h ctx hX hdy
  have huniq : ∀ (q0 a q0' a' : ℕ),
      (1 < q0 ∧ Odd q0 ∧ q0 ≤ B ∧ a < q0 ∧ 2 * orderOf (2 : ZMod q0) ≤ ctx.X) →
      (1 < q0' ∧ Odd q0' ∧ q0' ≤ B ∧ a' < q0' ∧ 2 * orderOf (2 : ZMod q0') ≤ ctx.X) →
      MatchesCompletion ctx.d (x + 1) (B + B + 1) q0 a →
      MatchesCompletion ctx.d (x + 1) (B + B + 1) q0' a' →
      ∀ i, dyadicDigit q0 a i = dyadicDigit q0' a' i := by
    rintro q0 a q0' a' ⟨hq0, _, hqB, ha, _⟩ ⟨hq0', _, hqB', ha', _⟩ hm hm' i
    have hsep : 2 * q0 * q0' ≤ 2 ^ (B + B + 1) := two_mul_mul_le_two_pow hqB hqB'
    have hval : (a : ℝ) / (q0 : ℝ) = (a' : ℝ) / (q0' : ℝ) :=
      descentCentre_unique_of_matches (by omega) (by omega) ha ha' hsep hm hm'
    exact dyadicDigit_congr (by omega) (by omega)
      (centre_cross_of_div_eq (by omega) (by omega) hval) i
  obtain ⟨q0, a, ⟨hq0, hodd, hqB, ha, hord⟩, hm⟩ :=
    tailMatch_of_perDepth_unique (B + B + 1)
      (P := fun q0 a =>
        1 < q0 ∧ Odd q0 ∧ q0 ≤ B ∧ a < q0 ∧ 2 * orderOf (2 : ZMod q0) ≤ ctx.X)
      hex huniq
  exact ⟨x, q0, a, hq0, hodd, hx, hord, hm⟩

/-- The relaxation costs nothing: the deep tail match conversely supplies the per-depth
successor (constant witnesses, numerator normalized to a genuine residue). -/
theorem perDepthMatch_of_deepDyadicTailMatch (h : DeepDyadicTailMatch) :
    DeepDyadicPerDepthMatch := by
  intro ctx hX hdy
  obtain ⟨x, q0, a, hq0, hodd, hx, hord, hm⟩ := h ctx hX hdy
  exact ⟨x, q0, hx, fun n =>
    ⟨q0, a % q0, ⟨hq0, hodd, le_refl q0, Nat.mod_lt _ (by omega), hord⟩,
      matchesCompletion_of_tailMatch (tailMatch_normalize hm) n⟩⟩

/-- The sharpened successor is exactly as strong as the deep tail match. -/
theorem deepDyadicPerDepthMatch_iff : DeepDyadicPerDepthMatch ↔ DeepDyadicTailMatch :=
  ⟨deepDyadicTailMatch_of_perDepthMatch, perDepthMatch_of_deepDyadicTailMatch⟩

/-- **The endpoint through the relaxed successor**: `Erdos260Statement` from per-depth
bounded-denominator matches plus the lever-shrunk wave-5 surfaces. -/
theorem erdos260_of_dyadicPerDepthMatch (h : DeepDyadicPerDepthMatch)
    (surfaces : DyadicValueLever → Erdos260DyadicLeverResidual) : Erdos260Statement :=
  erdos260_of_dyadicTailMatch (deepDyadicTailMatch_of_perDepthMatch h) surfaces

/-- **The no-free-lunch core** (the honest refutation of "self-match is free at pinned
contexts"): at a dyadic-value context NO window-compatible tail match exists at all — so
any unconditional tail-match supplier at pinned contexts would have to void them outright.
(The pinned value is the WEIGHTED `∑ n·d_n/2^n`, not the plain binary value whose
expansion `TailMatch` demands; and the wave-7/8 voiding closes the door formally.) -/
theorem shellValueDyadic_tailMatch_void (ctx : ActualFailureContext)
    (hdy : ShellValueDyadic ctx) {x q0 a : ℕ}
    (hq0 : 1 < q0) (hodd : Odd q0) (hx : x ≤ ctx.X)
    (hord : 2 * orderOf (2 : ZMod q0) ≤ ctx.X)
    (hm : TailMatch ctx.d x q0 a) : False :=
  shellValueDyadic_void_of_windowPeriodic ctx
    (windowPeriodic_of_tailMatch ctx hq0 hodd hx hord hm) hdy

/-- **NO FREE LUNCH, dyadic family**: the frontier prop `DeepDyadicTailMatch` is logically
EQUIVALENT to the full dyadic-value lever it was meant to supply.  (Forward: the in-tree
wave-8 bridge.  Backward: the lever EMPTIES the hypothesis class, so the supply is
vacuous.)  Supplying the tail match at pinned contexts IS the voiding — there is no
intermediate waypoint. -/
theorem deepDyadicTailMatch_iff_lever : DeepDyadicTailMatch ↔ DyadicValueLever :=
  ⟨dyadicValueLever_of_tailMatch, fun hlever ctx _ hdy => absurd hdy (hlever ctx)⟩

/-- The tail-match prop is also equivalent to the wave-7 periodicity prop it refines: at
dyadic contexts, "tail match" and "window periodic" have identical strength (both equal
the voiding). -/
theorem deepDyadicTailMatch_iff_windowPeriodicity :
    DeepDyadicTailMatch ↔ DeepDyadicWindowPeriodicity :=
  ⟨deepDyadicWindowPeriodicity_of_tailMatch,
   fun hwp ctx _ hdy => absurd hdy (dyadicValueLever_of_windowPeriodicity hwp ctx)⟩

/-- No free lunch, fifth family (`(15,1)`: value `1/(5·2^t)`). -/
theorem deepFifthTailMatch_iff_lever : DeepFifthTailMatch ↔ TowerFifthValueLever := by
  constructor
  · exact towerFifthValueLever_of_tailMatch
  · intro hlever ctx _ hval
    obtain ⟨t, ht⟩ := hval
    exact absurd ht (hlever ctx t)

/-- No free lunch, thirds family (`(15,2)`: value `2/(3·2^t)`). -/
theorem deepThirdsTailMatch_iff_lever : DeepThirdsTailMatch ↔ TowerThirdsValueLever := by
  constructor
  · exact towerThirdsValueLever_of_tailMatch
  · intro hlever ctx _ hval
    obtain ⟨t, ht⟩ := hval
    exact absurd ht (hlever ctx t)

/-- No free lunch, the five fixed families (`(3,1)`, `(21,3)`, `(15,1)`, `(15,2)`,
`(105,7)`): the family tail-match prop IS the family voiding. -/
theorem deepFixedFamilyTailMatch_iff_void :
    DeepFixedFamilyTailMatch ↔ ∀ ctx : ActualFailureContext, ¬ FixedFamilyHit ctx :=
  ⟨fixedFamilyHit_void_of_tailMatch,
   fun hvoid ctx _ hhit => absurd hhit (hvoid ctx)⟩

/-! ## Part 6.  Machine-readable status (honest) -/

/-- Honest machine-readable status of the tail-match supply module. -/
def tailMatchSupplyStatus : List String :=
  [ "SUPPLY-CHAIN MAP (goal 1) - the tree's MatchesCompletion d s n q0 a " ++
      "(DescentDepthAgreementCore) is supplied ONLY through DescentWindowMatch.hmatch " ++
      "(equivalently ofPeriodic's hper+hbase), itself discharged into the s25.1 " ++
      "certificate as (D1) singularSquareBound_of_matches + (D2) NoLargeRun carry " ++
      "routing (DescentDepthClosureCore); the witness centre there is the FIXED " ++
      "canonical (canonicalCenter ctx).q0 with per-start numerators a k, and the depth " ++
      "is the FIXED proofV4DensePackSpread+1 - there is NO depth parameter in-tree, so " ++
      "no in-tree object yet supplies matches at unboundedly many depths.  The witness " ++
      "centre does not vary with a depth because no in-tree statement quantifies one.",
    "PROMOTION (goal 2, PROVED) - tailMatch_of_perDepth_unique: per-depth existence of " ++
      "a matching centre + depth-N0 uniqueness of the completion word promote to ONE " ++
      "centre matching at ALL depths (the eventually-constant-centre chain: the " ++
      "depth-(N0+i+1) witness restricts to depth N0, separation identifies its " ++
      "completion with the depth-N0 witness's, transporting digit i).  Concrete forms: " ++
      "tailMatch_of_perDepth_bounded (denominators <= B; separation depth B+B+1, where " ++
      "2*q0*q0' <= 2^(B+B+1) via descentCentre_unique_of_matches + the new " ++
      "dyadicDigit_congr: equal centres have IDENTICAL completion words, by pure " ++
      "division-algorithm arithmetic dyadicResidue_cross) and " ++
      "tailMatch_of_perDepth_fixedDenominator (the DescentWindowMatch shape: fixed q0, " ++
      "per-depth numerators).  Exact characterization: tailMatch_iff_perDepth_bounded - " ++
      "TailMatch at some centre IFF the per-depth matches admit a UNIFORM denominator " ++
      "bound.",
    "FREE SUPPLY (goal 2, PROVED, unconditional) - matchesCompletion_exists_perDepth: " ++
      "EVERY binary word matches a small-odd-denominator completion to EVERY depth n, " ++
      "with q0 = 2^(n+2)-1 (the window padded by two zeros, repeated; digit extraction " ++
      "dyadicDigit_windowCylinderValue via the shift recurrence 2*V_j = V_{j+1} + " ++
      "(2^m-1)*w_j and remainder uniqueness).  So per-depth EXISTENCE costs nothing; " ++
      "the frontier's entire content is the uniform denominator BOUND (the manuscript " ++
      "q <= Qp denominator drop) - exactly what the iterated 25.1/25.3 descent must " ++
      "deliver and what no in-tree object yet delivers.",
    "SELF-MATCH VERDICT (goal 2, the honest refutation) - the hoped-for free TailMatch " ++
      "at pinned contexts FAILS, for an identified reason: ctx.hrational pins the " ++
      "WEIGHTED value realWeightedValue = sum n*d_n/2^n = P/Q, while TailMatch demands " ++
      "the tail equal the PLAIN binary expansion dyadicDigit q0 a of a/q0; the " ++
      "functionals differ, so the word is NOT (definitionally or otherwise) the " ++
      "expansion of its own pinned value.  Decisively, the tree itself PROVES no " ++
      "window-compatible tail match can exist at pinned contexts " ++
      "(pinnedValue_tailMatch_void; restated here as shellValueDyadic_tailMatch_void): " ++
      "a free self-match supplier would already BE the voiding.  Formalized as the " ++
      "no-free-lunch equivalences: deepDyadicTailMatch_iff_lever (DeepDyadicTailMatch " ++
      "<-> DyadicValueLever), deepDyadicTailMatch_iff_windowPeriodicity, " ++
      "deepFifthTailMatch_iff_lever, deepThirdsTailMatch_iff_lever, " ++
      "deepFixedFamilyTailMatch_iff_void - each conditional tail-match prop is " ++
      "logically EQUIVALENT to the voiding it was meant to supply (forward: the wave-8 " ++
      "bridges; backward: the lever empties the hypothesis class).  There is no " ++
      "intermediate waypoint; goal 3's unconditional voidings are therefore NOT " ++
      "deliverable by this route, honestly reported.",
    "EXACT REACH (PROVED) - tailMatch_iff_eventuallyPeriodic: a binary word admits a " ++
      "small-odd-denominator tail match at onset x IFF it is eventually periodic past " ++
      "x AND has a zero past x.  Forward: dyadicDigit_period + dyadicDigit_exists_zero " ++
      "(all-ones tails are impossible for genuine residues: 2^k + r <= q0 diverges).  " ++
      "Backward: tailMatch_of_eventuallyPeriodic with q0 = 2^p - 1 and ord_{q0}(2) <= " ++
      "p, so the WindowPeriodic budget 2p <= X transports to the tail-match budget " ++
      "2*ord <= X - the two strata are the same stratum.",
    "SHARPENED SUCCESSOR (goal 3 partial delivery) - DeepDyadicPerDepthMatch: per-depth " ++
      "matches at one onset with a uniform denominator bound, numerator AND denominator " ++
      "free to vary with depth - strictly closer to the in-tree (D1) data shape than " ++
      "DeepDyadicTailMatch's one-(q0,a)-for-all-depths.  " ++
      "deepDyadicTailMatch_of_perDepthMatch promotes it (the promotion firing at ctx " ++
      "level), erdos260_of_dyadicPerDepthMatch is the endpoint, and " ++
      "deepDyadicPerDepthMatch_iff certifies the relaxation hides no strength.  The " ++
      "precise residual gap to close it from the in-tree side: extend " ++
      "DescentWindowMatch's fixed-depth (spread+1) canonical-centre match to all " ++
      "depths n at the same start - boundedness is then automatic (the canonical q0 is " ++
      "fixed), and tailMatch_of_perDepth_fixedDenominator finishes.",
    "WHAT RESISTS - the uniform denominator bound itself.  Unbounded per-depth matches " ++
      "are free (this module); bounded per-depth matches are EQUIVALENT to TailMatch " ++
      "(this module); TailMatch at pinned contexts is EQUIVALENT to the voiding " ++
      "(this module); and the in-tree (D1)/(D2) machinery supplies only a fixed-depth " ++
      "match conditional on DescentWindowMatch.hmatch.  The manuscript's iterated " ++
      "25.1/25.3 descent - producing matches at depth ~p/2 for EVERY period scale p " ++
      "with denominator <= Qp - remains the irreducible analytic input; its formal " ++
      "target is now the sharpest available: DeepDyadicPerDepthMatch (one onset, " ++
      "bounded denominators, free numerators).",
    "HYGIENE - additive only (no existing file edited); no sorry / admit / new axiom / " ++
      "native_decide; all #print axioms in [propext, Classical.choice, Quot.sound]." ]

theorem tailMatchSupplyStatus_nonempty : tailMatchSupplyStatus ≠ [] := by
  simp [tailMatchSupplyStatus]

/-! ## Part 7.  Axiom-cleanliness audit
Every key declaration; expected axioms `[propext, Classical.choice, Quot.sound]` or fewer. -/

#print axioms divByMulAdd_eq
#print axioms modByMulAdd_eq
#print axioms centre_cross_of_div_eq
#print axioms dyadicResidue_cross
#print axioms dyadicDigit_congr
#print axioms dyadicResidue_mod_left
#print axioms dyadicDigit_mod_left
#print axioms tailMatch_normalize
#print axioms two_mul_mul_le_two_pow
#print axioms tailMatch_centre_unique
#print axioms tailMatch_digit_unique
#print axioms tailMatch_numerator_unique
#print axioms matchesCompletion_mono
#print axioms tailMatch_of_perDepth_unique
#print axioms tailMatch_of_perDepth_bounded
#print axioms tailMatch_of_perDepth_fixedDenominator
#print axioms tailMatch_iff_perDepth_bounded
#print axioms sum_range_two_pow_reflect
#print axioms windowValue_step_of_periodic
#print axioms windowValue_lt_of_zero
#print axioms exists_shift_mod
#print axioms dyadicDigit_windowCylinderValue
#print axioms paddedPeriodicWord_le_one
#print axioms paddedPeriodicWord_periodic
#print axioms paddedPeriodicWord_window_zero
#print axioms paddedPeriodicWord_eq_of_lt
#print axioms matchesCompletion_exists_perDepth
#print axioms matchesCompletion_exists_perDepth_ctx
#print axioms dyadicDigit_exists_zero
#print axioms tailMatch_of_eventuallyPeriodic
#print axioms tailMatch_iff_eventuallyPeriodic
#print axioms deepDyadicTailMatch_of_perDepthMatch
#print axioms perDepthMatch_of_deepDyadicTailMatch
#print axioms deepDyadicPerDepthMatch_iff
#print axioms erdos260_of_dyadicPerDepthMatch
#print axioms shellValueDyadic_tailMatch_void
#print axioms deepDyadicTailMatch_iff_lever
#print axioms deepDyadicTailMatch_iff_windowPeriodicity
#print axioms deepFifthTailMatch_iff_lever
#print axioms deepThirdsTailMatch_iff_lever
#print axioms deepFixedFamilyTailMatch_iff_void
#print axioms tailMatchSupplyStatus_nonempty

end

end Erdos260
