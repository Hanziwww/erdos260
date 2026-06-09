import Erdos260.SemiperiodicMatchEnrichCore

/-!
# §25.1/25.2 carry-cylinder reduction: deriving `Section251CylinderMatchResidual`

`SemiperiodicMatchEnrichCore.lean` (wave-18) reduced the entire §25.1 *match* to one isolated residual,
`Section251CylinderMatchResidual ctx` (`NoLargeRun ctx → Nonempty (DescentCylinderMatchData ctx)`): the
actual shell digits in each descent window `[k+r, k+r+spread]` must spell the depth-`(spread+1)` dyadic
cylinder index of the phase-shifted residual centre `a_k/q₀`.

This file (NEW; it edits no existing file) attacks that residual through the genuine §25.1/25.2
carry/cylinder geometry, **building on the proved dichotomy `Residual.residual_cylinder_dichotomy`**.

## The carry-cylinder reduction (genuinely PROVED here, no `sorry`/`axiom`/`admit`/`native_decide`)

The §25.1 carry relation `M·Qp − ν·D = R` is, for a descent window, the integer relation between
the **actual window value** `M = windowCylinderValue d s n` (the `n`-bit integer of the shell digits,
`D = 2ⁿ`) and the **residual centre** `ν/Qp = a/q₀` (`Qp = q₀`).  The singular-square bound is
`|R|·2ⁿ < D·Qp`, i.e. `|M/D − a/q₀| < 2⁻ⁿ`.

* `cylinder_succ_excluded_of_singularSquare` — **the bound alone excludes the *upper* adjacency**
  `kν = kM + 1`.  Because the window point `M/D = kM/2ⁿ` is *exactly* dyadic (the left endpoint of its
  own cylinder), `2⁻ⁿ`-closeness forces `a/q₀ < (kM+1)/2ⁿ`, so the centre cannot sit one cylinder to
  the right.  This is a genuine sharpening of the generic dichotomy, proved from
  `Residual.residual_fractional_approx`.
* `dyadicCylinder_center_of_singularSquare` — **THE REDUCTION, CLOSED.**  Feeding the carry relation and
  the singular-square bound to `residual_cylinder_dichotomy` gives the equal-or-adjacent trichotomy;
  the upper adjacency is excluded by the bound (above), and the *carry* adjacency `kM = kν + 1` is
  excluded by the routed `NoLargeRun` hypothesis `hcarry`; what remains is the **equal-cylinder** branch
  `kM = kν`, which is exactly `DyadicCylinder n (windowCylinderValue d s n) (a/q₀)`.
* `section251CylinderMatchResidual_of_certificate` — **`Section251CylinderMatchResidual` DERIVED** from a
  `SingularSquareCertificate ctx`: per-window singular-square bound + the `NoLargeRun`-routed carry
  exclusion + the (flagged) §24 floor + the bounded-period calibration.  Wiring the reduction through
  `descentCylinderMatchData_canonical` (the canonical residual centre `a_k/q₀` of the actual shell)
  builds `DescentCylinderMatchData ctx`; `NoLargeRun` is *genuinely consumed* through `hcarry`.
* `matchedDescentWindows_of_singularSquareCertificate` — the capstone: composing with the wave-18
  `matchedDescentWindows_of_section251` closes the entire §25.1 match from the certificate.
* `windowCylinderValue_dyadicDigit_self` / `singularSquare_reduction_fires_orbit` — **non-vacuity**: for
  any genuine small-odd-denominator centre `a/q₀` (`a < q₀`, `q₀` odd, e.g. the `1/3` orbit), the window
  value of its *own* dyadic-digit word equals its cylinder index, so the singular-square bound and the
  carry exclusion both hold and the reduction fires.  No constant/all-zero shortcut.

## The sharp surviving Diophantine residual (audit verdict)

`Section251CylinderMatchResidual ctx` is **NOT** unconditionally derived; it is reduced to the
`SingularSquareCertificate`, whose two genuine fields are the irreducible core:

* **(D1) the singular-square bound `hbound`** for the *actual* shell windows: `|R|·2ⁿ < D·Qp`, i.e. the
  shell digits over `[k+r, k+r+spread]` approximate `a_k/q₀` to within `2⁻⁽ˢᵖʳᵉᵃᵈ⁺¹⁾`.  This is the
  genuine Diophantine heart: a depth-`n` cylinder has width `2⁻ⁿ` while fractions of denominator `q₀`
  are spaced `1/q₀`, so for `q₀ < 2ⁿ` a *generic* window cylinder contains **no** fraction `a/q₀` — the
  failing shell forces this singular approximation (the `DirtyCrossing`/`CoareaOldNew` old/new
  singular-square content).  It is **not reachable** from the cylinder geometry alone.
* **(D2) the carry-run routing `hcarry`** (`NoLargeRun ctx → ¬ carry-adjacency`): the manuscript's
  L.4.1/25.2 statement that a carry (the centre sitting in the *previous* cylinder `kM − 1`, a maximal
  boundary run `ξ1̄0⋯0`) is a class-`1` large run, so `NoLargeRun` excludes it.  Connecting the binary
  carry structure to the hit-gap window-excess classifier `runClsOfShell` is the genuine combinatorial
  companion, kept as the routed input.

Everything strictly between (D1)+(D2) and `MatchedDescentWindows ctx` — the dichotomy routing, the
equal-cylinder identification, the upper-adjacency exclusion, the centre packaging — is proved here.
The §24 density floor and the bounded-period calibration are the separately-flagged calibration inputs.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## Part A — A finite binary reconstruction identity -/

/-- **Binary reconstruction.**  A natural number `K < 2ⁿ` is the sum of its first `n` binary digits:
`∑_{i<n} (K / 2ⁱ % 2)·2ⁱ = K`.  Proved by peeling the least-significant bit
(`K = 2·(K/2) + K%2`). -/
theorem sumBits_div_two_pow : ∀ (n K : ℕ), K < 2 ^ n →
    ∑ i ∈ Finset.range n, (K / 2 ^ i % 2) * 2 ^ i = K := by
  intro n
  induction n with
  | zero =>
    intro K hK
    simp only [pow_zero, Nat.lt_one_iff] at hK
    subst hK
    simp
  | succ n ih =>
    intro K hK
    rw [Finset.sum_range_succ']
    have hK2 : K / 2 < 2 ^ n := by
      rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)]
      calc K < 2 ^ (n + 1) := hK
        _ = 2 ^ n * 2 := by rw [pow_succ]
    have step : (∑ i ∈ Finset.range n, (K / 2 ^ (i + 1) % 2) * 2 ^ (i + 1))
        = 2 * ∑ i ∈ Finset.range n, (K / 2 / 2 ^ i % 2) * 2 ^ i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have e1 : K / 2 ^ (i + 1) = K / 2 / 2 ^ i := by
        rw [pow_succ', Nat.div_div_eq_div_mul]
      rw [e1, pow_succ]
      ring
    rw [step, ih (K / 2) hK2]
    simp only [pow_zero, Nat.div_one, mul_one]
    omega

/-! ## Part B — The carry-cylinder reduction (built on `residual_cylinder_dichotomy`) -/

/--
**The singular-square bound excludes the upper adjacency.**

For the §25.1 carry relation of a descent window — actual value `M = windowCylinderValue d s n`,
dyadic denominator `D = 2ⁿ`, residual centre `a/q₀` — the singular-square bound `|R|·2ⁿ < D·q₀` forces
the centre's depth-`n` cylinder index `kν = cylinderIndex n (a/q₀)` to satisfy `kν ≠ kM + 1`.

The window point `M/D = kM/2ⁿ` is *exactly* the left endpoint of its own cylinder, so
`2⁻ⁿ`-closeness pins `a/q₀ < (kM+1)/2ⁿ`, ruling out the next cylinder to the right.  This is a genuine
sharpening of `residual_cylinder_dichotomy`, using `residual_fractional_approx`.
-/
theorem cylinder_succ_excluded_of_singularSquare
    {d : ℕ → ℕ} {s n q0 a : ℕ} (hq0 : 0 < q0)
    (hbound : |(windowCylinderValue d s n : ℝ) * (q0 : ℝ) - (a : ℝ) * (2 : ℝ) ^ n|
        * 2 ^ n < (2 : ℝ) ^ n * (q0 : ℝ)) :
    cylinderIndex n ((a : ℝ) / (q0 : ℝ)) ≠ windowCylinderValue d s n + 1 := by
  intro hkν1
  have hD : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hQp : (0 : ℝ) < (q0 : ℝ) := by exact_mod_cast hq0
  have happrox := residual_fractional_approx
    (M := (windowCylinderValue d s n : ℝ)) (Qp := (q0 : ℝ)) (D := (2 : ℝ) ^ n)
    (ν := (a : ℝ))
    (R := (windowCylinderValue d s n : ℝ) * (q0 : ℝ) - (a : ℝ) * (2 : ℝ) ^ n)
    (n := n) hD hQp rfl hbound
  have hcylν : DyadicCylinder n (cylinderIndex n ((a : ℝ) / (q0 : ℝ)))
      ((a : ℝ) / (q0 : ℝ)) :=
    dyadicCylinder_cylinderIndex (by positivity)
  rw [abs_sub_lt_iff] at happrox
  have hlow := hcylν.1
  rw [hkν1] at hlow
  push_cast at hlow
  rw [add_div] at hlow
  linarith [happrox.2]

/--
**THE CARRY-CYLINDER REDUCTION, CLOSED.**

The §25.1 equal-cylinder branch from the singular-square bound and the routed carry exclusion.

Given the singular-square bound `|R|·2ⁿ < D·q₀` (`hbound`) and the carry exclusion
`windowCylinderValue d s n ≠ kν + 1` (`hcarry`, the `NoLargeRun`-routed boundary-run exclusion), the
actual window value's depth-`n` dyadic cylinder *contains* the residual centre `a/q₀`:
`DyadicCylinder n (windowCylinderValue d s n) (a/q₀)`.

Proof: `residual_cylinder_dichotomy` gives `kM = kν ∨ kν = kM+1 ∨ kM = kν+1`; the second is excluded by
`cylinder_succ_excluded_of_singularSquare` (the bound), the third by `hcarry`; the first *is* the
conclusion (the window value indexes the centre's cylinder).
-/
theorem dyadicCylinder_center_of_singularSquare
    {d : ℕ → ℕ} {s n q0 a : ℕ} (hq0 : 0 < q0)
    (hbound : |(windowCylinderValue d s n : ℝ) * (q0 : ℝ) - (a : ℝ) * (2 : ℝ) ^ n|
        * 2 ^ n < (2 : ℝ) ^ n * (q0 : ℝ))
    (hcarry : windowCylinderValue d s n ≠ cylinderIndex n ((a : ℝ) / (q0 : ℝ)) + 1) :
    DyadicCylinder n (windowCylinderValue d s n) ((a : ℝ) / (q0 : ℝ)) := by
  have hD : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hQp : (0 : ℝ) < (q0 : ℝ) := by exact_mod_cast hq0
  have hcylM : DyadicCylinder n (windowCylinderValue d s n)
      ((windowCylinderValue d s n : ℝ) / (2 : ℝ) ^ n) :=
    dyadicCylinder_windowMaskPoint d s n
  have hcylν : DyadicCylinder n (cylinderIndex n ((a : ℝ) / (q0 : ℝ)))
      ((a : ℝ) / (q0 : ℝ)) :=
    dyadicCylinder_cylinderIndex (by positivity)
  have hdich := residual_cylinder_dichotomy
    (M := (windowCylinderValue d s n : ℝ)) (Qp := (q0 : ℝ)) (D := (2 : ℝ) ^ n)
    (ν := (a : ℝ))
    (R := (windowCylinderValue d s n : ℝ) * (q0 : ℝ) - (a : ℝ) * (2 : ℝ) ^ n)
    (n0 := n) hD hQp rfl hbound hcylM hcylν
  rcases hdich with heq | hkν1 | hkM1
  · rw [heq]; exact hcylν
  · exact absurd hkν1 (cylinder_succ_excluded_of_singularSquare hq0 hbound)
  · exact absurd hkM1 hcarry

/-! ## Part C — The §25.1 singular-square certificate and the derivation -/

/--
**The §25.1 singular-square certificate — the isolated Diophantine residual.**

For the actual failure context `ctx`, with depth `n = spread + 1`, window start `k + r`, and the
canonical residual centre `a_k/q₀` (`q₀ = (canonicalCenter ctx).q0`), the data packages, for each
genuine DensePack start `k`:

* **(D1)** the singular-square bound `hbound`: `|R|·2ⁿ < D·q₀` for the actual shell window;
* **(D2)** the carry-run routing `hcarry`: `NoLargeRun ctx` excludes the carry adjacency
  `windowValue = kν + 1` (the boundary-run / class-`1` exclusion);

together with the (flagged) §24 period-density floor `hdens` and the bounded-period calibration `hpb`
consumed verbatim by `descentCylinderMatchData_canonical`.
-/
structure SingularSquareCertificate (ctx : ActualFailureContext) where
  /-- The per-start residual-centre numerator (the `2^{φ_k}`-shifted centre). -/
  a : ℕ → ℕ
  /-- **(D1)** the singular-square residual bound `|R|·2ⁿ < D·q₀` for each genuine descent window. -/
  hbound : ∀ k ∈ genuineDensePackStarts ctx,
    |(windowCylinderValue ctx.shell.d (k + ctx.n24CarryData.r)
          (proofV4DensePackSpread ctx.shell + 1) : ℝ) * ((canonicalCenter ctx).q0 : ℝ)
        - (a k : ℝ) * (2 : ℝ) ^ (proofV4DensePackSpread ctx.shell + 1)|
      * 2 ^ (proofV4DensePackSpread ctx.shell + 1)
    < (2 : ℝ) ^ (proofV4DensePackSpread ctx.shell + 1) * ((canonicalCenter ctx).q0 : ℝ)
  /-- **(D2)** the carry-run routing: `NoLargeRun` excludes the carry adjacency for each genuine start. -/
  hcarry : NoLargeRun ctx → ∀ k ∈ genuineDensePackStarts ctx,
    windowCylinderValue ctx.shell.d (k + ctx.n24CarryData.r)
        (proofV4DensePackSpread ctx.shell + 1)
      ≠ cylinderIndex (proofV4DensePackSpread ctx.shell + 1)
          ((a k : ℝ) / ((canonicalCenter ctx).q0 : ℝ)) + 1
  /-- The §24 period-density floor on the orbit word (separately flagged calibration). -/
  hdens : ∀ k ∈ genuineDensePackStarts ctx,
    manuscriptRhoD * (orderOf (2 : ZMod (canonicalCenter ctx).q0) : ℝ)
      ≤ (windowWeight (dyadicDigit (canonicalCenter ctx).q0 (a k)) 0
          (orderOf (2 : ZMod (canonicalCenter ctx).q0)) : ℝ)
  /-- The bounded-period calibration. -/
  hpb : Classical.choose ctx.shell.hXdyadic + orderOf (2 : ZMod (canonicalCenter ctx).q0)
      ≤ proofV4DensePackSpread ctx.shell + 2

/--
**`Section251CylinderMatchResidual` DERIVED from the singular-square certificate.**

Under `NoLargeRun ctx`, the certificate's per-window singular-square bound (D1) and the routed carry
exclusion (D2) feed the carry-cylinder reduction `dyadicCylinder_center_of_singularSquare` to identify
each actual descent-window value with the residual centre's depth-`(spread+1)` cylinder; packaged by
`descentCylinderMatchData_canonical` (with the flagged floor and calibration) this is the
`DescentCylinderMatchData ctx` demanded by `Section251CylinderMatchResidual ctx`.  `NoLargeRun` is
consumed exactly through (D2).
-/
theorem section251CylinderMatchResidual_of_certificate (ctx : ActualFailureContext)
    (cert : SingularSquareCertificate ctx) :
    Section251CylinderMatchResidual ctx := by
  intro hnlr
  refine ⟨descentCylinderMatchData_canonical ctx cert.a (fun k hk => ?_) cert.hdens cert.hpb⟩
  exact dyadicCylinder_center_of_singularSquare (canonicalCenter ctx).q0_pos
    (cert.hbound k hk) (cert.hcarry hnlr k hk)

/--
**Capstone: the §25.1 match from the singular-square certificate.**

Composing the derived `Section251CylinderMatchResidual` with the wave-18 reduction
`matchedDescentWindows_of_section251` closes the whole §25.1 match `MatchedDescentWindows ctx` from the
certificate together with `NoLargeRun ctx`.
-/
theorem matchedDescentWindows_of_singularSquareCertificate (ctx : ActualFailureContext)
    (hnlr : NoLargeRun ctx) (cert : SingularSquareCertificate ctx) :
    MatchedDescentWindows ctx :=
  matchedDescentWindows_of_section251 ctx hnlr
    (section251CylinderMatchResidual_of_certificate ctx cert)

/-! ## Part D — Non-vacuity: the reduction fires on genuine orbit windows -/

/--
**The window value of an orbit word IS its cylinder index.**

For a small-odd-denominator centre `a/q₀` with `a < q₀`, the depth-`n` window value of the *own*
dyadic-digit word `dyadicDigit q₀ a` (started at `0`) equals the centre's depth-`n` cylinder index:
`windowCylinderValue (dyadicDigit q₀ a) 0 n = cylinderIndex n (a/q₀)`.  This realises the
equal-cylinder hypothesis of the reduction *exactly*, with no constant/zero shortcut.
-/
theorem windowCylinderValue_dyadicDigit_self {q0 a : ℕ} (hq0 : 0 < q0) (ha : a < q0) (n : ℕ) :
    windowCylinderValue (dyadicDigit q0 a) 0 n = cylinderIndex n ((a : ℝ) / (q0 : ℝ)) := by
  set K := cylinderIndex n ((a : ℝ) / (q0 : ℝ)) with hKdef
  have hKval : K = (2 ^ n * a) / q0 := hKdef.trans (cylinderIndex_ratCast q0 a n)
  have hKlt : K < 2 ^ n := by
    rw [hKval, Nat.div_lt_iff_lt_mul hq0]
    exact mul_lt_mul_of_pos_left ha (by positivity)
  have hterm : ∀ i ∈ Finset.range n,
      dyadicDigit q0 a (0 + (n - 1 - i)) * 2 ^ i = (K / 2 ^ i % 2) * 2 ^ i := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [zero_add]
    congr 1
    rw [(binaryDigitWord_ratCast hq0 a (n - 1 - i)).symm,
      binaryDigitWord_eq_cylinderBit (by omega : n - 1 - i < n) hKdef.symm,
      show n - 1 - (n - 1 - i) = i from by omega]
  rw [windowCylinderValue_eq_reflect]
  exact (Finset.sum_congr rfl hterm).trans (sumBits_div_two_pow n K hKlt)

/--
**Non-vacuity: the carry-cylinder reduction fires on a genuine orbit window.**

For any small-odd-denominator centre `a/q₀` (`1 < q₀`, `a < q₀`, e.g. `a = 1, q₀ = 3`, the `1/3` run
obstruction), the depth-`n` window value of its own dyadic-digit word lands the centre in the actual
window's cylinder — `dyadicCylinder_center_of_singularSquare` applies, since the singular-square bound
reduces to `(2ⁿ·a mod q₀) < q₀` and the carry adjacency `kν ≠ kν + 1` is trivial.
-/
theorem singularSquare_reduction_fires_orbit {q0 a : ℕ} (hq0 : 1 < q0) (ha : a < q0) (n : ℕ) :
    DyadicCylinder n (windowCylinderValue (dyadicDigit q0 a) 0 n) ((a : ℝ) / (q0 : ℝ)) := by
  have hq0' : 0 < q0 := by omega
  refine dyadicCylinder_center_of_singularSquare hq0' ?_ ?_
  · rw [windowCylinderValue_dyadicDigit_self hq0' ha n, cylinderIndex_ratCast q0 a n]
    have hreal : ((((2 ^ n * a) / q0 : ℕ) : ℝ) * (q0 : ℝ) - (a : ℝ) * (2 : ℝ) ^ n)
        = -(((2 ^ n * a) % q0 : ℕ) : ℝ) := by
      have h := congrArg (fun t : ℕ => (t : ℝ)) (Nat.div_add_mod (2 ^ n * a) q0)
      push_cast at h
      linear_combination h
    rw [hreal, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (((2 ^ n * a) % q0 : ℕ) : ℝ)),
      mul_comm ((2 : ℝ) ^ n) ((q0 : ℝ))]
    exact mul_lt_mul_of_pos_right (by exact_mod_cast Nat.mod_lt (2 ^ n * a) hq0') (by positivity)
  · rw [windowCylinderValue_dyadicDigit_self hq0' ha n]
    omega

/-- Concrete `1/3`-orbit instance of the non-vacuity (the canonical run-obstruction centre). -/
theorem singularSquare_reduction_fires_oneThird (n : ℕ) :
    DyadicCylinder n (windowCylinderValue (dyadicDigit 3 1) 0 n) ((1 : ℝ) / 3) := by
  have h := singularSquare_reduction_fires_orbit (q0 := 3) (a := 1) (by norm_num) (by norm_num) n
  simpa using h

/-! ## Part E — Honest residual inventory -/

/-- The precise status of `Section251CylinderMatchResidual` after this module. -/
def dirtyCrossingCylinderCoreResiduals : List String :=
  [ "CLOSED (upper-adjacency exclusion) — cylinder_succ_excluded_of_singularSquare: the " ++
      "singular-square bound |R|·2ⁿ < D·q₀ alone excludes kν = kM+1, because the window point " ++
      "M/D = kM/2ⁿ is exactly dyadic; a genuine sharpening of residual_cylinder_dichotomy via " ++
      "residual_fractional_approx. Only the carry adjacency kM = kν+1 then needs NoLargeRun.",
    "CLOSED (THE REDUCTION) — dyadicCylinder_center_of_singularSquare: carry relation M·Qp−ν·D=R + " ++
      "singular-square bound fed to residual_cylinder_dichotomy give the equal-or-adjacent " ++
      "trichotomy; the bound kills the upper adjacency, the routed NoLargeRun hypothesis hcarry " ++
      "kills the carry adjacency, leaving the EQUAL-cylinder branch DyadicCylinder n " ++
      "(windowCylinderValue d s n) (a/q₀) — the §25.1 cylinder match.",
    "DERIVED (the headline) — section251CylinderMatchResidual_of_certificate: from a " ++
      "SingularSquareCertificate, Section251CylinderMatchResidual ctx follows through " ++
      "descentCylinderMatchData_canonical at the actual shell's canonical residual centre a_k/q₀; " ++
      "NoLargeRun is genuinely consumed via the certificate's carry-routing field. " ++
      "matchedDescentWindows_of_singularSquareCertificate composes with the wave-18 " ++
      "matchedDescentWindows_of_section251 to close the entire §25.1 match.",
    "RESIDUAL (D1, the irreducible Diophantine heart) — SingularSquareCertificate.hbound: the " ++
      "singular-square bound |R|·2ⁿ < D·q₀ for the ACTUAL shell windows, i.e. the shell digits over " ++
      "[k+r, k+r+spread] approximate a_k/q₀ to within 2^−(spread+1). A depth-n cylinder has width " ++
      "2^−n while denominator-q₀ fractions are spaced 1/q₀, so for q₀ < 2ⁿ a generic window cylinder " ++
      "contains NO fraction a/q₀; the failing shell forces this singular approximation (the " ++
      "DirtyCrossing/CoareaOldNew old/new singular-square content). NOT reachable from the cylinder " ++
      "geometry alone — the genuine combinatorial core.",
    "RESIDUAL (D2, the combinatorial companion) — SingularSquareCertificate.hcarry: NoLargeRun ctx → " ++
      "the carry adjacency windowValue = kν+1 is excluded. The manuscript L.4.1/25.2 statement that " ++
      "a carry (centre in the previous cylinder kM−1, a maximal boundary run ξ1̄0⋯0) is a class-1 " ++
      "large run, so runClsOfShell ≠ 1 excludes it; linking the binary carry to the hit-gap " ++
      "window-excess classifier is the routed combinatorial input.",
    "CALIBRATION (flagged, not blocking) — SingularSquareCertificate.hdens / hpb are the §24 " ++
      "period-density floor (the 1/(4Q) ρ_D calibration) and the bounded-period calibration, " ++
      "consumed verbatim by descentCylinderMatchData_canonical; the construction is parametric in " ++
      "manuscriptRhoD and stays correct under either calibration.",
    "NON-DEGENERATE — windowCylinderValue_dyadicDigit_self / singularSquare_reduction_fires_orbit / " ++
      "_oneThird: the window value of an orbit word a/q₀ (a < q₀) IS its cylinder index, so the " ++
      "reduction fires on the genuine 1/3 run obstruction and every small-odd-denominator centre; " ++
      "no constant/all-zero shortcut.",
    "WAVE-20 (D1 IS the equal-or-carry cylinder containment; the D1 RESIDUAL above SOFTENED) — " ++
      "SingularSquareBoundCore.singularSquareBound_iff_cylinder: the bound |R|·2ⁿ < D·q₀ holds IFF " ++
      "kν = M ∨ (kν+1 = M ∧ q₀ ∤ 2ⁿ·a), so (D1) is EXACTLY the equal-or-carry-adjacent containment of " ++
      "the centre a/q₀ — NOT a second analytic input beyond the §25.1 cylinder match (it subsumes the " ++
      "upper-adjacency exclusion above). The 'D1 ... NOT reachable from the cylinder geometry' framing " ++
      "is thereby softened: D1 IS the cylinder geometry. The genuine obstruction is made exact — a " ++
      "centre exists IFF the residue (M·q₀) mod 2ⁿ lies in [0,q₀) ∪ (2ⁿ−q₀, 2ⁿ) " ++
      "(exists_singularSquareBound_iff), and the forbidden middle band (nonempty for 2q₀ ≤ 2ⁿ) is " ++
      "singular-square-free (not_singularSquareBound_of_residue_band). The lone irreducible step is the " ++
      "window-selection (descent-depth) agreement ‖η − η_{x,w}‖ < 2^(−depth), whose rational-separation " ++
      "kernel is SingularSquareBoundCore.singularSquare_center_unique.",
    "CALIBRATION RE-FLAG (wave-20, NOT fixed) — the §24 period-density floor hdens / bounded-period " ++
      "calibration hpb (the 1/(4Q) ρ_D Q-calibration) remain SEPARATELY FLAGGED upstream inputs, " ++
      "consumed verbatim and untouched by the wave-20 cylinder/existence sharpening; the construction " ++
      "stays parametric in manuscriptRhoD. Re-flagged here, not resolved." ]

theorem dirtyCrossingCylinderCoreResiduals_nonempty :
    dirtyCrossingCylinderCoreResiduals ≠ [] := by
  simp [dirtyCrossingCylinderCoreResiduals]

/-! ## Part F — Axiom-cleanliness audit -/

#print axioms sumBits_div_two_pow
#print axioms cylinder_succ_excluded_of_singularSquare
#print axioms dyadicCylinder_center_of_singularSquare
#print axioms section251CylinderMatchResidual_of_certificate
#print axioms matchedDescentWindows_of_singularSquareCertificate
#print axioms windowCylinderValue_dyadicDigit_self
#print axioms singularSquare_reduction_fires_orbit
#print axioms singularSquare_reduction_fires_oneThird

end

end Erdos260
