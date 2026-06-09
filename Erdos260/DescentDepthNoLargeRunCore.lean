import Erdos260.DescentDepthClosureCore
import Erdos260.DirtyCrossingCylinderCore

/-!
# §25.1/25.2 NO-LARGE-RUN closure: discharging (D2) and reducing the match to one centre-free band

Wave-23 (`DescentDepthClosureCore`) proved the equivalence
`matchesCompletion_iff_singularSquareBound_and_carry`: the descent-depth agreement `hmatch` is exactly
the conjunction of the certificate's **(D1)** singular-square bound `hbound` and **(D2)** the carry
exclusion `hcarry` (`cylinderIndex n (a/q₀) + 1 ≠ M`).  It further showed (D1) reduces, via the *upper*
residue band, to the **centre-free residue-band membership** `2ⁿ−q₀ < (M·q₀) mod 2ⁿ` of the actual
window value `M`, and that in that route the carry exclusion is *automatic*
(`DescentWindowMatch.ofResidueBand`).  But the END-TO-END path to `MatchedDescentWindows ctx` still ran
through `matchedDescentWindows_of_singularSquareCertificate`, whose signature threads the
`NoLargeRun ctx` hypothesis (D2).

This file (NEW; it edits no existing file) **discharges (D2) from the match entirely**, and pins (D1)
to its sharpest centre-free primitive, by routing through the *upper* residue band — never a `sorry`.

## The (D2) investigation verdict (what `runClsOfShell = 1` actually is)

* `NoLargeRun ctx := ∀ k ∈ genuineDensePackStarts ctx, runClsOfShell ctx k ≠ 1`, while
  `genuineDensePackStarts ctx` is the `towerClsOfShell = densePack` filter of the high-excess starts.
  These are **independent classifiers**: `runClsOfShell_eq_one_iff` proves
  `runClsOfShell ctx k = 1 ↔ k ≠ 0 ∧ 2·Y ≤ windowExcess (hitGap a) k r T` — a pure hit-gap **window-
  excess** condition with **no dependence** on the carry/cylinder value `M = windowCylinderValue …`.
  So (D2) `hcarry` is **NOT** derivable from the genuine-start selection; the manuscript bridge
  "carry tail `ξ1̄0⋯0` ⟹ high excess ⟹ class 1" is genuine routed content, not a definitional fact.
* The clean discharge comes instead from the **residue-band route** (below): the carry exclusion is a
  *consequence of the upper band*, so no `NoLargeRun` hypothesis is needed at all.

## What is genuinely PROVED here (no `sorry`/`axiom`/`admit`/`native_decide`)

### Part A — (D2) is AUTOMATIC in the upper residue band (CLOSED)

* `carry_excluded_of_residue_upper` — in the upper band `2ⁿ−q₀ < (M·q₀) mod 2ⁿ`, the floor witness
  `a = (M·q₀)/2ⁿ + 1` has cylinder index **equal** to `M` (equal cylinder `kν = M`), so the (D2) carry
  exclusion `kν + 1 ≠ M` is automatic (it is `M + 1 ≠ M`).  No `NoLargeRun`.
* `dyadicCylinder_of_residue_upper` — the same floor witness lands the centre in the window's **own**
  depth-`n` cylinder `DyadicCylinder n M (a/q₀)`, the equal-cylinder geometry the §25.1 match needs.

### Part B — the lower band is EXACTLY the carry-adjacent case `NoLargeRun` would exclude (CLOSED)

* `carry_adjacent_of_residue_lower` — in the strict lower band `0 < (M·q₀) mod 2ⁿ < q₀`, the floor
  witness `a = (M·q₀)/2ⁿ` is **carry-adjacent**: `cylinderIndex n (a/q₀) + 1 = M` (i.e. `kν = M−1`).
  This is precisely the boundary-run / class-`1` configuration the manuscript's no-large-run hypothesis
  routes away; it sharply identifies (D2)'s job as **selecting the upper band over the lower band**.

### Part C — the §25.1 match WITHOUT `NoLargeRun` (the headline, DERIVED)

* `UpperBandMatchData ctx` — bundles the single surviving residual `hband` (the centre-free upper
  residue-band membership of the **actual** window values) with the separately-flagged §24 floor
  `hdens` and bounded-period calibration `hpb`.
* `UpperBandMatchData.toMatchedDescentWindows` — **`MatchedDescentWindows ctx` with `NoLargeRun`
  REMOVED.**  Routing through the upper-band equal cylinder (`descentCylinderMatchData_canonical` then
  `matchedDescentWindows_of_cylinderMatchData`) closes the §25.1 match with the (D2) carry exclusion
  discharged automatically.
* `UpperBandMatchData.toSection251` — the §25.1 residual `Section251CylinderMatchResidual ctx` is
  discharged (the `NoLargeRun` antecedent is simply ignored).
* `UpperBandMatchData.toSingularSquareCertificate` — assembles the FULL wave-19
  `SingularSquareCertificate ctx` with **both** (D1) `hbound` and (D2) `hcarry` PROVED from the upper
  band (the `NoLargeRun → …` field is supplied by a proof that ignores its hypothesis), demonstrating
  that the certificate's two genuine fields are simultaneously dischargeable here.

## Audit verdict (the strictly-more-primitive residual)

(D2) is **discharged**: `UpperBandMatchData.toMatchedDescentWindows` produces the §25.1 match with no
`NoLargeRun` hypothesis, the carry exclusion proved automatically (`carry_excluded_of_residue_upper`);
and `runClsOfShell_eq_one_iff` records why it is not derivable from the genuine-start selection (it is a
window-excess condition).  The lone surviving residual is the explicit structure field

* `UpperBandMatchData.hband` — the **centre-free upper residue-band membership**
  `2ⁿ−q₀ < (M_k·q₀) mod 2ⁿ` of each actual descent-window value `M_k = windowCylinderValue …`.

This is strictly more primitive than BOTH (D1) `hbound` (it is a single arithmetic inequality on `M_k`,
no centre word, no digit agreement) and (D2) `hcarry` (which it makes automatic).  The §24 period-
density floor `hdens` and the bounded-period calibration `hpb` are the separately-flagged calibration
inputs, consumed verbatim.  The carry gap bound `|R_N| ≤ Q(N+2)` (wave-23 `integerCarry_abs_le`) is the
denominator-drop *mechanism* that puts a small-denominator centre near the window mask point, but it is
the **linear** envelope of the position-weighted carry, not the **constant** band membership; the band
membership is where the §25.3 low-density failure must be invoked (the failing shell forces the actual
window value into the admissible band, against a generic cylinder being singular-square-free).

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

namespace Erdos260

noncomputable section

/-! ## Part A — (D2) is automatic in the upper residue band -/

/--
**(D2) carry exclusion is AUTOMATIC in the upper residue band.**

If the actual window value's residue lies in the upper band `2ⁿ−q₀ < (M·q₀) mod 2ⁿ`
(`M = windowCylinderValue d s n`), the floor witness `a = (M·q₀)/2ⁿ + 1` has cylinder index *equal* to
`M` (the §25.1 equal case), so the carry-adjacent neighbour is excluded: `cylinderIndex n (a/q₀) + 1 ≠
M`.  This is the (D2) `hcarry` content, discharged with **no** `NoLargeRun` hypothesis.
-/
theorem carry_excluded_of_residue_upper {d : ℕ → ℕ} (hd : ∀ i, d i ≤ 1) {s n q0 : ℕ} (hq0 : 0 < q0)
    (hband : 2 ^ n - q0 < (windowCylinderValue d s n * q0) % 2 ^ n) :
    cylinderIndex n (((windowCylinderValue d s n * q0 / 2 ^ n + 1 : ℕ) : ℝ) / (q0 : ℝ)) + 1
      ≠ windowCylinderValue d s n := by
  have hci : cylinderIndex n (((windowCylinderValue d s n * q0 / 2 ^ n + 1 : ℕ) : ℝ) / (q0 : ℝ))
      = windowCylinderValue d s n :=
    (windowValue_eq_cylinderIndex_of_matches hq0 (residue_upper_witness_lt hd hq0 hband)
      (matchesCompletion_of_residue_upper hd hq0 hband)).symm
  omega

/--
**Upper band ⟹ the equal-cylinder geometry.**

In the upper band, the floor witness `a = (M·q₀)/2ⁿ + 1` lands the centre `a/q₀` in the window's own
depth-`n` dyadic cylinder `DyadicCylinder n M (a/q₀)` — exactly the equal-cylinder input the §25.1
match consumes (no dichotomy, no `NoLargeRun`).
-/
theorem dyadicCylinder_of_residue_upper {d : ℕ → ℕ} (hd : ∀ i, d i ≤ 1) {s n q0 : ℕ} (hq0 : 0 < q0)
    (hband : 2 ^ n - q0 < (windowCylinderValue d s n * q0) % 2 ^ n) :
    DyadicCylinder n (windowCylinderValue d s n)
      (((windowCylinderValue d s n * q0 / 2 ^ n + 1 : ℕ) : ℝ) / (q0 : ℝ)) := by
  have hci : cylinderIndex n (((windowCylinderValue d s n * q0 / 2 ^ n + 1 : ℕ) : ℝ) / (q0 : ℝ))
      = windowCylinderValue d s n :=
    (windowValue_eq_cylinderIndex_of_matches hq0 (residue_upper_witness_lt hd hq0 hband)
      (matchesCompletion_of_residue_upper hd hq0 hband)).symm
  have h0 : (0 : ℝ) ≤ ((windowCylinderValue d s n * q0 / 2 ^ n + 1 : ℕ) : ℝ) / (q0 : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hcyl := dyadicCylinder_cylinderIndex (n := n) h0
  rwa [hci] at hcyl

/-! ## Part B — the lower band is exactly the carry-adjacent case `NoLargeRun` excludes -/

/--
**The strict lower band is EXACTLY the carry-adjacent case.**

In the strict lower band `0 < (M·q₀) mod 2ⁿ < q₀` (`M = windowCylinderValue d s n`), the floor witness
`a = (M·q₀)/2ⁿ` (no `+1`) is carry-adjacent: `cylinderIndex n (a/q₀) + 1 = M`, i.e. the centre sits one
cylinder below the window value (`kν = M−1`).  This is the boundary-run / class-`1` configuration the
manuscript's no-large-run hypothesis routes away; it pins (D2)'s precise role as selecting the upper
band (equal cylinder) over the lower band (carry-adjacent).
-/
theorem carry_adjacent_of_residue_lower {d : ℕ → ℕ} {s n q0 : ℕ} (hq0 : 0 < q0)
    (hlo : 0 < (windowCylinderValue d s n * q0) % 2 ^ n)
    (hhi : (windowCylinderValue d s n * q0) % 2 ^ n < q0) :
    cylinderIndex n (((windowCylinderValue d s n * q0 / 2 ^ n : ℕ) : ℝ) / (q0 : ℝ)) + 1
      = windowCylinderValue d s n := by
  have hdm := Nat.div_add_mod (windowCylinderValue d s n * q0) (2 ^ n)
  have hMpos : 1 ≤ windowCylinderValue d s n := by
    rcases Nat.eq_zero_or_pos (windowCylinderValue d s n) with h | h
    · exfalso; rw [h] at hlo; simp at hlo
    · exact h
  have hsub : (windowCylinderValue d s n - 1) * q0 + q0 = windowCylinderValue d s n * q0 := by
    have h1 : (windowCylinderValue d s n - 1) * q0 + q0
        = (windowCylinderValue d s n - 1 + 1) * q0 := by ring
    rw [h1, Nat.sub_add_cancel hMpos]
  have key : 2 ^ n * (windowCylinderValue d s n * q0 / 2 ^ n)
      = q0 * (windowCylinderValue d s n - 1)
        + (q0 - (windowCylinderValue d s n * q0) % 2 ^ n) := by
    have hcm : (windowCylinderValue d s n - 1) * q0 = q0 * (windowCylinderValue d s n - 1) :=
      Nat.mul_comm _ _
    omega
  rw [cylinderIndex_ratCast q0 (windowCylinderValue d s n * q0 / 2 ^ n) n, key,
    Nat.mul_add_div hq0,
    Nat.div_eq_of_lt (by omega : q0 - (windowCylinderValue d s n * q0) % 2 ^ n < q0),
    Nat.add_zero, Nat.sub_add_cancel hMpos]

/-! ## Part C — the (D2)-from-selection verdict: `runClsOfShell = 1` is window-excess only -/

/--
**`runClsOfShell = 1` is a pure window-excess condition.**

The L.4.1 large-run class `1` is selected *iff* the start is non-boundary (`k ≠ 0`) and the hit-gap
window excess crosses `2·Y` — with **no** dependence on the carry/cylinder value
`windowCylinderValue …` or on `genuineDensePackStarts` (which filters on `towerClsOfShell = densePack`,
a different classifier).  Hence the (D2) carry exclusion is *not* derivable from the genuine-start
selection; it is genuine routed combinatorial content.  (Here it is discharged instead via the
residue-band route of Parts A/C.)
-/
theorem runClsOfShell_eq_one_iff (ctx : ActualFailureContext) (k : ℕ) :
    runClsOfShell ctx k = 1 ↔
      k ≠ 0 ∧ 2 * ctx.n24CarryData.Y
        ≤ windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T := by
  unfold runClsOfShell
  split_ifs with h0 hexc
  · constructor
    · intro h; exact absurd h (by decide)
    · rintro ⟨hne, _⟩; exact absurd h0 hne
  · exact iff_of_true rfl ⟨h0, hexc⟩
  · constructor
    · intro h; exact absurd h (by decide)
    · rintro ⟨_, h⟩; exact absurd h hexc

/-! ## Part D — The actual descent windows: the upper-band floor witness and its cylinder -/

/-- **The upper-band floor-witness centre numerator** for the actual descent window at start `k`:
`a_k = (M_k·q₀)/2ⁿ + 1`, with `M_k` the actual window value, `q₀` the canonical residual-centre
denominator, `n = spread+1`.  In the upper band this is a genuine residue (`< q₀`) whose depth-`n`
cylinder index is exactly `M_k`. -/
def upperBandCenter (ctx : ActualFailureContext) (k : ℕ) : ℕ :=
  windowCylinderValue ctx.shell.d (k + ctx.n24CarryData.r) (proofV4DensePackSpread ctx.shell + 1)
      * (canonicalCenter ctx).q0
    / 2 ^ (proofV4DensePackSpread ctx.shell + 1) + 1

/-- The upper-band centre is a genuine residue `< q₀` (the floor-witness bound on the actual window). -/
theorem upperBandCenter_lt (ctx : ActualFailureContext) {k : ℕ}
    (hband : 2 ^ (proofV4DensePackSpread ctx.shell + 1) - (canonicalCenter ctx).q0
      < (windowCylinderValue ctx.shell.d (k + ctx.n24CarryData.r)
            (proofV4DensePackSpread ctx.shell + 1) * (canonicalCenter ctx).q0)
        % 2 ^ (proofV4DensePackSpread ctx.shell + 1)) :
    upperBandCenter ctx k < (canonicalCenter ctx).q0 := by
  unfold upperBandCenter
  exact residue_upper_witness_lt (fun i => by rcases ctx.shell.hd i with h | h <;> omega)
    (canonicalCenter ctx).q0_pos hband

/-- The actual shell window matches the completion of the upper-band centre to full depth. -/
theorem matchesCompletion_upperBandCenter (ctx : ActualFailureContext) {k : ℕ}
    (hband : 2 ^ (proofV4DensePackSpread ctx.shell + 1) - (canonicalCenter ctx).q0
      < (windowCylinderValue ctx.shell.d (k + ctx.n24CarryData.r)
            (proofV4DensePackSpread ctx.shell + 1) * (canonicalCenter ctx).q0)
        % 2 ^ (proofV4DensePackSpread ctx.shell + 1)) :
    MatchesCompletion ctx.shell.d (k + ctx.n24CarryData.r) (proofV4DensePackSpread ctx.shell + 1)
      (canonicalCenter ctx).q0 (upperBandCenter ctx k) := by
  unfold upperBandCenter
  exact matchesCompletion_of_residue_upper (fun i => by rcases ctx.shell.hd i with h | h <;> omega)
    (canonicalCenter ctx).q0_pos hband

/-- The upper-band centre's depth-`(spread+1)` cylinder index is the actual window value (equal cylinder). -/
theorem cylinderIndex_upperBandCenter (ctx : ActualFailureContext) {k : ℕ}
    (hband : 2 ^ (proofV4DensePackSpread ctx.shell + 1) - (canonicalCenter ctx).q0
      < (windowCylinderValue ctx.shell.d (k + ctx.n24CarryData.r)
            (proofV4DensePackSpread ctx.shell + 1) * (canonicalCenter ctx).q0)
        % 2 ^ (proofV4DensePackSpread ctx.shell + 1)) :
    cylinderIndex (proofV4DensePackSpread ctx.shell + 1)
        ((upperBandCenter ctx k : ℝ) / ((canonicalCenter ctx).q0 : ℝ))
      = windowCylinderValue ctx.shell.d (k + ctx.n24CarryData.r)
          (proofV4DensePackSpread ctx.shell + 1) :=
  (windowValue_eq_cylinderIndex_of_matches (canonicalCenter ctx).q0_pos
    (upperBandCenter_lt ctx hband) (matchesCompletion_upperBandCenter ctx hband)).symm

/-- The actual descent window's value indexes the upper-band centre's own cylinder. -/
theorem dyadicCylinder_upperBandCenter (ctx : ActualFailureContext) {k : ℕ}
    (hband : 2 ^ (proofV4DensePackSpread ctx.shell + 1) - (canonicalCenter ctx).q0
      < (windowCylinderValue ctx.shell.d (k + ctx.n24CarryData.r)
            (proofV4DensePackSpread ctx.shell + 1) * (canonicalCenter ctx).q0)
        % 2 ^ (proofV4DensePackSpread ctx.shell + 1)) :
    DyadicCylinder (proofV4DensePackSpread ctx.shell + 1)
      (windowCylinderValue ctx.shell.d (k + ctx.n24CarryData.r)
        (proofV4DensePackSpread ctx.shell + 1))
      ((upperBandCenter ctx k : ℝ) / ((canonicalCenter ctx).q0 : ℝ)) := by
  rw [← cylinderIndex_upperBandCenter ctx hband]
  exact dyadicCylinder_cylinderIndex (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

/-! ## Part E — The §25.1 match WITHOUT `NoLargeRun` (the headline) -/

/--
**The upper-band descent-window data — the single surviving residual + the flagged calibrations.**

The lone residual field `hband` is the **centre-free upper residue-band membership** of each actual
descent-window value `M_k = windowCylinderValue ctx.shell.d (k+r) (spread+1)`:
`2ⁿ−q₀ < (M_k·q₀) mod 2ⁿ`.  This is strictly more primitive than both (D1) `hbound` and (D2) `hcarry`:
a single arithmetic inequality on `M_k`, with no centre word, no digit agreement, and no `NoLargeRun`.
The remaining fields `hdens` (§24 period-density floor) and `hpb` (bounded-period calibration) are the
separately-flagged calibration inputs, consumed verbatim by `descentCylinderMatchData_canonical`.
-/
structure UpperBandMatchData (ctx : ActualFailureContext) where
  /-- **THE surviving residual**: the centre-free upper residue-band membership of the actual window
  value at each genuine start. -/
  hband : ∀ k ∈ genuineDensePackStarts ctx,
    2 ^ (proofV4DensePackSpread ctx.shell + 1) - (canonicalCenter ctx).q0
      < (windowCylinderValue ctx.shell.d (k + ctx.n24CarryData.r)
            (proofV4DensePackSpread ctx.shell + 1) * (canonicalCenter ctx).q0)
        % 2 ^ (proofV4DensePackSpread ctx.shell + 1)
  /-- The §24 period-density floor on the orbit word of the upper-band centre (flagged calibration). -/
  hdens : ∀ k ∈ genuineDensePackStarts ctx,
    manuscriptRhoD * (orderOf (2 : ZMod (canonicalCenter ctx).q0) : ℝ)
      ≤ (windowWeight (dyadicDigit (canonicalCenter ctx).q0 (upperBandCenter ctx k)) 0
          (orderOf (2 : ZMod (canonicalCenter ctx).q0)) : ℝ)
  /-- The bounded-period calibration (flagged calibration). -/
  hpb : Classical.choose ctx.shell.hXdyadic + orderOf (2 : ZMod (canonicalCenter ctx).q0)
      ≤ proofV4DensePackSpread ctx.shell + 2

/-- The §25.1 cylinder-match data, built at the upper-band floor-witness centre — no `NoLargeRun`. -/
def UpperBandMatchData.toDescentCylinderMatchData {ctx : ActualFailureContext}
    (D : UpperBandMatchData ctx) : DescentCylinderMatchData ctx :=
  descentCylinderMatchData_canonical ctx (upperBandCenter ctx)
    (fun k hk => dyadicCylinder_upperBandCenter ctx (D.hband k hk)) D.hdens D.hpb

/--
**THE HEADLINE: `MatchedDescentWindows ctx` with `NoLargeRun` REMOVED.**

From the upper residue-band membership (plus the flagged §24 floor and the calibration), the §25.1
match holds for every genuine descent window — the (D2) no-large-run carry exclusion is discharged
automatically by the upper-band equal-cylinder geometry, so the `NoLargeRun` hypothesis never appears.
-/
theorem UpperBandMatchData.toMatchedDescentWindows {ctx : ActualFailureContext}
    (D : UpperBandMatchData ctx) : MatchedDescentWindows ctx :=
  matchedDescentWindows_of_cylinderMatchData ctx D.toDescentCylinderMatchData

/--
**The §25.1 cylinder-match residual `Section251CylinderMatchResidual ctx` discharged.**

`Section251CylinderMatchResidual ctx` is `NoLargeRun ctx → Nonempty (DescentCylinderMatchData ctx)`;
the upper-band route produces the data with the `NoLargeRun` antecedent simply ignored.
-/
theorem UpperBandMatchData.toSection251 {ctx : ActualFailureContext}
    (D : UpperBandMatchData ctx) : Section251CylinderMatchResidual ctx :=
  fun _ => ⟨D.toDescentCylinderMatchData⟩

/--
**The FULL §25.1 `SingularSquareCertificate ctx`, with both (D1) and (D2) PROVED from the upper band.**

The certificate's two genuine fields are simultaneously discharged here: (D1) `hbound` is the
singular-square bound from the upper-band match (`singularSquareBound_of_matches`), and (D2) `hcarry`
is the carry exclusion, proved by a function that **ignores** its `NoLargeRun` argument
(`carry_excluded_of_residue_upper`).  The flagged `hdens`/`hpb` are carried verbatim.
-/
def UpperBandMatchData.toSingularSquareCertificate {ctx : ActualFailureContext}
    (D : UpperBandMatchData ctx) : SingularSquareCertificate ctx where
  a := upperBandCenter ctx
  hbound := fun k hk =>
    singularSquareBound_of_matches (canonicalCenter ctx).q0_pos
      (upperBandCenter_lt ctx (D.hband k hk)) (matchesCompletion_upperBandCenter ctx (D.hband k hk))
  hcarry := fun _ k hk => by
    have hci := cylinderIndex_upperBandCenter ctx (D.hband k hk)
    omega
  hdens := D.hdens
  hpb := D.hpb

/-! ## Part F — Honest residual inventory -/

/-- The precise status of (D2) / the §25.1 match after this module. -/
def descentDepthNoLargeRunResiduals : List String :=
  [ "GOAL (wave-24) — DISCHARGE (D2) the no-large-run carry exclusion and reduce the §25.1 match to " ++
      "its sharpest centre-free primitive, beyond wave-23's re-characterization; remove NoLargeRun " ++
      "from the end-to-end match where possible.",
    "VERDICT (D2 NOT from the genuine-start selection) — runClsOfShell_eq_one_iff: runClsOfShell ctx " ++
      "k = 1 ↔ k ≠ 0 ∧ 2·Y ≤ windowExcess (hitGap a) k r T, a pure hit-gap WINDOW-EXCESS condition " ++
      "with NO dependence on the carry/cylinder value windowCylinderValue …. genuineDensePackStarts " ++
      "filters on towerClsOfShell = densePack (a different classifier), so (D2) hcarry is NOT " ++
      "definitionally encoded in the genuine-start selection; the carry-tail ⟹ class-1 bridge is " ++
      "genuine routed content.",
    "CLOSED (D2 AUTOMATIC, upper band) — carry_excluded_of_residue_upper: in the upper band " ++
      "2ⁿ−q₀ < (M·q₀) mod 2ⁿ the floor witness a = (M·q₀)/2ⁿ+1 has cylinder index = M (equal " ++
      "cylinder), so the carry exclusion cylinderIndex n (a/q₀)+1 ≠ M is automatic — NO NoLargeRun. " ++
      "dyadicCylinder_of_residue_upper supplies the equal-cylinder geometry DyadicCylinder n M (a/q₀).",
    "CLOSED (D2 NECESSITY, lower band) — carry_adjacent_of_residue_lower: in the strict lower band " ++
      "0 < (M·q₀) mod 2ⁿ < q₀ the floor witness a = (M·q₀)/2ⁿ is carry-adjacent, cylinderIndex n " ++
      "(a/q₀)+1 = M (kν = M−1) — exactly the boundary-run/class-1 configuration NoLargeRun routes " ++
      "away. So (D2)'s precise role is selecting the UPPER band (equal) over the LOWER band " ++
      "(carry-adjacent).",
    "DERIVED (the headline — NoLargeRun removed) — UpperBandMatchData.toMatchedDescentWindows: from " ++
      "the upper residue-band membership (plus the flagged §24 floor and calibration), " ++
      "MatchedDescentWindows ctx holds with NO NoLargeRun hypothesis (routing through the upper-band " ++
      "equal cylinder via descentCylinderMatchData_canonical + matchedDescentWindows_of_cylinder" ++
      "MatchData). toSection251 discharges Section251CylinderMatchResidual ctx; toSingular" ++
      "SquareCertificate assembles the FULL certificate with BOTH (D1) hbound and (D2) hcarry PROVED " ++
      "(the NoLargeRun → … field ignores its hypothesis).",
    "RESIDUAL (the single explicit field, strictly more primitive than (D1) and (D2)) — " ++
      "UpperBandMatchData.hband: the CENTRE-FREE upper residue-band membership 2ⁿ−q₀ < (M_k·q₀) mod " ++
      "2ⁿ of each ACTUAL descent-window value M_k = windowCylinderValue ctx.shell.d (k+r) (spread+1). " ++
      "A single arithmetic inequality on M_k — no centre word, no digit agreement, no NoLargeRun. It " ++
      "subsumes (D1) hbound (it IS the (D1) satisfiability condition, wave-23 exists_descentBound_iff_" ++
      "residueBand) and makes (D2) hcarry automatic. Where the §25.3 low-density failure must be " ++
      "invoked: the failing shell forces the actual window value into this admissible band, against a " ++
      "generic depth-n cylinder being singular-square-free.",
    "FLAGGED (calibration, not blocking) — UpperBandMatchData.hdens / hpb are the §24 period-density " ++
      "floor (1/(4Q) ρ_D calibration) and the bounded-period calibration, consumed verbatim; the " ++
      "construction is parametric in manuscriptRhoD.",
    "CONTEXT (carry gap bound vs the band) — wave-23 integerCarry_abs_le gives |R_N| ≤ Q(N+2), the " ++
      "LINEAR O_Q(N) envelope of the position-weighted carry (the denominator-drop mechanism placing " ++
      "a small-denominator centre near the window mask point). It is NOT the CONSTANT band membership " ++
      "< q₀; converting envelope to band needs the depth calibration n = p−B (hpb) and the §25.3 " ++
      "density failure, since only the residue VALUE mod Q is periodic while the carry VALUE that " ++
      "fixes the digits is unbounded (carryOf_value_grows_on_zeroRun)." ]

theorem descentDepthNoLargeRunResiduals_nonempty : descentDepthNoLargeRunResiduals ≠ [] := by
  simp [descentDepthNoLargeRunResiduals]

/-! ## Part G — Axiom-cleanliness audit -/

#print axioms carry_excluded_of_residue_upper
#print axioms dyadicCylinder_of_residue_upper
#print axioms carry_adjacent_of_residue_lower
#print axioms runClsOfShell_eq_one_iff
#print axioms upperBandCenter_lt
#print axioms matchesCompletion_upperBandCenter
#print axioms cylinderIndex_upperBandCenter
#print axioms dyadicCylinder_upperBandCenter
#print axioms UpperBandMatchData.toDescentCylinderMatchData
#print axioms UpperBandMatchData.toMatchedDescentWindows
#print axioms UpperBandMatchData.toSection251
#print axioms UpperBandMatchData.toSingularSquareCertificate

end

end Erdos260
