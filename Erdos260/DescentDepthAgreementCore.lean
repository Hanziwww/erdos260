import Erdos260.SingularSquareBoundCore
import Erdos260.FailingShellPeriodicityCore

/-!
# §25.1 descent-depth agreement (D1): the failing-shell window matches its rational completion

Wave-20 (`SingularSquareBoundCore`) proved the singular-square bound (D1) is **inter-reducible** with
the §25.1 equal-or-carry cylinder containment of the residual centre `a/q₀`, isolating the lone
genuinely irreducible step as the **descent-depth agreement** `‖η − η_{x,w}‖ < 2^{−depth}`: the actual
descent-window mask point `M / 2^n` lands within `2^{−n}` of the centre `a/q₀`.  Wave-21
(`FailingShellPeriodicityCore`) proved the §24 carry root: the integer carry residue is eventually
periodic mod `Q` with period `ord_{q₀}(2)`, delivering the period-`ord_{q₀}(2)` rational completion
`dyadicDigit q₀ a` to depth.

This file (NEW; it edits no existing file) **discharges the (D1) `SingularSquareBound` /
`SingularSquareCertificate.hbound` field for the actual descent windows** from the descent-depth
agreement, and pins the agreement to the single genuinely irreducible window-selection input — never a
`sorry`.

## What is genuinely PROVED here (no `sorry`/`axiom`/`admit`/`native_decide`)

### Part A/B — the master reduction (CLOSED)

* `MatchesCompletion d s n q₀ a` — the **descent-depth agreement, digit form**: the window word `d`
  spells, over `[s, s+n)`, the first `n` digits of the rational completion `dyadicDigit q₀ a` of
  `a/q₀`.
* `windowCylinderValue_congr` — the depth-`n` window value depends only on the window digits.
* `windowValue_eq_cylinderIndex_of_matches` — agreement ⟹ the window value **is** the centre's
  depth-`n` cylinder index (`= cylinderIndex n (a/q₀)`), via the congruence and the proved
  `windowCylinderValue_dyadicDigit_self`.
* `singularSquareBound_of_matches` — **(D1) from the agreement**: `singularSquareBound_of_cylinderIndex_eq`
  then gives `SingularSquareBound n (windowCylinderValue d s n) q₀ a` (the manuscript eq. 25.1 bound
  `|R| · 2ⁿ < D · q₀`, i.e. `|M/2ⁿ − a/q₀| < 2^{−n}`).

### Part C — carry/order periodicity delivers the agreement to depth (CLOSED)

* `matchesCompletion_of_periodicOn` — if the window word is `PeriodicOn` with a period `t` that is
  **also** a period of the completion, then agreement on ONE period `[0, t)` extends to full depth `n`
  (strong induction over the periods).
* `matchesCompletion_of_periodicOn_orbit` / `singularSquareBound_of_periodicOn_orbit` — specialized to
  `t = ord_{q₀}(2)` via the proved completion periodicity `dyadicDigit_period`: this is exactly "the
  window digits agree with a period-`ord_{q₀}(2)` rational completion".

### Part D — non-vacuity: the completion realises the agreement freely (CLOSED)

* `matchesCompletion_self`, `singularSquareBound_completion` — the completion `dyadicDigit q₀ a`
  realises the agreement at EVERY depth, so (D1) is genuinely proved for the period-`ord_{q₀}(2)`
  rational completion model; `completion_periodicOn` (`= orbitWord_periodicOn`) records that the model
  is itself periodic.  No constant/all-zero shortcut.

### Part E — rational separation pins the centre (CLOSED)

* `descentCentre_unique` / `descentCentre_unique_of_matches` — a single window value achieving the
  agreement for two small denominators `q₀, q₀'` with `2 q₀ q₀' ≤ 2ⁿ` forces `a/q₀ = a'/q₀'`
  (`SingularSquareBoundCore.singularSquare_center_unique`, the §24.3 separation kernel).  The
  descent-depth agreement determines the centre.

### Part F — discharging the §25.1 certificate (D1) field (DERIVED)

* `descentWindow_singularSquareBound` — from a `DescentWindowMatch ctx` (per-genuine-start full-depth
  match plus the residue bookkeeping `a_k < q₀`), the singular-square bound holds for **every** genuine
  DensePack start — *exactly* the `DirtyCrossingCylinderCore.SingularSquareCertificate.hbound` field.
* `singularSquareCertificate_of_descentWindowMatch` — assembles the FULL certificate by combining the
  discharged (D1) with the separately-flagged (D2) carry routing, the §24 density floor, and the period
  calibration (taken verbatim as inputs); compose with the existing
  `matchedDescentWindows_of_singularSquareCertificate` to close the entire §25.1 match.
* `DescentWindowMatch.ofPeriodic` — pushes the per-window match down to its sharpest form: the window
  word being `PeriodicOn` with the orbit period plus a ONE-PERIOD value match.

## The single surviving residual (audit verdict)

The full chain from the **descent-depth agreement** to (D1) and to the §25.1 certificate's `hbound`
field is proved here.  The lone irreducible input is `DescentWindowMatch.hmatch` (equivalently the
`hper + hbase` of `ofPeriodic`): the ACTUAL failing-shell window's first `spread+1` digits equal those
of the rational completion `dyadicDigit q₀ a_k`.  This is the manuscript denominator-drop agreement
`|R| ≪_Q X + p` — the failing low-density shell matches its rational completion to descent depth
`p − B`.  It is a window-**selection** fact, upstream of the cylinder geometry: carry-RESIDUE
periodicity mod `Q` is proved upstream (`FailingShellPeriodicityCore.carryOf_eventually_periodic_mod`),
but the carry VALUE that fixes the digits is unbounded
(`carryOf_value_grows_on_zeroRun`), so neither window-digit periodicity nor the one-period match is
delivered by residue periodicity alone.  It is stated here as one explicit, documented hypothesis
FIELD — never a `sorry`.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

namespace Erdos260

noncomputable section

/-! ## Part A — The descent-depth agreement predicate and the window-value congruence -/

/-- **The descent-depth agreement (digit form).**  The window word `d`, read over `[s, s+n)`, spells
the first `n` binary digits of the rational completion `dyadicDigit q₀ a` of the centre `a/q₀`. -/
def MatchesCompletion (d : ℕ → ℕ) (s n q0 a : ℕ) : Prop :=
  ∀ i, i < n → d (s + i) = dyadicDigit q0 a i

/-- **The depth-`N` window value depends only on the window digits.**  `windowCylinderValue` is the
fixed combination `∑_{i<N} d(s+i)·2^{N-1-i}`, so equal window digits give equal values. -/
theorem windowCylinderValue_congr {d d' : ℕ → ℕ} {s s' N : ℕ}
    (h : ∀ i, i < N → d (s + i) = d' (s' + i)) :
    windowCylinderValue d s N = windowCylinderValue d' s' N := by
  unfold windowCylinderValue
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mem_range] at hi
  rw [h i hi]

/-! ## Part B — The master reduction: agreement ⟹ (D1) -/

/-- **Agreement ⟹ the window value is the centre's cylinder index.**  If the window matches the
completion to depth `n`, then `windowCylinderValue d s n = cylinderIndex n (a/q₀)` — the window lands
in the centre's own depth-`n` dyadic cylinder.  (Congruence + `windowCylinderValue_dyadicDigit_self`.) -/
theorem windowValue_eq_cylinderIndex_of_matches {d : ℕ → ℕ} {s n q0 a : ℕ}
    (hq0 : 0 < q0) (ha : a < q0) (hmatch : MatchesCompletion d s n q0 a) :
    windowCylinderValue d s n = cylinderIndex n ((a : ℝ) / (q0 : ℝ)) := by
  rw [windowCylinderValue_congr (d := d) (d' := dyadicDigit q0 a) (s := s) (s' := 0) (N := n)
      (fun i hi => by rw [hmatch i hi, Nat.zero_add])]
  exact windowCylinderValue_dyadicDigit_self hq0 ha n

/--
**THE MASTER REDUCTION (D1 from the descent-depth agreement).**

If the actual window word matches the rational completion `dyadicDigit q₀ a` to depth `n`
(`MatchesCompletion`), then the singular-square bound holds:
`SingularSquareBound n (windowCylinderValue d s n) q₀ a`, i.e. `|R| · 2ⁿ < D · q₀` with
`R = M·q₀ − a·2ⁿ`, `M = windowCylinderValue d s n`, `D = 2ⁿ` (manuscript eq. 25.1).  The agreement
makes the window value the centre's cylinder index, and equal cylinders give (D1) by
`singularSquareBound_of_cylinderIndex_eq`.
-/
theorem singularSquareBound_of_matches {d : ℕ → ℕ} {s n q0 a : ℕ}
    (hq0 : 0 < q0) (ha : a < q0) (hmatch : MatchesCompletion d s n q0 a) :
    SingularSquareBound n (windowCylinderValue d s n) q0 a :=
  singularSquareBound_of_cylinderIndex_eq hq0
    (windowValue_eq_cylinderIndex_of_matches hq0 ha hmatch).symm

/-! ## Part C — Carry/order periodicity delivers the agreement to depth -/

/--
**Periodicity extends the agreement from one period to full depth.**

If the window word `d` is `PeriodicOn [s, s+n)` with period `t`, and `t` is **also** a period of the
completion `dyadicDigit q₀ a` (`hcompper`), then agreement on the first period `[0, t)` (`hbase`)
extends to agreement to the full depth `n`.  Strong induction over the number of periods: each index
`i ≥ t` is reduced to `i − t` using the period of `d` and the period of the completion.
-/
theorem matchesCompletion_of_periodicOn {d : ℕ → ℕ} {s n q0 a t : ℕ}
    (hper : PeriodicOn d s n t)
    (hcompper : ∀ j, dyadicDigit q0 a (j + t) = dyadicDigit q0 a j)
    (hbase : ∀ i, i < t → d (s + i) = dyadicDigit q0 a i) :
    MatchesCompletion d s n q0 a := by
  have ht0 : 0 < t := hper.1
  intro i
  induction i using Nat.strong_induction_on with
  | _ i IH =>
    intro hi
    rcases Nat.lt_or_ge i t with hlt | hge
    · exact hbase i hlt
    · have hsit : s + (i - t) + t = s + i := by omega
      have hit : i - t + t = i := by omega
      have hkey : d (s + (i - t) + t) = d (s + (i - t)) := hper.2 (i - t) (by omega)
      have hIH : d (s + (i - t)) = dyadicDigit q0 a (i - t) := IH (i - t) (by omega) (by omega)
      have hcp : dyadicDigit q0 a (i - t + t) = dyadicDigit q0 a (i - t) := hcompper (i - t)
      calc d (s + i) = d (s + (i - t) + t) := by rw [hsit]
        _ = d (s + (i - t)) := hkey
        _ = dyadicDigit q0 a (i - t) := hIH
        _ = dyadicDigit q0 a (i - t + t) := hcp.symm
        _ = dyadicDigit q0 a i := by rw [hit]

/-- **Carry/order periodicity, orbit-period form.**  Specialising to `t = ord_{q₀}(2)` (a period of the
completion by the proved `dyadicDigit_period`), agreement on one orbit period extends to full depth. -/
theorem matchesCompletion_of_periodicOn_orbit {d : ℕ → ℕ} {s n q0 a : ℕ}
    (hper : PeriodicOn d s n (orderOf (2 : ZMod q0)))
    (hbase : ∀ i, i < orderOf (2 : ZMod q0) → d (s + i) = dyadicDigit q0 a i) :
    MatchesCompletion d s n q0 a :=
  matchesCompletion_of_periodicOn hper (dyadicDigit_period q0 a) hbase

/-- **(D1) from carry/order periodicity + a one-period match.**  Combining the master reduction with
the periodicity extension: a periodic window agreeing with the completion on one orbit period satisfies
the singular-square bound to full depth. -/
theorem singularSquareBound_of_periodicOn_orbit {d : ℕ → ℕ} {s n q0 a : ℕ}
    (hq0 : 0 < q0) (ha : a < q0)
    (hper : PeriodicOn d s n (orderOf (2 : ZMod q0)))
    (hbase : ∀ i, i < orderOf (2 : ZMod q0) → d (s + i) = dyadicDigit q0 a i) :
    SingularSquareBound n (windowCylinderValue d s n) q0 a :=
  singularSquareBound_of_matches hq0 ha (matchesCompletion_of_periodicOn_orbit hper hbase)

/-! ## Part D — Non-vacuity: the rational completion realises the agreement freely -/

/-- The rational completion trivially matches itself to every depth. -/
theorem matchesCompletion_self (q0 a n : ℕ) : MatchesCompletion (dyadicDigit q0 a) 0 n q0 a := by
  intro i _
  rw [Nat.zero_add]

/-- **(D1) is genuinely proved for the period-`ord_{q₀}(2)` rational completion model.**  For a
small-odd-denominator centre `a/q₀` (`a < q₀`), the window value of its own completion word equals its
cylinder index at every depth, so the singular-square bound holds — no constant/all-zero shortcut. -/
theorem singularSquareBound_completion {q0 a : ℕ} (hq0 : 0 < q0) (ha : a < q0) (n : ℕ) :
    SingularSquareBound n (windowCylinderValue (dyadicDigit q0 a) 0 n) q0 a :=
  singularSquareBound_of_matches hq0 ha (matchesCompletion_self q0 a n)

/-- The completion model is itself periodic with period `ord_{q₀}(2)` (the §24 carry root delivered to
depth), so the descent-depth agreement is witnessed by a genuinely periodic word. -/
theorem completion_periodicOn {q0 : ℕ} (hq0 : 1 < q0) (hodd : Odd q0) (a s n : ℕ) :
    PeriodicOn (dyadicDigit q0 a) s n (orderOf (2 : ZMod q0)) :=
  orbitWord_periodicOn hq0 hodd a s n

/-! ## Part E — Rational separation: the descent-depth agreement pins a unique centre -/

/--
**The descent-depth agreement determines the centre (rational separation).**

If a single window value `M` lands in the depth-`n` cylinders of two small-denominator centres
`a/q₀, a'/q₀'` with `2 q₀ q₀' ≤ 2ⁿ` (both achieve the descent-depth agreement), the centres coincide:
`a/q₀ = a'/q₀'`.  This is `SingularSquareBoundCore.singularSquare_center_unique`, the §24.3 separation
kernel, routed through the equal-cylinder reduction.
-/
theorem descentCentre_unique {n q0 q0' M a a' : ℕ}
    (hq0 : 0 < q0) (hq0' : 0 < q0') (hsep : 2 * q0 * q0' ≤ 2 ^ n)
    (h : cylinderIndex n ((a : ℝ) / (q0 : ℝ)) = M)
    (h' : cylinderIndex n ((a' : ℝ) / (q0' : ℝ)) = M) :
    (a : ℝ) / (q0 : ℝ) = (a' : ℝ) / (q0' : ℝ) :=
  singularSquare_center_unique hq0 hq0' hsep
    (singularSquareBound_of_cylinderIndex_eq hq0 h)
    (singularSquareBound_of_cylinderIndex_eq hq0' h')

/-- **Two completions matched by one window have equal centres.**  If the SAME window word matches the
completions of two small-denominator centres to depth `n` (separation `2 q₀ q₀' ≤ 2ⁿ`), then
`a/q₀ = a'/q₀'`. -/
theorem descentCentre_unique_of_matches {d : ℕ → ℕ} {s n q0 q0' a a' : ℕ}
    (hq0 : 0 < q0) (hq0' : 0 < q0') (ha : a < q0) (ha' : a' < q0')
    (hsep : 2 * q0 * q0' ≤ 2 ^ n)
    (hm : MatchesCompletion d s n q0 a) (hm' : MatchesCompletion d s n q0' a') :
    (a : ℝ) / (q0 : ℝ) = (a' : ℝ) / (q0' : ℝ) :=
  descentCentre_unique hq0 hq0' hsep
    (windowValue_eq_cylinderIndex_of_matches hq0 ha hm).symm
    (windowValue_eq_cylinderIndex_of_matches hq0' ha' hm').symm

/-! ## Part F — Discharging the §25.1 `SingularSquareCertificate` (D1) for the actual descent windows -/

/--
**The descent-window match data — the single irreducible window-selection input.**

For the actual failure context `ctx`, the per-genuine-start residual-centre numerators `a k` (each a
genuine residue `a k < q₀`) together with the **descent-depth agreement** `hmatch`: the actual shell
window over `[k+r, k+r+spread]` spells the first `spread+1` digits of the rational completion
`dyadicDigit q₀ (a k)` of the centre `a_k/q₀`.  This `hmatch` field is the manuscript denominator-drop
agreement `|R| ≪_Q X + p`; it is the lone irreducible input, stated explicitly (never a `sorry`).
-/
structure DescentWindowMatch (ctx : ActualFailureContext) where
  /-- The per-start residual-centre numerator (the `2^{φ_k}`-shifted centre). -/
  a : ℕ → ℕ
  /-- Each numerator is a genuine residue mod `q₀`. -/
  ha : ∀ k ∈ genuineDensePackStarts ctx, a k < (canonicalCenter ctx).q0
  /-- **THE descent-depth agreement** for each genuine descent window (the irreducible selection
  input): the shell digits over `[k+r, k+r+spread]` equal the completion `dyadicDigit q₀ (a k)`. -/
  hmatch : ∀ k ∈ genuineDensePackStarts ctx,
    MatchesCompletion ctx.shell.d (k + ctx.n24CarryData.r)
      (proofV4DensePackSpread ctx.shell + 1) (canonicalCenter ctx).q0 (a k)

/--
**The §25.1 singular-square bound (D1) DISCHARGED for the actual descent windows.**

From a `DescentWindowMatch ctx`, the singular-square bound holds for every genuine DensePack start.
This is *exactly* the `DirtyCrossingCylinderCore.SingularSquareCertificate.hbound` field — the genuine
Diophantine (D1) heart — now reduced to the descent-depth agreement.
-/
theorem descentWindow_singularSquareBound (ctx : ActualFailureContext)
    (W : DescentWindowMatch ctx) :
    ∀ k ∈ genuineDensePackStarts ctx,
      SingularSquareBound (proofV4DensePackSpread ctx.shell + 1)
        (windowCylinderValue ctx.shell.d (k + ctx.n24CarryData.r)
          (proofV4DensePackSpread ctx.shell + 1))
        (canonicalCenter ctx).q0 (W.a k) := by
  intro k hk
  exact singularSquareBound_of_matches (canonicalCenter ctx).q0_pos (W.ha k hk) (W.hmatch k hk)

/--
**The full §25.1 certificate, assembled from the descent-depth agreement.**

The (D1) `hbound` field is discharged by `descentWindow_singularSquareBound`; the remaining fields are
the separately-flagged residual/calibration inputs taken verbatim — (D2) the `NoLargeRun`-routed carry
exclusion `hcarry`, the §24 period-density floor `hdens`, and the bounded-period calibration `hpb`.
Composing with `matchedDescentWindows_of_singularSquareCertificate` then closes the §25.1 match.
-/
def singularSquareCertificate_of_descentWindowMatch (ctx : ActualFailureContext)
    (W : DescentWindowMatch ctx)
    (hcarry : NoLargeRun ctx → ∀ k ∈ genuineDensePackStarts ctx,
      windowCylinderValue ctx.shell.d (k + ctx.n24CarryData.r)
          (proofV4DensePackSpread ctx.shell + 1)
        ≠ cylinderIndex (proofV4DensePackSpread ctx.shell + 1)
            ((W.a k : ℝ) / ((canonicalCenter ctx).q0 : ℝ)) + 1)
    (hdens : ∀ k ∈ genuineDensePackStarts ctx,
      manuscriptRhoD * (orderOf (2 : ZMod (canonicalCenter ctx).q0) : ℝ)
        ≤ (windowWeight (dyadicDigit (canonicalCenter ctx).q0 (W.a k)) 0
            (orderOf (2 : ZMod (canonicalCenter ctx).q0)) : ℝ))
    (hpb : Classical.choose ctx.shell.hXdyadic + orderOf (2 : ZMod (canonicalCenter ctx).q0)
        ≤ proofV4DensePackSpread ctx.shell + 2) :
    SingularSquareCertificate ctx :=
  { a := W.a
    hbound := descentWindow_singularSquareBound ctx W
    hcarry := hcarry
    hdens := hdens
    hpb := hpb }

/--
**The per-window match reduced to its sharpest form (carry periodicity).**

A `DescentWindowMatch` is produced from, per genuine start, (i) the shell window being `PeriodicOn`
with the orbit period `ord_{q₀}(2)` and (ii) a ONE-PERIOD value match.  The full-depth agreement then
follows by `matchesCompletion_of_periodicOn_orbit` (the completion is periodic with that period by the
proved `dyadicDigit_period`).  Both inputs are value-level: residue periodicity alone does not deliver
them, but together they are the sharpest statement of the selection residual.
-/
def DescentWindowMatch.ofPeriodic (ctx : ActualFailureContext)
    (a : ℕ → ℕ)
    (ha : ∀ k ∈ genuineDensePackStarts ctx, a k < (canonicalCenter ctx).q0)
    (hper : ∀ k ∈ genuineDensePackStarts ctx,
      PeriodicOn ctx.shell.d (k + ctx.n24CarryData.r) (proofV4DensePackSpread ctx.shell + 1)
        (orderOf (2 : ZMod (canonicalCenter ctx).q0)))
    (hbase : ∀ k ∈ genuineDensePackStarts ctx, ∀ i,
        i < orderOf (2 : ZMod (canonicalCenter ctx).q0) →
          ctx.shell.d (k + ctx.n24CarryData.r + i)
            = dyadicDigit (canonicalCenter ctx).q0 (a k) i) :
    DescentWindowMatch ctx :=
  { a := a
    ha := ha
    hmatch := fun k hk => matchesCompletion_of_periodicOn_orbit (hper k hk) (hbase k hk) }

/-! ## Part G — Honest residual inventory -/

/-- The precise status of the §25.1 descent-depth agreement / (D1) after this module. -/
def descentDepthAgreementResiduals : List String :=
  [ "GOAL (wave-22) — discharge the §25.1 (D1) singular-square bound |R| < q₀ for the ACTUAL descent " ++
      "windows: the window value M = windowCylinderValue d (k+r) (spread+1) approximates the canonical " ++
      "residual centre a_k/q₀ to within 2^−(spread+1) (the descent-depth agreement / SingularSquare" ++
      "Certificate.hbound field).",
    "CLOSED (master reduction) — singularSquareBound_of_matches: if the window word matches the " ++
      "rational completion dyadicDigit q₀ a to depth n (MatchesCompletion) then windowCylinderValue " ++
      "d s n = cylinderIndex n (a/q₀) (windowValue_eq_cylinderIndex_of_matches, via windowCylinderValue" ++
      "_congr + windowCylinderValue_dyadicDigit_self), so (D1) holds by singularSquareBound_of_" ++
      "cylinderIndex_eq. The descent-depth agreement IS the digit match.",
    "CLOSED (carry/order periodicity delivers agreement to depth) — matchesCompletion_of_periodicOn: a " ++
      "window word PeriodicOn with a period t that is also a period of the completion, agreeing on ONE " ++
      "period [0,t), agrees to full depth n. matchesCompletion_of_periodicOn_orbit / singularSquare" ++
      "Bound_of_periodicOn_orbit specialise to t = ord_{q₀}(2) via the proved dyadicDigit_period — " ++
      "exactly 'the window digits agree with a period-ord_{q₀}(2) rational completion'.",
    "CLOSED (non-vacuity) — the completion dyadicDigit q₀ a realises the agreement FREELY at every " ++
      "depth (matchesCompletion_self, singularSquareBound_completion) and is itself periodic with " ++
      "period ord_{q₀}(2) (completion_periodicOn = orbitWord_periodicOn). (D1) is genuinely proved for " ++
      "the period-ord_{q₀}(2) completion model; no constant/all-zero shortcut.",
    "CLOSED (rational separation) — descentCentre_unique / descentCentre_unique_of_matches: a single " ++
      "window value achieving the agreement for two small denominators q₀,q₀' with 2q₀q₀' ≤ 2ⁿ pins a " ++
      "UNIQUE centre a/q₀ = a'/q₀' (SingularSquareBoundCore.singularSquare_center_unique, the §24.3 " ++
      "separation kernel). The agreement determines the centre.",
    "DERIVED (§25.1 certificate D1 field) — descentWindow_singularSquareBound: from a DescentWindow" ++
      "Match ctx (per-genuine-start full-depth match + a_k < q₀) the SingularSquareBound (spread+1) " ++
      "(windowCylinderValue …) q₀ (a k) holds for every genuine DensePack start — EXACTLY the Dirty" ++
      "CrossingCylinderCore.SingularSquareCertificate.hbound field. singularSquareCertificate_of_" ++
      "descentWindowMatch assembles the FULL certificate (discharged D1 + the verbatim D2 carry " ++
      "routing + §24 density floor + period calibration); compose with matchedDescentWindows_of_" ++
      "singularSquareCertificate to close the §25.1 match.",
    "DELIVERED (residual pushed to one period) — DescentWindowMatch.ofPeriodic: the per-window full-" ++
      "depth match reduces, via matchesCompletion_of_periodicOn_orbit, to (i) the window word being " ++
      "PeriodicOn with the orbit period and (ii) a ONE-PERIOD value match.",
    "RESIDUAL (the single explicit numeric/selection input, never a sorry) — DescentWindowMatch.hmatch " ++
      "(equivalently hper + hbase of ofPeriodic): the ACTUAL shell window's first spread+1 digits equal " ++
      "those of the rational completion dyadicDigit q₀ a_k. This is the manuscript denominator-drop " ++
      "agreement |R| ≪_Q X+p (the failing low-density shell matches its rational completion to depth " ++
      "p−B), a window-SELECTION fact upstream of the cylinder geometry. Carry-RESIDUE periodicity mod Q " ++
      "is proved (FailingShellPeriodicityCore.carryOf_eventually_periodic_mod) but the carry VALUE that " ++
      "fixes the digits is unbounded (carryOf_value_grows_on_zeroRun), so residue periodicity alone " ++
      "delivers neither window-digit periodicity nor the one-period match. Stated as one explicit, " ++
      "documented hypothesis FIELD." ]

theorem descentDepthAgreementResiduals_nonempty : descentDepthAgreementResiduals ≠ [] := by
  simp [descentDepthAgreementResiduals]

/-! ## Part H — Axiom-cleanliness audit -/

#print axioms windowCylinderValue_congr
#print axioms windowValue_eq_cylinderIndex_of_matches
#print axioms singularSquareBound_of_matches
#print axioms matchesCompletion_of_periodicOn
#print axioms matchesCompletion_of_periodicOn_orbit
#print axioms singularSquareBound_of_periodicOn_orbit
#print axioms matchesCompletion_self
#print axioms singularSquareBound_completion
#print axioms completion_periodicOn
#print axioms descentCentre_unique
#print axioms descentCentre_unique_of_matches
#print axioms descentWindow_singularSquareBound
#print axioms singularSquareCertificate_of_descentWindowMatch
#print axioms DescentWindowMatch.ofPeriodic

end

end Erdos260
