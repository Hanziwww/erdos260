import Erdos260.GeomDetectConstruction
import Erdos260.RunDescentConstruction

/-!
# Package realization: the two structural realization facts isolated by the obstruction/run workers

This file (new; it edits no existing file) discharges, *as far as the existing definitions
allow*, the two **structural realization** primitives that the obstruction-detection
(`GeomDetectConstruction.lean`) and run-descent (`RunDescentConstruction.lean`) constructions
isolated.  These facts are about **how** the lift/obstruction states are *constructed*, not
the deep K/L/N/§25.2 geometry.

## TARGET 1 — geomDetect coverage (the markers are total on PKG-exits)

`GeomDetectConstruction.lean` reduced the obstruction geometry to a six-marker priority scan
`CNLPackageMarkers.labelOf` and a single coverage residual `pkg_marked` ("every classifier-
flagged package exit fires a marker").  We make the *structure* of that coverage explicit:

* `CNLPackageMarkers.labelOf_isSome_iff_anyMarker` — **the priority scan is total at a state
  iff some marker fires** (the converse of `labelOf_isSome_of_any`, NEW).  So the six-marker
  scan, unlike the seven-class J.1.1 scan, has *no* free catch-all: its totality is exactly
  the coverage residual.
* `CNLPackageMarkers.j11Scan_isSome_of_toRouting` — **the seven-class J.1.1 scan is total for
  free**, because the CleanCNL catch-all (class `1`) is always present
  (`j11Scan_isSome_of_one_mem ∘ toRouting_cleanCNL_mem`).  This isolates *why* the seven-class
  scan is free while the six-marker scan is not.
* `CNLPackageMarkers.labelOf_isSome_of_pkg_exit` — **`labelOf` is total on every PKG-verdict
  state**, PROVED for *any* `CNLPackageMarkers` from its `pkg_marked` field.
* `CNLPackageMarkers.labelOf_total_on_pkg_iff_pkgCovered` — totality on PKG-exits is *exactly
  equivalent* to the single-Boolean coverage `PkgCovered`; this pins the smallest residual.
* `CNLPackageMarkers.pkg_exit_classify_ne_one` / `pkg_exit_classify_eq_scanned_charge` — a
  PKG-verdict state is routed by the J.1.1 first-obstruction scan to a *genuine package charge*
  (`≠ 1`), namely the charge of its scanned marker.

**Verdict (TARGET 1): CLOSED relative to the `CNLPackageMarkers` interface.**  Totality on
PKG-exits, the genuine-package landing, and the routing-pinning are all proved.  The irreducible
input is the structure's own `pkg_marked` coverage field — the smallest K/L/N primitive (there
is deliberately no catch-all package, so coverage cannot be derived from bare lift-state data).

## TARGET 2 — run realization (the mean-low premise from the L.4.1 verdict)

`RunDescentConstruction.lean` proved the L.4.2 one-step half-decrease
`run_period_halfDecrease_of_smallDenom` from §25.2 + Fine–Wilf, leaving the geometric-
realization premises `hold`/`hMeanLow`/`hbp_le_old`/`hoverlap`.  We **peel `hMeanLow` off**:

* `classify_eq_zero_iff` — the L.4.1 trichotomy's mean-low branch is exactly its
  `isLowDensity` discriminant.
* `MeanLowRunWindow` — bundles the §25.2 dyadic small-denominator realization data, defining
  its run state's `isLowDensity` discriminant *by the actual segment density test*
  `segmentSum (dyadicDigit q₀ a) u N < c₀p`.
* `MeanLowRunWindow.hMeanLow_of_verdict` — **the §25.2 mean-low premise is DERIVED from the
  L.4.1 mean-low verdict** (`classify = 0`), with no extra hypothesis.
* `MeanLowRunWindow.halfDecrease_of_meanLow_verdict` — **the one-step half-decrease, with
  `hMeanLow` derived from the verdict and `hNlen` derived from `hoverlap`**.  Only the
  geometric-realization fields remain.

**Verdict (TARGET 2): reduced.**  The mean-low premise `hMeanLow` (and the length premise
`hNlen`) are now *derived* from the classifier verdict; the smaller residual is the geometric
realization "the run obstruction *is* a §25.2 mean-low small-denominator dyadic segment with old
period dominating the threshold on a long-enough window" (`MeanLowRunWindow`'s data fields).

No `sorry`, `axiom`, or `admit`.
-/

namespace Erdos260

noncomputable section

/-! ## TARGET 1 — geomDetect coverage: the six-marker scan is total on PKG-exits -/

namespace CNLPackageMarkers

variable (D : CNLPackageMarkers)

/-- The single Boolean "exposes some package" predicate: the disjunction of the six markers.
This is the smallest form of the coverage residual. -/
def anyMarker (s : LiftState) : Bool :=
  D.markProgress s || D.markTower s || D.markDensePack s || D.markReturn s ||
    D.markRun s || D.markOldRes s

/-- `anyMarker` unfolded to the six-way disjunction (the `pkg_marked` shape). -/
theorem anyMarker_iff (s : LiftState) :
    D.anyMarker s = true ↔
      (D.markProgress s = true ∨ D.markTower s = true ∨ D.markDensePack s = true ∨
        D.markReturn s = true ∨ D.markRun s = true ∨ D.markOldRes s = true) := by
  unfold anyMarker
  simp only [Bool.or_eq_true]
  tauto

/-- **The six-marker priority scan is total at a state iff some marker fires.**  The forward
direction is the converse of `labelOf_isSome_of_any`: unlike the seven-class J.1.1 scan (which
carries the CleanCNL catch-all), the six-marker scan returns `none` exactly when no marker
fires, so it has no free totality. -/
theorem labelOf_isSome_iff_anyMarker (s : LiftState) :
    (D.labelOf s).isSome = true ↔ D.anyMarker s = true := by
  unfold labelOf anyMarker
  split_ifs <;> simp_all

/-- **`labelOf` is total on every PKG-verdict state** — proved for any `CNLPackageMarkers`
from its `pkg_marked` coverage field. -/
theorem labelOf_isSome_of_pkg_exit {s : LiftState}
    (h : canonicalCNLSelector (D.cnlOf s) = some CNLClass.pkg) :
    (D.labelOf s).isSome = true := by
  obtain ⟨p, hp⟩ := D.labelOf_isSome_of_any s (D.pkg_marked s h)
  rw [hp]; rfl

/-- The smallest TARGET-1 residual, as a single Boolean coverage predicate. -/
def PkgCovered : Prop :=
  ∀ s, canonicalCNLSelector (D.cnlOf s) = some CNLClass.pkg → D.anyMarker s = true

/-- The coverage residual holds for any `CNLPackageMarkers` (its `pkg_marked` field, repackaged
through the single-Boolean `anyMarker`). -/
theorem pkgCovered : D.PkgCovered :=
  fun s h => (D.anyMarker_iff s).2 (D.pkg_marked s h)

/-- **Totality of the six-marker scan on PKG-exits is *exactly* the coverage residual.**  This
pins the smallest residual: it is necessary and sufficient for totality. -/
theorem labelOf_total_on_pkg_iff_pkgCovered :
    (∀ s, canonicalCNLSelector (D.cnlOf s) = some CNLClass.pkg →
        (D.labelOf s).isSome = true) ↔ D.PkgCovered := by
  constructor
  · intro htot s hs
    exact (D.labelOf_isSome_iff_anyMarker s).1 (htot s hs)
  · intro hcov s hs
    exact (D.labelOf_isSome_iff_anyMarker s).2 (hcov s hs)

/-- **The seven-class J.1.1 first-obstruction scan is total for free.**  CleanCNL (class `1`)
is always present in the obstruction profile (`toRouting_cleanCNL_mem`), so
`j11Scan_isSome_of_one_mem` applies — no coverage residual is needed for the seven-class scan,
in contrast to the six-marker scan above. -/
theorem j11Scan_isSome_of_toRouting (config : ℕ → LiftState) (k : ℕ) :
    (j11Scan ((D.toMarking.toObstructionGeometry.toRouting config).obstruction k)).isSome :=
  j11Scan_isSome_of_one_mem
    (D.toMarking.toObstructionGeometry.toRouting_cleanCNL_mem config k)

/-- **A PKG-verdict state is routed to a genuine package class (`≠ CleanCNL`).**  Derived from
the constructed geometry's CleanCNL characterisation, whose hypothesis (`pkg_exposes`) is the
proved consequence of the coverage residual. -/
theorem pkg_exit_classify_ne_one (config : ℕ → LiftState) {k : ℕ}
    (h : canonicalCNLSelector (D.cnlOf (config k)) = some CNLClass.pkg) :
    (D.toMarking.toObstructionGeometry.toRouting config).classify k ≠ 1 := by
  intro hcl
  exact (D.toMarking.toObstructionGeometry.classify_eq_one_iff config k).1 hcl h

/-- **A PKG-verdict state is routed to its scanned marker's charge.**  Coverage supplies the
marker; `classify_eq_charge_of_label` pins the J.1.1 first-obstruction routing exactly. -/
theorem pkg_exit_classify_eq_scanned_charge (config : ℕ → LiftState) {k : ℕ}
    (h : canonicalCNLSelector (D.cnlOf (config k)) = some CNLClass.pkg) :
    ∃ p : GeomPackage, D.labelOf (config k) = some p ∧
      (D.toMarking.toObstructionGeometry.toRouting config).classify k = p.toCharge := by
  obtain ⟨p, hp⟩ := D.labelOf_isSome_of_any (config k) (D.pkg_marked (config k) h)
  exact ⟨p, hp, D.toMarking.classify_eq_charge_of_label config h hp⟩

end CNLPackageMarkers

/-! ## TARGET 2 — run realization: the §25.2 mean-low premise from the L.4.1 verdict -/

/-- **The L.4.1 trichotomy's mean-low branch is exactly its `isLowDensity` discriminant.**
`classify s = 0` (mean-low) iff `s.isLowDensity = true`.  The other three classes
(`local-spike`, `boundary`, `shortening-chain`) are `1, 2, 3`. -/
theorem classify_eq_zero_iff (s : RunState) :
    classify s = 0 ↔ s.isLowDensity = true := by
  cases hld : s.isLowDensity <;> cases hdb : s.hasDenseBlock <;> cases hbd : s.atBoundary <;>
    simp [classify, hld, hdb, hbd]

/--
**A run obstruction realized as a §25.2 mean-low small-denominator segment.**

This bundles the geometric-realization residual of `run_period_halfDecrease_of_smallDenom`:
the run window genuinely *is* the dyadic digit segment of `a/q₀` (odd small denominator `q₀`),
carrying an old run period `oldPeriod` that dominates the §25.2 threshold `⌊βp/4⌋` on a
long-enough window (`hoverlap`).  The L.4.1 mean-low discriminant `isLowDensity` of its run
state is *defined* by the actual segment density test, so the classifier's mean-low verdict
DERIVES the §25.2 mean-low premise (`hMeanLow_of_verdict`) rather than assuming it.
-/
structure MeanLowRunWindow where
  /-- §25.2 odd small denominator `q₀`. -/
  q0 : ℕ
  /-- The numerator `a`, coprime to `q₀`. -/
  a : ℕ
  /-- Window start. -/
  u : ℕ
  /-- Window length. -/
  N : ℕ
  /-- The §25.2 ones-density threshold `c₀p`. -/
  c0p : ℕ
  /-- The §25.2 period threshold `⌊βp/4⌋`. -/
  betap_div_4 : ℕ
  /-- The old run period `wt(Oᵢ)`. -/
  oldPeriod : ℕ
  /-- The run branch weight (carried for fidelity; unused by the verdict). -/
  weight : ℝ
  /-- RESIDUAL — `q₀ > 1`. -/
  hq0 : 1 < q0
  /-- RESIDUAL — `q₀` odd (after stripping the 2-adic preperiod, §25.2). -/
  hodd : Odd q0
  /-- RESIDUAL — numerator coprime to `q₀`. -/
  hcop : Nat.Coprime a q0
  /-- RESIDUAL — §25.2 sizing `2 q₀ (c₀p+1) ≤ ⌊βp/4⌋(⌊βp/4⌋+1)`. -/
  hsize : 2 * q0 * (c0p + 1) ≤ betap_div_4 * (betap_div_4 + 1)
  /-- RESIDUAL — the run window carries the old period on its dyadic digit word. -/
  hold : PeriodicOn (dyadicDigit q0 a) u N oldPeriod
  /-- RESIDUAL — the old period dominates the §25.2 threshold. -/
  hbp_le_old : betap_div_4 ≤ oldPeriod
  /-- RESIDUAL — the window is long enough for the Fine–Wilf overlap. -/
  hoverlap : oldPeriod + betap_div_4 ≤ N

namespace MeanLowRunWindow

variable (W : MeanLowRunWindow)

/-- The §25.2 ones-density of the window (number of ones in the dyadic digit segment). -/
def density : ℕ := segmentSum (dyadicDigit W.q0 W.a) W.u W.N

/-- The L.4.1 run state of the window: the mean-low discriminant is *defined* by the §25.2
density test `density < c₀p`, so the classifier's mean-low verdict feeds back the §25.2 premise. -/
def toRunState : RunState where
  weight := W.weight
  isLowDensity := decide (W.density < W.c0p)
  hasDenseBlock := false
  atBoundary := false

@[simp] theorem toRunState_isLowDensity :
    W.toRunState.isLowDensity = decide (W.density < W.c0p) := rfl

/-- **The L.4.1 mean-low verdict (`classify = 0`) holds iff the window is genuinely §25.2
mean-low** (segment density below `c₀p`). -/
theorem meanLow_verdict_iff :
    classify W.toRunState = 0 ↔ W.density < W.c0p := by
  rw [classify_eq_zero_iff, toRunState_isLowDensity]
  simp

/-- **The §25.2 mean-low premise, DERIVED from the L.4.1 mean-low verdict.**  The classifier's
mean-low branch supplies `segmentSum (dyadicDigit q₀ a) u N < c₀p` for free — no extra
hypothesis. -/
theorem hMeanLow_of_verdict (h : classify W.toRunState = 0) :
    W.density < W.c0p :=
  (W.meanLow_verdict_iff).1 h

/--
**One-step period half-decrease for a mean-low run window (L.4.2 via §25.2 + Fine–Wilf).**

Given the L.4.1 mean-low verdict (`classify W.toRunState = 0`), every premise of
`run_period_halfDecrease_of_smallDenom` is met — the mean-low premise `hMeanLow` is DERIVED
from the verdict (`hMeanLow_of_verdict`), the length premise `hNlen` is DERIVED from `hoverlap`,
and the rest are the isolated geometric-realization fields — so §25.2 + Fine–Wilf produces a
strictly shorter period `p'` with `2·p' ≤ oldPeriod` (the manuscript's `wt(O_{i+1}) ≤ wt(Oᵢ)/2`).
-/
theorem halfDecrease_of_meanLow_verdict (h : classify W.toRunState = 0) :
    ∃ p', PeriodicOn (dyadicDigit W.q0 W.a) W.u W.N p' ∧ 0 < p' ∧ 2 * p' ≤ W.oldPeriod := by
  have hNlen : W.betap_div_4 ≤ W.N :=
    le_trans (Nat.le_add_left W.betap_div_4 W.oldPeriod) W.hoverlap
  have hML : segmentSum (dyadicDigit W.q0 W.a) W.u W.N < W.c0p := W.hMeanLow_of_verdict h
  exact run_period_halfDecrease_of_smallDenom W.hq0 W.hodd W.hcop hNlen W.hsize
    W.hold hML W.hbp_le_old W.hoverlap

end MeanLowRunWindow

/-! ### Non-vacuity: the realization data is inhabited -/

private theorem orderOf_two_zmod3_pos : 0 < orderOf (2 : ZMod 3) :=
  orderOf_pos_iff.mpr (isOfFinOrder_two_zmod (by norm_num) (by decide))

private theorem orderOf_two_zmod3_ge_two : 2 ≤ orderOf (2 : ZMod 3) := by
  have hne : orderOf (2 : ZMod 3) ≠ 1 := by
    intro he
    exact absurd (orderOf_eq_one_iff.mp he) (by decide)
  have hpos := orderOf_two_zmod3_pos
  omega

/-- A concrete `MeanLowRunWindow` over the dyadic digit word of `1/3`, witnessing that the
geometric-realization data is inhabited (its mean-low verdict is the residual realization). -/
def meanLowRunWindowWitness : MeanLowRunWindow where
  q0 := 3
  a := 1
  u := 0
  N := 3 * orderOf (2 : ZMod 3)
  c0p := 0
  betap_div_4 := orderOf (2 : ZMod 3)
  oldPeriod := orderOf (2 : ZMod 3)
  weight := 0
  hq0 := by norm_num
  hodd := by decide
  hcop := Nat.coprime_one_left 3
  hsize := by
    have ht2 : 2 ≤ orderOf (2 : ZMod 3) := orderOf_two_zmod3_ge_two
    have h : 2 * 3 ≤ orderOf (2 : ZMod 3) * (orderOf (2 : ZMod 3) + 1) :=
      Nat.mul_le_mul ht2 (by omega)
    omega
  hold := ⟨orderOf_two_zmod3_pos, fun i _ => dyadicDigit_period 3 1 (0 + i)⟩
  hbp_le_old := le_refl _
  hoverlap := by
    have hpos := orderOf_two_zmod3_pos
    omega

theorem meanLowRunWindow_nonempty : Nonempty MeanLowRunWindow :=
  ⟨meanLowRunWindowWitness⟩

/-! ## Residual inventory (honest) -/

/-- The smallest residual primitives remaining after this round, per target. -/
def packageRealizationResiduals : List String :=
  [ "TARGET 1 (CLOSED rel. interface): six-marker coverage `CNLPackageMarkers.pkg_marked` " ++
      "— every PKG-verdict state fires a marker (no catch-all package; the smallest K/L/N " ++
      "coverage primitive). The seven-class J.1.1 scan totality is free.",
    "TARGET 2 (reduced): geometric realization `MeanLowRunWindow` data — the run obstruction " ++
      "IS a §25.2 mean-low small-denominator dyadic segment with old period dominating the " ++
      "threshold on a long-enough window (hq0/hodd/hcop/hsize/hold/hbp_le_old/hoverlap). " ++
      "The mean-low premise hMeanLow and the length premise hNlen are now DERIVED." ]

theorem packageRealizationResiduals_nonempty : packageRealizationResiduals ≠ [] := by
  simp [packageRealizationResiduals]

end

end Erdos260
