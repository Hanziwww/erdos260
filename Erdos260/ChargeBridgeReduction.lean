import Mathlib
import Erdos260.HighExcessChargeFactory
import Erdos260.AppendixI_PhaseMass

/-!
# Charge-bridge reduction to a priority routing (Phase D0)

The central charge bridge `highExcessMass ≤ ClosurePhaseMass`
(`HighExcessChargeFactory.HighExcessChargeData.highExcess_le_phaseMass`) is the
single deepest obligation of the whole development.  This file isolates its
*faithful summation skeleton* from its *dynamical content*.

A **routing** `route : ℕ → Fin 6` assigns each high-excess start to one of the
six phase classes (DensePack / Chernoff-progress / Return-endpoint / clean-CNL /
Tower-bdd / Run, in the manuscript's J.1.1 priority partition).  We prove,
unconditionally, the **mass-conservation identity**

`highExcessMass(highExcessStarts …) = ∑_{i : Fin 6} routedClassMass route i`

(a finite-partition identity that holds for *any* routing — `Finset.sum_fiberwise`),
and deduce that the charge bridge follows once each routed class mass is bounded
by the matching phase-mass term (`termChernoff`, …, `termRun`).

This converts the monolithic `highExcess_le_phaseMass` into the **minimal honest
obligations**: *exhibit the priority routing and prove the six per-class mass
bounds*.  Those six bounds are precisely the manuscript's J.1.1 partition + the
L.2 / N.3.3 per-class estimates (the family/transcript dynamics), which remain
the deep content.  No `sorry`/`axiom` is used; only the summation is proved here.
-/

namespace Erdos260

open Finset

noncomputable section

/-- The high-excess mass routed to phase class `i` (of six): the window-excess
mass of the high-excess starts assigned to class `i` by `route`. -/
def routedClassMass {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr) (route : Nat → Fin 6) (i : Fin 6) : ℝ :=
  ∑ k ∈ (highExcessStarts carryData.starts (hitGap carryData.a)
        carryData.r carryData.T carryData.Y).filter (fun k => route k = i),
    windowExcess (hitGap carryData.a) k carryData.r carryData.T

/-- **Mass conservation (J.1.1 priority partition, faithful).**

Any routing of the high-excess starts into six classes conserves the high-excess
mass: the sum of the six routed class masses equals the total high-excess mass.
This is the finite-partition identity underlying the manuscript's priority
decomposition; it holds for an *arbitrary* routing (no dynamics required), and is
the conservation half of Phase D1. -/
theorem highExcessMass_eq_sum_routedClassMass
    {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr) (route : Nat → Fin 6) :
    highExcessMass (highExcessStarts carryData.starts (hitGap carryData.a)
        carryData.r carryData.T carryData.Y)
        (hitGap carryData.a) carryData.r carryData.T
      = ∑ i : Fin 6, routedClassMass carryData route i := by
  simp only [highExcessMass, routedClassMass]
  exact (Finset.sum_fiberwise _ route _).symm

/-- **J.1.1 partition, disjointness (faithful).**  Distinct routing classes own
disjoint high-excess starts.  A routing is a total function, so its class fibres
are automatically disjoint - the faithful Lean form of the manuscript's
"single-valued priority scan". -/
theorem routedClass_disjoint
    {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr) (route : Nat → Fin 6)
    {i j : Fin 6} (hij : i ≠ j) :
    Disjoint
      ((highExcessStarts carryData.starts (hitGap carryData.a)
          carryData.r carryData.T carryData.Y).filter (fun k => route k = i))
      ((highExcessStarts carryData.starts (hitGap carryData.a)
          carryData.r carryData.T carryData.Y).filter (fun k => route k = j)) := by
  rw [Finset.disjoint_left]
  intro k hki hkj
  rw [Finset.mem_filter] at hki hkj
  exact hij (hki.2.symm.trans hkj.2)

/-- **J.1.1 partition, exhaustiveness (faithful).**  Every high-excess start lies
in some routing class: the six class fibres cover all high-excess starts.  This
is the manuscript's "exhaustive partition" of the priority scan. -/
theorem routedClass_biUnion
    {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr) (route : Nat → Fin 6) :
    ((Finset.univ : Finset (Fin 6)).biUnion
      (fun i => (highExcessStarts carryData.starts (hitGap carryData.a)
          carryData.r carryData.T carryData.Y).filter (fun k => route k = i)))
      = highExcessStarts carryData.starts (hitGap carryData.a)
          carryData.r carryData.T carryData.Y := by
  ext k
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, hk, _⟩; exact hk
  · intro hk; exact ⟨route k, hk, rfl⟩

/-- **Routed high-excess charge data (faithful charge-bridge reduction).**

A priority routing of the high-excess starts into the six phase classes whose
routed class masses are each dominated by the matching phase-mass term.  This is
the minimal faithful contract that discharges the central charge bridge: the
routing and the six per-class bounds are exactly the manuscript J.1.1 partition
plus the L.2 / N.3.3 per-class estimates. -/
structure RoutedHighExcessChargeData
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr) where
  /-- Priority routing of each high-excess start to one of the six classes. -/
  route : Nat → Fin 6
  /-- Class 0 — Chernoff high-cost / progress mass. -/
  hChernoff : routedClassMass carryData route 0 ≤ termChernoff phases.toClosurePhaseData
  /-- Class 1 — clean-CNL Kraft tail. -/
  hCnl : routedClassMass carryData route 1 ≤ termCnl phases.toClosurePhaseData
  /-- Class 2 — bounded transient tower exits. -/
  hTower : routedClassMass carryData route 2 ≤ termTower phases.toClosurePhaseData
  /-- Class 3 — DensePack marker mass. -/
  hDensePack : routedClassMass carryData route 3 ≤ termDensePack phases.toClosurePhaseData
  /-- Class 4 — return / endpoint / OLC leakage. -/
  hReturn : routedClassMass carryData route 4 ≤ termReturn phases.toClosurePhaseData
  /-- Class 5 — run / variation-drop mass. -/
  hRun : routedClassMass carryData route 5 ≤ termRun phases.toClosurePhaseData

/-- **Charge bridge from a routing.**  A `RoutedHighExcessChargeData` discharges
the central bridge `highExcessMass ≤ ClosurePhaseMass`, by mass conservation plus
the six per-class bounds.  The summation is fully proved; only the routing and
the per-class bounds (the family/transcript dynamics) are inputs. -/
def RoutedHighExcessChargeData.toHighExcessChargeData
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ)}
    {carryData : CarryDataFromFailure shell cPr}
    (data : RoutedHighExcessChargeData phases carryData) :
    HighExcessChargeData phases carryData where
  highExcess_le_phaseMass := by
    rw [highExcessMass_eq_sum_routedClassMass carryData data.route, Fin.sum_univ_six]
    exact sum_le_phaseMass_of_termBounds phases.toClosurePhaseData
      data.hChernoff data.hCnl data.hTower data.hDensePack data.hReturn data.hRun

/-- **Routed high-excess charge data — same-threshold (TRT) joint form (faithful).**

A WEAKER, audit-corrected variant of `RoutedHighExcessChargeData`.

**Audit finding (manuscript soundness review).**  The six per-class mass bounds of
`RoutedHighExcessChargeData` are *not* independent in the real proof.  The
Return-endpoint (class 4), Run / variation-drop (class 5) and bounded-Tower-exit
(class 2) classes are *mutually recursive* — a Return charge can re-enter a Tower,
which can spawn a Run, which can again Return — so they are **never bounded
individually**.  They are bounded only **jointly**, by the Appendix-N
*same-threshold* (TRT) compression of Lemma N.24, which collapses the
Tower ↔ Return ↔ Run recursion at one shared threshold and yields the single
combined estimate

`Return + Run + Tower ≤ termTower + termReturn + termRun`.

Only the three non-recursive classes — Chernoff / shell-paid progress (class 0),
clean-CNL (class 1) and DensePack (class 3) — admit *separate* per-class bounds.

Accordingly this contract replaces the three individual hypotheses `hTower`,
`hReturn`, `hRun` of `RoutedHighExcessChargeData` by the single joint TRT bound
`hTRT`.  It is strictly weaker (any data satisfying the six independent bounds
satisfies this one, by adding the Tower/Return/Run bounds), hence it still
faithfully discharges the central charge bridge
`highExcessMass ≤ ClosurePhaseMass`. -/
structure RoutedHighExcessChargeDataTRT
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr) where
  /-- Priority routing of each high-excess start to one of the six classes. -/
  route : Nat → Fin 6
  /-- Class 0 — Chernoff high-cost / progress mass (separable). -/
  hChernoff : routedClassMass carryData route 0 ≤ termChernoff phases.toClosurePhaseData
  /-- Class 1 — clean-CNL Kraft tail (separable). -/
  hCnl : routedClassMass carryData route 1 ≤ termCnl phases.toClosurePhaseData
  /-- Class 3 — DensePack marker mass (separable). -/
  hDensePack : routedClassMass carryData route 3 ≤ termDensePack phases.toClosurePhaseData
  /-- Classes 2 + 4 + 5 — Tower + Return + Run, bounded **jointly** by the
  Appendix-N same-threshold (TRT) compression (Lemma N.24).  These three classes
  are mutually recursive and are never summed individually. -/
  hTRT : routedClassMass carryData route 2 + routedClassMass carryData route 4
        + routedClassMass carryData route 5
      ≤ termTower phases.toClosurePhaseData + termReturn phases.toClosurePhaseData
        + termRun phases.toClosurePhaseData

/-- **Charge bridge from a TRT routing (faithful summation).**  A
`RoutedHighExcessChargeDataTRT` discharges the central bridge
`highExcessMass ≤ ClosurePhaseMass`, by mass conservation
(`highExcessMass_eq_sum_routedClassMass`), the six-term decomposition of the phase
mass (`ClosurePhaseMass_eq_six_terms`), the three separable per-class bounds, and
the single joint Tower+Return+Run (TRT) bound.  The six `routedClassMass` summands
sum to `highExcessMass`, while the four hypotheses bound them by the six phase-mass
terms whose sum is `ClosurePhaseMass`; the residual is closed by `linarith`.  Only
the routing, the three separable bounds, and the joint TRT bound (the manuscript's
N.24 same-threshold compression) are inputs. -/
def RoutedHighExcessChargeDataTRT.toHighExcessChargeData
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ)}
    {carryData : CarryDataFromFailure shell cPr}
    (data : RoutedHighExcessChargeDataTRT phases carryData) :
    HighExcessChargeData phases carryData where
  highExcess_le_phaseMass := by
    rw [highExcessMass_eq_sum_routedClassMass carryData data.route, Fin.sum_univ_six,
      ClosurePhaseMass_eq_six_terms]
    have hChernoff := data.hChernoff
    have hCnl := data.hCnl
    have hDensePack := data.hDensePack
    have hTRT := data.hTRT
    linarith

/-! ## v5 old-residual extension (Lemma L.6.1 trichotomy + Lemmas L.6.4 / L.6.5)

**Manuscript soundness repair (proof_v4 → v5).**  The OLD manuscript closed the
non-DensePack terminal mass with a *dichotomy* (low-residual / shell-paid): every
high-residual fibre was claimed shell-paid, and Lemma L.6.1a/c/e asserted "the
residual multiplier after fixed margins would be bounded by a constant depending
only on `Q`".  That directly contradicted Definition K.1.2, which keeps the
residual multiplier `Y_res = Y_ν − Y_sh` *unbounded by a constant* — only
`Y_res ≤ C_dp·Y = Θ(L)` (K.2b), because the OLD excess may contribute up to
`(1−η)Y` on a new threshold fibre.  An escaping fibre (high old excess
`E_old ≈ (1−η)Y`, so `Y_res > C_Q`, with a single cheap obstruction
`𝔰 = O_Q(1) < c_Q·Y`, and NOT dense — DensePack keys on hit-*density*, not window
height) was neither low-residual nor shell-paid, so it fed the master recurrence
with no smallness factor and the recurrence did not contract.

The v5 fix replaces the dichotomy by a **trichotomy** (Lemma L.6.1, eq. L.10'):
each terminal event fibre is `Ω^low ⊔ Ω^paid ⊔ Ω^oldres`, where
`Ω^oldres = {Y_res > C_Q ∧ 𝔰 < c_Q·Y}` is the new *old-residual* class catching
exactly the escaping fibre.  Its aggregate mass is collected at branch level as
`OldRes_{s,j}(Y)` (Lemma L.6.4, eq. L.15) and added as an explicit term to the
recurrence (eq. I.11': `A ≤ C_η·A* + C_Q·ξ·sX|I_j| + C_Q·OldRes + o`).  Crucially,
`OldRes` is NOT bounded per fibre by a constant; instead Lemma L.6.5 (eq. L.17)
bounds it under the contradictory low-density hypothesis `A_S(2X)−A_S(X) < c_*X`:
the per-fibre multiplier stays `Y_res ≤ C_Q·Y` (eq. L.20), the per-hit-index
endpoint support is `≤ C_Q|I_j|` (eq. L.21, K.1.3A disjointness), and the number
of terminal endpoints is `≤ c_*X + O(rL)` (eq. L.22, the density hypothesis), so
`OldRes ≤ C_Q·c_*·sX|I_j| + o(sX|I_j|)`.  Choosing `c_*` AFTER all other constants
(Convention "Constants, threshold ladder, and order of quantifiers") absorbs it
below the pressure floor.  This is the *same* mechanism already used for DensePack
(Lemma I.4.1): a multiplier linear in `Y` times a low-density-bounded branch count.

This section reflects that repair faithfully:

* `routedClassMassOf` / `highExcessMass_eq_sum_routedClassMassOf` — the routing
  conservation identity for an *arbitrary* finite routing target (here `Fin 7`).
* `RoutedHighExcessChargeDataOldRes` — the v5 **seven-class** routing: the three
  separable phase classes (Chernoff / CNL / DensePack), the joint Tower+Return+Run
  TRT bound (N.24), and the new **old-residual** seventh class bounded by
  `oldResMass`.  It discharges the *augmented* bridge
  `highExcessMass ≤ ClosurePhaseMass + oldResMass` — faithfully the extra `+OldRes`
  term of recurrence I.11'.
* `RoutedHighExcessChargeDataOldRes.toHighExcessChargeData_of_oldRes_nonpos` — when
  no old-residual mass leaks (`oldResMass ≤ 0`) the augmented bridge collapses to
  the original `highExcessMass ≤ ClosurePhaseMass`.
* `oldRes_le_of_density` (Lemma L.6.5 core) and `oldRes_le_lowDensityWindow` — the
  density-sensitive support estimate: smallness carried by the endpoint *count*,
  the multiplier kept linear in `Y` (K.1.2-consistent, no false constant bound).
* `highExcess_le_phaseMass_add_smallOldRes` — the capstone: the seven-class routing
  plus Lemma L.6.5 gives `highExcessMass ≤ ClosurePhaseMass + (c_*X + collar)·bound`.

No `sorry`/`axiom`; only the summation and the support arithmetic are proved here,
exactly as in the rest of this file.  The per-index multiplier bound (L.20), the
per-index endpoint support (L.21), and the low-density endpoint count (L.22) remain
the genuine analytic inputs, supplied as hypotheses. -/

/-- The high-excess mass routed to class `i` for an **arbitrary** finite routing
target `ι`.  Generalizes `routedClassMass` (the `ι = Fin 6` case) so the v5
seven-class routing can reuse the same conservation identity. -/
def routedClassMassOf {shell : FailingDyadicShell} {cPr : ℝ} {ι : Type*} [DecidableEq ι]
    (carryData : CarryDataFromFailure shell cPr) (route : Nat → ι) (i : ι) : ℝ :=
  ∑ k ∈ (highExcessStarts carryData.starts (hitGap carryData.a)
        carryData.r carryData.T carryData.Y).filter (fun k => route k = i),
    windowExcess (hitGap carryData.a) k carryData.r carryData.T

/-- `routedClassMassOf` agrees with `routedClassMass` on the original six-class
routing — the new general definition is a conservative extension. -/
theorem routedClassMassOf_eq_routedClassMass
    {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr) (route : Nat → Fin 6) (i : Fin 6) :
    routedClassMassOf carryData route i = routedClassMass carryData route i := rfl

/-- Each routed class mass is nonnegative (the window excess is a positive part). -/
theorem routedClassMassOf_nonneg
    {shell : FailingDyadicShell} {cPr : ℝ} {ι : Type*} [DecidableEq ι]
    (carryData : CarryDataFromFailure shell cPr) (route : Nat → ι) (i : ι) :
    0 ≤ routedClassMassOf carryData route i :=
  Finset.sum_nonneg fun _k _ => positivePart_nonneg _

/-- **Mass conservation for an arbitrary finite routing (faithful).**  For any
routing of the high-excess starts into a finite class type `ι`, the sum of the
routed class masses equals the total high-excess mass.  This is `Finset.sum_fiberwise`;
it holds for an arbitrary routing (no dynamics), generalizing
`highExcessMass_eq_sum_routedClassMass`. -/
theorem highExcessMass_eq_sum_routedClassMassOf
    {shell : FailingDyadicShell} {cPr : ℝ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (carryData : CarryDataFromFailure shell cPr) (route : Nat → ι) :
    highExcessMass (highExcessStarts carryData.starts (hitGap carryData.a)
        carryData.r carryData.T carryData.Y)
        (hitGap carryData.a) carryData.r carryData.T
      = ∑ i : ι, routedClassMassOf carryData route i := by
  simp only [highExcessMass, routedClassMassOf]
  exact (Finset.sum_fiberwise _ route _).symm

/-- **Routed high-excess charge data with the v5 old-residual class (faithful).**

The seven-class refinement of `RoutedHighExcessChargeDataTRT` that reflects the v5
Lemma L.6.1 *trichotomy*.  High-excess starts are routed into `Fin 7`:

* `0` — Chernoff / shell-paid progress (separable);
* `1` — clean-CNL Kraft tail (separable);
* `3` — DensePack marker mass (separable);
* `2 + 4 + 5` — Tower + Return + Run, bounded **jointly** by the Appendix-N
  same-threshold (TRT) compression (Lemma N.24, see `RoutedHighExcessChargeDataTRT`);
* `6` — the new **old-residual** class `Ω^oldres` (Lemma L.6.4), the high-residual
  low-cost leakage caught by the trichotomy, bounded by the branch-level mass
  `oldResMass = OldRes_{s,j}(Y)` (estimated by Lemma L.6.5).

It discharges the *augmented* charge bridge
`highExcessMass ≤ ClosurePhaseMass + oldResMass`, faithfully the extra `+C_Q·OldRes`
term of the v5 recurrence I.11'.  When `oldResMass` is genuinely small (Lemma L.6.5)
this still contracts after `c_*` is chosen last. -/
structure RoutedHighExcessChargeDataOldRes
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ))
    (carryData : CarryDataFromFailure shell cPr)
    (oldResMass : ℝ) where
  /-- Priority routing of each high-excess start to one of the seven classes. -/
  route : Nat → Fin 7
  /-- Class 0 — Chernoff high-cost / progress mass (separable). -/
  hChernoff : routedClassMassOf carryData route 0 ≤ termChernoff phases.toClosurePhaseData
  /-- Class 1 — clean-CNL Kraft tail (separable). -/
  hCnl : routedClassMassOf carryData route 1 ≤ termCnl phases.toClosurePhaseData
  /-- Class 3 — DensePack marker mass (separable). -/
  hDensePack : routedClassMassOf carryData route 3 ≤ termDensePack phases.toClosurePhaseData
  /-- Classes 2 + 4 + 5 — Tower + Return + Run, bounded **jointly** by the
  Appendix-N same-threshold (TRT) compression (Lemma N.24). -/
  hTRT : routedClassMassOf carryData route 2 + routedClassMassOf carryData route 4
        + routedClassMassOf carryData route 5
      ≤ termTower phases.toClosurePhaseData + termReturn phases.toClosurePhaseData
        + termRun phases.toClosurePhaseData
  /-- Class 6 — the v5 **old-residual** leakage class `Ω^oldres` (Lemma L.6.4),
  bounded by the branch-level mass `OldRes_{s,j}(Y)` (Lemma L.6.5). -/
  hOldRes : routedClassMassOf carryData route 6 ≤ oldResMass

/-- **Augmented charge bridge from a v5 seven-class routing (faithful summation).**

A `RoutedHighExcessChargeDataOldRes` discharges the augmented bridge
`highExcessMass ≤ ClosurePhaseMass + oldResMass`, by mass conservation over the
seven fibres (`highExcessMass_eq_sum_routedClassMassOf`), the six-term phase-mass
decomposition (`ClosurePhaseMass_eq_six_terms`), the three separable per-class
bounds, the joint Tower+Return+Run (TRT) bound, and the old-residual class bound.
The seven `routedClassMassOf` summands sum to `highExcessMass`, while the five
hypotheses bound them by the six phase-mass terms plus `oldResMass`; `linarith`
closes the residual.  This is exactly the extra `+OldRes` term of recurrence I.11'. -/
theorem RoutedHighExcessChargeDataOldRes.highExcess_le_phaseMass_add_oldRes
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ)}
    {carryData : CarryDataFromFailure shell cPr}
    {oldResMass : ℝ}
    (data : RoutedHighExcessChargeDataOldRes phases carryData oldResMass) :
    highExcessMass (highExcessStarts carryData.starts (hitGap carryData.a)
        carryData.r carryData.T carryData.Y)
        (hitGap carryData.a) carryData.r carryData.T
      ≤ ClosurePhaseMass phases.toClosurePhaseData + oldResMass := by
  rw [highExcessMass_eq_sum_routedClassMassOf carryData data.route, Fin.sum_univ_seven,
    ClosurePhaseMass_eq_six_terms]
  have hChernoff := data.hChernoff
  have hCnl := data.hCnl
  have hDensePack := data.hDensePack
  have hTRT := data.hTRT
  have hOldRes := data.hOldRes
  linarith

/-- **Recovery of the original bridge when no old-residual mass leaks.**

If the old-residual class carries no mass (`oldResMass ≤ 0`), the augmented bridge
collapses to the original `highExcessMass ≤ ClosurePhaseMass`, i.e. a genuine
`HighExcessChargeData`.  This is the degenerate case in which every terminal fibre
is low-residual or shell-paid (the OLD manuscript's implicit assumption); the v5
trichotomy reduces to the dichotomy and the original argument goes through. -/
def RoutedHighExcessChargeDataOldRes.toHighExcessChargeData_of_oldRes_nonpos
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ)}
    {carryData : CarryDataFromFailure shell cPr}
    {oldResMass : ℝ}
    (data : RoutedHighExcessChargeDataOldRes phases carryData oldResMass)
    (holdRes : oldResMass ≤ 0) :
    HighExcessChargeData phases carryData where
  highExcess_le_phaseMass := by
    have h := data.highExcess_le_phaseMass_add_oldRes
    linarith

/-- **Lemma L.6.5 — density-sensitive old-residual support estimate (faithful core).**

Models the branch-level old-residual mass `OldRes_{s,j}(Y) = ∑_{k ∈ K} oldResAt k`
of Lemma L.6.4, where `K` is the set of retained terminal hit indices and `oldResAt k`
is the old-residual mass charged at index `k`.  On each retained index the manuscript
gives two bounds:

* the residual multiplier is `Y_res ≤ Cres·Y` (eq. L.20) — **linear in the active
  floor `Y`, NOT an absolute constant**.  This is the K.1.2-consistent bound and the
  entire point of the v5 trichotomy: no false `O_Q(1)` bound is asserted;
* the endpoint/carry support is `∫ μ_T(Ω^oldres) ≤ Csupp·Ij` (eq. L.21, from the
  K.1.3A bin-summed endpoint disjointness),

so `oldResAt k ≤ (Cres·Y)·(Csupp·Ij)`; and the number of terminal hit indices obeys
`|K| ≤ Nendpoints` (eq. L.22).  The conclusion is the L.17 product bound
`OldRes ≤ Nendpoints · (Cres·Y)·(Csupp·Ij)`.

**The smallness is carried entirely by the endpoint count `Nendpoints` (≈ `c_*X`
under the low-density hypothesis), never by a per-fibre constant bound** — exactly
how the v5 fix evades the K.1.2 ↔ L.6.1 contradiction. -/
theorem oldRes_le_of_density {K : Finset ℕ} {oldResAt : ℕ → ℝ}
    {Cres Y Csupp Ij Nendpoints : ℝ}
    (hpoint : ∀ k ∈ K, oldResAt k ≤ (Cres * Y) * (Csupp * Ij))
    (hbound_nonneg : 0 ≤ (Cres * Y) * (Csupp * Ij))
    (hcard : (K.card : ℝ) ≤ Nendpoints) :
    (∑ k ∈ K, oldResAt k) ≤ Nendpoints * ((Cres * Y) * (Csupp * Ij)) := by
  calc
    (∑ k ∈ K, oldResAt k) ≤ ∑ _k ∈ K, (Cres * Y) * (Csupp * Ij) := Finset.sum_le_sum hpoint
    _ = (K.card : ℝ) * ((Cres * Y) * (Csupp * Ij)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Nendpoints * ((Cres * Y) * (Csupp * Ij)) :=
        mul_le_mul_of_nonneg_right hcard hbound_nonneg

/-- **Lemma L.6.5 / eq. L.22 — old-residual under the low-density hypothesis.**

Specializes `oldRes_le_of_density` to the low-density endpoint count
`Nendpoints ≤ c_*·X + collar` (eq. L.22: `#{k : a_k ∈ [X−CrL, 2X+CrL]} ≤ c_*X + O(rL)`
under `A_S(2X)−A_S(X) < c_*X`, the `collar = O(rL)` being the harmless boundary band).
This yields the L.17 split into the genuinely-small main term `c_*·X·bound` and the
`o(sX|I_j|)` collar term `collar·bound`.  Because the per-index `bound = (Cres·Y)·(Csupp·Ij)`
keeps the multiplier linear in `Y ≍ s`, the main term is the manuscript's
`C_Q·c_*·sX|I_j|`. -/
theorem oldRes_le_lowDensityWindow {K : Finset ℕ} {oldResAt : ℕ → ℝ}
    {Cres Y Csupp Ij cStar X collar : ℝ}
    (hpoint : ∀ k ∈ K, oldResAt k ≤ (Cres * Y) * (Csupp * Ij))
    (hbound_nonneg : 0 ≤ (Cres * Y) * (Csupp * Ij))
    (hcard : (K.card : ℝ) ≤ cStar * X + collar) :
    (∑ k ∈ K, oldResAt k)
      ≤ cStar * X * ((Cres * Y) * (Csupp * Ij)) + collar * ((Cres * Y) * (Csupp * Ij)) := by
  have h := oldRes_le_of_density hpoint hbound_nonneg hcard
  nlinarith [h]

/-- **Capstone — augmented bridge with the v5 old-residual term made small.**

Combines the seven-class routing (`RoutedHighExcessChargeDataOldRes`) with the
density-sensitive estimate (`oldRes_le_lowDensityWindow`).  Given the routing, the
identification of `oldResMass` as the branch-level sum `∑_{k ∈ K} oldResAt k`
(Lemma L.6.4), and the L.6.5 inputs (per-index multiplier × support bound and the
low-density endpoint count), the high-excess mass obeys

`highExcessMass ≤ ClosurePhaseMass + (c_*·X·bound + collar·bound)`,

i.e. the phase mass plus a genuinely small (∝ `c_*`) old-residual term, exactly the
v5 recurrence I.11' specialized by Lemma L.6.5.  Choosing `c_*` after the other
constants drives the extra term below the pressure floor. -/
theorem RoutedHighExcessChargeDataOldRes.highExcess_le_phaseMass_add_smallOldRes
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : ℝ)}
    {carryData : CarryDataFromFailure shell cPr}
    {oldResMass : ℝ}
    (data : RoutedHighExcessChargeDataOldRes phases carryData oldResMass)
    {K : Finset ℕ} {oldResAt : ℕ → ℝ}
    {Cres Y Csupp Ij cStarD X collar : ℝ}
    (holdResMass : oldResMass = ∑ k ∈ K, oldResAt k)
    (hpoint : ∀ k ∈ K, oldResAt k ≤ (Cres * Y) * (Csupp * Ij))
    (hbound_nonneg : 0 ≤ (Cres * Y) * (Csupp * Ij))
    (hcard : (K.card : ℝ) ≤ cStarD * X + collar) :
    highExcessMass (highExcessStarts carryData.starts (hitGap carryData.a)
        carryData.r carryData.T carryData.Y)
        (hitGap carryData.a) carryData.r carryData.T
      ≤ ClosurePhaseMass phases.toClosurePhaseData
        + (cStarD * X * ((Cres * Y) * (Csupp * Ij))
            + collar * ((Cres * Y) * (Csupp * Ij))) := by
  have hbridge := data.highExcess_le_phaseMass_add_oldRes
  have hsmall := oldRes_le_lowDensityWindow hpoint hbound_nonneg hcard
  rw [holdResMass] at hbridge
  linarith

end

end Erdos260
