import Erdos260.RhoDQFinalConsumerBridgeCore
import Erdos260.DescentDepthAgreementCore
import Erdos260.DirtyCrossingCylinderCore

/-!
# Q-correct (rho_D(q0) = 1/(4 q0)) drop-in analogues of the pinned density-precursor consumers

`RhoDQCalibrationCore` / `RhoDQFrontierDischargeCore` / `RhoDQFinalConsumerBridgeCore` (the wave-23/24
cores) proved the genuine Q-dependent dense-marker density floor `rhoDQ q0 = 1/(4 q0)`, its
calibration `rhoDQ q0 <= 1/(3 q0)` for every `q0`, the matched-window atom on the actual word, and the
frontier-shaped discharge `frontierDensityDischarge_rhoDQ`.  They left the global
`Erdos260.Constants.manuscriptRhoD = 1/4` untouched (the `Q = 1` representative).

This module (NEW; it edits no existing file, and does not change `manuscriptRhoD`) finishes the wiring:
it produces Q-correct drop-in analogues of the remaining pinned precursor CONSUMER types -- the
structures and definitions that still hard-code `manuscriptRhoD` in a density field -- and composes
them with `frontierDensityDischarge_rhoDQ` so the density atoms used along the actual-shell path are
honest for every `Q` (not just `q0 = 1`).

Each pinned precursor either is parametric in the rate (then we supply the `rhoDQ` instance) or
hard-codes `manuscriptRhoD` (then we add a parallel rate-generic type with the pinned one as the
`manuscriptRhoD` instance, plus a `rhoDQ` constructor -- never mutating the pinned one).  A projection
lemma in each case exhibits the pinned precursor as the `manuscriptRhoD` instance of the new analogue.

## What is genuinely PROVED here (no `sorry`/`axiom`/`admit`/`native_decide`)

* (1) `MatchedSemiperiodicWindow.hdens`/`.ofDyadicMatch`: `MatchedSemiperiodicWindowAt rho` is the
  rate-generic packet (derived `periodicOn`/`windowWeight_period_ge`/`windowWeight_ge`);
  `MatchedSemiperiodicWindow.toAt` projects the pinned one to the `manuscriptRhoD` instance;
  `ofDyadicMatch`/`ofDyadicMatchRhoDQ` ground it from a 25.1 match.
* (2) `matchedWindow_of_descentMatch` (its `hcal`): `matchedWindowRhoDQ_of_descentMatch` produces the
  matched window at rate `rhoDQ q0` with NO `hcal` (`manuscriptRhoD <= 1/(3 q0)` is false for q0 >= 2).
* (3) `DescentCylinderMatchData.hdens`/`descentCylinderMatchData_canonical`:
  `DescentCylinderMatchDataAt rho` rate-generic; `.toAt` projection; `..._rhoDQ_canonical` constructor;
  `MatchedDescentWindowsAt rho` + `matchedDescentWindowsAt_of_cylinderMatchDataAt`.
* (4) `SingularSquareCertificate.hdens`: `SingularSquareCertificateAt rho` rate-generic; `.toAt`
  projection; `..._rhoDQ_ofDescentWindowMatch` constructor; rate-free cylinder reduction at rate rho.
* (5) `proofV4DensePackMinHits = floor(manuscriptRhoD*L)`: `proofV4DensePackMinHitsRhoDQ` +
  `..._le_pinned`; `densePackEndpointDensityRhoDQ` + `..._of_pinned` / `..._of_descentWindowMatch` /
  `..._of_matchedDescentWindowsAt`.
* (6) `Class2IndexSDR.ofSemiperiodicDensity` / `Class2AreaPacking.floor`: the SDR chain is
  rate-parametric (the `rhoDQ` instance is `Class2IndexSDR.ofDyadicMatchesRhoDQ`);
  `Class2IndexSDR.toAreaPacking` (+ `toAreaPacking_floor`) exposes the area-packing floor route.
* (7) `rhoDQ_precursorConsumers_of_descentWindowMatch` composes all of the above from one
  `DescentWindowMatch ctx`.

`Constants.manuscriptRhoD` is left UNTOUCHED; every existing module still builds.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

namespace Erdos260

open Finset

noncomputable section

set_option linter.unusedVariables false

/-! ## 1.  The rate-generic matched semiperiodic window

`SemiperiodicWindowCore.MatchedSemiperiodicWindow` hard-codes `manuscriptRhoD` in its `hdens` field.
`MatchedSemiperiodicWindowAt rho` is the same packet with the rate exposed as a parameter (and the
nonnegativity `hrho : 0 <= rho` carried), so the pinned packet is exactly its `manuscriptRhoD` instance
(`MatchedSemiperiodicWindow.toAt`) and the `rhoDQ` packet is a sibling instance. -/

/-- **The rate-generic matched semiperiodic window.** -/
structure MatchedSemiperiodicWindowAt (rho : ℝ) (d : ℕ → ℕ) (start len : ℕ) where
  /-- The model orbit word (e.g. `dyadicDigit q0 a`). -/
  w : ℕ → ℕ
  /-- The (bounded primitive) period. -/
  period : ℕ
  /-- The period is positive. -/
  hperiod_pos : 0 < period
  /-- The period fits inside the window. -/
  hperiod_le : period ≤ len
  /-- The model word is `PeriodicOn` the window with this period. -/
  hper : PeriodicOn w 0 len period
  /-- The rate is nonnegative. -/
  hrho : 0 ≤ rho
  /-- The period density is at least `rho` (the section-24 floor at rate `rho`). -/
  hdens : rho * (period : ℝ) ≤ (windowWeight w 0 period : ℝ)
  /-- **The 25.1 match** -- the actual word is the orbit word here. -/
  hmatch : WindowMatch d w start len

namespace MatchedSemiperiodicWindowAt

variable {rho : ℝ} {d : ℕ → ℕ} {start len : ℕ}

/-- **The actual descent window is genuinely `PeriodicOn`** -- derived from the match. -/
theorem periodicOn (W : MatchedSemiperiodicWindowAt rho d start len) :
    PeriodicOn d start len W.period :=
  periodicOn_of_match W.hmatch W.hper

/-- **The actual descent window carries the rate-`rho` density floor.** -/
theorem windowWeight_period_ge (W : MatchedSemiperiodicWindowAt rho d start len) :
    rho * (W.period : ℝ) ≤ (windowWeight d start W.period : ℝ) := by
  rw [windowWeight_congr_of_match W.hmatch W.hperiod_le]
  exact W.hdens

/-- **The shared SDR atom on the actual word at rate `rho`.** -/
theorem windowWeight_ge (W : MatchedSemiperiodicWindowAt rho d start len) {L : ℕ}
    (hlen : L + W.period ≤ len + 1) :
    rho * (L : ℝ) ≤ (windowWeight d start len : ℝ) :=
  windowWeight_ge_floor_mul_L_of_match rho W.hrho W.hperiod_pos W.hmatch W.hper W.hdens W.hperiod_le
    hlen

end MatchedSemiperiodicWindowAt

/-- **The rate-generic grounding on the residual-center orbit word.** -/
def MatchedSemiperiodicWindowAt.ofDyadicMatch {rho : ℝ} {d : ℕ → ℕ} {start len q0 a : ℕ}
    (hq0 : 1 < q0) (hodd : Odd q0) (hrho : 0 ≤ rho)
    (hperiod_le : orderOf (2 : ZMod q0) ≤ len)
    (hdens : rho * ((orderOf (2 : ZMod q0) : ℕ) : ℝ)
        ≤ (windowWeight (dyadicDigit q0 a) 0 (orderOf (2 : ZMod q0)) : ℝ))
    (hmatch : WindowMatch d (dyadicDigit q0 a) start len) :
    MatchedSemiperiodicWindowAt rho d start len where
  w := dyadicDigit q0 a
  period := orderOf (2 : ZMod q0)
  hperiod_pos := orderOf_pos_iff.mpr (isOfFinOrder_two_zmod hq0 hodd)
  hperiod_le := hperiod_le
  hper := by simpa using dyadicDigit_periodicOn_mul hq0 hodd Nat.one_pos a 0 len
  hrho := hrho
  hdens := hdens
  hmatch := hmatch

/-- **The `rhoDQ`-rate grounding from the residual-center orbit word.** -/
def MatchedSemiperiodicWindowAt.ofDyadicMatchRhoDQ {d : ℕ → ℕ} {start len q0 a : ℕ}
    (hq0 : 1 < q0) (hodd : Odd q0) (hcop : Nat.Coprime a q0)
    (hperiod_le : orderOf (2 : ZMod q0) ≤ len)
    (hmatch : WindowMatch d (dyadicDigit q0 a) start len) :
    MatchedSemiperiodicWindowAt (rhoDQ q0) d start len :=
  MatchedSemiperiodicWindowAt.ofDyadicMatch hq0 hodd (rhoDQ_pos (by omega)).le hperiod_le
    (dyadicDigit_density_floor_rhoDQ hq0 hodd hcop) hmatch

/-- **Projection.**  The pinned `MatchedSemiperiodicWindow` is the `manuscriptRhoD` instance. -/
def MatchedSemiperiodicWindow.toAt {d : ℕ → ℕ} {start len : ℕ}
    (W : MatchedSemiperiodicWindow d start len) :
    MatchedSemiperiodicWindowAt manuscriptRhoD d start len where
  w := W.w
  period := W.period
  hperiod_pos := W.hperiod_pos
  hperiod_le := W.hperiod_le
  hper := W.hper
  hrho := manuscriptRhoD_pos.le
  hdens := W.hdens
  hmatch := W.hmatch

/-! ## 2.  `matchedWindow_of_descentMatch` without the (`q0 = 1`-only) `hcal` -/

/-- **The `matchedWindow_of_descentMatch` analogue at rate `rhoDQ q0`, no `hcal`.** -/
def matchedWindowRhoDQ_of_descentMatch {d : ℕ → ℕ} {start len q0 a : ℕ}
    (hq0 : 1 < q0) (hodd : Odd q0) (hcop : Nat.Coprime a q0)
    (hle : orderOf (2 : ZMod q0) ≤ len)
    (hmatch : WindowMatch d (dyadicDigit q0 a) start len) :
    MatchedSemiperiodicWindowAt (rhoDQ q0) d start len :=
  MatchedSemiperiodicWindowAt.ofDyadicMatchRhoDQ hq0 hodd hcop hle hmatch

/-- The matched-window density atom read off the `rhoDQ` packet (no `hcal`). -/
theorem matchedWindowRhoDQ_windowWeight_ge {d : ℕ → ℕ} {start len L q0 a : ℕ}
    (hq0 : 1 < q0) (hodd : Odd q0) (hcop : Nat.Coprime a q0)
    (hle : orderOf (2 : ZMod q0) ≤ len)
    (hlen : L + orderOf (2 : ZMod q0) ≤ len + 1)
    (hmatch : WindowMatch d (dyadicDigit q0 a) start len) :
    rhoDQ q0 * (L : ℝ) ≤ (windowWeight d start len : ℝ) :=
  (matchedWindowRhoDQ_of_descentMatch hq0 hodd hcop hle hmatch).windowWeight_ge hlen

/-! ## 3.  The rate-generic descent-cylinder match data -/

/-- **The rate-generic 25.1 cylinder-match data.** -/
structure DescentCylinderMatchDataAt (rho : ℝ) (ctx : ActualFailureContext) where
  /-- The reduced odd residual-center denominator. -/
  q0 : ℕ
  /-- The per-start center numerator. -/
  a : ℕ → ℕ
  /-- `q0 > 1`. -/
  hq0 : 1 < q0
  /-- `q0` is odd. -/
  hodd : Odd q0
  /-- The rate is nonnegative. -/
  hrho : 0 ≤ rho
  /-- **(ii) the 25.1 cylinder match** for each genuine start. -/
  hcyl : ∀ k ∈ genuineDensePackStarts ctx,
    DyadicCylinder (proofV4DensePackSpread ctx.shell + 1)
      (windowCylinderValue ctx.shell.d (k + ctx.n24CarryData.r)
        (proofV4DensePackSpread ctx.shell + 1))
      ((a k : ℝ) / (q0 : ℝ))
  /-- The rate-`rho` section-24 period-density floor on the orbit word. -/
  hdens : ∀ k ∈ genuineDensePackStarts ctx,
    rho * (orderOf (2 : ZMod q0) : ℝ)
      ≤ (windowWeight (dyadicDigit q0 (a k)) 0 (orderOf (2 : ZMod q0)) : ℝ)
  /-- The bounded-period calibration. -/
  hpb : Classical.choose ctx.shell.hXdyadic + orderOf (2 : ZMod q0)
      ≤ proofV4DensePackSpread ctx.shell + 2

/-- **Projection.**  The pinned `DescentCylinderMatchData` is the `manuscriptRhoD` instance. -/
def DescentCylinderMatchData.toAt {ctx : ActualFailureContext}
    (data : DescentCylinderMatchData ctx) :
    DescentCylinderMatchDataAt manuscriptRhoD ctx where
  q0 := data.q0
  a := data.a
  hq0 := data.hq0
  hodd := data.hodd
  hrho := manuscriptRhoD_pos.le
  hcyl := data.hcyl
  hdens := data.hdens
  hpb := data.hpb

/-- **The canonical `rhoDQ` cylinder-match data** (analogue of `descentCylinderMatchData_canonical`). -/
def descentCylinderMatchDataAt_rhoDQ_canonical (ctx : ActualFailureContext)
    (a : ℕ → ℕ)
    (hcyl : ∀ k ∈ genuineDensePackStarts ctx,
      DyadicCylinder (proofV4DensePackSpread ctx.shell + 1)
        (windowCylinderValue ctx.shell.d (k + ctx.n24CarryData.r)
          (proofV4DensePackSpread ctx.shell + 1))
        ((a k : ℝ) / ((canonicalCenter ctx).q0 : ℝ)))
    (hcop : ∀ k ∈ genuineDensePackStarts ctx, Nat.Coprime (a k) (canonicalCenter ctx).q0)
    (hpb : Classical.choose ctx.shell.hXdyadic + orderOf (2 : ZMod (canonicalCenter ctx).q0)
        ≤ proofV4DensePackSpread ctx.shell + 2) :
    DescentCylinderMatchDataAt (rhoDQ (canonicalCenter ctx).q0) ctx where
  q0 := (canonicalCenter ctx).q0
  a := a
  hq0 := runFOfShell_q0_gt_one ctx
  hodd := runFOfShell_q0_odd ctx
  hrho := (rhoDQ_pos (canonicalCenter ctx).q0_pos).le
  hcyl := hcyl
  hdens := descentDensityFloor_rhoDQ_all_Q ctx a hcop
  hpb := hpb

/-- **The rate-generic derived matched descent-window family.** -/
def MatchedDescentWindowsAt (rho : ℝ) (ctx : ActualFailureContext) : Prop :=
  ∀ k ∈ genuineDensePackStarts ctx,
    ∃ W : MatchedSemiperiodicWindowAt rho ctx.shell.d (k + ctx.n24CarryData.r)
            (proofV4DensePackSpread ctx.shell + 1),
      Classical.choose ctx.shell.hXdyadic + W.period ≤ proofV4DensePackSpread ctx.shell + 2

/-- **`MatchedDescentWindowsAt` derived from the rate-generic cylinder geometry.** -/
theorem matchedDescentWindowsAt_of_cylinderMatchDataAt {rho : ℝ} (ctx : ActualFailureContext)
    (data : DescentCylinderMatchDataAt rho ctx) : MatchedDescentWindowsAt rho ctx := by
  have hd : ∀ i, ctx.shell.d i ≤ 1 := fun i => by
    rcases ctx.shell.hd i with h | h <;> omega
  have hClen : 1 ≤ Classical.choose ctx.shell.hXdyadic := by
    have := ctx.shell_carryLarge; omega
  have hpb := data.hpb
  intro k hk
  have hmatch : WindowMatch ctx.shell.d (dyadicDigit data.q0 (data.a k))
      (k + ctx.n24CarryData.r) (proofV4DensePackSpread ctx.shell + 1) :=
    windowMatch_dyadicDigit_of_cylinder hd (by have := data.hq0; omega) (data.hcyl k hk)
  exact ⟨MatchedSemiperiodicWindowAt.ofDyadicMatch data.hq0 data.hodd data.hrho (by omega)
    (data.hdens k hk) hmatch, hpb⟩

/-- **Projection.**  The pinned `MatchedDescentWindows` is the `manuscriptRhoD` instance. -/
theorem MatchedDescentWindows.toAt {ctx : ActualFailureContext}
    (h : MatchedDescentWindows ctx) : MatchedDescentWindowsAt manuscriptRhoD ctx := by
  intro k hk
  obtain ⟨W, hW⟩ := h k hk
  exact ⟨W.toAt, hW⟩

/-! ## 4.  The rate-generic singular-square certificate -/

/-- **The rate-generic 25.1 singular-square certificate.** -/
structure SingularSquareCertificateAt (rho : ℝ) (ctx : ActualFailureContext) where
  /-- The per-start residual-center numerator. -/
  a : ℕ → ℕ
  /-- **(D1)** the singular-square residual bound for each genuine descent window. -/
  hbound : ∀ k ∈ genuineDensePackStarts ctx,
    |(windowCylinderValue ctx.shell.d (k + ctx.n24CarryData.r)
          (proofV4DensePackSpread ctx.shell + 1) : ℝ) * ((canonicalCenter ctx).q0 : ℝ)
        - (a k : ℝ) * (2 : ℝ) ^ (proofV4DensePackSpread ctx.shell + 1)|
      * 2 ^ (proofV4DensePackSpread ctx.shell + 1)
    < (2 : ℝ) ^ (proofV4DensePackSpread ctx.shell + 1) * ((canonicalCenter ctx).q0 : ℝ)
  /-- **(D2)** the carry-run routing: `NoLargeRun` excludes the carry adjacency. -/
  hcarry : NoLargeRun ctx → ∀ k ∈ genuineDensePackStarts ctx,
    windowCylinderValue ctx.shell.d (k + ctx.n24CarryData.r)
        (proofV4DensePackSpread ctx.shell + 1)
      ≠ cylinderIndex (proofV4DensePackSpread ctx.shell + 1)
          ((a k : ℝ) / ((canonicalCenter ctx).q0 : ℝ)) + 1
  /-- The rate is nonnegative. -/
  hrho : 0 ≤ rho
  /-- The rate-`rho` section-24 period-density floor on the orbit word. -/
  hdens : ∀ k ∈ genuineDensePackStarts ctx,
    rho * (orderOf (2 : ZMod (canonicalCenter ctx).q0) : ℝ)
      ≤ (windowWeight (dyadicDigit (canonicalCenter ctx).q0 (a k)) 0
          (orderOf (2 : ZMod (canonicalCenter ctx).q0)) : ℝ)
  /-- The bounded-period calibration. -/
  hpb : Classical.choose ctx.shell.hXdyadic + orderOf (2 : ZMod (canonicalCenter ctx).q0)
      ≤ proofV4DensePackSpread ctx.shell + 2

/-- **Projection.**  The pinned `SingularSquareCertificate` is the `manuscriptRhoD` instance. -/
def SingularSquareCertificate.toAt {ctx : ActualFailureContext}
    (cert : SingularSquareCertificate ctx) :
    SingularSquareCertificateAt manuscriptRhoD ctx where
  a := cert.a
  hbound := cert.hbound
  hcarry := cert.hcarry
  hrho := manuscriptRhoD_pos.le
  hdens := cert.hdens
  hpb := cert.hpb

/-- **The `rhoDQ` singular-square certificate from a `DescentWindowMatch`.** -/
def SingularSquareCertificateAt.rhoDQ_ofDescentWindowMatch (ctx : ActualFailureContext)
    (W : DescentWindowMatch ctx)
    (hcop : ∀ k ∈ genuineDensePackStarts ctx, Nat.Coprime (W.a k) (canonicalCenter ctx).q0)
    (hcarry : NoLargeRun ctx → ∀ k ∈ genuineDensePackStarts ctx,
      windowCylinderValue ctx.shell.d (k + ctx.n24CarryData.r)
          (proofV4DensePackSpread ctx.shell + 1)
        ≠ cylinderIndex (proofV4DensePackSpread ctx.shell + 1)
            ((W.a k : ℝ) / ((canonicalCenter ctx).q0 : ℝ)) + 1)
    (hpb : Classical.choose ctx.shell.hXdyadic + orderOf (2 : ZMod (canonicalCenter ctx).q0)
        ≤ proofV4DensePackSpread ctx.shell + 2) :
    SingularSquareCertificateAt (rhoDQ (canonicalCenter ctx).q0) ctx where
  a := W.a
  hbound := descentWindow_singularSquareBound ctx W
  hcarry := hcarry
  hrho := (rhoDQ_pos (canonicalCenter ctx).q0_pos).le
  hdens := singularSquareCertificate_hdens_rhoDQ ctx W hcop
  hpb := hpb

/-- **The rate-generic carry-cylinder reduction.** -/
def descentCylinderMatchDataAt_of_certificateAt {rho : ℝ} (ctx : ActualFailureContext)
    (cert : SingularSquareCertificateAt rho ctx) (hnlr : NoLargeRun ctx) :
    DescentCylinderMatchDataAt rho ctx where
  q0 := (canonicalCenter ctx).q0
  a := cert.a
  hq0 := runFOfShell_q0_gt_one ctx
  hodd := runFOfShell_q0_odd ctx
  hrho := cert.hrho
  hcyl := fun k hk => dyadicCylinder_center_of_singularSquare (canonicalCenter ctx).q0_pos
    (cert.hbound k hk) (cert.hcarry hnlr k hk)
  hdens := cert.hdens
  hpb := cert.hpb

/-- **`MatchedDescentWindowsAt` from the rate-generic certificate.** -/
theorem matchedDescentWindowsAt_of_certificateAt {rho : ℝ} (ctx : ActualFailureContext)
    (hnlr : NoLargeRun ctx) (cert : SingularSquareCertificateAt rho ctx) :
    MatchedDescentWindowsAt rho ctx :=
  matchedDescentWindowsAt_of_cylinderMatchDataAt ctx
    (descentCylinderMatchDataAt_of_certificateAt ctx cert hnlr)

/-! ## 5.  The Q-correct DensePack hit-density floor -/

/-- **The Q-correct DensePack hit-density floor** `floor(rhoDQ q0 * L)`. -/
def proofV4DensePackMinHitsRhoDQ (ctx : ActualFailureContext) : ℕ :=
  Nat.floor (rhoDQ (canonicalCenter ctx).q0 * ((Classical.choose ctx.shell.hXdyadic : ℕ) : ℝ))

/-- The Q-correct floor never exceeds the pinned floor (`rhoDQ q0 <= manuscriptRhoD`). -/
theorem proofV4DensePackMinHitsRhoDQ_le_pinned (ctx : ActualFailureContext) :
    proofV4DensePackMinHitsRhoDQ ctx ≤ proofV4DensePackMinHits ctx.shell := by
  unfold proofV4DensePackMinHitsRhoDQ proofV4DensePackMinHits
  exact Nat.floor_mono
    (mul_le_mul_of_nonneg_right (rhoDQ_le_manuscriptRhoD (canonicalCenter ctx).q0_pos)
      (by positivity))

/-- **The Q-correct coarea hit-density predicate.** -/
def densePackEndpointDensityRhoDQ (ctx : ActualFailureContext) : Prop :=
  ∀ k ∈ genuineDensePackStarts ctx,
    proofV4DensePackMinHitsRhoDQ ctx
      ≤ (proofV4DensePackSupportWindow ctx.shell (k + ctx.n24CarryData.r)).card

/-- **Projection.**  The pinned (`q0 = 1`-only) coarea floor implies the Q-correct one. -/
theorem densePackEndpointDensityRhoDQ_of_pinned (ctx : ActualFailureContext)
    (h : densePackEndpointDensity ctx) : densePackEndpointDensityRhoDQ ctx :=
  fun k hk => le_trans (proofV4DensePackMinHitsRhoDQ_le_pinned ctx) (h k hk)

/-- **Rate-generic coarea floor from a matched window.** -/
theorem densePackMinHitsFloorAt_le_supportWindow {rho : ℝ} (shell : FailingDyadicShell) {m L : ℕ}
    (hlo : shell.X < m)
    (hhi : m + proofV4DensePackSpread shell ≤ 2 * shell.X)
    (W : MatchedSemiperiodicWindowAt rho shell.d m (proofV4DensePackSpread shell + 1))
    (hlen : L + W.period ≤ proofV4DensePackSpread shell + 2) :
    Nat.floor (rho * (L : ℝ)) ≤ (proofV4DensePackSupportWindow shell m).card := by
  have hatom : rho * (L : ℝ)
      ≤ (windowWeight shell.d m (proofV4DensePackSpread shell + 1) : ℝ) :=
    W.windowWeight_ge (by omega)
  have hge0 : (0 : ℝ) ≤ rho * (L : ℝ) := mul_nonneg W.hrho (by positivity)
  have hfloorNat : Nat.floor (rho * (L : ℝ))
      ≤ windowWeight shell.d m (proofV4DensePackSpread shell + 1) := by
    have hcast : (Nat.floor (rho * (L : ℝ)) : ℝ)
        ≤ (windowWeight shell.d m (proofV4DensePackSpread shell + 1) : ℝ) :=
      le_trans (Nat.floor_le hge0) hatom
    exact_mod_cast hcast
  rw [windowWeight_eq_filter_card shell.hd] at hfloorNat
  exact le_trans hfloorNat (windowFilter_card_le_supportWindow shell hlo hhi)

/-- **The Q-correct coarea hit-density from the `rhoDQ` matched descent-window family.** -/
theorem densePackEndpointDensityRhoDQ_of_matchedDescentWindowsAt (ctx : ActualFailureContext)
    (hlo : ∀ k ∈ genuineDensePackStarts ctx, ctx.shell.X < k + ctx.n24CarryData.r)
    (hhi : ∀ k ∈ genuineDensePackStarts ctx,
        (k + ctx.n24CarryData.r) + proofV4DensePackSpread ctx.shell ≤ 2 * ctx.shell.X)
    (h : MatchedDescentWindowsAt (rhoDQ (canonicalCenter ctx).q0) ctx) :
    densePackEndpointDensityRhoDQ ctx := by
  intro k hk
  obtain ⟨W, hlenL⟩ := h k hk
  exact densePackMinHitsFloorAt_le_supportWindow ctx.shell (hlo k hk) (hhi k hk) W hlenL

/-- **The Q-correct coarea hit-density for ALL Q from the lone 25.1 residual.** -/
theorem densePackEndpointDensityRhoDQ_of_descentWindowMatch (ctx : ActualFailureContext)
    (W : DescentWindowMatch ctx)
    (hcop : ∀ k ∈ genuineDensePackStarts ctx, Nat.Coprime (W.a k) (canonicalCenter ctx).q0)
    (hlo : ∀ k ∈ genuineDensePackStarts ctx, ctx.shell.X < k + ctx.n24CarryData.r)
    (hhi : ∀ k ∈ genuineDensePackStarts ctx,
        (k + ctx.n24CarryData.r) + proofV4DensePackSpread ctx.shell ≤ 2 * ctx.shell.X)
    (hpb : Classical.choose ctx.shell.hXdyadic + orderOf (2 : ZMod (canonicalCenter ctx).q0)
        ≤ proofV4DensePackSpread ctx.shell + 2) :
    densePackEndpointDensityRhoDQ ctx :=
  fun k hk =>
    densePackEndpointDensity_rhoDQ_of_descentWindowMatch ctx W hcop hlo hhi (fun _ _ => hpb) k hk

/-! ## 6.  The Tower area-packing floor route at rate `rhoDQ` -/

/-- **The Tower area-packing of a class-2 index SDR** (the `Class2AreaPacking.floor` route). -/
def Class2IndexSDR.toAreaPacking {ctx : ActualFailureContext} (S : Class2IndexSDR ctx) :
    Class2AreaPacking ctx :=
  Class2AreaPacking.ofOwnershipPacking (Class2OwnershipPacking.ofShellSDR S.toShellSDR)

/-- **The area-packing floor is the SDR's own rate times scale.** -/
theorem Class2IndexSDR.toAreaPacking_floor {ctx : ActualFailureContext} (S : Class2IndexSDR ctx) :
    S.toAreaPacking.floor = S.rhoD * S.L := rfl

/-- **Tower Core 3 through the area-packing route.** -/
theorem Class2IndexSDR.toAreaPacking_towerSubMass {ctx : ActualFailureContext}
    (S : Class2IndexSDR ctx) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
      ≤ erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  S.toAreaPacking.htowerSubMass

/-! ## 7.  The composition -- every Q-correct precursor analogue from one descent-window match -/

/-- **The bundle of Q-correct precursor analogues for the actual shell.**  Packages the data-valued
`rhoDQ` singular-square certificate together with the Q-correct coarea hit-density and the (NoLargeRun)
matched descent-window family (a structure is used since the certificate is `Type`-valued, so the three
cannot be combined by `And`). -/
structure RhoDQPrecursorConsumerBundle (ctx : ActualFailureContext) where
  /-- The Q-correct singular-square certificate (analogue of `SingularSquareCertificate`). -/
  cert : SingularSquareCertificateAt (rhoDQ (canonicalCenter ctx).q0) ctx
  /-- The Q-correct coarea hit-density (analogue of `densePackEndpointDensity`), for every `Q`. -/
  endpointDensity : densePackEndpointDensityRhoDQ ctx
  /-- The `rhoDQ` matched descent-window family under `NoLargeRun` (analogue of
  `MatchedDescentWindows`). -/
  matchedWindows : NoLargeRun ctx → MatchedDescentWindowsAt (rhoDQ (canonicalCenter ctx).q0) ctx

/-- **The composed Q-correct precursor discharge.**  A single `DescentWindowMatch ctx` (the lone
irreducible 25.1 residual) + coprimality + shell geometry + the (D2) carry routing yields the whole
`RhoDQPrecursorConsumerBundle ctx`, composing the new precursor analogues with the existing
`frontierDensityDischarge_rhoDQ` route. -/
def rhoDQ_precursorConsumers_of_descentWindowMatch (ctx : ActualFailureContext)
    (W : DescentWindowMatch ctx)
    (hcop : ∀ k ∈ genuineDensePackStarts ctx, Nat.Coprime (W.a k) (canonicalCenter ctx).q0)
    (hlo : ∀ k ∈ genuineDensePackStarts ctx, ctx.shell.X < k + ctx.n24CarryData.r)
    (hhi : ∀ k ∈ genuineDensePackStarts ctx,
        (k + ctx.n24CarryData.r) + proofV4DensePackSpread ctx.shell ≤ 2 * ctx.shell.X)
    (hpb : Classical.choose ctx.shell.hXdyadic + orderOf (2 : ZMod (canonicalCenter ctx).q0)
        ≤ proofV4DensePackSpread ctx.shell + 2)
    (hcarry : NoLargeRun ctx → ∀ k ∈ genuineDensePackStarts ctx,
      windowCylinderValue ctx.shell.d (k + ctx.n24CarryData.r)
          (proofV4DensePackSpread ctx.shell + 1)
        ≠ cylinderIndex (proofV4DensePackSpread ctx.shell + 1)
            ((W.a k : ℝ) / ((canonicalCenter ctx).q0 : ℝ)) + 1) :
    RhoDQPrecursorConsumerBundle ctx where
  cert := SingularSquareCertificateAt.rhoDQ_ofDescentWindowMatch ctx W hcop hcarry hpb
  endpointDensity := densePackEndpointDensityRhoDQ_of_descentWindowMatch ctx W hcop hlo hhi hpb
  matchedWindows := fun hnlr =>
    matchedDescentWindowsAt_of_certificateAt ctx hnlr
      (SingularSquareCertificateAt.rhoDQ_ofDescentWindowMatch ctx W hcop hcarry hpb)

/-! ## 8.  Honest residual / status inventory -/

/-- The precise status of the pinned density-precursor consumers after this module. -/
def rhoDQPrecursorConsumerResiduals : List String :=
  [ "GOAL -- Q-correct (rate rhoDQ q0 = 1/(4 q0)) drop-in analogues of the remaining pinned " ++
      "density-precursor CONSUMER types, composing with frontierDensityDischarge_rhoDQ so the density " ++
      "atoms along the actual-shell path are honest for EVERY Q. manuscriptRhoD untouched.",
    "CLOSED (MatchedSemiperiodicWindow) -- MatchedSemiperiodicWindowAt rho rate-generic; " ++
      "MatchedSemiperiodicWindow.toAt projects the pinned packet to the manuscriptRhoD instance; " ++
      "ofDyadicMatch / ofDyadicMatchRhoDQ ground it from a 25.1 match.",
    "CLOSED (matchedWindow_of_descentMatch hcal) -- matchedWindowRhoDQ_of_descentMatch builds the " ++
      "matched window at rate rhoDQ q0 from the 25.1 match alone, NO hcal.",
    "CLOSED (DescentCylinderMatchData.hdens) -- DescentCylinderMatchDataAt rho rate-generic; .toAt " ++
      "projection; descentCylinderMatchDataAt_rhoDQ_canonical constructor; MatchedDescentWindowsAt rho " ++
      "+ matchedDescentWindowsAt_of_cylinderMatchDataAt; MatchedDescentWindows.toAt projection.",
    "CLOSED (SingularSquareCertificate.hdens) -- SingularSquareCertificateAt rho rate-generic; .toAt " ++
      "projection; SingularSquareCertificateAt.rhoDQ_ofDescentWindowMatch constructor; rate-free " ++
      "cylinder reduction descentCylinderMatchDataAt_of_certificateAt / matchedDescentWindowsAt_of_" ++
      "certificateAt.",
    "CLOSED (proofV4DensePackMinHits) -- proofV4DensePackMinHitsRhoDQ = floor(rhoDQ q0*L) <= pinned; " ++
      "densePackEndpointDensityRhoDQ implied by the pinned floor and PROVED for all Q from the 25.1 " ++
      "match (densePackEndpointDensityRhoDQ_of_descentWindowMatch) or a matched-window family.",
    "CLOSED (Class2IndexSDR.ofSemiperiodicDensity / Class2AreaPacking.floor) -- rate-parametric SDR " ++
      "chain; rhoDQ instance is Class2IndexSDR.ofDyadicMatchesRhoDQ; Class2IndexSDR.toAreaPacking " ++
      "exposes the floor route, toAreaPacking_floor = S.rhoD*S.L (= rhoDQ q0*L for the rhoDQ SDR).",
    "COMPOSED -- rhoDQ_precursorConsumers_of_descentWindowMatch: one DescentWindowMatch ctx + " ++
      "coprimality + shell geometry + the (D2) carry routing yields the rhoDQ singular-square " ++
      "certificate, the Q-correct coarea hit-density (every Q), and (under NoLargeRun) the rhoDQ " ++
      "matched descent-window family.",
    "RESIDUAL (out of density scope) -- the genuine 25.1 cylinder geometry (hcyl / hbound / hcarry) " ++
      "remains the irreducible non-density input, carried verbatim. manuscriptRhoD (Constants) is " ++
      "UNCHANGED.",
    "NON-DEGENERATE -- every rate-generic packet carries hrho : 0 <= rho and a POSITIVE rhoDQ q0 " ++
      "floor; the density is the genuine telescoped periodic count, no zero-floor / vacuous shortcut." ]

theorem rhoDQPrecursorConsumerResiduals_nonempty : rhoDQPrecursorConsumerResiduals ≠ [] := by
  simp [rhoDQPrecursorConsumerResiduals]

/-! ## 9.  Axiom-cleanliness audit -/

#print axioms MatchedSemiperiodicWindowAt.windowWeight_ge
#print axioms MatchedSemiperiodicWindowAt.ofDyadicMatch
#print axioms MatchedSemiperiodicWindowAt.ofDyadicMatchRhoDQ
#print axioms MatchedSemiperiodicWindow.toAt
#print axioms matchedWindowRhoDQ_of_descentMatch
#print axioms matchedWindowRhoDQ_windowWeight_ge
#print axioms DescentCylinderMatchData.toAt
#print axioms descentCylinderMatchDataAt_rhoDQ_canonical
#print axioms matchedDescentWindowsAt_of_cylinderMatchDataAt
#print axioms MatchedDescentWindows.toAt
#print axioms SingularSquareCertificate.toAt
#print axioms SingularSquareCertificateAt.rhoDQ_ofDescentWindowMatch
#print axioms descentCylinderMatchDataAt_of_certificateAt
#print axioms matchedDescentWindowsAt_of_certificateAt
#print axioms proofV4DensePackMinHitsRhoDQ_le_pinned
#print axioms densePackEndpointDensityRhoDQ_of_pinned
#print axioms densePackMinHitsFloorAt_le_supportWindow
#print axioms densePackEndpointDensityRhoDQ_of_matchedDescentWindowsAt
#print axioms densePackEndpointDensityRhoDQ_of_descentWindowMatch
#print axioms Class2IndexSDR.toAreaPacking_floor
#print axioms Class2IndexSDR.toAreaPacking_towerSubMass
#print axioms rhoDQ_precursorConsumers_of_descentWindowMatch

end

end Erdos260
