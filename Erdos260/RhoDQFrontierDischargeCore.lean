import Erdos260.RhoDQCalibrationCore
import Erdos260.DescentDepthAgreementCore

/-!
# The frontier-shaped Q-dependent density discharge at rate `rho_D(q0) = 1/(4 q0)`

This module (NEW; it edits no existing file, and does **not** change the global
`Erdos260.Constants.manuscriptRhoD = 1/4`) makes the genuine Q-dependent dense-marker density floor
`rhoDQ q0 = 1/(4 q0)` (proved standalone in `RhoDQCalibrationCore`) **usable at the §25.1 frontier**:
it produces the exact density-atom field(s) the frontier reduction layer consumes, but at the
Q-correct rate, **dischargeable for EVERY actual failing shell (every `Q`)** given only the genuine
coprimality of the residue numerators -- where the pinned `manuscriptRhoD = 1/4` version is
dischargeable **only at `q0 = 1`**.

## Investigation result (audit)

`erdos260_of_minimalResidualV3` and its residual `Erdos260MinimalResidualV3` **abstract over the
rate**: the Tower field is `Class2ActiveFloorCount` (`hbdry` + the scalar count
`#fibre2 * positivePart(2 Y) <= xi X/6`) and the DensePack field is `DensePackCoareaSupport`
(owner/marker maps) -- **neither mentions `manuscriptRhoD`**.  The pinned `1/4` density hypothesis is
consumed only inside the density-reduction *sub-layer* that builds toward those structural fields:

* `FailingShellPeriodicityCore.matchedWindow_of_descentMatch` via `hcal : manuscriptRhoD <= 1/(3 q0)`;
* `SemiperiodicWindowCore.MatchedSemiperiodicWindow.hdens` / `.ofDyadicMatch`
  (`manuscriptRhoD * period <= wt`);
* `SemiperiodicMatchEnrichCore.DescentCylinderMatchData.hdens` / `descentCylinderMatchData_canonical`;
* `DirtyCrossingCylinderCore.SingularSquareCertificate.hdens`, assembled in
  `DescentDepthAgreementCore.singularSquareCertificate_of_descentWindowMatch` (its `hdens` argument);
* `SDRDensityCore` (`proofV4DensePackMinHits = floor(manuscriptRhoD * L)`,
  `Class2IndexSDR.ofSemiperiodicDensity`) and the `Class2AreaPacking.floor`/`hcard` Tower route.

For the **actual** shell the reduced residual-center denominator `q0 = (canonicalCenter ctx).q0` is
`> 1` and odd (`runFOfShell_q0_gt_one`/`_q0_odd`), hence `q0 >= 3`.  At `q0 >= 2` the pinned
`manuscriptRhoD = 1/4` STRICTLY exceeds the genuine §24 fixed-period density floor `1/(3 q0)`
(`manuscriptRhoD_gt_third_of_two_le`), so the `manuscriptRhoD`-shaped `hdens`/`hcal` is NOT
§24-dischargeable.  The Q-dependent `rhoDQ q0 = 1/(4 q0) <= 1/(3 q0)` (`rhoDQ_le_third`, for EVERY
`q0`) repairs every one of these atoms.

## What is genuinely PROVED here (no `sorry`/`axiom`/`admit`/`native_decide`)

* `manuscriptRhoD_le_third_iff_q0_eq_one` -- **the sharp diagnosis**: the §24-dischargeability
  hypothesis `manuscriptRhoD <= 1/(3 q0)` (the `hcal` of `matchedWindow_of_descentMatch`) holds iff
  `q0 = 1`.  `manuscriptRhoD_hcal_false_for_shell` / `rhoDQ_hcal_holds_for_shell`: for the actual
  shell (`q0 >= 3`) the pinned `hcal` is FALSE while the `rhoDQ` analogue is automatic.
* `singularSquareCertificate_hdens_rhoDQ` -- **the drop-in `hdens` field at rate `rhoDQ`, all Q**:
  exactly the shape of the `hdens` argument of
  `DescentDepthAgreementCore.singularSquareCertificate_of_descentWindowMatch`
  (= `SingularSquareCertificate.hdens` / `DescentCylinderMatchData.hdens`), over the actual canonical
  center, at rate `rhoDQ (canonicalCenter ctx).q0` instead of the `q0=1`-only `manuscriptRhoD`,
  discharged for every `ctx` from the coprimality of the per-start residue numerators.
* `windowWeight_ge_rhoDQ_of_descentMatch` -- **the `matchedWindow_of_descentMatch` analogue, no
  `hcal`**: from the §25.1 descent-depth match alone (plus coprimality + the length calibration) the
  actual descent window packs `rhoDQ q0 * L <= windowWeight d start len` -- the real density atom that
  `MatchedSemiperiodicWindow.windowWeight_ge` delivers, but at the Q-correct rate and needing **no**
  `hcal` smallness, so it holds for every `Q`.
* `descentWindowMatch_windowAtom_rhoDQ` -- the same atom on the *actual* shell's genuine descent
  windows, sourced from the lone §25.1 residual `DescentWindowMatch ctx` (its `hmatch` = the
  descent-depth agreement) + coprimality.
* `densePackSupportFloor_rhoDQ_of_descentWindowMatch` -- **the `Class2AreaPacking.hcard`-shaped real
  support floor** `rhoDQ q0 * L <= |supportWindow(k+r)|` for every genuine start (via the
  `rho_D`-free shell injection `windowFilter_card_le_supportWindow`).  `Class2AreaPacking` is
  parametric in its `floor` field, so this feeds it at `floor := rhoDQ q0 * L`.
* `densePackEndpointDensity_rhoDQ_of_descentWindowMatch` -- **the K.1.1 coarea hit-density**
  `floor(rhoDQ q0 * L) <= |supportWindow(k+r)|` for every genuine start (the Q-correct replacement of
  the pinned `proofV4DensePackMinHits = floor(manuscriptRhoD * L)`).
* `frontierDensityDischarge_rhoDQ` -- **the composition**: a single `DescentWindowMatch ctx` (the lone
  irreducible §25.1 residual) + coprimality + shell geometry discharges ALL the Q-correct density
  atoms the frontier density-layer needs (the cert `hdens`, the real support floor, the floored coarea
  floor), for every `Q`.

The Tower capacity floor `routedClassMassOf ... 2 <= xi X / 6` at rate `rhoDQ q0` is already proved in
`RhoDQCalibrationCore.towerSubMass_of_dyadicMatchesRhoDQ` (the parametric `Class2IndexSDR.ofIntervals`
fed at `rhoDQ q0`); it composes here unchanged.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

namespace Erdos260

open Finset

noncomputable section

set_option linter.unusedVariables false

/-! ## 1.  The sharp diagnosis: the `manuscriptRhoD` density-discharge holds only at `q0 = 1` -/

/-- **The sharp diagnosis.**  The §24-dischargeability hypothesis `manuscriptRhoD <= 1/(3 q0)` -- the
`hcal` field consumed by `FailingShellPeriodicityCore.matchedWindow_of_descentMatch`, and the exact
condition under which the `manuscriptRhoD`-shaped `hdens` (`manuscriptRhoD * t <= wt`) follows from the
genuine §24 floor `1/(3 q0) * t <= wt` -- holds **iff** `q0 = 1`.  Hence the pinned `1/4` density atom
is honest only at the `Q = 1` representative. -/
theorem manuscriptRhoD_le_third_iff_q0_eq_one {q0 : ℕ} (hq0 : 0 < q0) :
    manuscriptRhoD ≤ (1 : ℝ) / ((3 * q0 : ℕ) : ℝ) ↔ q0 = 1 := by
  constructor
  · intro h
    by_contra hne
    have h2 : 2 ≤ q0 := by omega
    exact absurd h (not_le.mpr (manuscriptRhoD_gt_third_of_two_le h2))
  · rintro rfl
    have hcast : ((3 * 1 : ℕ) : ℝ) = 3 := by norm_num
    rw [hcast]; unfold manuscriptRhoD; norm_num

/-- **The Q-dependent floor stays below the genuine §24 floor for the actual shell.**  For the actual
canonical residual-center denominator `q0 = (canonicalCenter ctx).q0` (`> 1`, odd) the `rhoDQ`
calibration satisfies `rhoDQ q0 <= 1/(3 q0)` automatically -- so the `rhoDQ` density atom is
§24-dischargeable for every `ctx`. -/
theorem rhoDQ_hcal_holds_for_shell (ctx : ActualFailureContext) :
    rhoDQ (canonicalCenter ctx).q0 ≤ (1 : ℝ) / ((3 * (canonicalCenter ctx).q0 : ℕ) : ℝ) :=
  rhoDQ_le_third (canonicalCenter ctx).q0_pos

/-- **The pinned `hcal` is FALSE for the actual shell.**  Because `q0 = (canonicalCenter ctx).q0 >= 3`
for the actual failing shell, the `manuscriptRhoD`-shaped §24-dischargeability hypothesis
`manuscriptRhoD <= 1/(3 q0)` consumed by `matchedWindow_of_descentMatch` cannot hold -- the precise
reason the pinned density atom is not honestly dischargeable for any genuine `Q`, and must be
recalibrated to `rhoDQ q0`. -/
theorem manuscriptRhoD_hcal_false_for_shell (ctx : ActualFailureContext) :
    ¬ (manuscriptRhoD ≤ (1 : ℝ) / ((3 * (canonicalCenter ctx).q0 : ℕ) : ℝ)) := by
  have h1 : 1 < (canonicalCenter ctx).q0 := runFOfShell_q0_gt_one ctx
  have h2 : 2 ≤ (canonicalCenter ctx).q0 := by omega
  exact not_le.mpr (manuscriptRhoD_gt_third_of_two_le h2)

/-! ## 2.  The drop-in `hdens` field at rate `rhoDQ`, dischargeable for ALL Q

`DescentDepthAgreementCore.singularSquareCertificate_of_descentWindowMatch` assembles a
`SingularSquareCertificate ctx` from a rate-free `DescentWindowMatch ctx` plus, among others, the
`hdens` argument

```
forall k in genuineDensePackStarts ctx,
  manuscriptRhoD * orderOf (2 : ZMod (canonicalCenter ctx).q0)
    <= windowWeight (dyadicDigit (canonicalCenter ctx).q0 (W.a k)) 0 (orderOf ...)
```

at rate `manuscriptRhoD`.  The lemma below is *exactly this argument*, but at the Q-correct rate
`rhoDQ (canonicalCenter ctx).q0` -- discharged for every `ctx` from coprimality alone. -/

/-- **The §24 density floor in the `SingularSquareCertificate.hdens` / `DescentCylinderMatchData.hdens`
shape, at rate `rhoDQ`, for ALL Q.**  Given the genuine coprimality of the per-start residue
numerators `W.a k` to the actual reduced denominator `q0 = (canonicalCenter ctx).q0`, every genuine
DensePack start's orbit word packs `rhoDQ q0 * t <= wt(period)`.  This is the drop-in replacement for
the `q0=1`-only `manuscriptRhoD` `hdens` argument, honest for every actual shell. -/
theorem singularSquareCertificate_hdens_rhoDQ (ctx : ActualFailureContext)
    (W : DescentWindowMatch ctx)
    (hcop : ∀ k ∈ genuineDensePackStarts ctx, Nat.Coprime (W.a k) (canonicalCenter ctx).q0) :
    ∀ k ∈ genuineDensePackStarts ctx,
      rhoDQ (canonicalCenter ctx).q0 * (orderOf (2 : ZMod (canonicalCenter ctx).q0) : ℝ)
        ≤ (windowWeight (dyadicDigit (canonicalCenter ctx).q0 (W.a k)) 0
            (orderOf (2 : ZMod (canonicalCenter ctx).q0)) : ℝ) :=
  descentDensityFloor_rhoDQ_all_Q ctx W.a hcop

/-! ## 3.  The matched-window density atom at rate `rhoDQ`, the `matchedWindow_of_descentMatch`
analogue (no `hcal`)

`FailingShellPeriodicityCore.matchedWindow_of_descentMatch` builds a `MatchedSemiperiodicWindow`
(baked at `manuscriptRhoD`) and *requires* `hcal : manuscriptRhoD <= 1/(3 q0)` -- satisfiable only at
`q0 = 1` (§1).  Its derived `MatchedSemiperiodicWindow.windowWeight_ge` then yields
`manuscriptRhoD * L <= windowWeight d start len`.  The version below produces the same real density
atom on the actual word, at rate `rhoDQ q0`, with **no** `hcal` smallness -- dischargeable for every
`Q`. -/

/-- **The descent-window density atom at rate `rhoDQ` (the `matchedWindow_of_descentMatch` analogue).**
From the §25.1 descent-depth match `WindowMatch d (dyadicDigit q0 a) start len` (the genuine
irreducible residual), the coprimality `a` to `q0`, the period-in-window `orderOf <= len`, and the
length calibration `L + orderOf <= len + 1`, the actual descent window packs
`rhoDQ q0 * L <= windowWeight d start len`.  No `hcal : manuscriptRhoD <= 1/(3 q0)` is needed (the
`rhoDQ` calibration is automatic, `rhoDQ_le_third`), so this holds for every `q0`. -/
theorem windowWeight_ge_rhoDQ_of_descentMatch {d : ℕ → ℕ} {start len L q0 a : ℕ}
    (hq0 : 1 < q0) (hodd : Odd q0) (hcop : Nat.Coprime a q0)
    (hle : orderOf (2 : ZMod q0) ≤ len)
    (hlen : L + orderOf (2 : ZMod q0) ≤ len + 1)
    (hmatch : WindowMatch d (dyadicDigit q0 a) start len) :
    rhoDQ q0 * (L : ℝ) ≤ (windowWeight d start len : ℝ) :=
  windowWeight_ge_rhoDQ_of_dyadicMatch hq0 hodd hcop hle hlen hmatch

/-- **The descent-window density atom on the ACTUAL shell, from the lone §25.1 residual.**  Sourced
from a `DescentWindowMatch ctx` (whose `hmatch` field is the descent-depth agreement, definitionally a
`WindowMatch` to the canonical orbit word) plus coprimality and the bounded-period calibration `hpb`,
every genuine descent window packs `rhoDQ q0 * L <= windowWeight ctx.shell.d (k+r) (spread+1)`
(`L := Classical.choose ctx.shell.hXdyadic`, the manuscript window length), for every `Q`. -/
theorem descentWindowMatch_windowAtom_rhoDQ (ctx : ActualFailureContext)
    (W : DescentWindowMatch ctx)
    (hcop : ∀ k ∈ genuineDensePackStarts ctx, Nat.Coprime (W.a k) (canonicalCenter ctx).q0)
    (hpb : ∀ k ∈ genuineDensePackStarts ctx,
        Classical.choose ctx.shell.hXdyadic + orderOf (2 : ZMod (canonicalCenter ctx).q0)
          ≤ proofV4DensePackSpread ctx.shell + 2) :
    ∀ k ∈ genuineDensePackStarts ctx,
      rhoDQ (canonicalCenter ctx).q0 * ((Classical.choose ctx.shell.hXdyadic : ℕ) : ℝ)
        ≤ (windowWeight ctx.shell.d (k + ctx.n24CarryData.r)
            (proofV4DensePackSpread ctx.shell + 1) : ℝ) := by
  intro k hk
  have hq0 := runFOfShell_q0_gt_one ctx
  have hodd := runFOfShell_q0_odd ctx
  have hClen : 1 ≤ Classical.choose ctx.shell.hXdyadic := by
    have := ctx.shell_carryLarge; omega
  have hle : orderOf (2 : ZMod (canonicalCenter ctx).q0) ≤ proofV4DensePackSpread ctx.shell + 1 := by
    have := hpb k hk; omega
  exact windowWeight_ge_rhoDQ_of_dyadicMatch hq0 hodd (hcop k hk) hle (hpb k hk) (W.hmatch k hk)

/-! ## 4.  The DensePack support floors at rate `rhoDQ` -- the `Class2AreaPacking.hcard` shape and the
K.1.1 coarea hit-density, for ALL Q -/

/-- **The `Class2AreaPacking.hcard`-shaped real support floor at rate `rhoDQ`.**  Every genuine descent
window packs `rhoDQ q0 * L <= |supportWindow(k+r)|` real-valued, via the `rho_D`-free shell injection
`windowFilter_card_le_supportWindow`.  `Class2AreaPacking` carries its per-member floor as a *field*
`floor : R` with `hcard : floor <= |window k|`; this discharges that field at `floor := rhoDQ q0 * L`
and `window := proofV4DensePackSupportWindow ctx.shell`, for every `Q`. -/
theorem densePackSupportFloor_rhoDQ_of_descentWindowMatch (ctx : ActualFailureContext)
    (W : DescentWindowMatch ctx)
    (hcop : ∀ k ∈ genuineDensePackStarts ctx, Nat.Coprime (W.a k) (canonicalCenter ctx).q0)
    (hlo : ∀ k ∈ genuineDensePackStarts ctx, ctx.shell.X < k + ctx.n24CarryData.r)
    (hhi : ∀ k ∈ genuineDensePackStarts ctx,
        (k + ctx.n24CarryData.r) + proofV4DensePackSpread ctx.shell ≤ 2 * ctx.shell.X)
    (hpb : ∀ k ∈ genuineDensePackStarts ctx,
        Classical.choose ctx.shell.hXdyadic + orderOf (2 : ZMod (canonicalCenter ctx).q0)
          ≤ proofV4DensePackSpread ctx.shell + 2) :
    ∀ k ∈ genuineDensePackStarts ctx,
      rhoDQ (canonicalCenter ctx).q0 * ((Classical.choose ctx.shell.hXdyadic : ℕ) : ℝ)
        ≤ ((proofV4DensePackSupportWindow ctx.shell (k + ctx.n24CarryData.r)).card : ℝ) := by
  intro k hk
  have hatom := descentWindowMatch_windowAtom_rhoDQ ctx W hcop hpb k hk
  have hfc := windowFilter_card_le_supportWindow ctx.shell (hlo k hk) (hhi k hk)
  rw [← windowWeight_eq_filter_card ctx.shell.hd (k + ctx.n24CarryData.r)
      (proofV4DensePackSpread ctx.shell + 1)] at hfc
  have hfcR : (windowWeight ctx.shell.d (k + ctx.n24CarryData.r)
        (proofV4DensePackSpread ctx.shell + 1) : ℝ)
      ≤ ((proofV4DensePackSupportWindow ctx.shell (k + ctx.n24CarryData.r)).card : ℝ) := by
    exact_mod_cast hfc
  exact le_trans hatom hfcR

/-- **The K.1.1 coarea hit-density at rate `rhoDQ`, the `densePackEndpointDensity` analogue, for ALL
Q.**  Every genuine descent window satisfies `floor(rhoDQ q0 * L) <= |supportWindow(k+r)|` -- the
Q-correct replacement for the pinned `proofV4DensePackMinHits = floor(manuscriptRhoD * L) <=
|supportWindow|` (which, with `manuscriptRhoD = 1/4`, is the `q0=1`-only floor). -/
theorem densePackEndpointDensity_rhoDQ_of_descentWindowMatch (ctx : ActualFailureContext)
    (W : DescentWindowMatch ctx)
    (hcop : ∀ k ∈ genuineDensePackStarts ctx, Nat.Coprime (W.a k) (canonicalCenter ctx).q0)
    (hlo : ∀ k ∈ genuineDensePackStarts ctx, ctx.shell.X < k + ctx.n24CarryData.r)
    (hhi : ∀ k ∈ genuineDensePackStarts ctx,
        (k + ctx.n24CarryData.r) + proofV4DensePackSpread ctx.shell ≤ 2 * ctx.shell.X)
    (hpb : ∀ k ∈ genuineDensePackStarts ctx,
        Classical.choose ctx.shell.hXdyadic + orderOf (2 : ZMod (canonicalCenter ctx).q0)
          ≤ proofV4DensePackSpread ctx.shell + 2) :
    ∀ k ∈ genuineDensePackStarts ctx,
      Nat.floor (rhoDQ (canonicalCenter ctx).q0 * ((Classical.choose ctx.shell.hXdyadic : ℕ) : ℝ))
        ≤ (proofV4DensePackSupportWindow ctx.shell (k + ctx.n24CarryData.r)).card := by
  intro k hk
  have hq0 := runFOfShell_q0_gt_one ctx
  have hodd := runFOfShell_q0_odd ctx
  have hClen : 1 ≤ Classical.choose ctx.shell.hXdyadic := by
    have := ctx.shell_carryLarge; omega
  have hle : orderOf (2 : ZMod (canonicalCenter ctx).q0) ≤ proofV4DensePackSpread ctx.shell + 1 := by
    have := hpb k hk; omega
  exact densePackMinHitsFloor_rhoDQ_le_supportWindow ctx.shell (hlo k hk) (hhi k hk)
    hq0 hodd (hcop k hk) hle (hpb k hk) (W.hmatch k hk)

/-! ## 5.  The composition: one §25.1 residual discharges every Q-correct density atom -/

/-- **The frontier-shaped Q-density discharge, composed.**  A single `DescentWindowMatch ctx` (the lone
irreducible §25.1 residual -- the descent-depth agreement) together with the genuine coprimality of the
per-start residue numerators and the shell geometry/period calibration discharges, **for every `Q`**,
all three Q-correct density atoms the frontier reduction layer consumes:

* the `SingularSquareCertificate.hdens` / `DescentCylinderMatchData.hdens` field at rate `rhoDQ`;
* the `Class2AreaPacking.hcard`-shaped real support floor `rhoDQ q0 * L <= |supportWindow(k+r)|`;
* the K.1.1 coarea hit-density `floor(rhoDQ q0 * L) <= |supportWindow(k+r)|`
  (the `densePackEndpointDensity` analogue).

Where the `manuscriptRhoD`-pinned versions of all three are dischargeable only at `q0 = 1`
(§1), these hold for every actual failing shell. -/
theorem frontierDensityDischarge_rhoDQ (ctx : ActualFailureContext)
    (W : DescentWindowMatch ctx)
    (hcop : ∀ k ∈ genuineDensePackStarts ctx, Nat.Coprime (W.a k) (canonicalCenter ctx).q0)
    (hlo : ∀ k ∈ genuineDensePackStarts ctx, ctx.shell.X < k + ctx.n24CarryData.r)
    (hhi : ∀ k ∈ genuineDensePackStarts ctx,
        (k + ctx.n24CarryData.r) + proofV4DensePackSpread ctx.shell ≤ 2 * ctx.shell.X)
    (hpb : ∀ k ∈ genuineDensePackStarts ctx,
        Classical.choose ctx.shell.hXdyadic + orderOf (2 : ZMod (canonicalCenter ctx).q0)
          ≤ proofV4DensePackSpread ctx.shell + 2) :
    (∀ k ∈ genuineDensePackStarts ctx,
        rhoDQ (canonicalCenter ctx).q0 * (orderOf (2 : ZMod (canonicalCenter ctx).q0) : ℝ)
          ≤ (windowWeight (dyadicDigit (canonicalCenter ctx).q0 (W.a k)) 0
              (orderOf (2 : ZMod (canonicalCenter ctx).q0)) : ℝ))
      ∧ (∀ k ∈ genuineDensePackStarts ctx,
        rhoDQ (canonicalCenter ctx).q0 * ((Classical.choose ctx.shell.hXdyadic : ℕ) : ℝ)
          ≤ ((proofV4DensePackSupportWindow ctx.shell (k + ctx.n24CarryData.r)).card : ℝ))
      ∧ (∀ k ∈ genuineDensePackStarts ctx,
        Nat.floor (rhoDQ (canonicalCenter ctx).q0 * ((Classical.choose ctx.shell.hXdyadic : ℕ) : ℝ))
          ≤ (proofV4DensePackSupportWindow ctx.shell (k + ctx.n24CarryData.r)).card) :=
  ⟨singularSquareCertificate_hdens_rhoDQ ctx W hcop,
   densePackSupportFloor_rhoDQ_of_descentWindowMatch ctx W hcop hlo hhi hpb,
   densePackEndpointDensity_rhoDQ_of_descentWindowMatch ctx W hcop hlo hhi hpb⟩

/-! ## 6.  Honest residual / status inventory -/

/-- The precise status of the frontier-shaped `rho_D` Q-discharge after this module. -/
def rhoDQFrontierDischargeResiduals : List String :=
  [ "GOAL — make the Q-dependent density floor rhoDQ q0 = 1/(4 q0) USABLE at the §25.1 frontier: " ++
      "produce the exact density-atom field(s) the frontier reduction layer consumes, at the Q-correct " ++
      "rate, dischargeable for EVERY actual shell (every Q) from coprimality of the residue numerators.",
    "AUDIT (frontier abstracts over the rate) — Erdos260MinimalResidualV3 mentions NO manuscriptRhoD: " ++
      "the Tower field is Class2ActiveFloorCount (#fibre2·positivePart(2Y) ≤ ξX/6) and the DensePack " ++
      "field is DensePackCoareaSupport (owner/marker maps). manuscriptRhoD = 1/4 is consumed only in the " ++
      "density-reduction sub-layer building toward those fields: matchedWindow_of_descentMatch (hcal), " ++
      "MatchedSemiperiodicWindow.hdens, DescentCylinderMatchData.hdens, SingularSquareCertificate.hdens " ++
      "(assembled in singularSquareCertificate_of_descentWindowMatch), SDRDensityCore " ++
      "(proofV4DensePackMinHits = ⌊manuscriptRhoD·L⌋, Class2IndexSDR.ofSemiperiodicDensity), and the " ++
      "Class2AreaPacking.floor/hcard Tower route.",
    "CLOSED (diagnosis) — manuscriptRhoD_le_third_iff_q0_eq_one: the §24-dischargeability hypothesis " ++
      "manuscriptRhoD ≤ 1/(3 q0) (the hcal of matchedWindow_of_descentMatch) holds IFF q0 = 1. For the " ++
      "actual shell q0 = (canonicalCenter ctx).q0 ≥ 3, so manuscriptRhoD_hcal_false_for_shell: the pinned " ++
      "hcal is FALSE, while rhoDQ_hcal_holds_for_shell: rhoDQ q0 ≤ 1/(3 q0) automatically.",
    "CLOSED (drop-in hdens, ALL Q) — singularSquareCertificate_hdens_rhoDQ: EXACTLY the hdens argument " ++
      "of singularSquareCertificate_of_descentWindowMatch (= SingularSquareCertificate.hdens / " ++
      "DescentCylinderMatchData.hdens), at rate rhoDQ (canonicalCenter ctx).q0 instead of the q0=1-only " ++
      "manuscriptRhoD, discharged for every ctx from coprimality (= descentDensityFloor_rhoDQ_all_Q).",
    "CLOSED (matched-window atom, no hcal) — windowWeight_ge_rhoDQ_of_descentMatch: the " ++
      "matchedWindow_of_descentMatch analogue producing rhoDQ q0 · L ≤ windowWeight d start len from the " ++
      "§25.1 match alone, with NO hcal smallness (rhoDQ_le_third is automatic), for every q0. " ++
      "descentWindowMatch_windowAtom_rhoDQ sources it from the lone residual DescentWindowMatch ctx.",
    "CLOSED (DensePack floors, ALL Q) — densePackSupportFloor_rhoDQ_of_descentWindowMatch: the " ++
      "Class2AreaPacking.hcard-shaped real floor rhoDQ q0 · L ≤ |supportWindow(k+r)| (via the rho_D-free " ++
      "windowFilter_card_le_supportWindow); densePackEndpointDensity_rhoDQ_of_descentWindowMatch: the " ++
      "K.1.1 coarea ⌊rhoDQ q0 · L⌋ ≤ |supportWindow(k+r)| (the Q-correct replacement of the pinned " ++
      "proofV4DensePackMinHits floor).",
    "CLOSED (composition) — frontierDensityDischarge_rhoDQ: ONE DescentWindowMatch ctx + coprimality + " ++
      "shell geometry discharges ALL three Q-correct density atoms (cert hdens + real support floor + " ++
      "floored coarea floor) for every Q. The Tower floor routedClassMassOf … 2 ≤ ξX/6 at rate rhoDQ is " ++
      "RhoDQCalibrationCore.towerSubMass_of_dyadicMatchesRhoDQ, composing unchanged.",
    "WIRING (for consolidation; not applied here, NEW file only) — to make the frontier density-layer " ++
      "honest for all Q, recalibrate each consuming hdens/hcal field type manuscriptRhoD ↦ " ++
      "rhoDQ (canonicalCenter ctx).q0 (or rhoDQ q0) and discharge it with the matching lemma above: " ++
      "SingularSquareCertificate.hdens / DescentCylinderMatchData.hdens / MatchedSemiperiodicWindow.hdens, " ++
      "the hcal of matchedWindow_of_descentMatch, the hdens arg of " ++
      "singularSquareCertificate_of_descentWindowMatch, the proofV4DensePackMinHits floor and the " ++
      "Class2IndexSDR / Class2AreaPacking rate (its huniform/hconst smallness 2(c0 ε) ≤ (ξ/6)ρ stays an " ++
      "INPUT, Q-dependent for large q0 — a separate K.4-constant concern, not a density-atom defect). " ++
      "Constants.manuscriptRhoD is left UNTOUCHED.",
    "NON-DEGENERATE — rhoDQ q0 > 0; every floor packs a POSITIVE Q-dependent density inherited from the " ++
      "genuine §24/Fine-Wilf telescoped periodic count, no empty / zero-floor / vacuous shortcut." ]

theorem rhoDQFrontierDischargeResiduals_nonempty : rhoDQFrontierDischargeResiduals ≠ [] := by
  simp [rhoDQFrontierDischargeResiduals]

/-! ## 7.  Axiom-cleanliness audit -/

#print axioms manuscriptRhoD_le_third_iff_q0_eq_one
#print axioms rhoDQ_hcal_holds_for_shell
#print axioms manuscriptRhoD_hcal_false_for_shell
#print axioms singularSquareCertificate_hdens_rhoDQ
#print axioms windowWeight_ge_rhoDQ_of_descentMatch
#print axioms descentWindowMatch_windowAtom_rhoDQ
#print axioms densePackSupportFloor_rhoDQ_of_descentWindowMatch
#print axioms densePackEndpointDensity_rhoDQ_of_descentWindowMatch
#print axioms frontierDensityDischarge_rhoDQ

end

end Erdos260
