import Mathlib
import Erdos260.ResidualScalarBudgets
import Erdos260.PositiveDensityRichShell
import Erdos260.DensePackFactoryConstruction
import Erdos260.ReturnFactoryConstruction

/-!
# Per-shell SCALAR / REGIME side-conditions discharged for a failing dyadic shell

The capstone `erdos260_reduced_minimal''` (`Erdos260.UnconditionalAssemblyTight2`) and its
factory reductions (`DensePackFactoryConstruction`, `ReturnFactoryConstruction`) leave four
*pure scalar / regime* side-conditions per shell.  This file (NEW; it edits no existing file)
discharges them for a **genuine failing shell** `shell : FailingDyadicShell` at sufficiently
large scale `X = 2^L`, deriving each from the failing-shell hypothesis **where genuinely
possible**, and pinning down precisely the residual genuine extra input where not.

The four side-conditions, and their honest status after this file:

1. **Chernoff length calibration** `m ≤ c₁·Y` (H.4 block length; `ResidualScalarBudgets`):
   **CLOSED.**  At the pinned manuscript constants the H.4 regime `C_drop ≤ 2 − η` holds
   (`manuscriptCdrop_lt_two_sub_eta`), and the only scale input — the nonnegativity
   `0 ≤ c₁·ε·L` — is automatic for `X = 2^L` (`L : ℕ`, so `(L : ℝ) ≥ 0`).  Hence
   `failingShell_h4_calibration` discharges `m₁ ≤ c₁·Y₁` for every failing shell given the
   manuscript O(1) error bound `err ≤ 1`; for an arbitrary O(1) bound `err ≤ Cerr` the
   calibration holds once `L` clears an *explicit* threshold
   (`failingShell_h4_calibration_of_largeL_explicit`).

2. **DensePack 2-condition regime** `c0 ≤ κ/16` and `carryB Q + 25 ≤ L` (`X = 2^L`):
   * `carryB Q + 25 ≤ L`: **CLOSED** from `aboveCarryThreshold` (= `carryThreshold (carryB Q+19) ≤ X`)
     via `carryLarge_of_carryThreshold_le`.  See `failingShell_carryLarge_of_aboveCarryThreshold`.
   * `c0 ≤ κ/16`: **REDUCED** to the manuscript failure-constant pin `c0 = manuscriptC0 = κ/64`
     (the K.4 tighter form `c0 ≪ κ`).  The bare `FailingDyadicShell` carries only `c0 < κ`
     (`hc0_lt_kappa`), which is *not* enough.  Under the pin it is CLOSED
     (`failingShell_c0_le_kappa_div_sixteen_of_pin`, via `manuscriptC0_le_kappa_div_sixteen`).

3. **Return regime** `2·M_L ≤ s` (manuscript `M_L = o(r)`, `ResidualScalarBudgets`):
   **REDUCED** to the asymptotic `M_L =o[atTop] s`.  The Return scale `s` and the dirty
   multiplicity `M_L = cleanedDirtyEnvelope` are Return-side quantities, *not* fields of the
   failing shell, so `2·M_L ≤ s` cannot be closed from failing-shell data.  For the failing
   shell at large scale (`L → ∞`) the regime holds eventually
   (`eventually_cleanedDirtyEnvelope_regime_of_isLittleO`), and then feeds the proved J.4
   envelope budget (`eventually_failingShell_mL_budget_of_isLittleO`).

4. **`1 ≤ supportCount d X`** (a support hit at/below `X`):
   **CLOSED** from the genuine "sufficiently large dyadic `X`" start threshold
   `appendixNChainCompressionStartThreshold ≤ X`
   (`failingShell_supportCount_pos_of_startThreshold_le`, reusing the same engine as
   `richShell_of_startThreshold_le`).  The weaker `aboveCarryThreshold` gate alone does *not*
   give it (a nonterminating shell whose first hit sits beyond `X` has `supportCount = 0`), so
   under that gate it is carried as the precise side input `hSupport`.

The closeable scale facts are bundled in `ShellScalarRegime` with builders
`shellRegime_of_failing_large` (from the start threshold + the `c0` pin) and
`shellRegime_of_aboveCarryThreshold` (from `aboveCarryThreshold` + the support side input +
the `c0` pin), feeding the DensePack factory datum (`ShellScalarRegime.densePackRegimeInput`,
`ShellScalarRegime.densePackFactoryData`) and the linear richness
(`ShellScalarRegime.richShell`).  Non-vacuity witnesses confirm the added hypotheses
(`c0 = manuscriptC0`, the large-scale gate) are mutually consistent, never `False`.

No `sorry`, `admit`, `native_decide`, or new `axiom`; no false / vacuous hypotheses.
-/

namespace Erdos260

open Asymptotics Filter

noncomputable section

/-! ## Target 2 — Chernoff length calibration `m ≤ c₁·Y` (H.4 block length)

`ResidualScalarBudgets.h4m1_le_c1_Y1` proves the calibration from the H.4 chain `C_drop ≤ 2 − η`,
the nonnegativity `0 ≤ c₁·ε·L`, and the O(1) error bound `err ≤ 1`; the manuscript-pinned form
is `manuscript_h4m1_le_c1_Y1`.  For a failing shell `X = 2^L` the dyadic exponent
`L = Classical.choose shell.hXdyadic` is a `ℕ`, so `(L : ℝ) ≥ 0` and the nonnegativity input is
automatic. -/

/--
**Target 2 (CLOSED for the failing shell).**  The H.4 length calibration `m₁ ≤ c₁·Y₁` at the
pinned manuscript constants, for the dyadic exponent of a failing shell, given the manuscript's
O(1) error bound `err ≤ 1`.  The H.4 regime `C_drop ≤ 2 − η` is a pinned constant fact, and the
nonnegativity `0 ≤ c₁·ε·L` is automatic since `L = Classical.choose shell.hXdyadic : ℕ`. -/
theorem failingShell_h4_calibration
    (shell : FailingDyadicShell) {err : ℝ} (herr : err ≤ 1) :
    h4m1 manuscriptCdrop manuscriptC1 manuscriptEps
        ((Classical.choose shell.hXdyadic : ℕ) : ℝ) err
      ≤ manuscriptC1 * h4Y1 manuscriptEta manuscriptEps
        ((Classical.choose shell.hXdyadic : ℕ) : ℝ) :=
  manuscript_h4m1_le_c1_Y1
    (mul_nonneg (mul_nonneg manuscriptC1_pos.le manuscriptEps_pos.le) (Nat.cast_nonneg _))
    herr

/--
**Target 2 (strict large-`L` form, hypothesis-stated threshold).**  For an arbitrary O(1) error
bound `err ≤ Cerr`, the calibration holds once `L` clears the explicit linear threshold built from
the *strict* manuscript gap `(1 − η) − (C_drop − 1) = 7/8 > 0`. -/
theorem failingShell_h4_calibration_of_large
    (shell : FailingDyadicShell) {err Cerr : ℝ}
    (herr : err ≤ Cerr)
    (hL : Cerr - 1 ≤ manuscriptC1 * manuscriptEps * ((Classical.choose shell.hXdyadic : ℕ) : ℝ)
            * ((1 - manuscriptEta) - (manuscriptCdrop - 1))) :
    h4m1 manuscriptCdrop manuscriptC1 manuscriptEps ((Classical.choose shell.hXdyadic : ℕ) : ℝ) err
      ≤ manuscriptC1 * h4Y1 manuscriptEta manuscriptEps ((Classical.choose shell.hXdyadic : ℕ) : ℝ) :=
  h4m1_le_c1_Y1_of_large_L herr hL

/--
**Target 2 (strict large-`L` form, explicit numeric threshold).**  With the pinned constants
`c₁·ε = 1/16384` and gap `7/8`, the calibration holds for an O(1) bound `err ≤ Cerr` once the
dyadic exponent satisfies `(131072/7)·(Cerr − 1) ≤ L`.  (For the manuscript bound `Cerr = 1` the
threshold is `0 ≤ L`, i.e. every scale; the threshold only bites for larger error budgets.) -/
theorem failingShell_h4_calibration_of_largeL_explicit
    (shell : FailingDyadicShell) {err Cerr : ℝ}
    (herr : err ≤ Cerr)
    (hL : (131072 / 7 : ℝ) * (Cerr - 1) ≤ ((Classical.choose shell.hXdyadic : ℕ) : ℝ)) :
    h4m1 manuscriptCdrop manuscriptC1 manuscriptEps ((Classical.choose shell.hXdyadic : ℕ) : ℝ) err
      ≤ manuscriptC1 * h4Y1 manuscriptEta manuscriptEps ((Classical.choose shell.hXdyadic : ℕ) : ℝ) := by
  refine failingShell_h4_calibration_of_large shell herr ?_
  have hgap : (1 - manuscriptEta) - (manuscriptCdrop - 1) = (7 / 8 : ℝ) := by
    unfold manuscriptEta manuscriptCdrop; norm_num
  have hce : manuscriptC1 * manuscriptEps = (1 / 16384 : ℝ) := by
    unfold manuscriptC1 manuscriptEps; norm_num
  rw [hgap, hce]
  have key : (1 : ℝ) / 16384 * ((Classical.choose shell.hXdyadic : ℕ) : ℝ) * (7 / 8)
      = 7 / 131072 * ((Classical.choose shell.hXdyadic : ℕ) : ℝ) := by ring
  rw [key]
  linarith [hL]

/-! ## Target 2-condition / 4 — carry scale and support hit (CLOSED from the scale gates) -/

/--
**The start threshold subsumes `aboveCarryThreshold`.**  The genuine "sufficiently large dyadic
`X`" gate `appendixNChainCompressionStartThreshold ≤ X` implies `aboveCarryThreshold`
(= `carryThreshold (carryB Q + 19) ≤ X`), since `carryThreshold (carryB Q + 19)` is a summand of
the start threshold. -/
theorem aboveCarryThreshold_of_startThreshold_le
    (shell : FailingDyadicShell)
    (hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd shell.hnonterm
        ≤ shell.X) :
    shell.aboveCarryThreshold :=
  le_trans carryThreshold_le_appendixNChainCompressionStartThreshold hXge

/--
**Target (DensePack scale, `Classical.choose` form), CLOSED from `aboveCarryThreshold`.**

The carry scale `carryB Q + 25 ≤ Classical.choose shell.hXdyadic` — the exact `hCarryLarge`
argument of `densePackFactoryDataCanonical` — derived from `aboveCarryThreshold` via
`carryLarge_of_carryThreshold_le`. -/
theorem failingShell_carryLarge_of_aboveCarryThreshold
    (shell : FailingDyadicShell) (hlarge : shell.aboveCarryThreshold) :
    carryB shell.Q + 25 ≤ Classical.choose shell.hXdyadic := by
  have hlarge' : carryThreshold (carryB shell.Q + 19) ≤ shell.X := hlarge
  exact carryLarge_of_carryThreshold_le (Classical.choose_spec shell.hXdyadic) hlarge'

/--
**Target (DensePack scale, `X = 2^L` form), CLOSED from `aboveCarryThreshold`.**  For an explicit
dyadic exponent `X = 2^L`, the carry scale reads `carryB Q + 25 ≤ L`. -/
theorem failingShell_carryLarge_of_aboveCarryThreshold_eq
    (shell : FailingDyadicShell) {L : ℕ} (hX_eq : shell.X = 2 ^ L)
    (hlarge : shell.aboveCarryThreshold) :
    carryB shell.Q + 25 ≤ L := by
  have hlarge' : carryThreshold (carryB shell.Q + 19) ≤ shell.X := hlarge
  exact carryLarge_of_carryThreshold_le hX_eq hlarge'

/--
**Target 4 (`1 ≤ supportCount d X`), CLOSED from the start threshold.**  Reuses the same engine
as `richShell_of_startThreshold_le`: the start threshold supplies a support hit at or below `X`.
The weaker `aboveCarryThreshold` gate alone does *not* give this. -/
theorem failingShell_supportCount_pos_of_startThreshold_le
    (shell : FailingDyadicShell)
    (hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd shell.hnonterm
        ≤ shell.X) :
    1 ≤ supportCount shell.d shell.X :=
  supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge

/-! ## Target DensePack `c0 ≤ κ/16` — REDUCED to the manuscript failure-constant pin

The bare `FailingDyadicShell` carries only `c0 < κ` (`hc0_lt_kappa`), which does **not** imply
`c0 ≤ κ/16`.  The manuscript pins the failure constant at `c0 = manuscriptC0 = κ/64` (the K.4
tighter form `c0 ≪ κ`); under that pin the DensePack small-density condition is CLOSED. -/

/--
**Target (DensePack small density `c0 ≤ κ/16`), CLOSED under the manuscript pin.**  Under
`shell.c0 = manuscriptC0` (= κ/64, the manuscript failure constant), `c0 ≤ κ/16` holds via
`manuscriptC0_le_kappa_div_sixteen`.  This is the exact `hc0Small` argument of
`densePackFactoryDataCanonical`. -/
theorem failingShell_c0_le_kappa_div_sixteen_of_pin
    (shell : FailingDyadicShell) (hpin : shell.c0 = manuscriptC0) :
    shell.c0 ≤ manuscriptKappa / 16 := by
  rw [hpin]; exact manuscriptC0_le_kappa_div_sixteen

/-! ## Bundle — `ShellScalarRegime` (the closeable per-shell scalar facts) -/

/--
The three closeable per-shell scalar facts feeding the DensePack factory datum and the linear
shell richness: the small-density constant `c0 ≤ κ/16`, the carry scale
`carryB Q + 25 ≤ Classical.choose shell.hXdyadic`, and the support hit `1 ≤ supportCount d X`. -/
structure ShellScalarRegime (shell : FailingDyadicShell) : Prop where
  /-- Small-density constant (Lemma I.4.1): `c0 ≤ κ/16`. -/
  c0Small : shell.c0 ≤ manuscriptKappa / 16
  /-- Large carry scale (DensePack / K.1.3): `carryB Q + 25 ≤ L` with `X = 2^L`. -/
  carryLarge : carryB shell.Q + 25 ≤ Classical.choose shell.hXdyadic
  /-- Support hit at or below `X` (A.1 companion): `1 ≤ supportCount d X`. -/
  supportPos : 1 ≤ supportCount shell.d shell.X

/--
**Bundle builder from the genuine start-threshold gate + the manuscript `c0` pin.**  From the
"sufficiently large dyadic `X`" gate `appendixNChainCompressionStartThreshold ≤ X` and the
manuscript failure-constant pin `c0 = manuscriptC0`, both scale facts are CLOSED and the small
density follows from the pin. -/
theorem shellRegime_of_failing_large
    (shell : FailingDyadicShell)
    (hpin : shell.c0 = manuscriptC0)
    (hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd shell.hnonterm
        ≤ shell.X) :
    ShellScalarRegime shell where
  c0Small := failingShell_c0_le_kappa_div_sixteen_of_pin shell hpin
  carryLarge := carryLarge_of_appendixNChainCompressionStartThreshold_le hXge
  supportPos := supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge

/--
**Bundle builder from the weaker `aboveCarryThreshold` gate.**  Under the weaker gate the carry
scale is still CLOSED, but the support hit must be supplied as the precise side input
`hSupport : 1 ≤ supportCount d X` (the `ShellWindowInputs.h_supportCount_pos` companion); the small
density follows from the manuscript `c0` pin. -/
theorem shellRegime_of_aboveCarryThreshold
    (shell : FailingDyadicShell)
    (hpin : shell.c0 = manuscriptC0)
    (hlarge : shell.aboveCarryThreshold)
    (hSupport : 1 ≤ supportCount shell.d shell.X) :
    ShellScalarRegime shell where
  c0Small := failingShell_c0_le_kappa_div_sixteen_of_pin shell hpin
  carryLarge := failingShell_carryLarge_of_aboveCarryThreshold shell hlarge
  supportPos := hSupport

/-- The DensePack reduced per-shell input (in-regime branch) built from the bundle. -/
def ShellScalarRegime.densePackRegimeInput {shell : FailingDyadicShell}
    (h : ShellScalarRegime shell) : DensePackRegimeInput shell :=
  Sum.inl (PLift.up ⟨h.c0Small, h.carryLarge⟩)

/-- The full canonical DensePack factory datum (cover/count/budget/packing all closed) built from
the bundle — the exact per-shell `densePack` factory atom of the capstone. -/
def ShellScalarRegime.densePackFactoryData {shell : FailingDyadicShell}
    (h : ShellScalarRegime shell) :
    DensePackFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ) :=
  densePackFactoryDataCanonical shell h.c0Small h.carryLarge

/-- `densePackRegimeInput` builds the same factory datum as `densePackFactoryData`. -/
theorem ShellScalarRegime.densePackRegimeInput_build {shell : FailingDyadicShell}
    (h : ShellScalarRegime shell) :
    h.densePackRegimeInput.build = h.densePackFactoryData :=
  rfl

/--
**Linear shell richness from the bundle.**  The bundle's support hit + carry scale feed
`richShell_card_choose` (manuscript A.1), giving `L + 1 ≤ |supportShell d X|`. -/
theorem ShellScalarRegime.richShell {shell : FailingDyadicShell}
    (h : ShellScalarRegime shell) :
    Classical.choose shell.hXdyadic + 1 ≤ (supportShell shell.d shell.X).card :=
  richShell_card_choose h.supportPos h.carryLarge

/-! ## Target 3 — Return regime `2·M_L ≤ s` (REDUCED to the asymptotic `M_L = o(s)`)

The Return scale `s` and the dirty multiplicity `M_L = cleanedDirtyEnvelope` are Return-side
quantities, not fields of the failing shell, so `2·M_L ≤ s` cannot be closed from failing-shell
data.  For the failing shell at large scale (`L → ∞`, i.e. the `atTop` filter) the manuscript
`M_L = o(r)` (a genuine asymptotic input, line 1614) yields the regime eventually. -/

/-- If `M_L = o(s)` (eventually nonnegative), then eventually `2·M_L ≤ s`.  The doubled form of
`ResidualScalarBudgets.eventually_le_half_of_isLittleO`. -/
theorem eventually_two_mul_le_of_isLittleO
    {mL sScale : ℕ → ℝ}
    (hmL : ∀ᶠ L in atTop, 0 ≤ mL L)
    (hs : ∀ᶠ L in atTop, 0 ≤ sScale L)
    (hlittleO : (fun L => mL L) =o[atTop] fun L => sScale L) :
    ∀ᶠ L in atTop, 2 * mL L ≤ sScale L := by
  filter_upwards [eventually_le_half_of_isLittleO hmL hs hlittleO] with L hL
  linarith

/--
**Target 3, asymptotic form for the concrete dirty envelope.**  If
`M_L = cleanedDirtyEnvelope logStar CM L = o(s)` (manuscript `M_L = o(r)`), then for the failing
shell at large scale the Return regime `2·M_L ≤ s` holds eventually. -/
theorem eventually_cleanedDirtyEnvelope_regime_of_isLittleO
    {logStar : ℕ → ℕ} {CM : ℕ} {sScale : ℕ → ℝ}
    (hs : ∀ᶠ L in atTop, 0 ≤ sScale L)
    (hlittleO :
      (fun L => (cleanedDirtyEnvelope logStar CM L : ℝ)) =o[atTop] fun L => sScale L) :
    ∀ᶠ L in atTop, 2 * (cleanedDirtyEnvelope logStar CM L : ℝ) ≤ sScale L := by
  have hmL : ∀ᶠ L in atTop, 0 ≤ (cleanedDirtyEnvelope logStar CM L : ℝ) := by
    filter_upwards with L
    exact_mod_cast Nat.zero_le _
  exact eventually_two_mul_le_of_isLittleO hmL hs hlittleO

/--
**Target 3, feeding the proved J.4 envelope budget.**  Under the asymptotic `M_L = o(s)`, the
failing shell at large scale eventually satisfies the J.4 envelope budget
`M_L·X·|I_j| ≤ s·X·|I_j|/2` consumed by `ReturnNestingCore.olc_ML_budget` (via the proved
`ResidualScalarBudgets.mL_budget_of_envelope_scale`). -/
theorem eventually_failingShell_mL_budget_of_isLittleO
    {logStar : ℕ → ℕ} {CM : ℕ} {sScale : ℕ → ℝ} {X ij : ℝ}
    (hXij : 0 ≤ X * ij)
    (hs : ∀ᶠ L in atTop, 0 ≤ sScale L)
    (hlittleO :
      (fun L => (cleanedDirtyEnvelope logStar CM L : ℝ)) =o[atTop] fun L => sScale L) :
    ∀ᶠ L in atTop,
      (cleanedDirtyEnvelope logStar CM L : ℝ) * X * ij ≤ sScale L * X * ij / 2 := by
  filter_upwards [eventually_cleanedDirtyEnvelope_regime_of_isLittleO hs hlittleO] with L hL
  exact mL_budget_of_envelope_scale hL hXij

/-! ## Non-vacuity — the added hypotheses are mutually consistent, never `False` -/

/-- `n ≤ 2^n` (elementary), used to certify the large-scale gate is achievable. -/
theorem nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    have hsplit : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
    have hk : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega

/-- **Non-vacuity of the large-scale gate.**  For any threshold `T` there is a dyadic scale
`X = 2^L ≥ T`, so the gate `appendixNChainCompressionStartThreshold ≤ X` (and the weaker
`aboveCarryThreshold`) is achievable, not vacuous. -/
theorem exists_dyadic_ge (T : ℕ) : ∃ L : ℕ, T ≤ 2 ^ L :=
  ⟨T, nat_le_two_pow T⟩

/-- **Non-vacuity of the `c0` pin.**  The manuscript failure constant `manuscriptC0 = κ/64` is a
consistent value for a `FailingDyadicShell`'s `c0` field — it satisfies `0 < c0`, `c0 < κ`,
`c0 ≤ cQ`, and the DensePack pin `c0 ≤ κ/16` — so `shell.c0 = manuscriptC0` is not a `False`
hypothesis. -/
theorem manuscriptC0_consistent :
    0 < manuscriptC0 ∧ manuscriptC0 < manuscriptKappa ∧
      manuscriptC0 ≤ erdos260Constants.cQ ∧ manuscriptC0 ≤ manuscriptKappa / 16 :=
  ⟨manuscriptC0_pos, manuscriptC0_lt_kappa, manuscriptC0_le_cQ,
    manuscriptC0_le_kappa_div_sixteen⟩

/-- **Non-vacuity of the Return asymptotic.**  The asymptotic regime input `M_L =o[atTop] s` is
satisfiable: e.g. the zero envelope is `o` of any positive scale, so the eventual regime
`2·M_L ≤ s` it produces is a genuine (non-`False`) consequence. -/
theorem return_regime_isLittleO_satisfiable :
    (fun _ : ℕ => (0 : ℝ)) =o[atTop] fun L => (L : ℝ) :=
  isLittleO_zero _ _

/-! ## Honest per-condition status inventory -/

/-- The honest status of each of the four per-shell scalar / regime side-conditions after this
file: which are CLOSED (derived from the failing shell) and which are REDUCED (and to what). -/
def shellRegimeClosureStatus : List String :=
  [ "Target 2 (Chernoff calibration m ≤ c₁Y, H.4 block length): CLOSED for the failing shell — " ++
      "the H.4 regime C_drop ≤ 2−η is pinned (manuscriptCdrop_lt_two_sub_eta) and the only scale " ++
      "input 0 ≤ c₁εL is automatic for X = 2^L (L : ℕ). failingShell_h4_calibration (err ≤ 1); " ++
      "failingShell_h4_calibration_of_largeL_explicit for an arbitrary O(1) bound err ≤ Cerr.",
    "Target DensePack scale (carryB Q + 25 ≤ L): CLOSED from aboveCarryThreshold via " ++
      "carryLarge_of_carryThreshold_le (failingShell_carryLarge_of_aboveCarryThreshold).",
    "Target DensePack small density (c0 ≤ κ/16): REDUCED to the manuscript failure-constant pin " ++
      "c0 = manuscriptC0 = κ/64 (the K.4 tighter form c0 ≪ κ). The bare FailingDyadicShell gives " ++
      "only c0 < κ (hc0_lt_kappa), insufficient. CLOSED under the pin " ++
      "(failingShell_c0_le_kappa_div_sixteen_of_pin, via manuscriptC0_le_kappa_div_sixteen).",
    "Target 3 (Return regime 2·M_L ≤ s, manuscript M_L = o(r)): REDUCED to the asymptotic " ++
      "M_L =o[atTop] s. The Return scale s and M_L = cleanedDirtyEnvelope are Return-side, not " ++
      "failing-shell fields, so it cannot be closed from shell data; at large scale (L → ∞) it " ++
      "holds eventually (eventually_cleanedDirtyEnvelope_regime_of_isLittleO) and feeds the J.4 " ++
      "budget (eventually_failingShell_mL_budget_of_isLittleO).",
    "Target 4 (1 ≤ supportCount d X): CLOSED from the start threshold " ++
      "appendixNChainCompressionStartThreshold ≤ X (failingShell_supportCount_pos_of_startThreshold_le, " ++
      "same engine as richShell_of_startThreshold_le). The weaker aboveCarryThreshold gate alone " ++
      "does NOT give it; under that gate it is carried as the side input hSupport.",
    "Bundle: ShellScalarRegime (c0Small, carryLarge, supportPos) with builders " ++
      "shellRegime_of_failing_large (start threshold + c0 pin) and shellRegime_of_aboveCarryThreshold " ++
      "(weaker gate + support side input + c0 pin); feeds densePackRegimeInput / densePackFactoryData " ++
      "and the linear richness ShellScalarRegime.richShell." ]

theorem shellRegimeClosureStatus_nonempty : shellRegimeClosureStatus ≠ [] := by
  simp [shellRegimeClosureStatus]

end

end Erdos260
