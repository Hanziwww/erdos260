import Erdos260.ShellRegimeClosure

/-!
# Unconditional providers for the DensePack (Class 3) and Return (Class 4) per-shell phases

This file (NEW; it edits no existing file) supplies the two per-shell factory providers consumed by
`GlobalAssemblyCoreInputs` (`Erdos260.GlobalClosureAssembly`):

```
densePack  : ∀ shell, shell.cQ = erdos260Constants.cQ →
               DensePackFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)
returnPkg  : ∀ shell, shell.cQ = erdos260Constants.cQ →
               ReturnFactoryData  erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)
```

together with the Return-mass nonnegativity `0 ≤ (returnPkg shell hcQ).massSum` that the coordinator
needs for `returnRunMassNonneg`.

## DensePack — the `c0 = κ/64` PIN IS ELIMINATED (main result)

The prior all-shells route `densePackRegime_field_of_pin`
(`Erdos260.DensePackUnconditionalClosure`) builds the genuine canonical datum
`densePackFactoryDataCanonical` only under the manuscript **K.4 failure-constant pin**
`hpin : shell.c0 = manuscriptC0 (= κ/64)`, used solely to reach `shell.c0 ≤ κ/16` for the I.4.1
smallness `proofV4DensePackSmallness_of_smallLarge`.  But a bare `FailingDyadicShell` only carries
`c0 < κ` (`hc0_lt_kappa`); the pin `∀ shell with cQ = …, c0 = κ/64` is **false** over the
over-quantified shell type (the `c0` field is free in `(0, κ)`), so that route is *not* genuinely
unconditional.

**Key arithmetic observation (`densePack_fortyKappa_le_budget`).**  The I.4.1 smallness only needs
`cStarSmall · (2·spread+1) ≤ cStar·ξ/6`, and on a large shell
`cStarSmall · (2·spread+1) = (c0/minHits)·(2·spread+1) ≤ 40·c0` (since `minHits ≥ L/8` and
`2·spread+1 ≤ 5L`).  Because

```
40·κ = 40·17/262144 = 680/262144  <  31/1536 = cStar·ξ/6
```

with a factor `≈ 7.8` of slack (`cStar·ξ/6 ÷ ((5/2)·κ) = 16`, and `40/(5/2) = 16`), the bound
`40·c0 ≤ cStar·ξ/6` holds for **every** `c0 < κ`.  Hence the genuine datum is built with NO `c0`
pin, using only `shell.hc0_lt_kappa` — a property of every failing shell.

`densePackProvider` is therefore total and the `aboveCarryThreshold` shells (the *only* shells the
assembly feeds: `startThreshold = carryThreshold (carryB Q + 19) = 2^(carryB Q + 25)`) carry the
**genuine** datum (real actual-support marker set `proofV4DensePackActualPoints`, positive spread,
positive density constant, I.4.1/K.1.3 budget), independent of `c0`.  Sub-threshold shells
(`¬ aboveCarryThreshold`) — never fed by the assembly, and where the manuscript provides no
large-scale dense packing (`AuditAnalyticInputs.audit_densePack_inRegime_forces_scale`: in-regime
forces `X ≥ 2^25`) — keep the faithful upper-bound fallback, exactly as the accepted baseline
`densePackRegime_field_of_pin` does on the same zone.

## Return — genuinely conditional on the per-shell return geometry (honest residual)

Unlike DensePack (whose genuine point set is built from the shell support windows), the Return OLC
dirty family `Finset DirtyCrossing` is NOT recoverable from a bare shell: the naive shell family
provably fails the K.2.5 envelope (`DirtyFaithfulFamilyCore`), and the regime `2·M_L ≤ s` is a
Return-side fact, not a shell field (`ShellRegimeClosure` Target 3).  So the sharpest honest Return
provider is parameterised by the per-shell genuine residual `GenuineReturnShellInput` — the proved
`ReturnFactoryReducedInput` (M.2.1 nesting + I.5.1 routing already theorems via
`ReturnNestingConstruction`) plus the manuscript nonnegativity of the three non-OLC return masses —
and `returnPkgProvider` then yields the exact `returnPkg` field with
`returnPkgProvider_massSum_nonneg` discharging the coordinator's Return-mass nonnegativity.

No `sorry`, `admit`, `native_decide`, or new `axiom`.  No false/vacuous hypotheses.  The only empty
witness is the sub-threshold DensePack fallback, used exclusively where no genuine large-scale
packing exists and which the assembly never reaches.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 1. DensePack — the K.4 numerical budget with the full `c0 < κ` margin -/

/-- **The I.4.1 budget holds with the full `c0 < κ` margin (no `c0 ≤ κ/16` pin).**

`40·κ ≤ cStar·ξ/6`.  Numerically `40·(17/262144) = 680/262144 < 31/1536 = cStar·ξ/6`.  This is `16×`
the pinned budget `(5/2)·κ ≤ cStar·ξ/6` (`erdos260_densePack_fixed_smallness_budget`); the factor
`16 = (κ/16)⁻¹·κ` is exactly the gap between the pinned `c0 ≤ κ/16` and the bare-shell `c0 < κ`,
so it is precisely the slack that lets the genuine datum drop the failure-constant pin. -/
theorem densePack_fortyKappa_le_budget :
    (40 : ℝ) * manuscriptKappa ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 := by
  unfold manuscriptKappa manuscriptCdrop manuscriptC1 manuscriptEps erdos260Constants
    manuscriptCstar manuscriptXi
  norm_num

/-- **The I.4.1 / K.1 final DensePack smallness, with the `c0 = κ/64` PIN REMOVED.**

Identical conclusion to `proofV4DensePackSmallness_of_smallLarge`, but the only `c0` hypothesis used
is `shell.hc0_lt_kappa : c0 < κ` — a field of **every** failing shell — instead of the pinned
`c0 ≤ κ/16`.  The `16×` slack in `densePack_fortyKappa_le_budget` absorbs the difference. -/
theorem densePackSmallness_of_carryLarge_c0free {shell : FailingDyadicShell}
    (hCarryLarge : carryB shell.Q + 25 ≤ Classical.choose shell.hXdyadic) :
    DensePackSmallnessInputData erdos260Constants.cStar erdos260Constants.ξ
      (shell.X : ℝ)
      (shell.c0 / (proofV4DensePackMinHits shell : ℝ))
      (proofV4DensePackSpread shell) where
  hsmall := by
    let L := Classical.choose shell.hXdyadic
    let m : ℝ := (proofV4DensePackMinHits shell : ℝ)
    let S : ℝ := ((2 * proofV4DensePackSpread shell + 1 : Nat) : ℝ)
    let C : ℝ := erdos260Constants.cStar * erdos260Constants.ξ / 6
    have hLge4Nat : 4 ≤ L := by omega
    have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
    have hm_lb : (L : ℝ) / 8 ≤ m := by
      simpa [L, m] using
        proofV4DensePackMinHits_ge_L_div_eight_of_carryLarge (shell := shell) hCarryLarge
    have hm_pos : 0 < m := by nlinarith [hm_lb, hLpos]
    have hS_nonneg : 0 ≤ S := by
      dsimp [S]; exact_mod_cast Nat.zero_le (2 * proofV4DensePackSpread shell + 1)
    have hS_le : S ≤ 5 * (L : ℝ) := by
      simpa [L, S] using
        proofV4DensePackSpread_factor_le_five_L_of_carryLarge (shell := shell) hCarryLarge
    have hk_nonneg : (0 : ℝ) ≤ manuscriptKappa := le_of_lt manuscriptKappa_pos
    have hc0_le : shell.c0 ≤ manuscriptKappa := le_of_lt shell.hc0_lt_kappa
    have hc0S : shell.c0 * S ≤ manuscriptKappa * (5 * (L : ℝ)) :=
      mul_le_mul hc0_le hS_le hS_nonneg hk_nonneg
    have hconst : manuscriptKappa * (5 * (L : ℝ)) ≤ C * ((L : ℝ) / 8) := by
      have hbudget := densePack_fortyKappa_le_budget
      dsimp [C] at hbudget ⊢
      nlinarith [hbudget, hLpos]
    have hC_nonneg : (0 : ℝ) ≤ C := by
      dsimp [C]
      exact le_of_lt
        (div_pos (mul_pos erdos260Constants.cStar_pos erdos260Constants.ξ_pos) (by norm_num))
    have hCm : C * ((L : ℝ) / 8) ≤ C * m := mul_le_mul_of_nonneg_left hm_lb hC_nonneg
    have hmul : shell.c0 * S ≤ C * m := hc0S.trans (hconst.trans hCm)
    have hcoef : shell.c0 / m * S ≤ C := by
      have hcoef' : shell.c0 * S / m ≤ C := by
        rw [div_le_iff₀ hm_pos]; exact hmul
      calc
        shell.c0 / m * S = shell.c0 * S / m := by ring
        _ ≤ C := hcoef'
    have hX_nonneg : (0 : ℝ) ≤ (shell.X : ℝ) := shell.X_nonneg_real
    calc
      (shell.c0 / (proofV4DensePackMinHits shell : ℝ)) * (shell.X : ℝ) *
            (((2 * proofV4DensePackSpread shell + 1 : Nat) : ℝ))
          = (shell.c0 / m * S) * (shell.X : ℝ) := by simp only [m, S]; ring
      _ ≤ C * (shell.X : ℝ) := mul_le_mul_of_nonneg_right hcoef hX_nonneg
      _ = erdos260Constants.cStar * erdos260Constants.ξ * (shell.X : ℝ) / 6 := by dsimp [C]; ring

/-! ## 2. DensePack — the genuine, `c0`-pin-free factory datum for a large shell -/

/-- **The genuine grounded DensePack datum for an above-threshold shell, with NO `c0` pin.**

Built from the canonical actual-support greedy density datum
(`DensePackProofV4ShellGreedyInputData.ofActualSupportWindows`):

* `densePackPoints` is the genuine actual-support marker set `proofV4DensePackActualPoints shell`;
* `markers` is the greedy maximal-separated marker family;
* `cover_input` is the K.1.2 neighbourhood cover from greedy maximality;
* `hcount` is the K.1.3 density-under-failure count (`shell.hfailure` + the K.1.5 packing);
* `hsmall` is the I.4.1 budget proved **without** the `c0 = κ/64` pin
  (`densePackSmallness_of_carryLarge_c0free`).

The only hypothesis is `hCarryLarge : carryB Q + 25 ≤ L` (`X = 2^L`), discharged from
`aboveCarryThreshold`. -/
def densePackGroundedLarge (shell : FailingDyadicShell)
    (hCarryLarge : carryB shell.Q + 25 ≤ Classical.choose shell.hXdyadic) :
    GroundedDensePackLocalData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ) :=
  let card := (DensePackProofV4ShellGreedyInputData.ofActualSupportWindows
    shell).toDensePackProofV4ShellCardinalityInputData
  { densePackPoints := card.densePackPoints
    markers := card.markers
    spread := proofV4DensePackSpread shell
    cover_input := card.cover.cover_input
    cStarSmall := shell.c0 / (proofV4DensePackMinHits shell : ℝ)
    hcount := card.hcount hCarryLarge
    hsmall := (densePackSmallness_of_carryLarge_c0free hCarryLarge).hsmall }

/-- **The genuine, `c0`-pin-free DensePack factory datum for an above-threshold shell.** -/
def densePackFactoryLarge (shell : FailingDyadicShell)
    (hCarryLarge : carryB shell.Q + 25 ≤ Classical.choose shell.hXdyadic) :
    DensePackFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ) :=
  (densePackGroundedLarge shell hCarryLarge).toDensePackFactoryData

/-- The genuine datum uses the **real** actual-support marker set (not the empty fallback). -/
theorem densePackFactoryLarge_points (shell : FailingDyadicShell)
    (hCarryLarge : carryB shell.Q + 25 ≤ Classical.choose shell.hXdyadic) :
    (densePackFactoryLarge shell hCarryLarge).densePackPoints
      = proofV4DensePackActualPoints shell := rfl

/-- The genuine datum's spread is `proofV4DensePackSpread shell = L + carryB Q + 1` (**positive**). -/
theorem densePackFactoryLarge_spread_pos (shell : FailingDyadicShell)
    (hCarryLarge : carryB shell.Q + 25 ≤ Classical.choose shell.hXdyadic) :
    0 < (densePackFactoryLarge shell hCarryLarge).spread := by
  show 0 < proofV4DensePackSpread shell
  unfold proofV4DensePackSpread
  omega

/-- The genuine datum's density constant is `c0/minHits` (**positive**: `c0 > 0`, `minHits > 0`). -/
theorem densePackFactoryLarge_cStarSmall_pos (shell : FailingDyadicShell)
    (hCarryLarge : carryB shell.Q + 25 ≤ Classical.choose shell.hXdyadic) :
    0 < (densePackFactoryLarge shell hCarryLarge).cStarSmall := by
  show 0 < shell.c0 / (proofV4DensePackMinHits shell : ℝ)
  apply div_pos shell.hc0_pos
  exact_mod_cast proofV4DensePackMinHits_pos_of_carryLarge hCarryLarge

/-- **The genuine I.4.1 / K.1.3 point-count budget, with NO `c0` pin.** -/
theorem densePackFactoryLarge_card_le_budget (shell : FailingDyadicShell)
    (hCarryLarge : carryB shell.Q + 25 ≤ Classical.choose shell.hXdyadic) :
    ((densePackFactoryLarge shell hCarryLarge).densePackPoints.card : ℝ)
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (shell.X : ℝ) / 6 :=
  (densePackGroundedLarge shell hCarryLarge).densePack_bound

/-! ## 3. DensePack — the total provider (genuine on every above-threshold shell) -/

/-- The faithful sub-threshold upper-bound fallback, used ONLY where no genuine large-scale
DensePack exists (`¬ aboveCarryThreshold`, equivalently `X < 2^(carryB Q + 25)`) and which the
global assembly never feeds (it pins `startThreshold = 2^(carryB Q + 25)`). -/
def densePackFactoryFallback (shell : FailingDyadicShell) :
    DensePackFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ) :=
  densePackFactoryData_trivial
    (div_nonneg
      (mul_nonneg
        (mul_nonneg erdos260Constants.cStar_pos.le erdos260Constants.ξ_pos.le)
        shell.X_nonneg_real)
      (by norm_num))

open Classical in
/-- **The DensePack provider, UNCONDITIONAL and `c0`-pin-FREE.**

Inhabits `GlobalAssemblyCoreInputs.densePack` with NO hypotheses: on every `aboveCarryThreshold`
shell (the only shells the assembly feeds) it uses the genuine `densePackFactoryLarge` (real marker
set, positive spread/density, I.4.1/K.1.3 budget), regardless of `shell.c0`; below threshold it uses
the faithful fallback. -/
def densePackProvider :
    ∀ shell : FailingDyadicShell, shell.cQ = erdos260Constants.cQ →
      DensePackFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ) :=
  fun shell _hcQ =>
    if h : shell.aboveCarryThreshold then
      densePackFactoryLarge shell (failingShell_carryLarge_of_aboveCarryThreshold shell h)
    else
      densePackFactoryFallback shell

/-- On every above-threshold shell, the provider yields the **genuine** datum (real marker set),
independent of `shell.c0`. -/
theorem densePackProvider_eq_genuine (shell : FailingDyadicShell)
    (hcQ : shell.cQ = erdos260Constants.cQ) (hlarge : shell.aboveCarryThreshold) :
    densePackProvider shell hcQ
      = densePackFactoryLarge shell (failingShell_carryLarge_of_aboveCarryThreshold shell hlarge) := by
  simp only [densePackProvider, dif_pos hlarge]

/-- Consequently, on every above-threshold shell the provider's point set is the genuine
actual-support marker set — never the empty fallback. -/
theorem densePackProvider_points (shell : FailingDyadicShell)
    (hcQ : shell.cQ = erdos260Constants.cQ) (hlarge : shell.aboveCarryThreshold) :
    (densePackProvider shell hcQ).densePackPoints = proofV4DensePackActualPoints shell := by
  rw [densePackProvider_eq_genuine shell hcQ hlarge]
  exact densePackFactoryLarge_points shell _

/-- The provider has exactly the type of the `GlobalAssemblyCoreInputs.densePack` field. -/
example :
    (∀ shell : FailingDyadicShell, shell.cQ = erdos260Constants.cQ →
      DensePackFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)) :=
  densePackProvider

/-! ## 4. Return — the genuine per-shell residual and the `returnPkg` provider -/

/-- **The genuine per-shell Return residual.**

The proved `ReturnFactoryReducedInput` (its M.2.1 nesting and I.5.1 routing are theorems via
`ReturnNestingConstruction`; the residue is the J.4 envelope `2·M_L ≤ s`, the M.2 return-slot
routing, the L.2.2 non-OLC counts, and the K.4 smallness) together with the manuscript fact that the
three non-OLC return masses are **nonnegative** (§I phase masses / J.1.1 charging: each is a count or
a weighted sum of nonnegative window weights).  The OLC mass `= |dirtyFamily|` is automatically
`≥ 0`. -/
structure GenuineReturnShellInput (shell : FailingDyadicShell) where
  /-- The proved reduced Return input (`2·M_L ≤ s` regime; nesting + routing already discharged). -/
  reduced : ReturnFactoryReducedInput erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)
  /-- §I/J.1.1 nonnegativity of the ordinary-short return mass. -/
  ordinaryShort_nonneg : 0 ≤ reduced.ordinaryShort
  /-- §I/J.1.1 nonnegativity of the semiperiodic-short return mass. -/
  semiperiodic_nonneg : 0 ≤ reduced.semiperiodic
  /-- §I/J.1.1 nonnegativity of the nonlocal-long return mass. -/
  nonlocalLong_nonneg : 0 ≤ reduced.nonlocalLong

/-- **The Return provider, built from a per-shell genuine residual.**

Yields exactly the `GlobalAssemblyCoreInputs.returnPkg` field type.  The OLC mass is the genuine
cleaned endpoint count `|dirtyFamily|`; the Prop. I.5.1 budget is `nonRunReturnBound_of_factory`. -/
def returnPkgProvider
    (provider : ∀ shell : FailingDyadicShell, shell.cQ = erdos260Constants.cQ →
        GenuineReturnShellInput shell) :
    ∀ shell : FailingDyadicShell, shell.cQ = erdos260Constants.cQ →
      ReturnFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ) :=
  fun shell hcQ => (provider shell hcQ).reduced.toFactoryData

/-- The provider has exactly the type of the `GlobalAssemblyCoreInputs.returnPkg` field. -/
example
    (provider : ∀ shell : FailingDyadicShell, shell.cQ = erdos260Constants.cQ →
        GenuineReturnShellInput shell) :
    (∀ shell : FailingDyadicShell, shell.cQ = erdos260Constants.cQ →
      ReturnFactoryData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)) :=
  returnPkgProvider provider

/-- The Return four-piece sum equals the genuine masses with the OLC slot `= |dirtyFamily|`. -/
theorem returnPkgProvider_massSum_eq
    (provider : ∀ shell : FailingDyadicShell, shell.cQ = erdos260Constants.cQ →
        GenuineReturnShellInput shell)
    (shell : FailingDyadicShell) (hcQ : shell.cQ = erdos260Constants.cQ) :
    (returnPkgProvider provider shell hcQ).massSum
      = (provider shell hcQ).reduced.ordinaryShort + (provider shell hcQ).reduced.semiperiodic
        + ((provider shell hcQ).reduced.dirtyFamily.card : ℝ)
        + (provider shell hcQ).reduced.nonlocalLong := rfl

/-- **Return-mass nonnegativity** (the coordinator's `returnRunMassNonneg` Return half).

`0 ≤ (returnPkgProvider provider shell hcQ).massSum`: the OLC mass is a cardinality, and the three
non-OLC masses are nonnegative by the §I / J.1.1 manuscript charging. -/
theorem returnPkgProvider_massSum_nonneg
    (provider : ∀ shell : FailingDyadicShell, shell.cQ = erdos260Constants.cQ →
        GenuineReturnShellInput shell)
    (shell : FailingDyadicShell) (hcQ : shell.cQ = erdos260Constants.cQ) :
    0 ≤ (returnPkgProvider provider shell hcQ).massSum := by
  rw [returnPkgProvider_massSum_eq]
  have h1 := (provider shell hcQ).ordinaryShort_nonneg
  have h2 := (provider shell hcQ).semiperiodic_nonneg
  have h3 := (provider shell hcQ).nonlocalLong_nonneg
  have h4 : (0 : ℝ) ≤ ((provider shell hcQ).reduced.dirtyFamily.card : ℝ) := Nat.cast_nonneg _
  linarith

/-- **Prop. I.5.1 Return budget** for the provider's datum (sanity: the genuine non-run return mass,
OLC slot `= |dirtyFamily|`, fits the return slot `cStar·ξ·X/6`). -/
theorem returnPkgProvider_nonRunReturn_bound
    (provider : ∀ shell : FailingDyadicShell, shell.cQ = erdos260Constants.cQ →
        GenuineReturnShellInput shell)
    (shell : FailingDyadicShell) (hcQ : shell.cQ = erdos260Constants.cQ) :
    (returnPkgProvider provider shell hcQ).massSum
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (shell.X : ℝ) / 6 :=
  nonRunReturnBound_of_factory (returnPkgProvider provider shell hcQ)

/-- **Non-vacuity certificate for the Return residual type.**

`GenuineReturnShellInput shell` is INHABITED for every shell (degenerate witness, all scales `0`):
the residual hypothesis is therefore genuinely satisfiable in principle, NOT a hidden contradiction
(contrast the round-2 `CNLUnconditionalKraftInput`, which is provably uninhabited).  This certifies
the Return reduction introduces no unsatisfiable obligation; it is a non-vacuity witness only, NOT a
closure (the masses/scales are `0`). -/
def genuineReturnShellInputTrivial (shell : FailingDyadicShell) :
    GenuineReturnShellInput shell where
  reduced :=
    { dirtyFamily := ∅
      ML := 0
      envelope := by simp
      shellSize := 0
      anchor_lt_shell := by intro x hx; simp at hx
      ordinaryShort := 0
      semiperiodic := 0
      nonlocalLong := 0
      c1 := 0, c2 := 0, c3 := 0, c4 := 0
      s := 0, ij := 0, smallError := 0
      shell_route := by simp
      hXij_area := by simp
      ml_regime := by norm_num
      olc_return_budget := by simp
      ordinaryShort_bound := by simp
      semiperiodic_bound := by simp
      nonlocalLong_bound := by simp
      hSmall := by
        simp only [add_zero, zero_mul, mul_zero]
        exact div_nonneg
          (mul_nonneg
            (mul_nonneg erdos260Constants.cStar_pos.le erdos260Constants.ξ_pos.le)
            shell.X_nonneg_real)
          (by norm_num) }
  ordinaryShort_nonneg := le_refl 0
  semiperiodic_nonneg := le_refl 0
  nonlocalLong_nonneg := le_refl 0

theorem genuineReturnShellInput_nonempty (shell : FailingDyadicShell) :
    Nonempty (GenuineReturnShellInput shell) :=
  ⟨genuineReturnShellInputTrivial shell⟩

/-! ## 5. Honest residual inventory -/

/-- The honest closed-vs-residual status of the two providers after this file. -/
def densePackReturnProviderResidual : List String :=
  [ "DensePack: c0 = κ/64 PIN ELIMINATED. densePackProvider is total; every aboveCarryThreshold " ++
      "shell carries the GENUINE densePackFactoryLarge (densePackProvider_points: real " ++
      "proofV4DensePackActualPoints; positive spread/density; densePackFactoryLarge_card_le_budget: " ++
      "card ≤ cStar·ξ·X/6) using ONLY c0 < κ (shell.hc0_lt_kappa), via the 16× slack " ++
      "densePack_fortyKappa_le_budget (40κ < cStar·ξ/6). No hpin.",
    "DensePack residual: only the large-scale gate aboveCarryThreshold (carryB Q + 25 ≤ L), " ++
      "discharged at the assembly from startThreshold = 2^(carryB Q + 25) ≤ X. Sub-threshold " ++
      "shells (never fed by the assembly; no large-scale packing per " ++
      "audit_densePack_inRegime_forces_scale) keep the faithful fallback densePackFactoryFallback.",
    "Return: returnPkgProvider yields the exact returnPkg field from a per-shell " ++
      "GenuineReturnShellInput; returnPkgProvider_massSum_nonneg gives 0 ≤ massSum.",
    "Return residual (irreducible from a bare shell): the per-shell GenuineReturnShellInput = the " ++
      "proved ReturnFactoryReducedInput (cleaned dirty family + K.2.5 envelope, I.5.1 shell " ++
      "containment, 2·M_L ≤ s regime, M.2 routing, L.2.2 non-OLC counts, K.4 smallness) + §I/J.1.1 " ++
      "mass nonnegativity. The dirty family is NOT recoverable from shell data (naive shell family " ++
      "fails the K.2.5 envelope, DirtyFaithfulFamilyCore); 2·M_L ≤ s is a Return-side fact " ++
      "(ShellRegimeClosure Target 3)." ]

theorem densePackReturnProviderResidual_nonempty :
    densePackReturnProviderResidual ≠ [] := by
  simp [densePackReturnProviderResidual]

#print axioms densePackProvider
#print axioms densePackFactoryLarge_card_le_budget
#print axioms returnPkgProvider
#print axioms returnPkgProvider_massSum_nonneg

end

end Erdos260
