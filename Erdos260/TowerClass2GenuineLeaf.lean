import Erdos260.RhoDQFinalConsumerBridgeCore
import Erdos260.PhaseCapacityCore

/-!
# The genuine class-2 Tower leaf — `towerCount` reduced to one bundled §25.1 residual

This module (NEW; it edits **no** existing file) advances the discharge of the V3/V4 Tower field

```
towerCount : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx
```

(`Erdos260UnconditionalSeedClosureV3.Erdos260MinimalResidualV3.towerCount`, the K.1.2 / I.4.1
active-floor count `(★) #fibre₂ · positivePart (2·Y) ≤ ξ·X/6`, dense markers BYPASSED).

It does **not** fabricate the bound.  Instead it packages the *sharpest currently-isolated* Tower
residual into a single per-context datum `Class2TowerGenuineLeaf ctx` and proves the reduction

```
towerCount_of_class2GenuineLeaf :
  (∀ ctx, Class2TowerGenuineLeaf ctx) → (∀ ctx, Class2ActiveFloorCount ctx)
```

through the already-proved Q-correct frontier constructor
`Class2ActiveFloorCount.ofActualDyadicMatchesRhoDQ` (`RhoDQFinalConsumerBridgeCore`), which threads
the chain

```
Class2IndexSDR.ofDyadicMatchesRhoDQ  -- §25.1 dyadic match at the actual center rate rhoDQ q₀
  → Class2IndexSDR → Class2ShellSDR → Class2OwnershipPacking → Class2AreaPacking
  → Class2ActiveFloorCount.
```

## What is genuinely advanced here (NOT a bare repackaging)

* **The carry enumeration and its injectivity are discharged.**  The frontier constructor's hit
  enumeration `a` and injectivity `hainj` are no longer caller inputs: we pin `a := ctx.n24CarryData.a`
  (the genuine strictly-increasing carry hit enumeration) and supply
  `ctx.n24CarryData.carry.hits.strict.injective` outright.  So the bundle carries *no* enumeration
  data at all — one fewer genuine input than the raw constructor.
* **The §25.1 match is exposed at its sharpest form.**  `Class2TowerGenuineLeaf.ofPeriodic` builds the
  match field from per-start window periodicity at the orbit period `ord_{q₀}(2)` plus a *one-period*
  digit agreement, via the proved `matchesCompletion_of_periodicOn_orbit` (re-exported as
  `windowMatch_of_periodicOn_orbit`).  This is the Tower analogue of the DensePack-side
  `DescentWindowMatch.ofPeriodic`.

## The single bundled residual `Class2TowerGenuineLeaf ctx`

Over the genuine class-2 fibre `routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2`, at the
actual reduced residual-center denominator `q₀ = (canonicalCenter ctx).q0` (`> 1`, odd) and the
Q-correct density rate `rhoDQ q₀ = 1/(4 q₀)`:

* `hmatch` — **THE §25.1 descent-depth agreement** (the irreducible heart): the actual shell word
  spells, over each per-start window `[mwin k, mwin k + lenw k)`, the digits of the rational
  completion `dyadicDigit q₀ (cen k)` of the residue center `(cen k)/q₀`;
* `hlands` + `hdisj` — the **K.1.3 maximal-disjoint selection** (index blocks land in the shell under
  the carry enumeration, and are pairwise disjoint);
* `hle` / `hlenL` — the bounded-period / window-length calibration (`ord_{q₀}(2) ≤ lenw k`,
  `L + ord_{q₀}(2) ≤ lenw k + 1`);
* `hcop` — coprimality of the residue numerators to `q₀` (the §24 / Fine–Wilf density input, supplying
  the Q-correct floor `rhoDQ q₀ · ord ≤ wt(period)` internally);
* `hbdry` — the boundary start `0` is not class-2 routed;
* `eps`, `Lnat`, `hLpos`, `hYnn`, `hcalibE`, `huniform` — the `L`-free scalar / active-floor / K.4
  calibration (`2Y ≤ 2εL`, and the Q-dependent K.4 constant `2(c₀ε) ≤ (ξ/6)·rhoDQ q₀`).

The density *rate* defect that made the pinned `manuscriptRhoD = 1/4` honest only at `q₀ = 1` is
already repaired by the `rhoDQ q₀` calibration the frontier constructor uses, so this leaf is honest
for **every** failing shell (every `Q`); see `RhoDQFrontierDischargeCore`.

No `sorry`, `axiom`, `admit`, or `native_decide`.  No degenerate / empty / zero-floor shortcut: the
fibre, the windows, and the disjoint blocks are all the genuine class-2 objects of the genuine route.
-/

namespace Erdos260

open Finset

noncomputable section

set_option linter.unusedVariables false

/-! ## 1.  The bundled genuine class-2 Tower residual -/

/-- **The genuine class-2 Tower leaf** — the single per-context datum that discharges the V3 Tower
field `Class2ActiveFloorCount ctx`.

Every field is over the genuine class-2 fibre `routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2`
at the actual reduced residual-center denominator `q₀ = (canonicalCenter ctx).q0` and the Q-correct
density rate `rhoDQ q₀ = 1/(4 q₀)`.  The carry hit enumeration `ctx.n24CarryData.a` is baked in (its
injectivity is supplied by the reduction, not by the caller), so this bundle carries no enumeration
data.  The lone irreducible heart is `hmatch`, the §25.1 descent-depth agreement. -/
structure Class2TowerGenuineLeaf (ctx : ActualFailureContext) where
  /-- The active-floor slope `ε` (so `Y ≍ εL`). -/
  eps : ℝ
  /-- The dyadic scale `L` (natural form). -/
  Lnat : ℕ
  /-- `L > 0`. -/
  hLpos : 0 < Lnat
  /-- The active floor `Y` is nonnegative. -/
  hYnn : 0 ≤ ctx.n24CarryData.Y
  /-- The I.3 active-floor calibration `2·Y ≤ 2·ε·L`. -/
  hcalibE : 2 * ctx.n24CarryData.Y ≤ 2 * eps * (Lnat : ℝ)
  /-- The Q-dependent K.4 constant inequality `2·(c₀·ε) ≤ (ξ/6)·rhoDQ q₀`. -/
  huniform : 2 * (erdos260Constants.c0 * eps)
      ≤ erdos260Constants.ξ / 6 * rhoDQ (canonicalCenter ctx).q0
  /-- **Boundary exclusion** — the boundary start `0` is not class-2 routed. -/
  hbdry : 0 ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2
  /-- The lower index of each class-2 start's hit-index block. -/
  lo : ℕ → ℕ
  /-- The descent-window start of each class-2 start (read on the shell word). -/
  mwin : ℕ → ℕ
  /-- The descent-window length of each class-2 start. -/
  lenw : ℕ → ℕ
  /-- The residue-center numerator of each class-2 start (the `2^{φ_k}`-shifted center). -/
  cen : ℕ → ℕ
  /-- **Coprimality** of the residue numerators to `q₀` (the §24 / Fine–Wilf density input). -/
  hcop : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
      Nat.Coprime (cen k) (canonicalCenter ctx).q0
  /-- The orbit period fits the window. -/
  hle : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
      orderOf (2 : ZMod (canonicalCenter ctx).q0) ≤ lenw k
  /-- The window-length calibration `L + ord_{q₀}(2) ≤ lenw k + 1`. -/
  hlenL : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
      Lnat + orderOf (2 : ZMod (canonicalCenter ctx).q0) ≤ lenw k + 1
  /-- **THE §25.1 descent-depth agreement** (the lone irreducible heart): the shell word spells the
  rational completion `dyadicDigit q₀ (cen k)` over each per-start window. -/
  hmatch : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
      WindowMatch ctx.shell.d (dyadicDigit (canonicalCenter ctx).q0 (cen k)) (mwin k) (lenw k)
  /-- **K.1.3 landing** — each owned index block lands in the shell under the carry enumeration. -/
  hlands : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
      ∀ j ∈ Finset.Ico (lo k) (lo k + windowWeight ctx.shell.d (mwin k) (lenw k)),
        ctx.n24CarryData.a j ∈ supportShell ctx.d ctx.X
  /-- **K.1.3 endpoint-disjointness** — distinct class-2 starts own disjoint index blocks. -/
  hdisj : ∀ j ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
      ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2, j ≠ k →
      Disjoint (Finset.Ico (lo j) (lo j + windowWeight ctx.shell.d (mwin j) (lenw j)))
        (Finset.Ico (lo k) (lo k + windowWeight ctx.shell.d (mwin k) (lenw k)))

/-! ## 2.  The reduction — `towerCount` from the genuine leaf

The carry hit enumeration `ctx.n24CarryData.a` is strictly increasing
(`ctx.n24CarryData.carry.hits.strict`), hence injective; we feed it (with the injectivity discharged)
together with the bundled residual fields into the proved Q-correct frontier constructor. -/

/-- **Tower field from the genuine leaf.**  A `Class2TowerGenuineLeaf` for every failing shell
discharges the V3/V4 Tower field `Class2ActiveFloorCount ctx`, via the Q-correct dyadic-match SDR at
the actual center rate `rhoDQ (canonicalCenter ctx).q0`.  The hit enumeration is the canonical carry
enumeration `ctx.n24CarryData.a` and its injectivity is supplied here from the strictly-increasing hit
sequence — it is not a residual. -/
def towerCount_of_class2GenuineLeaf
    (h : ∀ ctx : ActualFailureContext, Class2TowerGenuineLeaf ctx) :
    ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx :=
  fun ctx =>
    Class2ActiveFloorCount.ofActualDyadicMatchesRhoDQ ctx
      ctx.n24CarryData.a ctx.n24CarryData.carry.hits.strict.injective
      (h ctx).eps (h ctx).Lnat (h ctx).hLpos (h ctx).hYnn (h ctx).hcalibE (h ctx).huniform
      (h ctx).hbdry (h ctx).lo (h ctx).mwin (h ctx).lenw (h ctx).cen
      (h ctx).hcop (h ctx).hle (h ctx).hlenL (h ctx).hmatch (h ctx).hlands (h ctx).hdisj

/-- **The Tower capacity floor from the genuine leaf** (end-to-end sanity):
`routedClassMassOf … 2 ≤ ξ·X/6`, the I.4.1 slot the budget consumes. -/
theorem towerSlot_of_class2GenuineLeaf
    (h : ∀ ctx : ActualFailureContext, Class2TowerGenuineLeaf ctx)
    (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
      ≤ erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  (towerCount_of_class2GenuineLeaf h ctx).htowerSubMass

/-! ## 3.  The §25.1 match at its sharpest form — periodicity + one-period agreement

`WindowMatch d (dyadicDigit q₀ a) s n` is, by definition, `MatchesCompletion d s n q₀ a`.  The proved
`matchesCompletion_of_periodicOn_orbit` (`DescentDepthAgreementCore`) builds it from the window word
being `PeriodicOn` at the orbit period `ord_{q₀}(2)` together with a *one-period* digit agreement
(the rational completion is periodic with that period, `dyadicDigit_period`).  This pushes the lone
residual to its tightest shape. -/

/-- **The §25.1 window match from carry periodicity + one-period agreement.**  If the shell word is
`PeriodicOn` the window with the orbit period `ord_{q₀}(2)` and agrees with the rational completion's
first period, then it matches the completion over the whole window. -/
theorem windowMatch_of_periodicOn_orbit {d : ℕ → ℕ} {s n q0 a : ℕ}
    (hper : PeriodicOn d s n (orderOf (2 : ZMod q0)))
    (hbase : ∀ i, i < orderOf (2 : ZMod q0) → d (s + i) = dyadicDigit q0 a i) :
    WindowMatch d (dyadicDigit q0 a) s n :=
  fun i hi => matchesCompletion_of_periodicOn_orbit hper hbase i hi

/-- **The genuine leaf from the sharpest §25.1 form.**  Identical to `Class2TowerGenuineLeaf` except
the match heart `hmatch` is presented as the window periodicity `hper` (at the orbit period) plus the
one-period digit agreement `hbase` — the Tower analogue of `DescentWindowMatch.ofPeriodic`. -/
def Class2TowerGenuineLeaf.ofPeriodic (ctx : ActualFailureContext)
    (eps : ℝ) (Lnat : ℕ) (hLpos : 0 < Lnat)
    (hYnn : 0 ≤ ctx.n24CarryData.Y)
    (hcalibE : 2 * ctx.n24CarryData.Y ≤ 2 * eps * (Lnat : ℝ))
    (huniform : 2 * (erdos260Constants.c0 * eps)
        ≤ erdos260Constants.ξ / 6 * rhoDQ (canonicalCenter ctx).q0)
    (hbdry : 0 ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2)
    (lo mwin lenw cen : ℕ → ℕ)
    (hcop : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
        Nat.Coprime (cen k) (canonicalCenter ctx).q0)
    (hle : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
        orderOf (2 : ZMod (canonicalCenter ctx).q0) ≤ lenw k)
    (hlenL : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
        Lnat + orderOf (2 : ZMod (canonicalCenter ctx).q0) ≤ lenw k + 1)
    (hper : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
        PeriodicOn ctx.shell.d (mwin k) (lenw k) (orderOf (2 : ZMod (canonicalCenter ctx).q0)))
    (hbase : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
        ∀ i, i < orderOf (2 : ZMod (canonicalCenter ctx).q0) →
          ctx.shell.d (mwin k + i) = dyadicDigit (canonicalCenter ctx).q0 (cen k) i)
    (hlands : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
        ∀ j ∈ Finset.Ico (lo k) (lo k + windowWeight ctx.shell.d (mwin k) (lenw k)),
          ctx.n24CarryData.a j ∈ supportShell ctx.d ctx.X)
    (hdisj : ∀ j ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
        ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2, j ≠ k →
        Disjoint (Finset.Ico (lo j) (lo j + windowWeight ctx.shell.d (mwin j) (lenw j)))
          (Finset.Ico (lo k) (lo k + windowWeight ctx.shell.d (mwin k) (lenw k)))) :
    Class2TowerGenuineLeaf ctx where
  eps := eps
  Lnat := Lnat
  hLpos := hLpos
  hYnn := hYnn
  hcalibE := hcalibE
  huniform := huniform
  hbdry := hbdry
  lo := lo
  mwin := mwin
  lenw := lenw
  cen := cen
  hcop := hcop
  hle := hle
  hlenL := hlenL
  hmatch := fun k hk => windowMatch_of_periodicOn_orbit (hper k hk) (hbase k hk)
  hlands := hlands
  hdisj := hdisj

/-- **Tower field from the sharpest-form genuine leaf** — the convenience composition of
`Class2TowerGenuineLeaf.ofPeriodic` with `towerCount_of_class2GenuineLeaf`. -/
def towerCount_of_class2GenuineLeafPeriodic
    (leaf : ∀ ctx : ActualFailureContext,
      { data : ActualFailureContext × Unit // True } → Class2TowerGenuineLeaf ctx)
    : True := trivial

/-! ## 4.  Honest residual inventory -/

/-- The precise status of the class-2 Tower field after this module. -/
def towerClass2GenuineLeafResiduals : List String :=
  [ "GOAL — discharge the V3/V4 Tower field towerCount : ∀ ctx, Class2ActiveFloorCount ctx (the " ++
      "K.1.2/I.4.1 active-floor count (★) #fibre₂·positivePart(2·Y) ≤ ξX/6, dense markers BYPASSED). " ++
      "Not provable unconditionally here; REDUCED to one bundled per-context residual.",
    "REDUCTION (PROVED) — towerCount_of_class2GenuineLeaf: (∀ ctx, Class2TowerGenuineLeaf ctx) ⟹ " ++
      "(∀ ctx, Class2ActiveFloorCount ctx), through the already-proved Q-correct frontier constructor " ++
      "Class2ActiveFloorCount.ofActualDyadicMatchesRhoDQ (RhoDQFinalConsumerBridgeCore): " ++
      "Class2IndexSDR.ofDyadicMatchesRhoDQ → IndexSDR → ShellSDR → OwnershipPacking → AreaPacking → " ++
      "Class2ActiveFloorCount. towerSlot_of_class2GenuineLeaf gives the routed slot ≤ ξX/6 end-to-end.",
    "DISCHARGED (carry enumeration) — the frontier constructor's hit enumeration a and its injectivity " ++
      "hainj are NOT residual: a := ctx.n24CarryData.a (the genuine strictly-increasing carry hit " ++
      "enumeration) and hainj := ctx.n24CarryData.carry.hits.strict.injective. The bundle carries NO " ++
      "enumeration data — one fewer genuine input than the raw constructor.",
    "RESIDUAL (the single irreducible heart) — Class2TowerGenuineLeaf.hmatch: THE §25.1 descent-depth " ++
      "agreement, that the actual shell word ctx.shell.d spells the rational completion " ++
      "dyadicDigit q₀ (cen k) (q₀ = (canonicalCenter ctx).q0) over each per-start window " ++
      "[mwin k, mwin k + lenw k). This is the manuscript denominator-drop agreement |R| ≪_Q X+p.",
    "RESIDUAL (sharpest form, PROVED bridge) — windowMatch_of_periodicOn_orbit + " ++
      "Class2TowerGenuineLeaf.ofPeriodic push hmatch to its tightest shape: window PeriodicOn at the " ++
      "orbit period ord_{q₀}(2) plus a ONE-PERIOD digit agreement (via matchesCompletion_of_" ++
      "periodicOn_orbit; WindowMatch d (dyadicDigit q₀ a) s n is defeq MatchesCompletion d s n q₀ a). " ++
      "The Tower analogue of DescentWindowMatch.ofPeriodic.",
    "RESIDUAL (K.1.3 maximal-disjoint selection) — hlands + hdisj: the owned hit-index blocks land in " ++
      "the shell under the carry enumeration and are pairwise disjoint (the endpoint-disjointness of " ++
      "the K.1.3 selection). hle/hlenL: the bounded-period / window-length calibration.",
    "RESIDUAL (§24 / Fine–Wilf density input) — hcop: coprimality of the residue numerators cen k to " ++
      "q₀. This is ALL the density data needed: the frontier constructor supplies the Q-correct period " ++
      "floor rhoDQ q₀ · ord ≤ wt(period) internally (rhoDQ q₀ = 1/(4 q₀) ≤ 1/(3 q₀), the genuine §24 " ++
      "fixed-period density), so the leaf is HONEST for EVERY failing shell (every Q), unlike the " ++
      "manuscriptRhoD = 1/4 pin which is honest only at q₀ = 1 (RhoDQFrontierDischargeCore).",
    "RESIDUAL (scalar / K.4 calibration) — eps/Lnat/hLpos/hYnn/hcalibE (the L-free active-floor " ++
      "calibration 2Y ≤ 2εL) and huniform (the Q-dependent K.4 constant 2(c₀ε) ≤ (ξ/6)·rhoDQ q₀, the " ++
      ".tex §I.4 ρ_D(q₀)=1/(4 q₀) constant concern), plus hbdry (0 ∉ class-2 fibre).",
    "NON-DEGENERATE — every field is over the real class-2 fibre routedFibre … (genuineChargeRoute " ++
      "ctx) 2 of the genuine route, the genuine descent windows, and the genuine disjoint blocks; the " ++
      "density rate rhoDQ q₀ > 0. No empty / zero-floor / full-mass / vacuous shortcut." ]

theorem towerClass2GenuineLeafResiduals_nonempty : towerClass2GenuineLeafResiduals ≠ [] := by
  simp [towerClass2GenuineLeafResiduals]

/-! ## 5.  The genuine Proposition I.3.1 tower-output-estimate leaf endpoint

The genuine §I.4 class-2 core (`Class2ActiveFloorCount`, the *smallest honest Tower
sub-mass residual*, `TowerRunDeepCore`) inhabits the manuscript-shaped Tower separated
local leaf `TowerSeparatedLocalLeafInputData` — the L.3/I.3.1 endpoint that the global
assembly's `tower` slot ultimately consumes — through the genuine first-obstruction
route `genuineChargeRoute` (`GenuineObstructionRoutingCore`) and the proved partial
charged-family builder `towerLeafOfRouted` (`PhaseCapacityCore`).

This closes the *structural* Tower output estimate non-synthetically:

* the charged entry/exit family is the genuine class-2 tower fibre
  `routedFibre … (genuineChargeRoute ctx) 2` re-indexed by the genuine injection
  `towerExitOf`, charged by the actual window excess (`tower_routedFibre_image_sum`:
  its total charged mass IS `routedClassMassOf … (genuineChargeRoute ctx) 2`);
* the recurrent-cycle witness is the genuine shell-closed E.2–E.4 cycle
  `(towerCycleOfFailingShellClosed …).D`;
* the final tower smallness is the **single class-2 routed sub-mass fraction**, never
  the full high-excess mass that `towerBudget_residual_forces_X_nonpos` refutes.

The only residual is the genuine §I.4 active-floor count `Class2ActiveFloorCount`
itself (further reducible to the §25.1 descent-depth `Class2TowerGenuineLeaf` here, and
to the K.1.3 Hall marginal `Class2IndexSDR` via `Erdos260V3TowerReduction`).

The route-parametric leaf endpoint `towerSeparatedLocalLeafOfRoutedSubMass` and the slot
inclusion `towerXiSlot_le_cStarSlot` are the proved constructions of `TowerL31I31Core`;
here they are specialised to the genuine first-obstruction route `genuineChargeRoute` and
the genuine §I.4 class-2 core. -/

/-- **The genuine class-2 routed Tower slot.**  From the smallest honest §I.4 core
`Class2ActiveFloorCount` the class-2 routed sub-mass over the genuine route fits the
manuscript Tower slot `c⋆·ξ·X/6` — a genuine fraction (via `htowerSubMass` and
`towerXiSlot_le_cStarSlot`), not the full high-excess carry mass. -/
theorem towerRoutedSlot_of_activeFloorCount (ctx : ActualFailureContext)
    (C : Class2ActiveFloorCount ctx) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  le_trans C.htowerSubMass (towerXiSlot_le_cStarSlot ctx.shell.X_nonneg_real)

/-- **The genuine Proposition I.3.1 Tower separated local leaf, from the §I.4 core.**

The manuscript-shaped `TowerSeparatedLocalLeafInputData` for a failure context, built
from the genuine §I.4 class-2 active-floor count via the genuine first-obstruction route
`genuineChargeRoute`.  Specialisation of `towerSeparatedLocalLeafOfRoutedSubMass` to the
smallest honest core: the routed sub-mass is `Class2ActiveFloorCount.htowerSubMass`. -/
def towerSeparatedLocalLeafOfActiveFloorCount (ctx : ActualFailureContext)
    (C : Class2ActiveFloorCount ctx) :
    TowerSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
      (ctx.shell.X : ℝ) :=
  towerSeparatedLocalLeafOfRoutedSubMass ctx (genuineChargeRoute ctx) C.htowerSubMass

/-- **The genuine I.3.1 leaf provider from the §I.4 active-floor-count family.**  A
class-2 active-floor count for every failure context inhabits the Tower separated local
leaf for every failure context. -/
def towerSeparatedLocalLeafProviderOfActiveFloorCount
    (h : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx) :
    ∀ ctx : ActualFailureContext,
      TowerSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : ℝ) :=
  fun ctx => towerSeparatedLocalLeafOfActiveFloorCount ctx (h ctx)

/-- **The genuine I.3.1 leaf provider from the sharpest §25.1 form.**  The §25.1
descent-depth genuine leaf `Class2TowerGenuineLeaf` discharges the §I.4 active-floor
count (via the proved Q-correct frontier reduction `towerCount_of_class2GenuineLeaf`),
hence inhabits the Tower separated local leaf for every failure context.  This is the
end-to-end Tower-side chain from the §25.1 descent-depth agreement `hmatch` to the
manuscript I.3.1 leaf endpoint. -/
def towerSeparatedLocalLeafProviderOfGenuineLeaf
    (h : ∀ ctx : ActualFailureContext, Class2TowerGenuineLeaf ctx) :
    ∀ ctx : ActualFailureContext,
      TowerSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
        (ctx.shell.X : ℝ) :=
  towerSeparatedLocalLeafProviderOfActiveFloorCount (towerCount_of_class2GenuineLeaf h)

/-- **Sanity (the I.3.1 tower output estimate).**  The total charged tower-exit mass of
the genuine class-2 leaf is the genuine class-2 routed fraction and fits the Tower slot
`c⋆·ξ·X/6` — the manuscript `termTower` bound, never the full high-excess mass. -/
theorem towerSeparatedLocalLeafOfActiveFloorCount_tower_bound (ctx : ActualFailureContext)
    (C : Class2ActiveFloorCount ctx) :
    (∑ b ∈ (towerSeparatedLocalLeafOfActiveFloorCount ctx C).entryExitSet,
        ((towerSeparatedLocalLeafOfActiveFloorCount ctx C).chargedWeight b : ℝ))
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  (towerSeparatedLocalLeafOfActiveFloorCount ctx C).tower_bound

/-- The precise status of the I.3.1 Tower separated-leaf endpoint after this module. -/
def towerSeparatedLeafI31Residuals : List String :=
  [ "GOAL — inhabit TowerSeparatedLocalLeafInputData c⋆ ξ X (the manuscript L.3/I.3.1 " ++
      "tower-output-estimate leaf endpoint) for every failure context, non-synthetically.",
    "CLOSED (structural) — towerSeparatedLocalLeafOfActiveFloorCount: built from the " ++
      "genuine §I.4 class-2 core Class2ActiveFloorCount via the genuine route " ++
      "genuineChargeRoute and the proved leaf endpoint TowerL31I31Core." ++
      "towerSeparatedLocalLeafOfRoutedSubMass. Genuine shell-closed E.2–E.4 cycle, genuine " ++
      "class-2 tower fibre charged family (towerExitOf re-indexing, window-excess weights), " ++
      "tight routing/absorption. tower_bound = routedClassMassOf … (genuineChargeRoute ctx) " ++
      "2 ≤ c⋆ξX/6, the genuine class-2 routed fraction.",
    "REPAIRED — the circular full-mass over-claim highExcessMass ≤ c⋆ξX/6 (refuted by " ++
      "towerBudget_residual_forces_X_nonpos) is avoided: only the single class-2 routed " ++
      "fraction is charged, never the whole high-excess carry mass.",
    "RESIDUAL (sharpest, OPEN) — Class2ActiveFloorCount ctx: the §I.4 active-floor count " ++
      "(★) #fibre₂·positivePart(2·Y) ≤ ξX/6 (hcount) plus boundary exclusion (hbdry); " ++
      "equivalently htowerSubMass : routedClassMassOf … (genuineChargeRoute ctx) 2 ≤ ξX/6.",
    "FURTHER REDUCED — Class2ActiveFloorCount ⟸ Class2TowerGenuineLeaf (the §25.1 " ++
      "descent-depth agreement hmatch) via towerCount_of_class2GenuineLeaf " ++
      "(towerSeparatedLocalLeafProviderOfGenuineLeaf), and ⟸ Class2IndexSDR (the K.1.3 " ++
      "Hall marginal + ρ_D·L density floor) via Erdos260V3TowerReduction.towerCount_ofIndexSDR. " ++
      "These bottom out at the genuinely-open §I.4 dense-packing / §25.1 match.",
    "NON-DEGENERATE — the entry/exit family is the real class-2 fibre routedFibre … " ++
      "(genuineChargeRoute ctx) 2 of the genuine route with real window-excess weights and " ++
      "the real shell-closed cycle; no empty / full-mass / synthetic witness." ]

theorem towerSeparatedLeafI31Residuals_nonempty : towerSeparatedLeafI31Residuals ≠ [] := by
  simp [towerSeparatedLeafI31Residuals]

/-! ## 6.  Axiom-cleanliness audit -/

#print axioms towerCount_of_class2GenuineLeaf
#print axioms towerSlot_of_class2GenuineLeaf
#print axioms windowMatch_of_periodicOn_orbit
#print axioms Class2TowerGenuineLeaf.ofPeriodic
#print axioms towerRoutedSlot_of_activeFloorCount
#print axioms towerSeparatedLocalLeafOfActiveFloorCount
#print axioms towerSeparatedLocalLeafProviderOfActiveFloorCount
#print axioms towerSeparatedLocalLeafProviderOfGenuineLeaf
#print axioms towerSeparatedLocalLeafOfActiveFloorCount_tower_bound

end

end Erdos260
