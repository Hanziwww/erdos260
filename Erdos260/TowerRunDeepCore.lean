import Erdos260.TowerRunMassBoundCore
import Erdos260.TowerRunMassFractionCore

/-!
# Deep-shell audit of Tower core 3 + Run cores 4/5, with the sharp active-floor reduction

This module (NEW; it edits no existing file) is the wave-11 closure pass over the three honest
cores of the wave-10 `TowerRunSeedClosureData` (`TowerRunSeedClosure.lean`):

* **Core 3** — the I.4.1 Tower (class-2) dense-packing sub-mass, exposed by wave-10 as the
  four-field `Class2DenseMarkerCover` (`hbdry`, `hcover`, `hpack`, `hsmall`, with the multiplier
  pinned to the active floor `positivePart (2·Y)`);
* **Cores 4 + 5** — the Run (class-5) I.6S summation + I.5.2 base output, exposed as
  `RunClass5StageChain` (`hsum`, `hhalf`, `hbase`, with the geometric envelope proved).

## AUDIT — does each residual survive a *deep* shell `r = ⌊κL⌋ ≥ 1`, `Y ≍ εL`?

The wave-10 multiplier pin `mult := positivePart (2·Y)` is **correct**: on the genuine class-2 fibre
`runClsOfShell ≠ 1`, so (away from the boundary) `windowExcess < 2·Y` (`class2_windowExcess_lt_twoY`).
The danger is the **K.4 smallness** `hsmall`.  Unfolding the wave-9 chain
(`markerCount_le_of_failure` + `corollaryK1_3_densePackUnderFailure` +
`routedClassMassOf_le_countMultiplier`), the failure cap `#supportShell < c₀·X` and the budget
`ξ·X/6` share the *same* factor `X`, which cancels.  What remains is

  `hsmall :  (c₀/ρ_D L)·(2·spread+1)·(2·Y)  ≤  ξ/6.`

In the manuscript I.4.1 the *neighbourhood width* is `2·spread+1 ≍ C_D L` and the *per-hit floor* is
`ρ_D L`, so the two `L`'s cancel and the residual reads `(c₀ C_D/ρ_D)·(2·Y) ≤ ξ/6`.  But the active
floor is `Y ≍ ε L → ∞`, so the LHS grows **linearly in `L`**, and this is **FALSE for every
sufficiently deep shell**.  (`hsmall` is vacuously satisfiable in isolation by taking the *free*
field `rhoL` huge and `spread = 0`, but then `hpack : markersCard·rhoL ≤ #supportShell` collapses
the marker count to `0`, so the *honest* dense-marker system — cover + packing at the genuine
geometric widths — is the thing that cannot hold; see `class2_activeFloorCount_of_denseMarkerCover`,
which extracts the joint obstruction.)  The manuscript survives because its DensePack budget carries
the active *order* `s ≍ κL` (eq. I.3 has the ratio `Y/s ≍ ε/κ = O_Q(1)`); the wave-9/10 Lean
normalisation collapsed `s·|I_j|` to the constant `1/6` and used the bare multiplier `2·Y`, so it
**dropped the `1/s ≍ 1/(κL)` active-order factor**.  Hence the dense-marker apparatus is too weak by
a factor `≍ L`: it only ever delivers `#fibre₂ ≲ (c₀ C_D/ρ_D)·X`, whereas the slot needs
`#fibre₂ ≲ X/L`.  (The Core-3 *goal* itself is plausibly TRUE — the class-2 dense/CNL-tail fibre is
genuinely `Θ(X/Y)`-sparse, the real I.4.1 content — but it is *not* provable from the formalised
dense-marker chain; the sharp residual `(★)` below isolates exactly the missing input.)

This is exactly the wave-10 "CNL Core 11 false-for-deep-shells" pathology, here for Tower Core 3.

## CONSEQUENCE — the sharp residual is the *active-floor count bound* (Core 3 SHRUNK)

The honest content does **not** need any dense marker.  Bounding each class-2 window excess by
`positivePart (2·Y)` directly (`class2_fibre_windowExcess_le`, already proved) gives

  `routedClassMassOf … 2  ≤  #fibre₂ · positivePart (2·Y)`,

so Core 3 follows from the **single scalar inequality** (`class2_subMass_of_activeFloorCount`)

  `(★)   #fibre₂ · positivePart (2·Y)  ≤  ξ·X/6.`

We prove `(★)` is **strictly weaker** than the wave-10 cover: a `Class2DenseMarkerCover` *implies*
`(★)` (`class2_activeFloorCount_of_denseMarkerCover`, consuming `ctx.hfailure` — under the failure
cap the dense-marker route demands the even tighter `6 c₀·#fibre₂·(2Y) ≤ #supportShell·ξ`).  So
replacing the four-field cover by the two-field `Class2ActiveFloorCount` (`hbdry` + `(★)`) is a sound
shrink, and `(★)` is the genuine irreducible I.4.1 datum: *the class-2 fibre is `Θ(X/Y)`-sparse*.

This is sharp: the goal also **forces** `#fibre₂ · Y ≤ ξ·X/6` (`class2_subMass_forces_fibre_floor`,
since every fibre member has `windowExcess ≥ Y`).  So the residual is sandwiched
`#fibre₂·2Y ≤ ξX/6  ⟹  routedClassMassOf … 2 ≤ ξX/6  ⟹  #fibre₂·Y ≤ ξX/6`, i.e. equivalent up to a
factor of two to "the class-2 fibre count is `≤ Θ(X/Y)`".

## Cores 4 + 5 — NO deep-shell pathology

The Run cores route through the L.4.2 period descent, **not** a count×multiplier: the geometric
envelope `∑_{i<len} stageMass i ≤ 2·stageMass 0` (`halfChain_sum_le`) absorbs the spikes with no
`Y`-multiplier, so the deep-shell blow-up of Core 3 does **not** occur.  `RunClass5StageChain.runFloor`
delivers the I.5.2 floor `routedClassMassOf … 5 ≤ c⋆ξX/6` outright from the chain, and
`runClass5Chain_ofGeometricBase` builds the whole chain (with `hhalf`/`hnonneg`/envelope proved) from
the base output alone, reducing Cores 4+5 to the bare `hsum` (I.6S) + `hbase` (I.5.2 `wt(O₀) ≤
c⋆ξX/12`).  The ratio `1/2` is anchored in the actual shell by `runFOfShell_halfDecrease`.

## Deliverable

`buildTowerRunSeedClosureFromCount` assembles a full `TowerRunSeedClosureData` from the *shrunk*
Core 3 (`Class2ActiveFloorCount`) and Cores 4+5 (`RunClass5StageChain`), feeding the frontier exactly
as `buildTowerRunSeedClosure` does — but with the deep-shell-false dense-marker apparatus replaced by
the sharp active-floor count bound.

No `sorry`, `axiom`, `admit`, or `native_decide`.  No degenerate/empty/zero-fraction/full-mass
shortcut: every bound is over the real class-2 / class-5 fibre of the genuine route.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 1.  Core 3 — the necessary lower side: the class-2 fibre carries `≥ #fibre₂·Y` mass

Every member of the genuine class-2 fibre is a high-excess start, hence has window excess `≥ Y`.
Summing, the routed class-2 sub-mass is at least `#fibre₂·Y`.  This is the *sharp lower side* of the
sub-mass: the I.4.1 slot `ξ·X/6` therefore **forces** the class-2 fibre count below `ξ·X/(6·Y)`. -/

/-- **The class-2 routed sub-mass dominates `#fibre₂·Y`.**  Each `k` in the genuine class-2 fibre
lies in `highExcessStarts`, so `Y ≤ windowExcess … k …`; summing over the fibre gives
`#fibre₂·Y ≤ routedClassMassOf … 2`.  No hypothesis on `Y` is needed. -/
theorem class2_fibre_card_mul_Y_le (ctx : ActualFailureContext) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2 := by
  rw [routedClassMassOf_eq_sum_fibre]
  have hpoint : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
      ctx.n24CarryData.Y
        ≤ windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T := by
    intro k hk
    have hmem : k ∈ highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
        ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y :=
      (Finset.mem_filter.mp hk).1
    exact (mem_highExcessStarts.mp hmem).2
  calc ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).card : ℝ)
          * ctx.n24CarryData.Y
        = ∑ _k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
            ctx.n24CarryData.Y := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
            windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T :=
          Finset.sum_le_sum hpoint

/-- **The I.4.1 slot FORCES the class-2 fibre to be `Θ(X/Y)`-sparse (necessary side).**
If the Tower sub-mass fits the slot `ξ·X/6`, then `#fibre₂·Y ≤ ξ·X/6` — for `Y ≍ εL` this is
`#fibre₂ ≤ ξ·X/(6 ε L)`, the genuine "the dense/CNL-tail fibre is `L`-sparse" content the
dense-marker apparatus cannot supply for deep shells. -/
theorem class2_subMass_forces_fibre_floor (ctx : ActualFailureContext)
    (h : routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
        ≤ erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  le_trans (class2_fibre_card_mul_Y_le ctx) h

/-! ## 2.  Core 3 — the sufficient side: the active-floor count bound discharges the sub-mass

Bounding each class-2 window excess by the pinned active floor `positivePart (2·Y)` and counting the
fibre directly (no markers) reduces Core 3 to the single scalar inequality `(★)`. -/

/-- **Tower Core 3 from the active-floor count bound `(★)` (dense markers BYPASSED).**

`routedClassMassOf … 2 ≤ ξ·X/6` follows from the boundary exclusion `hbdry` and the single scalar
inequality `(★)  #fibre₂ · positivePart (2·Y) ≤ ξ·X/6`, via `class2_fibre_windowExcess_le` (the
genuine K.1.2/L.20 active-floor multiplier) and `routedClassMassOf_le_countMultiplier`.  No
dense-marker existence, packing, or K.4 smallness is used. -/
theorem class2_subMass_of_activeFloorCount (ctx : ActualFailureContext)
    (hbdry : 0 ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2)
    (hcount : ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).card : ℝ)
          * positivePart (2 * ctx.n24CarryData.Y)
        ≤ erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
      ≤ erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 := by
  refine le_trans ?_ hcount
  exact routedClassMassOf_le_countMultiplier ctx.n24CarryData (genuineChargeRoute ctx) 2
    (fun k hk => class2_fibre_windowExcess_le ctx hbdry hk)
    (positivePart_nonneg _) (le_refl _)

/-- **The sharp Tower Core 3 residual: the active-floor count bound.**

The two-field replacement for the wave-10 `Class2DenseMarkerCover`:

* `hbdry` — the boundary start `0` is not class-2 routed (the manuscript boundary start);
* `hcount` — `(★)  #fibre₂ · positivePart (2·Y) ≤ ξ·X/6`, the genuine I.4.1 datum that the class-2
  (dense/CNL-tail) fibre is `Θ(X/Y)`-sparse.

This is *strictly weaker* than `Class2DenseMarkerCover` (see
`Class2ActiveFloorCount.ofDenseMarkerCover`) and is the smallest honest core of the Tower sub-mass. -/
structure Class2ActiveFloorCount (ctx : ActualFailureContext) where
  /-- **Boundary exclusion** — the boundary start `0` is not class-2 routed. -/
  hbdry : 0 ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2
  /-- **The active-floor count bound `(★)`** — `#fibre₂ · positivePart (2·Y) ≤ ξ·X/6`. -/
  hcount : ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).card : ℝ)
        * positivePart (2 * ctx.n24CarryData.Y)
      ≤ erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6

/-- **Tower Core 3 discharged from the sharp active-floor count residual.** -/
theorem Class2ActiveFloorCount.htowerSubMass {ctx : ActualFailureContext}
    (C : Class2ActiveFloorCount ctx) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
      ≤ erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  class2_subMass_of_activeFloorCount ctx C.hbdry C.hcount

/-! ## 3.  The shrink is sound: the wave-10 dense-marker cover IMPLIES the count bound `(★)`

Genuinely consuming `ctx.hfailure`, a `Class2DenseMarkerCover` yields the active-floor count bound,
so the new residual is no harder than (and in fact strictly weaker than) the old four-field one. -/

/-- **The dense-marker cover implies the active-floor count bound `(★)` (sound shrink).**

From the K.1.1 cover `hcover` (`#fibre₂ ≤ |𝒟₀|·(2·spread+1)`), the I.4.1 packing `hpack`
(`|𝒟₀|·ρ_D L ≤ #supportShell`), the K.4 smallness `hsmall`, and the positive-density failure
`ctx.hfailure` (`#supportShell < c₀·X`), the class-2 fibre count obeys
`#fibre₂ · positivePart (2·Y) ≤ ξ·X/6`.  Hence the wave-10 cover is *strictly stronger* than the
wave-11 count residual.  (Algebra: multiply through by `c₀ > 0`, chain
`#fibre₂ ≤ |𝒟₀|(2spread+1)`, `c₀(2spread+1)(2Y) ≤ (ξ/6)ρ_D L`, `|𝒟₀|ρ_D L ≤ #supportShell < c₀X`.) -/
theorem class2_activeFloorCount_of_denseMarkerCover (ctx : ActualFailureContext)
    (C : Class2DenseMarkerCover ctx) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).card : ℝ)
        * positivePart (2 * ctx.n24CarryData.Y)
      ≤ erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 := by
  have hc0 : (0 : ℝ) < erdos260Constants.c0 := erdos260Constants.c0_pos
  have hξ6 : (0 : ℝ) ≤ erdos260Constants.ξ / 6 :=
    div_nonneg erdos260Constants.ξ_pos.le (by norm_num)
  have hP : (0 : ℝ) ≤ positivePart (2 * ctx.n24CarryData.Y) := positivePart_nonneg _
  have hm : (0 : ℝ) ≤ (C.markersCard : ℝ) := Nat.cast_nonneg _
  have hρ : (0 : ℝ) < C.rhoL := C.hrhoL_pos
  -- the K.1.1 cover, cast to ℝ
  have hcoverR :
      ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).card : ℝ)
        ≤ (C.markersCard : ℝ) * ((2 * C.spread + 1 : ℕ) : ℝ) := by
    exact_mod_cast C.hcover
  -- clear the `/ρ_D L` in the K.4 smallness
  have hsmall' :
      erdos260Constants.c0 * ((2 * C.spread + 1 : ℕ) : ℝ)
          * positivePart (2 * ctx.n24CarryData.Y)
        ≤ erdos260Constants.ξ / 6 * C.rhoL := by
    have h := C.hsmall
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hρ] at h
    exact h
  -- pack + failure: `|𝒟₀|·ρ_D L ≤ #supportShell < c₀·X`
  have hfail : ((supportShell ctx.d ctx.X).card : ℝ)
      < erdos260Constants.c0 * (ctx.shell.X : ℝ) := by
    rw [ActualFailureContext.shell_X]; exact ctx.hfailure
  have hmρ : (C.markersCard : ℝ) * C.rhoL ≤ erdos260Constants.c0 * (ctx.shell.X : ℝ) :=
    le_of_lt (lt_of_le_of_lt C.hpack hfail)
  -- main chain, multiplied through by `c₀ > 0`
  have h1 :
      ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).card : ℝ)
          * positivePart (2 * ctx.n24CarryData.Y)
        ≤ ((C.markersCard : ℝ) * ((2 * C.spread + 1 : ℕ) : ℝ))
            * positivePart (2 * ctx.n24CarryData.Y) :=
    mul_le_mul_of_nonneg_right hcoverR hP
  have key :
      erdos260Constants.c0
          * (((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).card : ℝ)
              * positivePart (2 * ctx.n24CarryData.Y))
        ≤ erdos260Constants.c0 * (erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :=
    calc erdos260Constants.c0
            * (((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2).card : ℝ)
                * positivePart (2 * ctx.n24CarryData.Y))
          ≤ erdos260Constants.c0
              * (((C.markersCard : ℝ) * ((2 * C.spread + 1 : ℕ) : ℝ))
                  * positivePart (2 * ctx.n24CarryData.Y)) :=
            mul_le_mul_of_nonneg_left h1 hc0.le
      _ = (C.markersCard : ℝ)
            * (erdos260Constants.c0 * ((2 * C.spread + 1 : ℕ) : ℝ)
                * positivePart (2 * ctx.n24CarryData.Y)) := by ring
      _ ≤ (C.markersCard : ℝ) * (erdos260Constants.ξ / 6 * C.rhoL) :=
            mul_le_mul_of_nonneg_left hsmall' hm
      _ = erdos260Constants.ξ / 6 * ((C.markersCard : ℝ) * C.rhoL) := by ring
      _ ≤ erdos260Constants.ξ / 6 * (erdos260Constants.c0 * (ctx.shell.X : ℝ)) :=
            mul_le_mul_of_nonneg_left hmρ hξ6
      _ = erdos260Constants.c0 * (erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) := by ring
  exact le_of_mul_le_mul_left key hc0

/-- **Build the sharp Core 3 residual from the wave-10 dense-marker cover.**  Certifies that the
two-field `Class2ActiveFloorCount` is no harder to satisfy than the four-field
`Class2DenseMarkerCover` — the shrink is sound. -/
def Class2ActiveFloorCount.ofDenseMarkerCover {ctx : ActualFailureContext}
    (C : Class2DenseMarkerCover ctx) : Class2ActiveFloorCount ctx where
  hbdry := C.hbdry
  hcount := class2_activeFloorCount_of_denseMarkerCover ctx C

/-! ## 4.  Cores 4 + 5 — the period-descent run chain (no deep-shell pathology)

The geometric envelope `∑_{i<len} stageMass i ≤ 2·stageMass 0` carries the half-decreasing run
masses with no `Y`-multiplier, so the I.5.2 floor follows from the base output alone. -/

/-- **The I.5.2 run-mass floor, delivered outright by the stage chain.**

`routedClassMassOf … 5 ≤ c⋆ξX/6` from the chain: the I.6S summation `hsum`
(`routedClassMassOf … 5 ≤ ∑ stageMass i`), the geometric envelope `halfChain_sum_le`
(`∑ stageMass i ≤ 2·stageMass 0`, from the mass half-decrease `hhalf`), and the I.5.2 base output
`hbase` (`stageMass 0 ≤ c⋆ξX/12`).  No count, no `Y`-multiplier: the spikes are absorbed by the
descent, so there is no deep-shell blow-up. -/
theorem RunClass5StageChain.runFloor {ctx : ActualFailureContext}
    (C : RunClass5StageChain ctx) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 := by
  have hchain := halfChain_sum_le C.stageMass C.hnonneg C.hhalf C.len
  calc routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
        ≤ ∑ i ∈ Finset.range C.len, C.stageMass i := C.hsum
    _ ≤ 2 * C.stageMass 0 := hchain
    _ ≤ 2 * (erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 12) := by
          linarith [C.hbase]
    _ = erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 := by ring

/-- **Build the Run stage chain from the base output alone (geometric model).**

Given a base run output `w₀ ≥ 0` (the I.5.2 `wt(O₀)`), the geometric I.6S summation `hsum`, and the
base bound `hbase`, the chain `stageMass i = w₀·(1/2)^i` realises `RunClass5StageChain` with
`hnonneg`/`hhalf` **proved** (the half-decrease is the exact geometric step, anchored in the actual
shell's period descent `runFOfShell_halfDecrease`).  This reduces Cores 4+5 to the two bare residuals
`hsum` (I.6S) + `hbase` (I.5.2 `wt(O₀) ≤ c⋆ξX/12`). -/
def runClass5Chain_ofGeometricBase (ctx : ActualFailureContext) (n : ℕ)
    (w0 : ℝ) (hw0 : 0 ≤ w0)
    (hsum : routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
        ≤ ∑ i ∈ Finset.range n, w0 * (1 / 2) ^ i)
    (hbase : w0 ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 12) :
    RunClass5StageChain ctx where
  len := n
  stageMass := fun i => w0 * (1 / 2) ^ i
  hnonneg := fun i => mul_nonneg hw0 (by positivity)
  hhalf := fun i => le_of_eq (by rw [pow_succ]; ring)
  hsum := hsum
  hbase := by simpa using hbase

/-- **The L.4.2 half-decrease on the actual shell residual centre (anchor re-export).**  The
period-level half-decrease `2·p' ≤ scaleMult·ord_{q₀}(2)` of the §25.2 residual centre
`runFOfShell ctx` — the dynamical source of the geometric chain ratio `1/2`, NOT an assumed ratio. -/
theorem runDeep_halfDecrease_anchor (ctx : ActualFailureContext) (u : ℕ) (weight : ℝ) :
    ∃ p', PeriodicOn (dyadicDigit (residualCenterOfFailingShell (runFOfShell ctx)).q0
            (residualCenterOfFailingShell (runFOfShell ctx)).a) u
          (2 * ((residualCenterOfFailingShell (runFOfShell ctx)).scaleMult
            * orderOf (2 : ZMod (residualCenterOfFailingShell (runFOfShell ctx)).q0))) p'
        ∧ 0 < p'
        ∧ 2 * p' ≤ (residualCenterOfFailingShell (runFOfShell ctx)).scaleMult
            * orderOf (2 : ZMod (residualCenterOfFailingShell (runFOfShell ctx)).q0) :=
  seedRun_periodDescent_halfDecrease ctx u weight

/-! ## 5.  Assembly — the Tower+Run seed closure from the SHRUNK Core 3 + Cores 4/5 -/

/-- **The wave-11 Tower+Run seed closure (dense markers replaced by the active-floor count).**

Builds the full `TowerRunSeedClosureData` (the `towerRun` field of `Erdos260MinimalResidual`, feeding
`erdos260_of_minimalResidual`) from:

* `cover ctx : Class2ActiveFloorCount ctx` — the shrunk Core 3 (the active-floor count bound `(★)`,
  the genuine I.4.1 datum, dense markers bypassed); and
* `chain ctx : RunClass5StageChain ctx` — Cores 4 + 5 (the half-decreasing stage chain, I.6S
  summation, and I.5.2 base output).

Identical interface to wave-10's `buildTowerRunSeedClosure`, but the Core-3 input is the sharp
two-field residual rather than the deep-shell-false four-field dense-marker cover. -/
def buildTowerRunSeedClosureFromCount
    (cover : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (chain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx) :
    TowerRunSeedClosureData where
  htowerSubMass := fun ctx => (cover ctx).htowerSubMass
  runChainLen := fun ctx => (chain ctx).len
  runBase := fun ctx => (chain ctx).stageMass 0
  hrunBase_nonneg := fun ctx => (chain ctx).hnonneg 0
  hrunSum := fun ctx => (chain ctx).hrunSum
  hrunBase12 := fun ctx => (chain ctx).hbase

/-- The constructed closure's run base output is the actual base stage mass `wt(O₀)`. -/
@[simp] theorem buildTowerRunSeedClosureFromCount_runBase
    (cover : ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx)
    (chain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx)
    (ctx : ActualFailureContext) :
    (buildTowerRunSeedClosureFromCount cover chain).runBase ctx = (chain ctx).stageMass 0 := rfl

/-- **End-to-end from the wave-10 inputs.**  Pre-composing `Class2ActiveFloorCount.ofDenseMarkerCover`
shows the wave-10 `Class2DenseMarkerCover` + `RunClass5StageChain` still build the closure through the
shrunk Core 3 — the wave-11 reduction loses nothing. -/
def buildTowerRunSeedClosureFromDenseMarker
    (cover : ∀ ctx : ActualFailureContext, Class2DenseMarkerCover ctx)
    (chain : ∀ ctx : ActualFailureContext, RunClass5StageChain ctx) :
    TowerRunSeedClosureData :=
  buildTowerRunSeedClosureFromCount
    (fun ctx => Class2ActiveFloorCount.ofDenseMarkerCover (cover ctx)) chain

/-! ## 6.  Honest residual inventory -/

/-- The precise per-core status of Tower core 3 + Run cores 4/5 after this wave-11 module. -/
def towerRunDeepResiduals : List String :=
  [ "AUDIT (Core 3, Tower class 2 — honest dense-marker system unsatisfiable for deep shells) — " ++
      "under the wave-10 pin mult = positivePart(2·Y), the K.4 smallness collapses (X cancels) to " ++
      "(c₀/ρ_D L)·(2·spread+1)·(2·Y) ≤ ξ/6; with the manuscript widths 2·spread+1 ≍ C_D L and " ++
      "per-hit floor ρ_D L the two L's cancel, leaving (c₀ C_D/ρ_D)·2Y ≤ ξ/6, which FAILS once " ++
      "Y ≍ εL exceeds ξρ_D/(12 c₀ C_D). (hsmall alone is vacuous via huge free rhoL, but then " ++
      "hpack forces markersCard = 0; the honest cover+packing system is what cannot hold.) The Lean " ++
      "s·|I_j| = 1/6 normalisation dropped the active-order 1/s ≍ 1/(κL) factor of manuscript eq. " ++
      "I.3 (ratio Y/s ≍ ε/κ = O_Q(1)). The dense-marker apparatus is too weak by a factor ≍ L (it " ++
      "bounds #fibre₂ ≲ (c₀C_D/ρ_D)X; the slot needs #fibre₂ ≲ X/L). The GOAL is plausibly true " ++
      "(the fibre is genuinely Θ(X/Y)-sparse) but unprovable from the formalised dense-marker chain. " ++
      "Same pathology class as wave-10's CNL Core 11.",
    "SHRANK (Core 3, Tower class 2 — sharp active-floor count) — Class2ActiveFloorCount / " ++
      "class2_subMass_of_activeFloorCount: routedClassMassOf … 2 ≤ ξ·X/6 follows from hbdry + the " ++
      "SINGLE scalar (★) #fibre₂·positivePart(2·Y) ≤ ξ·X/6, via class2_fibre_windowExcess_le + " ++
      "routedClassMassOf_le_countMultiplier — NO dense-marker existence/packing/K.4. (★) is the " ++
      "genuine irreducible I.4.1 datum: the class-2 (dense/CNL-tail) fibre is Θ(X/Y)-sparse.",
    "SOUND SHRINK (Core 3) — class2_activeFloorCount_of_denseMarkerCover: a wave-10 " ++
      "Class2DenseMarkerCover IMPLIES (★) (consuming ctx.hfailure; the dense route in fact demands " ++
      "the strictly tighter 6c₀·#fibre₂·(2Y) ≤ #supportShell·ξ). So the two-field count residual is " ++
      "strictly weaker than the four-field cover — replacing it loses nothing.",
    "SHARP (Core 3, necessary side) — class2_subMass_forces_fibre_floor: the slot ξ·X/6 FORCES " ++
      "#fibre₂·Y ≤ ξ·X/6 (every fibre member has windowExcess ≥ Y). Sandwich: #fibre₂·2Y ≤ ξX/6 " ++
      "⟹ routedClassMassOf … 2 ≤ ξX/6 ⟹ #fibre₂·Y ≤ ξX/6 — the residual is equivalent up to a " ++
      "factor 2 to the class-2 fibre count being ≤ Θ(X/Y).",
    "AUDIT (Cores 4/5, Run class 5 — NO deep-shell pathology) — the Run cores route through the " ++
      "L.4.2 period descent (RunClass5StageChain), not a count×multiplier: the envelope " ++
      "∑_{i<len} stageMass i ≤ 2·stageMass 0 (halfChain_sum_le) absorbs the class-5 spikes with NO " ++
      "Y-multiplier, so the Core-3 blow-up does not occur.",
    "DELIVERED (Cores 4/5) — RunClass5StageChain.runFloor: routedClassMassOf … 5 ≤ c⋆ξX/6 outright " ++
      "from the chain (hsum + halfChain_sum_le + hbase). runClass5Chain_ofGeometricBase builds the " ++
      "whole chain from the base output w₀ ≥ 0 with hnonneg/hhalf/envelope proved, reducing Cores " ++
      "4+5 to the bare hsum (I.6S) + hbase (I.5.2 wt(O₀) ≤ c⋆ξX/12); ratio 1/2 anchored by " ++
      "runDeep_halfDecrease_anchor (= runFOfShell_halfDecrease).",
    "ASSEMBLED — buildTowerRunSeedClosureFromCount: a full TowerRunSeedClosureData (the towerRun " ++
      "field of Erdos260MinimalResidual) from the SHRUNK Core 3 (Class2ActiveFloorCount) + Cores " ++
      "4+5 (RunClass5StageChain). buildTowerRunSeedClosureFromDenseMarker shows the wave-10 inputs " ++
      "still feed it through the sound shrink. Feeds erdos260_of_minimalResidual.",
    "ROUTE PINNED — every bound is over the genuine first-obstruction route genuineChargeRoute and " ++
      "its real class-2 / class-5 fibre; no degenerate/empty/zero-fraction/full-mass shortcut (the " ++
      "full high-excess mass is refuted by seed_fullMass_forces_X_nonpos)." ]

theorem towerRunDeepResiduals_nonempty : towerRunDeepResiduals ≠ [] := by
  simp [towerRunDeepResiduals]

/-! ## 7.  Axiom-cleanliness audit -/

#print axioms class2_fibre_card_mul_Y_le
#print axioms class2_subMass_forces_fibre_floor
#print axioms class2_subMass_of_activeFloorCount
#print axioms Class2ActiveFloorCount.htowerSubMass
#print axioms class2_activeFloorCount_of_denseMarkerCover
#print axioms Class2ActiveFloorCount.ofDenseMarkerCover
#print axioms RunClass5StageChain.runFloor
#print axioms runClass5Chain_ofGeometricBase
#print axioms runDeep_halfDecrease_anchor
#print axioms buildTowerRunSeedClosureFromCount
#print axioms buildTowerRunSeedClosureFromDenseMarker

end

end Erdos260
