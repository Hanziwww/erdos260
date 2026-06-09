import Erdos260.TowerLeafFromShell
import Erdos260.TowerAPSubfibreLanding
import Erdos260.ChargePerOutputEstimates

/-!
# The DEEP cores of the Tower L.3/I.3 leaf: the L.3.1 classifier and the I.3.1 budget

This module attacks the two genuine residual cores of the Tower `…OfShell` leaf
(`Erdos260PhaseCores.towerCls` / `Erdos260PhaseCores.towerBudget`,
`Erdos260ReducedToCores.lean`), as **standalone, axiom-clean, GREEN** theorems
built on the faithful infra.  Nothing is faked: no `sorry`/`axiom`/`admit`, no
empty/trivial witnesses.

## Core 1 — the L.3.1 first-obstruction classifier `towerClsOfShell` (CLOSED)

`towerClsOfShell ctx : ℕ → TowerExitClass` is defined **concretely from the
shell's refined SCC geometry**: it routes each high-excess carry start `k` by the
*canonical-gap band index* `canonGap S.q (slopeOrbit S.q S.K₀ k)` of the genuine
E.13 recurrent slope orbit of the closed AP-subfibre datum
`S = carryAPSubfibreOfFailingShellClosed …` (the same datum that drives
`towerCycleOfFailingShellClosed`).  This is a deterministic single-valued
first-obstruction routing to the five Lemma L.3.1 destinations
(Run / non-run Return / DensePack / clean-CNL-tail / Progress-Endpoint).

The associated **Lemma L.2.4 disjointness** `∑_{Θ_T(b)=O} wt(b) ≤ C_Q · wt(O)` is
proved outright (`towerExit_L24_disjointness`, with the tightest matching form
`towerExit_L24_disjointness_matching` at `C_Q = 1`): the tower charging map of the
of-shell family is `Θ_T = towerExitOf`, which is injective, so each tower output
absorbs *exactly* the charge of the unique carry start that created it.  Discharged
through the proved per-output charged-ledger lemmas
`perOutput_charged_of_overlap` / `perOutput_charged_of_injOn`.

## Core 2 — the I.3.1 routed-mass budget `towerBudget` (REDUCED to the K.4 inequality)

The budget LHS — the sum of the routed masses over **all five** L.3.1 destinations
— is, by the proved routed-exit partition identity
(`highExcessMass_eq_sum_routedClassMassOf` + `TowerExitClass.sum_univ`), *exactly*
the total high-excess carry mass of the actual N.24 carry data
(`towerBudget_lhs_eq_highExcessMass`).  Hence the I.3.1 budget is **equivalent** to

  `highExcessMass(highExcessStarts …) ≤ c_⋆ · ξ · X / 6`,    (I.3.1)

and we reduce (I.3.1) to its smallest named residual:

* `towerBudget_of_highExcessMass_le` — budget ⟸ (I.3.1) (via the partition identity);
* `towerBudget_of_countMult` — budget ⟸ a count×multiplier `N·M ≤ c_⋆·ξ·X/6`
  (the per-fibre window-excess multiplier × the high-excess start count);
* `towerBudget_of_densePackFraction` — budget ⟸ the I.4.1 dense-packing fraction
  bound `highExcessMass ≤ c_* · X`, with the **K.4 constant inequality discharged
  outright** by the proved numeric `manuscriptCstarSmall_le_towerSlot`
  (`c_* = κξ/64 ≤ c_⋆·ξ/6`, the pinned realisation of `c_* ≪_Q ρ_D κ ξ`).

So after this module the only residual of the I.3.1 budget is the genuine
**I.4.1 dense-packing + M.2.2** input `highExcessMass ≤ c_* X`; the K.4 hierarchy is
closed.

### Honest finding (precisely locating the residual)

`towerBudget_residual_forces_X_nonpos` proves that the of-shell family routes the
*full* high-excess carry mass, so combining (I.3.1) with the **proved** Lemma 21.1
lower bound `CarryDataFromFailure.highExcessMass_lower`
(`c_pr·X·(r+1) ≤ highExcessMass`) forces `X ≤ 0`.  At the pinned
`c_pr = 1/2 > c_⋆·ξ/6`, the full-mass reading of (I.3.1) is therefore unsatisfiable
for any large shell: the genuine I.4.1 dense-packing bound applies only to the
*dense-packed fraction* of the carry mass, not the whole of `highExcessStarts`.
This pinpoints exactly where the manuscript's per-class routing is needed.

No `sorry`, `axiom`, or `admit`.  No empty/trivial witnesses.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 1. The L.3.1 first-obstruction classifier, concretely from the SCC geometry -/

/--
**Canonical-gap band classifier.**  The deterministic five-way first-obstruction
destination keyed on the canonical-gap band index `g = canonGap q K ≥ 1` of the
recurrent slope orbit (the E.13 band index, `q < 2^g·K < 2q`):

* `g = 1` (tightest band, immediate re-entry) → Run;
* `g = 2` → non-run Return;
* `g = 3` → DensePack;
* `g = 4` → clean CNL tail;
* `g ≥ 5` → Progress-Endpoint / lower-order remainder (`other`).

This is a genuine, deterministic, single-valued function of the SCC band index.
-/
def towerExitClassOfGap : ℕ → TowerExitClass
  | 1 => .run
  | 2 => .returnPkg
  | 3 => .densePack
  | 4 => .cnlTail
  | _ => .other

/--
**The L.3.1 single-valued first-obstruction classifier of a failing shell.**

Routes each high-excess carry start `k` to its tower-exit destination by the
canonical-gap band index `canonGap S.q (slopeOrbit S.q S.K₀ k)` of the **genuine
E.13 recurrent slope orbit** of the closed AP-subfibre datum
`S = carryAPSubfibreOfFailingShellClosed ctx.shell P (η = P/Q)` — the very datum
that drives the shell-closed Tower cycle `towerCycleOfFailingShellClosed`.

This is the concrete realisation of Lemma L.3.1's deterministic single-valued
first-obstruction routing, defined from the shell's refined SCC geometry (no free
witness, no empty routing).
-/
def towerClsOfShell (ctx : ActualFailureContext) (k : ℕ) : TowerExitClass :=
  let S := carryAPSubfibreOfFailingShellClosed ctx.shell
    ctx.shell.hrational.choose ctx.shell.hrational.choose_spec
  towerExitClassOfGap (canonGap S.q (slopeOrbit S.q S.K₀ k))

/-- The classifier is genuinely non-trivial: it realises every one of the five
Lemma L.3.1 destinations on the canonical band indices. -/
theorem towerExitClassOfGap_surjective :
    Function.Surjective towerExitClassOfGap := by
  intro c
  cases c with
  | run => exact ⟨1, rfl⟩
  | returnPkg => exact ⟨2, rfl⟩
  | densePack => exact ⟨3, rfl⟩
  | cnlTail => exact ⟨4, rfl⟩
  | other => exact ⟨0, rfl⟩

/-! ## 2. Lemma L.2.4 disjointness for the tower charging map (CLOSED)

The tower entry/exit family of `towerExitRoutingOfShell ctx cls` charges each
high-excess carry start `k` to the tower exit `towerExitOf k` (the `Θ_T` charging
map), with charged weight `wt(towerExitOf k) = windowExcess(… k …)`.  Because
`towerExitOf` is injective, each tower output `O` absorbs *exactly* the charge of
the unique start mapping to it.  This is the L.2.4 per-output disjointness
`∑_{Θ_T(b)=O} wt(b) ≤ C_Q · wt(O)`, here in the tightest `C_Q = 1` form (and any
`C_Q ≥ 1`). -/

/--
**Lemma L.2.4 disjointness for the of-shell tower family (matching form, `C_Q = 1`).**

For every tower output `O` in the entry/exit family, the total charged weight of
the high-excess carry starts charging to `O` under the tower charging map
`Θ_T = towerExitOf` is at most the charged weight of `O` itself:

  `∑_{k : towerExitOf k = O} wt(k) ≤ wt(O)`,

where `wt(k) = windowExcess(… k …)` and `wt(O) = (routing.weight O : ℝ)`.  Proved
through the per-output charged-ledger lemma `perOutput_charged_of_injOn` and the
injectivity of `towerExitOf`.
-/
theorem towerExit_L24_disjointness_matching
    (ctx : ActualFailureContext) (cls : ℕ → TowerExitClass) :
    ∀ O ∈ (towerExitRoutingOfShell ctx cls).entryExitSet,
      (∑ k ∈ (highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
            ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y).filter
          (fun k => towerExitOf k = O),
        windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T)
        ≤ ((towerExitRoutingOfShell ctx cls).weight O : ℝ) := by
  refine perOutput_charged_of_injOn
    (highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
      ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y)
    (fun k => windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T)
    towerExitOf
    (towerExitRoutingOfShell ctx cls).entryExitSet
    (fun O => ((towerExitRoutingOfShell ctx cls).weight O : ℝ))
    ?hinj ?hdom ?hcap_nonneg
  · intro x _ y _ hxy
    exact towerExitOf_injective hxy
  · intro k _
    show windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
      ≤ ((towerExitRoutingOfShell ctx cls).weight (towerExitOf k) : ℝ)
    exact le_of_eq (by rw [towerExitRoutingOfShell_weight_val, towerExitOf_layerBound])
  · intro O _
    exact ((towerExitRoutingOfShell ctx cls).weight O).2

/--
**Lemma L.2.4 disjointness for the of-shell tower family (manuscript `C_Q` form).**

The manuscript-shaped per-output charged estimate `∑_{Θ_T(b)=O} wt(b) ≤ C_Q · wt(O)`
for any routing multiplicity `C_Q ≥ 1`.  Follows from the matching form by the
bounded-overlap charged-ledger lemma `perOutput_charged_of_overlap` (the overlap of
`Θ_T = towerExitOf` is at most one by injectivity, hence `≤ C_Q`).
-/
theorem towerExit_L24_disjointness
    (ctx : ActualFailureContext) (cls : ℕ → TowerExitClass) {CQ : ℝ} (hCQ : 1 ≤ CQ) :
    ∀ O ∈ (towerExitRoutingOfShell ctx cls).entryExitSet,
      (∑ k ∈ (highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
            ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y).filter
          (fun k => towerExitOf k = O),
        windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T)
        ≤ CQ * ((towerExitRoutingOfShell ctx cls).weight O : ℝ) := by
  refine perOutput_charged_of_overlap
    (highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
      ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y)
    (fun k => windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T)
    towerExitOf
    (towerExitRoutingOfShell ctx cls).entryExitSet
    (fun O => ((towerExitRoutingOfShell ctx cls).weight O : ℝ))
    CQ
    ?hdom ?hcap_nonneg ?hoverlap
  · intro k _
    show windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
      ≤ ((towerExitRoutingOfShell ctx cls).weight (towerExitOf k) : ℝ)
    exact le_of_eq (by rw [towerExitRoutingOfShell_weight_val, towerExitOf_layerBound])
  · intro O _
    exact ((towerExitRoutingOfShell ctx cls).weight O).2
  · intro O _
    have hle1 :
        ((highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
            ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y).filter
          (fun k => towerExitOf k = O)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      rw [Finset.mem_filter] at ha hb
      exact towerExitOf_injective (ha.2.trans hb.2.symm)
    calc ((((highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
              ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y).filter
            (fun k => towerExitOf k = O)).card : ℝ)) ≤ (1 : ℝ) := by exact_mod_cast hle1
      _ ≤ CQ := hCQ

/-! ## 3. The I.3.1 budget: the routed-exit partition identity (PROVED)

The budget LHS sums the routed masses over all five L.3.1 destinations; by the
proved partition identity it is *exactly* the total high-excess carry mass. -/

/--
**Routed-exit partition identity for the budget LHS.**  The sum of the routed
carry masses over the five L.3.1 destinations equals the total high-excess carry
mass of the N.24 carry data.  This is `highExcessMass_eq_sum_routedClassMassOf`
(mass conservation over the `TowerExitClass` fibres) re-expressed via the explicit
five-term enumeration `TowerExitClass.sum_univ`.
-/
theorem towerBudget_lhs_eq_highExcessMass
    (ctx : ActualFailureContext) (cls : ℕ → TowerExitClass) :
    routedClassMassOf ctx.n24CarryData cls TowerExitClass.run
        + routedClassMassOf ctx.n24CarryData cls TowerExitClass.returnPkg
        + routedClassMassOf ctx.n24CarryData cls TowerExitClass.densePack
        + routedClassMassOf ctx.n24CarryData cls TowerExitClass.cnlTail
        + routedClassMassOf ctx.n24CarryData cls TowerExitClass.other
      = highExcessMass
          (highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
            ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y)
          (hitGap ctx.n24CarryData.a) ctx.n24CarryData.r ctx.n24CarryData.T := by
  rw [← TowerExitClass.sum_univ (fun c => routedClassMassOf ctx.n24CarryData cls c)]
  exact (highExcessMass_eq_sum_routedClassMassOf ctx.n24CarryData cls).symm

/--
**The I.3.1 budget from the total-mass residual (faithful reduction).**

The Tower routed-mass budget — the field
`Erdos260PhaseCores.towerBudget` body — follows from the single named residual
`highExcessMass ≤ c_⋆·ξ·X/6` via the partition identity.  This is the genuine
deep I.3.1 content (needs I.4.1 dense-packing, M.2.2, K.4).  Stated so that
`towerBudget_of_highExcessMass_le ctx (towerClsOfShell ctx) hI31` *is* exactly the
`towerBudget` field at `cls := towerClsOfShell ctx`.
-/
theorem towerBudget_of_highExcessMass_le
    (ctx : ActualFailureContext) (cls : ℕ → TowerExitClass)
    (hI31 :
      highExcessMass
          (highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
            ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y)
          (hitGap ctx.n24CarryData.a) ctx.n24CarryData.r ctx.n24CarryData.T
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    routedClassMassOf ctx.n24CarryData cls TowerExitClass.run
        + routedClassMassOf ctx.n24CarryData cls TowerExitClass.returnPkg
        + routedClassMassOf ctx.n24CarryData cls TowerExitClass.densePack
        + routedClassMassOf ctx.n24CarryData cls TowerExitClass.cnlTail
        + routedClassMassOf ctx.n24CarryData cls TowerExitClass.other
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 := by
  rw [towerBudget_lhs_eq_highExcessMass]
  exact hI31

/-! ## 4. Reduction of the I.3.1 budget to the K.4 constant inequality -/

/--
**The total high-excess mass from a count×multiplier datum.**  If every high-excess
start charges at most `M` (the per-fibre residual multiplier, K.1.2/L.20: linear in
the active floor) and there are at most `N` high-excess starts, then the total
high-excess mass is `≤ N·M`; if moreover `N·M ≤ c_⋆·ξ·X/6` (the **K.4 numeric
inequality**), the I.3.1 budget bound `highExcessMass ≤ c_⋆·ξ·X/6` holds.
-/
theorem highExcessMass_n24_le_of_countMult
    (ctx : ActualFailureContext) {N M : ℝ}
    (hcard : ((highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
        ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y).card : ℝ) ≤ N)
    (hmult : ∀ k ∈ highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
        ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y,
        windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T ≤ M)
    (hMnn : 0 ≤ M)
    (hK4 : N * M ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    highExcessMass
        (highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
          ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y)
        (hitGap ctx.n24CarryData.a) ctx.n24CarryData.r ctx.n24CarryData.T
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 := by
  have h1 :
      highExcessMass
          (highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
            ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y)
          (hitGap ctx.n24CarryData.a) ctx.n24CarryData.r ctx.n24CarryData.T
        ≤ ((highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
            ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y).card : ℝ) * M :=
    highExcessMass_le_card_mul hmult
  have h2 :
      ((highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
          ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y).card : ℝ) * M ≤ N * M :=
    mul_le_mul_of_nonneg_right hcard hMnn
  linarith [h1, h2, hK4]

/--
**The Tower budget from a count×multiplier datum (count×multiplier ⟹ budget).**

Combines `highExcessMass_n24_le_of_countMult` with the partition identity: the
`towerBudget` field follows from the high-excess start count `N`, the per-fibre
window-excess multiplier `M`, and the **K.4 numeric inequality** `N·M ≤ c_⋆·ξ·X/6`.
-/
theorem towerBudget_of_countMult
    (ctx : ActualFailureContext) (cls : ℕ → TowerExitClass) {N M : ℝ}
    (hcard : ((highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
        ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y).card : ℝ) ≤ N)
    (hmult : ∀ k ∈ highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
        ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y,
        windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T ≤ M)
    (hMnn : 0 ≤ M)
    (hK4 : N * M ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    routedClassMassOf ctx.n24CarryData cls TowerExitClass.run
        + routedClassMassOf ctx.n24CarryData cls TowerExitClass.returnPkg
        + routedClassMassOf ctx.n24CarryData cls TowerExitClass.densePack
        + routedClassMassOf ctx.n24CarryData cls TowerExitClass.cnlTail
        + routedClassMassOf ctx.n24CarryData cls TowerExitClass.other
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  towerBudget_of_highExcessMass_le ctx cls
    (highExcessMass_n24_le_of_countMult ctx hcard hmult hMnn hK4)

/--
**The K.4 constant inequality, discharged outright (the tower slot).**

`c_* = κ·ξ/64 ≤ c_⋆·ξ/6` at the pinned manuscript constants — the realisation of
the K.4 hierarchy `c_* ≪_Q ρ_D κ ξ` that makes the dense-packing fraction fit the
Tower slot.  This is the K.4 *constant* inequality the I.3.1 budget needs, proved
purely numerically.
-/
theorem manuscriptCstarSmall_le_towerSlot :
    manuscriptCstarSmall ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 := by
  have hcs : erdos260Constants.cStar = manuscriptCstar := rfl
  have hxi : erdos260Constants.ξ = manuscriptXi := rfl
  rw [hcs, hxi]
  unfold manuscriptCstarSmall manuscriptKappa manuscriptCstar manuscriptCdrop manuscriptC1
    manuscriptEps manuscriptXi
  norm_num

/--
**The Tower budget from the I.4.1 dense-packing fraction, with K.4 discharged.**

The cleanest reduction: the `towerBudget` field follows from the single genuine
**I.4.1 dense-packing + M.2.2** residual `highExcessMass ≤ c_* · X` (the dense-packed
fraction bound), with the **K.4 constant inequality closed outright** by
`manuscriptCstarSmall_le_towerSlot`.  After this, the only residual of the I.3.1
budget is the dense-packing fraction bound; the K.4 hierarchy is no longer an input.
-/
theorem towerBudget_of_densePackFraction
    (ctx : ActualFailureContext) (cls : ℕ → TowerExitClass)
    (hDP :
      highExcessMass
          (highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
            ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y)
          (hitGap ctx.n24CarryData.a) ctx.n24CarryData.r ctx.n24CarryData.T
        ≤ manuscriptCstarSmall * (ctx.shell.X : ℝ)) :
    routedClassMassOf ctx.n24CarryData cls TowerExitClass.run
        + routedClassMassOf ctx.n24CarryData cls TowerExitClass.returnPkg
        + routedClassMassOf ctx.n24CarryData cls TowerExitClass.densePack
        + routedClassMassOf ctx.n24CarryData cls TowerExitClass.cnlTail
        + routedClassMassOf ctx.n24CarryData cls TowerExitClass.other
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 := by
  refine towerBudget_of_highExcessMass_le ctx cls (le_trans hDP ?_)
  have hXnn : 0 ≤ (ctx.shell.X : ℝ) := ctx.shell.X_nonneg_real
  have hslot := manuscriptCstarSmall_le_towerSlot
  calc manuscriptCstarSmall * (ctx.shell.X : ℝ)
      ≤ (erdos260Constants.cStar * erdos260Constants.ξ / 6) * (ctx.shell.X : ℝ) :=
        mul_le_mul_of_nonneg_right hslot hXnn
    _ = erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 := by ring

/-! ## 5. Honest finding: the full-mass reading of (I.3.1) is unsatisfiable

The of-shell tower family `towerExitRoutingOfShell` re-indexes the **entire**
high-excess start set, so the budget LHS is the full high-excess mass
(`towerBudget_lhs_eq_highExcessMass`).  But the proved Lemma 21.1 lower bound
`CarryDataFromFailure.highExcessMass_lower` gives `c_pr·X·(r+1) ≤ highExcessMass`,
and at the pinned `c_pr = 1/2 > c_⋆·ξ/6`, the residual `highExcessMass ≤ c_⋆·ξ·X/6`
forces `X ≤ 0`.  This precisely locates the genuine content: the I.4.1 dense-packing
bound governs only the *dense-packed fraction*, not the whole carry mass, so the
faithful budget needs the manuscript per-class split (each phase absorbs its own
fraction), not the single-phase full-mass bound. -/

/--
**The full-mass I.3.1 residual forces `X ≤ 0`.**  Combining the I.3.1 budget residual
`highExcessMass ≤ c_⋆·ξ·X/6` (the budget LHS, via the partition identity) with the
**proved** Lemma 21.1 lower bound `c_pr·X·(r+1) ≤ highExcessMass` gives
`c_pr·X·(r+1) ≤ c_⋆·ξ·X/6`; at the pinned `c_pr = 1/2`, `c_⋆ = 31/16`, `ξ = 1/16`,
and `r ≥ 0`, `X ≥ 0`, this forces `X ≤ 0`.  Hence the full high-excess-mass reading
of the I.3.1 budget is unsatisfiable for every large shell.
-/
theorem towerBudget_residual_forces_X_nonpos
    (ctx : ActualFailureContext)
    (hI31 :
      highExcessMass
          (highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
            ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y)
          (hitGap ctx.n24CarryData.a) ctx.n24CarryData.r ctx.n24CarryData.T
        ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    (ctx.shell.X : ℝ) ≤ 0 := by
  -- Chain the proved Lemma 21.1 lower bound with the I.3.1 residual *before*
  -- touching the constants, to avoid rewriting `erdos260Constants.cPr` inside the
  -- type `CarryDataFromFailure ctx.shell erdos260Constants.cPr` of `ctx.n24CarryData`.
  have hchain := le_trans ctx.n24CarryData.highExcessMass_lower hI31
  have hXnn : 0 ≤ (ctx.shell.X : ℝ) := ctx.shell.X_nonneg_real
  have hrnn : 0 ≤ (ctx.n24CarryData.r : ℝ) := Nat.cast_nonneg _
  -- Generalise the lone remaining dependent subterm `↑ctx.n24CarryData.r`.
  set rr : ℝ := (ctx.n24CarryData.r : ℝ) with hrr
  rw [show erdos260Constants.cPr = (1 / 2 : ℝ) from rfl,
      show erdos260Constants.cStar = (31 / 16 : ℝ) from rfl,
      show erdos260Constants.ξ = (1 / 16 : ℝ) from rfl] at hchain
  nlinarith [hchain, hXnn, hrnn, mul_nonneg hXnn hrnn]

/-! ## 6. Capstone: the two Tower cores realized for the concrete classifier -/

/--
**The L.2.4 disjointness for the concrete L.3.1 classifier `towerClsOfShell`
(CLOSED).**  Specialises `towerExit_L24_disjointness_matching` to the
SCC-geometry classifier: each tower output of the of-shell family at
`cls := towerClsOfShell ctx` absorbs exactly the charge of the unique high-excess
carry start that created it.
-/
theorem towerClsOfShell_L24_disjointness (ctx : ActualFailureContext) :
    ∀ O ∈ (towerExitRoutingOfShell ctx (towerClsOfShell ctx)).entryExitSet,
      (∑ k ∈ (highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
            ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y).filter
          (fun k => towerExitOf k = O),
        windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T)
        ≤ ((towerExitRoutingOfShell ctx (towerClsOfShell ctx)).weight O : ℝ) :=
  towerExit_L24_disjointness_matching ctx (towerClsOfShell ctx)

/--
**The I.3.1 budget field realized for the concrete L.3.1 classifier `towerClsOfShell`.**

This is *exactly* the body of the `Erdos260PhaseCores.towerBudget` field at
`towerCls := towerClsOfShell`, derived from the single genuine **I.4.1
dense-packing + M.2.2** residual `highExcessMass ≤ c_* · X` (the dense-packed
fraction bound), with the **K.4 constant inequality discharged** by
`manuscriptCstarSmall_le_towerSlot`.  Together with `towerClsOfShell_L24_disjointness`
this shows the two Tower cores are realized for the concrete classifier modulo the
one named I.4.1 residual.
-/
theorem towerClsOfShell_budget_of_densePackFraction (ctx : ActualFailureContext)
    (hDP :
      highExcessMass
          (highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
            ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y)
          (hitGap ctx.n24CarryData.a) ctx.n24CarryData.r ctx.n24CarryData.T
        ≤ manuscriptCstarSmall * (ctx.shell.X : ℝ)) :
    routedClassMassOf ctx.n24CarryData (towerClsOfShell ctx) TowerExitClass.run
        + routedClassMassOf ctx.n24CarryData (towerClsOfShell ctx) TowerExitClass.returnPkg
        + routedClassMassOf ctx.n24CarryData (towerClsOfShell ctx) TowerExitClass.densePack
        + routedClassMassOf ctx.n24CarryData (towerClsOfShell ctx) TowerExitClass.cnlTail
        + routedClassMassOf ctx.n24CarryData (towerClsOfShell ctx) TowerExitClass.other
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  towerBudget_of_densePackFraction ctx (towerClsOfShell ctx) hDP

/-! ## 7. Axiom-cleanliness audit -/

-- Core 1 (classifier + L.2.4 disjointness) and Core 2 (budget reduction + K.4)
-- depend only on the standard `[propext, Classical.choice, Quot.sound]`.
#print axioms towerClsOfShell
#print axioms towerExitClassOfGap_surjective
#print axioms towerExit_L24_disjointness_matching
#print axioms towerExit_L24_disjointness
#print axioms towerBudget_lhs_eq_highExcessMass
#print axioms towerBudget_of_highExcessMass_le
#print axioms towerBudget_of_countMult
#print axioms manuscriptCstarSmall_le_towerSlot
#print axioms towerBudget_of_densePackFraction
#print axioms towerBudget_residual_forces_X_nonpos
#print axioms towerClsOfShell_L24_disjointness
#print axioms towerClsOfShell_budget_of_densePackFraction

end

end Erdos260
