import Erdos260.V30CycleMassBalance
import Erdos260.V30RetirementDischarge
import Erdos260.MissDistanceClosure
import Erdos260.V30DensePackSupport
import Erdos260.V30TopBandReadTail
import Erdos260.O2AmbientInjection
import Erdos260.O2SupplyEmbedding

/-!
# V30 off-pin exit-mass cap (`V30OffPinExitCap`) — LANE C, the (C1) convergence point

This module (NEW; it edits no existing file) ASSEMBLES the v30 direct off-pin
exit-mass certificate **(C1)** of `proof_v4_repaired_core_v30.tex`
(`cor:ac-offpin-cap-closed`, line 11603) on top of the two built-green prerequisites,
and delivers the supplier target `ExitMassControlOffPin` for the off-pin classes
`{3,4,5}` plus the class-0 leg `MdcClass0ExitMassControl` (class `0`) — the four
off-pin classes `{0,3,4,5}` of (R3).

## The v30 (C1) mechanism, assembled here

The off-pin recurrent fibres split (Appendix AB, `prop:ab-safe-cone-closed-summed`
11254 / `lem:ab-safe-complement-exhaustion` 11315) into

* a **safe exposure cone** (cells with `1536·h(c)·b ≤ 31·c`), capped by the v30
  mass-NORMALIZED balance of Appendix R (Lane B `cmb_offPin_safeCone_cap`), and
* the **unsafe exit-light long-cycle core** (`b = 1`, `c ≥ 64`,
  `1536·⌊(r+c)/c⌋ > 31·c`; `def:ab-unsafe-core` 11346), which Appendix AC empties
  (`prop:ac-unsafe-core-empty` 11579) — discharged UNCONDITIONALLY by the Lane
  D-discharge module (`unsafeOffPinCoreSet_eq_empty`, no `PriorityRouting` hyp).

### The convergence (what is genuinely new here)

The two prerequisites bridge on a SHARED constant: the in-tree descent order
`ctx.n24CarryData.r = ⌊κ·L⌋` (`scc_r_eq_floor`) and Lane D's `rActive L = ⌊κ·L⌋`
(`V30BoundedPeriodRetirement.rActive`) use the **same** `manuscriptKappa`, so
`v30_ctx_r_eq_rActive : ctx.n24CarryData.r = rActive (shellLadderDepth ctx)`.  Hence
the overlap factor of Lane B, `cmbOverlap ctx c = ⌊(r+c)/c⌋`, is Lane D's overlap.

Consequently the worst case — the **exit-light long cycle** `b = 1`, `c ≥ 64` that
the Lean program could never feed (`EmcSpacedShareDatum` unprovable) — is handled
WITHOUT any proportional share: a live M.5/L.3 ledger survivor has `c > P_hand·L`,
so `⌊(r+c)/c⌋ = 1` (Lane D `surviving_unit_overlap`), and the safe-cone cell
inequality `1536·1·1 ≤ 31·c` holds for `c ≥ 64` (`31·64 = 1984 > 1536`).  This is
exactly the AC emptiness, re-read as "the unsafe shape is FORCED safe"
(`v30_exitLight_ledger_safe`, routed through the D-discharge
`unsafeCore_empty_of_ledger_period`).  The class mass then clears the cap through the
in-tree event-count chain (`emc2_classMass_le_fibreDevMass` ∘
`emc2_fibreDevMass_le_overlap` ∘ `cmb_offPin_safeCone_cap`).

### The two named residuals (RISK b / RISK c) — honest verdicts

The mass-normalized balance needs, per cell, the two genuinely measure-theoretic
inputs the manuscript treats as substantive (V30 reroute plan §9):

* **RISK c** `V30MeasurePreservation` — the discrete measure preservation
  `c·ExitMass ≤ b·M_tot` around the recurrent cycle
  (`lem:r-cycle-map-preserves-measure`, v30 line 9110; `prop:r-exit-share-closed`,
  9203).  Its WORD-LEVEL shadow is DISCHARGED in tree (Lane B
  `cmb_windowExcess_cyclic`, from `c`-periodicity of the gap word); the phase-mass
  lift is CARRIED (Lane B abstracts it as `CycleMassDatum.preserved`).
* **RISK b** `V30AmbientAccounting` — the disjoint-cell ambient phase-mass bound
  `M_tot ≤ X` (`lem:ad-summed-ambient-support`, v30 line 11671; per-cell
  `lem:ab-ambient-support-bound`, 11187, injectivity 11216-11218).  CARRIED: the
  closest in-tree shadow is the support-count bound `scc_supportShell_lt`
  (`W < (17/2²⁴)·X`), but the phase-forgetting injectivity is a genuine
  measure-theoretic partition claim, not an in-tree atom.

Both are NAMED residuals (NOT discharged): see `v30OffPinExitCapStatus`.  Neither is
`(C1)`-circular, and the cell structure (spacing/period, RISK e) is supplied by the
AB recurrent-pair certificate.  The pivotal worst case (the unsafe core) needs
NEITHER residual: it is empty by Lane D alone.

## Deliverables

* `v30_offPinExitCap : V30OffPinSafeConeRegime → ExitMassControlOffPin` — classes
  `{3,4,5}` (the assembly; via `cmb_offPin_safeCone_cap`, directly, NOT through the
  false `emc2_offPin_of_regime` share datum).
* `v30_mdcClass0ExitMassControl_of_safeCone : V30Class0SafeConeRegime →
  MdcClass0ExitMassControl` — class `0` leg (via `cmb_safeCone_nat`).
* `v30_offPin_allClasses` — all four off-pin classes `{0,3,4,5}` at once.
* `v30_exitLight_ledger_safe` / `v30_ctx_exitLight_safe` — the AC emptiness consumed:
  exit-light long cycles are FORCED into the safe cone (no share needed).
* Corollary suppliers off the same cap: `v30_localExitLight_of_cap` (R4 densepack
  span-rarity currency, `K1LocalExitLight`), `v30_topBandPushforward_of_cap` +
  `v30_laneGResidual_of` (Lane G R5/R6 `V30TopBandPushforward` /
  `V30ReadTailExitCount`).

No `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace Erdos260

noncomputable section

open V30BoundedPeriodRetirement V30RetirementDischarge

set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option maxRecDepth 8192

/-! ## Part 0.  The currency bridge — Lane B's `r` is Lane D's `rActive L`

Both the in-tree descent order `ctx.n24CarryData.r` (`scc_r_eq_floor`) and Lane D's
`rActive L` (`V30BoundedPeriodRetirement.rActive`) are `⌊manuscriptKappa·L⌋`, so they
coincide at `L = shellLadderDepth ctx`.  This lets the Lane D unit-overlap fact feed
Lane B's overlap factor `cmbOverlap`. -/

/-- **The currency bridge**: the in-tree descent order is Lane D's `rActive` at the
shell scale — both are `⌊κ·L⌋` with the SAME `manuscriptKappa`. -/
theorem v30_ctx_r_eq_rActive (ctx : ActualFailureContext) :
    ctx.n24CarryData.r = rActive (shellLadderDepth ctx) := by
  rw [scc_r_eq_floor]; rfl

/-- Lane B's overlap factor `cmbOverlap ctx c = ⌊(r+c)/c⌋` is Lane D's overlap
`⌊(rActive L + c)/c⌋`. -/
theorem v30_cmbOverlap_eq (ctx : ActualFailureContext) (c : ℕ) :
    cmbOverlap ctx c = (rActive (shellLadderDepth ctx) + c) / c := by
  unfold cmbOverlap
  rw [v30_ctx_r_eq_rActive]

/-! ## Part 1.  Consuming Lane D — the unsafe core is empty, so exit-light long cycles
are FORCED safe

This is the heart of the v30 (C1) closure (Appendix AC).  The exit-light long-cycle
core (`b = 1`, `c ≥ 64`, `1536·⌊(r+c)/c⌋ > 31·c`) is EMPTY for live M.5/L.3 ledger
fibres (D-discharge `unsafeCore_empty_of_ledger_period`), which — read as a positive
statement — says the exit-light long-cycle cell ALWAYS satisfies the safe-cone cell
inequality.  No proportional share is used. -/

/-- The unit-overlap arithmetic, scale form (`lem:ac-surviving-long-cycle-unit-overlap`,
v30 line 11555): a ledger survivor `c > P_hand·L+C_Q` has `⌊(rActive L + c)/c⌋ = 1`. -/
theorem v30_unit_overlap_of_gt_threshold {L c : ℕ}
    (hsurv : boundedThreshold L < c) : (rActive L + c) / c = 1 := by
  have hrc : rActive L < c := lt_trans (rActive_lt_threshold L) hsurv
  have hc_pos : 0 < c := by omega
  have h0 : rActive L / c = 0 := Nat.div_eq_of_lt hrc
  have h1 : (rActive L + c) / c = rActive L / c + 1 := Nat.add_div_right (rActive L) hc_pos
  omega

/-- **The AC emptiness, consumed (`CycleParams` form)**: a live M.5/L.3 ledger fibre
(`boundedThreshold L < cyc.p`) with the exit-light shape `b = 1`, `c ≥ 64` SATISFIES
the safe-cone cell inequality `1536·⌊(r+c)/c⌋·b ≤ 31·c`.  Proof: if it failed, the
fibre would lie in the unsafe off-pin core, contradicting the D-discharge
`unsafeCore_empty_of_ledger_period` (`prop:ac-unsafe-core-empty`, v30 line 11579). -/
theorem v30_exitLight_ledger_safe {L : ℕ} (cyc : CycleParams)
    (hsurv : boundedThreshold L < cyc.p) (hb : cyc.b = 1) (hc64 : 64 ≤ cyc.c) :
    1536 * ((rActive L + cyc.c) / cyc.c * cyc.b) ≤ 31 * cyc.c := by
  rw [hb, mul_one]
  by_contra hcon
  exact unsafeCore_empty_of_ledger_period hsurv ⟨hb, hc64, not_le.mp hcon⟩

/-- **The AC emptiness, consumed (`ctx` form, Lane B currency)**: at any context, an
exit-light long cycle (`b = 1`, `c ≥ 64`) whose refined length is a ledger survivor
(`c > P_hand·L+C_Q`) satisfies Lane B's safe-cone cell inequality
`1536·(cmbOverlap ctx c · b) ≤ 31·c` — the cell condition is FREE for the worst case,
routed through `v30_exitLight_ledger_safe`. -/
theorem v30_ctx_exitLight_safe (ctx : ActualFailureContext) {b c : ℕ}
    (hsurv : boundedThreshold (shellLadderDepth ctx) < c) (hb : b = 1) (hc64 : 64 ≤ c) :
    1536 * (cmbOverlap ctx c * b) ≤ 31 * c := by
  rw [v30_cmbOverlap_eq]
  have hc_pos : 0 < c := by omega
  exact v30_exitLight_ledger_safe (L := shellLadderDepth ctx)
    ⟨c, c, b, hc_pos, hc_pos, dvd_refl c⟩ hsurv hb hc64

/-- **`𝔠_unsafe^offpin = ∅`** re-exported as a visible dependency of Lane C: the v30
unsafe off-pin core is empty, UNCONDITIONALLY, from the Lane D-discharge module
(`cor:ac-offpin-cap-closed` precursor). -/
theorem v30_unsafeOffPinCore_empty (L : ℕ) : unsafeOffPinCoreSet L = ∅ :=
  unsafeOffPinCoreSet_eq_empty L

/-! ## Part 2.  The per-class safe-cone cap — the reusable (C1) engine

Composition of the three proved inputs, in Lane B's `ctx` currency:
`routedClassMassOf ≤ emcFibreDevMass` (band `≤ 4`, `emc2_classMass_le_fibreDevMass`)
`≤ cmbOverlap·emcFibreExitMass = cmbNormalizedExposure` (`c`-spacing,
`emc2_fibreDevMass_le_overlap`) `≤ emcCap` (safe cone, `cmb_offPin_safeCone_cap`). -/

/-- **THE PER-CLASS (C1) SAFE-CONE CAP** (off-pin class `i`).  On a band-`≤4`,
`c`-spaced safe-cone cell with the mass-normalized balance `c·ExitMass ≤ b·M_tot`
(RISK c) and ambient bound `M_tot ≤ X` (RISK b), the routed class mass clears the
corrected per-class capacity `emcCap = (31/1536)·X`. -/
theorem v30_offPin_classCap (ctx : ActualFailureContext) (i : Fin 7)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4) {b c Mtot : ℕ} (hc : 1 ≤ c)
    (hspace : ∀ x ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i,
      ∀ z ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i,
        x ≤ z → c ∣ z - x)
    (hbalance : c * emcFibreExitMass ctx i ≤ b * Mtot)
    (hsafe : 1536 * (cmbOverlap ctx c * b) ≤ 31 * c)
    (hambient : Mtot ≤ ctx.shell.X) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) i ≤ emcCap ctx := by
  have h1 := emc2_classMass_le_fibreDevMass ctx hband i
  have h2 : emcFibreDevMass ctx i ≤ cmbNormalizedExposure ctx i c := by
    unfold cmbNormalizedExposure cmbOverlap
    exact emc2_fibreDevMass_le_overlap ctx i hc hspace
  have h2R : ((emcFibreDevMass ctx i : ℕ) : ℝ)
      ≤ ((cmbNormalizedExposure ctx i c : ℕ) : ℝ) := by exact_mod_cast h2
  have h3 := cmb_offPin_safeCone_cap ctx i hc hbalance hsafe hambient
  linarith [h1, h2R, h3]

/-- **THE EXIT-LIGHT WORST-CASE CAP** — the crux of the v30 (C1) closure.  An off-pin
exit-light long cycle (`b = 1`, refined length `c ≥ 64`) that is a live M.5/L.3 ledger
survivor (`c > P_hand·L+C_Q`) is capped using ONLY band `≤ 4`, the fibre `c`-spacing,
the mass-normalized balance (RISK c) and the ambient bound (RISK b): the safe-cone cell
inequality is supplied FOR FREE by the Lane D-discharge unsafe-core emptiness
(`v30_ctx_exitLight_safe`).  This is the precise object the Lean program could never
feed (`EmcSpacedShareDatum` at `b = 1`, `c ≥ 64`), now closed WITHOUT any proportional
total-exit share. -/
theorem v30_offPin_classCap_exitLight (ctx : ActualFailureContext) (i : Fin 7)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4) {c Mtot : ℕ}
    (hsurv : boundedThreshold (shellLadderDepth ctx) < c) (hc64 : 64 ≤ c)
    (hspace : ∀ x ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i,
      ∀ z ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i,
        x ≤ z → c ∣ z - x)
    (hbalance : c * emcFibreExitMass ctx i ≤ 1 * Mtot)
    (hambient : Mtot ≤ ctx.shell.X) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) i ≤ emcCap ctx :=
  v30_offPin_classCap ctx i hband (by omega) hspace hbalance
    (v30_ctx_exitLight_safe ctx hsurv rfl hc64) hambient

/-- Finite-error version of the per-class (C1) cap.  If the ambient phase mass
is known only up to an explicit collar/error term `err`, the same safe-cone
calculation gives the cap with the corresponding additive
`(31/1536) * err` remainder.  This is the Lean shape of the TeX
`+ o(X|I_j|)` term; it does not pretend to feed the no-error C1 endpoint. -/
def V30OffPinClassCapWithError
    (ctx : ActualFailureContext) (i : Fin 7) (err : ℕ) : Prop :=
  routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) i
    ≤ emcCap ctx + ((31 : ℝ) / 1536) * (err : ℝ)

/-- A zero finite-error cap is exactly the no-error off-pin per-class cap
consumed by `ExitMassControlOffPin`. -/
theorem v30_offPin_classCap_of_withError_zero
    {ctx : ActualFailureContext} {i : Fin 7}
    (h : V30OffPinClassCapWithError ctx i 0) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) i ≤ emcCap ctx := by
  simpa [V30OffPinClassCapWithError] using h

/-! ## Part 3.  The named residuals (RISK b / RISK c) and the off-pin regime -/

/-- **RISK c (NAMED RESIDUAL)** — the discrete measure preservation around the
recurrent cycle: the mass-normalized balance `c·ExitMass ≤ b·M_tot`
(`lem:r-cycle-map-preserves-measure`, v30 line 9110; `prop:r-exit-share-closed`,
9203).  Its word-level shadow is DISCHARGED in Lane B (`cmb_windowExcess_cyclic`);
this phase-mass lift is CARRIED (= `CycleMassDatum.preserved`). -/
def V30MeasurePreservation (ctx : ActualFailureContext) (i : Fin 7) (b c Mtot : ℕ) : Prop :=
  c * emcFibreExitMass ctx i ≤ b * Mtot

/-- **RISK b (NAMED RESIDUAL)** — the disjoint-cell ambient phase-mass bound
`M_tot ≤ X` (`lem:ad-summed-ambient-support`, v30 line 11671; per-cell
`lem:ab-ambient-support-bound`, 11187, injectivity 11216-11218).  CARRIED: the in-tree
shadow is the support-count bound `scc_supportShell_lt` (`W < (17/2²⁴)·X`); the
phase-forgetting injectivity is a genuine measure-theoretic partition claim. -/
def V30AmbientAccounting (ctx : ActualFailureContext) (Mtot : ℕ) : Prop :=
  Mtot ≤ ctx.shell.X

/-- Interval-scaled form of the RISK-b ambient accounting statement, matching the
summed TeX statements `M_tot <= X*|I_j|`.  The existing `V30AmbientAccounting`
is the unit-interval specialization consumed by the C1 safe-cone cap. -/
def V30AmbientAccountingOn (ctx : ActualFailureContext) (cardIj Mtot : ℕ) : Prop :=
  Mtot ≤ ctx.shell.X * cardIj

/-- **RISK b from the O2 ambient-injection core, summed form.**  This is the
Lean-facing version of `lem:ab-ambient-support-bound-summed`,
`lem:ad-summed-ambient-support`, and `lem:ak-ambient-support-sum`: if selected
cells are fibres of one label map inside a carrier that injects into a
start/threshold rectangle of size at most `X*|I_j|`, then their total supplied
ambient mass is at most `X*|I_j|`. -/
theorem v30AmbientAccountingOn_of_o2_summed_carrier
    {Ω β A : Type*} [DecidableEq Ω] (ctx : ActualFailureContext)
    {cardIj Mtot : Nat}
    (S : Finset A) (cells : A -> Finset Ω) (Λ : Ω -> A) (masses : A -> Nat)
    (carrier : Finset Ω) (rect : Finset β) (πst : Ω -> β)
    (hMtot : Mtot <= Finset.sum S masses)
    (hsub : forall a, a ∈ S -> cells a ⊆ carrier)
    (hfib : forall a, a ∈ S -> forall ω, ω ∈ cells a -> Λ ω = a)
    (hcell : forall a, a ∈ S -> masses a <= (cells a).card)
    (hmaps : forall ω, ω ∈ carrier -> πst ω ∈ rect)
    (hinj : Set.InjOn πst carrier)
    (hrect : rect.card <= ctx.shell.X * cardIj) :
    V30AmbientAccountingOn ctx cardIj Mtot :=
  le_trans hMtot
    (O2AmbientInjection.o2_ambient_support_summed S cells Λ masses
      carrier rect πst ctx.shell.X cardIj hsub hfib hcell hmaps hinj hrect)

/-- Unit-interval specialization of the summed O2 ambient bridge. -/
theorem v30AmbientAccounting_of_o2_summed_unit_carrier
    {Ω β A : Type*} [DecidableEq Ω] (ctx : ActualFailureContext) {Mtot : Nat}
    (S : Finset A) (cells : A -> Finset Ω) (Λ : Ω -> A) (masses : A -> Nat)
    (carrier : Finset Ω) (rect : Finset β) (πst : Ω -> β)
    (hMtot : Mtot <= Finset.sum S masses)
    (hsub : forall a, a ∈ S -> cells a ⊆ carrier)
    (hfib : forall a, a ∈ S -> forall ω, ω ∈ cells a -> Λ ω = a)
    (hcell : forall a, a ∈ S -> masses a <= (cells a).card)
    (hmaps : forall ω, ω ∈ carrier -> πst ω ∈ rect)
    (hinj : Set.InjOn πst carrier)
    (hrect : rect.card <= ctx.shell.X) :
    V30AmbientAccounting ctx Mtot := by
  have hrect' : rect.card <= ctx.shell.X * 1 := by
    simpa using hrect
  have h := v30AmbientAccountingOn_of_o2_summed_carrier ctx
    (cardIj := 1) (Mtot := Mtot) S cells Λ masses carrier rect πst hMtot
    hsub hfib hcell hmaps hinj hrect'
  simpa [V30AmbientAccounting, V30AmbientAccountingOn] using h

/-- V30-facing bridge from the constructed-rectangle O2 supply surface.  The
O2 module discharges the rectangle cardinality and carry-faithful injectivity;
V30 only records the resulting interval-scaled ambient accounting bound. -/
theorem v30AmbientAccountingOn_of_o2_supply_inputs
    (P₀ Q : Int) {β A : Type*} (ctx : ActualFailureContext) {Mtot : Nat}
    (S : Finset A) (Omega : A -> Finset (Nat -> Int))
    (Lambda : (Nat -> Int) -> A) (masses : A -> Nat)
    (carrier : Finset (Nat -> Int)) (Ij : Finset β)
    (piSt : (Nat -> Int) -> Nat × β)
    (keyOf : Nat × β -> Int × (Nat -> Int))
    (hMtot : Mtot <= Finset.sum S masses)
    (I : O2SupplyEmbedding.O2SupplyInputs P₀ Q S Omega Lambda masses carrier Ij
      ctx.shell.X piSt keyOf) :
    V30AmbientAccountingOn ctx Ij.card Mtot :=
  le_trans hMtot
    (O2SupplyEmbedding.O2SupplyInputs.capstone P₀ Q S Omega Lambda masses carrier
      Ij ctx.shell.X piSt keyOf I)

/-- Coordinate-split version of the constructed-rectangle O2 bridge. -/
theorem v30AmbientAccountingOn_of_o2_supply_coordinate_inputs
    (P₀ Q : Int) {β A : Type*} (ctx : ActualFailureContext) {Mtot : Nat}
    (S : Finset A) (Omega : A -> Finset (Nat -> Int))
    (Lambda : (Nat -> Int) -> A) (masses : A -> Nat)
    (carrier : Finset (Nat -> Int)) (Ij : Finset β)
    (piSt : (Nat -> Int) -> Nat × β)
    (keyOf : Nat × β -> Int × (Nat -> Int))
    (hMtot : Mtot <= Finset.sum S masses)
    (I : O2SupplyEmbedding.O2SupplyCoordinateInputs P₀ Q S Omega Lambda masses carrier
      Ij ctx.shell.X piSt keyOf) :
    V30AmbientAccountingOn ctx Ij.card Mtot :=
  le_trans hMtot
    (O2SupplyEmbedding.O2SupplyCoordinateInputs.capstone P₀ Q S Omega Lambda masses
      carrier Ij ctx.shell.X piSt keyOf I)

/-- Unit-interval specialization of the constructed-rectangle O2 supply bridge,
matching the scalar ambient accounting field consumed by the C1 safe-cone cap. -/
theorem v30AmbientAccounting_of_o2_supply_unit_inputs
    (P₀ Q : Int) {β A : Type*} (ctx : ActualFailureContext) {Mtot : Nat}
    (S : Finset A) (Omega : A -> Finset (Nat -> Int))
    (Lambda : (Nat -> Int) -> A) (masses : A -> Nat)
    (carrier : Finset (Nat -> Int)) (Ij : Finset β)
    (piSt : (Nat -> Int) -> Nat × β)
    (keyOf : Nat × β -> Int × (Nat -> Int))
    (hMtot : Mtot <= Finset.sum S masses)
    (hIj : Ij.card = 1)
    (I : O2SupplyEmbedding.O2SupplyInputs P₀ Q S Omega Lambda masses carrier Ij
      ctx.shell.X piSt keyOf) :
    V30AmbientAccounting ctx Mtot := by
  have h := v30AmbientAccountingOn_of_o2_supply_inputs P₀ Q ctx S Omega Lambda
    masses carrier Ij piSt keyOf hMtot I
  simpa [V30AmbientAccounting, V30AmbientAccountingOn, hIj] using h

/-- Coordinate-split unit-interval specialization of the O2 supply bridge. -/
theorem v30AmbientAccounting_of_o2_supply_coordinate_unit_inputs
    (P₀ Q : Int) {β A : Type*} (ctx : ActualFailureContext) {Mtot : Nat}
    (S : Finset A) (Omega : A -> Finset (Nat -> Int))
    (Lambda : (Nat -> Int) -> A) (masses : A -> Nat)
    (carrier : Finset (Nat -> Int)) (Ij : Finset β)
    (piSt : (Nat -> Int) -> Nat × β)
    (keyOf : Nat × β -> Int × (Nat -> Int))
    (hMtot : Mtot <= Finset.sum S masses)
    (hIj : Ij.card = 1)
    (I : O2SupplyEmbedding.O2SupplyCoordinateInputs P₀ Q S Omega Lambda masses carrier
      Ij ctx.shell.X piSt keyOf) :
    V30AmbientAccounting ctx Mtot := by
  have h := v30AmbientAccountingOn_of_o2_supply_coordinate_inputs P₀ Q ctx S Omega
    Lambda masses carrier Ij piSt keyOf hMtot I
  simpa [V30AmbientAccounting, V30AmbientAccountingOn, hIj] using h

/-- **RISK b from the O2 ambient-injection core, single-cell form.**  If one
recurrent cell has mass bounded by its event carrier, and that carrier injects
into a start/threshold rectangle of size at most `X`, then it supplies exactly
the v30 ambient accounting input `M_tot <= X`.  This is the `|I_j| = 1`
specialization of `O2AmbientInjection.o2_ambient_support_summed`. -/
theorem v30AmbientAccounting_of_o2_unit_carrier
    {Ω β : Type*} [DecidableEq Ω] (ctx : ActualFailureContext) {Mtot : Nat}
    (cell carrier : Finset Ω) (rect : Finset β) (πst : Ω -> β)
    (hsub : cell ⊆ carrier)
    (hcell : Mtot <= cell.card)
    (hmaps : forall ω, ω ∈ carrier -> πst ω ∈ rect)
    (hinj : Set.InjOn πst carrier)
    (hrect : rect.card <= ctx.shell.X) :
    V30AmbientAccounting ctx Mtot := by
  let S : Finset Unit := Finset.univ
  let cells : Unit -> Finset Ω := fun _ => cell
  let masses : Unit -> Nat := fun _ => Mtot
  have hsub' : forall a, a ∈ S -> cells a ⊆ carrier := by
    intro a _ha
    cases a
    exact hsub
  have hfib : forall a, a ∈ S -> forall ω, ω ∈ cells a -> (fun _ : Ω => ()) ω = a := by
    intro a _ha ω _hω
    cases a
    rfl
  have hcell' : forall a, a ∈ S -> masses a <= (cells a).card := by
    intro a _ha
    cases a
    exact hcell
  have hrect' : rect.card <= ctx.shell.X * 1 := by
    simpa using hrect
  have hsum :
      Finset.sum S masses <= ctx.shell.X * 1 :=
    O2AmbientInjection.o2_ambient_support_summed S cells (fun _ : Ω => ()) masses
      carrier rect πst ctx.shell.X 1 hsub' hfib hcell' hmaps hinj hrect'
  simpa [S, cells, masses] using hsum

/-- Interval-scaled RISK-b ambient accounting with a single explicit collar
remainder.  This is the V30-facing finite version of the TeX
`M_tot <= X |I_j| + o(X|I_j|)` statements; it is deliberately distinct from
`V30AmbientAccounting`, which is the no-remainder input consumed by the C1 cap. -/
def V30AmbientAccountingWithErrorOn
    (ctx : ActualFailureContext) (cardIj err Mtot : ℕ) : Prop :=
  Mtot <= ctx.shell.X * cardIj + err

/-- Unit-interval specialization of `V30AmbientAccountingWithErrorOn`. -/
def V30AmbientAccountingWithError
    (ctx : ActualFailureContext) (err Mtot : ℕ) : Prop :=
  Mtot <= ctx.shell.X + err

/-- A zero collar/error term recovers the no-remainder RISK-b accounting input
consumed by the C1 cap. -/
theorem v30AmbientAccounting_of_withError_zero
    (ctx : ActualFailureContext) {Mtot : Nat}
    (h : V30AmbientAccountingWithError ctx 0 Mtot) :
    V30AmbientAccounting ctx Mtot := by
  simpa [V30AmbientAccounting, V30AmbientAccountingWithError] using h

/-- A zero collar/error term also recovers the interval-scaled no-remainder
RISK-b accounting statement. -/
theorem v30AmbientAccountingOn_of_withErrorOn_zero
    (ctx : ActualFailureContext) {cardIj Mtot : Nat}
    (h : V30AmbientAccountingWithErrorOn ctx cardIj 0 Mtot) :
    V30AmbientAccountingOn ctx cardIj Mtot := by
  simpa [V30AmbientAccountingOn, V30AmbientAccountingWithErrorOn] using h

/-- Unit-interval zero-error form of the interval-scaled accounting statement. -/
theorem v30AmbientAccounting_of_withErrorOn_unit_zero
    (ctx : ActualFailureContext) {cardIj Mtot : Nat}
    (hIj : cardIj = 1)
    (h : V30AmbientAccountingWithErrorOn ctx cardIj 0 Mtot) :
    V30AmbientAccounting ctx Mtot := by
  simpa [V30AmbientAccounting, V30AmbientAccountingWithErrorOn, hIj] using h

/-- Per-class safe-cone cap with an explicit finite ambient error.  The proof is
the same Lane-B arithmetic as `v30_offPin_classCap`, run with ambient budget
`X + err`; the output records the unavoidable additive cap error instead of
erasing it. -/
theorem v30_offPin_classCap_withError (ctx : ActualFailureContext) (i : Fin 7)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4) {b c err Mtot : ℕ} (hc : 1 ≤ c)
    (hspace : ∀ x ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i,
      ∀ z ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i,
        x ≤ z → c ∣ z - x)
    (hbalance : c * emcFibreExitMass ctx i ≤ b * Mtot)
    (hsafe : 1536 * (cmbOverlap ctx c * b) ≤ 31 * c)
    (hambient : V30AmbientAccountingWithError ctx err Mtot) :
    V30OffPinClassCapWithError ctx i err := by
  have h1 := emc2_classMass_le_fibreDevMass ctx hband i
  have h2 : emcFibreDevMass ctx i ≤ cmbNormalizedExposure ctx i c := by
    unfold cmbNormalizedExposure cmbOverlap
    exact emc2_fibreDevMass_le_overlap ctx i hc hspace
  have h2R : ((emcFibreDevMass ctx i : ℕ) : ℝ)
      ≤ ((cmbNormalizedExposure ctx i c : ℕ) : ℝ) := by exact_mod_cast h2
  have hnat :
      1536 * cmbNormalizedExposure ctx i c ≤ 31 * (ctx.shell.X + err) := by
    exact cmb_safeCone_nat (cmbOverlap ctx c) (emcFibreExitMass ctx i) b c Mtot
      (ctx.shell.X + err) hc hbalance hsafe hambient
  have hcast : (1536 : ℝ) * (cmbNormalizedExposure ctx i c : ℝ)
      ≤ 31 * ((ctx.shell.X + err : ℕ) : ℝ) := by exact_mod_cast hnat
  have hsplit : ((ctx.shell.X + err : ℕ) : ℝ)
      = (ctx.shell.X : ℝ) + (err : ℝ) := by norm_num
  have h3 : (cmbNormalizedExposure ctx i c : ℝ)
      ≤ emcCap ctx + ((31 : ℝ) / 1536) * (err : ℝ) := by
    rw [hsplit] at hcast
    unfold emcCap
    nlinarith
  exact h1.trans (h2R.trans h3)

/-- V30-facing bridge from the O2 collar supply surface, retaining the deleted
endpoint/carry/tie collar as the exact finite error `collar.card`. -/
theorem v30AmbientAccountingWithErrorOn_of_o2_collar_supply_inputs
    (P₀ Q : Int) {β A : Type*} [DecidableEq (Nat -> Int)]
    (ctx : ActualFailureContext) {Mtot : Nat}
    (S : Finset A) (Omega : A -> Finset (Nat -> Int))
    (Lambda : (Nat -> Int) -> A) (masses : A -> Nat)
    (carrier post collar : Finset (Nat -> Int)) (Ij : Finset β)
    (piSt : (Nat -> Int) -> Nat × β)
    (keyOf : Nat × β -> Int × (Nat -> Int))
    (hMtot : Mtot <= Finset.sum S masses)
    (I : O2SupplyEmbedding.O2CollarSupplyInputs P₀ Q S Omega Lambda masses carrier
      post collar Ij ctx.shell.X piSt keyOf) :
    V30AmbientAccountingWithErrorOn ctx Ij.card collar.card Mtot :=
  le_trans hMtot
    (O2SupplyEmbedding.O2CollarSupplyInputs.summed_bound P₀ Q S Omega Lambda
      masses carrier post collar Ij ctx.shell.X piSt keyOf I)

/-- V30-facing O2 collar bridge after a finite estimate on the collar size. -/
theorem v30AmbientAccountingWithErrorOn_of_o2_collar_supply_inputs_with_error
    (P₀ Q : Int) {β A : Type*} [DecidableEq (Nat -> Int)]
    (ctx : ActualFailureContext) {Mtot E : Nat}
    (S : Finset A) (Omega : A -> Finset (Nat -> Int))
    (Lambda : (Nat -> Int) -> A) (masses : A -> Nat)
    (carrier post collar : Finset (Nat -> Int)) (Ij : Finset β)
    (piSt : (Nat -> Int) -> Nat × β)
    (keyOf : Nat × β -> Int × (Nat -> Int))
    (hMtot : Mtot <= Finset.sum S masses)
    (I : O2SupplyEmbedding.O2CollarSupplyInputs P₀ Q S Omega Lambda masses carrier
      post collar Ij ctx.shell.X piSt keyOf)
    (hcollar : collar.card <= E) :
    V30AmbientAccountingWithErrorOn ctx Ij.card E Mtot :=
  le_trans hMtot
    (O2SupplyEmbedding.O2CollarSupplyInputs.summed_bound_with_error P₀ Q S Omega
      Lambda masses carrier post collar Ij ctx.shell.X E piSt keyOf I hcollar)

/-- Coordinate-split version of the V30-facing O2 collar bridge, retaining
`collar.card` as the exact finite error. -/
theorem v30AmbientAccountingWithErrorOn_of_o2_collar_supply_coordinate_inputs
    (P₀ Q : Int) {β A : Type*} [DecidableEq (Nat -> Int)]
    (ctx : ActualFailureContext) {Mtot : Nat}
    (S : Finset A) (Omega : A -> Finset (Nat -> Int))
    (Lambda : (Nat -> Int) -> A) (masses : A -> Nat)
    (carrier post collar : Finset (Nat -> Int)) (Ij : Finset β)
    (piSt : (Nat -> Int) -> Nat × β)
    (keyOf : Nat × β -> Int × (Nat -> Int))
    (hMtot : Mtot <= Finset.sum S masses)
    (I : O2SupplyEmbedding.O2CollarSupplyCoordinateInputs P₀ Q S Omega Lambda
      masses carrier post collar Ij ctx.shell.X piSt keyOf) :
    V30AmbientAccountingWithErrorOn ctx Ij.card collar.card Mtot :=
  le_trans hMtot
    (O2SupplyEmbedding.O2CollarSupplyCoordinateInputs.summed_bound P₀ Q S Omega
      Lambda masses carrier post collar Ij ctx.shell.X piSt keyOf I)

/-- Coordinate-split O2 collar bridge after a finite estimate on the collar size. -/
theorem v30AmbientAccountingWithErrorOn_of_o2_collar_supply_coordinate_inputs_with_error
    (P₀ Q : Int) {β A : Type*} [DecidableEq (Nat -> Int)]
    (ctx : ActualFailureContext) {Mtot E : Nat}
    (S : Finset A) (Omega : A -> Finset (Nat -> Int))
    (Lambda : (Nat -> Int) -> A) (masses : A -> Nat)
    (carrier post collar : Finset (Nat -> Int)) (Ij : Finset β)
    (piSt : (Nat -> Int) -> Nat × β)
    (keyOf : Nat × β -> Int × (Nat -> Int))
    (hMtot : Mtot <= Finset.sum S masses)
    (I : O2SupplyEmbedding.O2CollarSupplyCoordinateInputs P₀ Q S Omega Lambda
      masses carrier post collar Ij ctx.shell.X piSt keyOf)
    (hcollar : collar.card <= E) :
    V30AmbientAccountingWithErrorOn ctx Ij.card E Mtot :=
  le_trans hMtot
    (O2SupplyEmbedding.O2CollarSupplyCoordinateInputs.summed_bound_with_error P₀ Q
      S Omega Lambda masses carrier post collar Ij ctx.shell.X E piSt keyOf I hcollar)

/-- Unit-interval collar bridge, retaining the exact collar cardinality. -/
theorem v30AmbientAccountingWithError_of_o2_collar_supply_unit_inputs
    (P₀ Q : Int) {β A : Type*} [DecidableEq (Nat -> Int)]
    (ctx : ActualFailureContext) {Mtot : Nat}
    (S : Finset A) (Omega : A -> Finset (Nat -> Int))
    (Lambda : (Nat -> Int) -> A) (masses : A -> Nat)
    (carrier post collar : Finset (Nat -> Int)) (Ij : Finset β)
    (piSt : (Nat -> Int) -> Nat × β)
    (keyOf : Nat × β -> Int × (Nat -> Int))
    (hMtot : Mtot <= Finset.sum S masses)
    (hIj : Ij.card = 1)
    (I : O2SupplyEmbedding.O2CollarSupplyInputs P₀ Q S Omega Lambda masses carrier
      post collar Ij ctx.shell.X piSt keyOf) :
    V30AmbientAccountingWithError ctx collar.card Mtot := by
  have h := v30AmbientAccountingWithErrorOn_of_o2_collar_supply_inputs P₀ Q ctx
    S Omega Lambda masses carrier post collar Ij piSt keyOf hMtot I
  simpa [V30AmbientAccountingWithError, V30AmbientAccountingWithErrorOn, hIj] using h

/-- Unit-interval collar bridge after a finite estimate on the collar size. -/
theorem v30AmbientAccountingWithError_of_o2_collar_supply_unit_inputs_with_error
    (P₀ Q : Int) {β A : Type*} [DecidableEq (Nat -> Int)]
    (ctx : ActualFailureContext) {Mtot E : Nat}
    (S : Finset A) (Omega : A -> Finset (Nat -> Int))
    (Lambda : (Nat -> Int) -> A) (masses : A -> Nat)
    (carrier post collar : Finset (Nat -> Int)) (Ij : Finset β)
    (piSt : (Nat -> Int) -> Nat × β)
    (keyOf : Nat × β -> Int × (Nat -> Int))
    (hMtot : Mtot <= Finset.sum S masses)
    (hIj : Ij.card = 1)
    (I : O2SupplyEmbedding.O2CollarSupplyInputs P₀ Q S Omega Lambda masses carrier
      post collar Ij ctx.shell.X piSt keyOf)
    (hcollar : collar.card <= E) :
    V30AmbientAccountingWithError ctx E Mtot := by
  have h := v30AmbientAccountingWithErrorOn_of_o2_collar_supply_inputs_with_error
    P₀ Q ctx S Omega Lambda masses carrier post collar Ij piSt keyOf hMtot I hcollar
  simpa [V30AmbientAccountingWithError, V30AmbientAccountingWithErrorOn, hIj] using h

/-- Unit-interval coordinate-split collar bridge, retaining the exact collar
cardinality. -/
theorem v30AmbientAccountingWithError_of_o2_collar_supply_coordinate_unit_inputs
    (P₀ Q : Int) {β A : Type*} [DecidableEq (Nat -> Int)]
    (ctx : ActualFailureContext) {Mtot : Nat}
    (S : Finset A) (Omega : A -> Finset (Nat -> Int))
    (Lambda : (Nat -> Int) -> A) (masses : A -> Nat)
    (carrier post collar : Finset (Nat -> Int)) (Ij : Finset β)
    (piSt : (Nat -> Int) -> Nat × β)
    (keyOf : Nat × β -> Int × (Nat -> Int))
    (hMtot : Mtot <= Finset.sum S masses)
    (hIj : Ij.card = 1)
    (I : O2SupplyEmbedding.O2CollarSupplyCoordinateInputs P₀ Q S Omega Lambda
      masses carrier post collar Ij ctx.shell.X piSt keyOf) :
    V30AmbientAccountingWithError ctx collar.card Mtot := by
  have h := v30AmbientAccountingWithErrorOn_of_o2_collar_supply_coordinate_inputs
    P₀ Q ctx S Omega Lambda masses carrier post collar Ij piSt keyOf hMtot I
  simpa [V30AmbientAccountingWithError, V30AmbientAccountingWithErrorOn, hIj] using h

/-- Unit-interval coordinate-split collar bridge after a finite estimate on the
collar size. -/
theorem v30AmbientAccountingWithError_of_o2_collar_supply_coordinate_unit_inputs_with_error
    (P₀ Q : Int) {β A : Type*} [DecidableEq (Nat -> Int)]
    (ctx : ActualFailureContext) {Mtot E : Nat}
    (S : Finset A) (Omega : A -> Finset (Nat -> Int))
    (Lambda : (Nat -> Int) -> A) (masses : A -> Nat)
    (carrier post collar : Finset (Nat -> Int)) (Ij : Finset β)
    (piSt : (Nat -> Int) -> Nat × β)
    (keyOf : Nat × β -> Int × (Nat -> Int))
    (hMtot : Mtot <= Finset.sum S masses)
    (hIj : Ij.card = 1)
    (I : O2SupplyEmbedding.O2CollarSupplyCoordinateInputs P₀ Q S Omega Lambda
      masses carrier post collar Ij ctx.shell.X piSt keyOf)
    (hcollar : collar.card <= E) :
    V30AmbientAccountingWithError ctx E Mtot := by
  have h :=
    v30AmbientAccountingWithErrorOn_of_o2_collar_supply_coordinate_inputs_with_error
      P₀ Q ctx S Omega Lambda masses carrier post collar Ij piSt keyOf hMtot I hcollar
  simpa [V30AmbientAccountingWithError, V30AmbientAccountingWithErrorOn, hIj] using h

/-- If the deleted collar is actually empty in the packaged O2 collar surface,
the interval-scaled no-remainder ambient accounting bound is recovered. -/
theorem v30AmbientAccountingOn_of_o2_collar_supply_inputs_zero_collar
    (P₀ Q : Int) {β A : Type*} [DecidableEq (Nat -> Int)]
    (ctx : ActualFailureContext) {Mtot : Nat}
    (S : Finset A) (Omega : A -> Finset (Nat -> Int))
    (Lambda : (Nat -> Int) -> A) (masses : A -> Nat)
    (carrier post collar : Finset (Nat -> Int)) (Ij : Finset β)
    (piSt : (Nat -> Int) -> Nat × β)
    (keyOf : Nat × β -> Int × (Nat -> Int))
    (hMtot : Mtot <= Finset.sum S masses)
    (I : O2SupplyEmbedding.O2CollarSupplyInputs P₀ Q S Omega Lambda masses carrier
      post collar Ij ctx.shell.X piSt keyOf)
    (hcollar : collar.card = 0) :
    V30AmbientAccountingOn ctx Ij.card Mtot := by
  have h := v30AmbientAccountingWithErrorOn_of_o2_collar_supply_inputs_with_error
    P₀ Q ctx S Omega Lambda masses carrier post collar Ij piSt keyOf hMtot I
    (E := 0) (by simp [hcollar])
  exact v30AmbientAccountingOn_of_withErrorOn_zero ctx h

/-- Empty-collar shorthand for the no-remainder interval-scaled O2 collar bridge. -/
theorem v30AmbientAccountingOn_of_o2_collar_supply_inputs_empty_collar
    (P₀ Q : Int) {β A : Type*} [DecidableEq (Nat -> Int)]
    (ctx : ActualFailureContext) {Mtot : Nat}
    (S : Finset A) (Omega : A -> Finset (Nat -> Int))
    (Lambda : (Nat -> Int) -> A) (masses : A -> Nat)
    (carrier post : Finset (Nat -> Int)) (Ij : Finset β)
    (piSt : (Nat -> Int) -> Nat × β)
    (keyOf : Nat × β -> Int × (Nat -> Int))
    (hMtot : Mtot <= Finset.sum S masses)
    (I : O2SupplyEmbedding.O2CollarSupplyInputs P₀ Q S Omega Lambda masses carrier
      post ∅ Ij ctx.shell.X piSt keyOf) :
    V30AmbientAccountingOn ctx Ij.card Mtot := by
  exact v30AmbientAccountingOn_of_o2_collar_supply_inputs_zero_collar P₀ Q ctx
    S Omega Lambda masses carrier post ∅ Ij piSt keyOf hMtot I (by simp)

/-- Unit-interval no-remainder ambient accounting from an O2 collar surface with
zero collar. -/
theorem v30AmbientAccounting_of_o2_collar_supply_unit_inputs_zero_collar
    (P₀ Q : Int) {β A : Type*} [DecidableEq (Nat -> Int)]
    (ctx : ActualFailureContext) {Mtot : Nat}
    (S : Finset A) (Omega : A -> Finset (Nat -> Int))
    (Lambda : (Nat -> Int) -> A) (masses : A -> Nat)
    (carrier post collar : Finset (Nat -> Int)) (Ij : Finset β)
    (piSt : (Nat -> Int) -> Nat × β)
    (keyOf : Nat × β -> Int × (Nat -> Int))
    (hMtot : Mtot <= Finset.sum S masses)
    (hIj : Ij.card = 1)
    (I : O2SupplyEmbedding.O2CollarSupplyInputs P₀ Q S Omega Lambda masses carrier
      post collar Ij ctx.shell.X piSt keyOf)
    (hcollar : collar.card = 0) :
    V30AmbientAccounting ctx Mtot := by
  have h := v30AmbientAccountingWithError_of_o2_collar_supply_unit_inputs_with_error
    P₀ Q ctx S Omega Lambda masses carrier post collar Ij piSt keyOf hMtot hIj I
    (E := 0) (by simp [hcollar])
  exact v30AmbientAccounting_of_withError_zero ctx h

/-- Unit-interval no-remainder ambient accounting from an O2 collar surface with
empty collar. -/
theorem v30AmbientAccounting_of_o2_collar_supply_unit_inputs_empty_collar
    (P₀ Q : Int) {β A : Type*} [DecidableEq (Nat -> Int)]
    (ctx : ActualFailureContext) {Mtot : Nat}
    (S : Finset A) (Omega : A -> Finset (Nat -> Int))
    (Lambda : (Nat -> Int) -> A) (masses : A -> Nat)
    (carrier post : Finset (Nat -> Int)) (Ij : Finset β)
    (piSt : (Nat -> Int) -> Nat × β)
    (keyOf : Nat × β -> Int × (Nat -> Int))
    (hMtot : Mtot <= Finset.sum S masses)
    (hIj : Ij.card = 1)
    (I : O2SupplyEmbedding.O2CollarSupplyInputs P₀ Q S Omega Lambda masses carrier
      post ∅ Ij ctx.shell.X piSt keyOf) :
    V30AmbientAccounting ctx Mtot := by
  exact v30AmbientAccounting_of_o2_collar_supply_unit_inputs_zero_collar P₀ Q ctx
    S Omega Lambda masses carrier post ∅ Ij piSt keyOf hMtot hIj I (by simp)

/-- Coordinate-split zero-collar version of the no-remainder interval-scaled O2
collar bridge. -/
theorem v30AmbientAccountingOn_of_o2_collar_supply_coordinate_inputs_zero_collar
    (P₀ Q : Int) {β A : Type*} [DecidableEq (Nat -> Int)]
    (ctx : ActualFailureContext) {Mtot : Nat}
    (S : Finset A) (Omega : A -> Finset (Nat -> Int))
    (Lambda : (Nat -> Int) -> A) (masses : A -> Nat)
    (carrier post collar : Finset (Nat -> Int)) (Ij : Finset β)
    (piSt : (Nat -> Int) -> Nat × β)
    (keyOf : Nat × β -> Int × (Nat -> Int))
    (hMtot : Mtot <= Finset.sum S masses)
    (I : O2SupplyEmbedding.O2CollarSupplyCoordinateInputs P₀ Q S Omega Lambda
      masses carrier post collar Ij ctx.shell.X piSt keyOf)
    (hcollar : collar.card = 0) :
    V30AmbientAccountingOn ctx Ij.card Mtot := by
  have h :=
    v30AmbientAccountingWithErrorOn_of_o2_collar_supply_coordinate_inputs_with_error
      P₀ Q ctx S Omega Lambda masses carrier post collar Ij piSt keyOf hMtot I
      (E := 0) (by simp [hcollar])
  exact v30AmbientAccountingOn_of_withErrorOn_zero ctx h

/-- Coordinate-split empty-collar shorthand for no-remainder interval accounting. -/
theorem v30AmbientAccountingOn_of_o2_collar_supply_coordinate_inputs_empty_collar
    (P₀ Q : Int) {β A : Type*} [DecidableEq (Nat -> Int)]
    (ctx : ActualFailureContext) {Mtot : Nat}
    (S : Finset A) (Omega : A -> Finset (Nat -> Int))
    (Lambda : (Nat -> Int) -> A) (masses : A -> Nat)
    (carrier post : Finset (Nat -> Int)) (Ij : Finset β)
    (piSt : (Nat -> Int) -> Nat × β)
    (keyOf : Nat × β -> Int × (Nat -> Int))
    (hMtot : Mtot <= Finset.sum S masses)
    (I : O2SupplyEmbedding.O2CollarSupplyCoordinateInputs P₀ Q S Omega Lambda
      masses carrier post ∅ Ij ctx.shell.X piSt keyOf) :
    V30AmbientAccountingOn ctx Ij.card Mtot := by
  exact v30AmbientAccountingOn_of_o2_collar_supply_coordinate_inputs_zero_collar P₀ Q ctx
    S Omega Lambda masses carrier post ∅ Ij piSt keyOf hMtot I (by simp)

/-- Unit-interval coordinate-split zero-collar bridge to the no-remainder ambient
accounting input consumed by the C1 cap. -/
theorem v30AmbientAccounting_of_o2_collar_supply_coordinate_unit_inputs_zero_collar
    (P₀ Q : Int) {β A : Type*} [DecidableEq (Nat -> Int)]
    (ctx : ActualFailureContext) {Mtot : Nat}
    (S : Finset A) (Omega : A -> Finset (Nat -> Int))
    (Lambda : (Nat -> Int) -> A) (masses : A -> Nat)
    (carrier post collar : Finset (Nat -> Int)) (Ij : Finset β)
    (piSt : (Nat -> Int) -> Nat × β)
    (keyOf : Nat × β -> Int × (Nat -> Int))
    (hMtot : Mtot <= Finset.sum S masses)
    (hIj : Ij.card = 1)
    (I : O2SupplyEmbedding.O2CollarSupplyCoordinateInputs P₀ Q S Omega Lambda
      masses carrier post collar Ij ctx.shell.X piSt keyOf)
    (hcollar : collar.card = 0) :
    V30AmbientAccounting ctx Mtot := by
  have h :=
    v30AmbientAccountingWithError_of_o2_collar_supply_coordinate_unit_inputs_with_error
      P₀ Q ctx S Omega Lambda masses carrier post collar Ij piSt keyOf hMtot hIj I
      (E := 0) (by simp [hcollar])
  exact v30AmbientAccounting_of_withError_zero ctx h

/-- Unit-interval coordinate-split empty-collar bridge to the no-remainder ambient
accounting input consumed by the C1 cap. -/
theorem v30AmbientAccounting_of_o2_collar_supply_coordinate_unit_inputs_empty_collar
    (P₀ Q : Int) {β A : Type*} [DecidableEq (Nat -> Int)]
    (ctx : ActualFailureContext) {Mtot : Nat}
    (S : Finset A) (Omega : A -> Finset (Nat -> Int))
    (Lambda : (Nat -> Int) -> A) (masses : A -> Nat)
    (carrier post : Finset (Nat -> Int)) (Ij : Finset β)
    (piSt : (Nat -> Int) -> Nat × β)
    (keyOf : Nat × β -> Int × (Nat -> Int))
    (hMtot : Mtot <= Finset.sum S masses)
    (hIj : Ij.card = 1)
    (I : O2SupplyEmbedding.O2CollarSupplyCoordinateInputs P₀ Q S Omega Lambda
      masses carrier post ∅ Ij ctx.shell.X piSt keyOf) :
    V30AmbientAccounting ctx Mtot := by
  exact v30AmbientAccounting_of_o2_collar_supply_coordinate_unit_inputs_zero_collar P₀ Q ctx
    S Omega Lambda masses carrier post ∅ Ij piSt keyOf hMtot hIj I (by simp)

/-- The v30 off-pin SAFE-CONE cell datum for class `i`: a period `c ≥ 1`, a share
numerator `b`, an ambient phase mass `M_tot`, the fibre `c`-spacing (RISK e, AB
recurrent-pair certificate), the RISK c balance (3rd conjunct), the safe-cone cell
inequality (FREE for exit-light survivors via `v30_ctx_exitLight_safe`), and the
RISK b ambient bound (5th conjunct). -/
def V30OffPinSafeConeDatum (ctx : ActualFailureContext) (i : Fin 7) (b c Mtot : ℕ) : Prop :=
  1 ≤ c
  ∧ (∀ x ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i,
      ∀ z ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i,
        x ≤ z → c ∣ z - x)
  ∧ c * emcFibreExitMass ctx i ≤ b * Mtot
  ∧ 1536 * (cmbOverlap ctx c * b) ≤ 31 * c
  ∧ Mtot ≤ ctx.shell.X

/-- Finite-error variant of `V30OffPinSafeConeDatum`.  This is the exact
post-collar datum shape: the safe-cone geometry and mass-normalized balance are
unchanged, while the ambient accounting keeps an explicit `err` term. -/
def V30OffPinSafeConeDatumWithError
    (ctx : ActualFailureContext) (i : Fin 7) (b c err Mtot : ℕ) : Prop :=
  1 ≤ c
  ∧ (∀ x ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i,
      ∀ z ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i,
        x ≤ z → c ∣ z - x)
  ∧ c * emcFibreExitMass ctx i ≤ b * Mtot
  ∧ 1536 * (cmbOverlap ctx c * b) ≤ 31 * c
  ∧ V30AmbientAccountingWithError ctx err Mtot

/-- The datum's 3rd conjunct IS the named RISK c residual `V30MeasurePreservation`. -/
theorem v30_safeConeDatum_riskc_eq (ctx : ActualFailureContext) (i : Fin 7) (b c Mtot : ℕ) :
    V30MeasurePreservation ctx i b c Mtot ↔ c * emcFibreExitMass ctx i ≤ b * Mtot :=
  Iff.rfl

/-- The datum's 5th conjunct IS the named RISK b residual `V30AmbientAccounting`. -/
theorem v30_safeConeDatum_riskb_eq (ctx : ActualFailureContext) (Mtot : ℕ) :
    V30AmbientAccounting ctx Mtot ↔ Mtot ≤ ctx.shell.X :=
  Iff.rfl

/-- A zero-error finite datum recovers the ordinary safe-cone datum. -/
theorem v30_safeConeDatum_of_withError_zero
    (ctx : ActualFailureContext) (i : Fin 7) {b c Mtot : ℕ}
    (h : V30OffPinSafeConeDatumWithError ctx i b c 0 Mtot) :
    V30OffPinSafeConeDatum ctx i b c Mtot := by
  obtain ⟨hc, hspace, hbal, hsafe, hamb⟩ := h
  exact ⟨hc, hspace, hbal, hsafe,
    v30AmbientAccounting_of_withError_zero ctx hamb⟩

/-- The per-class cap, fed from the safe-cone datum. -/
theorem v30_offPin_classCap_of_datum (ctx : ActualFailureContext) (i : Fin 7)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4) {b c Mtot : ℕ}
    (h : V30OffPinSafeConeDatum ctx i b c Mtot) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) i ≤ emcCap ctx := by
  obtain ⟨hc, hspace, hbal, hsafe, hamb⟩ := h
  exact v30_offPin_classCap ctx i hband hc hspace hbal hsafe hamb

/-- The per-class cap with an explicit finite collar/error term, fed from the
finite-error safe-cone datum. -/
theorem v30_offPin_classCap_withError_of_datum
    (ctx : ActualFailureContext) (i : Fin 7)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4) {b c err Mtot : ℕ}
    (h : V30OffPinSafeConeDatumWithError ctx i b c err Mtot) :
    V30OffPinClassCapWithError ctx i err := by
  obtain ⟨hc, hspace, hbal, hsafe, hamb⟩ := h
  exact v30_offPin_classCap_withError ctx i hband hc hspace hbal hsafe hamb

/-- Assemble the off-pin safe-cone datum from the two named residuals and the
geometric safe-cone inputs.  This keeps RISK b/c as explicit inputs while closing
the bookkeeping step that feeds the C1 capstone. -/
theorem v30_safeConeDatum_of_measure_ambient (ctx : ActualFailureContext) (i : Fin 7)
    {b c Mtot : Nat} (hc : 1 <= c)
    (hspace : forall x, x ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
      forall z, z ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
        x <= z -> c ∣ z - x)
    (hmeasure : V30MeasurePreservation ctx i b c Mtot)
    (hsafe : 1536 * (cmbOverlap ctx c * b) <= 31 * c)
    (hambient : V30AmbientAccounting ctx Mtot) :
    V30OffPinSafeConeDatum ctx i b c Mtot :=
  ⟨hc, hspace, hmeasure, hsafe, hambient⟩

/-- Assemble the finite-error off-pin safe-cone datum from the same RISK-c and
geometric inputs, but with RISK-b supplied in explicit-error form. -/
theorem v30_safeConeDatumWithError_of_measure_ambient
    (ctx : ActualFailureContext) (i : Fin 7)
    {b c err Mtot : Nat} (hc : 1 <= c)
    (hspace : forall x, x ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
      forall z, z ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
        x <= z -> c ∣ z - x)
    (hmeasure : V30MeasurePreservation ctx i b c Mtot)
    (hsafe : 1536 * (cmbOverlap ctx c * b) <= 31 * c)
    (hambient : V30AmbientAccountingWithError ctx err Mtot) :
    V30OffPinSafeConeDatumWithError ctx i b c err Mtot :=
  ⟨hc, hspace, hmeasure, hsafe, hambient⟩

/-- Safe-cone datum with RISK b supplied by the O2 ambient-injection core in the
single-cell form.  RISK c and the AB safe-cone geometry stay explicit. -/
theorem v30_safeConeDatum_of_measure_o2_unit_carrier
    {Ω β : Type*} [DecidableEq Ω]
    (ctx : ActualFailureContext) (i : Fin 7) {b c Mtot : Nat}
    (hc : 1 <= c)
    (hspace : forall x, x ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
      forall z, z ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
        x <= z -> c ∣ z - x)
    (hmeasure : V30MeasurePreservation ctx i b c Mtot)
    (hsafe : 1536 * (cmbOverlap ctx c * b) <= 31 * c)
    (cell carrier : Finset Ω) (rect : Finset β) (πst : Ω -> β)
    (hsub : cell ⊆ carrier)
    (hcell : Mtot <= cell.card)
    (hmaps : forall ω, ω ∈ carrier -> πst ω ∈ rect)
    (hinj : Set.InjOn πst carrier)
    (hrect : rect.card <= ctx.shell.X) :
    V30OffPinSafeConeDatum ctx i b c Mtot :=
  v30_safeConeDatum_of_measure_ambient ctx i hc hspace hmeasure hsafe
    (v30AmbientAccounting_of_o2_unit_carrier ctx cell carrier rect πst
      hsub hcell hmaps hinj hrect)

/-- Safe-cone datum with RISK b supplied by the constructed-rectangle O2
supply surface.  This is the direct consumer-facing form of the AK/AD O2
package for a unit interval `|I_j| = 1`; RISK c and the AB safe-cone geometry
remain explicit. -/
theorem v30_safeConeDatum_of_measure_o2_supply_unit_inputs
    (P₀ Q : Int) {β A : Type*}
    (ctx : ActualFailureContext) (i : Fin 7) {b c Mtot : Nat}
    (hc : 1 <= c)
    (hspace : forall x, x ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
      forall z, z ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
        x <= z -> c ∣ z - x)
    (hmeasure : V30MeasurePreservation ctx i b c Mtot)
    (hsafe : 1536 * (cmbOverlap ctx c * b) <= 31 * c)
    (S : Finset A) (Omega : A -> Finset (Nat -> Int))
    (Lambda : (Nat -> Int) -> A) (masses : A -> Nat)
    (carrier : Finset (Nat -> Int)) (Ij : Finset β)
    (piSt : (Nat -> Int) -> Nat × β)
    (keyOf : Nat × β -> Int × (Nat -> Int))
    (hMtot : Mtot <= Finset.sum S masses)
    (hIj : Ij.card = 1)
    (I : O2SupplyEmbedding.O2SupplyInputs P₀ Q S Omega Lambda masses carrier Ij
      ctx.shell.X piSt keyOf) :
    V30OffPinSafeConeDatum ctx i b c Mtot :=
  v30_safeConeDatum_of_measure_ambient ctx i hc hspace hmeasure hsafe
    (v30AmbientAccounting_of_o2_supply_unit_inputs P₀ Q ctx S Omega Lambda masses
      carrier Ij piSt keyOf hMtot hIj I)

/-- Per-class C1 cap with RISK b supplied by the constructed-rectangle O2
supply surface. -/
theorem v30_offPin_classCap_of_measure_o2_supply_unit_inputs
    (P₀ Q : Int) {β A : Type*}
    (ctx : ActualFailureContext) (i : Fin 7)
    (hband : fixedFamilyRecurrentBand ctx <= 4) {b c Mtot : Nat}
    (hc : 1 <= c)
    (hspace : forall x, x ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
      forall z, z ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
        x <= z -> c ∣ z - x)
    (hmeasure : V30MeasurePreservation ctx i b c Mtot)
    (hsafe : 1536 * (cmbOverlap ctx c * b) <= 31 * c)
    (S : Finset A) (Omega : A -> Finset (Nat -> Int))
    (Lambda : (Nat -> Int) -> A) (masses : A -> Nat)
    (carrier : Finset (Nat -> Int)) (Ij : Finset β)
    (piSt : (Nat -> Int) -> Nat × β)
    (keyOf : Nat × β -> Int × (Nat -> Int))
    (hMtot : Mtot <= Finset.sum S masses)
    (hIj : Ij.card = 1)
    (I : O2SupplyEmbedding.O2SupplyInputs P₀ Q S Omega Lambda masses carrier Ij
      ctx.shell.X piSt keyOf) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) i <= emcCap ctx :=
  v30_offPin_classCap_of_datum ctx i hband
    (v30_safeConeDatum_of_measure_o2_supply_unit_inputs P₀ Q ctx i hc hspace
      hmeasure hsafe S Omega Lambda masses carrier Ij piSt keyOf hMtot hIj I)

/-- Safe-cone datum with RISK b supplied by the coordinate-split constructed O2
supply surface.  This is the direct consumer-facing coordinate version of the
AK/AD O2 package for a unit interval `|I_j| = 1`. -/
theorem v30_safeConeDatum_of_measure_o2_supply_coordinate_unit_inputs
    (P₀ Q : Int) {β A : Type*}
    (ctx : ActualFailureContext) (i : Fin 7) {b c Mtot : Nat}
    (hc : 1 <= c)
    (hspace : forall x, x ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
      forall z, z ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
        x <= z -> c ∣ z - x)
    (hmeasure : V30MeasurePreservation ctx i b c Mtot)
    (hsafe : 1536 * (cmbOverlap ctx c * b) <= 31 * c)
    (S : Finset A) (Omega : A -> Finset (Nat -> Int))
    (Lambda : (Nat -> Int) -> A) (masses : A -> Nat)
    (carrier : Finset (Nat -> Int)) (Ij : Finset β)
    (piSt : (Nat -> Int) -> Nat × β)
    (keyOf : Nat × β -> Int × (Nat -> Int))
    (hMtot : Mtot <= Finset.sum S masses)
    (hIj : Ij.card = 1)
    (I : O2SupplyEmbedding.O2SupplyCoordinateInputs P₀ Q S Omega Lambda masses
      carrier Ij ctx.shell.X piSt keyOf) :
    V30OffPinSafeConeDatum ctx i b c Mtot :=
  v30_safeConeDatum_of_measure_ambient ctx i hc hspace hmeasure hsafe
    (v30AmbientAccounting_of_o2_supply_coordinate_unit_inputs P₀ Q ctx S Omega
      Lambda masses carrier Ij piSt keyOf hMtot hIj I)

/-- Per-class C1 cap with RISK b supplied by the coordinate-split constructed
O2 supply surface. -/
theorem v30_offPin_classCap_of_measure_o2_supply_coordinate_unit_inputs
    (P₀ Q : Int) {β A : Type*}
    (ctx : ActualFailureContext) (i : Fin 7)
    (hband : fixedFamilyRecurrentBand ctx <= 4) {b c Mtot : Nat}
    (hc : 1 <= c)
    (hspace : forall x, x ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
      forall z, z ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
        x <= z -> c ∣ z - x)
    (hmeasure : V30MeasurePreservation ctx i b c Mtot)
    (hsafe : 1536 * (cmbOverlap ctx c * b) <= 31 * c)
    (S : Finset A) (Omega : A -> Finset (Nat -> Int))
    (Lambda : (Nat -> Int) -> A) (masses : A -> Nat)
    (carrier : Finset (Nat -> Int)) (Ij : Finset β)
    (piSt : (Nat -> Int) -> Nat × β)
    (keyOf : Nat × β -> Int × (Nat -> Int))
    (hMtot : Mtot <= Finset.sum S masses)
    (hIj : Ij.card = 1)
    (I : O2SupplyEmbedding.O2SupplyCoordinateInputs P₀ Q S Omega Lambda masses
      carrier Ij ctx.shell.X piSt keyOf) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) i <= emcCap ctx :=
  v30_offPin_classCap_of_datum ctx i hband
    (v30_safeConeDatum_of_measure_o2_supply_coordinate_unit_inputs P₀ Q ctx i hc
      hspace hmeasure hsafe S Omega Lambda masses carrier Ij piSt keyOf hMtot hIj I)

/-- Finite-error safe-cone datum with RISK b supplied by the coordinate-split
O2 collar supply surface.  Unlike the zero-collar entry points below, this
keeps the deleted collar as the explicit error term `collar.card`. -/
theorem v30_safeConeDatumWithError_of_measure_o2_collar_supply_coordinate_unit_inputs
    (P₀ Q : Int) {β A : Type*} [DecidableEq (Nat -> Int)]
    (ctx : ActualFailureContext) (i : Fin 7) {b c Mtot : Nat}
    (hc : 1 <= c)
    (hspace : forall x, x ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
      forall z, z ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
        x <= z -> c ∣ z - x)
    (hmeasure : V30MeasurePreservation ctx i b c Mtot)
    (hsafe : 1536 * (cmbOverlap ctx c * b) <= 31 * c)
    (S : Finset A) (Omega : A -> Finset (Nat -> Int))
    (Lambda : (Nat -> Int) -> A) (masses : A -> Nat)
    (carrier post collar : Finset (Nat -> Int)) (Ij : Finset β)
    (piSt : (Nat -> Int) -> Nat × β)
    (keyOf : Nat × β -> Int × (Nat -> Int))
    (hMtot : Mtot <= Finset.sum S masses)
    (hIj : Ij.card = 1)
    (I : O2SupplyEmbedding.O2CollarSupplyCoordinateInputs P₀ Q S Omega Lambda
      masses carrier post collar Ij ctx.shell.X piSt keyOf) :
    V30OffPinSafeConeDatumWithError ctx i b c collar.card Mtot :=
  v30_safeConeDatumWithError_of_measure_ambient ctx i hc hspace hmeasure hsafe
    (v30AmbientAccountingWithError_of_o2_collar_supply_coordinate_unit_inputs
      P₀ Q ctx S Omega Lambda masses carrier post collar Ij piSt keyOf hMtot hIj I)

/-- Per-class finite-error cap with the ambient bound supplied by the
coordinate-split O2 collar supply surface.  This is the explicit-collar
counterpart of `v30_offPin_classCap_of_measure_o2_supply_coordinate_unit_inputs`. -/
theorem v30_offPin_classCapWithError_of_measure_o2_collar_supply_coordinate_unit_inputs
    (P₀ Q : Int) {β A : Type*} [DecidableEq (Nat -> Int)]
    (ctx : ActualFailureContext) (i : Fin 7)
    (hband : fixedFamilyRecurrentBand ctx <= 4) {b c Mtot : Nat}
    (hc : 1 <= c)
    (hspace : forall x, x ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
      forall z, z ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
        x <= z -> c ∣ z - x)
    (hmeasure : V30MeasurePreservation ctx i b c Mtot)
    (hsafe : 1536 * (cmbOverlap ctx c * b) <= 31 * c)
    (S : Finset A) (Omega : A -> Finset (Nat -> Int))
    (Lambda : (Nat -> Int) -> A) (masses : A -> Nat)
    (carrier post collar : Finset (Nat -> Int)) (Ij : Finset β)
    (piSt : (Nat -> Int) -> Nat × β)
    (keyOf : Nat × β -> Int × (Nat -> Int))
    (hMtot : Mtot <= Finset.sum S masses)
    (hIj : Ij.card = 1)
    (I : O2SupplyEmbedding.O2CollarSupplyCoordinateInputs P₀ Q S Omega Lambda
      masses carrier post collar Ij ctx.shell.X piSt keyOf) :
    V30OffPinClassCapWithError ctx i collar.card :=
  v30_offPin_classCap_withError_of_datum ctx i hband
    (v30_safeConeDatumWithError_of_measure_o2_collar_supply_coordinate_unit_inputs
      P₀ Q ctx i hc hspace hmeasure hsafe S Omega Lambda masses carrier post collar
      Ij piSt keyOf hMtot hIj I)

/-- A Lane-B cycle mass datum supplies the named RISK-c measure-preservation
input used by the Lane-C safe-cone datum, once its exit mass is identified with
the routed class fibre exit mass. -/
theorem v30_measurePreservation_of_cycleDatum
    (ctx : ActualFailureContext) (i : Fin 7) (D : CycleMassDatum)
    (hexit : D.exitMass = emcFibreExitMass ctx i) {Mtot : Nat}
    (hM : D.totalMass <= Mtot) :
    V30MeasurePreservation ctx i D.E.card D.c Mtot :=
  cmb_balance_of_datum ctx i D hexit hM

/-- A Lane-B cycle mass datum, the ambient accounting residual, and the AB
safe-cone geometry assemble the full Lane-C safe-cone datum.  This is the direct
`CycleMassDatum` form of `v30_safeConeDatum_of_measure_ambient`. -/
theorem v30_safeConeDatum_of_cycleDatum_ambient
    (ctx : ActualFailureContext) (i : Fin 7) (D : CycleMassDatum)
    (hexit : D.exitMass = emcFibreExitMass ctx i) {Mtot : Nat}
    (hM : D.totalMass <= Mtot)
    (hspace : forall x, x ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
      forall z, z ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
        x <= z -> D.c ∣ z - x)
    (hsafe : 1536 * (cmbOverlap ctx D.c * D.E.card) <= 31 * D.c)
    (hambient : V30AmbientAccounting ctx Mtot) :
    V30OffPinSafeConeDatum ctx i D.E.card D.c Mtot :=
  v30_safeConeDatum_of_measure_ambient ctx i D.hc hspace
    (v30_measurePreservation_of_cycleDatum ctx i D hexit hM) hsafe hambient

/-- Per-class C1 cap stated directly from the Lane-B cycle mass datum plus the
remaining ambient/safe-cone geometric inputs. -/
theorem v30_offPin_classCap_of_cycleDatum_ambient
    (ctx : ActualFailureContext) (i : Fin 7)
    (hband : fixedFamilyRecurrentBand ctx <= 4) (D : CycleMassDatum)
    (hexit : D.exitMass = emcFibreExitMass ctx i) {Mtot : Nat}
    (hM : D.totalMass <= Mtot)
    (hspace : forall x, x ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
      forall z, z ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
        x <= z -> D.c ∣ z - x)
    (hsafe : 1536 * (cmbOverlap ctx D.c * D.E.card) <= 31 * D.c)
    (hambient : V30AmbientAccounting ctx Mtot) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) i <= emcCap ctx :=
  v30_offPin_classCap_of_datum ctx i hband
    (v30_safeConeDatum_of_cycleDatum_ambient ctx i D hexit hM hspace hsafe hambient)

/-- Lane-B cycle mass plus the O2 ambient-injection core assemble the full
Lane-C safe-cone datum: RISK c comes from `CycleMassDatum`, while RISK b comes
from the single-cell O2 carrier injection. -/
theorem v30_safeConeDatum_of_cycleDatum_o2_unit_carrier
    {Ω β : Type*} [DecidableEq Ω]
    (ctx : ActualFailureContext) (i : Fin 7) (D : CycleMassDatum)
    (hexit : D.exitMass = emcFibreExitMass ctx i) {Mtot : Nat}
    (hM : D.totalMass <= Mtot)
    (hspace : forall x, x ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
      forall z, z ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
        x <= z -> D.c ∣ z - x)
    (hsafe : 1536 * (cmbOverlap ctx D.c * D.E.card) <= 31 * D.c)
    (cell carrier : Finset Ω) (rect : Finset β) (πst : Ω -> β)
    (hsub : cell ⊆ carrier)
    (hcell : Mtot <= cell.card)
    (hmaps : forall ω, ω ∈ carrier -> πst ω ∈ rect)
    (hinj : Set.InjOn πst carrier)
    (hrect : rect.card <= ctx.shell.X) :
    V30OffPinSafeConeDatum ctx i D.E.card D.c Mtot :=
  v30_safeConeDatum_of_measure_o2_unit_carrier ctx i D.hc hspace
    (v30_measurePreservation_of_cycleDatum ctx i D hexit hM) hsafe
    cell carrier rect πst hsub hcell hmaps hinj hrect

/-- Per-class C1 cap from the two in-tree supply bridges together: the Lane-B
cycle mass datum supplies the phase balance and the O2 carrier injection supplies
the ambient accounting. -/
theorem v30_offPin_classCap_of_cycleDatum_o2_unit_carrier
    {Ω β : Type*} [DecidableEq Ω]
    (ctx : ActualFailureContext) (i : Fin 7)
    (hband : fixedFamilyRecurrentBand ctx <= 4) (D : CycleMassDatum)
    (hexit : D.exitMass = emcFibreExitMass ctx i) {Mtot : Nat}
    (hM : D.totalMass <= Mtot)
    (hspace : forall x, x ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
      forall z, z ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
        x <= z -> D.c ∣ z - x)
    (hsafe : 1536 * (cmbOverlap ctx D.c * D.E.card) <= 31 * D.c)
    (cell carrier : Finset Ω) (rect : Finset β) (πst : Ω -> β)
    (hsub : cell ⊆ carrier)
    (hcell : Mtot <= cell.card)
    (hmaps : forall ω, ω ∈ carrier -> πst ω ∈ rect)
    (hinj : Set.InjOn πst carrier)
    (hrect : rect.card <= ctx.shell.X) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) i <= emcCap ctx :=
  v30_offPin_classCap_of_datum ctx i hband
    (v30_safeConeDatum_of_cycleDatum_o2_unit_carrier ctx i D hexit hM hspace hsafe
      cell carrier rect πst hsub hcell hmaps hinj hrect)

/-- Exit-light singleton-exit cycle datum plus O2 ambient carrier data assemble
the worst-case safe-cone datum directly. -/
theorem v30_exitLight_safeConeDatum_of_cycleDatum_o2_unit_carrier
    {Ω β : Type*} [DecidableEq Ω]
    (ctx : ActualFailureContext) (i : Fin 7) (D : CycleMassDatum)
    (hexit : D.exitMass = emcFibreExitMass ctx i) (hcard : D.E.card = 1)
    {Mtot : Nat} (hM : D.totalMass <= Mtot)
    (hsurv : boundedThreshold (shellLadderDepth ctx) < D.c) (hc64 : 64 <= D.c)
    (hspace : forall x, x ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
      forall z, z ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
        x <= z -> D.c ∣ z - x)
    (cell carrier : Finset Ω) (rect : Finset β) (πst : Ω -> β)
    (hsub : cell ⊆ carrier)
    (hcell : Mtot <= cell.card)
    (hmaps : forall ω, ω ∈ carrier -> πst ω ∈ rect)
    (hinj : Set.InjOn πst carrier)
    (hrect : rect.card <= ctx.shell.X) :
    V30OffPinSafeConeDatum ctx i 1 D.c Mtot := by
  have hmeasure : V30MeasurePreservation ctx i 1 D.c Mtot := by
    rw [← hcard]
    exact v30_measurePreservation_of_cycleDatum ctx i D hexit hM
  exact v30_safeConeDatum_of_measure_o2_unit_carrier ctx i D.hc hspace hmeasure
    (v30_ctx_exitLight_safe ctx hsurv rfl hc64)
    cell carrier rect πst hsub hcell hmaps hinj hrect

/-- Exit-light C1 cap from a singleton-exit `CycleMassDatum` plus the O2
ambient carrier injection. -/
theorem v30_offPin_classCap_exitLight_of_cycleDatum_o2_unit_carrier
    {Ω β : Type*} [DecidableEq Ω]
    (ctx : ActualFailureContext) (i : Fin 7)
    (hband : fixedFamilyRecurrentBand ctx <= 4) (D : CycleMassDatum)
    (hexit : D.exitMass = emcFibreExitMass ctx i) (hcard : D.E.card = 1)
    {Mtot : Nat} (hM : D.totalMass <= Mtot)
    (hsurv : boundedThreshold (shellLadderDepth ctx) < D.c) (hc64 : 64 <= D.c)
    (hspace : forall x, x ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
      forall z, z ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
        x <= z -> D.c ∣ z - x)
    (cell carrier : Finset Ω) (rect : Finset β) (πst : Ω -> β)
    (hsub : cell ⊆ carrier)
    (hcell : Mtot <= cell.card)
    (hmaps : forall ω, ω ∈ carrier -> πst ω ∈ rect)
    (hinj : Set.InjOn πst carrier)
    (hrect : rect.card <= ctx.shell.X) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) i <= emcCap ctx :=
  v30_offPin_classCap_of_datum ctx i hband
    (v30_exitLight_safeConeDatum_of_cycleDatum_o2_unit_carrier ctx i D hexit hcard hM
      hsurv hc64 hspace cell carrier rect πst hsub hcell hmaps hinj hrect)

/-- Packaged single-cell off-pin supply surface: Lane B's cycle mass datum,
O2's ambient carrier injection, and the AB safe-cone geometry for one class.
It exposes no new mathematics; it is the compact input form consumed by the
combined RISK b/c bridge above. -/
structure V30CycleO2SafeConeInputs {Ω β : Type*} [DecidableEq Ω]
    (ctx : ActualFailureContext) (i : Fin 7) where
  D : CycleMassDatum
  Mtot : Nat
  hexit : D.exitMass = emcFibreExitMass ctx i
  hM : D.totalMass <= Mtot
  hspace : forall x, x ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
    forall z, z ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
      x <= z -> D.c ∣ z - x
  hsafe : 1536 * (cmbOverlap ctx D.c * D.E.card) <= 31 * D.c
  cell : Finset Ω
  carrier : Finset Ω
  rect : Finset β
  πst : Ω -> β
  hsub : cell ⊆ carrier
  hcell : Mtot <= cell.card
  hmaps : forall ω, ω ∈ carrier -> πst ω ∈ rect
  hinj : Set.InjOn πst carrier
  hrect : rect.card <= ctx.shell.X

namespace V30CycleO2SafeConeInputs

/-- The packaged Cycle/O2 input exposes the named RISK-c
measure-preservation residual supplied by the Lane-B cycle mass datum. -/
theorem measurePreservation {Ω β : Type*} [DecidableEq Ω]
    {ctx : ActualFailureContext} {i : Fin 7}
    (I : V30CycleO2SafeConeInputs (Ω := Ω) (β := β) ctx i) :
    V30MeasurePreservation ctx i I.D.E.card I.D.c I.Mtot :=
  v30_measurePreservation_of_cycleDatum ctx i I.D I.hexit I.hM

/-- The packaged Cycle/O2 input exposes the named RISK-b ambient-accounting
residual supplied by the single-cell O2 carrier injection. -/
theorem ambientAccounting {Ω β : Type*} [DecidableEq Ω]
    {ctx : ActualFailureContext} {i : Fin 7}
    (I : V30CycleO2SafeConeInputs (Ω := Ω) (β := β) ctx i) :
    V30AmbientAccounting ctx I.Mtot :=
  v30AmbientAccounting_of_o2_unit_carrier ctx I.cell I.carrier I.rect I.πst
    I.hsub I.hcell I.hmaps I.hinj I.hrect

/-- The packaged Cycle/O2 input supplies the full safe-cone datum. -/
theorem safeConeDatum {Ω β : Type*} [DecidableEq Ω]
    {ctx : ActualFailureContext} {i : Fin 7}
    (I : V30CycleO2SafeConeInputs (Ω := Ω) (β := β) ctx i) :
    V30OffPinSafeConeDatum ctx i I.D.E.card I.D.c I.Mtot :=
  v30_safeConeDatum_of_measure_ambient ctx i I.D.hc I.hspace
    (measurePreservation I) I.hsafe (ambientAccounting I)

/-- The packaged Cycle/O2 input gives the per-class off-pin C1 cap. -/
theorem classCap {Ω β : Type*} [DecidableEq Ω]
    {ctx : ActualFailureContext} {i : Fin 7}
    (I : V30CycleO2SafeConeInputs (Ω := Ω) (β := β) ctx i)
    (hband : fixedFamilyRecurrentBand ctx <= 4) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) i <= emcCap ctx :=
  v30_offPin_classCap_of_cycleDatum_o2_unit_carrier ctx i hband I.D I.hexit
    I.hM I.hspace I.hsafe I.cell I.carrier I.rect I.πst I.hsub I.hcell
    I.hmaps I.hinj I.hrect

/-- In the exit-light singleton case, the packaged input supplies the worst-case
safe-cone datum with share numerator `1`; the safe-cell inequality comes from
Lane D rather than the generic `hsafe` field. -/
theorem exitLightSafeConeDatum {Ω β : Type*} [DecidableEq Ω]
    {ctx : ActualFailureContext} {i : Fin 7}
    (I : V30CycleO2SafeConeInputs (Ω := Ω) (β := β) ctx i)
    (hcard : I.D.E.card = 1)
    (hsurv : boundedThreshold (shellLadderDepth ctx) < I.D.c) (hc64 : 64 <= I.D.c) :
    V30OffPinSafeConeDatum ctx i 1 I.D.c I.Mtot :=
  v30_exitLight_safeConeDatum_of_cycleDatum_o2_unit_carrier ctx i I.D I.hexit hcard
    I.hM hsurv hc64 I.hspace I.cell I.carrier I.rect I.πst I.hsub I.hcell
    I.hmaps I.hinj I.hrect

/-- Exit-light per-class C1 cap from the packaged Cycle/O2 input. -/
theorem exitLightClassCap {Ω β : Type*} [DecidableEq Ω]
    {ctx : ActualFailureContext} {i : Fin 7}
    (I : V30CycleO2SafeConeInputs (Ω := Ω) (β := β) ctx i)
    (hband : fixedFamilyRecurrentBand ctx <= 4) (hcard : I.D.E.card = 1)
    (hsurv : boundedThreshold (shellLadderDepth ctx) < I.D.c) (hc64 : 64 <= I.D.c) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) i <= emcCap ctx :=
  v30_offPin_classCap_exitLight_of_cycleDatum_o2_unit_carrier ctx i hband I.D
    I.hexit hcard I.hM hsurv hc64 I.hspace I.cell I.carrier I.rect I.πst I.hsub
    I.hcell I.hmaps I.hinj I.hrect

end V30CycleO2SafeConeInputs

/-- Exit-light `b = 1` cells can consume a Lane-B cycle mass datum directly:
the singleton exit-phase condition rewrites the datum's share numerator into the
worst-case Lane-D safe-cell form. -/
theorem v30_exitLight_safeConeDatum_of_cycleDatum_ambient
    (ctx : ActualFailureContext) (i : Fin 7) (D : CycleMassDatum)
    (hexit : D.exitMass = emcFibreExitMass ctx i) (hcard : D.E.card = 1)
    {Mtot : Nat} (hM : D.totalMass <= Mtot)
    (hsurv : boundedThreshold (shellLadderDepth ctx) < D.c) (hc64 : 64 <= D.c)
    (hspace : forall x, x ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
      forall z, z ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
        x <= z -> D.c ∣ z - x)
    (hambient : V30AmbientAccounting ctx Mtot) :
    V30OffPinSafeConeDatum ctx i 1 D.c Mtot := by
  have hmeasure : V30MeasurePreservation ctx i 1 D.c Mtot := by
    rw [← hcard]
    exact v30_measurePreservation_of_cycleDatum ctx i D hexit hM
  exact v30_safeConeDatum_of_measure_ambient ctx i D.hc hspace hmeasure
    (v30_ctx_exitLight_safe ctx hsurv rfl hc64) hambient

/-- Exit-light per-class cap stated directly from a singleton-exit
`CycleMassDatum`, the ambient accounting residual, and the AB spacing input. -/
theorem v30_offPin_classCap_exitLight_of_cycleDatum_ambient
    (ctx : ActualFailureContext) (i : Fin 7)
    (hband : fixedFamilyRecurrentBand ctx <= 4) (D : CycleMassDatum)
    (hexit : D.exitMass = emcFibreExitMass ctx i) (hcard : D.E.card = 1)
    {Mtot : Nat} (hM : D.totalMass <= Mtot)
    (hsurv : boundedThreshold (shellLadderDepth ctx) < D.c) (hc64 : 64 <= D.c)
    (hspace : forall x, x ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
      forall z, z ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
        x <= z -> D.c ∣ z - x)
    (hambient : V30AmbientAccounting ctx Mtot) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) i <= emcCap ctx :=
  v30_offPin_classCap_of_datum ctx i hband
    (v30_exitLight_safeConeDatum_of_cycleDatum_ambient ctx i D hexit hcard hM
      hsurv hc64 hspace hambient)

/-- Exit-light long cycles get the safe-cone inequality from Lane D, so the two
named residuals plus the AB spacing input already form the full C1 datum. -/
theorem v30_exitLight_safeConeDatum_of_measure_ambient
    (ctx : ActualFailureContext) (i : Fin 7) {c Mtot : Nat}
    (hsurv : boundedThreshold (shellLadderDepth ctx) < c) (hc64 : 64 <= c)
    (hspace : forall x, x ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
      forall z, z ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
        x <= z -> c ∣ z - x)
    (hmeasure : V30MeasurePreservation ctx i 1 c Mtot)
    (hambient : V30AmbientAccounting ctx Mtot) :
    V30OffPinSafeConeDatum ctx i 1 c Mtot :=
  v30_safeConeDatum_of_measure_ambient ctx i (by omega) hspace hmeasure
    (v30_ctx_exitLight_safe ctx hsurv rfl hc64) hambient

/-- Exit-light capstone stated directly in terms of the two named residuals.
The safe-cone cell inequality is supplied by the AC/Lane-D emptiness theorem. -/
theorem v30_offPin_classCap_exitLight_of_measure_ambient
    (ctx : ActualFailureContext) (i : Fin 7)
    (hband : fixedFamilyRecurrentBand ctx <= 4) {c Mtot : Nat}
    (hsurv : boundedThreshold (shellLadderDepth ctx) < c) (hc64 : 64 <= c)
    (hspace : forall x, x ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
      forall z, z ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
        x <= z -> c ∣ z - x)
    (hmeasure : V30MeasurePreservation ctx i 1 c Mtot)
    (hambient : V30AmbientAccounting ctx Mtot) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) i <= emcCap ctx :=
  v30_offPin_classCap_of_datum ctx i hband
    (v30_exitLight_safeConeDatum_of_measure_ambient ctx i hsurv hc64 hspace hmeasure hambient)

/-- Packaged constructed-O2 supply surface for one off-pin recurrent class.
Lane B supplies the cycle mass datum (RISK c), the AB safe-cone geometry remains
explicit, and `O2SupplyEmbedding.O2SupplyInputs` supplies RISK b through the
constructed start/threshold rectangle rather than an abstract carrier. -/
structure V30CycleO2SupplySafeConeInputs {β A : Type*} (P₀ Q : Int)
    (ctx : ActualFailureContext) (i : Fin 7) where
  D : CycleMassDatum
  Mtot : Nat
  hexit : D.exitMass = emcFibreExitMass ctx i
  hM : D.totalMass <= Mtot
  hspace : forall x, x ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
    forall z, z ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
      x <= z -> D.c ∣ z - x
  hsafe : 1536 * (cmbOverlap ctx D.c * D.E.card) <= 31 * D.c
  S : Finset A
  Omega : A -> Finset (Nat -> Int)
  Lambda : (Nat -> Int) -> A
  masses : A -> Nat
  carrier : Finset (Nat -> Int)
  Ij : Finset β
  piSt : (Nat -> Int) -> Nat × β
  keyOf : Nat × β -> Int × (Nat -> Int)
  hMtot : Mtot <= Finset.sum S masses
  hIj : Ij.card = 1
  supply : O2SupplyEmbedding.O2SupplyInputs P₀ Q S Omega Lambda masses carrier Ij
    ctx.shell.X piSt keyOf

namespace V30CycleO2SupplySafeConeInputs

/-- The constructed O2 supply surface also exposes the named RISK-c
measure-preservation residual supplied by its Lane-B cycle mass datum. -/
theorem measurePreservation {β A : Type*} {P₀ Q : Int}
    {ctx : ActualFailureContext} {i : Fin 7}
    (I : V30CycleO2SupplySafeConeInputs (β := β) (A := A) P₀ Q ctx i) :
    V30MeasurePreservation ctx i I.D.E.card I.D.c I.Mtot :=
  v30_measurePreservation_of_cycleDatum ctx i I.D I.hexit I.hM

/-- The constructed O2 supply surface supplies the scalar ambient accounting
input consumed by the V30 safe-cone cap. -/
theorem ambientAccounting {β A : Type*} {P₀ Q : Int}
    {ctx : ActualFailureContext} {i : Fin 7}
    (I : V30CycleO2SupplySafeConeInputs (β := β) (A := A) P₀ Q ctx i) :
    V30AmbientAccounting ctx I.Mtot :=
  v30AmbientAccounting_of_o2_supply_unit_inputs P₀ Q ctx I.S I.Omega I.Lambda
    I.masses I.carrier I.Ij I.piSt I.keyOf I.hMtot I.hIj I.supply

/-- The packaged constructed-O2 input supplies the full safe-cone datum. -/
theorem safeConeDatum {β A : Type*} {P₀ Q : Int}
    {ctx : ActualFailureContext} {i : Fin 7}
    (I : V30CycleO2SupplySafeConeInputs (β := β) (A := A) P₀ Q ctx i) :
    V30OffPinSafeConeDatum ctx i I.D.E.card I.D.c I.Mtot :=
  v30_safeConeDatum_of_measure_ambient ctx i I.D.hc I.hspace
    (measurePreservation I) I.hsafe (ambientAccounting I)

/-- The packaged constructed-O2 input gives the per-class off-pin C1 cap. -/
theorem classCap {β A : Type*} {P₀ Q : Int}
    {ctx : ActualFailureContext} {i : Fin 7}
    (I : V30CycleO2SupplySafeConeInputs (β := β) (A := A) P₀ Q ctx i)
    (hband : fixedFamilyRecurrentBand ctx <= 4) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) i <= emcCap ctx :=
  v30_offPin_classCap_of_cycleDatum_ambient ctx i hband I.D I.hexit I.hM
    I.hspace I.hsafe (ambientAccounting I)

/-- Exit-light singleton case from the packaged constructed-O2 input. -/
theorem exitLightSafeConeDatum {β A : Type*} {P₀ Q : Int}
    {ctx : ActualFailureContext} {i : Fin 7}
    (I : V30CycleO2SupplySafeConeInputs (β := β) (A := A) P₀ Q ctx i)
    (hcard : I.D.E.card = 1)
    (hsurv : boundedThreshold (shellLadderDepth ctx) < I.D.c) (hc64 : 64 <= I.D.c) :
    V30OffPinSafeConeDatum ctx i 1 I.D.c I.Mtot :=
  v30_exitLight_safeConeDatum_of_cycleDatum_ambient ctx i I.D I.hexit hcard I.hM
    hsurv hc64 I.hspace (ambientAccounting I)

/-- Exit-light per-class cap from the packaged constructed-O2 input. -/
theorem exitLightClassCap {β A : Type*} {P₀ Q : Int}
    {ctx : ActualFailureContext} {i : Fin 7}
    (I : V30CycleO2SupplySafeConeInputs (β := β) (A := A) P₀ Q ctx i)
    (hband : fixedFamilyRecurrentBand ctx <= 4) (hcard : I.D.E.card = 1)
    (hsurv : boundedThreshold (shellLadderDepth ctx) < I.D.c) (hc64 : 64 <= I.D.c) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) i <= emcCap ctx :=
  v30_offPin_classCap_exitLight_of_cycleDatum_ambient ctx i hband I.D I.hexit
    hcard I.hM hsurv hc64 I.hspace (ambientAccounting I)

end V30CycleO2SupplySafeConeInputs

/-- Packaged constructed-O2 collar supply surface for one off-pin recurrent
class in the special no-remainder case.  The `collarZero` field is the explicit
finite assertion that allows the collar accounting surface to recover the
no-error `V30AmbientAccounting` input consumed by C1. -/
structure V30CycleO2CollarSupplySafeConeInputs {β A : Type*}
    [DecidableEq (Nat -> Int)] (P₀ Q : Int)
    (ctx : ActualFailureContext) (i : Fin 7) where
  D : CycleMassDatum
  Mtot : Nat
  hexit : D.exitMass = emcFibreExitMass ctx i
  hM : D.totalMass <= Mtot
  hspace : forall x, x ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
    forall z, z ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
      x <= z -> D.c ∣ z - x
  hsafe : 1536 * (cmbOverlap ctx D.c * D.E.card) <= 31 * D.c
  S : Finset A
  Omega : A -> Finset (Nat -> Int)
  Lambda : (Nat -> Int) -> A
  masses : A -> Nat
  carrier : Finset (Nat -> Int)
  post : Finset (Nat -> Int)
  collar : Finset (Nat -> Int)
  Ij : Finset β
  piSt : (Nat -> Int) -> Nat × β
  keyOf : Nat × β -> Int × (Nat -> Int)
  hMtot : Mtot <= Finset.sum S masses
  hIj : Ij.card = 1
  collarZero : collar.card = 0
  supply : O2SupplyEmbedding.O2CollarSupplyInputs P₀ Q S Omega Lambda masses carrier
    post collar Ij ctx.shell.X piSt keyOf

namespace V30CycleO2CollarSupplySafeConeInputs

/-- The zero-collar constructed O2 collar surface exposes the named RISK-c
measure-preservation residual supplied by its Lane-B cycle mass datum. -/
theorem measurePreservation {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    {ctx : ActualFailureContext} {i : Fin 7}
    (I : V30CycleO2CollarSupplySafeConeInputs (β := β) (A := A) P₀ Q ctx i) :
    V30MeasurePreservation ctx i I.D.E.card I.D.c I.Mtot :=
  v30_measurePreservation_of_cycleDatum ctx i I.D I.hexit I.hM

/-- A zero-collar constructed O2 collar surface supplies the scalar ambient
accounting input consumed by the V30 safe-cone cap. -/
theorem ambientAccounting {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    {ctx : ActualFailureContext} {i : Fin 7}
    (I : V30CycleO2CollarSupplySafeConeInputs (β := β) (A := A) P₀ Q ctx i) :
    V30AmbientAccounting ctx I.Mtot :=
  v30AmbientAccounting_of_o2_collar_supply_unit_inputs_zero_collar P₀ Q ctx
    I.S I.Omega I.Lambda I.masses I.carrier I.post I.collar I.Ij I.piSt I.keyOf
    I.hMtot I.hIj I.supply I.collarZero

/-- The packaged zero-collar constructed-O2 input supplies the full safe-cone
datum. -/
theorem safeConeDatum {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    {ctx : ActualFailureContext} {i : Fin 7}
    (I : V30CycleO2CollarSupplySafeConeInputs (β := β) (A := A) P₀ Q ctx i) :
    V30OffPinSafeConeDatum ctx i I.D.E.card I.D.c I.Mtot :=
  v30_safeConeDatum_of_measure_ambient ctx i I.D.hc I.hspace
    (measurePreservation I) I.hsafe (ambientAccounting I)

/-- The packaged zero-collar constructed-O2 input gives the per-class off-pin
C1 cap. -/
theorem classCap {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    {ctx : ActualFailureContext} {i : Fin 7}
    (I : V30CycleO2CollarSupplySafeConeInputs (β := β) (A := A) P₀ Q ctx i)
    (hband : fixedFamilyRecurrentBand ctx <= 4) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) i <= emcCap ctx :=
  v30_offPin_classCap_of_cycleDatum_ambient ctx i hband I.D I.hexit I.hM
    I.hspace I.hsafe (ambientAccounting I)

/-- Exit-light singleton case from the packaged zero-collar constructed-O2
input. -/
theorem exitLightSafeConeDatum {β A : Type*} [DecidableEq (Nat -> Int)]
    {P₀ Q : Int} {ctx : ActualFailureContext} {i : Fin 7}
    (I : V30CycleO2CollarSupplySafeConeInputs (β := β) (A := A) P₀ Q ctx i)
    (hcard : I.D.E.card = 1)
    (hsurv : boundedThreshold (shellLadderDepth ctx) < I.D.c) (hc64 : 64 <= I.D.c) :
    V30OffPinSafeConeDatum ctx i 1 I.D.c I.Mtot :=
  v30_exitLight_safeConeDatum_of_cycleDatum_ambient ctx i I.D I.hexit hcard I.hM
    hsurv hc64 I.hspace (ambientAccounting I)

/-- Exit-light per-class C1 cap from the packaged zero-collar constructed-O2
input. -/
theorem exitLightClassCap {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    {ctx : ActualFailureContext} {i : Fin 7}
    (I : V30CycleO2CollarSupplySafeConeInputs (β := β) (A := A) P₀ Q ctx i)
    (hband : fixedFamilyRecurrentBand ctx <= 4) (hcard : I.D.E.card = 1)
    (hsurv : boundedThreshold (shellLadderDepth ctx) < I.D.c) (hc64 : 64 <= I.D.c) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) i <= emcCap ctx :=
  v30_offPin_classCap_exitLight_of_cycleDatum_ambient ctx i hband I.D I.hexit
    hcard I.hM hsurv hc64 I.hspace (ambientAccounting I)

end V30CycleO2CollarSupplySafeConeInputs

/-- Coordinate-split version of the zero-collar constructed-O2 collar supply
surface for one off-pin recurrent class. -/
structure V30CycleO2CollarSupplyCoordinateSafeConeInputs {β A : Type*}
    [DecidableEq (Nat -> Int)] (P₀ Q : Int)
    (ctx : ActualFailureContext) (i : Fin 7) where
  D : CycleMassDatum
  Mtot : Nat
  hexit : D.exitMass = emcFibreExitMass ctx i
  hM : D.totalMass <= Mtot
  hspace : forall x, x ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
    forall z, z ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
      x <= z -> D.c ∣ z - x
  hsafe : 1536 * (cmbOverlap ctx D.c * D.E.card) <= 31 * D.c
  S : Finset A
  Omega : A -> Finset (Nat -> Int)
  Lambda : (Nat -> Int) -> A
  masses : A -> Nat
  carrier : Finset (Nat -> Int)
  post : Finset (Nat -> Int)
  collar : Finset (Nat -> Int)
  Ij : Finset β
  piSt : (Nat -> Int) -> Nat × β
  keyOf : Nat × β -> Int × (Nat -> Int)
  hMtot : Mtot <= Finset.sum S masses
  hIj : Ij.card = 1
  collarZero : collar.card = 0
  supply : O2SupplyEmbedding.O2CollarSupplyCoordinateInputs P₀ Q S Omega Lambda
    masses carrier post collar Ij ctx.shell.X piSt keyOf

namespace V30CycleO2CollarSupplyCoordinateSafeConeInputs

/-- The coordinate-split zero-collar input exposes the named RISK-c
measure-preservation residual supplied by its Lane-B cycle mass datum. -/
theorem measurePreservation {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    {ctx : ActualFailureContext} {i : Fin 7}
    (I : V30CycleO2CollarSupplyCoordinateSafeConeInputs
      (β := β) (A := A) P₀ Q ctx i) :
    V30MeasurePreservation ctx i I.D.E.card I.D.c I.Mtot :=
  v30_measurePreservation_of_cycleDatum ctx i I.D I.hexit I.hM

/-- The coordinate-split zero-collar O2 collar surface supplies the scalar
ambient accounting input consumed by the V30 safe-cone cap. -/
theorem ambientAccounting {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    {ctx : ActualFailureContext} {i : Fin 7}
    (I : V30CycleO2CollarSupplyCoordinateSafeConeInputs
      (β := β) (A := A) P₀ Q ctx i) :
    V30AmbientAccounting ctx I.Mtot :=
  v30AmbientAccounting_of_o2_collar_supply_coordinate_unit_inputs_zero_collar
    P₀ Q ctx I.S I.Omega I.Lambda I.masses I.carrier I.post I.collar I.Ij
    I.piSt I.keyOf I.hMtot I.hIj I.supply I.collarZero

/-- The packaged coordinate-split zero-collar input supplies the full safe-cone
datum. -/
theorem safeConeDatum {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    {ctx : ActualFailureContext} {i : Fin 7}
    (I : V30CycleO2CollarSupplyCoordinateSafeConeInputs
      (β := β) (A := A) P₀ Q ctx i) :
    V30OffPinSafeConeDatum ctx i I.D.E.card I.D.c I.Mtot :=
  v30_safeConeDatum_of_measure_ambient ctx i I.D.hc I.hspace
    (measurePreservation I) I.hsafe (ambientAccounting I)

/-- The packaged coordinate-split zero-collar input gives the per-class off-pin
C1 cap. -/
theorem classCap {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    {ctx : ActualFailureContext} {i : Fin 7}
    (I : V30CycleO2CollarSupplyCoordinateSafeConeInputs
      (β := β) (A := A) P₀ Q ctx i)
    (hband : fixedFamilyRecurrentBand ctx <= 4) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) i <= emcCap ctx :=
  v30_offPin_classCap_of_cycleDatum_ambient ctx i hband I.D I.hexit I.hM
    I.hspace I.hsafe (ambientAccounting I)

/-- Exit-light singleton case from the coordinate-split zero-collar input. -/
theorem exitLightSafeConeDatum {β A : Type*} [DecidableEq (Nat -> Int)]
    {P₀ Q : Int} {ctx : ActualFailureContext} {i : Fin 7}
    (I : V30CycleO2CollarSupplyCoordinateSafeConeInputs
      (β := β) (A := A) P₀ Q ctx i)
    (hcard : I.D.E.card = 1)
    (hsurv : boundedThreshold (shellLadderDepth ctx) < I.D.c) (hc64 : 64 <= I.D.c) :
    V30OffPinSafeConeDatum ctx i 1 I.D.c I.Mtot :=
  v30_exitLight_safeConeDatum_of_cycleDatum_ambient ctx i I.D I.hexit hcard I.hM
    hsurv hc64 I.hspace (ambientAccounting I)

/-- Exit-light per-class C1 cap from the coordinate-split zero-collar input. -/
theorem exitLightClassCap {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    {ctx : ActualFailureContext} {i : Fin 7}
    (I : V30CycleO2CollarSupplyCoordinateSafeConeInputs
      (β := β) (A := A) P₀ Q ctx i)
    (hband : fixedFamilyRecurrentBand ctx <= 4) (hcard : I.D.E.card = 1)
    (hsurv : boundedThreshold (shellLadderDepth ctx) < I.D.c) (hc64 : 64 <= I.D.c) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) i <= emcCap ctx :=
  v30_offPin_classCap_exitLight_of_cycleDatum_ambient ctx i hband I.D I.hexit
    hcard I.hM hsurv hc64 I.hspace (ambientAccounting I)

end V30CycleO2CollarSupplyCoordinateSafeConeInputs

/-- Coordinate-split O2 collar supply surface for one off-pin recurrent class,
retaining the finite collar as an explicit error term.  This is the nonzero-collar
counterpart of `V30CycleO2CollarSupplyCoordinateSafeConeInputs`: it deliberately
does not contain `collarZero`, so its cap conclusion is
`V30OffPinClassCapWithError` rather than the no-error endpoint cap. -/
structure V30CycleO2CollarSupplyCoordinateSafeConeInputsWithError {β A : Type*}
    [DecidableEq (Nat -> Int)] (P₀ Q : Int)
    (ctx : ActualFailureContext) (i : Fin 7) where
  D : CycleMassDatum
  Mtot : Nat
  hexit : D.exitMass = emcFibreExitMass ctx i
  hM : D.totalMass <= Mtot
  hspace : forall x, x ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
    forall z, z ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i ->
      x <= z -> D.c ∣ z - x
  hsafe : 1536 * (cmbOverlap ctx D.c * D.E.card) <= 31 * D.c
  S : Finset A
  Omega : A -> Finset (Nat -> Int)
  Lambda : (Nat -> Int) -> A
  masses : A -> Nat
  carrier : Finset (Nat -> Int)
  post : Finset (Nat -> Int)
  collar : Finset (Nat -> Int)
  Ij : Finset β
  piSt : (Nat -> Int) -> Nat × β
  keyOf : Nat × β -> Int × (Nat -> Int)
  hMtot : Mtot <= Finset.sum S masses
  hIj : Ij.card = 1
  supply : O2SupplyEmbedding.O2CollarSupplyCoordinateInputs P₀ Q S Omega Lambda
    masses carrier post collar Ij ctx.shell.X piSt keyOf

namespace V30CycleO2CollarSupplyCoordinateSafeConeInputsWithError

/-- The finite-error coordinate collar input exposes the named RISK-c
measure-preservation residual supplied by its Lane-B cycle mass datum. -/
theorem measurePreservation {β A : Type*} [DecidableEq (Nat -> Int)]
    {P₀ Q : Int} {ctx : ActualFailureContext} {i : Fin 7}
    (I : V30CycleO2CollarSupplyCoordinateSafeConeInputsWithError
      (β := β) (A := A) P₀ Q ctx i) :
    V30MeasurePreservation ctx i I.D.E.card I.D.c I.Mtot :=
  v30_measurePreservation_of_cycleDatum ctx i I.D I.hexit I.hM

/-- The packaged coordinate-split collar input supplies finite-error ambient
accounting with error exactly `collar.card`. -/
theorem ambientAccountingWithError {β A : Type*} [DecidableEq (Nat -> Int)]
    {P₀ Q : Int} {ctx : ActualFailureContext} {i : Fin 7}
    (I : V30CycleO2CollarSupplyCoordinateSafeConeInputsWithError
      (β := β) (A := A) P₀ Q ctx i) :
    V30AmbientAccountingWithError ctx I.collar.card I.Mtot :=
  v30AmbientAccountingWithError_of_o2_collar_supply_coordinate_unit_inputs
    P₀ Q ctx I.S I.Omega I.Lambda I.masses I.carrier I.post I.collar I.Ij
    I.piSt I.keyOf I.hMtot I.hIj I.supply

/-- The packaged nonzero-collar input supplies the finite-error safe-cone datum. -/
theorem safeConeDatumWithError {β A : Type*} [DecidableEq (Nat -> Int)]
    {P₀ Q : Int} {ctx : ActualFailureContext} {i : Fin 7}
    (I : V30CycleO2CollarSupplyCoordinateSafeConeInputsWithError
      (β := β) (A := A) P₀ Q ctx i) :
    V30OffPinSafeConeDatumWithError ctx i I.D.E.card I.D.c I.collar.card I.Mtot :=
  v30_safeConeDatumWithError_of_measure_ambient ctx i I.D.hc I.hspace
    (measurePreservation I) I.hsafe (ambientAccountingWithError I)

/-- The packaged nonzero-collar input gives the per-class off-pin cap with the
explicit additive collar error. -/
theorem classCapWithError {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    {ctx : ActualFailureContext} {i : Fin 7}
    (I : V30CycleO2CollarSupplyCoordinateSafeConeInputsWithError
      (β := β) (A := A) P₀ Q ctx i)
    (hband : fixedFamilyRecurrentBand ctx <= 4) :
    V30OffPinClassCapWithError ctx i I.collar.card :=
  v30_offPin_classCap_withError_of_datum ctx i hband
    (safeConeDatumWithError I)

/-- A finite-error coordinate collar input with a genuine zero collar is exactly
the existing coordinate zero-collar input surface. -/
def toZeroCollar {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    {ctx : ActualFailureContext} {i : Fin 7}
    (I : V30CycleO2CollarSupplyCoordinateSafeConeInputsWithError
      (β := β) (A := A) P₀ Q ctx i)
    (hcollar : I.collar.card = 0) :
    V30CycleO2CollarSupplyCoordinateSafeConeInputs
      (β := β) (A := A) P₀ Q ctx i where
  D := I.D
  Mtot := I.Mtot
  hexit := I.hexit
  hM := I.hM
  hspace := I.hspace
  hsafe := I.hsafe
  S := I.S
  Omega := I.Omega
  Lambda := I.Lambda
  masses := I.masses
  carrier := I.carrier
  post := I.post
  collar := I.collar
  Ij := I.Ij
  piSt := I.piSt
  keyOf := I.keyOf
  hMtot := I.hMtot
  hIj := I.hIj
  collarZero := hcollar
  supply := I.supply

end V30CycleO2CollarSupplyCoordinateSafeConeInputsWithError

/-- **THE v30 OFF-PIN SAFE-CONE REGIME** (classes `{3,4,5}`): at every deep pin-free
context the recurrent band is `≤ 4` and each off-pin recurrent class `3,4,5` admits a
safe-cone cell datum.  This is the v30 analogue of `EmcOffPinSpacedShareRegime`, but
built on the PROVABLE mass-normalized balance (RISK c) + ambient bound (RISK b), NOT
the false proportional total-exit share. -/
def V30OffPinSafeConeRegime : Prop :=
  ∀ ctx : ActualFailureContext, 2 ^ 986891 < ctx.X →
    ¬ OrbitBandPinned ctx 2 → ¬ OrbitBandPinned ctx 3 → ¬ OrbitBandPinned ctx 4 →
    fixedFamilyRecurrentBand ctx ≤ 4
      ∧ (∃ b c Mtot : ℕ, V30OffPinSafeConeDatum ctx 3 b c Mtot)
      ∧ (∃ b c Mtot : ℕ, V30OffPinSafeConeDatum ctx 4 b c Mtot)
      ∧ (∃ b c Mtot : ℕ, V30OffPinSafeConeDatum ctx 5 b c Mtot)

/-- **THE OFF-PIN EXIT CAP (C1), classes `{3,4,5}`**: the v30 safe-cone regime supplies
the wave-19 supplier target `ExitMassControlOffPin` — the corrected per-class caps on
pin-free deep contexts — assembled DIRECTLY through `cmb_offPin_safeCone_cap` (the
mass-normalized balance), never through the false `EmcSpacedShareDatum`. -/
theorem v30_offPinExitCap (H : V30OffPinSafeConeRegime) : ExitMassControlOffPin := by
  intro ctx hX h2 h3 h4
  obtain ⟨hband, ⟨b3, c3, M3, hd3⟩, ⟨b4, c4, M4, hd4⟩, ⟨b5, c5, M5, hd5⟩⟩ := H ctx hX h2 h3 h4
  exact ⟨v30_offPin_classCap_of_datum ctx 3 hband hd3,
    v30_offPin_classCap_of_datum ctx 4 hband hd4,
    v30_offPin_classCap_of_datum ctx 5 hband hd5⟩

/-! ## Part 4.  The class-0 leg — `MdcClass0ExitMassControl` off the same safe cone -/

/-- The v30 safe-cone regime for the class-0 survivor leg (`MissDistanceClosure`
shape): at every class-0 datum survivor, a share numerator `b` and ambient phase mass
`M_tot ≤ X` with the class-0 mass-normalized balance and the survivor-period safe-cone
cell inequality. -/
def V30Class0SafeConeRegime : Prop :=
  ∀ ctx : ActualFailureContext, Class0DatumSurvivor ctx →
    ∃ b Mtot : ℕ,
      class0SurvivorPeriod (class1SlopeDatum ctx).q * mdcClass0ExitMass ctx ≤ b * Mtot
      ∧ 1536 * (((ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
            / class0SurvivorPeriod (class1SlopeDatum ctx).q) * b)
          ≤ 31 * class0SurvivorPeriod (class1SlopeDatum ctx).q
      ∧ Mtot ≤ ctx.shell.X

/-- Packaged class-0 single-cell supply surface: the class-0 mass-normalized
balance and safe-cell inequality, plus the O2 ambient carrier injection that
supplies `M_tot <= X`.  This is the class-0 analogue of
`V30CycleO2SafeConeInputs` for the off-pin classes `{3,4,5}`. -/
structure V30Class0O2SafeConeInputs {Ω β : Type*} [DecidableEq Ω]
    (ctx : ActualFailureContext) where
  b : Nat
  Mtot : Nat
  hbalance :
    class0SurvivorPeriod (class1SlopeDatum ctx).q * mdcClass0ExitMass ctx <= b * Mtot
  hsafe :
    1536 * (((ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
          / class0SurvivorPeriod (class1SlopeDatum ctx).q) * b)
      <= 31 * class0SurvivorPeriod (class1SlopeDatum ctx).q
  cell : Finset Ω
  carrier : Finset Ω
  rect : Finset β
  πst : Ω -> β
  hsub : cell ⊆ carrier
  hcell : Mtot <= cell.card
  hmaps : forall ω, ω ∈ carrier -> πst ω ∈ rect
  hinj : Set.InjOn πst carrier
  hrect : rect.card <= ctx.shell.X

namespace V30Class0O2SafeConeInputs

/-- The packaged class-0 O2 carrier data supplies the ambient accounting field. -/
theorem ambientAccounting {Ω β : Type*} [DecidableEq Ω] {ctx : ActualFailureContext}
    (I : V30Class0O2SafeConeInputs (Ω := Ω) (β := β) ctx) :
    V30AmbientAccounting ctx I.Mtot :=
  v30AmbientAccounting_of_o2_unit_carrier ctx I.cell I.carrier I.rect I.πst
    I.hsub I.hcell I.hmaps I.hinj I.hrect

/-- The packaged class-0 input is exactly one witness for
`V30Class0SafeConeRegime` at the current context. -/
theorem safeConeWitness {Ω β : Type*} [DecidableEq Ω] {ctx : ActualFailureContext}
    (I : V30Class0O2SafeConeInputs (Ω := Ω) (β := β) ctx) :
    ∃ b Mtot : Nat,
      class0SurvivorPeriod (class1SlopeDatum ctx).q * mdcClass0ExitMass ctx <= b * Mtot
      ∧ 1536 * (((ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
            / class0SurvivorPeriod (class1SlopeDatum ctx).q) * b)
          <= 31 * class0SurvivorPeriod (class1SlopeDatum ctx).q
      ∧ Mtot <= ctx.shell.X := by
  refine ⟨I.b, I.Mtot, I.hbalance, I.hsafe, ?_⟩
  exact ambientAccounting I

end V30Class0O2SafeConeInputs

/-- A context-wise provider of packaged class-0 O2 safe-cone inputs supplies the
class-0 safe-cone regime consumed by the C1 class-0 leg. -/
theorem v30Class0SafeConeRegime_of_o2_unit_provider
    {Ω β : Type*} [DecidableEq Ω]
    (H : forall ctx : ActualFailureContext, Class0DatumSurvivor ctx ->
      V30Class0O2SafeConeInputs (Ω := Ω) (β := β) ctx) :
    V30Class0SafeConeRegime := by
  intro ctx hsurv
  exact V30Class0O2SafeConeInputs.safeConeWitness (H ctx hsurv)

/-- **THE CLASS-0 LEG (C1)**: the class-0 safe-cone regime supplies the named class-0
atom `MdcClass0ExitMassControl` (`MissDistanceClosure`) — the survivor-telescoped
class-0 share clears `1536·⌈(r+1)/c⌉·mdcClass0ExitMass ≤ 31·X` — via the same Lane B
arithmetic core `cmb_safeCone_nat`. -/
theorem v30_mdcClass0ExitMassControl_of_safeCone (H : V30Class0SafeConeRegime) :
    MdcClass0ExitMassControl := by
  intro ctx hsurv
  obtain ⟨b, Mtot, hbal, hsafe, hamb⟩ := H ctx hsurv
  exact cmb_safeCone_nat
    ((ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
        / class0SurvivorPeriod (class1SlopeDatum ctx).q)
    (mdcClass0ExitMass ctx) b
    (class0SurvivorPeriod (class1SlopeDatum ctx).q) Mtot ctx.shell.X
    (tfaClass0SurvivorPeriod_pos _) hbal hsafe hamb

/-- Class-0 C1 control with an explicit context-wise finite ambient error.  This
keeps the collar remainder visible instead of pretending that it is part of the
no-remainder `MdcClass0ExitMassControl` input. -/
def MdcClass0ExitMassControlWithError
    (errOf : ActualFailureContext -> Nat) : Prop :=
  forall ctx : ActualFailureContext, Class0DatumSurvivor ctx ->
    1536 * (((ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
          / class0SurvivorPeriod (class1SlopeDatum ctx).q)
        * mdcClass0ExitMass ctx)
      <= 31 * (ctx.shell.X + errOf ctx)

/-- Finite-error class-0 safe-cone regime: same balance and safe-cell data as
`V30Class0SafeConeRegime`, but the ambient accounting conclusion is
`M_tot <= X + err`. -/
def V30Class0SafeConeRegimeWithError
    (errOf : ActualFailureContext -> Nat) : Prop :=
  forall ctx : ActualFailureContext, Class0DatumSurvivor ctx ->
    exists b Mtot : Nat,
      class0SurvivorPeriod (class1SlopeDatum ctx).q * mdcClass0ExitMass ctx <= b * Mtot
      ∧ 1536 * (((ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
            / class0SurvivorPeriod (class1SlopeDatum ctx).q) * b)
          <= 31 * class0SurvivorPeriod (class1SlopeDatum ctx).q
      ∧ V30AmbientAccountingWithError ctx (errOf ctx) Mtot

/-- The class-0 finite-error safe cone gives the corresponding finite-error C1
control by the same `cmb_safeCone_nat` arithmetic used in the no-error theorem. -/
theorem v30_mdcClass0ExitMassControl_withError_of_safeCone
    {errOf : ActualFailureContext -> Nat}
    (H : V30Class0SafeConeRegimeWithError errOf) :
    MdcClass0ExitMassControlWithError errOf := by
  intro ctx hsurv
  obtain ⟨b, Mtot, hbal, hsafe, hamb⟩ := H ctx hsurv
  exact cmb_safeCone_nat
    ((ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
        / class0SurvivorPeriod (class1SlopeDatum ctx).q)
    (mdcClass0ExitMass ctx) b
    (class0SurvivorPeriod (class1SlopeDatum ctx).q) Mtot (ctx.shell.X + errOf ctx)
    (tfaClass0SurvivorPeriod_pos _) hbal hsafe hamb

/-- A zero error term recovers the original no-remainder class-0 C1 control. -/
theorem v30_mdcClass0ExitMassControl_of_withError_zero
    (H : MdcClass0ExitMassControlWithError (fun _ => 0)) :
    MdcClass0ExitMassControl := by
  intro ctx hsurv
  simpa [MdcClass0ExitMassControl, MdcClass0ExitMassControlWithError] using H ctx hsurv

/-- A zero-error finite safe-cone regime recovers the no-remainder class-0
safe-cone regime. -/
theorem v30Class0SafeConeRegime_of_withError_zero
    (H : V30Class0SafeConeRegimeWithError (fun _ => 0)) :
    V30Class0SafeConeRegime := by
  intro ctx hsurv
  obtain ⟨b, Mtot, hbal, hsafe, hamb⟩ := H ctx hsurv
  exact ⟨b, Mtot, hbal, hsafe, v30AmbientAccounting_of_withError_zero ctx hamb⟩

/-- Class-0 C1 leg supplied directly from a provider of class-0 O2 safe-cone
inputs. -/
theorem v30_mdcClass0ExitMassControl_of_o2_unit_provider
    {Ω β : Type*} [DecidableEq Ω]
    (H : forall ctx : ActualFailureContext, Class0DatumSurvivor ctx ->
      V30Class0O2SafeConeInputs (Ω := Ω) (β := β) ctx) :
    MdcClass0ExitMassControl :=
  v30_mdcClass0ExitMassControl_of_safeCone
    (v30Class0SafeConeRegime_of_o2_unit_provider H)

/-- Packaged class-0 supply surface using the constructed O2 rectangle, rather
than a raw abstract carrier/injection.  This is the class-0 analogue of the AK
`O2SupplyInputs` bridge: the rectangle cardinality and faithful projection have
already been discharged by `O2SupplyEmbedding`. -/
structure V30Class0O2SupplySafeConeInputs {β A : Type*} (P₀ Q : Int)
    (ctx : ActualFailureContext) where
  b : Nat
  Mtot : Nat
  hbalance :
    class0SurvivorPeriod (class1SlopeDatum ctx).q * mdcClass0ExitMass ctx <= b * Mtot
  hsafe :
    1536 * (((ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
          / class0SurvivorPeriod (class1SlopeDatum ctx).q) * b)
      <= 31 * class0SurvivorPeriod (class1SlopeDatum ctx).q
  S : Finset A
  Omega : A -> Finset (Nat -> Int)
  Lambda : (Nat -> Int) -> A
  masses : A -> Nat
  carrier : Finset (Nat -> Int)
  Ij : Finset β
  piSt : (Nat -> Int) -> Nat × β
  keyOf : Nat × β -> Int × (Nat -> Int)
  hMtot : Mtot <= Finset.sum S masses
  hIj : Ij.card = 1
  supply : O2SupplyEmbedding.O2SupplyInputs P₀ Q S Omega Lambda masses carrier Ij
    ctx.shell.X piSt keyOf

namespace V30Class0O2SupplySafeConeInputs

/-- The constructed O2 supply surface supplies the ambient accounting field. -/
theorem ambientAccounting {β A : Type*} {P₀ Q : Int} {ctx : ActualFailureContext}
    (I : V30Class0O2SupplySafeConeInputs (β := β) (A := A) P₀ Q ctx) :
    V30AmbientAccounting ctx I.Mtot :=
  v30AmbientAccounting_of_o2_supply_unit_inputs P₀ Q ctx I.S I.Omega I.Lambda
    I.masses I.carrier I.Ij I.piSt I.keyOf I.hMtot I.hIj I.supply

/-- The constructed O2 supply input is one class-0 safe-cone witness. -/
theorem safeConeWitness {β A : Type*} {P₀ Q : Int} {ctx : ActualFailureContext}
    (I : V30Class0O2SupplySafeConeInputs (β := β) (A := A) P₀ Q ctx) :
    ∃ b Mtot : Nat,
      class0SurvivorPeriod (class1SlopeDatum ctx).q * mdcClass0ExitMass ctx <= b * Mtot
      ∧ 1536 * (((ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
            / class0SurvivorPeriod (class1SlopeDatum ctx).q) * b)
          <= 31 * class0SurvivorPeriod (class1SlopeDatum ctx).q
      ∧ Mtot <= ctx.shell.X := by
  refine ⟨I.b, I.Mtot, I.hbalance, I.hsafe, ?_⟩
  exact ambientAccounting I

end V30Class0O2SupplySafeConeInputs

/-- A context-wise provider of constructed class-0 O2 supply inputs supplies the
class-0 safe-cone regime. -/
theorem v30Class0SafeConeRegime_of_o2_supply_provider
    {β A : Type*} (P₀ Q : Int)
    (H : forall ctx : ActualFailureContext, Class0DatumSurvivor ctx ->
      V30Class0O2SupplySafeConeInputs (β := β) (A := A) P₀ Q ctx) :
    V30Class0SafeConeRegime := by
  intro ctx hsurv
  exact V30Class0O2SupplySafeConeInputs.safeConeWitness (H ctx hsurv)

/-- Class-0 C1 leg supplied directly from the constructed O2 supply surface. -/
theorem v30_mdcClass0ExitMassControl_of_o2_supply_provider
    {β A : Type*} (P₀ Q : Int)
    (H : forall ctx : ActualFailureContext, Class0DatumSurvivor ctx ->
      V30Class0O2SupplySafeConeInputs (β := β) (A := A) P₀ Q ctx) :
    MdcClass0ExitMassControl :=
  v30_mdcClass0ExitMassControl_of_safeCone
    (v30Class0SafeConeRegime_of_o2_supply_provider P₀ Q H)

/-- Packaged class-0 collar supply surface in the special no-remainder case.
The explicit `collarZero` field is what turns the deleted-collar ambient bound
back into the no-error `M_tot <= X` input consumed by `cmb_safeCone_nat`. -/
structure V30Class0O2CollarSupplySafeConeInputs {β A : Type*}
    [DecidableEq (Nat -> Int)] (P₀ Q : Int) (ctx : ActualFailureContext) where
  b : Nat
  Mtot : Nat
  hbalance :
    class0SurvivorPeriod (class1SlopeDatum ctx).q * mdcClass0ExitMass ctx <= b * Mtot
  hsafe :
    1536 * (((ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
          / class0SurvivorPeriod (class1SlopeDatum ctx).q) * b)
      <= 31 * class0SurvivorPeriod (class1SlopeDatum ctx).q
  S : Finset A
  Omega : A -> Finset (Nat -> Int)
  Lambda : (Nat -> Int) -> A
  masses : A -> Nat
  carrier : Finset (Nat -> Int)
  post : Finset (Nat -> Int)
  collar : Finset (Nat -> Int)
  Ij : Finset β
  piSt : (Nat -> Int) -> Nat × β
  keyOf : Nat × β -> Int × (Nat -> Int)
  hMtot : Mtot <= Finset.sum S masses
  hIj : Ij.card = 1
  collarZero : collar.card = 0
  supply : O2SupplyEmbedding.O2CollarSupplyInputs P₀ Q S Omega Lambda masses carrier
    post collar Ij ctx.shell.X piSt keyOf

namespace V30Class0O2CollarSupplySafeConeInputs

/-- The zero-collar class-0 O2 collar surface supplies the ambient accounting
field. -/
theorem ambientAccounting {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    {ctx : ActualFailureContext}
    (I : V30Class0O2CollarSupplySafeConeInputs (β := β) (A := A) P₀ Q ctx) :
    V30AmbientAccounting ctx I.Mtot :=
  v30AmbientAccounting_of_o2_collar_supply_unit_inputs_zero_collar P₀ Q ctx
    I.S I.Omega I.Lambda I.masses I.carrier I.post I.collar I.Ij I.piSt I.keyOf
    I.hMtot I.hIj I.supply I.collarZero

/-- The zero-collar class-0 O2 collar input is one class-0 safe-cone witness. -/
theorem safeConeWitness {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    {ctx : ActualFailureContext}
    (I : V30Class0O2CollarSupplySafeConeInputs (β := β) (A := A) P₀ Q ctx) :
    ∃ b Mtot : Nat,
      class0SurvivorPeriod (class1SlopeDatum ctx).q * mdcClass0ExitMass ctx <= b * Mtot
      ∧ 1536 * (((ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
            / class0SurvivorPeriod (class1SlopeDatum ctx).q) * b)
          <= 31 * class0SurvivorPeriod (class1SlopeDatum ctx).q
      ∧ Mtot <= ctx.shell.X := by
  refine ⟨I.b, I.Mtot, I.hbalance, I.hsafe, ?_⟩
  exact ambientAccounting I

end V30Class0O2CollarSupplySafeConeInputs

/-- A context-wise provider of zero-collar class-0 O2 collar inputs supplies the
class-0 safe-cone regime. -/
theorem v30Class0SafeConeRegime_of_o2_collar_supply_provider
    {β A : Type*} [DecidableEq (Nat -> Int)] (P₀ Q : Int)
    (H : forall ctx : ActualFailureContext, Class0DatumSurvivor ctx ->
      V30Class0O2CollarSupplySafeConeInputs (β := β) (A := A) P₀ Q ctx) :
    V30Class0SafeConeRegime := by
  intro ctx hsurv
  exact V30Class0O2CollarSupplySafeConeInputs.safeConeWitness (H ctx hsurv)

/-- Class-0 C1 leg supplied directly from a provider of zero-collar class-0 O2
collar inputs. -/
theorem v30_mdcClass0ExitMassControl_of_o2_collar_supply_provider
    {β A : Type*} [DecidableEq (Nat -> Int)] (P₀ Q : Int)
    (H : forall ctx : ActualFailureContext, Class0DatumSurvivor ctx ->
      V30Class0O2CollarSupplySafeConeInputs (β := β) (A := A) P₀ Q ctx) :
    MdcClass0ExitMassControl :=
  v30_mdcClass0ExitMassControl_of_safeCone
    (v30Class0SafeConeRegime_of_o2_collar_supply_provider P₀ Q H)

/-- Coordinate-split class-0 collar supply surface in the special no-remainder
case. -/
structure V30Class0O2CollarSupplyCoordinateSafeConeInputs {β A : Type*}
    [DecidableEq (Nat -> Int)] (P₀ Q : Int) (ctx : ActualFailureContext) where
  b : Nat
  Mtot : Nat
  hbalance :
    class0SurvivorPeriod (class1SlopeDatum ctx).q * mdcClass0ExitMass ctx <= b * Mtot
  hsafe :
    1536 * (((ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
          / class0SurvivorPeriod (class1SlopeDatum ctx).q) * b)
      <= 31 * class0SurvivorPeriod (class1SlopeDatum ctx).q
  S : Finset A
  Omega : A -> Finset (Nat -> Int)
  Lambda : (Nat -> Int) -> A
  masses : A -> Nat
  carrier : Finset (Nat -> Int)
  post : Finset (Nat -> Int)
  collar : Finset (Nat -> Int)
  Ij : Finset β
  piSt : (Nat -> Int) -> Nat × β
  keyOf : Nat × β -> Int × (Nat -> Int)
  hMtot : Mtot <= Finset.sum S masses
  hIj : Ij.card = 1
  collarZero : collar.card = 0
  supply : O2SupplyEmbedding.O2CollarSupplyCoordinateInputs P₀ Q S Omega Lambda
    masses carrier post collar Ij ctx.shell.X piSt keyOf

namespace V30Class0O2CollarSupplyCoordinateSafeConeInputs

/-- The coordinate-split zero-collar class-0 O2 surface supplies ambient
accounting. -/
theorem ambientAccounting {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    {ctx : ActualFailureContext}
    (I : V30Class0O2CollarSupplyCoordinateSafeConeInputs
      (β := β) (A := A) P₀ Q ctx) :
    V30AmbientAccounting ctx I.Mtot :=
  v30AmbientAccounting_of_o2_collar_supply_coordinate_unit_inputs_zero_collar
    P₀ Q ctx I.S I.Omega I.Lambda I.masses I.carrier I.post I.collar I.Ij
    I.piSt I.keyOf I.hMtot I.hIj I.supply I.collarZero

/-- The coordinate-split zero-collar class-0 input is one class-0 safe-cone
witness. -/
theorem safeConeWitness {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    {ctx : ActualFailureContext}
    (I : V30Class0O2CollarSupplyCoordinateSafeConeInputs
      (β := β) (A := A) P₀ Q ctx) :
    ∃ b Mtot : Nat,
      class0SurvivorPeriod (class1SlopeDatum ctx).q * mdcClass0ExitMass ctx <= b * Mtot
      ∧ 1536 * (((ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
            / class0SurvivorPeriod (class1SlopeDatum ctx).q) * b)
          <= 31 * class0SurvivorPeriod (class1SlopeDatum ctx).q
      ∧ Mtot <= ctx.shell.X := by
  refine ⟨I.b, I.Mtot, I.hbalance, I.hsafe, ?_⟩
  exact ambientAccounting I

end V30Class0O2CollarSupplyCoordinateSafeConeInputs

/-- A context-wise provider of coordinate-split zero-collar class-0 O2 inputs
supplies the class-0 safe-cone regime. -/
theorem v30Class0SafeConeRegime_of_o2_collar_supply_coordinate_provider
    {β A : Type*} [DecidableEq (Nat -> Int)] (P₀ Q : Int)
    (H : forall ctx : ActualFailureContext, Class0DatumSurvivor ctx ->
      V30Class0O2CollarSupplyCoordinateSafeConeInputs (β := β) (A := A) P₀ Q ctx) :
    V30Class0SafeConeRegime := by
  intro ctx hsurv
  exact V30Class0O2CollarSupplyCoordinateSafeConeInputs.safeConeWitness (H ctx hsurv)

/-- Class-0 C1 leg supplied directly from coordinate-split zero-collar class-0
O2 inputs. -/
theorem v30_mdcClass0ExitMassControl_of_o2_collar_supply_coordinate_provider
    {β A : Type*} [DecidableEq (Nat -> Int)] (P₀ Q : Int)
    (H : forall ctx : ActualFailureContext, Class0DatumSurvivor ctx ->
      V30Class0O2CollarSupplyCoordinateSafeConeInputs (β := β) (A := A) P₀ Q ctx) :
    MdcClass0ExitMassControl :=
  v30_mdcClass0ExitMassControl_of_safeCone
    (v30Class0SafeConeRegime_of_o2_collar_supply_coordinate_provider P₀ Q H)

/-- Coordinate-split class-0 collar supply surface retaining the finite collar
as an explicit error term.  This is the class-0 counterpart of
`V30CycleO2CollarSupplyCoordinateSafeConeInputsWithError`: it omits
`collarZero`, so it concludes the finite-error class-0 bound rather than the
no-error `MdcClass0ExitMassControl`. -/
structure V30Class0O2CollarSupplyCoordinateSafeConeInputsWithError {β A : Type*}
    [DecidableEq (Nat -> Int)] (P₀ Q : Int) (ctx : ActualFailureContext) where
  b : Nat
  Mtot : Nat
  hbalance :
    class0SurvivorPeriod (class1SlopeDatum ctx).q * mdcClass0ExitMass ctx <= b * Mtot
  hsafe :
    1536 * (((ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
          / class0SurvivorPeriod (class1SlopeDatum ctx).q) * b)
      <= 31 * class0SurvivorPeriod (class1SlopeDatum ctx).q
  S : Finset A
  Omega : A -> Finset (Nat -> Int)
  Lambda : (Nat -> Int) -> A
  masses : A -> Nat
  carrier : Finset (Nat -> Int)
  post : Finset (Nat -> Int)
  collar : Finset (Nat -> Int)
  Ij : Finset β
  piSt : (Nat -> Int) -> Nat × β
  keyOf : Nat × β -> Int × (Nat -> Int)
  hMtot : Mtot <= Finset.sum S masses
  hIj : Ij.card = 1
  supply : O2SupplyEmbedding.O2CollarSupplyCoordinateInputs P₀ Q S Omega Lambda
    masses carrier post collar Ij ctx.shell.X piSt keyOf

namespace V30Class0O2CollarSupplyCoordinateSafeConeInputsWithError

/-- The coordinate-split class-0 collar input supplies finite-error ambient
accounting with error exactly `collar.card`. -/
theorem ambientAccountingWithError {β A : Type*} [DecidableEq (Nat -> Int)]
    {P₀ Q : Int} {ctx : ActualFailureContext}
    (I : V30Class0O2CollarSupplyCoordinateSafeConeInputsWithError
      (β := β) (A := A) P₀ Q ctx) :
    V30AmbientAccountingWithError ctx I.collar.card I.Mtot :=
  v30AmbientAccountingWithError_of_o2_collar_supply_coordinate_unit_inputs
    P₀ Q ctx I.S I.Omega I.Lambda I.masses I.carrier I.post I.collar I.Ij
    I.piSt I.keyOf I.hMtot I.hIj I.supply

/-- The packaged nonzero-collar class-0 input is one finite-error safe-cone
witness at the current context. -/
theorem safeConeWitnessWithError {β A : Type*} [DecidableEq (Nat -> Int)]
    {P₀ Q : Int} {ctx : ActualFailureContext}
    (I : V30Class0O2CollarSupplyCoordinateSafeConeInputsWithError
      (β := β) (A := A) P₀ Q ctx) :
    exists b Mtot : Nat,
      class0SurvivorPeriod (class1SlopeDatum ctx).q * mdcClass0ExitMass ctx <= b * Mtot
      ∧ 1536 * (((ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
            / class0SurvivorPeriod (class1SlopeDatum ctx).q) * b)
          <= 31 * class0SurvivorPeriod (class1SlopeDatum ctx).q
      ∧ V30AmbientAccountingWithError ctx I.collar.card Mtot := by
  refine ⟨I.b, I.Mtot, I.hbalance, I.hsafe, ?_⟩
  exact ambientAccountingWithError I

/-- The packaged nonzero-collar class-0 input gives the finite-error numerical
C1 bound with the collar retained on the right-hand side. -/
theorem exitMassControlWithError {β A : Type*} [DecidableEq (Nat -> Int)]
    {P₀ Q : Int} {ctx : ActualFailureContext}
    (I : V30Class0O2CollarSupplyCoordinateSafeConeInputsWithError
      (β := β) (A := A) P₀ Q ctx) :
    1536 * (((ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
          / class0SurvivorPeriod (class1SlopeDatum ctx).q)
        * mdcClass0ExitMass ctx)
      <= 31 * (ctx.shell.X + I.collar.card) :=
  cmb_safeCone_nat
    ((ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
        / class0SurvivorPeriod (class1SlopeDatum ctx).q)
    (mdcClass0ExitMass ctx) I.b
    (class0SurvivorPeriod (class1SlopeDatum ctx).q) I.Mtot
    (ctx.shell.X + I.collar.card)
    (tfaClass0SurvivorPeriod_pos _) I.hbalance I.hsafe
    (ambientAccountingWithError I)

/-- A finite-error coordinate collar input for class `0` with a genuine zero
collar is exactly the existing coordinate zero-collar class-0 surface. -/
def toZeroCollar {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    {ctx : ActualFailureContext}
    (I : V30Class0O2CollarSupplyCoordinateSafeConeInputsWithError
      (β := β) (A := A) P₀ Q ctx)
    (hcollar : I.collar.card = 0) :
    V30Class0O2CollarSupplyCoordinateSafeConeInputs
      (β := β) (A := A) P₀ Q ctx where
  b := I.b
  Mtot := I.Mtot
  hbalance := I.hbalance
  hsafe := I.hsafe
  S := I.S
  Omega := I.Omega
  Lambda := I.Lambda
  masses := I.masses
  carrier := I.carrier
  post := I.post
  collar := I.collar
  Ij := I.Ij
  piSt := I.piSt
  keyOf := I.keyOf
  hMtot := I.hMtot
  hIj := I.hIj
  collarZero := hcollar
  supply := I.supply

end V30Class0O2CollarSupplyCoordinateSafeConeInputsWithError

/-! ## Part 5.  The four off-pin classes `{0,3,4,5}` together (AD aggregation) -/

/-- Packaged O2 supply surface for the full v30 off-pin C1 closure.  The
off-pin classes `{3,4,5}` are supplied by the Cycle/O2 bridge, while class `0`
is supplied by the class-0 O2 bridge above. -/
structure V30OffPinFullO2SafeConeInputs {Ω β : Type*} [DecidableEq Ω] where
  hband : forall ctx : ActualFailureContext, 2 ^ 986891 < ctx.X ->
    Not (OrbitBandPinned ctx 2) -> Not (OrbitBandPinned ctx 3) ->
    Not (OrbitBandPinned ctx 4) -> fixedFamilyRecurrentBand ctx <= 4
  class3 : forall ctx : ActualFailureContext, 2 ^ 986891 < ctx.X ->
    Not (OrbitBandPinned ctx 2) -> Not (OrbitBandPinned ctx 3) ->
    Not (OrbitBandPinned ctx 4) ->
      V30CycleO2SafeConeInputs (Ω := Ω) (β := β) ctx 3
  class4 : forall ctx : ActualFailureContext, 2 ^ 986891 < ctx.X ->
    Not (OrbitBandPinned ctx 2) -> Not (OrbitBandPinned ctx 3) ->
    Not (OrbitBandPinned ctx 4) ->
      V30CycleO2SafeConeInputs (Ω := Ω) (β := β) ctx 4
  class5 : forall ctx : ActualFailureContext, 2 ^ 986891 < ctx.X ->
    Not (OrbitBandPinned ctx 2) -> Not (OrbitBandPinned ctx 3) ->
    Not (OrbitBandPinned ctx 4) ->
      V30CycleO2SafeConeInputs (Ω := Ω) (β := β) ctx 5
  class0 : forall ctx : ActualFailureContext, Class0DatumSurvivor ctx ->
    V30Class0O2SafeConeInputs (Ω := Ω) (β := β) ctx

namespace V30OffPinFullO2SafeConeInputs

/-- The packaged O2 full input supplies the off-pin safe-cone regime for
classes `{3,4,5}`. -/
theorem offPinRegime {Ω β : Type*} [DecidableEq Ω]
    (I : V30OffPinFullO2SafeConeInputs (Ω := Ω) (β := β)) :
    V30OffPinSafeConeRegime := by
  intro ctx hX h2 h3 h4
  let I3 := I.class3 ctx hX h2 h3 h4
  let I4 := I.class4 ctx hX h2 h3 h4
  let I5 := I.class5 ctx hX h2 h3 h4
  have hband := I.hband ctx hX h2 h3 h4
  refine ⟨hband, ?_, ?_, ?_⟩
  · exact ⟨I3.D.E.card, I3.D.c, I3.Mtot, V30CycleO2SafeConeInputs.safeConeDatum I3⟩
  · exact ⟨I4.D.E.card, I4.D.c, I4.Mtot, V30CycleO2SafeConeInputs.safeConeDatum I4⟩
  · exact ⟨I5.D.E.card, I5.D.c, I5.Mtot, V30CycleO2SafeConeInputs.safeConeDatum I5⟩

/-- The packaged O2 full input supplies the class-0 safe-cone regime. -/
theorem class0Regime {Ω β : Type*} [DecidableEq Ω]
    (I : V30OffPinFullO2SafeConeInputs (Ω := Ω) (β := β)) :
    V30Class0SafeConeRegime :=
  v30Class0SafeConeRegime_of_o2_unit_provider I.class0

end V30OffPinFullO2SafeConeInputs

/-- The full v30 off-pin regime over all four off-pin classes `{0,3,4,5}`. -/
def V30OffPinFullRegime : Prop :=
  V30OffPinSafeConeRegime ∧ V30Class0SafeConeRegime

/-- The packaged O2 full input supplies the full off-pin regime over all four
off-pin classes `{0,3,4,5}`. -/
theorem v30OffPinFullRegime_of_o2_full_provider
    {Ω β : Type*} [DecidableEq Ω]
    (I : V30OffPinFullO2SafeConeInputs (Ω := Ω) (β := β)) :
    V30OffPinFullRegime :=
  ⟨V30OffPinFullO2SafeConeInputs.offPinRegime I,
    V30OffPinFullO2SafeConeInputs.class0Regime I⟩

/-- **THE OFF-PIN M.5/L.3 CAP OVER ALL FOUR CLASSES `{0,3,4,5}`** (the AD-summed (C1)):
classes `3,4,5` via `ExitMassControlOffPin`, class `0` via `MdcClass0ExitMassControl`. -/
theorem v30_offPin_allClasses (H : V30OffPinFullRegime) :
    ExitMassControlOffPin ∧ MdcClass0ExitMassControl :=
  ⟨v30_offPinExitCap H.1, v30_mdcClass0ExitMassControl_of_safeCone H.2⟩

/-- The full four-class off-pin C1 cap supplied directly from the packaged O2
full provider. -/
theorem v30_offPin_allClasses_of_o2_full_provider
    {Ω β : Type*} [DecidableEq Ω]
    (I : V30OffPinFullO2SafeConeInputs (Ω := Ω) (β := β)) :
    ExitMassControlOffPin ∧ MdcClass0ExitMassControl :=
  v30_offPin_allClasses (v30OffPinFullRegime_of_o2_full_provider I)

/-- Full constructed-O2 supply surface for the v30 off-pin C1 closure.  Classes
`3,4,5` use `V30CycleO2SupplySafeConeInputs`; class `0` uses the constructed
class-0 supply wrapper.  This is the AK/AD-facing counterpart of
`V30OffPinFullO2SafeConeInputs`, with the start/threshold rectangle already
discharged by `O2SupplyEmbedding`. -/
structure V30OffPinFullO2SupplySafeConeInputs {β A : Type*} (P₀ Q : Int) where
  hband : forall ctx : ActualFailureContext, 2 ^ 986891 < ctx.X ->
    Not (OrbitBandPinned ctx 2) -> Not (OrbitBandPinned ctx 3) ->
    Not (OrbitBandPinned ctx 4) -> fixedFamilyRecurrentBand ctx <= 4
  class3 : forall ctx : ActualFailureContext, 2 ^ 986891 < ctx.X ->
    Not (OrbitBandPinned ctx 2) -> Not (OrbitBandPinned ctx 3) ->
    Not (OrbitBandPinned ctx 4) ->
      V30CycleO2SupplySafeConeInputs (β := β) (A := A) P₀ Q ctx 3
  class4 : forall ctx : ActualFailureContext, 2 ^ 986891 < ctx.X ->
    Not (OrbitBandPinned ctx 2) -> Not (OrbitBandPinned ctx 3) ->
    Not (OrbitBandPinned ctx 4) ->
      V30CycleO2SupplySafeConeInputs (β := β) (A := A) P₀ Q ctx 4
  class5 : forall ctx : ActualFailureContext, 2 ^ 986891 < ctx.X ->
    Not (OrbitBandPinned ctx 2) -> Not (OrbitBandPinned ctx 3) ->
    Not (OrbitBandPinned ctx 4) ->
      V30CycleO2SupplySafeConeInputs (β := β) (A := A) P₀ Q ctx 5
  class0 : forall ctx : ActualFailureContext, Class0DatumSurvivor ctx ->
    V30Class0O2SupplySafeConeInputs (β := β) (A := A) P₀ Q ctx

namespace V30OffPinFullO2SupplySafeConeInputs

/-- The full constructed-O2 supply input supplies the off-pin safe-cone regime
for classes `{3,4,5}`. -/
theorem offPinRegime {β A : Type*} {P₀ Q : Int}
    (I : V30OffPinFullO2SupplySafeConeInputs (β := β) (A := A) P₀ Q) :
    V30OffPinSafeConeRegime := by
  intro ctx hX h2 h3 h4
  let I3 := I.class3 ctx hX h2 h3 h4
  let I4 := I.class4 ctx hX h2 h3 h4
  let I5 := I.class5 ctx hX h2 h3 h4
  have hband := I.hband ctx hX h2 h3 h4
  refine ⟨hband, ?_, ?_, ?_⟩
  · exact ⟨I3.D.E.card, I3.D.c, I3.Mtot,
      V30CycleO2SupplySafeConeInputs.safeConeDatum I3⟩
  · exact ⟨I4.D.E.card, I4.D.c, I4.Mtot,
      V30CycleO2SupplySafeConeInputs.safeConeDatum I4⟩
  · exact ⟨I5.D.E.card, I5.D.c, I5.Mtot,
      V30CycleO2SupplySafeConeInputs.safeConeDatum I5⟩

/-- The full constructed-O2 supply input supplies the class-0 safe-cone regime. -/
theorem class0Regime {β A : Type*} {P₀ Q : Int}
    (I : V30OffPinFullO2SupplySafeConeInputs (β := β) (A := A) P₀ Q) :
    V30Class0SafeConeRegime :=
  v30Class0SafeConeRegime_of_o2_supply_provider P₀ Q I.class0

end V30OffPinFullO2SupplySafeConeInputs

/-- The full constructed-O2 supply input supplies the full off-pin regime over
all four off-pin classes `{0,3,4,5}`. -/
theorem v30OffPinFullRegime_of_o2_supply_full_provider
    {β A : Type*} (P₀ Q : Int)
    (I : V30OffPinFullO2SupplySafeConeInputs (β := β) (A := A) P₀ Q) :
    V30OffPinFullRegime :=
  ⟨V30OffPinFullO2SupplySafeConeInputs.offPinRegime I,
    V30OffPinFullO2SupplySafeConeInputs.class0Regime I⟩

/-- The four-class off-pin C1 cap supplied directly from the full constructed-O2
supply provider. -/
theorem v30_offPin_allClasses_of_o2_supply_full_provider
    {β A : Type*} (P₀ Q : Int)
    (I : V30OffPinFullO2SupplySafeConeInputs (β := β) (A := A) P₀ Q) :
    ExitMassControlOffPin ∧ MdcClass0ExitMassControl :=
  v30_offPin_allClasses (v30OffPinFullRegime_of_o2_supply_full_provider P₀ Q I)

/-- Full zero-collar constructed-O2 collar supply surface for the v30 off-pin
C1 closure.  This is the deleted-collar counterpart of
`V30OffPinFullO2SupplySafeConeInputs`; every component carries an explicit
`collar.card = 0` certificate before it is consumed by C1. -/
structure V30OffPinFullO2CollarSupplySafeConeInputs {β A : Type*}
    [DecidableEq (Nat -> Int)] (P₀ Q : Int) where
  hband : forall ctx : ActualFailureContext, 2 ^ 986891 < ctx.X ->
    Not (OrbitBandPinned ctx 2) -> Not (OrbitBandPinned ctx 3) ->
    Not (OrbitBandPinned ctx 4) -> fixedFamilyRecurrentBand ctx <= 4
  class3 : forall ctx : ActualFailureContext, 2 ^ 986891 < ctx.X ->
    Not (OrbitBandPinned ctx 2) -> Not (OrbitBandPinned ctx 3) ->
    Not (OrbitBandPinned ctx 4) ->
      V30CycleO2CollarSupplySafeConeInputs (β := β) (A := A) P₀ Q ctx 3
  class4 : forall ctx : ActualFailureContext, 2 ^ 986891 < ctx.X ->
    Not (OrbitBandPinned ctx 2) -> Not (OrbitBandPinned ctx 3) ->
    Not (OrbitBandPinned ctx 4) ->
      V30CycleO2CollarSupplySafeConeInputs (β := β) (A := A) P₀ Q ctx 4
  class5 : forall ctx : ActualFailureContext, 2 ^ 986891 < ctx.X ->
    Not (OrbitBandPinned ctx 2) -> Not (OrbitBandPinned ctx 3) ->
    Not (OrbitBandPinned ctx 4) ->
      V30CycleO2CollarSupplySafeConeInputs (β := β) (A := A) P₀ Q ctx 5
  class0 : forall ctx : ActualFailureContext, Class0DatumSurvivor ctx ->
    V30Class0O2CollarSupplySafeConeInputs (β := β) (A := A) P₀ Q ctx

namespace V30OffPinFullO2CollarSupplySafeConeInputs

/-- The full zero-collar O2 collar supply input supplies the off-pin safe-cone
regime for classes `{3,4,5}`. -/
theorem offPinRegime {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (I : V30OffPinFullO2CollarSupplySafeConeInputs (β := β) (A := A) P₀ Q) :
    V30OffPinSafeConeRegime := by
  intro ctx hX h2 h3 h4
  let I3 := I.class3 ctx hX h2 h3 h4
  let I4 := I.class4 ctx hX h2 h3 h4
  let I5 := I.class5 ctx hX h2 h3 h4
  have hband := I.hband ctx hX h2 h3 h4
  refine ⟨hband, ?_, ?_, ?_⟩
  · exact ⟨I3.D.E.card, I3.D.c, I3.Mtot,
      V30CycleO2CollarSupplySafeConeInputs.safeConeDatum I3⟩
  · exact ⟨I4.D.E.card, I4.D.c, I4.Mtot,
      V30CycleO2CollarSupplySafeConeInputs.safeConeDatum I4⟩
  · exact ⟨I5.D.E.card, I5.D.c, I5.Mtot,
      V30CycleO2CollarSupplySafeConeInputs.safeConeDatum I5⟩

/-- The full zero-collar O2 collar supply input supplies the class-0 safe-cone
regime. -/
theorem class0Regime {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (I : V30OffPinFullO2CollarSupplySafeConeInputs (β := β) (A := A) P₀ Q) :
    V30Class0SafeConeRegime :=
  v30Class0SafeConeRegime_of_o2_collar_supply_provider P₀ Q I.class0

end V30OffPinFullO2CollarSupplySafeConeInputs

/-- The full zero-collar O2 collar supply input supplies the full off-pin regime
over all four off-pin classes `{0,3,4,5}`. -/
theorem v30OffPinFullRegime_of_o2_collar_supply_full_provider
    {β A : Type*} [DecidableEq (Nat -> Int)] (P₀ Q : Int)
    (I : V30OffPinFullO2CollarSupplySafeConeInputs (β := β) (A := A) P₀ Q) :
    V30OffPinFullRegime :=
  ⟨V30OffPinFullO2CollarSupplySafeConeInputs.offPinRegime I,
    V30OffPinFullO2CollarSupplySafeConeInputs.class0Regime I⟩

/-- The four-class off-pin C1 cap supplied directly from the full zero-collar
O2 collar supply provider. -/
theorem v30_offPin_allClasses_of_o2_collar_supply_full_provider
    {β A : Type*} [DecidableEq (Nat -> Int)] (P₀ Q : Int)
    (I : V30OffPinFullO2CollarSupplySafeConeInputs (β := β) (A := A) P₀ Q) :
    ExitMassControlOffPin ∧ MdcClass0ExitMassControl :=
  v30_offPin_allClasses
    (v30OffPinFullRegime_of_o2_collar_supply_full_provider P₀ Q I)

/-- Full coordinate-split zero-collar O2 collar supply surface for the v30
off-pin C1 closure. -/
structure V30OffPinFullO2CollarSupplyCoordinateSafeConeInputs {β A : Type*}
    [DecidableEq (Nat -> Int)] (P₀ Q : Int) where
  hband : forall ctx : ActualFailureContext, 2 ^ 986891 < ctx.X ->
    Not (OrbitBandPinned ctx 2) -> Not (OrbitBandPinned ctx 3) ->
    Not (OrbitBandPinned ctx 4) -> fixedFamilyRecurrentBand ctx <= 4
  class3 : forall ctx : ActualFailureContext, 2 ^ 986891 < ctx.X ->
    Not (OrbitBandPinned ctx 2) -> Not (OrbitBandPinned ctx 3) ->
    Not (OrbitBandPinned ctx 4) ->
      V30CycleO2CollarSupplyCoordinateSafeConeInputs (β := β) (A := A) P₀ Q ctx 3
  class4 : forall ctx : ActualFailureContext, 2 ^ 986891 < ctx.X ->
    Not (OrbitBandPinned ctx 2) -> Not (OrbitBandPinned ctx 3) ->
    Not (OrbitBandPinned ctx 4) ->
      V30CycleO2CollarSupplyCoordinateSafeConeInputs (β := β) (A := A) P₀ Q ctx 4
  class5 : forall ctx : ActualFailureContext, 2 ^ 986891 < ctx.X ->
    Not (OrbitBandPinned ctx 2) -> Not (OrbitBandPinned ctx 3) ->
    Not (OrbitBandPinned ctx 4) ->
      V30CycleO2CollarSupplyCoordinateSafeConeInputs (β := β) (A := A) P₀ Q ctx 5
  class0 : forall ctx : ActualFailureContext, Class0DatumSurvivor ctx ->
    V30Class0O2CollarSupplyCoordinateSafeConeInputs (β := β) (A := A) P₀ Q ctx

namespace V30OffPinFullO2CollarSupplyCoordinateSafeConeInputs

/-- The full coordinate-split zero-collar input supplies the off-pin safe-cone
regime for classes `{3,4,5}`. -/
theorem offPinRegime {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (I : V30OffPinFullO2CollarSupplyCoordinateSafeConeInputs
      (β := β) (A := A) P₀ Q) :
    V30OffPinSafeConeRegime := by
  intro ctx hX h2 h3 h4
  let I3 := I.class3 ctx hX h2 h3 h4
  let I4 := I.class4 ctx hX h2 h3 h4
  let I5 := I.class5 ctx hX h2 h3 h4
  have hband := I.hband ctx hX h2 h3 h4
  refine ⟨hband, ?_, ?_, ?_⟩
  · exact ⟨I3.D.E.card, I3.D.c, I3.Mtot,
      V30CycleO2CollarSupplyCoordinateSafeConeInputs.safeConeDatum I3⟩
  · exact ⟨I4.D.E.card, I4.D.c, I4.Mtot,
      V30CycleO2CollarSupplyCoordinateSafeConeInputs.safeConeDatum I4⟩
  · exact ⟨I5.D.E.card, I5.D.c, I5.Mtot,
      V30CycleO2CollarSupplyCoordinateSafeConeInputs.safeConeDatum I5⟩

/-- The full coordinate-split zero-collar input supplies the class-0 safe-cone
regime. -/
theorem class0Regime {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (I : V30OffPinFullO2CollarSupplyCoordinateSafeConeInputs
      (β := β) (A := A) P₀ Q) :
    V30Class0SafeConeRegime :=
  v30Class0SafeConeRegime_of_o2_collar_supply_coordinate_provider P₀ Q I.class0

end V30OffPinFullO2CollarSupplyCoordinateSafeConeInputs

/-- The full coordinate-split zero-collar input supplies the full off-pin
regime over all four off-pin classes `{0,3,4,5}`. -/
theorem v30OffPinFullRegime_of_o2_collar_supply_coordinate_full_provider
    {β A : Type*} [DecidableEq (Nat -> Int)] (P₀ Q : Int)
    (I : V30OffPinFullO2CollarSupplyCoordinateSafeConeInputs
      (β := β) (A := A) P₀ Q) :
    V30OffPinFullRegime :=
  ⟨V30OffPinFullO2CollarSupplyCoordinateSafeConeInputs.offPinRegime I,
    V30OffPinFullO2CollarSupplyCoordinateSafeConeInputs.class0Regime I⟩

/-- The four-class off-pin C1 cap supplied directly from the full
coordinate-split zero-collar provider. -/
theorem v30_offPin_allClasses_of_o2_collar_supply_coordinate_full_provider
    {β A : Type*} [DecidableEq (Nat -> Int)] (P₀ Q : Int)
    (I : V30OffPinFullO2CollarSupplyCoordinateSafeConeInputs
      (β := β) (A := A) P₀ Q) :
    ExitMassControlOffPin ∧ MdcClass0ExitMassControl :=
  v30_offPin_allClasses
    (v30OffPinFullRegime_of_o2_collar_supply_coordinate_full_provider P₀ Q I)

/-- Full coordinate-split O2 collar supply surface retaining the finite collar
errors for all four off-pin classes `{0,3,4,5}`.  This is intentionally not an
`ExitMassControlOffPin` provider: the finite collars are preserved in the
conclusions until a genuine zero/absorbed-error argument is supplied. -/
structure V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError {β A : Type*}
    [DecidableEq (Nat -> Int)] (P₀ Q : Int) where
  hband : forall ctx : ActualFailureContext, 2 ^ 986891 < ctx.X ->
    Not (OrbitBandPinned ctx 2) -> Not (OrbitBandPinned ctx 3) ->
    Not (OrbitBandPinned ctx 4) -> fixedFamilyRecurrentBand ctx <= 4
  class3 : forall ctx : ActualFailureContext, 2 ^ 986891 < ctx.X ->
    Not (OrbitBandPinned ctx 2) -> Not (OrbitBandPinned ctx 3) ->
    Not (OrbitBandPinned ctx 4) ->
      V30CycleO2CollarSupplyCoordinateSafeConeInputsWithError
        (β := β) (A := A) P₀ Q ctx 3
  class4 : forall ctx : ActualFailureContext, 2 ^ 986891 < ctx.X ->
    Not (OrbitBandPinned ctx 2) -> Not (OrbitBandPinned ctx 3) ->
    Not (OrbitBandPinned ctx 4) ->
      V30CycleO2CollarSupplyCoordinateSafeConeInputsWithError
        (β := β) (A := A) P₀ Q ctx 4
  class5 : forall ctx : ActualFailureContext, 2 ^ 986891 < ctx.X ->
    Not (OrbitBandPinned ctx 2) -> Not (OrbitBandPinned ctx 3) ->
    Not (OrbitBandPinned ctx 4) ->
      V30CycleO2CollarSupplyCoordinateSafeConeInputsWithError
        (β := β) (A := A) P₀ Q ctx 5
  class0 : forall ctx : ActualFailureContext, Class0DatumSurvivor ctx ->
    V30Class0O2CollarSupplyCoordinateSafeConeInputsWithError
      (β := β) (A := A) P₀ Q ctx

namespace V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError

/-- Finite-error cap for class `3` supplied by the full nonzero-collar provider. -/
theorem class3CapWithError {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (I : V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError
      (β := β) (A := A) P₀ Q)
    {ctx : ActualFailureContext} (hX : 2 ^ 986891 < ctx.X)
    (hn2 : Not (OrbitBandPinned ctx 2)) (hn3 : Not (OrbitBandPinned ctx 3))
    (hn4 : Not (OrbitBandPinned ctx 4)) :
    V30OffPinClassCapWithError ctx 3
      ((I.class3 ctx hX hn2 hn3 hn4).collar.card) :=
  V30CycleO2CollarSupplyCoordinateSafeConeInputsWithError.classCapWithError
    (I.class3 ctx hX hn2 hn3 hn4) (I.hband ctx hX hn2 hn3 hn4)

/-- Finite-error cap for class `4` supplied by the full nonzero-collar provider. -/
theorem class4CapWithError {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (I : V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError
      (β := β) (A := A) P₀ Q)
    {ctx : ActualFailureContext} (hX : 2 ^ 986891 < ctx.X)
    (hn2 : Not (OrbitBandPinned ctx 2)) (hn3 : Not (OrbitBandPinned ctx 3))
    (hn4 : Not (OrbitBandPinned ctx 4)) :
    V30OffPinClassCapWithError ctx 4
      ((I.class4 ctx hX hn2 hn3 hn4).collar.card) :=
  V30CycleO2CollarSupplyCoordinateSafeConeInputsWithError.classCapWithError
    (I.class4 ctx hX hn2 hn3 hn4) (I.hband ctx hX hn2 hn3 hn4)

/-- Finite-error cap for class `5` supplied by the full nonzero-collar provider. -/
theorem class5CapWithError {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (I : V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError
      (β := β) (A := A) P₀ Q)
    {ctx : ActualFailureContext} (hX : 2 ^ 986891 < ctx.X)
    (hn2 : Not (OrbitBandPinned ctx 2)) (hn3 : Not (OrbitBandPinned ctx 3))
    (hn4 : Not (OrbitBandPinned ctx 4)) :
    V30OffPinClassCapWithError ctx 5
      ((I.class5 ctx hX hn2 hn3 hn4).collar.card) :=
  V30CycleO2CollarSupplyCoordinateSafeConeInputsWithError.classCapWithError
    (I.class5 ctx hX hn2 hn3 hn4) (I.hband ctx hX hn2 hn3 hn4)

/-- Finite-error class-0 C1 inequality supplied by the full nonzero-collar
provider. -/
theorem class0ExitMassControlWithError {β A : Type*} [DecidableEq (Nat -> Int)]
    {P₀ Q : Int}
    (I : V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError
      (β := β) (A := A) P₀ Q)
    {ctx : ActualFailureContext} (hsurv : Class0DatumSurvivor ctx) :
    1536 * (((ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
          / class0SurvivorPeriod (class1SlopeDatum ctx).q)
        * mdcClass0ExitMass ctx)
      <= 31 * (ctx.shell.X + (I.class0 ctx hsurv).collar.card) :=
  V30Class0O2CollarSupplyCoordinateSafeConeInputsWithError.exitMassControlWithError
    (I.class0 ctx hsurv)

/-- The full nonzero-collar provider exposes exactly the four finite-error
deliverables needed before any later zero/absorption step. -/
theorem finiteErrorDeliverables {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (I : V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError
      (β := β) (A := A) P₀ Q) :
    (forall (ctx : ActualFailureContext) (hX : 2 ^ 986891 < ctx.X)
      (hn2 : Not (OrbitBandPinned ctx 2)) (hn3 : Not (OrbitBandPinned ctx 3))
      (hn4 : Not (OrbitBandPinned ctx 4)),
        V30OffPinClassCapWithError ctx 3
          ((I.class3 ctx hX hn2 hn3 hn4).collar.card))
    ∧ (forall (ctx : ActualFailureContext) (hX : 2 ^ 986891 < ctx.X)
      (hn2 : Not (OrbitBandPinned ctx 2)) (hn3 : Not (OrbitBandPinned ctx 3))
      (hn4 : Not (OrbitBandPinned ctx 4)),
        V30OffPinClassCapWithError ctx 4
          ((I.class4 ctx hX hn2 hn3 hn4).collar.card))
    ∧ (forall (ctx : ActualFailureContext) (hX : 2 ^ 986891 < ctx.X)
      (hn2 : Not (OrbitBandPinned ctx 2)) (hn3 : Not (OrbitBandPinned ctx 3))
      (hn4 : Not (OrbitBandPinned ctx 4)),
        V30OffPinClassCapWithError ctx 5
          ((I.class5 ctx hX hn2 hn3 hn4).collar.card))
    ∧ (forall (ctx : ActualFailureContext) (hsurv : Class0DatumSurvivor ctx),
      1536 * (((ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
            / class0SurvivorPeriod (class1SlopeDatum ctx).q)
          * mdcClass0ExitMass ctx)
        <= 31 * (ctx.shell.X + (I.class0 ctx hsurv).collar.card)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ctx hX hn2 hn3 hn4
    exact class3CapWithError I hX hn2 hn3 hn4
  · intro ctx hX hn2 hn3 hn4
    exact class4CapWithError I hX hn2 hn3 hn4
  · intro ctx hX hn2 hn3 hn4
    exact class5CapWithError I hX hn2 hn3 hn4
  · intro ctx hsurv
    exact class0ExitMassControlWithError I hsurv

/-- A full finite-error coordinate collar provider with genuinely zero collars
is the existing full coordinate zero-collar provider surface. -/
def toZeroCollarProvider {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (I : V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError
      (β := β) (A := A) P₀ Q)
    (h3zero : forall (ctx : ActualFailureContext) (hX : 2 ^ 986891 < ctx.X)
      (hn2 : Not (OrbitBandPinned ctx 2)) (hn3 : Not (OrbitBandPinned ctx 3))
      (hn4 : Not (OrbitBandPinned ctx 4)),
        (I.class3 ctx hX hn2 hn3 hn4).collar.card = 0)
    (h4zero : forall (ctx : ActualFailureContext) (hX : 2 ^ 986891 < ctx.X)
      (hn2 : Not (OrbitBandPinned ctx 2)) (hn3 : Not (OrbitBandPinned ctx 3))
      (hn4 : Not (OrbitBandPinned ctx 4)),
        (I.class4 ctx hX hn2 hn3 hn4).collar.card = 0)
    (h5zero : forall (ctx : ActualFailureContext) (hX : 2 ^ 986891 < ctx.X)
      (hn2 : Not (OrbitBandPinned ctx 2)) (hn3 : Not (OrbitBandPinned ctx 3))
      (hn4 : Not (OrbitBandPinned ctx 4)),
        (I.class5 ctx hX hn2 hn3 hn4).collar.card = 0)
    (h0zero : forall (ctx : ActualFailureContext) (hsurv : Class0DatumSurvivor ctx),
      (I.class0 ctx hsurv).collar.card = 0) :
    V30OffPinFullO2CollarSupplyCoordinateSafeConeInputs
      (β := β) (A := A) P₀ Q where
  hband := I.hband
  class3 := fun ctx hX hn2 hn3 hn4 =>
    V30CycleO2CollarSupplyCoordinateSafeConeInputsWithError.toZeroCollar
      (I.class3 ctx hX hn2 hn3 hn4) (h3zero ctx hX hn2 hn3 hn4)
  class4 := fun ctx hX hn2 hn3 hn4 =>
    V30CycleO2CollarSupplyCoordinateSafeConeInputsWithError.toZeroCollar
      (I.class4 ctx hX hn2 hn3 hn4) (h4zero ctx hX hn2 hn3 hn4)
  class5 := fun ctx hX hn2 hn3 hn4 =>
    V30CycleO2CollarSupplyCoordinateSafeConeInputsWithError.toZeroCollar
      (I.class5 ctx hX hn2 hn3 hn4) (h5zero ctx hX hn2 hn3 hn4)
  class0 := fun ctx hsurv =>
    V30Class0O2CollarSupplyCoordinateSafeConeInputsWithError.toZeroCollar
      (I.class0 ctx hsurv) (h0zero ctx hsurv)

/-- The same zero-collar conversion recovers the full off-pin safe-cone regime,
not merely the already-assembled endpoint inequalities. -/
theorem fullRegime_of_zeroCollarProvider {β A : Type*} [DecidableEq (Nat -> Int)]
    {P₀ Q : Int}
    (I : V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError
      (β := β) (A := A) P₀ Q)
    (h3zero : forall (ctx : ActualFailureContext) (hX : 2 ^ 986891 < ctx.X)
      (hn2 : Not (OrbitBandPinned ctx 2)) (hn3 : Not (OrbitBandPinned ctx 3))
      (hn4 : Not (OrbitBandPinned ctx 4)),
        (I.class3 ctx hX hn2 hn3 hn4).collar.card = 0)
    (h4zero : forall (ctx : ActualFailureContext) (hX : 2 ^ 986891 < ctx.X)
      (hn2 : Not (OrbitBandPinned ctx 2)) (hn3 : Not (OrbitBandPinned ctx 3))
      (hn4 : Not (OrbitBandPinned ctx 4)),
        (I.class4 ctx hX hn2 hn3 hn4).collar.card = 0)
    (h5zero : forall (ctx : ActualFailureContext) (hX : 2 ^ 986891 < ctx.X)
      (hn2 : Not (OrbitBandPinned ctx 2)) (hn3 : Not (OrbitBandPinned ctx 3))
      (hn4 : Not (OrbitBandPinned ctx 4)),
        (I.class5 ctx hX hn2 hn3 hn4).collar.card = 0)
    (h0zero : forall (ctx : ActualFailureContext) (hsurv : Class0DatumSurvivor ctx),
      (I.class0 ctx hsurv).collar.card = 0) :
    V30OffPinFullRegime :=
  v30OffPinFullRegime_of_o2_collar_supply_coordinate_full_provider P₀ Q
    (toZeroCollarProvider I h3zero h4zero h5zero h0zero)

/-- If the full finite-error provider's three off-pin collars are zero, its
finite-error caps recover the no-error `ExitMassControlOffPin` supplier. -/
theorem offPinExitCap_of_zeroCollars {β A : Type*} [DecidableEq (Nat -> Int)]
    {P₀ Q : Int}
    (I : V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError
      (β := β) (A := A) P₀ Q)
    (h3zero : forall (ctx : ActualFailureContext) (hX : 2 ^ 986891 < ctx.X)
      (hn2 : Not (OrbitBandPinned ctx 2)) (hn3 : Not (OrbitBandPinned ctx 3))
      (hn4 : Not (OrbitBandPinned ctx 4)),
        (I.class3 ctx hX hn2 hn3 hn4).collar.card = 0)
    (h4zero : forall (ctx : ActualFailureContext) (hX : 2 ^ 986891 < ctx.X)
      (hn2 : Not (OrbitBandPinned ctx 2)) (hn3 : Not (OrbitBandPinned ctx 3))
      (hn4 : Not (OrbitBandPinned ctx 4)),
        (I.class4 ctx hX hn2 hn3 hn4).collar.card = 0)
    (h5zero : forall (ctx : ActualFailureContext) (hX : 2 ^ 986891 < ctx.X)
      (hn2 : Not (OrbitBandPinned ctx 2)) (hn3 : Not (OrbitBandPinned ctx 3))
      (hn4 : Not (OrbitBandPinned ctx 4)),
        (I.class5 ctx hX hn2 hn3 hn4).collar.card = 0) :
    ExitMassControlOffPin := by
  intro ctx hX hn2 hn3 hn4
  refine ⟨?_, ?_, ?_⟩
  · have hcap := class3CapWithError I hX hn2 hn3 hn4
    have hzero := h3zero ctx hX hn2 hn3 hn4
    have hcap0 : V30OffPinClassCapWithError ctx 3 0 := by
      simpa [hzero] using hcap
    exact v30_offPin_classCap_of_withError_zero hcap0
  · have hcap := class4CapWithError I hX hn2 hn3 hn4
    have hzero := h4zero ctx hX hn2 hn3 hn4
    have hcap0 : V30OffPinClassCapWithError ctx 4 0 := by
      simpa [hzero] using hcap
    exact v30_offPin_classCap_of_withError_zero hcap0
  · have hcap := class5CapWithError I hX hn2 hn3 hn4
    have hzero := h5zero ctx hX hn2 hn3 hn4
    have hcap0 : V30OffPinClassCapWithError ctx 5 0 := by
      simpa [hzero] using hcap
    exact v30_offPin_classCap_of_withError_zero hcap0

/-- If the class-0 collar in the full finite-error provider is zero, its
finite-error class-0 inequality recovers `MdcClass0ExitMassControl`. -/
theorem class0ExitMassControl_of_zeroCollars {β A : Type*}
    [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (I : V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError
      (β := β) (A := A) P₀ Q)
    (h0zero : forall (ctx : ActualFailureContext) (hsurv : Class0DatumSurvivor ctx),
      (I.class0 ctx hsurv).collar.card = 0) :
    MdcClass0ExitMassControl := by
  intro ctx hsurv
  have hcap := class0ExitMassControlWithError I hsurv
  have hzero := h0zero ctx hsurv
  simpa [MdcClass0ExitMassControl, hzero] using hcap

/-- Zero collars in the full finite-error provider recover the same four-class
no-error deliverable as the explicit zero-collar provider surface. -/
theorem allClasses_of_zeroCollars {β A : Type*} [DecidableEq (Nat -> Int)]
    {P₀ Q : Int}
    (I : V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError
      (β := β) (A := A) P₀ Q)
    (h3zero : forall (ctx : ActualFailureContext) (hX : 2 ^ 986891 < ctx.X)
      (hn2 : Not (OrbitBandPinned ctx 2)) (hn3 : Not (OrbitBandPinned ctx 3))
      (hn4 : Not (OrbitBandPinned ctx 4)),
        (I.class3 ctx hX hn2 hn3 hn4).collar.card = 0)
    (h4zero : forall (ctx : ActualFailureContext) (hX : 2 ^ 986891 < ctx.X)
      (hn2 : Not (OrbitBandPinned ctx 2)) (hn3 : Not (OrbitBandPinned ctx 3))
      (hn4 : Not (OrbitBandPinned ctx 4)),
        (I.class4 ctx hX hn2 hn3 hn4).collar.card = 0)
    (h5zero : forall (ctx : ActualFailureContext) (hX : 2 ^ 986891 < ctx.X)
      (hn2 : Not (OrbitBandPinned ctx 2)) (hn3 : Not (OrbitBandPinned ctx 3))
      (hn4 : Not (OrbitBandPinned ctx 4)),
        (I.class5 ctx hX hn2 hn3 hn4).collar.card = 0)
    (h0zero : forall (ctx : ActualFailureContext) (hsurv : Class0DatumSurvivor ctx),
      (I.class0 ctx hsurv).collar.card = 0) :
    ExitMassControlOffPin ∧ MdcClass0ExitMassControl :=
  ⟨offPinExitCap_of_zeroCollars I h3zero h4zero h5zero,
    class0ExitMassControl_of_zeroCollars I h0zero⟩

/-- If the four finite-error collars are literally empty, then they supply the
same zero-collar coordinate provider.  This is the endpoint form closest to the
TeX phrasing that the relevant endpoint/carry collars have been deleted. -/
def toZeroCollarProvider_of_emptyCollars {β A : Type*} [DecidableEq (Nat -> Int)]
    {P₀ Q : Int}
    (I : V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError
      (β := β) (A := A) P₀ Q)
    (h3empty : forall (ctx : ActualFailureContext) (hX : 2 ^ 986891 < ctx.X)
      (hn2 : Not (OrbitBandPinned ctx 2)) (hn3 : Not (OrbitBandPinned ctx 3))
      (hn4 : Not (OrbitBandPinned ctx 4)),
        (I.class3 ctx hX hn2 hn3 hn4).collar = ∅)
    (h4empty : forall (ctx : ActualFailureContext) (hX : 2 ^ 986891 < ctx.X)
      (hn2 : Not (OrbitBandPinned ctx 2)) (hn3 : Not (OrbitBandPinned ctx 3))
      (hn4 : Not (OrbitBandPinned ctx 4)),
        (I.class4 ctx hX hn2 hn3 hn4).collar = ∅)
    (h5empty : forall (ctx : ActualFailureContext) (hX : 2 ^ 986891 < ctx.X)
      (hn2 : Not (OrbitBandPinned ctx 2)) (hn3 : Not (OrbitBandPinned ctx 3))
      (hn4 : Not (OrbitBandPinned ctx 4)),
        (I.class5 ctx hX hn2 hn3 hn4).collar = ∅)
    (h0empty : forall (ctx : ActualFailureContext) (hsurv : Class0DatumSurvivor ctx),
      (I.class0 ctx hsurv).collar = ∅) :
    V30OffPinFullO2CollarSupplyCoordinateSafeConeInputs
      (β := β) (A := A) P₀ Q :=
  toZeroCollarProvider I
    (fun ctx hX hn2 hn3 hn4 => by
      simp [h3empty ctx hX hn2 hn3 hn4])
    (fun ctx hX hn2 hn3 hn4 => by
      simp [h4empty ctx hX hn2 hn3 hn4])
    (fun ctx hX hn2 hn3 hn4 => by
      simp [h5empty ctx hX hn2 hn3 hn4])
    (fun ctx hsurv => by
      simp [h0empty ctx hsurv])

/-- Empty collars recover the full off-pin safe-cone regime by first passing
through the zero-collar provider bridge. -/
theorem fullRegime_of_emptyCollars {β A : Type*} [DecidableEq (Nat -> Int)]
    {P₀ Q : Int}
    (I : V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError
      (β := β) (A := A) P₀ Q)
    (h3empty : forall (ctx : ActualFailureContext) (hX : 2 ^ 986891 < ctx.X)
      (hn2 : Not (OrbitBandPinned ctx 2)) (hn3 : Not (OrbitBandPinned ctx 3))
      (hn4 : Not (OrbitBandPinned ctx 4)),
        (I.class3 ctx hX hn2 hn3 hn4).collar = ∅)
    (h4empty : forall (ctx : ActualFailureContext) (hX : 2 ^ 986891 < ctx.X)
      (hn2 : Not (OrbitBandPinned ctx 2)) (hn3 : Not (OrbitBandPinned ctx 3))
      (hn4 : Not (OrbitBandPinned ctx 4)),
        (I.class4 ctx hX hn2 hn3 hn4).collar = ∅)
    (h5empty : forall (ctx : ActualFailureContext) (hX : 2 ^ 986891 < ctx.X)
      (hn2 : Not (OrbitBandPinned ctx 2)) (hn3 : Not (OrbitBandPinned ctx 3))
      (hn4 : Not (OrbitBandPinned ctx 4)),
        (I.class5 ctx hX hn2 hn3 hn4).collar = ∅)
    (h0empty : forall (ctx : ActualFailureContext) (hsurv : Class0DatumSurvivor ctx),
      (I.class0 ctx hsurv).collar = ∅) :
    V30OffPinFullRegime :=
  v30OffPinFullRegime_of_o2_collar_supply_coordinate_full_provider P₀ Q
    (toZeroCollarProvider_of_emptyCollars I h3empty h4empty h5empty h0empty)

/-- Empty collars in the finite-error full provider recover the same four-class
no-error deliverable as the zero-collar API. -/
theorem allClasses_of_emptyCollars {β A : Type*} [DecidableEq (Nat -> Int)]
    {P₀ Q : Int}
    (I : V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError
      (β := β) (A := A) P₀ Q)
    (h3empty : forall (ctx : ActualFailureContext) (hX : 2 ^ 986891 < ctx.X)
      (hn2 : Not (OrbitBandPinned ctx 2)) (hn3 : Not (OrbitBandPinned ctx 3))
      (hn4 : Not (OrbitBandPinned ctx 4)),
        (I.class3 ctx hX hn2 hn3 hn4).collar = ∅)
    (h4empty : forall (ctx : ActualFailureContext) (hX : 2 ^ 986891 < ctx.X)
      (hn2 : Not (OrbitBandPinned ctx 2)) (hn3 : Not (OrbitBandPinned ctx 3))
      (hn4 : Not (OrbitBandPinned ctx 4)),
        (I.class4 ctx hX hn2 hn3 hn4).collar = ∅)
    (h5empty : forall (ctx : ActualFailureContext) (hX : 2 ^ 986891 < ctx.X)
      (hn2 : Not (OrbitBandPinned ctx 2)) (hn3 : Not (OrbitBandPinned ctx 3))
      (hn4 : Not (OrbitBandPinned ctx 4)),
        (I.class5 ctx hX hn2 hn3 hn4).collar = ∅)
    (h0empty : forall (ctx : ActualFailureContext) (hsurv : Class0DatumSurvivor ctx),
      (I.class0 ctx hsurv).collar = ∅) :
    ExitMassControlOffPin ∧ MdcClass0ExitMassControl :=
  allClasses_of_zeroCollars I
    (fun ctx hX hn2 hn3 hn4 => by
      simp [h3empty ctx hX hn2 hn3 hn4])
    (fun ctx hX hn2 hn3 hn4 => by
      simp [h4empty ctx hX hn2 hn3 hn4])
    (fun ctx hX hn2 hn3 hn4 => by
      simp [h5empty ctx hX hn2 hn3 hn4])
    (fun ctx hsurv => by
      simp [h0empty ctx hsurv])

end V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError

/-- Packaged endpoint-facing version of the TeX phrase that the relevant
endpoint/carry collars have been deleted.  The underlying O2/AB/R provider is
kept in the faithful finite-error form, while the four fields record literal
emptiness of the collar sets. -/
structure V30OffPinFullO2CollarSupplyCoordinateEmptyCollarSafeConeInputs
    {β A : Type*} [DecidableEq (Nat -> Int)] (P₀ Q : Int) where
  /-- Concrete coordinate O2/AB/R provider for the four off-pin classes, retaining
  collar errors before the emptiness facts are applied. -/
  provider : V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError
    (β := β) (A := A) P₀ Q
  /-- The class-3 collar is literally empty on every pin-free deep context. -/
  class3Empty : forall (ctx : ActualFailureContext) (hX : 2 ^ 986891 < ctx.X)
    (hn2 : Not (OrbitBandPinned ctx 2)) (hn3 : Not (OrbitBandPinned ctx 3))
    (hn4 : Not (OrbitBandPinned ctx 4)),
      (provider.class3 ctx hX hn2 hn3 hn4).collar = ∅
  /-- The class-4 collar is literally empty on every pin-free deep context. -/
  class4Empty : forall (ctx : ActualFailureContext) (hX : 2 ^ 986891 < ctx.X)
    (hn2 : Not (OrbitBandPinned ctx 2)) (hn3 : Not (OrbitBandPinned ctx 3))
    (hn4 : Not (OrbitBandPinned ctx 4)),
      (provider.class4 ctx hX hn2 hn3 hn4).collar = ∅
  /-- The class-5 collar is literally empty on every pin-free deep context. -/
  class5Empty : forall (ctx : ActualFailureContext) (hX : 2 ^ 986891 < ctx.X)
    (hn2 : Not (OrbitBandPinned ctx 2)) (hn3 : Not (OrbitBandPinned ctx 3))
    (hn4 : Not (OrbitBandPinned ctx 4)),
      (provider.class5 ctx hX hn2 hn3 hn4).collar = ∅
  /-- The class-0 collar is literally empty on every class-0 survivor context. -/
  class0Empty : forall (ctx : ActualFailureContext) (hsurv : Class0DatumSurvivor ctx),
    (provider.class0 ctx hsurv).collar = ∅

namespace V30OffPinFullO2CollarSupplyCoordinateEmptyCollarSafeConeInputs

/-- Literal class-3 collar deletion implies the zero-cardinality hypothesis used
by the finite-error O2 endpoint surface. -/
theorem class3Zero {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (I : V30OffPinFullO2CollarSupplyCoordinateEmptyCollarSafeConeInputs
      (β := β) (A := A) P₀ Q) :
    forall (ctx : ActualFailureContext) (hX : 2 ^ 986891 < ctx.X)
      (hn2 : Not (OrbitBandPinned ctx 2)) (hn3 : Not (OrbitBandPinned ctx 3))
      (hn4 : Not (OrbitBandPinned ctx 4)),
        (I.provider.class3 ctx hX hn2 hn3 hn4).collar.card = 0 := by
  intro ctx hX hn2 hn3 hn4
  simp [I.class3Empty ctx hX hn2 hn3 hn4]

/-- Literal class-4 collar deletion implies the zero-cardinality hypothesis used
by the finite-error O2 endpoint surface. -/
theorem class4Zero {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (I : V30OffPinFullO2CollarSupplyCoordinateEmptyCollarSafeConeInputs
      (β := β) (A := A) P₀ Q) :
    forall (ctx : ActualFailureContext) (hX : 2 ^ 986891 < ctx.X)
      (hn2 : Not (OrbitBandPinned ctx 2)) (hn3 : Not (OrbitBandPinned ctx 3))
      (hn4 : Not (OrbitBandPinned ctx 4)),
        (I.provider.class4 ctx hX hn2 hn3 hn4).collar.card = 0 := by
  intro ctx hX hn2 hn3 hn4
  simp [I.class4Empty ctx hX hn2 hn3 hn4]

/-- Literal class-5 collar deletion implies the zero-cardinality hypothesis used
by the finite-error O2 endpoint surface. -/
theorem class5Zero {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (I : V30OffPinFullO2CollarSupplyCoordinateEmptyCollarSafeConeInputs
      (β := β) (A := A) P₀ Q) :
    forall (ctx : ActualFailureContext) (hX : 2 ^ 986891 < ctx.X)
      (hn2 : Not (OrbitBandPinned ctx 2)) (hn3 : Not (OrbitBandPinned ctx 3))
      (hn4 : Not (OrbitBandPinned ctx 4)),
        (I.provider.class5 ctx hX hn2 hn3 hn4).collar.card = 0 := by
  intro ctx hX hn2 hn3 hn4
  simp [I.class5Empty ctx hX hn2 hn3 hn4]

/-- Literal class-0 collar deletion implies the zero-cardinality hypothesis used
by the finite-error O2 endpoint surface. -/
theorem class0Zero {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (I : V30OffPinFullO2CollarSupplyCoordinateEmptyCollarSafeConeInputs
      (β := β) (A := A) P₀ Q) :
    forall (ctx : ActualFailureContext) (hsurv : Class0DatumSurvivor ctx),
      (I.provider.class0 ctx hsurv).collar.card = 0 := by
  intro ctx hsurv
  simp [I.class0Empty ctx hsurv]

/-- The packaged empty-collar provider is exactly a coordinate zero-collar
provider after reducing `collar = ∅` to `collar.card = 0`. -/
def toZeroCollarProvider {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (I : V30OffPinFullO2CollarSupplyCoordinateEmptyCollarSafeConeInputs
      (β := β) (A := A) P₀ Q) :
    V30OffPinFullO2CollarSupplyCoordinateSafeConeInputs (β := β) (A := A) P₀ Q :=
  V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError.toZeroCollarProvider
    I.provider (class3Zero I) (class4Zero I) (class5Zero I) (class0Zero I)

/-- The packaged empty-collar provider supplies the full off-pin safe-cone
regime. -/
theorem fullRegime {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (I : V30OffPinFullO2CollarSupplyCoordinateEmptyCollarSafeConeInputs
      (β := β) (A := A) P₀ Q) :
    V30OffPinFullRegime :=
  V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError.fullRegime_of_emptyCollars
    I.provider I.class3Empty I.class4Empty I.class5Empty I.class0Empty

/-- The packaged empty-collar provider supplies the no-error four-class C1
deliverable consumed by the endpoint. -/
theorem allClasses {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (I : V30OffPinFullO2CollarSupplyCoordinateEmptyCollarSafeConeInputs
      (β := β) (A := A) P₀ Q) :
    ExitMassControlOffPin ∧ MdcClass0ExitMassControl :=
  V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError.allClasses_of_emptyCollars
    I.provider I.class3Empty I.class4Empty I.class5Empty I.class0Empty

end V30OffPinFullO2CollarSupplyCoordinateEmptyCollarSafeConeInputs

/-! ## Part 6.  Corollary suppliers off the same exit-mass currency

These three feed sibling lanes from the SAME exit-mass safe-cone currency. -/

/-- **R4 densepack supplier** (`V30DensePackSupport` consumes this via
`v30SpanRarity_of_localExitLight`): a per-span exit-mass cap
`32·(r+1)·localExitMass(m) < L` supplies `K1LocalExitLight` — every width-`W` span is
exit-light `(r+1)·localExitMass < 2Y` (`Y = L/64`).  The densepack lane collapses onto
the (C1) exit-mass family. -/
theorem v30_localExitLight_of_cap (ctx : ActualFailureContext)
    (H : ∀ m : ℕ,
      32 * ((ctx.n24CarryData.r + 1) * k1acLocalExitMass ctx m) < shellLadderDepth ctx) :
    K1LocalExitLight ctx := by
  intro m
  rw [n24CarryData_Y_eq_div]
  have hR : (32 : ℝ) * (((ctx.n24CarryData.r + 1) * k1acLocalExitMass ctx m : ℕ) : ℝ)
      < ((shellLadderDepth ctx : ℕ) : ℝ) := by exact_mod_cast H m
  linarith

/-- The named R4 local-exit-light atom is exactly strong enough to recover the
numeric per-span cap form used by the localized endpoint supplier. -/
theorem v30_spanCap_of_localExitLight (ctx : ActualFailureContext)
    (H : K1LocalExitLight ctx) :
    ∀ m : ℕ,
      32 * ((ctx.n24CarryData.r + 1) * k1acLocalExitMass ctx m) < shellLadderDepth ctx := by
  intro m
  have hlight := H m
  rw [n24CarryData_Y_eq_div] at hlight
  have hR : (32 : ℝ) *
        (((ctx.n24CarryData.r + 1) * k1acLocalExitMass ctx m : ℕ) : ℝ)
      < ((shellLadderDepth ctx : ℕ) : ℝ) := by
    nlinarith
  exact_mod_cast hR

/-- The named R4 local-exit-light atom is equivalent to the numeric per-span
cap used by the localized endpoint surface. -/
theorem v30_localExitLight_iff_spanCap (ctx : ActualFailureContext) :
    Iff (K1LocalExitLight ctx)
      (forall m : Nat,
        32 * ((ctx.n24CarryData.r + 1) * k1acLocalExitMass ctx m) < shellLadderDepth ctx) := by
  constructor
  · exact v30_spanCap_of_localExitLight ctx
  · exact v30_localExitLight_of_cap ctx

/-- **R4 densepack span-rarity, end to end**: the per-span exit-mass cap (at band `≤ 4`)
supplies `K1SpanRarity` through the in-tree `v30SpanRarity_of_localExitLight` consumer —
the densepack disjointification on the exit-mass currency, no cluster floor / density /
SDR. -/
theorem v30_spanRarity_of_cap (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4)
    (H : ∀ m : ℕ,
      32 * ((ctx.n24CarryData.r + 1) * k1acLocalExitMass ctx m) < shellLadderDepth ctx) :
    K1SpanRarity ctx :=
  v30SpanRarity_of_localExitLight ctx hband (v30_localExitLight_of_cap ctx H)

/-- **Lane G R5 supplier**: a top-band exit-mass cap `64·agcTopBandDev ctx < L`
(with band `≤ 4`) supplies `V30TopBandPushforward` — the top-band L.3.1 exits routed
into the (R3) ledger sit below the heaviness floor `Y = L/64`. -/
theorem v30_topBandPushforward_of_cap
    (H : ∀ ctx : ActualFailureContext, fixedFamilyRecurrentBand ctx ≤ 4
        ∧ 64 * agcTopBandDev ctx < shellLadderDepth ctx) :
    V30TopBandPushforward := by
  intro ctx
  obtain ⟨hb, hcap⟩ := H ctx
  refine ⟨hb, ?_⟩
  rw [n24CarryData_Y_eq_div]
  have hR : (64 : ℝ) * (agcTopBandDev ctx : ℝ) < ((shellLadderDepth ctx : ℕ) : ℝ) := by
    exact_mod_cast hcap
  linarith

/-- Top-band exit-freeness supplies the numeric cap form used by the localized
R5 supplier.  Appendix P first proves that the unlocalized top-band exit family is
empty; the existing `dscTopBandDevLight_of_exitFree` turns that into
`agcTopBandDev < Y`, and `Y = L/64` gives the integer cap below. -/
theorem v30_topBandCap_of_exitFree
    (H : ∀ ctx : ActualFailureContext, fixedFamilyRecurrentBand ctx ≤ 4
        ∧ DscTopBandExitFree ctx) :
    ∀ ctx : ActualFailureContext, fixedFamilyRecurrentBand ctx ≤ 4
        ∧ 64 * agcTopBandDev ctx < shellLadderDepth ctx := by
  intro ctx
  refine ⟨(H ctx).1, ?_⟩
  have hlight : (agcTopBandDev ctx : ℝ) < ctx.n24CarryData.Y :=
    dscTopBandDevLight_of_exitFree ctx (H ctx).2
  rw [n24CarryData_Y_eq_div] at hlight
  have hR : (64 : ℝ) * (agcTopBandDev ctx : ℝ)
      < ((shellLadderDepth ctx : ℕ) : ℝ) := by
    nlinarith
  exact_mod_cast hR

/-- Band-following onsets at or below the top-band start are an in-tree source of
Appendix-P top-band exit-freeness, hence of the numeric R5 cap. -/
theorem v30_topBandCap_of_onsets
    (H : forall ctx : ActualFailureContext,
      And (fixedFamilyRecurrentBand ctx <= 4)
        (Exists (fun k1 : Nat =>
          And (k1 + (ctx.n24CarryData.r + 1) <= emF ctx + emW ctx)
            (forall k : Nat, k1 <= k ->
              hitGap ctx.n24CarryData.a k = fixedFamilyRecurrentBand ctx)))) :
    forall ctx : ActualFailureContext,
      And (fixedFamilyRecurrentBand ctx <= 4)
        (64 * agcTopBandDev ctx < shellLadderDepth ctx) :=
  v30_topBandCap_of_exitFree (mdcTopBandSlot_of_onsets H)

/-- **Lane G residual builder (R5 + R6)**: from a top-band exit-mass cap (supplying R5,
`V30TopBandPushforward`) and the named read-tail exit-count bridge (R6,
`V30ReadTailExitCount`, the four band-reading dispatcher inequalities) assemble the
Lane G residual `V30TopBandReadTailResidual`. -/
def v30_laneGResidual_of
    (htop : ∀ ctx : ActualFailureContext, fixedFamilyRecurrentBand ctx ≤ 4
        ∧ 64 * agcTopBandDev ctx < shellLadderDepth ctx)
    (hread : V30ReadTailExitCount) : V30TopBandReadTailResidual where
  topBand := v30_topBandPushforward_of_cap htop
  readTail := hread

/-- Appendix-P top-band exit-freeness plus the read-tail bridge assemble the
Lane-G residual without exposing the intermediate numeric top-band cap as a
separate endpoint input. -/
def v30_laneGResidual_of_topBandExitFree
    (htop : forall ctx : ActualFailureContext,
      And (fixedFamilyRecurrentBand ctx <= 4) (DscTopBandExitFree ctx))
    (hread : V30ReadTailExitCount) : V30TopBandReadTailResidual :=
  v30_laneGResidual_of (v30_topBandCap_of_exitFree htop) hread

/-- Lane-G residual from the concrete band-following onset supplier for R5. -/
def v30_laneGResidual_of_topBandOnsets
    (htop : forall ctx : ActualFailureContext,
      And (fixedFamilyRecurrentBand ctx <= 4)
        (Exists (fun k1 : Nat =>
          And (k1 + (ctx.n24CarryData.r + 1) <= emF ctx + emW ctx)
            (forall k : Nat, k1 <= k ->
              hitGap ctx.n24CarryData.a k = fixedFamilyRecurrentBand ctx))))
    (hread : V30ReadTailExitCount) : V30TopBandReadTailResidual :=
  v30_laneGResidual_of (v30_topBandCap_of_onsets htop) hread

/-- Endpoint form of the Lane-C/Lane-G handoff: the top-band cap and read-tail
bridge build the Lane-G residual and slot it into the convergence surface. -/
theorem v30Erdos260_of_laneGCap
    (htop : ∀ ctx : ActualFailureContext, fixedFamilyRecurrentBand ctx ≤ 4
        ∧ 64 * agcTopBandDev ctx < shellLadderDepth ctx)
    (hread : V30ReadTailExitCount) (other : Erdos260ConvergenceResidual) :
    Erdos260Statement :=
  v30Erdos260_of_other (v30_laneGResidual_of htop hread) other

/-- Endpoint form with Appendix-P top-band exit-freeness as the R5 source. -/
theorem v30Erdos260_of_laneGTopBandExitFree
    (htop : forall ctx : ActualFailureContext,
      And (fixedFamilyRecurrentBand ctx <= 4) (DscTopBandExitFree ctx))
    (hread : V30ReadTailExitCount) (other : Erdos260ConvergenceResidual) :
    Erdos260Statement :=
  v30Erdos260_of_other (v30_laneGResidual_of_topBandExitFree htop hread) other

/-- Endpoint form with band-following onsets as the R5 source. -/
theorem v30Erdos260_of_laneGTopBandOnsets
    (htop : forall ctx : ActualFailureContext,
      And (fixedFamilyRecurrentBand ctx <= 4)
        (Exists (fun k1 : Nat =>
          And (k1 + (ctx.n24CarryData.r + 1) <= emF ctx + emW ctx)
            (forall k : Nat, k1 <= k ->
              hitGap ctx.n24CarryData.a k = fixedFamilyRecurrentBand ctx))))
    (hread : V30ReadTailExitCount) (other : Erdos260ConvergenceResidual) :
    Erdos260Statement :=
  v30Erdos260_of_other (v30_laneGResidual_of_topBandOnsets htop hread) other

/-! ## Part 7.  Honest machine-readable status -/

/-- Machine-readable, honest status of the Lane C off-pin exit-mass cap (C1) pass. -/
def v30OffPinExitCapStatus : List String :=
  [ "LANE C (V30OffPinExitCap) — assembles the v30 direct off-pin exit-mass cap (C1), " ++
      "cor:ac-offpin-cap-closed (v30 line 11603), on top of the two built-green " ++
      "prerequisites (Lane B V30CycleMassBalance + Lane D-discharge V30RetirementDischarge). " ++
      "Additive: module-local V30 surface, no axiom/sorry shortcut.",
    "CONVERGENCE BRIDGE (PROVED): the in-tree descent order ctx.n24CarryData.r = floor(kappa*L) " ++
      "(scc_r_eq_floor) and Lane D's rActive L = floor(kappa*L) use the SAME manuscriptKappa, so " ++
      "v30_ctx_r_eq_rActive : ctx.n24CarryData.r = rActive (shellLadderDepth ctx), and Lane B's " ++
      "overlap cmbOverlap ctx c = floor((r+c)/c) is Lane D's overlap (v30_cmbOverlap_eq).",
    "UNSAFE CORE EMPTY, CONSUMED (PROVED): the exit-light long-cycle core (b=1, c>=64, " ++
      "1536*floor((r+c)/c) > 31*c) is EMPTY for live M.5/L.3 ledger fibres (D-discharge " ++
      "unsafeOffPinCoreSet_eq_empty / unsafeCore_empty_of_ledger_period, NO PriorityRouting hyp). " ++
      "Read positively: an exit-light long cycle is FORCED into the safe cone " ++
      "(v30_exitLight_ledger_safe CycleParams form / v30_ctx_exitLight_safe ctx form): a ledger " ++
      "survivor has c > P_hand*L so floor((r+c)/c) = 1, and 1536*1*1 = 1536 <= 31*c for c >= 64 " ++
      "(31*64 = 1984). NO proportional share. This is the v30 (C1) crux — the worst case the Lean " ++
      "program could never feed (EmcSpacedShareDatum unprovable) needs NEITHER RISK b nor RISK c.",
    "PER-CLASS (C1) ENGINE (PROVED, v30_offPin_classCap): band <= 4 + c-spacing + the " ++
      "mass-normalized balance c*ExitMass <= b*M_tot (RISK c) + safe cell 1536*(overlap*b) <= 31*c " ++
      "+ ambient M_tot <= X (RISK b) ==> routedClassMass_i <= emcCap = (31/1536)*X. Chain: " ++
      "emc2_classMass_le_fibreDevMass (band<=4) ∘ emc2_fibreDevMass_le_overlap (spacing) ∘ " ++
      "cmb_offPin_safeCone_cap (Lane B). Direct — NOT through the false emc2_offPin_of_regime / " ++
      "EmcSpacedShareDatum (the share c*fibreExit <= b*totalExit is refuted, AppendixRVerdict).",
    "DELIVERED: ExitMassControlOffPin (classes 3,4,5) via v30_offPinExitCap from " ++
      "V30OffPinSafeConeRegime; MdcClass0ExitMassControl (class 0) via " ++
      "v30_mdcClass0ExitMassControl_of_safeCone from V30Class0SafeConeRegime (Lane B cmb_safeCone_nat); " ++
      "BOTH together (all four off-pin classes {0,3,4,5}) via v30_offPin_allClasses from " ++
      "V30OffPinFullRegime — the AD-summed (C1) off-pin cap.",
    "RISK b VERDICT: NAMED (carried), NOT discharged. V30AmbientAccounting ctx Mtot := Mtot <= " ++
      "ctx.shell.X = the disjoint-cell ambient phase-mass bound (lem:ad-summed-ambient-support " ++
      "v30 11671 / lem:ab-ambient-support-bound 11187, phase-forgetting injectivity 11216-11218). " ++
      "In-tree shadow: support-count scc_supportShell_lt (W < (17/2^24)*X); the genuine measure-" ++
      "theoretic partition (no multiplicity) is NOT an in-tree atom. It is the 5th datum conjunct " ++
      "(v30_safeConeDatum_riskb_eq). O2 constructed-rectangle suppliers feed the no-remainder " ++
      "V30AmbientAccountingOn/unit surface; O2 collar suppliers feed the explicit finite-error " ++
      "V30AmbientAccountingWithErrorOn surface with error collar.card (or any E >= collar.card). " ++
      "The collar remainder is not erased: v30_offPin_classCap_withError and " ++
      "V30CycleO2CollarSupplyCoordinateSafeConeInputsWithError give the faithful cap " ++
      "with additive (31/1536)*collar.card error; MdcClass0ExitMassControlWithError and " ++
      "V30Class0O2CollarSupplyCoordinateSafeConeInputsWithError give the faithful class-0 " ++
      "finite-error inequality with right side 31*(X + collar.card). Only the zero-error " ++
      "lemmas recover V30AmbientAccounting / MdcClass0ExitMassControl. The full four-class " ++
      "nonzero-collar surface V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError " ++
      "packages exactly these finite-error deliverables without claiming the no-error endpoint; " ++
      "toZeroCollarProvider / fullRegime_of_zeroCollarProvider recover the existing zero-collar " ++
      "provider and V30OffPinFullRegime when the four collars are genuinely zero, and " ++
      "allClasses_of_zeroCollars is the corresponding bridge back to the no-error C1 deliverable; " ++
      "toZeroCollarProvider_of_emptyCollars / fullRegime_of_emptyCollars / " ++
      "allClasses_of_emptyCollars consume the TeX-style collar = empty-set facts and reduce " ++
      "them to the same card = 0 zero-collar API; " ++
      "V30OffPinFullO2CollarSupplyCoordinateEmptyCollarSafeConeInputs packages those " ++
      "empty-collar facts as the endpoint-facing provider. " ++
      "The packaged zero-collar C1 entry points are V30CycleO2CollarSupplySafeConeInputs, " ++
      "V30Class0O2CollarSupplySafeConeInputs, and the four-class " ++
      "V30OffPinFullO2CollarSupplySafeConeInputs, with coordinate-split counterparts ending in " ++
      "CollarSupplyCoordinateSafeConeInputs.",
    "RISK c VERDICT: word-level DISCHARGED, phase-mass lift NAMED (carried). " ++
      "V30MeasurePreservation ctx i b c Mtot := c*emcFibreExitMass ctx i <= b*Mtot = the discrete " ++
      "measure preservation balance (lem:r-cycle-map-preserves-measure v30 9110 / " ++
      "prop:r-exit-share-closed 9203). The WORD-LEVEL shadow IS proved in Lane B " ++
      "(cmb_windowExcess_cyclic, from c-periodicity of the gap word, reusing emcT_windowExcess_drift); " ++
      "the phase-mass lift is CARRIED (= CycleMassDatum.preserved). It is the 3rd datum conjunct " ++
      "(v30_safeConeDatum_riskc_eq). Provable from conservation alone; NOT (C1)-circular.",
    "RISK e (cell structure): the fibre c-spacing/period + band <= 4 — supplied by the AB finite " ++
      "recurrent-pair certificate (lem:ab-safe-complement-exhaustion 11315), carried in the datum. " ++
      "The safe-cell inequality is FREE for the exit-light long-cycle worst case via Lane D " ++
      "(v30_ctx_exitLight_safe); only the non-exit-light cells use the AB table classification.",
    "COROLLARY SUPPLIERS (PROVED, same exit-mass currency): (R4) v30_localExitLight_of_cap — a " ++
      "per-span exit cap 32*(r+1)*localExitMass(m) < L supplies K1LocalExitLight, and " ++
      "v30_spanCap_of_localExitLight recovers the numeric cap from that named atom; " ++
      "v30_localExitLight_iff_spanCap records the exact equivalence for endpoint reuse; " ++
      "V30DensePackSupport.v30SpanRarity_of_localExitLight gives the end-to-end " ++
      "v30_spanRarity_of_cap -> K1SpanRarity. (R5) v30_topBandCap_of_exitFree turns Appendix-P top-band " ++
      "exit-freeness into the numeric cap 64*agcTopBandDev < L; " ++
      "v30_topBandPushforward_of_cap then supplies V30TopBandPushforward. " ++
      "(R6) v30_laneGResidual_of — builds the Lane G " ++
      "residual V30TopBandReadTailResidual from the R5 cap + the named V30ReadTailExitCount bridge; " ++
      "v30_laneGResidual_of_topBandExitFree and v30Erdos260_of_laneGTopBandExitFree expose " ++
      "the same handoff with Appendix-P DscTopBandExitFree as the R5 source; " ++
      "v30_topBandCap_of_onsets / v30_laneGResidual_of_topBandOnsets additionally compose " ++
      "the MissDistanceClosure band-following onset supplier into this endpoint.",
    "ORBIT PINS: NOT supplied here (DeepOrbitPinVoiding is voided by the in-tree period-bound route, " ++
      "Lane D / Appendix U); this module supplies only the OFF-PIN cap (the pin-free conjunct of " ++
      "exitMassControl_iff_split).",
    "WHAT REMAINS for a fully unconditional erdos260_of_v30Residual (Lane H): supply the concrete " ++
      "V30OffPinFullO2SafeConeInputs data, i.e. V30MeasurePreservation (RISK c phase-mass lift), " ++
      "O2SupplyEmbedding constructed-rectangle data for V30AmbientAccounting (RISK b), or collar " ++
      "data plus a genuine zero/absorbed-error argument before the finite-error cap can be " ++
      "turned into the no-error C1 endpoint " ++
      "(the zero-collar four-class case is packaged by " ++
      "V30OffPinFullO2CollarSupplySafeConeInputs and its coordinate-split counterpart), and the AB " ++
      "cell structure (RISK e) " ++
      "per off-pin cell, to instantiate V30OffPinFullRegime; " ++
      "then wire ExitMassControlOffPin + MdcClass0ExitMassControl (+ class-1 R2 from Lane A) through " ++
      "exitMassControl_iff_split / the keystone reduction.",
    "AXIOMS: every key declaration reports exactly [propext, Classical.choice, Quot.sound] or fewer; " ++
      "no sorry / admit / native_decide; no new axiom." ]

/-- The status ledger is non-empty (honest, non-vacuous). -/
theorem v30OffPinExitCapStatus_nonempty : v30OffPinExitCapStatus ≠ [] := by
  unfold v30OffPinExitCapStatus
  simp

/-! ## Part 8.  Axiom-cleanliness audit
Every key declaration; expected axioms `[propext, Classical.choice, Quot.sound]` or
fewer. -/

#print axioms v30_ctx_r_eq_rActive
#print axioms v30_cmbOverlap_eq
#print axioms v30_unit_overlap_of_gt_threshold
#print axioms v30_exitLight_ledger_safe
#print axioms v30_ctx_exitLight_safe
#print axioms v30_unsafeOffPinCore_empty
#print axioms v30_offPin_classCap
#print axioms v30_offPin_classCap_exitLight
#print axioms V30OffPinClassCapWithError
#print axioms v30_offPin_classCap_of_withError_zero
#print axioms v30_offPin_classCap_of_datum
#print axioms V30AmbientAccountingOn
#print axioms v30AmbientAccountingOn_of_o2_summed_carrier
#print axioms v30AmbientAccounting_of_o2_summed_unit_carrier
#print axioms v30AmbientAccountingOn_of_o2_supply_inputs
#print axioms v30AmbientAccountingOn_of_o2_supply_coordinate_inputs
#print axioms v30AmbientAccounting_of_o2_supply_unit_inputs
#print axioms v30AmbientAccounting_of_o2_supply_coordinate_unit_inputs
#print axioms v30AmbientAccounting_of_o2_unit_carrier
#print axioms V30AmbientAccountingWithErrorOn
#print axioms V30AmbientAccountingWithError
#print axioms v30AmbientAccounting_of_withError_zero
#print axioms v30AmbientAccountingOn_of_withErrorOn_zero
#print axioms v30AmbientAccounting_of_withErrorOn_unit_zero
#print axioms v30_offPin_classCap_withError
#print axioms v30AmbientAccountingWithErrorOn_of_o2_collar_supply_inputs
#print axioms v30AmbientAccountingWithErrorOn_of_o2_collar_supply_inputs_with_error
#print axioms v30AmbientAccountingWithErrorOn_of_o2_collar_supply_coordinate_inputs
#print axioms v30AmbientAccountingWithErrorOn_of_o2_collar_supply_coordinate_inputs_with_error
#print axioms v30AmbientAccountingWithError_of_o2_collar_supply_unit_inputs
#print axioms v30AmbientAccountingWithError_of_o2_collar_supply_unit_inputs_with_error
#print axioms v30AmbientAccountingWithError_of_o2_collar_supply_coordinate_unit_inputs
#print axioms v30AmbientAccountingWithError_of_o2_collar_supply_coordinate_unit_inputs_with_error
#print axioms v30AmbientAccountingOn_of_o2_collar_supply_inputs_zero_collar
#print axioms v30AmbientAccountingOn_of_o2_collar_supply_inputs_empty_collar
#print axioms v30AmbientAccounting_of_o2_collar_supply_unit_inputs_zero_collar
#print axioms v30AmbientAccounting_of_o2_collar_supply_unit_inputs_empty_collar
#print axioms v30AmbientAccountingOn_of_o2_collar_supply_coordinate_inputs_zero_collar
#print axioms v30AmbientAccountingOn_of_o2_collar_supply_coordinate_inputs_empty_collar
#print axioms v30AmbientAccounting_of_o2_collar_supply_coordinate_unit_inputs_zero_collar
#print axioms v30AmbientAccounting_of_o2_collar_supply_coordinate_unit_inputs_empty_collar
#print axioms v30_safeConeDatum_of_measure_o2_unit_carrier
#print axioms v30_safeConeDatum_of_measure_o2_supply_unit_inputs
#print axioms v30_offPin_classCap_of_measure_o2_supply_unit_inputs
#print axioms v30_safeConeDatum_of_measure_o2_supply_coordinate_unit_inputs
#print axioms v30_offPin_classCap_of_measure_o2_supply_coordinate_unit_inputs
#print axioms V30OffPinSafeConeDatumWithError
#print axioms v30_safeConeDatum_of_withError_zero
#print axioms v30_offPin_classCap_withError_of_datum
#print axioms v30_safeConeDatumWithError_of_measure_ambient
#print axioms v30_safeConeDatumWithError_of_measure_o2_collar_supply_coordinate_unit_inputs
#print axioms v30_offPin_classCapWithError_of_measure_o2_collar_supply_coordinate_unit_inputs
#print axioms v30_measurePreservation_of_cycleDatum
#print axioms v30_safeConeDatum_of_cycleDatum_ambient
#print axioms v30_offPin_classCap_of_cycleDatum_ambient
#print axioms v30_safeConeDatum_of_cycleDatum_o2_unit_carrier
#print axioms v30_offPin_classCap_of_cycleDatum_o2_unit_carrier
#print axioms v30_exitLight_safeConeDatum_of_cycleDatum_o2_unit_carrier
#print axioms v30_offPin_classCap_exitLight_of_cycleDatum_o2_unit_carrier
#print axioms V30CycleO2SafeConeInputs
#print axioms V30CycleO2SafeConeInputs.measurePreservation
#print axioms V30CycleO2SafeConeInputs.ambientAccounting
#print axioms V30CycleO2SafeConeInputs.safeConeDatum
#print axioms V30CycleO2SafeConeInputs.classCap
#print axioms V30CycleO2SafeConeInputs.exitLightSafeConeDatum
#print axioms V30CycleO2SafeConeInputs.exitLightClassCap
#print axioms V30CycleO2SupplySafeConeInputs
#print axioms V30CycleO2SupplySafeConeInputs.measurePreservation
#print axioms V30CycleO2SupplySafeConeInputs.ambientAccounting
#print axioms V30CycleO2SupplySafeConeInputs.safeConeDatum
#print axioms V30CycleO2SupplySafeConeInputs.classCap
#print axioms V30CycleO2SupplySafeConeInputs.exitLightSafeConeDatum
#print axioms V30CycleO2SupplySafeConeInputs.exitLightClassCap
#print axioms V30CycleO2CollarSupplySafeConeInputs
#print axioms V30CycleO2CollarSupplySafeConeInputs.measurePreservation
#print axioms V30CycleO2CollarSupplySafeConeInputs.ambientAccounting
#print axioms V30CycleO2CollarSupplySafeConeInputs.safeConeDatum
#print axioms V30CycleO2CollarSupplySafeConeInputs.classCap
#print axioms V30CycleO2CollarSupplySafeConeInputs.exitLightSafeConeDatum
#print axioms V30CycleO2CollarSupplySafeConeInputs.exitLightClassCap
#print axioms V30CycleO2CollarSupplyCoordinateSafeConeInputs
#print axioms V30CycleO2CollarSupplyCoordinateSafeConeInputs.measurePreservation
#print axioms V30CycleO2CollarSupplyCoordinateSafeConeInputs.ambientAccounting
#print axioms V30CycleO2CollarSupplyCoordinateSafeConeInputs.safeConeDatum
#print axioms V30CycleO2CollarSupplyCoordinateSafeConeInputs.classCap
#print axioms V30CycleO2CollarSupplyCoordinateSafeConeInputs.exitLightSafeConeDatum
#print axioms V30CycleO2CollarSupplyCoordinateSafeConeInputs.exitLightClassCap
#print axioms V30CycleO2CollarSupplyCoordinateSafeConeInputsWithError
#print axioms V30CycleO2CollarSupplyCoordinateSafeConeInputsWithError.measurePreservation
#print axioms V30CycleO2CollarSupplyCoordinateSafeConeInputsWithError.ambientAccountingWithError
#print axioms V30CycleO2CollarSupplyCoordinateSafeConeInputsWithError.safeConeDatumWithError
#print axioms V30CycleO2CollarSupplyCoordinateSafeConeInputsWithError.classCapWithError
#print axioms V30CycleO2CollarSupplyCoordinateSafeConeInputsWithError.toZeroCollar
#print axioms v30_exitLight_safeConeDatum_of_cycleDatum_ambient
#print axioms v30_offPin_classCap_exitLight_of_cycleDatum_ambient
#print axioms v30_offPinExitCap
#print axioms v30_mdcClass0ExitMassControl_of_safeCone
#print axioms MdcClass0ExitMassControlWithError
#print axioms V30Class0SafeConeRegimeWithError
#print axioms v30_mdcClass0ExitMassControl_withError_of_safeCone
#print axioms v30_mdcClass0ExitMassControl_of_withError_zero
#print axioms v30Class0SafeConeRegime_of_withError_zero
#print axioms V30Class0O2SafeConeInputs
#print axioms V30Class0O2SafeConeInputs.ambientAccounting
#print axioms V30Class0O2SafeConeInputs.safeConeWitness
#print axioms v30Class0SafeConeRegime_of_o2_unit_provider
#print axioms v30_mdcClass0ExitMassControl_of_o2_unit_provider
#print axioms V30Class0O2SupplySafeConeInputs
#print axioms V30Class0O2SupplySafeConeInputs.ambientAccounting
#print axioms V30Class0O2SupplySafeConeInputs.safeConeWitness
#print axioms v30Class0SafeConeRegime_of_o2_supply_provider
#print axioms v30_mdcClass0ExitMassControl_of_o2_supply_provider
#print axioms V30Class0O2CollarSupplySafeConeInputs
#print axioms V30Class0O2CollarSupplySafeConeInputs.ambientAccounting
#print axioms V30Class0O2CollarSupplySafeConeInputs.safeConeWitness
#print axioms v30Class0SafeConeRegime_of_o2_collar_supply_provider
#print axioms v30_mdcClass0ExitMassControl_of_o2_collar_supply_provider
#print axioms V30Class0O2CollarSupplyCoordinateSafeConeInputs
#print axioms V30Class0O2CollarSupplyCoordinateSafeConeInputs.ambientAccounting
#print axioms V30Class0O2CollarSupplyCoordinateSafeConeInputs.safeConeWitness
#print axioms v30Class0SafeConeRegime_of_o2_collar_supply_coordinate_provider
#print axioms v30_mdcClass0ExitMassControl_of_o2_collar_supply_coordinate_provider
#print axioms V30Class0O2CollarSupplyCoordinateSafeConeInputsWithError
#print axioms V30Class0O2CollarSupplyCoordinateSafeConeInputsWithError.ambientAccountingWithError
#print axioms V30Class0O2CollarSupplyCoordinateSafeConeInputsWithError.safeConeWitnessWithError
#print axioms V30Class0O2CollarSupplyCoordinateSafeConeInputsWithError.exitMassControlWithError
#print axioms V30Class0O2CollarSupplyCoordinateSafeConeInputsWithError.toZeroCollar
#print axioms V30OffPinFullO2SafeConeInputs
#print axioms V30OffPinFullO2SafeConeInputs.offPinRegime
#print axioms V30OffPinFullO2SafeConeInputs.class0Regime
#print axioms v30OffPinFullRegime_of_o2_full_provider
#print axioms v30_offPin_allClasses
#print axioms v30_offPin_allClasses_of_o2_full_provider
#print axioms V30OffPinFullO2SupplySafeConeInputs
#print axioms V30OffPinFullO2SupplySafeConeInputs.offPinRegime
#print axioms V30OffPinFullO2SupplySafeConeInputs.class0Regime
#print axioms v30OffPinFullRegime_of_o2_supply_full_provider
#print axioms v30_offPin_allClasses_of_o2_supply_full_provider
#print axioms V30OffPinFullO2CollarSupplySafeConeInputs
#print axioms V30OffPinFullO2CollarSupplySafeConeInputs.offPinRegime
#print axioms V30OffPinFullO2CollarSupplySafeConeInputs.class0Regime
#print axioms v30OffPinFullRegime_of_o2_collar_supply_full_provider
#print axioms v30_offPin_allClasses_of_o2_collar_supply_full_provider
#print axioms V30OffPinFullO2CollarSupplyCoordinateSafeConeInputs
#print axioms V30OffPinFullO2CollarSupplyCoordinateSafeConeInputs.offPinRegime
#print axioms V30OffPinFullO2CollarSupplyCoordinateSafeConeInputs.class0Regime
#print axioms v30OffPinFullRegime_of_o2_collar_supply_coordinate_full_provider
#print axioms v30_offPin_allClasses_of_o2_collar_supply_coordinate_full_provider
#print axioms V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError
#print axioms V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError.class3CapWithError
#print axioms V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError.class4CapWithError
#print axioms V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError.class5CapWithError
#print axioms V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError.class0ExitMassControlWithError
#print axioms V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError.finiteErrorDeliverables
#print axioms V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError.toZeroCollarProvider
#print axioms V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError.fullRegime_of_zeroCollarProvider
#print axioms V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError.offPinExitCap_of_zeroCollars
#print axioms V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError.class0ExitMassControl_of_zeroCollars
#print axioms V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError.allClasses_of_zeroCollars
#print axioms V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError.toZeroCollarProvider_of_emptyCollars
#print axioms V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError.fullRegime_of_emptyCollars
#print axioms V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError.allClasses_of_emptyCollars
#print axioms V30OffPinFullO2CollarSupplyCoordinateEmptyCollarSafeConeInputs
#print axioms V30OffPinFullO2CollarSupplyCoordinateEmptyCollarSafeConeInputs.class3Zero
#print axioms V30OffPinFullO2CollarSupplyCoordinateEmptyCollarSafeConeInputs.class4Zero
#print axioms V30OffPinFullO2CollarSupplyCoordinateEmptyCollarSafeConeInputs.class5Zero
#print axioms V30OffPinFullO2CollarSupplyCoordinateEmptyCollarSafeConeInputs.class0Zero
#print axioms V30OffPinFullO2CollarSupplyCoordinateEmptyCollarSafeConeInputs.toZeroCollarProvider
#print axioms V30OffPinFullO2CollarSupplyCoordinateEmptyCollarSafeConeInputs.fullRegime
#print axioms V30OffPinFullO2CollarSupplyCoordinateEmptyCollarSafeConeInputs.allClasses
#print axioms v30_localExitLight_of_cap
#print axioms v30_spanCap_of_localExitLight
#print axioms v30_localExitLight_iff_spanCap
#print axioms v30_spanRarity_of_cap
#print axioms v30_topBandPushforward_of_cap
#print axioms v30_topBandCap_of_exitFree
#print axioms v30_topBandCap_of_onsets
#print axioms v30_laneGResidual_of
#print axioms v30_laneGResidual_of_topBandExitFree
#print axioms v30_laneGResidual_of_topBandOnsets
#print axioms v30Erdos260_of_laneGCap
#print axioms v30Erdos260_of_laneGTopBandExitFree
#print axioms v30Erdos260_of_laneGTopBandOnsets
#print axioms v30OffPinExitCapStatus_nonempty

end

end Erdos260
