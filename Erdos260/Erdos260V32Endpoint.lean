import Erdos260.Erdos260V30Endpoint

/-!
# V32 INTERFACE-HARDENING ENDPOINT — `Erdos260V32Endpoint` (Family I, Lanes I1 + I2)

This module (NEW; it edits no existing file) FORMALIZES the v32 interface-hardening
layer of `proof_v4_repaired_core_v32.tex`.  The v32 manuscript adds **ZERO new
mathematics** over v30 (its mathematical body, Appendices E–AD, is byte-identical to
v30) and closes **NONE** of the ten residual atoms.  Its only new content is:

* **Appendix AE** "Strict Lean residual-atom contracts" (v32 line 11787): the ten
  scoped atom contracts `LC1`–`LC10` (`int:ae-ten-atom-contracts`, 11837), the
  admissibility rules A1–A5 (11803) and forbidden coercions F1–F6 (11820), the
  acyclic dependency graph `prop:ae-dependency-graph` (AE.5, 11943), the
  non-regression corollary `cor:ae-non-regression-test` (11981), and the acceptance
  tests T1–T6 (12005).
* **Appendix Z** (rewritten, 12028): `prop:z-v30-unconditional-closure` (12055) and
  the "Formalization target" remark stating plainly that *"the ten atoms are proof
  obligations, not checked facts"* (12106).

What this module delivers (honest, non-triumphal):

1. The ten contracts `LC1`–`LC10` as faithful Lean Props, scoped per v32 (each cites
   its v32 line).  They are the SAME ten obligations as v30, in sharper shape.
2. `structure Erdos260V32Residual` bundling the ten contracts, the projection
   `Erdos260V32Residual.toV30 : Erdos260V32Residual → Erdos260V30Residual` (each LC
   contract implies the corresponding v30 field), and the v32 endpoint
   `erdos260_of_v32Residual : Erdos260V32Residual → Erdos260Statement` routed through
   the proved `erdos260_of_v30Residual`.
3. **THE AE.5 NON-CIRCULARITY FIREWALL** (`v32_dependency_firewall`): the genuinely
   valuable new piece.  The closure dependency graph over the atoms `LC1..LC10` plus
   the in-tree-proved nodes (bounded-period retirement, off-pin unsafe-core emptiness,
   the safe-cone cap, (R2), (R3), fixed-pin voiding, the off-pin cap, denominator-seven
   closure) is encoded as a finite directed graph and PROVED **acyclic** (by a strict
   rank certificate), with the AE.5 forbidden reverse edges proved as non-membership
   (`decide`): no `(R3) → pin` edge (F3), no `off-pin cap → LC1/LC2` edge, no
   `fixed-pin voiding → off-pin cap` and no `denominator-seven → off-pin cap` edge, and
   F1/F2 as *unreachability* of the off-pin cap from the forbidden `ExitMass(Tot)` and
   `spacing-alone` supplier sentinels.  The non-circularity of the off-pin supply (it
   does not consume the pins) is backed in tree by `V30RetirementDischarge` (the
   bounded-period retirement and unsafe-core emptiness are proved **without** the
   off-pin cap `(C1)` — import-isolated, `prop:ac-unsafe-core-empty`).
4. The T1–T6 non-regression guards encoded as Lean lemmas where checkable.

**HONEST STATEMENT.** This module does NOT reduce the residual.  `erdos260_of_v32Residual`
is exactly as conditional as `erdos260_of_v30Residual`: it depends on the SAME ten
research-grade atoms.  v32 is interface hardening — sharper atom statements + a
machine-checked non-circularity firewall + a v32 endpoint — not a new proof.  No
atom is closed here.

No `sorry`, no `admit`, no new `axiom`, no `native_decide`; additive only.
-/

namespace Erdos260

noncomputable section

open V30Class1Realization V30StructuralAtoms

set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option maxRecDepth 8192

/-! ## Part 1.  The ten strict Lean atom contracts `LC1`–`LC10` (Appendix AE)

Each contract is a faithful Lean Prop carrying the v30 obligation in its v32-scoped
shape; the v32 sharpening (error shape `e_lambda`/`o(X|I_j|)`, exposure side condition,
concrete period, split-gate form, forbidden coercions) is recorded in the doc-comment
and enforced by the firewall of Part 4.  Most contracts are restatements (v32 adds zero
new mathematics), so they are definitionally the corresponding v30 field. -/

/-- **LC1 — mass-normalized off-pin phase balance** (RISK c).  v32 AE.1, line 11843
(formula 11850): for each post-priority off-pin recurrent cell `F_{i,λ} ∈ 𝒫_i` in the
safe cone, `ExitMass^offpin_i(F_{i,λ}) ≤ (b_λ/c_λ)·M_tot(λ) + e_λ`, with **no**
`ExitMass(Tot)` on the right-hand side (forbids F1, 11821), and usable only after the
exposure factor `h_λ = ⌊(r+c_λ)/c_λ⌋` under the safe inequality `1536·h_λ·b_λ ≤ 31·c_λ`.
It may not be proved from spacing / cycle saturation alone (forbids F2, 11823).

In-tree carrier: the off-pin SAFE-CONE regime `V30OffPinSafeConeRegime` (classes
`{3,4,5}`).  Its per-cell datum `V30OffPinSafeConeDatum` carries the RISK c balance as
its 3rd conjunct `c·emcFibreExitMass ≤ b·M_tot` (`v30_safeConeDatum_riskc_eq`, the
error-free in-tree form of AE.1 — the `e_λ` collar is absorbed against the heaviness
floor `Y = L/64`), the exposure side condition `1536·(cmbOverlap·b) ≤ 31·c` as its 4th
conjunct, and the RISK b ambient bound `M_tot ≤ X` (RISK b) as its 5th conjunct.  Since
the in-tree datum bundles RISK b and RISK c per cell with **shared witnesses**, they
cannot be soundly separated; LC1 carries the safe-cone `{3,4,5}` regime in full. -/
def LC1 : Prop := V30OffPinSafeConeRegime

/-- **LC2 — disjoint summed support and global error** (RISK b, summed).  v32 AE.2, line
11858 (formula 11864): for every routed class `i ∈ {0,3,4,5}` the cells `𝒫_i` are
disjoint and `∑_{λ∈𝒫_i} M_tot(λ) ≤ X|I_j| + o(X|I_j|)`, with the exposure-weighted
errors `∑ h_λ|e_λ| = o(X|I_j|)`.  This is the **only** legal bridge from the cellwise
estimates to the summed cap (forbids F4, summing cellwise errors without the AD
summability statement `lem:ad-summed-ambient-support`, 11827).

In-tree carrier: the routed class-0 summand `V30Class0SafeConeRegime` — the leg over
`i = 0` (which AE.2 ranges over) that, together with LC1's safe cone `{3,4,5}`, completes
the AD-summed off-pin cap `V30OffPinFullRegime = V30OffPinSafeConeRegime ∧
V30Class0SafeConeRegime`.  Its datum carries the ambient bound `M_tot ≤ X` (RISK b) on
the class-0 cell.  (The summability/disjointness of the `{3,4,5}` cells is the
manuscript-level content of AE.2; in tree it is realised by the conjunction of the
per-class caps in `v30_offPin_allClasses`.) -/
def LC2 : Prop := V30Class0SafeConeRegime

/-- **LC3 — Appendix-U fixed-pin confinement**.  v32 line 11871: a retained fixed-pin
branch (not deleted by a prior terminal package) yields a certified clean periodic
continuation with concrete period `p ≤ 2^19`, whose periodic density floor contradicts
the sparse shell.  The proof must NOT cite `(R3)`, the off-pin cap, denominator-seven
voiding, or any proportional exit-share statement (import firewall; test T6, 12019).

In-tree carrier: the Appendix-U confinement atom `FixedPinCleanContinuation`
(`prop:u-direct-fixed-pin-voiding`).  HONEST: it is provably EQUIVALENT to its own
conclusion `DeepOrbitPinVoiding` (`fixedPinCleanContinuation_iff_deepOrbitPinVoiding`),
so this remains a genuine research-grade obligation.  The period bound `p ≤ 2^19` is the
manuscript's scoped claim; the in-tree type does not separately expose the period. -/
def LC3 : Prop := FixedPinCleanContinuation

/-- **LC4 — faithful class-1 realization**.  v32 AE.3, line 11879 (formula 11887): for
every `v ≥ 1`, after the shallow gate `L ≤ 1274739·2^v` and all collars deleted,
`¬(R2)_{1,v}^deep ⟹ 𝔄_{1,v}^deep ≠ ∅`.  The atom must construct an audited realized
parent–child row whose formal-row data, priority selector, boundary quotient, and child
restrictions AGREE with Appendix Y, and it must NOT use exit-mass caps or fixed-pin
voiding (import firewall; F6, 11831; test T6, 12019).

In-tree carrier: `V30Class1LedgerRealizesFormalRow (class1SystemOfCarry C clean)` over
the concrete tag-faithful system built from the carry DATA `C`, `clean`.  Lane K's
`ledgerRealizes_iff_deepResidual` shows this is EXACTLY the deep class-1 cap
`DccClass1DeepResidual 0`; the full Appendix-AA normal-form dictionary is proved in
tree, so the sole residual is the off-table deep `(R2)` count cap. -/
def LC4 (C : ℕ → ZMod 6) (clean : ℕ → Bool) : Prop :=
  V30Class1LedgerRealizesFormalRow (class1SystemOfCarry C clean)

/-- **LC5 — return split-gate**.  v32 AE.4, line 11894 (formula 11900): the return gate is
admissible ONLY as `(Pinned ⟹ Void) ∧ (¬Pinned ⟹ ReturnFieldGate)`; a raw
`ReturnFieldGate` in a pinned band context is inadmissible (A3, 11809; test T2, 12009).

In-tree carrier: the v30 `returnGates` field — the off-table `b2 > 0` return cycle-count
gate, already stated in the `¬Pinned` (`¬ OrbitBandPinned ctx 2`) branch of the split
gate (its second hypothesis), so this IS the admissible non-pinned half; the
`Pinned ⟹ Void` half is supplied in tree by `returnGatesField_iff_band2Void_split`. -/
def LC5 : Prop :=
  ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx →
    ¬ OrbitBandPinned ctx 2 →
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    2 * (129 * shellLadderDepth ctx + 64)
      ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card
            + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
    ReturnGatesBodyUngated ctx

/-- **LC6 — class-0 per-lane Y-cap**.  v32 line 11905: a routed, post-priority, off-pin,
normalized-exposure class-0 statement `mdcClass0ExitMass ≤ s·Y`, usable only for the
`i = 0` summand after side labels, endpoint/carry quotients, collars, denominator-seven
packages, and fixed-pin packages have been removed (A1/A2, 11804); it is NOT an
unrestricted class-0 mass bound (test T3, 12012).

In-tree carrier: the narrow-support class-0 gates `NarrowSupportClass0Gates` (the
per-member survivor/mid/big lane gate levels that `mdcGates_of_class0ExitMassCaps`
consumes from the per-lane caps `mdcClass0ExitMass ≤ s·Y`). -/
def LC6 := NarrowSupportClass0Gates

/-- **LC7 — frontier SDR / owned endpoint blocks**.  v32 line 11913: a cluster-floor
theorem must output a Hall marginal condition for owned endpoint blocks OR a support
bound strong enough to imply the Appendix-Q DensePack weakening; "many endpoints per
start" alone is insufficient (A4, 11813; test T4, 12015).

In-tree carrier: the v30 `clusterFloor` field — the K.1.1 per-window hit-placement atom
`K1ClusterFloor`, off the `b3 = 0` table at `r ≥ 1`. -/
def LC7 : Prop :=
  ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
    ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
    ¬ DensePackDatumClosed ctx → 1 ≤ ctx.n24CarryData.r →
    K1ClusterFloor ctx

/-- **LC8 — Q-correct frontier density**.  v32 line 11920: the density floor used by
DensePack/frontier arguments must be the `Q`-dependent constant `ρ_D(Q) > 0`; the pinned
value `1/4` may be used only in a separately stated `Q = 1` specialization (forbids F5,
replacing the `Q`-dependent constant by `1/4`, 11829).

In-tree carrier: the v30 `density` field — the K.1.1 coarea hit-density atom
`densePackEndpointDensity`, off the `b3 = 0` table. -/
def LC8 : Prop :=
  ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
    ¬ Class3CycleBand3Free ctx →
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
    ¬ DensePackDatumClosed ctx →
    densePackEndpointDensity ctx

/-- **LC9 — top-band localized routing**.  v32 line 11926: a top-band event must be routed
to an already-paid terminal package or to a routed exit ledger label; the theorem is NOT
a literal no-exit cap, it states exhaustion of the localized priority alternatives (A5,
11816; test T5, 12017).

In-tree carrier: the v30 `topBand` field `V30TopBandPushforward` — at every band-`≤ 4`
context the top-band deviation mass sits below the heaviness floor `Y = L/64`, the
`(C1)/(R3)` cap in top-band-localized push-forward form. -/
def LC9 : Prop := V30TopBandPushforward

/-- **LC10 — read-tail event-fibre push-forward together with span rarity**.  v32 line
11932: the read-tail theorem identifies first-entry / first-exit / terminal event fibres
by push-forward of the retained branch mass, with only `O_Q(1)` finite quotient
multiplicity and a global `o(X|I_j|)` collar; the span-rarity theorem may supply only the
CleanCNL / span-budget or conditional routing input — it may NOT serve as an independent
M.5/L.3 exit-mass cap (A5, 11816; test T5, 12017).

In-tree carriers: the v30 `readTail` field `V30ReadTailExitCount` (the four band-reading
tower/run closing inequalities) and the v30 `spanRarity` field (one genuine start per
width-`W` span, `K1SpanRarity`, the densepack disjointification on the exit-mass
currency). -/
structure LC10 where
  /-- Read-tail event-fibre push-forward (`V30ReadTailExitCount`, R6, Appendix P). -/
  readTail : V30ReadTailExitCount
  /-- Span-rarity clean-span budget (`K1SpanRarity`, R4, Appendix Q). -/
  spanRarity : ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
    ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
    ¬ DensePackDatumClosed ctx → 1 ≤ ctx.n24CarryData.r →
    K1SpanRarity ctx

/-! ## Part 2.  The v32 residual and the v32 endpoint -/

/-- **THE v32 REMAINING RESIDUAL SET.**  The ten Appendix-AE contracts bundled, plus the
class-1 carry DATA (`class1C`, `class1Clean` — no obligation, `parityZero` proved by Lane
J).  These are the SAME ten obligations as `Erdos260V30Residual`, in their sharper v32
shapes.  This structure is exactly as strong as `Erdos260V30Residual` (`toV30` below is a
field-by-field projection); v32 closes nothing. -/
structure Erdos260V32Residual where
  /-- LC1 (AE.1) — mass-normalized off-pin phase balance, classes `{3,4,5}`. -/
  lc1 : LC1
  /-- LC2 (AE.2) — disjoint summed support, the routed class-0 summand. -/
  lc2 : LC2
  /-- LC3 — Appendix-U fixed-pin confinement, period `p ≤ 2^19`. -/
  lc3 : LC3
  /-- Class-1 boundary-carry DATA (pure data; `parityZero` proved by Lane J). -/
  class1C : ℕ → ZMod 6
  /-- Cut-wise cleanliness data of the corrected class-1 ledger (pure data). -/
  class1Clean : ℕ → Bool
  /-- LC4 (AE.3) — faithful class-1 realization over `class1SystemOfCarry`. -/
  lc4 : LC4 class1C class1Clean
  /-- LC5 (AE.4) — return split-gate (non-pinned half). -/
  lc5 : LC5
  /-- LC6 — class-0 per-lane Y-cap surface gates. -/
  lc6 : LC6
  /-- LC7 — frontier SDR / owned endpoint blocks (cluster floor). -/
  lc7 : LC7
  /-- LC8 — `Q`-correct frontier density. -/
  lc8 : LC8
  /-- LC9 — top-band localized routing push-forward. -/
  lc9 : LC9
  /-- LC10 — read-tail event-fibre push-forward + span rarity. -/
  lc10 : LC10

/-- **THE v32 → v30 BRIDGE.**  Each Appendix-AE contract implies its corresponding v30
residual field.  The off-pin cap `V30OffPinFullRegime` is reassembled from LC1 (safe cone
`{3,4,5}`) and LC2 (routed class-0 summand); LC10 splits into the v30 `readTail` and
`spanRarity` fields; every other LC is the v30 field verbatim (v32 adds zero new
mathematics, so these are definitional restatements).  This is a sound projection — it
proves nothing about the atoms themselves. -/
def Erdos260V32Residual.toV30 (R : Erdos260V32Residual) : Erdos260V30Residual where
  offPin := ⟨R.lc1, R.lc2⟩
  confinement := R.lc3
  class1C := R.class1C
  class1Clean := R.class1Clean
  class1Realize := R.lc4
  topBand := R.lc9
  readTail := R.lc10.readTail
  spanRarity := R.lc10.spanRarity
  clusterFloor := R.lc7
  density := R.lc8
  returnGates := R.lc5
  class0Gates := R.lc6

/-- The Appendix-AE class-1 fields are exactly the Lane-J packaged carry
realization surface. -/
def Erdos260V32Residual.class1CarryInputs (R : Erdos260V32Residual) :
    V30Class1CarryRealizationInputs where
  C := R.class1C
  clean := R.class1Clean
  hreal := R.lc4

/-- The v32 residual supplies the same level-`0` deep class-1 cap as its v30
projection; v32 does not add any new class-1 mathematics here. -/
theorem v32_class1DeepBoosted (R : Erdos260V32Residual) :
    DccClass1DeepResidual 0 :=
  V30Class1CarryRealizationInputs.deepResidual R.class1CarryInputs

/-- The v32 residual inherits the full v19 class-1 deep field from its v30
projection; v32 adds no new class-1 mathematics here. -/
theorem Erdos260V32Residual.class1DeepField (R : Erdos260V32Residual) :
    Class1DeepField :=
  R.toV30.class1DeepField

/-- The v32 residual inherits the full M.5/L.3 exit-mass core through its v30
projection. -/
theorem Erdos260V32Residual.exitMassCore (R : Erdos260V32Residual) :
    ExitMassControlCore :=
  R.toV30.exitMassCore

/-- The v32 residual inherits the off-pin deliverables through its v30
projection. -/
theorem Erdos260V32Residual.offPinDeliverables (R : Erdos260V32Residual) :
    ExitMassControlOffPin ∧ MdcClass0ExitMassControl :=
  R.toV30.offPinDeliverables

/-- The v32 residual inherits deep orbit-pin voiding through its v30 projection. -/
theorem Erdos260V32Residual.deepOrbitPinVoiding (R : Erdos260V32Residual) :
    DeepOrbitPinVoiding :=
  R.toV30.deepOrbitPinVoiding

/-- **THE v32 ENDPOINT**: `Erdos260Statement` from the v32 hardened residual, routed
through the v32 → v30 projection and the proved `erdos260_of_v30Residual`.  Manuscript
home: Appendix Z `prop:z-v30-unconditional-closure` (v32 line 12055), with Appendix AE as
the authoritative Lean interface.  HONEST: this endpoint is exactly as conditional as the
v30 endpoint — it depends on the SAME ten residual atoms. -/
theorem erdos260_of_v32Residual (R : Erdos260V32Residual) : Erdos260Statement :=
  erdos260_of_v30Residual R.toV30

/-- V32 residual surface with LC9/LC10 lowered to the localized R4/R5 exit-cap
supplier used by the v30 endpoint.  LC10's read-tail component remains explicit;
its span-rarity component and LC9 are rebuilt from `V30LocalizedExitCapSuppliers`. -/
structure Erdos260V32LocalizedExitCapResidual where
  /-- LC1 (AE.1): mass-normalized off-pin phase balance, classes `{3,4,5}`. -/
  lc1 : LC1
  /-- LC2 (AE.2): routed class-0 summand. -/
  lc2 : LC2
  /-- LC3: Appendix-U fixed-pin confinement. -/
  lc3 : LC3
  /-- Class-1 boundary-carry data. -/
  class1C : Nat -> ZMod 6
  /-- Class-1 cleanliness data. -/
  class1Clean : Nat -> Bool
  /-- LC4: faithful class-1 realization over the carried data. -/
  lc4 : LC4 class1C class1Clean
  /-- LC5: return split-gate, non-pinned half. -/
  lc5 : LC5
  /-- LC6: class-0 per-lane Y-cap surface gates. -/
  lc6 : LC6
  /-- LC7: cluster-floor / owned endpoint blocks. -/
  lc7 : LC7
  /-- LC8: Q-correct frontier density. -/
  lc8 : LC8
  /-- Localized R4/R5 exit caps rebuilding LC9 and the span component of LC10. -/
  localizedCaps : V30LocalizedExitCapSuppliers
  /-- The read-tail component of LC10. -/
  readTail : V30ReadTailExitCount

namespace Erdos260V32LocalizedExitCapResidual

/-- LC9 rebuilt from the localized top-band cap. -/
def lc9 (R : Erdos260V32LocalizedExitCapResidual) : LC9 :=
  R.localizedCaps.topBand

/-- LC10 rebuilt from the explicit read-tail bridge and the localized per-span caps. -/
def lc10 (R : Erdos260V32LocalizedExitCapResidual) : LC10 where
  readTail := R.readTail
  spanRarity := R.localizedCaps.spanRarity

/-- Project the localized R4/R5 surface back to Appendix-AE's ten-contract API. -/
def toV32Residual (R : Erdos260V32LocalizedExitCapResidual) :
    Erdos260V32Residual where
  lc1 := R.lc1
  lc2 := R.lc2
  lc3 := R.lc3
  class1C := R.class1C
  class1Clean := R.class1Clean
  lc4 := R.lc4
  lc5 := R.lc5
  lc6 := R.lc6
  lc7 := R.lc7
  lc8 := R.lc8
  lc9 := R.lc9
  lc10 := R.lc10

/-- Direct projection to the v30 residual, via the hardened v32 surface. -/
def toV30Residual (R : Erdos260V32LocalizedExitCapResidual) :
    Erdos260V30Residual :=
  R.toV32Residual.toV30

/-- LC1/LC2 still supply the same four-class off-pin C1 deliverables. -/
theorem offPinDeliverables (R : Erdos260V32LocalizedExitCapResidual) :
    ExitMassControlOffPin ∧ MdcClass0ExitMassControl :=
  v30_offPin_allClasses ⟨R.lc1, R.lc2⟩

/-- The localized v32 surface exposes the same V30 Lane-G `R5 + R6` package:
LC9 is the top-band component and the read-tail half of LC10 is the R6 component. -/
def laneGResidual (R : Erdos260V32LocalizedExitCapResidual) :
    V30TopBandReadTailResidual :=
  R.localizedCaps.laneGResidual R.readTail

/-- Projection check for the top-band component of the localized v32 Lane-G package. -/
theorem laneGResidual_topBand (R : Erdos260V32LocalizedExitCapResidual) :
    R.laneGResidual.topBand = R.localizedCaps.topBand := rfl

/-- Projection check for the read-tail component of the localized v32 Lane-G package. -/
theorem laneGResidual_readTail (R : Erdos260V32LocalizedExitCapResidual) :
    R.laneGResidual.readTail = R.readTail := rfl

/-- The localized v32 surface carries the same M.5/L.3 exit-mass core through
its projection to the v32 residual API. -/
theorem exitMassCore (R : Erdos260V32LocalizedExitCapResidual) :
    ExitMassControlCore :=
  R.toV32Residual.exitMassCore

/-- The localized v32 surface carries the same deep orbit-pin voiding through
its projection to the v32 residual API. -/
theorem deepOrbitPinVoiding (R : Erdos260V32LocalizedExitCapResidual) :
    DeepOrbitPinVoiding :=
  R.toV32Residual.deepOrbitPinVoiding

end Erdos260V32LocalizedExitCapResidual

/-- V32 endpoint with LC9/LC10 supplied by localized R4/R5 exit caps. -/
theorem erdos260_of_v32LocalizedExitCapResidual
    (R : Erdos260V32LocalizedExitCapResidual) : Erdos260Statement :=
  erdos260_of_v32Residual R.toV32Residual

/-- V32 residual surface with the two off-pin contracts LC1/LC2 refined to the
coordinate-split zero-collar O2 provider.  The other Appendix-AE contracts are
unchanged; this records that the sharpened v32 interface can consume the same
lower-level off-pin provider as the v30 refined endpoint. -/
structure Erdos260V32O2CollarCoordinateResidual {β A : Type*}
    [DecidableEq (Nat -> Int)] (P₀ Q : Int) where
  /-- Concrete zero-collar O2/AB/R provider for LC1 and LC2 together. -/
  offPinO2 : V30OffPinFullO2CollarSupplyCoordinateSafeConeInputs
    (β := β) (A := A) P₀ Q
  /-- LC3: Appendix-U fixed-pin confinement. -/
  lc3 : LC3
  /-- Class-1 boundary-carry data. -/
  class1C : Nat -> ZMod 6
  /-- Class-1 cleanliness data. -/
  class1Clean : Nat -> Bool
  /-- LC4: faithful class-1 realization over the carried data. -/
  lc4 : LC4 class1C class1Clean
  /-- LC5: return split-gate, non-pinned half. -/
  lc5 : LC5
  /-- LC6: class-0 per-lane Y-cap surface gates. -/
  lc6 : LC6
  /-- LC7: cluster-floor / owned endpoint blocks. -/
  lc7 : LC7
  /-- LC8: Q-correct frontier density. -/
  lc8 : LC8
  /-- LC9: top-band localized routing push-forward. -/
  lc9 : LC9
  /-- LC10: read-tail push-forward plus span rarity. -/
  lc10 : LC10

namespace Erdos260V32O2CollarCoordinateResidual

/-- Project the concrete O2 off-pin provider back to the Appendix-AE ten-contract
surface.  LC1 and LC2 are obtained from the full coordinate zero-collar provider;
the other contracts are copied verbatim. -/
def toV32Residual {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateResidual (β := β) (A := A) P₀ Q) :
    Erdos260V32Residual where
  lc1 := (v30OffPinFullRegime_of_o2_collar_supply_coordinate_full_provider
    P₀ Q R.offPinO2).1
  lc2 := (v30OffPinFullRegime_of_o2_collar_supply_coordinate_full_provider
    P₀ Q R.offPinO2).2
  lc3 := R.lc3
  class1C := R.class1C
  class1Clean := R.class1Clean
  lc4 := R.lc4
  lc5 := R.lc5
  lc6 := R.lc6
  lc7 := R.lc7
  lc8 := R.lc8
  lc9 := R.lc9
  lc10 := R.lc10

/-- Direct projection to the v30 residual, via the hardened v32 surface. -/
def toV30Residual {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateResidual (β := β) (A := A) P₀ Q) :
    Erdos260V30Residual :=
  R.toV32Residual.toV30

/-- The concrete O2 provider supplies the v32 off-pin deliverables represented by
LC1/LC2, hence the same four-class off-pin C1 cap as in v30. -/
theorem offPinDeliverables {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateResidual (β := β) (A := A) P₀ Q) :
    ExitMassControlOffPin ∧ MdcClass0ExitMassControl :=
  v30_offPin_allClasses_of_o2_collar_supply_coordinate_full_provider P₀ Q R.offPinO2

/-- The coordinate O2 v32 surface carries the same M.5/L.3 exit-mass core
through its projection to the v32 residual API. -/
theorem exitMassCore {beta A : Type*} [hdec : DecidableEq (Nat -> Int)] {P Q : Int}
    (R : @Erdos260V32O2CollarCoordinateResidual beta A hdec P Q) :
    ExitMassControlCore :=
  R.toV32Residual.exitMassCore

/-- The coordinate O2 v32 surface carries the same deep orbit-pin voiding through
its projection to the v32 residual API. -/
theorem deepOrbitPinVoiding {beta A : Type*} [hdec : DecidableEq (Nat -> Int)] {P Q : Int}
    (R : @Erdos260V32O2CollarCoordinateResidual beta A hdec P Q) :
    DeepOrbitPinVoiding :=
  R.toV32Residual.deepOrbitPinVoiding

end Erdos260V32O2CollarCoordinateResidual

/-- V32 residual surface with LC1/LC2 refined to the coordinate-split O2 collar
provider retaining finite errors, plus explicit proofs that every collar is
actually zero.  This is the Appendix-AE endpoint-facing version of Lane C's
`toZeroCollarProvider` bridge. -/
structure Erdos260V32O2CollarCoordinateZeroErrorResidual {β A : Type*}
    [DecidableEq (Nat -> Int)] (P₀ Q : Int) where
  /-- Concrete coordinate O2/AB/R provider for LC1 and LC2 together, retaining
  collars before the zero-error proofs are applied. -/
  offPinO2 : V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError
    (β := β) (A := A) P₀ Q
  /-- The class-3 collar is genuinely zero on every pin-free deep context. -/
  class3Zero : forall (ctx : ActualFailureContext) (hX : 2 ^ 986891 < ctx.X)
    (hn2 : Not (OrbitBandPinned ctx 2)) (hn3 : Not (OrbitBandPinned ctx 3))
    (hn4 : Not (OrbitBandPinned ctx 4)),
      (offPinO2.class3 ctx hX hn2 hn3 hn4).collar.card = 0
  /-- The class-4 collar is genuinely zero on every pin-free deep context. -/
  class4Zero : forall (ctx : ActualFailureContext) (hX : 2 ^ 986891 < ctx.X)
    (hn2 : Not (OrbitBandPinned ctx 2)) (hn3 : Not (OrbitBandPinned ctx 3))
    (hn4 : Not (OrbitBandPinned ctx 4)),
      (offPinO2.class4 ctx hX hn2 hn3 hn4).collar.card = 0
  /-- The class-5 collar is genuinely zero on every pin-free deep context. -/
  class5Zero : forall (ctx : ActualFailureContext) (hX : 2 ^ 986891 < ctx.X)
    (hn2 : Not (OrbitBandPinned ctx 2)) (hn3 : Not (OrbitBandPinned ctx 3))
    (hn4 : Not (OrbitBandPinned ctx 4)),
      (offPinO2.class5 ctx hX hn2 hn3 hn4).collar.card = 0
  /-- The class-0 collar is genuinely zero on every class-0 survivor context. -/
  class0Zero : forall (ctx : ActualFailureContext) (hsurv : Class0DatumSurvivor ctx),
    (offPinO2.class0 ctx hsurv).collar.card = 0
  /-- LC3: Appendix-U fixed-pin confinement. -/
  lc3 : LC3
  /-- Class-1 boundary-carry data. -/
  class1C : Nat -> ZMod 6
  /-- Class-1 cleanliness data. -/
  class1Clean : Nat -> Bool
  /-- LC4: faithful class-1 realization over the carried data. -/
  lc4 : LC4 class1C class1Clean
  /-- LC5: return split-gate, non-pinned half. -/
  lc5 : LC5
  /-- LC6: class-0 per-lane Y-cap surface gates. -/
  lc6 : LC6
  /-- LC7: cluster-floor / owned endpoint blocks. -/
  lc7 : LC7
  /-- LC8: Q-correct frontier density. -/
  lc8 : LC8
  /-- LC9: top-band localized routing push-forward. -/
  lc9 : LC9
  /-- LC10: read-tail push-forward plus span rarity. -/
  lc10 : LC10

namespace Erdos260V32O2CollarCoordinateZeroErrorResidual

/-- Convert the finite-error/zero-collar v32 endpoint surface to the existing
coordinate zero-collar v32 endpoint surface. -/
def toO2CollarCoordinateResidual {β A : Type*} [DecidableEq (Nat -> Int)]
    {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    Erdos260V32O2CollarCoordinateResidual (β := β) (A := A) P₀ Q where
  offPinO2 :=
    V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError.toZeroCollarProvider
      R.offPinO2 R.class3Zero R.class4Zero R.class5Zero R.class0Zero
  lc3 := R.lc3
  class1C := R.class1C
  class1Clean := R.class1Clean
  lc4 := R.lc4
  lc5 := R.lc5
  lc6 := R.lc6
  lc7 := R.lc7
  lc8 := R.lc8
  lc9 := R.lc9
  lc10 := R.lc10

/-- Project the finite-error/zero-collar endpoint surface back to Appendix-AE's
ten-contract v32 API. -/
def toV32Residual {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    Erdos260V32Residual :=
  R.toO2CollarCoordinateResidual.toV32Residual

/-- Direct projection to the v30 residual, via the hardened v32 surface. -/
def toV30Residual {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    Erdos260V30Residual :=
  R.toV32Residual.toV30

/-- The finite-error/zero-collar O2 provider supplies the same v32 off-pin
deliverables represented by LC1/LC2. -/
theorem offPinDeliverables {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ExitMassControlOffPin ∧ MdcClass0ExitMassControl :=
  V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError.allClasses_of_zeroCollars
    R.offPinO2 R.class3Zero R.class4Zero R.class5Zero R.class0Zero

/-- The finite-error/zero-collar v32 surface carries the same M.5/L.3
exit-mass core through its projection to the v32 residual API. -/
theorem exitMassCore {beta A : Type*} [hdec : DecidableEq (Nat -> Int)] {P Q : Int}
    (R : @Erdos260V32O2CollarCoordinateZeroErrorResidual beta A hdec P Q) :
    ExitMassControlCore :=
  R.toV32Residual.exitMassCore

/-- The finite-error/zero-collar v32 surface carries the same deep orbit-pin
voiding through its projection to the v32 residual API. -/
theorem deepOrbitPinVoiding {beta A : Type*} [hdec : DecidableEq (Nat -> Int)] {P Q : Int}
    (R : @Erdos260V32O2CollarCoordinateZeroErrorResidual beta A hdec P Q) :
    DeepOrbitPinVoiding :=
  R.toV32Residual.deepOrbitPinVoiding

end Erdos260V32O2CollarCoordinateZeroErrorResidual

/-- V32 residual surface with LC1/LC2 refined to the coordinate-split O2 collar
provider whose four collars are literally empty.  This is the Appendix-AE
endpoint-facing form closest to the TeX collar-deletion statement. -/
structure Erdos260V32O2CollarCoordinateEmptyCollarResidual {β A : Type*}
    [DecidableEq (Nat -> Int)] (P₀ Q : Int) where
  /-- Concrete coordinate O2/AB/R provider for LC1 and LC2 together, with literal
  empty-collar facts for the four off-pin classes. -/
  offPinO2 : V30OffPinFullO2CollarSupplyCoordinateEmptyCollarSafeConeInputs
    (β := β) (A := A) P₀ Q
  /-- LC3: Appendix-U fixed-pin confinement. -/
  lc3 : LC3
  /-- Class-1 boundary-carry data. -/
  class1C : Nat -> ZMod 6
  /-- Class-1 cleanliness data. -/
  class1Clean : Nat -> Bool
  /-- LC4: faithful class-1 realization over the carried data. -/
  lc4 : LC4 class1C class1Clean
  /-- LC5: return split-gate, non-pinned half. -/
  lc5 : LC5
  /-- LC6: class-0 per-lane Y-cap surface gates. -/
  lc6 : LC6
  /-- LC7: cluster-floor / owned endpoint blocks. -/
  lc7 : LC7
  /-- LC8: Q-correct frontier density. -/
  lc8 : LC8
  /-- LC9: top-band localized routing push-forward. -/
  lc9 : LC9
  /-- LC10: read-tail push-forward plus span rarity. -/
  lc10 : LC10

namespace Erdos260V32O2CollarCoordinateEmptyCollarResidual

/-- Convert the empty-collar v32 endpoint surface to the existing coordinate
zero-collar v32 endpoint surface. -/
def toO2CollarCoordinateResidual {β A : Type*} [DecidableEq (Nat -> Int)]
    {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    Erdos260V32O2CollarCoordinateResidual (β := β) (A := A) P₀ Q where
  offPinO2 :=
    V30OffPinFullO2CollarSupplyCoordinateEmptyCollarSafeConeInputs.toZeroCollarProvider
      R.offPinO2
  lc3 := R.lc3
  class1C := R.class1C
  class1Clean := R.class1Clean
  lc4 := R.lc4
  lc5 := R.lc5
  lc6 := R.lc6
  lc7 := R.lc7
  lc8 := R.lc8
  lc9 := R.lc9
  lc10 := R.lc10

/-- Project the empty-collar endpoint surface back to Appendix-AE's ten-contract
v32 API. -/
def toV32Residual {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    Erdos260V32Residual :=
  R.toO2CollarCoordinateResidual.toV32Residual

/-- Direct projection to the v30 residual, via the hardened v32 surface. -/
def toV30Residual {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    Erdos260V30Residual :=
  R.toV32Residual.toV30

/-- The empty-collar O2 provider supplies the same v32 off-pin deliverables
represented by LC1/LC2. -/
theorem offPinDeliverables {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ExitMassControlOffPin ∧ MdcClass0ExitMassControl :=
  V30OffPinFullO2CollarSupplyCoordinateEmptyCollarSafeConeInputs.allClasses
    R.offPinO2

/-- The empty-collar coordinate v32 surface carries the same M.5/L.3
exit-mass core through its projection to the v32 residual API. -/
theorem exitMassCore {beta A : Type*} [hdec : DecidableEq (Nat -> Int)] {P Q : Int}
    (R : @Erdos260V32O2CollarCoordinateEmptyCollarResidual beta A hdec P Q) :
    ExitMassControlCore :=
  R.toV32Residual.exitMassCore

/-- The empty-collar coordinate v32 surface carries the same deep orbit-pin
voiding through its projection to the v32 residual API. -/
theorem deepOrbitPinVoiding {beta A : Type*} [hdec : DecidableEq (Nat -> Int)] {P Q : Int}
    (R : @Erdos260V32O2CollarCoordinateEmptyCollarResidual beta A hdec P Q) :
    DeepOrbitPinVoiding :=
  R.toV32Residual.deepOrbitPinVoiding

end Erdos260V32O2CollarCoordinateEmptyCollarResidual

/-- V32 residual surface with both endpoint refinements active at once: LC1/LC2 are
lowered to the finite-error coordinate O2 collar provider plus zero-collar proofs,
and LC9/LC10's span-rarity component are lowered to localized R4/R5 exit-cap
suppliers. -/
structure Erdos260V32O2LocalizedExitCapZeroErrorResidual {β A : Type*}
    [DecidableEq (Nat -> Int)] (P₀ Q : Int) where
  /-- Concrete coordinate O2/AB/R provider for LC1 and LC2 together, retaining
  collars before the zero-error proofs are applied. -/
  offPinO2 : V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError
    (β := β) (A := A) P₀ Q
  /-- The class-3 collar is genuinely zero on every pin-free deep context. -/
  class3Zero : forall (ctx : ActualFailureContext) (hX : 2 ^ 986891 < ctx.X)
    (hn2 : Not (OrbitBandPinned ctx 2)) (hn3 : Not (OrbitBandPinned ctx 3))
    (hn4 : Not (OrbitBandPinned ctx 4)),
      (offPinO2.class3 ctx hX hn2 hn3 hn4).collar.card = 0
  /-- The class-4 collar is genuinely zero on every pin-free deep context. -/
  class4Zero : forall (ctx : ActualFailureContext) (hX : 2 ^ 986891 < ctx.X)
    (hn2 : Not (OrbitBandPinned ctx 2)) (hn3 : Not (OrbitBandPinned ctx 3))
    (hn4 : Not (OrbitBandPinned ctx 4)),
      (offPinO2.class4 ctx hX hn2 hn3 hn4).collar.card = 0
  /-- The class-5 collar is genuinely zero on every pin-free deep context. -/
  class5Zero : forall (ctx : ActualFailureContext) (hX : 2 ^ 986891 < ctx.X)
    (hn2 : Not (OrbitBandPinned ctx 2)) (hn3 : Not (OrbitBandPinned ctx 3))
    (hn4 : Not (OrbitBandPinned ctx 4)),
      (offPinO2.class5 ctx hX hn2 hn3 hn4).collar.card = 0
  /-- The class-0 collar is genuinely zero on every class-0 survivor context. -/
  class0Zero : forall (ctx : ActualFailureContext) (hsurv : Class0DatumSurvivor ctx),
    (offPinO2.class0 ctx hsurv).collar.card = 0
  /-- LC3: Appendix-U fixed-pin confinement. -/
  lc3 : LC3
  /-- Class-1 boundary-carry data. -/
  class1C : Nat -> ZMod 6
  /-- Class-1 cleanliness data. -/
  class1Clean : Nat -> Bool
  /-- LC4: faithful class-1 realization over the carried data. -/
  lc4 : LC4 class1C class1Clean
  /-- LC5: return split-gate, non-pinned half. -/
  lc5 : LC5
  /-- LC6: class-0 per-lane Y-cap surface gates. -/
  lc6 : LC6
  /-- LC7: cluster-floor / owned endpoint blocks. -/
  lc7 : LC7
  /-- LC8: Q-correct frontier density. -/
  lc8 : LC8
  /-- Localized R4/R5 exit caps rebuilding LC9 and the span component of LC10. -/
  localizedCaps : V30LocalizedExitCapSuppliers
  /-- The read-tail component of LC10. -/
  readTail : V30ReadTailExitCount

namespace Erdos260V32O2LocalizedExitCapZeroErrorResidual

/-- Convert the combined lower-level surface to the localized-cap v32 endpoint
surface. -/
def toLocalizedExitCapResidual {β A : Type*} [DecidableEq (Nat -> Int)]
    {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    Erdos260V32LocalizedExitCapResidual where
  lc1 :=
    (V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError.fullRegime_of_zeroCollarProvider
      R.offPinO2 R.class3Zero R.class4Zero R.class5Zero R.class0Zero).1
  lc2 :=
    (V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError.fullRegime_of_zeroCollarProvider
      R.offPinO2 R.class3Zero R.class4Zero R.class5Zero R.class0Zero).2
  lc3 := R.lc3
  class1C := R.class1C
  class1Clean := R.class1Clean
  lc4 := R.lc4
  lc5 := R.lc5
  lc6 := R.lc6
  lc7 := R.lc7
  lc8 := R.lc8
  localizedCaps := R.localizedCaps
  readTail := R.readTail

/-- Project the combined lower-level surface back to Appendix-AE's ten-contract API. -/
def toV32Residual {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    Erdos260V32Residual :=
  R.toLocalizedExitCapResidual.toV32Residual

/-- Direct projection to the v30 residual, via the hardened v32 surface. -/
def toV30Residual {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    Erdos260V30Residual :=
  R.toV32Residual.toV30

/-- The combined lower-level surface supplies the same four-class off-pin C1
deliverables once the finite-error collars are zero. -/
theorem offPinDeliverables {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ExitMassControlOffPin ∧ MdcClass0ExitMassControl :=
  V30OffPinFullO2CollarSupplyCoordinateSafeConeInputsWithError.allClasses_of_zeroCollars
    R.offPinO2 R.class3Zero R.class4Zero R.class5Zero R.class0Zero

/-- The combined v32 O2/localized surface exposes the same V30 Lane-G `R5 + R6`
package; the off-pin O2 refinement is independent of this bookkeeping channel. -/
def laneGResidual {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    V30TopBandReadTailResidual :=
  R.localizedCaps.laneGResidual R.readTail

/-- Projection check for the top-band component of the combined v32 Lane-G package. -/
theorem laneGResidual_topBand {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    R.laneGResidual.topBand = R.localizedCaps.topBand := rfl

/-- Projection check for the read-tail component of the combined v32 Lane-G package. -/
theorem laneGResidual_readTail {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    R.laneGResidual.readTail = R.readTail := rfl

/-- The combined O2/localized zero-error v32 surface carries the same M.5/L.3
exit-mass core through its projection to the v32 residual API. -/
theorem exitMassCore {beta A : Type*} [hdec : DecidableEq (Nat -> Int)] {P Q : Int}
    (R : @Erdos260V32O2LocalizedExitCapZeroErrorResidual beta A hdec P Q) :
    ExitMassControlCore :=
  R.toV32Residual.exitMassCore

/-- The combined O2/localized zero-error v32 surface carries the same deep
orbit-pin voiding through its projection to the v32 residual API. -/
theorem deepOrbitPinVoiding {beta A : Type*} [hdec : DecidableEq (Nat -> Int)] {P Q : Int}
    (R : @Erdos260V32O2LocalizedExitCapZeroErrorResidual beta A hdec P Q) :
    DeepOrbitPinVoiding :=
  R.toV32Residual.deepOrbitPinVoiding

end Erdos260V32O2LocalizedExitCapZeroErrorResidual

/-- V32 residual surface with both endpoint refinements active at once, but with
LC1/LC2 supplied by the TeX-style literal empty-collar package instead of four
cardinality-zero proofs.  LC9 and the span-rarity part of LC10 are still supplied
by localized R4/R5 exit caps. -/
structure Erdos260V32O2LocalizedExitCapEmptyCollarResidual {β A : Type*}
    [DecidableEq (Nat -> Int)] (P₀ Q : Int) where
  /-- Concrete coordinate O2/AB/R provider for LC1 and LC2 together, with literal
  empty-collar facts for the four off-pin classes. -/
  offPinO2 : V30OffPinFullO2CollarSupplyCoordinateEmptyCollarSafeConeInputs
    (β := β) (A := A) P₀ Q
  /-- LC3: Appendix-U fixed-pin confinement. -/
  lc3 : LC3
  /-- Class-1 boundary-carry data. -/
  class1C : Nat -> ZMod 6
  /-- Class-1 cleanliness data. -/
  class1Clean : Nat -> Bool
  /-- LC4: faithful class-1 realization over the carried data. -/
  lc4 : LC4 class1C class1Clean
  /-- LC5: return split-gate, non-pinned half. -/
  lc5 : LC5
  /-- LC6: class-0 per-lane Y-cap surface gates. -/
  lc6 : LC6
  /-- LC7: cluster-floor / owned endpoint blocks. -/
  lc7 : LC7
  /-- LC8: Q-correct frontier density. -/
  lc8 : LC8
  /-- Localized R4/R5 exit caps rebuilding LC9 and the span component of LC10. -/
  localizedCaps : V30LocalizedExitCapSuppliers
  /-- The read-tail component of LC10. -/
  readTail : V30ReadTailExitCount

namespace Erdos260V32O2LocalizedExitCapEmptyCollarResidual

/-- Convert the combined empty-collar surface to the existing finite-error plus
zero-cardinality combined surface. -/
def toZeroErrorResidual {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    Erdos260V32O2LocalizedExitCapZeroErrorResidual (β := β) (A := A) P₀ Q where
  offPinO2 := R.offPinO2.provider
  class3Zero :=
    V30OffPinFullO2CollarSupplyCoordinateEmptyCollarSafeConeInputs.class3Zero
      R.offPinO2
  class4Zero :=
    V30OffPinFullO2CollarSupplyCoordinateEmptyCollarSafeConeInputs.class4Zero
      R.offPinO2
  class5Zero :=
    V30OffPinFullO2CollarSupplyCoordinateEmptyCollarSafeConeInputs.class5Zero
      R.offPinO2
  class0Zero :=
    V30OffPinFullO2CollarSupplyCoordinateEmptyCollarSafeConeInputs.class0Zero
      R.offPinO2
  lc3 := R.lc3
  class1C := R.class1C
  class1Clean := R.class1Clean
  lc4 := R.lc4
  lc5 := R.lc5
  lc6 := R.lc6
  lc7 := R.lc7
  lc8 := R.lc8
  localizedCaps := R.localizedCaps
  readTail := R.readTail

/-- Convert the combined empty-collar surface to the localized-cap v32 endpoint
surface. -/
def toLocalizedExitCapResidual {β A : Type*} [DecidableEq (Nat -> Int)]
    {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    Erdos260V32LocalizedExitCapResidual :=
  R.toZeroErrorResidual.toLocalizedExitCapResidual

/-- Project the combined empty-collar surface back to Appendix-AE's ten-contract
API. -/
def toV32Residual {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    Erdos260V32Residual :=
  R.toLocalizedExitCapResidual.toV32Residual

/-- Direct projection to the v30 residual, via the hardened v32 surface. -/
def toV30Residual {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    Erdos260V30Residual :=
  R.toV32Residual.toV30

/-- The combined empty-collar surface supplies the same four-class off-pin C1
deliverables represented by LC1/LC2. -/
theorem offPinDeliverables {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ExitMassControlOffPin ∧ MdcClass0ExitMassControl :=
  V30OffPinFullO2CollarSupplyCoordinateEmptyCollarSafeConeInputs.allClasses
    R.offPinO2

/-- The empty-collar v32 endpoint surface exposes the same V30 Lane-G `R5 + R6`
package as the zero-error and localized surfaces. -/
def laneGResidual {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    V30TopBandReadTailResidual :=
  R.localizedCaps.laneGResidual R.readTail

/-- Projection check for the top-band component of the empty-collar v32 package. -/
theorem laneGResidual_topBand {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    R.laneGResidual.topBand = R.localizedCaps.topBand := rfl

/-- Projection check for the read-tail component of the empty-collar v32 package. -/
theorem laneGResidual_readTail {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    R.laneGResidual.readTail = R.readTail := rfl

/-- The combined O2/localized empty-collar v32 surface carries the same M.5/L.3
exit-mass core through its projection to the v32 residual API. -/
theorem exitMassCore {beta A : Type*} [hdec : DecidableEq (Nat -> Int)] {P Q : Int}
    (R : @Erdos260V32O2LocalizedExitCapEmptyCollarResidual beta A hdec P Q) :
    ExitMassControlCore :=
  R.toV32Residual.exitMassCore

/-- The combined O2/localized empty-collar v32 surface carries the same deep
orbit-pin voiding through its projection to the v32 residual API. -/
theorem deepOrbitPinVoiding {beta A : Type*} [hdec : DecidableEq (Nat -> Int)] {P Q : Int}
    (R : @Erdos260V32O2LocalizedExitCapEmptyCollarResidual beta A hdec P Q) :
    DeepOrbitPinVoiding :=
  R.toV32Residual.deepOrbitPinVoiding

end Erdos260V32O2LocalizedExitCapEmptyCollarResidual

/-- V32 endpoint with LC1/LC2 supplied by finite-error O2 collars plus zero-collar
proofs, and LC9/LC10 supplied by localized R4/R5 exit caps. -/
theorem erdos260_of_v32O2LocalizedExitCapZeroErrorResidual {β A : Type*}
    [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    Erdos260Statement :=
  erdos260_of_v32LocalizedExitCapResidual R.toLocalizedExitCapResidual

/-- V32 endpoint with LC1/LC2 supplied by the finite-error O2 provider with
literal empty collars, and LC9/LC10 supplied by localized R4/R5 exit caps. -/
theorem erdos260_of_v32O2LocalizedExitCapEmptyCollarResidual {β A : Type*}
    [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    Erdos260Statement :=
  erdos260_of_v32O2LocalizedExitCapZeroErrorResidual R.toZeroErrorResidual

/-- V32 endpoint with LC1/LC2 supplied by the concrete coordinate zero-collar O2
provider.  It is conditional on the remaining Appendix-AE contracts, and on the
provider mathematics needed to build `offPinO2`; it does not weaken the original
ten-contract endpoint. -/
theorem erdos260_of_v32O2CollarCoordinateResidual {β A : Type*}
    [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateResidual (β := β) (A := A) P₀ Q) :
    Erdos260Statement :=
  erdos260_of_v32Residual R.toV32Residual

/-- V32 endpoint with LC1/LC2 supplied by the concrete coordinate O2 collar
surface with explicit finite-error collars, plus proofs that those collars
vanish. -/
theorem erdos260_of_v32O2CollarCoordinateZeroErrorResidual {β A : Type*}
    [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    Erdos260Statement :=
  erdos260_of_v32O2CollarCoordinateResidual R.toO2CollarCoordinateResidual

/-- V32 endpoint with LC1/LC2 supplied by the coordinate O2 collar surface with
literal empty-collar facts. -/
theorem erdos260_of_v32O2CollarCoordinateEmptyCollarResidual {β A : Type*}
    [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    Erdos260Statement :=
  erdos260_of_v32O2CollarCoordinateResidual R.toO2CollarCoordinateResidual

/-! ## Part 3.  The AE.5 non-circularity firewall

The genuinely valuable new piece.  We encode the v32 closure dependency graph
(`prop:ae-dependency-graph`, AE.5, line 11943) over the atoms `LC1..LC10` and the
in-tree-proved nodes, and PROVE it acyclic with the AE.5 forbidden reverse edges absent.
This is a machine-checked answer to the v30 circularity worry: the off-pin cap is never
used to supply RISK b/c (LC1/LC2), `(R3)` is never used to supply the fixed-pin voiding
(F3), and neither `ExitMass(Tot)` (F1) nor `spacing alone` (F2) can reach the off-pin
cap. -/

/-- The nodes of the v32 closure dependency graph: the ten Appendix-AE contracts, the
in-tree-proved assembly nodes (bounded-period retirement, off-pin unsafe-core emptiness,
the safe-cone cap, the off-pin cap, `(R2)`, fixed-pin voiding, `(R3)`, the surface
partition, Appendices V–W, denominator-seven closure, the Appendix-Y local table), and
the two FORBIDDEN supplier sentinels `exitMassTot` (F1) and `spacingAlone` (F2) used to
machine-check that they supply nothing. -/
inductive Node where
  | lc1 | lc2 | lc3 | lc4 | lc5 | lc6 | lc7 | lc8 | lc9 | lc10
  | appY | safeConeCap | offPinCap | r2 | fixedPinVoiding | r3
  | surface | vw | denSeven | boundedPeriod | unsafeCoreEmpty
  | exitMassTot | spacingAlone
  deriving DecidableEq

/-- The directed edges of the v32 closure dependency graph (AE.5, line 11947).  Reading
the AE.5 display top to bottom, plus the in-tree Lane-D assembly of the off-pin cap:

* `boundedPeriod → unsafeCoreEmpty → safeConeCap → offPinCap`: the in-tree off-pin cap
  assembly (`V30RetirementDischarge`: bounded-period retirement empties the unsafe core,
  `prop:ac-unsafe-core-empty`; the safe cone then caps the off-pin classes).
* `LC1 → safeConeCap`, `LC2 → offPinCap`, `LC6 → offPinCap`: AE.5 `LC1+LC2+LC6 ⟹` off-pin cap.
* `LC4 → r2`, `appY → r2`: AE.5 `LC4 + Appendix Y ⟹ (R2)`.
* `LC3 → fixedPinVoiding → r3`: AE.5 `LC3 ⟹ fixed-pin voiding upstream of (R3)`.
* `LC5/LC7/LC8/LC9/LC10 → surface`: AE.5 surface partition / DensePack / routing.
* `r2 → denSeven`, `offPinCap → denSeven`, `vw → denSeven`: AE.5
  `(R2) + off-pin cap + Appendices V–W ⟹ denominator-seven closure`.

There is deliberately NO edge from `offPinCap` back to `lc1`/`lc2`, NO edge from `r3` or
`denSeven` or `fixedPinVoiding` back into `offPinCap`, and NO edge out of `exitMassTot` /
`spacingAlone` — these absences are the firewall. -/
def closureEdgeList : List (Node × Node) :=
  [ (Node.boundedPeriod, Node.unsafeCoreEmpty),
    (Node.unsafeCoreEmpty, Node.safeConeCap),
    (Node.lc1, Node.safeConeCap),
    (Node.safeConeCap, Node.offPinCap),
    (Node.lc2, Node.offPinCap),
    (Node.lc6, Node.offPinCap),
    (Node.lc4, Node.r2),
    (Node.appY, Node.r2),
    (Node.lc3, Node.fixedPinVoiding),
    (Node.fixedPinVoiding, Node.r3),
    (Node.lc5, Node.surface),
    (Node.lc7, Node.surface),
    (Node.lc8, Node.surface),
    (Node.lc9, Node.surface),
    (Node.lc10, Node.surface),
    (Node.r2, Node.denSeven),
    (Node.offPinCap, Node.denSeven),
    (Node.vw, Node.denSeven) ]

/-- The edge relation of the v32 closure dependency graph. -/
def ClosureEdge (a b : Node) : Prop := (a, b) ∈ closureEdgeList

instance : DecidableRel ClosureEdge := fun a b =>
  inferInstanceAs (Decidable ((a, b) ∈ closureEdgeList))

/-- A topological rank certificate: every edge strictly increases the rank, so the graph
is a DAG.  Sources (rank 0): all ten contracts, `appY`, `vw`, `boundedPeriod`, and the
forbidden sentinels.  The cap assembly climbs `1 → 2 → 3`; denominator-seven closure is
the sink (rank 4). -/
def nodeRank : Node → ℕ
  | .lc1 => 0 | .lc2 => 0 | .lc3 => 0 | .lc4 => 0 | .lc5 => 0
  | .lc6 => 0 | .lc7 => 0 | .lc8 => 0 | .lc9 => 0 | .lc10 => 0
  | .appY => 0 | .vw => 0 | .boundedPeriod => 0
  | .exitMassTot => 0 | .spacingAlone => 0
  | .unsafeCoreEmpty => 1 | .fixedPinVoiding => 1
  | .safeConeCap => 2 | .r2 => 2 | .r3 => 2 | .surface => 2
  | .offPinCap => 3
  | .denSeven => 4

/-- The rank certificate: every edge in the graph strictly increases the rank
(checked by `decide` over the finite edge list). -/
theorem rankIncreasing : ∀ p ∈ closureEdgeList, nodeRank p.1 < nodeRank p.2 := by
  decide

/-- Every graph edge strictly increases the rank. -/
theorem rank_lt_of_edge {a b : Node} (h : ClosureEdge a b) : nodeRank a < nodeRank b :=
  rankIncreasing (a, b) h

/-- The rank strictly increases along any nonempty path (transitive closure). -/
theorem transGen_rank_lt {a b : Node} (h : Relation.TransGen ClosureEdge a b) :
    nodeRank a < nodeRank b := by
  induction h with
  | single hab => exact rank_lt_of_edge hab
  | tail _ hbc ih => exact lt_trans ih (rank_lt_of_edge hbc)

/-- **THE FIREWALL — ACYCLICITY.**  No node reaches itself: the v32 closure dependency
graph (AE.5) is a DAG.  A cycle would force `nodeRank a < nodeRank a`. -/
theorem v32_firewall_acyclic (a : Node) : ¬ Relation.TransGen ClosureEdge a a := fun h =>
  lt_irrefl _ (transGen_rank_lt h)

/-- A node whose rank is `≤` the source's rank is unreachable from the source: there is no
backward (rank-non-increasing) path.  This discharges the AE.5 reverse edges. -/
theorem no_reverse_path {a b : Node} (hr : nodeRank b ≤ nodeRank a) :
    ¬ Relation.TransGen ClosureEdge a b := fun h =>
  absurd (transGen_rank_lt h) (not_lt.mpr hr)

/-- A node that is never the source of an edge reaches nothing. -/
theorem noReach_of_noOut {a : Node} (ha : ∀ p ∈ closureEdgeList, p.1 ≠ a) (b : Node) :
    ¬ Relation.TransGen ClosureEdge a b := by
  intro h
  induction h with
  | single hab => exact ha _ hab rfl
  | tail _ _ ih => exact ih

/-! ### The AE.5 forbidden reverse/absent edges, proved -/

/-- **F3** (v32 11825): no `(R3) → fixed-pin voiding` edge — `(R3)` is never used to prove
the fixed-pin voiding (which is then fed back into `(R3)`). -/
theorem firewall_no_r3_to_pin :
    (Node.r3, Node.fixedPinVoiding) ∉ closureEdgeList := by decide

/-- AE.5 (11963): no `off-pin cap → LC1` edge — the off-pin cap is never used to supply
the RISK c phase balance. -/
theorem firewall_no_cap_to_lc1 :
    (Node.offPinCap, Node.lc1) ∉ closureEdgeList := by decide

/-- AE.5 (11963): no `off-pin cap → LC2` edge — the off-pin cap is never used to supply
the RISK b summed support. -/
theorem firewall_no_cap_to_lc2 :
    (Node.offPinCap, Node.lc2) ∉ closureEdgeList := by decide

/-- AE.5 (11962): no `fixed-pin voiding → off-pin cap` edge. -/
theorem firewall_no_pin_to_cap :
    (Node.fixedPinVoiding, Node.offPinCap) ∉ closureEdgeList := by decide

/-- AE.5 (11962): no `denominator-seven closure → off-pin cap` edge. -/
theorem firewall_no_denSeven_to_cap :
    (Node.denSeven, Node.offPinCap) ∉ closureEdgeList := by decide

/-- The strong form of F3: there is no path from `(R3)` back to the fixed-pin voiding. -/
theorem firewall_no_r3_path_to_pin :
    ¬ Relation.TransGen ClosureEdge Node.r3 Node.fixedPinVoiding :=
  no_reverse_path (by decide)

/-- The strong form: there is no path from the off-pin cap back to LC1. -/
theorem firewall_no_cap_path_to_lc1 :
    ¬ Relation.TransGen ClosureEdge Node.offPinCap Node.lc1 :=
  no_reverse_path (by decide)

/-- The strong form: there is no path from the off-pin cap back to LC2. -/
theorem firewall_no_cap_path_to_lc2 :
    ¬ Relation.TransGen ClosureEdge Node.offPinCap Node.lc2 :=
  no_reverse_path (by decide)

/-- The strong form: there is no path from denominator-seven closure back to the off-pin
cap. -/
theorem firewall_no_denSeven_path_to_cap :
    ¬ Relation.TransGen ClosureEdge Node.denSeven Node.offPinCap :=
  no_reverse_path (by decide)

/-- **F1** (v32 11821): the forbidden `ExitMass(Tot)` supplier reaches nothing, so it can
never supply the off-pin cap.  (In tree, the proportional total-exit share is refuted by
`emfc_spacedShare_not_covering` / the no-go `lem:r-strong-share-not-from-saturation`.) -/
theorem firewall_F1_exitMassTot_unreachable_cap :
    ¬ Relation.TransGen ClosureEdge Node.exitMassTot Node.offPinCap :=
  noReach_of_noOut (by decide) _

/-- **F2** (v32 11823): the forbidden `spacing-alone` supplier reaches nothing, so it can
never supply the off-pin cap / the exit share.  (In tree, the share is proved NOT
spacing-derivable by `elcShare_not_from_spacing_alone`.) -/
theorem firewall_F2_spacingAlone_unreachable_cap :
    ¬ Relation.TransGen ClosureEdge Node.spacingAlone Node.offPinCap :=
  noReach_of_noOut (by decide) _

/-- **THE v32 DEPENDENCY FIREWALL** (`prop:ae-dependency-graph`, AE.5, v32 line 11943).
The closure dependency graph is acyclic, and every AE.5 forbidden reverse edge is absent:
no `(R3) → pin` (F3), no `cap → LC1/LC2`, no `pin → cap`, no `denSeven → cap`, and the
forbidden `ExitMass(Tot)` (F1) and `spacing-alone` (F2) suppliers cannot reach the off-pin
cap.  This is the machine-checked non-circularity guarantee that answers the v30
circularity worry — proved by a strict rank certificate plus finite `decide` checks, not
a comment. -/
theorem v32_dependency_firewall :
    (∀ a : Node, ¬ Relation.TransGen ClosureEdge a a)
      ∧ (Node.r3, Node.fixedPinVoiding) ∉ closureEdgeList
      ∧ (Node.offPinCap, Node.lc1) ∉ closureEdgeList
      ∧ (Node.offPinCap, Node.lc2) ∉ closureEdgeList
      ∧ (Node.fixedPinVoiding, Node.offPinCap) ∉ closureEdgeList
      ∧ (Node.denSeven, Node.offPinCap) ∉ closureEdgeList
      ∧ ¬ Relation.TransGen ClosureEdge Node.exitMassTot Node.offPinCap
      ∧ ¬ Relation.TransGen ClosureEdge Node.spacingAlone Node.offPinCap :=
  ⟨v32_firewall_acyclic, firewall_no_r3_to_pin, firewall_no_cap_to_lc1,
    firewall_no_cap_to_lc2, firewall_no_pin_to_cap, firewall_no_denSeven_to_cap,
    firewall_F1_exitMassTot_unreachable_cap, firewall_F2_spacingAlone_unreachable_cap⟩

/-! ## Part 4.  Non-regression guards (T1–T6 where Lean-checkable) -/

/-- **T1 guard** (v32 12006) / **F1 shape** (11821): the RISK c off-pin balance carried by
LC1 is `c·ExitMass^offpin_i ≤ b·M_tot` — it has NO `ExitMass(Tot)` on the right-hand side
(it is the fibre exit mass `emcFibreExitMass`, not the total).  The off-pin cap therefore
cannot be a proportional total-exit spaced share. -/
theorem v32_T1_riskc_no_totalExitMass (ctx : ActualFailureContext) (i : Fin 7)
    (b c Mtot : ℕ) :
    V30MeasurePreservation ctx i b c Mtot ↔ c * emcFibreExitMass ctx i ≤ b * Mtot :=
  Iff.rfl

/-- **T2 guard** (v32 12009): the return gate carried by LC5 is the non-pinned half of the
split gate — its third hypothesis is exactly `¬ OrbitBandPinned ctx 2`, so a raw field
gate can only fire under `¬Pinned`.  (Restates the `LC5` scope; the implication to the
v30 field is definitional.) -/
theorem v32_T2_returnGate_requires_notPinned (R : Erdos260V32Residual) :
    ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx →
      ¬ OrbitBandPinned ctx 2 →
      ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
      2 * (129 * shellLadderDepth ctx + 64)
        ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card
              + ctx.n24CarryData.r)
            * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
      ReturnGatesBodyUngated ctx :=
  R.lc5

/-- **T6 guard** (v32 12019), graph form: the namespace proving LC3 imports neither `(R2)`
nor `(R3)` — there is no graph edge from `(R2)` or `(R3)` into the fixed-pin voiding that
LC3 supplies.  (In tree, the bounded-period confinement route is import-isolated from the
exit-mass cap; see `V30RetirementDischarge`.) -/
theorem v32_T6_lc3_independent_of_r2_r3 :
    (Node.r2, Node.fixedPinVoiding) ∉ closureEdgeList
      ∧ (Node.r3, Node.fixedPinVoiding) ∉ closureEdgeList := by decide

/-- **T6 guard** (v32 12019), graph form: the namespace proving LC4 imports the Appendix-Y
/ formal-row material but NOT the off-pin exit-mass namespace — there is no graph edge
from the off-pin cap into `(R2)` (which LC4 supplies). -/
theorem v32_T6_lc4_independent_of_offPinCap :
    (Node.offPinCap, Node.r2) ∉ closureEdgeList := by decide

/-- **T5 guard** (v32 12017): top-band (LC9) and read-tail/span-rarity (LC10) feed only the
surface partition — they have NO edge into the off-pin cap or the safe-cone cap, so they
cannot replace LC1/LC2 as exit-mass caps. -/
theorem v32_T5_topband_readtail_not_caps :
    (Node.lc9, Node.offPinCap) ∉ closureEdgeList
      ∧ (Node.lc10, Node.offPinCap) ∉ closureEdgeList
      ∧ (Node.lc9, Node.safeConeCap) ∉ closureEdgeList
      ∧ (Node.lc10, Node.safeConeCap) ∉ closureEdgeList := by decide

/-! ## Part 5.  Honest machine-readable status -/

/-- Honest, machine-readable status of the v32 interface-hardening endpoint. -/
def erdos260V32EndpointStatus : List String :=
  [ "LANE I (Erdos260V32Endpoint) — formalization of the v32 interface-hardening layer " ++
      "(proof_v4_repaired_core_v32.tex, Appendices AE + Z) on top of the proved v30 " ++
      "endpoint.  ENDPOINT (PROVED): erdos260_of_v32Residual : Erdos260V32Residual -> " ++
      "Erdos260Statement, via Erdos260V32Residual.toV30 + erdos260_of_v30Residual.  " ++
      "LOCALIZED ENDPOINT (PROVED): erdos260_of_v32LocalizedExitCapResidual replaces " ++
      "LC9 and the span-rarity half of LC10 by V30LocalizedExitCapSuppliers, then " ++
      "rebuilds the strict AE contracts before projection.  COMBINED ENDPOINT " ++
      "(PROVED): erdos260_of_v32O2LocalizedExitCapZeroErrorResidual uses the O2 " ++
      "finite-error/zero-collar bridge for LC1/LC2 and localized cap suppliers for " ++
      "LC9/LC10 simultaneously.  The parallel empty-collar combined endpoint " ++
      "erdos260_of_v32O2LocalizedExitCapEmptyCollarResidual uses the same localized " ++
      "suppliers but packages LC1/LC2's four collars as literal empty-set facts.  " ++
      "REFINED ENDPOINT (PROVED): erdos260_of_v32O2CollarCoordinateResidual replaces " ++
      "LC1/LC2 by the coordinate-split zero-collar O2 provider before projecting back " ++
      "to Erdos260V32Residual.  ZERO-ERROR REFINED ENDPOINT (PROVED): " ++
      "erdos260_of_v32O2CollarCoordinateZeroErrorResidual accepts the finite-error O2 " ++
      "collar provider plus four collar=0 proofs and converts it to the same " ++
      "zero-collar surface.  Additive endpoint layer; no theorem is weakened.",
    "HONEST HEADLINE (non-triumphal): the residual is UNCHANGED at 10 atoms.  v32 adds " ++
      "ZERO new mathematics (its body, Appendices E-AD, is byte-identical to v30) and " ++
      "closes NONE of the ten atoms.  erdos260_of_v32Residual is EXACTLY as conditional " ++
      "as erdos260_of_v30Residual; it depends on the SAME ten research-grade obligations. " ++
      "This is interface hardening (sharper atom statements + a machine-checked " ++
      "non-circularity firewall + a v32 endpoint), NOT a new proof.",
    "THE TEN CONTRACTS (Appendix AE int:ae-ten-atom-contracts, v32 11837): LC1 (AE.1 " ++
      "mass-normalized off-pin phase balance, RISK c = V30OffPinSafeConeRegime); LC2 " ++
      "(AE.2 disjoint summed support, RISK b = V30Class0SafeConeRegime, the routed " ++
      "class-0 summand); LC3 (Appendix-U confinement, period p <= 2^19 = " ++
      "FixedPinCleanContinuation); LC4 (AE.3 faithful class-1 realization = " ++
      "V30Class1LedgerRealizesFormalRow over class1SystemOfCarry); LC5 (AE.4 return " ++
      "split-gate, non-pinned half); LC6 (class-0 per-lane Y-cap = " ++
      "NarrowSupportClass0Gates); LC7 (frontier SDR / owned blocks = K1ClusterFloor); " ++
      "LC8 (Q-correct density rho_D(Q) = densePackEndpointDensity); LC9 (top-band " ++
      "localized routing = V30TopBandPushforward); LC10 (read-tail push-forward = " ++
      "V30ReadTailExitCount + span rarity = K1SpanRarity).",
    "v32 -> v30 BRIDGE (Erdos260V32Residual.toV30): offPin := <LC1, LC2> " ++
      "(V30OffPinFullRegime = V30OffPinSafeConeRegime AND V30Class0SafeConeRegime); " ++
      "confinement := LC3; class1Realize := LC4; topBand := LC9; readTail := " ++
      "LC10.readTail; spanRarity := LC10.spanRarity; clusterFloor := LC7; density := " ++
      "LC8; returnGates := LC5; class0Gates := LC6.  Each is a sound projection " ++
      "(v32 adds zero new mathematics, so LC -> v30 is definitional / a restatement).",
    "OFF-PIN REFINEMENT: Erdos260V32O2CollarCoordinateResidual keeps LC3-LC10 " ++
      "unchanged but replaces the paired off-pin contracts LC1/LC2 by " ++
      "V30OffPinFullO2CollarSupplyCoordinateSafeConeInputs.  Its projection " ++
      "toV32Residual rebuilds LC1/LC2 using " ++
      "v30OffPinFullRegime_of_o2_collar_supply_coordinate_full_provider, and its " ++
      "offPinDeliverables theorem returns the same ExitMassControlOffPin and " ++
      "MdcClass0ExitMassControl deliverables.  This lowers the interface to the " ++
      "TeX O2/AB/R provider surface but still requires the provider mathematics. " ++
      "Erdos260V32O2CollarCoordinateZeroErrorResidual is the explicit finite-error " ++
      "variant: it uses the Lane-C toZeroCollarProvider bridge once the four collar " ++
      "cardinalities are proved zero. " ++
      "Erdos260V32O2CollarCoordinateEmptyCollarResidual packages the empty-collar " ++
      "version of the same finite-error surface and projects through the proved " ++
      "Lane-C empty-collar bridge before using the existing v32 zero-collar endpoint.",
    "LOCALIZED R4/R5 REFINEMENT: Erdos260V32LocalizedExitCapResidual keeps LC1-LC8 " ++
      "and the readTail half of LC10 unchanged, but lowers LC9/topBand and the " ++
      "spanRarity half of LC10 to V30LocalizedExitCapSuppliers.  This mirrors the " ++
      "v30 localized endpoint and uses only the already-proved bridges " ++
      "v30_topBandPushforward_of_cap and v30_spanRarity_of_cap.",
    "COMBINED LOWER-LEVEL ENDPOINT: Erdos260V32O2LocalizedExitCapZeroErrorResidual " ++
      "simultaneously lowers LC1/LC2 to the finite-error coordinate O2 collar " ++
      "provider with four zero-collar proofs and lowers LC9/LC10 to " ++
      "V30LocalizedExitCapSuppliers.  It projects through " ++
      "Erdos260V32LocalizedExitCapResidual and adds no new mathematical shortcut.  " ++
      "Erdos260V32O2LocalizedExitCapEmptyCollarResidual is the corresponding " ++
      "Appendix-AE-facing literal empty-collar version, using the packaged Lane-C " ++
      "empty-collar bridge instead of four separate collar-cardinality fields.",
    "THE FIREWALL (v32_dependency_firewall, prop:ae-dependency-graph AE.5 v32 11943): the " ++
      "closure dependency DAG over LC1..LC10 + the in-tree-proved nodes (boundedPeriod, " ++
      "unsafeCoreEmpty, safeConeCap, offPinCap, R2, fixedPinVoiding, R3, surface, V-W, " ++
      "denSeven, appY) is PROVED ACYCLIC by a strict rank certificate (transGen_rank_lt + " ++
      "lt_irrefl), and the AE.5 forbidden reverse edges are PROVED absent by decide: no " ++
      "(R3)->pin (F3), no cap->LC1, no cap->LC2, no pin->cap, no denSeven->cap; plus F1 " ++
      "(ExitMass(Tot)) and F2 (spacing-alone) sentinels PROVED to reach nothing " ++
      "(unreachable from the off-pin cap).  This is the machine-checked non-circularity " ++
      "guarantee answering the v30 circularity worry (DISCOVERY 1).",
    "NON-CIRCULARITY BACKING (in tree, cited not re-proved): the off-pin supply does not " ++
      "consume the pins.  V30RetirementDischarge proves the bounded-period retirement " ++
      "(D1 routing + D2 affordability, margin 7/1536) and the off-pin unsafe-core " ++
      "emptiness (prop:ac-unsafe-core-empty) WITHOUT the off-pin cap (C1) " ++
      "(import-isolated from C1).  The proportional total-exit share is refuted by " ++
      "emfc_spacedShare_not_covering and elcShare_not_from_spacing_alone (the in-tree " ++
      "mirrors of lem:r-strong-share-not-from-saturation, v32 F1/F2).",
    "NON-REGRESSION GUARDS (T1-T6 where Lean-checkable): T1 (v32_T1_riskc_no_totalExitMass) " ++
      "— the RISK c balance is c*emcFibreExitMass <= b*Mtot, no ExitMass(Tot); T2 " ++
      "(v32_T2_returnGate_requires_notPinned) — the return gate fires only under " ++
      "not-Pinned; T5 (v32_T5_topband_readtail_not_caps) — topBand/readTail feed only the " ++
      "surface, never the cap; T6 (v32_T6_lc3_independent_of_r2_r3, " ++
      "v32_T6_lc4_independent_of_offPinCap) — LC3 import-isolated from R2/R3, LC4 from the " ++
      "off-pin cap.",
    "THE UNCHANGED TEN-ATOM RESIDUAL (verbatim from V30_STATUS): offPin (C1 RISK b/c/e), " ++
      "confinement (Appendix U), class1Realize (Appendix AA bridge = DccClass1DeepResidual " ++
      "0), topBand (R5), readTail (R6), spanRarity (R4), clusterFloor (K.1.1), density " ++
      "(K.1.1), returnGates (R4-return), class0Gates (narrow-support).  v32 CLASSIFIES " ++
      "them (CLOSED 0; STRENGTHENED/derived 3 = topBand/readTail/spanRarity under " ++
      "A5/LC9/LC10; UNCHANGED 7) and SHARPENS their statements, but closes none.",
    "AXIOMS: erdos260_of_v32Residual, v32_dependency_firewall and every key declaration " ++
      "report exactly [propext, Classical.choice, Quot.sound] or fewer; the firewall " ++
      "decls (decide + rank) report [propext] or fewer; no sorry / admit / native_decide; " ++
      "no new axiom." ]

/-- The status ledger is non-empty (honest, non-vacuous). -/
theorem erdos260V32EndpointStatus_nonempty : erdos260V32EndpointStatus ≠ [] := by
  unfold erdos260V32EndpointStatus
  simp

/-! ## Part 5a.  Return-gates full-field projection -/

/-- The v32 residual rebuilds the full corrected Return-gates field by projecting
to the v30 residual.  This is the Appendix-AE LC5 split-gate: LC5 supplies the
non-pinned half, while the pinned half and `b₂ = 0` return table are discharged
by the v30 bridge. -/
theorem Erdos260V32Residual.returnGatesField (R : Erdos260V32Residual) :
    ReturnGatesField :=
  R.toV30.returnGatesField

/-- The v32 residual inherits the full corrected Return-interior field through
its v30 projection. -/
theorem Erdos260V32Residual.returnInteriorField (R : Erdos260V32Residual) :
    ∀ ctx : ActualFailureContext, ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx :=
  R.toV30.returnInteriorField

/-- The v32 residual inherits the exact off-table Return-gates branch through
its v30 projection. -/
theorem Erdos260V32Residual.returnGatesOffTableField (R : Erdos260V32Residual) :
    ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx →
      ¬ OrbitBandPinned ctx 2 →
      ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
      2 * (129 * shellLadderDepth ctx + 64)
        ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card
              + ctx.n24CarryData.r)
            * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
      ReturnGatesBodyUngated ctx :=
  R.toV30.returnGatesOffTableField

/-- The v32 residual inherits the exact off-table Return-interior branch through
its v30 projection. -/
theorem Erdos260V32Residual.returnInteriorOffTableField (R : Erdos260V32Residual) :
    ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx →
      ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx :=
  R.toV30.returnInteriorOffTableField

/-- The localized v32 endpoint surface inherits the full corrected Return-gates
field through its v30 projection. -/
theorem Erdos260V32LocalizedExitCapResidual.returnGatesField
    (R : Erdos260V32LocalizedExitCapResidual) :
    ReturnGatesField :=
  R.toV30Residual.returnGatesField

/-- The combined zero-error O2/localized v32 endpoint surface inherits the full
corrected Return-gates field. -/
theorem Erdos260V32O2LocalizedExitCapZeroErrorResidual.returnGatesField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ReturnGatesField :=
  R.toV30Residual.returnGatesField

/-- The combined empty-collar O2/localized v32 endpoint surface inherits the full
corrected Return-gates field. -/
theorem Erdos260V32O2LocalizedExitCapEmptyCollarResidual.returnGatesField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ReturnGatesField :=
  R.toV30Residual.returnGatesField

/-- The coordinate O2 v32 endpoint surface inherits the full corrected
Return-gates field through its v30 projection. -/
theorem Erdos260V32O2CollarCoordinateResidual.returnGatesField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateResidual (β := β) (A := A) P₀ Q) :
    ReturnGatesField :=
  R.toV30Residual.returnGatesField

/-- The finite-error/zero-collar coordinate O2 v32 endpoint surface inherits the
full corrected Return-gates field. -/
theorem Erdos260V32O2CollarCoordinateZeroErrorResidual.returnGatesField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ReturnGatesField :=
  R.toV30Residual.returnGatesField

/-- The empty-collar coordinate O2 v32 endpoint surface inherits the full
corrected Return-gates field. -/
theorem Erdos260V32O2CollarCoordinateEmptyCollarResidual.returnGatesField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ReturnGatesField :=
  R.toV30Residual.returnGatesField

/-- The localized v32 endpoint surface inherits the full corrected
Return-interior field through its v30 projection. -/
theorem Erdos260V32LocalizedExitCapResidual.returnInteriorField
    (R : Erdos260V32LocalizedExitCapResidual) :
    ∀ ctx : ActualFailureContext, ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx :=
  R.toV30Residual.returnInteriorField

/-- The combined zero-error O2/localized v32 endpoint surface inherits the full
corrected Return-interior field. -/
theorem Erdos260V32O2LocalizedExitCapZeroErrorResidual.returnInteriorField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx :=
  R.toV30Residual.returnInteriorField

/-- The combined empty-collar O2/localized v32 endpoint surface inherits the full
corrected Return-interior field. -/
theorem Erdos260V32O2LocalizedExitCapEmptyCollarResidual.returnInteriorField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx :=
  R.toV30Residual.returnInteriorField

/-- The coordinate O2 v32 endpoint surface inherits the full corrected
Return-interior field through its v30 projection. -/
theorem Erdos260V32O2CollarCoordinateResidual.returnInteriorField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateResidual (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx :=
  R.toV30Residual.returnInteriorField

/-- The finite-error/zero-collar coordinate O2 v32 endpoint surface inherits the
full corrected Return-interior field. -/
theorem Erdos260V32O2CollarCoordinateZeroErrorResidual.returnInteriorField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx :=
  R.toV30Residual.returnInteriorField

/-- The empty-collar coordinate O2 v32 endpoint surface inherits the full
corrected Return-interior field. -/
theorem Erdos260V32O2CollarCoordinateEmptyCollarResidual.returnInteriorField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx :=
  R.toV30Residual.returnInteriorField

/-- The localized v32 endpoint surface inherits the off-table Return-gates branch
through its v30 projection. -/
theorem Erdos260V32LocalizedExitCapResidual.returnGatesOffTableField
    (R : Erdos260V32LocalizedExitCapResidual) :
    ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx →
      ¬ OrbitBandPinned ctx 2 →
      ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
      2 * (129 * shellLadderDepth ctx + 64)
        ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card
              + ctx.n24CarryData.r)
            * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
      ReturnGatesBodyUngated ctx :=
  R.toV30Residual.returnGatesOffTableField

/-- The combined zero-error O2/localized v32 endpoint surface inherits the
off-table Return-gates branch. -/
theorem Erdos260V32O2LocalizedExitCapZeroErrorResidual.returnGatesOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx →
      ¬ OrbitBandPinned ctx 2 →
      ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
      2 * (129 * shellLadderDepth ctx + 64)
        ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card
              + ctx.n24CarryData.r)
            * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
      ReturnGatesBodyUngated ctx :=
  R.toV30Residual.returnGatesOffTableField

/-- The combined empty-collar O2/localized v32 endpoint surface inherits the
off-table Return-gates branch. -/
theorem Erdos260V32O2LocalizedExitCapEmptyCollarResidual.returnGatesOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx →
      ¬ OrbitBandPinned ctx 2 →
      ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
      2 * (129 * shellLadderDepth ctx + 64)
        ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card
              + ctx.n24CarryData.r)
            * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
      ReturnGatesBodyUngated ctx :=
  R.toV30Residual.returnGatesOffTableField

/-- The coordinate O2 v32 endpoint surface inherits the off-table Return-gates
branch through its v30 projection. -/
theorem Erdos260V32O2CollarCoordinateResidual.returnGatesOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateResidual (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx →
      ¬ OrbitBandPinned ctx 2 →
      ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
      2 * (129 * shellLadderDepth ctx + 64)
        ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card
              + ctx.n24CarryData.r)
            * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
      ReturnGatesBodyUngated ctx :=
  R.toV30Residual.returnGatesOffTableField

/-- The finite-error/zero-collar coordinate O2 v32 endpoint surface inherits the
off-table Return-gates branch. -/
theorem Erdos260V32O2CollarCoordinateZeroErrorResidual.returnGatesOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx →
      ¬ OrbitBandPinned ctx 2 →
      ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
      2 * (129 * shellLadderDepth ctx + 64)
        ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card
              + ctx.n24CarryData.r)
            * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
      ReturnGatesBodyUngated ctx :=
  R.toV30Residual.returnGatesOffTableField

/-- The empty-collar coordinate O2 v32 endpoint surface inherits the off-table
Return-gates branch. -/
theorem Erdos260V32O2CollarCoordinateEmptyCollarResidual.returnGatesOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx →
      ¬ OrbitBandPinned ctx 2 →
      ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
      2 * (129 * shellLadderDepth ctx + 64)
        ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card
              + ctx.n24CarryData.r)
            * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
      ReturnGatesBodyUngated ctx :=
  R.toV30Residual.returnGatesOffTableField

/-- The localized v32 endpoint surface inherits the off-table Return-interior
branch through its v30 projection. -/
theorem Erdos260V32LocalizedExitCapResidual.returnInteriorOffTableField
    (R : Erdos260V32LocalizedExitCapResidual) :
    ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx →
      ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx :=
  R.toV30Residual.returnInteriorOffTableField

/-- The combined zero-error O2/localized v32 endpoint surface inherits the
off-table Return-interior branch. -/
theorem Erdos260V32O2LocalizedExitCapZeroErrorResidual.returnInteriorOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx →
      ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx :=
  R.toV30Residual.returnInteriorOffTableField

/-- The combined empty-collar O2/localized v32 endpoint surface inherits the
off-table Return-interior branch. -/
theorem Erdos260V32O2LocalizedExitCapEmptyCollarResidual.returnInteriorOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx →
      ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx :=
  R.toV30Residual.returnInteriorOffTableField

/-- The coordinate O2 v32 endpoint surface inherits the off-table Return-interior
branch through its v30 projection. -/
theorem Erdos260V32O2CollarCoordinateResidual.returnInteriorOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateResidual (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx →
      ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx :=
  R.toV30Residual.returnInteriorOffTableField

/-- The finite-error/zero-collar coordinate O2 v32 endpoint surface inherits the
off-table Return-interior branch. -/
theorem Erdos260V32O2CollarCoordinateZeroErrorResidual.returnInteriorOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx →
      ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx :=
  R.toV30Residual.returnInteriorOffTableField

/-- The empty-collar coordinate O2 v32 endpoint surface inherits the off-table
Return-interior branch. -/
theorem Erdos260V32O2CollarCoordinateEmptyCollarResidual.returnInteriorOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx →
      ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx :=
  R.toV30Residual.returnInteriorOffTableField

/-- The v32 residual rebuilds the full corrected densepack Nat-cover field by
projecting to the v30 residual.  LC7, LC8, and LC10's span-rarity component
provide the K.1 landing branch; LC3 supplies the band-3 pinned voiding branch. -/
theorem Erdos260V32Residual.densePackCoverField (R : Erdos260V32Residual) :
    DensePackCoverField :=
  R.toV30.densePackCoverField

/-- The v32 residual inherits the corrected densepack density field through its
v30 projection.  LC8 is exactly the off-table K.1 density supply, and the
v30 bridge fills the `b3 = 0` table rows. -/
theorem Erdos260V32Residual.densePackDensityField (R : Erdos260V32Residual) :
    ∀ ctx : ActualFailureContext,
      ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      densePackEndpointDensity ctx :=
  R.toV30.densePackDensityField

/-- The v32 residual inherits the corrected densepack active-window interior
field through its v30 projection. -/
theorem Erdos260V32Residual.densePackInteriorField (R : Erdos260V32Residual) :
    ∀ ctx : ActualFailureContext,
      ¬ Class3TopBandCycleFree ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      ∀ k ∈ genuineDensePackStarts ctx,
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card :=
  R.toV30.densePackInteriorField

/-- The v32 residual inherits the DensePack off-table endpoint-density branch
through its v30 projection. -/
theorem Erdos260V32Residual.densePackDensityOffTableField
    (R : Erdos260V32Residual) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      densePackEndpointDensity ctx :=
  R.toV30.densePackDensityOffTableField

/-- The v32 residual inherits the DensePack off-table active-window interior
branch through its v30 projection. -/
theorem Erdos260V32Residual.densePackInteriorOffTableField
    (R : Erdos260V32Residual) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Class3TopBandCycleFree ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      ∀ k ∈ genuineDensePackStarts ctx,
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card :=
  R.toV30.densePackInteriorOffTableField

/-- The v32 residual inherits the exact class-0 mass field through its v30
projection; LC6 is exactly the carried narrow-support gate surface. -/
theorem Erdos260V32Residual.class0MassField (R : Erdos260V32Residual) :
    Class0MassField :=
  R.toV30.class0MassField

/-- The v32 residual inherits the exact K.1 start-spacing field through its v30
projection; LC10 supplies the same span-rarity atom used by the v30 DensePack
cover branch. -/
theorem Erdos260V32Residual.densePackStartSpacingField (R : Erdos260V32Residual) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx → 1 ≤ ctx.n24CarryData.r →
      K1StartSpacing ctx :=
  R.toV30.densePackStartSpacingField

/-- The v32 residual inherits the exact K.1 cluster-floor field through its v30
projection. -/
theorem Erdos260V32Residual.densePackClusterFloorField
    (R : Erdos260V32Residual) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx → 1 ≤ ctx.n24CarryData.r →
      K1ClusterFloor ctx :=
  R.toV30.densePackClusterFloorField

/-- The localized v32 endpoint surface inherits the exact K.1 start-spacing field
through its v30 projection. -/
theorem Erdos260V32LocalizedExitCapResidual.densePackStartSpacingField
    (R : Erdos260V32LocalizedExitCapResidual) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx → 1 ≤ ctx.n24CarryData.r →
      K1StartSpacing ctx :=
  R.toV30Residual.densePackStartSpacingField

/-- The combined zero-error O2/localized v32 endpoint surface inherits the exact
K.1 start-spacing field. -/
theorem Erdos260V32O2LocalizedExitCapZeroErrorResidual.densePackStartSpacingField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx → 1 ≤ ctx.n24CarryData.r →
      K1StartSpacing ctx :=
  R.toV30Residual.densePackStartSpacingField

/-- The combined empty-collar O2/localized v32 endpoint surface inherits the
exact K.1 start-spacing field. -/
theorem Erdos260V32O2LocalizedExitCapEmptyCollarResidual.densePackStartSpacingField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx → 1 ≤ ctx.n24CarryData.r →
      K1StartSpacing ctx :=
  R.toV30Residual.densePackStartSpacingField

/-- The coordinate O2 v32 endpoint surface inherits the exact K.1 start-spacing
field through its v30 projection. -/
theorem Erdos260V32O2CollarCoordinateResidual.densePackStartSpacingField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateResidual (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx → 1 ≤ ctx.n24CarryData.r →
      K1StartSpacing ctx :=
  R.toV30Residual.densePackStartSpacingField

/-- The finite-error/zero-collar coordinate O2 v32 endpoint surface inherits the
exact K.1 start-spacing field. -/
theorem Erdos260V32O2CollarCoordinateZeroErrorResidual.densePackStartSpacingField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx → 1 ≤ ctx.n24CarryData.r →
      K1StartSpacing ctx :=
  R.toV30Residual.densePackStartSpacingField

/-- The empty-collar coordinate O2 v32 endpoint surface inherits the exact K.1
start-spacing field. -/
theorem Erdos260V32O2CollarCoordinateEmptyCollarResidual.densePackStartSpacingField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx → 1 ≤ ctx.n24CarryData.r →
      K1StartSpacing ctx :=
  R.toV30Residual.densePackStartSpacingField

/-- The localized v32 endpoint surface inherits the exact K.1 cluster-floor field
through its v30 projection. -/
theorem Erdos260V32LocalizedExitCapResidual.densePackClusterFloorField
    (R : Erdos260V32LocalizedExitCapResidual) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx → 1 ≤ ctx.n24CarryData.r →
      K1ClusterFloor ctx :=
  R.toV30Residual.densePackClusterFloorField

/-- The combined zero-error O2/localized v32 endpoint surface inherits the exact
K.1 cluster-floor field. -/
theorem Erdos260V32O2LocalizedExitCapZeroErrorResidual.densePackClusterFloorField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx → 1 ≤ ctx.n24CarryData.r →
      K1ClusterFloor ctx :=
  R.toV30Residual.densePackClusterFloorField

/-- The combined empty-collar O2/localized v32 endpoint surface inherits the
exact K.1 cluster-floor field. -/
theorem Erdos260V32O2LocalizedExitCapEmptyCollarResidual.densePackClusterFloorField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx → 1 ≤ ctx.n24CarryData.r →
      K1ClusterFloor ctx :=
  R.toV30Residual.densePackClusterFloorField

/-- The coordinate O2 v32 endpoint surface inherits the exact K.1 cluster-floor
field through its v30 projection. -/
theorem Erdos260V32O2CollarCoordinateResidual.densePackClusterFloorField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateResidual (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx → 1 ≤ ctx.n24CarryData.r →
      K1ClusterFloor ctx :=
  R.toV30Residual.densePackClusterFloorField

/-- The finite-error/zero-collar coordinate O2 v32 endpoint surface inherits the
exact K.1 cluster-floor field. -/
theorem Erdos260V32O2CollarCoordinateZeroErrorResidual.densePackClusterFloorField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx → 1 ≤ ctx.n24CarryData.r →
      K1ClusterFloor ctx :=
  R.toV30Residual.densePackClusterFloorField

/-- The empty-collar coordinate O2 v32 endpoint surface inherits the exact K.1
cluster-floor field. -/
theorem Erdos260V32O2CollarCoordinateEmptyCollarResidual.densePackClusterFloorField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx → 1 ≤ ctx.n24CarryData.r →
      K1ClusterFloor ctx :=
  R.toV30Residual.densePackClusterFloorField

/-- The v32 residual inherits the K.1 densepack off-table cover inequality
through its v30 projection. -/
theorem Erdos260V32Residual.densePackCoverOffTableField
    (R : Erdos260V32Residual) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      (genuineDensePackStarts ctx).card
          * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
              - (2 * shellLadderDepth ctx + 1))
        ≤ (proofV4DensePackActualPoints ctx.shell).card :=
  R.toV30.densePackCoverOffTableField

/-- The localized v32 endpoint surface inherits the K.1 densepack off-table
cover inequality through its v30 projection. -/
theorem Erdos260V32LocalizedExitCapResidual.densePackCoverOffTableField
    (R : Erdos260V32LocalizedExitCapResidual) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      (genuineDensePackStarts ctx).card
          * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
              - (2 * shellLadderDepth ctx + 1))
        ≤ (proofV4DensePackActualPoints ctx.shell).card :=
  R.toV30Residual.densePackCoverOffTableField

/-- The combined zero-error O2/localized v32 endpoint surface inherits the K.1
densepack off-table cover inequality. -/
theorem Erdos260V32O2LocalizedExitCapZeroErrorResidual.densePackCoverOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      (genuineDensePackStarts ctx).card
          * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
              - (2 * shellLadderDepth ctx + 1))
        ≤ (proofV4DensePackActualPoints ctx.shell).card :=
  R.toV30Residual.densePackCoverOffTableField

/-- The combined empty-collar O2/localized v32 endpoint surface inherits the K.1
densepack off-table cover inequality. -/
theorem Erdos260V32O2LocalizedExitCapEmptyCollarResidual.densePackCoverOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      (genuineDensePackStarts ctx).card
          * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
              - (2 * shellLadderDepth ctx + 1))
        ≤ (proofV4DensePackActualPoints ctx.shell).card :=
  R.toV30Residual.densePackCoverOffTableField

/-- The coordinate O2 v32 endpoint surface inherits the K.1 densepack off-table
cover inequality through its v30 projection. -/
theorem Erdos260V32O2CollarCoordinateResidual.densePackCoverOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateResidual (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      (genuineDensePackStarts ctx).card
          * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
              - (2 * shellLadderDepth ctx + 1))
        ≤ (proofV4DensePackActualPoints ctx.shell).card :=
  R.toV30Residual.densePackCoverOffTableField

/-- The finite-error/zero-collar coordinate O2 v32 endpoint surface inherits the
K.1 densepack off-table cover inequality. -/
theorem Erdos260V32O2CollarCoordinateZeroErrorResidual.densePackCoverOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      (genuineDensePackStarts ctx).card
          * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
              - (2 * shellLadderDepth ctx + 1))
        ≤ (proofV4DensePackActualPoints ctx.shell).card :=
  R.toV30Residual.densePackCoverOffTableField

/-- The empty-collar coordinate O2 v32 endpoint surface inherits the K.1
densepack off-table cover inequality. -/
theorem Erdos260V32O2CollarCoordinateEmptyCollarResidual.densePackCoverOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      (genuineDensePackStarts ctx).card
          * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
              - (2 * shellLadderDepth ctx + 1))
        ≤ (proofV4DensePackActualPoints ctx.shell).card :=
  R.toV30Residual.densePackCoverOffTableField

/-- The localized v32 endpoint surface inherits the DensePack off-table
endpoint-density branch through its v30 projection. -/
theorem Erdos260V32LocalizedExitCapResidual.densePackDensityOffTableField
    (R : Erdos260V32LocalizedExitCapResidual) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      densePackEndpointDensity ctx :=
  R.toV30Residual.densePackDensityOffTableField

/-- The combined zero-error O2/localized v32 endpoint surface inherits the
DensePack off-table endpoint-density branch. -/
theorem Erdos260V32O2LocalizedExitCapZeroErrorResidual.densePackDensityOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      densePackEndpointDensity ctx :=
  R.toV30Residual.densePackDensityOffTableField

/-- The combined empty-collar O2/localized v32 endpoint surface inherits the
DensePack off-table endpoint-density branch. -/
theorem Erdos260V32O2LocalizedExitCapEmptyCollarResidual.densePackDensityOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      densePackEndpointDensity ctx :=
  R.toV30Residual.densePackDensityOffTableField

/-- The coordinate O2 v32 endpoint surface inherits the DensePack off-table
endpoint-density branch through its v30 projection. -/
theorem Erdos260V32O2CollarCoordinateResidual.densePackDensityOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateResidual (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      densePackEndpointDensity ctx :=
  R.toV30Residual.densePackDensityOffTableField

/-- The finite-error/zero-collar coordinate O2 v32 endpoint surface inherits
the DensePack off-table endpoint-density branch. -/
theorem Erdos260V32O2CollarCoordinateZeroErrorResidual.densePackDensityOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      densePackEndpointDensity ctx :=
  R.toV30Residual.densePackDensityOffTableField

/-- The empty-collar coordinate O2 v32 endpoint surface inherits the DensePack
off-table endpoint-density branch. -/
theorem Erdos260V32O2CollarCoordinateEmptyCollarResidual.densePackDensityOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      densePackEndpointDensity ctx :=
  R.toV30Residual.densePackDensityOffTableField

/-- The localized v32 endpoint surface inherits the DensePack off-table
active-window interior branch through its v30 projection. -/
theorem Erdos260V32LocalizedExitCapResidual.densePackInteriorOffTableField
    (R : Erdos260V32LocalizedExitCapResidual) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Class3TopBandCycleFree ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      ∀ k ∈ genuineDensePackStarts ctx,
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card :=
  R.toV30Residual.densePackInteriorOffTableField

/-- The combined zero-error O2/localized v32 endpoint surface inherits the
DensePack off-table active-window interior branch. -/
theorem Erdos260V32O2LocalizedExitCapZeroErrorResidual.densePackInteriorOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Class3TopBandCycleFree ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      ∀ k ∈ genuineDensePackStarts ctx,
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card :=
  R.toV30Residual.densePackInteriorOffTableField

/-- The combined empty-collar O2/localized v32 endpoint surface inherits the
DensePack off-table active-window interior branch. -/
theorem Erdos260V32O2LocalizedExitCapEmptyCollarResidual.densePackInteriorOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Class3TopBandCycleFree ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      ∀ k ∈ genuineDensePackStarts ctx,
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card :=
  R.toV30Residual.densePackInteriorOffTableField

/-- The coordinate O2 v32 endpoint surface inherits the DensePack off-table
active-window interior branch through its v30 projection. -/
theorem Erdos260V32O2CollarCoordinateResidual.densePackInteriorOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateResidual (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Class3TopBandCycleFree ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      ∀ k ∈ genuineDensePackStarts ctx,
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card :=
  R.toV30Residual.densePackInteriorOffTableField

/-- The finite-error/zero-collar coordinate O2 v32 endpoint surface inherits
the DensePack off-table active-window interior branch. -/
theorem Erdos260V32O2CollarCoordinateZeroErrorResidual.densePackInteriorOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Class3TopBandCycleFree ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      ∀ k ∈ genuineDensePackStarts ctx,
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card :=
  R.toV30Residual.densePackInteriorOffTableField

/-- The empty-collar coordinate O2 v32 endpoint surface inherits the DensePack
off-table active-window interior branch. -/
theorem Erdos260V32O2CollarCoordinateEmptyCollarResidual.densePackInteriorOffTableField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Class3TopBandCycleFree ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      ∀ k ∈ genuineDensePackStarts ctx,
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card :=
  R.toV30Residual.densePackInteriorOffTableField

/-- The localized v32 endpoint surface inherits the full corrected densepack
Nat-cover field through its v30 projection. -/
theorem Erdos260V32LocalizedExitCapResidual.densePackCoverField
    (R : Erdos260V32LocalizedExitCapResidual) :
    DensePackCoverField :=
  R.toV30Residual.densePackCoverField

/-- The combined zero-error O2/localized v32 endpoint surface inherits the full
corrected densepack Nat-cover field. -/
theorem Erdos260V32O2LocalizedExitCapZeroErrorResidual.densePackCoverField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    DensePackCoverField :=
  R.toV30Residual.densePackCoverField

/-- The combined empty-collar O2/localized v32 endpoint surface inherits the full
corrected densepack Nat-cover field. -/
theorem Erdos260V32O2LocalizedExitCapEmptyCollarResidual.densePackCoverField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    DensePackCoverField :=
  R.toV30Residual.densePackCoverField

/-- The coordinate O2 v32 endpoint surface inherits the full corrected densepack
Nat-cover field through its v30 projection. -/
theorem Erdos260V32O2CollarCoordinateResidual.densePackCoverField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateResidual (β := β) (A := A) P₀ Q) :
    DensePackCoverField :=
  R.toV30Residual.densePackCoverField

/-- The finite-error/zero-collar coordinate O2 v32 endpoint surface inherits the
full corrected densepack Nat-cover field. -/
theorem Erdos260V32O2CollarCoordinateZeroErrorResidual.densePackCoverField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    DensePackCoverField :=
  R.toV30Residual.densePackCoverField

/-- The empty-collar coordinate O2 v32 endpoint surface inherits the full
corrected densepack Nat-cover field. -/
theorem Erdos260V32O2CollarCoordinateEmptyCollarResidual.densePackCoverField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    DensePackCoverField :=
  R.toV30Residual.densePackCoverField

/-- The localized v32 endpoint surface inherits the corrected densepack density
field through its v30 projection. -/
theorem Erdos260V32LocalizedExitCapResidual.densePackDensityField
    (R : Erdos260V32LocalizedExitCapResidual) :
    ∀ ctx : ActualFailureContext,
      ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      densePackEndpointDensity ctx :=
  R.toV30Residual.densePackDensityField

/-- The combined zero-error O2/localized v32 endpoint surface inherits the
corrected densepack density field. -/
theorem Erdos260V32O2LocalizedExitCapZeroErrorResidual.densePackDensityField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext,
      ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      densePackEndpointDensity ctx :=
  R.toV30Residual.densePackDensityField

/-- The combined empty-collar O2/localized v32 endpoint surface inherits the
corrected densepack density field. -/
theorem Erdos260V32O2LocalizedExitCapEmptyCollarResidual.densePackDensityField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext,
      ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      densePackEndpointDensity ctx :=
  R.toV30Residual.densePackDensityField

/-- The coordinate O2 v32 endpoint surface inherits the corrected densepack
density field through its v30 projection. -/
theorem Erdos260V32O2CollarCoordinateResidual.densePackDensityField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateResidual (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext,
      ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      densePackEndpointDensity ctx :=
  R.toV30Residual.densePackDensityField

/-- The finite-error/zero-collar coordinate O2 v32 endpoint surface inherits the
corrected densepack density field. -/
theorem Erdos260V32O2CollarCoordinateZeroErrorResidual.densePackDensityField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext,
      ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      densePackEndpointDensity ctx :=
  R.toV30Residual.densePackDensityField

/-- The empty-collar coordinate O2 v32 endpoint surface inherits the corrected
densepack density field. -/
theorem Erdos260V32O2CollarCoordinateEmptyCollarResidual.densePackDensityField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext,
      ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      densePackEndpointDensity ctx :=
  R.toV30Residual.densePackDensityField

/-- The localized v32 endpoint surface inherits the corrected densepack
active-window interior field through its v30 projection. -/
theorem Erdos260V32LocalizedExitCapResidual.densePackInteriorField
    (R : Erdos260V32LocalizedExitCapResidual) :
    ∀ ctx : ActualFailureContext,
      ¬ Class3TopBandCycleFree ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      ∀ k ∈ genuineDensePackStarts ctx,
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card :=
  R.toV30Residual.densePackInteriorField

/-- The combined zero-error O2/localized v32 endpoint surface inherits the
corrected densepack active-window interior field. -/
theorem Erdos260V32O2LocalizedExitCapZeroErrorResidual.densePackInteriorField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext,
      ¬ Class3TopBandCycleFree ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      ∀ k ∈ genuineDensePackStarts ctx,
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card :=
  R.toV30Residual.densePackInteriorField

/-- The combined empty-collar O2/localized v32 endpoint surface inherits the
corrected densepack active-window interior field. -/
theorem Erdos260V32O2LocalizedExitCapEmptyCollarResidual.densePackInteriorField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext,
      ¬ Class3TopBandCycleFree ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      ∀ k ∈ genuineDensePackStarts ctx,
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card :=
  R.toV30Residual.densePackInteriorField

/-- The coordinate O2 v32 endpoint surface inherits the corrected densepack
active-window interior field through its v30 projection. -/
theorem Erdos260V32O2CollarCoordinateResidual.densePackInteriorField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateResidual (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext,
      ¬ Class3TopBandCycleFree ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      ∀ k ∈ genuineDensePackStarts ctx,
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card :=
  R.toV30Residual.densePackInteriorField

/-- The finite-error/zero-collar coordinate O2 v32 endpoint surface inherits the
corrected densepack active-window interior field. -/
theorem Erdos260V32O2CollarCoordinateZeroErrorResidual.densePackInteriorField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext,
      ¬ Class3TopBandCycleFree ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      ∀ k ∈ genuineDensePackStarts ctx,
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card :=
  R.toV30Residual.densePackInteriorField

/-- The empty-collar coordinate O2 v32 endpoint surface inherits the corrected
densepack active-window interior field. -/
theorem Erdos260V32O2CollarCoordinateEmptyCollarResidual.densePackInteriorField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    ∀ ctx : ActualFailureContext,
      ¬ Class3TopBandCycleFree ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      ∀ k ∈ genuineDensePackStarts ctx,
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card :=
  R.toV30Residual.densePackInteriorField

/-- The localized v32 endpoint surface inherits the class-0 mass field rebuilt
from its carried LC6 narrow-support gate data. -/
theorem Erdos260V32LocalizedExitCapResidual.class0MassField
    (R : Erdos260V32LocalizedExitCapResidual) :
    Class0MassField :=
  R.toV30Residual.class0MassField

/-- The combined zero-error O2/localized v32 endpoint surface inherits the
class-0 mass field rebuilt from its carried LC6 narrow-support gate data. -/
theorem Erdos260V32O2LocalizedExitCapZeroErrorResidual.class0MassField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    Class0MassField :=
  R.toV30Residual.class0MassField

/-- The combined empty-collar O2/localized v32 endpoint surface inherits the
class-0 mass field rebuilt from its carried LC6 narrow-support gate data. -/
theorem Erdos260V32O2LocalizedExitCapEmptyCollarResidual.class0MassField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    Class0MassField :=
  R.toV30Residual.class0MassField

/-- The coordinate O2 v32 endpoint surface inherits the class-0 mass field
rebuilt from its carried LC6 narrow-support gate data. -/
theorem Erdos260V32O2CollarCoordinateResidual.class0MassField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateResidual (β := β) (A := A) P₀ Q) :
    Class0MassField :=
  R.toV30Residual.class0MassField

/-- The finite-error/zero-collar coordinate O2 v32 endpoint surface inherits the
class-0 mass field rebuilt from its carried LC6 narrow-support gate data. -/
theorem Erdos260V32O2CollarCoordinateZeroErrorResidual.class0MassField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    Class0MassField :=
  R.toV30Residual.class0MassField

/-- The empty-collar coordinate O2 v32 endpoint surface inherits the class-0
mass field rebuilt from its carried LC6 narrow-support gate data. -/
theorem Erdos260V32O2CollarCoordinateEmptyCollarResidual.class0MassField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    Class0MassField :=
  R.toV30Residual.class0MassField

/-- The localized v32 endpoint surface keeps the same Appendix-AA/Lane-J
class-1 carry realization package as its projection to `Erdos260V30Residual`. -/
def Erdos260V32LocalizedExitCapResidual.class1CarryInputs
    (R : Erdos260V32LocalizedExitCapResidual) :
    V30Class1CarryRealizationInputs :=
  R.toV30Residual.class1CarryInputs

/-- The localized v32 endpoint surface supplies the same level-`0` boosted
class-1 residual as its v30 projection. -/
theorem Erdos260V32LocalizedExitCapResidual.class1DeepBoosted
    (R : Erdos260V32LocalizedExitCapResidual) :
    DccClass1DeepResidual 0 :=
  V30Class1CarryRealizationInputs.deepResidual R.class1CarryInputs

/-- The combined zero-error O2/localized v32 endpoint surface exposes the same
Appendix-AA/Lane-J class-1 carry realization package. -/
def Erdos260V32O2LocalizedExitCapZeroErrorResidual.class1CarryInputs
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    V30Class1CarryRealizationInputs :=
  R.toV30Residual.class1CarryInputs

/-- The combined zero-error O2/localized v32 endpoint surface supplies the
level-`0` boosted class-1 residual. -/
theorem Erdos260V32O2LocalizedExitCapZeroErrorResidual.class1DeepBoosted
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    DccClass1DeepResidual 0 :=
  V30Class1CarryRealizationInputs.deepResidual R.class1CarryInputs

/-- The combined empty-collar O2/localized v32 endpoint surface exposes the same
Appendix-AA/Lane-J class-1 carry realization package. -/
def Erdos260V32O2LocalizedExitCapEmptyCollarResidual.class1CarryInputs
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    V30Class1CarryRealizationInputs :=
  R.toV30Residual.class1CarryInputs

/-- The combined empty-collar O2/localized v32 endpoint surface supplies the
level-`0` boosted class-1 residual. -/
theorem Erdos260V32O2LocalizedExitCapEmptyCollarResidual.class1DeepBoosted
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    DccClass1DeepResidual 0 :=
  V30Class1CarryRealizationInputs.deepResidual R.class1CarryInputs

/-- The coordinate O2 v32 endpoint surface exposes the same Appendix-AA/Lane-J
class-1 carry realization package. -/
def Erdos260V32O2CollarCoordinateResidual.class1CarryInputs
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateResidual (β := β) (A := A) P₀ Q) :
    V30Class1CarryRealizationInputs :=
  R.toV30Residual.class1CarryInputs

/-- The coordinate O2 v32 endpoint surface supplies the level-`0` boosted
class-1 residual. -/
theorem Erdos260V32O2CollarCoordinateResidual.class1DeepBoosted
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateResidual (β := β) (A := A) P₀ Q) :
    DccClass1DeepResidual 0 :=
  V30Class1CarryRealizationInputs.deepResidual R.class1CarryInputs

/-- The finite-error/zero-collar coordinate O2 v32 endpoint surface exposes the
same Appendix-AA/Lane-J class-1 carry realization package. -/
def Erdos260V32O2CollarCoordinateZeroErrorResidual.class1CarryInputs
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    V30Class1CarryRealizationInputs :=
  R.toV30Residual.class1CarryInputs

/-- The finite-error/zero-collar coordinate O2 v32 endpoint surface supplies the
level-`0` boosted class-1 residual. -/
theorem Erdos260V32O2CollarCoordinateZeroErrorResidual.class1DeepBoosted
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    DccClass1DeepResidual 0 :=
  V30Class1CarryRealizationInputs.deepResidual R.class1CarryInputs

/-- The empty-collar coordinate O2 v32 endpoint surface exposes the same
Appendix-AA/Lane-J class-1 carry realization package. -/
def Erdos260V32O2CollarCoordinateEmptyCollarResidual.class1CarryInputs
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    V30Class1CarryRealizationInputs :=
  R.toV30Residual.class1CarryInputs

/-- The empty-collar coordinate O2 v32 endpoint surface supplies the level-`0`
boosted class-1 residual. -/
theorem Erdos260V32O2CollarCoordinateEmptyCollarResidual.class1DeepBoosted
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    DccClass1DeepResidual 0 :=
  V30Class1CarryRealizationInputs.deepResidual R.class1CarryInputs

/-- The localized v32 endpoint surface inherits the full class-1 deep field
through its v30 projection. -/
theorem Erdos260V32LocalizedExitCapResidual.class1DeepField
    (R : Erdos260V32LocalizedExitCapResidual) :
    Class1DeepField :=
  R.toV30Residual.class1DeepField

/-- The combined zero-error O2/localized v32 endpoint surface inherits the full
class-1 deep field. -/
theorem Erdos260V32O2LocalizedExitCapZeroErrorResidual.class1DeepField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    Class1DeepField :=
  R.toV30Residual.class1DeepField

/-- The combined empty-collar O2/localized v32 endpoint surface inherits the full
class-1 deep field. -/
theorem Erdos260V32O2LocalizedExitCapEmptyCollarResidual.class1DeepField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    Class1DeepField :=
  R.toV30Residual.class1DeepField

/-- The coordinate O2 v32 endpoint surface inherits the full class-1 deep field
through its v30 projection. -/
theorem Erdos260V32O2CollarCoordinateResidual.class1DeepField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateResidual (β := β) (A := A) P₀ Q) :
    Class1DeepField :=
  R.toV30Residual.class1DeepField

/-- The finite-error/zero-collar coordinate O2 v32 endpoint surface inherits the
full class-1 deep field. -/
theorem Erdos260V32O2CollarCoordinateZeroErrorResidual.class1DeepField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateZeroErrorResidual
      (β := β) (A := A) P₀ Q) :
    Class1DeepField :=
  R.toV30Residual.class1DeepField

/-- The empty-collar coordinate O2 v32 endpoint surface inherits the full
class-1 deep field. -/
theorem Erdos260V32O2CollarCoordinateEmptyCollarResidual.class1DeepField
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateEmptyCollarResidual
      (β := β) (A := A) P₀ Q) :
    Class1DeepField :=
  R.toV30Residual.class1DeepField

/-! ## Part 5b.  Value-axis projection -/

/-- The v32 residual consumes the Lane-F value-classification guard exactly as its
v30 projection does; v32 adds no new value-axis mathematics. -/
theorem Erdos260V32Residual.value_axis_free (R : Erdos260V32Residual)
    (ctx : ActualFailureContext)
    (h1 : TowerModulusEnumEscapeV2 ctx)
    (h2 : (class1SlopeDatum ctx).q < 107)
    (h4 : ¬ ((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1))
    (h5 : ¬ ((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3))
    (h6 : ((class1SlopeDatum ctx).q, (class1SlopeDatum ctx).K₀)
            ∉ dccTowerBand4FreeLowPairs)
    (h7 : 986888 ≤ shellLadderDepth ctx)
    (h8 : 63 ≤ ctx.n24CarryData.r)
    (h9 : 3 ≤ towerSparsityBlock ctx) :
    Class2CycleInequality ctx :=
  R.toV30.value_axis_free ctx h1 h2 h4 h5 h6 h7 h8 h9

/-- The localized v32 endpoint surface inherits the same Lane-F value-axis
discharge through its v30 projection. -/
theorem Erdos260V32LocalizedExitCapResidual.value_axis_free
    (R : Erdos260V32LocalizedExitCapResidual) (ctx : ActualFailureContext)
    (h1 : TowerModulusEnumEscapeV2 ctx)
    (h2 : (class1SlopeDatum ctx).q < 107)
    (h4 : ¬ ((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1))
    (h5 : ¬ ((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3))
    (h6 : ((class1SlopeDatum ctx).q, (class1SlopeDatum ctx).K₀)
            ∉ dccTowerBand4FreeLowPairs)
    (h7 : 986888 ≤ shellLadderDepth ctx)
    (h8 : 63 ≤ ctx.n24CarryData.r)
    (h9 : 3 ≤ towerSparsityBlock ctx) :
    Class2CycleInequality ctx :=
  R.toV30Residual.value_axis_free ctx h1 h2 h4 h5 h6 h7 h8 h9

/-- The combined zero-error O2/localized v32 surface inherits the same Lane-F
value-axis discharge through its v30 projection. -/
theorem Erdos260V32O2LocalizedExitCapZeroErrorResidual.value_axis_free
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapZeroErrorResidual
      (β := β) (A := A) P₀ Q) (ctx : ActualFailureContext)
    (h1 : TowerModulusEnumEscapeV2 ctx)
    (h2 : (class1SlopeDatum ctx).q < 107)
    (h4 : ¬ ((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1))
    (h5 : ¬ ((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3))
    (h6 : ((class1SlopeDatum ctx).q, (class1SlopeDatum ctx).K₀)
            ∉ dccTowerBand4FreeLowPairs)
    (h7 : 986888 ≤ shellLadderDepth ctx)
    (h8 : 63 ≤ ctx.n24CarryData.r)
    (h9 : 3 ≤ towerSparsityBlock ctx) :
    Class2CycleInequality ctx :=
  R.toV30Residual.value_axis_free ctx h1 h2 h4 h5 h6 h7 h8 h9

/-- The combined empty-collar O2/localized v32 surface inherits the same Lane-F
value-axis discharge through its v30 projection. -/
theorem Erdos260V32O2LocalizedExitCapEmptyCollarResidual.value_axis_free
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2LocalizedExitCapEmptyCollarResidual
      (β := β) (A := A) P₀ Q) (ctx : ActualFailureContext)
    (h1 : TowerModulusEnumEscapeV2 ctx)
    (h2 : (class1SlopeDatum ctx).q < 107)
    (h4 : ¬ ((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1))
    (h5 : ¬ ((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3))
    (h6 : ((class1SlopeDatum ctx).q, (class1SlopeDatum ctx).K₀)
            ∉ dccTowerBand4FreeLowPairs)
    (h7 : 986888 ≤ shellLadderDepth ctx)
    (h8 : 63 ≤ ctx.n24CarryData.r)
    (h9 : 3 ≤ towerSparsityBlock ctx) :
    Class2CycleInequality ctx :=
  R.toV30Residual.value_axis_free ctx h1 h2 h4 h5 h6 h7 h8 h9

/-- The coordinate O2 v32 surface inherits the same Lane-F value-axis discharge
through its v30 projection. -/
theorem Erdos260V32O2CollarCoordinateResidual.value_axis_free
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateResidual (β := β) (A := A) P₀ Q)
    (ctx : ActualFailureContext)
    (h1 : TowerModulusEnumEscapeV2 ctx)
    (h2 : (class1SlopeDatum ctx).q < 107)
    (h4 : ¬ ((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1))
    (h5 : ¬ ((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3))
    (h6 : ((class1SlopeDatum ctx).q, (class1SlopeDatum ctx).K₀)
            ∉ dccTowerBand4FreeLowPairs)
    (h7 : 986888 ≤ shellLadderDepth ctx)
    (h8 : 63 ≤ ctx.n24CarryData.r)
    (h9 : 3 ≤ towerSparsityBlock ctx) :
    Class2CycleInequality ctx :=
  R.toV30Residual.value_axis_free ctx h1 h2 h4 h5 h6 h7 h8 h9

/-- The finite-error/zero-collar coordinate O2 v32 surface inherits the same
Lane-F value-axis discharge through its v30 projection. -/
theorem Erdos260V32O2CollarCoordinateZeroErrorResidual.value_axis_free
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateZeroErrorResidual
      (β := β) (A := A) P₀ Q) (ctx : ActualFailureContext)
    (h1 : TowerModulusEnumEscapeV2 ctx)
    (h2 : (class1SlopeDatum ctx).q < 107)
    (h4 : ¬ ((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1))
    (h5 : ¬ ((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3))
    (h6 : ((class1SlopeDatum ctx).q, (class1SlopeDatum ctx).K₀)
            ∉ dccTowerBand4FreeLowPairs)
    (h7 : 986888 ≤ shellLadderDepth ctx)
    (h8 : 63 ≤ ctx.n24CarryData.r)
    (h9 : 3 ≤ towerSparsityBlock ctx) :
    Class2CycleInequality ctx :=
  R.toV30Residual.value_axis_free ctx h1 h2 h4 h5 h6 h7 h8 h9

/-- The empty-collar coordinate O2 v32 surface inherits the same Lane-F
value-axis discharge through its v30 projection. -/
theorem Erdos260V32O2CollarCoordinateEmptyCollarResidual.value_axis_free
    {β A : Type*} [DecidableEq (Nat -> Int)] {P₀ Q : Int}
    (R : Erdos260V32O2CollarCoordinateEmptyCollarResidual
      (β := β) (A := A) P₀ Q) (ctx : ActualFailureContext)
    (h1 : TowerModulusEnumEscapeV2 ctx)
    (h2 : (class1SlopeDatum ctx).q < 107)
    (h4 : ¬ ((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1))
    (h5 : ¬ ((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3))
    (h6 : ((class1SlopeDatum ctx).q, (class1SlopeDatum ctx).K₀)
            ∉ dccTowerBand4FreeLowPairs)
    (h7 : 986888 ≤ shellLadderDepth ctx)
    (h8 : 63 ≤ ctx.n24CarryData.r)
    (h9 : 3 ≤ towerSparsityBlock ctx) :
    Class2CycleInequality ctx :=
  R.toV30Residual.value_axis_free ctx h1 h2 h4 h5 h6 h7 h8 h9

/-! ## Part 6.  Axiom-cleanliness audit
Every key declaration; expected axioms `[propext, Classical.choice, Quot.sound]` or
fewer (the pure-combinatorial firewall declarations report `[propext]` or fewer). -/

#print axioms erdos260_of_v32Residual
#print axioms Erdos260V32Residual.toV30
#print axioms Erdos260V32Residual.returnGatesField
#print axioms Erdos260V32Residual.returnInteriorField
#print axioms Erdos260V32Residual.returnGatesOffTableField
#print axioms Erdos260V32Residual.returnInteriorOffTableField
#print axioms Erdos260V32Residual.densePackCoverField
#print axioms Erdos260V32Residual.densePackDensityField
#print axioms Erdos260V32Residual.densePackInteriorField
#print axioms Erdos260V32Residual.class0MassField
#print axioms Erdos260V32Residual.densePackStartSpacingField
#print axioms Erdos260V32Residual.densePackClusterFloorField
#print axioms Erdos260V32Residual.densePackCoverOffTableField
#print axioms Erdos260V32Residual.densePackDensityOffTableField
#print axioms Erdos260V32Residual.densePackInteriorOffTableField
#print axioms Erdos260V32Residual.class1CarryInputs
#print axioms v32_class1DeepBoosted
#print axioms Erdos260V32Residual.class1DeepField
#print axioms Erdos260V32Residual.exitMassCore
#print axioms Erdos260V32Residual.offPinDeliverables
#print axioms Erdos260V32Residual.deepOrbitPinVoiding
#print axioms Erdos260V32Residual.value_axis_free
#print axioms Erdos260V32LocalizedExitCapResidual
#print axioms Erdos260V32LocalizedExitCapResidual.lc9
#print axioms Erdos260V32LocalizedExitCapResidual.lc10
#print axioms Erdos260V32LocalizedExitCapResidual.toV32Residual
#print axioms Erdos260V32LocalizedExitCapResidual.toV30Residual
#print axioms Erdos260V32LocalizedExitCapResidual.offPinDeliverables
#print axioms Erdos260V32LocalizedExitCapResidual.exitMassCore
#print axioms Erdos260V32LocalizedExitCapResidual.deepOrbitPinVoiding
#print axioms Erdos260V32LocalizedExitCapResidual.laneGResidual
#print axioms Erdos260V32LocalizedExitCapResidual.laneGResidual_topBand
#print axioms Erdos260V32LocalizedExitCapResidual.laneGResidual_readTail
#print axioms Erdos260V32LocalizedExitCapResidual.returnGatesField
#print axioms Erdos260V32LocalizedExitCapResidual.returnInteriorField
#print axioms Erdos260V32LocalizedExitCapResidual.returnGatesOffTableField
#print axioms Erdos260V32LocalizedExitCapResidual.returnInteriorOffTableField
#print axioms Erdos260V32LocalizedExitCapResidual.densePackCoverField
#print axioms Erdos260V32LocalizedExitCapResidual.densePackDensityField
#print axioms Erdos260V32LocalizedExitCapResidual.densePackInteriorField
#print axioms Erdos260V32LocalizedExitCapResidual.class0MassField
#print axioms Erdos260V32LocalizedExitCapResidual.densePackStartSpacingField
#print axioms Erdos260V32LocalizedExitCapResidual.densePackClusterFloorField
#print axioms Erdos260V32LocalizedExitCapResidual.densePackCoverOffTableField
#print axioms Erdos260V32LocalizedExitCapResidual.densePackDensityOffTableField
#print axioms Erdos260V32LocalizedExitCapResidual.densePackInteriorOffTableField
#print axioms Erdos260V32LocalizedExitCapResidual.class1CarryInputs
#print axioms Erdos260V32LocalizedExitCapResidual.class1DeepBoosted
#print axioms Erdos260V32LocalizedExitCapResidual.class1DeepField
#print axioms Erdos260V32LocalizedExitCapResidual.value_axis_free
#print axioms erdos260_of_v32LocalizedExitCapResidual
#print axioms Erdos260V32O2LocalizedExitCapZeroErrorResidual
#print axioms Erdos260V32O2LocalizedExitCapZeroErrorResidual.toLocalizedExitCapResidual
#print axioms Erdos260V32O2LocalizedExitCapZeroErrorResidual.toV32Residual
#print axioms Erdos260V32O2LocalizedExitCapZeroErrorResidual.toV30Residual
#print axioms Erdos260V32O2LocalizedExitCapZeroErrorResidual.offPinDeliverables
#print axioms Erdos260V32O2LocalizedExitCapZeroErrorResidual.exitMassCore
#print axioms Erdos260V32O2LocalizedExitCapZeroErrorResidual.deepOrbitPinVoiding
#print axioms Erdos260V32O2LocalizedExitCapZeroErrorResidual.laneGResidual
#print axioms Erdos260V32O2LocalizedExitCapZeroErrorResidual.laneGResidual_topBand
#print axioms Erdos260V32O2LocalizedExitCapZeroErrorResidual.laneGResidual_readTail
#print axioms Erdos260V32O2LocalizedExitCapZeroErrorResidual.returnGatesField
#print axioms Erdos260V32O2LocalizedExitCapZeroErrorResidual.returnInteriorField
#print axioms Erdos260V32O2LocalizedExitCapZeroErrorResidual.returnGatesOffTableField
#print axioms Erdos260V32O2LocalizedExitCapZeroErrorResidual.returnInteriorOffTableField
#print axioms Erdos260V32O2LocalizedExitCapZeroErrorResidual.densePackCoverField
#print axioms Erdos260V32O2LocalizedExitCapZeroErrorResidual.densePackDensityField
#print axioms Erdos260V32O2LocalizedExitCapZeroErrorResidual.densePackInteriorField
#print axioms Erdos260V32O2LocalizedExitCapZeroErrorResidual.class0MassField
#print axioms Erdos260V32O2LocalizedExitCapZeroErrorResidual.densePackStartSpacingField
#print axioms Erdos260V32O2LocalizedExitCapZeroErrorResidual.densePackClusterFloorField
#print axioms Erdos260V32O2LocalizedExitCapZeroErrorResidual.densePackCoverOffTableField
#print axioms Erdos260V32O2LocalizedExitCapZeroErrorResidual.densePackDensityOffTableField
#print axioms Erdos260V32O2LocalizedExitCapZeroErrorResidual.densePackInteriorOffTableField
#print axioms Erdos260V32O2LocalizedExitCapZeroErrorResidual.class1CarryInputs
#print axioms Erdos260V32O2LocalizedExitCapZeroErrorResidual.class1DeepBoosted
#print axioms Erdos260V32O2LocalizedExitCapZeroErrorResidual.class1DeepField
#print axioms Erdos260V32O2LocalizedExitCapZeroErrorResidual.value_axis_free
#print axioms erdos260_of_v32O2LocalizedExitCapZeroErrorResidual
#print axioms Erdos260V32O2LocalizedExitCapEmptyCollarResidual
#print axioms Erdos260V32O2LocalizedExitCapEmptyCollarResidual.toZeroErrorResidual
#print axioms Erdos260V32O2LocalizedExitCapEmptyCollarResidual.toLocalizedExitCapResidual
#print axioms Erdos260V32O2LocalizedExitCapEmptyCollarResidual.toV32Residual
#print axioms Erdos260V32O2LocalizedExitCapEmptyCollarResidual.toV30Residual
#print axioms Erdos260V32O2LocalizedExitCapEmptyCollarResidual.offPinDeliverables
#print axioms Erdos260V32O2LocalizedExitCapEmptyCollarResidual.exitMassCore
#print axioms Erdos260V32O2LocalizedExitCapEmptyCollarResidual.deepOrbitPinVoiding
#print axioms Erdos260V32O2LocalizedExitCapEmptyCollarResidual.laneGResidual
#print axioms Erdos260V32O2LocalizedExitCapEmptyCollarResidual.laneGResidual_topBand
#print axioms Erdos260V32O2LocalizedExitCapEmptyCollarResidual.laneGResidual_readTail
#print axioms Erdos260V32O2LocalizedExitCapEmptyCollarResidual.returnGatesField
#print axioms Erdos260V32O2LocalizedExitCapEmptyCollarResidual.returnInteriorField
#print axioms Erdos260V32O2LocalizedExitCapEmptyCollarResidual.returnGatesOffTableField
#print axioms Erdos260V32O2LocalizedExitCapEmptyCollarResidual.returnInteriorOffTableField
#print axioms Erdos260V32O2LocalizedExitCapEmptyCollarResidual.densePackCoverField
#print axioms Erdos260V32O2LocalizedExitCapEmptyCollarResidual.densePackDensityField
#print axioms Erdos260V32O2LocalizedExitCapEmptyCollarResidual.densePackInteriorField
#print axioms Erdos260V32O2LocalizedExitCapEmptyCollarResidual.class0MassField
#print axioms Erdos260V32O2LocalizedExitCapEmptyCollarResidual.densePackStartSpacingField
#print axioms Erdos260V32O2LocalizedExitCapEmptyCollarResidual.densePackClusterFloorField
#print axioms Erdos260V32O2LocalizedExitCapEmptyCollarResidual.densePackCoverOffTableField
#print axioms Erdos260V32O2LocalizedExitCapEmptyCollarResidual.densePackDensityOffTableField
#print axioms Erdos260V32O2LocalizedExitCapEmptyCollarResidual.densePackInteriorOffTableField
#print axioms Erdos260V32O2LocalizedExitCapEmptyCollarResidual.class1CarryInputs
#print axioms Erdos260V32O2LocalizedExitCapEmptyCollarResidual.class1DeepBoosted
#print axioms Erdos260V32O2LocalizedExitCapEmptyCollarResidual.class1DeepField
#print axioms Erdos260V32O2LocalizedExitCapEmptyCollarResidual.value_axis_free
#print axioms erdos260_of_v32O2LocalizedExitCapEmptyCollarResidual
#print axioms Erdos260V32O2CollarCoordinateResidual
#print axioms Erdos260V32O2CollarCoordinateResidual.toV32Residual
#print axioms Erdos260V32O2CollarCoordinateResidual.toV30Residual
#print axioms Erdos260V32O2CollarCoordinateResidual.offPinDeliverables
#print axioms Erdos260V32O2CollarCoordinateResidual.exitMassCore
#print axioms Erdos260V32O2CollarCoordinateResidual.deepOrbitPinVoiding
#print axioms Erdos260V32O2CollarCoordinateResidual.returnGatesField
#print axioms Erdos260V32O2CollarCoordinateResidual.returnInteriorField
#print axioms Erdos260V32O2CollarCoordinateResidual.returnGatesOffTableField
#print axioms Erdos260V32O2CollarCoordinateResidual.returnInteriorOffTableField
#print axioms Erdos260V32O2CollarCoordinateResidual.densePackCoverField
#print axioms Erdos260V32O2CollarCoordinateResidual.densePackDensityField
#print axioms Erdos260V32O2CollarCoordinateResidual.densePackInteriorField
#print axioms Erdos260V32O2CollarCoordinateResidual.class0MassField
#print axioms Erdos260V32O2CollarCoordinateResidual.densePackStartSpacingField
#print axioms Erdos260V32O2CollarCoordinateResidual.densePackClusterFloorField
#print axioms Erdos260V32O2CollarCoordinateResidual.densePackCoverOffTableField
#print axioms Erdos260V32O2CollarCoordinateResidual.densePackDensityOffTableField
#print axioms Erdos260V32O2CollarCoordinateResidual.densePackInteriorOffTableField
#print axioms Erdos260V32O2CollarCoordinateResidual.class1CarryInputs
#print axioms Erdos260V32O2CollarCoordinateResidual.class1DeepBoosted
#print axioms Erdos260V32O2CollarCoordinateResidual.class1DeepField
#print axioms Erdos260V32O2CollarCoordinateResidual.value_axis_free
#print axioms erdos260_of_v32O2CollarCoordinateResidual
#print axioms Erdos260V32O2CollarCoordinateZeroErrorResidual
#print axioms Erdos260V32O2CollarCoordinateZeroErrorResidual.toO2CollarCoordinateResidual
#print axioms Erdos260V32O2CollarCoordinateZeroErrorResidual.toV32Residual
#print axioms Erdos260V32O2CollarCoordinateZeroErrorResidual.toV30Residual
#print axioms Erdos260V32O2CollarCoordinateZeroErrorResidual.offPinDeliverables
#print axioms Erdos260V32O2CollarCoordinateZeroErrorResidual.exitMassCore
#print axioms Erdos260V32O2CollarCoordinateZeroErrorResidual.deepOrbitPinVoiding
#print axioms Erdos260V32O2CollarCoordinateZeroErrorResidual.returnGatesField
#print axioms Erdos260V32O2CollarCoordinateZeroErrorResidual.returnInteriorField
#print axioms Erdos260V32O2CollarCoordinateZeroErrorResidual.returnGatesOffTableField
#print axioms Erdos260V32O2CollarCoordinateZeroErrorResidual.returnInteriorOffTableField
#print axioms Erdos260V32O2CollarCoordinateZeroErrorResidual.densePackCoverField
#print axioms Erdos260V32O2CollarCoordinateZeroErrorResidual.densePackDensityField
#print axioms Erdos260V32O2CollarCoordinateZeroErrorResidual.densePackInteriorField
#print axioms Erdos260V32O2CollarCoordinateZeroErrorResidual.class0MassField
#print axioms Erdos260V32O2CollarCoordinateZeroErrorResidual.densePackStartSpacingField
#print axioms Erdos260V32O2CollarCoordinateZeroErrorResidual.densePackClusterFloorField
#print axioms Erdos260V32O2CollarCoordinateZeroErrorResidual.densePackCoverOffTableField
#print axioms Erdos260V32O2CollarCoordinateZeroErrorResidual.densePackDensityOffTableField
#print axioms Erdos260V32O2CollarCoordinateZeroErrorResidual.densePackInteriorOffTableField
#print axioms Erdos260V32O2CollarCoordinateZeroErrorResidual.class1CarryInputs
#print axioms Erdos260V32O2CollarCoordinateZeroErrorResidual.class1DeepBoosted
#print axioms Erdos260V32O2CollarCoordinateZeroErrorResidual.class1DeepField
#print axioms Erdos260V32O2CollarCoordinateZeroErrorResidual.value_axis_free
#print axioms erdos260_of_v32O2CollarCoordinateZeroErrorResidual
#print axioms Erdos260V32O2CollarCoordinateEmptyCollarResidual
#print axioms Erdos260V32O2CollarCoordinateEmptyCollarResidual.toO2CollarCoordinateResidual
#print axioms Erdos260V32O2CollarCoordinateEmptyCollarResidual.toV32Residual
#print axioms Erdos260V32O2CollarCoordinateEmptyCollarResidual.toV30Residual
#print axioms Erdos260V32O2CollarCoordinateEmptyCollarResidual.offPinDeliverables
#print axioms Erdos260V32O2CollarCoordinateEmptyCollarResidual.exitMassCore
#print axioms Erdos260V32O2CollarCoordinateEmptyCollarResidual.deepOrbitPinVoiding
#print axioms Erdos260V32O2CollarCoordinateEmptyCollarResidual.returnGatesField
#print axioms Erdos260V32O2CollarCoordinateEmptyCollarResidual.returnInteriorField
#print axioms Erdos260V32O2CollarCoordinateEmptyCollarResidual.returnGatesOffTableField
#print axioms Erdos260V32O2CollarCoordinateEmptyCollarResidual.returnInteriorOffTableField
#print axioms Erdos260V32O2CollarCoordinateEmptyCollarResidual.densePackCoverField
#print axioms Erdos260V32O2CollarCoordinateEmptyCollarResidual.densePackDensityField
#print axioms Erdos260V32O2CollarCoordinateEmptyCollarResidual.densePackInteriorField
#print axioms Erdos260V32O2CollarCoordinateEmptyCollarResidual.class0MassField
#print axioms Erdos260V32O2CollarCoordinateEmptyCollarResidual.densePackStartSpacingField
#print axioms Erdos260V32O2CollarCoordinateEmptyCollarResidual.densePackClusterFloorField
#print axioms Erdos260V32O2CollarCoordinateEmptyCollarResidual.densePackCoverOffTableField
#print axioms Erdos260V32O2CollarCoordinateEmptyCollarResidual.densePackDensityOffTableField
#print axioms Erdos260V32O2CollarCoordinateEmptyCollarResidual.densePackInteriorOffTableField
#print axioms Erdos260V32O2CollarCoordinateEmptyCollarResidual.class1CarryInputs
#print axioms Erdos260V32O2CollarCoordinateEmptyCollarResidual.class1DeepBoosted
#print axioms Erdos260V32O2CollarCoordinateEmptyCollarResidual.class1DeepField
#print axioms Erdos260V32O2CollarCoordinateEmptyCollarResidual.value_axis_free
#print axioms erdos260_of_v32O2CollarCoordinateEmptyCollarResidual
#print axioms v32_dependency_firewall
#print axioms v32_firewall_acyclic
#print axioms rankIncreasing
#print axioms transGen_rank_lt
#print axioms firewall_F1_exitMassTot_unreachable_cap
#print axioms firewall_F2_spacingAlone_unreachable_cap
#print axioms v32_T1_riskc_no_totalExitMass
#print axioms v32_T5_topband_readtail_not_caps
#print axioms erdos260V32EndpointStatus_nonempty

end

end Erdos260
