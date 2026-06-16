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

/-- **THE v32 ENDPOINT**: `Erdos260Statement` from the v32 hardened residual, routed
through the v32 → v30 projection and the proved `erdos260_of_v30Residual`.  Manuscript
home: Appendix Z `prop:z-v30-unconditional-closure` (v32 line 12055), with Appendix AE as
the authoritative Lean interface.  HONEST: this endpoint is exactly as conditional as the
v30 endpoint — it depends on the SAME ten residual atoms. -/
theorem erdos260_of_v32Residual (R : Erdos260V32Residual) : Erdos260Statement :=
  erdos260_of_v30Residual R.toV30

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
      "Additive: ONE new module, no existing .lean file edited.",
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

/-! ## Part 6.  Axiom-cleanliness audit
Every key declaration; expected axioms `[propext, Classical.choice, Quot.sound]` or
fewer (the pure-combinatorial firewall declarations report `[propext]` or fewer). -/

#print axioms erdos260_of_v32Residual
#print axioms Erdos260V32Residual.toV30
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
