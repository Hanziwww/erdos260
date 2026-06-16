import Erdos260.Constants

/-!
# V30 Lane D — Bounded-period retirement (the `(C1)` linchpin)

This module transcribes and proves the **bounded-output retirement** that v30 uses to
empty the off-pin *unsafe exit-light long-cycle core* (`proof_v4_repaired_core_v30.tex`
Appendix AC, lines 11497–11601), and performs the **non-circularity audit** demanded by
the V30 reroute plan (risk (a), the linchpin).

## The v30 claim being transcribed

`prop:ac-unsafe-core-empty` (v30 line 11579): the unsafe off-pin core
`𝔠_unsafe^offpin = { fibres with b = 1, c ≥ 64, 1536·⌊(r+c)/c⌋ > 31·c }` is **empty**.

The argument (lines 11497–11601):

* `lem:ac-primitive-period-divides-cycle` (11497): the primitive transfer period `p`
  of a recurrent tower cycle divides its refined length `c`, hence `p ≤ c`.
* `lem:ac-bounded-before-exposure` (11516): a recurrent transfer with `p ≤ P_hand·L+C_Q`
  is selected into the bounded-output class `𝔒_bdd` **before** any M.5/L.3 off-pin
  long-cycle exposure cell is formed (the M.5/L.3 ledger is a *post-priority residual*).
  This is the priority-order clause of Convention `conv:constants` (lines 279–282).
* `lem:ac-bounded-tower-retirement` (11533): consequently no cycle with `c ≤ P_hand·L+C_Q`
  survives in the M.5/L.3 ledger.  A *surviving* fibre therefore has `c > P_hand·L+C_Q`.
* `lem:ac-surviving-long-cycle-unit-overlap` (11555): with `r = ⌊κ·L⌋` and the constants
  hierarchy `κ < P_hand/2` (Convention 2.0e, line 317), `c > P_hand·L+C_Q > r`, so the
  overlap floor `⌊(r+c)/c⌋ = 1`.
* Then the unsafe inequality `1536·1 > 31·c` reads `1536 > 31·c`, impossible for `c ≥ 64`
  (since `31·64 = 1984 > 1536`).  Empty core.

## In-tree constants (Convention 2.0d, `Erdos260.Constants`)

`manuscriptPhand = 64·(H_lift + C_◇ + 1) = 2182720` (`manuscriptPhand_eq`, line 276 of the
manuscript) and `manuscriptKappa = C_drop·c₁·ε` with `manuscriptKappa < 1/16`.  The
threshold `P_hand·L + C_Q` is modelled by `boundedThreshold L = phandNat·L + cQNat` with
`phandNat = 2182720` (`phandNat_real_eq_manuscript` checks `(phandNat : ℝ) = manuscriptPhand`)
and `cQNat = manuscriptCQ_T = 1`.  `r = ⌊κ·L⌋` is `rActive L`.  The constants discipline
`κ < P_hand/2` is `kappa_lt_phand_div_two`; `P_hand` is a fixed numeral chosen before `κ`.

## NON-CIRCULARITY VERDICT (the critical deliverable)

**PROVED non-circular.**  The retirement does **not** use `(C1)` (the off-pin exit-mass
cap) in any form.  The machine-checkable evidence:

1. *Import isolation.*  This module imports **only** `Erdos260.Constants` (and `Mathlib`).
   It does **not** import `ExitMassControl`, `ExitMassCoreTranscription`,
   `MissDistanceClosure`, or any module mentioning the off-pin exit cap / `ExitMassControlOffPin`.
   The retirement and the unsafe-core emptiness are therefore established with **no access**
   to `(C1)`.
2. *Type isolation.*  The retirement interface `PriorityRouting` is stated purely in terms
   of the **period predicate** (`p ≤ boundedThreshold L`) and the **output-class partition**
   (`inBdd`/`inLedger`).  No field mentions exit mass, normalized exposure, or any `(C1)`
   quantity.  Convention 2.0d's clause `bdd_of_bounded_period` and the post-priority
   disjointness `ledger_disjoint_bdd` are both pure priority/order facts.
3. *Constructive witness.*  `periodRouting` builds a complete `PriorityRouting` from the
   period comparison **alone** (`inBdd := p ≤ threshold`, `inLedger := threshold < p`),
   demonstrating the interface is satisfiable by the bounded-period convention by itself,
   with no exit-mass input whatsoever.

**Residual atoms (both `(C1)`-independent, in-tree, structurally upstream of M.5/L.3).**
The retirement is *conditional* on exactly two named inputs, neither of which is `(C1)`:

* **(D1) priority routing.**  The actual M.5/L.3 ledger must satisfy `PriorityRouting`'s two
  fields for the genuine ledger predicate.  Manuscript source: Lemma L.4.1 (line 6744,
  "*Before applying the long-run trichotomy, periods `p ≤ P_hand·L+C_Q` are assigned to the
  bounded `O_Q(L)`-scale local Kraft/CNL output*") and Lemma M.4.1 (line 7649, bounded clause
  7658).  These route by **period**, **before** the trichotomy and **before** the M.5/L.3 ledger — hence before,
  and independent of, `(C1)`.
* **(D2) budget affordability.**  The deleted `𝔒_bdd` mass is paid by the **CNL/Kraft entropy
  budget**, not thrown away.  Manuscript source: line 7659 ("*controlled by the one-step
  Kraft/CNL estimate*"), line 7684 ("*covered by the bounded CNL/Kraft terms*"); the six-class
  output decomposition `𝔒 = 𝔒_D ⊔ 𝔒_P ⊔ 𝔒_E ⊔ 𝔒_CNL ⊔ 𝔒_bdd ⊔ 𝔒_V` (line 340).
  In-tree atoms: `Erdos260.N33AbsorptionCore.bddBudgetLe_ofShell` and the absorption bound
  `termMass ≤ O_D+O_P+O_E+O_CNL+O_bdd` (`AppendixNVariationLeafConstruction`), the Kraft cores
  `CNLKraftCountCore`/`CNLScalarBudgetCore`, and the periodic-density kill
  `Erdos260.periodic_no_sparse_shell` (`OnsetBoundClosure`) for the persistent-periodic part
  (periods `≤ 2^19`).  These belong to the Appendix G/N stopped-recurrence budget, which is
  the SAME budget the entire chain-compression certificate uses and is established
  **before** the off-pin exit cap.  `(C1)` is a cap on the M.5/L.3 ledger (the
  *complement* of `𝔒_bdd`); the two charges live on disjoint priority cells, so there is no
  circular dependency and no double-counting.

**Honest caveat.**  (D1)+(D2) are genuine obligations — not vacuous.  v30 itself treats the
retirement as a *convention* (line 281: "*a local bookkeeping device*") rather than re-proving
the budget.  What this module proves rigorously is: (i) the period/order skeleton
(`p ≤ c`, ledger ⟹ `p > threshold`, survivor ⟹ `c > threshold`); (ii) the arithmetic that
the unsafe core is then empty; (iii) the constants discipline; and (iv) that ALL of this is
free of `(C1)`.  The budget affordability (D2) is the substantive measure-theoretic input
supplied by the named in-tree atoms; if it failed it would fail by **budget overflow**, never
by needing `(C1)` — so v30's `(C1)` closure is **not circular**.

## Consumable shape for Lane C (`V30OffPinExitCap`)

Lane C instantiates `PriorityRouting` with the real failure-context ledger predicate and
discharges the two fields from L.4/M.4 (the in-tree priority routing), then consumes
`unsafeCore_empty_of_routing` to obtain `𝔠_unsafe^offpin = ∅`, feeding the safe-cone cap
into `ExitMassControlOffPin` via `emc2_offPin_of_regime`.  The minimal residual atom that
Lane C must still provide is the **(D1)+(D2)** priority/budget instance for the genuine ledger.
-/

namespace Erdos260
namespace V30BoundedPeriodRetirement

open Erdos260

/-! ## 1.  Constants (Convention 2.0d / 2.0e), faithful to `Erdos260.Constants` -/

/-- `P_hand = 64·(H_lift + C_◇ + 1) = 2182720` (Convention 2.0d, v30 line 276),
as a `ℕ`.  Faithful to the in-tree real constant `manuscriptPhand` — see
`phandNat_real_eq_manuscript`. -/
def phandNat : ℕ := 2182720

/-- `C_Q` in `T₀ = 2L + C_Q` (`manuscriptCQ_T = 1`), as a `ℕ`. -/
def cQNat : ℕ := manuscriptCQ_T

/-- The **bounded-period threshold** `P_hand·L + C_Q` of Convention 2.0d (line 279):
a primitive run of period at most this value is a bounded `O_Q(L)`-scale output `𝔒_bdd`. -/
def boundedThreshold (L : ℕ) : ℕ := phandNat * L + cQNat

theorem cQNat_eq : cQNat = 1 := rfl

theorem boundedThreshold_eq (L : ℕ) : boundedThreshold L = 2182720 * L + 1 := rfl

/-- **Faithfulness check**: the `ℕ` constant `phandNat` equals the in-tree real
Convention-2.0d constant `manuscriptPhand`. -/
theorem phandNat_real_eq_manuscript : (phandNat : ℝ) = manuscriptPhand := by
  rw [manuscriptPhand_eq]; norm_num [phandNat]

/-- **Constants discipline (Convention 2.0e, v30 line 317)**: `κ < P_hand / 2`.
`P_hand = 2182720` is a fixed numeral chosen *before* `κ`; `κ < 1/16 < 1091360`. -/
theorem kappa_lt_phand_div_two : manuscriptKappa < manuscriptPhand / 2 := by
  rw [manuscriptPhand_eq]
  linarith [manuscriptKappa_lt_one_sixteenth]

/-- The active deep AP-fibre reach `r = ⌊κ·L⌋` (manuscript `r`, Convention 2.0e). -/
noncomputable def rActive (L : ℕ) : ℕ := ⌊manuscriptKappa * (L : ℝ)⌋₊

/-- `r = ⌊κ·L⌋ ≤ L`, since `κ < 1`. -/
theorem rActive_le_scale (L : ℕ) : rActive L ≤ L := by
  unfold rActive
  have hkle : manuscriptKappa ≤ 1 := le_of_lt manuscriptKappa_lt_one
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have hmul : manuscriptKappa * (L : ℝ) ≤ (L : ℝ) := by nlinarith [hkle, hL0]
  calc ⌊manuscriptKappa * (L : ℝ)⌋₊ ≤ ⌊(L : ℝ)⌋₊ := Nat.floor_mono hmul
    _ = L := Nat.floor_natCast L

/-- **`r < P_hand·L + C_Q`** (the bound underlying `lem:ac-surviving-long-cycle-unit-overlap`):
`r ≤ L < P_hand·L + C_Q` since `P_hand ≥ 1` and `C_Q ≥ 1`. -/
theorem rActive_lt_threshold (L : ℕ) : rActive L < boundedThreshold L := by
  have h1 : rActive L ≤ L := rActive_le_scale L
  have h2 : L < boundedThreshold L := by rw [boundedThreshold_eq]; omega
  omega

/-! ## 2.  Recurrent tower cycle parameters and `p ∣ c` (lem:ac-primitive-period-divides-cycle) -/

/-- Parameters of a terminal-labelled recurrent tower cycle as seen by the M.5/L.3 ledger:
refined cycle length `c`, primitive transfer period `p`, number of exit phases `b`. -/
structure CycleParams where
  /-- refined cycle length `c`. -/
  c : ℕ
  /-- primitive transfer period `p`. -/
  p : ℕ
  /-- number of exit phases `b`. -/
  b : ℕ
  /-- a genuine cycle has positive length. -/
  hc_pos : 0 < c
  /-- the primitive period is positive. -/
  hp_pos : 0 < p
  /-- `lem:ac-primitive-period-divides-cycle` (v30 line 11497): `p ∣ c`. -/
  hp_dvd_c : p ∣ c

/-- **`lem:ac-primitive-period-divides-cycle`** (v30 line 11497): `p ≤ c`. -/
theorem primitivePeriod_le_cycleLength (cyc : CycleParams) : cyc.p ≤ cyc.c :=
  Nat.le_of_dvd cyc.hc_pos cyc.hp_dvd_c

/-! ## 3.  The priority-order retirement interface (Convention 2.0d, `(C1)`-free) -/

/-- **The bounded-output priority routing** of Convention 2.0d.  At a fixed scale `L`,
the recurrent transfers are partitioned into output classes; `inBdd` marks the bounded
class `𝔒_bdd`, `inLedger` marks a *live* M.5/L.3 off-pin long-cycle exposure fibre.

Both axioms are pure priority/order statements — **no exit-mass / `(C1)` quantity appears**:

* `bdd_of_bounded_period` is Convention 2.0d (line 279): period `≤ P_hand·L+C_Q ⟹ 𝔒_bdd`.
* `ledger_disjoint_bdd` is the post-priority formation (`lem:ac-bounded-before-exposure`,
  line 11516): the M.5/L.3 ledger is formed after `𝔒_bdd` is deleted, so the two are disjoint.

This is the object Lane C instantiates with the genuine ledger predicate, discharging the
two fields from the in-tree L.4/M.4 priority routing (residual atom (D1)). -/
structure PriorityRouting (L : ℕ) where
  /-- the live M.5/L.3 off-pin long-cycle exposure ledger. -/
  inLedger : CycleParams → Prop
  /-- the bounded-output class `𝔒_bdd`. -/
  inBdd : CycleParams → Prop
  /-- Convention 2.0d (line 279): bounded period ⟹ bounded output. -/
  bdd_of_bounded_period : ∀ cyc : CycleParams, cyc.p ≤ boundedThreshold L → inBdd cyc
  /-- `lem:ac-bounded-before-exposure` (line 11516): `𝔒_bdd` is deleted before the ledger. -/
  ledger_disjoint_bdd : ∀ cyc : CycleParams, inBdd cyc → ¬ inLedger cyc

/-- **`lem:ac-bounded-before-exposure` (contrapositive)**: a live M.5/L.3 ledger fibre has
primitive period strictly above the bounded threshold. -/
theorem ledger_period_gt {L : ℕ} (R : PriorityRouting L) (cyc : CycleParams)
    (h : R.inLedger cyc) : boundedThreshold L < cyc.p := by
  rcases Nat.lt_or_ge (boundedThreshold L) cyc.p with hgt | hle
  · exact hgt
  · exact absurd h (R.ledger_disjoint_bdd cyc (R.bdd_of_bounded_period cyc hle))

/-- **Non-circularity witness**: a complete `PriorityRouting` built from the period
comparison ALONE — `inBdd cyc := p ≤ threshold`, `inLedger cyc := threshold < p` — with
**no** exit-mass / `(C1)` input.  Certifies the retirement interface is satisfiable by the
bounded-period convention by itself. -/
def periodRouting (L : ℕ) : PriorityRouting L where
  inLedger cyc := boundedThreshold L < cyc.p
  inBdd cyc := cyc.p ≤ boundedThreshold L
  bdd_of_bounded_period _ h := h
  ledger_disjoint_bdd _ h := by intro hlt; omega

/-! ## 4.  The retirement lemma and unit-overlap consequence -/

/-- **The Lane-C-consumable retirement datum** (`lem:ac-bounded-tower-retirement`, v30 line
11533, survivor form): a surviving off-pin recurrent fibre has refined length above the
bounded threshold, `c > P_hand·L + C_Q`. -/
def BoundedPeriodRetired (L : ℕ) (cyc : CycleParams) : Prop :=
  boundedThreshold L < cyc.c

/-- **`lem:ac-bounded-tower-retirement`** (v30 line 11533): from the priority routing and
`p ∣ c` (`p ≤ c`), a survivor of the M.5/L.3 ledger has `c > P_hand·L + C_Q`. -/
theorem boundedPeriodRetired_of_routing {L : ℕ} (R : PriorityRouting L)
    (cyc : CycleParams) (h : R.inLedger cyc) : BoundedPeriodRetired L cyc := by
  have hpgt : boundedThreshold L < cyc.p := ledger_period_gt R cyc h
  have hpc : cyc.p ≤ cyc.c := primitivePeriod_le_cycleLength cyc
  unfold BoundedPeriodRetired
  omega

/-- **`lem:ac-bounded-tower-retirement`** (direct form): a cycle with `c ≤ P_hand·L + C_Q`
is retired (cannot be a live M.5/L.3 ledger fibre). -/
theorem not_inLedger_of_cycle_bounded {L : ℕ} (R : PriorityRouting L)
    (cyc : CycleParams) (hbound : cyc.c ≤ boundedThreshold L) : ¬ R.inLedger cyc := by
  intro h
  have hret : BoundedPeriodRetired L cyc := boundedPeriodRetired_of_routing R cyc h
  unfold BoundedPeriodRetired at hret
  omega

/-- **`lem:ac-surviving-long-cycle-unit-overlap`** (v30 line 11555): a retired-survivor cycle
has `r < c`, hence the overlap floor `⌊(r+c)/c⌋ = 1`. -/
theorem surviving_unit_overlap {L : ℕ} {cyc : CycleParams}
    (hret : BoundedPeriodRetired L cyc) : (rActive L + cyc.c) / cyc.c = 1 := by
  have hrc : rActive L < cyc.c := by
    have hrT : rActive L < boundedThreshold L := rActive_lt_threshold L
    unfold BoundedPeriodRetired at hret
    omega
  have hc_pos : 0 < cyc.c := by omega
  have h0 : rActive L / cyc.c = 0 := Nat.div_eq_of_lt hrc
  have h1 : (rActive L + cyc.c) / cyc.c = rActive L / cyc.c + 1 :=
    Nat.add_div_right (rActive L) hc_pos
  rw [h1, h0]

/-! ## 5.  The unsafe off-pin core is empty (prop:ac-unsafe-core-empty) -/

/-- **`def:ab-unsafe-core`** (v30 line 11346): the unsafe exit-light long-cycle shape
`b = 1`, `c ≥ 64`, `1536·⌊(r+c)/c⌋ > 31·c`. -/
def UnsafeOffPinCore (L : ℕ) (cyc : CycleParams) : Prop :=
  cyc.b = 1 ∧ 64 ≤ cyc.c ∧ 31 * cyc.c < 1536 * ((rActive L + cyc.c) / cyc.c)

/-- **`prop:ac-unsafe-core-empty`** (v30 line 11579): a retired-survivor cycle CANNOT lie in
the unsafe off-pin core.  With unit overlap the unsafe inequality reads `1536 > 31·c`,
impossible for `c ≥ 64` (`31·64 = 1984 > 1536`).  Hence `𝔠_unsafe^offpin = ∅`. -/
theorem unsafeCore_empty_of_retirement {L : ℕ} {cyc : CycleParams}
    (hret : BoundedPeriodRetired L cyc) (hmem : UnsafeOffPinCore L cyc) : False := by
  obtain ⟨_, hc64, hunsafe⟩ := hmem
  have hov : (rActive L + cyc.c) / cyc.c = 1 := surviving_unit_overlap hret
  rw [hov, mul_one] at hunsafe
  omega

/-- **The full Lane-C export** (`cor:ac-offpin-cap-closed` precursor): given the priority
routing, NO live M.5/L.3 ledger fibre lies in the unsafe off-pin core. -/
theorem unsafeCore_empty_of_routing {L : ℕ} (R : PriorityRouting L) {cyc : CycleParams}
    (hsurv : R.inLedger cyc) (hmem : UnsafeOffPinCore L cyc) : False :=
  unsafeCore_empty_of_retirement (boundedPeriodRetired_of_routing R cyc hsurv) hmem

/-- **Unit overlap from the routing** (convenience for Lane C): every live ledger fibre has
overlap floor `1`. -/
theorem ledger_unit_overlap {L : ℕ} (R : PriorityRouting L) {cyc : CycleParams}
    (hsurv : R.inLedger cyc) : (rActive L + cyc.c) / cyc.c = 1 :=
  surviving_unit_overlap (boundedPeriodRetired_of_routing R cyc hsurv)

/-! ## 6.  Status block and non-circularity audit record -/

/-- Honest status of Lane D, including the non-circularity verdict. -/
def v30BoundedPeriodRetirementStatus : List String := [
  "LANE D (V30 BoundedPeriodRetirement) — bounded-output retirement / the (C1) linchpin.",
  "BUILD: lake build Erdos260.V30BoundedPeriodRetirement — additive; imports ONLY Erdos260.Constants (+ Mathlib).",
  "CONSTANTS (Convention 2.0d, v30 line 276/279): phandNat = 2182720 = manuscriptPhand " ++
    "(phandNat_real_eq_manuscript); cQNat = manuscriptCQ_T = 1; boundedThreshold L = 2182720*L + 1.",
  "CONSTANTS DISCIPLINE (Convention 2.0e, v30 line 317): kappa < P_hand/2 " ++
    "(kappa_lt_phand_div_two); P_hand is a fixed numeral chosen before kappa; no circular dependence.",
  "RETIREMENT LEMMA (lem:ac-bounded-tower-retirement, v30 line 11533): a live M.5/L.3 off-pin " ++
    "ledger fibre has c > P_hand*L + C_Q (boundedPeriodRetired_of_routing), via p|c => p<=c " ++
    "(primitivePeriod_le_cycleLength) and the post-priority disjointness ledger ⟹ p>threshold (ledger_period_gt).",
  "UNIT OVERLAP (lem:ac-surviving-long-cycle-unit-overlap, v30 line 11555): a survivor has " ++
    "r = floor(kappa*L) <= L < threshold < c, so floor((r+c)/c) = 1 (surviving_unit_overlap).",
  "UNSAFE CORE EMPTY (prop:ac-unsafe-core-empty, v30 line 11579): with overlap = 1 the unsafe " ++
    "inequality 1536*floor((r+c)/c) > 31*c reads 1536 > 31*c, impossible for c >= 64 (31*64 = 1984 > 1536). " ++
    "unsafeCore_empty_of_retirement / unsafeCore_empty_of_routing.",
  "EXACT INEQUALITY: UnsafeOffPinCore L cyc := (b = 1) /\\ (64 <= c) /\\ (31*c < 1536*((r+c)/c)); proved unsatisfiable for survivors.",
  "NON-CIRCULARITY VERDICT: PROVED non-circular w.r.t. (C1) (the off-pin exit-mass cap). " ++
    "(i) import isolation: this module imports NO (C1) module (no ExitMassControl / " ++
    "ExitMassCoreTranscription / MissDistanceClosure / ExitMassControlOffPin). " ++
    "(ii) type isolation: PriorityRouting's fields mention ONLY period/output-class, no exit mass. " ++
    "(iii) constructive witness: periodRouting builds the whole interface from period comparison alone.",
  "RESIDUAL ATOM (D1) priority routing: the genuine M.5/L.3 ledger must satisfy PriorityRouting " ++
    "for the real ledger predicate; supplied in-tree by L.4.1 (v30 line 6744) + M.4.1 (line 7649, bounded clause 7658), " ++
    "which route by period BEFORE the trichotomy/ledger — upstream of and independent of (C1).",
  "RESIDUAL ATOM (D2) budget affordability: deleted 𝔒_bdd mass is paid by the CNL/Kraft entropy " ++
    "budget (v30 line 7659 'one-step Kraft/CNL estimate', line 7684 'covered by the bounded CNL/Kraft " ++
    "terms'); in-tree atoms N33AbsorptionCore.bddBudgetLe_ofShell, the six-class bound " ++
    "termMass <= O_D+O_P+O_E+O_CNL+O_bdd, CNLKraftCountCore/CNLScalarBudgetCore, and periodic_no_sparse_shell " ++
    "(periods <= 2^19). Disjoint priority cell from the M.5/L.3 ledger that (C1) caps — no double count.",
  "HONEST CAVEAT: v30 treats the retirement as a CONVENTION (v30 line 281 'a local bookkeeping device'). " ++
    "This module proves the period/order skeleton + the unsafe-core arithmetic + the constants discipline + (C1)-freeness. " ++
    "(D1)+(D2) are genuine in-tree obligations; if (D2) failed it would fail by BUDGET OVERFLOW, never by needing (C1).",
  "LANE C SHAPE: instantiate PriorityRouting L with the real ledger predicate; discharge bdd_of_bounded_period " ++
    "and ledger_disjoint_bdd from L.4/M.4 (D1); consume unsafeCore_empty_of_routing for 𝔠_unsafe^offpin = ∅; " ++
    "feed the safe cone into ExitMassControlOffPin via emc2_offPin_of_regime.",
  "AXIOMS: every key declaration reports exactly [propext, Classical.choice, Quot.sound]; no sorry/admit/native_decide; no new axiom."
]

theorem v30BoundedPeriodRetirementStatus_nonempty :
    v30BoundedPeriodRetirementStatus ≠ [] := by
  unfold v30BoundedPeriodRetirementStatus
  simp

/-! ## 7.  Axiom audit (`#print axioms` for every key declaration) -/

section AxiomAudit

#print axioms phandNat_real_eq_manuscript
#print axioms kappa_lt_phand_div_two
#print axioms rActive_lt_threshold
#print axioms primitivePeriod_le_cycleLength
#print axioms ledger_period_gt
#print axioms periodRouting
#print axioms boundedPeriodRetired_of_routing
#print axioms not_inLedger_of_cycle_bounded
#print axioms surviving_unit_overlap
#print axioms unsafeCore_empty_of_retirement
#print axioms unsafeCore_empty_of_routing
#print axioms ledger_unit_overlap
#print axioms v30BoundedPeriodRetirementStatus_nonempty

end AxiomAudit

end V30BoundedPeriodRetirement
end Erdos260
