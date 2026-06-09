import Erdos260.RunObstructionRealization
import Erdos260.GlobalRunAssembly

/-!
# Run factory constructor: wiring the proved §25.2 half-decrease into `RunFactoryData`

The capstone `Erdos260MinimalAtoms` (in `UnconditionalAssembly.lean`) consumes the Run package
as a single higher-level datum
`run : … → RunFactoryData cStar ξ X`.  Two sibling files had already PROVED the deep Run content
but left it **un-wired** to that datum:

* `RunDescentConstruction.lean` — the L.4.2 one-step half-decrease `wt(O_{i+1}) ≤ wt(O_i)/2`
  (`run_period_halfDecrease_of_smallDenom`, from Lemma 25.2 + Fine–Wilf), the total L.4.1
  classifier `classify : RunState → Fin 4`, the family assembler
  `RunFamilyCore.ofDescentAndRouting`, and the budget `termRun_bound_of_construction`.
* `RunObstructionRealization.lean` — the §25.2 small-denominator realization `RunObstruction`
  with its derived `hold` periodicity, the canonical `RunObstruction.ofMeanLowScale` (the four
  geometric fields + the mean-low verdict from a *single* scale input `4 q₀ ≤ m·ord_{q₀}(2)`), and
  the realized half-decrease `RunObstruction.halfDecrease_of_meanLow_verdict` /
  `ofMeanLowScale_halfDecrease` on the genuine word `dyadicDigit q₀ a`.

The honest residual identified last round was: **there is no clean constructor
`RunObstruction → RunFactoryData`** — the capstone consumed `RunFactoryData` directly, so the
proved half-decrease + realization were never assembled into the exact datum the capstone needs.
This file (NEW; it edits no existing file) supplies that constructor.

## What is genuinely DONE here (new content)

* `RunFamilyCore.toRunFactoryData` — the generic projection
  `RunFamilyCore cStar ξ X α → RunFactoryData cStar ξ X`: the `trichotomy` ledger inequality is the
  proved `RunTrichotomyAbsorptionData.trichotomy_bound` fed the proved descent sum
  `RunPeriodShrink.descent_sum`, and `hSmall` is the family's K.4 smallness.  This is the missing
  bridge from the L.4.1/L.4.2 family core to the capstone's `RunFactoryData`.
* `obstructionPeriod` / `obstructionPeriod_halves` / `RunObstruction.toDescentChain` — the
  period-descent chain **seeded by the obstruction's old period** whose **first step is certified by
  the §25.2 + Fine–Wilf half-decrease** (`period 0 = oldPeriod`, `period 1 = p'` with the genuine
  `2·p' ≤ oldPeriod`), the tail continued geometrically.  So the chain's halving — the input that
  makes the `trichotomy` ledger hold — is the real L.4.2 descent at step 0, not a formal stipulation.
* `RunObstruction.toRunFactoryData` — **the constructor `RunObstruction → RunFactoryData`.**  Given
  the obstruction with its (proved) half-decrease, the L.4.1 routing data `RunRoutingData`, and the
  per-shell budget inputs, it builds the family core through `ofDescentAndRouting` and projects to
  `RunFactoryData`.  The L.4.2 half-decrease is **embedded, not assumed**.
* `runFactoryDataOfScale` — **the headline: `RunFactoryData` from the smallest §25.2 input.**  From
  the reduced data (`q₀ > 1` odd, `a` coprime) and the single scale `4 q₀ ≤ m·ord_{q₀}(2)`, it
  builds the obstruction (`ofMeanLowScale`), discharges the mean-low verdict and the half-decrease
  automatically (`halfDecrease_of_density`), and produces `RunFactoryData` from the routing + budget.
* `RunObstruction.maskPoint_digit` / `maskPoint_residue_zero` / `realized_maskPoint` /
  `oldPeriod_eq_periodMult_mul_order` — the §25.1/§25.2 **mask-point identification pinned
  definitionally**: the obstruction's word at position `j` is exactly the `j`-th binary digit
  `⌊2·rⱼ/q₀⌋` of the rational mask point `a/q₀` (`rⱼ = (2^j·a) mod q₀`), and the old run period is
  structurally the §25.2 dyadic period (a multiple of `ord_{q₀}(2)`).
* `runFactoryDataWitness` / `runFactoryDataWitness_runBound` — a concrete `RunFactoryData` built
  through the bridge on the `1/3` obstruction, with the Prop. I.5.2 budget `runMass ≤ cStar·ξ·X/6`.

## Honest status of the `run` atom

**REDUCED, not fully closed.**  After this file the `run` provider no longer needs the L.4.2
half-decrease as a black box: it is constructible by `runFactoryDataOfScale` from

1. the §25.2 reduced data + scale `4 q₀ ≤ m·ord_{q₀}(2)` (the *only* input to the now-PROVED
   half-decrease and the four geometric realization fields), plus
2. the genuinely shell-dependent analytic inputs that `RunFactoryData` is *about*: the L.4.1 routing
   `RunRoutingData` (per-branch tower/return/dense-pack absorption), and the per-shell budget data
   `chain_capture` (shortening mass ≤ seed period), `chainRoot_le`, and the K.4 smallness `hSmall`.

The mask-point identification (the run obstruction's point *is* `a/q₀` with `q₀` a small odd
denominator) is the §25.1/§25.2 construction-level fact; it is pinned definitionally here, but the
*provenance* of a concrete `(q₀, a, m)` for a given failing shell remains the geometric input.

No `sorry`, `axiom`, or `admit`.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## Part A — Generic projection `RunFamilyCore → RunFactoryData` -/

/--
**The missing bridge `RunFamilyCore → RunFactoryData`.**

`RunFactoryData` (the capstone's Run datum) is the run-mass ledger with two inequalities:
`runMass ≤ Σ slots + X·Ij·twoNegcY + smallError` (the L.4.1/L.4.2 `trichotomy`) and
`Σ slots + … ≤ cStar·ξ·X/6` (the K.4 `hSmall`).  Both are *already proved* for a `RunFamilyCore`:

* `trichotomy` is `RunTrichotomyAbsorptionData.trichotomy_bound` (the L.4.1 split + the four
  absorptions + the chain-root absorption) fed the L.4.2 descent sum `RunPeriodShrink.descent_sum`
  (`Σ wt(O_i) ≤ 2·wt(O_0)`, itself `halfGeometricSum_bound`);
* `hSmall` is the family core's own K.4 field.

So the projection introduces **no new analytic content** — it just exposes the family core in the
exact shape the capstone consumes.
-/
def RunFamilyCore.toRunFactoryData {cStar xi X : ℝ} {α : Type*}
    (core : RunFamilyCore cStar xi X α) : RunFactoryData cStar xi X where
  runMass := core.tri.runMass
  nextTower := core.nextTower
  nextReturn := core.nextReturn
  nextDensePack := core.nextDensePack
  twoNegcY := core.twoNegcY
  Ij := core.Ij
  smallError := core.smallError
  trichotomy := core.trichotomyData.trichotomy_bound core.shrink.descent_sum
  hSmall := core.hSmall

@[simp] theorem RunFamilyCore.toRunFactoryData_runMass {cStar xi X : ℝ} {α : Type*}
    (core : RunFamilyCore cStar xi X α) :
    core.toRunFactoryData.runMass = core.tri.runMass := rfl

/-! ## Part B — The obstruction-seeded descent chain (step-0 certified by §25.2) -/

/--
**Period sequence seeded by the obstruction.**

`period 0 = oldPeriod` (the run period `wt(O_0)`), and `period (k+1) = p'/2^k` for a witnessed
shorter period `p'`.  When `p'` is the period produced by the §25.2 + Fine–Wilf half-decrease
(`2·p' ≤ oldPeriod`), the step `0 → 1` is the genuine L.4.2 descent and the tail halves
geometrically.
-/
def obstructionPeriod (oldPeriod p' : ℕ) : ℕ → ℕ
  | 0 => oldPeriod
  | (k + 1) => p' / 2 ^ k

/--
**The seeded sequence halves at every step.**

Step `0`: `2·(p'/1) ≤ oldPeriod`, which is *exactly* the §25.2 + Fine–Wilf one-step half-decrease
`2·p' ≤ oldPeriod`.  Step `k+1`: `2·(p'/2^{k+1}) ≤ p'/2^k`, pure natural-number halving.
-/
theorem obstructionPeriod_halves {oldPeriod p' : ℕ} (hstep : 2 * p' ≤ oldPeriod) :
    ∀ n, 2 * obstructionPeriod oldPeriod p' (n + 1) ≤ obstructionPeriod oldPeriod p' n
  | 0 => by simpa [obstructionPeriod] using hstep
  | (k + 1) => by
      simp only [obstructionPeriod]
      have h : p' / 2 ^ (k + 1) = p' / 2 ^ k / 2 := by
        rw [pow_succ, Nat.div_div_eq_div_mul]
      rw [h]; omega

/--
**The L.4.2 period-descent chain of a run obstruction.**

The descent potential `wt(O_0) ⊋ wt(O_1) ⊋ …` whose seed is the obstruction's old period and whose
**first one-step half-decrease is the proved §25.2 + Fine–Wilf descent** (`hHD`), continued
geometrically.  Its `halves` field — the very input that drives the Run ledger inequality — is
therefore the genuine L.4.2 content at step 0.
-/
def RunObstruction.toDescentChain (O : RunObstruction)
    (hHD : ∃ p', PeriodicOn (dyadicDigit O.q0 O.a) O.u O.N p' ∧ 0 < p' ∧ 2 * p' ≤ O.oldPeriod) :
    RunPeriodDescentChain where
  period := obstructionPeriod O.oldPeriod hHD.choose
  halves := obstructionPeriod_halves hHD.choose_spec.2.2

@[simp] theorem RunObstruction.toDescentChain_period_zero (O : RunObstruction)
    (hHD : ∃ p', PeriodicOn (dyadicDigit O.q0 O.a) O.u O.N p' ∧ 0 < p' ∧ 2 * p' ≤ O.oldPeriod) :
    (O.toDescentChain hHD).period 0 = O.oldPeriod := rfl

/--
**The seed period is dominated by the descent potential.**

`wt(O_0) = oldPeriod = period 0 ≤ Σ_{i<len} period i` whenever `len ≥ 1` (the seed is one summand,
all summands nonnegative).  This lets a caller discharge the family core's `chain_capture` from the
clean bound "shortening-class mass ≤ seed period".
-/
theorem RunObstruction.oldPeriod_le_descentSum (O : RunObstruction)
    (hHD : ∃ p', PeriodicOn (dyadicDigit O.q0 O.a) O.u O.N p' ∧ 0 < p' ∧ 2 * p' ≤ O.oldPeriod)
    {len : ℕ} (hlen : 1 ≤ len) :
    (O.oldPeriod : ℝ) ≤ ∑ i ∈ Finset.range len, ((O.toDescentChain hHD).period i : ℝ) := by
  have hmem : (0 : ℕ) ∈ Finset.range len := Finset.mem_range.mpr hlen
  have hle := Finset.single_le_sum
    (f := fun i => ((O.toDescentChain hHD).period i : ℝ))
    (fun i _ => by positivity) hmem
  simpa using hle

/-! ## Part C — The constructor `RunObstruction → RunFactoryData` -/

/--
**The constructor `RunObstruction → RunFactoryData` (the residual the last round isolated).**

Given a §25.2 run obstruction `O` with its proved one-step half-decrease `hHD` on the genuine word
`dyadicDigit q₀ a`, the L.4.1 routing data `D` (per-branch tower/return/dense-pack absorption,
whose three class-mass bounds are proved in `RunDescentConstruction`), and the per-shell budget
inputs (`chain_capture`: the shortening-class mass is dominated by the seed period; `chainRoot_le`:
the doubled seed absorbs into the clean CNL tail; `hSmall`: the K.4 numerical smallness), this
assembles the **full** `RunFactoryData` the capstone consumes.

The L.4.2 half-decrease enters through `O.toDescentChain hHD`, whose halving at step 0 *is* the
§25.2 + Fine–Wilf descent — so the resulting `trichotomy` ledger rests on the proved half-decrease,
not on an assumed `RunPeriodShrink.half_decrease`.
-/
def RunObstruction.toRunFactoryData {cStar xi X : ℝ} {α : Type*}
    (O : RunObstruction)
    (hHD : ∃ p', PeriodicOn (dyadicDigit O.q0 O.a) O.u O.N p' ∧ 0 < p' ∧ 2 * p' ≤ O.oldPeriod)
    (D : RunRoutingData α) (len : ℕ) (hlen : 1 ≤ len)
    (smallError : ℝ) (hsmall_nonneg : 0 ≤ smallError) (twoNegcY Ij : ℝ)
    (chain_capture : D.toTri.chainMass ≤ (O.oldPeriod : ℝ))
    (chainRoot_le : 2 * (O.oldPeriod : ℝ) ≤ X * Ij * twoNegcY)
    (hSmall : D.towerBound + D.returnBound + D.densePackBound + X * Ij * twoNegcY + smallError
      ≤ cStar * xi * X / 6) :
    RunFactoryData cStar xi X :=
  (RunFamilyCore.ofDescentAndRouting D (O.toDescentChain hHD) len smallError hsmall_nonneg
    twoNegcY Ij
    (le_trans chain_capture (O.oldPeriod_le_descentSum hHD hlen))
    chainRoot_le hSmall).toRunFactoryData

/--
**The constructed Run datum meets the Prop. I.5.2 budget `runMass ≤ cStar·ξ·X/6`.**

Immediate from `runBound_of_factory` (the proved Phase-9 `runBound`).  This is the `termRun` slot,
now resting — through `RunObstruction.toRunFactoryData` — on the proved L.4.2 half-decrease.
-/
theorem RunObstruction.toRunFactoryData_runBound {cStar xi X : ℝ} {α : Type*}
    (O : RunObstruction)
    (hHD : ∃ p', PeriodicOn (dyadicDigit O.q0 O.a) O.u O.N p' ∧ 0 < p' ∧ 2 * p' ≤ O.oldPeriod)
    (D : RunRoutingData α) (len : ℕ) (hlen : 1 ≤ len)
    (smallError : ℝ) (hsmall_nonneg : 0 ≤ smallError) (twoNegcY Ij : ℝ)
    (chain_capture : D.toTri.chainMass ≤ (O.oldPeriod : ℝ))
    (chainRoot_le : 2 * (O.oldPeriod : ℝ) ≤ X * Ij * twoNegcY)
    (hSmall : D.towerBound + D.returnBound + D.densePackBound + X * Ij * twoNegcY + smallError
      ≤ cStar * xi * X / 6) :
    (O.toRunFactoryData hHD D len hlen smallError hsmall_nonneg twoNegcY Ij
      chain_capture chainRoot_le hSmall).runMass ≤ cStar * xi * X / 6 :=
  runBound_of_factory _

/--
**Constructor variant routed through the L.4.1 mean-low verdict.**

Identical to `RunObstruction.toRunFactoryData`, but the one-step half-decrease is supplied by the
L.4.1 classifier's mean-low verdict `classify O.toMeanLowRunWindow.toRunState = 0` through the proved
`RunObstruction.halfDecrease_of_meanLow_verdict` (whose §25.2 mean-low premise is DERIVED from the
verdict).  This is the manuscript routing: the L.4.1 trichotomy lands a run branch in the mean-low
class, and that verdict alone certifies the L.4.2 period half-decrease that drives the ledger.
-/
def RunObstruction.toRunFactoryDataOfVerdict {cStar xi X : ℝ} {α : Type*}
    (O : RunObstruction) (hverdict : classify O.toMeanLowRunWindow.toRunState = 0)
    (D : RunRoutingData α) (len : ℕ) (hlen : 1 ≤ len)
    (smallError : ℝ) (hsmall_nonneg : 0 ≤ smallError) (twoNegcY Ij : ℝ)
    (chain_capture : D.toTri.chainMass ≤ (O.oldPeriod : ℝ))
    (chainRoot_le : 2 * (O.oldPeriod : ℝ) ≤ X * Ij * twoNegcY)
    (hSmall : D.towerBound + D.returnBound + D.densePackBound + X * Ij * twoNegcY + smallError
      ≤ cStar * xi * X / 6) :
    RunFactoryData cStar xi X :=
  O.toRunFactoryData (O.halfDecrease_of_meanLow_verdict hverdict) D len hlen smallError
    hsmall_nonneg twoNegcY Ij chain_capture chainRoot_le hSmall

/--
**Headline: `RunFactoryData` from the smallest §25.2 input.**

From the §25.2 reduced data (`q₀ > 1` odd, `a` coprime) and the *single* scale condition
`4 q₀ ≤ m·ord_{q₀}(2)`, the canonical realization `RunObstruction.ofMeanLowScale` discharges the
four geometric fields (`hsize/hold/hbp_le_old/hoverlap`) and the mean-low verdict automatically, so
the one-step half-decrease (`halfDecrease_of_density`) fires on the genuine word `dyadicDigit q₀ a`.
The remaining inputs are exactly the shell-dependent analytic data that `RunFactoryData` is about:
the L.4.1 routing `D` and the per-shell budget `chain_capture / chainRoot_le / hSmall`.
-/
def runFactoryDataOfScale {cStar xi X : ℝ} {α : Type*}
    {q0 a m : ℕ} (hq0 : 1 < q0) (hodd : Odd q0) (hcop : Nat.Coprime a q0) (hm : 0 < m)
    (hscale : 4 * q0 ≤ m * orderOf (2 : ZMod q0)) (u : ℕ) (weight : ℝ)
    (D : RunRoutingData α) (len : ℕ) (hlen : 1 ≤ len)
    (smallError : ℝ) (hsmall_nonneg : 0 ≤ smallError) (twoNegcY Ij : ℝ)
    (chain_capture : D.toTri.chainMass ≤ ((m * orderOf (2 : ZMod q0) : ℕ) : ℝ))
    (chainRoot_le : 2 * ((m * orderOf (2 : ZMod q0) : ℕ) : ℝ) ≤ X * Ij * twoNegcY)
    (hSmall : D.towerBound + D.returnBound + D.densePackBound + X * Ij * twoNegcY + smallError
      ≤ cStar * xi * X / 6) :
    RunFactoryData cStar xi X :=
  let O := RunObstruction.ofMeanLowScale hq0 hodd hcop hm hscale u weight
  O.toRunFactoryData
    (O.halfDecrease_of_density (by
      have h1 := O.density_le
      have h2 : O.c0p = O.N + 1 := rfl
      omega))
    D len hlen smallError hsmall_nonneg twoNegcY Ij
    chain_capture chainRoot_le hSmall

/-! ## Part D — §25.1/§25.2 mask-point identification (definitional) -/

/--
**Mask-point identification (definitional).**

The run obstruction's underlying word at position `j` is exactly the `j`-th binary digit
`⌊2·rⱼ/q₀⌋` of the rational mask point `a/q₀`, where `rⱼ = (2^j·a) mod q₀` is the §25.2 dyadic
residue.  This is the construction-level §25.1/§25.2 statement "the run obstruction's mask point
*is* `a/q₀`", here a `rfl` because `dyadicDigit` is *defined* as this binary-division digit.
-/
theorem RunObstruction.maskPoint_digit (O : RunObstruction) (j : ℕ) :
    dyadicDigit O.q0 O.a j = (2 * ((2 ^ j * O.a) % O.q0)) / O.q0 := rfl

/-- The mask-point residue at position `0` is the reduced numerator `a mod q₀` — the start of the
binary expansion of `a/q₀`. -/
theorem RunObstruction.maskPoint_residue_zero (O : RunObstruction) :
    dyadicResidue O.q0 O.a 0 = O.a % O.q0 := by
  simp [dyadicResidue]

/-- The realized §25.2 window operates on exactly the mask-point datum: the same odd small
denominator `q₀` and numerator `a` (so its word is `dyadicDigit q₀ a`). -/
theorem RunObstruction.realized_maskPoint (O : RunObstruction) :
    O.toMeanLowRunWindow.q0 = O.q0 ∧ O.toMeanLowRunWindow.a = O.a := ⟨rfl, rfl⟩

/-- The old run period is structurally the §25.2 dyadic period — a positive multiple of the
fundamental period `ord_{q₀}(2)` (the manuscript's "the run period of a small-denominator segment
is its dyadic period"). -/
theorem RunObstruction.oldPeriod_eq_periodMult_mul_order (O : RunObstruction) :
    O.oldPeriod = O.periodMult * orderOf (2 : ZMod O.q0) := rfl

/-! ## Part E — Concrete non-vacuity witness -/

/--
A concrete `RunFactoryData` built through the constructor on the `1/3` run obstruction (odd
denominator `3`, scale `4·3 ≤ 6·ord₃(2)`), with a degenerate L.4.1 routing and the budget scaled to
the seed period `wt(O_0) = 6·ord₃(2)`.  Witnesses that the bridge yields a genuine, non-vacuous
`RunFactoryData` (the L.4.2 half-decrease genuinely fires on the real word `dyadicDigit 3 1`).
-/
def runFactoryDataWitness :
    RunFactoryData (12 * (runObstructionWitness.oldPeriod : ℝ) + 6) 1 1 :=
  runObstructionWitness.toRunFactoryData
    (runObstructionWitness.halfDecrease_of_density (by
      have h1 := runObstructionWitness.density_le
      have h2 : runObstructionWitness.c0p = runObstructionWitness.N + 1 := rfl
      omega))
    runRoutingDataTrivial 1 (le_refl 1) 0 (le_refl 0)
    (2 * (runObstructionWitness.oldPeriod : ℝ)) 1
    (by
      have h : runRoutingDataTrivial.toTri.chainMass = 0 := by
        simp [RunRoutingData.toTri, RunBranchTrichotomy.chainMass,
          RunBranchTrichotomy.classMass, runRoutingDataTrivial]
      rw [h]; positivity)
    (le_of_eq (by ring))
    (by
      have h0 : runRoutingDataTrivial.towerBound = 0 := by
        simp [RunRoutingData.towerBound, runRoutingDataTrivial]
      have h1 : runRoutingDataTrivial.returnBound = 0 := by
        simp [RunRoutingData.returnBound, runRoutingDataTrivial]
      have h2 : runRoutingDataTrivial.densePackBound = 0 := by
        simp [RunRoutingData.densePackBound, runRoutingDataTrivial]
      rw [h0, h1, h2]
      nlinarith [Nat.cast_nonneg (α := ℝ) runObstructionWitness.oldPeriod])

theorem runFactoryData_nonempty :
    Nonempty (RunFactoryData (12 * (runObstructionWitness.oldPeriod : ℝ) + 6) 1 1) :=
  ⟨runFactoryDataWitness⟩

/-- **The witness meets the Prop. I.5.2 budget `runMass ≤ cStar·ξ·X/6`.** -/
theorem runFactoryDataWitness_runBound :
    runFactoryDataWitness.runMass ≤ (12 * (runObstructionWitness.oldPeriod : ℝ) + 6) * 1 * 1 / 6 :=
  runBound_of_factory _

/-! ## Part F — Residual inventory (honest) -/

/-- The honest status of the `run` atom after this file wires the constructor. -/
def runFactoryConstructorResiduals : List String :=
  [ "WIRED — RunObstruction.toRunFactoryData / runFactoryDataOfScale: the missing constructor " ++
      "RunObstruction → RunFactoryData now exists, embedding the proved §25.2 + Fine–Wilf one-step " ++
      "half-decrease at step 0 of toDescentChain (not assumed).",
    "DEFINITIONAL — RunObstruction.maskPoint_digit: the obstruction's word IS the binary expansion " ++
      "of the rational mask point a/q₀ (rfl); oldPeriod is structurally periodMult·ord_{q₀}(2).",
    "REDUCED (run atom) — runFactoryDataOfScale builds RunFactoryData from: (1) the §25.2 reduced " ++
      "data q₀>1 odd, a coprime + the single scale 4 q₀ ≤ m·ord_{q₀}(2) (sole input to the now-PROVED " ++
      "half-decrease and the four geometric fields), and (2) the genuinely shell-dependent analytic " ++
      "inputs RunFactoryData is about: the L.4.1 routing RunRoutingData and the per-shell budget " ++
      "chain_capture / chainRoot_le / hSmall.",
    "RESIDUAL (geometric) — the provenance of a concrete (q₀, a, m) per failing shell: the §25.1 " ++
      "residual-cylinder reduction identifying the run obstruction's small odd denominator." ]

theorem runFactoryConstructorResiduals_nonempty :
    runFactoryConstructorResiduals ≠ [] := by
  simp [runFactoryConstructorResiduals]

end

end Erdos260
