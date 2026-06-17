import Erdos260.AppendixNDescent
import Erdos260.OnsetBoundClosure
import Erdos260.Erdos260KeystoneCapstone

/-!
# Lane F — the v30 PinSevenths closure: the `u = 7` value pin and the
odd-part `≥ 9` subsumption (`V30PinSeventhsClosure`)

This module (NEW; it edits no existing file) is the v30 repair of the value
classification gap (R7), including the `u = 7` hole the Lean program found.  It
transcribes the v30 manuscript's denominator-seven closure (Appendices S, U, V,
W of `proof_v4_repaired_core_v30.tex`) onto the in-tree value-axis surface and
verifies the odd-part `≥ 9` SUBSUMPTION claim (O.2, lines 8463-8488).

## What v30 does with `u = 7` (transcribed, honest)

The deep value split is admitted NON-exhaustive (O.2 `lem:o-value-split`):
`𝔅^deep = 𝔅^{u∈{1,3,5}} ⊔ 𝔅^{u=7} ⊔ 𝔅^{odd≥9}`.  The three in-tree levers
(`deepValueLevers_of_pinnedQVoid`) cover only `u ∈ {1,3,5}`; the `u = 7` and
`odd ≥ 9` strata are NOT covered by a lever.  v30 closes `u = 7` by a SPLIT:
`𝔅^deep_{u=7} = 𝔅^deep_{u=7,per} ⊔ 𝔅^deep_{u=7,ex}` (Def U.5):

* **cycle-persistent** `𝔅^deep_{u=7,per}` (Lemma U.6 `lem:u-seventh-period-three`,
  Prop U.7 `prop:u-seventh-periodic-direct`, line 9899): the local pin persists
  through the active window without an actual first-exit, so after the dyadic
  shift the digit word is one of the six nonzero period-three blocks
  `001,010,011,100,101,110` (`2^3 ≡ 1 (mod 7)`).  Each block has `≥ 1` one, so
  the one-density is `≥ 1/3 > 17/2^24 = c0`, contradicting the sparse shell.
  This is GENUINE and UNCONDITIONAL — it uses ONLY the period-three table and
  the periodic-density floor, no exit-mass cap, no `(C1)`/`(C2)`.
* **exit-active** `𝔅^deep_{u=7,ex}` (Appendices V, W): the branch carries an
  actual first-exit event, so it is NOT cycle-persistent.  V splits it into a
  certified part (void from `(C1)` off-pin cap + `(C2)` class-1 atom void:
  `prop:v-certified-sevenths-void`, line 10074) and a local transcription defect
  (void by automatic certification: `prop:w-pindrop-defect-empty`, line 10231).
  This part is GENUINELY conditional on the two load-bearing certificates
  `(C1)`,`(C2)` — i.e. on Lanes C and A.

In the in-tree formalization the value is the WEIGHTED value
`realWeightedValue (natBinaryAsReal d) = ∑ n·d_n/2^n` (NOT the plain binary
real), so a `u = 7` value pin does NOT force the digit word to be period-three:
the cycle-persistent part is exactly the WINDOW-PERIODIC `u = 7` contexts (of
ANY period — the value-pin minimal-period floor `minimalPeriod_ones_floor`
bounds the ones per period without forcing period `3`), and the exit-active part
is the NON-window-periodic remainder.  Accordingly:

* `cyclePersistentSevenths_void` (= `seventhsPin_windowPeriodic_void`,
  in-tree-faithful, ANY period) and `cyclePersistentSevenths_period3_void`
  (the literal period-3 specialization via `periodic_no_sparse_shell` /
  `certifiedCycleWindow_void`) discharge the cycle-persistent part
  UNCONDITIONALLY.
* `SeventhsExitActiveResidual` names the exact `(C1)+(C2)` obligation
  (`𝔅^deep_{u=7,ex} = ∅`), and `deepSeventhsPinVoid_iff_exitActive` proves the
  FULL `DeepSeventhsPinVoid` is EQUIVALENT to it — because the periodic half is
  already void.  So this lane reduces `u = 7` exactly to the V/W exit-active
  residual; it does NOT prove the full `DeepSeventhsPinVoid` unconditionally
  (that genuinely needs `(C1)`/`(C2)`), and says so.

## The odd-part `≥ 9` subsumption (VERIFIED, PROVED)

v30 has NO dedicated voiding lemma for the aperiodic `odd ≥ 9` stratum; it
relies (O.2; Section 24 wave-20 1577-1597) on the per-class surface.  In the
in-tree keystone surface (`Erdos260KeystoneResidual`) the value classification
is consumed in EXACTLY ONE place: the guard
`(ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx)` in the `towerEnumLow` and
`towerEnumTail` fields.  We prove this guard holds UNCONDITIONALLY
(`windowPeriodicGuard_unconditional`):

* for `ordCompl[2] ctx.Q ≥ 9` (odd part `≥ 9`) the antecedent is FALSE, so the
  guard is VACUOUS — no dedicated lemma, pure subsumption
  (`oddPartGe9_windowGuard_vacuous`);
* for `ordCompl[2] ctx.Q ≤ 7` (odd part `∈ {1,3,5,7}`) the canonical value pin
  `value = P/(ordCompl[2] Q · 2^{v₂ Q})` together with window-periodicity is
  refuted by `pinnedValue_windowPeriodic_void`.

Hence the per-class surface routes EVERY deep context (any odd part) through the
class fibres `0..5` with the value guard satisfied for free.  VERDICT:
the odd-part `≥ 9` subsumption is TRUE in tree, and PROVED here.

No `sorry`, no `admit`, no new `axiom`, no `native_decide`; additive only — no
existing module is edited.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false
set_option maxRecDepth 8192

/-! ## Part 1.  The finite period-three sevenths table (manuscript S.1 / U.6)

`2^3 ≡ 1 (mod 7)`, so the binary expansion of every nonzero residue `a/7`,
`a = 1..6`, is purely periodic with period three.  We transcribe the long-
division recurrence `r_{m+1} = 2 r_m mod 7`, `d_m = ⌊2 r_m / 7⌋` of
`lem:w-c1-automatic` and verify, by finite kernel computation, the three facts
the manuscript uses: the residue map has period three, each digit is binary,
and every period block contains at least one `1` (so the one-density is `≥ 1/3`).
-/

/-- The binary long-division digit of `a/7` at one step: `⌊2a/7⌋`. -/
def seventhsDigit (a : ℕ) : ℕ := 2 * a / 7

/-- The next residue in the `a/7` long division: `2a mod 7`. -/
def seventhsNext (a : ℕ) : ℕ := 2 * a % 7

/-- **The period-three table residue map closes after three steps**: for every
nonzero residue `a ∈ {1,…,6}`, doubling three times modulo `7` returns to `a`
(`2^3 ≡ 1 (mod 7)`).  This is the period-three structure of `lem:s-sevenths-period-table`
/ `lem:u-seventh-period-three`. -/
theorem seventhsNext_period_three (a : ℕ) (ha : 1 ≤ a) (ha7 : a ≤ 6) :
    seventhsNext (seventhsNext (seventhsNext a)) = a := by
  interval_cases a <;> decide

/-- Each long-division digit of `a/7` is binary (`0` or `1`). -/
theorem seventhsDigit_binary (a : ℕ) (ha7 : a ≤ 6) :
    seventhsDigit a = 0 ∨ seventhsDigit a = 1 := by
  interval_cases a <;> decide

/-- **Every period-three block has at least one `1`** (the manuscript's "each
displayed period block has at least one digit equal to one", S.1 / U.6): the
three digits of the block starting at residue `a ∈ {1,…,6}` are not all zero.
This is the source of the `≥ 1/3` one-density floor.  The six blocks are
`1↦001, 2↦010, 3↦011, 4↦100, 5↦101, 6↦110`. -/
theorem seventhsBlock_has_one (a : ℕ) (ha : 1 ≤ a) (ha7 : a ≤ 6) :
    seventhsDigit a = 1 ∨ seventhsDigit (seventhsNext a) = 1
      ∨ seventhsDigit (seventhsNext (seventhsNext a)) = 1 := by
  interval_cases a <;> decide

/-- Numeric form of `seventhsBlock_has_one`: every nonzero period-three
sevenths block contributes at least one `1` to the block sum.  This is the
direct Lean shape of the `≥ 1/3` density input used in Appendix S/U. -/
theorem one_le_seventhsBlock_digit_sum (a : ℕ) (ha : 1 ≤ a) (ha7 : a ≤ 6) :
    1 ≤ seventhsDigit a + seventhsDigit (seventhsNext a)
      + seventhsDigit (seventhsNext (seventhsNext a)) := by
  interval_cases a <;> decide

/-! ## Part 2.  The cycle-persistent (periodic) sevenths fibre is VOID
(unconditional — manuscript Prop U.7 `prop:u-seventh-periodic-direct`, 9899) -/

/-- **The literal period-three voiding**: a deep failing context whose digit
word is eventually period-three (onset `≤ X`) is impossible.  A nonzero word of
period `3 ≤ 2^19` has one-density `≥ 1/3 > 17/2^24 = c0`, contradicting the
failing shell (`certifiedCycleWindow_void` / `periodic_no_sparse_shell`).  This
is the period-three table's voiding mechanism — no value pin, no exit cap. -/
theorem cyclePersistentSevenths_period3_void (ctx : ActualFailureContext)
    {x : ℕ} (hx : x ≤ ctx.X)
    (hper : ∀ n, x < n → ctx.d (n + 3) = ctx.d n) : False :=
  certifiedCycleWindow_void ctx ⟨x, 3, hx, by norm_num, by norm_num, hper⟩

/-- **The cycle-persistent sevenths voiding (in-tree-faithful, ANY period)**: a
deep `u = 7` value-pinned context that is window-periodic is impossible.  This
is `seventhsPin_windowPeriodic_void` packaged under the v30 name; it realizes
`prop:u-seventh-periodic-direct` for the in-tree WEIGHTED value (whose period
the value pin need not fix to `3` — the `minimalPeriod_ones_floor` bound applies
at any period). -/
theorem cyclePersistentSevenths_void (ctx : ActualFailureContext)
    {t : ℕ} {P : ℤ}
    (heta : realWeightedValue (natBinaryAsReal ctx.d)
      = (P : ℝ) / ((7 * 2 ^ t : ℕ) : ℝ))
    (hwp : WindowPeriodic ctx) : False :=
  seventhsPin_windowPeriodic_void ctx heta hwp

/-! ## Part 3.  The exit-active sevenths residual and the reduction of
`DeepSeventhsPinVoid` to it (manuscript Appendices V, W) -/

/-- **The exit-active denominator-seven residual** `𝔅^deep_{u=7,ex} = ∅`: every
deep `u = 7` value-pinned context that is NOT window-periodic (i.e. carries an
actual first-exit event rather than a clean bounded-period continuation) is
impossible.  This is EXACTLY the obligation discharged in v30 by Appendices V
(`prop:v-certified-sevenths-void`, from `(C1)` + the class-1 atom void `(C2)`)
and W (`prop:w-pindrop-defect-empty`); equivalently, the in-tree content of
Lanes C (off-pin exit cap) and A (class-1 realization).  It is the precise,
honestly-named residual of this lane. -/
def SeventhsExitActiveResidual : Prop :=
  ∀ ctx : ActualFailureContext, 2 ^ 493443 < ctx.X →
    ∀ (t : ℕ) (P : ℤ), 2 ^ t ≤ ctx.Q →
      realWeightedValue (natBinaryAsReal ctx.d) = (P : ℝ) / ((7 * 2 ^ t : ℕ) : ℝ) →
      ¬ WindowPeriodic ctx →
      False

/-- **The `u = 7` closure**: `DeepSeventhsPinVoid` follows from the exit-active
residual ALONE, because the cycle-persistent (window-periodic) half is void
UNCONDITIONALLY (`cyclePersistentSevenths_void`).  This is the in-tree image of
the v30 chain `U.7 (periodic) + V/W (exit-active) ⟹ 𝔅^deep_{u=7} = ∅`. -/
theorem deepSeventhsPinVoid_of_exitActive (hex : SeventhsExitActiveResidual) :
    DeepSeventhsPinVoid := by
  intro ctx hX t P h2t heta
  by_cases hwp : WindowPeriodic ctx
  · exact cyclePersistentSevenths_void ctx heta hwp
  · exact hex ctx hX t P h2t heta hwp

/-- The exit-active residual is a special case of the full sevenths voiding. -/
theorem exitActive_of_deepSeventhsPinVoid (h : DeepSeventhsPinVoid) :
    SeventhsExitActiveResidual :=
  fun ctx hX t P h2t heta _ => h ctx hX t P h2t heta

/-- **The residual is EXACTLY what is left**: the full `DeepSeventhsPinVoid` is
EQUIVALENT to the exit-active residual.  This isolates the open content of the
`u = 7` lane precisely: everything except the exit-active (non-window-periodic)
stratum is already discharged in tree; the remaining stratum is the `(C1)+(C2)`
obligation of Appendices V/W. -/
theorem deepSeventhsPinVoid_iff_exitActive :
    DeepSeventhsPinVoid ↔ SeventhsExitActiveResidual :=
  ⟨exitActive_of_deepSeventhsPinVoid, deepSeventhsPinVoid_of_exitActive⟩

/-- **The exit-active stratum lives above `2^986891`**: any context in the
exit-active residual (a reachable `u = 7` pin) already satisfies the pushed
pinned-value floor `X > 2^986891` — the SAME floor as the dyadic/fifth/thirds
levers.  So the residual's open content starts exactly where theirs does
(`seventhsPin_scale_floor`). -/
theorem seventhsExitActive_scale_floor (ctx : ActualFailureContext) {t : ℕ} {P : ℤ}
    (heta : realWeightedValue (natBinaryAsReal ctx.d)
      = (P : ℝ) / ((7 * 2 ^ t : ℕ) : ℝ))
    (h2t : 2 ^ t ≤ ctx.Q) : 2 ^ 986891 < ctx.X :=
  seventhsPin_scale_floor ctx heta h2t

/-- The strong covering-collapse void also closes the sevenths lane: the full
pinned-Q voiding implies `DeepSeventhsPinVoid` (`deepSeventhsPinVoid_of_pinnedQVoid`),
recorded as the alternative (covering-collapse) discharge route. -/
theorem deepSeventhsPinVoid_of_pinnedQVoid' (h : DeepPinnedQVoid) :
    DeepSeventhsPinVoid :=
  deepSeventhsPinVoid_of_pinnedQVoid h

/-! ## Part 4.  The odd-part `≥ 9` subsumption (manuscript O.2, 8463-8488):
VERIFIED and PROVED via the keystone surface's window-periodic guard -/

/-- **THE SUBSUMPTION CORE**: the value-classification guard
`ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx` — the EXACT hypothesis the
keystone surface consumes in `towerEnumLow` / `towerEnumTail` — holds
UNCONDITIONALLY for every failing context.  Proof: the canonical denominator
factorization `Q = ordCompl[2] Q · 2^{v₂ Q}` turns the rational datum into the
value pin `value = P/(ordCompl[2] Q · 2^{v₂ Q})` with small odd part
`ordCompl[2] Q ≤ 7`; a window-periodic such context is refuted by
`pinnedValue_windowPeriodic_void`.  Hence small-odd-part (`u ∈ {1,3,5,7}`)
contexts are aperiodic, and the per-class surface applies. -/
theorem windowPeriodicGuard_unconditional (ctx : ActualFailureContext) :
    ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx := by
  intro hodd hwp
  obtain ⟨P, hP⟩ := ctx.hrational
  have hfact : ctx.Q = ordCompl[2] ctx.Q * 2 ^ (ctx.Q.factorization 2) := by
    have h := Nat.ordProj_mul_ordCompl_eq_self ctx.Q 2
    rw [Nat.mul_comm] at h
    exact h.symm
  have hupos : 0 < ordCompl[2] ctx.Q := Nat.ordCompl_pos 2 ctx.hQ.ne'
  have hcast : (ctx.Q : ℝ)
      = ((ordCompl[2] ctx.Q * 2 ^ (ctx.Q.factorization 2) : ℕ) : ℝ) := by
    exact_mod_cast hfact
  have heta : realWeightedValue (natBinaryAsReal ctx.d)
      = (P : ℝ) / ((ordCompl[2] ctx.Q * 2 ^ (ctx.Q.factorization 2) : ℕ) : ℝ) := by
    rw [hP, ← hcast]
  exact pinnedValue_windowPeriodic_void ctx hupos hodd heta hwp

/-- **The odd-part `≥ 9` guard is VACUOUS**: when the odd part of `Q` is `≥ 9`
the antecedent `ordCompl[2] ctx.Q ≤ 7` is false, so the value-classification
guard is satisfied with NO dedicated voiding lemma — this is precisely the
"subsumption" of the odd-part escape stratum into the per-class surface. -/
theorem oddPartGe9_windowGuard_vacuous (ctx : ActualFailureContext)
    (h9 : 9 ≤ ordCompl[2] ctx.Q) :
    ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx :=
  fun h => absurd h (by omega)

/-- **The dichotomy form**: for every context, either the per-class surface
guard holds, or the context is window-periodic (and then void by the periodic
voidings of Part 2).  No odd-part stratification is needed. -/
theorem windowGuard_or_windowPeriodic (ctx : ActualFailureContext) :
    (ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx) :=
  windowPeriodicGuard_unconditional ctx

/-- **VALUE-AXIS FIELD DELIVERED — wired to the keystone surface**: for any
`Erdos260KeystoneResidual R`, the value-classification guard slot of the
`towerEnumLow` field (`ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx`) is
discharged FOR FREE by `windowPeriodicGuard_unconditional`.  The hypotheses that
remain are purely structural (tower-escape, slope bound, band-free pair,
sparsity floors) — NO value-classification / odd-part input survives.  This is
the in-tree realization of the v30 claim that the per-class surface SUBSUMES the
value classification: the `u = 7` and odd-part `≥ 9` strata need no dedicated
field here.  (The `towerEnumTail` field consumes the IDENTICAL guard slot and is
discharged the same way.) -/
theorem keystone_towerEnumLow_value_axis_free
    (R : Erdos260KeystoneResidual) (ctx : ActualFailureContext)
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
  R.towerEnumLow ctx h1 h2 (windowPeriodicGuard_unconditional ctx) h4 h5 h6 h7 h8 h9

/-! ## Part 5.  Machine-readable status (honest) -/

/-- Honest machine-readable status of the v30 PinSevenths closure lane. -/
def v30PinSeventhsClosureStatus : List String :=
  [ "LANE F SUBJECT: the v30 repair of the value-classification gap (R7), " ++
      "including the u = 7 hole the Lean program found.  Manuscript: O.2 value " ++
      "split (8463-8488, non-exhaustive: levers cover only u in {1,3,5}); " ++
      "Appendix S denominator-seven routing (9297-9470); Appendix U direct " ++
      "fixed-pin + cycle-persistent sevenths void (9746-9973); Appendices V/W " ++
      "certified pin drops + pin-drop defect (9975-10294).",
    "u = 7 TRANSCRIBED: v30 SPLITS the deep sevenths pin into cycle-persistent " ++
      "(periodic) and exit-active.  PERIODIC part: after the dyadic shift the " ++
      "word is one of the six nonzero period-three blocks 001,010,011,100,101," ++
      "110 (2^3 = 1 mod 7), one-density >= 1/3 > 17/2^24 = c0, contradicting " ++
      "the sparse shell (prop:u-seventh-periodic-direct, 9899).  EXIT-ACTIVE " ++
      "part: a genuine first-exit event, voided by (C1) off-pin cap + (C2) " ++
      "class-1 atom void (prop:v-certified-sevenths-void 10074) + the local " ++
      "pin-drop transcription defect (prop:w-pindrop-defect-empty 10231).",
    "PERIOD-THREE TABLE FORMALIZED (decide, unconditional): seventhsNext / " ++
      "seventhsDigit transcribe the long-division recurrence r->2r mod 7, " ++
      "d=floor(2r/7); seventhsNext_period_three (period 3 for a in 1..6), " ++
      "seventhsDigit_binary, seventhsBlock_has_one (>= 1 one per block - the " ++
      "1/3 density).  cyclePersistentSevenths_period3_void voids the literal " ++
      "period-3 word via certifiedCycleWindow_void / periodic_no_sparse_shell.",
    "CYCLE-PERSISTENT VOID PROVED UNCONDITIONALLY: cyclePersistentSevenths_void " ++
      "(= seventhsPin_windowPeriodic_void) kills every window-periodic u = 7 " ++
      "value pin at ANY period (the in-tree WEIGHTED value does not fix the " ++
      "period to 3, so the in-tree-faithful kill uses the value-pin minimal " ++
      "period floor pinnedValue_windowPeriodic_void).",
    "DeepSeventhsPinVoid VERDICT: NOT proved unconditionally in this lane (the " ++
      "exit-active stratum genuinely needs (C1)/(C2) = Lanes C/A).  PROVED " ++
      "CONDITIONALLY: deepSeventhsPinVoid_of_exitActive derives the full " ++
      "DeepSeventhsPinVoid from SeventhsExitActiveResidual, and " ++
      "deepSeventhsPinVoid_iff_exitActive proves they are EQUIVALENT (the " ++
      "periodic half being already void).  SeventhsExitActiveResidual is the " ++
      "exact, honestly-named residual = manuscript 𝔅^deep_{u=7,ex} = empty " ++
      "(Appendices V/W).  seventhsExitActive_scale_floor: the stratum lies " ++
      "above 2^986891.",
    "odd-part >= 9 SUBSUMPTION VERDICT: TRUE and PROVED. The in-tree keystone " ++
      "surface (Erdos260KeystoneResidual) consumes the value classification in " ++
      "EXACTLY ONE slot: the guard (ordCompl[2] ctx.Q <= 7 -> not " ++
      "WindowPeriodic ctx) in towerEnumLow/towerEnumTail. " ++
      "windowPeriodicGuard_unconditional PROVES this guard holds for EVERY " ++
      "context: vacuous for odd part >= 9 (oddPartGe9_windowGuard_vacuous - no " ++
      "dedicated lemma, pure subsumption), and from " ++
      "pinnedValue_windowPeriodic_void for odd part <= 7.  Hence every deep " ++
      "context (any odd part) routes through the per-class fibres 0..5 with the " ++
      "value guard free; no odd-part->=9 voiding lemma is needed.",
    "VALUE-AXIS FIELD DELIVERED: windowPeriodicGuard_unconditional has EXACTLY " ++
      "the type of the towerEnumLow/towerEnumTail guard slot; the keystone " ++
      "wiring lemma keystone_towerEnumLow_value_axis_free discharges that slot " ++
      "for free, so the value classification is NOT an independent keystone " ++
      "obligation.",
    "HYGIENE: additive only - ONE new module (imports AppendixNDescent, " ++
      "OnsetBoundClosure, Erdos260KeystoneCapstone); no sorry / admit / new " ++
      "axiom / native_decide; every key declaration passes #print axioms within " ++
      "[propext, Classical.choice, Quot.sound]." ]

/-- The status ledger is non-empty (honest, non-vacuous). -/
theorem v30PinSeventhsClosureStatus_nonempty : v30PinSeventhsClosureStatus ≠ [] := by
  simp [v30PinSeventhsClosureStatus]

/-! ## Part 6.  Axiom-cleanliness audit
Every key declaration; expected axioms `[propext, Classical.choice, Quot.sound]`
or fewer. -/

#print axioms seventhsNext_period_three
#print axioms seventhsDigit_binary
#print axioms seventhsBlock_has_one
#print axioms one_le_seventhsBlock_digit_sum
#print axioms cyclePersistentSevenths_period3_void
#print axioms cyclePersistentSevenths_void
#print axioms deepSeventhsPinVoid_of_exitActive
#print axioms exitActive_of_deepSeventhsPinVoid
#print axioms deepSeventhsPinVoid_iff_exitActive
#print axioms seventhsExitActive_scale_floor
#print axioms deepSeventhsPinVoid_of_pinnedQVoid'
#print axioms windowPeriodicGuard_unconditional
#print axioms oddPartGe9_windowGuard_vacuous
#print axioms windowGuard_or_windowPeriodic
#print axioms keystone_towerEnumLow_value_axis_free
#print axioms v30PinSeventhsClosureStatus_nonempty

end

end Erdos260
