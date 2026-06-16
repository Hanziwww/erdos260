import Erdos260.OnsetBoundClosure
import Erdos260.ThirdsExclusionLever

/-!
# The off-cycle covering closure: the demand anatomy and the pinned-stratum split
(`OffCycleCoveringClosure`)

This module (NEW; it edits no existing file) works the wave-18 parallel covering lane:
the residual `OffCycleCoveringSupply` of `OnsetBoundClosure` — the covering-family
consumer's verbatim demand, confined (losslessly, `coveringFamilies_iff_offCycle`) to
deep contexts (`2^493443 < ctx.X`) OFF the certified-cycle stratum.

## Goal 1 — the demand's exact anatomy (all proved)

Per deep off-cycle context the demand is `∃ fam : ObligationScaleFamily` with
`fam.onset ≤ 493443 ∧ ctx.d = fam.d ∧ ctx.Q ≤ 2^(max fam.onset 5)`.  Over the
context's own word, the family's `Q`/rationality/nontermination fields are all
reusable from the context (`coveringDemand_of_tail` builds the natural family from
them); the ONLY genuinely new inputs are

* the `c0`-sparse tail at ALL scales `L ≥ onset` with `onset ≤ 493443`, and
* the cap `ctx.Q ≤ 2^(max onset 5)`.

What the context itself supplies is exactly ONE sparse scale — its own — and that
scale lies strictly ABOVE the cap (`ctx_sparse_scale_above_cap`: `X = 2^L` with
`493443 < L`).  Sparsity at one scale `X` says nothing about the shells in
`[2^onset, X)` (a word can be dense in lower shells and sparse at one shell), no
field of the obligation layer carries a second scale, and no in-tree descent/ladder
statement transports `ShellSparseAt` between scales — the bridge layer has the full
tail (`counterexample_shellsAtAllLargeScales`) but with UNCONTROLLED onset.  This is
what blocks the direct supply.  A "covering by staggered onsets" is structurally
void: each family's tail is a `∀`-tail from its own onset (not a band), so any single
onset-capped family already carries the full demand; the manuscript (Section
"Fixed-cycle instantiation of Proposition 24.3", H.5/H.6 onset remark) resolves onset
coordination ONLY through scale-independent constant density floors — which exist
exactly on the certified-cycle stratum, already voided in wave 18.

Conversely the demand, where it holds, yields hard per-context facts
(`coveringDemand_Q_cap`: `ctx.Q ≤ 2^493443`; `coveringDemand_sparse_at_cap`: a sparse
shell AT the cap scale `493443`; `coveringDemand_sibling`: the full sibling).

## Goal 2 — the pinned stratum is FORCED VOID; the split is lossless (all proved)

**The new lever**: the demand's own `Q`-cap supplies the flip's `t`-bound.  For ANY
pin `value = P/(u·2^t)` with `u ≤ 7` whose 2-power is inside the denominator
(`2^t ≤ ctx.Q`), the demanded family cannot exist: `2^t ≤ ctx.Q ≤ 2^(max onset 5)`
gives `t ≤ max onset 5 ≤ 2^(max onset 5)`, so the in-tree flip
(`ObligationScaleFamily.onset_above_cap_of_pinned`) forces `onset > 493443` —
contradiction (`coveringDemand_pinned_void`).  Moreover every such pinned context is
AUTOMATICALLY off-cycle (`pinnedValue_windowPeriodic_void`), so the off-cycle
restriction gives no relief there.  Hence:

* `offCycleCovering_forces_pinnedQVoid` — the supply IMPLIES the voiding of every
  deep context carrying a reachable pin (`DeepPinnedQVoid`); the supply cannot
  fabricate families on that stratum, it must deny the contexts.
* `offCycleCoveringSupply_iff_pinnedSplit` — **the lossless split**:
  `OffCycleCoveringSupply ↔ DeepPinnedQVoid ∧ NonPinnedCoveringSupply`.  Through
  `coveringFamilies_iff_offCycle` this rewrites the FULL consumer hypothesis
  (`coveringFamilies_iff_pinnedSplit`).
* `deepSmallOddPartVoid_of_pinnedQVoid` — the structural corollary: instantiating
  the pin at `Q`'s own factorization (`u = ordCompl[2] Q`, `t = ν₂(Q)`) voids every
  deep context with `ordCompl[2] ctx.Q ≤ 7` — the odd-part guard idiom of the
  wave-14..17 surfaces, now a consequence of the covering supply.
* `multiScaleSiblingSupply_forces_pinnedQVoid` — the crosscheck: the SAME voiding is
  forced already by the weaker `MultiScaleSiblingSupply`, so the obligation is
  intrinsic to the sibling lane, not an artifact of the family packaging.
* `offCycleCovering_forces_deepValueLevers` — the difficulty floor: the supply
  implies all three OPEN deep value levers (dyadic / fifth / thirds), so closing
  the covering lane is at least as hard as the whole deep-lever axis.

## The exhaustiveness verdict (honest; goal 2's question answered)

The in-tree value classification is NOT exhaustive, and the non-pinned aperiodic
stratum is NOT provably empty.  The strata of the residual:

* certified-cycle words — VOID (wave 18, `certifiedCycleWindow_void`);
* reachable-pin words (`∃ u ≤ 7, t, P : value = P/(u·2^t), 2^t ≤ Q` — includes all
  `ordCompl[2] Q ≤ 7` contexts and all hidden reduced pins with 2-depth inside `Q`)
  — the demand is per-context UNSATISFIABLE; the supply must VOID these contexts,
  and no in-tree surface does (the open deep value levers / `DeepOrbitPinVoiding`
  cover only the three shapes `1/2^t`, `1/(5·2^t)`, `2/(3·2^t)` and the five fixed
  orbit data — not e.g. `value = 3/(7·2^t)`);
* the ESCAPE stratum — aperiodic words whose value admits NO reachable `u ≤ 7` pin
  (reduced denominator odd part `≥ 9`: e.g. `1/9`, `1/11`, `5/13`): NO in-tree
  lemma constrains their deep contexts; the manuscript routes them through the
  per-class descent (Appendix N classes — in Lean the frontier surface fields),
  not through the covering lane.

So the deliverable is the CONDITIONAL supply: `erdos260_of_pinnedSplitCovering`
reaches the endpoint from the two named pieces (`DeepPinnedQVoid` — a voiding
obligation, and `NonPinnedCoveringSupply` — the family construction demanded only on
the escape stratum), wired to the consumer's exact shape.

No `sorry`, no `admit`, no new `axiom`, no `native_decide`; additive only — no
existing module is edited.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 1.  The demand's anatomy: what it yields, what would build it -/

/-- **The demand forces the denominator cap**: a context satisfying the per-context
covering demand has `Q ≤ 2^493443` — the cap is part of the demand's content, NOT
supplied by any context field (the only in-tree size constraint is `2^27·Q < X`,
which at deep scales leaves `Q` as large as `~X/2^27 > 2^493416`). -/
theorem coveringDemand_Q_cap (ctx : ActualFailureContext)
    (h : ∃ fam : ObligationScaleFamily,
      fam.onset ≤ 493443 ∧ ctx.d = fam.d ∧ ctx.Q ≤ 2 ^ max fam.onset 5) :
    ctx.Q ≤ 2 ^ 493443 := by
  obtain ⟨fam, hcap, _hword, hQwin⟩ := h
  have hmax : max fam.onset 5 ≤ 493443 := max_le hcap (by norm_num)
  exact le_trans hQwin (Nat.pow_le_pow_right (by norm_num) hmax)

/-- **The demand forces a sparse shell AT the cap scale**: the family tail fires at
`L = 493443` itself — a sparse shell of the context word at a scale the context's own
failure (which lives strictly above the cap at deep contexts) never reaches. -/
theorem coveringDemand_sparse_at_cap (ctx : ActualFailureContext)
    (h : ∃ fam : ObligationScaleFamily,
      fam.onset ≤ 493443 ∧ ctx.d = fam.d ∧ ctx.Q ≤ 2 ^ max fam.onset 5) :
    ShellSparseAt ctx.d 493443 := by
  obtain ⟨fam, hcap, hword, _hQwin⟩ := h
  rw [hword]
  exact fam.sparse 493443 hcap

/-- The demand yields the full per-context sibling (the consumer's intermediate
shape) — recorded here as the local form of `siblingShell_of_cover`. -/
theorem coveringDemand_sibling (ctx : ActualFailureContext)
    (h : ∃ fam : ObligationScaleFamily,
      fam.onset ≤ 493443 ∧ ctx.d = fam.d ∧ ctx.Q ≤ 2 ^ max fam.onset 5) :
    SiblingShellInFiringWindow ctx := by
  obtain ⟨fam, hcap, hword, hQwin⟩ := h
  exact fam.siblingShell_of_cover hcap ctx hword hQwin

/-- **The natural-family constructor (what WOULD build the demand)**: an onset-capped
`c0`-sparse tail over the context's OWN word, plus the `Q`-cap, is ALL that is missing —
every other family field is reused from the context.  This isolates the two genuinely
new inputs of the demand. -/
theorem coveringDemand_of_tail (ctx : ActualFailureContext) {L0 : ℕ}
    (hL0 : L0 ≤ 493443) (htail : ∀ L : ℕ, L0 ≤ L → ShellSparseAt ctx.d L)
    (hQwin : ctx.Q ≤ 2 ^ max L0 5) :
    ∃ fam : ObligationScaleFamily,
      fam.onset ≤ 493443 ∧ ctx.d = fam.d ∧ ctx.Q ≤ 2 ^ max fam.onset 5 :=
  ⟨{ Q := ctx.Q
     d := ctx.d
     hQ := ctx.hQ
     hd := ctx.hd
     hnonterm := ctx.hnonterm
     hrational := ctx.hrational
     onset := L0
     sparse := htail }, hL0, rfl, hQwin⟩

/-- **What the context actually supplies**: exactly ONE sparse scale — its own — and at
deep contexts that scale lies strictly ABOVE the cap.  The gap to
`coveringDemand_of_tail` is the tail at all scales in `[L0, L)` and `(L, ∞)`: no
obligation-layer field and no in-tree transport supplies sparsity at any second
scale. -/
theorem ctx_sparse_scale_above_cap (ctx : ActualFailureContext)
    (hX : 2 ^ 493443 < ctx.X) :
    ∃ L : ℕ, ctx.X = 2 ^ L ∧ 493443 < L ∧ ShellSparseAt ctx.d L := by
  obtain ⟨L, hL⟩ := ctx.hXdyadic
  refine ⟨L, hL, ?_, ?_⟩
  · rcases Nat.lt_or_ge 493443 L with h | h
    · exact h
    · exfalso
      have hle : (2 : ℕ) ^ L ≤ 2 ^ 493443 := Nat.pow_le_pow_right (by norm_num) h
      rw [hL] at hX
      exact Nat.lt_irrefl _ (lt_of_lt_of_le hX hle)
  · show ((supportShell ctx.d (2 ^ L)).card : ℝ)
      < erdos260Constants.c0 * ((2 ^ L : ℕ) : ℝ)
    rw [← hL]
    exact ctx.hfailure

/-! ## Part 2.  The pinned stratum: the demand is per-context UNSATISFIABLE

The new lever: the demand's own `Q`-cap supplies the flip's `t`-bound.  A pin
`P/(u·2^t)` with `u ≤ 7` is REACHABLE at a context when `2^t ≤ ctx.Q` (in particular
whenever the pin arises by reducing `P/ctx.Q`, since then `u·2^t ∣ ctx.Q`) — and at a
reachable pin no onset-capped family over the word can exist. -/

/-- **The per-context pinned kill**: at any context whose word value carries a `u ≤ 7`
pin with the 2-power reachable (`2^t ≤ ctx.Q`, or outright `t ≤ 5`), the covering
demand is FALSE: the cap chain `2^t ≤ ctx.Q ≤ 2^(max onset 5)` bounds `t` inside the
flip's window, and the flip pushes the onset above `493443`. -/
theorem coveringDemand_pinned_void (ctx : ActualFailureContext) {u t : ℕ} {P : ℤ}
    (hupos : 0 < u) (hu7 : u ≤ 7)
    (heta : realWeightedValue (natBinaryAsReal ctx.d)
      = (P : ℝ) / ((u * 2 ^ t : ℕ) : ℝ))
    (ht : 2 ^ t ≤ ctx.Q ∨ t ≤ 5)
    (h : ∃ fam : ObligationScaleFamily,
      fam.onset ≤ 493443 ∧ ctx.d = fam.d ∧ ctx.Q ≤ 2 ^ max fam.onset 5) :
    False := by
  obtain ⟨fam, hcap, hword, hQwin⟩ := h
  have htwin : t ≤ 2 ^ max fam.onset 5 := by
    rcases ht with h2t | h5t
    · have hle : (2 : ℕ) ^ t ≤ 2 ^ max fam.onset 5 := le_trans h2t hQwin
      have hlog := Nat.log_mono_right (b := 2) hle
      rw [Nat.log_pow (by norm_num), Nat.log_pow (by norm_num)] at hlog
      exact le_trans hlog (Nat.le_of_lt Nat.lt_two_pow_self)
    · have h5max : 5 ≤ max fam.onset 5 := le_max_right _ _
      have hself : max fam.onset 5 < 2 ^ max fam.onset 5 := Nat.lt_two_pow_self
      omega
  have hetaf : realWeightedValue (natBinaryAsReal fam.d)
      = (P : ℝ) / ((u * 2 ^ t : ℕ) : ℝ) := by
    rw [← hword]
    exact heta
  have hflip : 493443 < fam.onset := fam.onset_above_cap_of_pinned hu7 hupos hetaf htwin
  omega

/-- **The forced voiding obligation (the pinned piece of the split)**: NO deep failure
context carries a reachable `u ≤ 7` pin.  This is what the covering supply (and
already the sibling supply) FORCES — a context-voiding statement, not a
family-construction statement. -/
def DeepPinnedQVoid : Prop :=
  ∀ ctx : ActualFailureContext, 2 ^ 493443 < ctx.X →
    ∀ u t : ℕ, ∀ P : ℤ, 0 < u → u ≤ 7 → 2 ^ t ≤ ctx.Q →
      realWeightedValue (natBinaryAsReal ctx.d) ≠ (P : ℝ) / ((u * 2 ^ t : ℕ) : ℝ)

/-- **The family-construction piece of the split**: the covering demand, demanded only
at deep off-cycle contexts whose value admits NO reachable pin — the escape stratum
(reduced denominator odd part `≥ 9`, certified-cycle aperiodic). -/
def NonPinnedCoveringSupply : Prop :=
  ∀ ctx : ActualFailureContext, 2 ^ 493443 < ctx.X →
    ¬ CertifiedCycleWindow ctx →
    (∀ u t : ℕ, ∀ P : ℤ, 0 < u → u ≤ 7 → 2 ^ t ≤ ctx.Q →
      realWeightedValue (natBinaryAsReal ctx.d) ≠ (P : ℝ) / ((u * 2 ^ t : ℕ) : ℝ)) →
    ∃ fam : ObligationScaleFamily,
      fam.onset ≤ 493443 ∧ ctx.d = fam.d ∧ ctx.Q ≤ 2 ^ max fam.onset 5

/-- **The supply forces the pinned voiding**: a reachably-pinned deep context is
automatically off-cycle (the pin voids window periodicity, hence the certified-cycle
stratum), so the supply applies to it — and the demanded family collides with the
flip.  The covering supply can only hold by DENYING the pinned stratum. -/
theorem offCycleCovering_forces_pinnedQVoid (h : OffCycleCoveringSupply) :
    DeepPinnedQVoid := by
  intro ctx hX u t P hupos hu7 h2t heta
  have hoff : ¬ CertifiedCycleWindow ctx := fun hccw =>
    pinnedValue_windowPeriodic_void ctx hupos hu7 heta
      (windowPeriodic_of_certifiedCycleWindow ctx hccw)
  exact coveringDemand_pinned_void ctx hupos hu7 heta (Or.inl h2t) (h ctx hX hoff)

/-- The split rebuilds the supply: pinned deep contexts are void, escape-stratum
contexts are supplied. -/
theorem offCycleCoveringSupply_of_pinnedSplit (hvoid : DeepPinnedQVoid)
    (hsup : NonPinnedCoveringSupply) : OffCycleCoveringSupply := by
  intro ctx hX hoff
  by_cases hpin : ∃ u t : ℕ, ∃ P : ℤ, 0 < u ∧ u ≤ 7 ∧ 2 ^ t ≤ ctx.Q ∧
      realWeightedValue (natBinaryAsReal ctx.d) = (P : ℝ) / ((u * 2 ^ t : ℕ) : ℝ)
  · obtain ⟨u, t, P, hupos, hu7, h2t, heta⟩ := hpin
    exact absurd heta (hvoid ctx hX u t P hupos hu7 h2t)
  · refine hsup ctx hX hoff ?_
    intro u t P hupos hu7 h2t heta
    exact hpin ⟨u, t, P, hupos, hu7, h2t, heta⟩

/-- **THE LOSSLESS SPLIT**: the off-cycle covering residual is EQUIVALENT to the
conjunction of the pinned voiding obligation and the escape-stratum supply — no
strength gap in either direction. -/
theorem offCycleCoveringSupply_iff_pinnedSplit :
    OffCycleCoveringSupply ↔ DeepPinnedQVoid ∧ NonPinnedCoveringSupply := by
  constructor
  · intro h
    exact ⟨offCycleCovering_forces_pinnedQVoid h, fun ctx hX hoff _ => h ctx hX hoff⟩
  · rintro ⟨hvoid, hsup⟩
    exact offCycleCoveringSupply_of_pinnedSplit hvoid hsup

/-- The split transported to the consumer's FULL covering hypothesis (composing the
wave-18 lossless off-cycle reduction): the consumer's verbatim demand is equivalent
to the two named pieces. -/
theorem coveringFamilies_iff_pinnedSplit :
    (∀ ctx : ActualFailureContext, 2 ^ 493443 < ctx.X →
      ∃ fam : ObligationScaleFamily,
        fam.onset ≤ 493443 ∧ ctx.d = fam.d ∧ ctx.Q ≤ 2 ^ max fam.onset 5)
    ↔ DeepPinnedQVoid ∧ NonPinnedCoveringSupply :=
  coveringFamilies_iff_offCycle.trans offCycleCoveringSupply_iff_pinnedSplit

/-! ## Part 3.  The structural corollary and the lane-intrinsic crosscheck -/

/-- The odd-part form of the forced voiding: no deep context with
`ordCompl[2] Q ≤ 7` — the guard idiom of the wave-14..17 surfaces. -/
def DeepSmallOddPartVoid : Prop :=
  ∀ ctx : ActualFailureContext, 2 ^ 493443 < ctx.X → ordCompl[2] ctx.Q ≤ 7 → False

/-- **The structural corollary**: the pinned voiding instantiated at `Q`'s own
factorization (`u = ordCompl[2] Q`, `t = ν₂(Q)`, `2^t ≤ Q` for free) voids every deep
small-odd-part context. -/
theorem deepSmallOddPartVoid_of_pinnedQVoid (h : DeepPinnedQVoid) :
    DeepSmallOddPartVoid := by
  intro ctx hX hu7
  have hupos : 0 < ordCompl[2] ctx.Q := Nat.ordCompl_pos 2 ctx.hQ.ne'
  have hQfact : ctx.Q = ordCompl[2] ctx.Q * 2 ^ ctx.Q.factorization 2 := by
    have hsh := shell_Q_eq_oddpart_mul_pow ctx
    simpa using hsh
  obtain ⟨P, hP⟩ := ctx.hrational
  have heta : realWeightedValue (natBinaryAsReal ctx.d)
      = (P : ℝ) / ((ordCompl[2] ctx.Q * 2 ^ ctx.Q.factorization 2 : ℕ) : ℝ) := by
    rw [← hQfact]
    exact hP
  have h2t : 2 ^ ctx.Q.factorization 2 ≤ ctx.Q := by
    conv_rhs => rw [hQfact]
    exact Nat.le_mul_of_pos_left _ hupos
  exact h ctx hX (ordCompl[2] ctx.Q) (ctx.Q.factorization 2) P hupos hu7 h2t heta

/-- The covering supply forces the small-odd-part voiding outright. -/
theorem offCycleCovering_forces_smallOddPartVoid (h : OffCycleCoveringSupply) :
    DeepSmallOddPartVoid :=
  deepSmallOddPartVoid_of_pinnedQVoid (offCycleCovering_forces_pinnedQVoid h)

/-- **The lane-intrinsic crosscheck**: already the WEAKER `MultiScaleSiblingSupply`
(the consumer's discharged intermediate) forces the same pinned voiding — the sibling
shell's own window cap bounds `t` exactly as the family cap does.  The voiding
obligation is intrinsic to the sibling lane, not an artifact of the family
packaging. -/
theorem multiScaleSiblingSupply_forces_pinnedQVoid (h : MultiScaleSiblingSupply) :
    DeepPinnedQVoid := by
  intro ctx hX u t P hupos hu7 h2t heta
  obtain ⟨L', h5, hcapL, hQle, hsp⟩ := h ctx hX
  have htL : t ≤ 2 ^ L' := by
    have hle : (2 : ℕ) ^ t ≤ 2 ^ L' := le_trans h2t hQle
    have hlog := Nat.log_mono_right (b := 2) hle
    rw [Nat.log_pow (by norm_num), Nat.log_pow (by norm_num)] at hlog
    exact le_trans hlog (Nat.le_of_lt Nat.lt_two_pow_self)
  exact multiScale_void_of_rep_window hu7 hupos ctx.hd ctx.hnonterm heta
    ⟨L', h5, hcapL, htL, hsp⟩

/-! ## Part 4.  The difficulty floor and the consumer endpoints -/

/-- **The difficulty floor**: the covering supply implies all three OPEN deep value
levers — closing the covering lane is at least as hard as the whole wave-5/8
deep-lever axis (`DeepDyadicValueLever` + fifth + thirds, the levers that feed
`deepOrbitPin` on the frontier surface). -/
theorem offCycleCovering_forces_deepValueLevers (h : OffCycleCoveringSupply) :
    DeepDyadicValueLever ∧ DeepTowerFifthValueLever ∧ DeepTowerThirdsValueLever := by
  have hms : MultiScaleSiblingSupply := multiScaleSiblingSupply_of_offCycleCovering h
  exact ⟨deepDyadicValueLever_of_siblingSupply hms,
    deepTowerFifthValueLever_of_siblingSupply hms,
    deepTowerThirdsValueLever_of_siblingSupply hms⟩

/-- The split discharges the full multi-scale sibling supply. -/
theorem multiScaleSiblingSupply_of_pinnedSplit (hvoid : DeepPinnedQVoid)
    (hsup : NonPinnedCoveringSupply) : MultiScaleSiblingSupply :=
  multiScaleSiblingSupply_of_offCycleCovering
    (offCycleCoveringSupply_of_pinnedSplit hvoid hsup)

/-- **The conditional endpoint**: `Erdos260Statement` from the two named pieces of the
split (plus the wave-5 lever surfaces) — the consumer's exact shape, with the pinned
stratum's obligation made explicit as a VOIDING and the family construction demanded
only on the escape stratum. -/
theorem erdos260_of_pinnedSplitCovering (hvoid : DeepPinnedQVoid)
    (hsup : NonPinnedCoveringSupply)
    (surfaces : DyadicValueLever → Erdos260DyadicLeverResidual) :
    Erdos260Statement :=
  erdos260_of_offCycleCovering
    (offCycleCoveringSupply_of_pinnedSplit hvoid hsup) surfaces

/-! ## Part 5.  Machine-readable status (honest) -/

/-- Honest machine-readable status of the off-cycle covering closure module. -/
def offCycleCoveringClosureStatus : List String :=
  [ "THE DEMAND'S ANATOMY (proved): per deep off-cycle context, OffCycleCoveringSupply " ++
      "demands an ObligationScaleFamily over the context's word with onset <= 493443 " ++
      "and ctx.Q <= 2^max(onset,5).  Over the context's own word every family field " ++
      "except two is reusable from the context (coveringDemand_of_tail); the genuinely " ++
      "new inputs are (i) the c0-sparse tail at ALL scales >= onset <= 493443 and (ii) " ++
      "the Q-cap.  The demand in turn yields ctx.Q <= 2^493443 (coveringDemand_Q_cap), " ++
      "a sparse shell AT the cap scale 493443 (coveringDemand_sparse_at_cap), and the " ++
      "full sibling (coveringDemand_sibling).",
    "WHAT BLOCKS THE DIRECT SUPPLY (verified against the in-tree surface): the context " ++
      "supplies exactly ONE sparse scale - its own X = 2^L with 493443 < L " ++
      "(ctx_sparse_scale_above_cap) - and hfailure says nothing about the shells in " ++
      "[2^onset, X): sparsity at one scale does not propagate downward (a word can be " ++
      "dense in lower shells), no obligation-layer field carries a second scale, and " ++
      "no in-tree descent/ladder lemma transports ShellSparseAt between scales; the " ++
      "bridge layer has the full tail only with UNCONTROLLED onset " ++
      "(counterexample_shellsAtAllLargeScales).  Staggered-onset coverings are " ++
      "structurally void: each family's tail is a forall-tail from its own onset, so " ++
      "any single onset-capped family already carries the full demand; the " ++
      "manuscript's onset discussion (fixed-cycle instantiation of Prop 24.3, H.5/H.6 " ++
      "remark) resolves onset coordination only via scale-independent constant " ++
      "density floors, which exist exactly on the certified-cycle stratum - already " ++
      "voided in wave 18.",
    "THE PINNED STRATUM IS FORCED VOID (proved, NEW): the demand's own Q-cap supplies " ++
      "the flip's t-bound - for any pin value = P/(u*2^t) with u <= 7 and 2^t <= ctx.Q " ++
      "(every pin obtained by reducing P/ctx.Q is of this form), the chain 2^t <= " ++
      "ctx.Q <= 2^max(onset,5) gives t <= max(onset,5) <= 2^max(onset,5), so " ++
      "onset_above_cap_of_pinned forces onset > 493443: the demanded family cannot " ++
      "exist (coveringDemand_pinned_void).  Reachably-pinned contexts are " ++
      "automatically off-cycle (pinnedValue_windowPeriodic_void), so the supply must " ++
      "DENY the stratum: offCycleCovering_forces_pinnedQVoid.  Crosscheck: already " ++
      "MultiScaleSiblingSupply forces the same voiding " ++
      "(multiScaleSiblingSupply_forces_pinnedQVoid) - the obligation is intrinsic to " ++
      "the sibling lane.",
    "THE LOSSLESS SPLIT (proved): OffCycleCoveringSupply <-> DeepPinnedQVoid (the " ++
      "voiding obligation: no deep context carries a reachable u <= 7 pin) AND " ++
      "NonPinnedCoveringSupply (the family construction, demanded only at deep " ++
      "off-cycle contexts admitting NO reachable pin - the escape stratum) " ++
      "(offCycleCoveringSupply_iff_pinnedSplit); composed with the wave-18 reduction " ++
      "it rewrites the consumer's FULL hypothesis (coveringFamilies_iff_pinnedSplit).  " ++
      "Structural corollary: every deep ordCompl[2] Q <= 7 context is voided under " ++
      "the supply (deepSmallOddPartVoid_of_pinnedQVoid - the wave-14..17 odd-part " ++
      "guard idiom).",
    "THE EXHAUSTIVENESS VERDICT (honest, goal 2): the in-tree value classification is " ++
      "NOT exhaustive and the escape stratum is NOT provably empty.  Strata: " ++
      "certified-cycle words VOID (wave 18); reachable-pin words (all ordCompl[2] Q " ++
      "<= 7 contexts plus hidden reduced pins with 2-depth inside Q) - demand " ++
      "per-context UNSATISFIABLE, supply only via context voiding, which no in-tree " ++
      "surface provides (the open deep value levers / DeepOrbitPinVoiding cover only " ++
      "the shapes 1/2^t, 1/(5*2^t), 2/(3*2^t) and the five fixed orbit data " ++
      "(3,1),(21,3),(15,1),(15,2),(105,7) - not e.g. 3/(7*2^t)); ESCAPE stratum " ++
      "(reduced denominator odd part >= 9: 1/9, 1/11, 5/13, ...) - NO in-tree lemma " ++
      "constrains their deep contexts; the manuscript routes them through the " ++
      "per-class Appendix N descent (the frontier surface fields), not the covering " ++
      "lane.  DIFFICULTY FLOOR (proved): the supply implies all three OPEN deep " ++
      "value levers (offCycleCovering_forces_deepValueLevers) - closing the covering " ++
      "lane is at least as hard as the deep-lever axis.",
    "SUPPLY ACHIEVED: CONDITIONAL.  The full OffCycleCoveringSupply is NOT proved " ++
      "(and cannot be by family construction alone: its pinned piece is a voiding " ++
      "obligation equivalent in kind to the open deep-lever axis).  Delivered: the " ++
      "exact two-piece residual DeepPinnedQVoid + NonPinnedCoveringSupply with the " ++
      "lossless equivalence, the natural-family constructor isolating the two " ++
      "missing inputs, and the endpoints multiScaleSiblingSupply_of_pinnedSplit / " ++
      "erdos260_of_pinnedSplitCovering wired to the consumer's exact shape " ++
      "(erdos260_of_offCycleCovering + the wave-5 lever surfaces).",
    "HYGIENE: additive only - ONE new module; no sorry / admit / new axiom / " ++
      "native_decide; every key declaration passes #print axioms within [propext, " ++
      "Classical.choice, Quot.sound]." ]

/-- The status ledger is non-empty (honest, non-vacuous). -/
theorem offCycleCoveringClosureStatus_nonempty :
    offCycleCoveringClosureStatus ≠ [] := by
  simp [offCycleCoveringClosureStatus]

/-! ## Part 6.  Axiom-cleanliness audit
Every key declaration; expected axioms `[propext, Classical.choice, Quot.sound]` or
fewer. -/

#print axioms coveringDemand_Q_cap
#print axioms coveringDemand_sparse_at_cap
#print axioms coveringDemand_sibling
#print axioms coveringDemand_of_tail
#print axioms ctx_sparse_scale_above_cap
#print axioms coveringDemand_pinned_void
#print axioms offCycleCovering_forces_pinnedQVoid
#print axioms offCycleCoveringSupply_of_pinnedSplit
#print axioms offCycleCoveringSupply_iff_pinnedSplit
#print axioms coveringFamilies_iff_pinnedSplit
#print axioms deepSmallOddPartVoid_of_pinnedQVoid
#print axioms offCycleCovering_forces_smallOddPartVoid
#print axioms multiScaleSiblingSupply_forces_pinnedQVoid
#print axioms offCycleCovering_forces_deepValueLevers
#print axioms multiScaleSiblingSupply_of_pinnedSplit
#print axioms erdos260_of_pinnedSplitCovering
#print axioms offCycleCoveringClosureStatus_nonempty

end

end Erdos260
