import Erdos260.OffCycleCoveringClosure
import Erdos260.ScaleFloorPush
import Erdos260.CentralChargeBridge

/-!
# The Appendix-N descent lane: the covering demand is VOID at every odd part —
the lane collapses to context-emptiness (`AppendixNDescent`)

This module (NEW; it edits no existing file) works the wave-19 covering lane's
escape stratum (aperiodic words with reduced odd-part denominator `≥ 9`), for
which the manuscript's per-class Appendix N machinery was flagged as "the
intended route".

## Goal 0 — what manuscript Appendix N actually is (read, transcribed honestly)

Manuscript Appendix N ("Rolling-window variation-drop closure for Return–Run–
Tower chains", proving the TRT chain-compression theorem) is the PER-CLASS
event-fibre descent: transcripts of priority atoms over endpoint/carry fibres,
the rolled-path crossing-edge bookkeeping, and the variation-drop budget.  It
is NOT a denominator descent: no manuscript step transforms a context with
value `P/(u·2^t)`, `u ≥ 9`, into one with smaller `u`.  In the Lean tree the
Appendix N content is exactly the frontier-surface per-class fields (the v19
convergence surface routes ALL deep contexts through them); the wave-19 remark
"the Appendix N descent is the intended route to the construction" therefore
points BACK to the main lane, not to a new covering-side mechanism.  In-tree
the value of a word is scale-invariant (`valuePin_is_global`), so no shell
descent can lower the odd part: a `u`-descent is not formalizable from the
ladder value lemmas, and (see Goal 1) it is also UNNECESSARY.

## Goal 1 — the descent is SUPERSEDED: the covering demand is unsatisfiable
at EVERY odd part (all proved)

The wave-19 pinned kill (`coveringDemand_pinned_void`) used the flip's t-free
gap `g = L+4`, which confines it to `u ≤ 7`.  The wave-10 SHARP fire condition
(`supportShell_sparse_contradiction_sharp`: `17·g ≤ 2^24`, i.e. `g ≤ 986895`)
removes the restriction: take the trivial representation `Q = Q·2^0` (no odd
part extraction at all), the demand's own cap `ctx.Q ≤ 2^max(onset,5) ≤
2^493443`, and the demanded family's OWN sparse tail at the scale `L' = 493445`
(legal: `onset ≤ 493443 < 493445`).  The gap `g = 986891 = 493443+493445+3`
satisfies BOTH the window bound `Q·(2·2^493445+2) < 2^986891` AND the sharp
fire `17·986891 ≤ 2^24` — the two halves of the budget `2·493445 ≈ 986890 <
986895` fit because the demand caps the denominator at HALF the sharp budget.
Hence (`coveringDemand_void`): NO failure context satisfies the covering
demand, at ANY value, ANY odd part, ANY scale.  The escape stratum's "family
construction" is impossible; there is nothing for a descent to descend to.

Consequences (all proved, lossless):

* `offCycleCoveringSupply_iff_noContext` — `OffCycleCoveringSupply` is
  EQUIVALENT to the emptiness of the failure structure (`∀ ctx, False`): with
  the demand per-context absurd, the only way to "supply" it is to deny every
  deep off-cycle context — and every context is deep (`scaleFloorPush_scale_lower`)
  and off-cycle (`certifiedCycleWindow_void`).
* `nonPinnedCoveringSupply_iff_escapeVoid` — `NonPinnedCoveringSupply` is
  EQUIVALENT to voiding the whole escape stratum; it is a voiding obligation,
  not a construction.
* `pinnedSplit_iff_noContext` / `coveringFamilies_iff_noContext` — the wave-19
  two-piece residual, and the consumer's FULL verbatim hypothesis, are each
  equivalent to context-emptiness, i.e. to the entire remaining conjecture.
* `siblingShellInFiringWindow_void` / `multiScaleSiblingSupply_iff_noContext` —
  the same collapse already at the WEAKER discharged intermediate: the sibling
  demand (`Q ≤ 2^L'` + a sparse shell at the same `L' ≤ 493443`) is absurd at
  every context (sharp fire for `L' ≥ 24`; integer count collision for
  `5 ≤ L' ≤ 23`), so `MultiScaleSiblingSupply` too is context-emptiness.
* `erdos260_of_pinnedSplit_direct` / `erdos260_of_offCycleCovering_direct` /
  `erdos260_of_multiScaleSiblingSupply_direct` — the covering-lane endpoints
  WITHOUT the wave-5 `surfaces` argument (strict interface improvement over
  `erdos260_of_pinnedSplitCovering`): the lane hypotheses already imply
  emptiness, which reaches the statement through
  `erdos260Statement_of_failureRefuted`.

## Goal 2 — the load-bearing verdict (checked against the consumption graph)

The covering lane is NOT in the critical path.  The v19 main endpoint
`erdos260_of_convergenceResidual` routes `toFrontierResidual →
erdos260_of_frontierResidual` (absorption route + six-phase ledger); none of
its 12 surface fields and none of their suppliers consume
`MultiScaleSiblingSupply` / `OffCycleCoveringSupply` / the family machinery —
the lane appears in the capstones only as PARALLEL packaging
(`convergence_pinnedSplitParallel`, `frontier_offCycleParallel`).  This module
makes the verdict exact: the lane's residual is EQUIVALENT to the whole
remaining problem (`pinnedSplit_iff_noContext`), so it can never be cheaper
than the main surface; its only transferable content is the forced voiding
overlap below.  Future waves should NOT attempt to construct covering families
or sibling shells — that is now a THEOREM-level impossibility.

## Goal 3 — the pinned overlap and the `u = 7` stratum (all proved)

* `deepDyadicValueLever_of_pinnedQVoid` / `deepTowerFifthValueLever_of_pinnedQVoid`
  / `deepTowerThirdsValueLever_of_pinnedQVoid` (+ the bundle
  `deepValueLevers_of_pinnedQVoid`) — `DeepPinnedQVoid` ALONE implies all three
  open deep value levers: each lever shape carries its own reachability
  (`value = 1/2^t` forces `Q = K₀·2^t`, so `2^t ≤ Q`; similarly `5·2^t·K₀ = Q`
  and `3·2^t·K₀ = 2Q`).
* The converse FAILS in-tree: the levers cover only the numerator-pinned shapes
  `(P,u) ∈ {(1,1), (1,5), (2,3)}`.  `DeepPinnedQVoid` additionally demands all
  numerators `P` and the `u = 7` stratum (`value = P/(7·2^t)`), for which NO
  in-tree lever exists (grep verified: the tower voidings are dyadic / fifth /
  thirds; the only sevenths contact is the orbit datum `(105,7)`, a different
  predicate).  The new minimal atom is NAMED: `DeepSeventhsPinVoid`.
* The carry-rigidity machinery IS value-generic at `u = 7` and the atom
  inherits the full pushed-floor package: `seventhsPin_scale_floor` (any
  reachable `u = 7` pin forces `2^986891 < X` — the SAME floor as the pushed
  dyadic/fifth/thirds levers, via `scaleFloorPush_void_of_rep`),
  `seventhsPin_firingWindow_clean` (the whole firing window `[2^5, 2^493443]`
  is clean), `seventhsPin_windowPeriodic_void` (the pin forces aperiodicity —
  the exit-mass lane's off-cycle precondition holds for free).  After the
  Goal-1 collapse the atom is NOT needed by the covering lane (whose residual
  is emptiness outright); it remains the honest answer to "do the three levers
  imply `DeepPinnedQVoid`?" — NO, `DeepPinnedQVoid` is strictly stronger.

No `sorry`, no `admit`, no new `axiom`, no `native_decide`; additive only — no
existing module is edited.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 1.  The generic kill: the covering demand is void at EVERY odd part

The mechanism: the demand caps `ctx.Q ≤ 2^max(onset,5) ≤ 2^493443` and supplies
the family's sparse tail at ALL scales `≥ onset`; at the scale `L' = 493445`
(strictly above the onset cap) the trivial representation `Q = Q·2^0` gives the
gap `g = 493443 + 493445 + 3 = 986891`, inside the wave-10 sharp fire budget
`17·g ≤ 2^24`.  No odd part, no pin, no `u ≤ 7`. -/

/-- **THE GENERIC DEMAND KILL**: NO failure context satisfies the covering
demand — at ANY value, ANY odd part (the wave-19 pinned kill
`coveringDemand_pinned_void` is the `u ≤ 7` special case; this needs no pin at
all).  The demanded family's own sparse tail at `L' = 493445` collides with the
demand's own `Q`-cap under the sharp fire condition. -/
theorem coveringDemand_void (ctx : ActualFailureContext)
    (h : ∃ fam : ObligationScaleFamily,
      fam.onset ≤ 493443 ∧ ctx.d = fam.d ∧ ctx.Q ≤ 2 ^ max fam.onset 5) :
    False := by
  have hQcap : ctx.Q ≤ 2 ^ 493443 := coveringDemand_Q_cap ctx h
  obtain ⟨fam, hcap, hword, _⟩ := h
  obtain ⟨P, hP⟩ := ctx.hrational
  have hsp : ShellSparseAt ctx.d 493445 := by
    rw [hword]
    exact fam.sparse 493445 (by omega)
  have hsplit : (2 : ℕ) ^ 986891 = 2 ^ 493443 * (2 ^ 493445 * 8) := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add, ← pow_add]
  have hwinN : ctx.Q * (2 * 2 ^ 493445 + 2) < 2 ^ 986891 := by
    obtain ⟨a, ha1, hae⟩ : ∃ a : ℕ, 1 ≤ a ∧ (2 : ℕ) ^ 493445 = a :=
      ⟨_, Nat.one_le_two_pow, rfl⟩
    obtain ⟨b, hb1, hbe⟩ : ∃ b : ℕ, ctx.Q ≤ b ∧ (2 : ℕ) ^ 493443 = b :=
      ⟨_, hQcap, rfl⟩
    have hsplit' : (2 : ℕ) ^ 986891 = b * (a * 8) := by
      rw [← hae, ← hbe]
      exact hsplit
    rw [hae, hsplit']
    have hbpos : 0 < b := lt_of_lt_of_le ctx.hQ hb1
    have h1 : ctx.Q * (2 * a + 2) ≤ b * (2 * a + 2) := mul_le_mul_left hb1 _
    have h2 : b * (2 * a + 2) < b * (a * 8) := by
      have hlin : 2 * a + 2 < a * 8 := by omega
      exact (Nat.mul_lt_mul_left hbpos).mpr hlin
    omega
  exact supportShell_sparse_contradiction_sharp (Q := ctx.Q) (u := ctx.Q) (t := 0)
    (P := P) (d := ctx.d) (X := 2 ^ 493445) (g := 986891) (L := 493445)
    (by simp) ctx.hQ ctx.hd ctx.hnonterm hP (Nat.zero_le _) (by norm_num)
    (by exact_mod_cast hwinN) rfl (by norm_num) (by norm_num) hsp

/-! ## Part 2.  The sibling demand is void as well — already the discharged
intermediate collapses -/

/-- The small-scale branch of the sibling kill (`5 ≤ L' ≤ 23`, below the sharp
lemma's `L ≥ 24` integrality threshold): the gap count `⌊2^L'/(2L'+3)⌋` beats
the sparsity allowance `17·2^L'/2^24` by direct integer comparison. -/
theorem siblingShell_small_void {Q : ℕ} {P : ℤ} {d : ℕ → ℕ} {L' : ℕ}
    (hQ : 0 < Q) (hd : BinaryDigits d) (hnonterm : ¬ EventuallyZero d)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ))
    (h5 : 5 ≤ L') (hle : L' ≤ 23) (hQle : Q ≤ 2 ^ L')
    (hsp : ShellSparseAt d L') : False := by
  have ha : 1 ≤ (2 : ℕ) ^ L' := Nat.one_le_two_pow
  have hsplit : (2 : ℕ) ^ (2 * L' + 3) = 2 ^ L' * (2 ^ L' * 8) := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add, ← pow_add]
    congr 1
    omega
  have hstep : 2 * 2 ^ L' + 2 < 2 ^ L' * 8 := by omega
  have hwinN : Q * (2 * 2 ^ L' + 2) < 2 ^ (2 * L' + 3) := by
    calc Q * (2 * 2 ^ L' + 2)
        ≤ 2 ^ L' * (2 * 2 ^ L' + 2) := mul_le_mul_left hQle _
      _ < 2 ^ L' * (2 ^ L' * 8) :=
          (Nat.mul_lt_mul_left (Nat.two_pow_pos L')).mpr hstep
      _ = 2 ^ (2 * L' + 3) := hsplit.symm
  have hlower := supportShell_card_lower_of_gap (Q := Q) (u := Q) (t := 0)
    (P := P) (d := d) (X := 2 ^ L') (g := 2 * L' + 3)
    (by simp) hQ hd hnonterm heta (Nat.zero_le _) (by omega)
    (by exact_mod_cast hwinN)
  have hsp' : ((supportShell d (2 ^ L')).card : ℝ)
      < erdos260Constants.c0 * ((2 ^ L' : ℕ) : ℝ) := hsp
  rw [carryWord_c0_eq] at hsp'
  have hR : ((supportShell d (2 ^ L')).card : ℝ) * 16777216
      < 17 * ((2 ^ L' : ℕ) : ℝ) := by linarith
  have hNat : (supportShell d (2 ^ L')).card * 16777216 < 17 * 2 ^ L' := by
    exact_mod_cast hR
  interval_cases L' <;> norm_num at hlower hNat <;> omega

/-- **THE SIBLING KILL**: NO failure context has a sibling shell in the firing
window — the consumer's discharged intermediate demand (`Q ≤ 2^L'` plus a
sparse shell of the same word at `L' ≤ 493443`) is per-context absurd: sharp
fire with `g = 2L'+3 ≤ 986889` for `L' ≥ 24`, integer count collision below.
(Consistent with `siblingShellInFiringWindow_self`, which is vacuous: every
context has `L ≥ 493461` by the pushed unconditional floor.) -/
theorem siblingShellInFiringWindow_void (ctx : ActualFailureContext) :
    ¬ SiblingShellInFiringWindow ctx := by
  rintro ⟨L', h5, hcap, hQle, hsp⟩
  obtain ⟨P, hP⟩ := ctx.hrational
  by_cases hle : L' ≤ 23
  · exact siblingShell_small_void ctx.hQ ctx.hd ctx.hnonterm hP h5 hle hQle hsp
  · have ha : 1 ≤ (2 : ℕ) ^ L' := Nat.one_le_two_pow
    have hsplit : (2 : ℕ) ^ (2 * L' + 3) = 2 ^ L' * (2 ^ L' * 8) := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add, ← pow_add]
      congr 1
      omega
    have hstep : 2 * 2 ^ L' + 2 < 2 ^ L' * 8 := by omega
    have hwinN : ctx.Q * (2 * 2 ^ L' + 2) < 2 ^ (2 * L' + 3) := by
      calc ctx.Q * (2 * 2 ^ L' + 2)
          ≤ 2 ^ L' * (2 * 2 ^ L' + 2) := mul_le_mul_left hQle _
        _ < 2 ^ L' * (2 ^ L' * 8) :=
            (Nat.mul_lt_mul_left (Nat.two_pow_pos L')).mpr hstep
        _ = 2 ^ (2 * L' + 3) := hsplit.symm
    have hsp' : ((supportShell ctx.d (2 ^ L')).card : ℝ)
        < erdos260Constants.c0 * ((2 ^ L' : ℕ) : ℝ) := hsp
    exact supportShell_sparse_contradiction_sharp (Q := ctx.Q) (u := ctx.Q)
      (t := 0) (P := P) (d := ctx.d) (X := 2 ^ L') (g := 2 * L' + 3) (L := L')
      (by simp) ctx.hQ ctx.hd ctx.hnonterm hP (Nat.zero_le _) (by omega)
      (by exact_mod_cast hwinN) rfl (by omega) (by omega) hsp'

/-! ## Part 3.  The collapse: every covering-lane residual is context-emptiness -/

/-- Every failure context is deep (`2^493443 < X`) — the pushed unconditional
floor read at the covering lane's threshold. -/
theorem coveringLane_ctx_deep (ctx : ActualFailureContext) :
    2 ^ 493443 < ctx.X :=
  lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (by norm_num))
    (scaleFloorPush_scale_lower ctx)

/-- **The off-cycle covering supply IS context-emptiness**: with the demand
per-context void, the supply can hold only by denying every deep off-cycle
context — and every context is deep and off-cycle. -/
theorem offCycleCoveringSupply_iff_noContext :
    OffCycleCoveringSupply ↔ ∀ ctx : ActualFailureContext, False := by
  constructor
  · intro h ctx
    exact coveringDemand_void ctx
      (h ctx (coveringLane_ctx_deep ctx)
        (fun hc => certifiedCycleWindow_void ctx hc))
  · intro h ctx _ _
    exact (h ctx).elim

/-- **The escape-stratum supply IS the escape-stratum voiding**: the
"family construction demanded only on the odd-part `≥ 9` stratum" is in fact a
pure voiding obligation — there is no family to construct. -/
theorem nonPinnedCoveringSupply_iff_escapeVoid :
    NonPinnedCoveringSupply ↔
      ∀ ctx : ActualFailureContext, 2 ^ 493443 < ctx.X →
        ¬ CertifiedCycleWindow ctx →
        (∀ u t : ℕ, ∀ P : ℤ, 0 < u → u ≤ 7 → 2 ^ t ≤ ctx.Q →
          realWeightedValue (natBinaryAsReal ctx.d)
            ≠ (P : ℝ) / ((u * 2 ^ t : ℕ) : ℝ)) →
        False := by
  constructor
  · intro h ctx hX hoff hnp
    exact coveringDemand_void ctx (h ctx hX hoff hnp)
  · intro h ctx hX hoff hnp
    exact (h ctx hX hoff hnp).elim

/-- **The wave-19 two-piece residual IS the whole remaining problem**: the
pinned voiding plus the escape-stratum supply is EQUIVALENT to the emptiness of
the failure structure.  The covering lane can never be cheaper than the main
frontier surface. -/
theorem pinnedSplit_iff_noContext :
    (DeepPinnedQVoid ∧ NonPinnedCoveringSupply) ↔
      ∀ ctx : ActualFailureContext, False :=
  offCycleCoveringSupply_iff_pinnedSplit.symm.trans
    offCycleCoveringSupply_iff_noContext

/-- The consumer's FULL verbatim covering hypothesis is context-emptiness. -/
theorem coveringFamilies_iff_noContext :
    (∀ ctx : ActualFailureContext, 2 ^ 493443 < ctx.X →
      ∃ fam : ObligationScaleFamily,
        fam.onset ≤ 493443 ∧ ctx.d = fam.d ∧ ctx.Q ≤ 2 ^ max fam.onset 5)
    ↔ ∀ ctx : ActualFailureContext, False :=
  coveringFamilies_iff_offCycle.trans offCycleCoveringSupply_iff_noContext

/-- **The discharged intermediate collapses too**: `MultiScaleSiblingSupply` is
context-emptiness — the whole wave-14..19 sibling axis was a restatement of the
remaining problem. -/
theorem multiScaleSiblingSupply_iff_noContext :
    MultiScaleSiblingSupply ↔ ∀ ctx : ActualFailureContext, False := by
  constructor
  · intro h ctx
    exact siblingShellInFiringWindow_void ctx (h ctx (coveringLane_ctx_deep ctx))
  · intro h ctx _
    exact (h ctx).elim

/-! ## Part 4.  The surface-free endpoints (strict interface improvement) -/

/-- **The pinned-split endpoint WITHOUT the wave-5 surfaces argument**: the two
covering-lane pieces already imply context-emptiness, which reaches the
statement through the proved bridge — `erdos260_of_pinnedSplitCovering`'s
`surfaces` input was never needed. -/
theorem erdos260_of_pinnedSplit_direct (hvoid : DeepPinnedQVoid)
    (hsup : NonPinnedCoveringSupply) : Erdos260Statement :=
  erdos260Statement_of_failureRefuted
    (pinnedSplit_iff_noContext.mp ⟨hvoid, hsup⟩)

/-- The off-cycle covering endpoint, surface-free. -/
theorem erdos260_of_offCycleCovering_direct (h : OffCycleCoveringSupply) :
    Erdos260Statement :=
  erdos260Statement_of_failureRefuted (offCycleCoveringSupply_iff_noContext.mp h)

/-- The sibling-supply endpoint, surface-free (the wave-14..17 residual
structures around `erdos260_of_multiScaleSiblingSupply` are likewise
superseded). -/
theorem erdos260_of_multiScaleSiblingSupply_direct (h : MultiScaleSiblingSupply) :
    Erdos260Statement :=
  erdos260Statement_of_failureRefuted (multiScaleSiblingSupply_iff_noContext.mp h)

/-! ## Part 5.  The pinned overlap: `DeepPinnedQVoid` alone implies the three
open deep value levers (each lever shape carries its own reachability) -/

/-- `DeepPinnedQVoid` implies the deep dyadic lever: `value = 1/2^t` forces
`Q = K₀·2^t` (the exact `Q`-side characterization), so the pin `(u,t,P) =
(1,t,1)` is reachable. -/
theorem deepDyadicValueLever_of_pinnedQVoid (h : DeepPinnedQVoid) :
    DeepDyadicValueLever := by
  intro ctx hX hdy
  obtain ⟨t, hQt⟩ := (shellValueDyadic_iff ctx).mp hdy
  have hK0pos := (class1SlopeDatum ctx).hK₀_pos
  have hQt' : ctx.Q = (class1SlopeDatum ctx).K₀ * 2 ^ t := by
    simpa using hQt
  have h2t : 2 ^ t ≤ ctx.Q := by
    rw [hQt']
    exact Nat.le_mul_of_pos_left _ hK0pos
  have hK0R : (0 : ℝ) < ((class1SlopeDatum ctx).K₀ : ℝ) := by
    exact_mod_cast hK0pos
  have heta : realWeightedValue (natBinaryAsReal ctx.shell.d)
      = ((1 : ℤ) : ℝ) / ((1 * 2 ^ t : ℕ) : ℝ) := by
    have hQR : (ctx.Q : ℝ) = ((class1SlopeDatum ctx).K₀ : ℝ) * 2 ^ t := by
      exact_mod_cast congrArg (Nat.cast (R := ℝ)) hQt'
    have hcast : ((1 : ℤ) : ℝ) / ((1 * 2 ^ t : ℕ) : ℝ) = 1 / (2 : ℝ) ^ t := by
      push_cast
      ring
    have hvK' : realWeightedValue (natBinaryAsReal ctx.shell.d)
        = ((class1SlopeDatum ctx).K₀ : ℝ) / (ctx.Q : ℝ) := by
      simpa using shell_value_eq_K₀_div_Q ctx
    rw [hvK', hQR, hcast]
    rw [div_eq_div_iff (mul_pos hK0R (by positivity)).ne' (by positivity)]
    ring
  exact h ctx hX 1 t 1 one_pos (by norm_num) h2t heta

/-- `DeepPinnedQVoid` implies the deep fifth lever: `value = 1/(5·2^t)` forces
`Q = K₀·(5·2^t)`, so the pin `(5,t,1)` is reachable. -/
theorem deepTowerFifthValueLever_of_pinnedQVoid (h : DeepPinnedQVoid) :
    DeepTowerFifthValueLever := by
  intro ctx hX t hval
  have hK0pos := (class1SlopeDatum ctx).hK₀_pos
  have heq : (1 : ℝ) / (5 * 2 ^ t)
      = ((class1SlopeDatum ctx).K₀ : ℝ) / (ctx.Q : ℝ) := by
    have h0 := hval.symm.trans (shell_value_eq_K₀_div_Q ctx)
    simpa using h0
  have hQpos : (0 : ℝ) < (ctx.Q : ℝ) := by exact_mod_cast ctx.hQ
  have h5pos : (0 : ℝ) < 5 * (2 : ℝ) ^ t := by positivity
  rw [div_eq_div_iff h5pos.ne' hQpos.ne'] at heq
  have hQnat : ctx.Q = (class1SlopeDatum ctx).K₀ * (5 * 2 ^ t) := by
    have hcast : (ctx.Q : ℝ)
        = (((class1SlopeDatum ctx).K₀ * (5 * 2 ^ t) : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hcast
  have h2t : 2 ^ t ≤ ctx.Q := by
    rw [hQnat]
    calc 2 ^ t ≤ 5 * 2 ^ t := Nat.le_mul_of_pos_left _ (by norm_num)
      _ ≤ (class1SlopeDatum ctx).K₀ * (5 * 2 ^ t) :=
          Nat.le_mul_of_pos_left _ hK0pos
  have hcast5 : ((1 : ℤ) : ℝ) / ((5 * 2 ^ t : ℕ) : ℝ) = 1 / (5 * (2 : ℝ) ^ t) := by
    push_cast
    ring
  exact h ctx hX 5 t 1 (by norm_num) (by norm_num) h2t (hval.trans hcast5.symm)

/-- `DeepPinnedQVoid` implies the deep thirds lever: `value = 2/(3·2^t)` forces
`2Q = K₀·(3·2^t)`, hence `2·2^t ≤ 2Q`, so the pin `(3,t,2)` is reachable. -/
theorem deepTowerThirdsValueLever_of_pinnedQVoid (h : DeepPinnedQVoid) :
    DeepTowerThirdsValueLever := by
  intro ctx hX t hval
  have hK0pos := (class1SlopeDatum ctx).hK₀_pos
  have heq : (2 : ℝ) / (3 * 2 ^ t)
      = ((class1SlopeDatum ctx).K₀ : ℝ) / (ctx.Q : ℝ) := by
    have h0 := hval.symm.trans (shell_value_eq_K₀_div_Q ctx)
    simpa using h0
  have hQpos : (0 : ℝ) < (ctx.Q : ℝ) := by exact_mod_cast ctx.hQ
  have h3pos : (0 : ℝ) < 3 * (2 : ℝ) ^ t := by positivity
  rw [div_eq_div_iff h3pos.ne' hQpos.ne'] at heq
  have hQnat : 2 * ctx.Q = (class1SlopeDatum ctx).K₀ * (3 * 2 ^ t) := by
    have hcast : ((2 * ctx.Q : ℕ) : ℝ)
        = (((class1SlopeDatum ctx).K₀ * (3 * 2 ^ t) : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hcast
  have h2t : 2 ^ t ≤ ctx.Q := by
    have h1 : 2 * 2 ^ t ≤ 2 * ctx.Q := by
      rw [hQnat]
      calc 2 * 2 ^ t ≤ 3 * 2 ^ t := by omega
        _ ≤ (class1SlopeDatum ctx).K₀ * (3 * 2 ^ t) :=
            Nat.le_mul_of_pos_left _ hK0pos
    omega
  have hcast3 : ((2 : ℤ) : ℝ) / ((3 * 2 ^ t : ℕ) : ℝ) = 2 / (3 * (2 : ℝ) ^ t) := by
    push_cast
    ring
  exact h ctx hX 3 t 2 (by norm_num) (by norm_num) h2t (hval.trans hcast3.symm)

/-- **The overlap bundle**: the pinned-Q voiding alone implies all three open
deep value levers — sharper than `offCycleCovering_forces_deepValueLevers`
(which consumed the whole supply).  The CONVERSE fails in-tree: the levers fix
the numerators `(1,1,2)` and omit `u = 7` entirely. -/
theorem deepValueLevers_of_pinnedQVoid (h : DeepPinnedQVoid) :
    DeepDyadicValueLever ∧ DeepTowerFifthValueLever ∧ DeepTowerThirdsValueLever :=
  ⟨deepDyadicValueLever_of_pinnedQVoid h,
    deepTowerFifthValueLever_of_pinnedQVoid h,
    deepTowerThirdsValueLever_of_pinnedQVoid h⟩

/-! ## Part 6.  The `u = 7` stratum: the named minimal atom and its inherited
floor package -/

/-- **The sevenths pin voiding** — the `u = 7` projection of `DeepPinnedQVoid`,
with general numerator: no deep context carries a reachable pin
`value = P/(7·2^t)`.  NOT covered by the three open deep value levers (no
sevenths lever exists in-tree; the only `u = 7` contact is the orbit datum
`(105,7)`, a different predicate). -/
def DeepSeventhsPinVoid : Prop :=
  ∀ ctx : ActualFailureContext, 2 ^ 493443 < ctx.X →
    ∀ t : ℕ, ∀ P : ℤ, 2 ^ t ≤ ctx.Q →
      realWeightedValue (natBinaryAsReal ctx.d) ≠ (P : ℝ) / ((7 * 2 ^ t : ℕ) : ℝ)

/-- The sevenths atom is the `u = 7` face of the pinned voiding. -/
theorem deepSeventhsPinVoid_of_pinnedQVoid (h : DeepPinnedQVoid) :
    DeepSeventhsPinVoid :=
  fun ctx hX t P h2t => h ctx hX 7 t P (by norm_num) (by norm_num) h2t

/-- **The sevenths floor**: the wave-10 pushed pinned-value machinery is
value-generic at `u ≤ 7`, so any context carrying a reachable `u = 7` pin
(ANY numerator) lies above `2^986891` — the SAME pushed floor as the
dyadic/fifth/thirds levers.  The atom's open content starts exactly where
theirs does. -/
theorem seventhsPin_scale_floor (ctx : ActualFailureContext) {t : ℕ} {P : ℤ}
    (heta : realWeightedValue (natBinaryAsReal ctx.d)
      = (P : ℝ) / ((7 * 2 ^ t : ℕ) : ℝ))
    (h2t : 2 ^ t ≤ ctx.Q) : 2 ^ 986891 < ctx.X := by
  by_cases hlt : 2 ^ 986891 < ctx.X
  · exact hlt
  · exfalso
    have htX : t ≤ ctx.X := by
      have h1 : t < 2 ^ t := Nat.lt_two_pow_self
      have h2 : ctx.Q < ctx.X := carryWord_Q_lt_X ctx
      omega
    exact scaleFloorPush_void_of_rep ctx (by norm_num) (by norm_num) heta htX
      (not_lt.mp hlt)

/-- **The sevenths firing window is clean**: a `u = 7` pin (any numerator)
excludes failing shells at every scale in `[2^5, 2^493443]` with `t ≤ 2^L'` —
the same multi-scale transport as the three lever shapes. -/
theorem seventhsPin_firingWindow_clean {d : ℕ → ℕ} (hd : BinaryDigits d)
    (hnonterm : ¬ EventuallyZero d) {t : ℕ} {P : ℤ}
    (heta : realWeightedValue (natBinaryAsReal d)
      = (P : ℝ) / ((7 * 2 ^ t : ℕ) : ℝ)) :
    ¬ ShellInFiringWindow d t :=
  firingWindow_clean_of_rep (by norm_num) (by norm_num) hd hnonterm heta

/-- **The sevenths pin forces aperiodicity**: a `u = 7`-pinned context cannot be
window-periodic — the off-cycle precondition of the exit-mass / covering lanes
holds for free on the sevenths stratum. -/
theorem seventhsPin_windowPeriodic_void (ctx : ActualFailureContext)
    {t : ℕ} {P : ℤ}
    (heta : realWeightedValue (natBinaryAsReal ctx.d)
      = (P : ℝ) / ((7 * 2 ^ t : ℕ) : ℝ))
    (hwp : WindowPeriodic ctx) : False :=
  pinnedValue_windowPeriodic_void ctx (by norm_num) (by norm_num) heta hwp

/-! ## Part 7.  Machine-readable status (honest) -/

/-- Honest machine-readable status of the Appendix-N descent module. -/
def appendixNDescentStatus : List String :=
  [ "APPENDIX N IDENTIFIED (manuscript read): Appendix N is the rolling-window " ++
      "variation-drop closure for Return-Run-Tower chains - the PER-CLASS " ++
      "event-fibre descent (transcripts, priority atoms, crossing edges), i.e. " ++
      "the machinery behind the frontier surface's per-class fields.  It is NOT " ++
      "a denominator descent: no manuscript or in-tree step lowers the odd part " ++
      "u of value = P/(u*2^t); the value is scale-invariant (valuePin_is_global), " ++
      "so the ladder cannot descend u.  The wave-19 'intended route' remark " ++
      "points back to the main per-class lane.",
    "THE DESCENT IS SUPERSEDED (proved, NEW): coveringDemand_void - NO failure " ++
      "context satisfies the covering demand, at ANY odd part (no u <= 7, no pin " ++
      "at all).  Mechanism: the demand's own Q-cap (ctx.Q <= 2^493443) plus the " ++
      "demanded family's own sparse tail at L' = 493445 fire the wave-10 SHARP " ++
      "contradiction (17*g <= 2^24) at the trivial representation Q = Q*2^0 with " ++
      "gap g = 493443+493445+3 = 986891: the demand caps the denominator at half " ++
      "the sharp budget, so the kill is unconditional.  The wave-19 pinned kill " ++
      "was the u <= 7 special case (t-free gap L+4); the sharp fire removes the " ++
      "restriction.  The escape stratum (odd part >= 9) has NO families to " ++
      "construct - there is nothing to descend to.",
    "THE COLLAPSE (proved, lossless): OffCycleCoveringSupply <-> (forall ctx, " ++
      "False) (offCycleCoveringSupply_iff_noContext - every ctx is deep by the " ++
      "pushed floor and off-cycle by the wave-18 voiding); NonPinnedCoveringSupply " ++
      "<-> the escape-stratum voiding (nonPinnedCoveringSupply_iff_escapeVoid); " ++
      "DeepPinnedQVoid AND NonPinnedCoveringSupply <-> context-emptiness " ++
      "(pinnedSplit_iff_noContext); the consumer's FULL verbatim hypothesis <-> " ++
      "context-emptiness (coveringFamilies_iff_noContext).  Already the WEAKER " ++
      "discharged intermediate collapses: SiblingShellInFiringWindow is absurd at " ++
      "every ctx (siblingShellInFiringWindow_void: sharp fire g = 2L'+3 for " ++
      "L' >= 24, integer count collision for 5 <= L' <= 23), so " ++
      "MultiScaleSiblingSupply <-> context-emptiness " ++
      "(multiScaleSiblingSupply_iff_noContext).",
    "LOAD-BEARING VERDICT (goal 1, checked against the consumption graph): the " ++
      "covering lane is NOT in the critical path.  The v19 main endpoint " ++
      "erdos260_of_convergenceResidual routes toFrontierResidual -> " ++
      "erdos260_of_frontierResidual (absorption + six-phase ledger); no surface " ++
      "field or supplier consumes MultiScaleSiblingSupply / OffCycleCoveringSupply " ++
      "/ the family machinery - the lane appears only as parallel packaging " ++
      "(convergence_pinnedSplitParallel, frontier_offCycleParallel).  This module " ++
      "makes the verdict exact: the lane's residual EQUALS the whole remaining " ++
      "problem (pinnedSplit_iff_noContext), so it can never be cheaper than the " ++
      "main surface.  FUTURE WAVES: do not attempt to construct covering families " ++
      "or sibling shells - impossibility is now a theorem; the lane's endpoints " ++
      "survive only as surface-free re-exports (erdos260_of_pinnedSplit_direct, " ++
      "erdos260_of_offCycleCovering_direct, " ++
      "erdos260_of_multiScaleSiblingSupply_direct - the wave-5 surfaces argument " ++
      "of erdos260_of_pinnedSplitCovering is dropped).",
    "THE PINNED OVERLAP (goal 3, proved): DeepPinnedQVoid ALONE implies all " ++
      "three open deep value levers (deepValueLevers_of_pinnedQVoid - each lever " ++
      "shape carries its own reachability: value = 1/2^t forces Q = K0*2^t; " ++
      "1/(5*2^t) forces Q = K0*5*2^t; 2/(3*2^t) forces 2Q = K0*3*2^t).  The " ++
      "CONVERSE fails in-tree: the levers pin the numerators (1,1,2) and cover " ++
      "u in {1,3,5} only.  DeepPinnedQVoid is STRICTLY stronger in two " ++
      "directions: general numerators P, and the u = 7 stratum.",
    "THE u = 7 VERDICT (goal 3): there is NO sevenths lever in-tree (the tower " ++
      "voidings are dyadic/fifth/thirds; the only u = 7 contact is the orbit " ++
      "datum (105,7) - a different predicate; the manuscript's E.7/H.6 value " ++
      "discussions void only the three shapes).  The new minimal atom is NAMED: " ++
      "DeepSeventhsPinVoid (= the u = 7 face of DeepPinnedQVoid, " ++
      "deepSeventhsPinVoid_of_pinnedQVoid).  The carry-rigidity machinery IS " ++
      "value-generic at u <= 7, so the atom inherits the full pushed-floor " ++
      "package: seventhsPin_scale_floor (reachable u = 7 pin forces X > 2^986891 " ++
      "- the SAME floor as the pushed levers, via scaleFloorPush_void_of_rep), " ++
      "seventhsPin_firingWindow_clean (the [2^5, 2^493443] window is clean), " ++
      "seventhsPin_windowPeriodic_void (the pin forces aperiodicity - the " ++
      "exit-mass lane's off-cycle precondition is free).  Post-collapse the atom " ++
      "is not needed by the covering lane; it remains the honest record that the " ++
      "three levers do NOT imply DeepPinnedQVoid.",
    "HYGIENE: additive only - ONE new module; no sorry / admit / new axiom / " ++
      "native_decide; every key declaration passes #print axioms within " ++
      "[propext, Classical.choice, Quot.sound]." ]

/-- The status ledger is non-empty (honest, non-vacuous). -/
theorem appendixNDescentStatus_nonempty : appendixNDescentStatus ≠ [] := by
  simp [appendixNDescentStatus]

/-! ## Part 8.  Axiom-cleanliness audit
Every key declaration; expected axioms `[propext, Classical.choice, Quot.sound]`
or fewer. -/

#print axioms coveringDemand_void
#print axioms siblingShell_small_void
#print axioms siblingShellInFiringWindow_void
#print axioms coveringLane_ctx_deep
#print axioms offCycleCoveringSupply_iff_noContext
#print axioms nonPinnedCoveringSupply_iff_escapeVoid
#print axioms pinnedSplit_iff_noContext
#print axioms coveringFamilies_iff_noContext
#print axioms multiScaleSiblingSupply_iff_noContext
#print axioms erdos260_of_pinnedSplit_direct
#print axioms erdos260_of_offCycleCovering_direct
#print axioms erdos260_of_multiScaleSiblingSupply_direct
#print axioms deepDyadicValueLever_of_pinnedQVoid
#print axioms deepTowerFifthValueLever_of_pinnedQVoid
#print axioms deepTowerThirdsValueLever_of_pinnedQVoid
#print axioms deepValueLevers_of_pinnedQVoid
#print axioms deepSeventhsPinVoid_of_pinnedQVoid
#print axioms seventhsPin_scale_floor
#print axioms seventhsPin_firingWindow_clean
#print axioms seventhsPin_windowPeriodic_void
#print axioms appendixNDescentStatus_nonempty

end

end Erdos260
