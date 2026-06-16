import Erdos260.CarryWordRigidity
import Erdos260.TargetBridge

/-!
# Multi-scale rigidity — the value pin transported across scales, and the exact quantifier gap

This module (NEW; it edits no existing file) executes the multi-scale angle on the wave-6
carry-word rigidity (`CarryWordRigidity.lean`): a pinned value `P/(u·2^t)` is a property of
the digit word `d` ALONE (the weighted tail sum reads no context field), so the rigidity
contradiction can be run at ANY scale where a failing (sparse) shell of the SAME word exists
— not only at the scale of the pinning context.

## The quantifier verdict (goal 1 — the crux, read from the actual Lean definitions)

The formalized failure structure has TWO layers with DIFFERENT quantifiers:

* **The obligation layer** (`Erdos260ClosureCertificate.perFailure`,
  `GlobalPerFailureAssembly.perFailureAssembly`, and the actual-shell interface
  `GlobalAssemblyActualInputs` over `ActualFailureContext`): the failure hypothesis is
  consumed ONE SHELL AT A TIME.  Each obligation receives a single `(Q, d, X)` with the
  sparsity bound `|supportShell d X| < c0·X` at THAT `X` only, universally quantified over
  all failing shells with `startThreshold ≤ X` (a LOWER bound only).  An
  `ActualFailureContext` carries `hfailure` at its own `X` and NOTHING about other scales:
  when voiding a family at one ctx, no second shell is available from the structure.

* **The bridge layer** (`TargetBridge.lean` / `TailGap.lean` — the genuine global
  counterexample): `theoremA_contradicts_nonirrational_erdos_sum` derives
  `DyadicShellSublinearReal (tailDigit a N)`: for EVERY `ε > 0`, the `2^L`-shell is
  `ε`-sparse for ALL sufficiently large `L` (`∀ᶠ L in atTop`).  So the single hypothetical
  counterexample word has failing shells at EVERY sufficiently large scale — a FULL TAIL,
  not merely a cofinal family.  Formalized here: `ShellsAtAllLargeScales` and
  `shellsAtAllLargeScales_of_sublinear` / `counterexample_shellsAtAllLargeScales`.

* **BUT the tail onset is uncontrolled**: the threshold `L₀` in `∀ᶠ` depends on the rate of
  `a n / n → ∞` and cannot be placed below any fixed bound, while the rigidity firing
  window `L' ∈ [5, 493443]` is FIXED (it comes from `c0 = 17/2^24`).  The full tail need
  not reach down into the window, so the quantifiers DO NOT cooperate and no unconditional
  voiding follows.  This is mathematically genuine, not a formalization artifact: a
  pinned-value word can have shell density `≈ 1/(L+4)` — exactly the carry-rigidity floor —
  which is sublinear, so "pin + full-tail sparsity with deep onset" is consistent.

## The transport (goal 2 — verified)

`realWeightedValue (natBinaryAsReal d)` mentions no context field, and `ctx.shell.d` is
definitionally `ctx.d` (`valuePin_is_global` is an `rfl`-transport).  Accordingly the
workhorse `multiScale_void_of_rep` is stated on the RAW word: a value pin `P/(u·2^t)` with
`u ≤ 7` plus ONE sparse shell at scale `2^L'` with `5 ≤ L' ≤ 493443` and `t ≤ 2^L'` is
absurd.  Consequences:

* `firingWindow_clean_of_rep` and the per-value forms `dyadicValue_firingWindow_clean`,
  `fifthValue_firingWindow_clean`, `thirdsValue_firingWindow_clean`: any pinned word has a
  CLEAN firing window — no failing shell anywhere in `[2^5, 2^493443]` (scale-independent).
* `onset_above_cap_of_rep`: a pinned word satisfying an all-large-scales sparsity tail is
  forced to have its onset ABOVE `493443` — the exact quantitative form of the obstruction.

## The conditional voidings (goal 4 — the quantifiers do not cooperate)

The precise named gap, per context: `SiblingShellInFiringWindow ctx` — one failing shell of
the SAME word at a scale `2^L'` with `5 ≤ L' ≤ 493443` and `ctx.Q ≤ 2^L'`.  Under it ALL
pinned-value families void at ctx (`shellValueDyadic_void_of_sibling`,
`towerFifthValue_void_of_sibling`, `towerThirdsValue_void_of_sibling`,
`fixedFamilyHit_void_of_sibling` + the five per-pair forms); `siblingShellInFiringWindow_self`
shows the gap subsumes the wave-6 shallow regime (every ctx with `X ≤ 2^493443` supplies its
OWN sibling).  The single supply Prop `MultiScaleSiblingSupply` (demanded only at deep ctx)
discharges all four deep wave-6 levers (`deep*_of_siblingSupply`), hence the FULL levers
(`dyadicValueLever_of_siblingSupply`, …), and reaches the endpoint through
`Erdos260MultiScaleResidual.toStatement` / `erdos260_of_multiScaleSiblingSupply`.

## The manuscript H.4/H.5 check (goal 4, honest)

H.4 ("Two-step truncated variable-block iteration", manuscript ~line 2725) iterates the
charged recurrence in the THRESHOLD variables `(s, Y)` inside ONE fixed shell `X`; H.5
("Positive dyadic density", ~line 2791) assumes the failure `A_S(2X) − A_S(X) < c_*X` at an
arbitrary sufficiently large dyadic `X` and derives the pressure lower bound at that SAME
`X`.  Neither step produces a second failing shell at a different (smaller) scale: the
manuscript does NOT supply `SiblingShellInFiringWindow` / `MultiScaleSiblingSupply`.  The
H.5 quantifier ("for an arbitrary sufficiently large dyadic X") is exactly the formalized
per-shell certificate shape; the piece of the H-chain that IS multi-scale — the bridge's
sublinearity of the genuine counterexample — is formalized here as
`counterexample_shellsAtAllLargeScales`, and the missing content is EXACTLY an onset bound
(`shellInFiringWindow_of_onset` / `siblingShellInFiringWindow_of_onset`).

No `sorry`, `admit`, new `axiom`, or `native_decide`.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 1.  The transport verification: the value pin is a property of the word alone -/

/-- **The transport verification (goal 2)**: the weighted value reads ONLY the digit word —
`ctx.shell.d` is definitionally `ctx.d` and `realWeightedValue (natBinaryAsReal d)` mentions
no other context field, so a value pin established at one context is a property of the pair
`(d, value)` alone and transports verbatim to every scale.  (Definitionally an
`rfl`-transport; recorded to pin the verification.) -/
theorem valuePin_is_global (ctx : ActualFailureContext) {v : ℝ}
    (h : realWeightedValue (natBinaryAsReal ctx.shell.d) = v) :
    realWeightedValue (natBinaryAsReal ctx.d) = v := h

/-! ## Part 2.  The scale predicates -/

/-- The word `d` is sparse (failing) at the dyadic scale `2^L`, against the pinned failure
constant `c0 = manuscriptC0 = 17/16777216`. -/
def ShellSparseAt (d : ℕ → ℕ) (L : ℕ) : Prop :=
  ((supportShell d (2 ^ L)).card : ℝ) < erdos260Constants.c0 * ((2 ^ L : ℕ) : ℝ)

/-- **The firing window** for a pin with 2-adic depth `t`: one sparse shell at a scale
`2^L'` with `5 ≤ L' ≤ 493443` and `t ≤ 2^L'`.  Inside this window the t-free carry-word
gap bound `g = L'+4` beats the sparsity bound (`17·(2L'+8) ≤ 2^24`). -/
def ShellInFiringWindow (d : ℕ → ℕ) (t : ℕ) : Prop :=
  ∃ L' : ℕ, 5 ≤ L' ∧ L' ≤ 493443 ∧ t ≤ 2 ^ L' ∧ ShellSparseAt d L'

/-- **What the global failure structure actually supplies** (bridge layer): sparse shells at
ALL sufficiently large scales — a full tail with UNCONTROLLED onset. -/
def ShellsAtAllLargeScales (d : ℕ → ℕ) : Prop :=
  ∃ L0 : ℕ, ∀ L : ℕ, L0 ≤ L → ShellSparseAt d L

/-! ## Part 3.  The multi-scale workhorse: pin + one shell in the firing window is absurd -/

/-- **THE MULTI-SCALE TRANSPORT WORKHORSE**: a value pin `P/(u·2^t)` with odd part `u ≤ 7`
plus ONE sparse shell of the SAME word at a scale `2^L'` inside the firing window
(`5 ≤ L' ≤ 493443`, `t ≤ 2^L'`) is absurd.  No context is involved: the pin is a property
of `(d, value)` alone, so this fires at ANY scale — the contradiction transports. -/
theorem multiScale_void_of_rep {u t : ℕ} {P : ℤ} {d : ℕ → ℕ}
    (hu7 : u ≤ 7) (hupos : 0 < u)
    (hd : BinaryDigits d) (hnonterm : ¬ EventuallyZero d)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / ((u * 2 ^ t : ℕ) : ℝ))
    {L' : ℕ} (h5 : 5 ≤ L') (hcap : L' ≤ 493443) (ht : t ≤ 2 ^ L')
    (hsparse : ShellSparseAt d L') : False := by
  have hsp : ((supportShell d (2 ^ L')).card : ℝ)
      < erdos260Constants.c0 * ((2 ^ L' : ℕ) : ℝ) := hsparse
  have h32 : 32 ≤ (2 : ℕ) ^ L' := by
    calc (32 : ℕ) = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ L' := Nat.pow_le_pow_right (by norm_num) h5
  have hp4 : (2 : ℕ) ^ (L' + 4) = 16 * 2 ^ L' := by rw [pow_add]; norm_num [mul_comm]
  have hwinN : u * (2 * 2 ^ L' + 2) < 2 ^ (L' + 4) := by
    calc u * (2 * 2 ^ L' + 2) ≤ 7 * (2 * 2 ^ L' + 2) := mul_le_mul_left hu7 _
      _ < 2 ^ (L' + 4) := by omega
  have hsq : L' * L' < 2 ^ L' := carryWord_sq_lt_two_pow h5
  have h5L : 5 * L' ≤ L' * L' := mul_le_mul_left h5 L'
  have hX2g : 2 * (L' + 4) ≤ 2 ^ L' := by omega
  refine supportShell_sparse_contradiction (Q := u * 2 ^ t) (u := u) (t := t)
    (P := P) (d := d) (X := 2 ^ L') (g := L' + 4)
    (c0 := erdos260Constants.c0)
    rfl (Nat.mul_pos hupos (Nat.two_pow_pos t)) hd hnonterm heta ht (by omega)
    (by exact_mod_cast hwinN) hX2g ?_ hsp
  have hgle : 2 * (L' + 4) ≤ 986894 := by omega
  rw [carryWord_c0_eq]
  have hcast : ((2 * (L' + 4) : ℕ) : ℝ) ≤ 986894 := by exact_mod_cast hgle
  linarith

/-- The workhorse against the packaged window predicate. -/
theorem multiScale_void_of_rep_window {u t : ℕ} {P : ℤ} {d : ℕ → ℕ}
    (hu7 : u ≤ 7) (hupos : 0 < u)
    (hd : BinaryDigits d) (hnonterm : ¬ EventuallyZero d)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / ((u * 2 ^ t : ℕ) : ℝ))
    (hwin : ShellInFiringWindow d t) : False := by
  obtain ⟨L', h5, hcap, ht, hsp⟩ := hwin
  exact multiScale_void_of_rep hu7 hupos hd hnonterm heta h5 hcap ht hsp

/-- **The firing window of a pinned word is CLEAN** (contrapositive of the workhorse): a
value pin `P/(u·2^t)`, `u ≤ 7` excludes failing shells at EVERY scale in `[2^5, 2^493443]`
(with `t ≤ 2^L'`) — a scale-independent global consequence of a single pin. -/
theorem firingWindow_clean_of_rep {u t : ℕ} {P : ℤ} {d : ℕ → ℕ}
    (hu7 : u ≤ 7) (hupos : 0 < u)
    (hd : BinaryDigits d) (hnonterm : ¬ EventuallyZero d)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / ((u * 2 ^ t : ℕ) : ℝ)) :
    ¬ ShellInFiringWindow d t :=
  fun hwin => multiScale_void_of_rep_window hu7 hupos hd hnonterm heta hwin

/-- The dyadic pin `value = 1/2^t` keeps the whole firing window clean (`u = 1`, `P = 1`). -/
theorem dyadicValue_firingWindow_clean {d : ℕ → ℕ}
    (hd : BinaryDigits d) (hnonterm : ¬ EventuallyZero d) {t : ℕ}
    (heta : realWeightedValue (natBinaryAsReal d) = 1 / 2 ^ t) :
    ¬ ShellInFiringWindow d t := by
  have heta' : realWeightedValue (natBinaryAsReal d)
      = ((1 : ℤ) : ℝ) / ((1 * 2 ^ t : ℕ) : ℝ) := by
    rw [heta]; push_cast; ring
  exact firingWindow_clean_of_rep (by norm_num) (by norm_num) hd hnonterm heta'

/-- The fifth pin `value = 1/(5·2^t)` keeps the whole firing window clean (`u = 5`). -/
theorem fifthValue_firingWindow_clean {d : ℕ → ℕ}
    (hd : BinaryDigits d) (hnonterm : ¬ EventuallyZero d) {t : ℕ}
    (heta : realWeightedValue (natBinaryAsReal d) = 1 / (5 * 2 ^ t)) :
    ¬ ShellInFiringWindow d t := by
  have heta' : realWeightedValue (natBinaryAsReal d)
      = ((1 : ℤ) : ℝ) / ((5 * 2 ^ t : ℕ) : ℝ) := by
    rw [heta]; push_cast; ring
  exact firingWindow_clean_of_rep (by norm_num) (by norm_num) hd hnonterm heta'

/-- The thirds pin `value = 2/(3·2^t)` keeps the whole firing window clean (`u = 3`,
`P = 2`). -/
theorem thirdsValue_firingWindow_clean {d : ℕ → ℕ}
    (hd : BinaryDigits d) (hnonterm : ¬ EventuallyZero d) {t : ℕ}
    (heta : realWeightedValue (natBinaryAsReal d) = 2 / (3 * 2 ^ t)) :
    ¬ ShellInFiringWindow d t := by
  have heta' : realWeightedValue (natBinaryAsReal d)
      = ((2 : ℤ) : ℝ) / ((3 * 2 ^ t : ℕ) : ℝ) := by
    rw [heta]; push_cast; ring
  exact firingWindow_clean_of_rep (by norm_num) (by norm_num) hd hnonterm heta'

/-! ## Part 4.  The quantifier structure, formalized: what the global failure supplies -/

/-- **The bridge supply** (the genuine quantifier of the global failure structure): the
sublinearity derived from `a n / n → ∞` yields sparse shells at ALL sufficiently large
scales — a full tail, instantiated at `ε = c0`. -/
theorem shellsAtAllLargeScales_of_sublinear {d : ℕ → ℕ}
    (hsub : DyadicShellSublinearReal d) : ShellsAtAllLargeScales d := by
  have h := hsub erdos260Constants.c0 erdos260Constants.c0_pos
  rw [Filter.eventually_atTop] at h
  obtain ⟨L0, hL0⟩ := h
  exact ⟨L0, fun L hL => hL0 L hL⟩

/-- **The genuine counterexample word has failing shells at EVERY sufficiently large scale**
— the actual multi-scale structure behind the global contradiction argument
(`TargetBridge.lean`): a full tail, NOT merely a cofinal family.  The onset, however, is
uncontrolled — it depends on the rate of `a n / n → ∞`. -/
theorem counterexample_shellsAtAllLargeScales {a : ℕ → ℤ} {N : ℕ}
    (ha : StrictMono a) (hpos : ∀ n : ℕ, N ≤ n → 0 < a n)
    (hratio :
      Filter.Tendsto (fun n : ℕ => (a n : ℝ) / (n : ℝ)) Filter.atTop Filter.atTop) :
    ShellsAtAllLargeScales (tailDigit a N) :=
  shellsAtAllLargeScales_of_sublinear
    (tailDigit_dyadicShellSublinearReal_of_ratio ha hpos hratio)

/-- **The missing content is exactly an onset bound**: an all-large-scales tail whose onset
lies at or below the cap `493443` (with `t` below the window scale) places a shell in the
firing window. -/
theorem shellInFiringWindow_of_onset {d : ℕ → ℕ} {L0 t : ℕ}
    (h : ∀ L : ℕ, L0 ≤ L → ShellSparseAt d L)
    (hcap : L0 ≤ 493443) (ht : t ≤ 2 ^ max L0 5) :
    ShellInFiringWindow d t :=
  ⟨max L0 5, le_max_right _ _, max_le hcap (by norm_num), ht, h _ (le_max_left _ _)⟩

/-- **The exact quantitative obstruction**: a pinned word satisfying an all-large-scales
sparsity tail is forced to have its onset ABOVE the cap `493443` — the pin pushes the
failure structure out of the firing window instead of being voided by it. -/
theorem onset_above_cap_of_rep {u t : ℕ} {P : ℤ} {d : ℕ → ℕ}
    (hu7 : u ≤ 7) (hupos : 0 < u)
    (hd : BinaryDigits d) (hnonterm : ¬ EventuallyZero d)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / ((u * 2 ^ t : ℕ) : ℝ))
    {L0 : ℕ} (h : ∀ L : ℕ, L0 ≤ L → ShellSparseAt d L)
    (ht : t ≤ 2 ^ max L0 5) : 493443 < L0 := by
  by_contra hcon
  push Not at hcon
  exact multiScale_void_of_rep_window hu7 hupos hd hnonterm heta
    (shellInFiringWindow_of_onset h hcon ht)

/-! ## Part 5.  The per-context sibling gap and the conditional voidings -/

/-- **THE PRECISE NAMED GAP, per context**: a sibling failing shell of the SAME word at a
scale `2^L'` inside the firing window, with the context denominator below the sibling scale
(`ctx.Q ≤ 2^L'` — this dominates every pin depth `t`, since all four pin families force
`2^t ≤ Q`).  The formalized failure structure does NOT supply this (each
`ActualFailureContext` carries sparsity at its own scale only); the manuscript H.4/H.5
iteration does not either (it iterates thresholds inside ONE shell). -/
def SiblingShellInFiringWindow (ctx : ActualFailureContext) : Prop :=
  ∃ L' : ℕ, 5 ≤ L' ∧ L' ≤ 493443 ∧ ctx.Q ≤ 2 ^ L' ∧ ShellSparseAt ctx.d L'

/-- **The gap subsumes the wave-6 shallow regime**: every context at scale `X = 2^L` with
`L ≤ 493443` supplies its OWN sibling (its own failing shell lies in the firing window, and
`Q < X` by the scale bound). -/
theorem siblingShellInFiringWindow_self (ctx : ActualFailureContext) {L : ℕ}
    (hL : ctx.X = 2 ^ L) (hcap : L ≤ 493443) :
    SiblingShellInFiringWindow ctx := by
  have hL28 : 28 ≤ L := carryWord_L_ge_28 ctx hL
  have hQX : ctx.Q < ctx.X := carryWord_Q_lt_X ctx
  rw [hL] at hQX
  refine ⟨L, by omega, hcap, by omega, ?_⟩
  show ((supportShell ctx.d (2 ^ L)).card : ℝ)
      < erdos260Constants.c0 * ((2 ^ L : ℕ) : ℝ)
  rw [← hL]
  exact ctx.hfailure

/-- The sibling gap from an onset-bounded all-large-scales tail for the context word. -/
theorem siblingShellInFiringWindow_of_onset (ctx : ActualFailureContext) {L0 : ℕ}
    (h : ∀ L : ℕ, L0 ≤ L → ShellSparseAt ctx.d L)
    (hcap : L0 ≤ 493443) (hQ : ctx.Q ≤ 2 ^ max L0 5) :
    SiblingShellInFiringWindow ctx :=
  ⟨max L0 5, le_max_right _ _, max_le hcap (by norm_num), hQ, h _ (le_max_left _ _)⟩

/-- **The dyadic-value voiding under the sibling gap**: a context with `value = 1/2^t` and a
sibling shell in the firing window is absurd — the pin transports (it is a property of
`ctx.d` alone) and the rigidity fires at the sibling scale. -/
theorem shellValueDyadic_void_of_sibling (ctx : ActualFailureContext)
    (hsib : SiblingShellInFiringWindow ctx) : ¬ ShellValueDyadic ctx := by
  rintro ⟨t, hdy⟩
  obtain ⟨L', h5, hcap, hQle, hsp⟩ := hsib
  have hvK := shell_value_eq_K₀_div_Q ctx
  have heq : (1 : ℝ) / 2 ^ t = ((class1SlopeDatum ctx).K₀ : ℝ) / (ctx.Q : ℝ) := by
    have h := hdy.symm.trans hvK
    simpa using h
  have hK1 : (1 : ℝ) ≤ ((class1SlopeDatum ctx).K₀ : ℝ) := by
    exact_mod_cast (class1SlopeDatum ctx).hK₀_pos
  have hQpos : (0 : ℝ) < (ctx.Q : ℝ) := by exact_mod_cast ctx.hQ
  have h2t : (0 : ℝ) < (2 : ℝ) ^ t := by positivity
  rw [div_eq_div_iff (by positivity) hQpos.ne'] at heq
  have hmul : (1 : ℝ) * 2 ^ t ≤ ((class1SlopeDatum ctx).K₀ : ℝ) * 2 ^ t :=
    mul_le_mul_of_nonneg_right hK1 h2t.le
  have hQge : (2 : ℝ) ^ t ≤ (ctx.Q : ℝ) := by linarith
  have hQgeN : 2 ^ t ≤ ctx.Q := by exact_mod_cast hQge
  have ht2L : t ≤ 2 ^ L' := by
    have hlt : t < 2 ^ t := Nat.lt_two_pow_self
    omega
  have heta' : realWeightedValue (natBinaryAsReal ctx.d)
      = ((1 : ℤ) : ℝ) / ((1 * 2 ^ t : ℕ) : ℝ) := by
    rw [show realWeightedValue (natBinaryAsReal ctx.d) = 1 / 2 ^ t from hdy]
    push_cast
    ring
  exact multiScale_void_of_rep (by norm_num) (by norm_num)
    ctx.hd ctx.hnonterm heta' h5 hcap ht2L hsp

/-- The flip: a dyadic-value pin at ctx keeps the ENTIRE firing window of `ctx.d` clean. -/
theorem shellValueDyadic_firingWindow_clean (ctx : ActualFailureContext)
    (h : ShellValueDyadic ctx) : ¬ SiblingShellInFiringWindow ctx :=
  fun hsib => shellValueDyadic_void_of_sibling ctx hsib h

/-- **The fifth-value voiding under the sibling gap** (`value = 1/(5·2^t)`, `u = 5`). -/
theorem towerFifthValue_void_of_sibling (ctx : ActualFailureContext)
    (hsib : SiblingShellInFiringWindow ctx) (t : ℕ) :
    realWeightedValue (natBinaryAsReal ctx.shell.d) ≠ 1 / (5 * 2 ^ t) := by
  intro hval
  obtain ⟨L', h5, hcap, hQle, hsp⟩ := hsib
  have hvK := shell_value_eq_K₀_div_Q ctx
  have heq : (1 : ℝ) / (5 * 2 ^ t)
      = ((class1SlopeDatum ctx).K₀ : ℝ) / (ctx.Q : ℝ) := by
    have h := hval.symm.trans hvK
    simpa using h
  have hK1 : (1 : ℝ) ≤ ((class1SlopeDatum ctx).K₀ : ℝ) := by
    exact_mod_cast (class1SlopeDatum ctx).hK₀_pos
  have hQpos : (0 : ℝ) < (ctx.Q : ℝ) := by exact_mod_cast ctx.hQ
  have h2t : (0 : ℝ) < (2 : ℝ) ^ t := by positivity
  rw [div_eq_div_iff (by positivity) hQpos.ne'] at heq
  have hmul : (1 : ℝ) * (5 * 2 ^ t)
      ≤ ((class1SlopeDatum ctx).K₀ : ℝ) * (5 * 2 ^ t) :=
    mul_le_mul_of_nonneg_right hK1 (by positivity)
  have hQge : (2 : ℝ) ^ t ≤ (ctx.Q : ℝ) := by linarith
  have hQgeN : 2 ^ t ≤ ctx.Q := by exact_mod_cast hQge
  have ht2L : t ≤ 2 ^ L' := by
    have hlt : t < 2 ^ t := Nat.lt_two_pow_self
    omega
  have heta' : realWeightedValue (natBinaryAsReal ctx.d)
      = ((1 : ℤ) : ℝ) / ((5 * 2 ^ t : ℕ) : ℝ) := by
    rw [show realWeightedValue (natBinaryAsReal ctx.d) = 1 / (5 * 2 ^ t) from hval]
    push_cast
    ring
  exact multiScale_void_of_rep (by norm_num) (by norm_num)
    ctx.hd ctx.hnonterm heta' h5 hcap ht2L hsp

/-- **The thirds-value voiding under the sibling gap** (`value = 2/(3·2^t)`, `u = 3`). -/
theorem towerThirdsValue_void_of_sibling (ctx : ActualFailureContext)
    (hsib : SiblingShellInFiringWindow ctx) (t : ℕ) :
    realWeightedValue (natBinaryAsReal ctx.shell.d) ≠ 2 / (3 * 2 ^ t) := by
  intro hval
  obtain ⟨L', h5, hcap, hQle, hsp⟩ := hsib
  have hvK := shell_value_eq_K₀_div_Q ctx
  have heq : (2 : ℝ) / (3 * 2 ^ t)
      = ((class1SlopeDatum ctx).K₀ : ℝ) / (ctx.Q : ℝ) := by
    have h := hval.symm.trans hvK
    simpa using h
  have hK1 : (1 : ℝ) ≤ ((class1SlopeDatum ctx).K₀ : ℝ) := by
    exact_mod_cast (class1SlopeDatum ctx).hK₀_pos
  have hQpos : (0 : ℝ) < (ctx.Q : ℝ) := by exact_mod_cast ctx.hQ
  have h2t : (0 : ℝ) < (2 : ℝ) ^ t := by positivity
  rw [div_eq_div_iff (by positivity) hQpos.ne'] at heq
  have hmul : (1 : ℝ) * (3 * 2 ^ t)
      ≤ ((class1SlopeDatum ctx).K₀ : ℝ) * (3 * 2 ^ t) :=
    mul_le_mul_of_nonneg_right hK1 (by positivity)
  have hQge : (2 : ℝ) ^ t ≤ (ctx.Q : ℝ) := by linarith
  have hQgeN : 2 ^ t ≤ ctx.Q := by exact_mod_cast hQge
  have ht2L : t ≤ 2 ^ L' := by
    have hlt : t < 2 ^ t := Nat.lt_two_pow_self
    omega
  have heta' : realWeightedValue (natBinaryAsReal ctx.d)
      = ((2 : ℤ) : ℝ) / ((3 * 2 ^ t : ℕ) : ℝ) := by
    rw [show realWeightedValue (natBinaryAsReal ctx.d) = 2 / (3 * 2 ^ t) from hval]
    push_cast
    ring
  exact multiScale_void_of_rep (by norm_num) (by norm_num)
    ctx.hd ctx.hnonterm heta' h5 hcap ht2L hsp

/-- **All five fixed families void under the sibling gap**: a fixed-family hit pins
`oddpart(Q) ∈ {1,3,5,7}` and the value `P/(oddpart(Q)·2^{ν₂(Q)})` — the pin transports to
the sibling scale and the rigidity fires there. -/
theorem fixedFamilyHit_void_of_sibling (ctx : ActualFailureContext)
    (hsib : SiblingShellInFiringWindow ctx) : ¬ FixedFamilyHit ctx := by
  intro hhit
  obtain ⟨L', h5, hcap, hQle, hsp⟩ := hsib
  have hmem := fixedFamilyHit_oddpartQ_mem ctx hhit
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hu7 : ordCompl[2] ctx.Q ≤ 7 := by
    have hmem' : ordCompl[2] ctx.Q = 1 ∨ ordCompl[2] ctx.Q = 3
        ∨ ordCompl[2] ctx.Q = 5 ∨ ordCompl[2] ctx.Q = 7 := by simpa using hmem
    omega
  have hupos : 0 < ordCompl[2] ctx.Q := Nat.ordCompl_pos 2 ctx.hQ.ne'
  have hQfact : ctx.Q = ordCompl[2] ctx.Q * 2 ^ ctx.Q.factorization 2 := by
    have h := shell_Q_eq_oddpart_mul_pow ctx
    simpa using h
  obtain ⟨P, hP⟩ := ctx.hrational
  have heta' : realWeightedValue (natBinaryAsReal ctx.d)
      = (P : ℝ) / ((ordCompl[2] ctx.Q * 2 ^ ctx.Q.factorization 2 : ℕ) : ℝ) := by
    rw [← hQfact]
    exact hP
  have ht2L : ctx.Q.factorization 2 ≤ 2 ^ L' := by
    have h2t : 2 ^ ctx.Q.factorization 2 ≤ ctx.Q := Nat.ordProj_le 2 ctx.hQ.ne'
    have hlt : ctx.Q.factorization 2 < 2 ^ ctx.Q.factorization 2 := Nat.lt_two_pow_self
    omega
  exact multiScale_void_of_rep hu7 hupos ctx.hd ctx.hnonterm heta' h5 hcap ht2L hsp

/-- Band-2 `(3,1)` void under the sibling gap. -/
theorem returnFixedFamily_void_of_sibling (ctx : ActualFailureContext)
    (hsib : SiblingShellInFiringWindow ctx) :
    ¬((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1) :=
  fun hh => fixedFamilyHit_void_of_sibling ctx hsib (Or.inl hh)

/-- Band-3 `(21,3)` void under the sibling gap. -/
theorem densePackFixedFamily_void_of_sibling (ctx : ActualFailureContext)
    (hsib : SiblingShellInFiringWindow ctx) :
    ¬((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3) :=
  fun hh => fixedFamilyHit_void_of_sibling ctx hsib (Or.inr (Or.inl hh))

/-- Band-4 `(15,1)` void under the sibling gap. -/
theorem towerFP15_1Family_void_of_sibling (ctx : ActualFailureContext)
    (hsib : SiblingShellInFiringWindow ctx) :
    ¬((class1SlopeDatum ctx).q = 15 ∧ (class1SlopeDatum ctx).K₀ = 1) :=
  fun hh => fixedFamilyHit_void_of_sibling ctx hsib (Or.inr (Or.inr (Or.inl hh)))

/-- Band-4 `(15,2)` void under the sibling gap. -/
theorem towerFP15_2Family_void_of_sibling (ctx : ActualFailureContext)
    (hsib : SiblingShellInFiringWindow ctx) :
    ¬((class1SlopeDatum ctx).q = 15 ∧ (class1SlopeDatum ctx).K₀ = 2) :=
  fun hh =>
    fixedFamilyHit_void_of_sibling ctx hsib (Or.inr (Or.inr (Or.inr (Or.inl hh))))

/-- Band-4 `(105,7)` void under the sibling gap. -/
theorem towerFP105Family_void_of_sibling (ctx : ActualFailureContext)
    (hsib : SiblingShellInFiringWindow ctx) :
    ¬((class1SlopeDatum ctx).q = 105 ∧ (class1SlopeDatum ctx).K₀ = 7) :=
  fun hh =>
    fixedFamilyHit_void_of_sibling ctx hsib (Or.inr (Or.inr (Or.inr (Or.inr hh))))

/-! ## Part 6.  The supply Prop, the lever dischargers, and the endpoint wiring -/

/-- **THE SINGLE SUPPLY PROP**: every DEEP failing context (`X > 2^493443` — the shallow
ones supply their own sibling by `siblingShellInFiringWindow_self`) has a sibling failing
shell of the same word inside the firing window.  This is the one multi-scale fact that
would void ALL pinned-value families outright; the formalized failure structure supplies
sparse shells at all sufficiently large scales but with UNCONTROLLED onset, so this Prop is
genuinely open. -/
def MultiScaleSiblingSupply : Prop :=
  ∀ ctx : ActualFailureContext, 2 ^ 493443 < ctx.X → SiblingShellInFiringWindow ctx

/-- The supply discharges the wave-6 deep dyadic lever. -/
theorem deepDyadicValueLever_of_siblingSupply (h : MultiScaleSiblingSupply) :
    DeepDyadicValueLever :=
  fun ctx hX => shellValueDyadic_void_of_sibling ctx (h ctx hX)

/-- The supply discharges the wave-6 deep fifth lever. -/
theorem deepTowerFifthValueLever_of_siblingSupply (h : MultiScaleSiblingSupply) :
    DeepTowerFifthValueLever :=
  fun ctx hX t => towerFifthValue_void_of_sibling ctx (h ctx hX) t

/-- The supply discharges the wave-6 deep thirds lever. -/
theorem deepTowerThirdsValueLever_of_siblingSupply (h : MultiScaleSiblingSupply) :
    DeepTowerThirdsValueLever :=
  fun ctx hX t => towerThirdsValue_void_of_sibling ctx (h ctx hX) t

/-- The supply discharges the wave-6 deep family voiding (all five fixed pairs). -/
theorem deepFixedFamilyVoid_of_siblingSupply (h : MultiScaleSiblingSupply) :
    DeepFixedFamilyVoid :=
  fun ctx hX => fixedFamilyHit_void_of_sibling ctx (h ctx hX)

/-- **The FULL dyadic-value lever from the supply** (shallow half closed by wave 6). -/
theorem dyadicValueLever_of_siblingSupply (h : MultiScaleSiblingSupply) :
    DyadicValueLever :=
  dyadicValueLever_of_deepScale (deepDyadicValueLever_of_siblingSupply h)

/-- The full fifth lever from the supply. -/
theorem towerFifthValueLever_of_siblingSupply (h : MultiScaleSiblingSupply) :
    TowerFifthValueLever :=
  towerFifthValueLever_of_deepScale (deepTowerFifthValueLever_of_siblingSupply h)

/-- The full thirds lever from the supply. -/
theorem towerThirdsValueLever_of_siblingSupply (h : MultiScaleSiblingSupply) :
    TowerThirdsValueLever :=
  towerThirdsValueLever_of_deepScale (deepTowerThirdsValueLever_of_siblingSupply h)

/-- The full family voiding on EVERY context from the supply. -/
theorem fixedFamilyHit_void_of_siblingSupply (h : MultiScaleSiblingSupply)
    (ctx : ActualFailureContext) : ¬ FixedFamilyHit ctx :=
  fixedFamilyHit_void_of_deepScale (deepFixedFamilyVoid_of_siblingSupply h) ctx

/-- The tower escape shrinks under the supply (through the discharged lever). -/
theorem towerEscapeLever_of_towerEscape_siblingSupply (h : MultiScaleSiblingSupply)
    (ctx : ActualFailureContext) (hesc : TowerEscape ctx) : TowerEscapeLever ctx :=
  towerEscapeLever_of_towerEscape (dyadicValueLever_of_siblingSupply h) ctx hesc

/-- The tower field bridge under the supply: the lever residual rebuilds the full wave-4
`TowerFixedPointResidual`. -/
theorem towerFixedPointResidual_of_siblingSupply (h : MultiScaleSiblingSupply)
    (hres : TowerLeverResidual) : TowerFixedPointResidual :=
  towerFixedPointResidual_of_lever (dyadicValueLever_of_siblingSupply h) hres

/-- **The multi-scale conditional endpoint residual**: the sibling supply (demanded only at
deep contexts) plus the lever-shrunk wave-5 surfaces as a function of the discharged
lever. -/
structure Erdos260MultiScaleResidual where
  /-- The multi-scale sibling supply (the only content not closed by this module). -/
  supply : MultiScaleSiblingSupply
  /-- The remaining wave-5 surfaces, given the discharged lever. -/
  surfaces : DyadicValueLever → Erdos260DyadicLeverResidual

namespace Erdos260MultiScaleResidual

/-- Discharge the supply into the wave-6 deep-lever residual. -/
def toDeepLeverResidual (R : Erdos260MultiScaleResidual) : Erdos260DeepLeverResidual where
  deepLever := deepDyadicValueLever_of_siblingSupply R.supply
  surfaces := R.surfaces

/-- The final statement from the multi-scale residual, through the wave-6/wave-5/wave-4
capstones. -/
theorem toStatement (R : Erdos260MultiScaleResidual) : Erdos260Statement :=
  R.toDeepLeverResidual.toStatement

end Erdos260MultiScaleResidual

/-- **The multi-scale conditional endpoint**: `Erdos260Statement` from the sibling supply
plus the lever-shrunk surfaces. -/
theorem erdos260_of_multiScaleSiblingSupply (R : Erdos260MultiScaleResidual) :
    Erdos260Statement :=
  R.toStatement

/-! ## Part 7.  Machine-readable status (honest) -/

/-- Honest machine-readable status of the multi-scale rigidity module. -/
def multiScaleRigidityStatus : List String :=
  [ "THE QUANTIFIER VERDICT (goal 1, the crux; read from the actual Lean definitions): " ++
      "the formalized failure structure has TWO layers.  Obligation layer " ++
      "(Erdos260ClosureCertificate.perFailure, GlobalPerFailureAssembly, " ++
      "GlobalAssemblyActualInputs over ActualFailureContext): failure is consumed ONE " ++
      "SHELL AT A TIME - each obligation receives a single (Q, d, X) with sparsity at " ++
      "THAT X only, quantified over all failing shells with startThreshold <= X (a " ++
      "LOWER bound only); an ActualFailureContext carries hfailure at its own scale and " ++
      "NOTHING about other scales.  Bridge layer (TargetBridge/TailGap, the genuine " ++
      "counterexample): theoremA_contradicts_nonirrational_erdos_sum derives " ++
      "DyadicShellSublinearReal (tailDigit a N) - for EVERY eps > 0 the 2^L-shell is " ++
      "eps-sparse for ALL sufficiently large L (a FULL TAIL at every large scale, not " ++
      "merely cofinal), BUT with UNCONTROLLED onset (it depends on the rate of " ++
      "a n / n -> infinity).",
    "THE VERDICT, CONCLUDED: the rigidity firing window L' in [5, 493443] is FIXED " ++
      "(from c0 = 17/2^24) while the sparsity tail onset is uncontrolled, so the " ++
      "quantifiers DO NOT cooperate and no unconditional voiding follows.  This is " ++
      "mathematically genuine, not a formalization artifact: a pinned-value word can " ++
      "have shell density ~ 1/(L+4) - exactly the carry-rigidity floor - which is " ++
      "sublinear, so pin + full-tail sparsity with deep onset is consistent.",
    "THE TRANSPORT (goal 2, verified): realWeightedValue (natBinaryAsReal d) mentions " ++
      "no context field and ctx.shell.d = ctx.d definitionally (valuePin_is_global is " ++
      "an rfl-transport), so a value pin at one ctx is a property of (d, value) alone.  " ++
      "The workhorse multiScale_void_of_rep is stated on the RAW word: pin P/(u*2^t) " ++
      "with u <= 7 plus ONE sparse shell at 2^L' with 5 <= L' <= 493443, t <= 2^L' is " ++
      "absurd (window form multiScale_void_of_rep_window).",
    "THE CLEAN-WINDOW CONSEQUENCES (unconditional, scale-independent): any pinned word " ++
      "keeps the ENTIRE firing window clean - firingWindow_clean_of_rep, with per-value " ++
      "forms dyadicValue_firingWindow_clean (u=1), fifthValue_firingWindow_clean (u=5), " ++
      "thirdsValue_firingWindow_clean (u=3); onset form onset_above_cap_of_rep: a " ++
      "pinned word with an all-large-scales sparsity tail has onset FORCED above " ++
      "493443.",
    "THE SUPPLY SIDE (formalized): shellsAtAllLargeScales_of_sublinear extracts " ++
      "ShellsAtAllLargeScales from DyadicShellSublinearReal at eps = c0; " ++
      "counterexample_shellsAtAllLargeScales instantiates it for the genuine " ++
      "counterexample word tailDigit a N - failing shells at EVERY sufficiently large " ++
      "scale.  The missing content is EXACTLY an onset bound: " ++
      "shellInFiringWindow_of_onset / siblingShellInFiringWindow_of_onset place a " ++
      "shell in the window from onset <= 493443.",
    "THE PER-CTX CONDITIONAL VOIDINGS (goal 4; the quantifiers do not cooperate, so " ++
      "conditional): under SiblingShellInFiringWindow ctx (one failing shell of the " ++
      "SAME word at 2^L', 5 <= L' <= 493443, ctx.Q <= 2^L') ALL pinned-value families " ++
      "void at ctx: shellValueDyadic_void_of_sibling (+ flip " ++
      "shellValueDyadic_firingWindow_clean), towerFifthValue_void_of_sibling, " ++
      "towerThirdsValue_void_of_sibling, fixedFamilyHit_void_of_sibling + five " ++
      "per-pair forms (returnFixedFamily/densePackFixedFamily/towerFP15_1Family/" ++
      "towerFP15_2Family/towerFP105Family_void_of_sibling).  " ++
      "siblingShellInFiringWindow_self: the gap subsumes the wave-6 shallow regime " ++
      "(every ctx with X <= 2^493443 supplies its own sibling).",
    "THE SUPPLY PROP AND THE WIRING (additive): MultiScaleSiblingSupply (demanded only " ++
      "at deep ctx, X > 2^493443) discharges all four wave-6 deep levers " ++
      "(deepDyadicValueLever/deepTowerFifthValueLever/deepTowerThirdsValueLever/" ++
      "deepFixedFamilyVoid_of_siblingSupply), hence the FULL levers " ++
      "(dyadicValueLever/towerFifthValueLever/towerThirdsValueLever_of_siblingSupply, " ++
      "fixedFamilyHit_void_of_siblingSupply), the tower wiring " ++
      "(towerEscapeLever_of_towerEscape_siblingSupply, " ++
      "towerFixedPointResidual_of_siblingSupply), and the endpoint " ++
      "erdos260_of_multiScaleSiblingSupply : Erdos260MultiScaleResidual -> " ++
      "Erdos260Statement.",
    "THE MANUSCRIPT H.4/H.5 CHECK (goal 4, honest): H.4 (two-step truncated " ++
      "variable-block iteration, ~line 2725) iterates the charged recurrence in the " ++
      "THRESHOLD variables (s, Y) inside ONE fixed shell X; H.5 (positive dyadic " ++
      "density, ~line 2791) assumes failure at an arbitrary sufficiently large dyadic " ++
      "X and derives the pressure bound at that SAME X.  Neither produces a second " ++
      "failing shell at a different (smaller) scale: the manuscript does NOT supply " ++
      "SiblingShellInFiringWindow / MultiScaleSiblingSupply.  The H.5 quantifier is " ++
      "exactly the formalized per-shell certificate shape; the multi-scale piece of " ++
      "the chain - the bridge sublinearity - is formalized here " ++
      "(counterexample_shellsAtAllLargeScales).",
    "WHAT WOULD CLOSE EVERYTHING (the exact target for future waves): any proof that " ++
      "the failure structure places ONE failing shell of the counterexample word in " ++
      "the fixed window [2^5, 2^493443] (Q-compatibly) voids ALL pinned-value families " ++
      "outright - equivalently, an onset bound <= 493443 for the sparsity tail.  " ++
      "Conversely onset_above_cap_of_rep shows every pinned word pushes the onset " ++
      "above the cap, so the pin and the failure structure can only coexist in the " ++
      "deep tail.  Nothing re-proved, no existing file edited; no ctx claimed empty." ]

theorem multiScaleRigidityStatus_nonempty : multiScaleRigidityStatus ≠ [] := by
  simp [multiScaleRigidityStatus]

/-! ## Part 8.  Axiom-cleanliness audit -/

#print axioms valuePin_is_global
#print axioms multiScale_void_of_rep
#print axioms multiScale_void_of_rep_window
#print axioms firingWindow_clean_of_rep
#print axioms dyadicValue_firingWindow_clean
#print axioms fifthValue_firingWindow_clean
#print axioms thirdsValue_firingWindow_clean
#print axioms shellsAtAllLargeScales_of_sublinear
#print axioms counterexample_shellsAtAllLargeScales
#print axioms shellInFiringWindow_of_onset
#print axioms onset_above_cap_of_rep
#print axioms siblingShellInFiringWindow_self
#print axioms siblingShellInFiringWindow_of_onset
#print axioms shellValueDyadic_void_of_sibling
#print axioms shellValueDyadic_firingWindow_clean
#print axioms towerFifthValue_void_of_sibling
#print axioms towerThirdsValue_void_of_sibling
#print axioms fixedFamilyHit_void_of_sibling
#print axioms returnFixedFamily_void_of_sibling
#print axioms densePackFixedFamily_void_of_sibling
#print axioms towerFP15_1Family_void_of_sibling
#print axioms towerFP15_2Family_void_of_sibling
#print axioms towerFP105Family_void_of_sibling
#print axioms deepDyadicValueLever_of_siblingSupply
#print axioms deepTowerFifthValueLever_of_siblingSupply
#print axioms deepTowerThirdsValueLever_of_siblingSupply
#print axioms deepFixedFamilyVoid_of_siblingSupply
#print axioms dyadicValueLever_of_siblingSupply
#print axioms towerFifthValueLever_of_siblingSupply
#print axioms towerThirdsValueLever_of_siblingSupply
#print axioms fixedFamilyHit_void_of_siblingSupply
#print axioms towerEscapeLever_of_towerEscape_siblingSupply
#print axioms towerFixedPointResidual_of_siblingSupply
#print axioms Erdos260MultiScaleResidual.toDeepLeverResidual
#print axioms Erdos260MultiScaleResidual.toStatement
#print axioms erdos260_of_multiScaleSiblingSupply
#print axioms multiScaleRigidityStatus_nonempty

end

end Erdos260
