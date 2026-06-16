import Erdos260.Erdos260EnumCapstone

/-!
# Erdős 260 — the digit-side closure: type-level settlement of the Return digit demands,
# the index-window separation surface, and the vacuous `r = 0` top-start closure

This module (NEW; it edits no existing file) settles the brief's KEY type-level question
about the wave-5 digit-side leftovers and converts the answer into a strictly smaller
successor residual `DigitSideEnumResidual` with the endpoint
`erdos260_of_digitSideResidual : DigitSideEnumResidual → Erdos260Statement`.

## 1.  The type-level finding (the brief's goal 2, SETTLED)

The class-4 fibre `olcFibre ctx` lives in **hit-index space**: its members `k` are members
of `starts = Ico F (F + W)` (`cnlMulti_starts_eq_window`, `olcFibre_mem_window`), where
`F = firstIndexAbove X` is the index of the first support hit above `X` and
`W = |supportShell d X|`.  The digit fields evaluate `ctx.d` at **raw positions equal to
index values**:

* `returnMaxClean` demands `ctx.d (k + 1) = 0` — `k + 1` is the NUMBER `k + 1 ∈ (F, F + W]`,
  NOT the next hit position `a (k + 1)`.  The hit position of the fibre member sits in the
  shell `X < a k ≤ 2X` (`olcFibre_hitPosition_in_shell`); the demanded digit position
  `k + 1 ≤ F + W` is far below it whenever the sub-`X` support is not nearly full.
* `returnZero` demands `ctx.d j = 0` for raw `j ∈ (x, z] ⊆ (F, F + W]` with `x, z`
  same-slice fibre members.

So the demanded positions live in the raw interval `(F, F + W]`.  Since
`F ≤ supportCount d X + 1` (`digitSide_firstIndexAbove_le`), they are sub-`X` positions
(`k + 1 ≤ X`) unless the sub-`X` support is dense: `X ≤ supportCount d X + W`
(`digitSide_subX_dense_of_overflow`, `olcFibre_demand_dichotomy`).  In the sub-`X` regime the
digit value is EXACTLY pre-window support membership: `d(k+1) = 1` iff some hit of index
`j < F` lands at the position `k + 1` (`digitSide_subX_demand_iff`,
`digitSide_hit_index_lt_first`).

## 2.  The digit-support dictionary (the brief's goal 1, MINED)

The hit enumeration is COMPLETE: `d n = 1 ⟺ n ∈ range a` (`digitSide_eq_one_iff`,
`digitSide_eq_zero_iff`, bounded form `digitSide_eq_zero_iff_bounded` via `j ≤ a j`).  Hence
`d k = 1` exactly at hit positions, zero-runs between consecutive hits are AUTOMATIC
(`digitSide_zero_between_hits`), and the hit-gap structure is the only freedom — confirming
the brief's conjecture.  The demands therefore transform into pure HIT-AVOIDANCE statements:
`ReturnMaxCleanBody ⟺` no hit lands at any slice-max successor position
(`returnMaxCleanBody_iff_hitMiss`), `ReturnZeroBody ⟺` no hit lands in any same-slice gap
(`returnZeroBody_iff_hitMiss`).

## 3.  The new closure surface (the brief's goal 4)

`ReturnIndexWindowClean ctx` — the support avoids the raw index window `(F, F + W]`
(equivalently no hit position lands there, `returnIndexWindowClean_iff_hits_avoid`).  This
SINGLE digit-window fact closes BOTH remaining digit fields at once:
`returnZeroBody_of_indexWindowClean`, `returnCleanStep_of_indexWindowClean` (the FULL clean
step, stronger than the maxima reduction), `returnMaxCleanBody_of_indexWindowClean`.  The
successor residual demands `returnZero` / `returnMaxClean` only on `¬ ReturnIndexWindowClean`
contexts — i.e. only when the digit support genuinely meets the small window `(F, F + W]`.

## 4.  The `r = 0` top-start facts (the brief's goal 5, CLOSED + sharpened)

* The class-1 pair-residual `topStart` field is conditioned on `ctx.n24CarryData.r = 0`,
  and `n24_r_pos` proves `1 ≤ r` at EVERY actual failure context — so the whole field is a
  THEOREM (`class1PairTopStart_settled`) and `Class1PairResidual` collapses to its `deep`
  field alone (`class1PairResidual_of_deepOnly`).  The class-0 analogue was already packaged
  upstream (`class0WindowCycleCheck_of_r_eq_zero`).
* The hit-gap disequality `64·hitGap ≠ 129L + 64` itself: it holds AUTOMATICALLY at every
  index `j` with `j + 1 < F + W` — the in-window dyadic ceiling `hitGap ≤ L + B + 1` plus the
  proved `B + 25 ≤ L` keep `64·hitGap ≤ 128L − 1536 < 129L + 64`
  (`digitSide_interior_hitGap_diseq`).  Off `64 ∣ L` it is automatic at EVERY index by pure
  arithmetic (`digitSide_hitGap_diseq_of_not_dvd`).  The ONLY index where it can fail is the
  top start `F + W − 1`, whose gap straddles the upper shell boundary `2X`
  (`digitSide_topGap_straddle`) and is genuinely unpinned — honest residual content, now
  vacuous anyway through `n24_r_pos`.

## Honest summary

No unconditional closure of `returnZero` / `returnMaxClean` is claimed: the digit values on
`(F, F + W]` are genuinely free (the orbit pins constrain hit GAPS at indices `≥ k` and the
orbit at `k`, never the raw positions `≤ F + W`).  What IS new: the demands are now
hit-avoidance facts about ONE explicit small window, the sub-`X`/dense dichotomy localizes
them below `X` or forces near-full sub-`X` density, the class-1 `r = 0` field is closed
outright, and the hit-gap disequality is proved everywhere except the single boundary gap.

No `sorry`, `admit`, new `axiom`, or `native_decide`.
-/

namespace Erdos260

noncomputable section

/-! ## Part 0.  The raw-vs-shell digit agreement -/

/-- The shell projection keeps the raw digit word: `ctx.shell.d = ctx.d` (definitional). -/
theorem digitSide_shell_d_eq (ctx : ActualFailureContext) : ctx.shell.d = ctx.d := rfl

/-- Every enumerated hit position carries digit `1` (the raw-word form of
`hits.hit`). -/
theorem digitSide_hit (ctx : ActualFailureContext) (j : ℕ) :
    ctx.d (ctx.n24CarryData.a j) = 1 :=
  ctx.n24CarryData.carry.hits.hit j

/-! ## Part 1.  The digit-support dictionary: `d = 1` exactly at hit positions

The carry datum's `hits : HitSequence ctx.shell.d a` is strictly monotone, hits everywhere,
and COMPLETE — so the raw digit word is fully determined by the hit position set, and the
zero-runs between consecutive hits are automatic.  These are the mined goal-1 facts. -/

/-- **The positive dictionary**: `d n = 1` iff `n` is a hit position. -/
theorem digitSide_eq_one_iff (ctx : ActualFailureContext) (n : ℕ) :
    ctx.d n = 1 ↔ ∃ j, ctx.n24CarryData.a j = n := by
  constructor
  · intro h
    exact ctx.n24CarryData.carry.hits.complete n h
  · rintro ⟨j, hj⟩
    rw [← hj]
    exact digitSide_hit ctx j

/-- **The negative dictionary**: `d n = 0` iff NO hit lands at the position `n`. -/
theorem digitSide_eq_zero_iff (ctx : ActualFailureContext) (n : ℕ) :
    ctx.d n = 0 ↔ ∀ j, ctx.n24CarryData.a j ≠ n := by
  constructor
  · intro h j hj
    have hhit : ctx.shell.d (ctx.n24CarryData.a j) = 1 := ctx.n24CarryData.carry.hits.hit j
    rw [hj, digitSide_shell_d_eq] at hhit
    omega
  · intro h
    rcases ctx.hd n with h0 | h1
    · exact h0
    · obtain ⟨j, hj⟩ := ctx.n24CarryData.carry.hits.complete n h1
      exact absurd hj (h j)

/-- The hit enumeration dominates its index: `j ≤ a j` (strict monotonicity on `ℕ`). -/
theorem digitSide_index_le_a (ctx : ActualFailureContext) (j : ℕ) :
    j ≤ ctx.n24CarryData.a j := by
  induction j with
  | zero => exact Nat.zero_le _
  | succ j ih =>
      have h : ctx.n24CarryData.a j < ctx.n24CarryData.a (j + 1) :=
        ctx.n24CarryData.carry.hits.strict (Nat.lt_succ_self j)
      show j + 1 ≤ ctx.n24CarryData.a (j + 1)
      omega

/-- **The bounded negative dictionary**: only indices `j ≤ n` can hit the position `n`, so
`d n = 0` is a FINITE check. -/
theorem digitSide_eq_zero_iff_bounded (ctx : ActualFailureContext) (n : ℕ) :
    ctx.d n = 0 ↔ ∀ j, j ≤ n → ctx.n24CarryData.a j ≠ n := by
  rw [digitSide_eq_zero_iff]
  constructor
  · intro h j _
    exact h j
  · intro h j hj
    by_cases hle : j ≤ n
    · exact h j hle hj
    · have := digitSide_index_le_a ctx j
      omega

/-- **Zero-runs between consecutive hits are AUTOMATIC** (the goal-1 settlement): every raw
position strictly between `a j` and `a (j+1)` carries digit `0` — the hit-gap structure is
the only digit freedom. -/
theorem digitSide_zero_between_hits (ctx : ActualFailureContext) {j i : ℕ}
    (h1 : ctx.n24CarryData.a j < i) (h2 : i < ctx.n24CarryData.a (j + 1)) :
    ctx.d i = 0 := by
  have hadj := ctx.n24CarryData.carry.hits.adjacent ctx.shell.hd j
  have h := hadj.zero_between h1 h2
  rwa [digitSide_shell_d_eq] at h

/-! ## Part 2.  The type-level settlement: what the digit demands quantify over

The fibre member `k` is a hit INDEX in `[F, F + W)`; its hit POSITION `a k` sits in the
shell `(X, 2X]`; the demanded digit position is the raw NUMBER `k + 1 ∈ (F, F + W]`. -/

/-- **The fibre member's hit position sits in the dyadic shell**: `X < a k ≤ 2X`.  (This is
the object the orbit machinery pins — NOT the demanded digit position `k + 1`.) -/
theorem olcFibre_hitPosition_in_shell (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ olcFibre ctx) :
    ctx.shell.X < ctx.n24CarryData.a k ∧ ctx.n24CarryData.a k ≤ 2 * ctx.shell.X := by
  have hw := olcFibre_mem_window ctx hk
  constructor
  · have hspec := ctx.n24CarryData.carry.hits.firstIndexAbove_spec ctx.shell.X
    have hmono := ctx.n24CarryData.carry.hits.strict.monotone hw.1
    omega
  · exact ctx.n24CarryData.carry.hits.a_le_two_mul_of_lt_add_card ctx.shell.X hw.2

/-- **The demanded digit position is a small raw number**: for `k ∈ olcFibre ctx` the
`returnMaxClean` demand reads `ctx.d` at `k + 1 ∈ (F, F + W]` — index-window arithmetic,
not shell positions. -/
theorem olcFibre_demand_position (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ olcFibre ctx) :
    ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X < k + 1
      ∧ k + 1 ≤ ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + (supportShell ctx.shell.d ctx.shell.X).card := by
  have hw := olcFibre_mem_window ctx hk
  omega

/-- **Sub-`X` hit witnesses live strictly below the window**: a hit at a position `n ≤ X`
has index `j < F = firstIndexAbove X` — the pre-window region. -/
theorem digitSide_hit_index_lt_first (ctx : ActualFailureContext) {n j : ℕ}
    (hn : n ≤ ctx.shell.X) (hj : ctx.n24CarryData.a j = n) :
    j < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X := by
  by_contra h
  have hmono : ctx.n24CarryData.a (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X)
      ≤ ctx.n24CarryData.a j :=
    ctx.n24CarryData.carry.hits.strict.monotone (not_lt.mp h)
  have hspec := ctx.n24CarryData.carry.hits.firstIndexAbove_spec ctx.shell.X
  omega

/-- **The sub-`X` digit value is pre-window support membership** (index form): for
`1 ≤ n ≤ X`, `d n = 1` iff some hit of index `j < F` lands at `n`. -/
theorem digitSide_subX_demand_iff (ctx : ActualFailureContext) {n : ℕ}
    (hX : n ≤ ctx.shell.X) :
    ctx.d n = 1
      ↔ ∃ j, j < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          ∧ ctx.n24CarryData.a j = n := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := ctx.n24CarryData.carry.hits.complete n h
    exact ⟨j, digitSide_hit_index_lt_first ctx hX hj, hj⟩
  · rintro ⟨j, _, hj⟩
    rw [← hj]
    exact digitSide_hit ctx j

/-- **The sub-`X` digit value is support membership** (Finset form): for `1 ≤ n ≤ X`,
`d n = 1` iff `n ∈ supportIn d X`. -/
theorem digitSide_subX_support_iff (ctx : ActualFailureContext) {n : ℕ}
    (h1 : 1 ≤ n) (hX : n ≤ ctx.shell.X) :
    ctx.d n = 1 ↔ n ∈ supportIn ctx.shell.d ctx.shell.X := by
  rw [mem_supportIn, digitSide_shell_d_eq]
  exact ⟨fun h => ⟨h1, hX, h⟩, fun h => h.2.2⟩

/-- **The window start is controlled by the sub-`X` support count**:
`F ≤ supportCount d X + 1` (the indices `1 ≤ j < F` inject into `supportIn d X`). -/
theorem digitSide_firstIndexAbove_le (ctx : ActualFailureContext) :
    ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
      ≤ supportCount ctx.shell.d ctx.shell.X + 1 := by
  classical
  have hsub : (Finset.Ico 1
        (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X)).image
          (fun j => ctx.n24CarryData.a j)
      ⊆ supportIn ctx.shell.d ctx.shell.X := by
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨j, hj, rfl⟩ := hn
    rw [Finset.mem_Ico] at hj
    rw [mem_supportIn]
    refine ⟨?_, ?_, ctx.n24CarryData.carry.hits.hit j⟩
    · have := digitSide_index_le_a ctx j
      omega
    · exact ctx.n24CarryData.carry.hits.lt_firstIndexAbove ctx.shell.X hj.2
  have hcard : (Finset.Ico 1
        (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X)).card
      ≤ (supportIn ctx.shell.d ctx.shell.X).card := by
    rw [← Finset.card_image_of_injOn
      (fun x _ y _ hxy => ctx.n24CarryData.carry.hits.strict.injective hxy)]
    exact Finset.card_le_card hsub
  rw [Nat.card_Ico] at hcard
  unfold supportCount
  omega

/-- **The overflow regime forces near-full sub-`X` density**: if the raw index window
`(F, F + W]` escapes past `X`, then `X ≤ supportCount d X + W` — with the failure bound
`W < c₀·X` this means sub-`X` support density `> 1 − c₀`. -/
theorem digitSide_subX_dense_of_overflow (ctx : ActualFailureContext)
    (h : ctx.shell.X < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
        + (supportShell ctx.shell.d ctx.shell.X).card) :
    ctx.shell.X ≤ supportCount ctx.shell.d ctx.shell.X
        + (supportShell ctx.shell.d ctx.shell.X).card := by
  have h1 := digitSide_firstIndexAbove_le ctx
  omega

/-- **The demand dichotomy** (the goal-2/goal-3 settlement): every class-4 digit demand
position `k + 1` is a sub-`X` position, OR the shell's sub-`X` support is dense
(`X ≤ supportCount + W`). -/
theorem olcFibre_demand_dichotomy (ctx : ActualFailureContext) {k : ℕ}
    (hk : k ∈ olcFibre ctx) :
    k + 1 ≤ ctx.shell.X
      ∨ ctx.shell.X ≤ supportCount ctx.shell.d ctx.shell.X
          + (supportShell ctx.shell.d ctx.shell.X).card := by
  by_cases h : k + 1 ≤ ctx.shell.X
  · exact Or.inl h
  · right
    have hw := olcFibre_mem_window ctx hk
    exact digitSide_subX_dense_of_overflow ctx (by omega)

/-! ## Part 3.  The digit fields as hit-avoidance statements (sharp characterizations) -/

/-- **`returnMaxClean` is hit avoidance**: the field holds iff NO hit position equals
`k + 1` for any per-slice maximum `k` of the class-4 fibre. -/
theorem returnMaxCleanBody_iff_hitMiss (ctx : ActualFailureContext) :
    ReturnMaxCleanBody ctx
      ↔ ∀ k ∈ olcFibre ctx,
          (∀ z ∈ olcFibre ctx, returnSelfRefKey ctx z = returnSelfRefKey ctx k → z ≤ k) →
          ∀ j, ctx.n24CarryData.a j ≠ k + 1 := by
  constructor
  · intro h k hk hmax
    exact (digitSide_eq_zero_iff ctx (k + 1)).mp (h k hk hmax)
  · intro h k hk hmax
    exact (digitSide_eq_zero_iff ctx (k + 1)).mpr (h k hk hmax)

/-- **`returnZero` is hit avoidance**: the field holds iff NO hit position lands in any
same-slice gap `(x, z]` of the class-4 fibre. -/
theorem returnZeroBody_iff_hitMiss (ctx : ActualFailureContext) :
    ReturnZeroBody ctx
      ↔ ∀ y ∈ (olcFibre ctx).image (returnSelfRefKey ctx),
          ∀ x ∈ olcSlice ctx (returnSelfRefKey ctx) y,
            ∀ z ∈ olcSlice ctx (returnSelfRefKey ctx) y,
              x < z → ∀ n, x < n → n ≤ z → ∀ j, ctx.n24CarryData.a j ≠ n := by
  constructor
  · intro h y hy x hx z hz hxz n hn1 hn2
    exact (digitSide_eq_zero_iff ctx n).mp (h y hy x hx z hz hxz n hn1 hn2)
  · intro h y hy x hx z hz hxz n hn1 hn2
    exact (digitSide_eq_zero_iff ctx n).mpr (h y hy x hx z hz hxz n hn1 hn2)

/-! ## Part 4.  The index-window separation surface and the joint digit-field closure -/

/-- **The index-window separation Prop**: the raw digit word vanishes on the index window
`(F, F + W]` — equivalently the support avoids that explicit small interval.  This single
digit fact contains EVERY position demanded by `returnZero` and `returnMaxClean`. -/
def ReturnIndexWindowClean (ctx : ActualFailureContext) : Prop :=
  ∀ n, ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X < n →
    n ≤ ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
        + (supportShell ctx.shell.d ctx.shell.X).card →
    ctx.d n = 0

/-- The separation Prop in hit form: no hit position lands in `(F, F + W]`. -/
theorem returnIndexWindowClean_iff_hits_avoid (ctx : ActualFailureContext) :
    ReturnIndexWindowClean ctx
      ↔ ∀ j, ¬ (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            < ctx.n24CarryData.a j
          ∧ ctx.n24CarryData.a j
            ≤ ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card) := by
  constructor
  · rintro h j ⟨h1, h2⟩
    have hz := h _ h1 h2
    have hhit := digitSide_hit ctx j
    omega
  · intro h n hn1 hn2
    rw [digitSide_eq_zero_iff]
    intro j hj
    apply h j
    rw [hj]
    exact ⟨hn1, hn2⟩

/-- **The FULL clean step from window separation** (stronger than the maxima form): every
class-4 start gets `d(k + 1) = 0`. -/
theorem returnCleanStep_of_indexWindowClean (ctx : ActualFailureContext)
    (h : ReturnIndexWindowClean ctx) :
    ∀ k ∈ olcFibre ctx, ctx.d (k + 1) = 0 := by
  intro k hk
  have hw := olcFibre_mem_window ctx hk
  exact h (k + 1) (by omega) (by omega)

/-- **`returnMaxClean` from window separation.** -/
theorem returnMaxCleanBody_of_indexWindowClean (ctx : ActualFailureContext)
    (h : ReturnIndexWindowClean ctx) :
    ReturnMaxCleanBody ctx :=
  fun k hk _ => returnCleanStep_of_indexWindowClean ctx h k hk

/-- **`returnZero` from window separation**: every demanded position `j ∈ (x, z]` of a
same-slice pair sits inside `(F, F + W]`. -/
theorem returnZeroBody_of_indexWindowClean (ctx : ActualFailureContext)
    (h : ReturnIndexWindowClean ctx) :
    ReturnZeroBody ctx := by
  intro y hy x hx z hz hxz j hj1 hj2
  rw [olcSlice_def, Finset.mem_filter] at hx hz
  have hxw := olcFibre_mem_window ctx hx.1
  have hzw := olcFibre_mem_window ctx hz.1
  exact h j (by omega) (by omega)

/-! ## Part 5.  The `r = 0` top-start surface: vacuous closure and the hit-gap disequality -/

/-- **The class-1 pair-residual `topStart` field is a THEOREM**: it is conditioned on
`ctx.n24CarryData.r = 0`, and `n24_r_pos` proves `1 ≤ r` at every actual failure context —
the entire `r = 0` top-start hit-gap demand fires only vacuously. -/
theorem class1PairTopStart_settled :
    ∀ ctx : ActualFailureContext,
      ctx.n24CarryData.r = 0 →
      64 ∣ shellLadderDepth ctx →
      9 ≤ (class1SlopeDatum ctx).q →
      ((class1SlopeDatum ctx).q ≤ 15 ∨ 25 ≤ (class1SlopeDatum ctx).q) →
      (class1SlopeDatum ctx).q ∉ class1ClosedModuli →
      ¬ Class1DatumClosed ctx →
      ¬ Class1PairTopMiss ctx →
      ¬ Class1GcdWindowMiss ctx →
      cnlWindowTopStart ctx ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 := by
  intro ctx hr _ _ _ _ _ _ _
  exact absurd hr (by have := n24_r_pos ctx; omega)

/-- **`Class1PairResidual` collapses to its `deep` field**: the `topStart` field is filled
in by the vacuous closure above. -/
theorem class1PairResidual_of_deepOnly
    (hdeep : ∀ ctx : ActualFailureContext,
      1 ≤ ctx.n24CarryData.r →
      64 ∣ shellLadderDepth ctx →
      9 ≤ (class1SlopeDatum ctx).q →
      ((class1SlopeDatum ctx).q ≤ 15 ∨ 25 ≤ (class1SlopeDatum ctx).q) →
      (class1SlopeDatum ctx).q ∉ class1ClosedModuli →
      ¬ Class1DatumClosed ctx →
      ¬ Class1GcdWindowMiss ctx →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅) :
    Class1PairResidual :=
  ⟨class1PairTopStart_settled, hdeep⟩

/-- **The hit-gap disequality holds at every IN-WINDOW index** (`j + 1 < F + W`): the proved
dyadic ceiling `hitGap ≤ L + B + 1` and the carry-scale pin `B + 25 ≤ L` keep
`64·hitGap ≤ 128L − 1536 < 129L + 64`.  The single index this argument cannot reach is the
top start `F + W − 1`, whose gap crosses the shell boundary `2X`. -/
theorem digitSide_interior_hitGap_diseq (ctx : ActualFailureContext) {j : ℕ}
    (hj : j + 1 < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
        + (supportShell ctx.shell.d ctx.shell.X).card) :
    64 * hitGap ctx.n24CarryData.a j ≠ 129 * shellLadderDepth ctx + 64 := by
  have hceil := n24_hitGap_le_window ctx hj
  have hBL : carryB ctx.shell.Q + 25 ≤ shellLadderDepth ctx := ctx.shell_carryLarge
  omega

/-- **Off `64 ∣ L` the hit-gap disequality is pure arithmetic** at EVERY index:
`64·g = 129L + 64` forces `64 ∣ L`.  (The surviving `topStart` demand already carries the
`64 ∣ L` hypothesis — this lemma documents that it binds in no other regime.) -/
theorem digitSide_hitGap_diseq_of_not_dvd (ctx : ActualFailureContext) (j : ℕ)
    (h : ¬ 64 ∣ shellLadderDepth ctx) :
    64 * hitGap ctx.n24CarryData.a j ≠ 129 * shellLadderDepth ctx + 64 := by
  intro heq
  exact h (by omega)

/-- **The top gap straddles the upper shell boundary**: `a(top) ≤ 2X < a(top + 1)` — the
`r = 0` top hit-gap is the support gap across `2X`, the one gap the in-window dyadic
ceiling provably cannot reach. -/
theorem digitSide_topGap_straddle (ctx : ActualFailureContext) :
    ctx.n24CarryData.a (cnlWindowTopStart ctx) ≤ 2 * ctx.shell.X
      ∧ 2 * ctx.shell.X < ctx.n24CarryData.a (cnlWindowTopStart ctx + 1) := by
  have hF : 1 ≤ ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X :=
    ctx.n24CarryData.carry.hits.firstIndexAbove_pos_of_supportCount_pos
      ctx.n24SupportCount_pos
  have hW := cnlMulti_r_add_one_le_width ctx
  constructor
  · apply ctx.n24CarryData.carry.hits.a_le_two_mul_of_lt_add_card
    unfold cnlWindowTopStart
    omega
  · have h := ctx.n24CarryData.carry.hits.a_firstIndexAbove_add_card_gt ctx.shell.X
    have heq : cnlWindowTopStart ctx + 1
        = ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + (supportShell ctx.shell.d ctx.shell.X).card := by
      unfold cnlWindowTopStart
      omega
    rw [heq]
    exact h

/-! ## Part 6.  The strictly smaller successor residual and the endpoint -/

/-- **The digit-side enumeration residual** — the wave-5 `Erdos260EnumResidual` with three
strict reductions: `returnZero` and `returnMaxClean` are demanded only on contexts whose
digit support MEETS the raw index window `(F, F + W]` (`¬ ReturnIndexWindowClean`; separated
contexts close through Part 4), and the class-1 slot carries ONLY the deep field (the
`r = 0` `topStart` field is the proved `class1PairTopStart_settled`).  All other fields are
verbatim wave-5 surfaces. -/
structure DigitSideEnumResidual where
  /-- Tower / class 2 — verbatim wave-5 field. -/
  towerEnum : TowerModulusEnumerationResidual
  /-- Run / class 5 — verbatim wave-5 field. -/
  runNumeric : RunCycleNumericSettlementHyp
  /-- Return / class 4 count gates — verbatim wave-5 field. -/
  returnGates : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    2 * (129 * shellLadderDepth ctx + 64)
      ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
    ReturnGatesBody ctx
  /-- Return / class 4 digit Z — demanded additionally only where the support meets the
  raw index window `(F, F + W]`. -/
  returnZero : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    (∃ k ∈ olcFibre ctx,
      2 ^ carryVal2 ctx k < (supportShell ctx.shell.d ctx.shell.X).card) →
    ¬ ReturnIndexWindowClean ctx →
    ReturnZeroBody ctx
  /-- Return / class 4 clean step at slice maxima — demanded additionally only where the
  support meets the raw index window `(F, F + W]`. -/
  returnMaxClean : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnIndexWindowClean ctx → ReturnMaxCleanBody ctx
  /-- Return / class 4 K.1 interior — verbatim wave-5 field. -/
  returnInterior : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx
  /-- Chernoff / class 0 survivors — verbatim wave-5 field. -/
  class0Survivor : ∀ ctx : ActualFailureContext, Class0DatumSurvivor ctx →
    Class0SurvivorResidueMiss ctx
  /-- Chernoff / class 0 mid band — verbatim wave-5 field. -/
  class0Mid : ∀ ctx : ActualFailureContext, 48 ≤ (class1SlopeDatum ctx).q →
    (class1SlopeDatum ctx).q < 96 → Class0CycleMeetsShallow ctx →
    Class0WindowCycleCheck ctx
  /-- Chernoff / class 0 large moduli — verbatim wave-5 field. -/
  class0Big : ∀ ctx : ActualFailureContext, 96 ≤ (class1SlopeDatum ctx).q →
    Class0WindowCycleCheck ctx
  /-- CNL / class 1 — ONLY the deep (`r ≥ 1`) field of `Class1PairResidual`; the `r = 0`
  `topStart` field is closed by `class1PairTopStart_settled` (`n24_r_pos`). -/
  class1Deep : ∀ ctx : ActualFailureContext,
    1 ≤ ctx.n24CarryData.r →
    64 ∣ shellLadderDepth ctx →
    9 ≤ (class1SlopeDatum ctx).q →
    ((class1SlopeDatum ctx).q ≤ 15 ∨ 25 ≤ (class1SlopeDatum ctx).q) →
    (class1SlopeDatum ctx).q ∉ class1ClosedModuli →
    ¬ Class1DatumClosed ctx →
    ¬ Class1GcdWindowMiss ctx →
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅
  /-- DensePack / class 3 — verbatim wave-5 field. -/
  densePackGated : DensePackGatedClosureResidual

namespace DigitSideEnumResidual

/-- **The bridge into the wave-5 capstone residual**: separated contexts close the two
digit fields through Part 4, the class-1 `topStart` field is filled in vacuously, every
other field passes through verbatim. -/
def toEnum (R : DigitSideEnumResidual) : Erdos260EnumResidual where
  towerEnum := R.towerEnum
  runNumeric := R.runNumeric
  returnGates := R.returnGates
  returnZero := fun ctx hfree hone hex => by
    by_cases hcl : ReturnIndexWindowClean ctx
    · exact returnZeroBody_of_indexWindowClean ctx hcl
    · exact R.returnZero ctx hfree hone hex hcl
  returnMaxClean := fun ctx hfree => by
    by_cases hcl : ReturnIndexWindowClean ctx
    · exact returnMaxCleanBody_of_indexWindowClean ctx hcl
    · exact R.returnMaxClean ctx hfree hcl
  returnInterior := R.returnInterior
  class0Survivor := R.class0Survivor
  class0Mid := R.class0Mid
  class0Big := R.class0Big
  class1Pair := class1PairResidual_of_deepOnly R.class1Deep
  densePackGated := R.densePackGated

/-- The final statement from the digit-side residual, through the wave-5 capstone. -/
theorem toStatement (R : DigitSideEnumResidual) : Erdos260Statement :=
  erdos260_of_enumResidual R.toEnum

end DigitSideEnumResidual

/-- **The digit-side endpoint**: `Erdos260Statement` from the digit-side residual — the
wave-5 surface with `returnZero` / `returnMaxClean` demanded only off the index-window
separation regime and the class-1 `r = 0` field closed outright. -/
theorem erdos260_of_digitSideResidual (R : DigitSideEnumResidual) : Erdos260Statement :=
  R.toStatement

/-- **The weakening witness**: the wave-5 residual provides the digit-side residual
outright — every new field demands no more than its wave-5 counterpart (`returnZero` /
`returnMaxClean` drop the new separation hypothesis, `class1Deep` is the `deep` projection
of `class1Pair`). -/
def digitSideEnumResidual_of_enumResidual (R : Erdos260EnumResidual) :
    DigitSideEnumResidual where
  towerEnum := R.towerEnum
  runNumeric := R.runNumeric
  returnGates := R.returnGates
  returnZero := fun ctx hfree hone hex _ => R.returnZero ctx hfree hone hex
  returnMaxClean := fun ctx hfree _ => R.returnMaxClean ctx hfree
  returnInterior := R.returnInterior
  class0Survivor := R.class0Survivor
  class0Mid := R.class0Mid
  class0Big := R.class0Big
  class1Deep := R.class1Pair.deep
  densePackGated := R.densePackGated

/-! ## Part 7.  Honest machine-readable status -/

/-- Honest machine-readable status of the digit-side closure pass. -/
def digitSideClosureStatus : List String :=
  [ "SCOPE: the wave-5 digit-side leftovers - returnZero (same-slice zero-runs in the " ++
      "carryVal2 < log2 K regime), returnMaxClean (d(k+1) = 0 at slice maxima), and the " ++
      "r = 0 top-start hit-gap disequalities of class 1 (class 0 analogues were already " ++
      "packaged upstream).  Everything here is additive - no existing file is edited.",
    "TYPE-LEVEL SETTLEMENT (the brief's KEY question, goal 2): the class-4 fibre lives in " ++
      "HIT-INDEX space (olcFibre members k are starts, starts = Ico F (F+W) with " ++
      "F = firstIndexAbove X, W = |supportShell| - cnlMulti_starts_eq_window).  The " ++
      "returnMaxClean argument k+1 is the raw NUMBER k+1 in (F, F+W], NOT the next hit " ++
      "position a(k+1); the member's hit position sits in the shell X < a k <= 2X " ++
      "(olcFibre_hitPosition_in_shell) while the demanded digit position is " ++
      "k+1 <= F+W (olcFibre_demand_position).  Same for returnZero: the demanded js are " ++
      "raw positions in (x, z] subset (F, F+W] (goal 3).  ctx.d (k+1) is therefore a " ++
      "digit in the PRE-WINDOW/sub-X region whenever k+1 <= X.",
    "DIGIT DICTIONARY MINED (goal 1): the carry hits are COMPLETE - d n = 1 iff n is a " ++
      "hit position (digitSide_eq_one_iff / digitSide_eq_zero_iff, bounded finite form " ++
      "digitSide_eq_zero_iff_bounded via j <= a j), zero-runs between consecutive hits " ++
      "are AUTOMATIC (digitSide_zero_between_hits) - the hit-gap structure is the only " ++
      "digit freedom, exactly as conjectured.  But within the index window the demanded " ++
      "positions k+1 are NOT hit positions of pinned indices, so the dictionary " ++
      "transforms (not closes) the fields: returnMaxCleanBody_iff_hitMiss / " ++
      "returnZeroBody_iff_hitMiss - both fields are pure HIT-AVOIDANCE statements.",
    "SUB-X LOCALIZATION (goals 2-3): a hit at a position n <= X has index j < F " ++
      "(digitSide_hit_index_lt_first), so for k+1 <= X the demand reads pre-window " ++
      "support membership exactly: d(k+1) = 1 iff some j < F has a j = k+1 " ++
      "(digitSide_subX_demand_iff; Finset form digitSide_subX_support_iff).  " ++
      "F <= supportCount d X + 1 (digitSide_firstIndexAbove_le), so the only escape from " ++
      "the sub-X regime is near-full sub-X density: X <= supportCount + W " ++
      "(digitSide_subX_dense_of_overflow, olcFibre_demand_dichotomy; with the failure " ++
      "bound W < c0 X this is sub-X density > 1 - c0).",
    "NEW CLOSURE SURFACE (goal 4): ReturnIndexWindowClean - the support avoids the ONE " ++
      "explicit raw interval (F, F+W] (hit form returnIndexWindowClean_iff_hits_avoid).  " ++
      "It closes BOTH digit fields at once: returnZeroBody_of_indexWindowClean, " ++
      "returnCleanStep_of_indexWindowClean (the FULL clean step, stronger than the " ++
      "maxima reduction), returnMaxCleanBody_of_indexWindowClean.  HONEST: the " ++
      "separation is not implied by the shell failure bound (the window may contain " ++
      "support); it is the natural single-Prop digit surface, consumed as a guard.",
    "CLOSED OUTRIGHT (goal 5, the r = 0 top-start facts): class1PairTopStart_settled - " ++
      "the entire topStart field of Class1PairResidual is a THEOREM since n24_r_pos " ++
      "proves r >= 1 at every actual ctx (the r = 0 regime is vacuous); " ++
      "class1PairResidual_of_deepOnly collapses the class-1 residual to its deep field.  " ++
      "The class-0 analogues were already packaged upstream " ++
      "(class0WindowCycleCheck_of_r_eq_zero).",
    "HIT-GAP DISEQUALITY SHARPENED (goal 5): digitSide_interior_hitGap_diseq - at EVERY " ++
      "in-window index j+1 < F+W the disequality 64*hitGap != 129L+64 is a THEOREM (the " ++
      "dyadic ceiling hitGap <= L+B+1 plus the carry pin B+25 <= L give " ++
      "64*hitGap <= 128L-1536 < 129L+64); digitSide_hitGap_diseq_of_not_dvd - off " ++
      "64 | L it is pure arithmetic at EVERY index (64*g = 129L+64 forces 64 | L).  The " ++
      "ONLY unreachable index is the top start F+W-1, whose gap straddles the upper " ++
      "shell boundary 2X (digitSide_topGap_straddle) - genuinely unpinned, but vacuous " ++
      "anyway through n24_r_pos.",
    "RESIDUAL + ENDPOINT: DigitSideEnumResidual - the wave-5 surface with returnZero / " ++
      "returnMaxClean demanded only on not-ReturnIndexWindowClean contexts and class1 " ++
      "carrying ONLY the deep field; endpoint erdos260_of_digitSideResidual through " ++
      "toEnum into erdos260_of_enumResidual (nothing re-proved); weakening witness " ++
      "digitSideEnumResidual_of_enumResidual : Erdos260EnumResidual -> " ++
      "DigitSideEnumResidual (the new endpoint demands no more than wave 5).",
    "HONEST LIMIT (no fabricated closure): the digit values on (F, F+W] are genuinely " ++
      "free - the orbit pins constrain hit gaps at indices >= k and the orbit value at " ++
      "k, never the raw digit positions <= F+W; the M.2.1 congruence yields spacing, " ++
      "not digit values (upstream audit).  returnZero and returnMaxClean remain open on " ++
      "contexts where the support meets the index window; the residual above is their " ++
      "sharpest formalized surface in this pass." ]

theorem digitSideClosureStatus_nonempty : digitSideClosureStatus ≠ [] := by
  simp [digitSideClosureStatus]

/-! ## Part 8.  Audit -/

#print axioms digitSide_shell_d_eq
#print axioms digitSide_hit
#print axioms digitSide_eq_one_iff
#print axioms digitSide_eq_zero_iff
#print axioms digitSide_eq_zero_iff_bounded
#print axioms digitSide_zero_between_hits
#print axioms olcFibre_hitPosition_in_shell
#print axioms olcFibre_demand_position
#print axioms digitSide_hit_index_lt_first
#print axioms digitSide_subX_demand_iff
#print axioms digitSide_subX_support_iff
#print axioms digitSide_firstIndexAbove_le
#print axioms digitSide_subX_dense_of_overflow
#print axioms olcFibre_demand_dichotomy
#print axioms returnMaxCleanBody_iff_hitMiss
#print axioms returnZeroBody_iff_hitMiss
#print axioms returnIndexWindowClean_iff_hits_avoid
#print axioms returnCleanStep_of_indexWindowClean
#print axioms returnMaxCleanBody_of_indexWindowClean
#print axioms returnZeroBody_of_indexWindowClean
#print axioms class1PairTopStart_settled
#print axioms class1PairResidual_of_deepOnly
#print axioms digitSide_interior_hitGap_diseq
#print axioms digitSide_hitGap_diseq_of_not_dvd
#print axioms digitSide_topGap_straddle
#print axioms DigitSideEnumResidual.toEnum
#print axioms DigitSideEnumResidual.toStatement
#print axioms erdos260_of_digitSideResidual
#print axioms digitSideEnumResidual_of_enumResidual
#print axioms digitSideClosureStatus_nonempty

end

end Erdos260
