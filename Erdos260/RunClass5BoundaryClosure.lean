import Erdos260.Erdos260SharpCapstone

/-!
# Run / Class 5 — the boundary ceiling closure (`RunClass5BoundaryClosure`)

This wave-3 module (NEW; it edits no existing file) settles the **boundary side** of the
Run atom's wave-2 split surface `RunClass5SplitBoundary` (the capstone `runSplit` field):
it eliminates the `M`/`hM` fields outright, bounds the class-5 fibre by cycle density,
and reduces the whole atom to ONE Section 26 numeric at the canonical multiplier
`runDyadicMult ctx`.

## The keystone (NEW, overturns the wave-2 obstruction)

Wave 2 recorded the obstruction "*on the boundary band the window excess has NO formalized
ceiling — the dyadic gap estimate `hitGap ≤ L+B+1` covers only indices whose gap END stays
inside the shell window, which the overrun starts escape by construction*".  The brief
asked to investigate whether hit positions above the window admit any `f(X)` ceiling.

**They do.**  The dyadic gap principle is *self-referential*: a gap of length `h` starting
at position `N` forces the zero-run carry doubling `2^h ≤ R_{N+h} ≤ Q·(N+h+2)` — the run's
END is its START plus its LENGTH.  Applying the proved `zero_gap_len_le_dyadic_scale` to
the SUB-run of length exactly `L+B+1` of any putative longer gap yields the contradiction
`L+B+1 ≤ L+B`.  Hence **every hit gap whose START is within dyadic scale obeys the SAME
ceiling `L+B+1` as the in-window gaps** (`n24_hitGap_le_of_scale`); chaining positions
across the `≤ r` boundary indices (`n24_boundary_a_le`, polynomial-vs-`2^L` scale lemma
`n24_window_scale`) extends the ceiling to every index within window reach
(`n24_hitGap_le_reach`), so every carry-window start — boundary or interior — has

  `gapWindow ≤ (r+1)·(L+B+1)`   and   `windowExcess ≤ runDyadicMult ctx`

(`n24_gapWindow_le_of_start`, `n24_windowExcess_le_runDyadicMult`).

## What this closes / reduces (all proved here)

* **`M`/`hM` eliminated, sharper than asked**: the brief's boundary max
  `class5BoundaryMax ctx` (sup' of `windowExcess` over the top `r+1` band) is defined and
  shown `≤ runDyadicMult ctx` (`class5BoundaryMax_le_runDyadicMult`), so the split
  multiplier COLLAPSES: `max (runDyadicMult ctx) (class5BoundaryMax ctx) = runDyadicMult
  ctx` (`class5_split_multiplier_collapse`).  The capstone field `runSplit` follows from
  ONE numeric per ctx at `runDyadicMult` alone: `runSplitOfNumeric` (exact field type),
  `runSplitOfBoundaryMaxNumeric` (the brief's literal surface), `runSplitOfNumericAt`.
* **Gate ⟹ class-5 fibre EMPTY** (`class5Fibre_empty_of_gate_ceiling`): under the K.1
  numeric gate `64(r+1)(L+B+1) < 129L+64` the high-excess floor `129L+64 ≤ 64·gW` beats
  the now-universal ceiling, so the fibre vanishes — upgrading wave-2's boundary
  confinement (`|fibre₅| ≤ r+1`, `≤ 1` at `r = 0`) to emptiness.  Full Run-atom closures
  `runCoreOfGateCeiling` / `runCoreOfShallowShell` (`r = 0`) / `runCoreOfDepthLe`
  (`L ≤ 15420`).
* **Every actual context is UNGATED** (`n24_gate_violated`): the proved pressure floor
  (`chernoffClass0_highExcessStarts_nonempty`) exhibits a start whose floor meets the
  ceiling, forcing `129L+64 ≤ 64(r+1)(L+B+1)`.  Corollaries: `n24_r_pos` (`r ≥ 1`) and
  `shellLadderDepth_ge_15421` (`L ≥ 15421`) at EVERY `ActualFailureContext` — the entire
  `r = 0` regime of every atom is vacuous.  (Sanity per the wave brief: this does NOT
  prove all classes empty at all ctx — only at GATED shells, which are thereby shown not
  to exist; on the surviving ungated shells the floor and ceiling are compatible.)
* **Cycle-density count bound** (`class5Fibre_card_le_cycleDensity`): with any orbit
  period `c` (from `class1Fibre_orbit_period_exists`, `c ≤ q`), the class-5 fibre injects
  into (band-{1,4} cycle residues) × (window blocks):
  `#fibre₅ ≤ #class5CycleBand · ⌈W/c⌉` — existential form
  `class5Fibre_card_le_cycleDensity_exists`.
* **Finite cycle-check emptiness** (`class5Fibre_empty_of_cycle_band_free`): a period
  avoiding band 1 AND band 4 closes the fibre; fixed-point form
  `class5Fibre_empty_of_orbit_fixed`; NEW closed modulus family `(q, K₀) = (21, 3)`
  (`class5Fibre_empty_of_q21_K3`: the orbit is the fixed point `3` with band
  `canonGap 21 3 = 3`); Run-atom closures `runCoreOfCycleBandFree` / `runCoreOfQ21K3`.
* **Unconditional pointwise-max ceiling** (`runBaseMaxExcess_le_runDyadicMult_uncond`):
  the K.1 interior hypothesis of `RunSupportMaxCore` is now removable.

## The honest remaining residual (single numeric)

`∀ ctx, c0 · #fibre₅ · runDyadicMult ctx ≤ (c⋆ξ/12) · |supportShell|` — needed only on
the (automatically) ungated shells, where `runDyadicMult ≥ Y = L/64 > 0` is genuinely
positive, so it cannot collapse.  It is not derivable from the formalized content: the
model gives no lower bound on `|supportShell|` against `#fibre₅ · runDyadicMult` (the
failure hypothesis bounds `|supportShell|` from ABOVE), and the cycle-density count
`#fibre₅ ≤ b₁₄·⌈W/c⌉` closes it only when the per-(q,K₀) inequality
`c0·b₁₄·runDyadicMult ≲ (c⋆ξ/12)·c` holds — a finite per-family check
(`runSplitOfCycleNumeric`), not a universal theorem.  This is the manuscript's
irreducible Section 26 positive-density input, now carried by ONE scalar inequality.

No `sorry`, `admit`, `axiom`, or `native_decide`; no fabricated witnesses.
-/

namespace Erdos260

open Finset

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 1.  The universal in-scale hit-gap ceiling

The PROVED zero-run growth `2^h ≤ Q(N+h+2)` (`zero_gap_len_le_dyadic_scale`) applied to a
SUB-run of a putative long gap: a gap of length `≥ L+B+2` starting at `N` contains the
zero run `(N, N + (L+B+1)]`, and if `N + (L+B+3) ≤ 4X` that run forces `L+B+1 ≤ L+B` —
absurd.  So the in-window ceiling `L+B+1` holds at EVERY index whose gap START is within
scale, with no reference to the shell window. -/

/-- **The universal dyadic gap ceiling at in-scale starts** (the keystone): if the hit at
index `j` sits below `4X − (L+B+3)`, then `hitGap a j ≤ L + B + 1` — regardless of where
the NEXT hit lands.  Self-referential sub-run argument; no window hypothesis. -/
theorem n24_hitGap_le_of_scale (ctx : ActualFailureContext) {j : ℕ}
    (hscale : ctx.n24CarryData.a j
        + (shellLadderDepth ctx + carryB ctx.shell.Q + 3) ≤ 4 * ctx.shell.X) :
    hitGap ctx.n24CarryData.a j ≤ shellLadderDepth ctx + carryB ctx.shell.Q + 1 := by
  by_contra hcon
  have hgap_eq : hitGap ctx.n24CarryData.a j
      = ctx.n24CarryData.a (j + 1) - ctx.n24CarryData.a j := rfl
  have hstrict : ctx.n24CarryData.a j < ctx.n24CarryData.a (j + 1) :=
    ctx.n24CarryData.carry.hits.strict (Nat.lt_succ_self j)
  have hadj : AdjacentHits ctx.shell.d (ctx.n24CarryData.a j)
      (ctx.n24CarryData.a (j + 1)) :=
    ctx.n24CarryData.carry.hits.adjacent ctx.shell.hd j
  have hzero : ∀ i : ℕ, ctx.n24CarryData.a j < i →
      i ≤ ctx.n24CarryData.a j + (shellLadderDepth ctx + carryB ctx.shell.Q + 1) →
      ctx.shell.d i = 0 := by
    intro i hlo hhi
    exact hadj.zero_between hlo (by omega)
  have hRpos : 0 < integerCarry ctx.shell.Q (Classical.choose ctx.shell.hrational)
      ctx.shell.d (ctx.n24CarryData.a j) :=
    integerCarry_pos_of_later_one ctx.shell.hQ ctx.shell.hd
      (Classical.choose_spec ctx.shell.hrational) hstrict
      (ctx.n24CarryData.carry.hits.hit (j + 1))
  have hle : shellLadderDepth ctx + carryB ctx.shell.Q + 1
      ≤ shellLadderDepth ctx + carryB ctx.shell.Q :=
    zero_gap_len_le_dyadic_scale (C := 4) ctx.shell.hQ ctx.shell.hd
      (Classical.choose_spec ctx.shell.hrational) hRpos hzero
      (Classical.choose_spec ctx.shell.hXdyadic) (by omega)
      (carryB_spec ctx.shell.hQ)
  omega

/-- **Polynomial-vs-dyadic window scale**: `(r+1)(L+B+1) + 2 ≤ 2X`.  From `r ≤ L`
(`proofV4CarryOrder_le_L`), `B + 25 ≤ L`, `L ≥ 28`, and `L² + L + 1 ≤ 2^L`. -/
theorem n24_window_scale (ctx : ActualFailureContext) :
    (ctx.n24CarryData.r + 1) * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) + 2
      ≤ 2 * ctx.shell.X := by
  have hr : ctx.n24CarryData.r ≤ shellLadderDepth ctx := by
    have h := proofV4CarryOrder_le_L ctx.shell
    rw [cnlMulti_n24_r_eq]
    exact h
  have hB : carryB ctx.shell.Q + 25 ≤ shellLadderDepth ctx := ctx.shell_carryLarge
  have hL : 28 ≤ shellLadderDepth ctx := shellLadderDepth_ge ctx
  have hX : ctx.shell.X = 2 ^ shellLadderDepth ctx :=
    Classical.choose_spec ctx.shell.hXdyadic
  have hpoly : ∀ n : ℕ, 28 ≤ n → (n + 1) * (2 * n) + 2 ≤ 2 * 2 ^ n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
        have h28 : 28 * n ≤ n * n := Nat.mul_le_mul hn (le_refl n)
        have hstep : (n + 1 + 1) * (2 * (n + 1)) + 2
            ≤ 2 * ((n + 1) * (2 * n) + 2) := by nlinarith [h28, hn]
        calc (n + 1 + 1) * (2 * (n + 1)) + 2
            ≤ 2 * ((n + 1) * (2 * n) + 2) := hstep
          _ ≤ 2 * (2 * 2 ^ n) := by omega
          _ = 2 * 2 ^ (n + 1) := by rw [pow_succ]; ring
  have h1 : (ctx.n24CarryData.r + 1) * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)
      ≤ (shellLadderDepth ctx + 1) * (2 * shellLadderDepth ctx) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h2 := hpoly (shellLadderDepth ctx) hL
  rw [hX]
  omega

/-- **The boundary position chain**: the hit at the `m`-th index past the window top obeys
`a (F+W−1+m) ≤ 2X + m·(L+B+1)` for `m ≤ r` (induction: the top in-window hit is `≤ 2X`,
and each further gap is ceilinged by `n24_hitGap_le_of_scale`). -/
theorem n24_boundary_a_le (ctx : ActualFailureContext) :
    ∀ m : ℕ, m ≤ ctx.n24CarryData.r →
      ctx.n24CarryData.a
          (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card - 1 + m)
        ≤ 2 * ctx.shell.X
          + m * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) := by
  intro m
  induction m with
  | zero =>
      intro _
      have hF := n24_firstIndexAbove_pos ctx
      have h := ctx.n24CarryData.carry.hits.a_le_two_mul_of_lt_add_card
        ctx.shell.X
        (k := ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + (supportShell ctx.shell.d ctx.shell.X).card - 1)
        (by omega)
      simpa using h
  | succ m ih =>
      intro hm
      have ihm := ih (by omega)
      set j := ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
        + (supportShell ctx.shell.d ctx.shell.X).card - 1 + m with hj
      have hidx : ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + (supportShell ctx.shell.d ctx.shell.X).card - 1 + (m + 1) = j + 1 := by
        omega
      rw [hidx]
      have hgap : hitGap ctx.n24CarryData.a j
          ≤ shellLadderDepth ctx + carryB ctx.shell.Q + 1 := by
        apply n24_hitGap_le_of_scale
        have hpoly := n24_window_scale ctx
        have hmul : m * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)
            ≤ ctx.n24CarryData.r * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) :=
          Nat.mul_le_mul (by omega) (le_refl _)
        have hsplit : (ctx.n24CarryData.r + 1)
              * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)
            = ctx.n24CarryData.r * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)
              + (shellLadderDepth ctx + carryB ctx.shell.Q + 1) := by ring
        omega
      have hgap_eq : hitGap ctx.n24CarryData.a j
          = ctx.n24CarryData.a (j + 1) - ctx.n24CarryData.a j := rfl
      have hmono : ctx.n24CarryData.a j ≤ ctx.n24CarryData.a (j + 1) :=
        (ctx.n24CarryData.carry.hits.strict (Nat.lt_succ_self j)).le
      have hmulsucc : (m + 1) * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)
          = m * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)
            + (shellLadderDepth ctx + carryB ctx.shell.Q + 1) := by ring
      omega

/-- **The boundary gap ceiling**: the gap at the `m`-th index past the window top (any
`m ≤ r`) obeys the SAME ceiling `L+B+1` as in-window gaps. -/
theorem n24_boundary_hitGap_le (ctx : ActualFailureContext) {m : ℕ}
    (hm : m ≤ ctx.n24CarryData.r) :
    hitGap ctx.n24CarryData.a
        (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + (supportShell ctx.shell.d ctx.shell.X).card - 1 + m)
      ≤ shellLadderDepth ctx + carryB ctx.shell.Q + 1 := by
  apply n24_hitGap_le_of_scale
  have hpos := n24_boundary_a_le ctx m hm
  have hpoly := n24_window_scale ctx
  have hmul : m * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)
      ≤ ctx.n24CarryData.r * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) :=
    Nat.mul_le_mul hm (le_refl _)
  have hsplit : (ctx.n24CarryData.r + 1)
        * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)
      = ctx.n24CarryData.r * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)
        + (shellLadderDepth ctx + carryB ctx.shell.Q + 1) := by ring
  omega

/-- **The within-reach gap ceiling**: EVERY index `j < F + W + r` (covering every descent
window of every carry-window start, boundary included) has `hitGap a j ≤ L + B + 1`. -/
theorem n24_hitGap_le_reach (ctx : ActualFailureContext) {j : ℕ}
    (hj : j < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
        + (supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r) :
    hitGap ctx.n24CarryData.a j
      ≤ shellLadderDepth ctx + carryB ctx.shell.Q + 1 := by
  by_cases hwin : j + 1 < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
      + (supportShell ctx.shell.d ctx.shell.X).card
  · exact n24_hitGap_le_window ctx hwin
  · have hF := n24_firstIndexAbove_pos ctx
    have hidx : j = ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
        + (supportShell ctx.shell.d ctx.shell.X).card - 1
        + (j - (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card - 1)) := by omega
    rw [hidx]
    exact n24_boundary_hitGap_le ctx (by omega)

/-- **The ungated gap-window ceiling**: EVERY carry-window start (interior or boundary)
has `gapWindow ≤ (r+1)·(L+B+1)`. -/
theorem n24_gapWindow_le_of_start (ctx : ActualFailureContext) {k : ℕ}
    (hk : k < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
        + (supportShell ctx.shell.d ctx.shell.X).card) :
    gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
      ≤ (ctx.n24CarryData.r + 1) * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) := by
  unfold gapWindow
  calc ∑ i ∈ Finset.range (ctx.n24CarryData.r + 1), hitGap ctx.n24CarryData.a (k + i)
      ≤ ∑ _i ∈ Finset.range (ctx.n24CarryData.r + 1),
          (shellLadderDepth ctx + carryB ctx.shell.Q + 1) := by
        refine Finset.sum_le_sum ?_
        intro i hi
        rw [Finset.mem_range] at hi
        exact n24_hitGap_le_reach ctx (by omega)
    _ = (ctx.n24CarryData.r + 1) * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- **The ungated window-excess ceiling — the `M`/`hM` eliminator**: EVERY carry-window
start has `windowExcess ≤ runDyadicMult ctx`, with no interior hypothesis and no gate. -/
theorem n24_windowExcess_le_runDyadicMult (ctx : ActualFailureContext) {k : ℕ}
    (hk : k < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
        + (supportShell ctx.shell.d ctx.shell.X).card) :
    windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
      ≤ runDyadicMult ctx := by
  refine windowExcess_le_window_gap_multiplier (g₀ := runDyadicG0 ctx) ?_
    (run_scale_le_runDyadicMult ctx) (runDyadicMult_nonneg ctx)
  intro i hilo hihi
  exact n24_hitGap_le_reach ctx (by omega)

/-- **The unconditional pointwise-max ceiling**: `runBaseMaxExcess ≤ runDyadicMult` with
NO interior hypothesis (removes the `hinterior` side condition of `RunSupportMaxCore`'s
`runBaseMaxExcess_le_runDyadicMult`). -/
theorem runBaseMaxExcess_le_runDyadicMult_uncond (ctx : ActualFailureContext)
    (stageOf : ℕ → ℕ) :
    runBaseMaxExcess ctx stageOf ≤ runDyadicMult ctx := by
  refine runBaseMaxExcess_le_of_pointBound ctx stageOf (runDyadicMult_nonneg ctx) ?_
  intro k hk
  have hk5 : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5 :=
    (Finset.mem_filter.mp hk).1
  exact n24_windowExcess_le_runDyadicMult ctx (class5Fibre_mem_window ctx hk5).2

/-! ## Part 2.  The boundary max (the brief's literal `M`) and its collapse -/

/-- The top `r + 1` boundary band of the carry start window (a concrete `Finset`). -/
def class5BoundaryBand (ctx : ActualFailureContext) : Finset ℕ :=
  Finset.Ico
    (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
      + (supportShell ctx.shell.d ctx.shell.X).card - (ctx.n24CarryData.r + 1))
    (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
      + (supportShell ctx.shell.d ctx.shell.X).card)

/-- The boundary band is nonempty (`firstIndexAbove ≥ 1`). -/
theorem class5BoundaryBand_nonempty (ctx : ActualFailureContext) :
    (class5BoundaryBand ctx).Nonempty := by
  unfold class5BoundaryBand
  refine Finset.nonempty_Ico.mpr ?_
  have hF := n24_firstIndexAbove_pos ctx
  omega

/-- **The definitional boundary window-excess maximum** — the canonical witness for the
`M` field of `RunClass5SplitBoundary`. -/
def class5BoundaryMax (ctx : ActualFailureContext) : ℝ :=
  (class5BoundaryBand ctx).sup' (class5BoundaryBand_nonempty ctx)
    (fun k => windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
      ctx.n24CarryData.T)

/-- `class5BoundaryMax` satisfies the `hM` field of `RunClass5SplitBoundary` verbatim. -/
theorem windowExcess_le_class5BoundaryMax (ctx : ActualFailureContext) {k : ℕ}
    (hk1 : ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
        + (supportShell ctx.shell.d ctx.shell.X).card ≤ k + ctx.n24CarryData.r + 1)
    (hk2 : k < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
        + (supportShell ctx.shell.d ctx.shell.X).card) :
    windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
      ≤ class5BoundaryMax ctx := by
  have hmem : k ∈ class5BoundaryBand ctx := by
    unfold class5BoundaryBand
    rw [Finset.mem_Ico]
    omega
  unfold class5BoundaryMax
  exact Finset.le_sup'
    (fun j => windowExcess (hitGap ctx.n24CarryData.a) j ctx.n24CarryData.r
      ctx.n24CarryData.T) hmem

/-- **The boundary max sits below the canonical matched ceiling** (Part 1 pointwise). -/
theorem class5BoundaryMax_le_runDyadicMult (ctx : ActualFailureContext) :
    class5BoundaryMax ctx ≤ runDyadicMult ctx := by
  unfold class5BoundaryMax
  refine Finset.sup'_le _ _ ?_
  intro k hk
  unfold class5BoundaryBand at hk
  rw [Finset.mem_Ico] at hk
  exact n24_windowExcess_le_runDyadicMult ctx hk.2

/-- **The split multiplier collapses**: `max (runDyadicMult ctx) (class5BoundaryMax ctx)
= runDyadicMult ctx`. -/
theorem class5_split_multiplier_collapse (ctx : ActualFailureContext) :
    max (runDyadicMult ctx) (class5BoundaryMax ctx) = runDyadicMult ctx :=
  max_eq_left (class5BoundaryMax_le_runDyadicMult ctx)

/-! ## Part 3.  The single-numeric bridges to the capstone `runSplit` field -/

/-- **Per-context single-numeric entry**: `RunClass5SplitBoundary ctx` from ONE Section 26
numeric at `runDyadicMult ctx` — the `M`/`hM` fields are discharged by Part 1. -/
def runSplitOfNumericAt (ctx : ActualFailureContext)
    (hnum : erdos260Constants.c0
        * ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card : ℝ)
        * runDyadicMult ctx
      ≤ (erdos260Constants.cStar * erdos260Constants.ξ / 12)
        * ((supportShell ctx.d ctx.X).card : ℝ)) :
    RunClass5SplitBoundary ctx where
  M := runDyadicMult ctx
  hM := fun k _hk1 hk2 => n24_windowExcess_le_runDyadicMult ctx hk2
  hcount := by
    rw [max_self]
    exact hnum

/-- **The single-numeric bridge — EXACTLY the capstone `runSplit` field** from the family
of Section 26 numerics at the canonical multiplier `runDyadicMult`. -/
def runSplitOfNumeric
    (hnum : ∀ ctx : ActualFailureContext,
      erdos260Constants.c0
          * ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card : ℝ)
          * runDyadicMult ctx
        ≤ (erdos260Constants.cStar * erdos260Constants.ξ / 12)
          * ((supportShell ctx.d ctx.X).card : ℝ)) :
    ∀ ctx : ActualFailureContext, RunClass5SplitBoundary ctx :=
  fun ctx => runSplitOfNumericAt ctx (hnum ctx)

/-- **The brief's literal bridge**: the capstone `runSplit` field from the family of
numerics at the split multiplier `max (runDyadicMult ctx) (class5BoundaryMax ctx)`
(equivalent to `runSplitOfNumeric` by `class5_split_multiplier_collapse`). -/
def runSplitOfBoundaryMaxNumeric
    (hnum : ∀ ctx : ActualFailureContext,
      erdos260Constants.c0
          * ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card : ℝ)
          * max (runDyadicMult ctx) (class5BoundaryMax ctx)
        ≤ (erdos260Constants.cStar * erdos260Constants.ξ / 12)
          * ((supportShell ctx.d ctx.X).card : ℝ)) :
    ∀ ctx : ActualFailureContext, RunClass5SplitBoundary ctx :=
  fun ctx =>
  { M := class5BoundaryMax ctx
    hM := fun k hk1 hk2 => windowExcess_le_class5BoundaryMax ctx hk1 hk2
    hcount := hnum ctx }

/-- Count monotonicity for the single numeric: any proved fibre-count bound `N` reduces
the numeric to its `N`-form. -/
theorem class5_numeric_of_card_le (ctx : ActualFailureContext) {N : ℕ}
    (hcard : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card ≤ N)
    (hnum : erdos260Constants.c0 * (N : ℝ) * runDyadicMult ctx
      ≤ (erdos260Constants.cStar * erdos260Constants.ξ / 12)
        * ((supportShell ctx.d ctx.X).card : ℝ)) :
    erdos260Constants.c0
        * ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card : ℝ)
        * runDyadicMult ctx
      ≤ (erdos260Constants.cStar * erdos260Constants.ξ / 12)
        * ((supportShell ctx.d ctx.X).card : ℝ) := by
  refine le_trans ?_ hnum
  have hN : ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card : ℝ)
      ≤ (N : ℝ) := by exact_mod_cast hcard
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hN erdos260Constants.c0_pos.le)
    (runDyadicMult_nonneg ctx)

/-! ## Part 4.  Gate ⟹ emptiness, and the ungatedness of every actual context -/

/-- **Gate ⟹ class-5 fibre EMPTY** (upgrades wave-2's boundary confinement): under the
K.1 numeric gate `64(r+1)(L+B+1) < 129L+64`, the class-5 floor `129L+64 ≤ 64·gW` beats
the universal ceiling `gW ≤ (r+1)(L+B+1)`, so no start qualifies. -/
theorem class5Fibre_empty_of_gate_ceiling (ctx : ActualFailureContext)
    (hnum : 64 * ((ctx.n24CarryData.r + 1)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
        < 129 * shellLadderDepth ctx + 64) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5 = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro k hk
  have hfloor : 129 * shellLadderDepth ctx + 64
      ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r :=
    ((mem_class5Fibre_iff ctx k).mp hk).2.1
  have hceil := n24_gapWindow_le_of_start ctx (class5Fibre_mem_window ctx hk).2
  have h64 : 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
      ≤ 64 * ((ctx.n24CarryData.r + 1)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) :=
    Nat.mul_le_mul_left 64 hceil
  omega

/-- `r = 0` shells: the class-5 fibre is EMPTY (the gate is automatic). -/
theorem class5Fibre_empty_of_r_eq_zero (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5 = ∅ :=
  class5Fibre_empty_of_gate_ceiling ctx (class5_gate_of_r_eq_zero ctx hr)

/-- `L ≤ 15420` shells: the class-5 fibre is EMPTY (explicit-numeral form). -/
theorem class5Fibre_empty_of_L_le (ctx : ActualFailureContext)
    (hL : shellLadderDepth ctx ≤ 15420) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5 = ∅ :=
  class5Fibre_empty_of_gate_ceiling ctx (class5_gate_of_L_le ctx hL)

/-- **FULL Run-atom closure on every gated shell** — no interior hypothesis (supersedes
wave-2's `runCoreOfGateInterior`). -/
def runCoreOfGateCeiling (ctx : ActualFailureContext)
    (hnum : 64 * ((ctx.n24CarryData.r + 1)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
        < 129 * shellLadderDepth ctx + 64) :
    RunClass5LeafSupportMaxCoreResidual ctx :=
  runCoreOfClass5FibreEmpty ctx (class5Fibre_empty_of_gate_ceiling ctx hnum)

/-- **FULL Run-atom closure on every `r = 0` shell.** -/
def runCoreOfShallowShell (ctx : ActualFailureContext)
    (hr : ctx.n24CarryData.r = 0) :
    RunClass5LeafSupportMaxCoreResidual ctx :=
  runCoreOfClass5FibreEmpty ctx (class5Fibre_empty_of_r_eq_zero ctx hr)

/-- **FULL Run-atom closure on every `L ≤ 15420` shell.** -/
def runCoreOfDepthLe (ctx : ActualFailureContext)
    (hL : shellLadderDepth ctx ≤ 15420) :
    RunClass5LeafSupportMaxCoreResidual ctx :=
  runCoreOfClass5FibreEmpty ctx (class5Fibre_empty_of_L_le ctx hL)

/-- **Every actual failure context violates the K.1 gate**: the proved pressure floor
(`chernoffClass0_highExcessStarts_nonempty`) exhibits a start whose high-excess floor
`129L+64 ≤ 64·gW` must fit under the universal ceiling `64·gW ≤ 64(r+1)(L+B+1)`. -/
theorem n24_gate_violated (ctx : ActualFailureContext) :
    129 * shellLadderDepth ctx + 64
      ≤ 64 * ((ctx.n24CarryData.r + 1)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) := by
  obtain ⟨k, hk⟩ := chernoffClass0_highExcessStarts_nonempty ctx
  have hstart : k ∈ ctx.n24CarryData.starts := (mem_highExcessStarts.mp hk).1
  have hfloor : 129 * shellLadderDepth ctx + 64
      ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r :=
    (Y_le_windowExcess_iff_gapWindow ctx k).mp (mem_highExcessStarts.mp hk).2
  have hkwin : k < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
      + (supportShell ctx.shell.d ctx.shell.X).card := by
    rw [cnlMulti_starts_eq_window, Finset.mem_Ico] at hstart
    exact hstart.2
  have hceil := n24_gapWindow_le_of_start ctx hkwin
  have h64 : 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
      ≤ 64 * ((ctx.n24CarryData.r + 1)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) :=
    Nat.mul_le_mul_left 64 hceil
  omega

/-- **Every actual failure context has carry order `r ≥ 1`** (the `r = 0` regime is
vacuous: its automatic gate contradicts `n24_gate_violated`). -/
theorem n24_r_pos (ctx : ActualFailureContext) : 1 ≤ ctx.n24CarryData.r := by
  by_contra h
  have hr : ctx.n24CarryData.r = 0 := by omega
  have hgate := class5_gate_of_r_eq_zero ctx hr
  have hviol := n24_gate_violated ctx
  omega

/-- **Every actual failure context has ladder depth `L ≥ 15421`** (numeral form of
`n24_r_pos` through the `r = ⌊κL⌋` pin). -/
theorem shellLadderDepth_ge_15421 (ctx : ActualFailureContext) :
    15421 ≤ shellLadderDepth ctx := by
  by_contra h
  have hr := n24_r_eq_zero_of_L_le ctx (by omega)
  have hpos := n24_r_pos ctx
  omega

/-- **The ungated-numeric bridge** — the sharpest single-numeric entry: the Section 26
numeric is required only GIVEN the (automatically true) gate violation. -/
def runSplitOfUngatedNumeric
    (hnum : ∀ ctx : ActualFailureContext,
      129 * shellLadderDepth ctx + 64
        ≤ 64 * ((ctx.n24CarryData.r + 1)
            * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
      erdos260Constants.c0
          * ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card : ℝ)
          * runDyadicMult ctx
        ≤ (erdos260Constants.cStar * erdos260Constants.ξ / 12)
          * ((supportShell ctx.d ctx.X).card : ℝ)) :
    ∀ ctx : ActualFailureContext, RunClass5SplitBoundary ctx :=
  fun ctx => runSplitOfNumericAt ctx (hnum ctx (n24_gate_violated ctx))

/-! ## Part 5.  The class-5 cycle-density count bound and cycle-check closures -/

/-- The recurrent orbit value at any positive index equals its value at the residue index
`(k−1) % c + 1 ∈ [1, c]` of any period `c` valid from index `1`. -/
theorem slopeOrbit_eq_residue {q K₀ c : ℕ} (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m → slopeOrbit q K₀ (m + c) = slopeOrbit q K₀ m)
    {k : ℕ} (hk : 1 ≤ k) :
    slopeOrbit q K₀ k = slopeOrbit q K₀ ((k - 1) % c + 1) := by
  have hiter : ∀ t m : ℕ, 1 ≤ m → slopeOrbit q K₀ (m + t * c) = slopeOrbit q K₀ m := by
    intro t
    induction t with
    | zero => intro m _; simp
    | succ t ih =>
        intro m hm
        have he : m + (t + 1) * c = m + t * c + c := by ring
        rw [he, hper (m + t * c) (by omega), ih m hm]
  have hsplit : (k - 1) / c * c + (k - 1) % c = k - 1 := Nat.div_add_mod' (k - 1) c
  have hkey : (k - 1) % c + 1 + (k - 1) / c * c = k := by omega
  conv_lhs => rw [← hkey]
  exact hiter ((k - 1) / c) ((k - 1) % c + 1) (by omega)

/-- **The class-5 cycle band**: the residue indices `j ∈ [1, c]` of one orbit period whose
band is `1` (the `run` window `q < 2K`) or `4` (the `cnlTail` window `8K ≤ q < 16K`) —
the only bands class-5 routing can fire on (`class5Fibre_band_pin`). -/
def class5CycleBand (ctx : ActualFailureContext) (c : ℕ) : Finset ℕ :=
  (Finset.Icc 1 c).filter (fun j =>
    canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) = 1
      ∨ canonGap (class1SlopeDatum ctx).q
          (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) = 4)

theorem mem_class5CycleBand (ctx : ActualFailureContext) {c j : ℕ} :
    j ∈ class5CycleBand ctx c
      ↔ (1 ≤ j ∧ j ≤ c)
        ∧ (canonGap (class1SlopeDatum ctx).q
              (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) = 1
          ∨ canonGap (class1SlopeDatum ctx).q
              (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) = 4) := by
  unfold class5CycleBand
  rw [Finset.mem_filter, Finset.mem_Icc]

/-- Same residue and same window block force equality (the injectivity core of the
cycle-density count; `≤`-ordered form). -/
private theorem window_residue_block_inj {c F k₁ k₂ : ℕ} (hc : 1 ≤ c)
    (h₁1 : 1 ≤ k₁) (h₁F : F ≤ k₁) (h₂F : F ≤ k₂) (hle : k₁ ≤ k₂)
    (hmod : (k₁ - 1) % c = (k₂ - 1) % c)
    (hdiv : (k₁ - F) / c = (k₂ - F) / c) :
    k₁ = k₂ := by
  have hdvd : c ∣ (k₂ - 1) - (k₁ - 1) := (Nat.modEq_iff_dvd' (by omega)).mp hmod
  have hsub : (k₂ - 1) - (k₁ - 1) = k₂ - k₁ := by omega
  rw [hsub] at hdvd
  obtain ⟨u, hu⟩ := hdvd
  rcases Nat.eq_zero_or_pos u with rfl | hupos
  · omega
  · exfalso
    have hcu : c ≤ c * u := Nat.le_mul_of_pos_right c hupos
    have hA₁ : c * ((k₁ - F) / c) + (k₁ - F) % c = k₁ - F := Nat.div_add_mod _ _
    have hA₂ : c * ((k₂ - F) / c) + (k₂ - F) % c = k₂ - F := Nat.div_add_mod _ _
    rw [hdiv] at hA₁
    have hm₂ : (k₂ - F) % c < c := Nat.mod_lt _ (by omega)
    omega

/-- **The class-5 cycle-density count bound**: for any orbit period `c` valid from index
`1`, the class-5 fibre injects into (band-{1,4} cycle residues) × (window blocks):
`#fibre₅ ≤ #class5CycleBand · ⌈W/c⌉` with `⌈W/c⌉ = (W + c − 1)/c`, `W = |supportShell|`. -/
theorem class5Fibre_card_le_cycleDensity (ctx : ActualFailureContext) {c : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card
      ≤ (class5CycleBand ctx c).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c) := by
  classical
  have hW1 : 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card :=
    le_trans (Nat.le_add_left 1 ctx.n24CarryData.r) (cnlMulti_r_add_one_le_width ctx)
  have hmaps : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5,
      ((k - 1) % c + 1,
        (k - ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X) / c)
        ∈ (class5CycleBand ctx c) ×ˢ
            Finset.range
              (((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c) := by
    intro k hk
    have hk1 : 1 ≤ k := n24_starts_pos ctx ((mem_class5Fibre_iff ctx k).mp hk).1
    have hwin := class5Fibre_mem_window ctx hk
    rw [Finset.mem_product]
    constructor
    · rw [mem_class5CycleBand]
      have hmodlt : (k - 1) % c < c := Nat.mod_lt _ (by omega)
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      have heq := slopeOrbit_eq_residue hc hper hk1
      rcases class5Fibre_band_pin ctx hk with h1 | ⟨h4, _⟩
      · exact Or.inl (by rw [← heq]; exact h1)
      · exact Or.inr (by rw [← heq]; exact h4)
    · rw [Finset.mem_range]
      have hdle : (k - ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X) / c
          ≤ ((supportShell ctx.shell.d ctx.shell.X).card - 1) / c :=
        Nat.div_le_div_right (by omega)
      have hceil : ((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c
          = ((supportShell ctx.shell.d ctx.shell.X).card - 1) / c + 1 := by
        have he : (supportShell ctx.shell.d ctx.shell.X).card + c - 1
            = ((supportShell ctx.shell.d ctx.shell.X).card - 1) + c := by omega
        rw [he, Nat.add_div_right _ (by omega)]
      omega
  have hinj : Set.InjOn (fun k : ℕ =>
      ((k - 1) % c + 1,
        (k - ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X) / c))
      (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5) := by
    intro k₁ hk₁ k₂ hk₂ heq
    have hk₁' := Finset.mem_coe.mp hk₁
    have hk₂' := Finset.mem_coe.mp hk₂
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hmod1, hdiv⟩ := heq
    have hmod : (k₁ - 1) % c = (k₂ - 1) % c := by omega
    have h1F := (class5Fibre_mem_window ctx hk₁').1
    have h2F := (class5Fibre_mem_window ctx hk₂').1
    have h11 : 1 ≤ k₁ := n24_starts_pos ctx ((mem_class5Fibre_iff ctx k₁).mp hk₁').1
    have h21 : 1 ≤ k₂ := n24_starts_pos ctx ((mem_class5Fibre_iff ctx k₂).mp hk₂').1
    rcases le_total k₁ k₂ with hle | hle
    · exact window_residue_block_inj hc h11 h1F h2F hle hmod hdiv
    · exact (window_residue_block_inj hc h21 h2F h1F hle hmod.symm hdiv.symm).symm
  calc (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card
      ≤ ((class5CycleBand ctx c) ×ˢ
          Finset.range
            (((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c)).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ = (class5CycleBand ctx c).card
        * (((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c) := by
        rw [Finset.card_product, Finset.card_range]

/-- The cycle-density bound at SOME period `c ≤ q` — unconditional existence via
`class1Fibre_orbit_period_exists`. -/
theorem class5Fibre_card_le_cycleDensity_exists (ctx : ActualFailureContext) :
    ∃ c : ℕ, 1 ≤ c ∧ c ≤ (class1SlopeDatum ctx).q ∧
      (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5).card
        ≤ (class5CycleBand ctx c).card
          * (((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c) := by
  obtain ⟨c, hc1, hcq, hper⟩ := class1Fibre_orbit_period_exists ctx
  exact ⟨c, hc1, hcq, class5Fibre_card_le_cycleDensity ctx hc1 hper⟩

/-- **The finite cycle-check closure**: a period avoiding band `1` AND band `4` empties
the class-5 fibre (the class-5 analogue of `class1Fibre_empty_of_cycle_band_free`; at most
`q` canonical-gap evaluations per context). -/
theorem class5Fibre_empty_of_cycle_band_free (ctx : ActualFailureContext) {c : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hband : ∀ j, 1 ≤ j → j ≤ c →
      canonGap (class1SlopeDatum ctx).q
          (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) ≠ 1
        ∧ canonGap (class1SlopeDatum ctx).q
            (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) ≠ 4) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5 = ∅ := by
  have hempty : class5CycleBand ctx c = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro j hj
    rw [mem_class5CycleBand] at hj
    obtain ⟨⟨hj1, hjc⟩, hor⟩ := hj
    obtain ⟨hne1, hne4⟩ := hband j hj1 hjc
    rcases hor with h | h
    · exact hne1 h
    · exact hne4 h
  have hcard := class5Fibre_card_le_cycleDensity ctx hc hper
  rw [hempty, Finset.card_empty, Nat.zero_mul] at hcard
  exact Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)

/-- **Fixed-point cycle closure**: if the orbit is constant from index `1` on (period
`c = 1`) with band neither `1` nor `4`, the class-5 fibre is empty. -/
theorem class5Fibre_empty_of_orbit_fixed (ctx : ActualFailureContext)
    (hfix : slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 2
      = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 1)
    (h1 : canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 1) ≠ 1)
    (h4 : canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 1) ≠ 4) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5 = ∅ := by
  refine class5Fibre_empty_of_cycle_band_free ctx (c := 1) le_rfl ?_ ?_
  · intro m hm
    have hsh := slopeOrbit_eq_shift (q := (class1SlopeDatum ctx).q)
      (K₀ := (class1SlopeDatum ctx).K₀) hfix (m - 1)
    have e1 : 2 + (m - 1) = m + 1 := by omega
    have e2 : 1 + (m - 1) = m := by omega
    rw [e1, e2] at hsh
    exact hsh
  · intro j hj1 hjc
    have hj : j = 1 := by omega
    rw [hj]
    exact ⟨h1, h4⟩

private theorem nat_log_two_seven : Nat.log 2 7 = 2 :=
  Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)

/-- `canonGap 21 3 = 3`: the `(21, 3)` fixed point sits in band 3 (densePack window). -/
theorem canonGap_21_3 : canonGap 21 3 = 3 := by
  unfold canonGap
  norm_num [nat_log_two_seven]

/-- The E.13 step fixes `3` at modulus `21`: `2³·3 − 21 = 3`. -/
theorem boundedSlopeStep_21_3 : boundedSlopeStep 21 3 = 3 := by
  unfold boundedSlopeStep
  rw [canonGap_21_3]
  norm_num

/-- **NEW closed modulus family `(q, K₀) = (21, 3)`**: the orbit is the fixed point `3`
(band `canonGap 21 3 = 3`, never `run`/band-1 nor heavy band-4), so the class-5 fibre is
provably EMPTY — the first cycle-check family beyond the wave-2 `q < 5` closure. -/
theorem class5Fibre_empty_of_q21_K3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 21) (hK : (class1SlopeDatum ctx).K₀ = 3) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 5 = ∅ := by
  have h1 : slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 1 = 3 := by
    have hstep : slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 1
        = boundedSlopeStep (class1SlopeDatum ctx).q
            (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 0) := rfl
    have h0 : slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 0
        = (class1SlopeDatum ctx).K₀ := rfl
    rw [hstep, h0, hq, hK, boundedSlopeStep_21_3]
  have h2 : slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 2
      = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 1 := by
    have hstep : slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 2
        = boundedSlopeStep (class1SlopeDatum ctx).q
            (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ 1) := rfl
    rw [hstep, h1, hq, boundedSlopeStep_21_3]
  refine class5Fibre_empty_of_orbit_fixed ctx h2 ?_ ?_
  · rw [h1, hq, canonGap_21_3]
    norm_num
  · rw [h1, hq, canonGap_21_3]
    norm_num

/-- FULL Run-atom closure from a band-{1,4}-free cycle. -/
def runCoreOfCycleBandFree (ctx : ActualFailureContext) {c : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hband : ∀ j, 1 ≤ j → j ≤ c →
      canonGap (class1SlopeDatum ctx).q
          (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) ≠ 1
        ∧ canonGap (class1SlopeDatum ctx).q
            (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j) ≠ 4) :
    RunClass5LeafSupportMaxCoreResidual ctx :=
  runCoreOfClass5FibreEmpty ctx (class5Fibre_empty_of_cycle_band_free ctx hc hper hband)

/-- FULL Run-atom closure on the `(21, 3)` modulus family. -/
def runCoreOfQ21K3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 21) (hK : (class1SlopeDatum ctx).K₀ = 3) :
    RunClass5LeafSupportMaxCoreResidual ctx :=
  runCoreOfClass5FibreEmpty ctx (class5Fibre_empty_of_q21_K3 ctx hq hK)

/-- **The cycle-density numeric bridge**: the capstone `runSplit` field from a per-context
period together with the Section 26 numeric at the CYCLE-DENSITY count bound
`#class5CycleBand · ⌈W/c⌉` (a finite per-(q,K₀) surface) instead of the raw fibre count. -/
def runSplitOfCycleNumeric
    (h : ∀ ctx : ActualFailureContext, ∃ c : ℕ, 1 ≤ c ∧
      (∀ m, 1 ≤ m →
        slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
          = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m) ∧
      erdos260Constants.c0
          * (((class5CycleBand ctx c).card
              * (((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c) : ℕ) : ℝ)
          * runDyadicMult ctx
        ≤ (erdos260Constants.cStar * erdos260Constants.ξ / 12)
          * ((supportShell ctx.d ctx.X).card : ℝ)) :
    ∀ ctx : ActualFailureContext, RunClass5SplitBoundary ctx :=
  fun ctx =>
    runSplitOfNumericAt ctx
      (class5_numeric_of_card_le ctx
        (class5Fibre_card_le_cycleDensity ctx (h ctx).choose_spec.1
          (h ctx).choose_spec.2.1)
        (h ctx).choose_spec.2.2)

/-! ## Part 6.  Honest status -/

/-- The precise status of the Run / class 5 atom after this wave-3 module. -/
def runClass5BoundaryClosureStatus : List String :=
  [ "KEYSTONE (NEW; overturns the wave-2 obstruction): n24_hitGap_le_of_scale - the " ++
      "dyadic gap ceiling L+B+1 holds at EVERY index whose gap START is within scale " ++
      "(a j + L+B+3 <= 4X), with no window hypothesis: a longer gap contains the zero " ++
      "sub-run (a j, a j + (L+B+1)] whose carry doubling 2^h <= Q(N+h+2) " ++
      "(zero_gap_len_le_dyadic_scale) gives L+B+1 <= L+B. The wave-2 claim that the " ++
      "boundary windows escape every formalized hit ceiling is therefore RETIRED: the " ++
      "dyadic principle is self-referential (the run's end is its start plus its length).",
    "CLOSED (boundary ceiling chain): n24_window_scale ((r+1)(L+B+1)+2 <= 2X, from " ++
      "r <= L, B+25 <= L, L >= 28, and L^2-vs-2^L), n24_boundary_a_le (positions " ++
      "a(F+W-1+m) <= 2X + m(L+B+1) for m <= r), n24_boundary_hitGap_le, " ++
      "n24_hitGap_le_reach (every j < F+W+r), n24_gapWindow_le_of_start (EVERY start: " ++
      "gapWindow <= (r+1)(L+B+1)), n24_windowExcess_le_runDyadicMult (EVERY start: " ++
      "windowExcess <= runDyadicMult, ungated, interior-free), " ++
      "runBaseMaxExcess_le_runDyadicMult_uncond (the K.1 interior side condition of " ++
      "RunSupportMaxCore is removable).",
    "CLOSED (M/hM eliminated definitionally AND collapsed): class5BoundaryBand / " ++
      "class5BoundaryMax (sup' of windowExcess over the top r+1 band) with " ++
      "windowExcess_le_class5BoundaryMax discharging hM verbatim; the ceiling gives " ++
      "class5BoundaryMax_le_runDyadicMult, so the split multiplier collapses: " ++
      "max(runDyadicMult, class5BoundaryMax) = runDyadicMult " ++
      "(class5_split_multiplier_collapse). RunClass5SplitBoundary reduces to ONE " ++
      "Section 26 numeric: runSplitOfNumeric (exact capstone runSplit type, numeric at " ++
      "runDyadicMult), runSplitOfBoundaryMaxNumeric (the brief's literal max-form), " ++
      "runSplitOfNumericAt (per-ctx), class5_numeric_of_card_le (count monotonicity).",
    "CLOSED (gate => EMPTY; upgrades wave-2 boundary confinement |fibre5| <= r+1 and " ++
      "the r = 0 pin <= 1): class5Fibre_empty_of_gate_ceiling - under " ++
      "64(r+1)(L+B+1) < 129L+64 the class-5 floor beats the universal ceiling, so the " ++
      "fibre is EMPTY; class5Fibre_empty_of_r_eq_zero / class5Fibre_empty_of_L_le; " ++
      "FULL Run-atom closures runCoreOfGateCeiling / runCoreOfShallowShell / " ++
      "runCoreOfDepthLe (no interior hypothesis - supersedes runCoreOfGateInterior).",
    "CLOSED (ungatedness of every actual context - assembly-level intel): " ++
      "n24_gate_violated - the proved pressure floor " ++
      "(chernoffClass0_highExcessStarts_nonempty) plus the universal ceiling force " ++
      "129L+64 <= 64(r+1)(L+B+1) at EVERY ActualFailureContext; hence n24_r_pos " ++
      "(r >= 1 everywhere) and shellLadderDepth_ge_15421 (L >= 15421 everywhere): the " ++
      "whole r = 0 / L <= 15420 regime of EVERY atom is vacuous. Sanity audit per the " ++
      "wave brief: this proves all-classes-emptiness ONLY at gated shells, which are " ++
      "thereby shown nonexistent (the manuscript's intended K.1 outcome); at the " ++
      "surviving ungated shells floor and ceiling are compatible and class fibres " ++
      "persist. Entry runSplitOfUngatedNumeric: the residual numeric is needed only " ++
      "GIVEN the (automatic) gate violation.",
    "CLOSED (cycle-density count bound): slopeOrbit_eq_residue (orbit value = value at " ++
      "residue (k-1) % c + 1), class5CycleBand (band-{1,4} residues of one period, a " ++
      "finite per-(q,K0) readout), class5Fibre_card_le_cycleDensity (#fibre5 <= " ++
      "#class5CycleBand * ceil(W/c), by injection into residues x window blocks), " ++
      "existential form class5Fibre_card_le_cycleDensity_exists (some period c <= q, " ++
      "from class1Fibre_orbit_period_exists).",
    "CLOSED (finite cycle-check closures): class5Fibre_empty_of_cycle_band_free (a " ++
      "band-1-AND-4-free period empties the fibre; <= q gap evaluations per ctx), " ++
      "fixed-point form class5Fibre_empty_of_orbit_fixed, and the NEW closed modulus " ++
      "family (q, K0) = (21, 3) (class5Fibre_empty_of_q21_K3: orbit fixed at 3 with " ++
      "band canonGap 21 3 = 3) - the first family beyond the wave-2 q < 5 closure; " ++
      "runCoreOfCycleBandFree / runCoreOfQ21K3; combined entry runSplitOfCycleNumeric " ++
      "(numeric at the cycle-density count).",
    "NOT CLOSED (the honest single-numeric residual): forall ctx, c0 * #fibre5 * " ++
      "runDyadicMult ctx <= (cStar*xi/12) * |supportShell| - needed exactly on the " ++
      "(automatically) ungated shells, where runDyadicMult >= Y = L/64 > 0, so it " ++
      "cannot collapse to 0 <= nonneg. Not derivable from formalized content: the " ++
      "failure hypothesis bounds |supportShell| from ABOVE (< c0*X) with no lower " ++
      "bound against #fibre5 * runDyadicMult, and the cycle-density route closes it " ++
      "only when c0 * #class5CycleBand * runDyadicMult <~ (cStar*xi/12) * c per " ++
      "(q, K0, L) family - a finite check, not a universal theorem. This is the " ++
      "manuscript's irreducible Section 26 positive-density input, now carried by ONE " ++
      "scalar inequality with every windowExcess quantity eliminated." ]

theorem runClass5BoundaryClosureStatus_nonempty :
    runClass5BoundaryClosureStatus ≠ [] := by
  simp [runClass5BoundaryClosureStatus]

/-! ## Part 7.  Axiom-cleanliness audit -/

#print axioms n24_hitGap_le_of_scale
#print axioms n24_window_scale
#print axioms n24_boundary_a_le
#print axioms n24_boundary_hitGap_le
#print axioms n24_hitGap_le_reach
#print axioms n24_gapWindow_le_of_start
#print axioms n24_windowExcess_le_runDyadicMult
#print axioms runBaseMaxExcess_le_runDyadicMult_uncond
#print axioms class5BoundaryBand_nonempty
#print axioms windowExcess_le_class5BoundaryMax
#print axioms class5BoundaryMax_le_runDyadicMult
#print axioms class5_split_multiplier_collapse
#print axioms runSplitOfNumericAt
#print axioms runSplitOfNumeric
#print axioms runSplitOfBoundaryMaxNumeric
#print axioms class5_numeric_of_card_le
#print axioms class5Fibre_empty_of_gate_ceiling
#print axioms class5Fibre_empty_of_r_eq_zero
#print axioms class5Fibre_empty_of_L_le
#print axioms runCoreOfGateCeiling
#print axioms runCoreOfShallowShell
#print axioms runCoreOfDepthLe
#print axioms n24_gate_violated
#print axioms n24_r_pos
#print axioms shellLadderDepth_ge_15421
#print axioms runSplitOfUngatedNumeric
#print axioms slopeOrbit_eq_residue
#print axioms class5Fibre_card_le_cycleDensity
#print axioms class5Fibre_card_le_cycleDensity_exists
#print axioms class5Fibre_empty_of_cycle_band_free
#print axioms class5Fibre_empty_of_orbit_fixed
#print axioms canonGap_21_3
#print axioms boundedSlopeStep_21_3
#print axioms class5Fibre_empty_of_q21_K3
#print axioms runCoreOfCycleBandFree
#print axioms runCoreOfQ21K3
#print axioms runSplitOfCycleNumeric
#print axioms runClass5BoundaryClosureStatus_nonempty

end

end Erdos260
