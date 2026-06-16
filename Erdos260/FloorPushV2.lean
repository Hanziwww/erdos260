import Erdos260.Erdos260TrajectoryCapstone

/-!
# Erdős 260 — floor push v2: the small-`q` split floor (wave 10)

Wave 8 (`ScaleFloorPush`) pushed the unconditional floor to `X > 2^493460` with the sharp
fire condition `17·g ≤ 2^24` and noted the generic gap honestly stays `g ≈ 2L` because
`oddpart(Q)` can reach `2^(L−27)`.  Wave 9 (`PairInstanceClosure`) recorded the payoff
thresholds `r ≥ 42 / 85 / 106 / 149` for the tower counted windows `q = 9 / 11 / 13 /
(105,52)`.

## The split (route (i)), verified

The zero-gap rigidity is ALREADY oddpart-only: `pow_two_le_oddpart_of_zero_gap` divides
out `2^t` (`supportShell_card_lower_of_gap` demands only `u·(2X+2) < 2^g` with
`Q = u·2^t`, `t ≤ X`).  And the master `q`-pin `q = oddpart(Q)·(2K₀+1)`
(`datum_q_eq_oddpartQ_mul`) with `K₀ ≥ 1` gives `3·oddpart(Q) ≤ q` at EVERY ctx.  So a
small `q` bounds `oddpart(Q)` directly and the per-context gap collapses from `2L−25` to
`L + b + 1` whenever `oddpart(Q) < 2^b` (window `u·(2X+2) < 2^(L+b+1)`, needs only
`b ≤ L`, supplied by the wave-8 floor `L ≥ 493461`).  Sharp fire `17·(L+b+1) ≤ 2^24` iff
`L ≤ 986894 − b`.

**The split floors (all proved, exact):** master `oddpart(Q) < 2^b` (or `q < 3·2^b`),
`b ≤ 493461`: `X > 2^(986894−b)`.  Instances: `q ≤ 2^20` → `X > 2^986875`, `L ≥ 986876`,
`r ≥ 63`, `m₀ ≥ 3`; `q ≤ 2^15421` → `X > 2^971474`, `r ≥ 63`; `q ≤ 2^339246` →
`X > 2^647649`, `L ≥ 647650`, `r ≥ 42`; per-pair: `q = 9` (`u ≤ 3`) → `X > 2^986892`;
`q = 11 / 13 / (105,52)` (`u = 1` forced) → `X > 2^986893`; `q = 15` (`u ≤ 5`) →
`X > 2^986891`; `q = 63` (`u ≤ 21`) → `X > 2^986889`; `q = 105` (`u ≤ 35`) →
`X > 2^986888`; dyadic value `1/2^t` (`u = 1`) → `X > 2^986893` (was `2^986891`).

**The honest cap**: the sharp fire condition caps the void region at `L ≤ 986893` even at
`u = 1` (`g ≥ L+2`), so the deepest reachable floor is `L ≥ 986894` and the deepest
reachable order bound is `r = ⌊17L/2^18⌋ ≥ 63` (`r ≥ 64` needs `L ≥ 986896` — OUT of
reach of this comparison).  Hence the `q = 9` payoff threshold (`r ≥ 42`) IS crossed, but
the `q = 11 / 13 / (105,52)` thresholds (`r ≥ 85 / 106 / 149`) are NOT reachable by any
oddpart-route floor.

## What the crossed threshold honestly does (NOT a closure)

`r ≥ 63` at every `q ≤ 2^20` context forces `m₀ = ⌈3(r+1)/64⌉ ≥ 3` there.  The wave-3
`q = 9` count closure (`class2CycleInequality_of_modulus_nine`) fires on `m₀ ≤ 2`, so its
closure window `[32, 41]` is now EMPTY (`floorPushV2_q9_count_window_empty`): the `q = 9`
escape guard `3 ≤ m₀` of `TowerModulusEnumEscape` is a THEOREM at `q = 9` contexts
(`floorPushV2_q9_demand_everywhere`).  **"Voiding the `q = 9` window" therefore does NOT
close the pair** — it kills the count-bound route at `q = 9` and leaves the cycle
inequality demanded at EVERY `q = 9` context; the demand sharpens to voiding the contexts
themselves (their value pins are `4/2^t` (`u = 1`, dyadic) and `1/(3·2^t)` (`u = 3`), open
beyond the floors above).  The `q = 11 / 13 / (105,52)` windows merely NARROW to
`[63, 84] / [63, 105] / [63, 148]` (still live).  The class-0 19 survivors and class-1 23
pairs carry r-independent residue congruences (verified shapes: `Class0SurvivorResidueMiss`
concludes `k % c ≠ ρ`; `63@10` concludes `k % 2 = 0` — no `r` in any conclusion), so
`r ≥ 63` closes none of them; Run/DensePack ⌈W/c⌉-obstructions get HARDER as `r` grows.

## The `q = 63` crossover (route (ii))

`q = 63` is both a surviving exceptional cofactor (`ord_63(2) = 6`, proved exactly) and
the open class-1 pair `63@10`.  Assembled here: the divisor pin `K₀ ∈ {1,3,4,10,31}`,
the oddpart pin `oddpart(Q) ∈ {1,3,7,9,21}`, the split floor `X > 2^986889` (at `63@10`:
`oddpart(Q) = 3`, `Q = 3·2^t`, `value = 10/(3·2^t)`, `X > 2^986892`), `r ≥ 63`, and the
cycle gap-sum parity: every period of a `q = 63` orbit has `2 ∣ G` or `3 ∣ G` (the order
cofactor divides `63`, and every divisor `≥ 2` of `63` is divisible by `3` or `7`, whose
orders are `2` and `3`).

## The successor surface

`Erdos260FloorPushV2Residual` — the wave-9 `Erdos260TrajectoryResidual` with the (now
theorem) `q = 9` escape guard `3 ≤ m₀` DROPPED from `TowerModulusEnumEscape`
(`TowerModulusEnumEscapeV2`, pointwise equivalent at actual contexts:
`towerModulusEnumEscape_iff_v2`).  Bridges both ways, endpoint
`erdos260_of_floorPushV2`, `Nonempty` equivalence.  The pushed dyadic deep lever moves
`2^986891 → 2^986893` (`DeepDyadicValueLeverPushV2`, equivalent to the wave-8 lever).

Additive only: no existing file is edited; only existing public lemmas are consumed.
No `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 1.  The oddpart window bound and the split-floor masters -/

/-- **The collapsed window bound**: `oddpart < 2^b` (with `b ≤ L`, `X = 2^L`) gives
`u·(2X+2) < 2^(L+b+1)` — the per-context gap drops from the generic `2L−25` to `L+b+1`. -/
theorem floorPushV2_window_bound {u b L X : ℕ} (hu : u < 2 ^ b) (hbL : b ≤ L)
    (hX : X = 2 ^ L) : u * (2 * X + 2) < 2 ^ (L + b + 1) := by
  have hBA : (2 : ℕ) ^ (b + 1) ≤ 2 ^ (L + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2X : 2 * X + 2 = 2 ^ (L + 1) + 2 := by
    rw [hX, pow_succ]
    ring
  have hexp : (2 : ℕ) ^ (L + b + 1) = 2 ^ b * 2 ^ (L + 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [h2X, hexp]
  have hchain : u * (2 ^ (L + 1) + 2) + (2 ^ (L + 1) + 2)
      ≤ 2 ^ b * 2 ^ (L + 1) + 2 ^ (L + 1) := by
    calc u * (2 ^ (L + 1) + 2) + (2 ^ (L + 1) + 2)
        = (u + 1) * (2 ^ (L + 1) + 2) := by ring
      _ ≤ 2 ^ b * (2 ^ (L + 1) + 2) :=
          mul_le_mul_left (show u + 1 ≤ 2 ^ b from hu) _
      _ = 2 ^ b * 2 ^ (L + 1) + 2 ^ (b + 1) := by
          rw [pow_succ]
          ring
      _ ≤ 2 ^ b * 2 ^ (L + 1) + 2 ^ (L + 1) := Nat.add_le_add_left hBA _
  generalize hA : u * (2 ^ (L + 1) + 2) = a at hchain ⊢
  generalize hD : (2 : ℕ) ^ b * 2 ^ (L + 1) = dd at hchain ⊢
  generalize hC : (2 : ℕ) ^ (L + 1) = cc at hchain
  omega

/-- **The split-floor master, value-representation form**: a representation
`value = P/(u·2^t)` with `u < 2^b` (`b ≤ 493461`, `t ≤ X`) voids every scale
`X ≤ 2^(986894−b)` — sharp fire `17·(L+b+1) ≤ 2^24` iff `L ≤ 986894−b`; the wave-8
unconditional floor `L ≥ 493461` supplies `b ≤ L` for the window. -/
theorem floorPushV2_void_of_rep_lt (ctx : ActualFailureContext) {u t b : ℕ} {P : ℤ}
    (hble : b ≤ 493461) (hu : u < 2 ^ b) (hupos : 0 < u)
    (heta : realWeightedValue (natBinaryAsReal ctx.d)
      = (P : ℝ) / ((u * 2 ^ t : ℕ) : ℝ))
    (htX : t ≤ ctx.X)
    (hXle : ctx.X ≤ 2 ^ (986894 - b)) : False := by
  obtain ⟨L, hL⟩ := ctx.hXdyadic
  have hLfloor : 493461 ≤ L := by
    have hX := scaleFloorPush_scale_lower ctx
    rw [hL] at hX
    have h := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hX
    omega
  have hLle : L ≤ 986894 - b := by
    have h2 : (2 : ℕ) ^ L ≤ 2 ^ (986894 - b) := by
      rw [← hL]
      exact hXle
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2
  have hwinN : u * (2 * ctx.X + 2) < 2 ^ (L + b + 1) :=
    floorPushV2_window_bound hu (by omega) hL
  exact supportShell_sparse_contradiction_sharp (Q := u * 2 ^ t) (u := u) (t := t)
    (P := P) (d := ctx.d) (X := ctx.X) (g := L + b + 1) (L := L)
    rfl (by positivity) ctx.hd ctx.hnonterm heta htX (by omega)
    (by exact_mod_cast hwinN) hL (by omega) (by omega) ctx.hfailure

/-- **The split-floor master, oddpart form**: any ctx with `oddpart(Q) < 2^b`
(`b ≤ 493461`) is void at `X ≤ 2^(986894−b)`. -/
theorem floorPushV2_void_of_oddpart_lt (ctx : ActualFailureContext) {b : ℕ}
    (hble : b ≤ 493461) (hu : ordCompl[2] ctx.Q < 2 ^ b)
    (hXle : ctx.X ≤ 2 ^ (986894 - b)) : False := by
  have hupos : 0 < ordCompl[2] ctx.Q := Nat.ordCompl_pos 2 ctx.hQ.ne'
  have hQfact : ctx.Q = ordCompl[2] ctx.Q * 2 ^ ctx.Q.factorization 2 := by
    have h := shell_Q_eq_oddpart_mul_pow ctx
    simpa using h
  have htX : ctx.Q.factorization 2 ≤ ctx.X := by
    have h2t : 2 ^ ctx.Q.factorization 2 ≤ ctx.Q := Nat.ordProj_le 2 ctx.hQ.ne'
    have hlt : ctx.Q.factorization 2 < 2 ^ ctx.Q.factorization 2 := Nat.lt_two_pow_self
    have hQX : ctx.Q < ctx.X := carryWord_Q_lt_X ctx
    omega
  obtain ⟨P, hP⟩ := ctx.hrational
  have heta' : realWeightedValue (natBinaryAsReal ctx.d)
      = (P : ℝ) / ((ordCompl[2] ctx.Q * 2 ^ ctx.Q.factorization 2 : ℕ) : ℝ) := by
    rw [← hQfact]
    exact hP
  exact floorPushV2_void_of_rep_lt ctx hble hu hupos heta' htX hXle

/-- The oddpart split floor as a lower bound. -/
theorem floorPushV2_oddpart_scale_lower (ctx : ActualFailureContext) {b : ℕ}
    (hble : b ≤ 493461) (hu : ordCompl[2] ctx.Q < 2 ^ b) :
    2 ^ (986894 - b) < ctx.X := by
  by_contra hcon
  push Not at hcon
  exact floorPushV2_void_of_oddpart_lt ctx hble hu hcon

/-! ## Part 2.  The `q`-side split: `3·oddpart(Q) ≤ q` at every ctx -/

/-- **The `q`-side oddpart bound**: the master pin `q = oddpart(Q)·(2K₀+1)` with
`K₀ ≥ 1` gives `3·oddpart(Q) ≤ q` at EVERY actual failure context. -/
theorem floorPushV2_three_oddpartQ_le_q (ctx : ActualFailureContext) :
    3 * ordCompl[2] ctx.Q ≤ (class1SlopeDatum ctx).q := by
  have h := datum_q_eq_oddpartQ_mul ctx
  simp only [ActualFailureContext.shell_Q] at h
  have hK := (class1SlopeDatum ctx).hK₀_pos
  have h3 : 3 ≤ 2 * (class1SlopeDatum ctx).K₀ + 1 := by omega
  calc 3 * ordCompl[2] ctx.Q
      ≤ (2 * (class1SlopeDatum ctx).K₀ + 1) * ordCompl[2] ctx.Q :=
        mul_le_mul_left h3 _
    _ = ordCompl[2] ctx.Q * (2 * (class1SlopeDatum ctx).K₀ + 1) := Nat.mul_comm _ _
    _ = (class1SlopeDatum ctx).q := h.symm

/-- **The split-floor master, `q`-side form**: any ctx with `q < 3·2^b` (`b ≤ 493461`)
is void at `X ≤ 2^(986894−b)`. -/
theorem floorPushV2_void_of_q_lt (ctx : ActualFailureContext) {b : ℕ}
    (hble : b ≤ 493461) (hq : (class1SlopeDatum ctx).q < 3 * 2 ^ b)
    (hXle : ctx.X ≤ 2 ^ (986894 - b)) : False := by
  have h3 := floorPushV2_three_oddpartQ_le_q ctx
  have hu : ordCompl[2] ctx.Q < 2 ^ b :=
    Nat.lt_of_mul_lt_mul_left (lt_of_le_of_lt h3 hq)
  exact floorPushV2_void_of_oddpart_lt ctx hble hu hXle

/-! ## Part 3.  Depth and order harvest plumbing -/

/-- A scale lower bound pins the ladder depth. -/
theorem floorPushV2_depth_lower (ctx : ActualFailureContext) {E : ℕ}
    (hX : 2 ^ E < ctx.X) : E + 1 ≤ shellLadderDepth ctx := by
  have hXeq : ctx.shell.X = 2 ^ shellLadderDepth ctx :=
    Classical.choose_spec ctx.shell.hXdyadic
  rw [ActualFailureContext.shell_X] at hXeq
  rw [hXeq] at hX
  have h := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hX
  omega

/-- A depth lower bound pins the descent order through `r = ⌊κL⌋`, `κ = 17/2^18`:
`m·2^18 ≤ 17·D ≤ 17·L` gives `r ≥ m`. -/
theorem floorPushV2_r_lower (ctx : ActualFailureContext) {m D : ℕ}
    (hD : D ≤ shellLadderDepth ctx) (hm : m * 262144 ≤ 17 * D) :
    m ≤ ctx.n24CarryData.r := by
  have hL : (D : ℝ) ≤ (shellLadderDepth ctx : ℝ) := by exact_mod_cast hD
  have hm' : (m : ℝ) * 262144 ≤ 17 * (D : ℝ) := by exact_mod_cast hm
  have hgoal : (m : ℝ) ≤ manuscriptKappa * (shellLadderDepth ctx : ℝ) := by
    rw [towerKappa_eq]
    linarith
  rw [n24CarryData_r_eq_floor ctx]
  exact Nat.le_floor hgoal

/-! ## Part 4.  The small-`q` floors with exact constants -/

/-- **The `q ≤ 2^20` split floor (the headline conditional floor)**: contexts with
`q ≤ 1048576` are void at `X ≤ 2^986875` — `3u ≤ q ≤ 2^20` gives `u ≤ 349525 < 2^19`. -/
theorem floorPushV2_void_of_q_le_2pow20 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q ≤ 1048576) (hXle : ctx.X ≤ 2 ^ 986875) : False := by
  refine floorPushV2_void_of_q_lt ctx (b := 19) (by norm_num) ?_ ?_
  · have h19 : 3 * (2 : ℕ) ^ 19 = 1572864 := by norm_num
    omega
  · have he : (986894 - 19 : ℕ) = 986875 := by norm_num
    rw [he]
    exact hXle

/-- The `q ≤ 2^20` floor as a lower bound: `X > 2^986875`. -/
theorem floorPushV2_scale_lower_of_q_le_2pow20 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q ≤ 1048576) : 2 ^ 986875 < ctx.X := by
  by_contra hcon
  push Not at hcon
  exact floorPushV2_void_of_q_le_2pow20 ctx hq hcon

/-- `q ≤ 2^20` forces ladder depth `L ≥ 986876`. -/
theorem floorPushV2_depth_of_q_le_2pow20 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q ≤ 1048576) : 986876 ≤ shellLadderDepth ctx :=
  floorPushV2_depth_lower ctx (floorPushV2_scale_lower_of_q_le_2pow20 ctx hq)

/-- **`q ≤ 2^20` forces `r ≥ 63`** — `63·2^18 = 16515072 ≤ 17·986876 = 16776892`.
(Honest cap: `r ≥ 64` needs `L ≥ 986896`, out of reach of the sharp fire condition even
at `oddpart(Q) = 1`.) -/
theorem floorPushV2_r_ge_63_of_q_le_2pow20 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q ≤ 1048576) : 63 ≤ ctx.n24CarryData.r :=
  floorPushV2_r_lower ctx (floorPushV2_depth_of_q_le_2pow20 ctx hq) (by norm_num)

/-- `q ≤ 2^20` forces the sparsity block `m₀ ≥ 3`. -/
theorem floorPushV2_m0_ge_three_of_q_le_2pow20 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q ≤ 1048576) : 3 ≤ towerSparsityBlock ctx := by
  have hr := floorPushV2_r_ge_63_of_q_le_2pow20 ctx hq
  unfold towerSparsityBlock
  omega

/-- **The widest `r ≥ 63` band**: contexts with `q ≤ 2^15421` are void at
`X ≤ 2^971474`, hence have `L ≥ 971475` and `r ≥ 63` (sharp: `63·2^18 = 16515072 ≤
17·971475 = 16515075`). -/
theorem floorPushV2_void_of_q_le_2pow15421 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q ≤ 2 ^ 15421) (hXle : ctx.X ≤ 2 ^ 971474) : False := by
  refine floorPushV2_void_of_q_lt ctx (b := 15420) (by norm_num) ?_ ?_
  · calc (class1SlopeDatum ctx).q ≤ 2 ^ 15421 := hq
      _ = 2 * 2 ^ 15420 := by rw [pow_succ]; ring
      _ < 3 * 2 ^ 15420 := by
          have hpos : (0 : ℕ) < 2 ^ 15420 := by positivity
          omega
  · have he : (986894 - 15420 : ℕ) = 971474 := by norm_num
    rw [he]
    exact hXle

/-- `q ≤ 2^15421` forces `r ≥ 63`. -/
theorem floorPushV2_r_ge_63_of_q_le_2pow15421 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q ≤ 2 ^ 15421) : 63 ≤ ctx.n24CarryData.r := by
  have hlow : 2 ^ 971474 < ctx.X := by
    by_contra hcon
    push Not at hcon
    exact floorPushV2_void_of_q_le_2pow15421 ctx hq hcon
  exact floorPushV2_r_lower ctx (floorPushV2_depth_lower ctx hlow) (by norm_num)

/-- **The `q = 9` payoff band**: contexts with `q ≤ 2^339246` are void at
`X ≤ 2^647649`, hence have `L ≥ 647650` and `r ≥ 42` (sharp: `42·2^18 = 11010048 ≤
17·647650 = 11010050`) — the wave-9 `q = 9` threshold `r ≥ 42` is crossed on an
astronomically generous `q`-range. -/
theorem floorPushV2_void_of_q_le_2pow339246 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q ≤ 2 ^ 339246) (hXle : ctx.X ≤ 2 ^ 647649) : False := by
  refine floorPushV2_void_of_q_lt ctx (b := 339245) (by norm_num) ?_ ?_
  · calc (class1SlopeDatum ctx).q ≤ 2 ^ 339246 := hq
      _ = 2 * 2 ^ 339245 := by rw [pow_succ]; ring
      _ < 3 * 2 ^ 339245 := by
          have hpos : (0 : ℕ) < 2 ^ 339245 := by positivity
          omega
  · have he : (986894 - 339245 : ℕ) = 647649 := by norm_num
    rw [he]
    exact hXle

/-- `q ≤ 2^339246` forces `r ≥ 42` — the wave-9 `q = 9` payoff threshold. -/
theorem floorPushV2_r_ge_42_of_q_le_2pow339246 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q ≤ 2 ^ 339246) : 42 ≤ ctx.n24CarryData.r := by
  have hlow : 2 ^ 647649 < ctx.X := by
    by_contra hcon
    push Not at hcon
    exact floorPushV2_void_of_q_le_2pow339246 ctx hq hcon
  exact floorPushV2_r_lower ctx (floorPushV2_depth_lower ctx hlow) (by norm_num)

/-- `q ≤ 2^339246` forces `m₀ ≥ 3`. -/
theorem floorPushV2_m0_ge_three_of_q_le_2pow339246 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q ≤ 2 ^ 339246) : 3 ≤ towerSparsityBlock ctx := by
  have hr := floorPushV2_r_ge_42_of_q_le_2pow339246 ctx hq
  unfold towerSparsityBlock
  omega

/-! ## Part 5.  The per-pair tower floors (exact oddpart pins) -/

/-- `q = 9` pins `oddpart(Q) ≤ 3` (`3u ≤ 9`). -/
theorem floorPushV2_q9_oddpart_lt_four (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 9) : ordCompl[2] ctx.Q < 4 := by
  have h3 := floorPushV2_three_oddpartQ_le_q ctx
  omega

/-- **The `q = 9` floor**: void at `X ≤ 2^986892` (`u ≤ 3 < 2^2`, gap `L+3`). -/
theorem floorPushV2_void_q9 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 9) (hXle : ctx.X ≤ 2 ^ 986892) : False := by
  refine floorPushV2_void_of_oddpart_lt ctx (b := 2) (by norm_num) ?_ ?_
  · have h4 : (2 : ℕ) ^ 2 = 4 := by norm_num
    rw [h4]
    exact floorPushV2_q9_oddpart_lt_four ctx hq
  · have he : (986894 - 2 : ℕ) = 986892 := by norm_num
    rw [he]
    exact hXle

/-- The `q = 9` floor as a lower bound: `X > 2^986892`, hence `L ≥ 986893`. -/
theorem floorPushV2_q9_scale_lower (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 9) : 2 ^ 986892 < ctx.X := by
  by_contra hcon
  push Not at hcon
  exact floorPushV2_void_q9 ctx hq hcon

/-- `q = 9` forces `r ≥ 63` (`63·2^18 = 16515072 ≤ 17·986893 = 16777181`). -/
theorem floorPushV2_q9_r_ge_63 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 9) : 63 ≤ ctx.n24CarryData.r :=
  floorPushV2_r_lower ctx
    (floorPushV2_depth_lower ctx (floorPushV2_q9_scale_lower ctx hq)) (by norm_num)

/-- `q = 9` forces `m₀ ≥ 3` — the wave-5 escape guard `3 ≤ m₀` is a THEOREM at every
`q = 9` context. -/
theorem floorPushV2_q9_m0_ge_three (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 9) : 3 ≤ towerSparsityBlock ctx := by
  have hr := floorPushV2_q9_r_ge_63 ctx hq
  unfold towerSparsityBlock
  omega

/-- **The `q = 9` count-closure window `[32, 41]` is EMPTY** — the wave-3 count bound
(`class2CycleInequality_of_modulus_nine`, firing on `m₀ ≤ 2`) is vacuous at every actual
`q = 9` context.  HONEST: this does NOT close the pair; it kills the count route. -/
theorem floorPushV2_q9_count_window_empty (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 9) : ¬ towerSparsityBlock ctx ≤ 2 := by
  have h := floorPushV2_q9_m0_ge_three ctx hq
  omega

/-- **Every `q = 9` context is a `TowerModulusEnumEscape` context** — the residual cycle
inequality is demanded at ALL of them (the wave-9 dichotomy's closure branch is dead). -/
theorem floorPushV2_q9_demand_everywhere (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 9) : TowerModulusEnumEscape ctx :=
  Or.inl ⟨hq, floorPushV2_q9_m0_ge_three ctx hq⟩

/-- `q = 11` forces `oddpart(Q) = 1` (the only odd part compatible with `3u ≤ 11` and
`u·(2K₀+1) = 11`), hence `K₀ = 5` rides the full modulus. -/
theorem floorPushV2_q11_oddpart_eq_one (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 11) : ordCompl[2] ctx.Q = 1 := by
  have h := datum_q_eq_oddpartQ_mul ctx
  simp only [ActualFailureContext.shell_Q] at h
  rw [hq] at h
  have hupos : 0 < ordCompl[2] ctx.Q := Nat.ordCompl_pos 2 ctx.hQ.ne'
  have h3 := floorPushV2_three_oddpartQ_le_q ctx
  rw [hq] at h3
  obtain ⟨u, hu⟩ : ∃ u, ordCompl[2] ctx.Q = u := ⟨_, rfl⟩
  rw [hu] at h h3 hupos ⊢
  have hcases : u = 1 ∨ u = 2 ∨ u = 3 := by omega
  rcases hcases with rfl | rfl | rfl <;> omega

/-- **The `q = 11` floor**: void at `X ≤ 2^986893` (`u = 1`, gap `L+2` — the deepest
this comparison can reach). -/
theorem floorPushV2_void_q11 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 11) (hXle : ctx.X ≤ 2 ^ 986893) : False := by
  refine floorPushV2_void_of_oddpart_lt ctx (b := 1) (by norm_num) ?_ ?_
  · rw [floorPushV2_q11_oddpart_eq_one ctx hq]
    norm_num
  · have he : (986894 - 1 : ℕ) = 986893 := by norm_num
    rw [he]
    exact hXle

/-- The `q = 11` floor as a lower bound: `X > 2^986893`, `L ≥ 986894`. -/
theorem floorPushV2_q11_scale_lower (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 11) : 2 ^ 986893 < ctx.X := by
  by_contra hcon
  push Not at hcon
  exact floorPushV2_void_q11 ctx hq hcon

/-- `q = 13` forces `oddpart(Q) = 1`. -/
theorem floorPushV2_q13_oddpart_eq_one (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 13) : ordCompl[2] ctx.Q = 1 := by
  have h := datum_q_eq_oddpartQ_mul ctx
  simp only [ActualFailureContext.shell_Q] at h
  rw [hq] at h
  have hupos : 0 < ordCompl[2] ctx.Q := Nat.ordCompl_pos 2 ctx.hQ.ne'
  have h3 := floorPushV2_three_oddpartQ_le_q ctx
  rw [hq] at h3
  obtain ⟨u, hu⟩ : ∃ u, ordCompl[2] ctx.Q = u := ⟨_, rfl⟩
  rw [hu] at h h3 hupos ⊢
  have hcases : u = 1 ∨ u = 2 ∨ u = 3 ∨ u = 4 := by omega
  rcases hcases with rfl | rfl | rfl | rfl <;> omega

/-- **The `q = 13` floor**: void at `X ≤ 2^986893` (`u = 1`). -/
theorem floorPushV2_void_q13 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 13) (hXle : ctx.X ≤ 2 ^ 986893) : False := by
  refine floorPushV2_void_of_oddpart_lt ctx (b := 1) (by norm_num) ?_ ?_
  · rw [floorPushV2_q13_oddpart_eq_one ctx hq]
    norm_num
  · have he : (986894 - 1 : ℕ) = 986893 := by norm_num
    rw [he]
    exact hXle

/-- The `q = 13` floor as a lower bound: `X > 2^986893`. -/
theorem floorPushV2_q13_scale_lower (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 13) : 2 ^ 986893 < ctx.X := by
  by_contra hcon
  push Not at hcon
  exact floorPushV2_void_q13 ctx hq hcon

/-- `(q, K₀) = (105, 52)` forces `oddpart(Q) = 1` (`2·52+1 = 105` exhausts `q`). -/
theorem floorPushV2_q105K52_oddpart_eq_one (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 105) (hK : (class1SlopeDatum ctx).K₀ = 52) :
    ordCompl[2] ctx.Q = 1 := by
  have h := datum_q_eq_oddpartQ_mul ctx
  simp only [ActualFailureContext.shell_Q] at h
  rw [hq, hK] at h
  have h105 : 2 * 52 + 1 = 105 := by norm_num
  rw [h105] at h
  omega

/-- **The `(105, 52)` floor**: void at `X ≤ 2^986893` (`u = 1`). -/
theorem floorPushV2_void_q105K52 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 105) (hK : (class1SlopeDatum ctx).K₀ = 52)
    (hXle : ctx.X ≤ 2 ^ 986893) : False := by
  refine floorPushV2_void_of_oddpart_lt ctx (b := 1) (by norm_num) ?_ ?_
  · rw [floorPushV2_q105K52_oddpart_eq_one ctx hq hK]
    norm_num
  · have he : (986894 - 1 : ℕ) = 986893 := by norm_num
    rw [he]
    exact hXle

/-- The `(105, 52)` floor as a lower bound: `X > 2^986893`. -/
theorem floorPushV2_q105K52_scale_lower (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 105) (hK : (class1SlopeDatum ctx).K₀ = 52) :
    2 ^ 986893 < ctx.X := by
  by_contra hcon
  push Not at hcon
  exact floorPushV2_void_q105K52 ctx hq hK hcon

/-- **The `q = 15` floor**: void at `X ≤ 2^986891` (`3u ≤ 15` gives `u ≤ 5 < 2^3`). -/
theorem floorPushV2_void_q15 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 15) (hXle : ctx.X ≤ 2 ^ 986891) : False := by
  refine floorPushV2_void_of_oddpart_lt ctx (b := 3) (by norm_num) ?_ ?_
  · have h8 : (2 : ℕ) ^ 3 = 8 := by norm_num
    rw [h8]
    have h3 := floorPushV2_three_oddpartQ_le_q ctx
    omega
  · have he : (986894 - 3 : ℕ) = 986891 := by norm_num
    rw [he]
    exact hXle

/-- **The `q = 105` floor (any `K₀`)**: void at `X ≤ 2^986888` (`u ≤ 35 < 2^6`). -/
theorem floorPushV2_void_q105 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 105) (hXle : ctx.X ≤ 2 ^ 986888) : False := by
  refine floorPushV2_void_of_oddpart_lt ctx (b := 6) (by norm_num) ?_ ?_
  · have h64 : (2 : ℕ) ^ 6 = 64 := by norm_num
    rw [h64]
    have h3 := floorPushV2_three_oddpartQ_le_q ctx
    omega
  · have he : (986894 - 6 : ℕ) = 986888 := by norm_num
    rw [he]
    exact hXle

/-! ## Part 6.  The narrowed two-sided tower windows (harvest, honest)

The wave-9 closure thresholds (`r ≤ 84 / 105 / 148` for `q = 11 / 13 / (105,52)`) are
UPPER edges this lower floor cannot move; the live windows narrow to `[63, 84] /
[63, 105] / [63, 148]`.  The `q = 9` window `[32, 41]` is empty (Part 5).  NO pair
closes. -/

/-- `q = 11`: the live closure window narrows to `[63, 84]` — `r ≥ 63` AND the wave-9
count closure still fires on `r ≤ 84`. -/
theorem floorPushV2_q11_window (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 11) :
    63 ≤ ctx.n24CarryData.r
      ∧ (ctx.n24CarryData.r ≤ 84 → Class2CycleInequality ctx) :=
  ⟨floorPushV2_r_ge_63_of_q_le_2pow20 ctx (by omega),
   fun hr => tower_q11_closes_of_r_le_84 ctx hq hr⟩

/-- `q = 13`: the live closure window narrows to `[63, 105]`. -/
theorem floorPushV2_q13_window (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 13) :
    63 ≤ ctx.n24CarryData.r
      ∧ (ctx.n24CarryData.r ≤ 105 → Class2CycleInequality ctx) :=
  ⟨floorPushV2_r_ge_63_of_q_le_2pow20 ctx (by omega),
   fun hr => tower_q13_closes_of_r_le_105 ctx hq hr⟩

/-- `(105, 52)`: the live closure window narrows to `[63, 148]`. -/
theorem floorPushV2_q105K52_window (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 105) (hK : (class1SlopeDatum ctx).K₀ = 52) :
    63 ≤ ctx.n24CarryData.r
      ∧ (ctx.n24CarryData.r ≤ 148 → Class2CycleInequality ctx) :=
  ⟨floorPushV2_r_ge_63_of_q_le_2pow20 ctx (by omega),
   fun hr => tower_q105_K₀52_closes_of_r_le_148 ctx hq hK hr⟩

/-! ## Part 7.  The `q = 63` crossover assembly (route (ii)) -/

/-- **The `q = 63` divisor pin**: `K₀ ∈ {1, 3, 4, 10, 31}` (the odd divisors `2K₀+1` of
`63` at `K₀ ≥ 1`). -/
theorem floorPushV2_q63_K₀_pin (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) :
    (class1SlopeDatum ctx).K₀ = 1 ∨ (class1SlopeDatum ctx).K₀ = 3
      ∨ (class1SlopeDatum ctx).K₀ = 4 ∨ (class1SlopeDatum ctx).K₀ = 10
      ∨ (class1SlopeDatum ctx).K₀ = 31 := by
  have hdvd := class0_datum_dvd ctx
  rw [hq] at hdvd
  have hKpos := (class1SlopeDatum ctx).hK₀_pos
  have hle : 2 * (class1SlopeDatum ctx).K₀ + 1 ≤ 63 := Nat.le_of_dvd (by norm_num) hdvd
  have key : ∀ m : ℕ, m < 32 → 1 ≤ m → (2 * m + 1) ∣ 63 →
      m = 1 ∨ m = 3 ∨ m = 4 ∨ m = 10 ∨ m = 31 := by decide
  exact key _ (by omega) hKpos hdvd

/-- **The `q = 63` oddpart pin**: `oddpart(Q) ∈ {1, 3, 7, 9, 21}` (the divisors of `63`
below `22`). -/
theorem floorPushV2_q63_oddpart_pin (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) :
    ordCompl[2] ctx.Q = 1 ∨ ordCompl[2] ctx.Q = 3 ∨ ordCompl[2] ctx.Q = 7
      ∨ ordCompl[2] ctx.Q = 9 ∨ ordCompl[2] ctx.Q = 21 := by
  have h := datum_q_eq_oddpartQ_mul ctx
  simp only [ActualFailureContext.shell_Q] at h
  rw [hq] at h
  have hdvd : ordCompl[2] ctx.Q ∣ 63 := ⟨2 * (class1SlopeDatum ctx).K₀ + 1, h⟩
  have h3 := floorPushV2_three_oddpartQ_le_q ctx
  rw [hq] at h3
  have key : ∀ m : ℕ, m < 22 → m ∣ 63 →
      m = 1 ∨ m = 3 ∨ m = 7 ∨ m = 9 ∨ m = 21 := by decide
  exact key _ (by omega) hdvd

/-- **The `q = 63` split floor**: void at `X ≤ 2^986889` (`u ≤ 21 < 2^5`). -/
theorem floorPushV2_void_q63 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) (hXle : ctx.X ≤ 2 ^ 986889) : False := by
  refine floorPushV2_void_of_oddpart_lt ctx (b := 5) (by norm_num) ?_ ?_
  · have h32 : (2 : ℕ) ^ 5 = 32 := by norm_num
    rw [h32]
    have h3 := floorPushV2_three_oddpartQ_le_q ctx
    omega
  · have he : (986894 - 5 : ℕ) = 986889 := by norm_num
    rw [he]
    exact hXle

/-- The `q = 63` floor as a lower bound: `X > 2^986889`, `L ≥ 986890`. -/
theorem floorPushV2_q63_scale_lower (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) : 2 ^ 986889 < ctx.X := by
  by_contra hcon
  push Not at hcon
  exact floorPushV2_void_q63 ctx hq hcon

/-- `q = 63` forces `r ≥ 63` (`63·2^18 = 16515072 ≤ 17·986890 = 16777130`). -/
theorem floorPushV2_q63_r_ge_63 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) : 63 ≤ ctx.n24CarryData.r :=
  floorPushV2_r_lower ctx
    (floorPushV2_depth_lower ctx (floorPushV2_q63_scale_lower ctx hq)) (by norm_num)

/-- **The `63@10` oddpart**: the open class-1 pair has `oddpart(Q) = 3` exactly. -/
theorem floorPushV2_q63K10_oddpart_eq_three (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) (hK : (class1SlopeDatum ctx).K₀ = 10) :
    ordCompl[2] ctx.Q = 3 := by
  have h := datum_q_eq_oddpartQ_mul ctx
  simp only [ActualFailureContext.shell_Q] at h
  rw [hq, hK] at h
  have h21 : 2 * 10 + 1 = 21 := by norm_num
  rw [h21] at h
  omega

/-- **The `63@10` denominator shape**: `Q = 3·2^t`. -/
theorem floorPushV2_q63K10_Q_shape (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) (hK : (class1SlopeDatum ctx).K₀ = 10) :
    ∃ t : ℕ, ctx.Q = 3 * 2 ^ t := by
  refine ⟨ctx.Q.factorization 2, ?_⟩
  have hQfact : ctx.Q = ordCompl[2] ctx.Q * 2 ^ ctx.Q.factorization 2 := by
    have h := shell_Q_eq_oddpart_mul_pow ctx
    simpa using h
  rw [floorPushV2_q63K10_oddpart_eq_three ctx hq hK] at hQfact
  exact hQfact

/-- **The `63@10` value pin**: `value = 10/(3·2^t)` — a NEW pinned-value family (not the
in-tree dyadic/fifth/thirds shapes). -/
theorem floorPushV2_q63K10_value (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) (hK : (class1SlopeDatum ctx).K₀ = 10) :
    ∃ t : ℕ, realWeightedValue (natBinaryAsReal ctx.shell.d) = 10 / (3 * 2 ^ t) := by
  obtain ⟨t, hQ⟩ := floorPushV2_q63K10_Q_shape ctx hq hK
  refine ⟨t, ?_⟩
  have hv := shell_value_eq_K₀_div_Q ctx
  rw [hK] at hv
  rw [hv]
  simp only [ActualFailureContext.shell_Q]
  rw [hQ]
  push_cast
  ring

/-- **The `63@10` floor**: void at `X ≤ 2^986892` (`u = 3 < 2^2`). -/
theorem floorPushV2_void_q63K10 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) (hK : (class1SlopeDatum ctx).K₀ = 10)
    (hXle : ctx.X ≤ 2 ^ 986892) : False := by
  refine floorPushV2_void_of_oddpart_lt ctx (b := 2) (by norm_num) ?_ ?_
  · have h4 : (2 : ℕ) ^ 2 = 4 := by norm_num
    rw [h4, floorPushV2_q63K10_oddpart_eq_three ctx hq hK]
    norm_num
  · have he : (986894 - 2 : ℕ) = 986892 := by norm_num
    rw [he]
    exact hXle

/-- The `63@10` floor as a lower bound: `X > 2^986892`, `L ≥ 986893`. -/
theorem floorPushV2_q63K10_scale_lower (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) (hK : (class1SlopeDatum ctx).K₀ = 10) :
    2 ^ 986892 < ctx.X := by
  by_contra hcon
  push Not at hcon
  exact floorPushV2_void_q63K10 ctx hq hK hcon

/-! ## Part 8.  The `q = 63` cycle gap-sum parity (the `ord_63(2) = 6` structure) -/

/-- `n ∣ 2^G − 1` lifts to `(2 : ZMod n)^G = 1`. -/
theorem floorPushV2_zmod_two_pow_eq_one {n G : ℕ} (h : n ∣ 2 ^ G - 1) :
    (2 : ZMod n) ^ G = 1 := by
  have h1 : 1 ≤ 2 ^ G := Nat.one_le_two_pow
  obtain ⟨k, hk⟩ := h
  have heq : (2 : ℕ) ^ G = n * k + 1 := by omega
  calc (2 : ZMod n) ^ G = ((2 ^ G : ℕ) : ZMod n) := by push_cast; ring
    _ = ((n * k + 1 : ℕ) : ZMod n) := by rw [heq]
    _ = 1 := by push_cast [ZMod.natCast_self]; ring

/-- `ord_3(2) = 2`. -/
theorem floorPushV2_orderOf_two_zmod3 : orderOf (2 : ZMod 3) = 2 := by
  have h2 : (2 : ZMod 3) ^ 2 = 1 := by decide
  have hdvd := orderOf_dvd_of_pow_eq_one h2
  have hmem : orderOf (2 : ZMod 3) ∈ Nat.divisors 2 :=
    Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  rw [show Nat.divisors 2 = {1, 2} from by decide] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h
  · exfalso
    have hp := pow_orderOf_eq_one (2 : ZMod 3)
    rw [h, pow_one] at hp
    exact absurd hp (by decide)
  · exact h

/-- `ord_7(2) = 3`. -/
theorem floorPushV2_orderOf_two_zmod7 : orderOf (2 : ZMod 7) = 3 := by
  have h3 : (2 : ZMod 7) ^ 3 = 1 := by decide
  have hdvd := orderOf_dvd_of_pow_eq_one h3
  have hmem : orderOf (2 : ZMod 7) ∈ Nat.divisors 3 :=
    Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  rw [show Nat.divisors 3 = {1, 3} from by decide] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h
  · exfalso
    have hp := pow_orderOf_eq_one (2 : ZMod 7)
    rw [h, pow_one] at hp
    exact absurd hp (by decide)
  · exact h

/-- **`ord_63(2) = 6` exactly** (`63 = 2^6 − 1`; no smaller exponent works). -/
theorem floorPushV2_orderOf_two_zmod63 : orderOf (2 : ZMod 63) = 6 := by
  have h6 : (2 : ZMod 63) ^ 6 = 1 := by decide
  have hdvd := orderOf_dvd_of_pow_eq_one h6
  have hmem : orderOf (2 : ZMod 63) ∈ Nat.divisors 6 :=
    Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  rw [show Nat.divisors 6 = {1, 2, 3, 6} from by decide] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hp := pow_orderOf_eq_one (2 : ZMod 63)
  rcases hmem with h | h | h | h
  · exfalso
    rw [h, pow_one] at hp
    exact absurd hp (by decide)
  · exfalso
    rw [h] at hp
    exact absurd hp (by decide)
  · exfalso
    rw [h] at hp
    exact absurd hp (by decide)
  · exact h

/-- **The `q = 63` gap-sum parity**: every cycle of a `q = 63` orbit has gap sum `G`
divisible by `2` or by `3` — the order cofactor `q' = 63/gcd(63, K₁)` divides `63`, is
`≥ 2`, hence is divisible by `3` (with `ord_3(2) = 2 ∣ G`) or by `7`
(with `ord_7(2) = 3 ∣ G`). -/
theorem floorPushV2_q63_gapSum_two_or_three_dvd {K₀ c : ℕ}
    (hK1 : 1 ≤ K₀) (hKq : K₀ < 63) (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m → slopeOrbit 63 K₀ (m + c) = slopeOrbit 63 K₀ m) :
    2 ∣ (∑ i ∈ Finset.Icc 1 c, canonGap 63 (slopeOrbit 63 K₀ i))
      ∨ 3 ∣ (∑ i ∈ Finset.Icc 1 c, canonGap 63 (slopeOrbit 63 K₀ i)) := by
  have hodd : Odd (63 : ℕ) := by decide
  have hMers : orbitOrderModulus 63 K₀
      ∣ 2 ^ (∑ i ∈ Finset.Icc 1 c, canonGap 63 (slopeOrbit 63 K₀ i)) - 1 :=
    orbitOrderModulus_dvd_two_pow_gapSum_sub_one hodd hK1 hKq hc hper
  have hdvd63 : orbitOrderModulus 63 K₀ ∣ 63 :=
    Nat.div_dvd_of_dvd (Nat.gcd_dvd_left 63 (slopeOrbit 63 K₀ 1))
  have h2le : 2 ≤ orbitOrderModulus 63 K₀ := orbitOrderModulus_two_le hodd hK1 hKq
  have hle63 : orbitOrderModulus 63 K₀ ≤ 63 := Nat.le_of_dvd (by norm_num) hdvd63
  have key : ∀ m : ℕ, m < 64 → m ∣ 63 → 2 ≤ m → 3 ∣ m ∨ 7 ∣ m := by decide
  rcases key _ (by omega) hdvd63 h2le with h3 | h7
  · left
    have h3M : (3 : ℕ)
        ∣ 2 ^ (∑ i ∈ Finset.Icc 1 c, canonGap 63 (slopeOrbit 63 K₀ i)) - 1 :=
      dvd_trans h3 hMers
    have hpow := floorPushV2_zmod_two_pow_eq_one h3M
    have hord := orderOf_dvd_of_pow_eq_one hpow
    rwa [floorPushV2_orderOf_two_zmod3] at hord
  · right
    have h7M : (7 : ℕ)
        ∣ 2 ^ (∑ i ∈ Finset.Icc 1 c, canonGap 63 (slopeOrbit 63 K₀ i)) - 1 :=
      dvd_trans h7 hMers
    have hpow := floorPushV2_zmod_two_pow_eq_one h7M
    have hord := orderOf_dvd_of_pow_eq_one hpow
    rwa [floorPushV2_orderOf_two_zmod7] at hord

/-- The `q = 63` gap-sum parity at an actual failure context. -/
theorem floorPushV2_q63_ctx_gapSum (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) {c : ℕ} (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m) :
    2 ∣ (∑ i ∈ Finset.Icc 1 c, canonGap (class1SlopeDatum ctx).q
          (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ i))
      ∨ 3 ∣ (∑ i ∈ Finset.Icc 1 c, canonGap (class1SlopeDatum ctx).q
          (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ i)) := by
  have hK1 := (class1SlopeDatum ctx).hK₀_pos
  have hKq := (class1SlopeDatum ctx).hK₀_lt
  rw [hq] at hKq hper ⊢
  exact floorPushV2_q63_gapSum_two_or_three_dvd hK1 hKq hc hper

/-! ## Part 9.  The pushed dyadic deep lever: `2^986891 → 2^986893` -/

/-- **The pushed dyadic-value voiding v2**: no failing context with `value = 1/2^t`
exists at scale `X ≤ 2^986893` (`u = 1` allows the gap `L+2`; wave 8 used `u ≤ 7`,
gap `L+4`, reaching only `2^986891`). -/
theorem shellValueDyadic_void_of_scale_pushV2 (ctx : ActualFailureContext)
    (hXle : ctx.X ≤ 2 ^ 986893) : ¬ ShellValueDyadic ctx := by
  rintro ⟨t, hdy⟩
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
  have htX : t ≤ ctx.X := by
    have hlt : t < 2 ^ t := Nat.lt_two_pow_self
    have hQX : ctx.Q < ctx.X := carryWord_Q_lt_X ctx
    omega
  have heta' : realWeightedValue (natBinaryAsReal ctx.d)
      = ((1 : ℤ) : ℝ) / ((1 * 2 ^ t : ℕ) : ℝ) := by
    rw [show realWeightedValue (natBinaryAsReal ctx.d) = 1 / 2 ^ t from hdy]
    push_cast
    ring
  refine floorPushV2_void_of_rep_lt ctx (b := 1) (by norm_num) (by norm_num)
    (by norm_num) heta' htX ?_
  have he : (986894 - 1 : ℕ) = 986893 := by norm_num
  rw [he]
  exact hXle

/-- The pushed dyadic-value scale floor v2: exactly-dyadic value needs `X > 2^986893`. -/
theorem shellValueDyadic_scale_lower_pushV2 (ctx : ActualFailureContext)
    (h : ShellValueDyadic ctx) : 2 ^ 986893 < ctx.X := by
  by_contra hcon
  push Not at hcon
  exact shellValueDyadic_void_of_scale_pushV2 ctx hcon h

/-- **The pushed deep dyadic-value lever v2** — the dyadic exclusion demanded only at
`X > 2^986893` (the regime below is closed by `shellValueDyadic_void_of_scale_pushV2`;
demands strictly less than the wave-8 `DeepDyadicValueLeverPush` at `2^986891`). -/
def DeepDyadicValueLeverPushV2 : Prop :=
  ∀ ctx : ActualFailureContext, 2 ^ 986893 < ctx.X → ¬ ShellValueDyadic ctx

/-- The v2 deep lever discharges the full lever. -/
theorem dyadicValueLever_of_deepScalePushV2 (h : DeepDyadicValueLeverPushV2) :
    DyadicValueLever := by
  intro ctx hdy
  by_cases hX : 2 ^ 986893 < ctx.X
  · exact h ctx hX hdy
  · exact shellValueDyadic_void_of_scale_pushV2 ctx (not_lt.mp hX) hdy

/-- The v2 deep lever is equivalent to the full lever. -/
theorem dyadicValueLever_iff_deepScalePushV2 :
    DyadicValueLever ↔ DeepDyadicValueLeverPushV2 :=
  ⟨fun h ctx _ => h ctx, dyadicValueLever_of_deepScalePushV2⟩

/-- The v2 and wave-8 deep dyadic levers are equivalent (both collapse onto the full
lever; v2 demands strictly less). -/
theorem deepDyadicValueLeverPushV2_iff :
    DeepDyadicValueLeverPushV2 ↔ DeepDyadicValueLeverPush :=
  ⟨fun h ctx _ => dyadicValueLever_of_deepScalePushV2 h ctx,
   fun h ctx _ => dyadicValueLever_of_deepScalePush h ctx⟩

/-- The v2 deep-lever conditional route to the endpoint. -/
theorem erdos260_floorPushV2_deepLever_route (h : DeepDyadicValueLeverPushV2)
    (surfaces : DyadicValueLever → Erdos260DyadicLeverResidual) : Erdos260Statement :=
  (surfaces (dyadicValueLever_of_deepScalePushV2 h)).toStatement

/-! ## Part 10.  The successor surface — the `q = 9` escape guard dropped -/

/-- **The v2 tower escape**: `TowerModulusEnumEscape` with the (now theorem) `q = 9`
sparsity guard `3 ≤ m₀` removed — the only branch the split floor simplifies; the
`q = 11/13/105` guards (`m₀ ≥ 5/6/8` ⟺ `r ≥ 85/106/149`) are beyond the `r = 63` cap
of the oddpart route and stay. -/
def TowerModulusEnumEscapeV2 (ctx : ActualFailureContext) : Prop :=
  (class1SlopeDatum ctx).q = 9
  ∨ ((class1SlopeDatum ctx).q = 11 ∧ 5 ≤ towerSparsityBlock ctx)
  ∨ ((class1SlopeDatum ctx).q = 13 ∧ 6 ≤ towerSparsityBlock ctx)
  ∨ ((class1SlopeDatum ctx).q = 15 ∧ (class1SlopeDatum ctx).K₀ ≤ 2)
  ∨ ((class1SlopeDatum ctx).q = 105
      ∧ ((class1SlopeDatum ctx).K₀ = 7 ∨ 8 ≤ towerSparsityBlock ctx))
  ∨ TowerEnumEscape ctx
  ∨ 107 ≤ (class1SlopeDatum ctx).q

/-- **The escapes are pointwise EQUIVALENT at actual contexts** — the dropped `q = 9`
guard is supplied by `floorPushV2_q9_m0_ge_three`. -/
theorem towerModulusEnumEscape_iff_v2 (ctx : ActualFailureContext) :
    TowerModulusEnumEscape ctx ↔ TowerModulusEnumEscapeV2 ctx := by
  constructor
  · rintro (⟨hq, _⟩ | h)
    · exact Or.inl hq
    · exact Or.inr h
  · rintro (hq | h)
    · exact Or.inl ⟨hq, floorPushV2_q9_m0_ge_three ctx hq⟩
    · exact Or.inr h

/-- **The wave-10 floor-push-v2 residual** — the wave-9 `Erdos260TrajectoryResidual`
with `TowerModulusEnumEscape` replaced by `TowerModulusEnumEscapeV2` in the two tower
fields (the `q = 9` escape guard dropped — a theorem at the split floor); the other 12
fields are verbatim. -/
structure Erdos260FloorPushV2Residual where
  /-- Tower / class 2 — enumerated part (`q < 107`); the `q = 9` `m₀`-guard is GONE. -/
  towerEnumLow : ∀ ctx : ActualFailureContext,
    TowerModulusEnumEscapeV2 ctx → (class1SlopeDatum ctx).q < 107 →
    Class2CycleInequality ctx
  /-- Tower / class 2 — tail (`107 ≤ q`); the `q = 9` `m₀`-guard is GONE. -/
  towerEnumTail : ∀ ctx : ActualFailureContext,
    TowerModulusEnumEscapeV2 ctx →
    107 ≤ (class1SlopeDatum ctx).q →
    (((Nat.log 2 (class1SlopeDatum ctx).q + 1) * shellWidth ctx
        < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
            (class1SlopeDatum ctx).K₀)))
        ∧ TowerBand4Budget ctx)
      ∨ Class2CycleInequality ctx
  /-- Run / class 5 — enumerated part (`q < 64`); verbatim wave-9 field. -/
  runNumericLow : ∀ ctx : ActualFailureContext,
    (class1SlopeDatum ctx).q < 64 →
    Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx
  /-- Run / class 5 — tail (`64 ≤ q`); verbatim wave-9 field. -/
  runNumericTail : ∀ ctx : ActualFailureContext,
    64 ≤ (class1SlopeDatum ctx).q →
    ((Nat.log 2 (class1SlopeDatum ctx).q + 1)
        * (supportShell ctx.shell.d ctx.shell.X).card
      < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
          (class1SlopeDatum ctx).K₀)))
      ∧ RunBandBudget ctx
    ∨ Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx
  /-- Return / class 4 count gates — verbatim wave-9 field. -/
  returnGates : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    2 * (129 * shellLadderDepth ctx + 64)
      ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
    ReturnGatesBodyUngated ctx
  /-- Return / class 4 digit Z — trajectory form; verbatim wave-9 field. -/
  returnZeroTrajectory : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    (∃ k ∈ olcFibre ctx,
      2 ^ carryVal2 ctx k < (supportShell ctx.shell.d ctx.shell.X).card) →
    ¬ ReturnIndexWindowClean ctx →
    ReturnZeroBelowBandTrajectory ctx
  /-- Return / class 4 clean step — trajectory form; verbatim wave-9 field. -/
  returnMaxCleanTrajectory : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnIndexWindowClean ctx →
    ReturnMaxCleanCarryTrajectory ctx
  /-- Return / class 4 K.1 interior — verbatim wave-9 field. -/
  returnInterior : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx
  /-- Chernoff / class 0 survivors — verbatim wave-9 field. -/
  class0Survivor : ∀ ctx : ActualFailureContext, Class0DatumSurvivor ctx →
    Class0SurvivorResidueMiss ctx
  /-- Chernoff / class 0 mid band — verbatim wave-9 field. -/
  class0Mid : ∀ ctx : ActualFailureContext, 48 ≤ (class1SlopeDatum ctx).q →
    (class1SlopeDatum ctx).q < 96 → Class0CycleMeetsShallow ctx →
    Class0WindowCycleCheck ctx
  /-- Chernoff / class 0 large moduli (`96 ≤ q`) — verbatim wave-9 field. -/
  class0BigOrder : ∀ ctx : ActualFailureContext, 96 ≤ (class1SlopeDatum ctx).q →
    (∃ C, ((Nat.log 2 (class1SlopeDatum ctx).q + 1) * C
          < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
              (class1SlopeDatum ctx).K₀)))
        ∧ ∃ c, C < c ∧ c ≤ (class1SlopeDatum ctx).q
            ∧ (∀ m, 1 ≤ m →
                slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
                  = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
            ∧ ∀ k ∈ ctx.n24CarryData.starts,
                129 * shellLadderDepth ctx + 64
                    ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
                (class1SlopeDatum ctx).q
                  < 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀
                      (cycleRep c k))
    ∨ Class0WindowCycleCheck ctx
  /-- CNL / class 1 — enumerated deep part (`q < 101`); verbatim wave-9 field. -/
  class1DeepLow : ∀ ctx : ActualFailureContext,
    64 ∣ shellLadderDepth ctx →
    9 ≤ (class1SlopeDatum ctx).q →
    ((class1SlopeDatum ctx).q ≤ 15 ∨ 25 ≤ (class1SlopeDatum ctx).q) →
    (class1SlopeDatum ctx).q ∉ class1ClosedModuli →
    ¬ Class1DatumClosed ctx →
    ¬ Class1GcdWindowMiss ctx →
    (class1SlopeDatum ctx).q < 101 →
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅
  /-- CNL / class 1 — tail (`101 ≤ q`); verbatim wave-9 field. -/
  class1DeepTail : ∀ ctx : ActualFailureContext,
    101 ≤ (class1SlopeDatum ctx).q →
    Class1Band4FreePeriod ctx
    ∨ (64 ∣ shellLadderDepth ctx →
        9 ≤ (class1SlopeDatum ctx).q →
        ((class1SlopeDatum ctx).q ≤ 15 ∨ 25 ≤ (class1SlopeDatum ctx).q) →
        (class1SlopeDatum ctx).q ∉ class1ClosedModuli →
        ¬ Class1DatumClosed ctx →
        ¬ Class1GcdWindowMiss ctx →
        routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅)
  /-- DensePack / class 3 — verbatim wave-9 field. -/
  densePackUngated : DensePackUngatedClosureResidual

namespace Erdos260FloorPushV2Residual

/-- **The bridge into the wave-9 trajectory surface**: the two tower fields convert
through the pointwise escape equivalence; everything else passes verbatim. -/
def toTrajectoryResidual (R : Erdos260FloorPushV2Residual) : Erdos260TrajectoryResidual where
  towerEnumLow := fun ctx hesc =>
    R.towerEnumLow ctx ((towerModulusEnumEscape_iff_v2 ctx).mp hesc)
  towerEnumTail := fun ctx hesc =>
    R.towerEnumTail ctx ((towerModulusEnumEscape_iff_v2 ctx).mp hesc)
  runNumericLow := R.runNumericLow
  runNumericTail := R.runNumericTail
  returnGates := R.returnGates
  returnZeroTrajectory := R.returnZeroTrajectory
  returnMaxCleanTrajectory := R.returnMaxCleanTrajectory
  returnInterior := R.returnInterior
  class0Survivor := R.class0Survivor
  class0Mid := R.class0Mid
  class0BigOrder := R.class0BigOrder
  class1DeepLow := R.class1DeepLow
  class1DeepTail := R.class1DeepTail
  densePackUngated := R.densePackUngated

/-- The final statement from the floor-push-v2 residual, through the wave-9 capstone. -/
theorem toStatement (R : Erdos260FloorPushV2Residual) : Erdos260Statement :=
  erdos260_of_trajectoryResidual R.toTrajectoryResidual

end Erdos260FloorPushV2Residual

/-- **The wave-10 endpoint**: `Erdos260Statement` from the floor-push-v2 surface. -/
theorem erdos260_of_floorPushV2 (R : Erdos260FloorPushV2Residual) : Erdos260Statement :=
  R.toStatement

/-- The weakening witness: any wave-9 trajectory provider yields the v2 surface (the
re-added `q = 9` guard is supplied by the split floor through the escape equivalence). -/
def floorPushV2Residual_of_trajectoryResidual (R : Erdos260TrajectoryResidual) :
    Erdos260FloorPushV2Residual where
  towerEnumLow := fun ctx hesc =>
    R.towerEnumLow ctx ((towerModulusEnumEscape_iff_v2 ctx).mpr hesc)
  towerEnumTail := fun ctx hesc =>
    R.towerEnumTail ctx ((towerModulusEnumEscape_iff_v2 ctx).mpr hesc)
  runNumericLow := R.runNumericLow
  runNumericTail := R.runNumericTail
  returnGates := R.returnGates
  returnZeroTrajectory := R.returnZeroTrajectory
  returnMaxCleanTrajectory := R.returnMaxCleanTrajectory
  returnInterior := R.returnInterior
  class0Survivor := R.class0Survivor
  class0Mid := R.class0Mid
  class0BigOrder := R.class0BigOrder
  class1DeepLow := R.class1DeepLow
  class1DeepTail := R.class1DeepTail
  densePackUngated := R.densePackUngated

/-- **The two surfaces are EQUIVALENT** — the v2 surface is exactly the wave-9 one with
the dead `q = 9` escape guard folded in (a presentation refinement, honestly recorded). -/
theorem nonempty_floorPushV2_iff_trajectory :
    Nonempty Erdos260FloorPushV2Residual ↔ Nonempty Erdos260TrajectoryResidual :=
  ⟨fun ⟨R⟩ => ⟨R.toTrajectoryResidual⟩,
   fun ⟨R⟩ => ⟨floorPushV2Residual_of_trajectoryResidual R⟩⟩

/-! ## Part 11.  Machine-readable status (honest) -/

/-- Honest machine-readable status of the wave-10 floor push v2. -/
def floorPushV2Status : List String :=
  [ "THE SPLIT FLOOR MASTERS (proved) - floorPushV2_window_bound: oddpart(Q) < 2^b with " ++
      "b <= L collapses the per-context gap from the generic 2L-25 to L+b+1 (the rigidity " ++
      "chain pow_two_le_oddpart_of_zero_gap / supportShell_card_lower_of_gap is ALREADY " ++
      "oddpart-only - verified: the window condition is u*(2X+2) < 2^g with Q = u*2^t, " ++
      "t <= X; the 2^t part cancels).  floorPushV2_void_of_rep_lt / _of_oddpart_lt / " ++
      "_of_q_lt: u < 2^b (or q < 3*2^b via the master pin q = oddpart(Q)*(2K0+1), K0 >= 1, " ++
      "giving 3*oddpart(Q) <= q at EVERY ctx - floorPushV2_three_oddpartQ_le_q) voids " ++
      "X <= 2^(986894-b); sharp fire 17*(L+b+1) <= 2^24 iff L <= 986894-b; the wave-8 " ++
      "floor L >= 493461 supplies b <= L.",
    "THE SMALL-q FLOORS (exact constants, all proved): q <= 2^20 = 1048576 -> X > 2^986875, " ++
      "L >= 986876, r >= 63 (16515072 = 63*2^18 <= 17*986876 = 16776892), m0 >= 3 " ++
      "(floorPushV2_void/scale_lower/depth/r_ge_63/m0_ge_three_of_q_le_2pow20).  " ++
      "q <= 2^15421 -> X > 2^971474, r >= 63 (sharp: 17*971475 = 16515075).  " ++
      "q <= 2^339246 -> X > 2^647649, L >= 647650, r >= 42 (sharp: 17*647650 = 11010050 " ++
      ">= 42*2^18 = 11010048), m0 >= 3 - the wave-9 q=9 payoff threshold r >= 42 is " ++
      "crossed on an astronomically generous q-range.",
    "THE HONEST CAP: the sharp fire condition 17*g <= 2^24 caps the void region at " ++
      "L <= 986893 even at oddpart(Q) = 1 (g >= L+2), so the deepest reachable floor is " ++
      "L >= 986894 and r = floor(17L/2^18) >= 63 is the deepest reachable order bound " ++
      "(r >= 64 needs L >= 986896 - OUT of reach).  The wave-9 thresholds r >= 85/106/149 " ++
      "for q = 11/13/(105,52) are therefore NOT reachable by ANY oddpart-route floor; " ++
      "those windows only NARROW to [63,84]/[63,105]/[63,148] " ++
      "(floorPushV2_q11_window/q13_window/q105K52_window).",
    "PER-PAIR TOWER FLOORS (proved): q=9 -> oddpart(Q) <= 3, X > 2^986892, L >= 986893, " ++
      "r >= 63, m0 >= 3; q=11 -> oddpart(Q) = 1 FORCED, X > 2^986893, L >= 986894; " ++
      "q=13 -> oddpart(Q) = 1, X > 2^986893; (105,52) -> oddpart(Q) = 1, X > 2^986893; " ++
      "q=15 -> u <= 5, X > 2^986891; q=105 -> u <= 35, X > 2^986888; q=63 -> u <= 21, " ++
      "X > 2^986889, r >= 63.",
    "WHAT THE CROSSED q=9 THRESHOLD HONESTLY DOES (NO pair closes): r >= 63 at q=9 " ++
      "contexts forces m0 >= 3, so the wave-3 count closure (fires on m0 <= 2) has an " ++
      "EMPTY window [32,41] (floorPushV2_q9_count_window_empty) and EVERY q=9 context is " ++
      "an escape context (floorPushV2_q9_demand_everywhere).  'Voiding the q=9 window' " ++
      "kills the count-bound route; the cycle inequality stays demanded at ALL q=9 " ++
      "contexts and now amounts to voiding the contexts themselves: their value pins are " ++
      "4/2^t (u=1, the open dyadic lever beyond 2^986893) and 1/(3*2^t) (u=3, beyond " ++
      "2^986892).  The hoped 'close all four tower counted windows outright' is " ++
      "REFUTED: the m0-thresholds are upper closure edges, and pushing r UP moves contexts " ++
      "INTO the residual, not out of it.",
    "TARGET B RECHECK (honest, none closes): class-0 19 survivors and class-1 23 pairs " ++
      "all have q < 102 <= 2^20, so their contexts now carry X > 2^986875, r >= 63 - but " ++
      "their obstructions are r-independent residue congruences (verified shapes: " ++
      "Class0SurvivorResidueMiss concludes k % c != rho; class1Fibre_residue_of_datum_63_10 " ++
      "concludes k % 2 = 0 - no r in any conclusion; the r appears only in deep-window " ++
      "GATES, where larger r gates MORE positions in, making demands harder).  Run " ++
      "band-1/densepack: the ceil(W/c)-window and band-count obstructions have W >= r+1 " ++
      ">= 64 now - r-growth makes them strictly harder, closes nothing.",
    "THE q=63 CROSSOVER (route ii, proved): divisor pin K0 in {1,3,4,10,31} " ++
      "(floorPushV2_q63_K0_pin); oddpart pin u in {1,3,7,9,21} (floorPushV2_q63_oddpart_pin); " ++
      "split floor X > 2^986889, r >= 63 (floorPushV2_q63_scale_lower/r_ge_63); ord_63(2) = 6 " ++
      "EXACTLY (floorPushV2_orderOf_two_zmod63; also ord_3(2) = 2, ord_7(2) = 3); gap-sum " ++
      "parity: EVERY q=63 cycle has 2 | G or 3 | G (floorPushV2_q63_gapSum_two_or_three_dvd " ++
      "/ _ctx_gapSum - the order cofactor divides 63, every divisor >= 2 of 63 is divisible " ++
      "by 3 or 7).  The open class-1 instance 63@10: oddpart(Q) = 3 EXACTLY, Q = 3*2^t, " ++
      "value = 10/(3*2^t) (a NEW pinned-value family, not the in-tree dyadic/fifth/thirds " ++
      "shapes), X > 2^986892, plus the r-independent congruence k % 2 = 0 " ++
      "(class1Fibre_residue_of_datum_63_10, cited).  Sharpest joint characterization " ++
      "delivered; the instance itself stays OPEN.",
    "THE PUSHED DYADIC DEEP LEVER (proved): shellValueDyadic_void_of_scale_pushV2 / " ++
      "_scale_lower_pushV2 - the dyadic value 1/2^t is void at X <= 2^986893 (u = 1 allows " ++
      "g = L+2; wave-8's u <= 7 bound reached 2^986891).  Successor " ++
      "DeepDyadicValueLeverPushV2 (demand only at X > 2^986893), discharge " ++
      "dyadicValueLever_of_deepScalePushV2, equivalences dyadicValueLever_iff_deepScalePushV2 " ++
      "/ deepDyadicValueLeverPushV2_iff, route erdos260_floorPushV2_deepLever_route.  The " ++
      "fifth/thirds family floors stay at 2^986891 (u <= 5, 7 - no gain from this module).",
    "THE SUCCESSOR SURFACE (wave 10) - Erdos260FloorPushV2Residual: the wave-9 " ++
      "Erdos260TrajectoryResidual with TowerModulusEnumEscape replaced by " ++
      "TowerModulusEnumEscapeV2 (the q=9 escape guard 3 <= m0 DROPPED - a theorem at the " ++
      "split floor; pointwise equivalence towerModulusEnumEscape_iff_v2).  The q=11/13/105 " ++
      "guards stay (their thresholds r >= 85/106/149 exceed the r = 63 cap).  Endpoint " ++
      "erdos260_of_floorPushV2; bridges Erdos260FloorPushV2Residual.toTrajectoryResidual / " ++
      "floorPushV2Residual_of_trajectoryResidual; equivalence " ++
      "nonempty_floorPushV2_iff_trajectory.  Additive only; nothing upstream touched.",
    "WHAT RESISTS AND WHY (honest): the split floors are CONDITIONAL on small q (or small " ++
      "oddpart) per context; the unconditional floor stays the wave-8 X > 2^493460 (large-q " ++
      "contexts allow oddpart(Q) up to 2^(L-27), where the gap honestly stays ~2L).  At " ++
      "large q no lane becomes free: the order cofactor of a huge q can still be tiny " ++
      "(e.g. 63), so no unconditional cycle-length floor exists (the Mersenne exceptional " ++
      "list is the honest obstruction).  No context with q <= 2^20 and X > 2^986875 is " ++
      "claimed empty; no tower pair, class-0 survivor, class-1 pair, run pair, or densepack " ++
      "threshold is closed by this module.  No sorry / admit / new axiom / native_decide." ]

theorem floorPushV2Status_nonempty : floorPushV2Status ≠ [] := by
  simp [floorPushV2Status]

/-! ## Part 12.  Axiom-cleanliness audit -/

#print axioms floorPushV2_window_bound
#print axioms floorPushV2_void_of_rep_lt
#print axioms floorPushV2_void_of_oddpart_lt
#print axioms floorPushV2_oddpart_scale_lower
#print axioms floorPushV2_three_oddpartQ_le_q
#print axioms floorPushV2_void_of_q_lt
#print axioms floorPushV2_depth_lower
#print axioms floorPushV2_r_lower
#print axioms floorPushV2_void_of_q_le_2pow20
#print axioms floorPushV2_scale_lower_of_q_le_2pow20
#print axioms floorPushV2_depth_of_q_le_2pow20
#print axioms floorPushV2_r_ge_63_of_q_le_2pow20
#print axioms floorPushV2_m0_ge_three_of_q_le_2pow20
#print axioms floorPushV2_void_of_q_le_2pow15421
#print axioms floorPushV2_r_ge_63_of_q_le_2pow15421
#print axioms floorPushV2_void_of_q_le_2pow339246
#print axioms floorPushV2_r_ge_42_of_q_le_2pow339246
#print axioms floorPushV2_m0_ge_three_of_q_le_2pow339246
#print axioms floorPushV2_q9_oddpart_lt_four
#print axioms floorPushV2_void_q9
#print axioms floorPushV2_q9_scale_lower
#print axioms floorPushV2_q9_r_ge_63
#print axioms floorPushV2_q9_m0_ge_three
#print axioms floorPushV2_q9_count_window_empty
#print axioms floorPushV2_q9_demand_everywhere
#print axioms floorPushV2_q11_oddpart_eq_one
#print axioms floorPushV2_void_q11
#print axioms floorPushV2_q11_scale_lower
#print axioms floorPushV2_q13_oddpart_eq_one
#print axioms floorPushV2_void_q13
#print axioms floorPushV2_q13_scale_lower
#print axioms floorPushV2_q105K52_oddpart_eq_one
#print axioms floorPushV2_void_q105K52
#print axioms floorPushV2_q105K52_scale_lower
#print axioms floorPushV2_void_q15
#print axioms floorPushV2_void_q105
#print axioms floorPushV2_q11_window
#print axioms floorPushV2_q13_window
#print axioms floorPushV2_q105K52_window
#print axioms floorPushV2_q63_K₀_pin
#print axioms floorPushV2_q63_oddpart_pin
#print axioms floorPushV2_void_q63
#print axioms floorPushV2_q63_scale_lower
#print axioms floorPushV2_q63_r_ge_63
#print axioms floorPushV2_q63K10_oddpart_eq_three
#print axioms floorPushV2_q63K10_Q_shape
#print axioms floorPushV2_q63K10_value
#print axioms floorPushV2_void_q63K10
#print axioms floorPushV2_q63K10_scale_lower
#print axioms floorPushV2_zmod_two_pow_eq_one
#print axioms floorPushV2_orderOf_two_zmod3
#print axioms floorPushV2_orderOf_two_zmod7
#print axioms floorPushV2_orderOf_two_zmod63
#print axioms floorPushV2_q63_gapSum_two_or_three_dvd
#print axioms floorPushV2_q63_ctx_gapSum
#print axioms shellValueDyadic_void_of_scale_pushV2
#print axioms shellValueDyadic_scale_lower_pushV2
#print axioms dyadicValueLever_of_deepScalePushV2
#print axioms dyadicValueLever_iff_deepScalePushV2
#print axioms deepDyadicValueLeverPushV2_iff
#print axioms erdos260_floorPushV2_deepLever_route
#print axioms towerModulusEnumEscape_iff_v2
#print axioms Erdos260FloorPushV2Residual.toTrajectoryResidual
#print axioms Erdos260FloorPushV2Residual.toStatement
#print axioms erdos260_of_floorPushV2
#print axioms floorPushV2Residual_of_trajectoryResidual
#print axioms nonempty_floorPushV2_iff_trajectory
#print axioms floorPushV2Status_nonempty

end

end Erdos260
