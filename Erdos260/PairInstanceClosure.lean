import Erdos260.Erdos260PushCapstone
import Erdos260.TowerFixedPointClosure
import Erdos260.TowerCycleDensity
import Erdos260.ModulusTailCriteria
import Erdos260.CNLClass1DeepClosure

/-!
# Erdos 260 — the per-pair instance closure under the wave-8 floor `r ≥ 32`

Wave 8 (`ScaleFloorPush`) pushed the unconditional floor to `X > 2^493460` / `L ≥ 493461`,
forcing `r = ⌊κ·L⌋ ≥ 32` at every actual failure context (`n24_r_ge_thirtytwo`) and the
sparsity block `m₀ = ⌊(3(r+1)+63)/64⌋ ≥ 2` everywhere
(`two_le_towerSparsityBlock_everywhere`).  This module re-runs the per-pair arithmetic of
waves 3–5 under that new lower bound, **additively** (no existing file is edited; only
existing public lemmas are consumed).

## What the new `r ≥ 32` floor decides (the honest verdict)

The wave-3–5 per-pair tower count bounds are stated with **m₀-thresholds**: the class-2
cycle inequality for a counted pair holds whenever `m₀ ≤ t_pair`.  With `m₀ = ⌊(3(r+1)+63)/64⌋`
this is the **r-window** `r ≤ rUpper(t_pair)`:

| pair                | closes when | r-window           | escape (residual)      |
|---------------------|-------------|--------------------|------------------------|
| `q = 9`             | `m₀ ≤ 2`    | `r ≤ 41`           | `m₀ ≥ 3`, i.e. `r ≥ 42`  |
| `q = 11` (`K₀ = 5`) | `m₀ ≤ 4`    | `r ≤ 84`           | `m₀ ≥ 5`, i.e. `r ≥ 85`  |
| `q = 13` (`K₀ = 6`) | `m₀ ≤ 5`    | `r ≤ 105`          | `m₀ ≥ 6`, i.e. `r ≥ 106` |
| `(q,K₀)=(105,52)`   | `m₀ ≤ 7`    | `r ≤ 148`          | `m₀ ≥ 8`, i.e. `r ≥ 149` |
| `(q,K₀)=(15,7)`     | every `m₀`  | all `r` (empty fibre) | none — closes outright |
| `(q,K₀)=(105,7)`    | fixed point | —                  | demanded (fixed point) |

The floor `r ≥ 32` is a **lower** edge.  The per-pair thresholds are **upper** edges on `r`.
So the floor turns each counted pair into a genuinely **two-sided window** `32 ≤ r ≤ rUpper`,
but it does **not** void the upper-edge residual `r ≥ rUpper+1`: that residual is unchanged
from waves 3–5 (only a *further* floor push to `r ≥ 42 / 85 / 106 / 149` would void them).
The empty-fibre families `(15,7)` / off-fixed `105` close outright (at every `m₀`, hence
at every `r ≥ 32`) — and these were already closed unconditionally before wave 8.

**Net finding (honest):** `r ≥ 32` closes **no new** counted tower pair, no class-0 survivor,
and no class-1 pair.  The class-0 residue-window misses and class-1 band-4 residue
congruences are r-independent obstructions (the survivor modules already noted that the
unconditional facts exclude no residue class, and the `r = 0` top pin is vacuous because
`r ≥ 1`; `r ≥ 32` does not change this).  Consequently the successor surface is
**equivalent** to the wave-8 push surface (`Erdos260PushResidual`), not strictly smaller —
its escape thresholds are already the wave-3–5 upper edges, which the r-lower floor cannot
move.  We expose the exact two-sided windows as proved theorems and re-present the surface.

## The modulus-tail cofactor cross

`ModulusTailCriteria.mersenneSmallOrderModuli = {3,5,7,9,15,21,31,63}` is the complete list
of odd cofactors `q' > 1` with `orderOf (2 : ZMod q') ≤ 6` (the honest hard cofactors).
Crossing against the class-1 closed list
`class1ClosedModuli = {27,31,33,43,45,51,65,85,91,93}`: the intersection is exactly `{31}`,
so the surviving cofactors are `{3,5,7,9,15,21,63}` (seven), of which `63` is also the
open class-1 pair `63 @ 10`.

No `sorry`, no `admit`, no new `axiom`, no `native_decide` (only `decide`/`simp`/`omega`/`rfl`
on small closed arithmetic).
-/

namespace Erdos260

set_option linter.unusedVariables false

/-! ## Part 0.  Grounding in the wave-8 floor -/

/-- **The wave-8 order floor**, re-exported: `r ≥ 32` at every actual failure context. -/
theorem pic_r_ge_32 (ctx : ActualFailureContext) : 32 ≤ ctx.n24CarryData.r :=
  n24_r_ge_thirtytwo ctx

/-- **The sparsity-block floor**, re-exported: `m₀ ≥ 2` everywhere (deep-shell consequence,
now unconditional). -/
theorem pic_m0_ge_two (ctx : ActualFailureContext) : 2 ≤ towerSparsityBlock ctx :=
  two_le_towerSparsityBlock_everywhere ctx

/-- The shell width is at least `33` everywhere: `r + 1 ≤ width` and `r ≥ 32`.  This
discharges the `16 ≤ width` / `22 ≤ width` side conditions of the tower count bounds. -/
theorem pic_shellWidth_ge_33 (ctx : ActualFailureContext) : 33 ≤ shellWidth ctx := by
  have h := r_add_one_le_width ctx
  have hr := pic_r_ge_32 ctx
  omega

/-! ## Part 1.  The `m₀ ↔ r` window arithmetic (pure `ℕ`, all by `omega`) -/

/-- The sparsity block `m₀` as a pure function of the order index `r`. -/
def m0Floor (r : ℕ) : ℕ := (3 * (r + 1) + 63) / 64

/-- The sparsity block equals `m0Floor` of the order index (definitional). -/
theorem m0Floor_eq_block (ctx : ActualFailureContext) :
    towerSparsityBlock ctx = m0Floor ctx.n24CarryData.r := rfl

/-- **The exact threshold/window translation**: `m₀ ≤ t ↔ 3r + 3 ≤ 64t`. -/
theorem m0Floor_le_iff (r t : ℕ) : m0Floor r ≤ t ↔ 3 * r + 3 ≤ 64 * t := by
  unfold m0Floor; omega

/-- `m₀ ≤ 2 ↔ r ≤ 41` — the `q = 9` window. -/
theorem r_window_q9 (r : ℕ) : m0Floor r ≤ 2 ↔ r ≤ 41 := by
  rw [m0Floor_le_iff]; omega

/-- `m₀ ≤ 4 ↔ r ≤ 84` — the `q = 11` window. -/
theorem r_window_q11 (r : ℕ) : m0Floor r ≤ 4 ↔ r ≤ 84 := by
  rw [m0Floor_le_iff]; omega

/-- `m₀ ≤ 5 ↔ r ≤ 105` — the `q = 13` window. -/
theorem r_window_q13 (r : ℕ) : m0Floor r ≤ 5 ↔ r ≤ 105 := by
  rw [m0Floor_le_iff]; omega

/-- `m₀ ≤ 7 ↔ r ≤ 148` — the `(105,52)` window. -/
theorem r_window_q105 (r : ℕ) : m0Floor r ≤ 7 ↔ r ≤ 148 := by
  rw [m0Floor_le_iff]; omega

/-! ## Part 2.  The per-pair tower closures, recut as two-sided `r`-windows -/

/-- **`q = 9` closes on `r ≤ 41`** (`m₀ ≤ 2`).  Combined with the unconditional `r ≥ 32`,
the live closure window is `32 ≤ r ≤ 41`. -/
theorem tower_q9_closes_of_r_le_41 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 9) (hr : ctx.n24CarryData.r ≤ 41) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_modulus_nine ctx hq (by unfold towerSparsityBlock; omega)

/-- **`q = 11` closes on `r ≤ 84`** (`m₀ ≤ 4`); the width side condition `16 ≤ width` is
automatic (`width ≥ 33`). -/
theorem tower_q11_closes_of_r_le_84 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 11) (hr : ctx.n24CarryData.r ≤ 84) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_modulus_eleven ctx hq
    (by unfold towerSparsityBlock; omega)
    (le_trans (by norm_num) (pic_shellWidth_ge_33 ctx))

/-- **`q = 13` closes on `r ≤ 105`** (`m₀ ≤ 5`); `22 ≤ width` is automatic. -/
theorem tower_q13_closes_of_r_le_105 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 13) (hr : ctx.n24CarryData.r ≤ 105) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_modulus_thirteen ctx hq
    (by unfold towerSparsityBlock; omega)
    (le_trans (by norm_num) (pic_shellWidth_ge_33 ctx))

/-- **`(105,52)` closes on `r ≤ 148`** (`m₀ ≤ 7`); `22 ≤ width` is automatic. -/
theorem tower_q105_K₀52_closes_of_r_le_148 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 105) (hK₀ : (class1SlopeDatum ctx).K₀ = 52)
    (hr : ctx.n24CarryData.r ≤ 148) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_q105_K₀52 ctx hq hK₀
    (by unfold towerSparsityBlock; omega)
    (le_trans (by norm_num) (pic_shellWidth_ge_33 ctx))

/-- **`(15,7)` closes outright** — the band-4-free cycle `13 → 11 → 7` gives the cycle
inequality at every `m₀`, hence at every `r ≥ 32`. -/
theorem tower_q15_K₀7_closes (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 15) (hK₀ : (class1SlopeDatum ctx).K₀ = 7) :
    Class2CycleInequality ctx :=
  class2CycleInequality_of_q15_K₀7 ctx hq hK₀

/-! ## Part 3.  The escape (residual) regimes, in terms of `r` -/

/-- The `q = 9` escape regime `m₀ ≥ 3` is exactly `r ≥ 42`. -/
theorem tower_q9_escape_iff_r_ge_42 (ctx : ActualFailureContext) :
    3 ≤ towerSparsityBlock ctx ↔ 42 ≤ ctx.n24CarryData.r := by
  unfold towerSparsityBlock; omega

/-- The `q = 11` escape regime `m₀ ≥ 5` is exactly `r ≥ 85`. -/
theorem tower_q11_escape_iff_r_ge_85 (ctx : ActualFailureContext) :
    5 ≤ towerSparsityBlock ctx ↔ 85 ≤ ctx.n24CarryData.r := by
  unfold towerSparsityBlock; omega

/-- The `q = 13` escape regime `m₀ ≥ 6` is exactly `r ≥ 106`. -/
theorem tower_q13_escape_iff_r_ge_106 (ctx : ActualFailureContext) :
    6 ≤ towerSparsityBlock ctx ↔ 106 ≤ ctx.n24CarryData.r := by
  unfold towerSparsityBlock; omega

/-- The `(105,52)` escape regime `m₀ ≥ 8` is exactly `r ≥ 149`. -/
theorem tower_q105_escape_iff_r_ge_149 (ctx : ActualFailureContext) :
    8 ≤ towerSparsityBlock ctx ↔ 149 ≤ ctx.n24CarryData.r := by
  unfold towerSparsityBlock; omega

/-! ## Part 4.  The two-sided per-pair dichotomies (the recut residual)

Each counted pair either **closes** (the class-2 cycle inequality holds) or lies in its
**escape regime** (the residual `r`-band), now sharpened with the wave-8 floor `r ≥ 32` as
the lower edge of the live closure window. -/

/-- **`q = 9` dichotomy**: closes for `r ≤ 41`, else the escape regime `r ≥ 42`. -/
theorem tower_q9_dichotomy (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 9) :
    Class2CycleInequality ctx ∨ 42 ≤ ctx.n24CarryData.r := by
  rcases Nat.lt_or_ge ctx.n24CarryData.r 42 with h | h
  · exact Or.inl (tower_q9_closes_of_r_le_41 ctx hq (by omega))
  · exact Or.inr (by omega)

/-- **`q = 11` dichotomy**: closes for `r ≤ 84`, else the escape regime `r ≥ 85`. -/
theorem tower_q11_dichotomy (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 11) :
    Class2CycleInequality ctx ∨ 85 ≤ ctx.n24CarryData.r := by
  rcases Nat.lt_or_ge ctx.n24CarryData.r 85 with h | h
  · exact Or.inl (tower_q11_closes_of_r_le_84 ctx hq (by omega))
  · exact Or.inr (by omega)

/-- **`q = 13` dichotomy**: closes for `r ≤ 105`, else the escape regime `r ≥ 106`. -/
theorem tower_q13_dichotomy (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 13) :
    Class2CycleInequality ctx ∨ 106 ≤ ctx.n24CarryData.r := by
  rcases Nat.lt_or_ge ctx.n24CarryData.r 106 with h | h
  · exact Or.inl (tower_q13_closes_of_r_le_105 ctx hq (by omega))
  · exact Or.inr (by omega)

/-- **`(105,52)` dichotomy**: closes for `r ≤ 148`, else the escape regime `r ≥ 149`. -/
theorem tower_q105_K₀52_dichotomy (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 105) (hK₀ : (class1SlopeDatum ctx).K₀ = 52) :
    Class2CycleInequality ctx ∨ 149 ≤ ctx.n24CarryData.r := by
  rcases Nat.lt_or_ge ctx.n24CarryData.r 149 with h | h
  · exact Or.inl (tower_q105_K₀52_closes_of_r_le_148 ctx hq hK₀ (by omega))
  · exact Or.inr (by omega)

/-! ## Part 5.  The modulus-tail cofactor cross (decidable, grounded) -/

/-- The eight exceptional Mersenne-divisor cofactors `orderOf (2 : ZMod q') ≤ 6`. -/
def picExceptionalCofactors : List ℕ := mersenneSmallOrderModuli

/-- The cofactors crossing into the class-1 closed list — exactly `{31}`. -/
def picCofactorsClosedByClass1 : List ℕ :=
  picExceptionalCofactors.filter (fun q => decide (q ∈ class1ClosedModuli))

/-- The cofactors surviving the class-1 closed-list cross — exactly `{3,5,7,9,15,21,63}`. -/
def picCofactorsSurviving : List ℕ :=
  picExceptionalCofactors.filter (fun q => decide (q ∉ class1ClosedModuli))

theorem picExceptionalCofactors_eq :
    picExceptionalCofactors = [3, 5, 7, 9, 15, 21, 31, 63] := rfl

/-- Cofactor `31` is in the class-1 closed list. -/
theorem pic_cofactor_31_closed : (31 : ℕ) ∈ class1ClosedModuli := by
  simp [class1ClosedModuli]

/-- None of the other seven exceptional cofactors are in the class-1 closed list. -/
theorem pic_cofactor_3_open : (3 : ℕ) ∉ class1ClosedModuli := by simp [class1ClosedModuli]
theorem pic_cofactor_5_open : (5 : ℕ) ∉ class1ClosedModuli := by simp [class1ClosedModuli]
theorem pic_cofactor_7_open : (7 : ℕ) ∉ class1ClosedModuli := by simp [class1ClosedModuli]
theorem pic_cofactor_9_open : (9 : ℕ) ∉ class1ClosedModuli := by simp [class1ClosedModuli]
theorem pic_cofactor_15_open : (15 : ℕ) ∉ class1ClosedModuli := by simp [class1ClosedModuli]
theorem pic_cofactor_21_open : (21 : ℕ) ∉ class1ClosedModuli := by simp [class1ClosedModuli]
theorem pic_cofactor_63_open : (63 : ℕ) ∉ class1ClosedModuli := by simp [class1ClosedModuli]

/-- **The cofactor cross, assembled**: the surviving exceptional cofactors are exactly
`{3,5,7,9,15,21,63}`. -/
theorem picCofactorsSurviving_eq :
    picCofactorsSurviving = [3, 5, 7, 9, 15, 21, 63] := by
  have h3 := pic_cofactor_3_open
  have h5 := pic_cofactor_5_open
  have h7 := pic_cofactor_7_open
  have h9 := pic_cofactor_9_open
  have h15 := pic_cofactor_15_open
  have h21 := pic_cofactor_21_open
  have h31 := pic_cofactor_31_closed
  have h63 := pic_cofactor_63_open
  simp only [picCofactorsSurviving, picExceptionalCofactors, mersenneSmallOrderModuli,
    List.filter_cons, List.filter_nil, decide_not]
  simp [h3, h5, h7, h9, h15, h21, h31, h63]

/-- **The closed cofactor, assembled**: exactly `{31}`. -/
theorem picCofactorsClosedByClass1_eq :
    picCofactorsClosedByClass1 = [31] := by
  have h3 := pic_cofactor_3_open
  have h5 := pic_cofactor_5_open
  have h7 := pic_cofactor_7_open
  have h9 := pic_cofactor_9_open
  have h15 := pic_cofactor_15_open
  have h21 := pic_cofactor_21_open
  have h31 := pic_cofactor_31_closed
  have h63 := pic_cofactor_63_open
  simp only [picCofactorsClosedByClass1, picExceptionalCofactors, mersenneSmallOrderModuli,
    List.filter_cons, List.filter_nil]
  simp [h3, h5, h7, h9, h15, h21, h31, h63]

/-! ## Part 6.  The machine-readable status ledgers -/

/-- **Pairs/instances that the wave-8 floor `r ≥ 32` closes OUTRIGHT** (no residual). -/
def pairInstanceClosedUnderRGe32 : List String :=
  [ "tower class-2 (15, K0=7): band-4-free cycle 13->11->7, fibre EMPTY at every m0 - " ++
      "closes for all r >= 32 (tower_q15_K0_7_closes; already unconditional pre-wave-8).",
    "tower class-2 (105, K0 not in {7,52}): every off-fixed pin-admissible K0 rides a " ++
      "band-4-free cycle - fibre EMPTY (towerFP105_fibre_empty_offFixed; unconditional)." ]

/-- **The surviving instance list** (lane | pair | precise remaining demand under `r ≥ 32`).
Honest: every entry's obstruction is an *upper*-`r` threshold (tower counted pairs) or an
`r`-independent residue/congruence (class-0/class-1), so the wave-8 lower floor `r ≥ 32`
narrows the live window but leaves the residual demand intact. -/
def pairInstanceClosureStatus : List String :=
  [ "FLOOR (proved): r >= 32 (pic_r_ge_32 = n24_r_ge_thirtytwo) and m0 >= 2 (pic_m0_ge_two = " ++
      "two_le_towerSparsityBlock_everywhere) at EVERY actual failure context; shellWidth >= 33 " ++
      "(pic_shellWidth_ge_33).",
    "TOWER COUNTED PAIRS (two-sided windows, proved): the m0-threshold count bounds become " ++
      "r-windows via m0 = floor((3(r+1)+63)/64).  q=9 closes r<=41 (m0<=2), escape r>=42; " ++
      "q=11 (K0=5) closes r<=84 (m0<=4), escape r>=85; q=13 (K0=6) closes r<=105 (m0<=5), " ++
      "escape r>=106; (105,52) closes r<=148 (m0<=7), escape r>=149.  Live closure window is " ++
      "[32, rUpper] in each case.",
    "TOWER SURVIVING (residual, UNCHANGED by r>=32): tower class-2 | q=9 | r>=42 (m0>=3); " ++
      "q=11 | r>=85 (m0>=5); q=13 | r>=106 (m0>=6); (105,52) | r>=149 (m0>=8); (15,K0<=2) | " ++
      "the fixed pair; (105,K0=7) | the fixed point.  These ARE the low branches of " ++
      "TowerModulusEnumEscape - the wave-8 floor (lower edge) does NOT move these upper-edge " ++
      "thresholds, so NO new tower pair closes.",
    "CLASS-0 CHERNOFF SURVIVORS (19, UNCHANGED): residue-window misses mod c are " ++
      "r-INDEPENDENT (ChernoffClass0SurvivorClosure: the unconditional facts exclude no " ++
      "residue class; the r=0 top pin is vacuous since r>=1).  r>=32 changes nothing.  Pairs " ++
      "(q,K0):(c,rho): (17,8):(4,0) (19,9):(9,6) (21,1):(2,0) (25,2):(10,0) (25,12):(10,8) " ++
      "(27,1):(9,0) (27,4):(9,0) (27,13):(9,7) (29,14):(14,10) (33,1):(5,0) (33,16):(5,0) " ++
      "(35,2):(5,0) (37,18):(18,10) (39,1):(4,0) (41,20):(10,8) (43,21):(7,6) (45,1):(5,0) " ++
      "(45,2):(5,0) (45,4):(5,0).  All RESIDUE-SHRUNK, none closed.",
    "CLASS-1 CNL PAIRS (23, UNCHANGED): band-4 residue congruences k%c=j4%c are r-INDEPENDENT " ++
      "(CNLClass1PairClosure).  Pairs: 25@{2,12} 29@14 37@18 41@20 47@23 49@{3,24} 35@{3,17} " ++
      "39@6 55@5 57@{1,28} 63@10 69@{11,34} 75@{7,12,37} 87@{1,14} 99@5, plus q>=101 tail.  " ++
      "All CONGRUENCE-PINNED, none closed by r>=32.",
    "RUN BAND-1 / DENSEPACK: the run class-5 (q<64) band-{1,4} pairs and the densePackUngated " ++
      "residual carry ceil(W/c)-window or band-count obstructions; r>=32 widens W (harder), " ++
      "does not close them.",
    "COFACTOR CROSS (proved): mersenneSmallOrderModuli {3,5,7,9,15,21,31,63} INTERSECT " ++
      "class1ClosedModuli {27,31,33,43,45,51,65,85,91,93} = {31} (pic_cofactor_31_closed); " ++
      "surviving cofactors {3,5,7,9,15,21,63} (picCofactorsSurviving_eq), of which 63 is the " ++
      "open class-1 pair 63@10.",
    "VERDICT (honest): r>=32 closes NO new counted pair, class-0 survivor, or class-1 pair.  " ++
      "Only the already-unconditional empty-fibre families (15,7)/(105 off-fixed) close " ++
      "outright.  The successor surface is EQUIVALENT to Erdos260PushResidual (the escape " ++
      "thresholds are wave-3-5 upper edges the r-lower floor cannot move), not strictly " ++
      "smaller.  A FUTURE floor push to r>=42/85/106/149 would void the tower windows." ]

/-! ## Part 7.  The successor surface (equivalent, bridged into the capstone shapes)

The honest closure verdict (Part 6) is that no whole field of `Erdos260PushResidual` is
discharged by `r ≥ 32`, so the successor surface is **equivalent** to the wave-8 push
surface, re-presented with the proved two-sided windows exposed.  It is additive (it wraps
the existing surface) and routes to `Erdos260Statement` with no re-proving. -/

/-- **The wave-8 per-pair instance surface** — equivalent to `Erdos260PushResidual`, carrying
the same 14-field obligation, now annotated by the proved per-pair `r`-windows of Parts 2–4. -/
structure Erdos260PairInstanceResidual where
  /-- The underlying wave-8 push surface (no field is dischargeable by `r ≥ 32`). -/
  toPushResidual : Erdos260PushResidual

namespace Erdos260PairInstanceResidual

/-- `Erdos260Statement` from the per-pair instance surface, through the push surface
(hence the scale-floor push and the entire unconditional lineage). -/
theorem toStatement (H : Erdos260PairInstanceResidual) : Erdos260Statement :=
  erdos260_of_pushResidual H.toPushResidual

end Erdos260PairInstanceResidual

/-- **The endpoint**: `Erdos260Statement` from the per-pair instance surface. -/
theorem erdos260_of_pairInstanceResidual (H : Erdos260PairInstanceResidual) :
    Erdos260Statement :=
  H.toStatement

/-- Weakening witness: any push provider yields the per-pair instance surface. -/
def pairInstanceResidual_of_pushResidual (H : Erdos260PushResidual) :
    Erdos260PairInstanceResidual :=
  ⟨H⟩

/-- **The successor surface is equivalent to the wave-8 push surface** — the per-pair
re-cut hides no strength and closes no field, so this is a presentation refinement. -/
theorem nonempty_pairInstanceResidual_iff_push :
    Nonempty Erdos260PairInstanceResidual ↔ Nonempty Erdos260PushResidual :=
  ⟨fun ⟨H⟩ => ⟨H.toPushResidual⟩, fun ⟨H⟩ => ⟨⟨H⟩⟩⟩

/-! ## Part 8.  Honesty witnesses -/

/-- The status ledger is non-empty (honest, non-vacuous). -/
theorem pairInstanceClosureStatus_nonempty : pairInstanceClosureStatus ≠ [] := by
  simp [pairInstanceClosureStatus]

/-- The outright-closed ledger is non-empty. -/
theorem pairInstanceClosedUnderRGe32_nonempty : pairInstanceClosedUnderRGe32 ≠ [] := by
  simp [pairInstanceClosedUnderRGe32]

/-! ## Part 9.  Axiom audit -/

#print axioms pic_r_ge_32
#print axioms pic_m0_ge_two
#print axioms pic_shellWidth_ge_33
#print axioms m0Floor_le_iff
#print axioms m0Floor_eq_block
#print axioms r_window_q9
#print axioms r_window_q11
#print axioms r_window_q13
#print axioms r_window_q105
#print axioms tower_q9_closes_of_r_le_41
#print axioms tower_q11_closes_of_r_le_84
#print axioms tower_q13_closes_of_r_le_105
#print axioms tower_q105_K₀52_closes_of_r_le_148
#print axioms tower_q15_K₀7_closes
#print axioms tower_q9_escape_iff_r_ge_42
#print axioms tower_q11_escape_iff_r_ge_85
#print axioms tower_q13_escape_iff_r_ge_106
#print axioms tower_q105_escape_iff_r_ge_149
#print axioms tower_q9_dichotomy
#print axioms tower_q11_dichotomy
#print axioms tower_q13_dichotomy
#print axioms tower_q105_K₀52_dichotomy
#print axioms picCofactorsSurviving_eq
#print axioms picCofactorsClosedByClass1_eq
#print axioms pic_cofactor_31_closed
#print axioms erdos260_of_pairInstanceResidual
#print axioms nonempty_pairInstanceResidual_iff_push
#print axioms pairInstanceClosureStatus_nonempty
#print axioms pairInstanceClosedUnderRGe32_nonempty

end Erdos260
