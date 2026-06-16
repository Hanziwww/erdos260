import Erdos260.Erdos260EndgameCapstone

/-!
# Deep shells and enumerable tails of the wave-17 endgame surface

Wave-18 worker module on the four remaining enumerable/tail lanes of
`Erdos260EndgameCapstone` (`Erdos260EndgameResidual`, 14 fields).

## Workstream 1 — the deep shells `L > T` at the 110 class-1 table pairs

* **THE PARAMETRIC WIDTH GATE (the headline)**: the in-tree failure cap
  `2^24·W < 17·X` (`em_supportShell_strict`) combined with the GENERIC width count
  `|fibre₁| ≤ W` (`tfaFibre_card_le_width`) discharges the budget-free class-1 gate
  `24·n·L ≤ 31·X` (`sreAbsorption_of_nat_gate`) at EVERY context with
  `L ≤ ⌊31·2^24/408⌋ = 1274739` — independent of the datum `(q, K₀)`, of the period
  `c` and of the band-4 count `b4` (`dstClass1Absorption_of_depth_le`; ℕ core
  `dstWidthGate`, sharp at `1274740`, `dstWidthGate_sharp`).  This strictly EXTENDS
  the certified regime at the three table rows with `T < 1274739` — `(105,7)`
  (`T = 616809`), `(63,10)` and `(155,15)` (`T = 1233618`) — and covers every
  off-table datum (in particular the whole `200 ≤ q` tail) up to the same depth.
* **THE SUM ROUTE IS BLOCKED (honest negative)**: the only in-tree global deviation
  budget is the Lemma 21.1 pressure floor itself, and it sits ABOVE the corrected
  class-1 capacity at every context: `(31/1536)·X < (1/2)·X·(r+1) ≤ highExcessMass`
  (`dstSumRouteBudget_above_cap`).  Bounding `mass₁` by the global excess/deviation
  total can therefore NEVER clear the cap — there is no `c₀·X`-sized deviation
  budget in the tree, and the deep shells do NOT close all at once.
* **THE MINIMAL PER-PAIR DEEP ATOM**: at a table row `(q, K₀, c, b4, T)` the
  honest residual demand is confined to `max T 1274739 < L`
  (`DstClass1DeepPairAtom`, closure witness `dstClass1Pair_of_deepAtom`); such
  contexts carry `r ≥ 82` (`dstDeepShell_r_ge_82`; `r ≥ 1160` beyond the table
  maximum `T = 17887472`, `dstDeepShell_r_ge_1160`) on top of the q-side pin floor
  `L ≥ 986888` (all table rows have `q ≤ 199 < 384`, `dstTable_q_lt_384`).

## Workstream 2 — the `q ≥ 200` class-1 tail

* `dstClass1Tail_of_largeQ`: the parametric tail closure — at any `200 ≤ q` datum
  the field shape closes for `L ≤ 1274739`.  The brief's constant-`K` form
  `T ≥ 15·2^24·q/(408·K)` is SUBSUMED: the width cap `W < (17/2^24)·X` replaces
  the cycle-density count `b4·⌈W/c⌉` outright, and the resulting threshold
  `⌊31·2^24/408⌋` is q-uniform (no orbit equidistribution input is needed, and
  none is available in-tree).
* **NO `b4 = 0` THRESHOLD EXISTS**: band-4 membership is the interval condition
  `8 ≤ q/K < 16` (`canonGap q K = 4`), and the residue `K = q/8` realizes it at
  every modulus `q ≥ 64` (`dstBand4Residue_exists`) — the band-4 residue SET is
  never empty above `q₀ = 64`, so the tail cannot be closed by residue-level
  vacuity at any `q₀`; whether the ORBIT meets band 4 stays a per-pair fact
  (49 of the 136 sweep pairs were band-4-free), and no strip table applies.

## Workstream 3 — the tower enum lanes

No new unconditional closure exists: the `TowerModulusEnumeration` per-pair
thresholds `m₀ ≤ t ≈ c/b4` are sharp for the cycle-counting route (above them the
demanded density `1/m₀` falls below the certified cycle density `b4/c`).  Delivered
instead: (a) the parametric NECESSARY condition — any `Class2CycleInequality`
witness period at a band-4-reading cycle has `m₀ ≤ c`
(`dstTowerCycle_block_le_period`, verdict form `dstClass2Cycle_bandFree_or_blockLong`);
(b) the lane context floors — every `q < 107` tower context carries `L ≥ 986888`,
`r ≥ 63`, `m₀ ≥ 3`, every tail context `L ≥ 493461`, `r ≥ 32`, `m₀ ≥ 2`
(`dstBlock_ge_two`), with the pin upgrade below `q < 384`; (c) the exact wave-17
field shapes produced from floor-guarded supplies (`dstTowerEnumLow_field_of_floors`
/ `dstTowerEnumTail_field_of_floors`).

## Workstream 4 — the run numeric lanes (band-4-free contexts)

Same treatment: (a) the parametric NECESSARY conditions — a `Class5CycleNumericCloses`
witness has a band-{1,4}-free cycle or period `c ≥ 1537`
(`dstRunCycleNumeric_period_floor`, `dstClass5CycleNumeric_bandFree_or_long`); a
`Class5BandHeavyNumericCloses` witness has a band-1-free cycle or period `c ≥ 6145`
(`dstRunBandHeavy_period_floor`, `dstClass5BandHeavy_bandFree_or_long` — and the
witness carries `c ≤ W`, so its support width is at least `6145` there).  Both
floors are forced by the proved multiplier floor `runDyadicMult ≥ 31·L ≥ 31·493461`
against the `31/3072` / `31/6144` shares — at every `q < 64` datum the minimal
orbit period is `≤ 63`, so the band-free horn is the only realistic route (the
in-tree `RunCycleNumericClosure` verdict).  (b) The exact wave-17 field shapes from
floor-guarded supplies (`dstRunNumericLow_field_of_floors` /
`dstRunNumericTail_field_of_floors`).

No `sorry`, no `admit`, no new `axiom`, no `native_decide` (`decide` only on the
closed 110-row table scan and small numerals); additive only — no existing module
is edited; built standalone as `Erdos260.DeepShellTailClosure`.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Part 0.  Pinned constant shares and the ceiling workhorse -/

/-- The split Section 26 run share, numerically: `c⋆·ξ/12 = 31/3072`. -/
private theorem dstShare12_eq :
    erdos260Constants.cStar * erdos260Constants.ξ / 12 = 31 / 3072 := by
  have h1 : erdos260Constants.cStar = manuscriptCstar := rfl
  have h2 : erdos260Constants.ξ = manuscriptXi := rfl
  rw [h1, h2]
  unfold manuscriptCstar manuscriptXi
  norm_num

/-- The heavy half-share, numerically: `c⋆·ξ/24 = 31/6144`. -/
private theorem dstShare24_eq :
    erdos260Constants.cStar * erdos260Constants.ξ / 24 = 31 / 6144 := by
  have h1 : erdos260Constants.cStar = manuscriptCstar := rfl
  have h2 : erdos260Constants.ξ = manuscriptXi := rfl
  rw [h1, h2]
  unfold manuscriptCstar manuscriptXi
  norm_num

/-- The ℕ ceiling-division covering bound: `W ≤ ⌈W/c⌉·c`. -/
private theorem dstCeil_mul_ge {W c : ℕ} (hc : 1 ≤ c) :
    W ≤ (W + c - 1) / c * c := by
  obtain ⟨m, hm⟩ : ∃ m, (W + c - 1) / c = m := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, (W + c - 1) % c = s := ⟨_, rfl⟩
  have hdm := Nat.div_add_mod (W + c - 1) c
  rw [hm, hs] at hdm
  have hmod : s < c := by
    rw [← hs]
    exact Nat.mod_lt _ (by omega)
  rw [hm]
  have h1 : W + (c - 1) ≤ c * m + (c - 1) := by
    have hWc : W + (c - 1) = W + c - 1 := by omega
    rw [hWc, ← hdm]
    exact Nat.add_le_add_left (by omega) _
  have h2 : W ≤ c * m := Nat.le_of_add_le_add_right h1
  calc W ≤ c * m := h2
    _ = m * c := Nat.mul_comm c m

/-! ## Part 1.  Workstream 1+2: the parametric width gate

The corrected class-1 demand is `card(fibre₁)·Y ≤ (31/1536)·X` with `Y = L/64`; the
budget-free engine (`sreAbsorption_of_nat_gate`) reduces it to a count cap `n` plus
the ℕ gate `24·n·L ≤ 31·X`.  The SRE table route took `n = b4·⌈W/c⌉` (needs the
certified per-pair `(c, b4)` and the regime `408·b4·L ≤ 15·2^24·c`).  THIS route
takes the GENERIC width cap `n = W` (`tfaFibre_card_le_width`) against the failure
cap `2^24·W < 17·X` (`em_supportShell_strict`): the gate closes iff
`408·L ≤ 31·2^24`, i.e. `L ≤ 1274739` — no datum, period or band data at all. -/

/-- **The parametric width gate (pure ℕ)**: the failure cap `2^24·W ≤ 17·X` and the
depth regime `L ≤ 1274739 = ⌊31·2^24/408⌋` give the class-1 absorption gate
`24·W·L ≤ 31·X` (margin: `408·1274739 = 520093512 ≤ 520093696 = 31·2^24`). -/
private theorem dstWidthGate {W L X : ℕ}
    (hW : 16777216 * W ≤ 17 * X) (hL : L ≤ 1274739) :
    24 * (W * L) ≤ 31 * X := by
  have key : 16777216 * (24 * (W * L)) ≤ 16777216 * (31 * X) := by
    calc 16777216 * (24 * (W * L))
        = 24 * L * (16777216 * W) := by ring
      _ ≤ 24 * L * (17 * X) := Nat.mul_le_mul le_rfl hW
      _ = 408 * L * X := by ring
      _ ≤ 408 * 1274739 * X :=
          Nat.mul_le_mul (Nat.mul_le_mul le_rfl hL) le_rfl
      _ = 520093512 * X := by norm_num
      _ ≤ 520093696 * X := Nat.mul_le_mul (by norm_num) le_rfl
      _ = 16777216 * (31 * X) := by ring
  exact Nat.le_of_mul_le_mul_left key (by norm_num)

/-- **The width gate is sharp at `1274740`**: the pure-ℕ implication fails one step
above the threshold (witness `W = 17`, `X = 2^24`:
`408·1274740 = 520093920 > 520093696 = 31·2^24`). -/
theorem dstWidthGate_sharp :
    ∃ W X : ℕ, 16777216 * W ≤ 17 * X ∧ ¬ 24 * (W * 1274740) ≤ 31 * X :=
  ⟨17, 16777216, by norm_num, by norm_num⟩

/-- **THE PARAMETRIC CLASS-1 CLOSURE (the workstream-1/2 headline)**: at EVERY actual
failure context with `L ≤ 1274739` the corrected class-1 count-cap absorption holds in
the exact capstone field shape — independent of the datum `(q, K₀)`, with NO table
row, period certificate or band-4 count.  Inputs: the generic width count
`|fibre₁| ≤ W` (`tfaFibre_card_le_width`), the failure cap `2^24·W < 17·X`
(`em_supportShell_strict`), the budget-free gate engine
(`sreAbsorption_of_nat_gate`). -/
theorem dstClass1Absorption_of_depth_le (ctx : ActualFailureContext)
    (hL : shellLadderDepth ctx ≤ 1274739) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hW := em_supportShell_strict ctx
  unfold emW at hW
  exact sreAbsorption_of_nat_gate ctx ((supportShell ctx.shell.d ctx.shell.X).card)
    (tfaFibre_card_le_width ctx (genuineChargeRoute ctx) 1)
    (dstWidthGate (le_of_lt hW) hL)

/-- **The `200 ≤ q` tail closure (workstream 2)**: the parametric theorem of the
brief, with the q-UNIFORM threshold `⌊31·2^24/408⌋ = 1274739` in place of the
`K`-dependent `15·2^24·q/(408·K)` — the width cap subsumes every cycle-density
count, so no density constant `K` and no `q`-growth is needed (and none is
derivable in-tree: orbit equidistribution is not formalized). -/
theorem dstClass1Tail_of_largeQ (ctx : ActualFailureContext)
    (hq : 200 ≤ (class1SlopeDatum ctx).q)
    (hL : shellLadderDepth ctx ≤ 1274739) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) :=
  dstClass1Absorption_of_depth_le ctx hL

/-- **No `b4 = 0` modulus threshold exists (workstream-2 honest verdict)**: at every
modulus `q ≥ 64` the residue `K = q/8` reads band 4 (`canonGap q K = 4`, the
interval condition `8 ≤ q/K < 16`) — the band-4 residue set is NEVER empty above
`q₀ = 64`, so the `200 ≤ q` tail cannot be closed by residue-level band-4 vacuity
at any threshold `q₀`, and no finite strip table applies.  (Orbit-level vacuity
stays a genuine per-pair fact — 49 of the 136 sweep pairs.) -/
theorem dstBand4Residue_exists (q : ℕ) (hq : 64 ≤ q) :
    ∃ K : ℕ, 1 ≤ K ∧ K < q ∧ canonGap q K = 4 := by
  refine ⟨q / 8, ?_, ?_, ?_⟩
  · calc 1 ≤ 8 := by norm_num
      _ = 64 / 8 := by norm_num
      _ ≤ q / 8 := Nat.div_le_div_right hq
  · exact Nat.div_lt_self (by omega) (by norm_num)
  · have hq8 : 8 ≤ q / 8 := by
      calc 8 = 64 / 8 := by norm_num
        _ ≤ q / 8 := Nat.div_le_div_right hq
    have hq8pos : 0 < q / 8 := by omega
    have h8 : 8 ≤ q / (q / 8) := by
      rw [Nat.le_div_iff_mul_le hq8pos]
      calc 8 * (q / 8) = q / 8 * 8 := Nat.mul_comm _ _
        _ ≤ q := Nat.div_mul_le_self q 8
    have h16 : q / (q / 8) < 16 := by
      rw [Nat.div_lt_iff_lt_mul hq8pos]
      have hdm := Nat.div_add_mod q 8
      have hmod : q % 8 < 8 := Nat.mod_lt _ (by norm_num)
      obtain ⟨d, hd⟩ : ∃ d, q / 8 = d := ⟨_, rfl⟩
      rw [hd] at hdm hq8 ⊢
      omega
    have hlog : Nat.log 2 (q / (q / 8)) = 3 :=
      Nat.log_eq_of_pow_le_of_lt_pow (by simpa using h8) (by simpa using h16)
    unfold canonGap
    rw [hlog]

/-! ## Part 2.  Workstream 1: the sum route is blocked, the deep atoms are minimal -/

/-- **THE SUM ROUTE CANNOT CLEAR THE CAP (honest negative verdict)**: the only
in-tree global deviation/excess budget — the Lemma 21.1 pressure floor on the
high-excess mass — sits STRICTLY ABOVE the corrected class-1 capacity at every
actual context: `(31/1536)·X < (1/2)·X·(r+1) ≤ highExcessMass`.  Any route bounding
`mass₁` by the GLOBAL excess/deviation total (e.g. `em_windowExcess_le_devWindow`
summed over the fibre, then over all starts) is therefore structurally unable to
close the deep shells: the budget itself exceeds the target cap by the factor
`≥ 768/31·(r+1)`.  The deep-shell residual is genuinely per-pair. -/
theorem dstSumRouteBudget_above_cap (ctx : ActualFailureContext) :
    erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ)
      < highExcessMass
          (highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
            ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y)
          (hitGap ctx.n24CarryData.a) ctx.n24CarryData.r ctx.n24CarryData.T := by
  have hfloor2 : (1 / 2 : ℝ) * (ctx.shell.X : ℝ) * ((ctx.n24CarryData.r : ℝ) + 1)
      ≤ highExcessMass
          (highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
            ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y)
          (hitGap ctx.n24CarryData.a) ctx.n24CarryData.r ctx.n24CarryData.T :=
    ctx.n24CarryData.highExcessMass_lower
  have hX : (0 : ℝ) < (ctx.shell.X : ℝ) := ctx.shell.X_pos_real
  have hr : (0 : ℝ) ≤ (ctx.n24CarryData.r : ℝ) := Nat.cast_nonneg _
  have hcap : erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ)
      < (1 / 2 : ℝ) * (ctx.shell.X : ℝ) * ((ctx.n24CarryData.r : ℝ) + 1) := by
    rw [correctedCnlShare_eq]
    nlinarith [mul_nonneg hX.le hr]
  exact lt_of_lt_of_le hcap hfloor2

/-- Every threshold-table row has `q ≤ 199 < 384` — the q-side pin floor applies at
ALL 110 pairs (kernel scan of the closed table). -/
theorem dstTable_q_lt_384 :
    ∀ p ∈ sreClass1ThresholdTable, p.1 < 384 := by decide

/-- **The deep-shell `r` floor at the parametric threshold**: every context beyond
the width-gate regime (`L ≥ 1274740`) carries `r ≥ 82`
(`82·2^18 = 21495808 ≤ 17·1274740 = 21670580`). -/
theorem dstDeepShell_r_ge_82 (ctx : ActualFailureContext)
    (hL : 1274740 ≤ shellLadderDepth ctx) : 82 ≤ ctx.n24CarryData.r :=
  floorPushV2_r_lower ctx hL (by norm_num)

/-- **The `r` floor beyond the table maximum**: every context beyond the LARGEST
table threshold (`T = 17887472` at `(175,2)/(177,1)/(177,88)`) carries `r ≥ 1160`
(sharp to one unit: `1160·2^18 = 304087040 ≤ 17·17887473 = 304087041`). -/
theorem dstDeepShell_r_ge_1160 (ctx : ActualFailureContext)
    (hL : 17887473 ≤ shellLadderDepth ctx) : 1160 ≤ ctx.n24CarryData.r :=
  floorPushV2_r_lower ctx hL (by norm_num)

/-- **The minimal per-pair deep atom (workstream-1 deliverable b)**: at a certified
table pair the ONLY remaining class-1 demand, after the SRE regime gate (`L ≤ T`)
and the parametric width gate (`L ≤ 1274739`), is the field shape on the deep
shells `max T 1274739 < L` — where the context provably carries `L ≥ 986888`
(q-side pin, `q ≤ 199`), `r ≥ 82` (`dstDeepShell_r_ge_82`) and the certified
`(c, b4)` data of the row. -/
def DstClass1DeepPairAtom (qv Kv Tv : ℕ) : Prop :=
  ∀ ctx : ActualFailureContext,
    (class1SlopeDatum ctx).q = qv → (class1SlopeDatum ctx).K₀ = Kv →
    Tv < shellLadderDepth ctx → 1274739 < shellLadderDepth ctx →
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ)

/-- **The per-pair closure from the deep atom alone**: at a table row, the SRE
dispatcher (regime `L ≤ T`), the parametric width gate (`T < L ≤ 1274739`) and the
deep atom (`max T 1274739 < L`) jointly close the corrected class-1 absorption at
EVERY context carrying the row's datum — the atom is exactly the missing piece. -/
theorem dstClass1Pair_of_deepAtom {qv Kv cv bv Tv : ℕ}
    (hmem : (qv, Kv, cv, bv, Tv) ∈ sreClass1ThresholdTable)
    (hatom : DstClass1DeepPairAtom qv Kv Tv) :
    ∀ ctx : ActualFailureContext,
      (class1SlopeDatum ctx).q = qv → (class1SlopeDatum ctx).K₀ = Kv →
      ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
          * ctx.n24CarryData.Y
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  intro ctx hq hK
  rcases Nat.lt_or_ge Tv (shellLadderDepth ctx) with hT | hT
  · rcases Nat.lt_or_ge 1274739 (shellLadderDepth ctx) with hP | hP
    · exact hatom ctx hq hK hT hP
    · exact dstClass1Absorption_of_depth_le ctx hP
  · exact sreClass1Absorption_of_mem ctx hmem hq hK hT

/-- **The deep-shell context floors at a table row**: any context at a certified
pair beyond the parametric threshold carries the pin depth floor AND the deep `r`
floor — the sharply-stated environment of the per-pair atom. -/
theorem dstDeepShell_context_floors (ctx : ActualFailureContext)
    {qv Kv cv bv Tv : ℕ}
    (hmem : (qv, Kv, cv, bv, Tv) ∈ sreClass1ThresholdTable)
    (hq : (class1SlopeDatum ctx).q = qv)
    (hP : 1274740 ≤ shellLadderDepth ctx) :
    986888 ≤ shellLadderDepth ctx ∧ 82 ≤ ctx.n24CarryData.r := by
  refine ⟨?_, dstDeepShell_r_ge_82 ctx hP⟩
  have hqlt : qv < 384 := dstTable_q_lt_384 _ hmem
  exact sreDepth_ge_986888_of_q_lt_384 ctx (by omega)

/-- **The exact wave-17 `class1CapAbsorption` field from the DEEP supply alone**:
the capstone field shape (demanded at `1 ≤ r` and off-regime data) follows from a
supply restricted to the genuinely deep contexts `L ≥ 1274740` (which all carry
`r ≥ 82`) — the entire band `L ≤ 1274739` is relieved by the parametric width gate,
ON TOP of the 110-pair `L ≤ T` relief already in the capstone.  Additive wiring:
`R.class1CapAbsorption := dstClass1CapAbsorption_field_of_deep hdeep`. -/
theorem dstClass1CapAbsorption_field_of_deep
    (hdeep : ∀ ctx : ActualFailureContext,
      1274740 ≤ shellLadderDepth ctx → 82 ≤ ctx.n24CarryData.r →
      1 ≤ ctx.n24CarryData.r →
      ¬ (∃ cv bv Tv : ℕ,
        ((class1SlopeDatum ctx).q, (class1SlopeDatum ctx).K₀, cv, bv, Tv)
            ∈ sreClass1ThresholdTable
          ∧ shellLadderDepth ctx ≤ Tv) →
      ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
          * ctx.n24CarryData.Y
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ)) :
    ∀ ctx : ActualFailureContext,
      1 ≤ ctx.n24CarryData.r →
      ¬ (∃ cv bv Tv : ℕ,
        ((class1SlopeDatum ctx).q, (class1SlopeDatum ctx).K₀, cv, bv, Tv)
            ∈ sreClass1ThresholdTable
          ∧ shellLadderDepth ctx ≤ Tv) →
      ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
          * ctx.n24CarryData.Y
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  intro ctx hr hreg
  rcases Nat.lt_or_ge 1274739 (shellLadderDepth ctx) with hP | hP
  · exact hdeep ctx (by omega) (dstDeepShell_r_ge_82 ctx (by omega)) hr hreg
  · exact dstClass1Absorption_of_depth_le ctx hP

/-! ## Part 3.  Workstream 4: the run numeric lanes — parametric period floors -/

/-- The real-arithmetic core of the run cycle-numeric obstruction: with the
multiplier floor `M ≥ 31·493461`, a covering `W ≤ N·c` and a short period
`c ≤ 1536`, the inequality `(17/2^24)·N·M ≤ (31/3072)·W` is impossible
(`17·15297291·3072 = 798885725184 > 798863917056 = 31·2^24·1536`). -/
private theorem dstRunCycleCore {Wr Nr cr M : ℝ}
    (hW1 : 1 ≤ Wr) (hc0 : 0 < cr) (hc : cr ≤ 1536)
    (hWN : Wr ≤ Nr * cr) (hM : 15297291 ≤ M) (hM0 : 0 ≤ M)
    (hineq : 17 / 16777216 * Nr * M ≤ 31 / 3072 * Wr) : False := by
  have h1 : 17 / 16777216 * Nr * M * cr ≤ 31 / 3072 * Wr * cr :=
    mul_le_mul_of_nonneg_right hineq hc0.le
  have hWnn : (0 : ℝ) ≤ Wr := by linarith
  have h2 : 31 / 3072 * Wr * cr ≤ 31 / 3072 * Wr * 1536 := by
    nlinarith [mul_nonneg hWnn (show (0 : ℝ) ≤ 1536 - cr by linarith)]
  have h3 : 17 / 16777216 * Wr * M ≤ 17 / 16777216 * Nr * M * cr := by
    nlinarith [mul_le_mul_of_nonneg_right hWN hM0]
  have h4 : 17 / 16777216 * Wr * 15297291 ≤ 17 / 16777216 * Wr * M := by
    nlinarith [mul_le_mul_of_nonneg_left hM
      (show (0 : ℝ) ≤ 17 / 16777216 * Wr by positivity)]
  linarith

/-- **The run cycle-numeric period floor (workstream-4 parametric)**: if the period
window reads band {1,4} at all (`#class5CycleBand ≥ 1`), the
`Class5CycleNumericCloses` inequality at that period FORCES `c ≥ 1537` — the proved
multiplier floor `runDyadicMult ≥ 31·L ≥ 31·493461` against the `31/3072` share
caps the admissible density `1/c` from above.  At any `q < 64` datum the minimal
orbit period is `≤ 63 < 1537`: on minimal periods the band-free horn is the ONLY
route (the in-tree per-pair verdict, now parametric). -/
theorem dstRunCycleNumeric_period_floor (ctx : ActualFailureContext) {c : ℕ}
    (hc : 1 ≤ c)
    (hcnt : 1 ≤ (class5CycleBand ctx c).card)
    (hineq : erdos260Constants.c0
        * (((class5CycleBand ctx c).card
            * (((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c) : ℕ) : ℝ)
        * runDyadicMult ctx
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 12
        * ((supportShell ctx.d ctx.X).card : ℝ)) :
    1537 ≤ c := by
  by_contra hcon
  rw [carryWord_c0_eq, dstShare12_eq, ← carryWord_shell_d_eq ctx,
    ← ActualFailureContext.shell_X ctx] at hineq
  have hW1 : 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card :=
    le_trans (Nat.le_add_left 1 ctx.n24CarryData.r) (cnlMulti_r_add_one_le_width ctx)
  have hWN : (supportShell ctx.shell.d ctx.shell.X).card
      ≤ (class5CycleBand ctx c).card
          * (((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c) * c := by
    calc (supportShell ctx.shell.d ctx.shell.X).card
        ≤ ((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c * c :=
          dstCeil_mul_ge hc
      _ ≤ (class5CycleBand ctx c).card
            * (((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c) * c :=
          Nat.mul_le_mul (Nat.le_mul_of_pos_left _ hcnt) le_rfl
  have hM : (15297291 : ℝ) ≤ runDyadicMult ctx := by
    have h31 := tfaRunDyadicMult_ge_31L ctx
    have hLg : (493461 : ℝ) ≤ ((shellLadderDepth ctx : ℕ) : ℝ) := by
      exact_mod_cast shellLadderDepth_ge_493461 ctx
    linarith
  refine dstRunCycleCore (Wr := ((supportShell ctx.shell.d ctx.shell.X).card : ℝ))
    (Nr := (((class5CycleBand ctx c).card
      * (((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c) : ℕ) : ℝ))
    (cr := (c : ℝ)) (M := runDyadicMult ctx)
    ?_ ?_ ?_ ?_ hM (runDyadicMult_nonneg ctx) hineq
  · exact_mod_cast hW1
  · exact_mod_cast hc
  · exact_mod_cast (show c ≤ 1536 by omega)
  · exact_mod_cast hWN

/-- **Verdict form**: any `Class5CycleNumericCloses` witness is band-{1,4}-free on
its period or has period `≥ 1537` — the parametric tail bound of workstream 4. -/
theorem dstClass5CycleNumeric_bandFree_or_long (ctx : ActualFailureContext)
    (h : Class5CycleNumericCloses ctx) :
    ∃ c : ℕ, 1 ≤ c
      ∧ (∀ m, 1 ≤ m →
          slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
            = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
      ∧ ((class5CycleBand ctx c).card = 0 ∨ 1537 ≤ c) := by
  obtain ⟨c, hc, hper, hineq⟩ := h
  refine ⟨c, hc, hper, ?_⟩
  rcases Nat.eq_zero_or_pos (class5CycleBand ctx c).card with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (dstRunCycleNumeric_period_floor ctx hc h1 hineq)

/-- **The heavy-split band-1 period floor**: if the period reads band 1 at all
(`#class5Band1CycleBand ≥ 1`), the half-density scalar of
`Class5BandHeavyNumericCloses` FORCES `c ≥ 6145`
(`2·17·15297291 = 520107894 > 520093696 = 31·2^24`, against the `31/6144` share). -/
theorem dstRunBandHeavy_period_floor (ctx : ActualFailureContext) {c : ℕ}
    (hcnt : 1 ≤ (class5Band1CycleBand ctx c).card)
    (hineq : 2 * (((class5Band1CycleBand ctx c).card : ℝ)
          * (erdos260Constants.c0 * runDyadicMult ctx))
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 24 * (c : ℝ)) :
    6145 ≤ c := by
  by_contra hcon
  rw [carryWord_c0_eq, dstShare24_eq] at hineq
  have hcR : (c : ℝ) ≤ 6144 := by exact_mod_cast (show c ≤ 6144 by omega)
  have hcntR : (1 : ℝ) ≤ ((class5Band1CycleBand ctx c).card : ℝ) := by
    exact_mod_cast hcnt
  have hM0 : (0 : ℝ) ≤ runDyadicMult ctx := runDyadicMult_nonneg ctx
  have hM : (15297291 : ℝ) ≤ runDyadicMult ctx := by
    have h31 := tfaRunDyadicMult_ge_31L ctx
    have hLg : (493461 : ℝ) ≤ ((shellLadderDepth ctx : ℕ) : ℝ) := by
      exact_mod_cast shellLadderDepth_ge_493461 ctx
    linarith
  have hkey : (1 : ℝ) * (17 / 16777216 * runDyadicMult ctx)
      ≤ ((class5Band1CycleBand ctx c).card : ℝ)
          * (17 / 16777216 * runDyadicMult ctx) :=
    mul_le_mul_of_nonneg_right hcntR
      (mul_nonneg (by norm_num) hM0)
  nlinarith [hkey, hineq, hcR, hM]

/-- **Verdict form**: any `Class5BandHeavyNumericCloses` witness is band-1-free on
its period or has period `≥ 6145` (and the witness carries `c ≤ W`, so the support
width is `≥ 6145` in the long horn). -/
theorem dstClass5BandHeavy_bandFree_or_long (ctx : ActualFailureContext)
    (h : Class5BandHeavyNumericCloses ctx) :
    ∃ c : ℕ, 1 ≤ c
      ∧ (∀ m, 1 ≤ m →
          slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
            = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
      ∧ c ≤ (supportShell ctx.shell.d ctx.shell.X).card
      ∧ ((class5Band1CycleBand ctx c).card = 0 ∨ 6145 ≤ c) := by
  obtain ⟨c, hc, hper, hcW, hb1, hheavy⟩ := h
  refine ⟨c, hc, hper, hcW, ?_⟩
  rcases Nat.eq_zero_or_pos (class5Band1CycleBand ctx c).card with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (dstRunBandHeavy_period_floor ctx h1 hb1)

/-! ## Part 4.  Workstream 3: the tower lanes — the block-vs-period bound -/

/-- **The tower cycle-counting necessary condition**: a `Class2CycleInequality`
period that reads band 4 at all (`towerBand4CycleCount ≥ 1`) must satisfy
`m₀ ≤ c` — the demanded density `1/m₀` cannot beat one band-4 hit per period
(`m₀·⌈K/c⌉ ≤ K` against `K ≤ ⌈K/c⌉·c`).  Sharp at the recorded hard pair
`(63,10)` (`c = 2`, density `1/2`): every deep shell has `m₀ ≥ 2`, so the
counting route closes nothing there. -/
theorem dstTowerCycle_block_le_period (ctx : ActualFailureContext) {c : ℕ}
    (hc : 1 ≤ c)
    (hcnt : 1 ≤ towerBand4CycleCount (class1SlopeDatum ctx).q
        (class1SlopeDatum ctx).K₀ c)
    (hineq : towerSparsityBlock ctx
        * (towerBand4CycleCount (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ c
            * ((shellWidth ctx + c - 1) / c))
      ≤ shellWidth ctx) :
    towerSparsityBlock ctx ≤ c := by
  have hK1 : 1 ≤ shellWidth ctx := one_le_width ctx
  have h1 : towerSparsityBlock ctx * ((shellWidth ctx + c - 1) / c)
      ≤ shellWidth ctx := by
    refine le_trans (Nat.mul_le_mul le_rfl ?_) hineq
    exact Nat.le_mul_of_pos_left _ hcnt
  have h2 : towerSparsityBlock ctx * shellWidth ctx ≤ shellWidth ctx * c := by
    calc towerSparsityBlock ctx * shellWidth ctx
        ≤ towerSparsityBlock ctx * ((shellWidth ctx + c - 1) / c * c) :=
          Nat.mul_le_mul le_rfl (dstCeil_mul_ge hc)
      _ = towerSparsityBlock ctx * ((shellWidth ctx + c - 1) / c) * c :=
          (Nat.mul_assoc _ _ _).symm
      _ ≤ shellWidth ctx * c := Nat.mul_le_mul h1 le_rfl
  have h3 : towerSparsityBlock ctx * shellWidth ctx ≤ c * shellWidth ctx := by
    calc towerSparsityBlock ctx * shellWidth ctx
        ≤ shellWidth ctx * c := h2
      _ = c * shellWidth ctx := Nat.mul_comm _ _
  exact Nat.le_of_mul_le_mul_right
    (by rwa [Nat.mul_comm (towerSparsityBlock ctx) (shellWidth ctx),
      Nat.mul_comm c (shellWidth ctx)] at h3) (by omega)

/-- **Verdict form**: any `Class2CycleInequality` witness is band-4-free on its
period or has period `≥ m₀` — the tower mirror of the run period floors. -/
theorem dstClass2Cycle_bandFree_or_blockLong (ctx : ActualFailureContext)
    (h : Class2CycleInequality ctx) :
    ∃ c : ℕ, 1 ≤ c
      ∧ (∀ m, 1 ≤ m →
          slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
            = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
      ∧ (towerBand4CycleCount (class1SlopeDatum ctx).q
            (class1SlopeDatum ctx).K₀ c = 0
        ∨ towerSparsityBlock ctx ≤ c) := by
  obtain ⟨c, hc, hper, hineq⟩ := h
  refine ⟨c, hc, hper, ?_⟩
  rcases Nat.eq_zero_or_pos (towerBand4CycleCount (class1SlopeDatum ctx).q
      (class1SlopeDatum ctx).K₀ c) with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (dstTowerCycle_block_le_period ctx hc h1 hineq)

/-- The sparsity block is `≥ 2` at EVERY actual context (from the unconditional
`r ≥ 32`: `m₀ = ⌈3(r+1)/64⌉ ≥ ⌈99/64⌉ = 2`). -/
theorem dstBlock_ge_two (ctx : ActualFailureContext) :
    2 ≤ towerSparsityBlock ctx := by
  have hr := n24_r_ge_thirtytwo ctx
  unfold towerSparsityBlock
  omega

/-! ## Part 5.  The four lane fields from floor-guarded supplies

The exact wave-17 field shapes, each produced from a supply that may ADDITIONALLY
assume the proved context floors — the supplies are relieved of every shallow /
low-`r` / small-block context.  All four wire additively:
`R.towerEnumLow := dstTowerEnumLow_field_of_floors h`, etc. -/

/-- **The `towerEnumLow` field from a floor-guarded supply**: every `q < 107` lane
context carries `L ≥ 986888` (q-side pin, `q < 107 < 384`), `r ≥ 63` and `m₀ ≥ 3`
(`q < 2^20`) — the supply may assume all three. -/
theorem dstTowerEnumLow_field_of_floors
    (h : ∀ ctx : ActualFailureContext,
      TowerModulusEnumEscapeV2 ctx → (class1SlopeDatum ctx).q < 107 →
      (ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx) →
      ¬ ((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1) →
      ¬ ((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3) →
      986888 ≤ shellLadderDepth ctx → 63 ≤ ctx.n24CarryData.r →
      3 ≤ towerSparsityBlock ctx →
      Class2CycleInequality ctx) :
    ∀ ctx : ActualFailureContext,
      TowerModulusEnumEscapeV2 ctx → (class1SlopeDatum ctx).q < 107 →
      (ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx) →
      ¬ ((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1) →
      ¬ ((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3) →
      Class2CycleInequality ctx := by
  intro ctx hesc hq haper h31 h213
  exact h ctx hesc hq haper h31 h213
    (sreDepth_ge_986888_of_q_lt_384 ctx (by omega))
    (floorPushV2_r_ge_63_of_q_le_2pow20 ctx (by omega))
    (floorPushV2_m0_ge_three_of_q_le_2pow20 ctx (by omega))

/-- **The `towerEnumTail` field from a floor-guarded supply**: every tail context
carries `L ≥ 493461`, `r ≥ 32`, `m₀ ≥ 2` unconditionally, upgraded to
`L ≥ 986888` on the pinned band `107 ≤ q < 384`. -/
theorem dstTowerEnumTail_field_of_floors
    (h : ∀ ctx : ActualFailureContext,
      TowerModulusEnumEscapeV2 ctx → 107 ≤ (class1SlopeDatum ctx).q →
      (ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx) →
      493461 ≤ shellLadderDepth ctx → 32 ≤ ctx.n24CarryData.r →
      2 ≤ towerSparsityBlock ctx →
      ((class1SlopeDatum ctx).q < 384 → 986888 ≤ shellLadderDepth ctx) →
      (((Nat.log 2 (class1SlopeDatum ctx).q + 1) * shellWidth ctx
          < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
              (class1SlopeDatum ctx).K₀)))
          ∧ TowerBand4Budget ctx)
        ∨ Class2CycleInequality ctx) :
    ∀ ctx : ActualFailureContext,
      TowerModulusEnumEscapeV2 ctx → 107 ≤ (class1SlopeDatum ctx).q →
      (ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx) →
      (((Nat.log 2 (class1SlopeDatum ctx).q + 1) * shellWidth ctx
          < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
              (class1SlopeDatum ctx).K₀)))
          ∧ TowerBand4Budget ctx)
        ∨ Class2CycleInequality ctx := by
  intro ctx hesc hq haper
  exact h ctx hesc hq haper (shellLadderDepth_ge_493461 ctx)
    (n24_r_ge_thirtytwo ctx) (dstBlock_ge_two ctx)
    (fun hq384 => sreDepth_ge_986888_of_q_lt_384 ctx hq384)

/-- **The `runNumericLow` field from a floor-guarded supply**: every `q < 64` lane
context carries `L ≥ 986888` and `r ≥ 63` (so `runDyadicMult ≥ 31·986888`) — the
supply may assume both. -/
theorem dstRunNumericLow_field_of_floors
    (h : ∀ ctx : ActualFailureContext,
      ¬ OrbitBandPinned ctx 4 → (class1SlopeDatum ctx).q < 64 →
      986888 ≤ shellLadderDepth ctx → 63 ≤ ctx.n24CarryData.r →
      Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx) :
    ∀ ctx : ActualFailureContext,
      ¬ OrbitBandPinned ctx 4 → (class1SlopeDatum ctx).q < 64 →
      Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx := by
  intro ctx hpin hq
  exact h ctx hpin hq (sreDepth_ge_986888_of_q_lt_384 ctx (by omega))
    (floorPushV2_r_ge_63_of_q_le_2pow20 ctx (by omega))

/-- **The `runNumericTail` field from a floor-guarded supply**: unconditional
`L ≥ 493461`, `r ≥ 32`, with the pin upgrade on `64 ≤ q < 384`. -/
theorem dstRunNumericTail_field_of_floors
    (h : ∀ ctx : ActualFailureContext,
      ¬ OrbitBandPinned ctx 4 → 64 ≤ (class1SlopeDatum ctx).q →
      ¬ ((class1SlopeDatum ctx).q = 93 ∧ (class1SlopeDatum ctx).K₀ = 15) →
      493461 ≤ shellLadderDepth ctx → 32 ≤ ctx.n24CarryData.r →
      ((class1SlopeDatum ctx).q < 384 → 986888 ≤ shellLadderDepth ctx) →
      (((Nat.log 2 (class1SlopeDatum ctx).q + 1)
          * (supportShell ctx.shell.d ctx.shell.X).card
        < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
            (class1SlopeDatum ctx).K₀)))
        ∧ RunBandBudget ctx)
      ∨ (Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx)) :
    ∀ ctx : ActualFailureContext,
      ¬ OrbitBandPinned ctx 4 → 64 ≤ (class1SlopeDatum ctx).q →
      ¬ ((class1SlopeDatum ctx).q = 93 ∧ (class1SlopeDatum ctx).K₀ = 15) →
      (((Nat.log 2 (class1SlopeDatum ctx).q + 1)
          * (supportShell ctx.shell.d ctx.shell.X).card
        < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
            (class1SlopeDatum ctx).K₀)))
        ∧ RunBandBudget ctx)
      ∨ (Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx) := by
  intro ctx hpin hq h93
  exact h ctx hpin hq h93 (shellLadderDepth_ge_493461 ctx)
    (n24_r_ge_thirtytwo ctx)
    (fun hq384 => sreDepth_ge_986888_of_q_lt_384 ctx hq384)

/-! ## Part 6.  Honest machine-readable status -/

/-- Honest machine-readable status of the deep-shell / tail closure module. -/
def deepShellTailClosureStatus : List String :=
  [ "SUBJECT (wave-18 worker): the four enumerable/tail lanes left open by the " ++
      "wave-17 endgame capstone (Erdos260EndgameResidual, 14 fields) - (1) the " ++
      "class-1 deep shells L > T at the 110 SurvivorRegimeEnumeration table pairs, " ++
      "(2) the un-enumerated 200 <= q class-1 tail, (3) towerEnumLow/towerEnumTail, " ++
      "(4) runNumericLow/runNumericTail on band-4-free contexts.",
    "HEADLINE (workstreams 1+2, PROVED - THE PARAMETRIC WIDTH GATE): " ++
      "dstClass1Absorption_of_depth_le closes the corrected class-1 count-cap " ++
      "absorption (the EXACT capstone field shape) at EVERY context with L <= " ++
      "floor(31*2^24/408) = 1274739, INDEPENDENT of the datum (q, K0), the period " ++
      "c and the band-4 count b4: the generic width count |fibre1| <= W " ++
      "(tfaFibre_card_le_width) against the failure cap 2^24*W < 17*X " ++
      "(em_supportShell_strict) feeds the budget-free gate engine " ++
      "(sreAbsorption_of_nat_gate); the multiplier of the class-1 lane is Y = L/64 " ++
      "(not the class-0/3 (r+1)(L+B+1) - this is exactly why class 1 is " ++
      "parametrically closable while tfaClass0Gate_not_from_failureCap blocks the " ++
      "same route for class 0).  Sharp at one step (dstWidthGate_sharp).  The " ++
      "uniform threshold 1274739 BEATS the per-pair T at three table rows - " ++
      "(105,7) T=616809, (63,10) and (155,15) T=1233618 - and covers every " ++
      "off-table datum (all 200 <= q, all non-divisor-pin data) up to L <= 1274739; " ++
      "above the q-side pin floor L >= 986888 the band [986888, 1274739] is " ++
      "genuinely non-vacuous at every survivor datum.",
    "DEEP-SHELL VERDICT (workstream 1, honest): the SUM route does NOT clear the " ++
      "deep shells - dstSumRouteBudget_above_cap proves the only in-tree global " ++
      "deviation/excess budget (the Lemma 21.1 pressure floor on highExcessMass) " ++
      "sits STRICTLY ABOVE the corrected class-1 capacity at every context: " ++
      "(31/1536)*X < (1/2)*X*(r+1) <= highExcessMass.  Bounding mass1 by the " ++
      "global deviation total (em_windowExcess_le_devWindow summed) is " ++
      "structurally hopeless; no c0*X-sized budget exists in-tree.  The residual " ++
      "is per-pair: DstClass1DeepPairAtom (q,K0,T) confines the missing demand to " ++
      "max T 1274739 < L (dstClass1Pair_of_deepAtom closes the WHOLE pair from " ++
      "the atom); such contexts carry L >= 986888 + r >= 82 " ++
      "(dstDeepShell_context_floors, dstDeepShell_r_ge_82; r >= 1160 beyond the " ++
      "table maximum T = 17887472, dstDeepShell_r_ge_1160; table-wide q <= 199 < " ++
      "384 by kernel scan, dstTable_q_lt_384).  Field wiring: " ++
      "dstClass1CapAbsorption_field_of_deep produces the exact wave-17 " ++
      "class1CapAbsorption field from a supply restricted to L >= 1274740 (with " ++
      "r >= 82 free).",
    "q >= 200 TAIL VERDICT (workstream 2, honest): NO b4 = 0 threshold exists - " ++
      "dstBand4Residue_exists shows the band-4 residue set (the interval condition " ++
      "8 <= q/K < 16, canonGap = 4) is non-empty at EVERY q >= 64 (witness K = " ++
      "q/8), so residue-level vacuity closes nothing above any q0 and no strip " ++
      "table [200, q0) applies (the Python generator technique was therefore NOT " ++
      "needed); orbit-level band-4 freeness stays per-pair (49/136 sweep pairs).  " ++
      "The parametric theorem dstClass1Tail_of_largeQ (200 <= q, L <= 1274739) " ++
      "delivers the brief's class1Tail_of_largeQ with the q-UNIFORM threshold " ++
      "floor(31*2^24/408) in place of 15*2^24*q/(408*K): the width cap subsumes " ++
      "every cycle-density count b4*ceil(W/c), and no orbit-equidistribution " ++
      "density bound (b4 <= c*K/q + 1) is available in-tree to push T with q.  " ++
      "The honest tail residual: off-table data at L > 1274739.",
    "TOWER LANES VERDICT (workstream 3, honest): no new unconditional closure - " ++
      "the TowerModulusEnumeration thresholds m0 <= t are SHARP for the counting " ++
      "route (above t the demanded density 1/m0 falls below the certified b4/c; " ++
      "multiples of the period scale both b4 and c).  Delivered: " ++
      "dstTowerCycle_block_le_period - any Class2CycleInequality period reading " ++
      "band 4 forces m0 <= c (verdict dstClass2Cycle_bandFree_or_blockLong: " ++
      "band-4-free or c >= m0); with m0 >= 2 everywhere (dstBlock_ge_two, from " ++
      "r >= 32) and m0 >= 3 at q < 2^20.  Context floors wired to the EXACT " ++
      "wave-17 field shapes: dstTowerEnumLow_field_of_floors (the q < 107 supply " ++
      "may assume L >= 986888, r >= 63, m0 >= 3) and " ++
      "dstTowerEnumTail_field_of_floors (L >= 493461, r >= 32, m0 >= 2, plus the " ++
      "pin upgrade L >= 986888 on 107 <= q < 384).  No generated table applies: " ++
      "the open tower regimes are genuinely above the sharp per-pair thresholds.",
    "RUN LANES VERDICT (workstream 4, honest): the in-tree RunCycleNumericClosure " ++
      "verdict (band-free or per-ctx scalars) is made PARAMETRIC: " ++
      "dstRunCycleNumeric_period_floor - a Class5CycleNumericCloses period reading " ++
      "band {1,4} forces c >= 1537 (proved multiplier floor runDyadicMult >= 31*L " ++
      ">= 31*493461 against the 31/3072 share; margin 798885725184 > " ++
      "798863917056); dstRunBandHeavy_period_floor - a Class5BandHeavyNumericCloses " ++
      "period reading band 1 forces c >= 6145 (and the witness carries c <= W).  " ++
      "Verdict forms dstClass5CycleNumeric_bandFree_or_long / " ++
      "dstClass5BandHeavy_bandFree_or_long.  Since every q < 64 (resp. q < 128) " ++
      "datum has minimal orbit period <= 63 (resp. <= 127), the band-free horn is " ++
      "the only route on minimal periods - the parametric form of the FTS Part-3 " ++
      "finding (exactly one closer (93,15) in [64,128)).  Field wiring: " ++
      "dstRunNumericLow_field_of_floors (q < 64 supply may assume L >= 986888, " ++
      "r >= 63) and dstRunNumericTail_field_of_floors (L >= 493461, r >= 32, pin " ++
      "upgrade below 384).",
    "WHAT REMAINS OPEN AFTER THIS MODULE (the honest core): (a) class-1 deep " ++
      "shells - per pair (q,K0,c,b4,T) the atom at max T 1274739 < L (r >= 82, " ++
      "L >= 986888, certified (c,b4)); off-table data at L > 1274739; (b) " ++
      "towerEnumLow above the sharp per-pair thresholds (m0 > t), the wave-4 " ++
      "families, the hard core (15,1)/(15,2)/(105,7)/(63,10), and the " ++
      "un-enumerated 107 <= q tail modulo the order-gt escape; (c) " ++
      "runNumericLow/Tail on the 54+79 band-carrying pairs (band-1 half-density " ++
      "and heavy-span scalars; periods below the 1537/6145 floors force the " ++
      "band-free horn); (d) the three orbit-pin voidings and the other wave-17 " ++
      "fields - untouched here.",
    "HYGIENE: additive only - ONE new module, no existing file edited, not " ++
      "root-wired (built standalone as Erdos260.DeepShellTailClosure); no sorry / " ++
      "admit / new axiom / native_decide (decide only on the closed 110-row table " ++
      "scan dstTable_q_lt_384); every key declaration passes #print axioms within " ++
      "[propext, Classical.choice, Quot.sound]." ]

/-- The status ledger is non-empty (honest, non-vacuous). -/
theorem deepShellTailClosureStatus_nonempty :
    deepShellTailClosureStatus ≠ [] := by
  simp [deepShellTailClosureStatus]

/-! ## Part 7.  Axiom-cleanliness audit
Every key declaration; expected axioms `[propext, Classical.choice, Quot.sound]`
or fewer. -/

#print axioms dstWidthGate_sharp
#print axioms dstClass1Absorption_of_depth_le
#print axioms dstClass1Tail_of_largeQ
#print axioms dstBand4Residue_exists
#print axioms dstSumRouteBudget_above_cap
#print axioms dstTable_q_lt_384
#print axioms dstDeepShell_r_ge_82
#print axioms dstDeepShell_r_ge_1160
#print axioms dstClass1Pair_of_deepAtom
#print axioms dstDeepShell_context_floors
#print axioms dstClass1CapAbsorption_field_of_deep
#print axioms dstRunCycleNumeric_period_floor
#print axioms dstClass5CycleNumeric_bandFree_or_long
#print axioms dstRunBandHeavy_period_floor
#print axioms dstClass5BandHeavy_bandFree_or_long
#print axioms dstTowerCycle_block_le_period
#print axioms dstClass2Cycle_bandFree_or_blockLong
#print axioms dstBlock_ge_two
#print axioms dstTowerEnumLow_field_of_floors
#print axioms dstTowerEnumTail_field_of_floors
#print axioms dstRunNumericLow_field_of_floors
#print axioms dstRunNumericTail_field_of_floors
#print axioms deepShellTailClosureStatus_nonempty

end

end Erdos260
