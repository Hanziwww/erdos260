import Erdos260.Erdos260ConvergenceCapstone

/-!
# Deep counting closure — the boosted class-1 width gate and the band-free strata
# of the v19 convergence surface

Wave-20 worker module on the deep counting lanes of `Erdos260ConvergenceCapstone`
(`Erdos260ConvergenceResidual`, 12 fields).

## Workstream 1 — the class-1 deep lane (`class1Deep`, demanded at `L ≥ 1274740`)

* **THE VALUATION-BOOSTED WIDTH GATE (the parametric headline)**: the pure-ℕ gate
  `dccBoostGate` — a count `n` that is `2^v`-SPARSE in the support window
  (`2^v·n ≤ W`) clears the class-1 absorption gate `24·n·L ≤ 31·X` on the whole
  band `L ≤ 1274739·2^v` (margin `408·1274739 = 520093512 ≤ 520093696 = 31·2^24`,
  scale-invariant in `2^v`).  Sharp at one step for EVERY level
  (`dccBoostGate_sharp`: witness `n = 17, W = 17·2^v, X = 2^24·2^v` fails at
  `L = 1274740·2^v`).  Each in-tree sparsity level `v ≥ 1` therefore MULTIPLIES the
  closed class-1 regime by `2^v` — exactly the brief's carry-alignment mechanism,
  formalized as a supply interface.
* **Field producer**: `dccClass1Deep_field_of_boost` — an aligned-count supply at
  level `v` (`DccClass1AlignedCountSupply v`: deep contexts carry
  `2^v·#fibre₁ ≤ W`) plus a residual confined to `L > 1274739·2^v`
  (`DccClass1DeepResidual v`) rebuild the EXACT v19 `class1Deep` field.  At `v = 0`
  the supply is FREE (`dccAlignedSupply_zero_free`, from the generic width count
  `tfaFibre_card_le_width`) and the producer degenerates to the v19 demand
  verbatim (`dccBoost_zero_recovers`, converse `dccResidual_zero_of_field`) — the
  interface is an honest weakening ladder, not a re-statement.
* **Improved per-pair atoms**: `DccClass1DeepPairAtomBoosted (q, K₀, T, v)` is the
  v18/v19 `DstClass1DeepPairAtom` with the demand pushed from `max T 1274739 < L`
  out to `max T (1274739·2^v) < L`; `dccClass1Pair_of_boostedAtom` closes the WHOLE
  pair from the boosted atom plus a pair-local aligned supply
  (`DccClass1PairAlignedSupply`), through the SRE dispatcher (`L ≤ T`), the
  parametric width gate (`L ≤ 1274739`) and the boosted gate
  (`1274739 < L ≤ 1274739·2^v`).
* **The spacing→count tool**: `dccSpacedCount_le` — a pairwise `d`-spaced set
  inside a width-`W` window has `d·#S ≤ W + d − 1`; class-1 instance
  `dccAlignedCount_of_pairwiseSpacing` (fibre members pairwise `2^v`-spaced give
  `2^v·#fibre₁ ≤ W + 2^v − 1`, ONE UNIT short of the supply — recorded honestly).
* **THE CARRY-VALUATION HUNT (honest verdict)**: NO in-tree carry-valuation floor
  attaches to the class-1/band-4 fibre.  The wave-11/12 valuation machinery
  (`carryVal2_ge_dyadicPart`, `carryVal2_pos_of_Q_even`, the `2^t` same-slice
  spacing `sameSlice_gap_dvd_pow_dyadicPart`, the corrected global bound
  `routedFibre4_card_le_of_carryVal2_congruence`) lives ENTIRELY on the
  class-4/Return lane (`olcFibre`, the self-referential key) — no class-1 analogue
  exists.  The only in-tree class-1 spacing facts are the residue pins mod the
  orbit period `c` (the `b4·⌈W/c⌉` count, no 2-adic gain; the `63@10` parity pin
  `k % 2 = 0` is the mod-2 shadow of the mod-2 residue pin, not a new factor).
  The aligned supply (the spacing hypothesis) is therefore the honest residual of
  the carry-alignment route — no unconditional `v ≥ 1` is claimed.

## Workstream 2 — the band-free strata of the tower/run supplies

* **Run / class 5 (`runNumericLow`)**: the six kernel-certified band-`{1,4}`-free
  pairs `(3,1), (21,3), (51,1), (51,8), (63,1), (63,4)` close
  `Class5CycleNumericCloses` OUTRIGHT at every context (the cycle band is empty,
  the demanded numeric is `0 ≤ nonneg`) — `dccClass5CycleCloses_of_bandFreePair`.
  Dispatcher `dccRunNumericLow_field_of_bandReading`: the v19 `runNumericLow`
  field from a supply demanded only OFF the band-free list.
* **Tower / class 2 (`towerEnumLow`)**: NEW kernel cycle certificates
  (`dccCycle_5_1` … `dccCycle_63_4`) prove seven `q < 107` pairs band-4-free on a
  full period — `(5,1), (5,2), (7,3)` (band-1/2-reading but band-4-FREE, so the
  tower count is void) and `(51,1), (51,8), (63,1), (63,4)`;
  `dccClass2Cycle_of_band4FreePair` closes `Class2CycleInequality` outright there.
  Dispatcher `dccTowerEnumLow_field_of_bandReading`: the v19 `towerEnumLow` field
  from a supply demanded only OFF the band-4-free list.
* **What does NOT close (honest)**: at band-4-READING pairs the wave-18 necessities
  stand — `dstTowerCycle_block_le_period` (`m₀ ≤ c` at any band-4-reading witness
  period) against the unbounded `m₀ = ⌈3(r+1)/64⌉` (deep contexts), and the run
  period floors `c ≥ 1537` / `6145` (`dstClass5CycleNumeric_bandFree_or_long`,
  `dstClass5BandHeavy_bandFree_or_long`) against the `q < 64` minimal periods
  `≤ 63`: on band-reading pairs only the per-context scalar horns remain, and no
  in-tree numeric closes them at deep `L`.  The `q ≥ 107` tower tail and the
  `q ≥ 64` run tail carry no in-tree band-free certificates — untouched.

## Workstream 3 — additive wiring to the exact v19 surface

`dccConvergenceResidual_of_deepCounting` assembles a FULL
`Erdos260ConvergenceResidual` from the narrowed supplies (boosted class-1 pair,
band-reading tower/run lows, everything else verbatim);
`dccErdos260_of_deepCounting` is the endpoint to `Erdos260Statement`.

No `sorry`, no `admit`, no new `axiom`, no `native_decide`; additive only — no
existing module is edited; built standalone as `Erdos260.DeepCountingClosure`.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

/-! ## Part 1.  The valuation-boosted width gate (pure ℕ) -/

/-- **The boosted width gate**: a `2^v`-sparse count (`2^v·n ≤ W`) against the
failure cap `2^24·W ≤ 17·X` clears the class-1 absorption gate `24·n·L ≤ 31·X` on
the whole band `L ≤ 1274739·2^v` — the dst width-gate margin
`408·1274739 = 520093512 ≤ 520093696 = 31·2^24` is scale-invariant in `2^v`.
At `v = 0` this is exactly the wave-18 parametric width gate. -/
theorem dccBoostGate {v n W L X : ℕ}
    (hn : 2 ^ v * n ≤ W) (hW : 16777216 * W ≤ 17 * X)
    (hL : L ≤ 1274739 * 2 ^ v) :
    24 * (n * L) ≤ 31 * X := by
  have hpos : 0 < 16777216 * 2 ^ v := by positivity
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  calc (16777216 * 2 ^ v) * (24 * (n * L))
      = 24 * L * (16777216 * (2 ^ v * n)) := by ring
    _ ≤ 24 * L * (16777216 * W) :=
        Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hn)
    _ ≤ 24 * L * (17 * X) := Nat.mul_le_mul le_rfl hW
    _ = 408 * L * X := by ring
    _ ≤ 408 * (1274739 * 2 ^ v) * X :=
        Nat.mul_le_mul (Nat.mul_le_mul le_rfl hL) le_rfl
    _ = 520093512 * 2 ^ v * X := by ring
    _ ≤ 520093696 * 2 ^ v * X :=
        Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) le_rfl) le_rfl
    _ = (16777216 * 2 ^ v) * (31 * X) := by ring

/-- **The boosted gate is sharp at one step, at EVERY level `v`**: the witness
`n = 17`, `W = 17·2^v`, `X = 2^24·2^v` satisfies both hypotheses but fails the gate
at `L = 1274740·2^v` (`408·1274740 = 520093920 > 520093696 = 31·2^24`). -/
theorem dccBoostGate_sharp (v : ℕ) :
    ∃ n W X : ℕ, 2 ^ v * n ≤ W ∧ 16777216 * W ≤ 17 * X
      ∧ ¬ 24 * (n * (1274740 * 2 ^ v)) ≤ 31 * X := by
  refine ⟨17, 17 * 2 ^ v, 16777216 * 2 ^ v, le_of_eq (by ring), le_of_eq (by ring), ?_⟩
  intro h
  have h2 : 520093920 * 2 ^ v ≤ 520093696 * 2 ^ v := by
    calc 520093920 * 2 ^ v = 24 * (17 * (1274740 * 2 ^ v)) := by ring
      _ ≤ 31 * (16777216 * 2 ^ v) := h
      _ = 520093696 * 2 ^ v := by ring
  have hp : 0 < 2 ^ v := by positivity
  have := Nat.le_of_mul_le_mul_right h2 hp
  norm_num at this

/-- **The boosted class-1 absorption**: any count cap `n` that is `2^v`-sparse in
the support window closes the EXACT corrected class-1 absorption (the capstone
field conclusion) on the whole band `L ≤ 1274739·2^v` — through the in-tree failure
cap `2^24·W < 17·X` (`em_supportShell_strict`) and the budget-free gate engine
(`sreAbsorption_of_nat_gate`). -/
theorem dccClass1Absorption_of_spacedCount (ctx : ActualFailureContext) {v n : ℕ}
    (hcard : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card ≤ n)
    (hspace : 2 ^ v * n ≤ (supportShell ctx.shell.d ctx.shell.X).card)
    (hL : shellLadderDepth ctx ≤ 1274739 * 2 ^ v) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hW := em_supportShell_strict ctx
  unfold emW at hW
  exact sreAbsorption_of_nat_gate ctx n hcard
    (dccBoostGate hspace (le_of_lt hW) hL)

/-! ## Part 2.  The aligned-count supply interface and the v19 field producer -/

/-- **The aligned-count supply at level `v`** — the carry-alignment interface: on
the genuinely deep contexts (`L ≥ 1274740`, all carrying `r ≥ 82`) the class-1
fibre is `2^v`-sparse in the support window.  Level `0` is FREE
(`dccAlignedSupply_zero_free`); each level `v ≥ 1` MULTIPLIES the closed class-1
regime by `2^v` (`dccClass1Deep_field_of_boost`). -/
def DccClass1AlignedCountSupply (v : ℕ) : Prop :=
  ∀ ctx : ActualFailureContext,
    1274740 ≤ shellLadderDepth ctx → 82 ≤ ctx.n24CarryData.r →
    2 ^ v * (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (supportShell ctx.shell.d ctx.shell.X).card

/-- **The boosted deep residual at level `v`** — the v19 `class1Deep` demand pushed
out to `L > 1274739·2^v` (off-table guard verbatim; `r ≥ 82` is free there). -/
def DccClass1DeepResidual (v : ℕ) : Prop :=
  ∀ ctx : ActualFailureContext,
    1274739 * 2 ^ v < shellLadderDepth ctx → 82 ≤ ctx.n24CarryData.r →
    (¬ ∃ cv bv Tv : ℕ,
      ((class1SlopeDatum ctx).q, (class1SlopeDatum ctx).K₀, cv, bv, Tv)
          ∈ sreClass1ThresholdTable
        ∧ shellLadderDepth ctx ≤ Tv) →
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ)

/-- **Level `0` is free**: the generic width count `|fibre₁| ≤ W`
(`tfaFibre_card_le_width`) IS the level-0 aligned supply. -/
theorem dccAlignedSupply_zero_free : DccClass1AlignedCountSupply 0 := by
  intro ctx _ _
  simpa using tfaFibre_card_le_width ctx (genuineChargeRoute ctx) 1

/-- **The v19 `class1Deep` field from a boosted supply pair**: an aligned-count
supply at level `v` plus a residual confined to `L > 1274739·2^v` rebuild the EXACT
capstone field.  Additive wiring:
`R.class1Deep := dccClass1Deep_field_of_boost hal hres`. -/
theorem dccClass1Deep_field_of_boost {v : ℕ}
    (hal : DccClass1AlignedCountSupply v) (hres : DccClass1DeepResidual v) :
    ∀ ctx : ActualFailureContext,
      1274740 ≤ shellLadderDepth ctx → 82 ≤ ctx.n24CarryData.r →
      1 ≤ ctx.n24CarryData.r →
      (¬ ∃ cv bv Tv : ℕ,
        ((class1SlopeDatum ctx).q, (class1SlopeDatum ctx).K₀, cv, bv, Tv)
            ∈ sreClass1ThresholdTable
          ∧ shellLadderDepth ctx ≤ Tv) →
      ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
          * ctx.n24CarryData.Y
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  intro ctx hL hr82 hr1 hreg
  rcases Nat.lt_or_ge (1274739 * 2 ^ v) (shellLadderDepth ctx) with hdeep | hsh
  · exact hres ctx hdeep hr82 hreg
  · exact dccClass1Absorption_of_spacedCount ctx le_rfl (hal ctx hL hr82) hsh

/-- **Sanity (the ladder is honest, downward)**: at `v = 0` the producer
degenerates to the v19 demand verbatim — a level-0 residual alone rebuilds the
field with the FREE supply. -/
theorem dccBoost_zero_recovers (hres : DccClass1DeepResidual 0) :
    ∀ ctx : ActualFailureContext,
      1274740 ≤ shellLadderDepth ctx → 82 ≤ ctx.n24CarryData.r →
      1 ≤ ctx.n24CarryData.r →
      (¬ ∃ cv bv Tv : ℕ,
        ((class1SlopeDatum ctx).q, (class1SlopeDatum ctx).K₀, cv, bv, Tv)
            ∈ sreClass1ThresholdTable
          ∧ shellLadderDepth ctx ≤ Tv) →
      ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
          * ctx.n24CarryData.Y
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) :=
  dccClass1Deep_field_of_boost dccAlignedSupply_zero_free hres

/-- **Sanity (the ladder is honest, upward)**: the v19 field yields the level-0
residual — at `v = 0` the interface is an EQUIVALENT re-cut of the surface demand,
not a strengthening. -/
theorem dccResidual_zero_of_field
    (h : ∀ ctx : ActualFailureContext,
      1274740 ≤ shellLadderDepth ctx → 82 ≤ ctx.n24CarryData.r →
      1 ≤ ctx.n24CarryData.r →
      (¬ ∃ cv bv Tv : ℕ,
        ((class1SlopeDatum ctx).q, (class1SlopeDatum ctx).K₀, cv, bv, Tv)
            ∈ sreClass1ThresholdTable
          ∧ shellLadderDepth ctx ≤ Tv) →
      ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
          * ctx.n24CarryData.Y
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ)) :
    DccClass1DeepResidual 0 := by
  intro ctx hL hr hreg
  exact h ctx (by omega) hr (by omega) hreg

/-! ## Part 3.  The improved per-pair deep atoms -/

/-- **The boosted per-pair deep atom**: the wave-18 `DstClass1DeepPairAtom` with the
demand pushed from `max T 1274739 < L` out to `max T (1274739·2^v) < L`. -/
def DccClass1DeepPairAtomBoosted (qv Kv Tv v : ℕ) : Prop :=
  ∀ ctx : ActualFailureContext,
    (class1SlopeDatum ctx).q = qv → (class1SlopeDatum ctx).K₀ = Kv →
    Tv < shellLadderDepth ctx → 1274739 * 2 ^ v < shellLadderDepth ctx →
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ)

/-- **The pair-local aligned supply at level `v`** — the carry-alignment demand
restricted to one datum, on the deep band `L > 1274739` only. -/
def DccClass1PairAlignedSupply (qv Kv v : ℕ) : Prop :=
  ∀ ctx : ActualFailureContext,
    (class1SlopeDatum ctx).q = qv → (class1SlopeDatum ctx).K₀ = Kv →
    1274739 < shellLadderDepth ctx → 82 ≤ ctx.n24CarryData.r →
    2 ^ v * (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (supportShell ctx.shell.d ctx.shell.X).card

/-- **The per-pair closure from the boosted atom**: at a table row, the SRE
dispatcher (`L ≤ T`), the parametric width gate (`L ≤ 1274739`), the BOOSTED gate
(`1274739 < L ≤ 1274739·2^v`, from the pair-local aligned supply) and the boosted
atom (`max T (1274739·2^v) < L`) jointly close the corrected class-1 absorption at
EVERY context of the pair — the residual atom regime is `2^v` times deeper than the
wave-18 `dstClass1Pair_of_deepAtom`. -/
theorem dccClass1Pair_of_boostedAtom {qv Kv cv bv Tv v : ℕ}
    (hmem : (qv, Kv, cv, bv, Tv) ∈ sreClass1ThresholdTable)
    (hsup : DccClass1PairAlignedSupply qv Kv v)
    (hatom : DccClass1DeepPairAtomBoosted qv Kv Tv v) :
    ∀ ctx : ActualFailureContext,
      (class1SlopeDatum ctx).q = qv → (class1SlopeDatum ctx).K₀ = Kv →
      ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
          * ctx.n24CarryData.Y
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  intro ctx hq hK
  rcases Nat.lt_or_ge Tv (shellLadderDepth ctx) with hT | hT
  · rcases Nat.lt_or_ge 1274739 (shellLadderDepth ctx) with hP | hP
    · rcases Nat.lt_or_ge (1274739 * 2 ^ v) (shellLadderDepth ctx) with hD | hD
      · exact hatom ctx hq hK hT hD
      · exact dccClass1Absorption_of_spacedCount ctx le_rfl
          (hsup ctx hq hK hP (dstDeepShell_r_ge_82 ctx (by omega))) hD
    · exact dstClass1Absorption_of_depth_le ctx hP
  · exact sreClass1Absorption_of_mem ctx hmem hq hK hT

/-! ## Part 4.  The spacing→count tool (the carry-alignment bridge) -/

/-- **The spaced-count bound**: a pairwise `d`-spaced set (all gaps divisible by
`d`) inside a width-`W` window has `d·#S ≤ W + d − 1` — the counting content of the
brief's carry-alignment mechanism, in pure ℕ. -/
theorem dccSpacedCount_le {S : Finset ℕ} {a d W : ℕ} (hd : 1 ≤ d)
    (hwin : ∀ k ∈ S, a ≤ k ∧ k < a + W)
    (hspace : ∀ k ∈ S, ∀ l ∈ S, k ≤ l → d ∣ (l - k)) :
    d * S.card ≤ W + d - 1 := by
  classical
  rcases Nat.eq_zero_or_pos W with rfl | hW
  · have hS : S = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro k hk
      obtain ⟨h1, h2⟩ := hwin k hk
      omega
    rw [hS, Finset.card_empty, Nat.mul_zero]
    omega
  · have hkey : ∀ x ∈ S, ∀ y ∈ S, x ≤ y → (x - a) / d = (y - a) / d → x = y := by
      intro x hx y hy hxy heq
      obtain ⟨m, hm⟩ := hspace x hx y hy hxy
      have hax : a ≤ x := (hwin x hx).1
      have hay := (hwin y hy).1
      have hya : y - a = (x - a) + d * m := by omega
      have hdiv : (y - a) / d = (x - a) / d + m := by
        rw [hya, Nat.add_mul_div_left _ _ (by omega : 0 < d)]
      have hm0 : m = 0 := by omega
      rw [hm0, Nat.mul_zero] at hm
      omega
    have hmaps : ∀ k ∈ S, (k - a) / d ∈ Finset.range ((W + d - 1) / d) := by
      intro k hk
      rw [Finset.mem_range]
      obtain ⟨hak, hkW⟩ := hwin k hk
      have he : (W + d - 1) / d = (W - 1) / d + 1 := by
        have h1 : W + d - 1 = (W - 1) + d := by omega
        rw [h1, Nat.add_div_right _ (by omega : 0 < d)]
      have h2 : (k - a) / d ≤ (W - 1) / d := Nat.div_le_div_right (by omega)
      omega
    have hinj : Set.InjOn (fun k : ℕ => (k - a) / d) S := by
      intro x hx y hy heq
      rcases le_total x y with hxy | hyx
      · exact hkey x (Finset.mem_coe.mp hx) y (Finset.mem_coe.mp hy) hxy heq
      · exact (hkey y (Finset.mem_coe.mp hy) x (Finset.mem_coe.mp hx) hyx heq.symm).symm
    have hcard := Finset.card_le_card_of_injOn (fun k : ℕ => (k - a) / d) hmaps hinj
    rw [Finset.card_range] at hcard
    calc d * S.card ≤ d * ((W + d - 1) / d) := Nat.mul_le_mul le_rfl hcard
      _ ≤ W + d - 1 := by
          rw [Nat.mul_comm]
          exact Nat.div_mul_le_self _ _

/-- **The class-1 instance of the spacing tool (honest, one unit short)**: if the
class-1 fibre members are pairwise `2^v`-spaced, then `2^v·#fibre₁ ≤ W + 2^v − 1` —
ONE unit of slack away from the aligned supply `2^v·#fibre₁ ≤ W`.  A future
carry-alignment proof must either pin the window start to the alignment class or
spend one residue of the window; the gap is recorded, not papered over. -/
theorem dccAlignedCount_of_pairwiseSpacing (ctx : ActualFailureContext) (v : ℕ)
    (hspace : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1,
      ∀ l ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1,
      k ≤ l → 2 ^ v ∣ (l - k)) :
    2 ^ v * (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (supportShell ctx.shell.d ctx.shell.X).card + 2 ^ v - 1 :=
  dccSpacedCount_le (Nat.one_le_two_pow)
    (fun k hk => class1Fibre_mem_window ctx hk) hspace

/-! ## Part 5.  The run band-free strata (`runNumericLow`) -/

/-- The six kernel-certified band-`{1,4}`-free run pairs with `q < 64` (their
`Class5CycleNumericCloses` closures are in-tree, wave 13/18). -/
def dccRunBandFreeLowPairs : List (ℕ × ℕ) :=
  [(3, 1), (21, 3), (51, 1), (51, 8), (63, 1), (63, 4)]

/-- **The band-free run stratum closes outright**: at any context whose datum lies
in the certified band-free list, `Class5CycleNumericCloses` holds at EVERY scale —
the cycle band is empty, the demanded numeric is `0 ≤ nonneg`. -/
theorem dccClass5CycleCloses_of_bandFreePair (ctx : ActualFailureContext)
    (hmem : ((class1SlopeDatum ctx).q, (class1SlopeDatum ctx).K₀)
      ∈ dccRunBandFreeLowPairs) :
    Class5CycleNumericCloses ctx := by
  simp only [dccRunBandFreeLowPairs, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq] at hmem
  rcases hmem with ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩
  · exact class5CycleNumericCloses_of_datum_3_1 ctx hq hK
  · exact class5CycleNumericCloses_of_datum_21_3 ctx hq hK
  · exact class5CycleNumericCloses_of_datum_51_1 ctx hq hK
  · exact class5CycleNumericCloses_of_datum_51_8 ctx hq hK
  · exact class5CycleNumericCloses_of_datum_63_1 ctx hq hK
  · exact class5CycleNumericCloses_of_datum_63_4 ctx hq hK

/-- **The v19 `runNumericLow` field from a band-reading supply**: the supply is
demanded only OFF the six certified band-free pairs — the band-free stratum closes
through `dccClass5CycleCloses_of_bandFreePair`.  Additive wiring:
`R.runNumericLow := dccRunNumericLow_field_of_bandReading h`. -/
theorem dccRunNumericLow_field_of_bandReading
    (h : ∀ ctx : ActualFailureContext,
      ¬ OrbitBandPinned ctx 4 →
      (class1SlopeDatum ctx).q < 64 →
      ((class1SlopeDatum ctx).q, (class1SlopeDatum ctx).K₀)
        ∉ dccRunBandFreeLowPairs →
      986888 ≤ shellLadderDepth ctx → 63 ≤ ctx.n24CarryData.r →
      Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx) :
    ∀ ctx : ActualFailureContext,
      ¬ OrbitBandPinned ctx 4 →
      (class1SlopeDatum ctx).q < 64 →
      986888 ≤ shellLadderDepth ctx → 63 ≤ ctx.n24CarryData.r →
      Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx := by
  intro ctx hpin hq hL hr
  by_cases hmem : ((class1SlopeDatum ctx).q, (class1SlopeDatum ctx).K₀)
      ∈ dccRunBandFreeLowPairs
  · exact Or.inr (dccClass5CycleCloses_of_bandFreePair ctx hmem)
  · exact h ctx hpin hq hmem hL hr

/-! ## Part 6.  The tower band-4-free strata (`towerEnumLow`)

NEW kernel cycle certificates for seven `q < 107` pairs whose orbit period is
band-4-FREE — including `(5,1), (5,2), (7,3)`, which READ band 1/2 (so they are
invisible to the run band-free list) but never band 4: the tower count is void
there and `Class2CycleInequality` closes outright. -/

/-- `(5,1)`: period-2 cycle `3 → 1` from index 1; gaps `1, 3` — band-4-free. -/
private theorem dccCycle_5_1 :
    slopeOrbit 5 1 (1 + 2) = slopeOrbit 5 1 1
      ∧ (∀ j, 1 ≤ j → j ≤ 2 → canonGap 5 (slopeOrbit 5 1 j) ≠ 4) := by
  have e0 : slopeOrbit 5 1 0 = 1 := rfl
  have e1 : slopeOrbit 5 1 1 = 3 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 5 1 2 = 1 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 5 1 3 = 3 :=
    slopeOrbit_step_eval 2 2 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 5 1 3 = slopeOrbit 5 1 1
    rw [e3, e1]
  · intro j hj1 hj2
    interval_cases j
    · rw [e1]
      exact canonGap_ne_four_of_band (Or.inl (by norm_num))
    · rw [e2]
      exact canonGap_ne_four_of_band (Or.inl (by norm_num))

/-- `(5,2)`: period-2 cycle `3 → 1` from index 1 — band-4-free. -/
private theorem dccCycle_5_2 :
    slopeOrbit 5 2 (1 + 2) = slopeOrbit 5 2 1
      ∧ (∀ j, 1 ≤ j → j ≤ 2 → canonGap 5 (slopeOrbit 5 2 j) ≠ 4) := by
  have e0 : slopeOrbit 5 2 0 = 2 := rfl
  have e1 : slopeOrbit 5 2 1 = 3 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 5 2 2 = 1 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 5 2 3 = 3 :=
    slopeOrbit_step_eval 2 2 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 5 2 3 = slopeOrbit 5 2 1
    rw [e3, e1]
  · intro j hj1 hj2
    interval_cases j
    · rw [e1]
      exact canonGap_ne_four_of_band (Or.inl (by norm_num))
    · rw [e2]
      exact canonGap_ne_four_of_band (Or.inl (by norm_num))

/-- `(7,3)`: period-2 cycle `5 → 3` from index 1; gaps `1, 2` — band-4-free. -/
private theorem dccCycle_7_3 :
    slopeOrbit 7 3 (1 + 2) = slopeOrbit 7 3 1
      ∧ (∀ j, 1 ≤ j → j ≤ 2 → canonGap 7 (slopeOrbit 7 3 j) ≠ 4) := by
  have e0 : slopeOrbit 7 3 0 = 3 := rfl
  have e1 : slopeOrbit 7 3 1 = 5 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 7 3 2 = 3 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 7 3 3 = 5 :=
    slopeOrbit_step_eval 2 1 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 7 3 3 = slopeOrbit 7 3 1
    rw [e3, e1]
  · intro j hj1 hj2
    interval_cases j
    · rw [e1]
      exact canonGap_ne_four_of_band (Or.inl (by norm_num))
    · rw [e2]
      exact canonGap_ne_four_of_band (Or.inl (by norm_num))

/-- `(51,1)`: period-2 cycle `13 → 1` from index 1; gaps `2, 6` — band-4-free. -/
private theorem dccCycle_51_1 :
    slopeOrbit 51 1 (1 + 2) = slopeOrbit 51 1 1
      ∧ (∀ j, 1 ≤ j → j ≤ 2 → canonGap 51 (slopeOrbit 51 1 j) ≠ 4) := by
  have e0 : slopeOrbit 51 1 0 = 1 := rfl
  have e1 : slopeOrbit 51 1 1 = 13 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 51 1 2 = 1 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 51 1 3 = 13 :=
    slopeOrbit_step_eval 2 5 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 51 1 3 = slopeOrbit 51 1 1
    rw [e3, e1]
  · intro j hj1 hj2
    interval_cases j
    · rw [e1]
      exact canonGap_ne_four_of_band (Or.inl (by norm_num))
    · rw [e2]
      exact canonGap_ne_four_of_band (Or.inr (by norm_num))

/-- `(51,8)`: period-2 cycle `13 → 1` from index 1 — band-4-free. -/
private theorem dccCycle_51_8 :
    slopeOrbit 51 8 (1 + 2) = slopeOrbit 51 8 1
      ∧ (∀ j, 1 ≤ j → j ≤ 2 → canonGap 51 (slopeOrbit 51 8 j) ≠ 4) := by
  have e0 : slopeOrbit 51 8 0 = 8 := rfl
  have e1 : slopeOrbit 51 8 1 = 13 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 51 8 2 = 1 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 51 8 3 = 13 :=
    slopeOrbit_step_eval 2 5 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 51 8 3 = slopeOrbit 51 8 1
    rw [e3, e1]
  · intro j hj1 hj2
    interval_cases j
    · rw [e1]
      exact canonGap_ne_four_of_band (Or.inl (by norm_num))
    · rw [e2]
      exact canonGap_ne_four_of_band (Or.inr (by norm_num))

/-- `(63,1)`: fixed point `1` from index 1 (gap `6`) — band-4-free. -/
private theorem dccCycle_63_1 :
    slopeOrbit 63 1 (1 + 1) = slopeOrbit 63 1 1
      ∧ (∀ j, 1 ≤ j → j ≤ 1 → canonGap 63 (slopeOrbit 63 1 j) ≠ 4) := by
  have e0 : slopeOrbit 63 1 0 = 1 := rfl
  have e1 : slopeOrbit 63 1 1 = 1 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 63 1 2 = 1 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 63 1 2 = slopeOrbit 63 1 1
    rw [e2, e1]
  · intro j hj1 hj2
    interval_cases j
    rw [e1]
    exact canonGap_ne_four_of_band (Or.inr (by norm_num))

/-- `(63,4)`: falls to the fixed point `1` at index 1 — band-4-free from index 1. -/
private theorem dccCycle_63_4 :
    slopeOrbit 63 4 (1 + 1) = slopeOrbit 63 4 1
      ∧ (∀ j, 1 ≤ j → j ≤ 1 → canonGap 63 (slopeOrbit 63 4 j) ≠ 4) := by
  have e0 : slopeOrbit 63 4 0 = 4 := rfl
  have e1 : slopeOrbit 63 4 1 = 1 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 63 4 2 = 1 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 63 4 2 = slopeOrbit 63 4 1
    rw [e2, e1]
  · intro j hj1 hj2
    interval_cases j
    rw [e1]
    exact canonGap_ne_four_of_band (Or.inr (by norm_num))

/-- The seven kernel-certified band-4-free tower pairs with `q < 107` (the run
band-free pairs minus the guard-excluded `(3,1)/(21,3)`, PLUS the band-1/2-reading
but band-4-free `(5,1), (5,2), (7,3)`). -/
def dccTowerBand4FreeLowPairs : List (ℕ × ℕ) :=
  [(5, 1), (5, 2), (7, 3), (51, 1), (51, 8), (63, 1), (63, 4)]

/-- **The band-4-free tower stratum closes outright**: at any context whose datum
lies in the certified band-4-free list, `Class2CycleInequality` holds at EVERY
scale — the band-4 cycle count is `0` and the counting demand is `0 ≤ K`. -/
theorem dccClass2Cycle_of_band4FreePair (ctx : ActualFailureContext)
    (hmem : ((class1SlopeDatum ctx).q, (class1SlopeDatum ctx).K₀)
      ∈ dccTowerBand4FreeLowPairs) :
    Class2CycleInequality ctx := by
  simp only [dccTowerBand4FreeLowPairs, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq] at hmem
  rcases hmem with ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩ | ⟨hq, hK⟩
    | ⟨hq, hK⟩ | ⟨hq, hK⟩
  · refine class2CycleInequality_of_band_free ctx (c := 2) (by norm_num) ?_ ?_
    · rw [hq, hK]
      exact slopeOrbit_period_of_return dccCycle_5_1.1
    · rw [hq, hK]
      exact dccCycle_5_1.2
  · refine class2CycleInequality_of_band_free ctx (c := 2) (by norm_num) ?_ ?_
    · rw [hq, hK]
      exact slopeOrbit_period_of_return dccCycle_5_2.1
    · rw [hq, hK]
      exact dccCycle_5_2.2
  · refine class2CycleInequality_of_band_free ctx (c := 2) (by norm_num) ?_ ?_
    · rw [hq, hK]
      exact slopeOrbit_period_of_return dccCycle_7_3.1
    · rw [hq, hK]
      exact dccCycle_7_3.2
  · refine class2CycleInequality_of_band_free ctx (c := 2) (by norm_num) ?_ ?_
    · rw [hq, hK]
      exact slopeOrbit_period_of_return dccCycle_51_1.1
    · rw [hq, hK]
      exact dccCycle_51_1.2
  · refine class2CycleInequality_of_band_free ctx (c := 2) (by norm_num) ?_ ?_
    · rw [hq, hK]
      exact slopeOrbit_period_of_return dccCycle_51_8.1
    · rw [hq, hK]
      exact dccCycle_51_8.2
  · refine class2CycleInequality_of_band_free ctx (c := 1) (by norm_num) ?_ ?_
    · rw [hq, hK]
      exact slopeOrbit_period_of_return dccCycle_63_1.1
    · rw [hq, hK]
      exact dccCycle_63_1.2
  · refine class2CycleInequality_of_band_free ctx (c := 1) (by norm_num) ?_ ?_
    · rw [hq, hK]
      exact slopeOrbit_period_of_return dccCycle_63_4.1
    · rw [hq, hK]
      exact dccCycle_63_4.2

/-- **The v19 `towerEnumLow` field from a band-reading supply**: the supply is
demanded only OFF the seven certified band-4-free pairs.  Additive wiring:
`R.towerEnumLow := dccTowerEnumLow_field_of_bandReading h`. -/
theorem dccTowerEnumLow_field_of_bandReading
    (h : ∀ ctx : ActualFailureContext,
      TowerModulusEnumEscapeV2 ctx → (class1SlopeDatum ctx).q < 107 →
      (ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx) →
      ¬ ((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1) →
      ¬ ((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3) →
      ((class1SlopeDatum ctx).q, (class1SlopeDatum ctx).K₀)
        ∉ dccTowerBand4FreeLowPairs →
      986888 ≤ shellLadderDepth ctx → 63 ≤ ctx.n24CarryData.r →
      3 ≤ towerSparsityBlock ctx →
      Class2CycleInequality ctx) :
    ∀ ctx : ActualFailureContext,
      TowerModulusEnumEscapeV2 ctx → (class1SlopeDatum ctx).q < 107 →
      (ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx) →
      ¬ ((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1) →
      ¬ ((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3) →
      986888 ≤ shellLadderDepth ctx → 63 ≤ ctx.n24CarryData.r →
      3 ≤ towerSparsityBlock ctx →
      Class2CycleInequality ctx := by
  intro ctx hesc hq haper h31 h213 hL hr hm0
  by_cases hmem : ((class1SlopeDatum ctx).q, (class1SlopeDatum ctx).K₀)
      ∈ dccTowerBand4FreeLowPairs
  · exact dccClass2Cycle_of_band4FreePair ctx hmem
  · exact h ctx hesc hq haper h31 h213 hmem hL hr hm0

/-! ## Part 7.  Workstream 3: additive wiring to the exact v19 surface -/

/-- **The full v19 convergence surface from the deep-counting supplies**: the
class-1 deep pair (aligned supply at level `v` + boosted residual), the tower/run
low lanes narrowed to their band-reading strata, everything else verbatim. -/
def dccConvergenceResidual_of_deepCounting
    (v : ℕ)
    (hal : DccClass1AlignedCountSupply v)
    (hres : DccClass1DeepResidual v)
    (hPin : DeepOrbitPinVoiding)
    (hTowerLow : ∀ ctx : ActualFailureContext,
      TowerModulusEnumEscapeV2 ctx → (class1SlopeDatum ctx).q < 107 →
      (ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx) →
      ¬ ((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1) →
      ¬ ((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3) →
      ((class1SlopeDatum ctx).q, (class1SlopeDatum ctx).K₀)
        ∉ dccTowerBand4FreeLowPairs →
      986888 ≤ shellLadderDepth ctx → 63 ≤ ctx.n24CarryData.r →
      3 ≤ towerSparsityBlock ctx →
      Class2CycleInequality ctx)
    (hTowerTail : ∀ ctx : ActualFailureContext,
      TowerModulusEnumEscapeV2 ctx →
      107 ≤ (class1SlopeDatum ctx).q →
      (ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx) →
      493461 ≤ shellLadderDepth ctx → 32 ≤ ctx.n24CarryData.r →
      2 ≤ towerSparsityBlock ctx →
      ((class1SlopeDatum ctx).q < 384 → 986888 ≤ shellLadderDepth ctx) →
      (((Nat.log 2 (class1SlopeDatum ctx).q + 1) * shellWidth ctx
          < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
              (class1SlopeDatum ctx).K₀)))
          ∧ TowerBand4Budget ctx)
        ∨ Class2CycleInequality ctx)
    (hRunLow : ∀ ctx : ActualFailureContext,
      ¬ OrbitBandPinned ctx 4 →
      (class1SlopeDatum ctx).q < 64 →
      ((class1SlopeDatum ctx).q, (class1SlopeDatum ctx).K₀)
        ∉ dccRunBandFreeLowPairs →
      986888 ≤ shellLadderDepth ctx → 63 ≤ ctx.n24CarryData.r →
      Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx)
    (hRunTail : ∀ ctx : ActualFailureContext,
      ¬ OrbitBandPinned ctx 4 →
      64 ≤ (class1SlopeDatum ctx).q →
      ¬ ((class1SlopeDatum ctx).q = 93 ∧ (class1SlopeDatum ctx).K₀ = 15) →
      493461 ≤ shellLadderDepth ctx → 32 ≤ ctx.n24CarryData.r →
      ((class1SlopeDatum ctx).q < 384 → 986888 ≤ shellLadderDepth ctx) →
      (((Nat.log 2 (class1SlopeDatum ctx).q + 1)
          * (supportShell ctx.shell.d ctx.shell.X).card
        < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
            (class1SlopeDatum ctx).K₀)))
        ∧ RunBandBudget ctx)
      ∨ (Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx))
    (hRetGates : ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx →
      ¬ OrbitBandPinned ctx 2 →
      ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
      2 * (129 * shellLadderDepth ctx + 64)
        ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card
              + ctx.n24CarryData.r)
            * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
      ReturnGatesBodyUngated ctx)
    (hRetInterior : ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx →
      ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx)
    (hDpCover : ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      (genuineDensePackStarts ctx).card
          * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
              - (2 * shellLadderDepth ctx + 1))
        ≤ (proofV4DensePackActualPoints ctx.shell).card)
    (hDpDensity : ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      densePackEndpointDensity ctx)
    (hDpInterior : ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Class3TopBandCycleFree ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      ∀ k ∈ genuineDensePackStarts ctx,
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card)
    (gates : NarrowSupportClass0Gates) :
    Erdos260ConvergenceResidual where
  deepOrbitPin := hPin
  towerEnumLow := dccTowerEnumLow_field_of_bandReading hTowerLow
  towerEnumTail := hTowerTail
  runNumericLow := dccRunNumericLow_field_of_bandReading hRunLow
  runNumericTail := hRunTail
  returnGatesOffTable := hRetGates
  returnInteriorOffTable := hRetInterior
  densePackCoverOffTable := hDpCover
  densePackDensityOffTable := hDpDensity
  densePackInteriorOffTable := hDpInterior
  class0Gates := gates
  class1Deep := dccClass1Deep_field_of_boost hal hres

/-- **The deep-counting endpoint**: `Erdos260Statement` from the narrowed supplies,
through the v19 convergence route. -/
theorem dccErdos260_of_deepCounting
    (v : ℕ)
    (hal : DccClass1AlignedCountSupply v)
    (hres : DccClass1DeepResidual v)
    (hPin : DeepOrbitPinVoiding)
    (hTowerLow : ∀ ctx : ActualFailureContext,
      TowerModulusEnumEscapeV2 ctx → (class1SlopeDatum ctx).q < 107 →
      (ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx) →
      ¬ ((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1) →
      ¬ ((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3) →
      ((class1SlopeDatum ctx).q, (class1SlopeDatum ctx).K₀)
        ∉ dccTowerBand4FreeLowPairs →
      986888 ≤ shellLadderDepth ctx → 63 ≤ ctx.n24CarryData.r →
      3 ≤ towerSparsityBlock ctx →
      Class2CycleInequality ctx)
    (hTowerTail : ∀ ctx : ActualFailureContext,
      TowerModulusEnumEscapeV2 ctx →
      107 ≤ (class1SlopeDatum ctx).q →
      (ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx) →
      493461 ≤ shellLadderDepth ctx → 32 ≤ ctx.n24CarryData.r →
      2 ≤ towerSparsityBlock ctx →
      ((class1SlopeDatum ctx).q < 384 → 986888 ≤ shellLadderDepth ctx) →
      (((Nat.log 2 (class1SlopeDatum ctx).q + 1) * shellWidth ctx
          < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
              (class1SlopeDatum ctx).K₀)))
          ∧ TowerBand4Budget ctx)
        ∨ Class2CycleInequality ctx)
    (hRunLow : ∀ ctx : ActualFailureContext,
      ¬ OrbitBandPinned ctx 4 →
      (class1SlopeDatum ctx).q < 64 →
      ((class1SlopeDatum ctx).q, (class1SlopeDatum ctx).K₀)
        ∉ dccRunBandFreeLowPairs →
      986888 ≤ shellLadderDepth ctx → 63 ≤ ctx.n24CarryData.r →
      Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx)
    (hRunTail : ∀ ctx : ActualFailureContext,
      ¬ OrbitBandPinned ctx 4 →
      64 ≤ (class1SlopeDatum ctx).q →
      ¬ ((class1SlopeDatum ctx).q = 93 ∧ (class1SlopeDatum ctx).K₀ = 15) →
      493461 ≤ shellLadderDepth ctx → 32 ≤ ctx.n24CarryData.r →
      ((class1SlopeDatum ctx).q < 384 → 986888 ≤ shellLadderDepth ctx) →
      (((Nat.log 2 (class1SlopeDatum ctx).q + 1)
          * (supportShell ctx.shell.d ctx.shell.X).card
        < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
            (class1SlopeDatum ctx).K₀)))
        ∧ RunBandBudget ctx)
      ∨ (Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx))
    (hRetGates : ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx →
      ¬ OrbitBandPinned ctx 2 →
      ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
      2 * (129 * shellLadderDepth ctx + 64)
        ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card
              + ctx.n24CarryData.r)
            * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
      ReturnGatesBodyUngated ctx)
    (hRetInterior : ∀ ctx : ActualFailureContext, ¬ DscReturnB2ZeroDatum ctx →
      ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx)
    (hDpCover : ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Band3PinnedWide ctx → ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      (genuineDensePackStarts ctx).card
          * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
              - (2 * shellLadderDepth ctx + 1))
        ≤ (proofV4DensePackActualPoints ctx.shell).card)
    (hDpDensity : ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Class3CycleBand3Free ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      densePackEndpointDensity ctx)
    (hDpInterior : ∀ ctx : ActualFailureContext, ¬ DscBand3ZeroDatum ctx →
      ¬ Class3TopBandCycleFree ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      ∀ k ∈ genuineDensePackStarts ctx,
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card)
    (gates : NarrowSupportClass0Gates) :
    Erdos260Statement :=
  erdos260_of_convergenceResidual
    (dccConvergenceResidual_of_deepCounting v hal hres hPin hTowerLow hTowerTail
      hRunLow hRunTail hRetGates hRetInterior hDpCover hDpDensity hDpInterior gates)

/-! ## Part 8.  Honest machine-readable status -/

/-- Honest machine-readable status of the deep counting closure module. -/
def deepCountingClosureStatus : List String :=
  [ "SUBJECT (wave-20 worker): the deep counting lanes of the v19 convergence " ++
      "capstone (Erdos260ConvergenceResidual, 12 fields) - (1) class1Deep (the " ++
      "per-pair deep atoms at L > max(T, 1274739), r >= 82), (2) the " ++
      "towerEnumLow/towerEnumTail + runNumericLow/runNumericTail floor-guarded " ++
      "supplies.",
    "THE REGIME-GATE IDENTITY (re-derived honestly): the in-tree class-1 count " ++
      "|fibre1| <= b4*ceil(W/c) against W < (17/2^24)*X and Y = L/64 clears the " ++
      "corrected cap (31/1536)*X iff (b4/c)*L <= 31*2^24/408 ~ 1274739 - EXACTLY " ++
      "the SRE regime gate 408*b4*L <= 15*2^24*c-ish; the brief's apparent " ++
      "always-true bound dissolves because b4*ceil(W/c) >= W/c only at b4 = 1, " ++
      "and the gate IS the threshold (in-tree: dstWidthGate_sharp + " ++
      "emc_threshold_sharp, same constant).  A second count mechanism at " ++
      "(b4/c)*L > 1274739 is therefore REQUIRED, as the brief predicted.",
    "THE BOOSTED WIDTH GATE (workstream 1, PROVED): dccBoostGate - a 2^v-sparse " ++
      "count (2^v*n <= W) clears the class-1 gate 24*n*L <= 31*X on the whole " ++
      "band L <= 1274739*2^v (margin 408*1274739 = 520093512 <= 520093696 = " ++
      "31*2^24, scale-invariant in 2^v); sharp at one step at EVERY level " ++
      "(dccBoostGate_sharp, witness n=17, W=17*2^v, X=2^24*2^v at L = " ++
      "1274740*2^v).  dccClass1Absorption_of_spacedCount feeds it through " ++
      "em_supportShell_strict + sreAbsorption_of_nat_gate to the EXACT capstone " ++
      "absorption shape.  ANY in-tree sparsity level v >= 1 DOUBLES (x2^v) the " ++
      "closed class-1 regime - the brief's carry-alignment mechanism, formalized.",
    "THE CARRY-VALUATION HUNT (workstream 1, honest verdict): NO in-tree " ++
      "carry-valuation floor attaches to the class-1/band-4 fibre.  The " ++
      "wave-11/12 valuation machinery - carryVal2_ge_dyadicPart, " ++
      "carryVal2_pos_of_Q_even, the 2^t same-slice spacing " ++
      "sameSlice_gap_dvd_pow_dyadicPart (CarryValuationFloor), the corrected " ++
      "global bound routedFibre4_card_le_of_carryVal2_congruence " ++
      "(ReturnM21SliceCore) - lives ENTIRELY on the class-4/Return lane " ++
      "(olcFibre, the self-referential key); no class-1 analogue exists.  The " ++
      "only class-1 spacing facts are the residue pins mod the orbit period c " ++
      "(CNLClass1PairClosure: the b4*ceil(W/c) count; ParityResidueClosure: the " ++
      "63@10 parity pin k % 2 = 0 is the mod-2 shadow of the mod-2 residue pin, " ++
      "no NEW factor).  Hence v0 = 0 unconditionally; the aligned supply " ++
      "DccClass1AlignedCountSupply v (2^v * #fibre1 <= W on deep contexts) is " ++
      "the honest residual of the alignment route.  Level 0 is FREE " ++
      "(dccAlignedSupply_zero_free) and the v = 0 producer recovers the v19 " ++
      "demand verbatim both ways (dccBoost_zero_recovers, " ++
      "dccResidual_zero_of_field) - the interface is a genuine weakening " ++
      "ladder.  Tool: dccSpacedCount_le (pairwise d-spaced in a width-W window " ++
      "gives d*#S <= W + d - 1); class-1 instance " ++
      "dccAlignedCount_of_pairwiseSpacing is ONE UNIT short of the supply " ++
      "(W + 2^v - 1 vs W) - a future alignment proof must pin the window start " ++
      "to the alignment class; the gap is recorded, not papered over.",
    "THE IMPROVED PER-PAIR ATOMS (workstream 1): DccClass1DeepPairAtomBoosted " ++
      "(q,K0,T,v) confines the per-pair demand to max T (1274739*2^v) < L; " ++
      "dccClass1Pair_of_boostedAtom closes the WHOLE pair from the boosted atom " ++
      "+ the pair-local aligned supply (DccClass1PairAlignedSupply), through the " ++
      "SRE dispatcher (L <= T), the parametric width gate (L <= 1274739) and the " ++
      "boosted gate (1274739 < L <= 1274739*2^v).  Field producer " ++
      "dccClass1Deep_field_of_boost: aligned supply at level v + residual above " ++
      "1274739*2^v rebuild the EXACT v19 class1Deep field.",
    "RUN STRATA CLOSED (workstream 2): the six kernel-certified " ++
      "band-{1,4}-free q < 64 pairs (3,1),(21,3),(51,1),(51,8),(63,1),(63,4) " ++
      "close Class5CycleNumericCloses OUTRIGHT at every context " ++
      "(dccClass5CycleCloses_of_bandFreePair - empty cycle band, 0 <= nonneg); " ++
      "dispatcher dccRunNumericLow_field_of_bandReading narrows the v19 " ++
      "runNumericLow supply to the band-reading strata.  HONEST: at " ++
      "band-reading pairs the wave-18 period floors stand - a " ++
      "Class5CycleNumericCloses witness needs a band-free period or c >= 1537, " ++
      "a Class5BandHeavyNumericCloses witness band-1-free or c >= 6145 " ++
      "(dstClass5CycleNumeric/BandHeavy_bandFree_or_long), against minimal " ++
      "periods <= 63 at q < 64 - only the per-context scalar horns remain and " ++
      "no in-tree numeric closes them at deep L; the q >= 64 tail carries no " ++
      "in-tree band-free certificates (the (93,15) closer is guard-excluded) - " ++
      "untouched.",
    "TOWER STRATA CLOSED (workstream 2): SEVEN q < 107 pairs proved " ++
      "band-4-free on a full period by NEW kernel cycle certificates " ++
      "(dccCycle_5_1 ... dccCycle_63_4): (5,1),(5,2),(7,3) - band-1/2-READING " ++
      "(invisible to the run band-free list) but band-4-free, so the tower " ++
      "count is void - plus (51,1),(51,8),(63,1),(63,4); " ++
      "dccClass2Cycle_of_band4FreePair closes Class2CycleInequality outright " ++
      "(class2CycleInequality_of_band_free, count 0).  Dispatcher " ++
      "dccTowerEnumLow_field_of_bandReading narrows the v19 towerEnumLow supply " ++
      "to the band-4-reading strata.  HONEST: at band-4-reading pairs " ++
      "dstTowerCycle_block_le_period forces m0 <= c at any reading witness " ++
      "period, against the unbounded m0 = ceil(3(r+1)/64) on deep shells (m0 > " ++
      "98 once r >= 2091, i.e. within the demanded L >= 986888 regime band) - " ++
      "the certified short periods (c <= 98) cannot carry the counting horn " ++
      "deep; the q >= 107 tail has no in-tree band-free certificates - " ++
      "untouched.",
    "WIRING (workstream 3): dccConvergenceResidual_of_deepCounting assembles a " ++
      "FULL Erdos260ConvergenceResidual from the narrowed supplies (boosted " ++
      "class-1 pair, band-reading tower/run lows, everything else verbatim v19); " ++
      "endpoint dccErdos260_of_deepCounting : ... -> Erdos260Statement through " ++
      "erdos260_of_convergenceResidual.",
    "WHAT REMAINS OPEN AFTER THIS MODULE (the honest core): (a) the class-1 " ++
      "aligned supplies at any level v >= 1 (the carry-alignment spacing of the " ++
      "class-1 fibre - NOT derivable from the in-tree valuation lemmas, which " ++
      "are class-4-side) and the boosted residual atoms at L > 1274739*2^v per " ++
      "table pair; (b) towerEnumLow at the band-4-READING q < 107 pairs (the " ++
      "sharp m0 <= t thresholds) and the whole q >= 107 tail modulo the " ++
      "order-gt escape; (c) runNumericLow/Tail at the band-reading pairs (the " ++
      "band-1 half-density and heavy-span scalars; periods below the 1537/6145 " ++
      "floors force the band-free horn, which those pairs do not have); (d) " ++
      "deepOrbitPin (ExitMassControlCore supplies it), the return/densepack " ++
      "off-table fields, the class-0 gates at deep regimes - untouched here.",
    "HYGIENE: additive only - ONE new module, no existing file edited, not " ++
      "root-wired (built standalone as Erdos260.DeepCountingClosure); no sorry " ++
      "/ admit / new axiom / native_decide; every key declaration passes " ++
      "#print axioms within [propext, Classical.choice, Quot.sound]." ]

/-- The status ledger is non-empty (honest, non-vacuous). -/
theorem deepCountingClosureStatus_nonempty :
    deepCountingClosureStatus ≠ [] := by
  simp [deepCountingClosureStatus]

/-! ## Part 9.  Axiom-cleanliness audit
Every key declaration; expected axioms `[propext, Classical.choice, Quot.sound]`
or fewer. -/

#print axioms dccBoostGate
#print axioms dccBoostGate_sharp
#print axioms dccClass1Absorption_of_spacedCount
#print axioms dccAlignedSupply_zero_free
#print axioms dccClass1Deep_field_of_boost
#print axioms dccBoost_zero_recovers
#print axioms dccResidual_zero_of_field
#print axioms dccClass1Pair_of_boostedAtom
#print axioms dccSpacedCount_le
#print axioms dccAlignedCount_of_pairwiseSpacing
#print axioms dccClass5CycleCloses_of_bandFreePair
#print axioms dccRunNumericLow_field_of_bandReading
#print axioms dccClass2Cycle_of_band4FreePair
#print axioms dccTowerEnumLow_field_of_bandReading
#print axioms dccConvergenceResidual_of_deepCounting
#print axioms dccErdos260_of_deepCounting
#print axioms deepCountingClosureStatus_nonempty

end

end Erdos260
