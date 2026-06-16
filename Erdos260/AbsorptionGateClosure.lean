import Erdos260.Erdos260EndgameCapstone
import Erdos260.ExitMassTranscription

/-!
# Wave-18: the absorption-gate closure pass (`AbsorptionGateClosure`)

The absorption/count lanes of the wave-17 endgame capstone
(`Erdos260EndgameResidual`), worked through the EXIT-MASS (deviation) calculus of
`ExitMassTranscription`.  Five levers, each settled honestly:

* **Lever (a) — the global deviation budget.**  REFUTED IN-TREE.  All nineteen
  class-0 survivor pairs read recurrent band `canonGap q (slopeOrbit q K₀ 1) ∈
  {1, 2, 3}` (`agcSurvivorBand_le_four`), so the deviation calculus applies at
  every survivor context — but then so does the relocated Lemma 21.1 pressure
  floor `X ≤ 2·emExitMass` (`agcSurvivor_exitMass_floor`): the in-tree deviation
  budget over the shell window is bounded BELOW by `X/2 = (768/1536)·X`, which
  EXCEEDS the corrected per-class capacity `(31/1536)·X` by the factor `768/31 ≈
  24.8` (`agcCap_lt_devFloor`).  Every sum-route absorption gate built on the
  deviation budget is therefore FALSE at every survivor context
  (`agcClass0DevGate_refuted`, `agcGenericDevGate_refuted`) — the brief's hoped
  `D_total ≤ c₀·X` with `c₀ < 31/1536` is impossible: `c₀ ≥ 1/2` in-tree.

* **Lever (b) — the c-spacing overlap counting.**  PROVED EXACTLY
  (`agc_spaced_windowSum_le`): the windows of `c`-spaced members overlap-count
  each deviating gap at most `⌈(r+1)/c⌉ = (r+c)/c` times, so
  `mass₀ ≤ ((r+c)/c)·emExitMass` (`agcClass0Mass_le_overlap_devBudget`) — the
  sharp telescoped form of the count-times-max route.  HONEST comparison: with
  the in-tree ceiling `emExitMass ≤ (W+r)(L+B+1)` this is `((r+c)/c)(W+r)(L+B+1)`
  against the count route `⌈W/c⌉(r+1)(L+B+1)` — ratio `(W+r)/W ≤ 2`; the hoped
  factor `window/c` does NOT materialize because the count route already
  consumes the spacing in its count.  The gain is REAL only against the
  deviation mass itself, and lever (a) kills that budget.

* **Lever (c) — the mid/big emptiness razor.**  RAZOR CONFIRMED, DE-RAZORED:
  the corrected ledger row needs only `mass₀ ≤ (31/1536)·X`, and the new surface
  `Erdos260AbsorptionResidual` demands MASS caps on ALL THREE class-0 lanes
  (survivor, mid-band, big-order) — strictly weaker than the wave-17 fields
  (count-cap / emptiness / emptiness) — yet still reaches `Erdos260Statement`
  (`erdos260_of_absorptionResidual`): the `48 ≤ q < 96` band-free complement
  closes through `Class0CycleDeepBandFree`, the certificate horn of the big lane
  through `class0Tail_of_order_gt`, exactly as before.  The wave-17 surface maps
  in (`absorptionResidual_of_endgameResidual`); NO converse is claimed.

* **Lever (d) — the top-band-light interior demands.**  PROVED CONDITIONAL
  closures of the exact `returnInterior` / `densePackInterior` field types from
  a top-band deviation-light hypothesis (`agcReturnInteriorField_of_topBandDevLight`,
  `agcDensePackInteriorField_of_topBandDevLight`): heavy members carry `Y ≤
  windowExcess ≤ devWindow ≤` (top-band deviation mass), so top-band deviation
  `< Y` voids every heavy member there.  HONEST: the only in-tree ceiling on the
  top-band deviation is `(2r+1)(L+B+1) ≥ Y = L/64` (`agcTopBandDev_le_cap`) —
  no band-localized M.5 cap exists in-tree, so the hypothesis is a genuine new
  demand, not a theorem.  The spaced top-band POPULATION cap is unconditional
  at survivors: at most `(r+c)/c` class-0 members sit in the top band
  (`agcClass0TopBand_card_le`).

* **Lever (e) — the cycle-count gate on band-2-free contexts.**  PROVED
  CONDITIONAL: any certified period `c` with band-2 residue count `b₂` and the
  numeric regime `(W/c + 1)·b₂ ≤ r + 1` closes `ReturnGatesBodyUngated` and the
  exact `returnGatesFree` field (`agcReturnGatesUngated_of_cycleCount_ceil`,
  `agcReturnGatesFreeField_of_cycleCount`).  At band-2 pins `b₂ = c` and the
  regime is impossible (consistent with the wave-17 voiding split); on genuinely
  band-2-light cycles it is the honest `W ≲ (r+1)·c/b₂` window regime.

Additive only — ONE new module; no sorry / admit / new axiom / native_decide.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Part 0.  The survivor recurrent-band pins

`fixedFamilyRecurrentBand ctx = canonGap q (slopeOrbit q K₀ 1)`, evaluated at all
nineteen class-0 survivor pairs through the in-tree orbit-step evaluator.  All
nineteen bands land in `{1, 2, 3}` — the deviation calculus (`em_*`) applies at
EVERY survivor context, with no fixed-family hypothesis. -/

/-- One-step band evaluation: the orbit value at index `1` and its canonical gap,
both certified by the dyadic band data. -/
theorem agcBandPin (qv Kv g1 v1 g2 : ℕ) (hK1 : 1 ≤ Kv)
    (hlow1 : 2 ^ g1 * Kv ≤ qv) (hhigh1 : qv < 2 ^ (g1 + 1) * Kv)
    (hw1 : 2 ^ (g1 + 1) * Kv = qv + v1)
    (hv1 : 1 ≤ v1) (hlow2 : 2 ^ g2 * v1 ≤ qv) (hhigh2 : qv < 2 ^ (g2 + 1) * v1) :
    canonGap qv (slopeOrbit qv Kv 1) = g2 + 1 := by
  have e0 : slopeOrbit qv Kv 0 = Kv := rfl
  have e1 : slopeOrbit qv Kv 1 = v1 :=
    slopeOrbit_step_eval 0 g1 e0 hK1 hlow1 hhigh1 hw1
  rw [e1]
  exact canonGap_eval hv1 hlow2 hhigh2

/-- The `≤ 4` form consumed by the deviation calculus. -/
theorem agcBandPin_le_four (qv Kv g1 v1 g2 : ℕ) (hg2 : g2 ≤ 3) (hK1 : 1 ≤ Kv)
    (hlow1 : 2 ^ g1 * Kv ≤ qv) (hhigh1 : qv < 2 ^ (g1 + 1) * Kv)
    (hw1 : 2 ^ (g1 + 1) * Kv = qv + v1)
    (hv1 : 1 ≤ v1) (hlow2 : 2 ^ g2 * v1 ≤ qv) (hhigh2 : qv < 2 ^ (g2 + 1) * v1) :
    canonGap qv (slopeOrbit qv Kv 1) ≤ 4 := by
  rw [agcBandPin qv Kv g1 v1 g2 hK1 hlow1 hhigh1 hw1 hv1 hlow2 hhigh2]
  omega

/-- **The nineteen survivor band pins**: every class-0 survivor context has
recurrent band `≤ 4` (the values are `1`, `2` or `3` pair by pair) — the
EXIT-MASS calculus of `ExitMassTranscription` applies at every survivor pair. -/
theorem agcSurvivorBand_le_four (ctx : ActualFailureContext)
    (h : Class0DatumSurvivor ctx) : fixedFamilyRecurrentBand ctx ≤ 4 := by
  unfold fixedFamilyRecurrentBand
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · rw [h.1, h.2]
    exact agcBandPin_le_four 17 8 1 15 0 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [h.1, h.2]
    exact agcBandPin_le_four 19 9 1 17 0 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [h.1, h.2]
    exact agcBandPin_le_four 21 1 4 11 0 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [h.1, h.2]
    exact agcBandPin_le_four 25 2 3 7 1 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [h.1, h.2]
    exact agcBandPin_le_four 25 12 1 23 0 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [h.1, h.2]
    exact agcBandPin_le_four 27 1 4 5 2 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [h.1, h.2]
    exact agcBandPin_le_four 27 4 2 5 2 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [h.1, h.2]
    exact agcBandPin_le_four 27 13 1 25 0 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [h.1, h.2]
    exact agcBandPin_le_four 29 14 1 27 0 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [h.1, h.2]
    exact agcBandPin_le_four 33 1 5 31 0 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [h.1, h.2]
    exact agcBandPin_le_four 33 16 1 31 0 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [h.1, h.2]
    exact agcBandPin_le_four 35 2 4 29 0 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [h.1, h.2]
    exact agcBandPin_le_four 37 18 1 35 0 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [h.1, h.2]
    exact agcBandPin_le_four 39 1 5 25 0 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [h.1, h.2]
    exact agcBandPin_le_four 41 20 1 39 0 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [h.1, h.2]
    exact agcBandPin_le_four 43 21 1 41 0 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [h.1, h.2]
    exact agcBandPin_le_four 45 1 5 19 1 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [h.1, h.2]
    exact agcBandPin_le_four 45 2 4 19 1 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [h.1, h.2]
    exact agcBandPin_le_four 45 4 3 19 1 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The actual scale is positive (`2²⁴·W < 17·X` with any `W`). -/
theorem agcX_ge_one (ctx : ActualFailureContext) : 1 ≤ ctx.shell.X := by
  have h := em_supportShell_strict ctx
  omega

/-! ## Part 1.  Lever (b) made exact: the spaced-overlap window-sum bound

The windows `[k, k+r]` of `c`-spaced members cover each position at most
`⌈(r+1)/c⌉ = (r+c)/c` times: split `range (r+1)` into `(r+c)/c` blocks of length
`c`; within a block the shifted copies of a `c`-spaced set are pairwise disjoint
(a collision forces a spacing `< c`), so each block contributes at most one full
copy of the ambient weight sum. -/

/-- **The spaced-overlap window-sum bound** (generic): if `S` is `c`-spaced and
every window position lands in `U`, then the summed window weights telescope to
at most `⌈(r+1)/c⌉ = (r+c)/c` copies of the `U`-total. -/
theorem agc_spaced_windowSum_le {S U : Finset ℕ} {c r : ℕ} (w : ℕ → ℕ)
    (hc : 1 ≤ c)
    (hspace : ∀ x ∈ S, ∀ z ∈ S, x ≤ z → c ∣ z - x)
    (hU : ∀ k ∈ S, ∀ i, i < r + 1 → k + i ∈ U) :
    ∑ k ∈ S, ∑ i ∈ Finset.range (r + 1), w (k + i)
      ≤ ((r + c) / c) * ∑ j ∈ U, w j := by
  have hc0 : 0 < c := hc
  have hmaps : ∀ i ∈ Finset.range (r + 1), i / c ∈ Finset.range ((r + c) / c) := by
    intro i hi
    rw [Finset.mem_range] at hi ⊢
    have h1 : i / c ≤ r / c := Nat.div_le_div_right (by omega)
    have h2 : (r + c) / c = r / c + 1 := Nat.add_div_right r hc0
    omega
  have hblock : ∀ b ∈ Finset.range ((r + c) / c),
      ∑ i ∈ (Finset.range (r + 1)).filter (fun i => i / c = b),
        ∑ k ∈ S, w (k + i)
        ≤ ∑ j ∈ U, w j := by
    intro b _
    have hinj : ∀ p ∈ ((Finset.range (r + 1)).filter (fun i => i / c = b)) ×ˢ S,
        ∀ q ∈ ((Finset.range (r + 1)).filter (fun i => i / c = b)) ×ˢ S,
          (fun p : ℕ × ℕ => p.2 + p.1) p = (fun p : ℕ × ℕ => p.2 + p.1) q → p = q := by
      rintro ⟨i, k⟩ hp ⟨i', k'⟩ hq heq
      have heq' : k + i = k' + i' := heq
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hp hq
      have hub : i < (i / c + 1) * c := (Nat.div_lt_iff_lt_mul hc0).mp (Nat.lt_succ_self _)
      have hub' : i' < (i' / c + 1) * c := (Nat.div_lt_iff_lt_mul hc0).mp (Nat.lt_succ_self _)
      have hlb : i / c * c ≤ i := Nat.div_mul_le_self _ _
      have hlb' : i' / c * c ≤ i' := Nat.div_mul_le_self _ _
      have hii : i / c = i' / c := by rw [hp.1.2, hq.1.2]
      have key1 : i < i' + c := by
        calc i < (i / c + 1) * c := hub
          _ = i / c * c + c := by rw [add_one_mul]
          _ = i' / c * c + c := by rw [hii]
          _ ≤ i' + c := Nat.add_le_add_right hlb' c
      have key2 : i' < i + c := by
        calc i' < (i' / c + 1) * c := hub'
          _ = i' / c * c + c := by rw [add_one_mul]
          _ = i / c * c + c := by rw [hii]
          _ ≤ i + c := Nat.add_le_add_right hlb c
      rcases le_total k k' with hkk | hkk
      · have hdvd : c ∣ k' - k := hspace k hp.2 k' hq.2 hkk
        have h0 : k' - k = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
        have hk : k = k' := by omega
        have hi2 : i = i' := by omega
        rw [hk, hi2]
      · have hdvd : c ∣ k - k' := hspace k' hq.2 k hp.2 hkk
        have h0 : k - k' = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
        have hk : k = k' := by omega
        have hi2 : i = i' := by omega
        rw [hk, hi2]
    calc ∑ i ∈ (Finset.range (r + 1)).filter (fun i => i / c = b), ∑ k ∈ S, w (k + i)
        = ∑ p ∈ ((Finset.range (r + 1)).filter (fun i => i / c = b)) ×ˢ S,
            w (p.2 + p.1) :=
          (Finset.sum_product' ((Finset.range (r + 1)).filter (fun i => i / c = b)) S
            (fun i k => w (k + i))).symm
      _ = ∑ j ∈ (((Finset.range (r + 1)).filter (fun i => i / c = b)) ×ˢ S).image
            (fun p => p.2 + p.1), w j := (Finset.sum_image hinj).symm
      _ ≤ ∑ j ∈ U, w j := by
          refine Finset.sum_le_sum_of_subset ?_
          intro j hj
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hj
          simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hp
          exact hU p.2 hp.2 p.1 hp.1.1
  calc ∑ k ∈ S, ∑ i ∈ Finset.range (r + 1), w (k + i)
      = ∑ i ∈ Finset.range (r + 1), ∑ k ∈ S, w (k + i) := Finset.sum_comm
    _ = ∑ b ∈ Finset.range ((r + c) / c),
          ∑ i ∈ (Finset.range (r + 1)).filter (fun i => i / c = b),
            ∑ k ∈ S, w (k + i) :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ _b ∈ Finset.range ((r + c) / c), ∑ j ∈ U, w j :=
        Finset.sum_le_sum hblock
    _ = ((r + c) / c) * ∑ j ∈ U, w j := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- **The sum-route transcription** (any class, band `≤ 4`): the routed class mass
is the SUM of window excesses, each bounded by its window's DEVIATION content
(`em_windowExcess_le_devWindow`). -/
theorem agcClassMass_le_sum_devWindow (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4) (i : Fin 7) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) i
      ≤ ((∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i,
          emDevWindow ctx k : ℕ) : ℝ) := by
  rw [routedClassMassOf_eq_sum_fibre, Nat.cast_sum]
  exact Finset.sum_le_sum fun k _ => em_windowExcess_le_devWindow ctx hband k

/-- The class-0 fibre's summed deviation content telescopes through the survivor
`c`-spacing: each deviating gap is counted at most `(r+c)/c = ⌈(r+1)/c⌉` times. -/
theorem agcClass0DevSum_le_overlap (ctx : ActualFailureContext)
    (hsurv : Class0DatumSurvivor ctx) :
    ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0, emDevWindow ctx k
      ≤ ((ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
            / class0SurvivorPeriod (class1SlopeDatum ctx).q)
          * emExitMass ctx := by
  have hc : 1 ≤ class0SurvivorPeriod (class1SlopeDatum ctx).q :=
    tfaClass0SurvivorPeriod_pos _
  have hspace := ofcClass0Member_spacing_of_survivor ctx hsurv
  have hU : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0,
      ∀ i, i < ctx.n24CarryData.r + 1 → k + i ∈ emReach ctx := by
    intro k hk i hi
    have hks : k ∈ ctx.n24CarryData.starts :=
      (mem_highExcessStarts.mp (Finset.mem_filter.mp hk).1).1
    rw [cnlMulti_starts_eq_window, Finset.mem_Ico] at hks
    unfold emReach emF emW
    rw [Finset.mem_Ico]
    omega
  unfold emDevWindow emExitMass
  exact agc_spaced_windowSum_le (emExitWeight ctx) hc hspace hU

/-- **THE LEVER-(b) HEADLINE**: at every survivor pair the class-0 routed mass is
bounded by `⌈(r+1)/c⌉` copies of the TOTAL deviation mass — the exact telescoped
sum-route bound (`mass₀ ≤ ((r+c)/c)·emExitMass`), with no per-member
`runDyadicMult` ceiling consumed. -/
theorem agcClass0Mass_le_overlap_devBudget (ctx : ActualFailureContext)
    (hsurv : Class0DatumSurvivor ctx) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 0
      ≤ ((((ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
            / class0SurvivorPeriod (class1SlopeDatum ctx).q)
          * emExitMass ctx : ℕ) : ℝ) :=
  le_trans (agcClassMass_le_sum_devWindow ctx (agcSurvivorBand_le_four ctx hsurv) 0)
    (Nat.cast_le.mpr (agcClass0DevSum_le_overlap ctx hsurv))

/-- The generic-class sum-route budget (no spacing input): overlap factor `r + 1`
(the `(r+1)`-fold covering of `em_devWindow_sum_le`, restricted to the fibre). -/
theorem agcClassMass_le_devBudget (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4) (i : Fin 7) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) i
      ≤ (((ctx.n24CarryData.r + 1) * emExitMass ctx : ℕ) : ℝ) := by
  have hsub : routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i
      ⊆ ctx.n24CarryData.starts := by
    intro k hk
    exact (mem_highExcessStarts.mp (Finset.mem_filter.mp hk).1).1
  have h1 : ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i,
      emDevWindow ctx k ≤ (ctx.n24CarryData.r + 1) * emExitMass ctx :=
    le_trans (Finset.sum_le_sum_of_subset hsub) (em_devWindow_sum_le ctx)
  exact le_trans (agcClassMass_le_sum_devWindow ctx hband i) (Nat.cast_le.mpr h1)

/-! ## Part 2.  Lever (a): the sum-route gates and their HONEST refutation

The conditional gates are genuine theorems; the in-tree pressure floor then shows
their hypotheses are FALSE at every context where the calculus applies.  The
deviation budget is a floor (`X/2 ≤ emExitMass`), not a small ceiling: `c₀ = 1/2 >
31/1536`, factor `768/31 ≈ 24.8`. -/

/-- **The NEW sum-route absorption gate (conditional)**: the deviation-budget gate
`1536·⌈(r+1)/c⌉·emExitMass ≤ 31·X` closes the de-razored survivor-lane MASS cap
(the `Erdos260AbsorptionResidual` lane shape below). -/
theorem agcClass0MassAbsorption_of_devGate (ctx : ActualFailureContext)
    (hsurv : Class0DatumSurvivor ctx)
    (hgate : 1536 * (((ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
            / class0SurvivorPeriod (class1SlopeDatum ctx).q)
          * emExitMass ctx)
        ≤ 31 * ctx.shell.X) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 0
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have h1 := agcClass0Mass_le_overlap_devBudget ctx hsurv
  have h2 : (1536 : ℝ)
        * ((((ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
              / class0SurvivorPeriod (class1SlopeDatum ctx).q)
            * emExitMass ctx : ℕ) : ℝ)
      ≤ 31 * (ctx.shell.X : ℝ) := by exact_mod_cast hgate
  have hc6 : erdos260Constants.cStar * erdos260Constants.ξ / 6 = 31 / 1536 := by
    rw [tfaCstarXi_eq]; norm_num
  rw [hc6]
  linarith

/-- **The survivor exit-mass floor**: the relocated Lemma 21.1 pressure floor fires
at every survivor pair (band `≤ 4` there) — the in-tree deviation budget over the
shell window is at least `X/2`. -/
theorem agcSurvivor_exitMass_floor (ctx : ActualFailureContext)
    (hsurv : Class0DatumSurvivor ctx) :
    ctx.shell.X ≤ 2 * emExitMass ctx :=
  em_exitMass_lower_of_band ctx (agcSurvivorBand_le_four ctx hsurv)

/-- **THE LEVER-(a) ARITHMETIC**: wherever the deviation calculus applies the
corrected per-class capacity `(31/1536)·X` sits STRICTLY BELOW the deviation
budget itself — `(31/1536)·X < emExitMass` (`X/2 ≤ emExitMass` and `31/1536 <
1/2`).  No deviation-budget cap below the gate exists in-tree. -/
theorem agcCap_lt_devFloor (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4) :
    erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ)
      < (emExitMass ctx : ℝ) := by
  have hfloor := em_exitMass_lower_of_band ctx hband
  have hX1 := agcX_ge_one ctx
  have hcast : (ctx.shell.X : ℝ) ≤ 2 * (emExitMass ctx : ℝ) := by exact_mod_cast hfloor
  have hXR : (1 : ℝ) ≤ (ctx.shell.X : ℝ) := by exact_mod_cast hX1
  have hc6 : erdos260Constants.cStar * erdos260Constants.ξ / 6 = 31 / 1536 := by
    rw [tfaCstarXi_eq]; norm_num
  rw [hc6]
  linarith

/-- **The sum-route gate is REFUTED at every survivor pair**: even the sharpest
overlap factor cannot push `1536·⌈(r+1)/c⌉·emExitMass` under `31·X` — the floor
gives `1536·emExitMass ≥ 768·X > 31·X`.  Lever (a) is settled NEGATIVELY with
exact in-tree constants. -/
theorem agcClass0DevGate_refuted (ctx : ActualFailureContext)
    (hsurv : Class0DatumSurvivor ctx) :
    ¬ (1536 * (((ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
            / class0SurvivorPeriod (class1SlopeDatum ctx).q)
          * emExitMass ctx)
        ≤ 31 * ctx.shell.X) := by
  intro hgate
  have hfloor := agcSurvivor_exitMass_floor ctx hsurv
  have hX1 := agcX_ge_one ctx
  have hM : 1 ≤ (ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
      / class0SurvivorPeriod (class1SlopeDatum ctx).q :=
    (Nat.one_le_div_iff (tfaClass0SurvivorPeriod_pos _)).mpr (Nat.le_add_left _ _)
  have h3 : emExitMass ctx
      ≤ (ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
          / class0SurvivorPeriod (class1SlopeDatum ctx).q * emExitMass ctx :=
    Nat.le_mul_of_pos_left _ hM
  generalize hBdef : (ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
      / class0SurvivorPeriod (class1SlopeDatum ctx).q * emExitMass ctx = B at hgate h3
  omega

/-- The generic-class sum-route gate is refuted wherever the calculus applies
(class 3's width-gate analogue included): `1536·(r+1)·emExitMass > 31·X`. -/
theorem agcGenericDevGate_refuted (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4) :
    ¬ (1536 * ((ctx.n24CarryData.r + 1) * emExitMass ctx) ≤ 31 * ctx.shell.X) := by
  intro hgate
  have hfloor := em_exitMass_lower_of_band ctx hband
  have hX1 := agcX_ge_one ctx
  have h3 : emExitMass ctx ≤ (ctx.n24CarryData.r + 1) * emExitMass ctx :=
    Nat.le_mul_of_pos_left _ (by omega)
  generalize hBdef : (ctx.n24CarryData.r + 1) * emExitMass ctx = B at hgate h3
  omega

/-- The sum-route gate wired to the de-razored survivor lane (honest: by
`agcClass0DevGate_refuted` the hypothesis is unsatisfiable at survivor contexts —
recorded for SHAPE, the refutation is the substantive result). -/
theorem agcClass0MassLane_of_devGate
    (h : ∀ ctx : ActualFailureContext, Class0DatumSurvivor ctx →
      1536 * (((ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
            / class0SurvivorPeriod (class1SlopeDatum ctx).q)
          * emExitMass ctx)
        ≤ 31 * ctx.shell.X) :
    ∀ ctx : ActualFailureContext, Class0DatumSurvivor ctx →
      routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 0
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) :=
  fun ctx hs => agcClass0MassAbsorption_of_devGate ctx hs (h ctx hs)

/-! ## Part 3.  Lever (c): the fully de-razored absorption surface

The wave-17 class-0 field demands count-cap at survivors and EMPTINESS on the
mid/big lanes.  The corrected ledger row consumes only the routed MASS — the
surface below demands mass caps on all three lanes (strictly weaker on each) and
still reaches `Erdos260Statement` through the same walk. -/

/-- **The wave-18 absorption surface**: the wave-17 endgame surface with the
class-0 field de-razored to MASS form on ALL THREE lanes — survivor count-cap →
mass cap (`mass₀ ≤ count·runDyadicMult` is lossy), mid-band emptiness → mass cap,
big-order emptiness horn → mass cap.  All other thirteen fields verbatim. -/
structure Erdos260AbsorptionResidual where
  /-- Tower / class 2 - enumerated part (`q < 107`); verbatim wave-17 field. -/
  towerEnumLow : ∀ ctx : ActualFailureContext,
    TowerModulusEnumEscapeV2 ctx → (class1SlopeDatum ctx).q < 107 →
    (ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx) →
    ¬ ((class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1) →
    ¬ ((class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3) →
    Class2CycleInequality ctx
  /-- Tower / class 2 - tail (`107 ≤ q`); verbatim wave-17 field. -/
  towerEnumTail : ∀ ctx : ActualFailureContext,
    TowerModulusEnumEscapeV2 ctx →
    107 ≤ (class1SlopeDatum ctx).q →
    (ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx) →
    (((Nat.log 2 (class1SlopeDatum ctx).q + 1) * shellWidth ctx
        < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
            (class1SlopeDatum ctx).K₀)))
        ∧ TowerBand4Budget ctx)
      ∨ Class2CycleInequality ctx
  /-- The band-4 orbit-pin voiding (verbatim wave-17 field). -/
  runBand4Void : ∀ ctx : ActualFailureContext, ¬ OrbitBandPinned ctx 4
  /-- Run / class 5 - enumerated part (`q < 64`); verbatim wave-17 field. -/
  runNumericLow : ∀ ctx : ActualFailureContext,
    ¬ OrbitBandPinned ctx 4 →
    (class1SlopeDatum ctx).q < 64 →
    Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx
  /-- Run / class 5 - tail (`64 ≤ q`); verbatim wave-17 field. -/
  runNumericTail : ∀ ctx : ActualFailureContext,
    ¬ OrbitBandPinned ctx 4 →
    64 ≤ (class1SlopeDatum ctx).q →
    ¬ ((class1SlopeDatum ctx).q = 93 ∧ (class1SlopeDatum ctx).K₀ = 15) →
    ((Nat.log 2 (class1SlopeDatum ctx).q + 1)
        * (supportShell ctx.shell.d ctx.shell.X).card
      < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
          (class1SlopeDatum ctx).K₀)))
      ∧ RunBandBudget ctx
    ∨ Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx
  /-- The band-2 orbit-pin voiding (verbatim wave-17 field). -/
  returnBand2Void : ∀ ctx : ActualFailureContext, ¬ OrbitBandPinned ctx 2
  /-- Return / class 4 count gates on band-2-free contexts (verbatim wave-17). -/
  returnGatesFree : ∀ ctx : ActualFailureContext, ¬ OrbitBandPinned ctx 2 →
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    2 * (129 * shellLadderDepth ctx + 64)
      ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card
            + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
    ReturnGatesBodyUngated ctx
  /-- Return / class 4 K.1 interior (verbatim wave-17 field). -/
  returnInterior : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx
  /-- The wide band-3 orbit-pin voiding (verbatim wave-17 field). -/
  densePackBand3Void : ∀ ctx : ActualFailureContext, ¬ Band3PinnedWide ctx
  /-- DensePack / class 3 corrected K.1.2 Nat-cover on the wide band-3-free
  complement (verbatim wave-17 field). -/
  densePackCoverFree : ∀ ctx : ActualFailureContext, ¬ Band3PinnedWide ctx →
    ¬ Class3CycleBand3Free ctx →
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
    ¬ DensePackDatumClosed ctx →
    (genuineDensePackStarts ctx).card
        * ((ctx.n24CarryData.r + 1) * densePackDyadicG0 ctx
            - (2 * shellLadderDepth ctx + 1))
      ≤ (proofV4DensePackActualPoints ctx.shell).card
  /-- DensePack / class 3 K.1.1 coarea hit-density (verbatim wave-17 field). -/
  densePackDensity : ∀ ctx : ActualFailureContext,
    ¬ Class3CycleBand3Free ctx →
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
    ¬ DensePackDatumClosed ctx →
    densePackEndpointDensity ctx
  /-- DensePack / class 3 K.1 active-window interior (verbatim wave-17 field). -/
  densePackInterior : ∀ ctx : ActualFailureContext,
    ¬ Class3TopBandCycleFree ctx →
    ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
    ¬ DensePackDatumClosed ctx →
    ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r + 1
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card
  /-- **The fully de-razored class-0 field**: MASS caps on all three lanes.
  Survivor lane: `mass₀ ≤ (31/1536)·X` (weaker than the wave-17 count-cap, which
  is weaker than the wave-16 emptiness).  Mid lane (`48 ≤ q < 96`, cycle meets
  `{1,3,5}`): the mass cap REPLACES emptiness — the in-tree band-free complement
  closes the rest.  Big lane (`96 ≤ q`): the order/period certificate horn kept
  verbatim, the emptiness horn replaced by the mass cap. -/
  class0MassAbsorption : ∀ ctx : ActualFailureContext,
    (Class0DatumSurvivor ctx →
      routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 0
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ)) ∧
    (48 ≤ (class1SlopeDatum ctx).q → (class1SlopeDatum ctx).q < 96 →
      Class0CycleMeetsShallow ctx →
      routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 0
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ)) ∧
    (96 ≤ (class1SlopeDatum ctx).q →
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
      ∨ routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 0
          ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ))
  /-- The regime-folded class-1 absorption field (verbatim wave-17 field). -/
  class1CapAbsorption : ∀ ctx : ActualFailureContext,
    1 ≤ ctx.n24CarryData.r →
    (¬ ∃ cv bv Tv : ℕ,
      ((class1SlopeDatum ctx).q, (class1SlopeDatum ctx).K₀, cv, bv, Tv)
          ∈ sreClass1ThresholdTable
        ∧ shellLadderDepth ctx ≤ Tv) →
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ)

namespace Erdos260AbsorptionResidual

/-- The split fields rebuild the FULL wave-16 `returnGates` field. -/
theorem returnGatesField (R : Erdos260AbsorptionResidual) : ReturnGatesField :=
  returnGatesField_iff_band2Void_split.mpr ⟨R.returnBand2Void, R.returnGatesFree⟩

/-- The split fields rebuild the FULL wave-16 densepack Nat-cover field. -/
theorem densePackCoverField (R : Erdos260AbsorptionResidual) : DensePackCoverField :=
  densePackCoverField_iff_band3Void_split.mpr ⟨R.densePackBand3Void, R.densePackCoverFree⟩

/-- The collapsed densepack residual (verbatim wave-17 walk). -/
def densePackUngated (R : Erdos260AbsorptionResidual) : DensePackUngatedClosureResidual where
  ungatedDensity := R.densePackDensity
  ungatedInterior := R.densePackInterior
  ungatedCoverNat := R.densePackCoverField

/-- Tower lane (verbatim wave-17 walk). -/
def towerEnum (R : Erdos260AbsorptionResidual) : TowerModulusEnumerationResidual := by
  intro ctx _hdeep hesc
  have hescV2 : TowerModulusEnumEscapeV2 ctx :=
    (towerModulusEnumEscape_iff_v2 ctx).mp hesc
  have haper : ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx := fun hu7 hwp =>
    thirdsLever_windowPeriodic_void_of_oddpartQ_le_seven ctx hu7 hwp
  rcases Nat.lt_or_ge (class1SlopeDatum ctx).q 107 with hlt | hge
  · by_cases h31 : (class1SlopeDatum ctx).q = 3 ∧ (class1SlopeDatum ctx).K₀ = 1
    · exact anchoredCapstone_class2Ineq_of_datum_3_1 ctx h31.1 h31.2
    · by_cases h213 : (class1SlopeDatum ctx).q = 21 ∧ (class1SlopeDatum ctx).K₀ = 3
      · exact anchoredCapstone_class2Ineq_of_datum_21_3 ctx h213.1 h213.2
      · exact R.towerEnumLow ctx hescV2 hlt haper h31 h213
  · cases R.towerEnumTail ctx hescV2 hge haper with
    | inl ho => exact towerTail_of_order_gt ctx ho.1 ho.2
    | inr hineq => exact hineq

/-- The V3 tower count of the budget (verbatim wave-17 walk). -/
def towerCountV3 (R : Erdos260AbsorptionResidual) :
    ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx :=
  p9V3TowerCount_ofShallowDeep
    (towerDeepResidual_ofCountBound (towerCountBound_of_modulusEnumeration R.towerEnum))

/-- Run lane (verbatim wave-17 walk). -/
def runNumeric (R : Erdos260AbsorptionResidual) : RunCycleNumericSettlementHyp := by
  intro ctx _hr
  have hnp : ¬ OrbitBandPinned ctx 4 := R.runBand4Void ctx
  rcases Nat.lt_or_ge (class1SlopeDatum ctx).q 64 with hlt | hge
  · exact R.runNumericLow ctx hnp hlt
  · by_cases h93 : (class1SlopeDatum ctx).q = 93 ∧ (class1SlopeDatum ctx).K₀ = 15
    · exact Or.inr (ftRunCloses_of_datum_93_15 ctx h93.1 h93.2)
    · cases R.runNumericTail ctx hnp hge h93 with
      | inl ho => exact Or.inr (runTail_of_order_gt ctx ho.1 ho.2)
      | inr hrun => exact hrun

/-- The Run max-core family of the budget (verbatim wave-17 walk). -/
def runCore (R : Erdos260AbsorptionResidual) :
    ∀ ctx : ActualFailureContext, RunClass5LeafSupportMaxCoreResidual ctx :=
  fun ctx => (runSplitOfNumeric (runCycleNumericField_settled R.runNumeric) ctx).toCore

/-- The V3 run chain of the budget (verbatim wave-17 walk). -/
def runChain (R : Erdos260AbsorptionResidual) :
    ∀ ctx : ActualFailureContext, RunClass5StageChain ctx :=
  p9V3RunChainOfResidual (runClass5LeafResidual_ofSupportMaxCoreResidual R.runCore)

/-- The wave-3 4-way gate disjunction (verbatim wave-17 walk). -/
def returnGatesCycle (R : Erdos260AbsorptionResidual) :
    ∀ ctx : ActualFailureContext, ReturnGatesBody ctx := fun ctx => by
  by_cases hfree : ReturnB2FreeDatum ctx
  · exact (returnCtxAllFour_of_b2FreeDatum ctx hfree).1
  · by_cases hone : ReturnB2OneSpacedDatum ctx
    · exact (returnGatesZeroCard_of_b2OneSpacedDatum ctx hone).1
    · by_cases hnum : 64 * (((supportShell ctx.shell.d ctx.shell.X).card
            + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
          < 2 * (129 * shellLadderDepth ctx + 64)
      · exact returnGatesBody_of_reach_numeric ctx hnum
      · exact (returnGatesBody_iff_ungated ctx).mpr
          (R.returnGatesField ctx hfree hone (not_lt.mp hnum))

/-- The class-4 population bound from the gates (verbatim wave-17 walk). -/
theorem fibreSmall (R : Erdos260AbsorptionResidual) : Class4FibreSmall :=
  class4FibreSmall_of_gates R.returnGatesCycle

/-- The per-ctx K.1 interior (verbatim wave-17 walk). -/
def interiorAt (R : Erdos260AbsorptionResidual) (ctx : ActualFailureContext) :
    ReturnInteriorBody ctx := by
  by_cases hfree : ReturnB2FreeDatum ctx
  · exact (returnCtxAllFour_of_b2FreeDatum ctx hfree).2.2.2
  · exact R.returnInterior ctx hfree

/-- The Return slot (verbatim wave-17 walk). -/
def returnCharge (R : Erdos260AbsorptionResidual) :
    ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx :=
  fun ctx => Class4ReturnPerSliceCharge.ofCountsOnly ctx (R.interiorAt ctx) (R.fibreSmall ctx)

/-- The absorption budget — `v3Budget` over the genuine route (verbatim shape). -/
def budget (R : Erdos260AbsorptionResidual) :
    ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx :=
  v3Budget R.towerCountV3 R.runChain R.returnCharge

/-- **The de-razored class-0 ledger row at EVERY context** (MASS form): at the 19
survivor pairs from the mass lane DIRECTLY; at non-survivor `q < 48` from the
in-tree closure; on `48 ≤ q < 96` from the band-free complement OR the mid mass
lane; on `96 ≤ q` from the certificate horn OR the big mass lane. -/
theorem hcap0Mass (R : Erdos260AbsorptionResidual) (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 0
      ≤ termChernoff (correctedAllPhases ctx).toClosurePhaseData := by
  have hcap : erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ)
      = termChernoff (correctedAllPhases ctx).toClosurePhaseData := by
    rw [termChernoff_correctedAll_eq, div_mul_eq_mul_div]
  rcases Nat.lt_or_ge (class1SlopeDatum ctx).q 48 with h48 | h48
  · by_cases hs : Class0DatumSurvivor ctx
    · rw [← hcap]
      exact (R.class0MassAbsorption ctx).1 hs
    · have hpin := class0Pinned_of_datum_not_survivor ctx h48 hs
      have hcheck := (class0Pinned_iff_windowCycleCheck ctx).mp hpin
      have hempty := (ofcClass0Fibre_empty_iff_windowCycleCheck ctx).mpr hcheck
      exact le_trans (tfaMass_le_card_mul_mult ctx (genuineChargeRoute ctx) 0)
        (tfaClass0Absorption_of_fibreEmpty ctx hempty)
  · rcases Nat.lt_or_ge (class1SlopeDatum ctx).q 96 with h96 | h96
    · by_cases hfree : Class0CycleDeepBandFree ctx
      · have hempty := ofcClass0Fibre_empty_of_deepBandFree ctx hfree
        exact le_trans (tfaMass_le_card_mul_mult ctx (genuineChargeRoute ctx) 0)
          (tfaClass0Absorption_of_fibreEmpty ctx hempty)
      · have hmeet := class0CycleMeetsShallow_of_not_deepBandFree ctx h96 hfree
        rw [← hcap]
        exact (R.class0MassAbsorption ctx).2.1 h48 h96 hmeet
    · cases (R.class0MassAbsorption ctx).2.2 h96 with
      | inl hcert =>
          obtain ⟨C, horder, hcheck'⟩ := hcert
          have hcheck := class0Tail_of_order_gt ctx C horder hcheck'
          have hempty := (ofcClass0Fibre_empty_iff_windowCycleCheck ctx).mpr hcheck
          exact le_trans (tfaMass_le_card_mul_mult ctx (genuineChargeRoute ctx) 0)
            (tfaClass0Absorption_of_fibreEmpty ctx hempty)
      | inr hmass =>
          rw [← hcap]
          exact hmass

/-- The corrected class-1 count-cap at EVERY context (verbatim wave-17 walk). -/
theorem hcap1 (R : Erdos260AbsorptionResidual) (ctx : ActualFailureContext) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ termCnl (correctedAllPhases ctx).toClosurePhaseData := by
  rw [termCnl_correctedAll_eq, ← div_mul_eq_mul_div]
  rcases Nat.eq_zero_or_pos ctx.n24CarryData.r with hr0 | hr1
  · have hcard : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card ≤ 1 :=
      class1Fibre_card_le_one_of_r_eq_zero ctx hr0
    have hcardR : ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        ≤ 1 := by exact_mod_cast hcard
    have hY0 : (0 : ℝ) ≤ ctx.n24CarryData.Y := le_of_lt (n24CarryData_Y_pos ctx)
    have hYlt : ctx.n24CarryData.Y
        < erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
      have h := Y_lt_termCnl_corrected R.budget ctx
      rwa [termCnl_corrected_eq R.budget ctx] at h
    calc ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
          * ctx.n24CarryData.Y
        ≤ 1 * ctx.n24CarryData.Y := mul_le_mul_of_nonneg_right hcardR hY0
      _ = ctx.n24CarryData.Y := one_mul _
      _ ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) :=
          le_of_lt hYlt
  · by_cases hreg : ∃ cv bv Tv : ℕ,
        ((class1SlopeDatum ctx).q, (class1SlopeDatum ctx).K₀, cv, bv, Tv)
            ∈ sreClass1ThresholdTable
          ∧ shellLadderDepth ctx ≤ Tv
    · obtain ⟨cv, bv, Tv, hmem, hL⟩ := hreg
      exact sreClass1Absorption_of_mem ctx hmem rfl rfl hL
    · exact R.class1CapAbsorption ctx hr1 hreg

/-- The corrected DensePack residue at the absorption budget (verbatim walk). -/
def densePackCorrected (R : Erdos260AbsorptionResidual) :
    DensePackCorrectedResidue R.budget :=
  (R.densePackUngated.toGatedClosure.toDatumSplit.toCycleSplit.toRegimeSplit R.budget).toCorrected

/-- The corrected class-3 ledger row at EVERY context (verbatim walk). -/
theorem hDensePackAll (R : Erdos260AbsorptionResidual) (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (R.budget ctx).route 3
      ≤ termDensePack (correctedAllPhases ctx).toClosurePhaseData :=
  le_trans (R.densePackCorrected.hDensePackField (fun _ => rfl) ctx)
    (tfaDensePack_frozen_le_correctedAll R.budget ctx)

/-- **The fully-corrected ctx-pinned P9 ledger from the wave-18 surface**: the
class-0 row from the MASS-shaped walk directly (`hcap0Mass`), all others as in
the wave-17 capstone. -/
def toFullyCorrectedLedger (R : Erdos260AbsorptionResidual) :
    FullyCorrectedP9LedgerResidual where
  budget := R.budget
  hChernoff := fun ctx => by
    show routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 0
        ≤ termChernoff (correctedAllPhases ctx).toClosurePhaseData
    exact R.hcap0Mass ctx
  hCnl := fun ctx => by
    show routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 1
        ≤ termCnl (correctedAllPhases ctx).toClosurePhaseData
    rw [routedClassMass_one_eq_card_mul_Y]
    exact R.hcap1 ctx
  hDensePack := fun ctx => R.hDensePackAll ctx
  hTRT := fun ctx => by
    rw [termTower_correctedAll_eq, termReturn_correctedAll_eq, termRun_correctedAll_eq]
    have h2 := (R.budget ctx).towerSlot
    have h4 := (R.budget ctx).returnSlot
    have h5 := (R.budget ctx).runSlot
    linarith
  hOldRes := fun ctx => by
    show routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 6 ≤ 0
    exact le_of_eq (genuineChargeRoute_routed6_zero ctx)

/-- The final statement from the wave-18 surface.  Composition only. -/
theorem toStatement (R : Erdos260AbsorptionResidual) : Erdos260Statement :=
  R.toFullyCorrectedLedger.toStatement

end Erdos260AbsorptionResidual

/-- **THE WAVE-18 ENDPOINT**: `Erdos260Statement` from the fully de-razored
absorption surface — the class-0 lanes demand only ROUTED MASS caps (the sum of
window excesses), never counts, never emptiness. -/
theorem erdos260_of_absorptionResidual (R : Erdos260AbsorptionResidual) :
    Erdos260Statement :=
  R.toStatement

/-- **The weakening witness wave 17 → wave 18 (never harder)**: every wave-17
endgame inhabitant yields a wave-18 absorption inhabitant — survivor count-cap
gives the mass cap through `tfaMass_le_card_mul_mult`; mid/big emptiness gives the
mass caps through `tfaClass0Absorption_of_fibreEmpty`.  One direction only; NO
converse is claimed (the converse is exactly the wave-18 de-razoring). -/
def absorptionResidual_of_endgameResidual (R : Erdos260EndgameResidual) :
    Erdos260AbsorptionResidual where
  towerEnumLow := R.towerEnumLow
  towerEnumTail := R.towerEnumTail
  runBand4Void := R.runBand4Void
  runNumericLow := R.runNumericLow
  runNumericTail := R.runNumericTail
  returnBand2Void := R.returnBand2Void
  returnGatesFree := R.returnGatesFree
  returnInterior := R.returnInterior
  densePackBand3Void := R.densePackBand3Void
  densePackCoverFree := R.densePackCoverFree
  densePackDensity := R.densePackDensity
  densePackInterior := R.densePackInterior
  class0MassAbsorption := fun ctx => by
    have hcap : erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ)
        = termChernoff (correctedAllPhases ctx).toClosurePhaseData := by
      rw [termChernoff_correctedAll_eq, div_mul_eq_mul_div]
    refine ⟨fun hs => ?_, fun h48 h96 hmeet => ?_, fun h96 => ?_⟩
    · exact le_trans (tfaMass_le_card_mul_mult ctx (genuineChargeRoute ctx) 0)
        ((R.class0Absorption ctx).1 hs)
    · rw [hcap]
      exact le_trans (tfaMass_le_card_mul_mult ctx (genuineChargeRoute ctx) 0)
        (tfaClass0Absorption_of_fibreEmpty ctx
          ((R.class0Absorption ctx).2.1 h48 h96 hmeet))
    · refine ((R.class0Absorption ctx).2.2 h96).imp_right fun hempty => ?_
      rw [hcap]
      exact le_trans (tfaMass_le_card_mul_mult ctx (genuineChargeRoute ctx) 0)
        (tfaClass0Absorption_of_fibreEmpty ctx hempty)
  class1CapAbsorption := R.class1CapAbsorption

/-- Nonempty transport from the wave-17 endgame surface (one direction — honest). -/
theorem nonempty_absorptionResidual_of_endgameResidual
    (h : Nonempty Erdos260EndgameResidual) :
    Nonempty Erdos260AbsorptionResidual :=
  h.elim fun R => ⟨absorptionResidual_of_endgameResidual R⟩

/-- Sanity commutation: the wave-17 surface reaches the statement through the
wave-18 absorption route as well. -/
theorem erdos260_of_endgameResidual_via_absorption (R : Erdos260EndgameResidual) :
    Erdos260Statement :=
  (absorptionResidual_of_endgameResidual R).toStatement

/-! ## Part 4.  Lever (d): top-band deviation-light interior closures

`returnInterior` / `densePackInterior` demand that no fibre member start sits in
the top band `[F+W-r-1, F+W)`.  Fibre members are HEAVY (`Y ≤ windowExcess`), and
at band `≤ 4` their excess is carried by deviation content inside their window —
all within the top-band reach `[F+W-r-1, F+W+r)`.  A top-band deviation budget
below `Y` therefore voids every heavy member there. -/

/-- The top-band deviation mass: the exit weights over the top-band reach
`[F+W-(r+1), F+W+r)` (length `2r+1` since `W ≥ r+1`). -/
def agcTopBandDev (ctx : ActualFailureContext) : ℕ :=
  ∑ j ∈ Finset.Ico (emF ctx + emW ctx - (ctx.n24CarryData.r + 1))
      (emF ctx + emW ctx + ctx.n24CarryData.r), emExitWeight ctx j

/-- A window's deviation content is bounded by any interval sum covering it. -/
theorem agc_devWindow_le_Ico (ctx : ActualFailureContext) {k lo hi : ℕ}
    (hlo : lo ≤ k) (hhi : k + ctx.n24CarryData.r < hi) :
    emDevWindow ctx k ≤ ∑ j ∈ Finset.Ico lo hi, emExitWeight ctx j := by
  unfold emDevWindow
  rw [show (∑ i ∈ Finset.range (ctx.n24CarryData.r + 1), emExitWeight ctx (k + i))
      = ∑ j ∈ (Finset.range (ctx.n24CarryData.r + 1)).image (fun i => k + i),
          emExitWeight ctx j from (Finset.sum_image (fun x _ y _ h => by omega)).symm]
  refine Finset.sum_le_sum_of_subset ?_
  intro j hj
  obtain ⟨i, hi2, rfl⟩ := Finset.mem_image.mp hj
  rw [Finset.mem_range] at hi2
  rw [Finset.mem_Ico]
  omega

/-- **The Return-interior closure from top-band deviation light** (per ctx): if
the top-band deviation mass is below the heaviness floor `Y`, NO class-4 member
can sit in the top band — `ReturnInteriorBody` holds outright. -/
theorem agcReturnInterior_of_topBandDevLight (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4)
    (hlight : (agcTopBandDev ctx : ℝ) < ctx.n24CarryData.Y) :
    ReturnInteriorBody ctx := by
  intro k hk
  by_contra hcon
  push Not at hcon
  have hks : k ∈ ctx.n24CarryData.starts :=
    (mem_highExcessStarts.mp (Finset.mem_filter.mp hk).1).1
  rw [cnlMulti_starts_eq_window, Finset.mem_Ico] at hks
  have hW1 := cnlMulti_r_add_one_le_width ctx
  have hY := Y_le_windowExcess_of_mem_routedFibre ctx.n24CarryData
    (genuineChargeRoute ctx) 4 hk
  have hdev := em_windowExcess_le_devWindow ctx hband k
  have hsub : emDevWindow ctx k ≤ agcTopBandDev ctx := by
    unfold agcTopBandDev
    refine agc_devWindow_le_Ico ctx ?_ ?_
    · unfold emF emW
      omega
    · unfold emF emW
      omega
  have hsubR : (emDevWindow ctx k : ℝ) ≤ (agcTopBandDev ctx : ℝ) := Nat.cast_le.mpr hsub
  linarith

/-- The Return-interior closure in the EXACT `returnInterior` field shape. -/
theorem agcReturnInteriorField_of_topBandDevLight
    (h : ∀ ctx : ActualFailureContext,
      fixedFamilyRecurrentBand ctx ≤ 4 ∧ (agcTopBandDev ctx : ℝ) < ctx.n24CarryData.Y) :
    ∀ ctx : ActualFailureContext, ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx :=
  fun ctx _ => agcReturnInterior_of_topBandDevLight ctx (h ctx).1 (h ctx).2

/-- **The DensePack-interior closure from top-band deviation light** (per ctx):
genuine densepack starts are heavy, so the same banding voids the top band. -/
theorem agcDensePackInterior_of_topBandDevLight (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4)
    (hlight : (agcTopBandDev ctx : ℝ) < ctx.n24CarryData.Y) :
    ∀ k ∈ genuineDensePackStarts ctx,
      k + ctx.n24CarryData.r + 1
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card := by
  intro k hk
  by_contra hcon
  push Not at hcon
  have hmem := (mem_genuineDensePackStarts ctx k).mp hk
  have hks : k ∈ ctx.n24CarryData.starts := (mem_highExcessStarts.mp hmem.1).1
  rw [cnlMulti_starts_eq_window, Finset.mem_Ico] at hks
  have hW1 := cnlMulti_r_add_one_le_width ctx
  have hY : ctx.n24CarryData.Y
      ≤ windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
          ctx.n24CarryData.T :=
    (mem_highExcessStarts.mp hmem.1).2
  have hdev := em_windowExcess_le_devWindow ctx hband k
  have hsub : emDevWindow ctx k ≤ agcTopBandDev ctx := by
    unfold agcTopBandDev
    refine agc_devWindow_le_Ico ctx ?_ ?_
    · unfold emF emW
      omega
    · unfold emF emW
      omega
  have hsubR : (emDevWindow ctx k : ℝ) ≤ (agcTopBandDev ctx : ℝ) := Nat.cast_le.mpr hsub
  linarith

/-- The DensePack-interior closure in the EXACT `densePackInterior` field shape. -/
theorem agcDensePackInteriorField_of_topBandDevLight
    (h : ∀ ctx : ActualFailureContext,
      fixedFamilyRecurrentBand ctx ≤ 4 ∧ (agcTopBandDev ctx : ℝ) < ctx.n24CarryData.Y) :
    ∀ ctx : ActualFailureContext,
      ¬ Class3TopBandCycleFree ctx →
      ((class1SlopeDatum ctx).q = 5 ∨ 13 ≤ (class1SlopeDatum ctx).q) →
      ¬ DensePackDatumClosed ctx →
      ∀ k ∈ genuineDensePackStarts ctx,
        k + ctx.n24CarryData.r + 1
          < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
              + (supportShell ctx.shell.d ctx.shell.X).card :=
  fun ctx _ _ _ => agcDensePackInterior_of_topBandDevLight ctx (h ctx).1 (h ctx).2

/-- **HONEST in-tree ceiling on the top-band deviation**: the rigidity gap cap
gives only `(2r+1)·(L+B+1)`, which EXCEEDS the heaviness floor `Y = L/64` — the
deviation-light hypothesis is a genuine new demand; no band-localized M.5 cap
exists in-tree. -/
theorem agcTopBandDev_le_cap (ctx : ActualFailureContext) :
    agcTopBandDev ctx
      ≤ (2 * ctx.n24CarryData.r + 1)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) := by
  unfold agcTopBandDev
  have hW1 := cnlMulti_r_add_one_le_width ctx
  calc ∑ j ∈ Finset.Ico (emF ctx + emW ctx - (ctx.n24CarryData.r + 1))
        (emF ctx + emW ctx + ctx.n24CarryData.r), emExitWeight ctx j
      ≤ ∑ _j ∈ Finset.Ico (emF ctx + emW ctx - (ctx.n24CarryData.r + 1))
          (emF ctx + emW ctx + ctx.n24CarryData.r),
          (shellLadderDepth ctx + carryB ctx.shell.Q + 1) := by
        refine Finset.sum_le_sum ?_
        intro j hj
        rw [Finset.mem_Ico] at hj
        refine le_trans (emExitWeight_le_hitGap ctx j) ?_
        refine n24_hitGap_le_reach ctx ?_
        have hj2 := hj.2
        unfold emF emW at hj2
        omega
    _ = (Finset.Ico (emF ctx + emW ctx - (ctx.n24CarryData.r + 1))
          (emF ctx + emW ctx + ctx.n24CarryData.r)).card
            * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (2 * ctx.n24CarryData.r + 1)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) := by
        refine Nat.mul_le_mul ?_ le_rfl
        rw [Nat.card_Ico]
        have hW2 : ctx.n24CarryData.r + 1 ≤ emW ctx := by
          unfold emW
          exact hW1
        omega

/-- **The spaced top-band POPULATION cap (unconditional at survivors)**: at most
`⌈(r+1)/c⌉ = (r+c)/c` class-0 members can sit in the top band — the lever-(d)
count side, with no deviation hypothesis. -/
theorem agcClass0TopBand_card_le (ctx : ActualFailureContext)
    (hsurv : Class0DatumSurvivor ctx) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).filter
        (fun k => emF ctx + emW ctx ≤ k + ctx.n24CarryData.r + 1)).card
      ≤ (ctx.n24CarryData.r + 1 + class0SurvivorPeriod (class1SlopeDatum ctx).q - 1)
          / class0SurvivorPeriod (class1SlopeDatum ctx).q := by
  have hc := tfaClass0SurvivorPeriod_pos (class1SlopeDatum ctx).q
  have hspace := ofcClass0Member_spacing_of_survivor ctx hsurv
  refine spaced_finset_card_le hc (by omega : 1 ≤ ctx.n24CarryData.r + 1) ?_ ?_
  · intro x hx z hz hlt
    exact hspace x (Finset.mem_filter.mp hx).1 z (Finset.mem_filter.mp hz).1 (le_of_lt hlt)
  · intro x hx z hz hlt
    have hxf := Finset.mem_filter.mp hx
    have hzf := Finset.mem_filter.mp hz
    have hzs : z ∈ ctx.n24CarryData.starts :=
      (mem_highExcessStarts.mp (Finset.mem_filter.mp hzf.1).1).1
    rw [cnlMulti_starts_eq_window, Finset.mem_Ico] at hzs
    have hxb := hxf.2
    unfold emF emW at hxb
    omega

/-! ## Part 5.  Lever (e): the cycle-count gate on band-2-free contexts

The fourth `ReturnGatesBody` disjunct demands a period `c`, a tiling count `t`
with `W ≤ t·c`, and `t·b₂ ≤ r+1` where `b₂` counts the band-2 residues of the
cycle.  Any certified `(c, b₂)` with the window regime `(W/c + 1)·b₂ ≤ r + 1`
closes the gate; at band-2 PINS `b₂ = c` and the regime is impossible —
consistent with the wave-17 voiding split. -/

/-- The cycle-count gate from any tiling witness `t`. -/
theorem agcReturnGatesUngated_of_cycleCount (ctx : ActualFailureContext)
    {c t : ℕ} (hc1 : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hWt : (supportShell ctx.shell.d ctx.shell.X).card ≤ t * c)
    (hcount : t * ((Finset.Icc 1 c).filter (fun j =>
        canonGap (class1SlopeDatum ctx).q
          (slopeOrbit (class1SlopeDatum ctx).q
            (class1SlopeDatum ctx).K₀ j) = 2)).card
      ≤ ctx.n24CarryData.r + 1) :
    ReturnGatesBodyUngated ctx :=
  Or.inr (Or.inr ⟨c, t, hc1, hper, hWt, hcount⟩)

/-- The cycle-count gate with the canonical ceiling witness `t = W/c + 1`: the
numeric regime `(W/c + 1)·b₂ ≤ r + 1` alone closes `ReturnGatesBodyUngated`. -/
theorem agcReturnGatesUngated_of_cycleCount_ceil (ctx : ActualFailureContext)
    {c : ℕ} (hc1 : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hcount : ((supportShell ctx.shell.d ctx.shell.X).card / c + 1)
        * ((Finset.Icc 1 c).filter (fun j =>
            canonGap (class1SlopeDatum ctx).q
              (slopeOrbit (class1SlopeDatum ctx).q
                (class1SlopeDatum ctx).K₀ j) = 2)).card
      ≤ ctx.n24CarryData.r + 1) :
    ReturnGatesBodyUngated ctx := by
  refine agcReturnGatesUngated_of_cycleCount ctx hc1 hper ?_ hcount
  exact le_of_lt ((Nat.div_lt_iff_lt_mul hc1).mp (Nat.lt_succ_self _))

/-- The cycle-count closure in the EXACT `returnGatesFree` field shape: a per-ctx
certified period with the window regime closes the whole pin-free count gate. -/
theorem agcReturnGatesFreeField_of_cycleCount
    (h : ∀ ctx : ActualFailureContext, ∃ c, 1 ≤ c ∧
      (∀ m, 1 ≤ m →
        slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
          = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m) ∧
      ((supportShell ctx.shell.d ctx.shell.X).card / c + 1)
          * ((Finset.Icc 1 c).filter (fun j =>
              canonGap (class1SlopeDatum ctx).q
                (slopeOrbit (class1SlopeDatum ctx).q
                  (class1SlopeDatum ctx).K₀ j) = 2)).card
        ≤ ctx.n24CarryData.r + 1) :
    ∀ ctx : ActualFailureContext, ¬ OrbitBandPinned ctx 2 →
      ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
      2 * (129 * shellLadderDepth ctx + 64)
        ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card
              + ctx.n24CarryData.r)
            * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
      ReturnGatesBodyUngated ctx := by
  intro ctx _ _ _ _
  obtain ⟨c, hc1, hper, hcount⟩ := h ctx
  exact agcReturnGatesUngated_of_cycleCount_ceil ctx hc1 hper hcount

/-! ## Part 6.  Honest machine-readable status -/

/-- Machine-readable, honest status of the wave-18 absorption-gate closure pass. -/
def absorptionGateClosureStatus : List String :=
  [ "BAND PINS (PROVED, agcSurvivorBand_le_four): all nineteen class-0 survivor " ++
      "pairs read recurrent band canonGap q (slopeOrbit q K0 1) in {1,2,3} " ++
      "(values: 1 at fifteen pairs; 2 at (25,2),(45,1),(45,2),(45,4); 3 at " ++
      "(27,1),(27,4)) - the ExitMassTranscription deviation calculus " ++
      "(em_windowExcess_le_devWindow, em_exitMass_lower_of_band) applies at " ++
      "EVERY survivor context with no fixed-family hypothesis.",
    "LEVER (b) EXACT (PROVED, agc_spaced_windowSum_le): c-spaced members' " ++
      "windows overlap-count each deviating gap at most ceil((r+1)/c) = (r+c)/c " ++
      "times - blocks of length c partitioned range(r+1), within a block the " ++
      "shifted copies of a c-spaced set are pairwise disjoint.  Consequence " ++
      "(agcClass0Mass_le_overlap_devBudget): mass0 <= ((r+c)/c)*emExitMass at " ++
      "every survivor pair.  HONEST COMPARISON: against the in-tree ceiling " ++
      "emExitMass <= (W+r)(L+B+1) this gives ((r+c)/c)(W+r)(L+B+1) vs the " ++
      "count route ceil(W/c)(r+1)(L+B+1) - ratio (W+r)/W <= 2; the hoped " ++
      "window/c gain does NOT materialize (the count route already consumes " ++
      "the spacing).  The gain is real only against the deviation mass itself.",
    "LEVER (a) VERDICT (PROVED NEGATIVE): the in-tree deviation budget is a " ++
      "FLOOR, not a small ceiling.  At every survivor pair X <= 2*emExitMass " ++
      "(agcSurvivor_exitMass_floor - the relocated Lemma 21.1 pressure floor " ++
      "fires because the bands are <= 4), so the total deviation over the " ++
      "shell window is >= X/2 = (768/1536)*X while the corrected cap is " ++
      "(31/1536)*X - factor 768/31 ~ 24.8 (agcCap_lt_devFloor).  The sum-route " ++
      "gates are REFUTED: 1536*((r+c)/c)*emExitMass <= 31*X is FALSE at every " ++
      "survivor ctx (agcClass0DevGate_refuted); 1536*(r+1)*emExitMass <= 31*X " ++
      "is FALSE wherever band <= 4 (agcGenericDevGate_refuted, killing the " ++
      "class-3 width analogue too).  The brief's hoped D_total <= c0*X with " ++
      "c0 < 31/1536 = 0.0202 is impossible in-tree: c0 >= 1/2.  NO " ++
      "unconditional class-0/class-3 closure exists via the deviation budget; " ++
      "the count-route obstruction tfaClass0Gate_not_from_failureCap and this " ++
      "sum-route refutation together pin the class-0 gate as a genuine " ++
      "narrow-support condition from BOTH directions.  The conditional gate " ++
      "shapes are recorded (agcClass0MassAbsorption_of_devGate, " ++
      "agcClass0MassLane_of_devGate) with their unsatisfiability proved " ++
      "alongside - shape only, the refutation is the substantive result.",
    "LEVER (c) RAZOR VERDICT (POSITIVE - PROVED, THE WAVE-18 SURFACE): the " ++
      "mid/big emptiness language IS a razor artifact relative to the " ++
      "corrected ledger.  Erdos260AbsorptionResidual demands only MASS caps " ++
      "mass0 <= (31/1536)*X on ALL THREE class-0 lanes (survivor count-cap -> " ++
      "mass, mid emptiness -> mass, big emptiness horn -> mass; certificate " ++
      "horn kept) and still proves Erdos260Statement " ++
      "(erdos260_of_absorptionResidual) - the 48<=q<96 deep-band-free " ++
      "complement closes via Class0CycleDeepBandFree, the 96<=q certificate " ++
      "horn via class0Tail_of_order_gt, non-survivor q<48 via " ++
      "class0Pinned_of_datum_not_survivor, exactly as in wave 17.  Weakening " ++
      "witness absorptionResidual_of_endgameResidual (wave 17 -> wave 18); NO " ++
      "converse claimed.  CAVEAT (honest): per-LANE the emptiness demand " ++
      "remains EQUIVALENT to the windowed check " ++
      "(ofcClass0Fibre_empty_iff_windowCycleCheck) - the de-razoring is of the " ++
      "SURFACE (what the ledger needs), not a new closure of the lanes.",
    "LEVER (d) (PROVED, conditional): top-band deviation-light closes both " ++
      "interior fields at their EXACT types - if the deviation mass on the " ++
      "top-band reach [F+W-r-1, F+W+r) is < Y = L/64 then no heavy member " ++
      "sits in the top band (agcReturnInterior_of_topBandDevLight + field " ++
      "form agcReturnInteriorField_of_topBandDevLight; " ++
      "agcDensePackInterior_of_topBandDevLight + field form).  Unconditional " ++
      "POPULATION cap at survivors: at most (r+c)/c class-0 members in the " ++
      "top band (agcClass0TopBand_card_le).  HONEST: the only in-tree ceiling " ++
      "on the top-band deviation is (2r+1)(L+B+1) (agcTopBandDev_le_cap), " ++
      "which exceeds Y - no band-localized M.5 cap exists in-tree, so the " ++
      "light hypothesis is a genuine demand, not a theorem.",
    "LEVER (e) (PROVED, conditional): the cycle-count gate closes " ++
      "ReturnGatesBodyUngated from any certified period c with the window " ++
      "regime (W/c + 1)*b2 <= r + 1, b2 = #band-2 residues of the cycle " ++
      "(agcReturnGatesUngated_of_cycleCount, _ceil; exact returnGatesFree " ++
      "field shape agcReturnGatesFreeField_of_cycleCount).  Regime reading: " ++
      "W <~ (r+1)*c/b2; at band-2 pins b2 = c making it impossible " ++
      "(consistent with the wave-17 voiding split); live only on " ++
      "band-2-light cycles in narrow windows.  No per-pair b2 table added " ++
      "this wave - the gate is generic over certificates; honest residual: " ++
      "per-pair instantiation needs the orbit period certificates plus the " ++
      "W-regime, conditional per context.",
    "PER-FIELD VERDICTS: class0Absorption - DE-RAZORED (mass shape, all " ++
      "three lanes, endpoint proved); unconditional closure OPEN (count gate " ++
      "narrow-support, sum gate refuted).  returnGatesFree - conditional " ++
      "cycle-count closure (lever e); OPEN in general.  returnInterior / " ++
      "densePackInterior - conditional top-band-light closures (lever d); " ++
      "OPEN in general.  densePackCoverFree / densePackDensity - no new " ++
      "closure (the sum route's class-3 width gate is refuted by lever a); " ++
      "OPEN.  class1CapAbsorption / tower / run lanes - untouched.",
    "HYGIENE: additive only - ONE new module " ++
      "(Erdos260.AbsorptionGateClosure); no existing file edited; no sorry / " ++
      "admit / new axiom / native_decide; every key declaration passes " ++
      "#print axioms within [propext, Classical.choice, Quot.sound]." ]

/-- The status ledger is non-empty (honest, non-vacuous). -/
theorem absorptionGateClosureStatus_nonempty :
    absorptionGateClosureStatus ≠ [] := by
  simp [absorptionGateClosureStatus]

/-! ## Part 7.  Axiom-cleanliness audit
Every key declaration; expected axioms `[propext, Classical.choice, Quot.sound]`
or fewer. -/

#print axioms agcBandPin
#print axioms agcBandPin_le_four
#print axioms agcSurvivorBand_le_four
#print axioms agcX_ge_one
#print axioms agc_spaced_windowSum_le
#print axioms agcClassMass_le_sum_devWindow
#print axioms agcClass0DevSum_le_overlap
#print axioms agcClass0Mass_le_overlap_devBudget
#print axioms agcClassMass_le_devBudget
#print axioms agcClass0MassAbsorption_of_devGate
#print axioms agcSurvivor_exitMass_floor
#print axioms agcCap_lt_devFloor
#print axioms agcClass0DevGate_refuted
#print axioms agcGenericDevGate_refuted
#print axioms agcClass0MassLane_of_devGate
#print axioms Erdos260AbsorptionResidual.returnGatesField
#print axioms Erdos260AbsorptionResidual.densePackCoverField
#print axioms Erdos260AbsorptionResidual.densePackUngated
#print axioms Erdos260AbsorptionResidual.towerEnum
#print axioms Erdos260AbsorptionResidual.towerCountV3
#print axioms Erdos260AbsorptionResidual.runNumeric
#print axioms Erdos260AbsorptionResidual.runCore
#print axioms Erdos260AbsorptionResidual.runChain
#print axioms Erdos260AbsorptionResidual.returnGatesCycle
#print axioms Erdos260AbsorptionResidual.fibreSmall
#print axioms Erdos260AbsorptionResidual.interiorAt
#print axioms Erdos260AbsorptionResidual.returnCharge
#print axioms Erdos260AbsorptionResidual.budget
#print axioms Erdos260AbsorptionResidual.hcap0Mass
#print axioms Erdos260AbsorptionResidual.hcap1
#print axioms Erdos260AbsorptionResidual.densePackCorrected
#print axioms Erdos260AbsorptionResidual.hDensePackAll
#print axioms Erdos260AbsorptionResidual.toFullyCorrectedLedger
#print axioms Erdos260AbsorptionResidual.toStatement
#print axioms erdos260_of_absorptionResidual
#print axioms absorptionResidual_of_endgameResidual
#print axioms nonempty_absorptionResidual_of_endgameResidual
#print axioms erdos260_of_endgameResidual_via_absorption
#print axioms agcTopBandDev_le_cap
#print axioms agc_devWindow_le_Ico
#print axioms agcReturnInterior_of_topBandDevLight
#print axioms agcReturnInteriorField_of_topBandDevLight
#print axioms agcDensePackInterior_of_topBandDevLight
#print axioms agcDensePackInteriorField_of_topBandDevLight
#print axioms agcClass0TopBand_card_le
#print axioms agcReturnGatesUngated_of_cycleCount
#print axioms agcReturnGatesUngated_of_cycleCount_ceil
#print axioms agcReturnGatesFreeField_of_cycleCount
#print axioms absorptionGateClosureStatus_nonempty

end

end Erdos260
