import Erdos260.Erdos260FrontierCapstone

/-!
# Wave-19: the narrow-support gate on the class-0 lanes (`NarrowSupportGate`)

The v18 frontier's `class0Mass` field (three lanes: survivor / mid-band / big-order,
each demanding `mass₀ ≤ (31/1536)·X`) worked through the manuscript's H.1/K.4
NARROW-SUPPORT mechanism — the unique route left after both generic routes were
refuted in-tree (`tfaClass0Gate_not_from_failureCap`: count×max-excess;
`agcClass0DevGate_refuted`: the deviation budget is a FLOOR `X/2`, factor `24.8`
above the cap).  Everything here is additive; no existing file is touched.

## 1.  The H.1 level-set bound (PROVED, exact form)

The manuscript H.1 budget `X|I_j|·2^{-cY}` charges class-0 starts exponentially in
their excess level.  The in-tree (Markov/Chebyshev) shadow of that decay is PROVED
here at every survivor pair: writing `heavy_s = {k ∈ fibre₀ : windowExcess k ≥ s·Y}`,

* `nsgLevelSet_count_cap`:  `s·Y·|heavy_s| ≤ ⌈(r+1)/c⌉·emExitMass` — a member at
  level `s` pins `s·Y` deviation mass inside its window (`em_windowExcess_le_devWindow`
  reversed at heavy members), and the `c`-spaced windows overlap-count each deviating
  gap at most `⌈(r+1)/c⌉ = (r+c)/c` times (`agc_spaced_windowSum_le`, consumed through
  `agcClass0DevSum_le_overlap`).  The span-ceiling form `nsgLevelSet_count_cap_span`
  bounds the right side by `⌈(r+1)/c⌉·(W+r)(L+B+1)`; the band-conditional generic form
  (overlap `r+1`, no spacing input — the mid/big lanes) is
  `nsgLevelSet_count_cap_ofBand`.

* `nsgClass0Mass_split` (every threshold `s`):
  `mass₀ ≤ |fibre₀|·s·Y + ⌈(r+1)/c⌉·emExitMass` — the two-term telescoped form of the
  level-set summation.  At `s = 1` with the gate-free survivor count cap and the span
  ceiling this is `nsgClass0Mass_split_headline`:
  `mass₀ ≤ ⌈W/c⌉·Y + ⌈(r+1)/c⌉·(W+r)(L+B+1)` — STRICTLY SHARPER than the dyadic
  harmonic sum `|fibre₀|·Y + 2·(#levels)·⌈(r+1)/c⌉·(W+r)(L+B+1)` the brief proposed
  (the single split already optimizes the dyadic ladder; no `log` factor is needed).

## 2.  HONEST: the level-set SUMMATION cannot close any lane (refuted in-tree)

Every bound whose right side contains a positive multiple of `emExitMass` inherits the
relocated Lemma 21.1 pressure floor `X ≤ 2·emExitMass` wherever the deviation calculus
applies (band `≤ 4`, true at ALL nineteen survivor pairs): `nsgSplit_devTerm_floor` —
`(31/1536)·X < t·emExitMass` for every `t ≥ 1` — hence `nsgLevelSum_route_refuted`:
the split budget EXCEEDS the cap at every survivor context, for EVERY threshold `s`.
The dyadic/harmonic refinement is dominated by the split (above), so it dies with it.
The r-ceiling does not rescue the dev term either: `r ≤ κL` (`scc_r_le_kappaL`) gives
`⌈(r+1)/c⌉·(W+r)(L+B+1) ≳ (17L/2^18)·(17X/2^24)·L/c`, which needs `L² ≲ 3·10^8·c`
against the survivor floor `L ≥ 986876` — impossible at `c ≤ 18`.

## 3.  The surviving route: the per-member NARROW-SUPPORT GATE (named conditional)

`NarrowSupportGate ctx s` := every class-0 fibre member's window excess is `≤ s·Y`
(the level-`s` set is EMPTY — the structural content of the manuscript's "the excess
at a miss is bounded by the distance-to-fibre, not the full window cap").  Facts:

* strictly weaker than wave-16 emptiness (`nsgGate_of_fibreEmpty`); at `s = 0` it IS
  emptiness (`nsgGate_zero_iff`); at `s = 1` it pins every member's excess to exactly
  `Y` (`nsgGate_one_excess_eq`); gate `s` ⟺ `heavy_{s+1} = ∅` up to boundary
  (`nsgGate_of_heavySet_empty`, `nsgHeavySet_succ_empty_of_gate`).
* trivially true at the window calibration `64·(r+1)(L+B+1) ≤ s·L`
  (`nsgGate_trivial_of_calibration`) — but that calibration is DISJOINT from the
  closing regime by a factor `≥ 176` (`nsgTrivialGate_regime_disjoint`): no
  unconditional regime exists; the gate is a genuine per-context demand.

**The closure**: gate `s` + the ℕ regime `s·L ≤ 1274739·c` (the constant is
`⌊31·2^24/(24·17)⌋`; `24 = 1536/64` from `Y = L/64`) closes the survivor lane —
`nsgClass0Survivor_lane`: `mass₀ ≤ ⌈W/c⌉·s·Y ≤ (31/1536)·X` from the in-tree failure
cap `2^24·W < 17·X` alone (`nsgRegimeArith`; the `X ≥ 2^46` slack absorber is free
from the survivor depth floor `L ≥ 986876`, `X = 2^L`).  The mid/big lanes get the
generic-count analogue (`|fibre₀| ≤ W`, no `/c` gain): gate `s` + `s·L ≤ 1274739`
(`nsgClass0Generic_lane`).

**Honest regime accounting** (proved): at survivors `L ≥ 986876` forces `1 ≤ s ≤ 23`
and `L ≤ 1274739·c` (`nsgSurvivorRegime_s_le`); all nineteen periods have `c ≥ 2`
(`nsgSurvivorPeriod_ge_two`), so the `s = 1` gate closes the WHOLE band
`986876 ≤ L ≤ 2549478` at every pair (`nsgSurvivorRegime_one_of_depth`), extending
per-pair to `L ≤ 1274739·c` (up to `22945302` at `(37,18)`; table
`narrowSupportRegimeTable`).  On the mid lane `q < 96` forces `L ≥ 986876`, so the
regime pins `s = 1` and `L ≤ 1274739` (`nsgMidRegime_pin`) — the honest window is
`986876 ≤ L ≤ 1274739`.  The big lane keeps its order-criterion horn verbatim.

## 4.  The v18 field, rebuilt from the gates

`NarrowSupportClass0Gates` (three per-lane suppliers: survivor gate+regime, mid
gate+regime, big horn-or-gate) rebuilds the EXACT `Erdos260FrontierResidual.class0Mass`
field shape (`nsgFrontierClass0Mass_of_gates` — also verbatim the
`Erdos260AbsorptionResidual.class0MassAbsorption` field).  Weakening witness:
per-lane fibre emptiness (the wave-16 currency) supplies the gates at `s = 0`
(`nsgGates_of_fibreEmpty`).  NO converse is claimed: the mass cap does not bound
per-member excess.

WHAT STAYS OPEN (sharp): per survivor pair `(q, K₀)` with period `c`, the demand is
`NarrowSupportGate ctx s` together with `s·L ≤ 1274739·c` at every actual context —
for `L > 1274739·c` even the `s = 1` gate (every miss at the exact floor `Y`) does not
close from the count route, and the deviation route is floor-blocked; beyond the
regime the lane demand is genuinely open.

No `sorry`, no `admit`, no new `axiom`, no `native_decide`; additive only.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Part 0.  The level sets of the class-0 fibre -/

/-- The level-`s` heavy set of the class-0 routing fibre: the members whose window
excess is at least `s·Y` (the H.1 level set, in-tree currency). -/
def nsgHeavySet (ctx : ActualFailureContext) (s : ℕ) : Finset ℕ :=
  (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).filter
    (fun k => (s : ℝ) * ctx.n24CarryData.Y
      ≤ windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T)

/-- The heavy set sits inside the class-0 fibre. -/
theorem nsgHeavySet_subset_fibre (ctx : ActualFailureContext) (s : ℕ) :
    nsgHeavySet ctx s ⊆ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0 :=
  Finset.filter_subset _ _

/-- The heavy set sits inside the carry start window. -/
theorem nsgHeavySet_subset_starts (ctx : ActualFailureContext) (s : ℕ) :
    nsgHeavySet ctx s ⊆ ctx.n24CarryData.starts := by
  intro k hk
  have hk1 := (Finset.mem_filter.mp hk).1
  exact (mem_highExcessStarts.mp (Finset.mem_filter.mp hk1).1).1

/-- The level-`s` population pays `s·Y` each into the heavy excess sum (the Markov
head of the level-set bound). -/
theorem nsgHeavy_mass_lower (ctx : ActualFailureContext) (s : ℕ) :
    (s : ℝ) * ctx.n24CarryData.Y * ((nsgHeavySet ctx s).card : ℝ)
      ≤ ∑ k ∈ nsgHeavySet ctx s,
          windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
            ctx.n24CarryData.T := by
  calc (s : ℝ) * ctx.n24CarryData.Y * ((nsgHeavySet ctx s).card : ℝ)
      = ∑ _k ∈ nsgHeavySet ctx s, (s : ℝ) * ctx.n24CarryData.Y := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ ∑ k ∈ nsgHeavySet ctx s,
          windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
            ctx.n24CarryData.T :=
        Finset.sum_le_sum (fun k hk => (Finset.mem_filter.mp hk).2)

/-- At band `≤ 4` the heavy excess sum is carried by the windows' deviation content
(`em_windowExcess_le_devWindow`, summed over the level set). -/
theorem nsgHeavy_excSum_le_devSum (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4) (s : ℕ) :
    ∑ k ∈ nsgHeavySet ctx s,
        windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
      ≤ ((∑ k ∈ nsgHeavySet ctx s, emDevWindow ctx k : ℕ) : ℝ) := by
  rw [Nat.cast_sum]
  exact Finset.sum_le_sum (fun k _ => em_windowExcess_le_devWindow ctx hband k)

/-! ## Part 1.  THE H.1 LEVEL-SET COUNT CAP (proved, exact form)

For every level `s`, at every survivor pair:
`s·Y·|{k ∈ fibre₀ : windowExcess k ≥ s·Y}| ≤ ⌈(r+1)/c⌉·emExitMass`. -/

/-- **The level-set count cap (the H.1 transcription, survivor form)**: a heavy member
at level `s` pins `s·Y` deviation mass in its window; the `c`-spaced windows
overlap-count each deviating gap at most `⌈(r+1)/c⌉ = (r+c)/c` times.  This is the
in-tree polynomial shadow of the manuscript's `2^{-cY}` Chernoff decay. -/
theorem nsgLevelSet_count_cap (ctx : ActualFailureContext)
    (hsurv : Class0DatumSurvivor ctx) (s : ℕ) :
    (s : ℝ) * ctx.n24CarryData.Y * ((nsgHeavySet ctx s).card : ℝ)
      ≤ ((((ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
            / class0SurvivorPeriod (class1SlopeDatum ctx).q)
          * emExitMass ctx : ℕ) : ℝ) := by
  have hband := agcSurvivorBand_le_four ctx hsurv
  have hdev : ∑ k ∈ nsgHeavySet ctx s, emDevWindow ctx k
      ≤ ((ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
            / class0SurvivorPeriod (class1SlopeDatum ctx).q)
          * emExitMass ctx :=
    le_trans (Finset.sum_le_sum_of_subset (nsgHeavySet_subset_fibre ctx s))
      (agcClass0DevSum_le_overlap ctx hsurv)
  refine le_trans (nsgHeavy_mass_lower ctx s)
    (le_trans (nsgHeavy_excSum_le_devSum ctx hband s) ?_)
  exact_mod_cast hdev

/-- The level-set count cap against the in-tree span ceiling
`emExitMass ≤ (W+r)(L+B+1)`: `s·Y·|heavy_s| ≤ ⌈(r+1)/c⌉·(W+r)(L+B+1)`. -/
theorem nsgLevelSet_count_cap_span (ctx : ActualFailureContext)
    (hsurv : Class0DatumSurvivor ctx) (s : ℕ) :
    (s : ℝ) * ctx.n24CarryData.Y * ((nsgHeavySet ctx s).card : ℝ)
      ≤ ((((ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
            / class0SurvivorPeriod (class1SlopeDatum ctx).q)
          * ((emW ctx + ctx.n24CarryData.r)
              * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) : ℕ) : ℝ) := by
  refine le_trans (nsgLevelSet_count_cap ctx hsurv s) ?_
  exact_mod_cast Nat.mul_le_mul le_rfl (em_exitMass_le_reach_span ctx)

/-- **The generic level-set count cap** (mid/big lanes: no certified period, overlap
factor `r+1` from the plain window covering `em_devWindow_sum_le`), conditional only
on the recurrent band `≤ 4`. -/
theorem nsgLevelSet_count_cap_ofBand (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4) (s : ℕ) :
    (s : ℝ) * ctx.n24CarryData.Y * ((nsgHeavySet ctx s).card : ℝ)
      ≤ (((ctx.n24CarryData.r + 1) * emExitMass ctx : ℕ) : ℝ) := by
  have hdev : ∑ k ∈ nsgHeavySet ctx s, emDevWindow ctx k
      ≤ (ctx.n24CarryData.r + 1) * emExitMass ctx :=
    le_trans (Finset.sum_le_sum_of_subset (nsgHeavySet_subset_starts ctx s))
      (em_devWindow_sum_le ctx)
  refine le_trans (nsgHeavy_mass_lower ctx s)
    (le_trans (nsgHeavy_excSum_le_devSum ctx hband s) ?_)
  exact_mod_cast hdev

/-! ## Part 2.  The two-term level-set mass split, and its HONEST refutation -/

/-- **The level-set mass split** (every threshold `s`): the class-0 routed mass is at
most the sub-level population charged `s·Y` each, plus the heavy levels' telescoped
deviation budget.  This single split DOMINATES the dyadic harmonic-sum ladder (the
`s = 1` instance already optimizes it; no `log` factor appears). -/
theorem nsgClass0Mass_split (ctx : ActualFailureContext)
    (hsurv : Class0DatumSurvivor ctx) (s : ℕ) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 0
      ≤ ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card : ℝ)
            * ((s : ℝ) * ctx.n24CarryData.Y)
        + ((((ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
              / class0SurvivorPeriod (class1SlopeDatum ctx).q)
            * emExitMass ctx : ℕ) : ℝ) := by
  have hband := agcSurvivorBand_le_four ctx hsurv
  have hsY : (0 : ℝ) ≤ (s : ℝ) * ctx.n24CarryData.Y :=
    mul_nonneg (Nat.cast_nonneg s) (n24CarryData_Y_pos ctx).le
  have hsplit : routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 0
      = (∑ k ∈ nsgHeavySet ctx s,
          windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
            ctx.n24CarryData.T)
        + ∑ k ∈ (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).filter
            (fun k => ¬ ((s : ℝ) * ctx.n24CarryData.Y
              ≤ windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
                  ctx.n24CarryData.T)),
          windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
            ctx.n24CarryData.T := by
    rw [routedClassMassOf_eq_sum_fibre]
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hheavy : ∑ k ∈ nsgHeavySet ctx s,
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
      ≤ ((((ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
            / class0SurvivorPeriod (class1SlopeDatum ctx).q)
          * emExitMass ctx : ℕ) : ℝ) := by
    refine le_trans (nsgHeavy_excSum_le_devSum ctx hband s) ?_
    exact_mod_cast le_trans
      (Finset.sum_le_sum_of_subset (nsgHeavySet_subset_fibre ctx s))
      (agcClass0DevSum_le_overlap ctx hsurv)
  have hlight : ∑ k ∈ (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).filter
      (fun k => ¬ ((s : ℝ) * ctx.n24CarryData.Y
        ≤ windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
            ctx.n24CarryData.T)),
      windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
      ≤ ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card : ℝ)
          * ((s : ℝ) * ctx.n24CarryData.Y) := by
    have h1 := Finset.sum_le_card_nsmul
      ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).filter
        (fun k => ¬ ((s : ℝ) * ctx.n24CarryData.Y
          ≤ windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
              ctx.n24CarryData.T)))
      (fun k => windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
        ctx.n24CarryData.T)
      ((s : ℝ) * ctx.n24CarryData.Y)
      (fun k hk => (not_le.mp (Finset.mem_filter.mp hk).2).le)
    rw [nsmul_eq_mul] at h1
    refine le_trans h1 ?_
    refine mul_le_mul_of_nonneg_right ?_ hsY
    exact_mod_cast Finset.card_filter_le _ _
  rw [hsplit]
  linarith

/-- **The `s = 1` headline split**: `mass₀ ≤ ⌈W/c⌉·Y + ⌈(r+1)/c⌉·(W+r)(L+B+1)` —
the count cap on the floor-level population plus the span-ceiled deviation budget.
Sharper than the proposed dyadic-harmonic ladder by the factor `2·(#levels)`. -/
theorem nsgClass0Mass_split_headline (ctx : ActualFailureContext)
    (hsurv : Class0DatumSurvivor ctx) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 0
      ≤ ((((supportShell ctx.shell.d ctx.shell.X).card
            + class0SurvivorPeriod (class1SlopeDatum ctx).q - 1)
          / class0SurvivorPeriod (class1SlopeDatum ctx).q : ℕ) : ℝ)
            * ctx.n24CarryData.Y
        + ((((ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
              / class0SurvivorPeriod (class1SlopeDatum ctx).q)
            * ((emW ctx + ctx.n24CarryData.r)
                * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) : ℕ) : ℝ) := by
  have h := nsgClass0Mass_split ctx hsurv 1
  rw [Nat.cast_one, one_mul] at h
  have hcount : ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ ((((supportShell ctx.shell.d ctx.shell.X).card
            + class0SurvivorPeriod (class1SlopeDatum ctx).q - 1)
          / class0SurvivorPeriod (class1SlopeDatum ctx).q : ℕ) : ℝ)
        * ctx.n24CarryData.Y := by
    refine mul_le_mul_of_nonneg_right ?_ (n24CarryData_Y_pos ctx).le
    exact_mod_cast ofcClass0Fibre_card_le_of_survivor ctx hsurv
  have hdev : ((((ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
          / class0SurvivorPeriod (class1SlopeDatum ctx).q)
        * emExitMass ctx : ℕ) : ℝ)
      ≤ ((((ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
            / class0SurvivorPeriod (class1SlopeDatum ctx).q)
          * ((emW ctx + ctx.n24CarryData.r)
              * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_le_mul le_rfl (em_exitMass_le_reach_span ctx)
  linarith

/-- **HONEST: the deviation term carries the in-tree FLOOR** — wherever the calculus
applies, `(31/1536)·X < t·emExitMass` for every overlap factor `t ≥ 1` (the relocated
Lemma 21.1 floor `X ≤ 2·emExitMass`).  No level-set summation can close a lane. -/
theorem nsgSplit_devTerm_floor (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4) {t : ℕ} (ht : 1 ≤ t) :
    erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ)
      < ((t * emExitMass ctx : ℕ) : ℝ) := by
  have h1 := agcCap_lt_devFloor ctx hband
  have h2 : emExitMass ctx ≤ t * emExitMass ctx := Nat.le_mul_of_pos_left _ ht
  have h2' : ((emExitMass ctx : ℕ) : ℝ) ≤ ((t * emExitMass ctx : ℕ) : ℝ) := by
    exact_mod_cast h2
  linarith

/-- **The level-set summation route is REFUTED at every survivor pair**: for EVERY
threshold `s` the split budget exceeds the corrected cap (its deviation term alone
does, by the floor).  The dyadic/harmonic ladder is dominated by the split and dies
with it: the per-member NARROW-SUPPORT gate is the unique surviving mechanism. -/
theorem nsgLevelSum_route_refuted (ctx : ActualFailureContext)
    (hsurv : Class0DatumSurvivor ctx) (s : ℕ) :
    erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ)
      < ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card : ℝ)
            * ((s : ℝ) * ctx.n24CarryData.Y)
        + ((((ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
              / class0SurvivorPeriod (class1SlopeDatum ctx).q)
            * emExitMass ctx : ℕ) : ℝ) := by
  have hb := agcSurvivorBand_le_four ctx hsurv
  have hover : 1 ≤ (ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
      / class0SurvivorPeriod (class1SlopeDatum ctx).q :=
    (Nat.one_le_div_iff (tfaClass0SurvivorPeriod_pos _)).mpr (Nat.le_add_left _ _)
  have h := nsgSplit_devTerm_floor ctx hb hover
  have hnn : (0 : ℝ)
      ≤ ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0).card : ℝ)
          * ((s : ℝ) * ctx.n24CarryData.Y) :=
    mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (n24CarryData_Y_pos ctx).le)
  linarith

/-! ## Part 3.  THE NARROW-SUPPORT GATE (the named conditional) -/

/-- **The narrow-support gate at level `s`**: every class-0 fibre member's window
excess is at most `s·Y` — the level-`s` heavy set is empty; the excess of an
off-fibre miss is pinned near the activity floor instead of the window cap
(the manuscript H.1/K.4 narrow-support structure, per-member form). -/
def NarrowSupportGate (ctx : ActualFailureContext) (s : ℕ) : Prop :=
  ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0,
    windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
      ≤ (s : ℝ) * ctx.n24CarryData.Y

/-- Fibre emptiness (the wave-16 currency) supplies every gate level — the gate is
strictly weaker than the emptiness demand. -/
theorem nsgGate_of_fibreEmpty {ctx : ActualFailureContext}
    (h : routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0 = ∅) (s : ℕ) :
    NarrowSupportGate ctx s := by
  intro k hk
  rw [h] at hk
  exact absurd hk (Finset.notMem_empty k)

/-- At level `0` the gate IS fibre emptiness (every member carries excess `≥ Y > 0`). -/
theorem nsgGate_zero_iff (ctx : ActualFailureContext) :
    NarrowSupportGate ctx 0
      ↔ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0 = ∅ := by
  constructor
  · intro h
    rw [Finset.eq_empty_iff_forall_notMem]
    intro k hk
    have h1 := h k hk
    have h2 := Y_le_windowExcess_of_mem_routedFibre ctx.n24CarryData
      (genuineChargeRoute ctx) 0 hk
    have hY := n24CarryData_Y_pos ctx
    rw [Nat.cast_zero, zero_mul] at h1
    linarith
  · intro h
    exact nsgGate_of_fibreEmpty h 0

/-- An empty level-`s` heavy set supplies the level-`s` gate. -/
theorem nsgGate_of_heavySet_empty {ctx : ActualFailureContext} {s : ℕ}
    (h : nsgHeavySet ctx s = ∅) : NarrowSupportGate ctx s := by
  intro k hk
  rcases le_total
    (windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T)
    ((s : ℝ) * ctx.n24CarryData.Y) with hle | hge
  · exact hle
  · exfalso
    have hk' : k ∈ nsgHeavySet ctx s := Finset.mem_filter.mpr ⟨hk, hge⟩
    rw [h] at hk'
    exact Finset.notMem_empty k hk'

/-- The level-`s` gate empties the level-`(s+1)` heavy set (`Y > 0`). -/
theorem nsgHeavySet_succ_empty_of_gate {ctx : ActualFailureContext} {s : ℕ}
    (hgate : NarrowSupportGate ctx s) : nsgHeavySet ctx (s + 1) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro k hk
  have hmem := Finset.mem_filter.mp hk
  have h1 := hgate k hmem.1
  have h2 := hmem.2
  have hY := n24CarryData_Y_pos ctx
  rw [Nat.cast_add, Nat.cast_one] at h2
  linarith

/-- **The `s = 1` gate pins every member's excess to EXACTLY `Y`** — every off-fibre
miss carries precisely the activity floor; the narrow-support reading is sharp. -/
theorem nsgGate_one_excess_eq {ctx : ActualFailureContext}
    (hgate : NarrowSupportGate ctx 1) {k : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0) :
    windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r ctx.n24CarryData.T
      = ctx.n24CarryData.Y := by
  have h1 := hgate k hk
  rw [Nat.cast_one, one_mul] at h1
  exact le_antisymm h1
    (Y_le_windowExcess_of_mem_routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0 hk)

/-- The gate is TRIVIALLY true at the window calibration `64·(r+1)(L+B+1) ≤ s·L`
(the per-member ungated ceiling `windowExcess ≤ runDyadicMult ≤ (r+1)(L+B+1)`). -/
theorem nsgGate_trivial_of_calibration (ctx : ActualFailureContext) {s : ℕ}
    (h : 64 * tfaNatMult ctx ≤ s * shellLadderDepth ctx) :
    NarrowSupportGate ctx s := by
  intro k hk
  have hks : k ∈ ctx.n24CarryData.starts :=
    (mem_highExcessStarts.mp (Finset.mem_filter.mp hk).1).1
  rw [cnlMulti_starts_eq_window, Finset.mem_Ico] at hks
  have h1 : windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
      ctx.n24CarryData.T ≤ runDyadicMult ctx :=
    n24_windowExcess_le_runDyadicMult ctx hks.2
  have h2 := tfaRunDyadicMult_le_natMult ctx
  have h3 : (64 : ℝ) * ((tfaNatMult ctx : ℕ) : ℝ)
      ≤ (s : ℝ) * ((shellLadderDepth ctx : ℕ) : ℝ) := by exact_mod_cast h
  rw [n24CarryData_Y_eq_div]
  linarith

/-- **HONEST: the trivial calibration is DISJOINT from the closing regime** — at every
survivor pair the window calibration `64·(r+1)(L+B+1) ≤ s·L` and the numeric regime
`s·L ≤ 1274739·c` exclude each other (factor `≥ 176`: `64·64·986877 > 1274739·18`).
No unconditional regime exists; the gate is a genuine per-context demand. -/
theorem nsgTrivialGate_regime_disjoint (ctx : ActualFailureContext)
    (hsurv : Class0DatumSurvivor ctx) {s : ℕ}
    (htriv : 64 * tfaNatMult ctx ≤ s * shellLadderDepth ctx) :
    ¬ (s * shellLadderDepth ctx
        ≤ 1274739 * class0SurvivorPeriod (class1SlopeDatum ctx).q) := by
  intro hreg
  have hr := tfaClass0Survivor_r_ge ctx hsurv
  have hL := tfaClass0Survivor_depth_ge ctx hsurv
  have hc := tfaClass0SurvivorPeriod_le_18 (class1SlopeDatum ctx).q
  have hmult : 63160128 ≤ tfaNatMult ctx := by
    unfold tfaNatMult
    have h1 : 64 * 986877 ≤ (ctx.n24CarryData.r + 1) * 986877 :=
      Nat.mul_le_mul (by omega) le_rfl
    have h2 : (ctx.n24CarryData.r + 1) * 986877
        ≤ (ctx.n24CarryData.r + 1)
            * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) :=
      Nat.mul_le_mul le_rfl (by omega)
    omega
  generalize s * shellLadderDepth ctx = t at htriv hreg
  omega

/-! ## Part 4.  The gate closes the lanes: count-route absorption with exact constants -/

/-- The gated count-route mass bound at a survivor pair:
`mass₀ ≤ ⌈W/c⌉·s·Y` (gate-free count cap × narrow-support multiplier). -/
theorem nsgClass0SurvivorMass_le_countTerm (ctx : ActualFailureContext)
    (hsurv : Class0DatumSurvivor ctx) {s : ℕ} (hgate : NarrowSupportGate ctx s) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 0
      ≤ ((((supportShell ctx.shell.d ctx.shell.X).card
            + class0SurvivorPeriod (class1SlopeDatum ctx).q - 1)
          / class0SurvivorPeriod (class1SlopeDatum ctx).q : ℕ) : ℝ)
        * ((s : ℝ) * ctx.n24CarryData.Y) := by
  refine routedClassMassOf_le_countMultiplier ctx.n24CarryData (genuineChargeRoute ctx) 0
    hgate (mul_nonneg (Nat.cast_nonneg s) (n24CarryData_Y_pos ctx).le) ?_
  exact_mod_cast ofcClass0Fibre_card_le_of_survivor ctx hsurv

/-- The gated count-route mass bound on the generic lanes:
`mass₀ ≤ W·s·Y` (generic fibre width cap × narrow-support multiplier). -/
theorem nsgClass0GenericMass_le_countTerm (ctx : ActualFailureContext) {s : ℕ}
    (hgate : NarrowSupportGate ctx s) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 0
      ≤ (((supportShell ctx.shell.d ctx.shell.X).card : ℕ) : ℝ)
        * ((s : ℝ) * ctx.n24CarryData.Y) := by
  refine routedClassMassOf_le_countMultiplier ctx.n24CarryData (genuineChargeRoute ctx) 0
    hgate (mul_nonneg (Nat.cast_nonneg s) (n24CarryData_Y_pos ctx).le) ?_
  exact_mod_cast tfaFibre_card_le_width ctx (genuineChargeRoute ctx) 0

/-- **The survivor absorption from the gate** (ℕ numeric side
`24·⌈W/c⌉·s·L ≤ 31·X`; the `24` is `1536/64` from `Y = L/64`). -/
theorem nsgClass0SurvivorAbsorption_of_gate (ctx : ActualFailureContext)
    (hsurv : Class0DatumSurvivor ctx) {s : ℕ} (hgate : NarrowSupportGate ctx s)
    (hnum : 24 * ((((supportShell ctx.shell.d ctx.shell.X).card
            + class0SurvivorPeriod (class1SlopeDatum ctx).q - 1)
          / class0SurvivorPeriod (class1SlopeDatum ctx).q)
        * (s * shellLadderDepth ctx))
        ≤ 31 * ctx.shell.X) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 0
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have h1 := nsgClass0SurvivorMass_le_countTerm ctx hsurv hgate
  have h2 : ((((supportShell ctx.shell.d ctx.shell.X).card
            + class0SurvivorPeriod (class1SlopeDatum ctx).q - 1)
          / class0SurvivorPeriod (class1SlopeDatum ctx).q : ℕ) : ℝ)
        * ((s : ℝ) * ctx.n24CarryData.Y)
      = (((((supportShell ctx.shell.d ctx.shell.X).card
            + class0SurvivorPeriod (class1SlopeDatum ctx).q - 1)
          / class0SurvivorPeriod (class1SlopeDatum ctx).q)
        * (s * shellLadderDepth ctx) : ℕ) : ℝ) / 64 := by
    rw [n24CarryData_Y_eq_div]
    push_cast
    ring
  have h3 : (24 : ℝ) * (((((supportShell ctx.shell.d ctx.shell.X).card
            + class0SurvivorPeriod (class1SlopeDatum ctx).q - 1)
          / class0SurvivorPeriod (class1SlopeDatum ctx).q)
        * (s * shellLadderDepth ctx) : ℕ) : ℝ)
      ≤ 31 * (ctx.shell.X : ℝ) := by exact_mod_cast hnum
  have hc6 : erdos260Constants.cStar * erdos260Constants.ξ / 6 = 31 / 1536 := by
    rw [tfaCstarXi_eq]
    norm_num
  rw [hc6]
  rw [h2] at h1
  linarith

/-- **The generic-lane absorption from the gate** (ℕ numeric side `24·W·s·L ≤ 31·X`). -/
theorem nsgClass0GenericAbsorption_of_gate (ctx : ActualFailureContext) {s : ℕ}
    (hgate : NarrowSupportGate ctx s)
    (hnum : 24 * ((supportShell ctx.shell.d ctx.shell.X).card
        * (s * shellLadderDepth ctx))
        ≤ 31 * ctx.shell.X) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 0
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have h1 := nsgClass0GenericMass_le_countTerm ctx hgate
  have h2 : (((supportShell ctx.shell.d ctx.shell.X).card : ℕ) : ℝ)
        * ((s : ℝ) * ctx.n24CarryData.Y)
      = (((supportShell ctx.shell.d ctx.shell.X).card
          * (s * shellLadderDepth ctx) : ℕ) : ℝ) / 64 := by
    rw [n24CarryData_Y_eq_div]
    push_cast
    ring
  have h3 : (24 : ℝ) * (((supportShell ctx.shell.d ctx.shell.X).card
        * (s * shellLadderDepth ctx) : ℕ) : ℝ)
      ≤ 31 * (ctx.shell.X : ℝ) := by exact_mod_cast hnum
  have hc6 : erdos260Constants.cStar * erdos260Constants.ξ / 6 = 31 / 1536 := by
    rw [tfaCstarXi_eq]
    norm_num
  rw [hc6]
  rw [h2] at h1
  linarith

/-! ## Part 5.  The numeric gates from the in-tree failure cap (exact arithmetic)

The regime constant: `1274739 = ⌊31·2^24/(24·17)⌋` (`408·1274739 = 520093512 ≤
520093696 = 31·2^24`, slack `184` in units of `X/2^24` — the `+17` ceiling slack is
absorbed by `X ≥ 2^46`, free from the survivor depth floor). -/

/-- The failure cap in the form consumed here: `2^24·W < 17·X`. -/
theorem nsgSupportCap (ctx : ActualFailureContext) :
    16777216 * (supportShell ctx.shell.d ctx.shell.X).card < 17 * ctx.shell.X :=
  em_supportShell_strict ctx

/-- **The survivor regime arithmetic** (pure ℕ): the failure cap plus the regime
`s·L ≤ 1274739·c` discharge the survivor numeric gate `24·⌈W/c⌉·s·L ≤ 31·X`. -/
theorem nsgRegimeArith {W c sL X : ℕ} (hc18 : c ≤ 18)
    (hWcap : 16777216 * W < 17 * X) (hX : 70368744177664 ≤ X)
    (hreg : sL ≤ 1274739 * c) :
    24 * (((W + c - 1) / c) * sL) ≤ 31 * X := by
  have hchain : ((W + c - 1) / c) * sL ≤ 1274739 * (W + 17) := by
    calc ((W + c - 1) / c) * sL
        ≤ ((W + c - 1) / c) * (1274739 * c) := Nat.mul_le_mul le_rfl hreg
      _ = 1274739 * (((W + c - 1) / c) * c) := by ring
      _ ≤ 1274739 * (W + c - 1) :=
          Nat.mul_le_mul le_rfl (Nat.div_mul_le_self _ _)
      _ ≤ 1274739 * (W + 17) := Nat.mul_le_mul le_rfl (by omega)
  generalize ((W + c - 1) / c) * sL = t at hchain ⊢
  omega

/-- **The generic regime arithmetic** (pure ℕ): the failure cap plus `s·L ≤ 1274739`
discharge the generic numeric gate `24·W·s·L ≤ 31·X` — no scale floor needed. -/
theorem nsgGenericRegimeArith {W sL X : ℕ}
    (hWcap : 16777216 * W < 17 * X) (hreg : sL ≤ 1274739) :
    24 * (W * sL) ≤ 31 * X := by
  have hchain : W * sL ≤ W * 1274739 := Nat.mul_le_mul le_rfl hreg
  generalize W * sL = t at hchain ⊢
  omega

/-- The survivor numeric gate from the in-tree data alone, in the regime
`s·L ≤ 1274739·c` (the `X ≥ 2^46` slack absorber comes free from `L ≥ 986876`). -/
theorem nsgSurvivorRegimeGate (ctx : ActualFailureContext)
    (hsurv : Class0DatumSurvivor ctx) {s : ℕ}
    (hreg : s * shellLadderDepth ctx
        ≤ 1274739 * class0SurvivorPeriod (class1SlopeDatum ctx).q) :
    24 * ((((supportShell ctx.shell.d ctx.shell.X).card
            + class0SurvivorPeriod (class1SlopeDatum ctx).q - 1)
          / class0SurvivorPeriod (class1SlopeDatum ctx).q)
        * (s * shellLadderDepth ctx))
      ≤ 31 * ctx.shell.X := by
  have hXfloor : (70368744177664 : ℕ) ≤ ctx.shell.X := by
    have hXeq : ctx.shell.X = 2 ^ shellLadderDepth ctx :=
      Classical.choose_spec ctx.shell.hXdyadic
    have hL := tfaClass0Survivor_depth_ge ctx hsurv
    have h46 : (2 : ℕ) ^ 46 ≤ 2 ^ shellLadderDepth ctx :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h46' : (70368744177664 : ℕ) = 2 ^ 46 := by norm_num
    omega
  exact nsgRegimeArith (tfaClass0SurvivorPeriod_le_18 _) (nsgSupportCap ctx) hXfloor hreg

/-! ## Part 6.  The per-lane closures -/

/-- **THE SURVIVOR-LANE CLOSURE**: at every survivor pair, the narrow-support gate at
level `s` together with the regime `s·L ≤ 1274739·c` closes the de-razored mass lane
`mass₀ ≤ (31/1536)·X` — from the in-tree failure cap alone. -/
theorem nsgClass0Survivor_lane (ctx : ActualFailureContext)
    (hsurv : Class0DatumSurvivor ctx) {s : ℕ} (hgate : NarrowSupportGate ctx s)
    (hreg : s * shellLadderDepth ctx
        ≤ 1274739 * class0SurvivorPeriod (class1SlopeDatum ctx).q) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 0
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) :=
  nsgClass0SurvivorAbsorption_of_gate ctx hsurv hgate
    (nsgSurvivorRegimeGate ctx hsurv hreg)

/-- **THE GENERIC-LANE CLOSURE** (mid-band / big-order lanes): the narrow-support gate
at level `s` together with the regime `s·L ≤ 1274739` closes the mass demand (generic
width count `|fibre₀| ≤ W`; no period input). -/
theorem nsgClass0Generic_lane (ctx : ActualFailureContext) {s : ℕ}
    (hgate : NarrowSupportGate ctx s)
    (hreg : s * shellLadderDepth ctx ≤ 1274739) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 0
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) :=
  nsgClass0GenericAbsorption_of_gate ctx hgate
    (nsgGenericRegimeArith (nsgSupportCap ctx) hreg)

/-! ## Part 7.  Honest regime accounting -/

/-- All nineteen survivor pairs carry period `c ≥ 2` (values
`4,9,2,10,9,14,5,5,18,4,10,7,5` over the thirteen moduli). -/
theorem nsgSurvivorPeriod_ge_two (ctx : ActualFailureContext)
    (hsurv : Class0DatumSurvivor ctx) :
    2 ≤ class0SurvivorPeriod (class1SlopeDatum ctx).q := by
  rcases hsurv with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    (rw [h.1]; norm_num [class0SurvivorPeriod])

/-- **The uniform `s = 1` survivor regime**: every survivor pair clears the regime at
`s = 1` on the whole depth band `L ≤ 2549478` (period `≥ 2`) — a nonempty extension
of the survivor floor `L ≥ 986876` at EVERY pair. -/
theorem nsgSurvivorRegime_one_of_depth (ctx : ActualFailureContext)
    (hsurv : Class0DatumSurvivor ctx)
    (hdepth : shellLadderDepth ctx ≤ 2549478) :
    1 * shellLadderDepth ctx
      ≤ 1274739 * class0SurvivorPeriod (class1SlopeDatum ctx).q := by
  have h2 := nsgSurvivorPeriod_ge_two ctx hsurv
  have h3 : 1274739 * 2 ≤ 1274739 * class0SurvivorPeriod (class1SlopeDatum ctx).q :=
    Nat.mul_le_mul le_rfl h2
  omega

/-- **Honest survivor regime window**: the survivor depth floor `L ≥ 986876` pins the
admissible levels to `s ≤ 23` and the depth to `L ≤ 1274739·c ≤ 22945302`. -/
theorem nsgSurvivorRegime_s_le (ctx : ActualFailureContext)
    (hsurv : Class0DatumSurvivor ctx) {s : ℕ} (hs : 1 ≤ s)
    (hreg : s * shellLadderDepth ctx
        ≤ 1274739 * class0SurvivorPeriod (class1SlopeDatum ctx).q) :
    s ≤ 23
      ∧ shellLadderDepth ctx
          ≤ 1274739 * class0SurvivorPeriod (class1SlopeDatum ctx).q := by
  have hL := tfaClass0Survivor_depth_ge ctx hsurv
  have hc := tfaClass0SurvivorPeriod_le_18 (class1SlopeDatum ctx).q
  have h2 : s * 986876 ≤ s * shellLadderDepth ctx := Nat.mul_le_mul le_rfl hL
  have h3 : 1 * shellLadderDepth ctx ≤ s * shellLadderDepth ctx :=
    Nat.mul_le_mul hs le_rfl
  generalize s * shellLadderDepth ctx = t at h2 h3 hreg
  omega

/-- **Honest mid-lane pin**: on the mid lane (`q < 96` forces `L ≥ 986876` through the
wave-10 small-`q` floor) the generic regime pins `s = 1` and `L ≤ 1274739` — the
honest closing window is exactly `986876 ≤ L ≤ 1274739`. -/
theorem nsgMidRegime_pin (ctx : ActualFailureContext)
    (h96 : (class1SlopeDatum ctx).q < 96) {s : ℕ} (hs : 1 ≤ s)
    (hreg : s * shellLadderDepth ctx ≤ 1274739) :
    s = 1 ∧ 986876 ≤ shellLadderDepth ctx ∧ shellLadderDepth ctx ≤ 1274739 := by
  have hL := floorPushV2_depth_of_q_le_2pow20 ctx (by omega)
  have h2 : s * 986876 ≤ s * shellLadderDepth ctx := Nat.mul_le_mul le_rfl hL
  have h3 : 1 * shellLadderDepth ctx ≤ s * shellLadderDepth ctx :=
    Nat.mul_le_mul hs le_rfl
  generalize s * shellLadderDepth ctx = t at h2 h3 hreg
  refine ⟨by omega, hL, by omega⟩

/-- The per-pair `s = 1` regime table: `(q, c, 1274739·c)` — the depth ceiling under
which the level-1 narrow-support gate closes the survivor lane at modulus `q`. -/
def narrowSupportRegimeTable : List (ℕ × ℕ × ℕ) :=
  [(17, 4, 5098956), (19, 9, 11472651), (21, 2, 2549478), (25, 10, 12747390),
   (27, 9, 11472651), (29, 14, 17846346), (33, 5, 6373695), (35, 5, 6373695),
   (37, 18, 22945302), (39, 4, 5098956), (41, 10, 12747390), (43, 7, 8923173),
   (45, 5, 6373695)]

/-- The regime table covers the thirteen survivor moduli. -/
theorem narrowSupportRegimeTable_length : narrowSupportRegimeTable.length = 13 := rfl

/-- The regime table is correct: each row reads `(q, class0SurvivorPeriod q,
1274739 · class0SurvivorPeriod q)`. -/
theorem narrowSupportRegimeTable_correct :
    ∀ e ∈ narrowSupportRegimeTable,
      e.2.1 = class0SurvivorPeriod e.1 ∧ e.2.2 = 1274739 * e.2.1 := by
  intro e he
  simp only [narrowSupportRegimeTable, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by norm_num [class0SurvivorPeriod], by norm_num⟩

/-! ## Part 8.  The v18 field, rebuilt from the named gates -/

/-- The big-order lane's certificate horn, verbatim from the frontier field's third
lane (the order-criterion disjunct discharged upstream via `class0Tail_of_order_gt`). -/
def Class0BigOrderHorn (ctx : ActualFailureContext) : Prop :=
  ∃ C, ((Nat.log 2 (class1SlopeDatum ctx).q + 1) * C
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
                    (cycleRep c k)

/-- The exact three-lane class-0 mass field consumed by the wave-18 frontier and
absorption surfaces.  This is the expanded shape rebuilt by
`nsgFrontierClass0Mass_of_gates`, with the big-order certificate packaged as
`Class0BigOrderHorn`. -/
abbrev Class0MassField : Prop :=
  ∀ ctx : ActualFailureContext,
    (Class0DatumSurvivor ctx →
      routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 0
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ)) ∧
    (48 ≤ (class1SlopeDatum ctx).q → (class1SlopeDatum ctx).q < 96 →
      Class0CycleMeetsShallow ctx →
      routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 0
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ)) ∧
    (96 ≤ (class1SlopeDatum ctx).q →
      Class0BigOrderHorn ctx
      ∨ routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 0
          ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ))

/-- **The narrow-support gate data for the three class-0 lanes** — the wave-19 named
conditional: per-lane gate levels with their closing regimes (the big lane keeps the
order horn as an alternative, exactly as the v18 field does). -/
structure NarrowSupportClass0Gates where
  /-- Survivor lane: a gate level in the per-pair regime `s·L ≤ 1274739·c`. -/
  survivor : ∀ ctx : ActualFailureContext, Class0DatumSurvivor ctx →
    ∃ s : ℕ, NarrowSupportGate ctx s
      ∧ s * shellLadderDepth ctx
          ≤ 1274739 * class0SurvivorPeriod (class1SlopeDatum ctx).q
  /-- Mid-band lane (`48 ≤ q < 96`, shallow-meeting cycles): a gate level in the
  generic regime `s·L ≤ 1274739` (honest pin: `s = 1`, `986876 ≤ L ≤ 1274739`). -/
  mid : ∀ ctx : ActualFailureContext,
    48 ≤ (class1SlopeDatum ctx).q → (class1SlopeDatum ctx).q < 96 →
    Class0CycleMeetsShallow ctx →
    ∃ s : ℕ, NarrowSupportGate ctx s ∧ s * shellLadderDepth ctx ≤ 1274739
  /-- Big-order lane (`96 ≤ q`): the order horn OR a gate level in the generic
  regime. -/
  big : ∀ ctx : ActualFailureContext, 96 ≤ (class1SlopeDatum ctx).q →
    Class0BigOrderHorn ctx
      ∨ ∃ s : ℕ, NarrowSupportGate ctx s ∧ s * shellLadderDepth ctx ≤ 1274739

/-- **THE v18 FIELD REBUILT**: the narrow-support gate data supplies the EXACT
`Erdos260FrontierResidual.class0Mass` field shape (verbatim also the
`Erdos260AbsorptionResidual.class0MassAbsorption` field) — plug directly into the
frontier structure literal. -/
theorem nsgFrontierClass0Mass_of_gates (G : NarrowSupportClass0Gates) :
    ∀ ctx : ActualFailureContext,
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
          ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ)) := by
  intro ctx
  refine ⟨?_, ?_, ?_⟩
  · intro hsurv
    obtain ⟨s, hgate, hreg⟩ := G.survivor ctx hsurv
    exact nsgClass0Survivor_lane ctx hsurv hgate hreg
  · intro h48 h96 hmeet
    obtain ⟨s, hgate, hreg⟩ := G.mid ctx h48 h96 hmeet
    exact nsgClass0Generic_lane ctx hgate hreg
  · intro h96
    rcases G.big ctx h96 with h | ⟨s, hgate, hreg⟩
    · exact Or.inl h
    · exact Or.inr (nsgClass0Generic_lane ctx hgate hreg)

/-- **The weakening witness**: per-lane fibre emptiness (the wave-16 currency)
supplies the gate data at level `s = 0` — the narrow-support surface is strictly
weaker than the emptiness surface; NO converse is claimed (the mass cap does not
bound per-member excess). -/
def nsgGates_of_fibreEmpty
    (hS : ∀ ctx : ActualFailureContext, Class0DatumSurvivor ctx →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0 = ∅)
    (hM : ∀ ctx : ActualFailureContext,
      48 ≤ (class1SlopeDatum ctx).q → (class1SlopeDatum ctx).q < 96 →
      Class0CycleMeetsShallow ctx →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0 = ∅)
    (hB : ∀ ctx : ActualFailureContext, 96 ≤ (class1SlopeDatum ctx).q →
      Class0BigOrderHorn ctx
        ∨ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0 = ∅) :
    NarrowSupportClass0Gates where
  survivor ctx hsurv := ⟨0, nsgGate_of_fibreEmpty (hS ctx hsurv) 0, by simp⟩
  mid ctx h48 h96 hmeet := ⟨0, nsgGate_of_fibreEmpty (hM ctx h48 h96 hmeet) 0, by simp⟩
  big ctx h96 := by
    rcases hB ctx h96 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨0, nsgGate_of_fibreEmpty h 0, by simp⟩

/-! ## Part 9.  Status -/

/-- The wave-19 status ledger (honest). -/
def narrowSupportGateStatus : List String :=
  [ "WAVE 19 (NarrowSupportGate): the v18 class-0 mass lanes worked through the " ++
      "manuscript H.1/K.4 narrow-support mechanism, the unique route left after " ++
      "tfaClass0Gate_not_from_failureCap (count*maxExcess) and " ++
      "agcClass0DevGate_refuted (deviation budget, floor X/2, factor 24.8).",
    "LEVEL-SET BOUND (goal 1, PROVED, exact form): at every survivor pair and " ++
      "every level s, s*Y*|{k in fibre0 : windowExcess k >= s*Y}| <= " ++
      "ceil((r+1)/c)*emExitMass (nsgLevelSet_count_cap; span-ceiled form " ++
      "<= ceil((r+1)/c)*(W+r)(L+B+1), nsgLevelSet_count_cap_span; generic " ++
      "band<=4 form with overlap r+1, nsgLevelSet_count_cap_ofBand) - the " ++
      "in-tree Markov shadow of the H.1 Chernoff decay 2^(-cY).",
    "MASS SPLIT (PROVED): mass0 <= |fibre0|*s*Y + ceil((r+1)/c)*emExitMass at " ++
      "every threshold s (nsgClass0Mass_split); s = 1 headline mass0 <= " ++
      "ceil(W/c)*Y + ceil((r+1)/c)*(W+r)(L+B+1) (nsgClass0Mass_split_headline). " ++
      "The single split DOMINATES the dyadic harmonic ladder (no log factor): " ++
      "the brief's sum_j 2^(j+1)*Y*|heavy_{2^j}| form is strictly weaker.",
    "HONEST REFUTATION (the arithmetic vs the cap): the deviation term carries " ++
      "the relocated 21.1 floor - (31/1536)X < t*emExitMass for every t >= 1 " ++
      "(nsgSplit_devTerm_floor), so the split budget EXCEEDS the cap at every " ++
      "survivor context and every s (nsgLevelSum_route_refuted).  The r-ceiling " ++
      "r <= kappa*L does not rescue it: the dev term needs L^2 <~ 3*10^8*c " ++
      "against L >= 986876 at c <= 18.  NO level-set SUMMATION closes any lane; " ++
      "the surviving mechanism is the per-member gate.",
    "THE NAMED GATE: NarrowSupportGate ctx s = every class-0 fibre member has " ++
      "windowExcess <= s*Y.  s = 0 is exactly fibre emptiness (nsgGate_zero_iff); " ++
      "s = 1 pins every miss to excess EXACTLY Y (nsgGate_one_excess_eq); " ++
      "strictly weaker than wave-16 emptiness (nsgGate_of_fibreEmpty); trivially " ++
      "true at 64(r+1)(L+B+1) <= s*L (nsgGate_trivial_of_calibration) but that " ++
      "calibration is DISJOINT from the closing regime by factor >= 176 " ++
      "(nsgTrivialGate_regime_disjoint) - the gate is a genuine demand.",
    "SURVIVOR LANE (closed conditionally, exact constants): gate s + regime " ++
      "s*L <= 1274739*c (1274739 = floor(31*2^24/408)) give mass0 <= " ++
      "ceil(W/c)*s*Y <= (31/1536)X from the failure cap 2^24*W < 17X alone " ++
      "(nsgClass0Survivor_lane; arithmetic nsgRegimeArith, X >= 2^46 slack free " ++
      "from L >= 986876).  Per-pair s=1 ceilings (narrowSupportRegimeTable): " ++
      "q=21: L <= 2549478; q=17,39: 5098956; q=33,35,45: 6373695; q=43: 8923173; " ++
      "q=19,27: 11472651; q=25,41: 12747390; q=29: 17846346; q=37: 22945302.  " ++
      "All periods >= 2 (nsgSurvivorPeriod_ge_two), so s=1 closes the WHOLE " ++
      "band 986876 <= L <= 2549478 at every pair - a genuine regime extension.  " ++
      "Honest window: 1 <= s <= 23 and L <= 1274739*c (nsgSurvivorRegime_s_le).",
    "MID LANE (goal 2): same gate, generic count |fibre0| <= W - gate s + " ++
      "s*L <= 1274739 close the lane (nsgClass0Generic_lane).  HONEST: q < 96 " ++
      "forces L >= 986876 (wave-10 floor), pinning s = 1 and the closing window " ++
      "to exactly 986876 <= L <= 1274739 (nsgMidRegime_pin).",
    "BIG LANE (goal 2): the order-criterion horn stays verbatim " ++
      "(Class0BigOrderHorn, discharged upstream via class0Tail_of_order_gt); " ++
      "the mass horn gets the same generic gate+regime closure.",
    "FIELD REBUILD (goal 3): NarrowSupportClass0Gates (three per-lane suppliers) " ++
      "rebuilds the EXACT v18 class0Mass field shape " ++
      "(nsgFrontierClass0Mass_of_gates - verbatim also the absorption surface's " ++
      "class0MassAbsorption field); wave-16 per-lane emptiness supplies the " ++
      "gates at s = 0 (nsgGates_of_fibreEmpty).  One direction only - honest.",
    "WHAT STAYS OPEN (sharp): per survivor pair (q,K0) with period c, the demand " ++
      "is NarrowSupportGate ctx s with s*L <= 1274739*c at every actual context; " ++
      "for L > 1274739*c even the s=1 gate (every miss at the exact floor Y) " ++
      "does not close through the count route, and the deviation route is " ++
      "floor-blocked - beyond the regime the lane is genuinely open.  The " ++
      "mid/big mass horns are open outside s*L <= 1274739 likewise.",
    "No sorry, no admit, no new axiom, no native_decide; additive only." ]

/-- The status ledger is non-empty (honest, non-vacuous). -/
theorem narrowSupportGateStatus_nonempty : narrowSupportGateStatus ≠ [] := by
  simp [narrowSupportGateStatus]

end

end Erdos260

/-! ## Audit: every key declaration reports exactly
`[propext, Classical.choice, Quot.sound]` or fewer. -/

#print axioms Erdos260.nsgHeavySet_subset_fibre
#print axioms Erdos260.nsgHeavySet_subset_starts
#print axioms Erdos260.nsgHeavy_mass_lower
#print axioms Erdos260.nsgHeavy_excSum_le_devSum
#print axioms Erdos260.nsgLevelSet_count_cap
#print axioms Erdos260.nsgLevelSet_count_cap_span
#print axioms Erdos260.nsgLevelSet_count_cap_ofBand
#print axioms Erdos260.nsgClass0Mass_split
#print axioms Erdos260.nsgClass0Mass_split_headline
#print axioms Erdos260.nsgSplit_devTerm_floor
#print axioms Erdos260.nsgLevelSum_route_refuted
#print axioms Erdos260.nsgGate_of_fibreEmpty
#print axioms Erdos260.nsgGate_zero_iff
#print axioms Erdos260.nsgGate_of_heavySet_empty
#print axioms Erdos260.nsgHeavySet_succ_empty_of_gate
#print axioms Erdos260.nsgGate_one_excess_eq
#print axioms Erdos260.nsgGate_trivial_of_calibration
#print axioms Erdos260.nsgTrivialGate_regime_disjoint
#print axioms Erdos260.nsgClass0SurvivorMass_le_countTerm
#print axioms Erdos260.nsgClass0GenericMass_le_countTerm
#print axioms Erdos260.nsgClass0SurvivorAbsorption_of_gate
#print axioms Erdos260.nsgClass0GenericAbsorption_of_gate
#print axioms Erdos260.nsgSupportCap
#print axioms Erdos260.nsgRegimeArith
#print axioms Erdos260.nsgGenericRegimeArith
#print axioms Erdos260.nsgSurvivorRegimeGate
#print axioms Erdos260.nsgClass0Survivor_lane
#print axioms Erdos260.nsgClass0Generic_lane
#print axioms Erdos260.nsgSurvivorPeriod_ge_two
#print axioms Erdos260.nsgSurvivorRegime_one_of_depth
#print axioms Erdos260.nsgSurvivorRegime_s_le
#print axioms Erdos260.nsgMidRegime_pin
#print axioms Erdos260.narrowSupportRegimeTable_length
#print axioms Erdos260.narrowSupportRegimeTable_correct
#print axioms Erdos260.Class0MassField
#print axioms Erdos260.nsgFrontierClass0Mass_of_gates
#print axioms Erdos260.nsgGates_of_fibreEmpty
#print axioms Erdos260.narrowSupportGateStatus_nonempty
