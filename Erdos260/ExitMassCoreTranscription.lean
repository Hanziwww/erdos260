import Erdos260.ExitMassControl
import Erdos260.AbsorptionGateClosure
import Erdos260.SurvivorRegimeEnumeration
import Erdos260.FixedDataEndgame

/-!
# Exit-mass core transcription (`ExitMassCoreTranscription`)

This module (NEW; it edits no existing file) transcribes the manuscript's
L.3.1 / M.5.1 / I.3 mechanism ("clean in-cycle motion is not charged") against the
wave-19 single deep atom `ExitMassControlCore`, and settles WHICH form of that
mechanism the in-tree definitions support.

## (c) The telescoping / event-counting verdict

The corrected per-class mass is START-indexed: `routedClassMassOf ... i` is the sum
of the FULL window excesses over the class fibre (`routedClassMassOf_eq_sum_fibre`).
The manuscript's I.3 ledger ("charge only first entry / first exit; in-cycle clean
steps contribute zero", so a run of length `m` charges `entry + m * drift`) is NOT
the shape of this sum: each in-run member is charged its WHOLE excess, not its
increment.  What IS provable from the in-tree window machinery:

* **THE TELESCOPING ATOM** (`emcT_gapWindow_shift`, `emcT_windowExcess_drift`,
  `emcT_windowExcess_drift_rev`, `emcT_drift_le_reach`): consecutive (orbit-)starts'
  windows overlap in all but the boundary gaps, so the excess DIFFERENCE under a
  shift by `s+1` is bounded by the `s+1` boundary gaps alone — on the reach range
  `≤ (s+1)·(L+B+1)`, NOT the full window.  This is the manuscript's per-step drift
  bound, exactly.
* **THE HONEST RUN SUM** (`emcT_run_member_le`, `emcT_run_telescope`): iterating the
  drift bound, the `j`-th member of an in-fibre run of step `c` has excess
  `≤ entry + j·D`, so the run TOTAL telescopes to `m·entry + (m(m-1)/2)·D` — the
  accumulation is QUADRATIC in the run length, not the manuscript's linear
  `entry + m·D` (which bounds only the LAST member).  The start-indexed in-tree
  mass therefore does NOT support the linear in-cycle-uncharged form.
* **THE SUPPORTED FORM IS EVENT-COUNTING**: the exit-weighted budget.  The class
  fibre's deviation content telescopes through `c`-spacing into
  `≤ ⌈(r+1)/c⌉ = (r+c)/c` copies of the FIBRE-RESTRICTED exit mass
  (`emc2_fibreDevMass_le_overlap`, via the proved block decomposition
  `agc_spaced_windowSum_le`), and the class mass sits below the fibre deviation
  content (`agcClassMass_le_sum_devWindow`, band `≤ 4`).  The entry/exit event sets
  of a fibre under the step map are formalized (`emcFibreEntrySet` /
  `emcFibreExitSet`, nonempty whenever the fibre is — every maximal run has a first
  entry and a first exit).

## (d) The off-pin charge bound and the regimes

`emc2_cap_of_spacedShare` (THE MASTER CONDITIONAL): at any context with recurrent
band `≤ 4`, if the class-`i` fibre is `c`-spaced, its restricted exit mass carries
at most a `b/c` share of the total exit mass, and the numeric regime
`1536·((r+c)/c)·b·(W+r)·(L+B+1) ≤ 31·c·X` holds, then the corrected cap
`mass_i ≤ (31/1536)·X` follows — with exact in-tree constants
(`emExitMass ≤ (W+r)(L+B+1)`, `em_exitMass_le_reach_span`).

REGIMES CLEARED: NONE unconditionally.  The numeric regime is self-limiting: against
the unconditional support floor `X ≤ 2(W+r)(L+B+1)` (`fde_W_floor`) it FORCES
`768·((r+c)/c)·b ≤ 31·c` (`emc2_spacedShare_forces_threshold`), hence the absolute
proportionality threshold `768·b ≤ 31·c`, i.e. `c/b ≥ 768/31 ≈ 24.8`
(`emc2_spacedShare_forces_absolute`).

## (e) The proportionality residual (exact form, which pairs)

The minimal residual is the named `EmcSpacedShareDatum`: per class, a period `c`,
a share numerator `b`, the fibre `c`-spacing, the share
`c·(fibre exit mass) ≤ b·(total exit mass)` — the manuscript's "band-`c` residues
are `b_c` out of `c` per cycle" equidistribution — and the numeric regime.  NO
in-tree equidistribution atom exists (grep: none); the share is genuinely open.
Against the certified `(c, b₄)` table (`sreClass1ThresholdTable`, 110 rows):

* The absolute threshold `768·b ≤ 31·c` is cleared by EXACTLY EIGHT pairs
  (`emcProportionalClearedPairs_eq`): `(103,51)`, `(115,11)`, `(115,57)`,
  `(143,6)` (period 25–28, `b₄ = 1`), `(175,2)`, `(177,1)`, `(177,88)` (period 29,
  `b₄ = 1`), `(191,95)` (period 54, `b₄ = 2`).
* At DEEP scales the demand sharpens: `2^986891 < X` forces `L ≥ 986892`, hence
  `r = ⌊κL⌋ ≥ 63` (`emc2_deep_r_floor`), so the forced threshold becomes
  `768·((63+c)/c)·b ≤ 31·c` (`emc2_deep_spacedShare_threshold`) — and NO row of
  the certified table satisfies it (`emcDeepProportionalClearedPairs_eq_nil`,
  `emc2_deep_certified_pair_obstruction`, `emc2_deep_spacedShare_not_certified`).
  The overlap factor `(r+c)/c ≥ 2` at every certified period `c ≤ 98 ≥ 64`... 
  precisely: every certified `c ≤ 98` and `r ≥ 63` give `(63+c)/c ≥ 1`, and the
  products all overshoot.  A pair with `b = 1` and period `c ≥ 64` WOULD clear the
  deep threshold; the certified table contains none (max `b=1` period is 29).

So the off-pin core is NOT provable on any certified-pair regime through this
budget; the residual is the share datum itself at uncertified parameters (e.g. a
fibre spacing `c ≥ 64` with `b = 1` — a fully exit-light long cycle).

## (f) Wiring (the v19 shapes)

`EmcOffPinSpacedShareRegime` (the regime'd off-pin demand) ⟹ `ExitMassControlOffPin`
(`emc2_offPin_of_regime`); with `DeepOrbitPinVoiding` it rebuilds the full core
through the wave-19 split (`emc2_core_of_regime_and_voiding` via
`exitMassControl_iff_split`) and hence the v18 `deepOrbitPin` supply and the wave-8
axis (`emc2_deepFixedFamilyVoid_of_regime_and_voiding`,
`emc2_returnBand2Void_of_regime_and_voiding` etc.).

No `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option maxRecDepth 8192

/-! ## Part 1.  The telescoping atom: the window-shift drift calculus

The orbit step shifts the start index; consecutive members' windows overlap in all
but the boundary gaps.  The excess difference is bounded by the boundary gaps
alone — the per-step drift bound, the heart of the I.3 "clean in-cycle motion"
mechanism. -/

/-- **The window-shift identity**: shifting the window start by `s+1` exchanges the
`s+1` leading gaps for the `s+1` trailing ones — the two windows share everything
else.  (`gapWindow g k s` has `s+1` terms.) -/
theorem emcT_gapWindow_shift (g : ℕ → ℕ) (k r s : ℕ) :
    gapWindow g (k + (s + 1)) r + gapWindow g k s
      = gapWindow g k r + gapWindow g (k + r + 1) s := by
  have h1 := gapWindow_append g k s r
  have h2 := gapWindow_append g k r s
  rw [show s + r + 1 = r + s + 1 from by omega] at h1
  rw [show k + (s + 1) = k + s + 1 from by omega]
  omega

/-- The positive part is sub-translation: `(x + d)⁺ ≤ x⁺ + d` for `d ≥ 0`. -/
theorem emcT_positivePart_add_le (x d : ℝ) (hd : 0 ≤ d) :
    positivePart (x + d) ≤ positivePart x + d := by
  unfold positivePart
  refine max_le ?_ ?_
  · have h1 : x ≤ max x 0 := le_max_left x 0
    linarith
  · have h0 : (0 : ℝ) ≤ max x 0 := le_max_right x 0
    linarith

/-- **THE PER-STEP DRIFT BOUND (forward)**: shifting the start by `s+1` raises the
window excess by at most the `s+1` trailing boundary gaps — the in-cycle excess
difference is charged the boundary terms only, never the full window. -/
theorem emcT_windowExcess_drift (g : ℕ → ℕ) (k r s : ℕ) (T : ℝ) :
    windowExcess g (k + (s + 1)) r T
      ≤ windowExcess g k r T + ((gapWindow g (k + r + 1) s : ℕ) : ℝ) := by
  have hgap : gapWindow g (k + (s + 1)) r
      ≤ gapWindow g k r + gapWindow g (k + r + 1) s := by
    have h := emcT_gapWindow_shift g k r s
    omega
  have hgapR : ((gapWindow g (k + (s + 1)) r : ℕ) : ℝ)
      ≤ ((gapWindow g k r : ℕ) : ℝ) + ((gapWindow g (k + r + 1) s : ℕ) : ℝ) := by
    exact_mod_cast hgap
  unfold windowExcess
  calc positivePart (((gapWindow g (k + (s + 1)) r : ℕ) : ℝ) - T)
      ≤ positivePart (((gapWindow g k r : ℕ) : ℝ) - T
          + ((gapWindow g (k + r + 1) s : ℕ) : ℝ)) :=
        positivePart_mono (by linarith)
    _ ≤ positivePart (((gapWindow g k r : ℕ) : ℝ) - T)
          + ((gapWindow g (k + r + 1) s : ℕ) : ℝ) :=
        emcT_positivePart_add_le _ _ (by positivity)

/-- **The per-step drift bound (backward)**: the reverse shift is charged the `s+1`
leading boundary gaps. -/
theorem emcT_windowExcess_drift_rev (g : ℕ → ℕ) (k r s : ℕ) (T : ℝ) :
    windowExcess g k r T
      ≤ windowExcess g (k + (s + 1)) r T + ((gapWindow g k s : ℕ) : ℝ) := by
  have hgap : gapWindow g k r
      ≤ gapWindow g (k + (s + 1)) r + gapWindow g k s := by
    have h := emcT_gapWindow_shift g k r s
    omega
  have hgapR : ((gapWindow g k r : ℕ) : ℝ)
      ≤ ((gapWindow g (k + (s + 1)) r : ℕ) : ℝ) + ((gapWindow g k s : ℕ) : ℝ) := by
    exact_mod_cast hgap
  unfold windowExcess
  calc positivePart (((gapWindow g k r : ℕ) : ℝ) - T)
      ≤ positivePart (((gapWindow g (k + (s + 1)) r : ℕ) : ℝ) - T
          + ((gapWindow g k s : ℕ) : ℝ)) :=
        positivePart_mono (by linarith)
    _ ≤ positivePart (((gapWindow g (k + (s + 1)) r : ℕ) : ℝ) - T)
          + ((gapWindow g k s : ℕ) : ℝ) :=
        emcT_positivePart_add_le _ _ (by positivity)

/-- **The drift bound on the reach range, with the in-tree per-gap ceiling**: while
the shifted window stays inside the reach `[F, F+W+r)`, the per-step drift is
`≤ (s+1)·(L+B+1)` — the boundary gaps obey the carry-rigidity ceiling
`n24_hitGap_le_reach`, NOT the full-window ceiling `(r+1)(L+B+1)`. -/
theorem emcT_drift_le_reach (ctx : ActualFailureContext) {k s : ℕ}
    (hreach : k + ctx.n24CarryData.r + 1 + s
      < emF ctx + emW ctx + ctx.n24CarryData.r) :
    windowExcess (hitGap ctx.n24CarryData.a) (k + (s + 1)) ctx.n24CarryData.r
        ctx.n24CarryData.T
      ≤ windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
          ctx.n24CarryData.T
        + (((s + 1) * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) : ℕ) : ℝ) := by
  have hdrift := emcT_windowExcess_drift (hitGap ctx.n24CarryData.a) k
    ctx.n24CarryData.r s ctx.n24CarryData.T
  have hcap : gapWindow (hitGap ctx.n24CarryData.a) (k + ctx.n24CarryData.r + 1) s
      ≤ (s + 1) * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) := by
    refine gapWindow_le_of_pointwise ?_
    intro i hi
    refine n24_hitGap_le_reach ctx ?_
    unfold emF emW at hreach
    omega
  have hcapR : ((gapWindow (hitGap ctx.n24CarryData.a)
        (k + ctx.n24CarryData.r + 1) s : ℕ) : ℝ)
      ≤ (((s + 1) * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) : ℕ) : ℝ) := by
    exact_mod_cast hcap
  linarith

/-- **The run member bound**: iterating the per-step drift `D` along an in-fibre run
of step `c`, the `j`-th member's excess is at most the ENTRY excess plus `j·D` —
the L.3.1/I.3 "first entry pays, in-cycle motion drifts" form, valid for the LAST
member (and each member) of the run. -/
theorem emcT_run_member_le (g : ℕ → ℕ) (r : ℕ) (T : ℝ) (k c m : ℕ) {D : ℝ}
    (hstep : ∀ j < m, windowExcess g (k + (j + 1) * c) r T
      ≤ windowExcess g (k + j * c) r T + D) :
    ∀ j, j ≤ m → windowExcess g (k + j * c) r T
      ≤ windowExcess g k r T + (j : ℝ) * D := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ n ih =>
      intro hj
      have h2 := ih (by omega)
      have h1 := hstep n (by omega)
      calc windowExcess g (k + (n + 1) * c) r T
          ≤ windowExcess g (k + n * c) r T + D := h1
        _ ≤ windowExcess g k r T + (n : ℝ) * D + D := by linarith
        _ = windowExcess g k r T + ((n + 1 : ℕ) : ℝ) * D := by push_cast; ring

/-- **THE HONEST RUN TELESCOPING**: the start-indexed run TOTAL accumulates the
drift QUADRATICALLY — `Σ_{j<m} excess(k+jc) ≤ m·entry + (m(m-1)/2)·D`.  This is
what the in-tree mass (a sum of FULL excesses) supports; the manuscript's linear
`entry + m·D` bounds only the last member (`emcT_run_member_le`), not the sum —
the start-indexed `routedClassMassOf` does NOT realize the I.3
"in-cycle-uncharged" linear ledger. -/
theorem emcT_run_telescope (g : ℕ → ℕ) (r : ℕ) (T : ℝ) (k c m : ℕ) {D : ℝ}
    (hstep : ∀ j < m, windowExcess g (k + (j + 1) * c) r T
      ≤ windowExcess g (k + j * c) r T + D) :
    ∑ j ∈ Finset.range m, windowExcess g (k + j * c) r T
      ≤ (m : ℝ) * windowExcess g k r T + ((m * (m - 1) / 2 : ℕ) : ℝ) * D := by
  have hmem := emcT_run_member_le g r T k c m hstep
  have hgauss : (∑ j ∈ Finset.range m, j) = m * (m - 1) / 2 := by
    have h2 := Finset.sum_range_id_mul_two m
    omega
  calc ∑ j ∈ Finset.range m, windowExcess g (k + j * c) r T
      ≤ ∑ j ∈ Finset.range m, (windowExcess g k r T + (j : ℝ) * D) :=
        Finset.sum_le_sum (fun j hj => hmem j (le_of_lt (Finset.mem_range.mp hj)))
    _ = (m : ℝ) * windowExcess g k r T + (∑ j ∈ Finset.range m, (j : ℝ)) * D := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul, ← Finset.sum_mul]
    _ = (m : ℝ) * windowExcess g k r T + ((m * (m - 1) / 2 : ℕ) : ℝ) * D := by
        rw [show (∑ j ∈ Finset.range m, (j : ℝ))
            = ((∑ j ∈ Finset.range m, j : ℕ) : ℝ) from by push_cast; rfl, hgauss]

/-! ## Part 2.  The entry/exit event sets and the event-counting form

The supported transcription of the I.3 ledger: events, not members.  The fibre's
boundary under the index step map `k ↦ k + c` gives the entry/exit events; the
class deviation content telescopes through `c`-spacing into `⌈(r+1)/c⌉` copies of
the FIBRE-RESTRICTED exit mass. -/

/-- The fibre's reach: the union of its members' descent windows. -/
def emcFibreReach (ctx : ActualFailureContext) (i : Fin 7) : Finset ℕ :=
  (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i).biUnion
    (fun k => Finset.Ico k (k + ctx.n24CarryData.r + 1))

/-- The fibre-restricted exit mass: the L.3.1 deviation weight summed over the
fibre's own reach only — the per-CLASS share of the exit ledger. -/
def emcFibreExitMass (ctx : ActualFailureContext) (i : Fin 7) : ℕ :=
  ∑ j ∈ emcFibreReach ctx i, emExitWeight ctx j

/-- The fibre's deviation content: the summed per-window exit content. -/
def emcFibreDevMass (ctx : ActualFailureContext) (i : Fin 7) : ℕ :=
  ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i, emDevWindow ctx k

/-- **The entry event set** of the fibre under the step map `k ↦ k + c`: members
whose predecessor is not in the fibre (the run heads — L.3.1 first entries). -/
def emcFibreEntrySet (ctx : ActualFailureContext) (i : Fin 7) (c : ℕ) : Finset ℕ :=
  (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i).filter
    (fun k => k < c
      ∨ k - c ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i)

/-- **The exit event set** of the fibre under the step map: members whose successor
is not in the fibre (the run tails — L.3.1 first exits). -/
def emcFibreExitSet (ctx : ActualFailureContext) (i : Fin 7) (c : ℕ) : Finset ℕ :=
  (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i).filter
    (fun k => k + c ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i)

/-- Entry events are fibre members. -/
theorem emcFibreEntrySet_subset (ctx : ActualFailureContext) (i : Fin 7) (c : ℕ) :
    emcFibreEntrySet ctx i c
      ⊆ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i :=
  Finset.filter_subset _ _

/-- Exit events are fibre members. -/
theorem emcFibreExitSet_subset (ctx : ActualFailureContext) (i : Fin 7) (c : ℕ) :
    emcFibreExitSet ctx i c
      ⊆ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i :=
  Finset.filter_subset _ _

/-- A nonempty fibre has an entry event: its minimum member is a run head. -/
theorem emcFibreEntrySet_nonempty (ctx : ActualFailureContext) (i : Fin 7)
    {c : ℕ} (hc : 1 ≤ c)
    (hne : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i).Nonempty) :
    (emcFibreEntrySet ctx i c).Nonempty := by
  refine ⟨(routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i).min' hne, ?_⟩
  unfold emcFibreEntrySet
  rw [Finset.mem_filter]
  refine ⟨Finset.min'_mem _ hne, ?_⟩
  by_cases hk : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i).min' hne < c
  · exact Or.inl hk
  · refine Or.inr ?_
    intro hmem
    have hle := Finset.min'_le _ _ hmem
    omega

/-- A nonempty fibre has an exit event: its maximum member is a run tail. -/
theorem emcFibreExitSet_nonempty (ctx : ActualFailureContext) (i : Fin 7)
    {c : ℕ} (hc : 1 ≤ c)
    (hne : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i).Nonempty) :
    (emcFibreExitSet ctx i c).Nonempty := by
  refine ⟨(routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i).max' hne, ?_⟩
  unfold emcFibreExitSet
  rw [Finset.mem_filter]
  refine ⟨Finset.max'_mem _ hne, ?_⟩
  intro hmem
  have hle := Finset.le_max' _ _ hmem
  omega

/-- The fibre's reach sits inside the global reach range. -/
theorem emcFibreReach_subset (ctx : ActualFailureContext) (i : Fin 7) :
    emcFibreReach ctx i ⊆ emReach ctx := by
  intro j hj
  unfold emcFibreReach at hj
  rw [Finset.mem_biUnion] at hj
  obtain ⟨k, hk, hjk⟩ := hj
  rw [Finset.mem_Ico] at hjk
  have hks : k ∈ ctx.n24CarryData.starts :=
    (mem_highExcessStarts.mp
      ((mem_routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i k).mp hk).1).1
  rw [cnlMulti_starts_eq_window, Finset.mem_Ico] at hks
  unfold emReach emF emW
  rw [Finset.mem_Ico]
  omega

/-- The fibre-restricted exit mass is a part of the total exit mass. -/
theorem emcFibreExitMass_le_total (ctx : ActualFailureContext) (i : Fin 7) :
    emcFibreExitMass ctx i ≤ emExitMass ctx := by
  unfold emcFibreExitMass emExitMass
  exact Finset.sum_le_sum_of_subset (emcFibreReach_subset ctx i)

/-- **The spaced event-counting bound (any class)**: a `c`-spaced fibre's deviation
content telescopes to `⌈(r+1)/c⌉ = (r+c)/c` copies of its OWN restricted exit
mass — the exact block decomposition `agc_spaced_windowSum_le`, restricted to the
fibre's reach. -/
theorem emc2_fibreDevMass_le_overlap (ctx : ActualFailureContext) (i : Fin 7)
    {c : ℕ} (hc : 1 ≤ c)
    (hspace : ∀ x ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i,
      ∀ z ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i,
        x ≤ z → c ∣ z - x) :
    emcFibreDevMass ctx i
      ≤ ((ctx.n24CarryData.r + c) / c) * emcFibreExitMass ctx i := by
  unfold emcFibreDevMass emcFibreExitMass emDevWindow
  refine agc_spaced_windowSum_le (emExitWeight ctx) hc hspace ?_
  intro k hk j hj
  unfold emcFibreReach
  rw [Finset.mem_biUnion]
  exact ⟨k, hk, Finset.mem_Ico.mpr ⟨Nat.le_add_right _ _, by omega⟩⟩

/-- The class mass sits below the fibre's deviation content (band `≤ 4`) — the
in-tree `agcClassMass_le_sum_devWindow`, in the named shape. -/
theorem emc2_classMass_le_fibreDevMass (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4) (i : Fin 7) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) i
      ≤ ((emcFibreDevMass ctx i : ℕ) : ℝ) := by
  unfold emcFibreDevMass
  exact agcClassMass_le_sum_devWindow ctx hband i

/-! ## Part 3.  The master conditional cap and the forced proportionality
threshold -/

/-- **THE PROPORTIONALITY RESIDUAL (the minimal named datum)**: for class `i`, a
period `c ≥ 1` with (i) the fibre `c`-spacing, (ii) the per-class exit SHARE
`c·(fibre exit mass) ≤ b·(total exit mass)` — the word shadow of "the band-`c`
residues are `b_c` out of `c` per cycle pass" — and (iii) the numeric regime
charging `⌈(r+1)/c⌉` overlap copies of the `b/c` share of the reach-span ceiling
against the corrected capacity. -/
def EmcSpacedShareDatum (ctx : ActualFailureContext) (i : Fin 7) (b c : ℕ) : Prop :=
  1 ≤ c
  ∧ (∀ x ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i,
      ∀ z ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i,
        x ≤ z → c ∣ z - x)
  ∧ c * emcFibreExitMass ctx i ≤ b * emExitMass ctx
  ∧ 1536 * (((ctx.n24CarryData.r + c) / c)
        * (b * ((emW ctx + ctx.n24CarryData.r)
            * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))))
      ≤ 31 * (c * ctx.shell.X)

/-- The pure ℕ chain of the master cap. -/
theorem emc2_nat_chain {dev fex ex S X ov b c : ℕ} (hc : 1 ≤ c)
    (hdev : dev ≤ ov * fex) (hshare : c * fex ≤ b * ex) (hspan : ex ≤ S)
    (hnum : 1536 * (ov * (b * S)) ≤ 31 * (c * X)) :
    1536 * dev ≤ 31 * X := by
  have h5 : c * dev ≤ ov * (b * S) := by
    calc c * dev ≤ c * (ov * fex) := Nat.mul_le_mul le_rfl hdev
      _ = ov * (c * fex) := by ring
      _ ≤ ov * (b * ex) := Nat.mul_le_mul le_rfl hshare
      _ ≤ ov * (b * S) := Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hspan)
  have h6 : 1536 * (c * dev) ≤ 31 * (c * X) :=
    le_trans (Nat.mul_le_mul le_rfl h5) hnum
  have h7 : c * (1536 * dev) ≤ c * (31 * X) := by
    calc c * (1536 * dev) = 1536 * (c * dev) := by ring
      _ ≤ 31 * (c * X) := h6
      _ = c * (31 * X) := by ring
  exact Nat.le_of_mul_le_mul_left h7 (by omega)

/-- **THE MASTER CONDITIONAL CAP** (the off-pin charge bound, exact in-tree
constants): band `≤ 4` + the spaced-share datum give the corrected per-class cap
`mass_i ≤ (31/1536)·X` — the exact demand of `ExitMassControlOffPin` /
`ExitMassControlCore` at class `i`. -/
theorem emc2_cap_of_spacedShare (ctx : ActualFailureContext) (i : Fin 7)
    {b c : ℕ} (hband : fixedFamilyRecurrentBand ctx ≤ 4)
    (h : EmcSpacedShareDatum ctx i b c) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) i ≤ emcCap ctx := by
  obtain ⟨hc, hspace, hshare, hnum⟩ := h
  have hov := emc2_fibreDevMass_le_overlap ctx i hc hspace
  have hspan : emExitMass ctx
      ≤ (emW ctx + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) :=
    em_exitMass_le_reach_span ctx
  have hnat : 1536 * emcFibreDevMass ctx i ≤ 31 * ctx.shell.X :=
    emc2_nat_chain hc hov hshare hspan hnum
  have hdev := emc2_classMass_le_fibreDevMass ctx hband i
  have hcast : (1536 : ℝ) * ((emcFibreDevMass ctx i : ℕ) : ℝ)
      ≤ 31 * (ctx.shell.X : ℝ) := by exact_mod_cast hnat
  unfold emcCap
  linarith

/-- The pure ℕ threshold extraction. -/
theorem emc2_nat_threshold {ov b c S X : ℕ} (hS : 1 ≤ S) (hX : X ≤ 2 * S)
    (hnum : 1536 * (ov * (b * S)) ≤ 31 * (c * X)) :
    768 * (ov * b) ≤ 31 * c := by
  have h2 : 31 * (c * X) ≤ 31 * (c * (2 * S)) :=
    Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hX)
  have h4 : (1536 * (ov * b)) * S ≤ (62 * c) * S := by
    calc (1536 * (ov * b)) * S = 1536 * (ov * (b * S)) := by ring
      _ ≤ 31 * (c * (2 * S)) := le_trans hnum h2
      _ = (62 * c) * S := by ring
  have h5 : 1536 * (ov * b) ≤ 62 * c := Nat.le_of_mul_le_mul_right h4 (by omega)
  have h6 : 2 * (768 * (ov * b)) ≤ 2 * (31 * c) := by
    calc 2 * (768 * (ov * b)) = 1536 * (ov * b) := by ring
      _ ≤ 62 * c := h5
      _ = 2 * (31 * c) := by ring
  exact Nat.le_of_mul_le_mul_left h6 (by omega)

/-- **THE NUMERIC REGIME IS SELF-LIMITING**: against the unconditional support
floor `X ≤ 2(W+r)(L+B+1)` (`fde_W_floor`), the spaced-share datum FORCES the
overlap-weighted proportionality threshold `768·((r+c)/c)·b ≤ 31·c`. -/
theorem emc2_spacedShare_forces_threshold (ctx : ActualFailureContext) (i : Fin 7)
    {b c : ℕ} (h : EmcSpacedShareDatum ctx i b c) :
    768 * (((ctx.n24CarryData.r + c) / c) * b) ≤ 31 * c := by
  obtain ⟨hc, _, _, hnum⟩ := h
  have hS1 : 1 ≤ (emW ctx + ctx.n24CarryData.r)
      * (shellLadderDepth ctx + carryB ctx.shell.Q + 1) := by
    have h1 : 1 ≤ emW ctx := by
      simpa [emW] using fde_supportShell_card_pos ctx
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hXS : ctx.shell.X
      ≤ 2 * ((emW ctx + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) := by
    simpa [emW] using fde_W_floor ctx
  exact emc2_nat_threshold hS1 hXS hnum

/-- **The absolute proportionality threshold**: any spaced-share datum forces
`768·b ≤ 31·c`, i.e. `c/b ≥ 768/31 ≈ 24.8` — the exact event-counting share the
manuscript's proportional distribution must beat. -/
theorem emc2_spacedShare_forces_absolute (ctx : ActualFailureContext) (i : Fin 7)
    {b c : ℕ} (h : EmcSpacedShareDatum ctx i b c) :
    768 * b ≤ 31 * c := by
  have ht := emc2_spacedShare_forces_threshold ctx i h
  obtain ⟨hc, _, _, _⟩ := h
  have hov : 1 ≤ (ctx.n24CarryData.r + c) / c :=
    (Nat.one_le_div_iff (by omega)).mpr (by omega)
  have h1 : 1 * b ≤ ((ctx.n24CarryData.r + c) / c) * b :=
    Nat.mul_le_mul hov le_rfl
  rw [one_mul] at h1
  exact le_trans (Nat.mul_le_mul le_rfl h1) ht

/-! ## Part 4.  The deep regime and the certified `(c, b₄)` table -/

/-- **The deep descent-order floor**: `2^986891 < X` forces `L ≥ 986892`, hence
`r = ⌊κL⌋ ≥ ⌊17·986892/2^18⌋ = 63`. -/
theorem emc2_deep_r_floor (ctx : ActualFailureContext)
    (hX : 2 ^ 986891 < ctx.X) : 63 ≤ ctx.n24CarryData.r := by
  have hXeq : ctx.shell.X = 2 ^ shellLadderDepth ctx := scc_X_pow ctx
  rw [ActualFailureContext.shell_X] at hXeq
  rw [hXeq] at hX
  have hL : 986892 ≤ shellLadderDepth ctx := by
    have h := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hX
    omega
  rw [scc_r_eq_floor]
  apply Nat.le_floor
  rw [towerKappa_eq]
  have hLr : (986892 : ℝ) ≤ ((shellLadderDepth ctx : ℕ) : ℝ) := by exact_mod_cast hL
  have h63 : (63 : ℝ) ≤ 17 / 262144 * 986892 := by norm_num
  nlinarith [hLr, h63]

/-- **The deep proportionality threshold**: at deep scales (`r ≥ 63`) the forced
threshold sharpens to `768·((63+c)/c)·b ≤ 31·c`. -/
theorem emc2_deep_spacedShare_threshold (ctx : ActualFailureContext) (i : Fin 7)
    {b c : ℕ} (hX : 2 ^ 986891 < ctx.X) (h : EmcSpacedShareDatum ctx i b c) :
    768 * (((63 + c) / c) * b) ≤ 31 * c := by
  have ht := emc2_spacedShare_forces_threshold ctx i h
  have hr := emc2_deep_r_floor ctx hX
  have hdiv : (63 + c) / c ≤ (ctx.n24CarryData.r + c) / c :=
    Nat.div_le_div_right (by omega)
  have h1 : ((63 + c) / c) * b ≤ ((ctx.n24CarryData.r + c) / c) * b :=
    Nat.mul_le_mul hdiv le_rfl
  exact le_trans (Nat.mul_le_mul le_rfl h1) ht

/-- The certified rows clearing the ABSOLUTE proportionality threshold
`768·b₄ ≤ 31·c` (row shape `(q, K₀, c, b₄, T)`). -/
def emcProportionalClearedPairs : List (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  sreClass1ThresholdTable.filter (fun e => 768 * e.2.2.2.1 ≤ 31 * e.2.2.1)

/-- **THE EIGHT CLEARED PAIRS**: exactly the deep periods with `c/b₄ ≥ 24.8` —
periods 25, 28, 29 with `b₄ = 1` and period 54 with `b₄ = 2`. -/
theorem emcProportionalClearedPairs_eq :
    emcProportionalClearedPairs
      = [(103, 51, 28, 1, 17270663), (115, 11, 25, 1, 15420235),
         (115, 57, 25, 1, 15420235), (143, 6, 25, 1, 15420235),
         (175, 2, 29, 1, 17887472), (177, 1, 29, 1, 17887472),
         (177, 88, 29, 1, 17887472), (191, 95, 54, 2, 16653854)] := by rfl

/-- The certified rows clearing the DEEP threshold `768·((63+c)/c)·b₄ ≤ 31·c`. -/
def emcDeepProportionalClearedPairs : List (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  sreClass1ThresholdTable.filter
    (fun e => 768 * (((63 + e.2.2.1) / e.2.2.1) * e.2.2.2.1) ≤ 31 * e.2.2.1)

/-- **NO CERTIFIED PAIR SURVIVES THE DEEP THRESHOLD**: with the deep overlap floor
`r ≥ 63`, every certified `(c, b₄)` row overshoots — the largest `b₄ = 1` period
is 29 (needs `c ≥ 64` at `ov = 1`), and every `c ≥ 64` row has `b₄ ≥ 4`. -/
theorem emcDeepProportionalClearedPairs_eq_nil :
    emcDeepProportionalClearedPairs = [] := by rfl

/-- A certified row clearing the deep threshold is a contradiction — the list-level
obstruction, per row. -/
theorem emc2_deep_certified_pair_obstruction {e : ℕ × ℕ × ℕ × ℕ × ℕ}
    (he : e ∈ sreClass1ThresholdTable)
    (hcl : 768 * (((63 + e.2.2.1) / e.2.2.1) * e.2.2.2.1) ≤ 31 * e.2.2.1) :
    False := by
  have hmem : e ∈ emcDeepProportionalClearedPairs := by
    unfold emcDeepProportionalClearedPairs
    rw [List.mem_filter]
    exact ⟨he, decide_eq_true hcl⟩
  rw [emcDeepProportionalClearedPairs_eq_nil] at hmem
  simp at hmem

/-- **THE DEEP TABLE OBSTRUCTION (ctx form)**: at a deep context, NO spaced-share
datum can run on a certified `(c, b₄)` row — the regime is satisfiable only at
UNCERTIFIED parameters (e.g. `b = 1` with period `c ≥ 64`). -/
theorem emc2_deep_spacedShare_not_certified (ctx : ActualFailureContext)
    (i : Fin 7) {b c : ℕ} (hX : 2 ^ 986891 < ctx.X)
    (h : EmcSpacedShareDatum ctx i b c) {q K T : ℕ}
    (he : (q, K, c, b, T) ∈ sreClass1ThresholdTable) : False :=
  emc2_deep_certified_pair_obstruction he
    (emc2_deep_spacedShare_threshold ctx i hX h)

/-! ## Part 5.  Wiring: the regime'd off-pin core in the v19 shapes -/

/-- **The regime'd off-pin demand**: at every deep pin-free context, the recurrent
band is `≤ 4` and each recurrent class (3, 4, 5) carries a spaced-share datum. -/
def EmcOffPinSpacedShareRegime : Prop :=
  ∀ ctx : ActualFailureContext, 2 ^ 986891 < ctx.X →
    ¬ OrbitBandPinned ctx 2 → ¬ OrbitBandPinned ctx 3 → ¬ OrbitBandPinned ctx 4 →
    fixedFamilyRecurrentBand ctx ≤ 4
      ∧ (∃ b c : ℕ, EmcSpacedShareDatum ctx 3 b c)
      ∧ (∃ b c : ℕ, EmcSpacedShareDatum ctx 4 b c)
      ∧ (∃ b c : ℕ, EmcSpacedShareDatum ctx 5 b c)

/-- The regime supplies the wave-19 pin-free conjunct `ExitMassControlOffPin`. -/
theorem emc2_offPin_of_regime (h : EmcOffPinSpacedShareRegime) :
    ExitMassControlOffPin := by
  intro ctx hX h2 h3 h4
  obtain ⟨hband, ⟨b3, c3, hd3⟩, ⟨b4, c4, hd4⟩, ⟨b5, c5, hd5⟩⟩ := h ctx hX h2 h3 h4
  exact ⟨emc2_cap_of_spacedShare ctx 3 hband hd3,
    emc2_cap_of_spacedShare ctx 4 hband hd4,
    emc2_cap_of_spacedShare ctx 5 hband hd5⟩

/-- **The core from the regime + the open axis**: through the wave-19 split
`exitMassControl_iff_split`, the regime'd off-pin demand and the deep orbit-pin
voiding rebuild the FULL `ExitMassControlCore`. -/
theorem emc2_core_of_regime_and_voiding (h : EmcOffPinSpacedShareRegime)
    (hvoid : DeepOrbitPinVoiding) : ExitMassControlCore :=
  exitMassControl_iff_split.mpr ⟨hvoid, emc2_offPin_of_regime h⟩

/-- The regime + the axis supply the wave-8 deep axis `DeepFixedFamilyVoid`. -/
theorem emc2_deepFixedFamilyVoid_of_regime_and_voiding
    (h : EmcOffPinSpacedShareRegime) (hvoid : DeepOrbitPinVoiding) :
    DeepFixedFamilyVoid :=
  deepFixedFamilyVoid_of_exitMassControl (emc2_core_of_regime_and_voiding h hvoid)

/-- The regime + the axis supply the v17 `returnBand2Void` field. -/
theorem emc2_returnBand2Void_of_regime_and_voiding
    (h : EmcOffPinSpacedShareRegime) (hvoid : DeepOrbitPinVoiding) :
    ∀ ctx : ActualFailureContext, ¬ OrbitBandPinned ctx 2 :=
  returnBand2Void_of_exitMassControl (emc2_core_of_regime_and_voiding h hvoid)

/-- The regime + the axis supply the v17 `densePackBand3Void` field. -/
theorem emc2_densePackBand3Void_of_regime_and_voiding
    (h : EmcOffPinSpacedShareRegime) (hvoid : DeepOrbitPinVoiding) :
    ∀ ctx : ActualFailureContext, ¬ Band3PinnedWide ctx :=
  densePackBand3Void_of_exitMassControl (emc2_core_of_regime_and_voiding h hvoid)

/-- The regime + the axis supply the v17 `runBand4Void` field. -/
theorem emc2_runBand4Void_of_regime_and_voiding
    (h : EmcOffPinSpacedShareRegime) (hvoid : DeepOrbitPinVoiding) :
    ∀ ctx : ActualFailureContext, ¬ OrbitBandPinned ctx 4 :=
  runBand4Void_of_exitMassControl (emc2_core_of_regime_and_voiding h hvoid)

/-! ## Part 6.  Honest machine-readable status -/

/-- Machine-readable, honest status of the exit-mass core transcription pass. -/
def exitMassCoreTranscriptionStatus : List String :=
  [ "TELESCOPING VERDICT (PROVED): the in-tree corrected mass routedClassMassOf " ++
      "is START-indexed - a sum of FULL window excesses over the class fibre.  " ++
      "The per-step drift atom IS provable: consecutive starts' windows differ " ++
      "by boundary gaps only (emcT_gapWindow_shift), so the excess difference " ++
      "under a shift s+1 is <= the s+1 boundary gaps (emcT_windowExcess_drift " ++
      "/ _rev), <= (s+1)*(L+B+1) on the reach (emcT_drift_le_reach) - NOT the " ++
      "full window.  But the run SUM accumulates the drift QUADRATICALLY " ++
      "(emcT_run_telescope: m*entry + m(m-1)/2*D); the manuscript's linear " ++
      "'entry + m*drift' bounds only the LAST member (emcT_run_member_le).  " ++
      "The start-indexed mass does NOT realize the I.3 in-cycle-uncharged " ++
      "linear ledger; the supported form is EVENT-COUNTING.",
    "EVENT-COUNTING FORM (PROVED): entry/exit event sets of a class fibre under " ++
      "the step map k -> k+c (emcFibreEntrySet/emcFibreExitSet, nonempty when " ++
      "the fibre is - every maximal run has a first entry and a first exit); " ++
      "the c-spaced fibre's deviation content telescopes to ceil((r+1)/c) = " ++
      "(r+c)/c copies of its OWN restricted exit mass " ++
      "(emc2_fibreDevMass_le_overlap via agc_spaced_windowSum_le), and the " ++
      "class mass sits below the fibre deviation content at band <= 4 " ++
      "(emc2_classMass_le_fibreDevMass).",
    "THE MASTER CONDITIONAL CAP (PROVED, exact in-tree constants - " ++
      "emc2_cap_of_spacedShare): band <= 4 + c-spacing + the per-class exit " ++
      "share c*fibreExitMass <= b*emExitMass + the numeric regime " ++
      "1536*((r+c)/c)*b*(W+r)*(L+B+1) <= 31*c*X  ==>  the corrected cap " ++
      "mass_i <= (31/1536)*X - the exact ExitMassControlOffPin demand at " ++
      "class i.  The reach-span ceiling em_exitMass_le_reach_span supplies " ++
      "the (W+r)(L+B+1) budget.",
    "REGIMES CLEARED: NONE UNCONDITIONALLY - the regime is SELF-LIMITING.  " ++
      "Against the unconditional support floor X <= 2(W+r)(L+B+1) " ++
      "(fde_W_floor) the numeric regime FORCES 768*((r+c)/c)*b <= 31*c " ++
      "(emc2_spacedShare_forces_threshold), hence the absolute " ++
      "proportionality threshold 768*b <= 31*c, c/b >= 768/31 ~ 24.8 " ++
      "(emc2_spacedShare_forces_absolute) - the SAME 24.8 factor as the " ++
      "wave-18 deviation-floor verdict.",
    "THE PROPORTIONALITY RESIDUAL (exact form): EmcSpacedShareDatum - the " ++
      "share c*fibreExit <= b*totalExit is the word shadow of 'band-c " ++
      "residues are b_c out of c per cycle pass'.  NO in-tree " ++
      "equidistribution atom exists (grepped: none); the share is the " ++
      "genuinely open input.  Against the certified (c,b4) table " ++
      "(sreClass1ThresholdTable, 110 rows): EXACTLY EIGHT pairs clear the " ++
      "absolute threshold 768*b4 <= 31*c (emcProportionalClearedPairs_eq): " ++
      "(103,51) c=28, (115,11)/(115,57)/(143,6) c=25, " ++
      "(175,2)/(177,1)/(177,88) c=29 (all b4=1), (191,95) c=54 b4=2.",
    "THE DEEP VERDICT (PROVED): 2^986891 < X forces L >= 986892 and r = " ++
      "floor(17L/2^18) >= 63 (emc2_deep_r_floor), sharpening the forced " ++
      "threshold to 768*((63+c)/c)*b <= 31*c " ++
      "(emc2_deep_spacedShare_threshold).  NO certified row satisfies it " ++
      "(emcDeepProportionalClearedPairs_eq_nil): the eight cleared pairs " ++
      "have c <= 54 < 63 so overlap >= 2 and need 1536*b <= 31*c (best " ++
      "31*54 = 1674 < 3072); the large periods c >= 64 all carry b4 >= 4.  " ++
      "Hence emc2_deep_spacedShare_not_certified: at deep contexts the " ++
      "spaced-share regime can run only at UNCERTIFIED parameters - e.g. " ++
      "b = 1 with period c >= 64 (a fully exit-light long cycle), which no " ++
      "certified pair provides.  The off-pin core is NOT provable on any " ++
      "certified-pair regime through this budget.",
    "WIRING (PROVED, v19 shapes): EmcOffPinSpacedShareRegime ==> " ++
      "ExitMassControlOffPin (emc2_offPin_of_regime); + DeepOrbitPinVoiding " ++
      "==> the FULL ExitMassControlCore through exitMassControl_iff_split " ++
      "(emc2_core_of_regime_and_voiding) ==> DeepFixedFamilyVoid and the " ++
      "three v17 voiding fields (emc2_deepFixedFamilyVoid / " ++
      "emc2_returnBand2Void / emc2_densePackBand3Void / emc2_runBand4Void " ++
      "_of_regime_and_voiding).",
    "HYGIENE: additive only - ONE new module, no existing file edited, root " ++
      "import untouched; no sorry / admit / new axiom / native_decide; every " ++
      "key declaration passes #print axioms within [propext, " ++
      "Classical.choice, Quot.sound]." ]

/-- The status ledger is non-empty (honest, non-vacuous). -/
theorem exitMassCoreTranscriptionStatus_nonempty :
    exitMassCoreTranscriptionStatus ≠ [] := by
  simp [exitMassCoreTranscriptionStatus]

/-! ## Part 7.  Axiom-cleanliness audit
Every key declaration; expected axioms `[propext, Classical.choice, Quot.sound]`
or fewer. -/

#print axioms emcT_gapWindow_shift
#print axioms emcT_positivePart_add_le
#print axioms emcT_windowExcess_drift
#print axioms emcT_windowExcess_drift_rev
#print axioms emcT_drift_le_reach
#print axioms emcT_run_member_le
#print axioms emcT_run_telescope
#print axioms emcFibreEntrySet_nonempty
#print axioms emcFibreExitSet_nonempty
#print axioms emcFibreReach_subset
#print axioms emcFibreExitMass_le_total
#print axioms emc2_fibreDevMass_le_overlap
#print axioms emc2_classMass_le_fibreDevMass
#print axioms emc2_nat_chain
#print axioms emc2_cap_of_spacedShare
#print axioms emc2_nat_threshold
#print axioms emc2_spacedShare_forces_threshold
#print axioms emc2_spacedShare_forces_absolute
#print axioms emc2_deep_r_floor
#print axioms emc2_deep_spacedShare_threshold
#print axioms emcProportionalClearedPairs_eq
#print axioms emcDeepProportionalClearedPairs_eq_nil
#print axioms emc2_deep_certified_pair_obstruction
#print axioms emc2_deep_spacedShare_not_certified
#print axioms emc2_offPin_of_regime
#print axioms emc2_core_of_regime_and_voiding
#print axioms emc2_deepFixedFamilyVoid_of_regime_and_voiding
#print axioms emc2_returnBand2Void_of_regime_and_voiding
#print axioms emc2_densePackBand3Void_of_regime_and_voiding
#print axioms emc2_runBand4Void_of_regime_and_voiding
#print axioms exitMassCoreTranscriptionStatus_nonempty

end

end Erdos260
