import Erdos260.MissDistanceClosure
import Erdos260.ExitMassCoreTranscription

/-!
# The unified exit-mass family closure (`ExitMassFamilyClosure`)

This module (NEW; it edits no existing file) unifies the per-class fibre-restricted
exit-mass caps — the class-0 atom `MdcClass0ExitMassControl` and the class-3/4/5
spaced-share regime `EmcOffPinSpacedShareRegime` — into ONE family, and settles the
brief's KEY QUESTION about the exit-residue structure.

## (c) The `emcFibreExitMass` definition verdict: MULTIPLICITY-FREE

`emcFibreExitMass ctx i = Σ_{j ∈ emcFibreReach ctx i} emExitWeight ctx j` where
`emcFibreReach` is a `Finset.biUnion` — the UNION of the fibre members' windows.
Each exit index is counted ONCE no matter how many class-`i` windows contain it
(`emfc_fibreExitMass_le_total` re-proves the part-of-total bound).  The class-0
quantity is the SAME object: `mdcClass0ExitMass = emcFibreExitMass · 0`
(`emfc_class0ExitMass_eq_fibreExitMass`) — the family is genuinely unified.

## The share statement's TRUE status: a coverage obstruction (PROVED)

Because the fibre exit mass is the union mass, the share
`c·fibreExit ≤ b·totalExit` of `EmcSpacedShareDatum` interacts with window
coverage exactly as the brief feared:

* every spaced-share datum FORCES the exit-light cap
  `768·fibreExit ≤ 31·totalExit` (`emfc_spacedShare_forces_exitLight`, through
  the forced absolute threshold `768·b ≤ 31·c`) — the class windows may see at
  most a `31/768 ≈ 4%` fraction of the exit mass;
* hence the datum is INCOMPATIBLE with exit coverage: if the class-`i` window
  union contained the whole exit set, the share would force
  `768·E ≤ 31·E` with `E ≥ 1` — `False` (`emfc_spacedShare_not_covering`);
  every datum produces an exit index OUTSIDE the class reach
  (`emfc_spacedShare_misses_exit`).  Since survivor periods `c ≤ 18 ≪ r+1`
  make consecutive same-class windows overlap heavily, the share is NOT the
  innocuous equidistribution statement it reads as — it is an exit-AVOIDANCE
  demand on the class windows.  The named minimal necessary atom is
  `EmfcFibreExitLight` (`768·fibreExit ≤ 31·totalExit`), itself already strong
  enough to force a missed exit at band ≤ 4 (`emfc_exitLight_misses_exit`).

## (d) The binary-classification-improved drift bound

The binary gap-deviation classification (non-exit gaps deviate EXACTLY 0,
`mdc_nonExit_weight_eq_zero`) improves the wave-20 drift calculus: the boundary
gaps of a window shift split into band-followers (≤ 4 each) and exits (their
exit weight), so at band ≤ 4 the per-step drift is
`≤ 4·(s+1) + (exit weight in the s+1 boundary gaps)`
(`emfc_windowExcess_drift_binary`) instead of the generic `(s+1)·(L+B+1)` —
an exit-free boundary block drifts by `≤ 4·(s+1)` TOTAL
(`emfc_windowExcess_drift_exitFree`), a factor `~L/4` better.  Iterating with
DISJOINT consecutive boundary blocks, the `j`-th run member's excess is
`≤ entry + 4·j·c + (exit mass in the j·c-gap span, counted ONCE)`
(`emfc_run_member_le_binary`), and the run SUM obeys
`Σ ≤ m·entry + 2c·m(m−1) + m·(span exit mass)` (`emfc_run_sum_binary`) — the
band part now accumulates only `2c·m²` (vs `c·m²·(L+B+1)/2` generic), but the
exit part still multiplies by `m` and the entry term is floored:
`mass_i ≥ #fibre·Y` (`emfc_classMass_ge_card_Y`, `Y = L/64`).

REGIMES CLEARED: NONE unconditionally.  The `m·entry ≥ m·Y` floor means the
drift route can never undercut the count-shaped route, whose dead zone
(`emc_countTimesY_lt_cap`) already covers `L ≤ 1274739`; at deeper `L` the exit
term `m·(span exit mass)` meets the same `X/2` exit floor that refuted the
unrestricted budget.  The honest content of the binary improvement is the
per-member bound and the exit-light necessity above.

## (e) The class-0 reduction (one-way, with the converse obstruction located)

* `Class0WindowCycleCheck ctx ⟺ fibre₀ = ∅` (`emfc_class0FibreEmpty_iff_windowCheck`,
  chaining the in-tree pinned bridges) — the wave-16 windowed check IS per-context
  class-0 fibre emptiness;
* emptiness gives the atom for free: empty fibre ⇒ empty reach ⇒
  `mdcClass0ExitMass = 0` (`emfc_class0ExitMass_eq_zero_of_empty`) ⇒ the
  survivor cap holds (`emfc_class0Atom_of_windowCheck`); windowed checks on all
  survivor pairs supply the FULL `MdcClass0ExitMassControl`
  (`emfc_class0Control_of_windowChecks`);
* the reduction is strictly one-way: the atom does NOT force emptiness — but it
  DOES force structure: at band ≤ 4 the atom's inequality forces an exit index
  outside the class-0 reach (`emfc_class0Atom_misses_exit`, via the proved
  refutation of the unrestricted form).  TABLE VERDICT: NO survivor certificate
  discharges the windowed check in-tree — all nineteen survivor pairs defeat the
  window-free cycle check (`class0_datum_survivor_defeats_cycleCheck`), so the
  emptiness route is open at every survivor; it remains the cheapest sufficient
  input.

## (f) Wiring (additive, the v19/v20 shapes)

`EmfcUnifiedExitMassFamily` = `MdcClass0ExitMassControl ∧ EmcOffPinSpacedShareRegime`
supplies: the survivor class-0 mass row (`emfc_family_class0Row`),
`ExitMassControlOffPin` (`emfc_family_offPin`), and with `DeepOrbitPinVoiding`
the full `ExitMassControlCore` and `DeepFixedFamilyVoid`
(`emfc_family_core`, `emfc_family_deepVoid`).  The family's necessary shadow
is proved: on every deep pin-free context the regime forces all three recurrent
classes exit-light (`emfc_regime_forces_exitLight`) with a missed exit per class
(`emfc_regime_misses_exits`).

No `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## Part 0.  The unified family: the class-0 mass IS the `i = 0` instance -/

/-- **The reach unification**: the class-0 window union of `MissDistanceClosure` is
the `i = 0` instance of the per-class fibre reach of `ExitMassCoreTranscription`
(the window bounds differ only by `Nat` associativity). -/
theorem emfc_class0Reach_eq_fibreReach (ctx : ActualFailureContext) :
    mdcClass0Reach ctx = emcFibreReach ctx 0 := by
  unfold mdcClass0Reach emcFibreReach
  refine Finset.biUnion_congr rfl ?_
  intro k _
  rw [Nat.add_assoc]

/-- **The mass unification**: `mdcClass0ExitMass` is `emcFibreExitMass · 0` — the
class-0 atom caps the SAME multiplicity-free union quantity as the class-3/4/5
family. -/
theorem emfc_class0ExitMass_eq_fibreExitMass (ctx : ActualFailureContext) :
    mdcClass0ExitMass ctx = emcFibreExitMass ctx 0 := by
  unfold mdcClass0ExitMass emcFibreExitMass
  rw [emfc_class0Reach_eq_fibreReach]

/-- **The multiplicity verdict, usable form (any class)**: each member's window
deviation content sits below the fibre exit mass — because the fibre exit mass is
the UNION mass, one member's window is a subset.  (The multiplicity-free
definition is what makes this true; a with-multiplicity sum would only dominate
the member through its own copy.) -/
theorem emfc_devWindow_le_fibreExitMass (ctx : ActualFailureContext) (i : Fin 7)
    {k : ℕ} (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i) :
    emDevWindow ctx k ≤ emcFibreExitMass ctx i := by
  unfold emDevWindow emcFibreExitMass
  rw [show (∑ t ∈ Finset.range (ctx.n24CarryData.r + 1), emExitWeight ctx (k + t))
      = ∑ j ∈ (Finset.range (ctx.n24CarryData.r + 1)).image (fun t => k + t),
          emExitWeight ctx j from (Finset.sum_image (fun x _ y _ h => by omega)).symm]
  refine Finset.sum_le_sum_of_subset ?_
  intro j hj
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hj
  rw [Finset.mem_range] at ht
  exact Finset.mem_biUnion.mpr
    ⟨k, hk, Finset.mem_Ico.mpr ⟨Nat.le_add_right _ _, by omega⟩⟩

/-- The fibre exit mass is a share of the total (re-derivation at the family level;
the union reach sits inside the global reach). -/
theorem emfc_fibreExitMass_le_total (ctx : ActualFailureContext) (i : Fin 7) :
    emcFibreExitMass ctx i ≤ emExitMass ctx :=
  emcFibreExitMass_le_total ctx i

/-! ## Part 1.  The coverage obstruction: the share's true status

The share `c·fibreExit ≤ b·totalExit` reads as equidistribution but is in fact an
exit-AVOIDANCE demand: the forced threshold `768·b ≤ 31·c` turns it into the
exit-light cap `768·fibreExit ≤ 31·totalExit`, which is incompatible with the
class windows covering the exit set. -/

/-- The total exit mass is positive at every band-`≤ 4` context (the relocated
Lemma 21.1 floor `X ≤ 2·emExitMass` against `X ≥ 1`). -/
theorem emfc_exitMass_pos (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4) : 0 < emExitMass ctx := by
  have h1 := em_exitMass_lower_of_band ctx hband
  have h2 := agcX_ge_one ctx
  omega

/-- The exit mass is carried entirely by the exit SET (weights vanish on
band-followers — the binary classification). -/
theorem emfc_exitMass_eq_sum_exitSet_weight (ctx : ActualFailureContext) :
    emExitMass ctx = ∑ j ∈ emExitSet ctx, emExitWeight ctx j := by
  unfold emExitMass emExitSet
  exact (Finset.sum_filter_of_ne (fun j _ h => mdc_exit_of_weight_ne_zero ctx h)).symm

/-- **The coverage comparison**: if the class-`i` window union contains the exit
set, the fibre exit mass IS the total exit mass. -/
theorem emfc_coverage_le (ctx : ActualFailureContext) (i : Fin 7)
    (hcov : emExitSet ctx ⊆ emcFibreReach ctx i) :
    emExitMass ctx ≤ emcFibreExitMass ctx i := by
  rw [emfc_exitMass_eq_sum_exitSet_weight]
  unfold emcFibreExitMass
  exact Finset.sum_le_sum_of_subset hcov

/-- **THE NAMED MINIMAL ATOM**: the class-`i` windows are exit-LIGHT — they carry
at most a `31/768 ≈ 4%` share of the total exit mass.  Every spaced-share datum
forces it (`emfc_spacedShare_forces_exitLight`); it already forces a missed exit
at band ≤ 4 (`emfc_exitLight_misses_exit`). -/
def EmfcFibreExitLight (ctx : ActualFailureContext) (i : Fin 7) : Prop :=
  768 * emcFibreExitMass ctx i ≤ 31 * emExitMass ctx

/-- **Every spaced-share datum forces the exit-light cap**: the share
`c·fibreExit ≤ b·totalExit` against the forced absolute threshold `768·b ≤ 31·c`
gives `768·fibreExit ≤ 31·totalExit` after cancelling `c ≥ 1`. -/
theorem emfc_spacedShare_forces_exitLight (ctx : ActualFailureContext) (i : Fin 7)
    {b c : ℕ} (h : EmcSpacedShareDatum ctx i b c) :
    EmfcFibreExitLight ctx i := by
  have habs := emc2_spacedShare_forces_absolute ctx i h
  obtain ⟨hc, _, hshare, _⟩ := h
  have h1 : 768 * (c * emcFibreExitMass ctx i) ≤ 768 * (b * emExitMass ctx) :=
    Nat.mul_le_mul le_rfl hshare
  have h2 : 768 * (b * emExitMass ctx) ≤ 31 * (c * emExitMass ctx) := by
    calc 768 * (b * emExitMass ctx) = (768 * b) * emExitMass ctx := by ring
      _ ≤ (31 * c) * emExitMass ctx := Nat.mul_le_mul habs le_rfl
      _ = 31 * (c * emExitMass ctx) := by ring
  have h3 : c * (768 * emcFibreExitMass ctx i) ≤ c * (31 * emExitMass ctx) := by
    calc c * (768 * emcFibreExitMass ctx i)
        = 768 * (c * emcFibreExitMass ctx i) := by ring
      _ ≤ 31 * (c * emExitMass ctx) := le_trans h1 h2
      _ = c * (31 * emExitMass ctx) := by ring
  exact Nat.le_of_mul_le_mul_left h3 hc

/-- **The exit-light cap forces a missed exit** (band ≤ 4): the class windows
cannot cover the exit set — some L.3.1 exit lies OUTSIDE every class-`i` member's
window. -/
theorem emfc_exitLight_misses_exit (ctx : ActualFailureContext) (i : Fin 7)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4) (h : EmfcFibreExitLight ctx i) :
    ∃ j ∈ emExitSet ctx, j ∉ emcFibreReach ctx i := by
  by_contra hcon
  have hcov : emExitSet ctx ⊆ emcFibreReach ctx i := by
    intro j hj
    by_contra hnot
    exact hcon ⟨j, hj, hnot⟩
  have h1 := emfc_coverage_le ctx i hcov
  have h2 := emfc_exitMass_pos ctx hband
  unfold EmfcFibreExitLight at h
  omega

/-- **THE SHARE'S TRUE STATUS (the brief's key question, settled)**: every
spaced-share datum produces an exit index outside the class-`i` reach — the share
is an exit-avoidance demand, not an innocuous equidistribution count. -/
theorem emfc_spacedShare_misses_exit (ctx : ActualFailureContext) (i : Fin 7)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4) {b c : ℕ}
    (h : EmcSpacedShareDatum ctx i b c) :
    ∃ j ∈ emExitSet ctx, j ∉ emcFibreReach ctx i :=
  emfc_exitLight_misses_exit ctx i hband (emfc_spacedShare_forces_exitLight ctx i h)

/-- **THE COVERAGE REFUTATION**: a spaced-share datum is INCOMPATIBLE with the
class-`i` windows covering the exit set — if they did, `768·E ≤ 31·E` with
`E ≥ 1` would follow.  (This is the formal answer to "windows overlap across
classes, so the union is everything": wherever the union IS everything, the
share is FALSE.) -/
theorem emfc_spacedShare_not_covering (ctx : ActualFailureContext) (i : Fin 7)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4) {b c : ℕ}
    (h : EmcSpacedShareDatum ctx i b c)
    (hcov : emExitSet ctx ⊆ emcFibreReach ctx i) : False := by
  obtain ⟨j, hj, hnot⟩ := emfc_spacedShare_misses_exit ctx i hband h
  exact hnot (hcov hj)

/-! ## Part 2.  The binary-classification-improved drift calculus

The wave-20 drift bound charges a window shift its boundary gaps at the generic
per-gap ceiling `L+B+1`.  The binary classification (non-exit gaps deviate
EXACTLY 0) splits each boundary gap into band (≤ 4) + exit weight, improving the
per-step drift to `4·(s+1) + local exit mass`. -/

/-- The boundary-gap split: any gap window is at most its band budget plus its
exit content (per-gap binary split `em_hitGap_le_weight_add_band`, summed). -/
theorem emfc_gapWindow_le_band_add_exit (ctx : ActualFailureContext) (k s : ℕ) :
    gapWindow (hitGap ctx.n24CarryData.a) k s
      ≤ (s + 1) * fixedFamilyRecurrentBand ctx
        + ∑ t ∈ Finset.range (s + 1), emExitWeight ctx (k + t) := by
  unfold gapWindow
  calc ∑ t ∈ Finset.range (s + 1), hitGap ctx.n24CarryData.a (k + t)
      ≤ ∑ t ∈ Finset.range (s + 1),
          (emExitWeight ctx (k + t) + fixedFamilyRecurrentBand ctx) :=
        Finset.sum_le_sum (fun t _ => em_hitGap_le_weight_add_band ctx (k + t))
    _ = (∑ t ∈ Finset.range (s + 1), emExitWeight ctx (k + t))
          + (s + 1) * fixedFamilyRecurrentBand ctx := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
    _ = (s + 1) * fixedFamilyRecurrentBand ctx
          + ∑ t ∈ Finset.range (s + 1), emExitWeight ctx (k + t) := by ring

/-- **THE BINARY-IMPROVED PER-STEP DRIFT** (band ≤ 4): shifting the window start
by `s+1` raises the excess by at most `4·(s+1)` PLUS the exit weight of the
`s+1` boundary gaps — non-exit boundary gaps cost ≤ 4 each, not `L+B+1`. -/
theorem emfc_windowExcess_drift_binary (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4) (k r s : ℕ) (T : ℝ) :
    windowExcess (hitGap ctx.n24CarryData.a) (k + (s + 1)) r T
      ≤ windowExcess (hitGap ctx.n24CarryData.a) k r T
        + ((4 * (s + 1)
            + ∑ t ∈ Finset.range (s + 1), emExitWeight ctx (k + r + 1 + t) : ℕ) : ℝ) := by
  have hdrift := emcT_windowExcess_drift (hitGap ctx.n24CarryData.a) k r s T
  have hgap : gapWindow (hitGap ctx.n24CarryData.a) (k + r + 1) s
      ≤ 4 * (s + 1)
        + ∑ t ∈ Finset.range (s + 1), emExitWeight ctx (k + r + 1 + t) := by
    calc gapWindow (hitGap ctx.n24CarryData.a) (k + r + 1) s
        ≤ (s + 1) * fixedFamilyRecurrentBand ctx
            + ∑ t ∈ Finset.range (s + 1), emExitWeight ctx (k + r + 1 + t) :=
          emfc_gapWindow_le_band_add_exit ctx (k + r + 1) s
      _ ≤ (s + 1) * 4
            + ∑ t ∈ Finset.range (s + 1), emExitWeight ctx (k + r + 1 + t) :=
          Nat.add_le_add_right (Nat.mul_le_mul le_rfl hband) _
      _ = 4 * (s + 1)
            + ∑ t ∈ Finset.range (s + 1), emExitWeight ctx (k + r + 1 + t) := by ring
  have hgapR : ((gapWindow (hitGap ctx.n24CarryData.a) (k + r + 1) s : ℕ) : ℝ)
      ≤ ((4 * (s + 1)
          + ∑ t ∈ Finset.range (s + 1), emExitWeight ctx (k + r + 1 + t) : ℕ) : ℝ) := by
    exact_mod_cast hgap
  linarith

/-- **Exit-free boundary blocks drift by `≤ 4·(s+1)` TOTAL** — a factor `~L/4`
below the generic `(s+1)·(L+B+1)` ceiling: clean in-cycle motion is almost
uncharged, exactly the binary classification's promise. -/
theorem emfc_windowExcess_drift_exitFree (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4) (k r s : ℕ) (T : ℝ)
    (hfree : ∀ t, t < s + 1 → emExitWeight ctx (k + r + 1 + t) = 0) :
    windowExcess (hitGap ctx.n24CarryData.a) (k + (s + 1)) r T
      ≤ windowExcess (hitGap ctx.n24CarryData.a) k r T + ((4 * (s + 1) : ℕ) : ℝ) := by
  have h := emfc_windowExcess_drift_binary ctx hband k r s T
  have hz : ∑ t ∈ Finset.range (s + 1), emExitWeight ctx (k + r + 1 + t) = 0 :=
    Finset.sum_eq_zero (fun t ht => hfree t (Finset.mem_range.mp ht))
  rw [hz, Nat.add_zero] at h
  exact h

/-- **The binary run-member bound**: the `j`-th member of a `c`-spaced run pays
`entry + 4·j·c + (exit mass of the j·c-gap span, counted ONCE)` — consecutive
steps' boundary blocks are disjoint and consecutive, so their exit contents
CONCATENATE instead of accumulating. -/
theorem emfc_run_member_le_binary (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4) (k r : ℕ) (T : ℝ) {c : ℕ}
    (hc : 1 ≤ c) :
    ∀ j : ℕ, windowExcess (hitGap ctx.n24CarryData.a) (k + j * c) r T
      ≤ windowExcess (hitGap ctx.n24CarryData.a) k r T
        + ((4 * (j * c)
            + ∑ t ∈ Finset.range (j * c), emExitWeight ctx (k + r + 1 + t) : ℕ) : ℝ) := by
  intro j
  induction j with
  | zero => simp
  | succ n ih =>
      have hstep := emfc_windowExcess_drift_binary ctx hband (k + n * c) r (c - 1) T
      have hc1 : c - 1 + 1 = c := by omega
      rw [hc1] at hstep
      have harg : k + n * c + c = k + (n + 1) * c := by ring
      rw [harg] at hstep
      have hwidx : ∀ t : ℕ, k + n * c + r + 1 + t = k + r + 1 + (n * c + t) := by
        intro t; omega
      simp only [hwidx] at hstep
      have hsum : ∑ t ∈ Finset.range ((n + 1) * c), emExitWeight ctx (k + r + 1 + t)
          = (∑ t ∈ Finset.range (n * c), emExitWeight ctx (k + r + 1 + t))
            + ∑ t ∈ Finset.range c, emExitWeight ctx (k + r + 1 + (n * c + t)) := by
        rw [show (n + 1) * c = n * c + c from by ring]
        exact Finset.sum_range_add (fun t => emExitWeight ctx (k + r + 1 + t)) (n * c) c
      have hcast : ((4 * ((n + 1) * c)
            + ∑ t ∈ Finset.range ((n + 1) * c), emExitWeight ctx (k + r + 1 + t) : ℕ) : ℝ)
          = ((4 * (n * c)
              + ∑ t ∈ Finset.range (n * c), emExitWeight ctx (k + r + 1 + t) : ℕ) : ℝ)
            + ((4 * c
              + ∑ t ∈ Finset.range c,
                  emExitWeight ctx (k + r + 1 + (n * c + t)) : ℕ) : ℝ) := by
        rw [hsum]
        push_cast
        ring
      calc windowExcess (hitGap ctx.n24CarryData.a) (k + (n + 1) * c) r T
          ≤ windowExcess (hitGap ctx.n24CarryData.a) (k + n * c) r T
              + ((4 * c
                + ∑ t ∈ Finset.range c,
                    emExitWeight ctx (k + r + 1 + (n * c + t)) : ℕ) : ℝ) := hstep
        _ ≤ windowExcess (hitGap ctx.n24CarryData.a) k r T
              + ((4 * (n * c)
                  + ∑ t ∈ Finset.range (n * c), emExitWeight ctx (k + r + 1 + t) : ℕ) : ℝ)
              + ((4 * c
                + ∑ t ∈ Finset.range c,
                    emExitWeight ctx (k + r + 1 + (n * c + t)) : ℕ) : ℝ) := by
            linarith [ih]
        _ = windowExcess (hitGap ctx.n24CarryData.a) k r T
              + ((4 * ((n + 1) * c)
                + ∑ t ∈ Finset.range ((n + 1) * c),
                    emExitWeight ctx (k + r + 1 + t) : ℕ) : ℝ) := by
            rw [hcast]
            ring

/-- **The binary run-SUM bound (the best honest per-class drift mass bound)**:
`Σ_{j<m} excess(k+jc) ≤ m·entry + 2c·m(m−1) + m·(span exit mass)` — the band
part accumulates quadratically at constant 4 (vs `L+B+1` generic), the exit part
linearly in the run length against the span's exit mass counted once. -/
theorem emfc_run_sum_binary (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4) (k r : ℕ) (T : ℝ) {c : ℕ}
    (hc : 1 ≤ c) (m : ℕ) :
    ∑ j ∈ Finset.range m, windowExcess (hitGap ctx.n24CarryData.a) (k + j * c) r T
      ≤ (m : ℝ) * windowExcess (hitGap ctx.n24CarryData.a) k r T
        + ((2 * (c * (m * (m - 1)))
            + m * ∑ t ∈ Finset.range (m * c), emExitWeight ctx (k + r + 1 + t) : ℕ) : ℝ) := by
  have hmem := emfc_run_member_le_binary ctx hband k r T hc
  have hjle : ∀ j, j < m →
      4 * (j * c) + ∑ t ∈ Finset.range (j * c), emExitWeight ctx (k + r + 1 + t)
        ≤ 4 * (j * c) + ∑ t ∈ Finset.range (m * c), emExitWeight ctx (k + r + 1 + t) := by
    intro j hj
    refine Nat.add_le_add_left (Finset.sum_le_sum_of_subset ?_) _
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    have hmc : j * c ≤ m * c := Nat.mul_le_mul (le_of_lt hj) le_rfl
    omega
  have hperm : ∀ j ∈ Finset.range m,
      windowExcess (hitGap ctx.n24CarryData.a) (k + j * c) r T
        ≤ windowExcess (hitGap ctx.n24CarryData.a) k r T
          + ((4 * (j * c)
              + ∑ t ∈ Finset.range (m * c), emExitWeight ctx (k + r + 1 + t) : ℕ) : ℝ) := by
    intro j hj
    refine le_trans (hmem j) ?_
    have hcast : ((4 * (j * c)
          + ∑ t ∈ Finset.range (j * c), emExitWeight ctx (k + r + 1 + t) : ℕ) : ℝ)
        ≤ ((4 * (j * c)
          + ∑ t ∈ Finset.range (m * c), emExitWeight ctx (k + r + 1 + t) : ℕ) : ℝ) :=
      Nat.cast_le.mpr (hjle j (Finset.mem_range.mp hj))
    linarith
  have hnat : (∑ j ∈ Finset.range m,
        (4 * (j * c) + ∑ t ∈ Finset.range (m * c), emExitWeight ctx (k + r + 1 + t)))
      = 2 * (c * (m * (m - 1)))
        + m * ∑ t ∈ Finset.range (m * c), emExitWeight ctx (k + r + 1 + t) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
    congr 1
    have h2 := Finset.sum_range_id_mul_two m
    calc ∑ j ∈ Finset.range m, 4 * (j * c)
        = 4 * c * ∑ j ∈ Finset.range m, j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun j _ => by ring)
      _ = 2 * c * ((∑ j ∈ Finset.range m, j) * 2) := by ring
      _ = 2 * (c * (m * (m - 1))) := by rw [h2]; ring
  calc ∑ j ∈ Finset.range m, windowExcess (hitGap ctx.n24CarryData.a) (k + j * c) r T
      ≤ ∑ j ∈ Finset.range m,
          (windowExcess (hitGap ctx.n24CarryData.a) k r T
            + ((4 * (j * c)
                + ∑ t ∈ Finset.range (m * c),
                    emExitWeight ctx (k + r + 1 + t) : ℕ) : ℝ)) :=
        Finset.sum_le_sum hperm
    _ = (m : ℝ) * windowExcess (hitGap ctx.n24CarryData.a) k r T
          + ((∑ j ∈ Finset.range m,
              (4 * (j * c)
                + ∑ t ∈ Finset.range (m * c),
                    emExitWeight ctx (k + r + 1 + t)) : ℕ) : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul, Nat.cast_sum]
    _ = (m : ℝ) * windowExcess (hitGap ctx.n24CarryData.a) k r T
          + ((2 * (c * (m * (m - 1)))
              + m * ∑ t ∈ Finset.range (m * c),
                  emExitWeight ctx (k + r + 1 + t) : ℕ) : ℝ) := by
        rw [hnat]

/-- **The route-blocking floor**: every routed class mass is at least
`#fibre · Y` (`Y = L/64`) — the drift route's `m·entry` term is floored at the
count route's own currency, so no drift bound can undercut the count dead-zone
analysis. -/
theorem emfc_classMass_ge_card_Y (ctx : ActualFailureContext) (i : Fin 7) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) i := by
  rw [routedClassMassOf_eq_sum_fibre]
  calc ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i).card : ℝ)
        * ctx.n24CarryData.Y
      = ∑ _k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i,
          ctx.n24CarryData.Y := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i,
          windowExcess (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r
            ctx.n24CarryData.T :=
        Finset.sum_le_sum (fun k hk =>
          Y_le_windowExcess_of_mem_routedFibre ctx.n24CarryData
            (genuineChargeRoute ctx) i hk)

/-! ## Part 3.  The class-0 specialization: the windowed-check reduction -/

/-- **The wave-16 windowed check IS class-0 fibre emptiness** (per context):
chaining the pinned bridge `class0Fibre_empty_iff_pinned` with the window-residue
bridge `class0Pinned_iff_windowCycleCheck`. -/
theorem emfc_class0FibreEmpty_iff_windowCheck (ctx : ActualFailureContext) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0 = ∅
      ↔ Class0WindowCycleCheck ctx :=
  (class0Fibre_empty_iff_pinned ctx).trans (class0Pinned_iff_windowCycleCheck ctx)

/-- An empty class-0 fibre has zero exit mass (the reach is an empty union). -/
theorem emfc_class0ExitMass_eq_zero_of_empty (ctx : ActualFailureContext)
    (h : routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 0 = ∅) :
    mdcClass0ExitMass ctx = 0 := by
  unfold mdcClass0ExitMass mdcClass0Reach
  rw [h]
  simp

/-- **The windowed check discharges the class-0 atom's inequality** at its
context — emptiness kills the mass outright. -/
theorem emfc_class0Atom_of_windowCheck (ctx : ActualFailureContext)
    (h : Class0WindowCycleCheck ctx) :
    1536 * (((ctx.n24CarryData.r + class0SurvivorPeriod (class1SlopeDatum ctx).q)
          / class0SurvivorPeriod (class1SlopeDatum ctx).q)
        * mdcClass0ExitMass ctx)
      ≤ 31 * ctx.shell.X := by
  have hempty := (emfc_class0FibreEmpty_iff_windowCheck ctx).mpr h
  rw [emfc_class0ExitMass_eq_zero_of_empty ctx hempty]
  simp

/-- **The class-0 reduction (the goal-2 deliverable)**: windowed checks at every
survivor pair supply the FULL named atom `MdcClass0ExitMassControl`. -/
theorem emfc_class0Control_of_windowChecks
    (h : ∀ ctx : ActualFailureContext, Class0DatumSurvivor ctx →
      Class0WindowCycleCheck ctx) : MdcClass0ExitMassControl :=
  fun ctx hsurv => emfc_class0Atom_of_windowCheck ctx (h ctx hsurv)

/-- **The converse obstruction, located**: the atom does NOT force emptiness, but
at band ≤ 4 its inequality DOES force an exit index outside the class-0 reach —
through the proved refutation of the unrestricted form
(`mdcUnrestrictedAtom_refuted`). -/
theorem emfc_class0Atom_misses_exit (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4)
    (hatom : 1536 * (((ctx.n24CarryData.r
            + class0SurvivorPeriod (class1SlopeDatum ctx).q)
          / class0SurvivorPeriod (class1SlopeDatum ctx).q)
        * mdcClass0ExitMass ctx)
      ≤ 31 * ctx.shell.X) :
    ∃ j ∈ emExitSet ctx, j ∉ mdcClass0Reach ctx := by
  by_contra hcon
  have hcov : emExitSet ctx ⊆ emcFibreReach ctx 0 := by
    intro j hj
    by_contra hnot
    refine hcon ⟨j, hj, ?_⟩
    rw [emfc_class0Reach_eq_fibreReach]
    exact hnot
  have h1 := emfc_coverage_le ctx 0 hcov
  rw [← emfc_class0ExitMass_eq_fibreExitMass] at h1
  refine mdcUnrestrictedAtom_refuted ctx hband ?_
  exact le_trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl h1)) hatom

/-! ## Part 4.  The unified family and its wiring -/

/-- **THE UNIFIED EXIT-MASS FAMILY**: the class-0 atom together with the
class-3/4/5 spaced-share regime — the complete per-class fibre-restricted
exit-mass axis in one named surface. -/
def EmfcUnifiedExitMassFamily : Prop :=
  MdcClass0ExitMassControl ∧ EmcOffPinSpacedShareRegime

/-- The family supplies the survivor class-0 mass row in the exact v18/v19 shape. -/
theorem emfc_family_class0Row (h : EmfcUnifiedExitMassFamily) :
    ∀ ctx : ActualFailureContext, Class0DatumSurvivor ctx →
      routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 0
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) :=
  mdcClass0SurvivorMass_of_atom h.1

/-- The family supplies the wave-19 pin-free conjunct `ExitMassControlOffPin`. -/
theorem emfc_family_offPin (h : EmfcUnifiedExitMassFamily) :
    ExitMassControlOffPin :=
  emc2_offPin_of_regime h.2

/-- The family + the open axis rebuild the FULL `ExitMassControlCore`. -/
theorem emfc_family_core (h : EmfcUnifiedExitMassFamily)
    (hvoid : DeepOrbitPinVoiding) : ExitMassControlCore :=
  emc2_core_of_regime_and_voiding h.2 hvoid

/-- The family + the axis supply the wave-8 deep axis `DeepFixedFamilyVoid`. -/
theorem emfc_family_deepVoid (h : EmfcUnifiedExitMassFamily)
    (hvoid : DeepOrbitPinVoiding) : DeepFixedFamilyVoid :=
  deepFixedFamilyVoid_of_exitMassControl (emfc_family_core h hvoid)

/-- **The cheapest sufficient inputs**: windowed checks on the survivors plus the
spaced-share regime assemble the whole family. -/
theorem emfc_family_of_checks_and_regime
    (hw : ∀ ctx : ActualFailureContext, Class0DatumSurvivor ctx →
      Class0WindowCycleCheck ctx)
    (hr : EmcOffPinSpacedShareRegime) : EmfcUnifiedExitMassFamily :=
  ⟨emfc_class0Control_of_windowChecks hw, hr⟩

/-- **The family's necessary shadow (recurrent classes)**: on every deep pin-free
context the regime forces all three recurrent classes exit-light — at most a
`31/768` share of the exit mass each. -/
theorem emfc_regime_forces_exitLight (h : EmcOffPinSpacedShareRegime)
    (ctx : ActualFailureContext) (hX : 2 ^ 986891 < ctx.X)
    (h2 : ¬ OrbitBandPinned ctx 2) (h3 : ¬ OrbitBandPinned ctx 3)
    (h4 : ¬ OrbitBandPinned ctx 4) :
    EmfcFibreExitLight ctx 3 ∧ EmfcFibreExitLight ctx 4 ∧ EmfcFibreExitLight ctx 5 := by
  obtain ⟨hband, ⟨b3, c3, hd3⟩, ⟨b4, c4, hd4⟩, ⟨b5, c5, hd5⟩⟩ := h ctx hX h2 h3 h4
  exact ⟨emfc_spacedShare_forces_exitLight ctx 3 hd3,
    emfc_spacedShare_forces_exitLight ctx 4 hd4,
    emfc_spacedShare_forces_exitLight ctx 5 hd5⟩

/-- **The family's necessary shadow (missed exits)**: on every deep pin-free
context the regime forces an exit OUTSIDE each recurrent class's window union —
the family demands genuinely exit-avoiding routing at all three classes. -/
theorem emfc_regime_misses_exits (h : EmcOffPinSpacedShareRegime)
    (ctx : ActualFailureContext) (hX : 2 ^ 986891 < ctx.X)
    (h2 : ¬ OrbitBandPinned ctx 2) (h3 : ¬ OrbitBandPinned ctx 3)
    (h4 : ¬ OrbitBandPinned ctx 4) :
    (∃ j ∈ emExitSet ctx, j ∉ emcFibreReach ctx 3)
      ∧ (∃ j ∈ emExitSet ctx, j ∉ emcFibreReach ctx 4)
      ∧ (∃ j ∈ emExitSet ctx, j ∉ emcFibreReach ctx 5) := by
  obtain ⟨hband, ⟨b3, c3, hd3⟩, ⟨b4, c4, hd4⟩, ⟨b5, c5, hd5⟩⟩ := h ctx hX h2 h3 h4
  exact ⟨emfc_spacedShare_misses_exit ctx 3 hband hd3,
    emfc_spacedShare_misses_exit ctx 4 hband hd4,
    emfc_spacedShare_misses_exit ctx 5 hband hd5⟩

/-! ## Part 5.  Honest machine-readable status -/

/-- Machine-readable, honest status of the unified exit-mass family closure. -/
def exitMassFamilyClosureStatus : List String :=
  [ "MULTIPLICITY VERDICT (goal 1, settled by definition + proofs): " ++
      "emcFibreExitMass is MULTIPLICITY-FREE - the sum of emExitWeight over " ++
      "emcFibreReach, a Finset.biUnion (UNION) of the fibre members' windows; " ++
      "each exit is counted once however many same-class windows contain it.  " ++
      "The class-0 quantity is the SAME object: mdcClass0ExitMass = " ++
      "emcFibreExitMass at i = 0 (emfc_class0ExitMass_eq_fibreExitMass, via " ++
      "emfc_class0Reach_eq_fibreReach) - the family is genuinely unified.  " ++
      "Usable form: every member's window deviation content sits below the " ++
      "fibre exit mass (emfc_devWindow_le_fibreExitMass, any class).",
    "THE SHARE'S TRUE STATUS (goal 1, THE KEY QUESTION): the share " ++
      "c*fibreExit <= b*totalExit is NOT an innocuous equidistribution count " ++
      "- it is an exit-AVOIDANCE demand.  PROVED: every spaced-share datum " ++
      "forces the exit-light cap 768*fibreExit <= 31*totalExit " ++
      "(emfc_spacedShare_forces_exitLight, via the forced absolute threshold " ++
      "768*b <= 31*c) - the class windows may carry at most ~4% of the exit " ++
      "mass; hence the datum is INCOMPATIBLE with the class windows covering " ++
      "the exit set (emfc_spacedShare_not_covering) and always leaves an exit " ++
      "OUTSIDE the class reach (emfc_spacedShare_misses_exit).  Where the " ++
      "brief's 'windows overlap across classes so the union is everything' " ++
      "heuristic holds, the share is REFUTED; the share survives only on " ++
      "genuinely exit-avoiding routings.  NAMED MINIMAL ATOM: " ++
      "EmfcFibreExitLight (768*fibreExit <= 31*totalExit), the distilled " ++
      "necessary condition of the whole axis.",
    "BINARY-IMPROVED DRIFT (goal 1 drift route, PROVED): the binary " ++
      "classification (non-exit gaps deviate EXACTLY 0) splits each boundary " ++
      "gap into band (<= 4) + exit weight " ++
      "(emfc_gapWindow_le_band_add_exit), improving the per-step drift to " ++
      "4*(s+1) + local exit mass (emfc_windowExcess_drift_binary) from the " ++
      "generic (s+1)*(L+B+1); exit-free boundary blocks drift <= 4*(s+1) " ++
      "TOTAL (emfc_windowExcess_drift_exitFree) - factor ~L/4 better.  Run " ++
      "member j pays entry + 4*j*c + (span exit mass counted ONCE) " ++
      "(emfc_run_member_le_binary - disjoint consecutive boundary blocks " ++
      "concatenate); run SUM <= m*entry + 2c*m(m-1) + m*(span exit mass) " ++
      "(emfc_run_sum_binary).",
    "REGIMES CLEARED VIA DRIFT: NONE UNCONDITIONALLY (honest).  The m*entry " ++
      "term is floored at m*Y (emfc_classMass_ge_card_Y: mass_i >= #fibre*Y), " ++
      "the count route's own currency, so the drift route can never undercut " ++
      "the count dead-zone analysis (emc_countTimesY_lt_cap: the count row " ++
      "is a THEOREM for L <= 1274739); and at deep L the exit term " ++
      "m*(span exit mass) meets the X/2 exit floor that refuted the " ++
      "unrestricted budget (mdcUnrestrictedAtom_refuted, factor 768/31).  " ++
      "The binary improvement's honest content is the per-member bound and " ++
      "the exit-light necessity - the quadratic band part 2c*m^2 is now " ++
      "negligible (constant 4 vs L+B+1) but was never the obstruction.",
    "CLASS-0 REDUCTION (goal 2, one-way + converse obstruction located): " ++
      "Class0WindowCycleCheck ctx IS class-0 fibre emptiness " ++
      "(emfc_class0FibreEmpty_iff_windowCheck, chaining " ++
      "class0Fibre_empty_iff_pinned with class0Pinned_iff_windowCycleCheck); " ++
      "emptiness zeroes the class-0 exit mass " ++
      "(emfc_class0ExitMass_eq_zero_of_empty) and discharges the atom's " ++
      "inequality outright (emfc_class0Atom_of_windowCheck); windowed checks " ++
      "at every survivor pair supply the FULL MdcClass0ExitMassControl " ++
      "(emfc_class0Control_of_windowChecks).  NO equivalence: the atom does " ++
      "not force emptiness; but at band <= 4 it forces an exit outside the " ++
      "class-0 reach (emfc_class0Atom_misses_exit).  TABLE VERDICT: no " ++
      "survivor certificate discharges the windowed check in-tree - all " ++
      "nineteen survivor pairs defeat the window-free cycle check " ++
      "(class0_datum_survivor_defeats_cycleCheck upstream); the windowed " ++
      "check stays the cheapest open sufficient input per survivor.",
    "WIRING (goal 3, PROVED): EmfcUnifiedExitMassFamily = " ++
      "MdcClass0ExitMassControl AND EmcOffPinSpacedShareRegime supplies the " ++
      "survivor class-0 mass row (emfc_family_class0Row), " ++
      "ExitMassControlOffPin (emfc_family_offPin), and with " ++
      "DeepOrbitPinVoiding the full ExitMassControlCore and " ++
      "DeepFixedFamilyVoid (emfc_family_core / emfc_family_deepVoid); " ++
      "cheapest sufficient inputs assemble it " ++
      "(emfc_family_of_checks_and_regime).  The family's necessary shadow " ++
      "is proved: on deep pin-free contexts all three recurrent classes are " ++
      "forced exit-light with a missed exit each " ++
      "(emfc_regime_forces_exitLight / emfc_regime_misses_exits).",
    "WHAT REMAINS OPEN (honest named atoms): (a) EmcSpacedShareDatum at " ++
      "uncertified parameters (b = 1, period c >= 64 - the deep table " ++
      "obstruction emcDeepProportionalClearedPairs_eq_nil stands); (b) " ++
      "MdcClass0ExitMassControl itself, or per-survivor " ++
      "Class0WindowCycleCheck (strictly stronger, = fibre0 emptiness); (c) " ++
      "the distilled necessary atom EmfcFibreExitLight - any refutation of " ++
      "it at a recurrent class on deep pin-free contexts would kill the " ++
      "spaced-share route outright.",
    "HYGIENE: additive only - ONE new module, no existing file edited, root " ++
      "import untouched; no sorry / admit / new axiom / native_decide; every " ++
      "key declaration passes #print axioms within [propext, " ++
      "Classical.choice, Quot.sound]." ]

/-- The status ledger is non-empty (honest, non-vacuous). -/
theorem exitMassFamilyClosureStatus_nonempty :
    exitMassFamilyClosureStatus ≠ [] := by
  simp [exitMassFamilyClosureStatus]

/-! ## Part 6.  Axiom-cleanliness audit
Every key declaration; expected axioms `[propext, Classical.choice, Quot.sound]`
or fewer. -/

#print axioms emfc_class0Reach_eq_fibreReach
#print axioms emfc_class0ExitMass_eq_fibreExitMass
#print axioms emfc_devWindow_le_fibreExitMass
#print axioms emfc_fibreExitMass_le_total
#print axioms emfc_exitMass_pos
#print axioms emfc_exitMass_eq_sum_exitSet_weight
#print axioms emfc_coverage_le
#print axioms emfc_spacedShare_forces_exitLight
#print axioms emfc_exitLight_misses_exit
#print axioms emfc_spacedShare_misses_exit
#print axioms emfc_spacedShare_not_covering
#print axioms emfc_gapWindow_le_band_add_exit
#print axioms emfc_windowExcess_drift_binary
#print axioms emfc_windowExcess_drift_exitFree
#print axioms emfc_run_member_le_binary
#print axioms emfc_run_sum_binary
#print axioms emfc_classMass_ge_card_Y
#print axioms emfc_class0FibreEmpty_iff_windowCheck
#print axioms emfc_class0ExitMass_eq_zero_of_empty
#print axioms emfc_class0Atom_of_windowCheck
#print axioms emfc_class0Control_of_windowChecks
#print axioms emfc_class0Atom_misses_exit
#print axioms emfc_family_class0Row
#print axioms emfc_family_offPin
#print axioms emfc_family_core
#print axioms emfc_family_deepVoid
#print axioms emfc_family_of_checks_and_regime
#print axioms emfc_regime_forces_exitLight
#print axioms emfc_regime_misses_exits
#print axioms exitMassFamilyClosureStatus_nonempty

end

end Erdos260
