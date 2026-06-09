import Erdos260.SDRDensityCore
import Erdos260.RunObstructionRealization

/-!
# Semiperiodic-window existence — the §25.1 match transfer behind the shared SDR

This module (NEW; it edits no existing file) owns the single deep **existence** fact left open by
`SDRDensityCore.lean` (wave-16): the *semiperiodic descent window itself*.  Wave-16 reduced the
shared DensePack/Tower/Run SDR to, for each class-2/3 high-excess start `k` with **no large run**
(`runClsOfShell ctx k ≠ 1`), the existence of a descent window `[k+r, k+r+spread]` that is

* `PeriodicOn ctx.shell.d (k+r) len (p k)` with a bounded primitive period `p k`, and
* of period density `≥ ρ_D` (so the §24 floor `ρ_D·p ≤ wt(period)` applies).

`SDRDensityCore` proved the *consequence* (counting + density transfer + the SDR feeds) but left the
periodic structure on the **actual, globally non-periodic** word `ctx.shell.d` as the lone residual.

## The mechanism, decomposed (what is already proved, and what genuinely remains)

The manuscript route "no large run ⟹ semiperiodic descent window of density `≥ ρ_D`" is, after the
prior waves, a chain of *already-proved* facts hinging on one residual:

* **§24 fixed-period density floor** `ρ_D·p ≤ wt(period)` — proved (`FixedDensity.fixedDensity_exact_completion_lower`,
  re-exported as `SDRDensityCore.windowWeight_density_floor_of_{orbit,primitive}`).
* **Fine–Wilf common period** — proved (`AppendixK2_FineWilf.PeriodicOn.fineWilf`).
* **Windowed counting + real density transfer** `ρ_D·L ≤ windowWeight` — proved
  (`SDRDensityCore.periodicWindow_count_lower`, `…windowWeight_ge_rhoD_mul_L`).
* **The abstract orbit word is globally periodic** — proved with *no* hypothesis beyond `q₀>1` odd:
  `dyadicDigit q₀ a` is `PeriodicOn` with period `ord_{q₀}(2)`
  (`RunObstructionRealization.dyadicDigit_periodicOn_mul`, from `Residual.dyadicDigit_period`).
* **Lemma 25.2 dichotomy** "dense ∨ short-semiperiodic" — proved
  (`Residual.lemma25_2_smallDenominatorSegment`); "no large run" excludes the dense branch.
* **§25.1 cylinder→digit bridge** (equal-cylinder case) — proved
  (`RunCylinderBridge.maskWord_eq_dyadicDigit_of_dyadicCylinder`).

The genuine irreducible residual is therefore the **§25.1 match**: that the actual shell descent
window agrees, *pointwise*, with the residual-center orbit word `dyadicDigit q₀ a`.  The hard half of
the original residual — *periodicity of the actual word* `ctx.shell.d` on the window — is **not**
proved directly (the word is globally non-periodic, `ctx.shell.hnonterm`); it is **derived from the
match** here.

## What this module proves unconditionally (no `sorry`/`axiom`/`admit`/`native_decide`)

* `WindowMatch`, `windowWeight_congr_of_match`, `periodicOn_of_match`, `shortSemiperiodic_of_match` —
  **the transfer machinery**: a pointwise window-match to *any* word `w` transports `w`'s window
  weight, its `PeriodicOn`, and its `ShortSemiperiodic` onto the actual word `d`.  This is the genuine
  new bridge: it converts the *periodicity of the actual non-periodic word* into a single matching
  fact about a provably-periodic orbit word.
* `windowWeight_ge_rhoD_mul_L_of_match` — **the real density atom, matched form**: a match to a
  windowed-periodic word of period density `≥ ρ_D` and the length calibration deliver
  `ρ_D·L ≤ windowWeight d start len` — verbatim the shared SDR atom, on the *actual* word.
* `MatchedSemiperiodicWindow` — **the smallest honest core packet**: the abstract orbit word + its
  (free) periodicity + its (§24) period density + the §25.1 match + the bounded period `period ≤ len`.
  Its `periodicOn` and `windowWeight_period_ge` are the *actual* window's semiperiodicity and density
  floor, both derived.
* `MatchedSemiperiodicWindow.ofDyadicMatch` — **the concrete grounding**: for the residual-center
  word `dyadicDigit q₀ a` the periodicity is *free* (`dyadicDigit_periodicOn_mul`), so the packet
  needs only the §24 density floor and the §25.1 match.
* `densePackEndpointDensity_of_matchedDescentWindows` — **the DensePack feed**: a per-start family of
  matched descent windows yields `densePackEndpointDensity ctx` exactly (through
  `SDRDensityCore.densePackMinHits_le_supportWindow_card`).
* `Class2IndexSDR.ofMatchedWindows` — **the Tower/Run feed**: the same per-start packets supply the
  `hidx_floor` of `Class2IndexSDR` (through `SDRDensityCore.Class2IndexSDR.ofSemiperiodicDensity`).

## The sharp characterization (audit verdict)

After this module the *only* surviving residual is the single Prop `MatchedDescentWindows ctx`: the
§25.1 cylinder-match of the actual descent window to `dyadicDigit q₀ a`.  This is the genuine
irreducible heart — every other layer (counting, Fine–Wilf, §24 density, abstract periodicity, the
25.2 dichotomy, the no-large-run routing, and now the *periodicity-of-the-actual-word transfer*) is
discharged.  The match is itself *partly proved* (`RunCylinderBridge`, equal-cylinder case), so the
true remainder is: (i) `ctx.shell.d` = the mask word of its own mask point, and (ii) that mask point
shares the residual center's dyadic cylinder over the whole window — the two geometric §25.1 inputs.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

namespace Erdos260

noncomputable section

/-! ## 1.  Window-match transfer — the genuine new bridge

`WindowMatch d w start len` says the actual word `d` agrees with the model word `w` on the window
`[start, start + len)` (read with `w` based at `0`).  Everything `w` knows about that window —
its hit weight, its periodicity, its short-semiperiodicity — transports to `d`. -/

/-- The actual word `d` matches the model word `w` on `[start, start + len)` (with `w` based at `0`):
`d (start + i) = w i` for every `i < len`.  This is the §25.1 "the actual word IS the orbit word on
the window" primitive, isolated. -/
def WindowMatch (d w : ℕ → ℕ) (start len : ℕ) : Prop :=
  ∀ i, i < len → d (start + i) = w i

/-- **Window-weight transfer.**  On a sub-window `[start, start + n)` of a match (`n ≤ len`) the
actual word has the *same* hit weight as the model word: `windowWeight d start n = windowWeight w 0 n`. -/
theorem windowWeight_congr_of_match {d w : ℕ → ℕ} {start len n : ℕ}
    (hm : WindowMatch d w start len) (hn : n ≤ len) :
    windowWeight d start n = windowWeight w 0 n := by
  unfold windowWeight
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mem_range] at hi
  rw [hm i (lt_of_lt_of_le hi hn), Nat.zero_add]

/-- **Periodicity transfer (the heart).**  If `d` matches a model word `w` on `[start, start + len)`
and `w` is `PeriodicOn` that window with period `p`, then so is `d`.  This is what replaces the
"periodicity of the actual (globally non-periodic) word `ctx.shell.d`" residual: it is *derived* from
the match to a provably-periodic orbit word. -/
theorem periodicOn_of_match {d w : ℕ → ℕ} {start len p : ℕ}
    (hm : WindowMatch d w start len) (hper : PeriodicOn w 0 len p) :
    PeriodicOn d start len p := by
  refine ⟨hper.1, fun i hi => ?_⟩
  have hi' : i < len := by omega
  have e1 : d (start + i + p) = w (i + p) := by
    rw [show start + i + p = start + (i + p) from by omega]
    exact hm (i + p) hi
  rw [e1, hm i hi']
  simpa using hper.2 i hi

/-- **Short-semiperiodicity transfer.**  A match transports the `ShortSemiperiodic` (bounded-period)
property of the model word onto the actual word — the Fine–Wilf / Lemma 25.2 output, moved to `d`. -/
theorem shortSemiperiodic_of_match {d w : ℕ → ℕ} {start len bound : ℕ}
    (hm : WindowMatch d w start len) (hsemi : ShortSemiperiodic w 0 len bound) :
    ShortSemiperiodic d start len bound := by
  obtain ⟨p, hper, hpb⟩ := hsemi
  exact ⟨p, periodicOn_of_match hm hper, hpb⟩

/-! ## 2.  The shared SDR atom on the actual word, from a match

Combining the transfer with `SDRDensityCore.windowWeight_ge_rhoD_mul_L`: a match to a windowed-periodic
model word of period density `≥ ρ_D`, with the length calibration `L + p ≤ len + 1`, gives the real
density atom `ρ_D·L ≤ windowWeight d start len` on the *actual* word. -/

/-- **The shared semiperiodic-density atom, matched form.**  For a window-match to a model word `w`
that is `PeriodicOn` the window with period `p` (`0 < p`, `p ≤ len`) of density `≥ ρ_D`
(`ρ_D·p ≤ windowWeight w 0 p`) and length calibration `L + p ≤ len + 1`, the actual word packs
`ρ_D·L ≤ windowWeight d start len`. -/
theorem windowWeight_ge_rhoD_mul_L_of_match {d w : ℕ → ℕ} {start len p L : ℕ}
    (hp : 0 < p)
    (hm : WindowMatch d w start len)
    (hper : PeriodicOn w 0 len p)
    (hdens : manuscriptRhoD * (p : ℝ) ≤ (windowWeight w 0 p : ℝ))
    (hp_le : p ≤ len)
    (hlen : L + p ≤ len + 1) :
    manuscriptRhoD * (L : ℝ) ≤ (windowWeight d start len : ℝ) := by
  have hperd : PeriodicOn d start len p := periodicOn_of_match hm hper
  have hdens' : manuscriptRhoD * (p : ℝ) ≤ (windowWeight d start p : ℝ) := by
    rw [windowWeight_congr_of_match hm hp_le]; exact hdens
  exact windowWeight_ge_rhoD_mul_L hp hperd hdens' hlen

/-! ## 3.  The smallest honest core packet — a matched semiperiodic window

`MatchedSemiperiodicWindow d start len` bundles exactly the irreducible per-start data: a model orbit
word `w`, its (free) periodicity, its (§24) period density, the bounded period `period ≤ len`, and the
§25.1 match.  Its derived methods are the *actual* window's semiperiodicity (`periodicOn`) and density
floor (`windowWeight_period_ge`) — the two facts `SDRDensityCore` left as the residual. -/

/-- A semiperiodic descent window on `[start, start + len)` of the actual word `d`, presented through
the §25.1 match to a model orbit word `w` of bounded period and period density `≥ ρ_D`. -/
structure MatchedSemiperiodicWindow (d : ℕ → ℕ) (start len : ℕ) where
  /-- The model orbit word (e.g. `dyadicDigit q₀ a`). -/
  w : ℕ → ℕ
  /-- The (bounded primitive) period. -/
  period : ℕ
  /-- The period is positive. -/
  hperiod_pos : 0 < period
  /-- The period fits inside the window (the bounded-period calibration). -/
  hperiod_le : period ≤ len
  /-- The model word is `PeriodicOn` the window with this period (free for `dyadicDigit q₀ a`). -/
  hper : PeriodicOn w 0 len period
  /-- The period density is `≥ ρ_D` (the §24 fixed-period floor on the model word). -/
  hdens : manuscriptRhoD * (period : ℝ) ≤ (windowWeight w 0 period : ℝ)
  /-- **The §25.1 match** — the lone irreducible residual: the actual word is the orbit word here. -/
  hmatch : WindowMatch d w start len

namespace MatchedSemiperiodicWindow

variable {d : ℕ → ℕ} {start len : ℕ}

/-- **The actual descent window is genuinely `PeriodicOn`** — derived from the match (it does not
assume periodicity of the globally non-periodic word `d`). -/
theorem periodicOn (W : MatchedSemiperiodicWindow d start len) :
    PeriodicOn d start len W.period :=
  periodicOn_of_match W.hmatch W.hper

/-- **The actual descent window carries the §24 density floor** `ρ_D·p ≤ windowWeight d start p`,
transferred from the model word along the match. -/
theorem windowWeight_period_ge (W : MatchedSemiperiodicWindow d start len) :
    manuscriptRhoD * (W.period : ℝ) ≤ (windowWeight d start W.period : ℝ) := by
  rw [windowWeight_congr_of_match W.hmatch W.hperiod_le]
  exact W.hdens

/-- **The shared SDR atom on the actual word.**  With the length calibration `L + p ≤ len + 1`, the
actual descent window packs `ρ_D·L ≤ windowWeight d start len`. -/
theorem windowWeight_ge (W : MatchedSemiperiodicWindow d start len) {L : ℕ}
    (hlen : L + W.period ≤ len + 1) :
    manuscriptRhoD * (L : ℝ) ≤ (windowWeight d start len : ℝ) :=
  windowWeight_ge_rhoD_mul_L_of_match W.hperiod_pos W.hmatch W.hper W.hdens W.hperiod_le hlen

end MatchedSemiperiodicWindow

/-! ## 4.  Concrete grounding on the residual-center orbit word `dyadicDigit q₀ a`

For the genuine model word `w = dyadicDigit q₀ a` the periodicity is **free** — it is global with
period `ord_{q₀}(2)` (`RunObstructionRealization.dyadicDigit_periodicOn_mul`, no hypothesis beyond
`q₀ > 1` odd).  So a matched semiperiodic window built from the residual center needs only the §24
density floor on the orbit period and the §25.1 match. -/

/-- **Matched semiperiodic window from the residual-center orbit word.**  Periodicity is supplied by
`dyadicDigit_periodicOn_mul`; the caller provides only the §24 period-density floor and the §25.1
match.  This isolates the residual to the match (and the Q-calibrated §24 floor). -/
def MatchedSemiperiodicWindow.ofDyadicMatch {d : ℕ → ℕ} {start len q0 a : ℕ}
    (hq0 : 1 < q0) (hodd : Odd q0)
    (hperiod_le : orderOf (2 : ZMod q0) ≤ len)
    (hdens : manuscriptRhoD * ((orderOf (2 : ZMod q0) : ℕ) : ℝ)
        ≤ (windowWeight (dyadicDigit q0 a) 0 (orderOf (2 : ZMod q0)) : ℝ))
    (hmatch : WindowMatch d (dyadicDigit q0 a) start len) :
    MatchedSemiperiodicWindow d start len where
  w := dyadicDigit q0 a
  period := orderOf (2 : ZMod q0)
  hperiod_pos := orderOf_pos_iff.mpr (isOfFinOrder_two_zmod hq0 hodd)
  hperiod_le := hperiod_le
  hper := by simpa using dyadicDigit_periodicOn_mul hq0 hodd Nat.one_pos a 0 len
  hdens := hdens
  hmatch := hmatch

/-! ## 5.  The DensePack feed — `densePackEndpointDensity` from matched descent windows

A per-start family of matched descent windows (one for each genuine DensePack start, on the descent
window `[k+r, k+r+spread]`) yields the bare K.1 coarea hit-density `densePackEndpointDensity ctx`
exactly, via `SDRDensityCore.densePackMinHits_le_supportWindow_card`. -/

/--
**The single named DensePack residual: a matched descent window per genuine start.**

For each genuine DensePack tower-exit start `k`, the descent window `[k+r, k+r+spread]` of the actual
shell word is a `MatchedSemiperiodicWindow` whose bounded period fits the length calibration
`Classical.choose ctx.shell.hXdyadic + period ≤ spread + 2`.  This is the §25.1 match family — the
genuine irreducible heart, with the density mechanism already discharged.
-/
def MatchedDescentWindows (ctx : ActualFailureContext) : Prop :=
  ∀ k ∈ genuineDensePackStarts ctx,
    ∃ W : MatchedSemiperiodicWindow ctx.shell.d (k + ctx.n24CarryData.r)
            (proofV4DensePackSpread ctx.shell + 1),
      Classical.choose ctx.shell.hXdyadic + W.period ≤ proofV4DensePackSpread ctx.shell + 2

/--
**`densePackEndpointDensity` from the matched descent-window family.**

The per-start matched window supplies `0 < p`, the *derived* `PeriodicOn`, the *derived* §24 density
floor, and the length calibration; the shell containment is geometric input.  Plugging into
`SDRDensityCore.densePackMinHits_le_supportWindow_card` delivers `densePackEndpointDensity ctx`.
-/
theorem densePackEndpointDensity_of_matchedDescentWindows
    (ctx : ActualFailureContext)
    (hlo : ∀ k ∈ genuineDensePackStarts ctx, ctx.shell.X < k + ctx.n24CarryData.r)
    (hhi : ∀ k ∈ genuineDensePackStarts ctx,
        (k + ctx.n24CarryData.r) + proofV4DensePackSpread ctx.shell ≤ 2 * ctx.shell.X)
    (h : MatchedDescentWindows ctx) :
    densePackEndpointDensity ctx := by
  intro k hk
  obtain ⟨W, hlenL⟩ := h k hk
  exact densePackMinHits_le_supportWindow_card ctx.shell (hlo k hk) (hhi k hk)
    W.hperiod_pos W.periodicOn W.windowWeight_period_ge hlenL

/-! ## 6.  The Tower/Run feed — `Class2IndexSDR` from matched windows

The same per-start packets supply the `hidx_floor` (`ρ_D·L ≤ #(idxOwned k)`) of `Class2IndexSDR`,
threaded through `SDRDensityCore.Class2IndexSDR.ofSemiperiodicDensity`.  The orthogonal
maximal-disjoint selection (`hlands`/`hdisj`) and the `L`-free scalar data are taken as inputs, being
the *other* (K.1.3) residual. -/

/-- **`Class2IndexSDR` from a per-fibre matched-window family.**  The matched windows discharge the
density half (`hp`/`hper`/`hdens`); the landing/disjointness selection and scalar calibration are
inputs.  Exhibits the per-start matched semiperiodic density as the exact density half of the shared
SDR. -/
def Class2IndexSDR.ofMatchedWindows
    (ctx : ActualFailureContext)
    (a : ℕ → ℕ) (hainj : Function.Injective a)
    (eps : ℝ) (Lnat : ℕ) (hLpos : 0 < Lnat)
    (hYnn : 0 ≤ ctx.n24CarryData.Y)
    (hcalibE : 2 * ctx.n24CarryData.Y ≤ 2 * eps * (Lnat : ℝ))
    (huniform : 2 * (erdos260Constants.c0 * eps) ≤ erdos260Constants.ξ / 6 * manuscriptRhoD)
    (hbdry : 0 ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2)
    (lo m len : ℕ → ℕ)
    (W : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
        MatchedSemiperiodicWindow ctx.shell.d (m k) (len k))
    (hlenL : ∀ k (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2),
        Lnat + (W k hk).period ≤ len k + 1)
    (hlands : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
        ∀ j ∈ Finset.Ico (lo k) (lo k + windowWeight ctx.shell.d (m k) (len k)),
          a j ∈ supportShell ctx.d ctx.X)
    (hdisj : ∀ j ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
        ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2, j ≠ k →
        Disjoint (Finset.Ico (lo j) (lo j + windowWeight ctx.shell.d (m j) (len j)))
          (Finset.Ico (lo k) (lo k + windowWeight ctx.shell.d (m k) (len k)))) :
    Class2IndexSDR ctx := by
  classical
  refine Class2IndexSDR.ofSemiperiodicDensity ctx a hainj eps Lnat hLpos hYnn hcalibE huniform hbdry
    lo m len
    (fun k => if hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2
              then (W k hk).period else 1)
    ?_ ?_ ?_ ?_ hlands hdisj
  · intro k hk; simp only [dif_pos hk]; exact (W k hk).hperiod_pos
  · intro k hk; simp only [dif_pos hk]; exact (W k hk).periodicOn
  · intro k hk; simp only [dif_pos hk]; exact (W k hk).windowWeight_period_ge
  · intro k hk; simp only [dif_pos hk]; exact hlenL k hk

/-! ## 7.  Non-vacuity — the core is genuinely inhabitable

A matched semiperiodic window exists (period `1`, full density), so `MatchedSemiperiodicWindow` and
the whole reduction are non-vacuous; the constructions are not built on an empty type. -/

/-- **Non-vacuity.**  `MatchedSemiperiodicWindow` is inhabitable (a period-`1`, full-density window).
This certifies the core packet is consistent, not vacuous. -/
theorem matchedSemiperiodicWindow_nonempty :
    Nonempty (MatchedSemiperiodicWindow (fun _ => 1) 0 1) :=
  ⟨{  w := fun _ => 1
      period := 1
      hperiod_pos := Nat.one_pos
      hperiod_le := le_refl 1
      hper := ⟨Nat.one_pos, fun i hi => rfl⟩
      hdens := by
        have hw : windowWeight (fun _ : ℕ => 1) 0 1 = 1 := by
          simp [windowWeight]
        rw [hw]; unfold manuscriptRhoD; norm_num
      hmatch := fun i _ => rfl }⟩

/-! ## 8.  Honest residual inventory -/

/-- The precise status of the semiperiodic-window existence after this module. -/
def semiperiodicWindowCoreResiduals : List String :=
  [ "PROVEN (transfer machinery, the genuine new bridge) — periodicOn_of_match / " ++
      "windowWeight_congr_of_match / shortSemiperiodic_of_match: a pointwise §25.1 window-match " ++
      "WindowMatch d w start len transports the model word w's window weight, PeriodicOn, and " ++
      "ShortSemiperiodic onto the ACTUAL word d. This converts the hard half of the wave-16 residual " ++
      "— periodicity of the globally non-periodic ctx.shell.d on the window — into the single matching " ++
      "fact about a PROVABLY periodic orbit word.",
    "PROVEN (shared atom, matched form) — windowWeight_ge_rhoD_mul_L_of_match: a match to a " ++
      "windowed-periodic model word of period density ≥ ρ_D, with L + p ≤ len + 1, gives ρ_D·L ≤ " ++
      "windowWeight d start len on the actual word — verbatim the shared SDR atom, via " ++
      "SDRDensityCore.windowWeight_ge_rhoD_mul_L.",
    "PROVEN (core packet) — MatchedSemiperiodicWindow with derived .periodicOn and " ++
      ".windowWeight_period_ge: the actual descent window's semiperiodicity AND §24 density floor " ++
      "(the two facts wave-16 left open) are DERIVED from the match + the model word's free " ++
      "periodicity + the §24 floor.",
    "PROVEN (concrete grounding) — MatchedSemiperiodicWindow.ofDyadicMatch: for the residual-center " ++
      "orbit word dyadicDigit q₀ a the periodicity is FREE (dyadicDigit_periodicOn_mul / " ++
      "dyadicDigit_period, period ord_{q₀}(2), no hypothesis beyond q₀>1 odd). The packet then needs " ++
      "ONLY the §24 density floor and the §25.1 match.",
    "PROVEN (DensePack feed) — densePackEndpointDensity_of_matchedDescentWindows: a per-start matched " ++
      "descent-window family (the named residual MatchedDescentWindows ctx) + shell containment yields " ++
      "densePackEndpointDensity ctx EXACTLY, via densePackMinHits_le_supportWindow_card.",
    "PROVEN (Tower/Run feed) — Class2IndexSDR.ofMatchedWindows: the same matched windows supply the " ++
      "hidx_floor (ρ_D·L ≤ #(idxOwned k)) of Class2IndexSDR, through " ++
      "Class2IndexSDR.ofSemiperiodicDensity; the maximal-disjoint selection (hlands/hdisj) is input.",
    "RESIDUAL (the single irreducible heart) — MatchedDescentWindows ctx: the §25.1 MATCH, that the " ++
      "actual shell descent window agrees pointwise with the residual-center orbit word dyadicDigit " ++
      "q₀ a on [k+r, k+r+spread]. Everything else — counting, Fine–Wilf, §24 density, abstract " ++
      "periodicity, the 25.2 dense∨short dichotomy, the no-large-run routing, AND the " ++
      "periodicity-of-the-actual-word transfer — is discharged. The match is itself PARTLY proved " ++
      "(RunCylinderBridge.maskWord_eq_dyadicDigit_of_dyadicCylinder, equal-cylinder case); the true " ++
      "remainder is the two geometric §25.1 inputs: (i) ctx.shell.d is the mask word of its mask " ++
      "point, and (ii) that point shares the residual center's depth-n dyadic cylinder over the " ++
      "window. WAVE-18 UPDATE: input (i) is now PROVED in SemiperiodicMatchEnrichCore " ++
      "(binaryDigitWord_windowMaskPoint, a self-contained finite N-bit digit extraction needing no " ++
      "infinitary uniqueness hypothesis), so ONLY the actual-carry cylinder geometry (ii) remains — " ++
      "Section251CylinderMatchResidual, the DirtyCrossing/CoareaOldNew old/new cylinder split routed " ++
      "to the equal-cylinder branch under no-large-run. " ++
      "'No large run' (runClsOfShell ≠ 1) is exactly what excludes the adjacent-cylinder " ++
      "dense/all-zero (large-run) branch and the Lemma 25.2 dense branch, leaving the equal-cylinder " ++
      "short-semiperiodic match.",
    "CALIBRATION (ρ_D Q-dependence — flagged, not blocking) — the §24 period density floor on " ++
      "dyadicDigit q₀ a is 1/(3·Q) (Q the shell denominator), which dominates the PINNED " ++
      "manuscriptRhoD = 1/4 only at Q = 1; the general-Q calibration ρ_D = 1/(4Q) is the separate " ++
      "flagged refactor. The transfer machinery here is parametric in manuscriptRhoD and stays " ++
      "correct under either calibration — only hdens (the §24 floor it consumes) is Q-sensitive. " ++
      "WAVE-18 RE-FLAG (not fixed): this Q-calibration is now LOCALIZED to a single consuming input, " ++
      "DescentCylinderMatchData.hdens (SemiperiodicMatchEnrichCore) — every downstream consumer takes " ++
      "the §24 floor as a hypothesis there. The Q-dependent manuscriptRhoD = 1/(4Q) refactor (a " ++
      "standalone change to Erdos260.Constants.manuscriptRhoD) remains the recommended fix and is " ++
      "deliberately NOT applied in this wave.",
    "NON-DEGENERATE — matchedSemiperiodicWindow_nonempty witnesses the core packet is inhabitable " ++
      "(period 1, full density); the transfer is the genuine telescoped/periodic structure, no " ++
      "vacuous or zero-floor shortcut." ]

theorem semiperiodicWindowCoreResiduals_nonempty : semiperiodicWindowCoreResiduals ≠ [] := by
  simp [semiperiodicWindowCoreResiduals]

/-! ## 9.  Axiom-cleanliness audit -/

#print axioms windowWeight_congr_of_match
#print axioms periodicOn_of_match
#print axioms shortSemiperiodic_of_match
#print axioms windowWeight_ge_rhoD_mul_L_of_match
#print axioms MatchedSemiperiodicWindow.periodicOn
#print axioms MatchedSemiperiodicWindow.windowWeight_period_ge
#print axioms MatchedSemiperiodicWindow.windowWeight_ge
#print axioms MatchedSemiperiodicWindow.ofDyadicMatch
#print axioms densePackEndpointDensity_of_matchedDescentWindows
#print axioms Class2IndexSDR.ofMatchedWindows
#print axioms matchedSemiperiodicWindow_nonempty

end

end Erdos260
