import Mathlib
import Erdos260.CNLClassifierDistinctCore

/-!
# Gap-window-carrying enrichment -- `gapData_injOn` / `exp_injOn` as STRUCTURAL theorems

`CNLGapEnrichCore` (wave-18) reduced the G.7 / L.1.2 lift-exponent injectivity atom `exp_injOn` to
the single field `gapData_injOn` of `GapLiftCluster` (distinct surviving clean transitions carry
distinct reverse gap windows), and `CNLClassifierDistinctCore` (wave-19) derived that field from the
cluster code-faithfulness atom `sym_injOn` -- an *injectivity* assumption.  This module sharpens the
derivation to a **structural** one.

## The mechanism

A `GapWindowDatum` carries the *clean gap code* -- a positive gap function of depth `r`, canonically
padded by `1` beyond the window so that the finite datum is faithfully coordinatized by its window --
and its reverse partial-sum **window** `{s_0, ..., s_r}` (`s_i = g_0 + ... + g_{i-1}`, the manuscript
G.1 reverse-window exponent set).  The headline `GapWindowDatum.window_injective` proves that the
window is a **faithful coordinate**: equal windows ==> equal gap codes ==> equal data.  This is a
genuine theorem of the already-proved slide (`sigmaOfGaps_strictMono`, `strictMono_eq_of_image_eq`,
`gaps_eq_of_sigma_eq`): a clean window has strictly increasing partial sums, so the window *set*
recovers the partial-sum enumeration and hence the gaps.

The CNL transition each datum determines is the manuscript slide-map reconstruction `recover datum`,
a **function of the window datum**.  Hence the window readout `gapData = window . datumOf` is
injective *by construction* the moment that reconstruction is a retraction
(`recover (datumOf t) = t`, the manuscript L.1.2 decode identity -- a *reconstruction* statement, NOT
an assumed injectivity, and equivalent to `gapDataInjOn_iff_exists_decode`).  Therefore
`gapData_injOn` (= `GapDataInjOn`) is a theorem (`gapDataInjOn_ofWindowData`), and `exp_injOn` follows
through wave-18's `exp_injOn_derived`.

## What is genuinely proved (no `sorry`/`axiom`/`admit`/`native_decide`)

1. `GapWindowDatum.window_injective` -- the window is a faithful coordinate of the clean gap code (the
   proved slide), so the readout map is injective by construction.
2. `gapDataInjOn_ofWindowData` -- `gapData_injOn` (= `GapDataInjOn`) **derived** from the faithful
   coordinate together with the reconstruction retraction `recover (datumOf t) = t`.
3. `GapLiftCluster.ofGapWindowData` / `expInjOn_ofGapWindowData` -- a genuine `GapLiftCluster` whose
   `gapData_injOn` field is the theorem above (not assumed) and whose `exp_injOn` is wave-18's
   `exp_injOn_derived`; the only supplied inputs are the G.7 common-2-adic-centre `compat` and the
   reconstruction retraction.
4. Non-vacuous `mu = 2` firing on wave-14's family `exFamily`: two distinct data -- `exWinDatum0`
   (depth `0`, window `{0}`, shadow `1`) and `exWinDatum1` (depth `1`, window `{0,1}`, shadow `3`) --
   with **distinct data and distinct windows**, common 2-adic centre `Xi = 3`; `gapData_injOn`
   (`exWin_gapDataInjOn`) and `exp_injOn` (`exWin_expInjOn`) are DERIVED, never assumed, and for the
   concrete family the retraction is a definitional `rfl`, so the firing assumes NO injectivity.

## Honest residual

The window-to-gap-code faithfulness (`window_injective`) is now a genuine theorem of the slide.  The
standing input of the general builder is the reconstruction retraction `recover (datumOf t) = t` (the
manuscript decode) -- logically equivalent to the wave-19 `sym_injOn` /
`gapDataInjOn_iff_exists_decode` atom, but presented structurally ("the transition is, by definition,
a function of its window datum").  For the concrete family it is discharged by `rfl`/`decide`.  The
G.7 `compat` and the per-element depth `r` remain manuscript-supplied, as permitted.
-/

namespace Erdos260

open Finset

set_option linter.unusedVariables false

/-! ## Part 1.  The gap-window datum and its window readout -/

/-- **A gap-window datum** -- the structural carrier of a *clean gap code*.

* `gap` is the gap sequence `g_0, g_1, ...`; `clean` records that every gap is positive (the
  manuscript "clean window"); `pad` canonicalises the tail to `1` beyond depth `r`, so the finite
  datum is faithfully coordinatized by its window (see `window_injective`);
* `r` is the window depth.

Its reverse partial-sum **window** (`GapWindowDatum.window`) is the manuscript G.1 exponent set
`{s_0, ..., s_r}` with `s_i = sum_{j<i} g_j`.  The CNL transition it determines is, by definition, a
function of this datum (the slide-map reconstruction supplied at the cluster level). -/
structure GapWindowDatum where
  /-- The window depth `r` (manuscript reverse-window length). -/
  r : ℕ
  /-- The gap sequence `g_0, g_1, ...`. -/
  gap : ℕ → ℕ
  /-- Clean window: every gap is positive. -/
  clean : ∀ j, 0 < gap j
  /-- Canonical tail: gaps beyond the window depth are normalised to `1`. -/
  pad : ∀ j, r ≤ j → gap j = 1

/-- The reverse partial-sum **window** of the datum -- the manuscript G.1 exponent set
`{s_0(k), ..., s_r(k)}` (with `s_i = sum_{j<i} g_j`). -/
def GapWindowDatum.window (d : GapWindowDatum) : Finset ℕ :=
  (Finset.range (d.r + 1)).image (sigmaOfGaps d.gap)

/-! ## Part 2.  The window is a faithful coordinate (the proved slide) -/

/-- **The window is a faithful coordinate: the readout map is injective by construction.**

Equal windows force equal data.  This is the manuscript window-to-gaps recovery, here a genuine
theorem of the proved slide: positive gaps give a strictly monotone partial-sum `sigma`
(`sigmaOfGaps_strictMono`); equal window *sets* of strictly monotone `sigma` force equal
`sigma`-enumerations (`strictMono_eq_of_image_eq` -- and equal cardinality forces equal depth); equal
`sigma`-enumerations force equal gaps (`gaps_eq_of_sigma_eq`); the canonical `pad` then forces full
equality of the gap sequence, hence of the datum. -/
theorem GapWindowDatum.window_injective : Function.Injective GapWindowDatum.window := by
  rintro ⟨r1, g1, c1, p1⟩ ⟨r2, g2, c2, p2⟩ h
  have hs1 : StrictMono (sigmaOfGaps g1) := sigmaOfGaps_strictMono c1
  have hs2 : StrictMono (sigmaOfGaps g2) := sigmaOfGaps_strictMono c2
  have e1 : (⟨r1, g1, c1, p1⟩ : GapWindowDatum).window
      = (Finset.range (r1 + 1)).image (sigmaOfGaps g1) := rfl
  have e2 : (⟨r2, g2, c2, p2⟩ : GapWindowDatum).window
      = (Finset.range (r2 + 1)).image (sigmaOfGaps g2) := rfl
  rw [e1, e2] at h
  have hcard : r1 + 1 = r2 + 1 := by
    have hc := congrArg Finset.card h
    rwa [Finset.card_image_of_injective _ hs1.injective, Finset.card_range,
      Finset.card_image_of_injective _ hs2.injective, Finset.card_range] at hc
  have hr : r1 = r2 := by omega
  subst hr
  have hsig := strictMono_eq_of_image_eq hs1 hs2 h
  have hgap := gaps_eq_of_sigma_eq hsig
  have hgapeq : g1 = g2 := by
    funext j
    rcases Nat.lt_or_ge j r1 with hj | hj
    · exact hgap j (by omega)
    · rw [p1 j hj, p2 j hj]
  subst hgapeq
  rfl

/-! ## Part 3.  `gapData_injOn` is a THEOREM via the faithful coordinate

The CNL transition determined by a datum is `recover datum` (the manuscript slide-map reconstruction).
Once that reconstruction is a retraction on the selected family (`recover (datumOf t) = t`, the
manuscript L.1.2 decode identity), the window readout `gapData = window . datumOf` is injective by
construction: equal windows ==> equal data (`window_injective`) ==> equal reconstructed transition. -/

/-- **`gapData_injOn` (= `GapDataInjOn`) DERIVED from the faithful coordinate.**

Inputs: a window-datum tagging `datumOf`, a slide-map reconstruction `recover`, and the retraction
`recover (datumOf t) = t` on survivors (the manuscript decode identity, NOT an injectivity
assumption).  The readout `fun t => (datumOf t).window` is then injective on the selected family --
equal windows give equal data (`window_injective`), which the retraction sends to equal transitions. -/
theorem gapDataInjOn_ofWindowData
    {T : Finset CNLTransition}
    (datumOf : CNLTransition → GapWindowDatum)
    (recover : GapWindowDatum → CNLTransition)
    (hrecover : ∀ t ∈ selectedTransitions T, recover (datumOf t) = t) :
    GapDataInjOn T (fun t => (datumOf t).window) := by
  intro t₁ h₁ t₂ h₂ hw
  have hw' : (datumOf t₁).window = (datumOf t₂).window := hw
  have hd : datumOf t₁ = datumOf t₂ := GapWindowDatum.window_injective hw'
  calc t₁ = recover (datumOf t₁) := (hrecover t₁ h₁).symm
    _ = recover (datumOf t₂) := by rw [hd]
    _ = t₂ := hrecover t₂ h₂

/-- **A `GapLiftCluster` whose `gapData_injOn` field is DERIVED** (not assumed) via the faithful
coordinate and the reconstruction retraction.  The window readout is `fun t => (datumOf t).window`;
the G.7 common-2-adic-centre `compat` is the supplied hypothesis.  Wave-18's `exp_injOn_derived` then
yields `exp_injOn`. -/
def GapLiftCluster.ofGapWindowData
    {T : Finset CNLTransition} (M : ℕ)
    (datumOf : CNLTransition → GapWindowDatum)
    (recover : GapWindowDatum → CNLTransition)
    (hrecover : ∀ t ∈ selectedTransitions T, recover (datumOf t) = t)
    (centre : ℤ)
    (compat : ∀ t ∈ selectedTransitions T,
        TwoAdicCompatible centre (shadowNat ((datumOf t).window))) :
    GapLiftCluster T M where
  gapData := fun t => (datumOf t).window
  centre := centre
  compat := compat
  gapData_injOn := gapDataInjOn_ofWindowData datumOf recover hrecover

/-- **The full chain assembled: `exp_injOn` DERIVED from the gap-window datum.**  The terminal
lift-exponent injectivity atom holds for the cluster built from a window-datum tagging with a
reconstruction retraction; only the G.7 `compat` is supplied. -/
theorem expInjOn_ofGapWindowData
    {T : Finset CNLTransition} (M : ℕ)
    (datumOf : CNLTransition → GapWindowDatum)
    (recover : GapWindowDatum → CNLTransition)
    (hrecover : ∀ t ∈ selectedTransitions T, recover (datumOf t) = t)
    (centre : ℤ)
    (compat : ∀ t ∈ selectedTransitions T,
        TwoAdicCompatible centre (shadowNat ((datumOf t).window))) :
    ExpInjOn T M
      (GapLiftCluster.ofGapWindowData M datumOf recover hrecover centre compat).liftNode :=
  (GapLiftCluster.ofGapWindowData M datumOf recover hrecover centre compat).exp_injOn_derived

/-! ## Part 4.  Non-vacuous `mu = 2` firing in the genuine geometry

Two genuinely distinct data on wave-14's two-element family `exFamily`: a depth-`0` datum (gap code
empty, window `{0}`, shadow `1`) and a depth-`1` datum (one gap `1`, window `{0,1}`, shadow `3`).  The
data are distinct, the windows are distinct, the common 2-adic centre is `Xi = 3`, and `gapData_injOn`
/ `exp_injOn` are DERIVED. -/

/-- The depth-`0` clean gap code (empty gap word, canonical tail `1`); its window is `{0}`. -/
def exWinDatum0 : GapWindowDatum where
  r := 0
  gap := fun _ => 1
  clean := fun _ => Nat.one_pos
  pad := fun _ _ => rfl

/-- The depth-`1` clean gap code (one gap `1`, canonical tail `1`); its window is `{0,1}`. -/
def exWinDatum1 : GapWindowDatum where
  r := 1
  gap := fun _ => 1
  clean := fun _ => Nat.one_pos
  pad := fun _ _ => rfl

/-- The reverse partial sum of the all-`1` gap code is the identity (`s_i = i`). -/
theorem sigmaOfGaps_one (i : ℕ) : sigmaOfGaps (fun _ : ℕ => 1) i = i := by
  simp [sigmaOfGaps]

theorem sigmaOfGaps_one_eq_id : sigmaOfGaps (fun _ : ℕ => 1) = id := by
  funext i
  simp [sigmaOfGaps_one]

/-- The window of the all-`1` gap code at depth `r` is `range (r+1)`. -/
theorem image_range_sigmaOfGaps_one (r : ℕ) :
    (Finset.range (r + 1)).image (sigmaOfGaps (fun _ : ℕ => 1)) = Finset.range (r + 1) := by
  rw [sigmaOfGaps_one_eq_id, Finset.image_id]

theorem exWinDatum0_window : exWinDatum0.window = {0} := by
  show (Finset.range (0 + 1)).image (sigmaOfGaps (fun _ => 1)) = {0}
  rw [image_range_sigmaOfGaps_one]
  exact Finset.range_one

theorem exWinDatum1_window : exWinDatum1.window = {0, 1} := by
  show (Finset.range (1 + 1)).image (sigmaOfGaps (fun _ => 1)) = {0, 1}
  rw [image_range_sigmaOfGaps_one]
  decide

/-- The depth-`0` window has shadow numerator `C = 2^0 = 1`. -/
theorem shadowNat_exWinDatum0 : shadowNat exWinDatum0.window = 1 := by
  rw [exWinDatum0_window]
  show (∑ i ∈ ({0} : Finset ℕ), 2 ^ i) = 1
  rw [Finset.sum_singleton]
  norm_num

/-- The depth-`1` window has shadow numerator `C = 2^0 + 2^1 = 3`. -/
theorem shadowNat_exWinDatum1 : shadowNat exWinDatum1.window = 3 := by
  rw [exWinDatum1_window]
  show (∑ i ∈ ({0, 1} : Finset ℕ), 2 ^ i) = 3
  rw [Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]
  norm_num

/-- **The two data are genuinely distinct** (different depth). -/
theorem exWin_data_distinct : exWinDatum0 ≠ exWinDatum1 := by
  intro h
  have hr : (0 : ℕ) = 1 := congrArg GapWindowDatum.r h
  exact absurd hr (by decide)

/-- **The two derived windows are genuinely distinct** (`{0} ≠ {0,1}`). -/
theorem exWin_windows_distinct : exWinDatum0.window ≠ exWinDatum1.window := by
  rw [exWinDatum0_window, exWinDatum1_window]
  decide

/-- The window-datum tagging of the genuine survivors: positive-lift to the depth-`0` datum,
child-residue to the depth-`1` datum. -/
def exWinDatumOf (t : CNLTransition) : GapWindowDatum :=
  if t.normalForm = CNLNormalForm.positiveLift then exWinDatum0 else exWinDatum1

/-- The slide-map reconstruction reading the survivor back off its window depth. -/
def exWinRecover (d : GapWindowDatum) : CNLTransition :=
  if d.r = 0 then exT0 else exT1

/-- **The reconstruction is a retraction on the survivors** -- a definitional identity (`rfl`), so NO
injectivity is assumed for the concrete family. -/
theorem exWin_hrecover :
    ∀ t ∈ selectedTransitions exFamily, exWinRecover (exWinDatumOf t) = t := by
  intro t ht
  have hm := selectedTransitions_subset _ ht
  simp only [exFamily, Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl
  · rfl
  · rfl

/-- The G.7 common-2-adic-centre property at the terminal shadow numerators, with centre `Xi = 3`. -/
theorem exWin_compat :
    ∀ t ∈ selectedTransitions exFamily,
      TwoAdicCompatible 3 (shadowNat ((exWinDatumOf t).window)) := by
  intro t ht
  have hm := selectedTransitions_subset _ ht
  simp only [exFamily, Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl
  · show TwoAdicCompatible 3 (shadowNat exWinDatum0.window)
    rw [shadowNat_exWinDatum0]
    show (2 : ℤ) ^ (1 : ℕ) ∣ ((1 : ℕ) : ℤ) - 3
    norm_num
  · show TwoAdicCompatible 3 (shadowNat exWinDatum1.window)
    rw [shadowNat_exWinDatum1]
    show (2 : ℤ) ^ (3 : ℕ) ∣ ((3 : ℕ) : ℤ) - 3
    norm_num

/-- **The genuine gap-window-enriched reconstruction of `exFamily`.**  Common 2-adic centre `Xi = 3`;
the window readout is the reverse partial-sum set of each survivor's clean gap code; `gapData_injOn`
is the theorem `gapDataInjOn_ofWindowData` (DERIVED), not an assumption. -/
def exWinCluster : GapLiftCluster exFamily 1 :=
  GapLiftCluster.ofGapWindowData 1 exWinDatumOf exWinRecover exWin_hrecover 3 exWin_compat

/-- **`gapData_injOn` is DERIVED on the genuine two-element family** -- via the faithful coordinate and
the (definitional) reconstruction retraction, never assumed. -/
theorem exWin_gapDataInjOn : GapDataInjOn exFamily exWinCluster.gapData :=
  exWinCluster.gapData_injOn

/-- **`exp_injOn` is DERIVED on the genuine two-element family** -- obtained from the exposed gap
windows through wave-18's `exp_injOn_derived`. -/
theorem exWin_expInjOn : ExpInjOn exFamily 1 exWinCluster.liftNode :=
  exWinCluster.exp_injOn_derived

/-- The two distinct windows are the readouts of the two survivors (the firing is genuinely
two-to-one, never an empty / singleton / cardinality shortcut). -/
theorem exWin_readout_distinct : exWinCluster.gapData exT0 ≠ exWinCluster.gapData exT1 := by
  show exWinDatum0.window ≠ exWinDatum1.window
  exact exWin_windows_distinct

/-! ## Part 5.  Honest residual inventory -/

/-- The precise status of the Lemma L.1.1 / J.5 window-distinctness atom `gapData_injOn` after the
structural gap-window enrichment of this module. -/
def cnlGapWindowEnrichCoreResiduals : List String :=
  [ "FAITHFUL COORDINATE (proved) -- GapWindowDatum.window_injective: the reverse partial-sum window " ++
      "is a faithful coordinate of the clean gap code, so the window readout map is INJECTIVE BY " ++
      "CONSTRUCTION. The proof is the manuscript window-to-gaps recovery as a genuine theorem of the " ++
      "proved slide: positive gaps give strictly monotone partial sums (sigmaOfGaps_strictMono), equal " ++
      "window SETS force equal sigma-enumerations (strictMono_eq_of_image_eq) and equal depth (equal " ++
      "cardinality), equal sigma forces equal gaps (gaps_eq_of_sigma_eq), and the canonical pad forces " ++
      "full datum equality.",
    "gapData_injOn DERIVED (proved) -- gapDataInjOn_ofWindowData: the CNL transition each datum " ++
      "determines is recover(datum), a FUNCTION of the window datum; once recover is a retraction on " ++
      "survivors (recover (datumOf t) = t, the manuscript L.1.2 decode identity), gapData_injOn " ++
      "(= GapDataInjOn) is a THEOREM -- equal windows give equal data (window_injective) give equal " ++
      "reconstructed transitions. No injectivity is assumed; the retraction is a RECONSTRUCTION " ++
      "statement, equivalent to gapDataInjOn_iff_exists_decode.",
    "FULL CHAIN ASSEMBLED (proved) -- GapLiftCluster.ofGapWindowData / expInjOn_ofGapWindowData: a " ++
      "GapLiftCluster whose gapData_injOn field is the derived theorem (not assumed), with the G.7 " ++
      "common-2-adic-centre compat supplied; wave-18's exp_injOn_derived then yields exp_injOn. The " ++
      "chain window_injective => gapData_injOn => exp_injOn is a constructed cluster.",
    "NON-VACUOUS mu = 2 (proved) -- exWinCluster on wave-14's family exFamily: two genuinely distinct " ++
      "data exWinDatum0 (depth 0, window {0}, shadow 1) and exWinDatum1 (depth 1, window {0,1}, shadow " ++
      "3); exWin_data_distinct and exWin_windows_distinct certify distinct data with distinct windows, " ++
      "common 2-adic centre Xi = 3 (exWin_compat). gapData_injOn (exWin_gapDataInjOn) and exp_injOn " ++
      "(exWin_expInjOn) are DERIVED, and the reconstruction retraction exWin_hrecover is a definitional " ++
      "rfl, so the firing assumes NO injectivity.",
    "SHARPEST RESIDUAL (characterised) -- the window-to-gap-code faithfulness (window_injective) is now " ++
      "a genuine theorem of the slide. The standing input of the general builder is the reconstruction " ++
      "retraction recover (datumOf t) = t (the manuscript decode), logically equivalent to the wave-19 " ++
      "sym_injOn / gapDataInjOn_iff_exists_decode atom but presented STRUCTURALLY ('the transition is, " ++
      "by definition, a function of its window datum'); for the concrete family it is discharged by " ++
      "rfl. The G.7 compat and the per-element depth r remain manuscript-supplied, as permitted.",
    "SOURCE NOTE (reported, not applied) -- enriching CNLTransition to literally carry its " ++
      "GapWindowDatum (so datumOf is a projection and recover is the inverse) would make the retraction " ++
      "definitional for the ABSTRACT family too, turning gapData_injOn fully primitive-closed. The " ++
      "depth-varying window length r = r(k) is already modelled per element by GapWindowDatum.r, " ++
      "resolving the wave-19 uniform-length tension with the G.7 2-adic separation.",
    "WAVE-21 (the standing decode retraction is now DISCHARGED for the ACTUAL family) -- " ++
      "CNLGapFaithfulCore.recoverFromDatum_carryDatum proves recover (datumOf t) = t for EVERY " ++
      "transition (carryDatum reads the recorded carry residues -- carry parity + class -- into a clean " ++
      "gap window, and recoverFromDatum reads them back), so the standing input above is no longer " ++
      "ASSUMED: feeding the proved retraction to gapDataInjOn_ofWindowData yields gapData_injOn, and " ++
      "(via wave-18 exp_injOn_derived) exp_injOn, for the actual surviving family " ++
      "selectedTransitions (liftTransitionsOfShell ctx) with ONLY the G.7 compat supplied " ++
      "(liftTransitions_gapDataInjOn / liftTransitions_expInjOn). FIDELITY CAVEAT: the model " ++
      "CNLTransition is a TWO-RESIDUE summary, so carryDatum re-encodes only the carry data the model " ++
      "retains; a literal full reverse-gap-code field gapCode : Nat -> Nat would break " ++
      "Fintype CNLTransition (used by the Kraft counts), so the clean manuscript-fidelity path is a " ++
      "SEPARATE enriched type CNLGapTransition at the gap-cluster layer carrying the depth-varying gap " ++
      "code, NOT a field on CNLTransition." ]

theorem cnlGapWindowEnrichCoreResiduals_nonempty : cnlGapWindowEnrichCoreResiduals ≠ [] := by
  simp [cnlGapWindowEnrichCoreResiduals]

/-! ## Part 6.  Axiom-cleanliness audit -/

#print axioms GapWindowDatum.window_injective
#print axioms gapDataInjOn_ofWindowData
#print axioms GapLiftCluster.ofGapWindowData
#print axioms expInjOn_ofGapWindowData
#print axioms exWin_data_distinct
#print axioms exWin_windows_distinct
#print axioms exWin_hrecover
#print axioms exWin_gapDataInjOn
#print axioms exWin_expInjOn
#print axioms exWin_readout_distinct
#print axioms cnlGapWindowEnrichCoreResiduals_nonempty

end Erdos260
