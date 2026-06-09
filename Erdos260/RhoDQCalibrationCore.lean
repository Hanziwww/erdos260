import Erdos260.FailingShellPeriodicityCore
import Erdos260.SemiperiodicMatchEnrichCore

/-!
# The genuine Q-dependent dense-marker density floor `ρ_D(Q) = 1/(4 q₀)` (standalone calibration)

This module (NEW; it edits no existing file, and does **not** change the global
`Erdos260.Constants.manuscriptRhoD = 1/4`) fixes the long-flagged **`ρ_D` Q-calibration**: the pinned
`manuscriptRhoD = 1/4` is the `Q = 1` representative, and it is *too strong* for `Q ≥ 2`.  The genuine
manuscript dense-marker density is **Q-dependent**: `proof_v4` §I.4 (`ρ₀(Q) = 1/(4Q)`, ~line 962), and
the §24 fixed-period density floor is `1/(3 q₀)` where `q₀` is the ODD part of `Q` (powers of two are
eventually periodic mod `Q`, so only the odd part governs the orbit period `t = ord_{q₀}(2)`).

The shared density atom `ρ_D · L ≤ windowWeight` (the §24 / Fine–Wilf period-density transfer of
`SDRDensityCore` / `SemiperiodicWindowCore`, the §25.1 match of `DescentDepthAgreementCore`, and the
Tower / DensePack consumers) is genuinely **parametric in `ρ_D`**: the deepest atom
`SDRDensityCore.periodicWindow_count_lower` is `ρ_D`-free, and the only place `manuscriptRhoD` enters is
as a nonnegativity scalar (`windowWeight_ge_rhoD_mul_L`) or as the rate parameter of the parametric
selection builder `TowerSDRCore.Class2IndexSDR.ofIntervals`.  So the **least-invasive** correct fix is
to instantiate that parametric chain with the genuine Q-dependent floor

```
ρ_D(q₀) := 1 / (4 q₀)        (rhoDQ q₀ below)
```

threading `q₀ = oddPart Q` (concretely the actual shell's reduced residual-center denominator
`(canonicalCenter ctx).q0`, which is `> 1` and odd), *without* touching `manuscriptRhoD`.

## What is genuinely PROVED here (no `sorry`/`axiom`/`admit`/`native_decide`)

* `rhoDQ`, `rhoDQ_pos`, `rhoDQ_le_third`, `rhoDQ_le_manuscriptRhoD`, `rhoDQ_one_eq` — the Q-dependent
  floor and its calibration: `0 < 1/(4 q₀) ≤ 1/(3 q₀)` (so it stays **below** the genuine §24 floor for
  EVERY `q₀ ≥ 1`), `1/(4 q₀) ≤ 1/4 = manuscriptRhoD`, and `rhoDQ 1 = manuscriptRhoD` (the `Q = 1`
  specialization recovers the pinned value).
* `manuscriptRhoD_gt_third_of_two_le` — **the precise diagnosis**: for `q₀ ≥ 2` the pinned
  `manuscriptRhoD = 1/4` STRICTLY exceeds the genuine §24 floor `1/(3 q₀)`, so the `manuscriptRhoD`-form
  density atom cannot be discharged from §24 for `q₀ ≥ 2` — exactly the reported defect.
* `windowWeight_ge_floor_mul_L`, `windowWeight_ge_floor_mul_L_of_match` — the SDR density atom made
  **generic in the rate `ρ`** (re-proofs of `SDRDensityCore.windowWeight_ge_rhoD_mul_L` /
  `SemiperiodicWindowCore.windowWeight_ge_rhoD_mul_L_of_match` with `ρ` and `0 ≤ ρ` in place of the
  hard-wired `manuscriptRhoD` / `manuscriptRhoD_pos`).
* `dyadicDigit_density_floor_rhoDQ` — **the density atom, correct for ALL Q**: the orbit word
  `dyadicDigit q₀ a` (`q₀ > 1` odd, `a` coprime to `q₀`) packs `(1/(4 q₀)) · t ≤ wt(period)`, derived
  from the genuine `1/(3 q₀)` §24 floor (`FailingShellPeriodicityCore.dyadicDigit_density_floor`) via
  `rhoDQ_le_third`.  This holds for every odd part `q₀`, never just `q₀ = 1`.
* `windowWeight_ge_rhoDQ_of_dyadicMatch` — **the matched-window atom, correct for ALL Q**: from a §25.1
  window-match to `dyadicDigit q₀ a` plus the length calibration, the actual descent window packs
  `(1/(4 q₀)) · L ≤ windowWeight d start len` — the shared SDR atom on the *actual* word, for every `Q`.
* `Class2IndexSDR.ofDyadicMatchesRhoDQ`, `towerSubMass_of_dyadicMatchesRhoDQ` — **Tower composition**:
  the Q-dependent atom feeds the parametric `Class2IndexSDR.ofIntervals` at rate `rhoDQ q₀`, yielding a
  genuine `Class2IndexSDR ctx` and hence the Tower capacity floor `routedClassMassOf … 2 ≤ ξX/6` — the
  exact frontier budget input — now honestly for ALL Q.
* `densePackMinHitsFloor_rhoDQ_le_supportWindow` — **DensePack composition**: the K.1.1 coarea
  hit-density `⌊(1/(4 q₀)) · L⌋ ≤ |supportWindow(m)|`, via the generic shell injection
  `SDRDensityCore.windowFilter_card_le_supportWindow`, again for ALL Q.
* `descentDensityFloor_rhoDQ_all_Q` — **the drop-in `hdens` replacement, dischargeable for ALL Q**: the
  per-start §24 floor in exactly the shape of `DescentCylinderMatchData.hdens` /
  `SingularSquareCertificate.hdens`, but at the Q-dependent rate `rhoDQ (canonicalCenter ctx).q0`.
  Where the `manuscriptRhoD`-pinned field is dischargeable only at `q₀ = 1`, this one is dischargeable
  for *every* `ctx` (every `Q`), needing only the genuine coprimality of the residue numerators.

## Why this composes to the frontier (audit note)

`erdos260_of_minimalResidualV3` (and its residual `Erdos260MinimalResidualV3`) does **not** mention
`manuscriptRhoD` in its type: the Tower field is `Class2ActiveFloorCount` (`#fibre₂·positivePart(2Y) ≤
ξX/6`, dense markers bypassed) and the DensePack field is `DensePackCoareaSupport` (owner/marker maps).
`manuscriptRhoD` lives only inside the density-reduction lemmas as a *hypothesis* (`hdens`/`hcal`).
This module supplies the genuinely Q-correct rate for those hypotheses and re-derives the same Tower
capacity floor through the parametric SDR — so the global `manuscriptRhoD` constant is left untouched,
the whole library still builds green, and the frontier stays axiom-clean.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

namespace Erdos260

open Finset

noncomputable section

set_option linter.unusedVariables false

/-! ## 1.  The Q-dependent dense-marker density `ρ_D(q₀) = 1/(4 q₀)` and its calibration -/

/-- **The genuine Q-dependent dense-marker density floor** `ρ_D(q₀) = 1/(4 q₀)` (manuscript
`proof_v4` §I.4 `ρ₀(Q) = 1/(4Q)`, sharpened to the odd part `q₀ = oddPart Q` that governs the orbit
period).  This is the correct calibration for the shared density atom at *general* `Q`. -/
def rhoDQ (q0 : ℕ) : ℝ := 1 / (4 * (q0 : ℝ))

/-- `ρ_D(q₀) > 0` for `q₀ ≥ 1`. -/
theorem rhoDQ_pos {q0 : ℕ} (hq0 : 0 < q0) : 0 < rhoDQ q0 := by
  have hq0R : (0 : ℝ) < (q0 : ℝ) := by exact_mod_cast hq0
  have h4 : (0 : ℝ) < 4 * (q0 : ℝ) := mul_pos (by norm_num) hq0R
  unfold rhoDQ
  exact div_pos (by norm_num) h4

/-- **The key calibration** `ρ_D(q₀) = 1/(4 q₀) ≤ 1/(3 q₀)` — the Q-dependent floor stays **at or
below** the genuine §24 fixed-period density `1/(3 q₀)` for EVERY `q₀ ≥ 1`.  This is exactly what makes
the density atom dischargeable for all `Q` (the manuscript `ρ₀(Q)` is calibrated below the §24 floor). -/
theorem rhoDQ_le_third {q0 : ℕ} (hq0 : 0 < q0) :
    rhoDQ q0 ≤ (1 : ℝ) / ((3 * q0 : ℕ) : ℝ) := by
  have hq0R : (0 : ℝ) < (q0 : ℝ) := by exact_mod_cast hq0
  have h3cast : ((3 * q0 : ℕ) : ℝ) = 3 * (q0 : ℝ) := by push_cast; ring
  have h4 : (0 : ℝ) < 4 * (q0 : ℝ) := mul_pos (by norm_num) hq0R
  have h3 : (0 : ℝ) < 3 * (q0 : ℝ) := mul_pos (by norm_num) hq0R
  unfold rhoDQ
  rw [h3cast, div_le_div_iff₀ h4 h3]
  nlinarith [hq0R]

/-- `ρ_D(q₀) = 1/(4 q₀) ≤ 1/4 = manuscriptRhoD` for `q₀ ≥ 1`: the Q-dependent floor never exceeds the
pinned `Q = 1` value. -/
theorem rhoDQ_le_manuscriptRhoD {q0 : ℕ} (hq0 : 0 < q0) : rhoDQ q0 ≤ manuscriptRhoD := by
  have hq0R : (1 : ℝ) ≤ (q0 : ℝ) := by exact_mod_cast hq0
  have hmr : (manuscriptRhoD : ℝ) = 1 / 4 := rfl
  have h4 : (0 : ℝ) < 4 * (q0 : ℝ) := by nlinarith [hq0R]
  unfold rhoDQ
  rw [hmr, div_le_div_iff₀ h4 (by norm_num : (0 : ℝ) < 4)]
  nlinarith [hq0R]

/-- At `q₀ = 1` the Q-dependent floor recovers the pinned `manuscriptRhoD = 1/4`: the pin is exactly
the `Q = 1` specialization of `ρ_D(q₀)`. -/
theorem rhoDQ_one_eq : rhoDQ 1 = manuscriptRhoD := by
  unfold rhoDQ manuscriptRhoD; norm_num

/-- **The precise diagnosis of the reported defect.**  For `q₀ ≥ 2` the pinned `manuscriptRhoD = 1/4`
STRICTLY exceeds the genuine §24 fixed-period density floor `1/(3 q₀)`.  Hence the `manuscriptRhoD`-form
density atom `manuscriptRhoD · p ≤ wt(period)` is NOT derivable from the §24 bound `1/(3 q₀) · p ≤
wt(period)` once `q₀ ≥ 2` — it is valid only at `q₀ = 1`.  The Q-dependent `rhoDQ q₀` (`rhoDQ_le_third`)
repairs this for all `Q`. -/
theorem manuscriptRhoD_gt_third_of_two_le {q0 : ℕ} (hq0 : 2 ≤ q0) :
    (1 : ℝ) / ((3 * q0 : ℕ) : ℝ) < manuscriptRhoD := by
  have hq0R : (2 : ℝ) ≤ (q0 : ℝ) := by exact_mod_cast hq0
  have h3cast : ((3 * q0 : ℕ) : ℝ) = 3 * (q0 : ℝ) := by push_cast; ring
  have h3 : (0 : ℝ) < 3 * (q0 : ℝ) := by nlinarith [hq0R]
  have hmr : (manuscriptRhoD : ℝ) = 1 / 4 := rfl
  rw [h3cast, hmr, div_lt_div_iff₀ h3 (by norm_num : (0 : ℝ) < 4)]
  nlinarith [hq0R]

/-! ## 2.  The shared SDR density atom, made generic in the rate `ρ`

These are the `ρ`-parametric forms of `SDRDensityCore.windowWeight_ge_rhoD_mul_L` and
`SemiperiodicWindowCore.windowWeight_ge_rhoD_mul_L_of_match`: the proofs use only `0 ≤ ρ` (never any
property of `manuscriptRhoD`), so the density mechanism is genuinely parametric and instantiates at any
floor — in particular at the Q-dependent `rhoDQ q₀`. -/

/-- **The shared semiperiodic-density atom, generic rate form.**  For a windowed `PeriodicOn d m len p`
whose period block has density `≥ ρ` (`ρ · p ≤ windowWeight d m p`) and whose length covers the period
(`L + p ≤ len + 1`), the window packs `ρ · L ≤ windowWeight d m len`.  Identical to
`SDRDensityCore.windowWeight_ge_rhoD_mul_L` but with an arbitrary nonnegative rate `ρ`. -/
theorem windowWeight_ge_floor_mul_L (ρ : ℝ) (hρ : 0 ≤ ρ) {d : ℕ → ℕ} {m p len L : ℕ}
    (hp : 0 < p)
    (hper : PeriodicOn d m len p)
    (hdens : ρ * (p : ℝ) ≤ (windowWeight d m p : ℝ))
    (hlen : L + p ≤ len + 1) :
    ρ * (L : ℝ) ≤ (windowWeight d m len : ℝ) := by
  have hcount : (len / p) * windowWeight d m p ≤ windowWeight d m len :=
    periodicWindow_count_lower hper
  have hmpL : L ≤ (len / p) * p := by
    have hdm : p * (len / p) + len % p = len := Nat.div_add_mod len p
    have hmod : len % p < p := Nat.mod_lt len hp
    have hcomm : (len / p) * p = p * (len / p) := Nat.mul_comm _ _
    omega
  have hmbR : (0 : ℝ) ≤ ((len / p : ℕ) : ℝ) := by positivity
  have step1 :
      ((len / p : ℕ) : ℝ) * (ρ * (p : ℝ))
        ≤ ((len / p : ℕ) : ℝ) * (windowWeight d m p : ℝ) :=
    mul_le_mul_of_nonneg_left hdens hmbR
  have hmpLR : (L : ℝ) ≤ (((len / p) * p : ℕ) : ℝ) := by exact_mod_cast hmpL
  have step2 :
      ρ * (L : ℝ) ≤ ρ * (((len / p) * p : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left hmpLR hρ
  have hcountR :
      (((len / p) * windowWeight d m p : ℕ) : ℝ) ≤ (windowWeight d m len : ℝ) := by
    exact_mod_cast hcount
  calc ρ * (L : ℝ)
      ≤ ρ * (((len / p) * p : ℕ) : ℝ) := step2
    _ = ((len / p : ℕ) : ℝ) * (ρ * (p : ℝ)) := by push_cast; ring
    _ ≤ ((len / p : ℕ) : ℝ) * (windowWeight d m p : ℝ) := step1
    _ = (((len / p) * windowWeight d m p : ℕ) : ℝ) := by push_cast; ring
    _ ≤ (windowWeight d m len : ℝ) := hcountR

/-- **The shared semiperiodic-density atom, generic rate + match form.**  For a §25.1 window-match to a
model word `w` that is `PeriodicOn` the window with period `p` (`0 < p`, `p ≤ len`) of density `≥ ρ`,
and the length calibration `L + p ≤ len + 1`, the actual word packs `ρ · L ≤ windowWeight d start len`.
Identical to `SemiperiodicWindowCore.windowWeight_ge_rhoD_mul_L_of_match` but with an arbitrary
nonnegative rate `ρ`. -/
theorem windowWeight_ge_floor_mul_L_of_match (ρ : ℝ) (hρ : 0 ≤ ρ) {d w : ℕ → ℕ} {start len p L : ℕ}
    (hp : 0 < p)
    (hm : WindowMatch d w start len)
    (hper : PeriodicOn w 0 len p)
    (hdens : ρ * (p : ℝ) ≤ (windowWeight w 0 p : ℝ))
    (hp_le : p ≤ len)
    (hlen : L + p ≤ len + 1) :
    ρ * (L : ℝ) ≤ (windowWeight d start len : ℝ) := by
  have hperd : PeriodicOn d start len p := periodicOn_of_match hm hper
  have hdens' : ρ * (p : ℝ) ≤ (windowWeight d start p : ℝ) := by
    rw [windowWeight_congr_of_match hm hp_le]; exact hdens
  exact windowWeight_ge_floor_mul_L ρ hρ hp hperd hdens' hlen

/-! ## 3.  The density atom, CORRECT FOR ALL Q — the orbit word at rate `1/(4 q₀)`

For the residual-center orbit word `dyadicDigit q₀ a` (`q₀ > 1` odd, `a` coprime to `q₀`) the genuine
§24 floor is `(1/(3 q₀)) · t ≤ wt(period)` (`FailingShellPeriodicityCore.dyadicDigit_density_floor`,
proved unconditionally).  Since `rhoDQ q₀ = 1/(4 q₀) ≤ 1/(3 q₀)` for every `q₀`, the Q-dependent floor
holds for EVERY odd part `q₀` — never just `q₀ = 1`. -/

/-- **The Q-dependent density floor on the orbit word — correct for ALL Q.**  One full period of
`dyadicDigit q₀ a` (`q₀ > 1` odd, `a` coprime to `q₀`) packs `(1/(4 q₀)) · t ≤ wt`, where
`t = ord_{q₀}(2)`.  Derived from the genuine `1/(3 q₀)` §24 floor via `rhoDQ_le_third`. -/
theorem dyadicDigit_density_floor_rhoDQ {q0 a : ℕ} (hq0 : 1 < q0) (hodd : Odd q0)
    (hcop : Nat.Coprime a q0) :
    rhoDQ q0 * (orderOf (2 : ZMod q0) : ℝ)
      ≤ (windowWeight (dyadicDigit q0 a) 0 (orderOf (2 : ZMod q0)) : ℝ) := by
  have hfloor := dyadicDigit_density_floor hq0 hodd hcop
  have htnn : (0 : ℝ) ≤ (orderOf (2 : ZMod q0) : ℝ) := by positivity
  have hle : rhoDQ q0 ≤ (1 : ℝ) / ((3 * q0 : ℕ) : ℝ) := rhoDQ_le_third (by omega)
  exact le_trans (mul_le_mul_of_nonneg_right hle htnn) hfloor

/-- **The matched-window density atom on the ACTUAL word — correct for ALL Q.**  From a §25.1
window-match of the actual word `d` to the residual-center orbit word `dyadicDigit q₀ a` over
`[start, start+len)` (`q₀ > 1` odd, `a` coprime to `q₀`), with the period inside the window
(`ord_{q₀}(2) ≤ len`) and the length calibration `L + ord_{q₀}(2) ≤ len + 1`, the actual descent window
packs `(1/(4 q₀)) · L ≤ windowWeight d start len`.  This is the shared SDR atom on the actual word, now
honest for every `Q`. -/
theorem windowWeight_ge_rhoDQ_of_dyadicMatch {d : ℕ → ℕ} {start len L q0 a : ℕ}
    (hq0 : 1 < q0) (hodd : Odd q0) (hcop : Nat.Coprime a q0)
    (hle : orderOf (2 : ZMod q0) ≤ len)
    (hlen : L + orderOf (2 : ZMod q0) ≤ len + 1)
    (hmatch : WindowMatch d (dyadicDigit q0 a) start len) :
    rhoDQ q0 * (L : ℝ) ≤ (windowWeight d start len : ℝ) := by
  have hppos : 0 < orderOf (2 : ZMod q0) :=
    orderOf_pos_iff.mpr (isOfFinOrder_two_zmod hq0 hodd)
  have hper : PeriodicOn (dyadicDigit q0 a) 0 len (orderOf (2 : ZMod q0)) :=
    orbitWord_periodicOn hq0 hodd a 0 len
  have hdens := dyadicDigit_density_floor_rhoDQ hq0 hodd hcop
  exact windowWeight_ge_floor_mul_L_of_match (rhoDQ q0) (le_of_lt (rhoDQ_pos (by omega)))
    hppos hmatch hper hdens hle hlen

/-! ## 4.  Tower composition — the Q-dependent atom feeds the parametric `Class2IndexSDR.ofIntervals`

`TowerSDRCore.Class2IndexSDR.ofIntervals` is already parametric in the rate `ρ_D`.  Feeding it the
Q-dependent floor `rhoDQ q₀` (with the per-start orbit-word matches supplying the floor) builds a
genuine `Class2IndexSDR ctx`, hence the Tower capacity floor `routedClassMassOf … 2 ≤ ξX/6` — the exact
frontier budget input — at the correct Q-dependent rate, for all `Q`.  The orthogonal maximal-disjoint
selection (`hlands`/`hdisj`) and the `L`-free scalar / K.4 data (`hcalibE`/`huniform`, now with `rhoDQ
q₀`) are taken as inputs, exactly as in the original parametric builders. -/

/-- **`Class2IndexSDR` from a per-fibre family of §25.1 orbit-word matches, at rate `1/(4 q₀)`.**  The
Q-dependent matched-window atom (`windowWeight_ge_rhoDQ_of_dyadicMatch`) supplies the per-block floor
`rhoDQ q₀ · L ≤ #(idxOwned k)` for every class-2 start; the selection and scalar data are inputs.  This
is the Q-correct analogue of `SDRDensityCore.Class2IndexSDR.ofSemiperiodicDensity` /
`SemiperiodicWindowCore.Class2IndexSDR.ofMatchedWindows`. -/
def Class2IndexSDR.ofDyadicMatchesRhoDQ
    (ctx : ActualFailureContext)
    (a : ℕ → ℕ) (hainj : Function.Injective a)
    (q0 : ℕ) (hq0 : 1 < q0) (hodd : Odd q0)
    (eps : ℝ) (Lnat : ℕ) (hLpos : 0 < Lnat)
    (hYnn : 0 ≤ ctx.n24CarryData.Y)
    (hcalibE : 2 * ctx.n24CarryData.Y ≤ 2 * eps * (Lnat : ℝ))
    (huniform : 2 * (erdos260Constants.c0 * eps) ≤ erdos260Constants.ξ / 6 * rhoDQ q0)
    (hbdry : 0 ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2)
    (lo mwin lenw cen : ℕ → ℕ)
    (hcop : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
        Nat.Coprime (cen k) q0)
    (hle : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
        orderOf (2 : ZMod q0) ≤ lenw k)
    (hlenL : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
        Lnat + orderOf (2 : ZMod q0) ≤ lenw k + 1)
    (hmatch : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
        WindowMatch ctx.shell.d (dyadicDigit q0 (cen k)) (mwin k) (lenw k))
    (hlands : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
        ∀ j ∈ Finset.Ico (lo k) (lo k + windowWeight ctx.shell.d (mwin k) (lenw k)),
          a j ∈ supportShell ctx.d ctx.X)
    (hdisj : ∀ j ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
        ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2, j ≠ k →
        Disjoint (Finset.Ico (lo j) (lo j + windowWeight ctx.shell.d (mwin j) (lenw j)))
          (Finset.Ico (lo k) (lo k + windowWeight ctx.shell.d (mwin k) (lenw k)))) :
    Class2IndexSDR ctx :=
  Class2IndexSDR.ofIntervals ctx a hainj (rhoDQ q0) eps (Lnat : ℝ)
    (rhoDQ_pos (by omega)) (by exact_mod_cast hLpos) hYnn hcalibE huniform hbdry
    lo (fun k => windowWeight ctx.shell.d (mwin k) (lenw k))
    hlands hdisj
    (fun k hk => windowWeight_ge_rhoDQ_of_dyadicMatch hq0 hodd (hcop k hk) (hle k hk)
      (hlenL k hk) (hmatch k hk))

/-- **The Tower capacity floor `routedClassMassOf … 2 ≤ ξX/6` at the Q-dependent rate `1/(4 q₀)`.**  The
exact frontier budget input for class 2, now derived from the Q-correct density atom for all `Q`. -/
theorem towerSubMass_of_dyadicMatchesRhoDQ
    (ctx : ActualFailureContext)
    (a : ℕ → ℕ) (hainj : Function.Injective a)
    (q0 : ℕ) (hq0 : 1 < q0) (hodd : Odd q0)
    (eps : ℝ) (Lnat : ℕ) (hLpos : 0 < Lnat)
    (hYnn : 0 ≤ ctx.n24CarryData.Y)
    (hcalibE : 2 * ctx.n24CarryData.Y ≤ 2 * eps * (Lnat : ℝ))
    (huniform : 2 * (erdos260Constants.c0 * eps) ≤ erdos260Constants.ξ / 6 * rhoDQ q0)
    (hbdry : 0 ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2)
    (lo mwin lenw cen : ℕ → ℕ)
    (hcop : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
        Nat.Coprime (cen k) q0)
    (hle : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
        orderOf (2 : ZMod q0) ≤ lenw k)
    (hlenL : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
        Lnat + orderOf (2 : ZMod q0) ≤ lenw k + 1)
    (hmatch : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
        WindowMatch ctx.shell.d (dyadicDigit q0 (cen k)) (mwin k) (lenw k))
    (hlands : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
        ∀ j ∈ Finset.Ico (lo k) (lo k + windowWeight ctx.shell.d (mwin k) (lenw k)),
          a j ∈ supportShell ctx.d ctx.X)
    (hdisj : ∀ j ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
        ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2, j ≠ k →
        Disjoint (Finset.Ico (lo j) (lo j + windowWeight ctx.shell.d (mwin j) (lenw j)))
          (Finset.Ico (lo k) (lo k + windowWeight ctx.shell.d (mwin k) (lenw k)))) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
      ≤ erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  (Class2IndexSDR.ofDyadicMatchesRhoDQ ctx a hainj q0 hq0 hodd eps Lnat hLpos hYnn hcalibE huniform
    hbdry lo mwin lenw cen hcop hle hlenL hmatch hlands hdisj).htowerSubMass

/-! ## 5.  DensePack composition — the K.1.1 coarea hit-density at rate `1/(4 q₀)`

The DensePack reduction injects a shell-contained window of hits into the K.1 support packet
(`SDRDensityCore.windowFilter_card_le_supportWindow`, `ρ_D`-free).  Flooring the Q-dependent atom gives
`⌊(1/(4 q₀)) · L⌋ ≤ |supportWindow(m)|` — the coarea hit-density at the descent endpoint, for all `Q`. -/

/-- **The K.1.1 coarea hit-density at the Q-dependent rate `1/(4 q₀)`.**  A shell-contained descent
window matching the residual-center orbit word `dyadicDigit q₀ a` packs
`⌊(1/(4 q₀)) · L⌋ ≤ |supportWindow(m)|`.  This is the Q-correct replacement for the pinned
`proofV4DensePackMinHits = ⌊manuscriptRhoD · L⌋` floor, valid for all `Q`. -/
theorem densePackMinHitsFloor_rhoDQ_le_supportWindow
    (shell : FailingDyadicShell) {m L q0 a : ℕ}
    (hlo : shell.X < m)
    (hhi : m + proofV4DensePackSpread shell ≤ 2 * shell.X)
    (hq0 : 1 < q0) (hodd : Odd q0) (hcop : Nat.Coprime a q0)
    (hle : orderOf (2 : ZMod q0) ≤ proofV4DensePackSpread shell + 1)
    (hlen : L + orderOf (2 : ZMod q0) ≤ proofV4DensePackSpread shell + 2)
    (hmatch : WindowMatch shell.d (dyadicDigit q0 a) m (proofV4DensePackSpread shell + 1)) :
    Nat.floor (rhoDQ q0 * (L : ℝ)) ≤ (proofV4DensePackSupportWindow shell m).card := by
  have hatom : rhoDQ q0 * (L : ℝ)
      ≤ (windowWeight shell.d m (proofV4DensePackSpread shell + 1) : ℝ) :=
    windowWeight_ge_rhoDQ_of_dyadicMatch hq0 hodd hcop hle (by omega) hmatch
  have hge0 : (0 : ℝ) ≤ rhoDQ q0 * (L : ℝ) :=
    mul_nonneg (le_of_lt (rhoDQ_pos (by omega))) (by positivity)
  have hfloorNat : Nat.floor (rhoDQ q0 * (L : ℝ))
      ≤ windowWeight shell.d m (proofV4DensePackSpread shell + 1) := by
    have hcast : (Nat.floor (rhoDQ q0 * (L : ℝ)) : ℝ)
        ≤ (windowWeight shell.d m (proofV4DensePackSpread shell + 1) : ℝ) :=
      le_trans (Nat.floor_le hge0) hatom
    exact_mod_cast hcast
  rw [windowWeight_eq_filter_card shell.hd] at hfloorNat
  exact le_trans hfloorNat (windowFilter_card_le_supportWindow shell hlo hhi)

/-! ## 6.  Threading `q₀ = oddPart Q` — the drop-in `hdens` family, dischargeable for ALL Q

The existing §25.1 residual structures (`DescentCylinderMatchData.hdens`,
`SingularSquareCertificate.hdens`) carry the §24 floor at rate `manuscriptRhoD` over the actual shell's
reduced residual-center denominator `q₀ = (canonicalCenter ctx).q0` (`> 1`, odd, by
`runFOfShell_q0_gt_one` / `_q0_odd`) — dischargeable only at `q₀ = 1`.  Recalibrated to `rhoDQ q₀`, the
same family is dischargeable for EVERY `ctx` (every `Q`), needing only the genuine coprimality of the
per-start residue numerators. -/

/-- **The §24 density floor, Q-dependent and dischargeable for ALL Q.**  In exactly the shape of the
`hdens` field of `DescentCylinderMatchData` / `SingularSquareCertificate` (over the actual shell's
reduced residual-center denominator `q₀ = (canonicalCenter ctx).q0`), but at the genuine Q-dependent
rate `rhoDQ q₀ = 1/(4 q₀)` instead of the `Q = 1`-only `manuscriptRhoD`.  Given the genuine coprimality
of the per-start numerators, this holds for every genuine DensePack start, for every `Q` — the precise
recalibration that repairs the flagged defect. -/
theorem descentDensityFloor_rhoDQ_all_Q (ctx : ActualFailureContext)
    (a : ℕ → ℕ)
    (hcop : ∀ k ∈ genuineDensePackStarts ctx,
        Nat.Coprime (a k) (canonicalCenter ctx).q0) :
    ∀ k ∈ genuineDensePackStarts ctx,
      rhoDQ (canonicalCenter ctx).q0 * (orderOf (2 : ZMod (canonicalCenter ctx).q0) : ℝ)
        ≤ (windowWeight (dyadicDigit (canonicalCenter ctx).q0 (a k)) 0
            (orderOf (2 : ZMod (canonicalCenter ctx).q0)) : ℝ) := by
  intro k hk
  exact dyadicDigit_density_floor_rhoDQ (runFOfShell_q0_gt_one ctx) (runFOfShell_q0_odd ctx)
    (hcop k hk)

/-! ## 7.  Honest residual / status inventory -/

/-- The precise status of the `ρ_D` Q-calibration after this standalone module. -/
def rhoDQCalibrationResiduals : List String :=
  [ "GOAL — fix the ρ_D Q-calibration so the shared density atom ρ_D·L ≤ windowWeight is correct for " ++
      "ALL Q (the pinned manuscriptRhoD = 1/4 is valid only at Q = 1). Least-invasive route: instantiate " ++
      "the parametric density chain with the genuine Q-dependent floor rhoDQ q₀ = 1/(4 q₀), q₀ = oddPart " ++
      "Q, WITHOUT changing the global manuscriptRhoD.",
    "CLOSED (calibration) — rhoDQ q₀ = 1/(4 q₀): 0 < rhoDQ q₀ ≤ 1/(3 q₀) (rhoDQ_le_third) for EVERY " ++
      "q₀ ≥ 1, so the Q-dependent floor stays at/below the genuine §24 fixed-period density 1/(3 q₀); " ++
      "rhoDQ q₀ ≤ manuscriptRhoD (rhoDQ_le_manuscriptRhoD) and rhoDQ 1 = manuscriptRhoD (rhoDQ_one_eq).",
    "CLOSED (diagnosis) — manuscriptRhoD_gt_third_of_two_le: for q₀ ≥ 2 the pinned manuscriptRhoD = 1/4 " ++
      "STRICTLY exceeds the genuine §24 floor 1/(3 q₀), so the manuscriptRhoD-form atom cannot be " ++
      "discharged from §24 once q₀ ≥ 2 — exactly the reported defect, now repaired by rhoDQ.",
    "CLOSED (parametric atoms) — windowWeight_ge_floor_mul_L / _of_match: the SDR density atom is " ++
      "generic in the rate ρ (0 ≤ ρ); the deep periodic-count heart periodicWindow_count_lower is ρ-free, " ++
      "so the mechanism instantiates at any floor — in particular rhoDQ q₀.",
    "CLOSED (density atom, ALL Q) — dyadicDigit_density_floor_rhoDQ: (1/(4 q₀))·t ≤ wt(period) on the " ++
      "orbit word dyadicDigit q₀ a (q₀ > 1 odd, a coprime q₀) for EVERY q₀, from the genuine 1/(3 q₀) §24 " ++
      "floor. windowWeight_ge_rhoDQ_of_dyadicMatch transfers it to the ACTUAL word along a §25.1 match: " ++
      "(1/(4 q₀))·L ≤ windowWeight d start len, for every Q.",
    "CLOSED (Tower composition) — Class2IndexSDR.ofDyadicMatchesRhoDQ feeds the Q-dependent atom into the " ++
      "parametric Class2IndexSDR.ofIntervals at rate rhoDQ q₀; towerSubMass_of_dyadicMatchesRhoDQ then " ++
      "yields the Tower capacity floor routedClassMassOf … 2 ≤ ξX/6 (the frontier budget input) for ALL Q.",
    "CLOSED (DensePack composition) — densePackMinHitsFloor_rhoDQ_le_supportWindow: the K.1.1 coarea " ++
      "hit-density ⌊(1/(4 q₀))·L⌋ ≤ |supportWindow(m)| via the ρ_D-free shell injection " ++
      "windowFilter_card_le_supportWindow, for ALL Q (the Q-correct replacement of the pinned " ++
      "proofV4DensePackMinHits = ⌊manuscriptRhoD·L⌋).",
    "CLOSED (drop-in hdens, ALL Q) — descentDensityFloor_rhoDQ_all_Q: the per-start §24 floor in exactly " ++
      "the DescentCylinderMatchData.hdens / SingularSquareCertificate.hdens shape, at rate " ++
      "rhoDQ (canonicalCenter ctx).q0, dischargeable for EVERY ctx (every Q) from the genuine coprimality " ++
      "of the residue numerators — where the manuscriptRhoD-pinned field is dischargeable only at q₀ = 1.",
    "AUDIT (composes, global constant untouched) — erdos260_of_minimalResidualV3 does not mention " ++
      "manuscriptRhoD in its type (Tower field = Class2ActiveFloorCount, DensePack field = " ++
      "DensePackCoareaSupport, neither uses ρ_D); manuscriptRhoD enters only the density-reduction lemmas " ++
      "as a hypothesis. This module supplies the Q-correct rate for those hypotheses and re-derives the " ++
      "same Tower floor through the parametric SDR, leaving Constants.manuscriptRhoD and all existing " ++
      "green modules untouched.",
    "NON-DEGENERATE — rhoDQ q₀ > 0 (rhoDQ_pos); every floor packs a POSITIVE Q-dependent density; the " ++
      "periodic count is the genuine telescoped block weight inherited from SDRDensityCore, no empty / " ++
      "zero-floor / vacuous shortcut." ]

theorem rhoDQCalibrationResiduals_nonempty : rhoDQCalibrationResiduals ≠ [] := by
  simp [rhoDQCalibrationResiduals]

/-! ## 8.  Axiom-cleanliness audit -/

#print axioms rhoDQ_pos
#print axioms rhoDQ_le_third
#print axioms rhoDQ_le_manuscriptRhoD
#print axioms rhoDQ_one_eq
#print axioms manuscriptRhoD_gt_third_of_two_le
#print axioms windowWeight_ge_floor_mul_L
#print axioms windowWeight_ge_floor_mul_L_of_match
#print axioms dyadicDigit_density_floor_rhoDQ
#print axioms windowWeight_ge_rhoDQ_of_dyadicMatch
#print axioms Class2IndexSDR.ofDyadicMatchesRhoDQ
#print axioms towerSubMass_of_dyadicMatchesRhoDQ
#print axioms densePackMinHitsFloor_rhoDQ_le_supportWindow
#print axioms descentDensityFloor_rhoDQ_all_Q

end

end Erdos260
