import Erdos260.Erdos260KeystoneCapstone
import Erdos260.ChernoffClass0Routing
import Erdos260.GenuineObstructionRoutingCore
import Erdos260.DensePackInjectionCore
import Erdos260.ChernoffClass0DatumClosure
import Erdos260.RunClass5BoundaryClosure
import Erdos260.CNLClass1DeepClosure
import Erdos260.CNLClass1Closure
import Erdos260.ReturnAnchoredUnconditional
import Erdos260.CNLMultiChargeUnconditional

/-!
# Exit-light cycle certificates (`ExitLightCycleCertificates`)

The wave-20 mechanical target on the off-pin exit-mass core lane: hunt and certify
`(q, K₀)` pairs OUTSIDE the current survivor table whose slope cycles are exit-light
enough to feed `EmcSpacedShareDatum` at deep scales, and fire whatever part of
`ExitMassControlOffPin` the in-tree machinery supports at them.

## The survey (complete scan, `q` odd in `[3, 2000)`, ALL `1 ≤ K₀ < q`)

999000 pairs; EVERY pair is purely periodic from index 1 (the odd-numerator step is
a bijection, so no pair is lost to a transient).  Outcome:

* **EXIT-SILENT pairs** (every one-period band `≥ 5`): EXACTLY 384 pairs over 62
  moduli (`q = 31, 63, 93, 127, ..., 1953` - the moduli with a divisor `2^g - 1`,
  `g ≥ 5`), periods 1-2.  At these pairs the genuine route is IDENTICALLY 0 on the
  starts, so classes 1-5 routed fibres are EMPTY - the `ExitMassControlOffPin`
  conclusion holds OUTRIGHT (masses are `0 ≤ (31/1536)·X`), with NO deep, pin,
  band, share, or regime hypothesis.  34 of them have `q < 200` (they are not in
  any survivor table: the sweeps kept only band-4-bearing pairs).
* **`b₄ = 1` deep-clearing pairs** (`c ≥ 50`): 4578 pairs over 36 moduli
  (`q = 303, 909, ..., 1897`; min period 50, max 70+; NONE with `q < 200`) - the
  wave-20 hunt target exists in abundance just past the table horizon.  These feed
  classes 1/2 (the band-4 readers): the fibre spacing is CERTIFIED; the share is the
  open equidistribution input.
* **Full off-pin regime feasibility** (classes 3/4/5 each empty or spaced `≥ 50`,
  measured by the MAXIMAL spacing modulus = gcd of the class band-residue
  differences with `c`): ONLY the 384 exit-silent pairs.  NO pair in range carries a
  nonzero class-3/4/5 fibre with certifiable spacing ≥ 50 - the singleton/spacing
  route to the nonzero-share regime is EMPTY below `q = 2000`.

## The exact deep boundary (sharpens the wave-20 note)

The in-tree forced threshold `768·((63+c)/c)·b ≤ 31·c` at `b = 1` clears IFF
`c ≥ 50` (`elcDeepThresholdClears` / `elcDeepThresholdBlocked`): the overlap factor
is 2 (not 1) on `50 ≤ c ≤ 63` and `1536 ≤ 31·c` already holds at `c = 50` -
the brief's real-variable estimate `c ≥ 54` and the wave-20 note's `c ≥ 64` are
both safely above the true boundary.

## The share/tiling verdict (NEGATIVE at `b ≥ 1`; the b = 0 route FIRES)

`c`-spacing + reach containment do NOT imply the share `c·fibreExit ≤ 1·totalExit`:
`elcShare_not_from_spacing_alone` is a formal counterexample (weight concentrated on
the fibre's residue).  The in-tree overlap bound `emc2_fibreDevMass_le_overlap`
bounds the fibre's deviation mass by overlap copies of the fibre's OWN restricted
exit mass; it cannot compare fibre against total - and at deep scales `r ≥ 63`
grows with `L`, so window tiling (`r + 1 ≤ c`) eventually fails for every fixed
`c`.  The `b = 1` share IS the equidistribution content and stays open.  What DOES
close: at EMPTY fibres the `b = 0` spaced-share datum is proved outright
(`elcDatum_of_empty`), and the exit-silent stratum closes the whole off-pin demand
(`elcOffPinCaps_of_mem`).

## Wiring (additive, v19/v20 shapes)

`ElcOffPinUncoveredResidual` (the off-pin demand at deep pin-free contexts whose
datum is NOT exit-silent) → `ExitMassControlOffPin`
(`elcOffPin_of_uncoveredResidual`); + `DeepOrbitPinVoiding` → the FULL
`ExitMassControlCore` (`elcCore_of_uncoveredResidual_and_voiding`), keystone form
`elcKeystoneCore_of_uncoveredResidual` (consuming `Erdos260KeystoneResidual.
deepOrbitPin`).  At the 10 certified `b₄ = 1` pairs: class-1/2 spacing PROVED
(`elcSpacing_of_band4Cert`), per-pair caps conditional on exactly share + ctx regime
(`elcClass2Cap_*`), and the class-1 CORRECTED ABSORPTION shape at `q ≥ 200` data
(`elcClass1Absorption_*`) - the first deep-threshold-clearing certified spaced-share
parameters (every `sreClass1ThresholdTable` row overshoots:
`emcDeepProportionalClearedPairs_eq_nil`).

No `sorry`, no `admit`, no new `axiom`, no `native_decide` (`decide` only on small
closed numeric / Fin / list-literal goals); additive only - no existing module is
edited, NOT root-wired (built standalone as `Erdos260.ExitLightCycleCertificates`).
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

/-! ## Part 0.  The generic engines -/

/-- Equal `(· - 1) % c` residues of positive indices differ by a multiple of `c`. -/
theorem elcDvd_of_residue_eq {c x z : ℕ} (hx : 1 ≤ x) (hxz : x ≤ z)
    (h : (x - 1) % c = (z - 1) % c) : c ∣ z - x := by
  have hdvd : c ∣ (z - 1) - (x - 1) :=
    (Nat.modEq_iff_dvd' (show x - 1 ≤ z - 1 from by omega)).mp h
  rwa [show (z - 1) - (x - 1) = z - x from by omega] at hdvd

/-- **The route-0 pin from a one-period deep-band certificate**: if every residue of
one period reads the deep band `16·K_j ≤ q`, the genuine route is identically `0`
on positive indices (`genuineChargeRoute_eq_zero_iff_orbitBand`). -/
theorem elcRouteZero_of_deepCert (ctx : ActualFailureContext) {qv Kv c : ℕ}
    (hq : (class1SlopeDatum ctx).q = qv) (hK : (class1SlopeDatum ctx).K₀ = Kv)
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m → slopeOrbit qv Kv (m + c) = slopeOrbit qv Kv m)
    (hdeep : ∀ j, 1 ≤ j → j ≤ c → 16 * slopeOrbit qv Kv j ≤ qv)
    {k : ℕ} (hk : 1 ≤ k) : genuineChargeRoute ctx k = 0 := by
  rw [genuineChargeRoute_eq_zero_iff_orbitBand, hq, hK,
    slopeOrbit_eq_residue hc hper hk]
  have hmodlt : (k - 1) % c < c := Nat.mod_lt _ (by omega)
  exact hdeep _ (by omega) (by omega)

/-- **Exit-silent emptiness**: under the deep-band certificate every routed fibre of
a nonzero class is empty. -/
theorem elcFibreEmpty_of_deepCert (ctx : ActualFailureContext) {qv Kv c : ℕ}
    (hq : (class1SlopeDatum ctx).q = qv) (hK : (class1SlopeDatum ctx).K₀ = Kv)
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m → slopeOrbit qv Kv (m + c) = slopeOrbit qv Kv m)
    (hdeep : ∀ j, 1 ≤ j → j ≤ c → 16 * slopeOrbit qv Kv j ≤ qv)
    (i : Fin 7) (hi : i ≠ 0) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro k hk
  rw [mem_routedFibre] at hk
  have hk1 : 1 ≤ k := n24_starts_pos ctx (mem_highExcessStarts.mp hk.1).1
  exact hi (by rw [← hk.2, elcRouteZero_of_deepCert ctx hq hK hc hper hdeep hk1])

/-- An empty fibre meets the corrected per-class cap for free: its mass is `0`. -/
theorem elcMassCap_of_empty (ctx : ActualFailureContext) (i : Fin 7)
    (h : routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) i ≤ emcCap ctx := by
  rw [routedClassMassOf_eq_sum_fibre, h, Finset.sum_empty]
  unfold emcCap
  positivity

/-- **The `b = 0` spaced-share datum at an empty fibre is PROVED** - the share and
the numeric regime degenerate to `0 ≤ 0` / `0 ≤ 31·X`. -/
theorem elcDatum_of_empty (ctx : ActualFailureContext) (i : Fin 7)
    (h : routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅) :
    EmcSpacedShareDatum ctx i 0 1 := by
  have hre : emcFibreReach ctx i = ∅ := by
    ext x
    simp [emcFibreReach, h]
  have hz : emcFibreExitMass ctx i = 0 := by
    unfold emcFibreExitMass
    rw [hre, Finset.sum_empty]
  refine ⟨le_refl 1, ?_, ?_, ?_⟩
  · intro x hx
    rw [h] at hx
    exact absurd hx (Finset.notMem_empty x)
  · rw [hz]
    simp
  · simp

/-- Classes 1 and 2 of the genuine route read the E.13 band-4 window. -/
theorem elcFibreBand4 (ctx : ActualFailureContext) {i : Fin 7} (hi : i = 1 ∨ i = 2)
    {k : ℕ} (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i) :
    canonGap (class1SlopeDatum ctx).q
      (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 4 := by
  have hk2 := ((mem_routedFibre _ _ _ _).mp hk).2
  rcases hi with rfl | rfl
  · obtain ⟨ht, -, -, -⟩ := (genuineChargeRoute_eq_one_iff ctx k).mp hk2
    rw [towerClsOfShell_eq_band] at ht
    exact (towerExitClassOfGap_eq_cnlTail_iff _).mp ht
  · obtain ⟨ht, -, -⟩ := (genuineChargeRoute_eq_two_iff ctx k).mp hk2
    rw [towerClsOfShell_eq_band] at ht
    exact (towerExitClassOfGap_eq_cnlTail_iff _).mp ht

/-- A band-4 reading pins the index residue to the certified singleton slot. -/
theorem elcBand4Residue_of_cert (ctx : ActualFailureContext) {qv Kv c j4 : ℕ}
    (hq : (class1SlopeDatum ctx).q = qv) (hK : (class1SlopeDatum ctx).K₀ = Kv)
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m → slopeOrbit qv Kv (m + c) = slopeOrbit qv Kv m)
    (hb4 : ∀ j, 1 ≤ j → j ≤ c → canonGap qv (slopeOrbit qv Kv j) = 4 → j = j4)
    {k : ℕ} (hk : 1 ≤ k)
    (hband : canonGap (class1SlopeDatum ctx).q
      (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ k) = 4) :
    (k - 1) % c + 1 = j4 := by
  rw [hq, hK, slopeOrbit_eq_residue hc hper hk] at hband
  have hmodlt : (k - 1) % c < c := Nat.mod_lt _ (by omega)
  exact hb4 _ (by omega) (by omega) hband

/-- **The certified spacing**: a band-4 SINGLETON residue certificate makes the
class-1 and class-2 fibres `c`-spaced - the exact spacing conjunct of
`EmcSpacedShareDatum`. -/
theorem elcSpacing_of_band4Cert (ctx : ActualFailureContext) {qv Kv c j4 : ℕ}
    (hq : (class1SlopeDatum ctx).q = qv) (hK : (class1SlopeDatum ctx).K₀ = Kv)
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m → slopeOrbit qv Kv (m + c) = slopeOrbit qv Kv m)
    (hb4 : ∀ j, 1 ≤ j → j ≤ c → canonGap qv (slopeOrbit qv Kv j) = 4 → j = j4)
    (i : Fin 7) (hi : i = 1 ∨ i = 2) :
    ∀ x ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i,
      ∀ z ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i,
        x ≤ z → c ∣ z - x := by
  intro x hx z hz hxz
  have hx1 : 1 ≤ x :=
    n24_starts_pos ctx (mem_highExcessStarts.mp ((mem_routedFibre _ _ _ _).mp hx).1).1
  have hz1 : 1 ≤ z :=
    n24_starts_pos ctx (mem_highExcessStarts.mp ((mem_routedFibre _ _ _ _).mp hz).1).1
  have hxr := elcBand4Residue_of_cert ctx hq hK hc hper hb4 hx1
    (elcFibreBand4 ctx hi hx)
  have hzr := elcBand4Residue_of_cert ctx hq hK hc hper hb4 hz1
    (elcFibreBand4 ctx hi hz)
  rw [← hzr] at hxr
  exact elcDvd_of_residue_eq hx1 hxz (Nat.add_right_cancel hxr)

/-- **The `b = 1` datum from a band-4 singleton certificate**: spacing is supplied by
the certificate; the share and the per-context numeric regime are the EXACT open
hypotheses (the equidistribution content). -/
theorem elcDatum_of_band4Cert (ctx : ActualFailureContext) {qv Kv c j4 : ℕ}
    (hq : (class1SlopeDatum ctx).q = qv) (hK : (class1SlopeDatum ctx).K₀ = Kv)
    (hc : 1 ≤ c)
    (hret : slopeOrbit qv Kv (1 + c) = slopeOrbit qv Kv 1)
    (hb4 : ∀ j, 1 ≤ j → j ≤ c → canonGap qv (slopeOrbit qv Kv j) = 4 → j = j4)
    (i : Fin 7) (hi : i = 1 ∨ i = 2)
    (hshare : c * emcFibreExitMass ctx i ≤ 1 * emExitMass ctx)
    (hreg : 1536 * (((ctx.n24CarryData.r + c) / c)
          * (1 * ((emW ctx + ctx.n24CarryData.r)
              * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))))
        ≤ 31 * (c * ctx.shell.X)) :
    EmcSpacedShareDatum ctx i 1 c :=
  ⟨hc, elcSpacing_of_band4Cert ctx hq hK hc
    (slopeOrbit_period_of_return hret) hb4 i hi, hshare, hreg⟩

/-- **The exact deep boundary, cleared side**: at `b = 1` the in-tree forced deep
threshold `768·((63+c)/c)·1 ≤ 31·c` holds for EVERY `c ≥ 50` (overlap 2 on
`50..63`, overlap 1 from `64`). -/
theorem elcDeepThresholdClears {c : ℕ} (hc : 50 ≤ c) :
    768 * (((63 + c) / c) * 1) ≤ 31 * c := by
  have h3 : (63 + c) / c < 3 := by
    rw [Nat.div_lt_iff_lt_mul (by omega : 0 < c)]
    omega
  have h2 : (63 + c) / c ≤ 2 := Nat.lt_succ_iff.mp h3
  calc 768 * (((63 + c) / c) * 1)
      = 768 * ((63 + c) / c) := by ring
    _ ≤ 768 * 2 := Nat.mul_le_mul_left 768 h2
    _ = 1536 := by norm_num
    _ ≤ 31 * 50 := by norm_num
    _ ≤ 31 * c := Nat.mul_le_mul_left 31 hc

/-- **The exact deep boundary, blocked side**: at `b = 1` every period `c ≤ 49` is
REFUSED by the forced deep threshold - `c = 50` is the true boundary (the wave-20
note's `c ≥ 64` and the real-variable estimate `c ≥ 54` are both above it). -/
theorem elcDeepThresholdBlocked {c : ℕ} (hc1 : 1 ≤ c) (hc : c ≤ 49) :
    ¬ (768 * (((63 + c) / c) * 1) ≤ 31 * c) := by
  intro hcon
  have h2 : 2 ≤ (63 + c) / c :=
    (Nat.le_div_iff_mul_le (by omega : 0 < c)).mpr (by omega)
  have h4 : 768 * 2 ≤ 768 * (((63 + c) / c) * 1) := by
    have h5 : 2 ≤ ((63 + c) / c) * 1 := by rwa [mul_one]
    exact Nat.mul_le_mul_left 768 h5
  have hfin : (1536 : ℕ) ≤ 31 * c := le_trans (by norm_num) (le_trans h4 hcon)
  have hcap : 31 * c ≤ 31 * 49 := Nat.mul_le_mul_left 31 hc
  exact absurd (le_trans hfin hcap) (by norm_num)

/-- **THE SHARE-FROM-SPACING VERDICT (NEGATIVE)**: `c`-spacing plus containment does
NOT imply the `b = 1` share `c·(restricted mass) ≤ 1·(total mass)` - the weight can
concentrate on the fibre's residue class.  The share is genuinely equidistribution
content, not a tiling consequence. -/
theorem elcShare_not_from_spacing_alone :
    ∃ (w : ℕ → ℕ) (F R : Finset ℕ) (c : ℕ), 1 ≤ c ∧ F ⊆ R
      ∧ (∀ x ∈ F, ∀ z ∈ F, x ≤ z → c ∣ z - x)
      ∧ ¬ (c * ∑ j ∈ F, w j ≤ 1 * ∑ j ∈ R, w j) := by
  refine ⟨fun j => if j = 0 then 1 else 0, {0}, {0, 1}, 2,
    by norm_num, ?_, ?_, ?_⟩
  · intro x hx
    fin_cases hx <;> simp
  · intro x hx z hz hxz
    fin_cases hx <;> fin_cases hz <;> simp
  · rw [Finset.sum_singleton,
      show ({0, 1} : Finset ℕ) = insert 0 {1} from rfl,
      Finset.sum_insert (by decide), Finset.sum_singleton]
    norm_num

/-! ## Part 1.  The 384 exit-silent certificates

Per pair: the kernel `slopeOrbit_step_eval` chain, the return collision at `1 + c`,
and the one-period deep-band readout `16·K_j ≤ q` - hence (`elcSilent_<q>_<K₀>`)
every nonzero-class routed fibre is EMPTY at any context carrying the datum. -/

/-- `(31,1)`: period `1`, cycle `[1]`, all bands deep (`≥ 5`). -/
private theorem elcCert_31_1 :
    slopeOrbit 31 1 (1 + 1) = slopeOrbit 31 1 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 31 1 j ≤ 31 := by
  have e0 : slopeOrbit 31 1 0 = 1 := rfl
  have e1 : slopeOrbit 31 1 1 = 1 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 31 1 2 = 1 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 31 1 2 = slopeOrbit 31 1 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(31,1)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_31_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 31)
    (hK : (class1SlopeDatum ctx).K₀ = 1) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_31_1.1) elcCert_31_1.2 i hi

/-- `(31,2)`: period `1`, cycle `[1]`, all bands deep (`≥ 5`). -/
private theorem elcCert_31_2 :
    slopeOrbit 31 2 (1 + 1) = slopeOrbit 31 2 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 31 2 j ≤ 31 := by
  have e0 : slopeOrbit 31 2 0 = 2 := rfl
  have e1 : slopeOrbit 31 2 1 = 1 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 31 2 2 = 1 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 31 2 2 = slopeOrbit 31 2 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(31,2)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_31_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 31)
    (hK : (class1SlopeDatum ctx).K₀ = 2) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_31_2.1) elcCert_31_2.2 i hi

/-- `(31,4)`: period `1`, cycle `[1]`, all bands deep (`≥ 5`). -/
private theorem elcCert_31_4 :
    slopeOrbit 31 4 (1 + 1) = slopeOrbit 31 4 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 31 4 j ≤ 31 := by
  have e0 : slopeOrbit 31 4 0 = 4 := rfl
  have e1 : slopeOrbit 31 4 1 = 1 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 31 4 2 = 1 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 31 4 2 = slopeOrbit 31 4 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(31,4)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_31_4 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 31)
    (hK : (class1SlopeDatum ctx).K₀ = 4) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_31_4.1) elcCert_31_4.2 i hi

/-- `(31,8)`: period `1`, cycle `[1]`, all bands deep (`≥ 5`). -/
private theorem elcCert_31_8 :
    slopeOrbit 31 8 (1 + 1) = slopeOrbit 31 8 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 31 8 j ≤ 31 := by
  have e0 : slopeOrbit 31 8 0 = 8 := rfl
  have e1 : slopeOrbit 31 8 1 = 1 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 31 8 2 = 1 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 31 8 2 = slopeOrbit 31 8 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(31,8)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_31_8 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 31)
    (hK : (class1SlopeDatum ctx).K₀ = 8) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_31_8.1) elcCert_31_8.2 i hi

/-- `(31,16)`: period `1`, cycle `[1]`, all bands deep (`≥ 5`). -/
private theorem elcCert_31_16 :
    slopeOrbit 31 16 (1 + 1) = slopeOrbit 31 16 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 31 16 j ≤ 31 := by
  have e0 : slopeOrbit 31 16 0 = 16 := rfl
  have e1 : slopeOrbit 31 16 1 = 1 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 31 16 2 = 1 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 31 16 2 = slopeOrbit 31 16 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(31,16)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_31_16 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 31)
    (hK : (class1SlopeDatum ctx).K₀ = 16) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_31_16.1) elcCert_31_16.2 i hi

/-- `(63,1)`: period `1`, cycle `[1]`, all bands deep (`≥ 5`). -/
private theorem elcCert_63_1 :
    slopeOrbit 63 1 (1 + 1) = slopeOrbit 63 1 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 63 1 j ≤ 63 := by
  have e0 : slopeOrbit 63 1 0 = 1 := rfl
  have e1 : slopeOrbit 63 1 1 = 1 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 63 1 2 = 1 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 63 1 2 = slopeOrbit 63 1 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(63,1)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_63_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63)
    (hK : (class1SlopeDatum ctx).K₀ = 1) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_63_1.1) elcCert_63_1.2 i hi

/-- `(63,2)`: period `1`, cycle `[1]`, all bands deep (`≥ 5`). -/
private theorem elcCert_63_2 :
    slopeOrbit 63 2 (1 + 1) = slopeOrbit 63 2 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 63 2 j ≤ 63 := by
  have e0 : slopeOrbit 63 2 0 = 2 := rfl
  have e1 : slopeOrbit 63 2 1 = 1 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 63 2 2 = 1 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 63 2 2 = slopeOrbit 63 2 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(63,2)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_63_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63)
    (hK : (class1SlopeDatum ctx).K₀ = 2) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_63_2.1) elcCert_63_2.2 i hi

/-- `(63,4)`: period `1`, cycle `[1]`, all bands deep (`≥ 5`). -/
private theorem elcCert_63_4 :
    slopeOrbit 63 4 (1 + 1) = slopeOrbit 63 4 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 63 4 j ≤ 63 := by
  have e0 : slopeOrbit 63 4 0 = 4 := rfl
  have e1 : slopeOrbit 63 4 1 = 1 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 63 4 2 = 1 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 63 4 2 = slopeOrbit 63 4 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(63,4)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_63_4 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63)
    (hK : (class1SlopeDatum ctx).K₀ = 4) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_63_4.1) elcCert_63_4.2 i hi

/-- `(63,8)`: period `1`, cycle `[1]`, all bands deep (`≥ 5`). -/
private theorem elcCert_63_8 :
    slopeOrbit 63 8 (1 + 1) = slopeOrbit 63 8 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 63 8 j ≤ 63 := by
  have e0 : slopeOrbit 63 8 0 = 8 := rfl
  have e1 : slopeOrbit 63 8 1 = 1 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 63 8 2 = 1 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 63 8 2 = slopeOrbit 63 8 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(63,8)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_63_8 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63)
    (hK : (class1SlopeDatum ctx).K₀ = 8) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_63_8.1) elcCert_63_8.2 i hi

/-- `(63,16)`: period `1`, cycle `[1]`, all bands deep (`≥ 5`). -/
private theorem elcCert_63_16 :
    slopeOrbit 63 16 (1 + 1) = slopeOrbit 63 16 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 63 16 j ≤ 63 := by
  have e0 : slopeOrbit 63 16 0 = 16 := rfl
  have e1 : slopeOrbit 63 16 1 = 1 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 63 16 2 = 1 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 63 16 2 = slopeOrbit 63 16 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(63,16)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_63_16 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63)
    (hK : (class1SlopeDatum ctx).K₀ = 16) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_63_16.1) elcCert_63_16.2 i hi

/-- `(63,32)`: period `1`, cycle `[1]`, all bands deep (`≥ 5`). -/
private theorem elcCert_63_32 :
    slopeOrbit 63 32 (1 + 1) = slopeOrbit 63 32 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 63 32 j ≤ 63 := by
  have e0 : slopeOrbit 63 32 0 = 32 := rfl
  have e1 : slopeOrbit 63 32 1 = 1 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 63 32 2 = 1 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 63 32 2 = slopeOrbit 63 32 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(63,32)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_63_32 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63)
    (hK : (class1SlopeDatum ctx).K₀ = 32) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_63_32.1) elcCert_63_32.2 i hi

/-- `(93,3)`: period `1`, cycle `[3]`, all bands deep (`≥ 5`). -/
private theorem elcCert_93_3 :
    slopeOrbit 93 3 (1 + 1) = slopeOrbit 93 3 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 93 3 j ≤ 93 := by
  have e0 : slopeOrbit 93 3 0 = 3 := rfl
  have e1 : slopeOrbit 93 3 1 = 3 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 93 3 2 = 3 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 93 3 2 = slopeOrbit 93 3 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(93,3)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_93_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 93)
    (hK : (class1SlopeDatum ctx).K₀ = 3) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_93_3.1) elcCert_93_3.2 i hi

/-- `(93,6)`: period `1`, cycle `[3]`, all bands deep (`≥ 5`). -/
private theorem elcCert_93_6 :
    slopeOrbit 93 6 (1 + 1) = slopeOrbit 93 6 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 93 6 j ≤ 93 := by
  have e0 : slopeOrbit 93 6 0 = 6 := rfl
  have e1 : slopeOrbit 93 6 1 = 3 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 93 6 2 = 3 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 93 6 2 = slopeOrbit 93 6 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(93,6)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_93_6 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 93)
    (hK : (class1SlopeDatum ctx).K₀ = 6) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_93_6.1) elcCert_93_6.2 i hi

/-- `(93,12)`: period `1`, cycle `[3]`, all bands deep (`≥ 5`). -/
private theorem elcCert_93_12 :
    slopeOrbit 93 12 (1 + 1) = slopeOrbit 93 12 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 93 12 j ≤ 93 := by
  have e0 : slopeOrbit 93 12 0 = 12 := rfl
  have e1 : slopeOrbit 93 12 1 = 3 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 93 12 2 = 3 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 93 12 2 = slopeOrbit 93 12 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(93,12)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_93_12 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 93)
    (hK : (class1SlopeDatum ctx).K₀ = 12) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_93_12.1) elcCert_93_12.2 i hi

/-- `(93,24)`: period `1`, cycle `[3]`, all bands deep (`≥ 5`). -/
private theorem elcCert_93_24 :
    slopeOrbit 93 24 (1 + 1) = slopeOrbit 93 24 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 93 24 j ≤ 93 := by
  have e0 : slopeOrbit 93 24 0 = 24 := rfl
  have e1 : slopeOrbit 93 24 1 = 3 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 93 24 2 = 3 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 93 24 2 = slopeOrbit 93 24 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(93,24)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_93_24 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 93)
    (hK : (class1SlopeDatum ctx).K₀ = 24) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_93_24.1) elcCert_93_24.2 i hi

/-- `(93,48)`: period `1`, cycle `[3]`, all bands deep (`≥ 5`). -/
private theorem elcCert_93_48 :
    slopeOrbit 93 48 (1 + 1) = slopeOrbit 93 48 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 93 48 j ≤ 93 := by
  have e0 : slopeOrbit 93 48 0 = 48 := rfl
  have e1 : slopeOrbit 93 48 1 = 3 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 93 48 2 = 3 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 93 48 2 = slopeOrbit 93 48 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(93,48)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_93_48 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 93)
    (hK : (class1SlopeDatum ctx).K₀ = 48) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_93_48.1) elcCert_93_48.2 i hi

/-- `(127,1)`: period `1`, cycle `[1]`, all bands deep (`≥ 5`). -/
private theorem elcCert_127_1 :
    slopeOrbit 127 1 (1 + 1) = slopeOrbit 127 1 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 127 1 j ≤ 127 := by
  have e0 : slopeOrbit 127 1 0 = 1 := rfl
  have e1 : slopeOrbit 127 1 1 = 1 :=
    slopeOrbit_step_eval 0 6 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 127 1 2 = 1 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 127 1 2 = slopeOrbit 127 1 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(127,1)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_127_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 127)
    (hK : (class1SlopeDatum ctx).K₀ = 1) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_127_1.1) elcCert_127_1.2 i hi

/-- `(127,2)`: period `1`, cycle `[1]`, all bands deep (`≥ 5`). -/
private theorem elcCert_127_2 :
    slopeOrbit 127 2 (1 + 1) = slopeOrbit 127 2 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 127 2 j ≤ 127 := by
  have e0 : slopeOrbit 127 2 0 = 2 := rfl
  have e1 : slopeOrbit 127 2 1 = 1 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 127 2 2 = 1 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 127 2 2 = slopeOrbit 127 2 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(127,2)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_127_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 127)
    (hK : (class1SlopeDatum ctx).K₀ = 2) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_127_2.1) elcCert_127_2.2 i hi

/-- `(127,4)`: period `1`, cycle `[1]`, all bands deep (`≥ 5`). -/
private theorem elcCert_127_4 :
    slopeOrbit 127 4 (1 + 1) = slopeOrbit 127 4 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 127 4 j ≤ 127 := by
  have e0 : slopeOrbit 127 4 0 = 4 := rfl
  have e1 : slopeOrbit 127 4 1 = 1 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 127 4 2 = 1 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 127 4 2 = slopeOrbit 127 4 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(127,4)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_127_4 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 127)
    (hK : (class1SlopeDatum ctx).K₀ = 4) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_127_4.1) elcCert_127_4.2 i hi

/-- `(127,8)`: period `1`, cycle `[1]`, all bands deep (`≥ 5`). -/
private theorem elcCert_127_8 :
    slopeOrbit 127 8 (1 + 1) = slopeOrbit 127 8 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 127 8 j ≤ 127 := by
  have e0 : slopeOrbit 127 8 0 = 8 := rfl
  have e1 : slopeOrbit 127 8 1 = 1 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 127 8 2 = 1 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 127 8 2 = slopeOrbit 127 8 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(127,8)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_127_8 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 127)
    (hK : (class1SlopeDatum ctx).K₀ = 8) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_127_8.1) elcCert_127_8.2 i hi

/-- `(127,16)`: period `1`, cycle `[1]`, all bands deep (`≥ 5`). -/
private theorem elcCert_127_16 :
    slopeOrbit 127 16 (1 + 1) = slopeOrbit 127 16 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 127 16 j ≤ 127 := by
  have e0 : slopeOrbit 127 16 0 = 16 := rfl
  have e1 : slopeOrbit 127 16 1 = 1 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 127 16 2 = 1 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 127 16 2 = slopeOrbit 127 16 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(127,16)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_127_16 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 127)
    (hK : (class1SlopeDatum ctx).K₀ = 16) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_127_16.1) elcCert_127_16.2 i hi

/-- `(127,32)`: period `1`, cycle `[1]`, all bands deep (`≥ 5`). -/
private theorem elcCert_127_32 :
    slopeOrbit 127 32 (1 + 1) = slopeOrbit 127 32 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 127 32 j ≤ 127 := by
  have e0 : slopeOrbit 127 32 0 = 32 := rfl
  have e1 : slopeOrbit 127 32 1 = 1 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 127 32 2 = 1 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 127 32 2 = slopeOrbit 127 32 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(127,32)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_127_32 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 127)
    (hK : (class1SlopeDatum ctx).K₀ = 32) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_127_32.1) elcCert_127_32.2 i hi

/-- `(127,64)`: period `1`, cycle `[1]`, all bands deep (`≥ 5`). -/
private theorem elcCert_127_64 :
    slopeOrbit 127 64 (1 + 1) = slopeOrbit 127 64 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 127 64 j ≤ 127 := by
  have e0 : slopeOrbit 127 64 0 = 64 := rfl
  have e1 : slopeOrbit 127 64 1 = 1 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 127 64 2 = 1 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 127 64 2 = slopeOrbit 127 64 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(127,64)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_127_64 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 127)
    (hK : (class1SlopeDatum ctx).K₀ = 64) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_127_64.1) elcCert_127_64.2 i hi

/-- `(155,5)`: period `1`, cycle `[5]`, all bands deep (`≥ 5`). -/
private theorem elcCert_155_5 :
    slopeOrbit 155 5 (1 + 1) = slopeOrbit 155 5 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 155 5 j ≤ 155 := by
  have e0 : slopeOrbit 155 5 0 = 5 := rfl
  have e1 : slopeOrbit 155 5 1 = 5 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 155 5 2 = 5 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 155 5 2 = slopeOrbit 155 5 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(155,5)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_155_5 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 155)
    (hK : (class1SlopeDatum ctx).K₀ = 5) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_155_5.1) elcCert_155_5.2 i hi

/-- `(155,10)`: period `1`, cycle `[5]`, all bands deep (`≥ 5`). -/
private theorem elcCert_155_10 :
    slopeOrbit 155 10 (1 + 1) = slopeOrbit 155 10 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 155 10 j ≤ 155 := by
  have e0 : slopeOrbit 155 10 0 = 10 := rfl
  have e1 : slopeOrbit 155 10 1 = 5 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 155 10 2 = 5 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 155 10 2 = slopeOrbit 155 10 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(155,10)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_155_10 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 155)
    (hK : (class1SlopeDatum ctx).K₀ = 10) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_155_10.1) elcCert_155_10.2 i hi

/-- `(155,20)`: period `1`, cycle `[5]`, all bands deep (`≥ 5`). -/
private theorem elcCert_155_20 :
    slopeOrbit 155 20 (1 + 1) = slopeOrbit 155 20 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 155 20 j ≤ 155 := by
  have e0 : slopeOrbit 155 20 0 = 20 := rfl
  have e1 : slopeOrbit 155 20 1 = 5 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 155 20 2 = 5 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 155 20 2 = slopeOrbit 155 20 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(155,20)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_155_20 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 155)
    (hK : (class1SlopeDatum ctx).K₀ = 20) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_155_20.1) elcCert_155_20.2 i hi

/-- `(155,40)`: period `1`, cycle `[5]`, all bands deep (`≥ 5`). -/
private theorem elcCert_155_40 :
    slopeOrbit 155 40 (1 + 1) = slopeOrbit 155 40 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 155 40 j ≤ 155 := by
  have e0 : slopeOrbit 155 40 0 = 40 := rfl
  have e1 : slopeOrbit 155 40 1 = 5 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 155 40 2 = 5 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 155 40 2 = slopeOrbit 155 40 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(155,40)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_155_40 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 155)
    (hK : (class1SlopeDatum ctx).K₀ = 40) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_155_40.1) elcCert_155_40.2 i hi

/-- `(155,80)`: period `1`, cycle `[5]`, all bands deep (`≥ 5`). -/
private theorem elcCert_155_80 :
    slopeOrbit 155 80 (1 + 1) = slopeOrbit 155 80 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 155 80 j ≤ 155 := by
  have e0 : slopeOrbit 155 80 0 = 80 := rfl
  have e1 : slopeOrbit 155 80 1 = 5 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 155 80 2 = 5 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 155 80 2 = slopeOrbit 155 80 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(155,80)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_155_80 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 155)
    (hK : (class1SlopeDatum ctx).K₀ = 80) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_155_80.1) elcCert_155_80.2 i hi

/-- `(189,3)`: period `1`, cycle `[3]`, all bands deep (`≥ 5`). -/
private theorem elcCert_189_3 :
    slopeOrbit 189 3 (1 + 1) = slopeOrbit 189 3 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 189 3 j ≤ 189 := by
  have e0 : slopeOrbit 189 3 0 = 3 := rfl
  have e1 : slopeOrbit 189 3 1 = 3 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 189 3 2 = 3 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 189 3 2 = slopeOrbit 189 3 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(189,3)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_189_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 189)
    (hK : (class1SlopeDatum ctx).K₀ = 3) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_189_3.1) elcCert_189_3.2 i hi

/-- `(189,6)`: period `1`, cycle `[3]`, all bands deep (`≥ 5`). -/
private theorem elcCert_189_6 :
    slopeOrbit 189 6 (1 + 1) = slopeOrbit 189 6 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 189 6 j ≤ 189 := by
  have e0 : slopeOrbit 189 6 0 = 6 := rfl
  have e1 : slopeOrbit 189 6 1 = 3 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 189 6 2 = 3 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 189 6 2 = slopeOrbit 189 6 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(189,6)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_189_6 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 189)
    (hK : (class1SlopeDatum ctx).K₀ = 6) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_189_6.1) elcCert_189_6.2 i hi

/-- `(189,12)`: period `1`, cycle `[3]`, all bands deep (`≥ 5`). -/
private theorem elcCert_189_12 :
    slopeOrbit 189 12 (1 + 1) = slopeOrbit 189 12 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 189 12 j ≤ 189 := by
  have e0 : slopeOrbit 189 12 0 = 12 := rfl
  have e1 : slopeOrbit 189 12 1 = 3 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 189 12 2 = 3 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 189 12 2 = slopeOrbit 189 12 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(189,12)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_189_12 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 189)
    (hK : (class1SlopeDatum ctx).K₀ = 12) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_189_12.1) elcCert_189_12.2 i hi

/-- `(189,24)`: period `1`, cycle `[3]`, all bands deep (`≥ 5`). -/
private theorem elcCert_189_24 :
    slopeOrbit 189 24 (1 + 1) = slopeOrbit 189 24 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 189 24 j ≤ 189 := by
  have e0 : slopeOrbit 189 24 0 = 24 := rfl
  have e1 : slopeOrbit 189 24 1 = 3 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 189 24 2 = 3 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 189 24 2 = slopeOrbit 189 24 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(189,24)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_189_24 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 189)
    (hK : (class1SlopeDatum ctx).K₀ = 24) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_189_24.1) elcCert_189_24.2 i hi

/-- `(189,48)`: period `1`, cycle `[3]`, all bands deep (`≥ 5`). -/
private theorem elcCert_189_48 :
    slopeOrbit 189 48 (1 + 1) = slopeOrbit 189 48 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 189 48 j ≤ 189 := by
  have e0 : slopeOrbit 189 48 0 = 48 := rfl
  have e1 : slopeOrbit 189 48 1 = 3 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 189 48 2 = 3 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 189 48 2 = slopeOrbit 189 48 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(189,48)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_189_48 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 189)
    (hK : (class1SlopeDatum ctx).K₀ = 48) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_189_48.1) elcCert_189_48.2 i hi

/-- `(189,96)`: period `1`, cycle `[3]`, all bands deep (`≥ 5`). -/
private theorem elcCert_189_96 :
    slopeOrbit 189 96 (1 + 1) = slopeOrbit 189 96 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 189 96 j ≤ 189 := by
  have e0 : slopeOrbit 189 96 0 = 96 := rfl
  have e1 : slopeOrbit 189 96 1 = 3 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 189 96 2 = 3 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 189 96 2 = slopeOrbit 189 96 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(189,96)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_189_96 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 189)
    (hK : (class1SlopeDatum ctx).K₀ = 96) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_189_96.1) elcCert_189_96.2 i hi

/-- `(217,7)`: period `1`, cycle `[7]`, all bands deep (`≥ 5`). -/
private theorem elcCert_217_7 :
    slopeOrbit 217 7 (1 + 1) = slopeOrbit 217 7 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 217 7 j ≤ 217 := by
  have e0 : slopeOrbit 217 7 0 = 7 := rfl
  have e1 : slopeOrbit 217 7 1 = 7 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 217 7 2 = 7 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 217 7 2 = slopeOrbit 217 7 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(217,7)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_217_7 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 217)
    (hK : (class1SlopeDatum ctx).K₀ = 7) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_217_7.1) elcCert_217_7.2 i hi

/-- `(217,14)`: period `1`, cycle `[7]`, all bands deep (`≥ 5`). -/
private theorem elcCert_217_14 :
    slopeOrbit 217 14 (1 + 1) = slopeOrbit 217 14 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 217 14 j ≤ 217 := by
  have e0 : slopeOrbit 217 14 0 = 14 := rfl
  have e1 : slopeOrbit 217 14 1 = 7 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 217 14 2 = 7 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 217 14 2 = slopeOrbit 217 14 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(217,14)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_217_14 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 217)
    (hK : (class1SlopeDatum ctx).K₀ = 14) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_217_14.1) elcCert_217_14.2 i hi

/-- `(217,28)`: period `1`, cycle `[7]`, all bands deep (`≥ 5`). -/
private theorem elcCert_217_28 :
    slopeOrbit 217 28 (1 + 1) = slopeOrbit 217 28 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 217 28 j ≤ 217 := by
  have e0 : slopeOrbit 217 28 0 = 28 := rfl
  have e1 : slopeOrbit 217 28 1 = 7 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 217 28 2 = 7 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 217 28 2 = slopeOrbit 217 28 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(217,28)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_217_28 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 217)
    (hK : (class1SlopeDatum ctx).K₀ = 28) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_217_28.1) elcCert_217_28.2 i hi

/-- `(217,56)`: period `1`, cycle `[7]`, all bands deep (`≥ 5`). -/
private theorem elcCert_217_56 :
    slopeOrbit 217 56 (1 + 1) = slopeOrbit 217 56 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 217 56 j ≤ 217 := by
  have e0 : slopeOrbit 217 56 0 = 56 := rfl
  have e1 : slopeOrbit 217 56 1 = 7 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 217 56 2 = 7 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 217 56 2 = slopeOrbit 217 56 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(217,56)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_217_56 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 217)
    (hK : (class1SlopeDatum ctx).K₀ = 56) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_217_56.1) elcCert_217_56.2 i hi

/-- `(217,112)`: period `1`, cycle `[7]`, all bands deep (`≥ 5`). -/
private theorem elcCert_217_112 :
    slopeOrbit 217 112 (1 + 1) = slopeOrbit 217 112 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 217 112 j ≤ 217 := by
  have e0 : slopeOrbit 217 112 0 = 112 := rfl
  have e1 : slopeOrbit 217 112 1 = 7 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 217 112 2 = 7 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 217 112 2 = slopeOrbit 217 112 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(217,112)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_217_112 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 217)
    (hK : (class1SlopeDatum ctx).K₀ = 112) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_217_112.1) elcCert_217_112.2 i hi

/-- `(255,1)`: period `1`, cycle `[1]`, all bands deep (`≥ 5`). -/
private theorem elcCert_255_1 :
    slopeOrbit 255 1 (1 + 1) = slopeOrbit 255 1 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 255 1 j ≤ 255 := by
  have e0 : slopeOrbit 255 1 0 = 1 := rfl
  have e1 : slopeOrbit 255 1 1 = 1 :=
    slopeOrbit_step_eval 0 7 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 255 1 2 = 1 :=
    slopeOrbit_step_eval 1 7 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 255 1 2 = slopeOrbit 255 1 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(255,1)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_255_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 255)
    (hK : (class1SlopeDatum ctx).K₀ = 1) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_255_1.1) elcCert_255_1.2 i hi

/-- `(255,2)`: period `1`, cycle `[1]`, all bands deep (`≥ 5`). -/
private theorem elcCert_255_2 :
    slopeOrbit 255 2 (1 + 1) = slopeOrbit 255 2 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 255 2 j ≤ 255 := by
  have e0 : slopeOrbit 255 2 0 = 2 := rfl
  have e1 : slopeOrbit 255 2 1 = 1 :=
    slopeOrbit_step_eval 0 6 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 255 2 2 = 1 :=
    slopeOrbit_step_eval 1 7 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 255 2 2 = slopeOrbit 255 2 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(255,2)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_255_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 255)
    (hK : (class1SlopeDatum ctx).K₀ = 2) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_255_2.1) elcCert_255_2.2 i hi

/-- `(255,4)`: period `1`, cycle `[1]`, all bands deep (`≥ 5`). -/
private theorem elcCert_255_4 :
    slopeOrbit 255 4 (1 + 1) = slopeOrbit 255 4 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 255 4 j ≤ 255 := by
  have e0 : slopeOrbit 255 4 0 = 4 := rfl
  have e1 : slopeOrbit 255 4 1 = 1 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 255 4 2 = 1 :=
    slopeOrbit_step_eval 1 7 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 255 4 2 = slopeOrbit 255 4 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(255,4)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_255_4 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 255)
    (hK : (class1SlopeDatum ctx).K₀ = 4) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_255_4.1) elcCert_255_4.2 i hi

/-- `(255,8)`: period `1`, cycle `[1]`, all bands deep (`≥ 5`). -/
private theorem elcCert_255_8 :
    slopeOrbit 255 8 (1 + 1) = slopeOrbit 255 8 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 255 8 j ≤ 255 := by
  have e0 : slopeOrbit 255 8 0 = 8 := rfl
  have e1 : slopeOrbit 255 8 1 = 1 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 255 8 2 = 1 :=
    slopeOrbit_step_eval 1 7 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 255 8 2 = slopeOrbit 255 8 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(255,8)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_255_8 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 255)
    (hK : (class1SlopeDatum ctx).K₀ = 8) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_255_8.1) elcCert_255_8.2 i hi

/-- `(255,16)`: period `1`, cycle `[1]`, all bands deep (`≥ 5`). -/
private theorem elcCert_255_16 :
    slopeOrbit 255 16 (1 + 1) = slopeOrbit 255 16 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 255 16 j ≤ 255 := by
  have e0 : slopeOrbit 255 16 0 = 16 := rfl
  have e1 : slopeOrbit 255 16 1 = 1 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 255 16 2 = 1 :=
    slopeOrbit_step_eval 1 7 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 255 16 2 = slopeOrbit 255 16 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(255,16)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_255_16 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 255)
    (hK : (class1SlopeDatum ctx).K₀ = 16) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_255_16.1) elcCert_255_16.2 i hi

/-- `(255,32)`: period `1`, cycle `[1]`, all bands deep (`≥ 5`). -/
private theorem elcCert_255_32 :
    slopeOrbit 255 32 (1 + 1) = slopeOrbit 255 32 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 255 32 j ≤ 255 := by
  have e0 : slopeOrbit 255 32 0 = 32 := rfl
  have e1 : slopeOrbit 255 32 1 = 1 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 255 32 2 = 1 :=
    slopeOrbit_step_eval 1 7 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 255 32 2 = slopeOrbit 255 32 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(255,32)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_255_32 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 255)
    (hK : (class1SlopeDatum ctx).K₀ = 32) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_255_32.1) elcCert_255_32.2 i hi

/-- `(255,64)`: period `1`, cycle `[1]`, all bands deep (`≥ 5`). -/
private theorem elcCert_255_64 :
    slopeOrbit 255 64 (1 + 1) = slopeOrbit 255 64 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 255 64 j ≤ 255 := by
  have e0 : slopeOrbit 255 64 0 = 64 := rfl
  have e1 : slopeOrbit 255 64 1 = 1 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 255 64 2 = 1 :=
    slopeOrbit_step_eval 1 7 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 255 64 2 = slopeOrbit 255 64 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(255,64)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_255_64 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 255)
    (hK : (class1SlopeDatum ctx).K₀ = 64) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_255_64.1) elcCert_255_64.2 i hi

/-- `(255,128)`: period `1`, cycle `[1]`, all bands deep (`≥ 5`). -/
private theorem elcCert_255_128 :
    slopeOrbit 255 128 (1 + 1) = slopeOrbit 255 128 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 255 128 j ≤ 255 := by
  have e0 : slopeOrbit 255 128 0 = 128 := rfl
  have e1 : slopeOrbit 255 128 1 = 1 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 255 128 2 = 1 :=
    slopeOrbit_step_eval 1 7 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 255 128 2 = slopeOrbit 255 128 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(255,128)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_255_128 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 255)
    (hK : (class1SlopeDatum ctx).K₀ = 128) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_255_128.1) elcCert_255_128.2 i hi

/-- `(279,9)`: period `1`, cycle `[9]`, all bands deep (`≥ 5`). -/
private theorem elcCert_279_9 :
    slopeOrbit 279 9 (1 + 1) = slopeOrbit 279 9 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 279 9 j ≤ 279 := by
  have e0 : slopeOrbit 279 9 0 = 9 := rfl
  have e1 : slopeOrbit 279 9 1 = 9 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 279 9 2 = 9 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 279 9 2 = slopeOrbit 279 9 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(279,9)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_279_9 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 279)
    (hK : (class1SlopeDatum ctx).K₀ = 9) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_279_9.1) elcCert_279_9.2 i hi

/-- `(279,18)`: period `1`, cycle `[9]`, all bands deep (`≥ 5`). -/
private theorem elcCert_279_18 :
    slopeOrbit 279 18 (1 + 1) = slopeOrbit 279 18 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 279 18 j ≤ 279 := by
  have e0 : slopeOrbit 279 18 0 = 18 := rfl
  have e1 : slopeOrbit 279 18 1 = 9 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 279 18 2 = 9 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 279 18 2 = slopeOrbit 279 18 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(279,18)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_279_18 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 279)
    (hK : (class1SlopeDatum ctx).K₀ = 18) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_279_18.1) elcCert_279_18.2 i hi

/-- `(279,36)`: period `1`, cycle `[9]`, all bands deep (`≥ 5`). -/
private theorem elcCert_279_36 :
    slopeOrbit 279 36 (1 + 1) = slopeOrbit 279 36 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 279 36 j ≤ 279 := by
  have e0 : slopeOrbit 279 36 0 = 36 := rfl
  have e1 : slopeOrbit 279 36 1 = 9 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 279 36 2 = 9 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 279 36 2 = slopeOrbit 279 36 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(279,36)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_279_36 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 279)
    (hK : (class1SlopeDatum ctx).K₀ = 36) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_279_36.1) elcCert_279_36.2 i hi

/-- `(279,72)`: period `1`, cycle `[9]`, all bands deep (`≥ 5`). -/
private theorem elcCert_279_72 :
    slopeOrbit 279 72 (1 + 1) = slopeOrbit 279 72 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 279 72 j ≤ 279 := by
  have e0 : slopeOrbit 279 72 0 = 72 := rfl
  have e1 : slopeOrbit 279 72 1 = 9 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 279 72 2 = 9 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 279 72 2 = slopeOrbit 279 72 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(279,72)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_279_72 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 279)
    (hK : (class1SlopeDatum ctx).K₀ = 72) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_279_72.1) elcCert_279_72.2 i hi

/-- `(279,144)`: period `1`, cycle `[9]`, all bands deep (`≥ 5`). -/
private theorem elcCert_279_144 :
    slopeOrbit 279 144 (1 + 1) = slopeOrbit 279 144 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 279 144 j ≤ 279 := by
  have e0 : slopeOrbit 279 144 0 = 144 := rfl
  have e1 : slopeOrbit 279 144 1 = 9 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 279 144 2 = 9 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 279 144 2 = slopeOrbit 279 144 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(279,144)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_279_144 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 279)
    (hK : (class1SlopeDatum ctx).K₀ = 144) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_279_144.1) elcCert_279_144.2 i hi

/-- `(315,5)`: period `1`, cycle `[5]`, all bands deep (`≥ 5`). -/
private theorem elcCert_315_5 :
    slopeOrbit 315 5 (1 + 1) = slopeOrbit 315 5 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 315 5 j ≤ 315 := by
  have e0 : slopeOrbit 315 5 0 = 5 := rfl
  have e1 : slopeOrbit 315 5 1 = 5 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 315 5 2 = 5 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 315 5 2 = slopeOrbit 315 5 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(315,5)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_315_5 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 315)
    (hK : (class1SlopeDatum ctx).K₀ = 5) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_315_5.1) elcCert_315_5.2 i hi

/-- `(315,10)`: period `1`, cycle `[5]`, all bands deep (`≥ 5`). -/
private theorem elcCert_315_10 :
    slopeOrbit 315 10 (1 + 1) = slopeOrbit 315 10 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 315 10 j ≤ 315 := by
  have e0 : slopeOrbit 315 10 0 = 10 := rfl
  have e1 : slopeOrbit 315 10 1 = 5 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 315 10 2 = 5 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 315 10 2 = slopeOrbit 315 10 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(315,10)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_315_10 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 315)
    (hK : (class1SlopeDatum ctx).K₀ = 10) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_315_10.1) elcCert_315_10.2 i hi

/-- `(315,20)`: period `1`, cycle `[5]`, all bands deep (`≥ 5`). -/
private theorem elcCert_315_20 :
    slopeOrbit 315 20 (1 + 1) = slopeOrbit 315 20 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 315 20 j ≤ 315 := by
  have e0 : slopeOrbit 315 20 0 = 20 := rfl
  have e1 : slopeOrbit 315 20 1 = 5 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 315 20 2 = 5 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 315 20 2 = slopeOrbit 315 20 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(315,20)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_315_20 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 315)
    (hK : (class1SlopeDatum ctx).K₀ = 20) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_315_20.1) elcCert_315_20.2 i hi

/-- `(315,40)`: period `1`, cycle `[5]`, all bands deep (`≥ 5`). -/
private theorem elcCert_315_40 :
    slopeOrbit 315 40 (1 + 1) = slopeOrbit 315 40 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 315 40 j ≤ 315 := by
  have e0 : slopeOrbit 315 40 0 = 40 := rfl
  have e1 : slopeOrbit 315 40 1 = 5 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 315 40 2 = 5 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 315 40 2 = slopeOrbit 315 40 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(315,40)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_315_40 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 315)
    (hK : (class1SlopeDatum ctx).K₀ = 40) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_315_40.1) elcCert_315_40.2 i hi

/-- `(315,80)`: period `1`, cycle `[5]`, all bands deep (`≥ 5`). -/
private theorem elcCert_315_80 :
    slopeOrbit 315 80 (1 + 1) = slopeOrbit 315 80 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 315 80 j ≤ 315 := by
  have e0 : slopeOrbit 315 80 0 = 80 := rfl
  have e1 : slopeOrbit 315 80 1 = 5 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 315 80 2 = 5 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 315 80 2 = slopeOrbit 315 80 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(315,80)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_315_80 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 315)
    (hK : (class1SlopeDatum ctx).K₀ = 80) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_315_80.1) elcCert_315_80.2 i hi

/-- `(315,160)`: period `1`, cycle `[5]`, all bands deep (`≥ 5`). -/
private theorem elcCert_315_160 :
    slopeOrbit 315 160 (1 + 1) = slopeOrbit 315 160 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 315 160 j ≤ 315 := by
  have e0 : slopeOrbit 315 160 0 = 160 := rfl
  have e1 : slopeOrbit 315 160 1 = 5 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 315 160 2 = 5 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 315 160 2 = slopeOrbit 315 160 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(315,160)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_315_160 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 315)
    (hK : (class1SlopeDatum ctx).K₀ = 160) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_315_160.1) elcCert_315_160.2 i hi

/-- `(341,11)`: period `1`, cycle `[11]`, all bands deep (`≥ 5`). -/
private theorem elcCert_341_11 :
    slopeOrbit 341 11 (1 + 1) = slopeOrbit 341 11 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 341 11 j ≤ 341 := by
  have e0 : slopeOrbit 341 11 0 = 11 := rfl
  have e1 : slopeOrbit 341 11 1 = 11 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 341 11 2 = 11 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 341 11 2 = slopeOrbit 341 11 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(341,11)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_341_11 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 341)
    (hK : (class1SlopeDatum ctx).K₀ = 11) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_341_11.1) elcCert_341_11.2 i hi

/-- `(341,22)`: period `1`, cycle `[11]`, all bands deep (`≥ 5`). -/
private theorem elcCert_341_22 :
    slopeOrbit 341 22 (1 + 1) = slopeOrbit 341 22 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 341 22 j ≤ 341 := by
  have e0 : slopeOrbit 341 22 0 = 22 := rfl
  have e1 : slopeOrbit 341 22 1 = 11 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 341 22 2 = 11 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 341 22 2 = slopeOrbit 341 22 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(341,22)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_341_22 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 341)
    (hK : (class1SlopeDatum ctx).K₀ = 22) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_341_22.1) elcCert_341_22.2 i hi

/-- `(341,44)`: period `1`, cycle `[11]`, all bands deep (`≥ 5`). -/
private theorem elcCert_341_44 :
    slopeOrbit 341 44 (1 + 1) = slopeOrbit 341 44 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 341 44 j ≤ 341 := by
  have e0 : slopeOrbit 341 44 0 = 44 := rfl
  have e1 : slopeOrbit 341 44 1 = 11 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 341 44 2 = 11 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 341 44 2 = slopeOrbit 341 44 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(341,44)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_341_44 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 341)
    (hK : (class1SlopeDatum ctx).K₀ = 44) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_341_44.1) elcCert_341_44.2 i hi

/-- `(341,88)`: period `1`, cycle `[11]`, all bands deep (`≥ 5`). -/
private theorem elcCert_341_88 :
    slopeOrbit 341 88 (1 + 1) = slopeOrbit 341 88 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 341 88 j ≤ 341 := by
  have e0 : slopeOrbit 341 88 0 = 88 := rfl
  have e1 : slopeOrbit 341 88 1 = 11 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 341 88 2 = 11 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 341 88 2 = slopeOrbit 341 88 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(341,88)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_341_88 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 341)
    (hK : (class1SlopeDatum ctx).K₀ = 88) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_341_88.1) elcCert_341_88.2 i hi

/-- `(341,176)`: period `1`, cycle `[11]`, all bands deep (`≥ 5`). -/
private theorem elcCert_341_176 :
    slopeOrbit 341 176 (1 + 1) = slopeOrbit 341 176 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 341 176 j ≤ 341 := by
  have e0 : slopeOrbit 341 176 0 = 176 := rfl
  have e1 : slopeOrbit 341 176 1 = 11 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 341 176 2 = 11 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 341 176 2 = slopeOrbit 341 176 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(341,176)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_341_176 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 341)
    (hK : (class1SlopeDatum ctx).K₀ = 176) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_341_176.1) elcCert_341_176.2 i hi

/-- `(381,3)`: period `1`, cycle `[3]`, all bands deep (`≥ 5`). -/
private theorem elcCert_381_3 :
    slopeOrbit 381 3 (1 + 1) = slopeOrbit 381 3 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 381 3 j ≤ 381 := by
  have e0 : slopeOrbit 381 3 0 = 3 := rfl
  have e1 : slopeOrbit 381 3 1 = 3 :=
    slopeOrbit_step_eval 0 6 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 381 3 2 = 3 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 381 3 2 = slopeOrbit 381 3 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(381,3)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_381_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 381)
    (hK : (class1SlopeDatum ctx).K₀ = 3) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_381_3.1) elcCert_381_3.2 i hi

/-- `(381,6)`: period `1`, cycle `[3]`, all bands deep (`≥ 5`). -/
private theorem elcCert_381_6 :
    slopeOrbit 381 6 (1 + 1) = slopeOrbit 381 6 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 381 6 j ≤ 381 := by
  have e0 : slopeOrbit 381 6 0 = 6 := rfl
  have e1 : slopeOrbit 381 6 1 = 3 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 381 6 2 = 3 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 381 6 2 = slopeOrbit 381 6 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(381,6)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_381_6 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 381)
    (hK : (class1SlopeDatum ctx).K₀ = 6) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_381_6.1) elcCert_381_6.2 i hi

/-- `(381,12)`: period `1`, cycle `[3]`, all bands deep (`≥ 5`). -/
private theorem elcCert_381_12 :
    slopeOrbit 381 12 (1 + 1) = slopeOrbit 381 12 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 381 12 j ≤ 381 := by
  have e0 : slopeOrbit 381 12 0 = 12 := rfl
  have e1 : slopeOrbit 381 12 1 = 3 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 381 12 2 = 3 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 381 12 2 = slopeOrbit 381 12 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(381,12)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_381_12 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 381)
    (hK : (class1SlopeDatum ctx).K₀ = 12) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_381_12.1) elcCert_381_12.2 i hi

/-- `(381,24)`: period `1`, cycle `[3]`, all bands deep (`≥ 5`). -/
private theorem elcCert_381_24 :
    slopeOrbit 381 24 (1 + 1) = slopeOrbit 381 24 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 381 24 j ≤ 381 := by
  have e0 : slopeOrbit 381 24 0 = 24 := rfl
  have e1 : slopeOrbit 381 24 1 = 3 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 381 24 2 = 3 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 381 24 2 = slopeOrbit 381 24 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(381,24)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_381_24 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 381)
    (hK : (class1SlopeDatum ctx).K₀ = 24) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_381_24.1) elcCert_381_24.2 i hi

/-- `(381,48)`: period `1`, cycle `[3]`, all bands deep (`≥ 5`). -/
private theorem elcCert_381_48 :
    slopeOrbit 381 48 (1 + 1) = slopeOrbit 381 48 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 381 48 j ≤ 381 := by
  have e0 : slopeOrbit 381 48 0 = 48 := rfl
  have e1 : slopeOrbit 381 48 1 = 3 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 381 48 2 = 3 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 381 48 2 = slopeOrbit 381 48 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(381,48)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_381_48 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 381)
    (hK : (class1SlopeDatum ctx).K₀ = 48) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_381_48.1) elcCert_381_48.2 i hi

/-- `(381,96)`: period `1`, cycle `[3]`, all bands deep (`≥ 5`). -/
private theorem elcCert_381_96 :
    slopeOrbit 381 96 (1 + 1) = slopeOrbit 381 96 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 381 96 j ≤ 381 := by
  have e0 : slopeOrbit 381 96 0 = 96 := rfl
  have e1 : slopeOrbit 381 96 1 = 3 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 381 96 2 = 3 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 381 96 2 = slopeOrbit 381 96 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(381,96)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_381_96 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 381)
    (hK : (class1SlopeDatum ctx).K₀ = 96) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_381_96.1) elcCert_381_96.2 i hi

/-- `(381,192)`: period `1`, cycle `[3]`, all bands deep (`≥ 5`). -/
private theorem elcCert_381_192 :
    slopeOrbit 381 192 (1 + 1) = slopeOrbit 381 192 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 381 192 j ≤ 381 := by
  have e0 : slopeOrbit 381 192 0 = 192 := rfl
  have e1 : slopeOrbit 381 192 1 = 3 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 381 192 2 = 3 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 381 192 2 = slopeOrbit 381 192 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(381,192)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_381_192 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 381)
    (hK : (class1SlopeDatum ctx).K₀ = 192) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_381_192.1) elcCert_381_192.2 i hi

/-- `(403,13)`: period `1`, cycle `[13]`, all bands deep (`≥ 5`). -/
private theorem elcCert_403_13 :
    slopeOrbit 403 13 (1 + 1) = slopeOrbit 403 13 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 403 13 j ≤ 403 := by
  have e0 : slopeOrbit 403 13 0 = 13 := rfl
  have e1 : slopeOrbit 403 13 1 = 13 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 403 13 2 = 13 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 403 13 2 = slopeOrbit 403 13 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(403,13)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_403_13 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 403)
    (hK : (class1SlopeDatum ctx).K₀ = 13) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_403_13.1) elcCert_403_13.2 i hi

/-- `(403,26)`: period `1`, cycle `[13]`, all bands deep (`≥ 5`). -/
private theorem elcCert_403_26 :
    slopeOrbit 403 26 (1 + 1) = slopeOrbit 403 26 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 403 26 j ≤ 403 := by
  have e0 : slopeOrbit 403 26 0 = 26 := rfl
  have e1 : slopeOrbit 403 26 1 = 13 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 403 26 2 = 13 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 403 26 2 = slopeOrbit 403 26 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(403,26)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_403_26 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 403)
    (hK : (class1SlopeDatum ctx).K₀ = 26) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_403_26.1) elcCert_403_26.2 i hi

/-- `(403,52)`: period `1`, cycle `[13]`, all bands deep (`≥ 5`). -/
private theorem elcCert_403_52 :
    slopeOrbit 403 52 (1 + 1) = slopeOrbit 403 52 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 403 52 j ≤ 403 := by
  have e0 : slopeOrbit 403 52 0 = 52 := rfl
  have e1 : slopeOrbit 403 52 1 = 13 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 403 52 2 = 13 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 403 52 2 = slopeOrbit 403 52 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(403,52)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_403_52 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 403)
    (hK : (class1SlopeDatum ctx).K₀ = 52) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_403_52.1) elcCert_403_52.2 i hi

/-- `(403,104)`: period `1`, cycle `[13]`, all bands deep (`≥ 5`). -/
private theorem elcCert_403_104 :
    slopeOrbit 403 104 (1 + 1) = slopeOrbit 403 104 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 403 104 j ≤ 403 := by
  have e0 : slopeOrbit 403 104 0 = 104 := rfl
  have e1 : slopeOrbit 403 104 1 = 13 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 403 104 2 = 13 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 403 104 2 = slopeOrbit 403 104 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(403,104)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_403_104 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 403)
    (hK : (class1SlopeDatum ctx).K₀ = 104) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_403_104.1) elcCert_403_104.2 i hi

/-- `(403,208)`: period `1`, cycle `[13]`, all bands deep (`≥ 5`). -/
private theorem elcCert_403_208 :
    slopeOrbit 403 208 (1 + 1) = slopeOrbit 403 208 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 403 208 j ≤ 403 := by
  have e0 : slopeOrbit 403 208 0 = 208 := rfl
  have e1 : slopeOrbit 403 208 1 = 13 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 403 208 2 = 13 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 403 208 2 = slopeOrbit 403 208 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(403,208)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_403_208 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 403)
    (hK : (class1SlopeDatum ctx).K₀ = 208) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_403_208.1) elcCert_403_208.2 i hi

/-- `(441,7)`: period `1`, cycle `[7]`, all bands deep (`≥ 5`). -/
private theorem elcCert_441_7 :
    slopeOrbit 441 7 (1 + 1) = slopeOrbit 441 7 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 441 7 j ≤ 441 := by
  have e0 : slopeOrbit 441 7 0 = 7 := rfl
  have e1 : slopeOrbit 441 7 1 = 7 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 441 7 2 = 7 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 441 7 2 = slopeOrbit 441 7 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(441,7)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_441_7 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 441)
    (hK : (class1SlopeDatum ctx).K₀ = 7) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_441_7.1) elcCert_441_7.2 i hi

/-- `(441,14)`: period `1`, cycle `[7]`, all bands deep (`≥ 5`). -/
private theorem elcCert_441_14 :
    slopeOrbit 441 14 (1 + 1) = slopeOrbit 441 14 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 441 14 j ≤ 441 := by
  have e0 : slopeOrbit 441 14 0 = 14 := rfl
  have e1 : slopeOrbit 441 14 1 = 7 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 441 14 2 = 7 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 441 14 2 = slopeOrbit 441 14 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(441,14)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_441_14 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 441)
    (hK : (class1SlopeDatum ctx).K₀ = 14) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_441_14.1) elcCert_441_14.2 i hi

/-- `(441,28)`: period `1`, cycle `[7]`, all bands deep (`≥ 5`). -/
private theorem elcCert_441_28 :
    slopeOrbit 441 28 (1 + 1) = slopeOrbit 441 28 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 441 28 j ≤ 441 := by
  have e0 : slopeOrbit 441 28 0 = 28 := rfl
  have e1 : slopeOrbit 441 28 1 = 7 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 441 28 2 = 7 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 441 28 2 = slopeOrbit 441 28 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(441,28)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_441_28 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 441)
    (hK : (class1SlopeDatum ctx).K₀ = 28) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_441_28.1) elcCert_441_28.2 i hi

/-- `(441,56)`: period `1`, cycle `[7]`, all bands deep (`≥ 5`). -/
private theorem elcCert_441_56 :
    slopeOrbit 441 56 (1 + 1) = slopeOrbit 441 56 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 441 56 j ≤ 441 := by
  have e0 : slopeOrbit 441 56 0 = 56 := rfl
  have e1 : slopeOrbit 441 56 1 = 7 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 441 56 2 = 7 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 441 56 2 = slopeOrbit 441 56 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(441,56)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_441_56 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 441)
    (hK : (class1SlopeDatum ctx).K₀ = 56) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_441_56.1) elcCert_441_56.2 i hi

/-- `(441,112)`: period `1`, cycle `[7]`, all bands deep (`≥ 5`). -/
private theorem elcCert_441_112 :
    slopeOrbit 441 112 (1 + 1) = slopeOrbit 441 112 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 441 112 j ≤ 441 := by
  have e0 : slopeOrbit 441 112 0 = 112 := rfl
  have e1 : slopeOrbit 441 112 1 = 7 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 441 112 2 = 7 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 441 112 2 = slopeOrbit 441 112 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(441,112)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_441_112 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 441)
    (hK : (class1SlopeDatum ctx).K₀ = 112) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_441_112.1) elcCert_441_112.2 i hi

/-- `(441,224)`: period `1`, cycle `[7]`, all bands deep (`≥ 5`). -/
private theorem elcCert_441_224 :
    slopeOrbit 441 224 (1 + 1) = slopeOrbit 441 224 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 441 224 j ≤ 441 := by
  have e0 : slopeOrbit 441 224 0 = 224 := rfl
  have e1 : slopeOrbit 441 224 1 = 7 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 441 224 2 = 7 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 441 224 2 = slopeOrbit 441 224 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(441,224)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_441_224 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 441)
    (hK : (class1SlopeDatum ctx).K₀ = 224) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_441_224.1) elcCert_441_224.2 i hi

/-- `(465,15)`: period `1`, cycle `[15]`, all bands deep (`≥ 5`). -/
private theorem elcCert_465_15 :
    slopeOrbit 465 15 (1 + 1) = slopeOrbit 465 15 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 465 15 j ≤ 465 := by
  have e0 : slopeOrbit 465 15 0 = 15 := rfl
  have e1 : slopeOrbit 465 15 1 = 15 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 465 15 2 = 15 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 465 15 2 = slopeOrbit 465 15 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(465,15)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_465_15 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 465)
    (hK : (class1SlopeDatum ctx).K₀ = 15) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_465_15.1) elcCert_465_15.2 i hi

/-- `(465,30)`: period `1`, cycle `[15]`, all bands deep (`≥ 5`). -/
private theorem elcCert_465_30 :
    slopeOrbit 465 30 (1 + 1) = slopeOrbit 465 30 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 465 30 j ≤ 465 := by
  have e0 : slopeOrbit 465 30 0 = 30 := rfl
  have e1 : slopeOrbit 465 30 1 = 15 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 465 30 2 = 15 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 465 30 2 = slopeOrbit 465 30 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(465,30)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_465_30 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 465)
    (hK : (class1SlopeDatum ctx).K₀ = 30) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_465_30.1) elcCert_465_30.2 i hi

/-- `(465,60)`: period `1`, cycle `[15]`, all bands deep (`≥ 5`). -/
private theorem elcCert_465_60 :
    slopeOrbit 465 60 (1 + 1) = slopeOrbit 465 60 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 465 60 j ≤ 465 := by
  have e0 : slopeOrbit 465 60 0 = 60 := rfl
  have e1 : slopeOrbit 465 60 1 = 15 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 465 60 2 = 15 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 465 60 2 = slopeOrbit 465 60 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(465,60)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_465_60 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 465)
    (hK : (class1SlopeDatum ctx).K₀ = 60) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_465_60.1) elcCert_465_60.2 i hi

/-- `(465,120)`: period `1`, cycle `[15]`, all bands deep (`≥ 5`). -/
private theorem elcCert_465_120 :
    slopeOrbit 465 120 (1 + 1) = slopeOrbit 465 120 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 465 120 j ≤ 465 := by
  have e0 : slopeOrbit 465 120 0 = 120 := rfl
  have e1 : slopeOrbit 465 120 1 = 15 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 465 120 2 = 15 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 465 120 2 = slopeOrbit 465 120 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(465,120)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_465_120 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 465)
    (hK : (class1SlopeDatum ctx).K₀ = 120) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_465_120.1) elcCert_465_120.2 i hi

/-- `(465,240)`: period `1`, cycle `[15]`, all bands deep (`≥ 5`). -/
private theorem elcCert_465_240 :
    slopeOrbit 465 240 (1 + 1) = slopeOrbit 465 240 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 465 240 j ≤ 465 := by
  have e0 : slopeOrbit 465 240 0 = 240 := rfl
  have e1 : slopeOrbit 465 240 1 = 15 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 465 240 2 = 15 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 465 240 2 = slopeOrbit 465 240 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(465,240)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_465_240 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 465)
    (hK : (class1SlopeDatum ctx).K₀ = 240) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_465_240.1) elcCert_465_240.2 i hi

/-- `(511,1)`: period `1`, cycle `[1]`, all bands deep (`≥ 5`). -/
private theorem elcCert_511_1 :
    slopeOrbit 511 1 (1 + 1) = slopeOrbit 511 1 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 511 1 j ≤ 511 := by
  have e0 : slopeOrbit 511 1 0 = 1 := rfl
  have e1 : slopeOrbit 511 1 1 = 1 :=
    slopeOrbit_step_eval 0 8 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 511 1 2 = 1 :=
    slopeOrbit_step_eval 1 8 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 511 1 2 = slopeOrbit 511 1 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(511,1)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_511_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 511)
    (hK : (class1SlopeDatum ctx).K₀ = 1) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_511_1.1) elcCert_511_1.2 i hi

/-- `(511,2)`: period `1`, cycle `[1]`, all bands deep (`≥ 5`). -/
private theorem elcCert_511_2 :
    slopeOrbit 511 2 (1 + 1) = slopeOrbit 511 2 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 511 2 j ≤ 511 := by
  have e0 : slopeOrbit 511 2 0 = 2 := rfl
  have e1 : slopeOrbit 511 2 1 = 1 :=
    slopeOrbit_step_eval 0 7 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 511 2 2 = 1 :=
    slopeOrbit_step_eval 1 8 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 511 2 2 = slopeOrbit 511 2 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(511,2)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_511_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 511)
    (hK : (class1SlopeDatum ctx).K₀ = 2) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_511_2.1) elcCert_511_2.2 i hi

/-- `(511,4)`: period `1`, cycle `[1]`, all bands deep (`≥ 5`). -/
private theorem elcCert_511_4 :
    slopeOrbit 511 4 (1 + 1) = slopeOrbit 511 4 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 511 4 j ≤ 511 := by
  have e0 : slopeOrbit 511 4 0 = 4 := rfl
  have e1 : slopeOrbit 511 4 1 = 1 :=
    slopeOrbit_step_eval 0 6 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 511 4 2 = 1 :=
    slopeOrbit_step_eval 1 8 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 511 4 2 = slopeOrbit 511 4 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(511,4)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_511_4 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 511)
    (hK : (class1SlopeDatum ctx).K₀ = 4) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_511_4.1) elcCert_511_4.2 i hi

/-- `(511,8)`: period `1`, cycle `[1]`, all bands deep (`≥ 5`). -/
private theorem elcCert_511_8 :
    slopeOrbit 511 8 (1 + 1) = slopeOrbit 511 8 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 511 8 j ≤ 511 := by
  have e0 : slopeOrbit 511 8 0 = 8 := rfl
  have e1 : slopeOrbit 511 8 1 = 1 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 511 8 2 = 1 :=
    slopeOrbit_step_eval 1 8 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 511 8 2 = slopeOrbit 511 8 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(511,8)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_511_8 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 511)
    (hK : (class1SlopeDatum ctx).K₀ = 8) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_511_8.1) elcCert_511_8.2 i hi

/-- `(511,16)`: period `1`, cycle `[1]`, all bands deep (`≥ 5`). -/
private theorem elcCert_511_16 :
    slopeOrbit 511 16 (1 + 1) = slopeOrbit 511 16 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 511 16 j ≤ 511 := by
  have e0 : slopeOrbit 511 16 0 = 16 := rfl
  have e1 : slopeOrbit 511 16 1 = 1 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 511 16 2 = 1 :=
    slopeOrbit_step_eval 1 8 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 511 16 2 = slopeOrbit 511 16 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(511,16)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_511_16 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 511)
    (hK : (class1SlopeDatum ctx).K₀ = 16) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_511_16.1) elcCert_511_16.2 i hi

/-- `(511,32)`: period `1`, cycle `[1]`, all bands deep (`≥ 5`). -/
private theorem elcCert_511_32 :
    slopeOrbit 511 32 (1 + 1) = slopeOrbit 511 32 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 511 32 j ≤ 511 := by
  have e0 : slopeOrbit 511 32 0 = 32 := rfl
  have e1 : slopeOrbit 511 32 1 = 1 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 511 32 2 = 1 :=
    slopeOrbit_step_eval 1 8 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 511 32 2 = slopeOrbit 511 32 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(511,32)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_511_32 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 511)
    (hK : (class1SlopeDatum ctx).K₀ = 32) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_511_32.1) elcCert_511_32.2 i hi

/-- `(511,64)`: period `1`, cycle `[1]`, all bands deep (`≥ 5`). -/
private theorem elcCert_511_64 :
    slopeOrbit 511 64 (1 + 1) = slopeOrbit 511 64 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 511 64 j ≤ 511 := by
  have e0 : slopeOrbit 511 64 0 = 64 := rfl
  have e1 : slopeOrbit 511 64 1 = 1 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 511 64 2 = 1 :=
    slopeOrbit_step_eval 1 8 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 511 64 2 = slopeOrbit 511 64 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(511,64)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_511_64 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 511)
    (hK : (class1SlopeDatum ctx).K₀ = 64) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_511_64.1) elcCert_511_64.2 i hi

/-- `(511,128)`: period `1`, cycle `[1]`, all bands deep (`≥ 5`). -/
private theorem elcCert_511_128 :
    slopeOrbit 511 128 (1 + 1) = slopeOrbit 511 128 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 511 128 j ≤ 511 := by
  have e0 : slopeOrbit 511 128 0 = 128 := rfl
  have e1 : slopeOrbit 511 128 1 = 1 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 511 128 2 = 1 :=
    slopeOrbit_step_eval 1 8 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 511 128 2 = slopeOrbit 511 128 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(511,128)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_511_128 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 511)
    (hK : (class1SlopeDatum ctx).K₀ = 128) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_511_128.1) elcCert_511_128.2 i hi

/-- `(511,256)`: period `1`, cycle `[1]`, all bands deep (`≥ 5`). -/
private theorem elcCert_511_256 :
    slopeOrbit 511 256 (1 + 1) = slopeOrbit 511 256 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 511 256 j ≤ 511 := by
  have e0 : slopeOrbit 511 256 0 = 256 := rfl
  have e1 : slopeOrbit 511 256 1 = 1 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 511 256 2 = 1 :=
    slopeOrbit_step_eval 1 8 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 511 256 2 = slopeOrbit 511 256 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(511,256)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_511_256 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 511)
    (hK : (class1SlopeDatum ctx).K₀ = 256) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_511_256.1) elcCert_511_256.2 i hi

/-- `(527,17)`: period `1`, cycle `[17]`, all bands deep (`≥ 5`). -/
private theorem elcCert_527_17 :
    slopeOrbit 527 17 (1 + 1) = slopeOrbit 527 17 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 527 17 j ≤ 527 := by
  have e0 : slopeOrbit 527 17 0 = 17 := rfl
  have e1 : slopeOrbit 527 17 1 = 17 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 527 17 2 = 17 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 527 17 2 = slopeOrbit 527 17 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(527,17)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_527_17 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 527)
    (hK : (class1SlopeDatum ctx).K₀ = 17) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_527_17.1) elcCert_527_17.2 i hi

/-- `(527,34)`: period `1`, cycle `[17]`, all bands deep (`≥ 5`). -/
private theorem elcCert_527_34 :
    slopeOrbit 527 34 (1 + 1) = slopeOrbit 527 34 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 527 34 j ≤ 527 := by
  have e0 : slopeOrbit 527 34 0 = 34 := rfl
  have e1 : slopeOrbit 527 34 1 = 17 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 527 34 2 = 17 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 527 34 2 = slopeOrbit 527 34 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(527,34)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_527_34 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 527)
    (hK : (class1SlopeDatum ctx).K₀ = 34) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_527_34.1) elcCert_527_34.2 i hi

/-- `(527,68)`: period `1`, cycle `[17]`, all bands deep (`≥ 5`). -/
private theorem elcCert_527_68 :
    slopeOrbit 527 68 (1 + 1) = slopeOrbit 527 68 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 527 68 j ≤ 527 := by
  have e0 : slopeOrbit 527 68 0 = 68 := rfl
  have e1 : slopeOrbit 527 68 1 = 17 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 527 68 2 = 17 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 527 68 2 = slopeOrbit 527 68 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(527,68)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_527_68 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 527)
    (hK : (class1SlopeDatum ctx).K₀ = 68) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_527_68.1) elcCert_527_68.2 i hi

/-- `(527,136)`: period `1`, cycle `[17]`, all bands deep (`≥ 5`). -/
private theorem elcCert_527_136 :
    slopeOrbit 527 136 (1 + 1) = slopeOrbit 527 136 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 527 136 j ≤ 527 := by
  have e0 : slopeOrbit 527 136 0 = 136 := rfl
  have e1 : slopeOrbit 527 136 1 = 17 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 527 136 2 = 17 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 527 136 2 = slopeOrbit 527 136 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(527,136)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_527_136 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 527)
    (hK : (class1SlopeDatum ctx).K₀ = 136) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_527_136.1) elcCert_527_136.2 i hi

/-- `(527,272)`: period `1`, cycle `[17]`, all bands deep (`≥ 5`). -/
private theorem elcCert_527_272 :
    slopeOrbit 527 272 (1 + 1) = slopeOrbit 527 272 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 527 272 j ≤ 527 := by
  have e0 : slopeOrbit 527 272 0 = 272 := rfl
  have e1 : slopeOrbit 527 272 1 = 17 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 527 272 2 = 17 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 527 272 2 = slopeOrbit 527 272 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(527,272)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_527_272 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 527)
    (hK : (class1SlopeDatum ctx).K₀ = 272) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_527_272.1) elcCert_527_272.2 i hi

/-- `(567,9)`: period `1`, cycle `[9]`, all bands deep (`≥ 5`). -/
private theorem elcCert_567_9 :
    slopeOrbit 567 9 (1 + 1) = slopeOrbit 567 9 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 567 9 j ≤ 567 := by
  have e0 : slopeOrbit 567 9 0 = 9 := rfl
  have e1 : slopeOrbit 567 9 1 = 9 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 567 9 2 = 9 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 567 9 2 = slopeOrbit 567 9 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(567,9)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_567_9 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 567)
    (hK : (class1SlopeDatum ctx).K₀ = 9) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_567_9.1) elcCert_567_9.2 i hi

/-- `(567,18)`: period `1`, cycle `[9]`, all bands deep (`≥ 5`). -/
private theorem elcCert_567_18 :
    slopeOrbit 567 18 (1 + 1) = slopeOrbit 567 18 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 567 18 j ≤ 567 := by
  have e0 : slopeOrbit 567 18 0 = 18 := rfl
  have e1 : slopeOrbit 567 18 1 = 9 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 567 18 2 = 9 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 567 18 2 = slopeOrbit 567 18 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(567,18)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_567_18 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 567)
    (hK : (class1SlopeDatum ctx).K₀ = 18) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_567_18.1) elcCert_567_18.2 i hi

/-- `(567,36)`: period `1`, cycle `[9]`, all bands deep (`≥ 5`). -/
private theorem elcCert_567_36 :
    slopeOrbit 567 36 (1 + 1) = slopeOrbit 567 36 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 567 36 j ≤ 567 := by
  have e0 : slopeOrbit 567 36 0 = 36 := rfl
  have e1 : slopeOrbit 567 36 1 = 9 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 567 36 2 = 9 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 567 36 2 = slopeOrbit 567 36 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(567,36)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_567_36 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 567)
    (hK : (class1SlopeDatum ctx).K₀ = 36) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_567_36.1) elcCert_567_36.2 i hi

/-- `(567,72)`: period `1`, cycle `[9]`, all bands deep (`≥ 5`). -/
private theorem elcCert_567_72 :
    slopeOrbit 567 72 (1 + 1) = slopeOrbit 567 72 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 567 72 j ≤ 567 := by
  have e0 : slopeOrbit 567 72 0 = 72 := rfl
  have e1 : slopeOrbit 567 72 1 = 9 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 567 72 2 = 9 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 567 72 2 = slopeOrbit 567 72 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(567,72)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_567_72 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 567)
    (hK : (class1SlopeDatum ctx).K₀ = 72) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_567_72.1) elcCert_567_72.2 i hi

/-- `(567,144)`: period `1`, cycle `[9]`, all bands deep (`≥ 5`). -/
private theorem elcCert_567_144 :
    slopeOrbit 567 144 (1 + 1) = slopeOrbit 567 144 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 567 144 j ≤ 567 := by
  have e0 : slopeOrbit 567 144 0 = 144 := rfl
  have e1 : slopeOrbit 567 144 1 = 9 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 567 144 2 = 9 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 567 144 2 = slopeOrbit 567 144 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(567,144)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_567_144 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 567)
    (hK : (class1SlopeDatum ctx).K₀ = 144) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_567_144.1) elcCert_567_144.2 i hi

/-- `(567,288)`: period `1`, cycle `[9]`, all bands deep (`≥ 5`). -/
private theorem elcCert_567_288 :
    slopeOrbit 567 288 (1 + 1) = slopeOrbit 567 288 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 567 288 j ≤ 567 := by
  have e0 : slopeOrbit 567 288 0 = 288 := rfl
  have e1 : slopeOrbit 567 288 1 = 9 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 567 288 2 = 9 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 567 288 2 = slopeOrbit 567 288 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(567,288)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_567_288 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 567)
    (hK : (class1SlopeDatum ctx).K₀ = 288) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_567_288.1) elcCert_567_288.2 i hi

/-- `(589,19)`: period `1`, cycle `[19]`, all bands deep (`≥ 5`). -/
private theorem elcCert_589_19 :
    slopeOrbit 589 19 (1 + 1) = slopeOrbit 589 19 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 589 19 j ≤ 589 := by
  have e0 : slopeOrbit 589 19 0 = 19 := rfl
  have e1 : slopeOrbit 589 19 1 = 19 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 589 19 2 = 19 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 589 19 2 = slopeOrbit 589 19 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(589,19)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_589_19 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 589)
    (hK : (class1SlopeDatum ctx).K₀ = 19) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_589_19.1) elcCert_589_19.2 i hi

/-- `(589,38)`: period `1`, cycle `[19]`, all bands deep (`≥ 5`). -/
private theorem elcCert_589_38 :
    slopeOrbit 589 38 (1 + 1) = slopeOrbit 589 38 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 589 38 j ≤ 589 := by
  have e0 : slopeOrbit 589 38 0 = 38 := rfl
  have e1 : slopeOrbit 589 38 1 = 19 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 589 38 2 = 19 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 589 38 2 = slopeOrbit 589 38 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(589,38)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_589_38 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 589)
    (hK : (class1SlopeDatum ctx).K₀ = 38) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_589_38.1) elcCert_589_38.2 i hi

/-- `(589,76)`: period `1`, cycle `[19]`, all bands deep (`≥ 5`). -/
private theorem elcCert_589_76 :
    slopeOrbit 589 76 (1 + 1) = slopeOrbit 589 76 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 589 76 j ≤ 589 := by
  have e0 : slopeOrbit 589 76 0 = 76 := rfl
  have e1 : slopeOrbit 589 76 1 = 19 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 589 76 2 = 19 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 589 76 2 = slopeOrbit 589 76 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(589,76)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_589_76 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 589)
    (hK : (class1SlopeDatum ctx).K₀ = 76) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_589_76.1) elcCert_589_76.2 i hi

/-- `(589,152)`: period `1`, cycle `[19]`, all bands deep (`≥ 5`). -/
private theorem elcCert_589_152 :
    slopeOrbit 589 152 (1 + 1) = slopeOrbit 589 152 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 589 152 j ≤ 589 := by
  have e0 : slopeOrbit 589 152 0 = 152 := rfl
  have e1 : slopeOrbit 589 152 1 = 19 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 589 152 2 = 19 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 589 152 2 = slopeOrbit 589 152 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(589,152)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_589_152 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 589)
    (hK : (class1SlopeDatum ctx).K₀ = 152) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_589_152.1) elcCert_589_152.2 i hi

/-- `(589,304)`: period `1`, cycle `[19]`, all bands deep (`≥ 5`). -/
private theorem elcCert_589_304 :
    slopeOrbit 589 304 (1 + 1) = slopeOrbit 589 304 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 589 304 j ≤ 589 := by
  have e0 : slopeOrbit 589 304 0 = 304 := rfl
  have e1 : slopeOrbit 589 304 1 = 19 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 589 304 2 = 19 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 589 304 2 = slopeOrbit 589 304 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(589,304)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_589_304 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 589)
    (hK : (class1SlopeDatum ctx).K₀ = 304) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_589_304.1) elcCert_589_304.2 i hi

/-- `(635,5)`: period `1`, cycle `[5]`, all bands deep (`≥ 5`). -/
private theorem elcCert_635_5 :
    slopeOrbit 635 5 (1 + 1) = slopeOrbit 635 5 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 635 5 j ≤ 635 := by
  have e0 : slopeOrbit 635 5 0 = 5 := rfl
  have e1 : slopeOrbit 635 5 1 = 5 :=
    slopeOrbit_step_eval 0 6 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 635 5 2 = 5 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 635 5 2 = slopeOrbit 635 5 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(635,5)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_635_5 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 635)
    (hK : (class1SlopeDatum ctx).K₀ = 5) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_635_5.1) elcCert_635_5.2 i hi

/-- `(635,10)`: period `1`, cycle `[5]`, all bands deep (`≥ 5`). -/
private theorem elcCert_635_10 :
    slopeOrbit 635 10 (1 + 1) = slopeOrbit 635 10 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 635 10 j ≤ 635 := by
  have e0 : slopeOrbit 635 10 0 = 10 := rfl
  have e1 : slopeOrbit 635 10 1 = 5 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 635 10 2 = 5 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 635 10 2 = slopeOrbit 635 10 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(635,10)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_635_10 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 635)
    (hK : (class1SlopeDatum ctx).K₀ = 10) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_635_10.1) elcCert_635_10.2 i hi

/-- `(635,20)`: period `1`, cycle `[5]`, all bands deep (`≥ 5`). -/
private theorem elcCert_635_20 :
    slopeOrbit 635 20 (1 + 1) = slopeOrbit 635 20 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 635 20 j ≤ 635 := by
  have e0 : slopeOrbit 635 20 0 = 20 := rfl
  have e1 : slopeOrbit 635 20 1 = 5 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 635 20 2 = 5 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 635 20 2 = slopeOrbit 635 20 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(635,20)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_635_20 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 635)
    (hK : (class1SlopeDatum ctx).K₀ = 20) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_635_20.1) elcCert_635_20.2 i hi

/-- `(635,40)`: period `1`, cycle `[5]`, all bands deep (`≥ 5`). -/
private theorem elcCert_635_40 :
    slopeOrbit 635 40 (1 + 1) = slopeOrbit 635 40 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 635 40 j ≤ 635 := by
  have e0 : slopeOrbit 635 40 0 = 40 := rfl
  have e1 : slopeOrbit 635 40 1 = 5 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 635 40 2 = 5 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 635 40 2 = slopeOrbit 635 40 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(635,40)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_635_40 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 635)
    (hK : (class1SlopeDatum ctx).K₀ = 40) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_635_40.1) elcCert_635_40.2 i hi

/-- `(635,80)`: period `1`, cycle `[5]`, all bands deep (`≥ 5`). -/
private theorem elcCert_635_80 :
    slopeOrbit 635 80 (1 + 1) = slopeOrbit 635 80 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 635 80 j ≤ 635 := by
  have e0 : slopeOrbit 635 80 0 = 80 := rfl
  have e1 : slopeOrbit 635 80 1 = 5 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 635 80 2 = 5 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 635 80 2 = slopeOrbit 635 80 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(635,80)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_635_80 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 635)
    (hK : (class1SlopeDatum ctx).K₀ = 80) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_635_80.1) elcCert_635_80.2 i hi

/-- `(635,160)`: period `1`, cycle `[5]`, all bands deep (`≥ 5`). -/
private theorem elcCert_635_160 :
    slopeOrbit 635 160 (1 + 1) = slopeOrbit 635 160 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 635 160 j ≤ 635 := by
  have e0 : slopeOrbit 635 160 0 = 160 := rfl
  have e1 : slopeOrbit 635 160 1 = 5 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 635 160 2 = 5 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 635 160 2 = slopeOrbit 635 160 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(635,160)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_635_160 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 635)
    (hK : (class1SlopeDatum ctx).K₀ = 160) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_635_160.1) elcCert_635_160.2 i hi

/-- `(635,320)`: period `1`, cycle `[5]`, all bands deep (`≥ 5`). -/
private theorem elcCert_635_320 :
    slopeOrbit 635 320 (1 + 1) = slopeOrbit 635 320 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 635 320 j ≤ 635 := by
  have e0 : slopeOrbit 635 320 0 = 320 := rfl
  have e1 : slopeOrbit 635 320 1 = 5 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 635 320 2 = 5 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 635 320 2 = slopeOrbit 635 320 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(635,320)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_635_320 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 635)
    (hK : (class1SlopeDatum ctx).K₀ = 320) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_635_320.1) elcCert_635_320.2 i hi

/-- `(651,21)`: period `1`, cycle `[21]`, all bands deep (`≥ 5`). -/
private theorem elcCert_651_21 :
    slopeOrbit 651 21 (1 + 1) = slopeOrbit 651 21 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 651 21 j ≤ 651 := by
  have e0 : slopeOrbit 651 21 0 = 21 := rfl
  have e1 : slopeOrbit 651 21 1 = 21 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 651 21 2 = 21 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 651 21 2 = slopeOrbit 651 21 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(651,21)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_651_21 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 651)
    (hK : (class1SlopeDatum ctx).K₀ = 21) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_651_21.1) elcCert_651_21.2 i hi

/-- `(651,42)`: period `1`, cycle `[21]`, all bands deep (`≥ 5`). -/
private theorem elcCert_651_42 :
    slopeOrbit 651 42 (1 + 1) = slopeOrbit 651 42 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 651 42 j ≤ 651 := by
  have e0 : slopeOrbit 651 42 0 = 42 := rfl
  have e1 : slopeOrbit 651 42 1 = 21 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 651 42 2 = 21 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 651 42 2 = slopeOrbit 651 42 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(651,42)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_651_42 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 651)
    (hK : (class1SlopeDatum ctx).K₀ = 42) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_651_42.1) elcCert_651_42.2 i hi

/-- `(651,84)`: period `1`, cycle `[21]`, all bands deep (`≥ 5`). -/
private theorem elcCert_651_84 :
    slopeOrbit 651 84 (1 + 1) = slopeOrbit 651 84 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 651 84 j ≤ 651 := by
  have e0 : slopeOrbit 651 84 0 = 84 := rfl
  have e1 : slopeOrbit 651 84 1 = 21 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 651 84 2 = 21 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 651 84 2 = slopeOrbit 651 84 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(651,84)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_651_84 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 651)
    (hK : (class1SlopeDatum ctx).K₀ = 84) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_651_84.1) elcCert_651_84.2 i hi

/-- `(651,168)`: period `1`, cycle `[21]`, all bands deep (`≥ 5`). -/
private theorem elcCert_651_168 :
    slopeOrbit 651 168 (1 + 1) = slopeOrbit 651 168 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 651 168 j ≤ 651 := by
  have e0 : slopeOrbit 651 168 0 = 168 := rfl
  have e1 : slopeOrbit 651 168 1 = 21 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 651 168 2 = 21 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 651 168 2 = slopeOrbit 651 168 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(651,168)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_651_168 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 651)
    (hK : (class1SlopeDatum ctx).K₀ = 168) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_651_168.1) elcCert_651_168.2 i hi

/-- `(651,336)`: period `1`, cycle `[21]`, all bands deep (`≥ 5`). -/
private theorem elcCert_651_336 :
    slopeOrbit 651 336 (1 + 1) = slopeOrbit 651 336 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 651 336 j ≤ 651 := by
  have e0 : slopeOrbit 651 336 0 = 336 := rfl
  have e1 : slopeOrbit 651 336 1 = 21 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 651 336 2 = 21 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 651 336 2 = slopeOrbit 651 336 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(651,336)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_651_336 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 651)
    (hK : (class1SlopeDatum ctx).K₀ = 336) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_651_336.1) elcCert_651_336.2 i hi

/-- `(693,11)`: period `1`, cycle `[11]`, all bands deep (`≥ 5`). -/
private theorem elcCert_693_11 :
    slopeOrbit 693 11 (1 + 1) = slopeOrbit 693 11 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 693 11 j ≤ 693 := by
  have e0 : slopeOrbit 693 11 0 = 11 := rfl
  have e1 : slopeOrbit 693 11 1 = 11 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 693 11 2 = 11 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 693 11 2 = slopeOrbit 693 11 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(693,11)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_693_11 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 693)
    (hK : (class1SlopeDatum ctx).K₀ = 11) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_693_11.1) elcCert_693_11.2 i hi

/-- `(693,22)`: period `1`, cycle `[11]`, all bands deep (`≥ 5`). -/
private theorem elcCert_693_22 :
    slopeOrbit 693 22 (1 + 1) = slopeOrbit 693 22 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 693 22 j ≤ 693 := by
  have e0 : slopeOrbit 693 22 0 = 22 := rfl
  have e1 : slopeOrbit 693 22 1 = 11 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 693 22 2 = 11 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 693 22 2 = slopeOrbit 693 22 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(693,22)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_693_22 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 693)
    (hK : (class1SlopeDatum ctx).K₀ = 22) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_693_22.1) elcCert_693_22.2 i hi

/-- `(693,44)`: period `1`, cycle `[11]`, all bands deep (`≥ 5`). -/
private theorem elcCert_693_44 :
    slopeOrbit 693 44 (1 + 1) = slopeOrbit 693 44 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 693 44 j ≤ 693 := by
  have e0 : slopeOrbit 693 44 0 = 44 := rfl
  have e1 : slopeOrbit 693 44 1 = 11 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 693 44 2 = 11 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 693 44 2 = slopeOrbit 693 44 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(693,44)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_693_44 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 693)
    (hK : (class1SlopeDatum ctx).K₀ = 44) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_693_44.1) elcCert_693_44.2 i hi

/-- `(693,88)`: period `1`, cycle `[11]`, all bands deep (`≥ 5`). -/
private theorem elcCert_693_88 :
    slopeOrbit 693 88 (1 + 1) = slopeOrbit 693 88 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 693 88 j ≤ 693 := by
  have e0 : slopeOrbit 693 88 0 = 88 := rfl
  have e1 : slopeOrbit 693 88 1 = 11 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 693 88 2 = 11 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 693 88 2 = slopeOrbit 693 88 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(693,88)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_693_88 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 693)
    (hK : (class1SlopeDatum ctx).K₀ = 88) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_693_88.1) elcCert_693_88.2 i hi

/-- `(693,176)`: period `1`, cycle `[11]`, all bands deep (`≥ 5`). -/
private theorem elcCert_693_176 :
    slopeOrbit 693 176 (1 + 1) = slopeOrbit 693 176 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 693 176 j ≤ 693 := by
  have e0 : slopeOrbit 693 176 0 = 176 := rfl
  have e1 : slopeOrbit 693 176 1 = 11 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 693 176 2 = 11 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 693 176 2 = slopeOrbit 693 176 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(693,176)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_693_176 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 693)
    (hK : (class1SlopeDatum ctx).K₀ = 176) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_693_176.1) elcCert_693_176.2 i hi

/-- `(693,352)`: period `1`, cycle `[11]`, all bands deep (`≥ 5`). -/
private theorem elcCert_693_352 :
    slopeOrbit 693 352 (1 + 1) = slopeOrbit 693 352 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 693 352 j ≤ 693 := by
  have e0 : slopeOrbit 693 352 0 = 352 := rfl
  have e1 : slopeOrbit 693 352 1 = 11 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 693 352 2 = 11 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 693 352 2 = slopeOrbit 693 352 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(693,352)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_693_352 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 693)
    (hK : (class1SlopeDatum ctx).K₀ = 352) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_693_352.1) elcCert_693_352.2 i hi

/-- `(713,23)`: period `1`, cycle `[23]`, all bands deep (`≥ 5`). -/
private theorem elcCert_713_23 :
    slopeOrbit 713 23 (1 + 1) = slopeOrbit 713 23 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 713 23 j ≤ 713 := by
  have e0 : slopeOrbit 713 23 0 = 23 := rfl
  have e1 : slopeOrbit 713 23 1 = 23 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 713 23 2 = 23 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 713 23 2 = slopeOrbit 713 23 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(713,23)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_713_23 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 713)
    (hK : (class1SlopeDatum ctx).K₀ = 23) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_713_23.1) elcCert_713_23.2 i hi

/-- `(713,46)`: period `1`, cycle `[23]`, all bands deep (`≥ 5`). -/
private theorem elcCert_713_46 :
    slopeOrbit 713 46 (1 + 1) = slopeOrbit 713 46 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 713 46 j ≤ 713 := by
  have e0 : slopeOrbit 713 46 0 = 46 := rfl
  have e1 : slopeOrbit 713 46 1 = 23 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 713 46 2 = 23 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 713 46 2 = slopeOrbit 713 46 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(713,46)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_713_46 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 713)
    (hK : (class1SlopeDatum ctx).K₀ = 46) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_713_46.1) elcCert_713_46.2 i hi

/-- `(713,92)`: period `1`, cycle `[23]`, all bands deep (`≥ 5`). -/
private theorem elcCert_713_92 :
    slopeOrbit 713 92 (1 + 1) = slopeOrbit 713 92 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 713 92 j ≤ 713 := by
  have e0 : slopeOrbit 713 92 0 = 92 := rfl
  have e1 : slopeOrbit 713 92 1 = 23 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 713 92 2 = 23 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 713 92 2 = slopeOrbit 713 92 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(713,92)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_713_92 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 713)
    (hK : (class1SlopeDatum ctx).K₀ = 92) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_713_92.1) elcCert_713_92.2 i hi

/-- `(713,184)`: period `1`, cycle `[23]`, all bands deep (`≥ 5`). -/
private theorem elcCert_713_184 :
    slopeOrbit 713 184 (1 + 1) = slopeOrbit 713 184 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 713 184 j ≤ 713 := by
  have e0 : slopeOrbit 713 184 0 = 184 := rfl
  have e1 : slopeOrbit 713 184 1 = 23 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 713 184 2 = 23 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 713 184 2 = slopeOrbit 713 184 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(713,184)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_713_184 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 713)
    (hK : (class1SlopeDatum ctx).K₀ = 184) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_713_184.1) elcCert_713_184.2 i hi

/-- `(713,368)`: period `1`, cycle `[23]`, all bands deep (`≥ 5`). -/
private theorem elcCert_713_368 :
    slopeOrbit 713 368 (1 + 1) = slopeOrbit 713 368 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 713 368 j ≤ 713 := by
  have e0 : slopeOrbit 713 368 0 = 368 := rfl
  have e1 : slopeOrbit 713 368 1 = 23 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 713 368 2 = 23 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 713 368 2 = slopeOrbit 713 368 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(713,368)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_713_368 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 713)
    (hK : (class1SlopeDatum ctx).K₀ = 368) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_713_368.1) elcCert_713_368.2 i hi

/-- `(765,3)`: period `1`, cycle `[3]`, all bands deep (`≥ 5`). -/
private theorem elcCert_765_3 :
    slopeOrbit 765 3 (1 + 1) = slopeOrbit 765 3 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 765 3 j ≤ 765 := by
  have e0 : slopeOrbit 765 3 0 = 3 := rfl
  have e1 : slopeOrbit 765 3 1 = 3 :=
    slopeOrbit_step_eval 0 7 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 765 3 2 = 3 :=
    slopeOrbit_step_eval 1 7 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 765 3 2 = slopeOrbit 765 3 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(765,3)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_765_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 765)
    (hK : (class1SlopeDatum ctx).K₀ = 3) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_765_3.1) elcCert_765_3.2 i hi

/-- `(765,6)`: period `1`, cycle `[3]`, all bands deep (`≥ 5`). -/
private theorem elcCert_765_6 :
    slopeOrbit 765 6 (1 + 1) = slopeOrbit 765 6 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 765 6 j ≤ 765 := by
  have e0 : slopeOrbit 765 6 0 = 6 := rfl
  have e1 : slopeOrbit 765 6 1 = 3 :=
    slopeOrbit_step_eval 0 6 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 765 6 2 = 3 :=
    slopeOrbit_step_eval 1 7 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 765 6 2 = slopeOrbit 765 6 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(765,6)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_765_6 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 765)
    (hK : (class1SlopeDatum ctx).K₀ = 6) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_765_6.1) elcCert_765_6.2 i hi

/-- `(765,12)`: period `1`, cycle `[3]`, all bands deep (`≥ 5`). -/
private theorem elcCert_765_12 :
    slopeOrbit 765 12 (1 + 1) = slopeOrbit 765 12 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 765 12 j ≤ 765 := by
  have e0 : slopeOrbit 765 12 0 = 12 := rfl
  have e1 : slopeOrbit 765 12 1 = 3 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 765 12 2 = 3 :=
    slopeOrbit_step_eval 1 7 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 765 12 2 = slopeOrbit 765 12 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(765,12)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_765_12 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 765)
    (hK : (class1SlopeDatum ctx).K₀ = 12) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_765_12.1) elcCert_765_12.2 i hi

/-- `(765,24)`: period `1`, cycle `[3]`, all bands deep (`≥ 5`). -/
private theorem elcCert_765_24 :
    slopeOrbit 765 24 (1 + 1) = slopeOrbit 765 24 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 765 24 j ≤ 765 := by
  have e0 : slopeOrbit 765 24 0 = 24 := rfl
  have e1 : slopeOrbit 765 24 1 = 3 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 765 24 2 = 3 :=
    slopeOrbit_step_eval 1 7 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 765 24 2 = slopeOrbit 765 24 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(765,24)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_765_24 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 765)
    (hK : (class1SlopeDatum ctx).K₀ = 24) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_765_24.1) elcCert_765_24.2 i hi

/-- `(765,48)`: period `1`, cycle `[3]`, all bands deep (`≥ 5`). -/
private theorem elcCert_765_48 :
    slopeOrbit 765 48 (1 + 1) = slopeOrbit 765 48 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 765 48 j ≤ 765 := by
  have e0 : slopeOrbit 765 48 0 = 48 := rfl
  have e1 : slopeOrbit 765 48 1 = 3 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 765 48 2 = 3 :=
    slopeOrbit_step_eval 1 7 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 765 48 2 = slopeOrbit 765 48 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(765,48)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_765_48 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 765)
    (hK : (class1SlopeDatum ctx).K₀ = 48) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_765_48.1) elcCert_765_48.2 i hi

/-- `(765,96)`: period `1`, cycle `[3]`, all bands deep (`≥ 5`). -/
private theorem elcCert_765_96 :
    slopeOrbit 765 96 (1 + 1) = slopeOrbit 765 96 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 765 96 j ≤ 765 := by
  have e0 : slopeOrbit 765 96 0 = 96 := rfl
  have e1 : slopeOrbit 765 96 1 = 3 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 765 96 2 = 3 :=
    slopeOrbit_step_eval 1 7 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 765 96 2 = slopeOrbit 765 96 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(765,96)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_765_96 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 765)
    (hK : (class1SlopeDatum ctx).K₀ = 96) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_765_96.1) elcCert_765_96.2 i hi

/-- `(765,192)`: period `1`, cycle `[3]`, all bands deep (`≥ 5`). -/
private theorem elcCert_765_192 :
    slopeOrbit 765 192 (1 + 1) = slopeOrbit 765 192 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 765 192 j ≤ 765 := by
  have e0 : slopeOrbit 765 192 0 = 192 := rfl
  have e1 : slopeOrbit 765 192 1 = 3 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 765 192 2 = 3 :=
    slopeOrbit_step_eval 1 7 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 765 192 2 = slopeOrbit 765 192 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(765,192)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_765_192 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 765)
    (hK : (class1SlopeDatum ctx).K₀ = 192) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_765_192.1) elcCert_765_192.2 i hi

/-- `(765,384)`: period `1`, cycle `[3]`, all bands deep (`≥ 5`). -/
private theorem elcCert_765_384 :
    slopeOrbit 765 384 (1 + 1) = slopeOrbit 765 384 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 765 384 j ≤ 765 := by
  have e0 : slopeOrbit 765 384 0 = 384 := rfl
  have e1 : slopeOrbit 765 384 1 = 3 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 765 384 2 = 3 :=
    slopeOrbit_step_eval 1 7 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 765 384 2 = slopeOrbit 765 384 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(765,384)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_765_384 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 765)
    (hK : (class1SlopeDatum ctx).K₀ = 384) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_765_384.1) elcCert_765_384.2 i hi

/-- `(775,25)`: period `1`, cycle `[25]`, all bands deep (`≥ 5`). -/
private theorem elcCert_775_25 :
    slopeOrbit 775 25 (1 + 1) = slopeOrbit 775 25 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 775 25 j ≤ 775 := by
  have e0 : slopeOrbit 775 25 0 = 25 := rfl
  have e1 : slopeOrbit 775 25 1 = 25 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 775 25 2 = 25 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 775 25 2 = slopeOrbit 775 25 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(775,25)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_775_25 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 775)
    (hK : (class1SlopeDatum ctx).K₀ = 25) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_775_25.1) elcCert_775_25.2 i hi

/-- `(775,50)`: period `1`, cycle `[25]`, all bands deep (`≥ 5`). -/
private theorem elcCert_775_50 :
    slopeOrbit 775 50 (1 + 1) = slopeOrbit 775 50 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 775 50 j ≤ 775 := by
  have e0 : slopeOrbit 775 50 0 = 50 := rfl
  have e1 : slopeOrbit 775 50 1 = 25 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 775 50 2 = 25 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 775 50 2 = slopeOrbit 775 50 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(775,50)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_775_50 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 775)
    (hK : (class1SlopeDatum ctx).K₀ = 50) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_775_50.1) elcCert_775_50.2 i hi

/-- `(775,100)`: period `1`, cycle `[25]`, all bands deep (`≥ 5`). -/
private theorem elcCert_775_100 :
    slopeOrbit 775 100 (1 + 1) = slopeOrbit 775 100 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 775 100 j ≤ 775 := by
  have e0 : slopeOrbit 775 100 0 = 100 := rfl
  have e1 : slopeOrbit 775 100 1 = 25 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 775 100 2 = 25 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 775 100 2 = slopeOrbit 775 100 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(775,100)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_775_100 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 775)
    (hK : (class1SlopeDatum ctx).K₀ = 100) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_775_100.1) elcCert_775_100.2 i hi

/-- `(775,200)`: period `1`, cycle `[25]`, all bands deep (`≥ 5`). -/
private theorem elcCert_775_200 :
    slopeOrbit 775 200 (1 + 1) = slopeOrbit 775 200 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 775 200 j ≤ 775 := by
  have e0 : slopeOrbit 775 200 0 = 200 := rfl
  have e1 : slopeOrbit 775 200 1 = 25 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 775 200 2 = 25 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 775 200 2 = slopeOrbit 775 200 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(775,200)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_775_200 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 775)
    (hK : (class1SlopeDatum ctx).K₀ = 200) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_775_200.1) elcCert_775_200.2 i hi

/-- `(775,400)`: period `1`, cycle `[25]`, all bands deep (`≥ 5`). -/
private theorem elcCert_775_400 :
    slopeOrbit 775 400 (1 + 1) = slopeOrbit 775 400 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 775 400 j ≤ 775 := by
  have e0 : slopeOrbit 775 400 0 = 400 := rfl
  have e1 : slopeOrbit 775 400 1 = 25 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 775 400 2 = 25 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 775 400 2 = slopeOrbit 775 400 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(775,400)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_775_400 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 775)
    (hK : (class1SlopeDatum ctx).K₀ = 400) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_775_400.1) elcCert_775_400.2 i hi

/-- `(819,13)`: period `1`, cycle `[13]`, all bands deep (`≥ 5`). -/
private theorem elcCert_819_13 :
    slopeOrbit 819 13 (1 + 1) = slopeOrbit 819 13 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 819 13 j ≤ 819 := by
  have e0 : slopeOrbit 819 13 0 = 13 := rfl
  have e1 : slopeOrbit 819 13 1 = 13 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 819 13 2 = 13 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 819 13 2 = slopeOrbit 819 13 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(819,13)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_819_13 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 819)
    (hK : (class1SlopeDatum ctx).K₀ = 13) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_819_13.1) elcCert_819_13.2 i hi

/-- `(819,26)`: period `1`, cycle `[13]`, all bands deep (`≥ 5`). -/
private theorem elcCert_819_26 :
    slopeOrbit 819 26 (1 + 1) = slopeOrbit 819 26 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 819 26 j ≤ 819 := by
  have e0 : slopeOrbit 819 26 0 = 26 := rfl
  have e1 : slopeOrbit 819 26 1 = 13 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 819 26 2 = 13 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 819 26 2 = slopeOrbit 819 26 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(819,26)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_819_26 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 819)
    (hK : (class1SlopeDatum ctx).K₀ = 26) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_819_26.1) elcCert_819_26.2 i hi

/-- `(819,52)`: period `1`, cycle `[13]`, all bands deep (`≥ 5`). -/
private theorem elcCert_819_52 :
    slopeOrbit 819 52 (1 + 1) = slopeOrbit 819 52 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 819 52 j ≤ 819 := by
  have e0 : slopeOrbit 819 52 0 = 52 := rfl
  have e1 : slopeOrbit 819 52 1 = 13 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 819 52 2 = 13 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 819 52 2 = slopeOrbit 819 52 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(819,52)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_819_52 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 819)
    (hK : (class1SlopeDatum ctx).K₀ = 52) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_819_52.1) elcCert_819_52.2 i hi

/-- `(819,104)`: period `1`, cycle `[13]`, all bands deep (`≥ 5`). -/
private theorem elcCert_819_104 :
    slopeOrbit 819 104 (1 + 1) = slopeOrbit 819 104 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 819 104 j ≤ 819 := by
  have e0 : slopeOrbit 819 104 0 = 104 := rfl
  have e1 : slopeOrbit 819 104 1 = 13 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 819 104 2 = 13 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 819 104 2 = slopeOrbit 819 104 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(819,104)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_819_104 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 819)
    (hK : (class1SlopeDatum ctx).K₀ = 104) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_819_104.1) elcCert_819_104.2 i hi

/-- `(819,208)`: period `1`, cycle `[13]`, all bands deep (`≥ 5`). -/
private theorem elcCert_819_208 :
    slopeOrbit 819 208 (1 + 1) = slopeOrbit 819 208 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 819 208 j ≤ 819 := by
  have e0 : slopeOrbit 819 208 0 = 208 := rfl
  have e1 : slopeOrbit 819 208 1 = 13 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 819 208 2 = 13 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 819 208 2 = slopeOrbit 819 208 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(819,208)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_819_208 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 819)
    (hK : (class1SlopeDatum ctx).K₀ = 208) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_819_208.1) elcCert_819_208.2 i hi

/-- `(819,416)`: period `1`, cycle `[13]`, all bands deep (`≥ 5`). -/
private theorem elcCert_819_416 :
    slopeOrbit 819 416 (1 + 1) = slopeOrbit 819 416 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 819 416 j ≤ 819 := by
  have e0 : slopeOrbit 819 416 0 = 416 := rfl
  have e1 : slopeOrbit 819 416 1 = 13 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 819 416 2 = 13 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 819 416 2 = slopeOrbit 819 416 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(819,416)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_819_416 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 819)
    (hK : (class1SlopeDatum ctx).K₀ = 416) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_819_416.1) elcCert_819_416.2 i hi

/-- `(837,27)`: period `1`, cycle `[27]`, all bands deep (`≥ 5`). -/
private theorem elcCert_837_27 :
    slopeOrbit 837 27 (1 + 1) = slopeOrbit 837 27 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 837 27 j ≤ 837 := by
  have e0 : slopeOrbit 837 27 0 = 27 := rfl
  have e1 : slopeOrbit 837 27 1 = 27 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 837 27 2 = 27 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 837 27 2 = slopeOrbit 837 27 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(837,27)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_837_27 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 837)
    (hK : (class1SlopeDatum ctx).K₀ = 27) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_837_27.1) elcCert_837_27.2 i hi

/-- `(837,54)`: period `1`, cycle `[27]`, all bands deep (`≥ 5`). -/
private theorem elcCert_837_54 :
    slopeOrbit 837 54 (1 + 1) = slopeOrbit 837 54 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 837 54 j ≤ 837 := by
  have e0 : slopeOrbit 837 54 0 = 54 := rfl
  have e1 : slopeOrbit 837 54 1 = 27 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 837 54 2 = 27 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 837 54 2 = slopeOrbit 837 54 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(837,54)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_837_54 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 837)
    (hK : (class1SlopeDatum ctx).K₀ = 54) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_837_54.1) elcCert_837_54.2 i hi

/-- `(837,108)`: period `1`, cycle `[27]`, all bands deep (`≥ 5`). -/
private theorem elcCert_837_108 :
    slopeOrbit 837 108 (1 + 1) = slopeOrbit 837 108 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 837 108 j ≤ 837 := by
  have e0 : slopeOrbit 837 108 0 = 108 := rfl
  have e1 : slopeOrbit 837 108 1 = 27 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 837 108 2 = 27 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 837 108 2 = slopeOrbit 837 108 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(837,108)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_837_108 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 837)
    (hK : (class1SlopeDatum ctx).K₀ = 108) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_837_108.1) elcCert_837_108.2 i hi

/-- `(837,216)`: period `1`, cycle `[27]`, all bands deep (`≥ 5`). -/
private theorem elcCert_837_216 :
    slopeOrbit 837 216 (1 + 1) = slopeOrbit 837 216 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 837 216 j ≤ 837 := by
  have e0 : slopeOrbit 837 216 0 = 216 := rfl
  have e1 : slopeOrbit 837 216 1 = 27 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 837 216 2 = 27 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 837 216 2 = slopeOrbit 837 216 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(837,216)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_837_216 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 837)
    (hK : (class1SlopeDatum ctx).K₀ = 216) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_837_216.1) elcCert_837_216.2 i hi

/-- `(837,432)`: period `1`, cycle `[27]`, all bands deep (`≥ 5`). -/
private theorem elcCert_837_432 :
    slopeOrbit 837 432 (1 + 1) = slopeOrbit 837 432 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 837 432 j ≤ 837 := by
  have e0 : slopeOrbit 837 432 0 = 432 := rfl
  have e1 : slopeOrbit 837 432 1 = 27 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 837 432 2 = 27 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 837 432 2 = slopeOrbit 837 432 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(837,432)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_837_432 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 837)
    (hK : (class1SlopeDatum ctx).K₀ = 432) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_837_432.1) elcCert_837_432.2 i hi

/-- `(889,7)`: period `1`, cycle `[7]`, all bands deep (`≥ 5`). -/
private theorem elcCert_889_7 :
    slopeOrbit 889 7 (1 + 1) = slopeOrbit 889 7 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 889 7 j ≤ 889 := by
  have e0 : slopeOrbit 889 7 0 = 7 := rfl
  have e1 : slopeOrbit 889 7 1 = 7 :=
    slopeOrbit_step_eval 0 6 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 889 7 2 = 7 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 889 7 2 = slopeOrbit 889 7 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(889,7)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_889_7 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 889)
    (hK : (class1SlopeDatum ctx).K₀ = 7) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_889_7.1) elcCert_889_7.2 i hi

/-- `(889,14)`: period `1`, cycle `[7]`, all bands deep (`≥ 5`). -/
private theorem elcCert_889_14 :
    slopeOrbit 889 14 (1 + 1) = slopeOrbit 889 14 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 889 14 j ≤ 889 := by
  have e0 : slopeOrbit 889 14 0 = 14 := rfl
  have e1 : slopeOrbit 889 14 1 = 7 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 889 14 2 = 7 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 889 14 2 = slopeOrbit 889 14 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(889,14)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_889_14 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 889)
    (hK : (class1SlopeDatum ctx).K₀ = 14) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_889_14.1) elcCert_889_14.2 i hi

/-- `(889,28)`: period `1`, cycle `[7]`, all bands deep (`≥ 5`). -/
private theorem elcCert_889_28 :
    slopeOrbit 889 28 (1 + 1) = slopeOrbit 889 28 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 889 28 j ≤ 889 := by
  have e0 : slopeOrbit 889 28 0 = 28 := rfl
  have e1 : slopeOrbit 889 28 1 = 7 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 889 28 2 = 7 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 889 28 2 = slopeOrbit 889 28 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(889,28)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_889_28 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 889)
    (hK : (class1SlopeDatum ctx).K₀ = 28) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_889_28.1) elcCert_889_28.2 i hi

/-- `(889,56)`: period `1`, cycle `[7]`, all bands deep (`≥ 5`). -/
private theorem elcCert_889_56 :
    slopeOrbit 889 56 (1 + 1) = slopeOrbit 889 56 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 889 56 j ≤ 889 := by
  have e0 : slopeOrbit 889 56 0 = 56 := rfl
  have e1 : slopeOrbit 889 56 1 = 7 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 889 56 2 = 7 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 889 56 2 = slopeOrbit 889 56 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(889,56)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_889_56 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 889)
    (hK : (class1SlopeDatum ctx).K₀ = 56) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_889_56.1) elcCert_889_56.2 i hi

/-- `(889,112)`: period `1`, cycle `[7]`, all bands deep (`≥ 5`). -/
private theorem elcCert_889_112 :
    slopeOrbit 889 112 (1 + 1) = slopeOrbit 889 112 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 889 112 j ≤ 889 := by
  have e0 : slopeOrbit 889 112 0 = 112 := rfl
  have e1 : slopeOrbit 889 112 1 = 7 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 889 112 2 = 7 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 889 112 2 = slopeOrbit 889 112 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(889,112)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_889_112 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 889)
    (hK : (class1SlopeDatum ctx).K₀ = 112) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_889_112.1) elcCert_889_112.2 i hi

/-- `(889,224)`: period `1`, cycle `[7]`, all bands deep (`≥ 5`). -/
private theorem elcCert_889_224 :
    slopeOrbit 889 224 (1 + 1) = slopeOrbit 889 224 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 889 224 j ≤ 889 := by
  have e0 : slopeOrbit 889 224 0 = 224 := rfl
  have e1 : slopeOrbit 889 224 1 = 7 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 889 224 2 = 7 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 889 224 2 = slopeOrbit 889 224 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(889,224)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_889_224 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 889)
    (hK : (class1SlopeDatum ctx).K₀ = 224) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_889_224.1) elcCert_889_224.2 i hi

/-- `(889,448)`: period `1`, cycle `[7]`, all bands deep (`≥ 5`). -/
private theorem elcCert_889_448 :
    slopeOrbit 889 448 (1 + 1) = slopeOrbit 889 448 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 889 448 j ≤ 889 := by
  have e0 : slopeOrbit 889 448 0 = 448 := rfl
  have e1 : slopeOrbit 889 448 1 = 7 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 889 448 2 = 7 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 889 448 2 = slopeOrbit 889 448 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(889,448)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_889_448 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 889)
    (hK : (class1SlopeDatum ctx).K₀ = 448) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_889_448.1) elcCert_889_448.2 i hi

/-- `(899,29)`: period `1`, cycle `[29]`, all bands deep (`≥ 5`). -/
private theorem elcCert_899_29 :
    slopeOrbit 899 29 (1 + 1) = slopeOrbit 899 29 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 899 29 j ≤ 899 := by
  have e0 : slopeOrbit 899 29 0 = 29 := rfl
  have e1 : slopeOrbit 899 29 1 = 29 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 899 29 2 = 29 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 899 29 2 = slopeOrbit 899 29 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(899,29)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_899_29 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 899)
    (hK : (class1SlopeDatum ctx).K₀ = 29) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_899_29.1) elcCert_899_29.2 i hi

/-- `(899,58)`: period `1`, cycle `[29]`, all bands deep (`≥ 5`). -/
private theorem elcCert_899_58 :
    slopeOrbit 899 58 (1 + 1) = slopeOrbit 899 58 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 899 58 j ≤ 899 := by
  have e0 : slopeOrbit 899 58 0 = 58 := rfl
  have e1 : slopeOrbit 899 58 1 = 29 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 899 58 2 = 29 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 899 58 2 = slopeOrbit 899 58 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(899,58)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_899_58 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 899)
    (hK : (class1SlopeDatum ctx).K₀ = 58) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_899_58.1) elcCert_899_58.2 i hi

/-- `(899,116)`: period `1`, cycle `[29]`, all bands deep (`≥ 5`). -/
private theorem elcCert_899_116 :
    slopeOrbit 899 116 (1 + 1) = slopeOrbit 899 116 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 899 116 j ≤ 899 := by
  have e0 : slopeOrbit 899 116 0 = 116 := rfl
  have e1 : slopeOrbit 899 116 1 = 29 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 899 116 2 = 29 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 899 116 2 = slopeOrbit 899 116 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(899,116)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_899_116 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 899)
    (hK : (class1SlopeDatum ctx).K₀ = 116) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_899_116.1) elcCert_899_116.2 i hi

/-- `(899,232)`: period `1`, cycle `[29]`, all bands deep (`≥ 5`). -/
private theorem elcCert_899_232 :
    slopeOrbit 899 232 (1 + 1) = slopeOrbit 899 232 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 899 232 j ≤ 899 := by
  have e0 : slopeOrbit 899 232 0 = 232 := rfl
  have e1 : slopeOrbit 899 232 1 = 29 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 899 232 2 = 29 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 899 232 2 = slopeOrbit 899 232 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(899,232)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_899_232 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 899)
    (hK : (class1SlopeDatum ctx).K₀ = 232) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_899_232.1) elcCert_899_232.2 i hi

/-- `(899,464)`: period `1`, cycle `[29]`, all bands deep (`≥ 5`). -/
private theorem elcCert_899_464 :
    slopeOrbit 899 464 (1 + 1) = slopeOrbit 899 464 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 899 464 j ≤ 899 := by
  have e0 : slopeOrbit 899 464 0 = 464 := rfl
  have e1 : slopeOrbit 899 464 1 = 29 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 899 464 2 = 29 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 899 464 2 = slopeOrbit 899 464 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(899,464)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_899_464 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 899)
    (hK : (class1SlopeDatum ctx).K₀ = 464) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_899_464.1) elcCert_899_464.2 i hi

/-- `(945,15)`: period `1`, cycle `[15]`, all bands deep (`≥ 5`). -/
private theorem elcCert_945_15 :
    slopeOrbit 945 15 (1 + 1) = slopeOrbit 945 15 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 945 15 j ≤ 945 := by
  have e0 : slopeOrbit 945 15 0 = 15 := rfl
  have e1 : slopeOrbit 945 15 1 = 15 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 945 15 2 = 15 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 945 15 2 = slopeOrbit 945 15 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(945,15)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_945_15 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 945)
    (hK : (class1SlopeDatum ctx).K₀ = 15) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_945_15.1) elcCert_945_15.2 i hi

/-- `(945,30)`: period `1`, cycle `[15]`, all bands deep (`≥ 5`). -/
private theorem elcCert_945_30 :
    slopeOrbit 945 30 (1 + 1) = slopeOrbit 945 30 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 945 30 j ≤ 945 := by
  have e0 : slopeOrbit 945 30 0 = 30 := rfl
  have e1 : slopeOrbit 945 30 1 = 15 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 945 30 2 = 15 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 945 30 2 = slopeOrbit 945 30 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(945,30)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_945_30 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 945)
    (hK : (class1SlopeDatum ctx).K₀ = 30) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_945_30.1) elcCert_945_30.2 i hi

/-- `(945,60)`: period `1`, cycle `[15]`, all bands deep (`≥ 5`). -/
private theorem elcCert_945_60 :
    slopeOrbit 945 60 (1 + 1) = slopeOrbit 945 60 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 945 60 j ≤ 945 := by
  have e0 : slopeOrbit 945 60 0 = 60 := rfl
  have e1 : slopeOrbit 945 60 1 = 15 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 945 60 2 = 15 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 945 60 2 = slopeOrbit 945 60 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(945,60)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_945_60 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 945)
    (hK : (class1SlopeDatum ctx).K₀ = 60) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_945_60.1) elcCert_945_60.2 i hi

/-- `(945,120)`: period `1`, cycle `[15]`, all bands deep (`≥ 5`). -/
private theorem elcCert_945_120 :
    slopeOrbit 945 120 (1 + 1) = slopeOrbit 945 120 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 945 120 j ≤ 945 := by
  have e0 : slopeOrbit 945 120 0 = 120 := rfl
  have e1 : slopeOrbit 945 120 1 = 15 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 945 120 2 = 15 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 945 120 2 = slopeOrbit 945 120 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(945,120)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_945_120 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 945)
    (hK : (class1SlopeDatum ctx).K₀ = 120) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_945_120.1) elcCert_945_120.2 i hi

/-- `(945,240)`: period `1`, cycle `[15]`, all bands deep (`≥ 5`). -/
private theorem elcCert_945_240 :
    slopeOrbit 945 240 (1 + 1) = slopeOrbit 945 240 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 945 240 j ≤ 945 := by
  have e0 : slopeOrbit 945 240 0 = 240 := rfl
  have e1 : slopeOrbit 945 240 1 = 15 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 945 240 2 = 15 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 945 240 2 = slopeOrbit 945 240 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(945,240)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_945_240 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 945)
    (hK : (class1SlopeDatum ctx).K₀ = 240) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_945_240.1) elcCert_945_240.2 i hi

/-- `(945,480)`: period `1`, cycle `[15]`, all bands deep (`≥ 5`). -/
private theorem elcCert_945_480 :
    slopeOrbit 945 480 (1 + 1) = slopeOrbit 945 480 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 945 480 j ≤ 945 := by
  have e0 : slopeOrbit 945 480 0 = 480 := rfl
  have e1 : slopeOrbit 945 480 1 = 15 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 945 480 2 = 15 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 945 480 2 = slopeOrbit 945 480 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(945,480)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_945_480 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 945)
    (hK : (class1SlopeDatum ctx).K₀ = 480) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_945_480.1) elcCert_945_480.2 i hi

/-- `(961,31)`: period `1`, cycle `[31]`, all bands deep (`≥ 5`). -/
private theorem elcCert_961_31 :
    slopeOrbit 961 31 (1 + 1) = slopeOrbit 961 31 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 961 31 j ≤ 961 := by
  have e0 : slopeOrbit 961 31 0 = 31 := rfl
  have e1 : slopeOrbit 961 31 1 = 31 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 961 31 2 = 31 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 961 31 2 = slopeOrbit 961 31 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(961,31)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_961_31 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 961)
    (hK : (class1SlopeDatum ctx).K₀ = 31) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_961_31.1) elcCert_961_31.2 i hi

/-- `(961,62)`: period `1`, cycle `[31]`, all bands deep (`≥ 5`). -/
private theorem elcCert_961_62 :
    slopeOrbit 961 62 (1 + 1) = slopeOrbit 961 62 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 961 62 j ≤ 961 := by
  have e0 : slopeOrbit 961 62 0 = 62 := rfl
  have e1 : slopeOrbit 961 62 1 = 31 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 961 62 2 = 31 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 961 62 2 = slopeOrbit 961 62 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(961,62)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_961_62 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 961)
    (hK : (class1SlopeDatum ctx).K₀ = 62) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_961_62.1) elcCert_961_62.2 i hi

/-- `(961,124)`: period `1`, cycle `[31]`, all bands deep (`≥ 5`). -/
private theorem elcCert_961_124 :
    slopeOrbit 961 124 (1 + 1) = slopeOrbit 961 124 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 961 124 j ≤ 961 := by
  have e0 : slopeOrbit 961 124 0 = 124 := rfl
  have e1 : slopeOrbit 961 124 1 = 31 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 961 124 2 = 31 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 961 124 2 = slopeOrbit 961 124 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(961,124)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_961_124 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 961)
    (hK : (class1SlopeDatum ctx).K₀ = 124) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_961_124.1) elcCert_961_124.2 i hi

/-- `(961,248)`: period `1`, cycle `[31]`, all bands deep (`≥ 5`). -/
private theorem elcCert_961_248 :
    slopeOrbit 961 248 (1 + 1) = slopeOrbit 961 248 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 961 248 j ≤ 961 := by
  have e0 : slopeOrbit 961 248 0 = 248 := rfl
  have e1 : slopeOrbit 961 248 1 = 31 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 961 248 2 = 31 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 961 248 2 = slopeOrbit 961 248 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(961,248)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_961_248 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 961)
    (hK : (class1SlopeDatum ctx).K₀ = 248) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_961_248.1) elcCert_961_248.2 i hi

/-- `(961,496)`: period `1`, cycle `[31]`, all bands deep (`≥ 5`). -/
private theorem elcCert_961_496 :
    slopeOrbit 961 496 (1 + 1) = slopeOrbit 961 496 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 961 496 j ≤ 961 := by
  have e0 : slopeOrbit 961 496 0 = 496 := rfl
  have e1 : slopeOrbit 961 496 1 = 31 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 961 496 2 = 31 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 961 496 2 = slopeOrbit 961 496 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(961,496)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_961_496 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 961)
    (hK : (class1SlopeDatum ctx).K₀ = 496) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_961_496.1) elcCert_961_496.2 i hi

/-- `(1023,1)`: period `1`, cycle `[1]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1023_1 :
    slopeOrbit 1023 1 (1 + 1) = slopeOrbit 1023 1 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1023 1 j ≤ 1023 := by
  have e0 : slopeOrbit 1023 1 0 = 1 := rfl
  have e1 : slopeOrbit 1023 1 1 = 1 :=
    slopeOrbit_step_eval 0 9 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1023 1 2 = 1 :=
    slopeOrbit_step_eval 1 9 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1023 1 2 = slopeOrbit 1023 1 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1023,1)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1023_1 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1023)
    (hK : (class1SlopeDatum ctx).K₀ = 1) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1023_1.1) elcCert_1023_1.2 i hi

/-- `(1023,2)`: period `1`, cycle `[1]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1023_2 :
    slopeOrbit 1023 2 (1 + 1) = slopeOrbit 1023 2 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1023 2 j ≤ 1023 := by
  have e0 : slopeOrbit 1023 2 0 = 2 := rfl
  have e1 : slopeOrbit 1023 2 1 = 1 :=
    slopeOrbit_step_eval 0 8 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1023 2 2 = 1 :=
    slopeOrbit_step_eval 1 9 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1023 2 2 = slopeOrbit 1023 2 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1023,2)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1023_2 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1023)
    (hK : (class1SlopeDatum ctx).K₀ = 2) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1023_2.1) elcCert_1023_2.2 i hi

/-- `(1023,4)`: period `1`, cycle `[1]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1023_4 :
    slopeOrbit 1023 4 (1 + 1) = slopeOrbit 1023 4 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1023 4 j ≤ 1023 := by
  have e0 : slopeOrbit 1023 4 0 = 4 := rfl
  have e1 : slopeOrbit 1023 4 1 = 1 :=
    slopeOrbit_step_eval 0 7 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1023 4 2 = 1 :=
    slopeOrbit_step_eval 1 9 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1023 4 2 = slopeOrbit 1023 4 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1023,4)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1023_4 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1023)
    (hK : (class1SlopeDatum ctx).K₀ = 4) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1023_4.1) elcCert_1023_4.2 i hi

/-- `(1023,8)`: period `1`, cycle `[1]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1023_8 :
    slopeOrbit 1023 8 (1 + 1) = slopeOrbit 1023 8 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1023 8 j ≤ 1023 := by
  have e0 : slopeOrbit 1023 8 0 = 8 := rfl
  have e1 : slopeOrbit 1023 8 1 = 1 :=
    slopeOrbit_step_eval 0 6 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1023 8 2 = 1 :=
    slopeOrbit_step_eval 1 9 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1023 8 2 = slopeOrbit 1023 8 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1023,8)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1023_8 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1023)
    (hK : (class1SlopeDatum ctx).K₀ = 8) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1023_8.1) elcCert_1023_8.2 i hi

/-- `(1023,16)`: period `1`, cycle `[1]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1023_16 :
    slopeOrbit 1023 16 (1 + 1) = slopeOrbit 1023 16 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1023 16 j ≤ 1023 := by
  have e0 : slopeOrbit 1023 16 0 = 16 := rfl
  have e1 : slopeOrbit 1023 16 1 = 1 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1023 16 2 = 1 :=
    slopeOrbit_step_eval 1 9 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1023 16 2 = slopeOrbit 1023 16 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1023,16)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1023_16 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1023)
    (hK : (class1SlopeDatum ctx).K₀ = 16) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1023_16.1) elcCert_1023_16.2 i hi

/-- `(1023,32)`: period `1`, cycle `[1]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1023_32 :
    slopeOrbit 1023 32 (1 + 1) = slopeOrbit 1023 32 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1023 32 j ≤ 1023 := by
  have e0 : slopeOrbit 1023 32 0 = 32 := rfl
  have e1 : slopeOrbit 1023 32 1 = 1 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1023 32 2 = 1 :=
    slopeOrbit_step_eval 1 9 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1023 32 2 = slopeOrbit 1023 32 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1023,32)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1023_32 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1023)
    (hK : (class1SlopeDatum ctx).K₀ = 32) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1023_32.1) elcCert_1023_32.2 i hi

/-- `(1023,33)`: period `1`, cycle `[33]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1023_33 :
    slopeOrbit 1023 33 (1 + 1) = slopeOrbit 1023 33 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1023 33 j ≤ 1023 := by
  have e0 : slopeOrbit 1023 33 0 = 33 := rfl
  have e1 : slopeOrbit 1023 33 1 = 33 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1023 33 2 = 33 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1023 33 2 = slopeOrbit 1023 33 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1023,33)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1023_33 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1023)
    (hK : (class1SlopeDatum ctx).K₀ = 33) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1023_33.1) elcCert_1023_33.2 i hi

/-- `(1023,64)`: period `1`, cycle `[1]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1023_64 :
    slopeOrbit 1023 64 (1 + 1) = slopeOrbit 1023 64 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1023 64 j ≤ 1023 := by
  have e0 : slopeOrbit 1023 64 0 = 64 := rfl
  have e1 : slopeOrbit 1023 64 1 = 1 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1023 64 2 = 1 :=
    slopeOrbit_step_eval 1 9 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1023 64 2 = slopeOrbit 1023 64 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1023,64)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1023_64 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1023)
    (hK : (class1SlopeDatum ctx).K₀ = 64) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1023_64.1) elcCert_1023_64.2 i hi

/-- `(1023,66)`: period `1`, cycle `[33]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1023_66 :
    slopeOrbit 1023 66 (1 + 1) = slopeOrbit 1023 66 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1023 66 j ≤ 1023 := by
  have e0 : slopeOrbit 1023 66 0 = 66 := rfl
  have e1 : slopeOrbit 1023 66 1 = 33 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1023 66 2 = 33 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1023 66 2 = slopeOrbit 1023 66 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1023,66)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1023_66 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1023)
    (hK : (class1SlopeDatum ctx).K₀ = 66) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1023_66.1) elcCert_1023_66.2 i hi

/-- `(1023,128)`: period `1`, cycle `[1]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1023_128 :
    slopeOrbit 1023 128 (1 + 1) = slopeOrbit 1023 128 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1023 128 j ≤ 1023 := by
  have e0 : slopeOrbit 1023 128 0 = 128 := rfl
  have e1 : slopeOrbit 1023 128 1 = 1 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1023 128 2 = 1 :=
    slopeOrbit_step_eval 1 9 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1023 128 2 = slopeOrbit 1023 128 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1023,128)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1023_128 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1023)
    (hK : (class1SlopeDatum ctx).K₀ = 128) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1023_128.1) elcCert_1023_128.2 i hi

/-- `(1023,132)`: period `1`, cycle `[33]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1023_132 :
    slopeOrbit 1023 132 (1 + 1) = slopeOrbit 1023 132 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1023 132 j ≤ 1023 := by
  have e0 : slopeOrbit 1023 132 0 = 132 := rfl
  have e1 : slopeOrbit 1023 132 1 = 33 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1023 132 2 = 33 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1023 132 2 = slopeOrbit 1023 132 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1023,132)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1023_132 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1023)
    (hK : (class1SlopeDatum ctx).K₀ = 132) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1023_132.1) elcCert_1023_132.2 i hi

/-- `(1023,256)`: period `1`, cycle `[1]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1023_256 :
    slopeOrbit 1023 256 (1 + 1) = slopeOrbit 1023 256 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1023 256 j ≤ 1023 := by
  have e0 : slopeOrbit 1023 256 0 = 256 := rfl
  have e1 : slopeOrbit 1023 256 1 = 1 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1023 256 2 = 1 :=
    slopeOrbit_step_eval 1 9 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1023 256 2 = slopeOrbit 1023 256 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1023,256)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1023_256 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1023)
    (hK : (class1SlopeDatum ctx).K₀ = 256) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1023_256.1) elcCert_1023_256.2 i hi

/-- `(1023,264)`: period `1`, cycle `[33]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1023_264 :
    slopeOrbit 1023 264 (1 + 1) = slopeOrbit 1023 264 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1023 264 j ≤ 1023 := by
  have e0 : slopeOrbit 1023 264 0 = 264 := rfl
  have e1 : slopeOrbit 1023 264 1 = 33 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1023 264 2 = 33 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1023 264 2 = slopeOrbit 1023 264 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1023,264)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1023_264 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1023)
    (hK : (class1SlopeDatum ctx).K₀ = 264) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1023_264.1) elcCert_1023_264.2 i hi

/-- `(1023,512)`: period `1`, cycle `[1]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1023_512 :
    slopeOrbit 1023 512 (1 + 1) = slopeOrbit 1023 512 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1023 512 j ≤ 1023 := by
  have e0 : slopeOrbit 1023 512 0 = 512 := rfl
  have e1 : slopeOrbit 1023 512 1 = 1 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1023 512 2 = 1 :=
    slopeOrbit_step_eval 1 9 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1023 512 2 = slopeOrbit 1023 512 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1023,512)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1023_512 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1023)
    (hK : (class1SlopeDatum ctx).K₀ = 512) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1023_512.1) elcCert_1023_512.2 i hi

/-- `(1023,528)`: period `1`, cycle `[33]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1023_528 :
    slopeOrbit 1023 528 (1 + 1) = slopeOrbit 1023 528 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1023 528 j ≤ 1023 := by
  have e0 : slopeOrbit 1023 528 0 = 528 := rfl
  have e1 : slopeOrbit 1023 528 1 = 33 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1023 528 2 = 33 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1023 528 2 = slopeOrbit 1023 528 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1023,528)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1023_528 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1023)
    (hK : (class1SlopeDatum ctx).K₀ = 528) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1023_528.1) elcCert_1023_528.2 i hi

/-- `(1071,17)`: period `1`, cycle `[17]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1071_17 :
    slopeOrbit 1071 17 (1 + 1) = slopeOrbit 1071 17 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1071 17 j ≤ 1071 := by
  have e0 : slopeOrbit 1071 17 0 = 17 := rfl
  have e1 : slopeOrbit 1071 17 1 = 17 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1071 17 2 = 17 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1071 17 2 = slopeOrbit 1071 17 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1071,17)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1071_17 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1071)
    (hK : (class1SlopeDatum ctx).K₀ = 17) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1071_17.1) elcCert_1071_17.2 i hi

/-- `(1071,34)`: period `1`, cycle `[17]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1071_34 :
    slopeOrbit 1071 34 (1 + 1) = slopeOrbit 1071 34 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1071 34 j ≤ 1071 := by
  have e0 : slopeOrbit 1071 34 0 = 34 := rfl
  have e1 : slopeOrbit 1071 34 1 = 17 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1071 34 2 = 17 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1071 34 2 = slopeOrbit 1071 34 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1071,34)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1071_34 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1071)
    (hK : (class1SlopeDatum ctx).K₀ = 34) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1071_34.1) elcCert_1071_34.2 i hi

/-- `(1071,68)`: period `1`, cycle `[17]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1071_68 :
    slopeOrbit 1071 68 (1 + 1) = slopeOrbit 1071 68 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1071 68 j ≤ 1071 := by
  have e0 : slopeOrbit 1071 68 0 = 68 := rfl
  have e1 : slopeOrbit 1071 68 1 = 17 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1071 68 2 = 17 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1071 68 2 = slopeOrbit 1071 68 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1071,68)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1071_68 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1071)
    (hK : (class1SlopeDatum ctx).K₀ = 68) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1071_68.1) elcCert_1071_68.2 i hi

/-- `(1071,136)`: period `1`, cycle `[17]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1071_136 :
    slopeOrbit 1071 136 (1 + 1) = slopeOrbit 1071 136 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1071 136 j ≤ 1071 := by
  have e0 : slopeOrbit 1071 136 0 = 136 := rfl
  have e1 : slopeOrbit 1071 136 1 = 17 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1071 136 2 = 17 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1071 136 2 = slopeOrbit 1071 136 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1071,136)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1071_136 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1071)
    (hK : (class1SlopeDatum ctx).K₀ = 136) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1071_136.1) elcCert_1071_136.2 i hi

/-- `(1071,272)`: period `1`, cycle `[17]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1071_272 :
    slopeOrbit 1071 272 (1 + 1) = slopeOrbit 1071 272 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1071 272 j ≤ 1071 := by
  have e0 : slopeOrbit 1071 272 0 = 272 := rfl
  have e1 : slopeOrbit 1071 272 1 = 17 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1071 272 2 = 17 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1071 272 2 = slopeOrbit 1071 272 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1071,272)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1071_272 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1071)
    (hK : (class1SlopeDatum ctx).K₀ = 272) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1071_272.1) elcCert_1071_272.2 i hi

/-- `(1071,544)`: period `1`, cycle `[17]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1071_544 :
    slopeOrbit 1071 544 (1 + 1) = slopeOrbit 1071 544 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1071 544 j ≤ 1071 := by
  have e0 : slopeOrbit 1071 544 0 = 544 := rfl
  have e1 : slopeOrbit 1071 544 1 = 17 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1071 544 2 = 17 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1071 544 2 = slopeOrbit 1071 544 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1071,544)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1071_544 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1071)
    (hK : (class1SlopeDatum ctx).K₀ = 544) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1071_544.1) elcCert_1071_544.2 i hi

/-- `(1085,35)`: period `1`, cycle `[35]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1085_35 :
    slopeOrbit 1085 35 (1 + 1) = slopeOrbit 1085 35 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1085 35 j ≤ 1085 := by
  have e0 : slopeOrbit 1085 35 0 = 35 := rfl
  have e1 : slopeOrbit 1085 35 1 = 35 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1085 35 2 = 35 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1085 35 2 = slopeOrbit 1085 35 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1085,35)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1085_35 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1085)
    (hK : (class1SlopeDatum ctx).K₀ = 35) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1085_35.1) elcCert_1085_35.2 i hi

/-- `(1085,70)`: period `1`, cycle `[35]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1085_70 :
    slopeOrbit 1085 70 (1 + 1) = slopeOrbit 1085 70 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1085 70 j ≤ 1085 := by
  have e0 : slopeOrbit 1085 70 0 = 70 := rfl
  have e1 : slopeOrbit 1085 70 1 = 35 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1085 70 2 = 35 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1085 70 2 = slopeOrbit 1085 70 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1085,70)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1085_70 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1085)
    (hK : (class1SlopeDatum ctx).K₀ = 70) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1085_70.1) elcCert_1085_70.2 i hi

/-- `(1085,140)`: period `1`, cycle `[35]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1085_140 :
    slopeOrbit 1085 140 (1 + 1) = slopeOrbit 1085 140 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1085 140 j ≤ 1085 := by
  have e0 : slopeOrbit 1085 140 0 = 140 := rfl
  have e1 : slopeOrbit 1085 140 1 = 35 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1085 140 2 = 35 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1085 140 2 = slopeOrbit 1085 140 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1085,140)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1085_140 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1085)
    (hK : (class1SlopeDatum ctx).K₀ = 140) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1085_140.1) elcCert_1085_140.2 i hi

/-- `(1085,280)`: period `1`, cycle `[35]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1085_280 :
    slopeOrbit 1085 280 (1 + 1) = slopeOrbit 1085 280 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1085 280 j ≤ 1085 := by
  have e0 : slopeOrbit 1085 280 0 = 280 := rfl
  have e1 : slopeOrbit 1085 280 1 = 35 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1085 280 2 = 35 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1085 280 2 = slopeOrbit 1085 280 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1085,280)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1085_280 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1085)
    (hK : (class1SlopeDatum ctx).K₀ = 280) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1085_280.1) elcCert_1085_280.2 i hi

/-- `(1085,560)`: period `1`, cycle `[35]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1085_560 :
    slopeOrbit 1085 560 (1 + 1) = slopeOrbit 1085 560 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1085 560 j ≤ 1085 := by
  have e0 : slopeOrbit 1085 560 0 = 560 := rfl
  have e1 : slopeOrbit 1085 560 1 = 35 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1085 560 2 = 35 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1085 560 2 = slopeOrbit 1085 560 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1085,560)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1085_560 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1085)
    (hK : (class1SlopeDatum ctx).K₀ = 560) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1085_560.1) elcCert_1085_560.2 i hi

/-- `(1143,9)`: period `1`, cycle `[9]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1143_9 :
    slopeOrbit 1143 9 (1 + 1) = slopeOrbit 1143 9 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1143 9 j ≤ 1143 := by
  have e0 : slopeOrbit 1143 9 0 = 9 := rfl
  have e1 : slopeOrbit 1143 9 1 = 9 :=
    slopeOrbit_step_eval 0 6 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1143 9 2 = 9 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1143 9 2 = slopeOrbit 1143 9 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1143,9)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1143_9 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1143)
    (hK : (class1SlopeDatum ctx).K₀ = 9) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1143_9.1) elcCert_1143_9.2 i hi

/-- `(1143,18)`: period `1`, cycle `[9]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1143_18 :
    slopeOrbit 1143 18 (1 + 1) = slopeOrbit 1143 18 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1143 18 j ≤ 1143 := by
  have e0 : slopeOrbit 1143 18 0 = 18 := rfl
  have e1 : slopeOrbit 1143 18 1 = 9 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1143 18 2 = 9 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1143 18 2 = slopeOrbit 1143 18 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1143,18)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1143_18 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1143)
    (hK : (class1SlopeDatum ctx).K₀ = 18) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1143_18.1) elcCert_1143_18.2 i hi

/-- `(1143,36)`: period `1`, cycle `[9]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1143_36 :
    slopeOrbit 1143 36 (1 + 1) = slopeOrbit 1143 36 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1143 36 j ≤ 1143 := by
  have e0 : slopeOrbit 1143 36 0 = 36 := rfl
  have e1 : slopeOrbit 1143 36 1 = 9 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1143 36 2 = 9 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1143 36 2 = slopeOrbit 1143 36 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1143,36)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1143_36 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1143)
    (hK : (class1SlopeDatum ctx).K₀ = 36) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1143_36.1) elcCert_1143_36.2 i hi

/-- `(1143,72)`: period `1`, cycle `[9]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1143_72 :
    slopeOrbit 1143 72 (1 + 1) = slopeOrbit 1143 72 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1143 72 j ≤ 1143 := by
  have e0 : slopeOrbit 1143 72 0 = 72 := rfl
  have e1 : slopeOrbit 1143 72 1 = 9 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1143 72 2 = 9 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1143 72 2 = slopeOrbit 1143 72 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1143,72)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1143_72 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1143)
    (hK : (class1SlopeDatum ctx).K₀ = 72) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1143_72.1) elcCert_1143_72.2 i hi

/-- `(1143,144)`: period `1`, cycle `[9]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1143_144 :
    slopeOrbit 1143 144 (1 + 1) = slopeOrbit 1143 144 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1143 144 j ≤ 1143 := by
  have e0 : slopeOrbit 1143 144 0 = 144 := rfl
  have e1 : slopeOrbit 1143 144 1 = 9 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1143 144 2 = 9 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1143 144 2 = slopeOrbit 1143 144 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1143,144)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1143_144 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1143)
    (hK : (class1SlopeDatum ctx).K₀ = 144) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1143_144.1) elcCert_1143_144.2 i hi

/-- `(1143,288)`: period `1`, cycle `[9]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1143_288 :
    slopeOrbit 1143 288 (1 + 1) = slopeOrbit 1143 288 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1143 288 j ≤ 1143 := by
  have e0 : slopeOrbit 1143 288 0 = 288 := rfl
  have e1 : slopeOrbit 1143 288 1 = 9 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1143 288 2 = 9 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1143 288 2 = slopeOrbit 1143 288 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1143,288)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1143_288 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1143)
    (hK : (class1SlopeDatum ctx).K₀ = 288) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1143_288.1) elcCert_1143_288.2 i hi

/-- `(1143,576)`: period `1`, cycle `[9]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1143_576 :
    slopeOrbit 1143 576 (1 + 1) = slopeOrbit 1143 576 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1143 576 j ≤ 1143 := by
  have e0 : slopeOrbit 1143 576 0 = 576 := rfl
  have e1 : slopeOrbit 1143 576 1 = 9 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1143 576 2 = 9 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1143 576 2 = slopeOrbit 1143 576 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1143,576)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1143_576 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1143)
    (hK : (class1SlopeDatum ctx).K₀ = 576) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1143_576.1) elcCert_1143_576.2 i hi

/-- `(1147,37)`: period `1`, cycle `[37]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1147_37 :
    slopeOrbit 1147 37 (1 + 1) = slopeOrbit 1147 37 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1147 37 j ≤ 1147 := by
  have e0 : slopeOrbit 1147 37 0 = 37 := rfl
  have e1 : slopeOrbit 1147 37 1 = 37 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1147 37 2 = 37 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1147 37 2 = slopeOrbit 1147 37 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1147,37)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1147_37 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1147)
    (hK : (class1SlopeDatum ctx).K₀ = 37) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1147_37.1) elcCert_1147_37.2 i hi

/-- `(1147,74)`: period `1`, cycle `[37]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1147_74 :
    slopeOrbit 1147 74 (1 + 1) = slopeOrbit 1147 74 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1147 74 j ≤ 1147 := by
  have e0 : slopeOrbit 1147 74 0 = 74 := rfl
  have e1 : slopeOrbit 1147 74 1 = 37 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1147 74 2 = 37 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1147 74 2 = slopeOrbit 1147 74 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1147,74)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1147_74 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1147)
    (hK : (class1SlopeDatum ctx).K₀ = 74) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1147_74.1) elcCert_1147_74.2 i hi

/-- `(1147,148)`: period `1`, cycle `[37]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1147_148 :
    slopeOrbit 1147 148 (1 + 1) = slopeOrbit 1147 148 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1147 148 j ≤ 1147 := by
  have e0 : slopeOrbit 1147 148 0 = 148 := rfl
  have e1 : slopeOrbit 1147 148 1 = 37 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1147 148 2 = 37 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1147 148 2 = slopeOrbit 1147 148 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1147,148)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1147_148 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1147)
    (hK : (class1SlopeDatum ctx).K₀ = 148) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1147_148.1) elcCert_1147_148.2 i hi

/-- `(1147,296)`: period `1`, cycle `[37]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1147_296 :
    slopeOrbit 1147 296 (1 + 1) = slopeOrbit 1147 296 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1147 296 j ≤ 1147 := by
  have e0 : slopeOrbit 1147 296 0 = 296 := rfl
  have e1 : slopeOrbit 1147 296 1 = 37 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1147 296 2 = 37 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1147 296 2 = slopeOrbit 1147 296 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1147,296)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1147_296 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1147)
    (hK : (class1SlopeDatum ctx).K₀ = 296) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1147_296.1) elcCert_1147_296.2 i hi

/-- `(1147,592)`: period `1`, cycle `[37]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1147_592 :
    slopeOrbit 1147 592 (1 + 1) = slopeOrbit 1147 592 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1147 592 j ≤ 1147 := by
  have e0 : slopeOrbit 1147 592 0 = 592 := rfl
  have e1 : slopeOrbit 1147 592 1 = 37 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1147 592 2 = 37 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1147 592 2 = slopeOrbit 1147 592 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1147,592)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1147_592 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1147)
    (hK : (class1SlopeDatum ctx).K₀ = 592) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1147_592.1) elcCert_1147_592.2 i hi

/-- `(1197,19)`: period `1`, cycle `[19]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1197_19 :
    slopeOrbit 1197 19 (1 + 1) = slopeOrbit 1197 19 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1197 19 j ≤ 1197 := by
  have e0 : slopeOrbit 1197 19 0 = 19 := rfl
  have e1 : slopeOrbit 1197 19 1 = 19 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1197 19 2 = 19 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1197 19 2 = slopeOrbit 1197 19 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1197,19)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1197_19 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1197)
    (hK : (class1SlopeDatum ctx).K₀ = 19) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1197_19.1) elcCert_1197_19.2 i hi

/-- `(1197,38)`: period `1`, cycle `[19]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1197_38 :
    slopeOrbit 1197 38 (1 + 1) = slopeOrbit 1197 38 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1197 38 j ≤ 1197 := by
  have e0 : slopeOrbit 1197 38 0 = 38 := rfl
  have e1 : slopeOrbit 1197 38 1 = 19 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1197 38 2 = 19 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1197 38 2 = slopeOrbit 1197 38 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1197,38)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1197_38 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1197)
    (hK : (class1SlopeDatum ctx).K₀ = 38) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1197_38.1) elcCert_1197_38.2 i hi

/-- `(1197,76)`: period `1`, cycle `[19]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1197_76 :
    slopeOrbit 1197 76 (1 + 1) = slopeOrbit 1197 76 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1197 76 j ≤ 1197 := by
  have e0 : slopeOrbit 1197 76 0 = 76 := rfl
  have e1 : slopeOrbit 1197 76 1 = 19 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1197 76 2 = 19 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1197 76 2 = slopeOrbit 1197 76 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1197,76)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1197_76 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1197)
    (hK : (class1SlopeDatum ctx).K₀ = 76) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1197_76.1) elcCert_1197_76.2 i hi

/-- `(1197,152)`: period `1`, cycle `[19]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1197_152 :
    slopeOrbit 1197 152 (1 + 1) = slopeOrbit 1197 152 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1197 152 j ≤ 1197 := by
  have e0 : slopeOrbit 1197 152 0 = 152 := rfl
  have e1 : slopeOrbit 1197 152 1 = 19 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1197 152 2 = 19 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1197 152 2 = slopeOrbit 1197 152 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1197,152)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1197_152 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1197)
    (hK : (class1SlopeDatum ctx).K₀ = 152) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1197_152.1) elcCert_1197_152.2 i hi

/-- `(1197,304)`: period `1`, cycle `[19]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1197_304 :
    slopeOrbit 1197 304 (1 + 1) = slopeOrbit 1197 304 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1197 304 j ≤ 1197 := by
  have e0 : slopeOrbit 1197 304 0 = 304 := rfl
  have e1 : slopeOrbit 1197 304 1 = 19 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1197 304 2 = 19 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1197 304 2 = slopeOrbit 1197 304 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1197,304)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1197_304 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1197)
    (hK : (class1SlopeDatum ctx).K₀ = 304) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1197_304.1) elcCert_1197_304.2 i hi

/-- `(1197,608)`: period `1`, cycle `[19]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1197_608 :
    slopeOrbit 1197 608 (1 + 1) = slopeOrbit 1197 608 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1197 608 j ≤ 1197 := by
  have e0 : slopeOrbit 1197 608 0 = 608 := rfl
  have e1 : slopeOrbit 1197 608 1 = 19 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1197 608 2 = 19 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1197 608 2 = slopeOrbit 1197 608 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1197,608)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1197_608 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1197)
    (hK : (class1SlopeDatum ctx).K₀ = 608) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1197_608.1) elcCert_1197_608.2 i hi

/-- `(1209,39)`: period `1`, cycle `[39]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1209_39 :
    slopeOrbit 1209 39 (1 + 1) = slopeOrbit 1209 39 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1209 39 j ≤ 1209 := by
  have e0 : slopeOrbit 1209 39 0 = 39 := rfl
  have e1 : slopeOrbit 1209 39 1 = 39 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1209 39 2 = 39 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1209 39 2 = slopeOrbit 1209 39 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1209,39)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1209_39 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1209)
    (hK : (class1SlopeDatum ctx).K₀ = 39) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1209_39.1) elcCert_1209_39.2 i hi

/-- `(1209,78)`: period `1`, cycle `[39]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1209_78 :
    slopeOrbit 1209 78 (1 + 1) = slopeOrbit 1209 78 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1209 78 j ≤ 1209 := by
  have e0 : slopeOrbit 1209 78 0 = 78 := rfl
  have e1 : slopeOrbit 1209 78 1 = 39 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1209 78 2 = 39 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1209 78 2 = slopeOrbit 1209 78 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1209,78)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1209_78 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1209)
    (hK : (class1SlopeDatum ctx).K₀ = 78) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1209_78.1) elcCert_1209_78.2 i hi

/-- `(1209,156)`: period `1`, cycle `[39]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1209_156 :
    slopeOrbit 1209 156 (1 + 1) = slopeOrbit 1209 156 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1209 156 j ≤ 1209 := by
  have e0 : slopeOrbit 1209 156 0 = 156 := rfl
  have e1 : slopeOrbit 1209 156 1 = 39 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1209 156 2 = 39 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1209 156 2 = slopeOrbit 1209 156 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1209,156)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1209_156 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1209)
    (hK : (class1SlopeDatum ctx).K₀ = 156) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1209_156.1) elcCert_1209_156.2 i hi

/-- `(1209,312)`: period `1`, cycle `[39]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1209_312 :
    slopeOrbit 1209 312 (1 + 1) = slopeOrbit 1209 312 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1209 312 j ≤ 1209 := by
  have e0 : slopeOrbit 1209 312 0 = 312 := rfl
  have e1 : slopeOrbit 1209 312 1 = 39 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1209 312 2 = 39 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1209 312 2 = slopeOrbit 1209 312 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1209,312)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1209_312 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1209)
    (hK : (class1SlopeDatum ctx).K₀ = 312) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1209_312.1) elcCert_1209_312.2 i hi

/-- `(1209,624)`: period `1`, cycle `[39]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1209_624 :
    slopeOrbit 1209 624 (1 + 1) = slopeOrbit 1209 624 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1209 624 j ≤ 1209 := by
  have e0 : slopeOrbit 1209 624 0 = 624 := rfl
  have e1 : slopeOrbit 1209 624 1 = 39 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1209 624 2 = 39 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1209 624 2 = slopeOrbit 1209 624 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1209,624)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1209_624 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1209)
    (hK : (class1SlopeDatum ctx).K₀ = 624) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1209_624.1) elcCert_1209_624.2 i hi

/-- `(1271,41)`: period `1`, cycle `[41]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1271_41 :
    slopeOrbit 1271 41 (1 + 1) = slopeOrbit 1271 41 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1271 41 j ≤ 1271 := by
  have e0 : slopeOrbit 1271 41 0 = 41 := rfl
  have e1 : slopeOrbit 1271 41 1 = 41 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1271 41 2 = 41 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1271 41 2 = slopeOrbit 1271 41 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1271,41)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1271_41 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1271)
    (hK : (class1SlopeDatum ctx).K₀ = 41) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1271_41.1) elcCert_1271_41.2 i hi

/-- `(1271,82)`: period `1`, cycle `[41]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1271_82 :
    slopeOrbit 1271 82 (1 + 1) = slopeOrbit 1271 82 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1271 82 j ≤ 1271 := by
  have e0 : slopeOrbit 1271 82 0 = 82 := rfl
  have e1 : slopeOrbit 1271 82 1 = 41 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1271 82 2 = 41 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1271 82 2 = slopeOrbit 1271 82 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1271,82)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1271_82 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1271)
    (hK : (class1SlopeDatum ctx).K₀ = 82) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1271_82.1) elcCert_1271_82.2 i hi

/-- `(1271,164)`: period `1`, cycle `[41]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1271_164 :
    slopeOrbit 1271 164 (1 + 1) = slopeOrbit 1271 164 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1271 164 j ≤ 1271 := by
  have e0 : slopeOrbit 1271 164 0 = 164 := rfl
  have e1 : slopeOrbit 1271 164 1 = 41 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1271 164 2 = 41 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1271 164 2 = slopeOrbit 1271 164 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1271,164)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1271_164 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1271)
    (hK : (class1SlopeDatum ctx).K₀ = 164) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1271_164.1) elcCert_1271_164.2 i hi

/-- `(1271,328)`: period `1`, cycle `[41]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1271_328 :
    slopeOrbit 1271 328 (1 + 1) = slopeOrbit 1271 328 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1271 328 j ≤ 1271 := by
  have e0 : slopeOrbit 1271 328 0 = 328 := rfl
  have e1 : slopeOrbit 1271 328 1 = 41 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1271 328 2 = 41 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1271 328 2 = slopeOrbit 1271 328 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1271,328)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1271_328 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1271)
    (hK : (class1SlopeDatum ctx).K₀ = 328) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1271_328.1) elcCert_1271_328.2 i hi

/-- `(1271,656)`: period `1`, cycle `[41]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1271_656 :
    slopeOrbit 1271 656 (1 + 1) = slopeOrbit 1271 656 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1271 656 j ≤ 1271 := by
  have e0 : slopeOrbit 1271 656 0 = 656 := rfl
  have e1 : slopeOrbit 1271 656 1 = 41 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1271 656 2 = 41 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1271 656 2 = slopeOrbit 1271 656 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1271,656)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1271_656 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1271)
    (hK : (class1SlopeDatum ctx).K₀ = 656) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1271_656.1) elcCert_1271_656.2 i hi

/-- `(1275,5)`: period `1`, cycle `[5]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1275_5 :
    slopeOrbit 1275 5 (1 + 1) = slopeOrbit 1275 5 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1275 5 j ≤ 1275 := by
  have e0 : slopeOrbit 1275 5 0 = 5 := rfl
  have e1 : slopeOrbit 1275 5 1 = 5 :=
    slopeOrbit_step_eval 0 7 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1275 5 2 = 5 :=
    slopeOrbit_step_eval 1 7 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1275 5 2 = slopeOrbit 1275 5 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1275,5)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1275_5 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1275)
    (hK : (class1SlopeDatum ctx).K₀ = 5) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1275_5.1) elcCert_1275_5.2 i hi

/-- `(1275,10)`: period `1`, cycle `[5]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1275_10 :
    slopeOrbit 1275 10 (1 + 1) = slopeOrbit 1275 10 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1275 10 j ≤ 1275 := by
  have e0 : slopeOrbit 1275 10 0 = 10 := rfl
  have e1 : slopeOrbit 1275 10 1 = 5 :=
    slopeOrbit_step_eval 0 6 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1275 10 2 = 5 :=
    slopeOrbit_step_eval 1 7 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1275 10 2 = slopeOrbit 1275 10 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1275,10)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1275_10 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1275)
    (hK : (class1SlopeDatum ctx).K₀ = 10) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1275_10.1) elcCert_1275_10.2 i hi

/-- `(1275,20)`: period `1`, cycle `[5]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1275_20 :
    slopeOrbit 1275 20 (1 + 1) = slopeOrbit 1275 20 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1275 20 j ≤ 1275 := by
  have e0 : slopeOrbit 1275 20 0 = 20 := rfl
  have e1 : slopeOrbit 1275 20 1 = 5 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1275 20 2 = 5 :=
    slopeOrbit_step_eval 1 7 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1275 20 2 = slopeOrbit 1275 20 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1275,20)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1275_20 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1275)
    (hK : (class1SlopeDatum ctx).K₀ = 20) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1275_20.1) elcCert_1275_20.2 i hi

/-- `(1275,40)`: period `1`, cycle `[5]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1275_40 :
    slopeOrbit 1275 40 (1 + 1) = slopeOrbit 1275 40 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1275 40 j ≤ 1275 := by
  have e0 : slopeOrbit 1275 40 0 = 40 := rfl
  have e1 : slopeOrbit 1275 40 1 = 5 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1275 40 2 = 5 :=
    slopeOrbit_step_eval 1 7 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1275 40 2 = slopeOrbit 1275 40 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1275,40)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1275_40 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1275)
    (hK : (class1SlopeDatum ctx).K₀ = 40) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1275_40.1) elcCert_1275_40.2 i hi

/-- `(1275,80)`: period `1`, cycle `[5]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1275_80 :
    slopeOrbit 1275 80 (1 + 1) = slopeOrbit 1275 80 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1275 80 j ≤ 1275 := by
  have e0 : slopeOrbit 1275 80 0 = 80 := rfl
  have e1 : slopeOrbit 1275 80 1 = 5 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1275 80 2 = 5 :=
    slopeOrbit_step_eval 1 7 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1275 80 2 = slopeOrbit 1275 80 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1275,80)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1275_80 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1275)
    (hK : (class1SlopeDatum ctx).K₀ = 80) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1275_80.1) elcCert_1275_80.2 i hi

/-- `(1275,160)`: period `1`, cycle `[5]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1275_160 :
    slopeOrbit 1275 160 (1 + 1) = slopeOrbit 1275 160 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1275 160 j ≤ 1275 := by
  have e0 : slopeOrbit 1275 160 0 = 160 := rfl
  have e1 : slopeOrbit 1275 160 1 = 5 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1275 160 2 = 5 :=
    slopeOrbit_step_eval 1 7 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1275 160 2 = slopeOrbit 1275 160 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1275,160)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1275_160 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1275)
    (hK : (class1SlopeDatum ctx).K₀ = 160) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1275_160.1) elcCert_1275_160.2 i hi

/-- `(1275,320)`: period `1`, cycle `[5]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1275_320 :
    slopeOrbit 1275 320 (1 + 1) = slopeOrbit 1275 320 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1275 320 j ≤ 1275 := by
  have e0 : slopeOrbit 1275 320 0 = 320 := rfl
  have e1 : slopeOrbit 1275 320 1 = 5 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1275 320 2 = 5 :=
    slopeOrbit_step_eval 1 7 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1275 320 2 = slopeOrbit 1275 320 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1275,320)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1275_320 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1275)
    (hK : (class1SlopeDatum ctx).K₀ = 320) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1275_320.1) elcCert_1275_320.2 i hi

/-- `(1275,640)`: period `1`, cycle `[5]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1275_640 :
    slopeOrbit 1275 640 (1 + 1) = slopeOrbit 1275 640 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1275 640 j ≤ 1275 := by
  have e0 : slopeOrbit 1275 640 0 = 640 := rfl
  have e1 : slopeOrbit 1275 640 1 = 5 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1275 640 2 = 5 :=
    slopeOrbit_step_eval 1 7 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1275 640 2 = slopeOrbit 1275 640 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1275,640)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1275_640 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1275)
    (hK : (class1SlopeDatum ctx).K₀ = 640) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1275_640.1) elcCert_1275_640.2 i hi

/-- `(1323,21)`: period `1`, cycle `[21]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1323_21 :
    slopeOrbit 1323 21 (1 + 1) = slopeOrbit 1323 21 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1323 21 j ≤ 1323 := by
  have e0 : slopeOrbit 1323 21 0 = 21 := rfl
  have e1 : slopeOrbit 1323 21 1 = 21 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1323 21 2 = 21 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1323 21 2 = slopeOrbit 1323 21 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1323,21)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1323_21 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1323)
    (hK : (class1SlopeDatum ctx).K₀ = 21) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1323_21.1) elcCert_1323_21.2 i hi

/-- `(1323,42)`: period `1`, cycle `[21]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1323_42 :
    slopeOrbit 1323 42 (1 + 1) = slopeOrbit 1323 42 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1323 42 j ≤ 1323 := by
  have e0 : slopeOrbit 1323 42 0 = 42 := rfl
  have e1 : slopeOrbit 1323 42 1 = 21 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1323 42 2 = 21 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1323 42 2 = slopeOrbit 1323 42 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1323,42)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1323_42 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1323)
    (hK : (class1SlopeDatum ctx).K₀ = 42) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1323_42.1) elcCert_1323_42.2 i hi

/-- `(1323,84)`: period `1`, cycle `[21]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1323_84 :
    slopeOrbit 1323 84 (1 + 1) = slopeOrbit 1323 84 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1323 84 j ≤ 1323 := by
  have e0 : slopeOrbit 1323 84 0 = 84 := rfl
  have e1 : slopeOrbit 1323 84 1 = 21 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1323 84 2 = 21 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1323 84 2 = slopeOrbit 1323 84 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1323,84)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1323_84 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1323)
    (hK : (class1SlopeDatum ctx).K₀ = 84) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1323_84.1) elcCert_1323_84.2 i hi

/-- `(1323,168)`: period `1`, cycle `[21]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1323_168 :
    slopeOrbit 1323 168 (1 + 1) = slopeOrbit 1323 168 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1323 168 j ≤ 1323 := by
  have e0 : slopeOrbit 1323 168 0 = 168 := rfl
  have e1 : slopeOrbit 1323 168 1 = 21 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1323 168 2 = 21 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1323 168 2 = slopeOrbit 1323 168 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1323,168)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1323_168 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1323)
    (hK : (class1SlopeDatum ctx).K₀ = 168) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1323_168.1) elcCert_1323_168.2 i hi

/-- `(1323,336)`: period `1`, cycle `[21]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1323_336 :
    slopeOrbit 1323 336 (1 + 1) = slopeOrbit 1323 336 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1323 336 j ≤ 1323 := by
  have e0 : slopeOrbit 1323 336 0 = 336 := rfl
  have e1 : slopeOrbit 1323 336 1 = 21 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1323 336 2 = 21 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1323 336 2 = slopeOrbit 1323 336 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1323,336)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1323_336 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1323)
    (hK : (class1SlopeDatum ctx).K₀ = 336) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1323_336.1) elcCert_1323_336.2 i hi

/-- `(1323,672)`: period `1`, cycle `[21]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1323_672 :
    slopeOrbit 1323 672 (1 + 1) = slopeOrbit 1323 672 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1323 672 j ≤ 1323 := by
  have e0 : slopeOrbit 1323 672 0 = 672 := rfl
  have e1 : slopeOrbit 1323 672 1 = 21 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1323 672 2 = 21 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1323 672 2 = slopeOrbit 1323 672 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1323,672)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1323_672 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1323)
    (hK : (class1SlopeDatum ctx).K₀ = 672) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1323_672.1) elcCert_1323_672.2 i hi

/-- `(1333,43)`: period `1`, cycle `[43]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1333_43 :
    slopeOrbit 1333 43 (1 + 1) = slopeOrbit 1333 43 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1333 43 j ≤ 1333 := by
  have e0 : slopeOrbit 1333 43 0 = 43 := rfl
  have e1 : slopeOrbit 1333 43 1 = 43 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1333 43 2 = 43 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1333 43 2 = slopeOrbit 1333 43 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1333,43)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1333_43 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1333)
    (hK : (class1SlopeDatum ctx).K₀ = 43) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1333_43.1) elcCert_1333_43.2 i hi

/-- `(1333,86)`: period `1`, cycle `[43]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1333_86 :
    slopeOrbit 1333 86 (1 + 1) = slopeOrbit 1333 86 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1333 86 j ≤ 1333 := by
  have e0 : slopeOrbit 1333 86 0 = 86 := rfl
  have e1 : slopeOrbit 1333 86 1 = 43 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1333 86 2 = 43 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1333 86 2 = slopeOrbit 1333 86 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1333,86)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1333_86 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1333)
    (hK : (class1SlopeDatum ctx).K₀ = 86) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1333_86.1) elcCert_1333_86.2 i hi

/-- `(1333,172)`: period `1`, cycle `[43]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1333_172 :
    slopeOrbit 1333 172 (1 + 1) = slopeOrbit 1333 172 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1333 172 j ≤ 1333 := by
  have e0 : slopeOrbit 1333 172 0 = 172 := rfl
  have e1 : slopeOrbit 1333 172 1 = 43 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1333 172 2 = 43 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1333 172 2 = slopeOrbit 1333 172 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1333,172)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1333_172 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1333)
    (hK : (class1SlopeDatum ctx).K₀ = 172) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1333_172.1) elcCert_1333_172.2 i hi

/-- `(1333,344)`: period `1`, cycle `[43]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1333_344 :
    slopeOrbit 1333 344 (1 + 1) = slopeOrbit 1333 344 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1333 344 j ≤ 1333 := by
  have e0 : slopeOrbit 1333 344 0 = 344 := rfl
  have e1 : slopeOrbit 1333 344 1 = 43 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1333 344 2 = 43 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1333 344 2 = slopeOrbit 1333 344 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1333,344)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1333_344 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1333)
    (hK : (class1SlopeDatum ctx).K₀ = 344) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1333_344.1) elcCert_1333_344.2 i hi

/-- `(1333,688)`: period `1`, cycle `[43]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1333_688 :
    slopeOrbit 1333 688 (1 + 1) = slopeOrbit 1333 688 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1333 688 j ≤ 1333 := by
  have e0 : slopeOrbit 1333 688 0 = 688 := rfl
  have e1 : slopeOrbit 1333 688 1 = 43 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1333 688 2 = 43 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1333 688 2 = slopeOrbit 1333 688 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1333,688)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1333_688 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1333)
    (hK : (class1SlopeDatum ctx).K₀ = 688) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1333_688.1) elcCert_1333_688.2 i hi

/-- `(1365,11)`: period `2`, cycle `[43, 11]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1365_11 :
    slopeOrbit 1365 11 (1 + 2) = slopeOrbit 1365 11 1
      ∧ ∀ j, 1 ≤ j → j ≤ 2 → 16 * slopeOrbit 1365 11 j ≤ 1365 := by
  have e0 : slopeOrbit 1365 11 0 = 11 := rfl
  have e1 : slopeOrbit 1365 11 1 = 43 :=
    slopeOrbit_step_eval 0 6 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1365 11 2 = 11 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 1365 11 3 = 43 :=
    slopeOrbit_step_eval 2 6 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1365 11 3 = slopeOrbit 1365 11 1
    rw [e3, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num
    · rw [e2]
      norm_num

/-- `(1365,11)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1365_11 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1365)
    (hK : (class1SlopeDatum ctx).K₀ = 11) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1365_11.1) elcCert_1365_11.2 i hi

/-- `(1365,22)`: period `2`, cycle `[43, 11]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1365_22 :
    slopeOrbit 1365 22 (1 + 2) = slopeOrbit 1365 22 1
      ∧ ∀ j, 1 ≤ j → j ≤ 2 → 16 * slopeOrbit 1365 22 j ≤ 1365 := by
  have e0 : slopeOrbit 1365 22 0 = 22 := rfl
  have e1 : slopeOrbit 1365 22 1 = 43 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1365 22 2 = 11 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 1365 22 3 = 43 :=
    slopeOrbit_step_eval 2 6 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1365 22 3 = slopeOrbit 1365 22 1
    rw [e3, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num
    · rw [e2]
      norm_num

/-- `(1365,22)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1365_22 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1365)
    (hK : (class1SlopeDatum ctx).K₀ = 22) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1365_22.1) elcCert_1365_22.2 i hi

/-- `(1365,43)`: period `2`, cycle `[11, 43]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1365_43 :
    slopeOrbit 1365 43 (1 + 2) = slopeOrbit 1365 43 1
      ∧ ∀ j, 1 ≤ j → j ≤ 2 → 16 * slopeOrbit 1365 43 j ≤ 1365 := by
  have e0 : slopeOrbit 1365 43 0 = 43 := rfl
  have e1 : slopeOrbit 1365 43 1 = 11 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1365 43 2 = 43 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 1365 43 3 = 11 :=
    slopeOrbit_step_eval 2 4 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1365 43 3 = slopeOrbit 1365 43 1
    rw [e3, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num
    · rw [e2]
      norm_num

/-- `(1365,43)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1365_43 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1365)
    (hK : (class1SlopeDatum ctx).K₀ = 43) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1365_43.1) elcCert_1365_43.2 i hi

/-- `(1365,44)`: period `2`, cycle `[43, 11]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1365_44 :
    slopeOrbit 1365 44 (1 + 2) = slopeOrbit 1365 44 1
      ∧ ∀ j, 1 ≤ j → j ≤ 2 → 16 * slopeOrbit 1365 44 j ≤ 1365 := by
  have e0 : slopeOrbit 1365 44 0 = 44 := rfl
  have e1 : slopeOrbit 1365 44 1 = 43 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1365 44 2 = 11 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 1365 44 3 = 43 :=
    slopeOrbit_step_eval 2 6 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1365 44 3 = slopeOrbit 1365 44 1
    rw [e3, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num
    · rw [e2]
      norm_num

/-- `(1365,44)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1365_44 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1365)
    (hK : (class1SlopeDatum ctx).K₀ = 44) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1365_44.1) elcCert_1365_44.2 i hi

/-- `(1365,86)`: period `2`, cycle `[11, 43]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1365_86 :
    slopeOrbit 1365 86 (1 + 2) = slopeOrbit 1365 86 1
      ∧ ∀ j, 1 ≤ j → j ≤ 2 → 16 * slopeOrbit 1365 86 j ≤ 1365 := by
  have e0 : slopeOrbit 1365 86 0 = 86 := rfl
  have e1 : slopeOrbit 1365 86 1 = 11 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1365 86 2 = 43 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 1365 86 3 = 11 :=
    slopeOrbit_step_eval 2 4 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1365 86 3 = slopeOrbit 1365 86 1
    rw [e3, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num
    · rw [e2]
      norm_num

/-- `(1365,86)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1365_86 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1365)
    (hK : (class1SlopeDatum ctx).K₀ = 86) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1365_86.1) elcCert_1365_86.2 i hi

/-- `(1365,88)`: period `2`, cycle `[43, 11]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1365_88 :
    slopeOrbit 1365 88 (1 + 2) = slopeOrbit 1365 88 1
      ∧ ∀ j, 1 ≤ j → j ≤ 2 → 16 * slopeOrbit 1365 88 j ≤ 1365 := by
  have e0 : slopeOrbit 1365 88 0 = 88 := rfl
  have e1 : slopeOrbit 1365 88 1 = 43 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1365 88 2 = 11 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 1365 88 3 = 43 :=
    slopeOrbit_step_eval 2 6 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1365 88 3 = slopeOrbit 1365 88 1
    rw [e3, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num
    · rw [e2]
      norm_num

/-- `(1365,88)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1365_88 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1365)
    (hK : (class1SlopeDatum ctx).K₀ = 88) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1365_88.1) elcCert_1365_88.2 i hi

/-- `(1365,172)`: period `2`, cycle `[11, 43]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1365_172 :
    slopeOrbit 1365 172 (1 + 2) = slopeOrbit 1365 172 1
      ∧ ∀ j, 1 ≤ j → j ≤ 2 → 16 * slopeOrbit 1365 172 j ≤ 1365 := by
  have e0 : slopeOrbit 1365 172 0 = 172 := rfl
  have e1 : slopeOrbit 1365 172 1 = 11 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1365 172 2 = 43 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 1365 172 3 = 11 :=
    slopeOrbit_step_eval 2 4 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1365 172 3 = slopeOrbit 1365 172 1
    rw [e3, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num
    · rw [e2]
      norm_num

/-- `(1365,172)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1365_172 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1365)
    (hK : (class1SlopeDatum ctx).K₀ = 172) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1365_172.1) elcCert_1365_172.2 i hi

/-- `(1365,176)`: period `2`, cycle `[43, 11]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1365_176 :
    slopeOrbit 1365 176 (1 + 2) = slopeOrbit 1365 176 1
      ∧ ∀ j, 1 ≤ j → j ≤ 2 → 16 * slopeOrbit 1365 176 j ≤ 1365 := by
  have e0 : slopeOrbit 1365 176 0 = 176 := rfl
  have e1 : slopeOrbit 1365 176 1 = 43 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1365 176 2 = 11 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 1365 176 3 = 43 :=
    slopeOrbit_step_eval 2 6 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1365 176 3 = slopeOrbit 1365 176 1
    rw [e3, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num
    · rw [e2]
      norm_num

/-- `(1365,176)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1365_176 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1365)
    (hK : (class1SlopeDatum ctx).K₀ = 176) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1365_176.1) elcCert_1365_176.2 i hi

/-- `(1365,344)`: period `2`, cycle `[11, 43]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1365_344 :
    slopeOrbit 1365 344 (1 + 2) = slopeOrbit 1365 344 1
      ∧ ∀ j, 1 ≤ j → j ≤ 2 → 16 * slopeOrbit 1365 344 j ≤ 1365 := by
  have e0 : slopeOrbit 1365 344 0 = 344 := rfl
  have e1 : slopeOrbit 1365 344 1 = 11 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1365 344 2 = 43 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 1365 344 3 = 11 :=
    slopeOrbit_step_eval 2 4 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1365 344 3 = slopeOrbit 1365 344 1
    rw [e3, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num
    · rw [e2]
      norm_num

/-- `(1365,344)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1365_344 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1365)
    (hK : (class1SlopeDatum ctx).K₀ = 344) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1365_344.1) elcCert_1365_344.2 i hi

/-- `(1365,352)`: period `2`, cycle `[43, 11]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1365_352 :
    slopeOrbit 1365 352 (1 + 2) = slopeOrbit 1365 352 1
      ∧ ∀ j, 1 ≤ j → j ≤ 2 → 16 * slopeOrbit 1365 352 j ≤ 1365 := by
  have e0 : slopeOrbit 1365 352 0 = 352 := rfl
  have e1 : slopeOrbit 1365 352 1 = 43 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1365 352 2 = 11 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 1365 352 3 = 43 :=
    slopeOrbit_step_eval 2 6 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1365 352 3 = slopeOrbit 1365 352 1
    rw [e3, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num
    · rw [e2]
      norm_num

/-- `(1365,352)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1365_352 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1365)
    (hK : (class1SlopeDatum ctx).K₀ = 352) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1365_352.1) elcCert_1365_352.2 i hi

/-- `(1365,688)`: period `2`, cycle `[11, 43]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1365_688 :
    slopeOrbit 1365 688 (1 + 2) = slopeOrbit 1365 688 1
      ∧ ∀ j, 1 ≤ j → j ≤ 2 → 16 * slopeOrbit 1365 688 j ≤ 1365 := by
  have e0 : slopeOrbit 1365 688 0 = 688 := rfl
  have e1 : slopeOrbit 1365 688 1 = 11 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1365 688 2 = 43 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 1365 688 3 = 11 :=
    slopeOrbit_step_eval 2 4 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1365 688 3 = slopeOrbit 1365 688 1
    rw [e3, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num
    · rw [e2]
      norm_num

/-- `(1365,688)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1365_688 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1365)
    (hK : (class1SlopeDatum ctx).K₀ = 688) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1365_688.1) elcCert_1365_688.2 i hi

/-- `(1365,704)`: period `2`, cycle `[43, 11]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1365_704 :
    slopeOrbit 1365 704 (1 + 2) = slopeOrbit 1365 704 1
      ∧ ∀ j, 1 ≤ j → j ≤ 2 → 16 * slopeOrbit 1365 704 j ≤ 1365 := by
  have e0 : slopeOrbit 1365 704 0 = 704 := rfl
  have e1 : slopeOrbit 1365 704 1 = 43 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1365 704 2 = 11 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 1365 704 3 = 43 :=
    slopeOrbit_step_eval 2 6 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1365 704 3 = slopeOrbit 1365 704 1
    rw [e3, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num
    · rw [e2]
      norm_num

/-- `(1365,704)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1365_704 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1365)
    (hK : (class1SlopeDatum ctx).K₀ = 704) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1365_704.1) elcCert_1365_704.2 i hi

/-- `(1395,45)`: period `1`, cycle `[45]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1395_45 :
    slopeOrbit 1395 45 (1 + 1) = slopeOrbit 1395 45 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1395 45 j ≤ 1395 := by
  have e0 : slopeOrbit 1395 45 0 = 45 := rfl
  have e1 : slopeOrbit 1395 45 1 = 45 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1395 45 2 = 45 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1395 45 2 = slopeOrbit 1395 45 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1395,45)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1395_45 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1395)
    (hK : (class1SlopeDatum ctx).K₀ = 45) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1395_45.1) elcCert_1395_45.2 i hi

/-- `(1395,90)`: period `1`, cycle `[45]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1395_90 :
    slopeOrbit 1395 90 (1 + 1) = slopeOrbit 1395 90 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1395 90 j ≤ 1395 := by
  have e0 : slopeOrbit 1395 90 0 = 90 := rfl
  have e1 : slopeOrbit 1395 90 1 = 45 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1395 90 2 = 45 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1395 90 2 = slopeOrbit 1395 90 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1395,90)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1395_90 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1395)
    (hK : (class1SlopeDatum ctx).K₀ = 90) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1395_90.1) elcCert_1395_90.2 i hi

/-- `(1395,180)`: period `1`, cycle `[45]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1395_180 :
    slopeOrbit 1395 180 (1 + 1) = slopeOrbit 1395 180 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1395 180 j ≤ 1395 := by
  have e0 : slopeOrbit 1395 180 0 = 180 := rfl
  have e1 : slopeOrbit 1395 180 1 = 45 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1395 180 2 = 45 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1395 180 2 = slopeOrbit 1395 180 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1395,180)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1395_180 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1395)
    (hK : (class1SlopeDatum ctx).K₀ = 180) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1395_180.1) elcCert_1395_180.2 i hi

/-- `(1395,360)`: period `1`, cycle `[45]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1395_360 :
    slopeOrbit 1395 360 (1 + 1) = slopeOrbit 1395 360 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1395 360 j ≤ 1395 := by
  have e0 : slopeOrbit 1395 360 0 = 360 := rfl
  have e1 : slopeOrbit 1395 360 1 = 45 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1395 360 2 = 45 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1395 360 2 = slopeOrbit 1395 360 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1395,360)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1395_360 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1395)
    (hK : (class1SlopeDatum ctx).K₀ = 360) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1395_360.1) elcCert_1395_360.2 i hi

/-- `(1395,720)`: period `1`, cycle `[45]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1395_720 :
    slopeOrbit 1395 720 (1 + 1) = slopeOrbit 1395 720 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1395 720 j ≤ 1395 := by
  have e0 : slopeOrbit 1395 720 0 = 720 := rfl
  have e1 : slopeOrbit 1395 720 1 = 45 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1395 720 2 = 45 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1395 720 2 = slopeOrbit 1395 720 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1395,720)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1395_720 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1395)
    (hK : (class1SlopeDatum ctx).K₀ = 720) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1395_720.1) elcCert_1395_720.2 i hi

/-- `(1397,11)`: period `1`, cycle `[11]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1397_11 :
    slopeOrbit 1397 11 (1 + 1) = slopeOrbit 1397 11 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1397 11 j ≤ 1397 := by
  have e0 : slopeOrbit 1397 11 0 = 11 := rfl
  have e1 : slopeOrbit 1397 11 1 = 11 :=
    slopeOrbit_step_eval 0 6 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1397 11 2 = 11 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1397 11 2 = slopeOrbit 1397 11 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1397,11)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1397_11 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1397)
    (hK : (class1SlopeDatum ctx).K₀ = 11) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1397_11.1) elcCert_1397_11.2 i hi

/-- `(1397,22)`: period `1`, cycle `[11]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1397_22 :
    slopeOrbit 1397 22 (1 + 1) = slopeOrbit 1397 22 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1397 22 j ≤ 1397 := by
  have e0 : slopeOrbit 1397 22 0 = 22 := rfl
  have e1 : slopeOrbit 1397 22 1 = 11 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1397 22 2 = 11 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1397 22 2 = slopeOrbit 1397 22 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1397,22)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1397_22 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1397)
    (hK : (class1SlopeDatum ctx).K₀ = 22) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1397_22.1) elcCert_1397_22.2 i hi

/-- `(1397,44)`: period `1`, cycle `[11]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1397_44 :
    slopeOrbit 1397 44 (1 + 1) = slopeOrbit 1397 44 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1397 44 j ≤ 1397 := by
  have e0 : slopeOrbit 1397 44 0 = 44 := rfl
  have e1 : slopeOrbit 1397 44 1 = 11 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1397 44 2 = 11 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1397 44 2 = slopeOrbit 1397 44 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1397,44)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1397_44 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1397)
    (hK : (class1SlopeDatum ctx).K₀ = 44) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1397_44.1) elcCert_1397_44.2 i hi

/-- `(1397,88)`: period `1`, cycle `[11]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1397_88 :
    slopeOrbit 1397 88 (1 + 1) = slopeOrbit 1397 88 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1397 88 j ≤ 1397 := by
  have e0 : slopeOrbit 1397 88 0 = 88 := rfl
  have e1 : slopeOrbit 1397 88 1 = 11 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1397 88 2 = 11 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1397 88 2 = slopeOrbit 1397 88 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1397,88)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1397_88 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1397)
    (hK : (class1SlopeDatum ctx).K₀ = 88) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1397_88.1) elcCert_1397_88.2 i hi

/-- `(1397,176)`: period `1`, cycle `[11]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1397_176 :
    slopeOrbit 1397 176 (1 + 1) = slopeOrbit 1397 176 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1397 176 j ≤ 1397 := by
  have e0 : slopeOrbit 1397 176 0 = 176 := rfl
  have e1 : slopeOrbit 1397 176 1 = 11 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1397 176 2 = 11 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1397 176 2 = slopeOrbit 1397 176 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1397,176)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1397_176 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1397)
    (hK : (class1SlopeDatum ctx).K₀ = 176) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1397_176.1) elcCert_1397_176.2 i hi

/-- `(1397,352)`: period `1`, cycle `[11]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1397_352 :
    slopeOrbit 1397 352 (1 + 1) = slopeOrbit 1397 352 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1397 352 j ≤ 1397 := by
  have e0 : slopeOrbit 1397 352 0 = 352 := rfl
  have e1 : slopeOrbit 1397 352 1 = 11 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1397 352 2 = 11 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1397 352 2 = slopeOrbit 1397 352 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1397,352)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1397_352 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1397)
    (hK : (class1SlopeDatum ctx).K₀ = 352) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1397_352.1) elcCert_1397_352.2 i hi

/-- `(1397,704)`: period `1`, cycle `[11]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1397_704 :
    slopeOrbit 1397 704 (1 + 1) = slopeOrbit 1397 704 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1397 704 j ≤ 1397 := by
  have e0 : slopeOrbit 1397 704 0 = 704 := rfl
  have e1 : slopeOrbit 1397 704 1 = 11 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1397 704 2 = 11 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1397 704 2 = slopeOrbit 1397 704 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1397,704)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1397_704 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1397)
    (hK : (class1SlopeDatum ctx).K₀ = 704) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1397_704.1) elcCert_1397_704.2 i hi

/-- `(1449,23)`: period `1`, cycle `[23]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1449_23 :
    slopeOrbit 1449 23 (1 + 1) = slopeOrbit 1449 23 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1449 23 j ≤ 1449 := by
  have e0 : slopeOrbit 1449 23 0 = 23 := rfl
  have e1 : slopeOrbit 1449 23 1 = 23 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1449 23 2 = 23 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1449 23 2 = slopeOrbit 1449 23 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1449,23)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1449_23 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1449)
    (hK : (class1SlopeDatum ctx).K₀ = 23) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1449_23.1) elcCert_1449_23.2 i hi

/-- `(1449,46)`: period `1`, cycle `[23]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1449_46 :
    slopeOrbit 1449 46 (1 + 1) = slopeOrbit 1449 46 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1449 46 j ≤ 1449 := by
  have e0 : slopeOrbit 1449 46 0 = 46 := rfl
  have e1 : slopeOrbit 1449 46 1 = 23 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1449 46 2 = 23 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1449 46 2 = slopeOrbit 1449 46 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1449,46)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1449_46 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1449)
    (hK : (class1SlopeDatum ctx).K₀ = 46) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1449_46.1) elcCert_1449_46.2 i hi

/-- `(1449,92)`: period `1`, cycle `[23]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1449_92 :
    slopeOrbit 1449 92 (1 + 1) = slopeOrbit 1449 92 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1449 92 j ≤ 1449 := by
  have e0 : slopeOrbit 1449 92 0 = 92 := rfl
  have e1 : slopeOrbit 1449 92 1 = 23 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1449 92 2 = 23 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1449 92 2 = slopeOrbit 1449 92 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1449,92)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1449_92 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1449)
    (hK : (class1SlopeDatum ctx).K₀ = 92) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1449_92.1) elcCert_1449_92.2 i hi

/-- `(1449,184)`: period `1`, cycle `[23]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1449_184 :
    slopeOrbit 1449 184 (1 + 1) = slopeOrbit 1449 184 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1449 184 j ≤ 1449 := by
  have e0 : slopeOrbit 1449 184 0 = 184 := rfl
  have e1 : slopeOrbit 1449 184 1 = 23 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1449 184 2 = 23 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1449 184 2 = slopeOrbit 1449 184 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1449,184)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1449_184 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1449)
    (hK : (class1SlopeDatum ctx).K₀ = 184) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1449_184.1) elcCert_1449_184.2 i hi

/-- `(1449,368)`: period `1`, cycle `[23]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1449_368 :
    slopeOrbit 1449 368 (1 + 1) = slopeOrbit 1449 368 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1449 368 j ≤ 1449 := by
  have e0 : slopeOrbit 1449 368 0 = 368 := rfl
  have e1 : slopeOrbit 1449 368 1 = 23 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1449 368 2 = 23 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1449 368 2 = slopeOrbit 1449 368 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1449,368)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1449_368 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1449)
    (hK : (class1SlopeDatum ctx).K₀ = 368) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1449_368.1) elcCert_1449_368.2 i hi

/-- `(1449,736)`: period `1`, cycle `[23]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1449_736 :
    slopeOrbit 1449 736 (1 + 1) = slopeOrbit 1449 736 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1449 736 j ≤ 1449 := by
  have e0 : slopeOrbit 1449 736 0 = 736 := rfl
  have e1 : slopeOrbit 1449 736 1 = 23 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1449 736 2 = 23 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1449 736 2 = slopeOrbit 1449 736 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1449,736)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1449_736 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1449)
    (hK : (class1SlopeDatum ctx).K₀ = 736) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1449_736.1) elcCert_1449_736.2 i hi

/-- `(1457,47)`: period `1`, cycle `[47]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1457_47 :
    slopeOrbit 1457 47 (1 + 1) = slopeOrbit 1457 47 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1457 47 j ≤ 1457 := by
  have e0 : slopeOrbit 1457 47 0 = 47 := rfl
  have e1 : slopeOrbit 1457 47 1 = 47 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1457 47 2 = 47 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1457 47 2 = slopeOrbit 1457 47 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1457,47)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1457_47 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1457)
    (hK : (class1SlopeDatum ctx).K₀ = 47) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1457_47.1) elcCert_1457_47.2 i hi

/-- `(1457,94)`: period `1`, cycle `[47]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1457_94 :
    slopeOrbit 1457 94 (1 + 1) = slopeOrbit 1457 94 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1457 94 j ≤ 1457 := by
  have e0 : slopeOrbit 1457 94 0 = 94 := rfl
  have e1 : slopeOrbit 1457 94 1 = 47 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1457 94 2 = 47 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1457 94 2 = slopeOrbit 1457 94 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1457,94)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1457_94 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1457)
    (hK : (class1SlopeDatum ctx).K₀ = 94) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1457_94.1) elcCert_1457_94.2 i hi

/-- `(1457,188)`: period `1`, cycle `[47]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1457_188 :
    slopeOrbit 1457 188 (1 + 1) = slopeOrbit 1457 188 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1457 188 j ≤ 1457 := by
  have e0 : slopeOrbit 1457 188 0 = 188 := rfl
  have e1 : slopeOrbit 1457 188 1 = 47 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1457 188 2 = 47 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1457 188 2 = slopeOrbit 1457 188 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1457,188)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1457_188 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1457)
    (hK : (class1SlopeDatum ctx).K₀ = 188) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1457_188.1) elcCert_1457_188.2 i hi

/-- `(1457,376)`: period `1`, cycle `[47]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1457_376 :
    slopeOrbit 1457 376 (1 + 1) = slopeOrbit 1457 376 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1457 376 j ≤ 1457 := by
  have e0 : slopeOrbit 1457 376 0 = 376 := rfl
  have e1 : slopeOrbit 1457 376 1 = 47 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1457 376 2 = 47 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1457 376 2 = slopeOrbit 1457 376 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1457,376)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1457_376 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1457)
    (hK : (class1SlopeDatum ctx).K₀ = 376) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1457_376.1) elcCert_1457_376.2 i hi

/-- `(1457,752)`: period `1`, cycle `[47]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1457_752 :
    slopeOrbit 1457 752 (1 + 1) = slopeOrbit 1457 752 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1457 752 j ≤ 1457 := by
  have e0 : slopeOrbit 1457 752 0 = 752 := rfl
  have e1 : slopeOrbit 1457 752 1 = 47 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1457 752 2 = 47 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1457 752 2 = slopeOrbit 1457 752 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1457,752)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1457_752 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1457)
    (hK : (class1SlopeDatum ctx).K₀ = 752) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1457_752.1) elcCert_1457_752.2 i hi

/-- `(1519,49)`: period `1`, cycle `[49]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1519_49 :
    slopeOrbit 1519 49 (1 + 1) = slopeOrbit 1519 49 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1519 49 j ≤ 1519 := by
  have e0 : slopeOrbit 1519 49 0 = 49 := rfl
  have e1 : slopeOrbit 1519 49 1 = 49 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1519 49 2 = 49 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1519 49 2 = slopeOrbit 1519 49 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1519,49)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1519_49 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1519)
    (hK : (class1SlopeDatum ctx).K₀ = 49) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1519_49.1) elcCert_1519_49.2 i hi

/-- `(1519,98)`: period `1`, cycle `[49]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1519_98 :
    slopeOrbit 1519 98 (1 + 1) = slopeOrbit 1519 98 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1519 98 j ≤ 1519 := by
  have e0 : slopeOrbit 1519 98 0 = 98 := rfl
  have e1 : slopeOrbit 1519 98 1 = 49 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1519 98 2 = 49 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1519 98 2 = slopeOrbit 1519 98 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1519,98)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1519_98 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1519)
    (hK : (class1SlopeDatum ctx).K₀ = 98) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1519_98.1) elcCert_1519_98.2 i hi

/-- `(1519,196)`: period `1`, cycle `[49]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1519_196 :
    slopeOrbit 1519 196 (1 + 1) = slopeOrbit 1519 196 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1519 196 j ≤ 1519 := by
  have e0 : slopeOrbit 1519 196 0 = 196 := rfl
  have e1 : slopeOrbit 1519 196 1 = 49 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1519 196 2 = 49 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1519 196 2 = slopeOrbit 1519 196 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1519,196)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1519_196 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1519)
    (hK : (class1SlopeDatum ctx).K₀ = 196) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1519_196.1) elcCert_1519_196.2 i hi

/-- `(1519,392)`: period `1`, cycle `[49]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1519_392 :
    slopeOrbit 1519 392 (1 + 1) = slopeOrbit 1519 392 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1519 392 j ≤ 1519 := by
  have e0 : slopeOrbit 1519 392 0 = 392 := rfl
  have e1 : slopeOrbit 1519 392 1 = 49 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1519 392 2 = 49 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1519 392 2 = slopeOrbit 1519 392 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1519,392)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1519_392 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1519)
    (hK : (class1SlopeDatum ctx).K₀ = 392) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1519_392.1) elcCert_1519_392.2 i hi

/-- `(1519,784)`: period `1`, cycle `[49]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1519_784 :
    slopeOrbit 1519 784 (1 + 1) = slopeOrbit 1519 784 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1519 784 j ≤ 1519 := by
  have e0 : slopeOrbit 1519 784 0 = 784 := rfl
  have e1 : slopeOrbit 1519 784 1 = 49 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1519 784 2 = 49 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1519 784 2 = slopeOrbit 1519 784 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1519,784)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1519_784 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1519)
    (hK : (class1SlopeDatum ctx).K₀ = 784) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1519_784.1) elcCert_1519_784.2 i hi

/-- `(1533,3)`: period `1`, cycle `[3]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1533_3 :
    slopeOrbit 1533 3 (1 + 1) = slopeOrbit 1533 3 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1533 3 j ≤ 1533 := by
  have e0 : slopeOrbit 1533 3 0 = 3 := rfl
  have e1 : slopeOrbit 1533 3 1 = 3 :=
    slopeOrbit_step_eval 0 8 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1533 3 2 = 3 :=
    slopeOrbit_step_eval 1 8 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1533 3 2 = slopeOrbit 1533 3 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1533,3)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1533_3 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1533)
    (hK : (class1SlopeDatum ctx).K₀ = 3) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1533_3.1) elcCert_1533_3.2 i hi

/-- `(1533,6)`: period `1`, cycle `[3]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1533_6 :
    slopeOrbit 1533 6 (1 + 1) = slopeOrbit 1533 6 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1533 6 j ≤ 1533 := by
  have e0 : slopeOrbit 1533 6 0 = 6 := rfl
  have e1 : slopeOrbit 1533 6 1 = 3 :=
    slopeOrbit_step_eval 0 7 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1533 6 2 = 3 :=
    slopeOrbit_step_eval 1 8 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1533 6 2 = slopeOrbit 1533 6 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1533,6)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1533_6 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1533)
    (hK : (class1SlopeDatum ctx).K₀ = 6) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1533_6.1) elcCert_1533_6.2 i hi

/-- `(1533,12)`: period `1`, cycle `[3]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1533_12 :
    slopeOrbit 1533 12 (1 + 1) = slopeOrbit 1533 12 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1533 12 j ≤ 1533 := by
  have e0 : slopeOrbit 1533 12 0 = 12 := rfl
  have e1 : slopeOrbit 1533 12 1 = 3 :=
    slopeOrbit_step_eval 0 6 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1533 12 2 = 3 :=
    slopeOrbit_step_eval 1 8 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1533 12 2 = slopeOrbit 1533 12 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1533,12)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1533_12 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1533)
    (hK : (class1SlopeDatum ctx).K₀ = 12) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1533_12.1) elcCert_1533_12.2 i hi

/-- `(1533,24)`: period `1`, cycle `[3]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1533_24 :
    slopeOrbit 1533 24 (1 + 1) = slopeOrbit 1533 24 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1533 24 j ≤ 1533 := by
  have e0 : slopeOrbit 1533 24 0 = 24 := rfl
  have e1 : slopeOrbit 1533 24 1 = 3 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1533 24 2 = 3 :=
    slopeOrbit_step_eval 1 8 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1533 24 2 = slopeOrbit 1533 24 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1533,24)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1533_24 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1533)
    (hK : (class1SlopeDatum ctx).K₀ = 24) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1533_24.1) elcCert_1533_24.2 i hi

/-- `(1533,48)`: period `1`, cycle `[3]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1533_48 :
    slopeOrbit 1533 48 (1 + 1) = slopeOrbit 1533 48 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1533 48 j ≤ 1533 := by
  have e0 : slopeOrbit 1533 48 0 = 48 := rfl
  have e1 : slopeOrbit 1533 48 1 = 3 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1533 48 2 = 3 :=
    slopeOrbit_step_eval 1 8 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1533 48 2 = slopeOrbit 1533 48 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1533,48)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1533_48 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1533)
    (hK : (class1SlopeDatum ctx).K₀ = 48) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1533_48.1) elcCert_1533_48.2 i hi

/-- `(1533,96)`: period `1`, cycle `[3]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1533_96 :
    slopeOrbit 1533 96 (1 + 1) = slopeOrbit 1533 96 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1533 96 j ≤ 1533 := by
  have e0 : slopeOrbit 1533 96 0 = 96 := rfl
  have e1 : slopeOrbit 1533 96 1 = 3 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1533 96 2 = 3 :=
    slopeOrbit_step_eval 1 8 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1533 96 2 = slopeOrbit 1533 96 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1533,96)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1533_96 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1533)
    (hK : (class1SlopeDatum ctx).K₀ = 96) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1533_96.1) elcCert_1533_96.2 i hi

/-- `(1533,192)`: period `1`, cycle `[3]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1533_192 :
    slopeOrbit 1533 192 (1 + 1) = slopeOrbit 1533 192 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1533 192 j ≤ 1533 := by
  have e0 : slopeOrbit 1533 192 0 = 192 := rfl
  have e1 : slopeOrbit 1533 192 1 = 3 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1533 192 2 = 3 :=
    slopeOrbit_step_eval 1 8 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1533 192 2 = slopeOrbit 1533 192 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1533,192)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1533_192 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1533)
    (hK : (class1SlopeDatum ctx).K₀ = 192) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1533_192.1) elcCert_1533_192.2 i hi

/-- `(1533,384)`: period `1`, cycle `[3]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1533_384 :
    slopeOrbit 1533 384 (1 + 1) = slopeOrbit 1533 384 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1533 384 j ≤ 1533 := by
  have e0 : slopeOrbit 1533 384 0 = 384 := rfl
  have e1 : slopeOrbit 1533 384 1 = 3 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1533 384 2 = 3 :=
    slopeOrbit_step_eval 1 8 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1533 384 2 = slopeOrbit 1533 384 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1533,384)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1533_384 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1533)
    (hK : (class1SlopeDatum ctx).K₀ = 384) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1533_384.1) elcCert_1533_384.2 i hi

/-- `(1533,768)`: period `1`, cycle `[3]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1533_768 :
    slopeOrbit 1533 768 (1 + 1) = slopeOrbit 1533 768 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1533 768 j ≤ 1533 := by
  have e0 : slopeOrbit 1533 768 0 = 768 := rfl
  have e1 : slopeOrbit 1533 768 1 = 3 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1533 768 2 = 3 :=
    slopeOrbit_step_eval 1 8 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1533 768 2 = slopeOrbit 1533 768 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1533,768)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1533_768 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1533)
    (hK : (class1SlopeDatum ctx).K₀ = 768) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1533_768.1) elcCert_1533_768.2 i hi

/-- `(1575,25)`: period `1`, cycle `[25]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1575_25 :
    slopeOrbit 1575 25 (1 + 1) = slopeOrbit 1575 25 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1575 25 j ≤ 1575 := by
  have e0 : slopeOrbit 1575 25 0 = 25 := rfl
  have e1 : slopeOrbit 1575 25 1 = 25 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1575 25 2 = 25 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1575 25 2 = slopeOrbit 1575 25 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1575,25)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1575_25 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1575)
    (hK : (class1SlopeDatum ctx).K₀ = 25) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1575_25.1) elcCert_1575_25.2 i hi

/-- `(1575,50)`: period `1`, cycle `[25]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1575_50 :
    slopeOrbit 1575 50 (1 + 1) = slopeOrbit 1575 50 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1575 50 j ≤ 1575 := by
  have e0 : slopeOrbit 1575 50 0 = 50 := rfl
  have e1 : slopeOrbit 1575 50 1 = 25 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1575 50 2 = 25 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1575 50 2 = slopeOrbit 1575 50 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1575,50)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1575_50 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1575)
    (hK : (class1SlopeDatum ctx).K₀ = 50) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1575_50.1) elcCert_1575_50.2 i hi

/-- `(1575,100)`: period `1`, cycle `[25]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1575_100 :
    slopeOrbit 1575 100 (1 + 1) = slopeOrbit 1575 100 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1575 100 j ≤ 1575 := by
  have e0 : slopeOrbit 1575 100 0 = 100 := rfl
  have e1 : slopeOrbit 1575 100 1 = 25 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1575 100 2 = 25 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1575 100 2 = slopeOrbit 1575 100 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1575,100)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1575_100 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1575)
    (hK : (class1SlopeDatum ctx).K₀ = 100) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1575_100.1) elcCert_1575_100.2 i hi

/-- `(1575,200)`: period `1`, cycle `[25]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1575_200 :
    slopeOrbit 1575 200 (1 + 1) = slopeOrbit 1575 200 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1575 200 j ≤ 1575 := by
  have e0 : slopeOrbit 1575 200 0 = 200 := rfl
  have e1 : slopeOrbit 1575 200 1 = 25 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1575 200 2 = 25 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1575 200 2 = slopeOrbit 1575 200 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1575,200)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1575_200 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1575)
    (hK : (class1SlopeDatum ctx).K₀ = 200) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1575_200.1) elcCert_1575_200.2 i hi

/-- `(1575,400)`: period `1`, cycle `[25]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1575_400 :
    slopeOrbit 1575 400 (1 + 1) = slopeOrbit 1575 400 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1575 400 j ≤ 1575 := by
  have e0 : slopeOrbit 1575 400 0 = 400 := rfl
  have e1 : slopeOrbit 1575 400 1 = 25 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1575 400 2 = 25 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1575 400 2 = slopeOrbit 1575 400 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1575,400)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1575_400 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1575)
    (hK : (class1SlopeDatum ctx).K₀ = 400) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1575_400.1) elcCert_1575_400.2 i hi

/-- `(1575,800)`: period `1`, cycle `[25]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1575_800 :
    slopeOrbit 1575 800 (1 + 1) = slopeOrbit 1575 800 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1575 800 j ≤ 1575 := by
  have e0 : slopeOrbit 1575 800 0 = 800 := rfl
  have e1 : slopeOrbit 1575 800 1 = 25 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1575 800 2 = 25 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1575 800 2 = slopeOrbit 1575 800 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1575,800)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1575_800 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1575)
    (hK : (class1SlopeDatum ctx).K₀ = 800) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1575_800.1) elcCert_1575_800.2 i hi

/-- `(1581,51)`: period `1`, cycle `[51]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1581_51 :
    slopeOrbit 1581 51 (1 + 1) = slopeOrbit 1581 51 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1581 51 j ≤ 1581 := by
  have e0 : slopeOrbit 1581 51 0 = 51 := rfl
  have e1 : slopeOrbit 1581 51 1 = 51 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1581 51 2 = 51 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1581 51 2 = slopeOrbit 1581 51 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1581,51)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1581_51 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1581)
    (hK : (class1SlopeDatum ctx).K₀ = 51) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1581_51.1) elcCert_1581_51.2 i hi

/-- `(1581,102)`: period `1`, cycle `[51]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1581_102 :
    slopeOrbit 1581 102 (1 + 1) = slopeOrbit 1581 102 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1581 102 j ≤ 1581 := by
  have e0 : slopeOrbit 1581 102 0 = 102 := rfl
  have e1 : slopeOrbit 1581 102 1 = 51 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1581 102 2 = 51 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1581 102 2 = slopeOrbit 1581 102 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1581,102)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1581_102 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1581)
    (hK : (class1SlopeDatum ctx).K₀ = 102) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1581_102.1) elcCert_1581_102.2 i hi

/-- `(1581,204)`: period `1`, cycle `[51]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1581_204 :
    slopeOrbit 1581 204 (1 + 1) = slopeOrbit 1581 204 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1581 204 j ≤ 1581 := by
  have e0 : slopeOrbit 1581 204 0 = 204 := rfl
  have e1 : slopeOrbit 1581 204 1 = 51 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1581 204 2 = 51 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1581 204 2 = slopeOrbit 1581 204 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1581,204)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1581_204 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1581)
    (hK : (class1SlopeDatum ctx).K₀ = 204) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1581_204.1) elcCert_1581_204.2 i hi

/-- `(1581,408)`: period `1`, cycle `[51]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1581_408 :
    slopeOrbit 1581 408 (1 + 1) = slopeOrbit 1581 408 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1581 408 j ≤ 1581 := by
  have e0 : slopeOrbit 1581 408 0 = 408 := rfl
  have e1 : slopeOrbit 1581 408 1 = 51 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1581 408 2 = 51 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1581 408 2 = slopeOrbit 1581 408 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1581,408)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1581_408 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1581)
    (hK : (class1SlopeDatum ctx).K₀ = 408) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1581_408.1) elcCert_1581_408.2 i hi

/-- `(1581,816)`: period `1`, cycle `[51]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1581_816 :
    slopeOrbit 1581 816 (1 + 1) = slopeOrbit 1581 816 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1581 816 j ≤ 1581 := by
  have e0 : slopeOrbit 1581 816 0 = 816 := rfl
  have e1 : slopeOrbit 1581 816 1 = 51 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1581 816 2 = 51 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1581 816 2 = slopeOrbit 1581 816 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1581,816)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1581_816 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1581)
    (hK : (class1SlopeDatum ctx).K₀ = 816) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1581_816.1) elcCert_1581_816.2 i hi

/-- `(1643,53)`: period `1`, cycle `[53]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1643_53 :
    slopeOrbit 1643 53 (1 + 1) = slopeOrbit 1643 53 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1643 53 j ≤ 1643 := by
  have e0 : slopeOrbit 1643 53 0 = 53 := rfl
  have e1 : slopeOrbit 1643 53 1 = 53 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1643 53 2 = 53 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1643 53 2 = slopeOrbit 1643 53 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1643,53)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1643_53 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1643)
    (hK : (class1SlopeDatum ctx).K₀ = 53) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1643_53.1) elcCert_1643_53.2 i hi

/-- `(1643,106)`: period `1`, cycle `[53]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1643_106 :
    slopeOrbit 1643 106 (1 + 1) = slopeOrbit 1643 106 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1643 106 j ≤ 1643 := by
  have e0 : slopeOrbit 1643 106 0 = 106 := rfl
  have e1 : slopeOrbit 1643 106 1 = 53 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1643 106 2 = 53 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1643 106 2 = slopeOrbit 1643 106 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1643,106)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1643_106 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1643)
    (hK : (class1SlopeDatum ctx).K₀ = 106) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1643_106.1) elcCert_1643_106.2 i hi

/-- `(1643,212)`: period `1`, cycle `[53]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1643_212 :
    slopeOrbit 1643 212 (1 + 1) = slopeOrbit 1643 212 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1643 212 j ≤ 1643 := by
  have e0 : slopeOrbit 1643 212 0 = 212 := rfl
  have e1 : slopeOrbit 1643 212 1 = 53 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1643 212 2 = 53 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1643 212 2 = slopeOrbit 1643 212 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1643,212)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1643_212 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1643)
    (hK : (class1SlopeDatum ctx).K₀ = 212) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1643_212.1) elcCert_1643_212.2 i hi

/-- `(1643,424)`: period `1`, cycle `[53]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1643_424 :
    slopeOrbit 1643 424 (1 + 1) = slopeOrbit 1643 424 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1643 424 j ≤ 1643 := by
  have e0 : slopeOrbit 1643 424 0 = 424 := rfl
  have e1 : slopeOrbit 1643 424 1 = 53 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1643 424 2 = 53 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1643 424 2 = slopeOrbit 1643 424 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1643,424)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1643_424 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1643)
    (hK : (class1SlopeDatum ctx).K₀ = 424) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1643_424.1) elcCert_1643_424.2 i hi

/-- `(1643,848)`: period `1`, cycle `[53]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1643_848 :
    slopeOrbit 1643 848 (1 + 1) = slopeOrbit 1643 848 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1643 848 j ≤ 1643 := by
  have e0 : slopeOrbit 1643 848 0 = 848 := rfl
  have e1 : slopeOrbit 1643 848 1 = 53 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1643 848 2 = 53 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1643 848 2 = slopeOrbit 1643 848 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1643,848)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1643_848 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1643)
    (hK : (class1SlopeDatum ctx).K₀ = 848) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1643_848.1) elcCert_1643_848.2 i hi

/-- `(1651,13)`: period `1`, cycle `[13]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1651_13 :
    slopeOrbit 1651 13 (1 + 1) = slopeOrbit 1651 13 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1651 13 j ≤ 1651 := by
  have e0 : slopeOrbit 1651 13 0 = 13 := rfl
  have e1 : slopeOrbit 1651 13 1 = 13 :=
    slopeOrbit_step_eval 0 6 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1651 13 2 = 13 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1651 13 2 = slopeOrbit 1651 13 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1651,13)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1651_13 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1651)
    (hK : (class1SlopeDatum ctx).K₀ = 13) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1651_13.1) elcCert_1651_13.2 i hi

/-- `(1651,26)`: period `1`, cycle `[13]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1651_26 :
    slopeOrbit 1651 26 (1 + 1) = slopeOrbit 1651 26 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1651 26 j ≤ 1651 := by
  have e0 : slopeOrbit 1651 26 0 = 26 := rfl
  have e1 : slopeOrbit 1651 26 1 = 13 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1651 26 2 = 13 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1651 26 2 = slopeOrbit 1651 26 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1651,26)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1651_26 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1651)
    (hK : (class1SlopeDatum ctx).K₀ = 26) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1651_26.1) elcCert_1651_26.2 i hi

/-- `(1651,52)`: period `1`, cycle `[13]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1651_52 :
    slopeOrbit 1651 52 (1 + 1) = slopeOrbit 1651 52 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1651 52 j ≤ 1651 := by
  have e0 : slopeOrbit 1651 52 0 = 52 := rfl
  have e1 : slopeOrbit 1651 52 1 = 13 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1651 52 2 = 13 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1651 52 2 = slopeOrbit 1651 52 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1651,52)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1651_52 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1651)
    (hK : (class1SlopeDatum ctx).K₀ = 52) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1651_52.1) elcCert_1651_52.2 i hi

/-- `(1651,104)`: period `1`, cycle `[13]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1651_104 :
    slopeOrbit 1651 104 (1 + 1) = slopeOrbit 1651 104 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1651 104 j ≤ 1651 := by
  have e0 : slopeOrbit 1651 104 0 = 104 := rfl
  have e1 : slopeOrbit 1651 104 1 = 13 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1651 104 2 = 13 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1651 104 2 = slopeOrbit 1651 104 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1651,104)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1651_104 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1651)
    (hK : (class1SlopeDatum ctx).K₀ = 104) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1651_104.1) elcCert_1651_104.2 i hi

/-- `(1651,208)`: period `1`, cycle `[13]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1651_208 :
    slopeOrbit 1651 208 (1 + 1) = slopeOrbit 1651 208 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1651 208 j ≤ 1651 := by
  have e0 : slopeOrbit 1651 208 0 = 208 := rfl
  have e1 : slopeOrbit 1651 208 1 = 13 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1651 208 2 = 13 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1651 208 2 = slopeOrbit 1651 208 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1651,208)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1651_208 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1651)
    (hK : (class1SlopeDatum ctx).K₀ = 208) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1651_208.1) elcCert_1651_208.2 i hi

/-- `(1651,416)`: period `1`, cycle `[13]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1651_416 :
    slopeOrbit 1651 416 (1 + 1) = slopeOrbit 1651 416 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1651 416 j ≤ 1651 := by
  have e0 : slopeOrbit 1651 416 0 = 416 := rfl
  have e1 : slopeOrbit 1651 416 1 = 13 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1651 416 2 = 13 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1651 416 2 = slopeOrbit 1651 416 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1651,416)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1651_416 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1651)
    (hK : (class1SlopeDatum ctx).K₀ = 416) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1651_416.1) elcCert_1651_416.2 i hi

/-- `(1651,832)`: period `1`, cycle `[13]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1651_832 :
    slopeOrbit 1651 832 (1 + 1) = slopeOrbit 1651 832 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1651 832 j ≤ 1651 := by
  have e0 : slopeOrbit 1651 832 0 = 832 := rfl
  have e1 : slopeOrbit 1651 832 1 = 13 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1651 832 2 = 13 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1651 832 2 = slopeOrbit 1651 832 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1651,832)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1651_832 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1651)
    (hK : (class1SlopeDatum ctx).K₀ = 832) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1651_832.1) elcCert_1651_832.2 i hi

/-- `(1701,27)`: period `1`, cycle `[27]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1701_27 :
    slopeOrbit 1701 27 (1 + 1) = slopeOrbit 1701 27 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1701 27 j ≤ 1701 := by
  have e0 : slopeOrbit 1701 27 0 = 27 := rfl
  have e1 : slopeOrbit 1701 27 1 = 27 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1701 27 2 = 27 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1701 27 2 = slopeOrbit 1701 27 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1701,27)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1701_27 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1701)
    (hK : (class1SlopeDatum ctx).K₀ = 27) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1701_27.1) elcCert_1701_27.2 i hi

/-- `(1701,54)`: period `1`, cycle `[27]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1701_54 :
    slopeOrbit 1701 54 (1 + 1) = slopeOrbit 1701 54 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1701 54 j ≤ 1701 := by
  have e0 : slopeOrbit 1701 54 0 = 54 := rfl
  have e1 : slopeOrbit 1701 54 1 = 27 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1701 54 2 = 27 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1701 54 2 = slopeOrbit 1701 54 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1701,54)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1701_54 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1701)
    (hK : (class1SlopeDatum ctx).K₀ = 54) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1701_54.1) elcCert_1701_54.2 i hi

/-- `(1701,108)`: period `1`, cycle `[27]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1701_108 :
    slopeOrbit 1701 108 (1 + 1) = slopeOrbit 1701 108 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1701 108 j ≤ 1701 := by
  have e0 : slopeOrbit 1701 108 0 = 108 := rfl
  have e1 : slopeOrbit 1701 108 1 = 27 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1701 108 2 = 27 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1701 108 2 = slopeOrbit 1701 108 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1701,108)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1701_108 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1701)
    (hK : (class1SlopeDatum ctx).K₀ = 108) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1701_108.1) elcCert_1701_108.2 i hi

/-- `(1701,216)`: period `1`, cycle `[27]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1701_216 :
    slopeOrbit 1701 216 (1 + 1) = slopeOrbit 1701 216 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1701 216 j ≤ 1701 := by
  have e0 : slopeOrbit 1701 216 0 = 216 := rfl
  have e1 : slopeOrbit 1701 216 1 = 27 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1701 216 2 = 27 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1701 216 2 = slopeOrbit 1701 216 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1701,216)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1701_216 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1701)
    (hK : (class1SlopeDatum ctx).K₀ = 216) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1701_216.1) elcCert_1701_216.2 i hi

/-- `(1701,432)`: period `1`, cycle `[27]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1701_432 :
    slopeOrbit 1701 432 (1 + 1) = slopeOrbit 1701 432 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1701 432 j ≤ 1701 := by
  have e0 : slopeOrbit 1701 432 0 = 432 := rfl
  have e1 : slopeOrbit 1701 432 1 = 27 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1701 432 2 = 27 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1701 432 2 = slopeOrbit 1701 432 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1701,432)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1701_432 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1701)
    (hK : (class1SlopeDatum ctx).K₀ = 432) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1701_432.1) elcCert_1701_432.2 i hi

/-- `(1701,864)`: period `1`, cycle `[27]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1701_864 :
    slopeOrbit 1701 864 (1 + 1) = slopeOrbit 1701 864 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1701 864 j ≤ 1701 := by
  have e0 : slopeOrbit 1701 864 0 = 864 := rfl
  have e1 : slopeOrbit 1701 864 1 = 27 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1701 864 2 = 27 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1701 864 2 = slopeOrbit 1701 864 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1701,864)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1701_864 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1701)
    (hK : (class1SlopeDatum ctx).K₀ = 864) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1701_864.1) elcCert_1701_864.2 i hi

/-- `(1705,55)`: period `1`, cycle `[55]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1705_55 :
    slopeOrbit 1705 55 (1 + 1) = slopeOrbit 1705 55 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1705 55 j ≤ 1705 := by
  have e0 : slopeOrbit 1705 55 0 = 55 := rfl
  have e1 : slopeOrbit 1705 55 1 = 55 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1705 55 2 = 55 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1705 55 2 = slopeOrbit 1705 55 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1705,55)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1705_55 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1705)
    (hK : (class1SlopeDatum ctx).K₀ = 55) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1705_55.1) elcCert_1705_55.2 i hi

/-- `(1705,110)`: period `1`, cycle `[55]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1705_110 :
    slopeOrbit 1705 110 (1 + 1) = slopeOrbit 1705 110 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1705 110 j ≤ 1705 := by
  have e0 : slopeOrbit 1705 110 0 = 110 := rfl
  have e1 : slopeOrbit 1705 110 1 = 55 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1705 110 2 = 55 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1705 110 2 = slopeOrbit 1705 110 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1705,110)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1705_110 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1705)
    (hK : (class1SlopeDatum ctx).K₀ = 110) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1705_110.1) elcCert_1705_110.2 i hi

/-- `(1705,220)`: period `1`, cycle `[55]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1705_220 :
    slopeOrbit 1705 220 (1 + 1) = slopeOrbit 1705 220 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1705 220 j ≤ 1705 := by
  have e0 : slopeOrbit 1705 220 0 = 220 := rfl
  have e1 : slopeOrbit 1705 220 1 = 55 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1705 220 2 = 55 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1705 220 2 = slopeOrbit 1705 220 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1705,220)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1705_220 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1705)
    (hK : (class1SlopeDatum ctx).K₀ = 220) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1705_220.1) elcCert_1705_220.2 i hi

/-- `(1705,440)`: period `1`, cycle `[55]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1705_440 :
    slopeOrbit 1705 440 (1 + 1) = slopeOrbit 1705 440 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1705 440 j ≤ 1705 := by
  have e0 : slopeOrbit 1705 440 0 = 440 := rfl
  have e1 : slopeOrbit 1705 440 1 = 55 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1705 440 2 = 55 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1705 440 2 = slopeOrbit 1705 440 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1705,440)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1705_440 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1705)
    (hK : (class1SlopeDatum ctx).K₀ = 440) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1705_440.1) elcCert_1705_440.2 i hi

/-- `(1705,880)`: period `1`, cycle `[55]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1705_880 :
    slopeOrbit 1705 880 (1 + 1) = slopeOrbit 1705 880 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1705 880 j ≤ 1705 := by
  have e0 : slopeOrbit 1705 880 0 = 880 := rfl
  have e1 : slopeOrbit 1705 880 1 = 55 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1705 880 2 = 55 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1705 880 2 = slopeOrbit 1705 880 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1705,880)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1705_880 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1705)
    (hK : (class1SlopeDatum ctx).K₀ = 880) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1705_880.1) elcCert_1705_880.2 i hi

/-- `(1767,57)`: period `1`, cycle `[57]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1767_57 :
    slopeOrbit 1767 57 (1 + 1) = slopeOrbit 1767 57 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1767 57 j ≤ 1767 := by
  have e0 : slopeOrbit 1767 57 0 = 57 := rfl
  have e1 : slopeOrbit 1767 57 1 = 57 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1767 57 2 = 57 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1767 57 2 = slopeOrbit 1767 57 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1767,57)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1767_57 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1767)
    (hK : (class1SlopeDatum ctx).K₀ = 57) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1767_57.1) elcCert_1767_57.2 i hi

/-- `(1767,114)`: period `1`, cycle `[57]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1767_114 :
    slopeOrbit 1767 114 (1 + 1) = slopeOrbit 1767 114 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1767 114 j ≤ 1767 := by
  have e0 : slopeOrbit 1767 114 0 = 114 := rfl
  have e1 : slopeOrbit 1767 114 1 = 57 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1767 114 2 = 57 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1767 114 2 = slopeOrbit 1767 114 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1767,114)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1767_114 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1767)
    (hK : (class1SlopeDatum ctx).K₀ = 114) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1767_114.1) elcCert_1767_114.2 i hi

/-- `(1767,228)`: period `1`, cycle `[57]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1767_228 :
    slopeOrbit 1767 228 (1 + 1) = slopeOrbit 1767 228 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1767 228 j ≤ 1767 := by
  have e0 : slopeOrbit 1767 228 0 = 228 := rfl
  have e1 : slopeOrbit 1767 228 1 = 57 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1767 228 2 = 57 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1767 228 2 = slopeOrbit 1767 228 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1767,228)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1767_228 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1767)
    (hK : (class1SlopeDatum ctx).K₀ = 228) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1767_228.1) elcCert_1767_228.2 i hi

/-- `(1767,456)`: period `1`, cycle `[57]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1767_456 :
    slopeOrbit 1767 456 (1 + 1) = slopeOrbit 1767 456 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1767 456 j ≤ 1767 := by
  have e0 : slopeOrbit 1767 456 0 = 456 := rfl
  have e1 : slopeOrbit 1767 456 1 = 57 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1767 456 2 = 57 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1767 456 2 = slopeOrbit 1767 456 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1767,456)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1767_456 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1767)
    (hK : (class1SlopeDatum ctx).K₀ = 456) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1767_456.1) elcCert_1767_456.2 i hi

/-- `(1767,912)`: period `1`, cycle `[57]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1767_912 :
    slopeOrbit 1767 912 (1 + 1) = slopeOrbit 1767 912 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1767 912 j ≤ 1767 := by
  have e0 : slopeOrbit 1767 912 0 = 912 := rfl
  have e1 : slopeOrbit 1767 912 1 = 57 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1767 912 2 = 57 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1767 912 2 = slopeOrbit 1767 912 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1767,912)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1767_912 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1767)
    (hK : (class1SlopeDatum ctx).K₀ = 912) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1767_912.1) elcCert_1767_912.2 i hi

/-- `(1785,7)`: period `1`, cycle `[7]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1785_7 :
    slopeOrbit 1785 7 (1 + 1) = slopeOrbit 1785 7 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1785 7 j ≤ 1785 := by
  have e0 : slopeOrbit 1785 7 0 = 7 := rfl
  have e1 : slopeOrbit 1785 7 1 = 7 :=
    slopeOrbit_step_eval 0 7 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1785 7 2 = 7 :=
    slopeOrbit_step_eval 1 7 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1785 7 2 = slopeOrbit 1785 7 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1785,7)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1785_7 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1785)
    (hK : (class1SlopeDatum ctx).K₀ = 7) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1785_7.1) elcCert_1785_7.2 i hi

/-- `(1785,14)`: period `1`, cycle `[7]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1785_14 :
    slopeOrbit 1785 14 (1 + 1) = slopeOrbit 1785 14 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1785 14 j ≤ 1785 := by
  have e0 : slopeOrbit 1785 14 0 = 14 := rfl
  have e1 : slopeOrbit 1785 14 1 = 7 :=
    slopeOrbit_step_eval 0 6 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1785 14 2 = 7 :=
    slopeOrbit_step_eval 1 7 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1785 14 2 = slopeOrbit 1785 14 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1785,14)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1785_14 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1785)
    (hK : (class1SlopeDatum ctx).K₀ = 14) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1785_14.1) elcCert_1785_14.2 i hi

/-- `(1785,28)`: period `1`, cycle `[7]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1785_28 :
    slopeOrbit 1785 28 (1 + 1) = slopeOrbit 1785 28 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1785 28 j ≤ 1785 := by
  have e0 : slopeOrbit 1785 28 0 = 28 := rfl
  have e1 : slopeOrbit 1785 28 1 = 7 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1785 28 2 = 7 :=
    slopeOrbit_step_eval 1 7 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1785 28 2 = slopeOrbit 1785 28 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1785,28)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1785_28 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1785)
    (hK : (class1SlopeDatum ctx).K₀ = 28) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1785_28.1) elcCert_1785_28.2 i hi

/-- `(1785,56)`: period `1`, cycle `[7]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1785_56 :
    slopeOrbit 1785 56 (1 + 1) = slopeOrbit 1785 56 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1785 56 j ≤ 1785 := by
  have e0 : slopeOrbit 1785 56 0 = 56 := rfl
  have e1 : slopeOrbit 1785 56 1 = 7 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1785 56 2 = 7 :=
    slopeOrbit_step_eval 1 7 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1785 56 2 = slopeOrbit 1785 56 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1785,56)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1785_56 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1785)
    (hK : (class1SlopeDatum ctx).K₀ = 56) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1785_56.1) elcCert_1785_56.2 i hi

/-- `(1785,112)`: period `1`, cycle `[7]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1785_112 :
    slopeOrbit 1785 112 (1 + 1) = slopeOrbit 1785 112 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1785 112 j ≤ 1785 := by
  have e0 : slopeOrbit 1785 112 0 = 112 := rfl
  have e1 : slopeOrbit 1785 112 1 = 7 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1785 112 2 = 7 :=
    slopeOrbit_step_eval 1 7 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1785 112 2 = slopeOrbit 1785 112 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1785,112)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1785_112 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1785)
    (hK : (class1SlopeDatum ctx).K₀ = 112) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1785_112.1) elcCert_1785_112.2 i hi

/-- `(1785,224)`: period `1`, cycle `[7]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1785_224 :
    slopeOrbit 1785 224 (1 + 1) = slopeOrbit 1785 224 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1785 224 j ≤ 1785 := by
  have e0 : slopeOrbit 1785 224 0 = 224 := rfl
  have e1 : slopeOrbit 1785 224 1 = 7 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1785 224 2 = 7 :=
    slopeOrbit_step_eval 1 7 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1785 224 2 = slopeOrbit 1785 224 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1785,224)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1785_224 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1785)
    (hK : (class1SlopeDatum ctx).K₀ = 224) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1785_224.1) elcCert_1785_224.2 i hi

/-- `(1785,448)`: period `1`, cycle `[7]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1785_448 :
    slopeOrbit 1785 448 (1 + 1) = slopeOrbit 1785 448 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1785 448 j ≤ 1785 := by
  have e0 : slopeOrbit 1785 448 0 = 448 := rfl
  have e1 : slopeOrbit 1785 448 1 = 7 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1785 448 2 = 7 :=
    slopeOrbit_step_eval 1 7 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1785 448 2 = slopeOrbit 1785 448 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1785,448)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1785_448 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1785)
    (hK : (class1SlopeDatum ctx).K₀ = 448) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1785_448.1) elcCert_1785_448.2 i hi

/-- `(1785,896)`: period `1`, cycle `[7]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1785_896 :
    slopeOrbit 1785 896 (1 + 1) = slopeOrbit 1785 896 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1785 896 j ≤ 1785 := by
  have e0 : slopeOrbit 1785 896 0 = 896 := rfl
  have e1 : slopeOrbit 1785 896 1 = 7 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1785 896 2 = 7 :=
    slopeOrbit_step_eval 1 7 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1785 896 2 = slopeOrbit 1785 896 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1785,896)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1785_896 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1785)
    (hK : (class1SlopeDatum ctx).K₀ = 896) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1785_896.1) elcCert_1785_896.2 i hi

/-- `(1827,29)`: period `1`, cycle `[29]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1827_29 :
    slopeOrbit 1827 29 (1 + 1) = slopeOrbit 1827 29 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1827 29 j ≤ 1827 := by
  have e0 : slopeOrbit 1827 29 0 = 29 := rfl
  have e1 : slopeOrbit 1827 29 1 = 29 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1827 29 2 = 29 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1827 29 2 = slopeOrbit 1827 29 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1827,29)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1827_29 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1827)
    (hK : (class1SlopeDatum ctx).K₀ = 29) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1827_29.1) elcCert_1827_29.2 i hi

/-- `(1827,58)`: period `1`, cycle `[29]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1827_58 :
    slopeOrbit 1827 58 (1 + 1) = slopeOrbit 1827 58 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1827 58 j ≤ 1827 := by
  have e0 : slopeOrbit 1827 58 0 = 58 := rfl
  have e1 : slopeOrbit 1827 58 1 = 29 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1827 58 2 = 29 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1827 58 2 = slopeOrbit 1827 58 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1827,58)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1827_58 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1827)
    (hK : (class1SlopeDatum ctx).K₀ = 58) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1827_58.1) elcCert_1827_58.2 i hi

/-- `(1827,116)`: period `1`, cycle `[29]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1827_116 :
    slopeOrbit 1827 116 (1 + 1) = slopeOrbit 1827 116 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1827 116 j ≤ 1827 := by
  have e0 : slopeOrbit 1827 116 0 = 116 := rfl
  have e1 : slopeOrbit 1827 116 1 = 29 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1827 116 2 = 29 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1827 116 2 = slopeOrbit 1827 116 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1827,116)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1827_116 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1827)
    (hK : (class1SlopeDatum ctx).K₀ = 116) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1827_116.1) elcCert_1827_116.2 i hi

/-- `(1827,232)`: period `1`, cycle `[29]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1827_232 :
    slopeOrbit 1827 232 (1 + 1) = slopeOrbit 1827 232 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1827 232 j ≤ 1827 := by
  have e0 : slopeOrbit 1827 232 0 = 232 := rfl
  have e1 : slopeOrbit 1827 232 1 = 29 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1827 232 2 = 29 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1827 232 2 = slopeOrbit 1827 232 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1827,232)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1827_232 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1827)
    (hK : (class1SlopeDatum ctx).K₀ = 232) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1827_232.1) elcCert_1827_232.2 i hi

/-- `(1827,464)`: period `1`, cycle `[29]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1827_464 :
    slopeOrbit 1827 464 (1 + 1) = slopeOrbit 1827 464 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1827 464 j ≤ 1827 := by
  have e0 : slopeOrbit 1827 464 0 = 464 := rfl
  have e1 : slopeOrbit 1827 464 1 = 29 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1827 464 2 = 29 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1827 464 2 = slopeOrbit 1827 464 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1827,464)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1827_464 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1827)
    (hK : (class1SlopeDatum ctx).K₀ = 464) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1827_464.1) elcCert_1827_464.2 i hi

/-- `(1827,928)`: period `1`, cycle `[29]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1827_928 :
    slopeOrbit 1827 928 (1 + 1) = slopeOrbit 1827 928 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1827 928 j ≤ 1827 := by
  have e0 : slopeOrbit 1827 928 0 = 928 := rfl
  have e1 : slopeOrbit 1827 928 1 = 29 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1827 928 2 = 29 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1827 928 2 = slopeOrbit 1827 928 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1827,928)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1827_928 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1827)
    (hK : (class1SlopeDatum ctx).K₀ = 928) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1827_928.1) elcCert_1827_928.2 i hi

/-- `(1829,59)`: period `1`, cycle `[59]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1829_59 :
    slopeOrbit 1829 59 (1 + 1) = slopeOrbit 1829 59 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1829 59 j ≤ 1829 := by
  have e0 : slopeOrbit 1829 59 0 = 59 := rfl
  have e1 : slopeOrbit 1829 59 1 = 59 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1829 59 2 = 59 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1829 59 2 = slopeOrbit 1829 59 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1829,59)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1829_59 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1829)
    (hK : (class1SlopeDatum ctx).K₀ = 59) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1829_59.1) elcCert_1829_59.2 i hi

/-- `(1829,118)`: period `1`, cycle `[59]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1829_118 :
    slopeOrbit 1829 118 (1 + 1) = slopeOrbit 1829 118 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1829 118 j ≤ 1829 := by
  have e0 : slopeOrbit 1829 118 0 = 118 := rfl
  have e1 : slopeOrbit 1829 118 1 = 59 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1829 118 2 = 59 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1829 118 2 = slopeOrbit 1829 118 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1829,118)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1829_118 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1829)
    (hK : (class1SlopeDatum ctx).K₀ = 118) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1829_118.1) elcCert_1829_118.2 i hi

/-- `(1829,236)`: period `1`, cycle `[59]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1829_236 :
    slopeOrbit 1829 236 (1 + 1) = slopeOrbit 1829 236 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1829 236 j ≤ 1829 := by
  have e0 : slopeOrbit 1829 236 0 = 236 := rfl
  have e1 : slopeOrbit 1829 236 1 = 59 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1829 236 2 = 59 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1829 236 2 = slopeOrbit 1829 236 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1829,236)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1829_236 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1829)
    (hK : (class1SlopeDatum ctx).K₀ = 236) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1829_236.1) elcCert_1829_236.2 i hi

/-- `(1829,472)`: period `1`, cycle `[59]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1829_472 :
    slopeOrbit 1829 472 (1 + 1) = slopeOrbit 1829 472 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1829 472 j ≤ 1829 := by
  have e0 : slopeOrbit 1829 472 0 = 472 := rfl
  have e1 : slopeOrbit 1829 472 1 = 59 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1829 472 2 = 59 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1829 472 2 = slopeOrbit 1829 472 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1829,472)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1829_472 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1829)
    (hK : (class1SlopeDatum ctx).K₀ = 472) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1829_472.1) elcCert_1829_472.2 i hi

/-- `(1829,944)`: period `1`, cycle `[59]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1829_944 :
    slopeOrbit 1829 944 (1 + 1) = slopeOrbit 1829 944 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1829 944 j ≤ 1829 := by
  have e0 : slopeOrbit 1829 944 0 = 944 := rfl
  have e1 : slopeOrbit 1829 944 1 = 59 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1829 944 2 = 59 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1829 944 2 = slopeOrbit 1829 944 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1829,944)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1829_944 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1829)
    (hK : (class1SlopeDatum ctx).K₀ = 944) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1829_944.1) elcCert_1829_944.2 i hi

/-- `(1891,61)`: period `1`, cycle `[61]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1891_61 :
    slopeOrbit 1891 61 (1 + 1) = slopeOrbit 1891 61 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1891 61 j ≤ 1891 := by
  have e0 : slopeOrbit 1891 61 0 = 61 := rfl
  have e1 : slopeOrbit 1891 61 1 = 61 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1891 61 2 = 61 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1891 61 2 = slopeOrbit 1891 61 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1891,61)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1891_61 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1891)
    (hK : (class1SlopeDatum ctx).K₀ = 61) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1891_61.1) elcCert_1891_61.2 i hi

/-- `(1891,122)`: period `1`, cycle `[61]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1891_122 :
    slopeOrbit 1891 122 (1 + 1) = slopeOrbit 1891 122 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1891 122 j ≤ 1891 := by
  have e0 : slopeOrbit 1891 122 0 = 122 := rfl
  have e1 : slopeOrbit 1891 122 1 = 61 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1891 122 2 = 61 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1891 122 2 = slopeOrbit 1891 122 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1891,122)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1891_122 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1891)
    (hK : (class1SlopeDatum ctx).K₀ = 122) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1891_122.1) elcCert_1891_122.2 i hi

/-- `(1891,244)`: period `1`, cycle `[61]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1891_244 :
    slopeOrbit 1891 244 (1 + 1) = slopeOrbit 1891 244 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1891 244 j ≤ 1891 := by
  have e0 : slopeOrbit 1891 244 0 = 244 := rfl
  have e1 : slopeOrbit 1891 244 1 = 61 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1891 244 2 = 61 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1891 244 2 = slopeOrbit 1891 244 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1891,244)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1891_244 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1891)
    (hK : (class1SlopeDatum ctx).K₀ = 244) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1891_244.1) elcCert_1891_244.2 i hi

/-- `(1891,488)`: period `1`, cycle `[61]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1891_488 :
    slopeOrbit 1891 488 (1 + 1) = slopeOrbit 1891 488 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1891 488 j ≤ 1891 := by
  have e0 : slopeOrbit 1891 488 0 = 488 := rfl
  have e1 : slopeOrbit 1891 488 1 = 61 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1891 488 2 = 61 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1891 488 2 = slopeOrbit 1891 488 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1891,488)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1891_488 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1891)
    (hK : (class1SlopeDatum ctx).K₀ = 488) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1891_488.1) elcCert_1891_488.2 i hi

/-- `(1891,976)`: period `1`, cycle `[61]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1891_976 :
    slopeOrbit 1891 976 (1 + 1) = slopeOrbit 1891 976 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1891 976 j ≤ 1891 := by
  have e0 : slopeOrbit 1891 976 0 = 976 := rfl
  have e1 : slopeOrbit 1891 976 1 = 61 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1891 976 2 = 61 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1891 976 2 = slopeOrbit 1891 976 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1891,976)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1891_976 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1891)
    (hK : (class1SlopeDatum ctx).K₀ = 976) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1891_976.1) elcCert_1891_976.2 i hi

/-- `(1905,15)`: period `1`, cycle `[15]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1905_15 :
    slopeOrbit 1905 15 (1 + 1) = slopeOrbit 1905 15 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1905 15 j ≤ 1905 := by
  have e0 : slopeOrbit 1905 15 0 = 15 := rfl
  have e1 : slopeOrbit 1905 15 1 = 15 :=
    slopeOrbit_step_eval 0 6 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1905 15 2 = 15 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1905 15 2 = slopeOrbit 1905 15 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1905,15)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1905_15 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1905)
    (hK : (class1SlopeDatum ctx).K₀ = 15) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1905_15.1) elcCert_1905_15.2 i hi

/-- `(1905,30)`: period `1`, cycle `[15]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1905_30 :
    slopeOrbit 1905 30 (1 + 1) = slopeOrbit 1905 30 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1905 30 j ≤ 1905 := by
  have e0 : slopeOrbit 1905 30 0 = 30 := rfl
  have e1 : slopeOrbit 1905 30 1 = 15 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1905 30 2 = 15 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1905 30 2 = slopeOrbit 1905 30 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1905,30)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1905_30 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1905)
    (hK : (class1SlopeDatum ctx).K₀ = 30) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1905_30.1) elcCert_1905_30.2 i hi

/-- `(1905,60)`: period `1`, cycle `[15]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1905_60 :
    slopeOrbit 1905 60 (1 + 1) = slopeOrbit 1905 60 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1905 60 j ≤ 1905 := by
  have e0 : slopeOrbit 1905 60 0 = 60 := rfl
  have e1 : slopeOrbit 1905 60 1 = 15 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1905 60 2 = 15 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1905 60 2 = slopeOrbit 1905 60 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1905,60)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1905_60 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1905)
    (hK : (class1SlopeDatum ctx).K₀ = 60) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1905_60.1) elcCert_1905_60.2 i hi

/-- `(1905,120)`: period `1`, cycle `[15]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1905_120 :
    slopeOrbit 1905 120 (1 + 1) = slopeOrbit 1905 120 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1905 120 j ≤ 1905 := by
  have e0 : slopeOrbit 1905 120 0 = 120 := rfl
  have e1 : slopeOrbit 1905 120 1 = 15 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1905 120 2 = 15 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1905 120 2 = slopeOrbit 1905 120 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1905,120)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1905_120 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1905)
    (hK : (class1SlopeDatum ctx).K₀ = 120) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1905_120.1) elcCert_1905_120.2 i hi

/-- `(1905,240)`: period `1`, cycle `[15]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1905_240 :
    slopeOrbit 1905 240 (1 + 1) = slopeOrbit 1905 240 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1905 240 j ≤ 1905 := by
  have e0 : slopeOrbit 1905 240 0 = 240 := rfl
  have e1 : slopeOrbit 1905 240 1 = 15 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1905 240 2 = 15 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1905 240 2 = slopeOrbit 1905 240 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1905,240)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1905_240 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1905)
    (hK : (class1SlopeDatum ctx).K₀ = 240) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1905_240.1) elcCert_1905_240.2 i hi

/-- `(1905,480)`: period `1`, cycle `[15]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1905_480 :
    slopeOrbit 1905 480 (1 + 1) = slopeOrbit 1905 480 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1905 480 j ≤ 1905 := by
  have e0 : slopeOrbit 1905 480 0 = 480 := rfl
  have e1 : slopeOrbit 1905 480 1 = 15 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1905 480 2 = 15 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1905 480 2 = slopeOrbit 1905 480 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1905,480)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1905_480 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1905)
    (hK : (class1SlopeDatum ctx).K₀ = 480) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1905_480.1) elcCert_1905_480.2 i hi

/-- `(1905,960)`: period `1`, cycle `[15]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1905_960 :
    slopeOrbit 1905 960 (1 + 1) = slopeOrbit 1905 960 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1905 960 j ≤ 1905 := by
  have e0 : slopeOrbit 1905 960 0 = 960 := rfl
  have e1 : slopeOrbit 1905 960 1 = 15 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1905 960 2 = 15 :=
    slopeOrbit_step_eval 1 6 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1905 960 2 = slopeOrbit 1905 960 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1905,960)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1905_960 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1905)
    (hK : (class1SlopeDatum ctx).K₀ = 960) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1905_960.1) elcCert_1905_960.2 i hi

/-- `(1953,31)`: period `1`, cycle `[31]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1953_31 :
    slopeOrbit 1953 31 (1 + 1) = slopeOrbit 1953 31 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1953 31 j ≤ 1953 := by
  have e0 : slopeOrbit 1953 31 0 = 31 := rfl
  have e1 : slopeOrbit 1953 31 1 = 31 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1953 31 2 = 31 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1953 31 2 = slopeOrbit 1953 31 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1953,31)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1953_31 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1953)
    (hK : (class1SlopeDatum ctx).K₀ = 31) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1953_31.1) elcCert_1953_31.2 i hi

/-- `(1953,62)`: period `1`, cycle `[31]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1953_62 :
    slopeOrbit 1953 62 (1 + 1) = slopeOrbit 1953 62 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1953 62 j ≤ 1953 := by
  have e0 : slopeOrbit 1953 62 0 = 62 := rfl
  have e1 : slopeOrbit 1953 62 1 = 31 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1953 62 2 = 31 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1953 62 2 = slopeOrbit 1953 62 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1953,62)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1953_62 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1953)
    (hK : (class1SlopeDatum ctx).K₀ = 62) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1953_62.1) elcCert_1953_62.2 i hi

/-- `(1953,63)`: period `1`, cycle `[63]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1953_63 :
    slopeOrbit 1953 63 (1 + 1) = slopeOrbit 1953 63 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1953 63 j ≤ 1953 := by
  have e0 : slopeOrbit 1953 63 0 = 63 := rfl
  have e1 : slopeOrbit 1953 63 1 = 63 :=
    slopeOrbit_step_eval 0 4 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1953 63 2 = 63 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1953 63 2 = slopeOrbit 1953 63 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1953,63)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1953_63 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1953)
    (hK : (class1SlopeDatum ctx).K₀ = 63) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1953_63.1) elcCert_1953_63.2 i hi

/-- `(1953,124)`: period `1`, cycle `[31]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1953_124 :
    slopeOrbit 1953 124 (1 + 1) = slopeOrbit 1953 124 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1953 124 j ≤ 1953 := by
  have e0 : slopeOrbit 1953 124 0 = 124 := rfl
  have e1 : slopeOrbit 1953 124 1 = 31 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1953 124 2 = 31 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1953 124 2 = slopeOrbit 1953 124 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1953,124)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1953_124 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1953)
    (hK : (class1SlopeDatum ctx).K₀ = 124) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1953_124.1) elcCert_1953_124.2 i hi

/-- `(1953,126)`: period `1`, cycle `[63]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1953_126 :
    slopeOrbit 1953 126 (1 + 1) = slopeOrbit 1953 126 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1953 126 j ≤ 1953 := by
  have e0 : slopeOrbit 1953 126 0 = 126 := rfl
  have e1 : slopeOrbit 1953 126 1 = 63 :=
    slopeOrbit_step_eval 0 3 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1953 126 2 = 63 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1953 126 2 = slopeOrbit 1953 126 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1953,126)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1953_126 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1953)
    (hK : (class1SlopeDatum ctx).K₀ = 126) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1953_126.1) elcCert_1953_126.2 i hi

/-- `(1953,248)`: period `1`, cycle `[31]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1953_248 :
    slopeOrbit 1953 248 (1 + 1) = slopeOrbit 1953 248 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1953 248 j ≤ 1953 := by
  have e0 : slopeOrbit 1953 248 0 = 248 := rfl
  have e1 : slopeOrbit 1953 248 1 = 31 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1953 248 2 = 31 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1953 248 2 = slopeOrbit 1953 248 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1953,248)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1953_248 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1953)
    (hK : (class1SlopeDatum ctx).K₀ = 248) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1953_248.1) elcCert_1953_248.2 i hi

/-- `(1953,252)`: period `1`, cycle `[63]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1953_252 :
    slopeOrbit 1953 252 (1 + 1) = slopeOrbit 1953 252 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1953 252 j ≤ 1953 := by
  have e0 : slopeOrbit 1953 252 0 = 252 := rfl
  have e1 : slopeOrbit 1953 252 1 = 63 :=
    slopeOrbit_step_eval 0 2 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1953 252 2 = 63 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1953 252 2 = slopeOrbit 1953 252 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1953,252)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1953_252 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1953)
    (hK : (class1SlopeDatum ctx).K₀ = 252) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1953_252.1) elcCert_1953_252.2 i hi

/-- `(1953,496)`: period `1`, cycle `[31]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1953_496 :
    slopeOrbit 1953 496 (1 + 1) = slopeOrbit 1953 496 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1953 496 j ≤ 1953 := by
  have e0 : slopeOrbit 1953 496 0 = 496 := rfl
  have e1 : slopeOrbit 1953 496 1 = 31 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1953 496 2 = 31 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1953 496 2 = slopeOrbit 1953 496 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1953,496)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1953_496 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1953)
    (hK : (class1SlopeDatum ctx).K₀ = 496) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1953_496.1) elcCert_1953_496.2 i hi

/-- `(1953,504)`: period `1`, cycle `[63]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1953_504 :
    slopeOrbit 1953 504 (1 + 1) = slopeOrbit 1953 504 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1953 504 j ≤ 1953 := by
  have e0 : slopeOrbit 1953 504 0 = 504 := rfl
  have e1 : slopeOrbit 1953 504 1 = 63 :=
    slopeOrbit_step_eval 0 1 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1953 504 2 = 63 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1953 504 2 = slopeOrbit 1953 504 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1953,504)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1953_504 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1953)
    (hK : (class1SlopeDatum ctx).K₀ = 504) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1953_504.1) elcCert_1953_504.2 i hi

/-- `(1953,992)`: period `1`, cycle `[31]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1953_992 :
    slopeOrbit 1953 992 (1 + 1) = slopeOrbit 1953 992 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1953 992 j ≤ 1953 := by
  have e0 : slopeOrbit 1953 992 0 = 992 := rfl
  have e1 : slopeOrbit 1953 992 1 = 31 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1953 992 2 = 31 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1953 992 2 = slopeOrbit 1953 992 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1953,992)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1953_992 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1953)
    (hK : (class1SlopeDatum ctx).K₀ = 992) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1953_992.1) elcCert_1953_992.2 i hi

/-- `(1953,1008)`: period `1`, cycle `[63]`, all bands deep (`≥ 5`). -/
private theorem elcCert_1953_1008 :
    slopeOrbit 1953 1008 (1 + 1) = slopeOrbit 1953 1008 1
      ∧ ∀ j, 1 ≤ j → j ≤ 1 → 16 * slopeOrbit 1953 1008 j ≤ 1953 := by
  have e0 : slopeOrbit 1953 1008 0 = 1008 := rfl
  have e1 : slopeOrbit 1953 1008 1 = 63 :=
    slopeOrbit_step_eval 0 0 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1953 1008 2 = 63 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1953 1008 2 = slopeOrbit 1953 1008 1
    rw [e2, e1]
  · intro j h1 h2
    interval_cases j
    · rw [e1]
      norm_num

/-- `(1953,1008)` is exit-silent: every nonzero-class fibre is empty at its data. -/
theorem elcSilent_1953_1008 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 1953)
    (hK : (class1SlopeDatum ctx).K₀ = 1008) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ :=
  fun i hi => elcFibreEmpty_of_deepCert ctx hq hK (by norm_num)
    (slopeOrbit_period_of_return elcCert_1953_1008.1) elcCert_1953_1008.2 i hi

/-! ## Part 2.  The exit-silent table and the dispatchers -/

/-- Exit-silent table, chunk 1 of 4 (`(q, K₀, c)`). -/
def elcExitSilentTable1 : List (ℕ × ℕ × ℕ) := [ (31, 1, 1), (31, 2, 1), (31, 4, 1), (31, 8, 1),
   (31, 16, 1), (63, 1, 1), (63, 2, 1), (63, 4, 1), (63, 8, 1), (63, 16, 1), (63, 32, 1),
   (93, 3, 1), (93, 6, 1), (93, 12, 1), (93, 24, 1), (93, 48, 1), (127, 1, 1), (127, 2, 1),
   (127, 4, 1), (127, 8, 1), (127, 16, 1), (127, 32, 1), (127, 64, 1), (155, 5, 1), (155, 10, 1),
   (155, 20, 1), (155, 40, 1), (155, 80, 1), (189, 3, 1), (189, 6, 1), (189, 12, 1), (189, 24, 1),
   (189, 48, 1), (189, 96, 1), (217, 7, 1), (217, 14, 1), (217, 28, 1), (217, 56, 1),
   (217, 112, 1), (255, 1, 1), (255, 2, 1), (255, 4, 1), (255, 8, 1), (255, 16, 1), (255, 32, 1),
   (255, 64, 1), (255, 128, 1), (279, 9, 1), (279, 18, 1), (279, 36, 1), (279, 72, 1),
   (279, 144, 1), (315, 5, 1), (315, 10, 1), (315, 20, 1), (315, 40, 1), (315, 80, 1),
   (315, 160, 1), (341, 11, 1), (341, 22, 1), (341, 44, 1), (341, 88, 1), (341, 176, 1),
   (381, 3, 1), (381, 6, 1), (381, 12, 1), (381, 24, 1), (381, 48, 1), (381, 96, 1),
   (381, 192, 1), (403, 13, 1), (403, 26, 1), (403, 52, 1), (403, 104, 1), (403, 208, 1),
   (441, 7, 1), (441, 14, 1), (441, 28, 1), (441, 56, 1), (441, 112, 1), (441, 224, 1),
   (465, 15, 1), (465, 30, 1), (465, 60, 1), (465, 120, 1), (465, 240, 1), (511, 1, 1),
   (511, 2, 1), (511, 4, 1), (511, 8, 1), (511, 16, 1), (511, 32, 1), (511, 64, 1), (511, 128, 1),
   (511, 256, 1), (527, 17, 1)]

/-- Exit-silent table, chunk 2 of 4 (`(q, K₀, c)`). -/
def elcExitSilentTable2 : List (ℕ × ℕ × ℕ) := [ (527, 34, 1), (527, 68, 1), (527, 136, 1),
   (527, 272, 1), (567, 9, 1), (567, 18, 1), (567, 36, 1), (567, 72, 1), (567, 144, 1),
   (567, 288, 1), (589, 19, 1), (589, 38, 1), (589, 76, 1), (589, 152, 1), (589, 304, 1),
   (635, 5, 1), (635, 10, 1), (635, 20, 1), (635, 40, 1), (635, 80, 1), (635, 160, 1),
   (635, 320, 1), (651, 21, 1), (651, 42, 1), (651, 84, 1), (651, 168, 1), (651, 336, 1),
   (693, 11, 1), (693, 22, 1), (693, 44, 1), (693, 88, 1), (693, 176, 1), (693, 352, 1),
   (713, 23, 1), (713, 46, 1), (713, 92, 1), (713, 184, 1), (713, 368, 1), (765, 3, 1),
   (765, 6, 1), (765, 12, 1), (765, 24, 1), (765, 48, 1), (765, 96, 1), (765, 192, 1),
   (765, 384, 1), (775, 25, 1), (775, 50, 1), (775, 100, 1), (775, 200, 1), (775, 400, 1),
   (819, 13, 1), (819, 26, 1), (819, 52, 1), (819, 104, 1), (819, 208, 1), (819, 416, 1),
   (837, 27, 1), (837, 54, 1), (837, 108, 1), (837, 216, 1), (837, 432, 1), (889, 7, 1),
   (889, 14, 1), (889, 28, 1), (889, 56, 1), (889, 112, 1), (889, 224, 1), (889, 448, 1),
   (899, 29, 1), (899, 58, 1), (899, 116, 1), (899, 232, 1), (899, 464, 1), (945, 15, 1),
   (945, 30, 1), (945, 60, 1), (945, 120, 1), (945, 240, 1), (945, 480, 1), (961, 31, 1),
   (961, 62, 1), (961, 124, 1), (961, 248, 1), (961, 496, 1), (1023, 1, 1), (1023, 2, 1),
   (1023, 4, 1), (1023, 8, 1), (1023, 16, 1), (1023, 32, 1), (1023, 33, 1), (1023, 64, 1),
   (1023, 66, 1), (1023, 128, 1), (1023, 132, 1)]

/-- Exit-silent table, chunk 3 of 4 (`(q, K₀, c)`). -/
def elcExitSilentTable3 : List (ℕ × ℕ × ℕ) := [ (1023, 256, 1), (1023, 264, 1), (1023, 512, 1),
   (1023, 528, 1), (1071, 17, 1), (1071, 34, 1), (1071, 68, 1), (1071, 136, 1), (1071, 272, 1),
   (1071, 544, 1), (1085, 35, 1), (1085, 70, 1), (1085, 140, 1), (1085, 280, 1), (1085, 560, 1),
   (1143, 9, 1), (1143, 18, 1), (1143, 36, 1), (1143, 72, 1), (1143, 144, 1), (1143, 288, 1),
   (1143, 576, 1), (1147, 37, 1), (1147, 74, 1), (1147, 148, 1), (1147, 296, 1), (1147, 592, 1),
   (1197, 19, 1), (1197, 38, 1), (1197, 76, 1), (1197, 152, 1), (1197, 304, 1), (1197, 608, 1),
   (1209, 39, 1), (1209, 78, 1), (1209, 156, 1), (1209, 312, 1), (1209, 624, 1), (1271, 41, 1),
   (1271, 82, 1), (1271, 164, 1), (1271, 328, 1), (1271, 656, 1), (1275, 5, 1), (1275, 10, 1),
   (1275, 20, 1), (1275, 40, 1), (1275, 80, 1), (1275, 160, 1), (1275, 320, 1), (1275, 640, 1),
   (1323, 21, 1), (1323, 42, 1), (1323, 84, 1), (1323, 168, 1), (1323, 336, 1), (1323, 672, 1),
   (1333, 43, 1), (1333, 86, 1), (1333, 172, 1), (1333, 344, 1), (1333, 688, 1), (1365, 11, 2),
   (1365, 22, 2), (1365, 43, 2), (1365, 44, 2), (1365, 86, 2), (1365, 88, 2), (1365, 172, 2),
   (1365, 176, 2), (1365, 344, 2), (1365, 352, 2), (1365, 688, 2), (1365, 704, 2), (1395, 45, 1),
   (1395, 90, 1), (1395, 180, 1), (1395, 360, 1), (1395, 720, 1), (1397, 11, 1), (1397, 22, 1),
   (1397, 44, 1), (1397, 88, 1), (1397, 176, 1), (1397, 352, 1), (1397, 704, 1), (1449, 23, 1),
   (1449, 46, 1), (1449, 92, 1), (1449, 184, 1), (1449, 368, 1), (1449, 736, 1), (1457, 47, 1),
   (1457, 94, 1), (1457, 188, 1), (1457, 376, 1)]

/-- Exit-silent table, chunk 4 of 4 (`(q, K₀, c)`). -/
def elcExitSilentTable4 : List (ℕ × ℕ × ℕ) := [ (1457, 752, 1), (1519, 49, 1), (1519, 98, 1),
   (1519, 196, 1), (1519, 392, 1), (1519, 784, 1), (1533, 3, 1), (1533, 6, 1), (1533, 12, 1),
   (1533, 24, 1), (1533, 48, 1), (1533, 96, 1), (1533, 192, 1), (1533, 384, 1), (1533, 768, 1),
   (1575, 25, 1), (1575, 50, 1), (1575, 100, 1), (1575, 200, 1), (1575, 400, 1), (1575, 800, 1),
   (1581, 51, 1), (1581, 102, 1), (1581, 204, 1), (1581, 408, 1), (1581, 816, 1), (1643, 53, 1),
   (1643, 106, 1), (1643, 212, 1), (1643, 424, 1), (1643, 848, 1), (1651, 13, 1), (1651, 26, 1),
   (1651, 52, 1), (1651, 104, 1), (1651, 208, 1), (1651, 416, 1), (1651, 832, 1), (1701, 27, 1),
   (1701, 54, 1), (1701, 108, 1), (1701, 216, 1), (1701, 432, 1), (1701, 864, 1), (1705, 55, 1),
   (1705, 110, 1), (1705, 220, 1), (1705, 440, 1), (1705, 880, 1), (1767, 57, 1), (1767, 114, 1),
   (1767, 228, 1), (1767, 456, 1), (1767, 912, 1), (1785, 7, 1), (1785, 14, 1), (1785, 28, 1),
   (1785, 56, 1), (1785, 112, 1), (1785, 224, 1), (1785, 448, 1), (1785, 896, 1), (1827, 29, 1),
   (1827, 58, 1), (1827, 116, 1), (1827, 232, 1), (1827, 464, 1), (1827, 928, 1), (1829, 59, 1),
   (1829, 118, 1), (1829, 236, 1), (1829, 472, 1), (1829, 944, 1), (1891, 61, 1), (1891, 122, 1),
   (1891, 244, 1), (1891, 488, 1), (1891, 976, 1), (1905, 15, 1), (1905, 30, 1), (1905, 60, 1),
   (1905, 120, 1), (1905, 240, 1), (1905, 480, 1), (1905, 960, 1), (1953, 31, 1), (1953, 62, 1),
   (1953, 63, 1), (1953, 124, 1), (1953, 126, 1), (1953, 248, 1), (1953, 252, 1), (1953, 496, 1),
   (1953, 504, 1), (1953, 992, 1), (1953, 1008, 1)]

/-- **The complete exit-silent table**: all 384 pairs of `q < 2000` whose slope
cycle reads ONLY deep bands (`≥ 5`) on one period. -/
def elcExitSilentTable : List (ℕ × ℕ × ℕ) :=
  elcExitSilentTable1 ++ elcExitSilentTable2 ++ elcExitSilentTable3 ++
    elcExitSilentTable4

theorem elcExitSilentTable_length : elcExitSilentTable.length = 384 := rfl

private theorem elcSilentEmpty_of_mem1 (ctx : ActualFailureContext)
    {qv Kv cv : ℕ} (hmem : (qv, Kv, cv) ∈ elcExitSilentTable1)
    (hq : (class1SlopeDatum ctx).q = qv)
    (hK : (class1SlopeDatum ctx).K₀ = Kv) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ := by
  simp only [elcExitSilentTable1, List.mem_cons, List.not_mem_nil,
    or_false, Prod.mk.injEq] at hmem
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_31_1 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_31_2 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_31_4 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_31_8 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_31_16 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_63_1 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_63_2 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_63_4 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_63_8 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_63_16 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_63_32 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_93_3 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_93_6 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_93_12 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_93_24 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_93_48 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_127_1 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_127_2 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_127_4 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_127_8 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_127_16 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_127_32 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_127_64 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_155_5 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_155_10 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_155_20 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_155_40 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_155_80 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_189_3 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_189_6 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_189_12 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_189_24 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_189_48 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_189_96 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_217_7 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_217_14 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_217_28 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_217_56 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_217_112 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_255_1 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_255_2 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_255_4 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_255_8 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_255_16 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_255_32 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_255_64 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_255_128 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_279_9 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_279_18 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_279_36 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_279_72 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_279_144 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_315_5 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_315_10 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_315_20 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_315_40 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_315_80 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_315_160 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_341_11 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_341_22 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_341_44 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_341_88 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_341_176 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_381_3 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_381_6 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_381_12 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_381_24 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_381_48 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_381_96 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_381_192 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_403_13 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_403_26 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_403_52 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_403_104 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_403_208 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_441_7 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_441_14 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_441_28 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_441_56 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_441_112 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_441_224 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_465_15 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_465_30 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_465_60 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_465_120 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_465_240 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_511_1 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_511_2 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_511_4 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_511_8 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_511_16 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_511_32 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_511_64 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_511_128 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_511_256 ctx hq hK
  obtain ⟨rfl, rfl, rfl⟩ := hmem
  exact elcSilent_527_17 ctx hq hK

private theorem elcSilentEmpty_of_mem2 (ctx : ActualFailureContext)
    {qv Kv cv : ℕ} (hmem : (qv, Kv, cv) ∈ elcExitSilentTable2)
    (hq : (class1SlopeDatum ctx).q = qv)
    (hK : (class1SlopeDatum ctx).K₀ = Kv) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ := by
  simp only [elcExitSilentTable2, List.mem_cons, List.not_mem_nil,
    or_false, Prod.mk.injEq] at hmem
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_527_34 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_527_68 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_527_136 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_527_272 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_567_9 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_567_18 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_567_36 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_567_72 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_567_144 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_567_288 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_589_19 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_589_38 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_589_76 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_589_152 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_589_304 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_635_5 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_635_10 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_635_20 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_635_40 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_635_80 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_635_160 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_635_320 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_651_21 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_651_42 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_651_84 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_651_168 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_651_336 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_693_11 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_693_22 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_693_44 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_693_88 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_693_176 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_693_352 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_713_23 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_713_46 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_713_92 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_713_184 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_713_368 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_765_3 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_765_6 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_765_12 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_765_24 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_765_48 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_765_96 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_765_192 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_765_384 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_775_25 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_775_50 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_775_100 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_775_200 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_775_400 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_819_13 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_819_26 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_819_52 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_819_104 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_819_208 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_819_416 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_837_27 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_837_54 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_837_108 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_837_216 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_837_432 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_889_7 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_889_14 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_889_28 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_889_56 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_889_112 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_889_224 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_889_448 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_899_29 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_899_58 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_899_116 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_899_232 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_899_464 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_945_15 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_945_30 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_945_60 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_945_120 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_945_240 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_945_480 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_961_31 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_961_62 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_961_124 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_961_248 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_961_496 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1023_1 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1023_2 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1023_4 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1023_8 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1023_16 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1023_32 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1023_33 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1023_64 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1023_66 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1023_128 ctx hq hK
  obtain ⟨rfl, rfl, rfl⟩ := hmem
  exact elcSilent_1023_132 ctx hq hK

private theorem elcSilentEmpty_of_mem3 (ctx : ActualFailureContext)
    {qv Kv cv : ℕ} (hmem : (qv, Kv, cv) ∈ elcExitSilentTable3)
    (hq : (class1SlopeDatum ctx).q = qv)
    (hK : (class1SlopeDatum ctx).K₀ = Kv) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ := by
  simp only [elcExitSilentTable3, List.mem_cons, List.not_mem_nil,
    or_false, Prod.mk.injEq] at hmem
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1023_256 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1023_264 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1023_512 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1023_528 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1071_17 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1071_34 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1071_68 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1071_136 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1071_272 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1071_544 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1085_35 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1085_70 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1085_140 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1085_280 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1085_560 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1143_9 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1143_18 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1143_36 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1143_72 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1143_144 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1143_288 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1143_576 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1147_37 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1147_74 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1147_148 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1147_296 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1147_592 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1197_19 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1197_38 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1197_76 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1197_152 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1197_304 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1197_608 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1209_39 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1209_78 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1209_156 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1209_312 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1209_624 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1271_41 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1271_82 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1271_164 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1271_328 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1271_656 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1275_5 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1275_10 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1275_20 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1275_40 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1275_80 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1275_160 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1275_320 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1275_640 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1323_21 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1323_42 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1323_84 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1323_168 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1323_336 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1323_672 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1333_43 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1333_86 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1333_172 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1333_344 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1333_688 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1365_11 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1365_22 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1365_43 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1365_44 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1365_86 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1365_88 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1365_172 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1365_176 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1365_344 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1365_352 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1365_688 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1365_704 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1395_45 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1395_90 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1395_180 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1395_360 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1395_720 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1397_11 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1397_22 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1397_44 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1397_88 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1397_176 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1397_352 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1397_704 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1449_23 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1449_46 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1449_92 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1449_184 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1449_368 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1449_736 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1457_47 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1457_94 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1457_188 ctx hq hK
  obtain ⟨rfl, rfl, rfl⟩ := hmem
  exact elcSilent_1457_376 ctx hq hK

private theorem elcSilentEmpty_of_mem4 (ctx : ActualFailureContext)
    {qv Kv cv : ℕ} (hmem : (qv, Kv, cv) ∈ elcExitSilentTable4)
    (hq : (class1SlopeDatum ctx).q = qv)
    (hK : (class1SlopeDatum ctx).K₀ = Kv) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ := by
  simp only [elcExitSilentTable4, List.mem_cons, List.not_mem_nil,
    or_false, Prod.mk.injEq] at hmem
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1457_752 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1519_49 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1519_98 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1519_196 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1519_392 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1519_784 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1533_3 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1533_6 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1533_12 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1533_24 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1533_48 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1533_96 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1533_192 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1533_384 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1533_768 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1575_25 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1575_50 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1575_100 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1575_200 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1575_400 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1575_800 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1581_51 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1581_102 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1581_204 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1581_408 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1581_816 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1643_53 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1643_106 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1643_212 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1643_424 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1643_848 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1651_13 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1651_26 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1651_52 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1651_104 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1651_208 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1651_416 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1651_832 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1701_27 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1701_54 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1701_108 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1701_216 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1701_432 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1701_864 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1705_55 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1705_110 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1705_220 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1705_440 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1705_880 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1767_57 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1767_114 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1767_228 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1767_456 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1767_912 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1785_7 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1785_14 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1785_28 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1785_56 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1785_112 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1785_224 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1785_448 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1785_896 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1827_29 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1827_58 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1827_116 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1827_232 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1827_464 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1827_928 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1829_59 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1829_118 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1829_236 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1829_472 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1829_944 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1891_61 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1891_122 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1891_244 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1891_488 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1891_976 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1905_15 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1905_30 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1905_60 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1905_120 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1905_240 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1905_480 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1905_960 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1953_31 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1953_62 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1953_63 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1953_124 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1953_126 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1953_248 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1953_252 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1953_496 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1953_504 ctx hq hK
  rcases hmem with ⟨rfl, rfl, rfl⟩ | hmem
  · exact elcSilent_1953_992 ctx hq hK
  obtain ⟨rfl, rfl, rfl⟩ := hmem
  exact elcSilent_1953_1008 ctx hq hK

/-- **THE EXIT-SILENT DISPATCHER**: at any context whose slope datum row sits in the
table, every nonzero-class routed fibre is empty. -/
theorem elcSilentEmpty_of_mem (ctx : ActualFailureContext)
    {qv Kv cv : ℕ} (hmem : (qv, Kv, cv) ∈ elcExitSilentTable)
    (hq : (class1SlopeDatum ctx).q = qv)
    (hK : (class1SlopeDatum ctx).K₀ = Kv) :
    ∀ i : Fin 7, i ≠ 0 →
      routedFibre ctx.n24CarryData (genuineChargeRoute ctx) i = ∅ := by
  unfold elcExitSilentTable at hmem
  rw [List.mem_append, List.mem_append, List.mem_append] at hmem
  rcases hmem with ((h | h) | h) | h
  · exact elcSilentEmpty_of_mem1 ctx h hq hK
  · exact elcSilentEmpty_of_mem2 ctx h hq hK
  · exact elcSilentEmpty_of_mem3 ctx h hq hK
  · exact elcSilentEmpty_of_mem4 ctx h hq hK

/-- **THE OFF-PIN CAPS FIRE OUTRIGHT on the exit-silent stratum**: the EXACT
`ExitMassControlOffPin` conclusion at the context - NO deep, pin-freeness, band,
share, or regime hypothesis. -/
theorem elcOffPinCaps_of_mem (ctx : ActualFailureContext)
    {qv Kv cv : ℕ} (hmem : (qv, Kv, cv) ∈ elcExitSilentTable)
    (hq : (class1SlopeDatum ctx).q = qv)
    (hK : (class1SlopeDatum ctx).K₀ = Kv) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 3 ≤ emcCap ctx
      ∧ routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 4 ≤ emcCap ctx
      ∧ routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
          ≤ emcCap ctx := by
  have h := elcSilentEmpty_of_mem ctx hmem hq hK
  exact ⟨elcMassCap_of_empty ctx 3 (h 3 (by decide)),
    elcMassCap_of_empty ctx 4 (h 4 (by decide)),
    elcMassCap_of_empty ctx 5 (h 5 (by decide))⟩

/-- The class-1 fibre is empty on the exit-silent stratum (band 4 never occurs) -
the `Class1FibreEmpty` per-context shape at these data. -/
theorem elcClass1Empty_of_mem (ctx : ActualFailureContext)
    {qv Kv cv : ℕ} (hmem : (qv, Kv, cv) ∈ elcExitSilentTable)
    (hq : (class1SlopeDatum ctx).q = qv)
    (hK : (class1SlopeDatum ctx).K₀ = Kv) :
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅ :=
  elcSilentEmpty_of_mem ctx hmem hq hK 1 (by decide)

/-- The PROVED `b = 0` spaced-share datum at every nonzero class on the exit-silent
stratum - the degenerate-but-genuine inhabitant of `EmcSpacedShareDatum`. -/
theorem elcDatum_of_mem (ctx : ActualFailureContext)
    {qv Kv cv : ℕ} (hmem : (qv, Kv, cv) ∈ elcExitSilentTable)
    (hq : (class1SlopeDatum ctx).q = qv)
    (hK : (class1SlopeDatum ctx).K₀ = Kv)
    (i : Fin 7) (hi : i ≠ 0) :
    EmcSpacedShareDatum ctx i 0 1 :=
  elcDatum_of_empty ctx i (elcSilentEmpty_of_mem ctx hmem hq hK i hi)

/-! ## Part 3.  Ten representative `b₄ = 1` deep-clearing long-cycle certificates

The wave-20 hunt target: NEW pairs (none in `sreClass1ThresholdTable` - all have
`q ≥ 303 > 199`) with a SINGLETON band-4 residue and period `c ≥ 50` clearing the
deep threshold.  4578 such pairs exist below `q = 2000` (36 moduli); certified here:
one representative per modulus for the 10 smallest moduli, including the two
overlap-1 representatives `(987,5)` (`c = 70`) and `(1065,17)` (`c = 69`). -/

/-- `(303,5)`: period `55`, band-4 residue set `{35}` (value `23`), `b₄ = 1`;
deep threshold `768·((63+55)/55) = 1536 ≤ 1705 = 31·55` CLEARS. -/
private theorem elcCertB_303_5 :
    slopeOrbit 303 5 (1 + 55) = slopeOrbit 303 5 1
      ∧ ∀ j, 1 ≤ j → j ≤ 55 →
          canonGap 303 (slopeOrbit 303 5 j) = 4 → j = 35 := by
  have e0 : slopeOrbit 303 5 0 = 5 := rfl
  have e1 : slopeOrbit 303 5 1 = 17 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 303 5 2 = 241 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 303 5 3 = 179 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 303 5 4 = 55 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 303 5 5 = 137 :=
    slopeOrbit_step_eval 4 2 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 303 5 6 = 245 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 303 5 7 = 187 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 303 5 8 = 71 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 303 5 9 = 265 :=
    slopeOrbit_step_eval 8 2 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 303 5 10 = 227 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 303 5 11 = 151 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 303 5 12 = 301 :=
    slopeOrbit_step_eval 11 1 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 303 5 13 = 299 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 303 5 14 = 295 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 303 5 15 = 287 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 303 5 16 = 271 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 303 5 17 = 239 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 303 5 18 = 175 :=
    slopeOrbit_step_eval 17 0 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 303 5 19 = 47 :=
    slopeOrbit_step_eval 18 0 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 303 5 20 = 73 :=
    slopeOrbit_step_eval 19 2 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 303 5 21 = 281 :=
    slopeOrbit_step_eval 20 2 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 303 5 22 = 259 :=
    slopeOrbit_step_eval 21 0 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 303 5 23 = 215 :=
    slopeOrbit_step_eval 22 0 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 303 5 24 = 127 :=
    slopeOrbit_step_eval 23 0 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 303 5 25 = 205 :=
    slopeOrbit_step_eval 24 1 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 303 5 26 = 107 :=
    slopeOrbit_step_eval 25 0 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 303 5 27 = 125 :=
    slopeOrbit_step_eval 26 1 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 303 5 28 = 197 :=
    slopeOrbit_step_eval 27 1 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 303 5 29 = 91 :=
    slopeOrbit_step_eval 28 0 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 303 5 30 = 61 :=
    slopeOrbit_step_eval 29 1 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : slopeOrbit 303 5 31 = 185 :=
    slopeOrbit_step_eval 30 2 e30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e32 : slopeOrbit 303 5 32 = 67 :=
    slopeOrbit_step_eval 31 0 e31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e33 : slopeOrbit 303 5 33 = 233 :=
    slopeOrbit_step_eval 32 2 e32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e34 : slopeOrbit 303 5 34 = 163 :=
    slopeOrbit_step_eval 33 0 e33 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e35 : slopeOrbit 303 5 35 = 23 :=
    slopeOrbit_step_eval 34 0 e34 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e36 : slopeOrbit 303 5 36 = 65 :=
    slopeOrbit_step_eval 35 3 e35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e37 : slopeOrbit 303 5 37 = 217 :=
    slopeOrbit_step_eval 36 2 e36 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e38 : slopeOrbit 303 5 38 = 131 :=
    slopeOrbit_step_eval 37 0 e37 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e39 : slopeOrbit 303 5 39 = 221 :=
    slopeOrbit_step_eval 38 1 e38 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e40 : slopeOrbit 303 5 40 = 139 :=
    slopeOrbit_step_eval 39 0 e39 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e41 : slopeOrbit 303 5 41 = 253 :=
    slopeOrbit_step_eval 40 1 e40 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e42 : slopeOrbit 303 5 42 = 203 :=
    slopeOrbit_step_eval 41 0 e41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e43 : slopeOrbit 303 5 43 = 103 :=
    slopeOrbit_step_eval 42 0 e42 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e44 : slopeOrbit 303 5 44 = 109 :=
    slopeOrbit_step_eval 43 1 e43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e45 : slopeOrbit 303 5 45 = 133 :=
    slopeOrbit_step_eval 44 1 e44 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e46 : slopeOrbit 303 5 46 = 229 :=
    slopeOrbit_step_eval 45 1 e45 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e47 : slopeOrbit 303 5 47 = 155 :=
    slopeOrbit_step_eval 46 0 e46 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e48 : slopeOrbit 303 5 48 = 7 :=
    slopeOrbit_step_eval 47 0 e47 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e49 : slopeOrbit 303 5 49 = 145 :=
    slopeOrbit_step_eval 48 5 e48 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e50 : slopeOrbit 303 5 50 = 277 :=
    slopeOrbit_step_eval 49 1 e49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e51 : slopeOrbit 303 5 51 = 251 :=
    slopeOrbit_step_eval 50 0 e50 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e52 : slopeOrbit 303 5 52 = 199 :=
    slopeOrbit_step_eval 51 0 e51 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e53 : slopeOrbit 303 5 53 = 95 :=
    slopeOrbit_step_eval 52 0 e52 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e54 : slopeOrbit 303 5 54 = 77 :=
    slopeOrbit_step_eval 53 1 e53 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e55 : slopeOrbit 303 5 55 = 5 :=
    slopeOrbit_step_eval 54 1 e54 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e56 : slopeOrbit 303 5 56 = 17 :=
    slopeOrbit_step_eval 55 5 e55 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 303 5 56 = slopeOrbit 303 5 1
    rw [e56, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e26] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e27] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e28] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e29] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e30] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e31] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e32] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e33] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e34] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rfl
    · rw [e36] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e37] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e38] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e39] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e40] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e41] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e42] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e43] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e44] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e45] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e46] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e47] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e48] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e49] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e50] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e51] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e52] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e53] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e54] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e55] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(303,5)`: the pair is NEW - not a row of the certified survivor table. -/
theorem elcNewPair_303_5 :
    (303, 5) ∉ sreClass1ThresholdTable.map (fun e => (e.1, e.2.1)) := by
  decide

/-- `(303,5)`: the deep threshold at `(b, c) = (1, 55)` clears (the first
certified spaced-share parameters surviving `emc2_deep_spacedShare_threshold`'s
necessary condition). -/
theorem elcDeepClear_303_5 : 768 * (((63 + 55) / 55) * 1) ≤ 31 * 55 := by
  norm_num

/-- `(303,5)`: the class-2 (tower) corrected cap, conditional on EXACTLY the
share + the per-context numeric regime (spacing is CERTIFIED). -/
theorem elcClass2Cap_303_5 (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4)
    (hq : (class1SlopeDatum ctx).q = 303)
    (hK : (class1SlopeDatum ctx).K₀ = 5)
    (hshare : 55 * emcFibreExitMass ctx 2 ≤ 1 * emExitMass ctx)
    (hreg : 1536 * (((ctx.n24CarryData.r + 55) / 55)
          * (1 * ((emW ctx + ctx.n24CarryData.r)
              * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))))
        ≤ 31 * (55 * ctx.shell.X)) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
      ≤ emcCap ctx :=
  emc2_cap_of_spacedShare ctx 2 hband
    (elcDatum_of_band4Cert ctx hq hK (by norm_num) elcCertB_303_5.1
      elcCertB_303_5.2 2 (Or.inr rfl) hshare hreg)

/-- `(303,5)`: the class-1 CORRECTED ABSORPTION shape (the capstone
`class1CapAbsorption` field form) at a `q ≥ 200` pair, conditional on the share
+ the regime - territory un-enumerated by the survivor table. -/
theorem elcClass1Absorption_303_5 (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4)
    (hq : (class1SlopeDatum ctx).q = 303)
    (hK : (class1SlopeDatum ctx).K₀ = 5)
    (hshare : 55 * emcFibreExitMass ctx 1 ≤ 1 * emExitMass ctx)
    (hreg : 1536 * (((ctx.n24CarryData.r + 55) / 55)
          * (1 * ((emW ctx + ctx.n24CarryData.r)
              * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))))
        ≤ 31 * (55 * ctx.shell.X)) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6
          * (ctx.shell.X : ℝ) := by
  have h := emc2_cap_of_spacedShare ctx 1 hband
    (elcDatum_of_band4Cert ctx hq hK (by norm_num) elcCertB_303_5.1
      elcCertB_303_5.2 1 (Or.inl rfl) hshare hreg)
  rw [routedClassMass_one_eq_card_mul_Y] at h
  rwa [emcCap_eq_corrected] at h

/-- `(909,15)`: period `55`, band-4 residue set `{35}` (value `69`), `b₄ = 1`;
deep threshold `768·((63+55)/55) = 1536 ≤ 1705 = 31·55` CLEARS. -/
private theorem elcCertB_909_15 :
    slopeOrbit 909 15 (1 + 55) = slopeOrbit 909 15 1
      ∧ ∀ j, 1 ≤ j → j ≤ 55 →
          canonGap 909 (slopeOrbit 909 15 j) = 4 → j = 35 := by
  have e0 : slopeOrbit 909 15 0 = 15 := rfl
  have e1 : slopeOrbit 909 15 1 = 51 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 909 15 2 = 723 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 909 15 3 = 537 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 909 15 4 = 165 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 909 15 5 = 411 :=
    slopeOrbit_step_eval 4 2 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 909 15 6 = 735 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 909 15 7 = 561 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 909 15 8 = 213 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 909 15 9 = 795 :=
    slopeOrbit_step_eval 8 2 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 909 15 10 = 681 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 909 15 11 = 453 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 909 15 12 = 903 :=
    slopeOrbit_step_eval 11 1 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 909 15 13 = 897 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 909 15 14 = 885 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 909 15 15 = 861 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 909 15 16 = 813 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 909 15 17 = 717 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 909 15 18 = 525 :=
    slopeOrbit_step_eval 17 0 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 909 15 19 = 141 :=
    slopeOrbit_step_eval 18 0 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 909 15 20 = 219 :=
    slopeOrbit_step_eval 19 2 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 909 15 21 = 843 :=
    slopeOrbit_step_eval 20 2 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 909 15 22 = 777 :=
    slopeOrbit_step_eval 21 0 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 909 15 23 = 645 :=
    slopeOrbit_step_eval 22 0 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 909 15 24 = 381 :=
    slopeOrbit_step_eval 23 0 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 909 15 25 = 615 :=
    slopeOrbit_step_eval 24 1 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 909 15 26 = 321 :=
    slopeOrbit_step_eval 25 0 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 909 15 27 = 375 :=
    slopeOrbit_step_eval 26 1 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 909 15 28 = 591 :=
    slopeOrbit_step_eval 27 1 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 909 15 29 = 273 :=
    slopeOrbit_step_eval 28 0 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 909 15 30 = 183 :=
    slopeOrbit_step_eval 29 1 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : slopeOrbit 909 15 31 = 555 :=
    slopeOrbit_step_eval 30 2 e30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e32 : slopeOrbit 909 15 32 = 201 :=
    slopeOrbit_step_eval 31 0 e31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e33 : slopeOrbit 909 15 33 = 699 :=
    slopeOrbit_step_eval 32 2 e32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e34 : slopeOrbit 909 15 34 = 489 :=
    slopeOrbit_step_eval 33 0 e33 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e35 : slopeOrbit 909 15 35 = 69 :=
    slopeOrbit_step_eval 34 0 e34 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e36 : slopeOrbit 909 15 36 = 195 :=
    slopeOrbit_step_eval 35 3 e35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e37 : slopeOrbit 909 15 37 = 651 :=
    slopeOrbit_step_eval 36 2 e36 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e38 : slopeOrbit 909 15 38 = 393 :=
    slopeOrbit_step_eval 37 0 e37 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e39 : slopeOrbit 909 15 39 = 663 :=
    slopeOrbit_step_eval 38 1 e38 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e40 : slopeOrbit 909 15 40 = 417 :=
    slopeOrbit_step_eval 39 0 e39 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e41 : slopeOrbit 909 15 41 = 759 :=
    slopeOrbit_step_eval 40 1 e40 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e42 : slopeOrbit 909 15 42 = 609 :=
    slopeOrbit_step_eval 41 0 e41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e43 : slopeOrbit 909 15 43 = 309 :=
    slopeOrbit_step_eval 42 0 e42 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e44 : slopeOrbit 909 15 44 = 327 :=
    slopeOrbit_step_eval 43 1 e43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e45 : slopeOrbit 909 15 45 = 399 :=
    slopeOrbit_step_eval 44 1 e44 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e46 : slopeOrbit 909 15 46 = 687 :=
    slopeOrbit_step_eval 45 1 e45 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e47 : slopeOrbit 909 15 47 = 465 :=
    slopeOrbit_step_eval 46 0 e46 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e48 : slopeOrbit 909 15 48 = 21 :=
    slopeOrbit_step_eval 47 0 e47 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e49 : slopeOrbit 909 15 49 = 435 :=
    slopeOrbit_step_eval 48 5 e48 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e50 : slopeOrbit 909 15 50 = 831 :=
    slopeOrbit_step_eval 49 1 e49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e51 : slopeOrbit 909 15 51 = 753 :=
    slopeOrbit_step_eval 50 0 e50 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e52 : slopeOrbit 909 15 52 = 597 :=
    slopeOrbit_step_eval 51 0 e51 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e53 : slopeOrbit 909 15 53 = 285 :=
    slopeOrbit_step_eval 52 0 e52 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e54 : slopeOrbit 909 15 54 = 231 :=
    slopeOrbit_step_eval 53 1 e53 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e55 : slopeOrbit 909 15 55 = 15 :=
    slopeOrbit_step_eval 54 1 e54 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e56 : slopeOrbit 909 15 56 = 51 :=
    slopeOrbit_step_eval 55 5 e55 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 909 15 56 = slopeOrbit 909 15 1
    rw [e56, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e26] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e27] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e28] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e29] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e30] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e31] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e32] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e33] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e34] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rfl
    · rw [e36] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e37] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e38] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e39] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e40] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e41] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e42] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e43] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e44] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e45] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e46] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e47] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e48] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e49] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e50] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e51] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e52] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e53] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e54] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e55] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(909,15)`: the pair is NEW - not a row of the certified survivor table. -/
theorem elcNewPair_909_15 :
    (909, 15) ∉ sreClass1ThresholdTable.map (fun e => (e.1, e.2.1)) := by
  decide

/-- `(909,15)`: the deep threshold at `(b, c) = (1, 55)` clears (the first
certified spaced-share parameters surviving `emc2_deep_spacedShare_threshold`'s
necessary condition). -/
theorem elcDeepClear_909_15 : 768 * (((63 + 55) / 55) * 1) ≤ 31 * 55 := by
  norm_num

/-- `(909,15)`: the class-2 (tower) corrected cap, conditional on EXACTLY the
share + the per-context numeric regime (spacing is CERTIFIED). -/
theorem elcClass2Cap_909_15 (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4)
    (hq : (class1SlopeDatum ctx).q = 909)
    (hK : (class1SlopeDatum ctx).K₀ = 15)
    (hshare : 55 * emcFibreExitMass ctx 2 ≤ 1 * emExitMass ctx)
    (hreg : 1536 * (((ctx.n24CarryData.r + 55) / 55)
          * (1 * ((emW ctx + ctx.n24CarryData.r)
              * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))))
        ≤ 31 * (55 * ctx.shell.X)) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
      ≤ emcCap ctx :=
  emc2_cap_of_spacedShare ctx 2 hband
    (elcDatum_of_band4Cert ctx hq hK (by norm_num) elcCertB_909_15.1
      elcCertB_909_15.2 2 (Or.inr rfl) hshare hreg)

/-- `(909,15)`: the class-1 CORRECTED ABSORPTION shape (the capstone
`class1CapAbsorption` field form) at a `q ≥ 200` pair, conditional on the share
+ the regime - territory un-enumerated by the survivor table. -/
theorem elcClass1Absorption_909_15 (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4)
    (hq : (class1SlopeDatum ctx).q = 909)
    (hK : (class1SlopeDatum ctx).K₀ = 15)
    (hshare : 55 * emcFibreExitMass ctx 1 ≤ 1 * emExitMass ctx)
    (hreg : 1536 * (((ctx.n24CarryData.r + 55) / 55)
          * (1 * ((emW ctx + ctx.n24CarryData.r)
              * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))))
        ≤ 31 * (55 * ctx.shell.X)) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6
          * (ctx.shell.X : ℝ) := by
  have h := emc2_cap_of_spacedShare ctx 1 hband
    (elcDatum_of_band4Cert ctx hq hK (by norm_num) elcCertB_909_15.1
      elcCertB_909_15.2 1 (Or.inl rfl) hshare hreg)
  rw [routedClassMass_one_eq_card_mul_Y] at h
  rwa [emcCap_eq_corrected] at h

/-- `(921,7)`: period `51`, band-4 residue set `{9}` (value `59`), `b₄ = 1`;
deep threshold `768·((63+51)/51) = 1536 ≤ 1581 = 31·51` CLEARS. -/
private theorem elcCertB_921_7 :
    slopeOrbit 921 7 (1 + 51) = slopeOrbit 921 7 1
      ∧ ∀ j, 1 ≤ j → j ≤ 51 →
          canonGap 921 (slopeOrbit 921 7 j) = 4 → j = 9 := by
  have e0 : slopeOrbit 921 7 0 = 7 := rfl
  have e1 : slopeOrbit 921 7 1 = 871 :=
    slopeOrbit_step_eval 0 7 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 921 7 2 = 821 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 921 7 3 = 721 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 921 7 4 = 521 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 921 7 5 = 121 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 921 7 6 = 47 :=
    slopeOrbit_step_eval 5 2 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 921 7 7 = 583 :=
    slopeOrbit_step_eval 6 4 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 921 7 8 = 245 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 921 7 9 = 59 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 921 7 10 = 23 :=
    slopeOrbit_step_eval 9 3 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 921 7 11 = 551 :=
    slopeOrbit_step_eval 10 5 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 921 7 12 = 181 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 921 7 13 = 527 :=
    slopeOrbit_step_eval 12 2 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 921 7 14 = 133 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 921 7 15 = 143 :=
    slopeOrbit_step_eval 14 2 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 921 7 16 = 223 :=
    slopeOrbit_step_eval 15 2 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 921 7 17 = 863 :=
    slopeOrbit_step_eval 16 2 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 921 7 18 = 805 :=
    slopeOrbit_step_eval 17 0 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 921 7 19 = 689 :=
    slopeOrbit_step_eval 18 0 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 921 7 20 = 457 :=
    slopeOrbit_step_eval 19 0 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 921 7 21 = 907 :=
    slopeOrbit_step_eval 20 1 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 921 7 22 = 893 :=
    slopeOrbit_step_eval 21 0 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 921 7 23 = 865 :=
    slopeOrbit_step_eval 22 0 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 921 7 24 = 809 :=
    slopeOrbit_step_eval 23 0 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 921 7 25 = 697 :=
    slopeOrbit_step_eval 24 0 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 921 7 26 = 473 :=
    slopeOrbit_step_eval 25 0 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 921 7 27 = 25 :=
    slopeOrbit_step_eval 26 0 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 921 7 28 = 679 :=
    slopeOrbit_step_eval 27 5 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 921 7 29 = 437 :=
    slopeOrbit_step_eval 28 0 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 921 7 30 = 827 :=
    slopeOrbit_step_eval 29 1 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : slopeOrbit 921 7 31 = 733 :=
    slopeOrbit_step_eval 30 0 e30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e32 : slopeOrbit 921 7 32 = 545 :=
    slopeOrbit_step_eval 31 0 e31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e33 : slopeOrbit 921 7 33 = 169 :=
    slopeOrbit_step_eval 32 0 e32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e34 : slopeOrbit 921 7 34 = 431 :=
    slopeOrbit_step_eval 33 2 e33 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e35 : slopeOrbit 921 7 35 = 803 :=
    slopeOrbit_step_eval 34 1 e34 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e36 : slopeOrbit 921 7 36 = 685 :=
    slopeOrbit_step_eval 35 0 e35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e37 : slopeOrbit 921 7 37 = 449 :=
    slopeOrbit_step_eval 36 0 e36 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e38 : slopeOrbit 921 7 38 = 875 :=
    slopeOrbit_step_eval 37 1 e37 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e39 : slopeOrbit 921 7 39 = 829 :=
    slopeOrbit_step_eval 38 0 e38 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e40 : slopeOrbit 921 7 40 = 737 :=
    slopeOrbit_step_eval 39 0 e39 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e41 : slopeOrbit 921 7 41 = 553 :=
    slopeOrbit_step_eval 40 0 e40 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e42 : slopeOrbit 921 7 42 = 185 :=
    slopeOrbit_step_eval 41 0 e41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e43 : slopeOrbit 921 7 43 = 559 :=
    slopeOrbit_step_eval 42 2 e42 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e44 : slopeOrbit 921 7 44 = 197 :=
    slopeOrbit_step_eval 43 0 e43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e45 : slopeOrbit 921 7 45 = 655 :=
    slopeOrbit_step_eval 44 2 e44 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e46 : slopeOrbit 921 7 46 = 389 :=
    slopeOrbit_step_eval 45 0 e45 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e47 : slopeOrbit 921 7 47 = 635 :=
    slopeOrbit_step_eval 46 1 e46 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e48 : slopeOrbit 921 7 48 = 349 :=
    slopeOrbit_step_eval 47 0 e47 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e49 : slopeOrbit 921 7 49 = 475 :=
    slopeOrbit_step_eval 48 1 e48 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e50 : slopeOrbit 921 7 50 = 29 :=
    slopeOrbit_step_eval 49 0 e49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e51 : slopeOrbit 921 7 51 = 7 :=
    slopeOrbit_step_eval 50 4 e50 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e52 : slopeOrbit 921 7 52 = 871 :=
    slopeOrbit_step_eval 51 7 e51 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 921 7 52 = slopeOrbit 921 7 1
    rw [e52, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rfl
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e26] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e27] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e28] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e29] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e30] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e31] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e32] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e33] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e34] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e35] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e36] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e37] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e38] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e39] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e40] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e41] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e42] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e43] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e44] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e45] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e46] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e47] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e48] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e49] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e50] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e51] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(921,7)`: the pair is NEW - not a row of the certified survivor table. -/
theorem elcNewPair_921_7 :
    (921, 7) ∉ sreClass1ThresholdTable.map (fun e => (e.1, e.2.1)) := by
  decide

/-- `(921,7)`: the deep threshold at `(b, c) = (1, 51)` clears (the first
certified spaced-share parameters surviving `emc2_deep_spacedShare_threshold`'s
necessary condition). -/
theorem elcDeepClear_921_7 : 768 * (((63 + 51) / 51) * 1) ≤ 31 * 51 := by
  norm_num

/-- `(921,7)`: the class-2 (tower) corrected cap, conditional on EXACTLY the
share + the per-context numeric regime (spacing is CERTIFIED). -/
theorem elcClass2Cap_921_7 (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4)
    (hq : (class1SlopeDatum ctx).q = 921)
    (hK : (class1SlopeDatum ctx).K₀ = 7)
    (hshare : 51 * emcFibreExitMass ctx 2 ≤ 1 * emExitMass ctx)
    (hreg : 1536 * (((ctx.n24CarryData.r + 51) / 51)
          * (1 * ((emW ctx + ctx.n24CarryData.r)
              * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))))
        ≤ 31 * (51 * ctx.shell.X)) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
      ≤ emcCap ctx :=
  emc2_cap_of_spacedShare ctx 2 hband
    (elcDatum_of_band4Cert ctx hq hK (by norm_num) elcCertB_921_7.1
      elcCertB_921_7.2 2 (Or.inr rfl) hshare hreg)

/-- `(921,7)`: the class-1 CORRECTED ABSORPTION shape (the capstone
`class1CapAbsorption` field form) at a `q ≥ 200` pair, conditional on the share
+ the regime - territory un-enumerated by the survivor table. -/
theorem elcClass1Absorption_921_7 (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4)
    (hq : (class1SlopeDatum ctx).q = 921)
    (hK : (class1SlopeDatum ctx).K₀ = 7)
    (hshare : 51 * emcFibreExitMass ctx 1 ≤ 1 * emExitMass ctx)
    (hreg : 1536 * (((ctx.n24CarryData.r + 51) / 51)
          * (1 * ((emW ctx + ctx.n24CarryData.r)
              * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))))
        ≤ 31 * (51 * ctx.shell.X)) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6
          * (ctx.shell.X : ℝ) := by
  have h := emc2_cap_of_spacedShare ctx 1 hband
    (elcDatum_of_band4Cert ctx hq hK (by norm_num) elcCertB_921_7.1
      elcCertB_921_7.2 1 (Or.inl rfl) hshare hreg)
  rw [routedClassMass_one_eq_card_mul_Y] at h
  rwa [emcCap_eq_corrected] at h

/-- `(931,9)`: period `61`, band-4 residue set `{7}` (value `71`), `b₄ = 1`;
deep threshold `768·((63+61)/61) = 1536 ≤ 1891 = 31·61` CLEARS. -/
private theorem elcCertB_931_9 :
    slopeOrbit 931 9 (1 + 61) = slopeOrbit 931 9 1
      ∧ ∀ j, 1 ≤ j → j ≤ 61 →
          canonGap 931 (slopeOrbit 931 9 j) = 4 → j = 7 := by
  have e0 : slopeOrbit 931 9 0 = 9 := rfl
  have e1 : slopeOrbit 931 9 1 = 221 :=
    slopeOrbit_step_eval 0 6 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 931 9 2 = 837 :=
    slopeOrbit_step_eval 1 2 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 931 9 3 = 743 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 931 9 4 = 555 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 931 9 5 = 179 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 931 9 6 = 501 :=
    slopeOrbit_step_eval 5 2 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 931 9 7 = 71 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 931 9 8 = 205 :=
    slopeOrbit_step_eval 7 3 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 931 9 9 = 709 :=
    slopeOrbit_step_eval 8 2 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 931 9 10 = 487 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 931 9 11 = 43 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 931 9 12 = 445 :=
    slopeOrbit_step_eval 11 4 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 931 9 13 = 849 :=
    slopeOrbit_step_eval 12 1 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 931 9 14 = 767 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 931 9 15 = 603 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 931 9 16 = 275 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 931 9 17 = 169 :=
    slopeOrbit_step_eval 16 1 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 931 9 18 = 421 :=
    slopeOrbit_step_eval 17 2 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 931 9 19 = 753 :=
    slopeOrbit_step_eval 18 1 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 931 9 20 = 575 :=
    slopeOrbit_step_eval 19 0 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 931 9 21 = 219 :=
    slopeOrbit_step_eval 20 0 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 931 9 22 = 821 :=
    slopeOrbit_step_eval 21 2 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 931 9 23 = 711 :=
    slopeOrbit_step_eval 22 0 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 931 9 24 = 491 :=
    slopeOrbit_step_eval 23 0 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 931 9 25 = 51 :=
    slopeOrbit_step_eval 24 0 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 931 9 26 = 701 :=
    slopeOrbit_step_eval 25 4 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 931 9 27 = 471 :=
    slopeOrbit_step_eval 26 0 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 931 9 28 = 11 :=
    slopeOrbit_step_eval 27 0 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 931 9 29 = 477 :=
    slopeOrbit_step_eval 28 6 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 931 9 30 = 23 :=
    slopeOrbit_step_eval 29 0 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : slopeOrbit 931 9 31 = 541 :=
    slopeOrbit_step_eval 30 5 e30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e32 : slopeOrbit 931 9 32 = 151 :=
    slopeOrbit_step_eval 31 0 e31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e33 : slopeOrbit 931 9 33 = 277 :=
    slopeOrbit_step_eval 32 2 e32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e34 : slopeOrbit 931 9 34 = 177 :=
    slopeOrbit_step_eval 33 1 e33 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e35 : slopeOrbit 931 9 35 = 485 :=
    slopeOrbit_step_eval 34 2 e34 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e36 : slopeOrbit 931 9 36 = 39 :=
    slopeOrbit_step_eval 35 0 e35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e37 : slopeOrbit 931 9 37 = 317 :=
    slopeOrbit_step_eval 36 4 e36 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e38 : slopeOrbit 931 9 38 = 337 :=
    slopeOrbit_step_eval 37 1 e37 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e39 : slopeOrbit 931 9 39 = 417 :=
    slopeOrbit_step_eval 38 1 e38 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e40 : slopeOrbit 931 9 40 = 737 :=
    slopeOrbit_step_eval 39 1 e39 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e41 : slopeOrbit 931 9 41 = 543 :=
    slopeOrbit_step_eval 40 0 e40 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e42 : slopeOrbit 931 9 42 = 155 :=
    slopeOrbit_step_eval 41 0 e41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e43 : slopeOrbit 931 9 43 = 309 :=
    slopeOrbit_step_eval 42 2 e42 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e44 : slopeOrbit 931 9 44 = 305 :=
    slopeOrbit_step_eval 43 1 e43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e45 : slopeOrbit 931 9 45 = 289 :=
    slopeOrbit_step_eval 44 1 e44 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e46 : slopeOrbit 931 9 46 = 225 :=
    slopeOrbit_step_eval 45 1 e45 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e47 : slopeOrbit 931 9 47 = 869 :=
    slopeOrbit_step_eval 46 2 e46 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e48 : slopeOrbit 931 9 48 = 807 :=
    slopeOrbit_step_eval 47 0 e47 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e49 : slopeOrbit 931 9 49 = 683 :=
    slopeOrbit_step_eval 48 0 e48 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e50 : slopeOrbit 931 9 50 = 435 :=
    slopeOrbit_step_eval 49 0 e49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e51 : slopeOrbit 931 9 51 = 809 :=
    slopeOrbit_step_eval 50 1 e50 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e52 : slopeOrbit 931 9 52 = 687 :=
    slopeOrbit_step_eval 51 0 e51 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e53 : slopeOrbit 931 9 53 = 443 :=
    slopeOrbit_step_eval 52 0 e52 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e54 : slopeOrbit 931 9 54 = 841 :=
    slopeOrbit_step_eval 53 1 e53 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e55 : slopeOrbit 931 9 55 = 751 :=
    slopeOrbit_step_eval 54 0 e54 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e56 : slopeOrbit 931 9 56 = 571 :=
    slopeOrbit_step_eval 55 0 e55 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e57 : slopeOrbit 931 9 57 = 211 :=
    slopeOrbit_step_eval 56 0 e56 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e58 : slopeOrbit 931 9 58 = 757 :=
    slopeOrbit_step_eval 57 2 e57 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e59 : slopeOrbit 931 9 59 = 583 :=
    slopeOrbit_step_eval 58 0 e58 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e60 : slopeOrbit 931 9 60 = 235 :=
    slopeOrbit_step_eval 59 0 e59 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e61 : slopeOrbit 931 9 61 = 9 :=
    slopeOrbit_step_eval 60 1 e60 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e62 : slopeOrbit 931 9 62 = 221 :=
    slopeOrbit_step_eval 61 6 e61 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 931 9 62 = slopeOrbit 931 9 1
    rw [e62, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rfl
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e26] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e27] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e28] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e29] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e30] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e31] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e32] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e33] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e34] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e35] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e36] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e37] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e38] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e39] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e40] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e41] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e42] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e43] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e44] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e45] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e46] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e47] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e48] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e49] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e50] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e51] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e52] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e53] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e54] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e55] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e56] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e57] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e58] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e59] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e60] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e61] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(931,9)`: the pair is NEW - not a row of the certified survivor table. -/
theorem elcNewPair_931_9 :
    (931, 9) ∉ sreClass1ThresholdTable.map (fun e => (e.1, e.2.1)) := by
  decide

/-- `(931,9)`: the deep threshold at `(b, c) = (1, 61)` clears (the first
certified spaced-share parameters surviving `emc2_deep_spacedShare_threshold`'s
necessary condition). -/
theorem elcDeepClear_931_9 : 768 * (((63 + 61) / 61) * 1) ≤ 31 * 61 := by
  norm_num

/-- `(931,9)`: the class-2 (tower) corrected cap, conditional on EXACTLY the
share + the per-context numeric regime (spacing is CERTIFIED). -/
theorem elcClass2Cap_931_9 (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4)
    (hq : (class1SlopeDatum ctx).q = 931)
    (hK : (class1SlopeDatum ctx).K₀ = 9)
    (hshare : 61 * emcFibreExitMass ctx 2 ≤ 1 * emExitMass ctx)
    (hreg : 1536 * (((ctx.n24CarryData.r + 61) / 61)
          * (1 * ((emW ctx + ctx.n24CarryData.r)
              * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))))
        ≤ 31 * (61 * ctx.shell.X)) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
      ≤ emcCap ctx :=
  emc2_cap_of_spacedShare ctx 2 hband
    (elcDatum_of_band4Cert ctx hq hK (by norm_num) elcCertB_931_9.1
      elcCertB_931_9.2 2 (Or.inr rfl) hshare hreg)

/-- `(931,9)`: the class-1 CORRECTED ABSORPTION shape (the capstone
`class1CapAbsorption` field form) at a `q ≥ 200` pair, conditional on the share
+ the regime - territory un-enumerated by the survivor table. -/
theorem elcClass1Absorption_931_9 (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4)
    (hq : (class1SlopeDatum ctx).q = 931)
    (hK : (class1SlopeDatum ctx).K₀ = 9)
    (hshare : 61 * emcFibreExitMass ctx 1 ≤ 1 * emExitMass ctx)
    (hreg : 1536 * (((ctx.n24CarryData.r + 61) / 61)
          * (1 * ((emW ctx + ctx.n24CarryData.r)
              * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))))
        ≤ 31 * (61 * ctx.shell.X)) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6
          * (ctx.shell.X : ℝ) := by
  have h := emc2_cap_of_spacedShare ctx 1 hband
    (elcDatum_of_band4Cert ctx hq hK (by norm_num) elcCertB_931_9.1
      elcCertB_931_9.2 1 (Or.inl rfl) hshare hreg)
  rw [routedClassMass_one_eq_card_mul_Y] at h
  rwa [emcCap_eq_corrected] at h

/-- `(937,17)`: period `54`, band-4 residue set `{34}` (value `111`), `b₄ = 1`;
deep threshold `768·((63+54)/54) = 1536 ≤ 1674 = 31·54` CLEARS. -/
private theorem elcCertB_937_17 :
    slopeOrbit 937 17 (1 + 54) = slopeOrbit 937 17 1
      ∧ ∀ j, 1 ≤ j → j ≤ 54 →
          canonGap 937 (slopeOrbit 937 17 j) = 4 → j = 34 := by
  have e0 : slopeOrbit 937 17 0 = 17 := rfl
  have e1 : slopeOrbit 937 17 1 = 151 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 937 17 2 = 271 :=
    slopeOrbit_step_eval 1 2 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 937 17 3 = 147 :=
    slopeOrbit_step_eval 2 1 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 937 17 4 = 239 :=
    slopeOrbit_step_eval 3 2 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 937 17 5 = 19 :=
    slopeOrbit_step_eval 4 1 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 937 17 6 = 279 :=
    slopeOrbit_step_eval 5 5 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 937 17 7 = 179 :=
    slopeOrbit_step_eval 6 1 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 937 17 8 = 495 :=
    slopeOrbit_step_eval 7 2 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 937 17 9 = 53 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 937 17 10 = 759 :=
    slopeOrbit_step_eval 9 4 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 937 17 11 = 581 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 937 17 12 = 225 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 937 17 13 = 863 :=
    slopeOrbit_step_eval 12 2 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 937 17 14 = 789 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 937 17 15 = 641 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 937 17 16 = 345 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 937 17 17 = 443 :=
    slopeOrbit_step_eval 16 1 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 937 17 18 = 835 :=
    slopeOrbit_step_eval 17 1 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 937 17 19 = 733 :=
    slopeOrbit_step_eval 18 0 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 937 17 20 = 529 :=
    slopeOrbit_step_eval 19 0 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 937 17 21 = 121 :=
    slopeOrbit_step_eval 20 0 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 937 17 22 = 31 :=
    slopeOrbit_step_eval 21 2 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 937 17 23 = 55 :=
    slopeOrbit_step_eval 22 4 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 937 17 24 = 823 :=
    slopeOrbit_step_eval 23 4 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 937 17 25 = 709 :=
    slopeOrbit_step_eval 24 0 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 937 17 26 = 481 :=
    slopeOrbit_step_eval 25 0 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 937 17 27 = 25 :=
    slopeOrbit_step_eval 26 0 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 937 17 28 = 663 :=
    slopeOrbit_step_eval 27 5 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 937 17 29 = 389 :=
    slopeOrbit_step_eval 28 0 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 937 17 30 = 619 :=
    slopeOrbit_step_eval 29 1 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : slopeOrbit 937 17 31 = 301 :=
    slopeOrbit_step_eval 30 0 e30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e32 : slopeOrbit 937 17 32 = 267 :=
    slopeOrbit_step_eval 31 1 e31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e33 : slopeOrbit 937 17 33 = 131 :=
    slopeOrbit_step_eval 32 1 e32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e34 : slopeOrbit 937 17 34 = 111 :=
    slopeOrbit_step_eval 33 2 e33 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e35 : slopeOrbit 937 17 35 = 839 :=
    slopeOrbit_step_eval 34 3 e34 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e36 : slopeOrbit 937 17 36 = 741 :=
    slopeOrbit_step_eval 35 0 e35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e37 : slopeOrbit 937 17 37 = 545 :=
    slopeOrbit_step_eval 36 0 e36 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e38 : slopeOrbit 937 17 38 = 153 :=
    slopeOrbit_step_eval 37 0 e37 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e39 : slopeOrbit 937 17 39 = 287 :=
    slopeOrbit_step_eval 38 2 e38 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e40 : slopeOrbit 937 17 40 = 211 :=
    slopeOrbit_step_eval 39 1 e39 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e41 : slopeOrbit 937 17 41 = 751 :=
    slopeOrbit_step_eval 40 2 e40 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e42 : slopeOrbit 937 17 42 = 565 :=
    slopeOrbit_step_eval 41 0 e41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e43 : slopeOrbit 937 17 43 = 193 :=
    slopeOrbit_step_eval 42 0 e42 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e44 : slopeOrbit 937 17 44 = 607 :=
    slopeOrbit_step_eval 43 2 e43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e45 : slopeOrbit 937 17 45 = 277 :=
    slopeOrbit_step_eval 44 0 e44 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e46 : slopeOrbit 937 17 46 = 171 :=
    slopeOrbit_step_eval 45 1 e45 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e47 : slopeOrbit 937 17 47 = 431 :=
    slopeOrbit_step_eval 46 2 e46 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e48 : slopeOrbit 937 17 48 = 787 :=
    slopeOrbit_step_eval 47 1 e47 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e49 : slopeOrbit 937 17 49 = 637 :=
    slopeOrbit_step_eval 48 0 e48 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e50 : slopeOrbit 937 17 50 = 337 :=
    slopeOrbit_step_eval 49 0 e49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e51 : slopeOrbit 937 17 51 = 411 :=
    slopeOrbit_step_eval 50 1 e50 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e52 : slopeOrbit 937 17 52 = 707 :=
    slopeOrbit_step_eval 51 1 e51 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e53 : slopeOrbit 937 17 53 = 477 :=
    slopeOrbit_step_eval 52 0 e52 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e54 : slopeOrbit 937 17 54 = 17 :=
    slopeOrbit_step_eval 53 0 e53 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e55 : slopeOrbit 937 17 55 = 151 :=
    slopeOrbit_step_eval 54 5 e54 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 937 17 55 = slopeOrbit 937 17 1
    rw [e55, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e26] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e27] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e28] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e29] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e30] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e31] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e32] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e33] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rfl
    · rw [e35] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e36] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e37] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e38] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e39] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e40] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e41] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e42] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e43] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e44] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e45] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e46] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e47] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e48] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e49] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e50] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e51] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e52] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e53] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e54] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(937,17)`: the pair is NEW - not a row of the certified survivor table. -/
theorem elcNewPair_937_17 :
    (937, 17) ∉ sreClass1ThresholdTable.map (fun e => (e.1, e.2.1)) := by
  decide

/-- `(937,17)`: the deep threshold at `(b, c) = (1, 54)` clears (the first
certified spaced-share parameters surviving `emc2_deep_spacedShare_threshold`'s
necessary condition). -/
theorem elcDeepClear_937_17 : 768 * (((63 + 54) / 54) * 1) ≤ 31 * 54 := by
  norm_num

/-- `(937,17)`: the class-2 (tower) corrected cap, conditional on EXACTLY the
share + the per-context numeric regime (spacing is CERTIFIED). -/
theorem elcClass2Cap_937_17 (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4)
    (hq : (class1SlopeDatum ctx).q = 937)
    (hK : (class1SlopeDatum ctx).K₀ = 17)
    (hshare : 54 * emcFibreExitMass ctx 2 ≤ 1 * emExitMass ctx)
    (hreg : 1536 * (((ctx.n24CarryData.r + 54) / 54)
          * (1 * ((emW ctx + ctx.n24CarryData.r)
              * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))))
        ≤ 31 * (54 * ctx.shell.X)) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
      ≤ emcCap ctx :=
  emc2_cap_of_spacedShare ctx 2 hband
    (elcDatum_of_band4Cert ctx hq hK (by norm_num) elcCertB_937_17.1
      elcCertB_937_17.2 2 (Or.inr rfl) hshare hreg)

/-- `(937,17)`: the class-1 CORRECTED ABSORPTION shape (the capstone
`class1CapAbsorption` field form) at a `q ≥ 200` pair, conditional on the share
+ the regime - territory un-enumerated by the survivor table. -/
theorem elcClass1Absorption_937_17 (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4)
    (hq : (class1SlopeDatum ctx).q = 937)
    (hK : (class1SlopeDatum ctx).K₀ = 17)
    (hshare : 54 * emcFibreExitMass ctx 1 ≤ 1 * emExitMass ctx)
    (hreg : 1536 * (((ctx.n24CarryData.r + 54) / 54)
          * (1 * ((emW ctx + ctx.n24CarryData.r)
              * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))))
        ≤ 31 * (54 * ctx.shell.X)) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6
          * (ctx.shell.X : ℝ) := by
  have h := emc2_cap_of_spacedShare ctx 1 hband
    (elcDatum_of_band4Cert ctx hq hK (by norm_num) elcCertB_937_17.1
      elcCertB_937_17.2 1 (Or.inl rfl) hshare hreg)
  rw [routedClassMass_one_eq_card_mul_Y] at h
  rwa [emcCap_eq_corrected] at h

/-- `(979,19)`: period `56`, band-4 residue set `{41}` (value `63`), `b₄ = 1`;
deep threshold `768·((63+56)/56) = 1536 ≤ 1736 = 31·56` CLEARS. -/
private theorem elcCertB_979_19 :
    slopeOrbit 979 19 (1 + 56) = slopeOrbit 979 19 1
      ∧ ∀ j, 1 ≤ j → j ≤ 56 →
          canonGap 979 (slopeOrbit 979 19 j) = 4 → j = 41 := by
  have e0 : slopeOrbit 979 19 0 = 19 := rfl
  have e1 : slopeOrbit 979 19 1 = 237 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 979 19 2 = 917 :=
    slopeOrbit_step_eval 1 2 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 979 19 3 = 855 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 979 19 4 = 731 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 979 19 5 = 483 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 979 19 6 = 953 :=
    slopeOrbit_step_eval 5 1 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 979 19 7 = 927 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 979 19 8 = 875 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 979 19 9 = 771 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 979 19 10 = 563 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 979 19 11 = 147 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 979 19 12 = 197 :=
    slopeOrbit_step_eval 11 2 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 979 19 13 = 597 :=
    slopeOrbit_step_eval 12 2 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 979 19 14 = 215 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 979 19 15 = 741 :=
    slopeOrbit_step_eval 14 2 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 979 19 16 = 503 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 979 19 17 = 27 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 979 19 18 = 749 :=
    slopeOrbit_step_eval 17 5 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 979 19 19 = 519 :=
    slopeOrbit_step_eval 18 0 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 979 19 20 = 59 :=
    slopeOrbit_step_eval 19 0 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 979 19 21 = 909 :=
    slopeOrbit_step_eval 20 4 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 979 19 22 = 839 :=
    slopeOrbit_step_eval 21 0 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 979 19 23 = 699 :=
    slopeOrbit_step_eval 22 0 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 979 19 24 = 419 :=
    slopeOrbit_step_eval 23 0 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 979 19 25 = 697 :=
    slopeOrbit_step_eval 24 1 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 979 19 26 = 415 :=
    slopeOrbit_step_eval 25 0 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 979 19 27 = 681 :=
    slopeOrbit_step_eval 26 1 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 979 19 28 = 383 :=
    slopeOrbit_step_eval 27 0 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 979 19 29 = 553 :=
    slopeOrbit_step_eval 28 1 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 979 19 30 = 127 :=
    slopeOrbit_step_eval 29 0 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : slopeOrbit 979 19 31 = 37 :=
    slopeOrbit_step_eval 30 2 e30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e32 : slopeOrbit 979 19 32 = 205 :=
    slopeOrbit_step_eval 31 4 e31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e33 : slopeOrbit 979 19 33 = 661 :=
    slopeOrbit_step_eval 32 2 e32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e34 : slopeOrbit 979 19 34 = 343 :=
    slopeOrbit_step_eval 33 0 e33 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e35 : slopeOrbit 979 19 35 = 393 :=
    slopeOrbit_step_eval 34 1 e34 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e36 : slopeOrbit 979 19 36 = 593 :=
    slopeOrbit_step_eval 35 1 e35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e37 : slopeOrbit 979 19 37 = 207 :=
    slopeOrbit_step_eval 36 0 e36 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e38 : slopeOrbit 979 19 38 = 677 :=
    slopeOrbit_step_eval 37 2 e37 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e39 : slopeOrbit 979 19 39 = 375 :=
    slopeOrbit_step_eval 38 0 e38 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e40 : slopeOrbit 979 19 40 = 521 :=
    slopeOrbit_step_eval 39 1 e39 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e41 : slopeOrbit 979 19 41 = 63 :=
    slopeOrbit_step_eval 40 0 e40 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e42 : slopeOrbit 979 19 42 = 29 :=
    slopeOrbit_step_eval 41 3 e41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e43 : slopeOrbit 979 19 43 = 877 :=
    slopeOrbit_step_eval 42 5 e42 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e44 : slopeOrbit 979 19 44 = 775 :=
    slopeOrbit_step_eval 43 0 e43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e45 : slopeOrbit 979 19 45 = 571 :=
    slopeOrbit_step_eval 44 0 e44 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e46 : slopeOrbit 979 19 46 = 163 :=
    slopeOrbit_step_eval 45 0 e45 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e47 : slopeOrbit 979 19 47 = 325 :=
    slopeOrbit_step_eval 46 2 e46 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e48 : slopeOrbit 979 19 48 = 321 :=
    slopeOrbit_step_eval 47 1 e47 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e49 : slopeOrbit 979 19 49 = 305 :=
    slopeOrbit_step_eval 48 1 e48 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e50 : slopeOrbit 979 19 50 = 241 :=
    slopeOrbit_step_eval 49 1 e49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e51 : slopeOrbit 979 19 51 = 949 :=
    slopeOrbit_step_eval 50 2 e50 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e52 : slopeOrbit 979 19 52 = 919 :=
    slopeOrbit_step_eval 51 0 e51 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e53 : slopeOrbit 979 19 53 = 859 :=
    slopeOrbit_step_eval 52 0 e52 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e54 : slopeOrbit 979 19 54 = 739 :=
    slopeOrbit_step_eval 53 0 e53 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e55 : slopeOrbit 979 19 55 = 499 :=
    slopeOrbit_step_eval 54 0 e54 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e56 : slopeOrbit 979 19 56 = 19 :=
    slopeOrbit_step_eval 55 0 e55 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e57 : slopeOrbit 979 19 57 = 237 :=
    slopeOrbit_step_eval 56 5 e56 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 979 19 57 = slopeOrbit 979 19 1
    rw [e57, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e26] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e27] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e28] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e29] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e30] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e31] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e32] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e33] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e34] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e35] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e36] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e37] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e38] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e39] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e40] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rfl
    · rw [e42] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e43] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e44] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e45] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e46] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e47] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e48] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e49] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e50] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e51] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e52] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e53] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e54] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e55] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e56] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(979,19)`: the pair is NEW - not a row of the certified survivor table. -/
theorem elcNewPair_979_19 :
    (979, 19) ∉ sreClass1ThresholdTable.map (fun e => (e.1, e.2.1)) := by
  decide

/-- `(979,19)`: the deep threshold at `(b, c) = (1, 56)` clears (the first
certified spaced-share parameters surviving `emc2_deep_spacedShare_threshold`'s
necessary condition). -/
theorem elcDeepClear_979_19 : 768 * (((63 + 56) / 56) * 1) ≤ 31 * 56 := by
  norm_num

/-- `(979,19)`: the class-2 (tower) corrected cap, conditional on EXACTLY the
share + the per-context numeric regime (spacing is CERTIFIED). -/
theorem elcClass2Cap_979_19 (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4)
    (hq : (class1SlopeDatum ctx).q = 979)
    (hK : (class1SlopeDatum ctx).K₀ = 19)
    (hshare : 56 * emcFibreExitMass ctx 2 ≤ 1 * emExitMass ctx)
    (hreg : 1536 * (((ctx.n24CarryData.r + 56) / 56)
          * (1 * ((emW ctx + ctx.n24CarryData.r)
              * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))))
        ≤ 31 * (56 * ctx.shell.X)) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
      ≤ emcCap ctx :=
  emc2_cap_of_spacedShare ctx 2 hband
    (elcDatum_of_band4Cert ctx hq hK (by norm_num) elcCertB_979_19.1
      elcCertB_979_19.2 2 (Or.inr rfl) hshare hreg)

/-- `(979,19)`: the class-1 CORRECTED ABSORPTION shape (the capstone
`class1CapAbsorption` field form) at a `q ≥ 200` pair, conditional on the share
+ the regime - territory un-enumerated by the survivor table. -/
theorem elcClass1Absorption_979_19 (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4)
    (hq : (class1SlopeDatum ctx).q = 979)
    (hK : (class1SlopeDatum ctx).K₀ = 19)
    (hshare : 56 * emcFibreExitMass ctx 1 ≤ 1 * emExitMass ctx)
    (hreg : 1536 * (((ctx.n24CarryData.r + 56) / 56)
          * (1 * ((emW ctx + ctx.n24CarryData.r)
              * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))))
        ≤ 31 * (56 * ctx.shell.X)) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6
          * (ctx.shell.X : ℝ) := by
  have h := emc2_cap_of_spacedShare ctx 1 hband
    (elcDatum_of_band4Cert ctx hq hK (by norm_num) elcCertB_979_19.1
      elcCertB_979_19.2 1 (Or.inl rfl) hshare hreg)
  rw [routedClassMass_one_eq_card_mul_Y] at h
  rwa [emcCap_eq_corrected] at h

/-- `(987,5)`: period `70`, band-4 residue set `{48}` (value `73`), `b₄ = 1`;
deep threshold `768·((63+70)/70) = 768 ≤ 2170 = 31·70` CLEARS. -/
private theorem elcCertB_987_5 :
    slopeOrbit 987 5 (1 + 70) = slopeOrbit 987 5 1
      ∧ ∀ j, 1 ≤ j → j ≤ 70 →
          canonGap 987 (slopeOrbit 987 5 j) = 4 → j = 48 := by
  have e0 : slopeOrbit 987 5 0 = 5 := rfl
  have e1 : slopeOrbit 987 5 1 = 293 :=
    slopeOrbit_step_eval 0 7 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 987 5 2 = 185 :=
    slopeOrbit_step_eval 1 1 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 987 5 3 = 493 :=
    slopeOrbit_step_eval 2 2 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 987 5 4 = 985 :=
    slopeOrbit_step_eval 3 1 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 987 5 5 = 983 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 987 5 6 = 979 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 987 5 7 = 971 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 987 5 8 = 955 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 987 5 9 = 923 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 987 5 10 = 859 :=
    slopeOrbit_step_eval 9 0 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 987 5 11 = 731 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 987 5 12 = 475 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 987 5 13 = 913 :=
    slopeOrbit_step_eval 12 1 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 987 5 14 = 839 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 987 5 15 = 691 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 987 5 16 = 395 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 987 5 17 = 593 :=
    slopeOrbit_step_eval 16 1 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 987 5 18 = 199 :=
    slopeOrbit_step_eval 17 0 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 987 5 19 = 605 :=
    slopeOrbit_step_eval 18 2 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 987 5 20 = 223 :=
    slopeOrbit_step_eval 19 0 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 987 5 21 = 797 :=
    slopeOrbit_step_eval 20 2 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 987 5 22 = 607 :=
    slopeOrbit_step_eval 21 0 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 987 5 23 = 227 :=
    slopeOrbit_step_eval 22 0 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 987 5 24 = 829 :=
    slopeOrbit_step_eval 23 2 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 987 5 25 = 671 :=
    slopeOrbit_step_eval 24 0 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 987 5 26 = 355 :=
    slopeOrbit_step_eval 25 0 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 987 5 27 = 433 :=
    slopeOrbit_step_eval 26 1 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 987 5 28 = 745 :=
    slopeOrbit_step_eval 27 1 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 987 5 29 = 503 :=
    slopeOrbit_step_eval 28 0 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 987 5 30 = 19 :=
    slopeOrbit_step_eval 29 0 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : slopeOrbit 987 5 31 = 229 :=
    slopeOrbit_step_eval 30 5 e30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e32 : slopeOrbit 987 5 32 = 845 :=
    slopeOrbit_step_eval 31 2 e31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e33 : slopeOrbit 987 5 33 = 703 :=
    slopeOrbit_step_eval 32 0 e32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e34 : slopeOrbit 987 5 34 = 419 :=
    slopeOrbit_step_eval 33 0 e33 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e35 : slopeOrbit 987 5 35 = 689 :=
    slopeOrbit_step_eval 34 1 e34 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e36 : slopeOrbit 987 5 36 = 391 :=
    slopeOrbit_step_eval 35 0 e35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e37 : slopeOrbit 987 5 37 = 577 :=
    slopeOrbit_step_eval 36 1 e36 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e38 : slopeOrbit 987 5 38 = 167 :=
    slopeOrbit_step_eval 37 0 e37 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e39 : slopeOrbit 987 5 39 = 349 :=
    slopeOrbit_step_eval 38 2 e38 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e40 : slopeOrbit 987 5 40 = 409 :=
    slopeOrbit_step_eval 39 1 e39 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e41 : slopeOrbit 987 5 41 = 649 :=
    slopeOrbit_step_eval 40 1 e40 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e42 : slopeOrbit 987 5 42 = 311 :=
    slopeOrbit_step_eval 41 0 e41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e43 : slopeOrbit 987 5 43 = 257 :=
    slopeOrbit_step_eval 42 1 e42 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e44 : slopeOrbit 987 5 44 = 41 :=
    slopeOrbit_step_eval 43 1 e43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e45 : slopeOrbit 987 5 45 = 325 :=
    slopeOrbit_step_eval 44 4 e44 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e46 : slopeOrbit 987 5 46 = 313 :=
    slopeOrbit_step_eval 45 1 e45 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e47 : slopeOrbit 987 5 47 = 265 :=
    slopeOrbit_step_eval 46 1 e46 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e48 : slopeOrbit 987 5 48 = 73 :=
    slopeOrbit_step_eval 47 1 e47 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e49 : slopeOrbit 987 5 49 = 181 :=
    slopeOrbit_step_eval 48 3 e48 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e50 : slopeOrbit 987 5 50 = 461 :=
    slopeOrbit_step_eval 49 2 e49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e51 : slopeOrbit 987 5 51 = 857 :=
    slopeOrbit_step_eval 50 1 e50 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e52 : slopeOrbit 987 5 52 = 727 :=
    slopeOrbit_step_eval 51 0 e51 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e53 : slopeOrbit 987 5 53 = 467 :=
    slopeOrbit_step_eval 52 0 e52 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e54 : slopeOrbit 987 5 54 = 881 :=
    slopeOrbit_step_eval 53 1 e53 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e55 : slopeOrbit 987 5 55 = 775 :=
    slopeOrbit_step_eval 54 0 e54 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e56 : slopeOrbit 987 5 56 = 563 :=
    slopeOrbit_step_eval 55 0 e55 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e57 : slopeOrbit 987 5 57 = 139 :=
    slopeOrbit_step_eval 56 0 e56 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e58 : slopeOrbit 987 5 58 = 125 :=
    slopeOrbit_step_eval 57 2 e57 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e59 : slopeOrbit 987 5 59 = 13 :=
    slopeOrbit_step_eval 58 2 e58 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e60 : slopeOrbit 987 5 60 = 677 :=
    slopeOrbit_step_eval 59 6 e59 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e61 : slopeOrbit 987 5 61 = 367 :=
    slopeOrbit_step_eval 60 0 e60 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e62 : slopeOrbit 987 5 62 = 481 :=
    slopeOrbit_step_eval 61 1 e61 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e63 : slopeOrbit 987 5 63 = 937 :=
    slopeOrbit_step_eval 62 1 e62 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e64 : slopeOrbit 987 5 64 = 887 :=
    slopeOrbit_step_eval 63 0 e63 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e65 : slopeOrbit 987 5 65 = 787 :=
    slopeOrbit_step_eval 64 0 e64 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e66 : slopeOrbit 987 5 66 = 587 :=
    slopeOrbit_step_eval 65 0 e65 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e67 : slopeOrbit 987 5 67 = 187 :=
    slopeOrbit_step_eval 66 0 e66 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e68 : slopeOrbit 987 5 68 = 509 :=
    slopeOrbit_step_eval 67 2 e67 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e69 : slopeOrbit 987 5 69 = 31 :=
    slopeOrbit_step_eval 68 0 e68 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e70 : slopeOrbit 987 5 70 = 5 :=
    slopeOrbit_step_eval 69 4 e69 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e71 : slopeOrbit 987 5 71 = 293 :=
    slopeOrbit_step_eval 70 7 e70 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 987 5 71 = slopeOrbit 987 5 1
    rw [e71, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e26] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e27] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e28] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e29] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e30] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e31] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e32] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e33] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e34] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e35] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e36] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e37] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e38] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e39] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e40] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e41] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e42] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e43] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e44] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e45] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e46] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e47] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rfl
    · rw [e49] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e50] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e51] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e52] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e53] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e54] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e55] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e56] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e57] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e58] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e59] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e60] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e61] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e62] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e63] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e64] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e65] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e66] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e67] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e68] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e69] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e70] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(987,5)`: the pair is NEW - not a row of the certified survivor table. -/
theorem elcNewPair_987_5 :
    (987, 5) ∉ sreClass1ThresholdTable.map (fun e => (e.1, e.2.1)) := by
  decide

/-- `(987,5)`: the deep threshold at `(b, c) = (1, 70)` clears (the first
certified spaced-share parameters surviving `emc2_deep_spacedShare_threshold`'s
necessary condition). -/
theorem elcDeepClear_987_5 : 768 * (((63 + 70) / 70) * 1) ≤ 31 * 70 := by
  norm_num

/-- `(987,5)`: the class-2 (tower) corrected cap, conditional on EXACTLY the
share + the per-context numeric regime (spacing is CERTIFIED). -/
theorem elcClass2Cap_987_5 (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4)
    (hq : (class1SlopeDatum ctx).q = 987)
    (hK : (class1SlopeDatum ctx).K₀ = 5)
    (hshare : 70 * emcFibreExitMass ctx 2 ≤ 1 * emExitMass ctx)
    (hreg : 1536 * (((ctx.n24CarryData.r + 70) / 70)
          * (1 * ((emW ctx + ctx.n24CarryData.r)
              * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))))
        ≤ 31 * (70 * ctx.shell.X)) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
      ≤ emcCap ctx :=
  emc2_cap_of_spacedShare ctx 2 hband
    (elcDatum_of_band4Cert ctx hq hK (by norm_num) elcCertB_987_5.1
      elcCertB_987_5.2 2 (Or.inr rfl) hshare hreg)

/-- `(987,5)`: the class-1 CORRECTED ABSORPTION shape (the capstone
`class1CapAbsorption` field form) at a `q ≥ 200` pair, conditional on the share
+ the regime - territory un-enumerated by the survivor table. -/
theorem elcClass1Absorption_987_5 (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4)
    (hq : (class1SlopeDatum ctx).q = 987)
    (hK : (class1SlopeDatum ctx).K₀ = 5)
    (hshare : 70 * emcFibreExitMass ctx 1 ≤ 1 * emExitMass ctx)
    (hreg : 1536 * (((ctx.n24CarryData.r + 70) / 70)
          * (1 * ((emW ctx + ctx.n24CarryData.r)
              * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))))
        ≤ 31 * (70 * ctx.shell.X)) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6
          * (ctx.shell.X : ℝ) := by
  have h := emc2_cap_of_spacedShare ctx 1 hband
    (elcDatum_of_band4Cert ctx hq hK (by norm_num) elcCertB_987_5.1
      elcCertB_987_5.2 1 (Or.inl rfl) hshare hreg)
  rw [routedClassMass_one_eq_card_mul_Y] at h
  rwa [emcCap_eq_corrected] at h

/-- `(1053,17)`: period `53`, band-4 residue set `{2}` (value `67`), `b₄ = 1`;
deep threshold `768·((63+53)/53) = 1536 ≤ 1643 = 31·53` CLEARS. -/
private theorem elcCertB_1053_17 :
    slopeOrbit 1053 17 (1 + 53) = slopeOrbit 1053 17 1
      ∧ ∀ j, 1 ≤ j → j ≤ 53 →
          canonGap 1053 (slopeOrbit 1053 17 j) = 4 → j = 2 := by
  have e0 : slopeOrbit 1053 17 0 = 17 := rfl
  have e1 : slopeOrbit 1053 17 1 = 35 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1053 17 2 = 67 :=
    slopeOrbit_step_eval 1 4 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 1053 17 3 = 19 :=
    slopeOrbit_step_eval 2 3 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 1053 17 4 = 163 :=
    slopeOrbit_step_eval 3 5 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 1053 17 5 = 251 :=
    slopeOrbit_step_eval 4 2 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 1053 17 6 = 955 :=
    slopeOrbit_step_eval 5 2 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 1053 17 7 = 857 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 1053 17 8 = 661 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 1053 17 9 = 269 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 1053 17 10 = 23 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 1053 17 11 = 419 :=
    slopeOrbit_step_eval 10 5 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 1053 17 12 = 623 :=
    slopeOrbit_step_eval 11 1 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 1053 17 13 = 193 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 1053 17 14 = 491 :=
    slopeOrbit_step_eval 13 2 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 1053 17 15 = 911 :=
    slopeOrbit_step_eval 14 1 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 1053 17 16 = 769 :=
    slopeOrbit_step_eval 15 0 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 1053 17 17 = 485 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 1053 17 18 = 887 :=
    slopeOrbit_step_eval 17 1 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 1053 17 19 = 721 :=
    slopeOrbit_step_eval 18 0 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 1053 17 20 = 389 :=
    slopeOrbit_step_eval 19 0 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 1053 17 21 = 503 :=
    slopeOrbit_step_eval 20 1 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 1053 17 22 = 959 :=
    slopeOrbit_step_eval 21 1 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 1053 17 23 = 865 :=
    slopeOrbit_step_eval 22 0 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 1053 17 24 = 677 :=
    slopeOrbit_step_eval 23 0 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 1053 17 25 = 301 :=
    slopeOrbit_step_eval 24 0 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 1053 17 26 = 151 :=
    slopeOrbit_step_eval 25 1 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 1053 17 27 = 155 :=
    slopeOrbit_step_eval 26 2 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 1053 17 28 = 187 :=
    slopeOrbit_step_eval 27 2 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 1053 17 29 = 443 :=
    slopeOrbit_step_eval 28 2 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 1053 17 30 = 719 :=
    slopeOrbit_step_eval 29 1 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : slopeOrbit 1053 17 31 = 385 :=
    slopeOrbit_step_eval 30 0 e30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e32 : slopeOrbit 1053 17 32 = 487 :=
    slopeOrbit_step_eval 31 1 e31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e33 : slopeOrbit 1053 17 33 = 895 :=
    slopeOrbit_step_eval 32 1 e32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e34 : slopeOrbit 1053 17 34 = 737 :=
    slopeOrbit_step_eval 33 0 e33 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e35 : slopeOrbit 1053 17 35 = 421 :=
    slopeOrbit_step_eval 34 0 e34 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e36 : slopeOrbit 1053 17 36 = 631 :=
    slopeOrbit_step_eval 35 1 e35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e37 : slopeOrbit 1053 17 37 = 209 :=
    slopeOrbit_step_eval 36 0 e36 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e38 : slopeOrbit 1053 17 38 = 619 :=
    slopeOrbit_step_eval 37 2 e37 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e39 : slopeOrbit 1053 17 39 = 185 :=
    slopeOrbit_step_eval 38 0 e38 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e40 : slopeOrbit 1053 17 40 = 427 :=
    slopeOrbit_step_eval 39 2 e39 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e41 : slopeOrbit 1053 17 41 = 655 :=
    slopeOrbit_step_eval 40 1 e40 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e42 : slopeOrbit 1053 17 42 = 257 :=
    slopeOrbit_step_eval 41 0 e41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e43 : slopeOrbit 1053 17 43 = 1003 :=
    slopeOrbit_step_eval 42 2 e42 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e44 : slopeOrbit 1053 17 44 = 953 :=
    slopeOrbit_step_eval 43 0 e43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e45 : slopeOrbit 1053 17 45 = 853 :=
    slopeOrbit_step_eval 44 0 e44 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e46 : slopeOrbit 1053 17 46 = 653 :=
    slopeOrbit_step_eval 45 0 e45 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e47 : slopeOrbit 1053 17 47 = 253 :=
    slopeOrbit_step_eval 46 0 e46 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e48 : slopeOrbit 1053 17 48 = 971 :=
    slopeOrbit_step_eval 47 2 e47 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e49 : slopeOrbit 1053 17 49 = 889 :=
    slopeOrbit_step_eval 48 0 e48 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e50 : slopeOrbit 1053 17 50 = 725 :=
    slopeOrbit_step_eval 49 0 e49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e51 : slopeOrbit 1053 17 51 = 397 :=
    slopeOrbit_step_eval 50 0 e50 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e52 : slopeOrbit 1053 17 52 = 535 :=
    slopeOrbit_step_eval 51 1 e51 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e53 : slopeOrbit 1053 17 53 = 17 :=
    slopeOrbit_step_eval 52 0 e52 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e54 : slopeOrbit 1053 17 54 = 35 :=
    slopeOrbit_step_eval 53 5 e53 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1053 17 54 = slopeOrbit 1053 17 1
    rw [e54, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rfl
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e26] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e27] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e28] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e29] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e30] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e31] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e32] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e33] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e34] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e35] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e36] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e37] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e38] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e39] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e40] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e41] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e42] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e43] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e44] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e45] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e46] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e47] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e48] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e49] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e50] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e51] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e52] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e53] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(1053,17)`: the pair is NEW - not a row of the certified survivor table. -/
theorem elcNewPair_1053_17 :
    (1053, 17) ∉ sreClass1ThresholdTable.map (fun e => (e.1, e.2.1)) := by
  decide

/-- `(1053,17)`: the deep threshold at `(b, c) = (1, 53)` clears (the first
certified spaced-share parameters surviving `emc2_deep_spacedShare_threshold`'s
necessary condition). -/
theorem elcDeepClear_1053_17 : 768 * (((63 + 53) / 53) * 1) ≤ 31 * 53 := by
  norm_num

/-- `(1053,17)`: the class-2 (tower) corrected cap, conditional on EXACTLY the
share + the per-context numeric regime (spacing is CERTIFIED). -/
theorem elcClass2Cap_1053_17 (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4)
    (hq : (class1SlopeDatum ctx).q = 1053)
    (hK : (class1SlopeDatum ctx).K₀ = 17)
    (hshare : 53 * emcFibreExitMass ctx 2 ≤ 1 * emExitMass ctx)
    (hreg : 1536 * (((ctx.n24CarryData.r + 53) / 53)
          * (1 * ((emW ctx + ctx.n24CarryData.r)
              * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))))
        ≤ 31 * (53 * ctx.shell.X)) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
      ≤ emcCap ctx :=
  emc2_cap_of_spacedShare ctx 2 hband
    (elcDatum_of_band4Cert ctx hq hK (by norm_num) elcCertB_1053_17.1
      elcCertB_1053_17.2 2 (Or.inr rfl) hshare hreg)

/-- `(1053,17)`: the class-1 CORRECTED ABSORPTION shape (the capstone
`class1CapAbsorption` field form) at a `q ≥ 200` pair, conditional on the share
+ the regime - territory un-enumerated by the survivor table. -/
theorem elcClass1Absorption_1053_17 (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4)
    (hq : (class1SlopeDatum ctx).q = 1053)
    (hK : (class1SlopeDatum ctx).K₀ = 17)
    (hshare : 53 * emcFibreExitMass ctx 1 ≤ 1 * emExitMass ctx)
    (hreg : 1536 * (((ctx.n24CarryData.r + 53) / 53)
          * (1 * ((emW ctx + ctx.n24CarryData.r)
              * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))))
        ≤ 31 * (53 * ctx.shell.X)) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6
          * (ctx.shell.X : ℝ) := by
  have h := emc2_cap_of_spacedShare ctx 1 hband
    (elcDatum_of_band4Cert ctx hq hK (by norm_num) elcCertB_1053_17.1
      elcCertB_1053_17.2 1 (Or.inl rfl) hshare hreg)
  rw [routedClassMass_one_eq_card_mul_Y] at h
  rwa [emcCap_eq_corrected] at h

/-- `(1059,31)`: period `52`, band-4 residue set `{48}` (value `89`), `b₄ = 1`;
deep threshold `768·((63+52)/52) = 1536 ≤ 1612 = 31·52` CLEARS. -/
private theorem elcCertB_1059_31 :
    slopeOrbit 1059 31 (1 + 52) = slopeOrbit 1059 31 1
      ∧ ∀ j, 1 ≤ j → j ≤ 52 →
          canonGap 1059 (slopeOrbit 1059 31 j) = 4 → j = 48 := by
  have e0 : slopeOrbit 1059 31 0 = 31 := rfl
  have e1 : slopeOrbit 1059 31 1 = 925 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1059 31 2 = 791 :=
    slopeOrbit_step_eval 1 0 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 1059 31 3 = 523 :=
    slopeOrbit_step_eval 2 0 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 1059 31 4 = 1033 :=
    slopeOrbit_step_eval 3 1 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 1059 31 5 = 1007 :=
    slopeOrbit_step_eval 4 0 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 1059 31 6 = 955 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 1059 31 7 = 851 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 1059 31 8 = 643 :=
    slopeOrbit_step_eval 7 0 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 1059 31 9 = 227 :=
    slopeOrbit_step_eval 8 0 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 1059 31 10 = 757 :=
    slopeOrbit_step_eval 9 2 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 1059 31 11 = 455 :=
    slopeOrbit_step_eval 10 0 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 1059 31 12 = 761 :=
    slopeOrbit_step_eval 11 1 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 1059 31 13 = 463 :=
    slopeOrbit_step_eval 12 0 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 1059 31 14 = 793 :=
    slopeOrbit_step_eval 13 1 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 1059 31 15 = 527 :=
    slopeOrbit_step_eval 14 0 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 1059 31 16 = 1049 :=
    slopeOrbit_step_eval 15 1 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 1059 31 17 = 1039 :=
    slopeOrbit_step_eval 16 0 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 1059 31 18 = 1019 :=
    slopeOrbit_step_eval 17 0 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 1059 31 19 = 979 :=
    slopeOrbit_step_eval 18 0 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 1059 31 20 = 899 :=
    slopeOrbit_step_eval 19 0 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 1059 31 21 = 739 :=
    slopeOrbit_step_eval 20 0 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 1059 31 22 = 419 :=
    slopeOrbit_step_eval 21 0 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 1059 31 23 = 617 :=
    slopeOrbit_step_eval 22 1 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 1059 31 24 = 175 :=
    slopeOrbit_step_eval 23 0 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 1059 31 25 = 341 :=
    slopeOrbit_step_eval 24 2 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 1059 31 26 = 305 :=
    slopeOrbit_step_eval 25 1 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 1059 31 27 = 161 :=
    slopeOrbit_step_eval 26 1 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 1059 31 28 = 229 :=
    slopeOrbit_step_eval 27 2 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 1059 31 29 = 773 :=
    slopeOrbit_step_eval 28 2 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 1059 31 30 = 487 :=
    slopeOrbit_step_eval 29 0 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : slopeOrbit 1059 31 31 = 889 :=
    slopeOrbit_step_eval 30 1 e30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e32 : slopeOrbit 1059 31 32 = 719 :=
    slopeOrbit_step_eval 31 0 e31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e33 : slopeOrbit 1059 31 33 = 379 :=
    slopeOrbit_step_eval 32 0 e32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e34 : slopeOrbit 1059 31 34 = 457 :=
    slopeOrbit_step_eval 33 1 e33 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e35 : slopeOrbit 1059 31 35 = 769 :=
    slopeOrbit_step_eval 34 1 e34 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e36 : slopeOrbit 1059 31 36 = 479 :=
    slopeOrbit_step_eval 35 0 e35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e37 : slopeOrbit 1059 31 37 = 857 :=
    slopeOrbit_step_eval 36 1 e36 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e38 : slopeOrbit 1059 31 38 = 655 :=
    slopeOrbit_step_eval 37 0 e37 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e39 : slopeOrbit 1059 31 39 = 251 :=
    slopeOrbit_step_eval 38 0 e38 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e40 : slopeOrbit 1059 31 40 = 949 :=
    slopeOrbit_step_eval 39 2 e39 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e41 : slopeOrbit 1059 31 41 = 839 :=
    slopeOrbit_step_eval 40 0 e40 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e42 : slopeOrbit 1059 31 42 = 619 :=
    slopeOrbit_step_eval 41 0 e41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e43 : slopeOrbit 1059 31 43 = 179 :=
    slopeOrbit_step_eval 42 0 e42 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e44 : slopeOrbit 1059 31 44 = 373 :=
    slopeOrbit_step_eval 43 2 e43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e45 : slopeOrbit 1059 31 45 = 433 :=
    slopeOrbit_step_eval 44 1 e44 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e46 : slopeOrbit 1059 31 46 = 673 :=
    slopeOrbit_step_eval 45 1 e45 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e47 : slopeOrbit 1059 31 47 = 287 :=
    slopeOrbit_step_eval 46 0 e46 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e48 : slopeOrbit 1059 31 48 = 89 :=
    slopeOrbit_step_eval 47 1 e47 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e49 : slopeOrbit 1059 31 49 = 365 :=
    slopeOrbit_step_eval 48 3 e48 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e50 : slopeOrbit 1059 31 50 = 401 :=
    slopeOrbit_step_eval 49 1 e49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e51 : slopeOrbit 1059 31 51 = 545 :=
    slopeOrbit_step_eval 50 1 e50 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e52 : slopeOrbit 1059 31 52 = 31 :=
    slopeOrbit_step_eval 51 0 e51 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e53 : slopeOrbit 1059 31 53 = 925 :=
    slopeOrbit_step_eval 52 5 e52 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1059 31 53 = slopeOrbit 1059 31 1
    rw [e53, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e26] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e27] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e28] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e29] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e30] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e31] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e32] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e33] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e34] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e35] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e36] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e37] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e38] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e39] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e40] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e41] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e42] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e43] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e44] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e45] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e46] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e47] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rfl
    · rw [e49] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e50] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e51] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e52] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(1059,31)`: the pair is NEW - not a row of the certified survivor table. -/
theorem elcNewPair_1059_31 :
    (1059, 31) ∉ sreClass1ThresholdTable.map (fun e => (e.1, e.2.1)) := by
  decide

/-- `(1059,31)`: the deep threshold at `(b, c) = (1, 52)` clears (the first
certified spaced-share parameters surviving `emc2_deep_spacedShare_threshold`'s
necessary condition). -/
theorem elcDeepClear_1059_31 : 768 * (((63 + 52) / 52) * 1) ≤ 31 * 52 := by
  norm_num

/-- `(1059,31)`: the class-2 (tower) corrected cap, conditional on EXACTLY the
share + the per-context numeric regime (spacing is CERTIFIED). -/
theorem elcClass2Cap_1059_31 (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4)
    (hq : (class1SlopeDatum ctx).q = 1059)
    (hK : (class1SlopeDatum ctx).K₀ = 31)
    (hshare : 52 * emcFibreExitMass ctx 2 ≤ 1 * emExitMass ctx)
    (hreg : 1536 * (((ctx.n24CarryData.r + 52) / 52)
          * (1 * ((emW ctx + ctx.n24CarryData.r)
              * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))))
        ≤ 31 * (52 * ctx.shell.X)) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
      ≤ emcCap ctx :=
  emc2_cap_of_spacedShare ctx 2 hband
    (elcDatum_of_band4Cert ctx hq hK (by norm_num) elcCertB_1059_31.1
      elcCertB_1059_31.2 2 (Or.inr rfl) hshare hreg)

/-- `(1059,31)`: the class-1 CORRECTED ABSORPTION shape (the capstone
`class1CapAbsorption` field form) at a `q ≥ 200` pair, conditional on the share
+ the regime - territory un-enumerated by the survivor table. -/
theorem elcClass1Absorption_1059_31 (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4)
    (hq : (class1SlopeDatum ctx).q = 1059)
    (hK : (class1SlopeDatum ctx).K₀ = 31)
    (hshare : 52 * emcFibreExitMass ctx 1 ≤ 1 * emExitMass ctx)
    (hreg : 1536 * (((ctx.n24CarryData.r + 52) / 52)
          * (1 * ((emW ctx + ctx.n24CarryData.r)
              * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))))
        ≤ 31 * (52 * ctx.shell.X)) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6
          * (ctx.shell.X : ℝ) := by
  have h := emc2_cap_of_spacedShare ctx 1 hband
    (elcDatum_of_band4Cert ctx hq hK (by norm_num) elcCertB_1059_31.1
      elcCertB_1059_31.2 1 (Or.inl rfl) hshare hreg)
  rw [routedClassMass_one_eq_card_mul_Y] at h
  rwa [emcCap_eq_corrected] at h

/-- `(1065,17)`: period `69`, band-4 residue set `{56}` (value `113`), `b₄ = 1`;
deep threshold `768·((63+69)/69) = 768 ≤ 2139 = 31·69` CLEARS. -/
private theorem elcCertB_1065_17 :
    slopeOrbit 1065 17 (1 + 69) = slopeOrbit 1065 17 1
      ∧ ∀ j, 1 ≤ j → j ≤ 69 →
          canonGap 1065 (slopeOrbit 1065 17 j) = 4 → j = 56 := by
  have e0 : slopeOrbit 1065 17 0 = 17 := rfl
  have e1 : slopeOrbit 1065 17 1 = 23 :=
    slopeOrbit_step_eval 0 5 e0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e2 : slopeOrbit 1065 17 2 = 407 :=
    slopeOrbit_step_eval 1 5 e1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e3 : slopeOrbit 1065 17 3 = 563 :=
    slopeOrbit_step_eval 2 1 e2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e4 : slopeOrbit 1065 17 4 = 61 :=
    slopeOrbit_step_eval 3 0 e3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e5 : slopeOrbit 1065 17 5 = 887 :=
    slopeOrbit_step_eval 4 4 e4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e6 : slopeOrbit 1065 17 6 = 709 :=
    slopeOrbit_step_eval 5 0 e5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e7 : slopeOrbit 1065 17 7 = 353 :=
    slopeOrbit_step_eval 6 0 e6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e8 : slopeOrbit 1065 17 8 = 347 :=
    slopeOrbit_step_eval 7 1 e7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e9 : slopeOrbit 1065 17 9 = 323 :=
    slopeOrbit_step_eval 8 1 e8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e10 : slopeOrbit 1065 17 10 = 227 :=
    slopeOrbit_step_eval 9 1 e9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e11 : slopeOrbit 1065 17 11 = 751 :=
    slopeOrbit_step_eval 10 2 e10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e12 : slopeOrbit 1065 17 12 = 437 :=
    slopeOrbit_step_eval 11 0 e11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e13 : slopeOrbit 1065 17 13 = 683 :=
    slopeOrbit_step_eval 12 1 e12 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e14 : slopeOrbit 1065 17 14 = 301 :=
    slopeOrbit_step_eval 13 0 e13 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e15 : slopeOrbit 1065 17 15 = 139 :=
    slopeOrbit_step_eval 14 1 e14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e16 : slopeOrbit 1065 17 16 = 47 :=
    slopeOrbit_step_eval 15 2 e15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e17 : slopeOrbit 1065 17 17 = 439 :=
    slopeOrbit_step_eval 16 4 e16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e18 : slopeOrbit 1065 17 18 = 691 :=
    slopeOrbit_step_eval 17 1 e17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e19 : slopeOrbit 1065 17 19 = 317 :=
    slopeOrbit_step_eval 18 0 e18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e20 : slopeOrbit 1065 17 20 = 203 :=
    slopeOrbit_step_eval 19 1 e19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e21 : slopeOrbit 1065 17 21 = 559 :=
    slopeOrbit_step_eval 20 2 e20 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e22 : slopeOrbit 1065 17 22 = 53 :=
    slopeOrbit_step_eval 21 0 e21 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e23 : slopeOrbit 1065 17 23 = 631 :=
    slopeOrbit_step_eval 22 4 e22 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e24 : slopeOrbit 1065 17 24 = 197 :=
    slopeOrbit_step_eval 23 0 e23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e25 : slopeOrbit 1065 17 25 = 511 :=
    slopeOrbit_step_eval 24 2 e24 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e26 : slopeOrbit 1065 17 26 = 979 :=
    slopeOrbit_step_eval 25 1 e25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e27 : slopeOrbit 1065 17 27 = 893 :=
    slopeOrbit_step_eval 26 0 e26 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e28 : slopeOrbit 1065 17 28 = 721 :=
    slopeOrbit_step_eval 27 0 e27 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e29 : slopeOrbit 1065 17 29 = 377 :=
    slopeOrbit_step_eval 28 0 e28 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e30 : slopeOrbit 1065 17 30 = 443 :=
    slopeOrbit_step_eval 29 1 e29 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e31 : slopeOrbit 1065 17 31 = 707 :=
    slopeOrbit_step_eval 30 1 e30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e32 : slopeOrbit 1065 17 32 = 349 :=
    slopeOrbit_step_eval 31 0 e31 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e33 : slopeOrbit 1065 17 33 = 331 :=
    slopeOrbit_step_eval 32 1 e32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e34 : slopeOrbit 1065 17 34 = 259 :=
    slopeOrbit_step_eval 33 1 e33 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e35 : slopeOrbit 1065 17 35 = 1007 :=
    slopeOrbit_step_eval 34 2 e34 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e36 : slopeOrbit 1065 17 36 = 949 :=
    slopeOrbit_step_eval 35 0 e35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e37 : slopeOrbit 1065 17 37 = 833 :=
    slopeOrbit_step_eval 36 0 e36 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e38 : slopeOrbit 1065 17 38 = 601 :=
    slopeOrbit_step_eval 37 0 e37 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e39 : slopeOrbit 1065 17 39 = 137 :=
    slopeOrbit_step_eval 38 0 e38 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e40 : slopeOrbit 1065 17 40 = 31 :=
    slopeOrbit_step_eval 39 2 e39 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e41 : slopeOrbit 1065 17 41 = 919 :=
    slopeOrbit_step_eval 40 5 e40 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e42 : slopeOrbit 1065 17 42 = 773 :=
    slopeOrbit_step_eval 41 0 e41 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e43 : slopeOrbit 1065 17 43 = 481 :=
    slopeOrbit_step_eval 42 0 e42 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e44 : slopeOrbit 1065 17 44 = 859 :=
    slopeOrbit_step_eval 43 1 e43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e45 : slopeOrbit 1065 17 45 = 653 :=
    slopeOrbit_step_eval 44 0 e44 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e46 : slopeOrbit 1065 17 46 = 241 :=
    slopeOrbit_step_eval 45 0 e45 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e47 : slopeOrbit 1065 17 47 = 863 :=
    slopeOrbit_step_eval 46 2 e46 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e48 : slopeOrbit 1065 17 48 = 661 :=
    slopeOrbit_step_eval 47 0 e47 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e49 : slopeOrbit 1065 17 49 = 257 :=
    slopeOrbit_step_eval 48 0 e48 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e50 : slopeOrbit 1065 17 50 = 991 :=
    slopeOrbit_step_eval 49 2 e49 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e51 : slopeOrbit 1065 17 51 = 917 :=
    slopeOrbit_step_eval 50 0 e50 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e52 : slopeOrbit 1065 17 52 = 769 :=
    slopeOrbit_step_eval 51 0 e51 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e53 : slopeOrbit 1065 17 53 = 473 :=
    slopeOrbit_step_eval 52 0 e52 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e54 : slopeOrbit 1065 17 54 = 827 :=
    slopeOrbit_step_eval 53 1 e53 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e55 : slopeOrbit 1065 17 55 = 589 :=
    slopeOrbit_step_eval 54 0 e54 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e56 : slopeOrbit 1065 17 56 = 113 :=
    slopeOrbit_step_eval 55 0 e55 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e57 : slopeOrbit 1065 17 57 = 743 :=
    slopeOrbit_step_eval 56 3 e56 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e58 : slopeOrbit 1065 17 58 = 421 :=
    slopeOrbit_step_eval 57 0 e57 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e59 : slopeOrbit 1065 17 59 = 619 :=
    slopeOrbit_step_eval 58 1 e58 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e60 : slopeOrbit 1065 17 60 = 173 :=
    slopeOrbit_step_eval 59 0 e59 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e61 : slopeOrbit 1065 17 61 = 319 :=
    slopeOrbit_step_eval 60 2 e60 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e62 : slopeOrbit 1065 17 62 = 211 :=
    slopeOrbit_step_eval 61 1 e61 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e63 : slopeOrbit 1065 17 63 = 623 :=
    slopeOrbit_step_eval 62 2 e62 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e64 : slopeOrbit 1065 17 64 = 181 :=
    slopeOrbit_step_eval 63 0 e63 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e65 : slopeOrbit 1065 17 65 = 383 :=
    slopeOrbit_step_eval 64 2 e64 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e66 : slopeOrbit 1065 17 66 = 467 :=
    slopeOrbit_step_eval 65 1 e65 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e67 : slopeOrbit 1065 17 67 = 803 :=
    slopeOrbit_step_eval 66 1 e66 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e68 : slopeOrbit 1065 17 68 = 541 :=
    slopeOrbit_step_eval 67 0 e67 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e69 : slopeOrbit 1065 17 69 = 17 :=
    slopeOrbit_step_eval 68 0 e68 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have e70 : slopeOrbit 1065 17 70 = 23 :=
    slopeOrbit_step_eval 69 5 e69 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · show slopeOrbit 1065 17 70 = slopeOrbit 1065 17 1
    rw [e70, e1]
  · intro j h1 h2 hband
    interval_cases j
    · rw [e1] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e2] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e3] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e4] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e5] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e6] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e7] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e8] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e9] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e10] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e11] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e12] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e13] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e14] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e15] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e16] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e17] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e18] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e19] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e20] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e21] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e22] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e23] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e24] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e25] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e26] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e27] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e28] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e29] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e30] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e31] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e32] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e33] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e34] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e35] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e36] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e37] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e38] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e39] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e40] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))
    · rw [e41] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e42] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e43] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e44] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e45] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e46] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e47] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e48] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e49] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e50] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e51] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e52] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e53] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e54] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e55] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rfl
    · rw [e57] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e58] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e59] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e60] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e61] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e62] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e63] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e64] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e65] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e66] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e67] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e68] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inl (by norm_num)))
    · rw [e69] at hband
      exact absurd hband (canonGap_ne_four_of_band (Or.inr (by norm_num)))

/-- `(1065,17)`: the pair is NEW - not a row of the certified survivor table. -/
theorem elcNewPair_1065_17 :
    (1065, 17) ∉ sreClass1ThresholdTable.map (fun e => (e.1, e.2.1)) := by
  decide

/-- `(1065,17)`: the deep threshold at `(b, c) = (1, 69)` clears (the first
certified spaced-share parameters surviving `emc2_deep_spacedShare_threshold`'s
necessary condition). -/
theorem elcDeepClear_1065_17 : 768 * (((63 + 69) / 69) * 1) ≤ 31 * 69 := by
  norm_num

/-- `(1065,17)`: the class-2 (tower) corrected cap, conditional on EXACTLY the
share + the per-context numeric regime (spacing is CERTIFIED). -/
theorem elcClass2Cap_1065_17 (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4)
    (hq : (class1SlopeDatum ctx).q = 1065)
    (hK : (class1SlopeDatum ctx).K₀ = 17)
    (hshare : 69 * emcFibreExitMass ctx 2 ≤ 1 * emExitMass ctx)
    (hreg : 1536 * (((ctx.n24CarryData.r + 69) / 69)
          * (1 * ((emW ctx + ctx.n24CarryData.r)
              * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))))
        ≤ 31 * (69 * ctx.shell.X)) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
      ≤ emcCap ctx :=
  emc2_cap_of_spacedShare ctx 2 hband
    (elcDatum_of_band4Cert ctx hq hK (by norm_num) elcCertB_1065_17.1
      elcCertB_1065_17.2 2 (Or.inr rfl) hshare hreg)

/-- `(1065,17)`: the class-1 CORRECTED ABSORPTION shape (the capstone
`class1CapAbsorption` field form) at a `q ≥ 200` pair, conditional on the share
+ the regime - territory un-enumerated by the survivor table. -/
theorem elcClass1Absorption_1065_17 (ctx : ActualFailureContext)
    (hband : fixedFamilyRecurrentBand ctx ≤ 4)
    (hq : (class1SlopeDatum ctx).q = 1065)
    (hK : (class1SlopeDatum ctx).K₀ = 17)
    (hshare : 69 * emcFibreExitMass ctx 1 ≤ 1 * emExitMass ctx)
    (hreg : 1536 * (((ctx.n24CarryData.r + 69) / 69)
          * (1 * ((emW ctx + ctx.n24CarryData.r)
              * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))))
        ≤ 31 * (69 * ctx.shell.X)) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6
          * (ctx.shell.X : ℝ) := by
  have h := emc2_cap_of_spacedShare ctx 1 hband
    (elcDatum_of_band4Cert ctx hq hK (by norm_num) elcCertB_1065_17.1
      elcCertB_1065_17.2 1 (Or.inl rfl) hshare hreg)
  rw [routedClassMass_one_eq_card_mul_Y] at h
  rwa [emcCap_eq_corrected] at h

/-- The 10 certified `b₄ = 1` long-cycle representatives (`(q, K₀, c, j₄)`). -/
def elcLongCycleTable : List (ℕ × ℕ × ℕ × ℕ) := [ (303, 5, 55, 35), (909, 15, 55, 35),
   (921, 7, 51, 9), (931, 9, 61, 7), (937, 17, 54, 34), (979, 19, 56, 41), (987, 5, 70, 48),
   (1053, 17, 53, 2), (1059, 31, 52, 48), (1065, 17, 69, 56)]

theorem elcLongCycleTable_length : elcLongCycleTable.length = 10 := rfl

/-- The 36 moduli of `q < 2000` carrying `b₄ = 1` deep-clearing pairs (survey
tabulation; 4578 pairs in total - documentation list). -/
def elcLongCycleModuli : List ℕ := [ 303, 909, 921, 931, 937, 979, 987, 1053, 1059, 1065, 1115,
   1157, 1163, 1165, 1183, 1243, 1251, 1255, 1289, 1351, 1375, 1393, 1405, 1421, 1441, 1457, 1515,
   1521, 1553, 1561, 1683, 1765, 1767, 1779, 1893, 1897]

theorem elcLongCycleModuli_length : elcLongCycleModuli.length = 36 := rfl

/-! ## Part 4.  Wiring: the off-pin core through the exit-silent stratum -/

/-- The context's slope datum is an exit-silent table pair. -/
def ElcSilentCtx (ctx : ActualFailureContext) : Prop :=
  ∃ e ∈ elcExitSilentTable, (class1SlopeDatum ctx).q = e.1
    ∧ (class1SlopeDatum ctx).K₀ = e.2.1

/-- The off-pin demand holds at EVERY exit-silent context (unconditional). -/
theorem elcOffPin_at_silent (ctx : ActualFailureContext) (h : ElcSilentCtx ctx) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 3 ≤ emcCap ctx
      ∧ routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 4 ≤ emcCap ctx
      ∧ routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
          ≤ emcCap ctx := by
  obtain ⟨⟨qv, Kv, cv⟩, hmem, hq, hK⟩ := h
  exact elcOffPinCaps_of_mem ctx hmem hq hK

/-- **THE HONEST RESIDUAL**: the off-pin demand at deep pin-free contexts whose
datum is NOT an exit-silent pair - everything the certificates do not cover. -/
def ElcOffPinUncoveredResidual : Prop :=
  ∀ ctx : ActualFailureContext, 2 ^ 986891 < ctx.X →
    ¬ OrbitBandPinned ctx 2 → ¬ OrbitBandPinned ctx 3 →
    ¬ OrbitBandPinned ctx 4 → ¬ ElcSilentCtx ctx →
    (routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 3 ≤ emcCap ctx
      ∧ routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 4 ≤ emcCap ctx
      ∧ routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 5
          ≤ emcCap ctx)

/-- **The off-pin core from the uncovered residual**: the exit-silent stratum is
carved out unconditionally; only the uncovered contexts remain demanded. -/
theorem elcOffPin_of_uncoveredResidual (h : ElcOffPinUncoveredResidual) :
    ExitMassControlOffPin := by
  intro ctx hX h2 h3 h4
  by_cases hcov : ElcSilentCtx ctx
  · exact elcOffPin_at_silent ctx hcov
  · exact h ctx hX h2 h3 h4 hcov

/-- The FULL core from the uncovered residual + the open voiding axis (the wave-19
split `exitMassControl_iff_split`). -/
theorem elcCore_of_uncoveredResidual_and_voiding (h : ElcOffPinUncoveredResidual)
    (hvoid : DeepOrbitPinVoiding) : ExitMassControlCore :=
  exitMassControl_iff_split.mpr ⟨hvoid, elcOffPin_of_uncoveredResidual h⟩

/-- The keystone form: the uncovered residual + the keystone's kept `deepOrbitPin`
field rebuild the FULL `ExitMassControlCore` (the wave-20 keystone shape). -/
theorem elcKeystoneCore_of_uncoveredResidual (h : ElcOffPinUncoveredResidual)
    (R : Erdos260KeystoneResidual) : ExitMassControlCore :=
  elcCore_of_uncoveredResidual_and_voiding h R.deepOrbitPin

/-- The regime route commutes: the spaced-share regime alone (the wave-19 shape)
also factors through this module's split - sanity that nothing was lost. -/
theorem elcOffPin_of_regime (h : EmcOffPinSpacedShareRegime) :
    ExitMassControlOffPin :=
  emc2_offPin_of_regime h

/-! ## Part 5.  Machine-readable status (honest) -/

/-- Honest machine-readable status of the exit-light cycle certificate pass. -/
def exitLightCycleCertificatesStatus : List String :=
  [ "SUBJECT (wave-20 exit-light long cycles): hunt + certify (q, K0) pairs outside the " ++
      "survivor table feeding EmcSpacedShareDatum at deep scales, and fire what the in-tree " ++
      "machinery supports of ExitMassControlOffPin at them.  Complete survey: q odd in [3, " ++
      "2000), ALL 1 <= K0 < q - 999000 pairs, every one purely periodic from index 1 (no " ++
      "transient loss).",
    "SURVEY OUTCOME 1 (the prize stratum): EXACTLY 384 EXIT-SILENT pairs (every one-period " ++
      "band >= 5; 62 moduli q = 31..1953, the moduli with a divisor 2^g - 1, g >= 5; periods " ++
      "1-2; 34 pairs have q < 200 and are in NO survivor table - the sweeps kept only " ++
      "band-4-bearing pairs).  At these pairs the genuine route is identically 0 on starts, " ++
      "classes 1-5 fibres are EMPTY (elcSilent_*, dispatcher elcSilentEmpty_of_mem), the b = 0 " ++
      "spaced-share datum is PROVED (elcDatum_of_empty / elcDatum_of_mem), and the " ++
      "ExitMassControlOffPin conclusion holds OUTRIGHT - masses are 0 <= (31/1536)X with NO " ++
      "deep / pin / band / share / regime hypothesis (elcOffPinCaps_of_mem, " ++
      "elcOffPin_at_silent).  Class-1 fibre is empty too (elcClass1Empty_of_mem).",
    "SURVEY OUTCOME 2 (the brief's headline target): 4578 pairs with b4 = 1 and deep-clearing " ++
      "period c >= 50 exist below q = 2000 (36 moduli, min q = 303 with c = 55, periods up to " ++
      "70+; NONE below q = 200 - the wave-20 note 'every certified period >= 64 carries b4 >= " ++
      "4' is about the q < 200 table only, and the hunt target materializes just past the " ++
      "horizon).  Ten representatives certified (elcCertB_*: kernel slopeOrbit_step_eval " ++
      "chains, return collision, SINGLETON band-4 residue), one per modulus for the 10 smallest " ++
      "moduli incl. the overlap-1 pairs (987,5) c=70 and (1065,17) c=69; all ten proved NEW vs " ++
      "sreClass1ThresholdTable (elcNewPair_*).",
    "SURVEY OUTCOME 3 (the regime-feasibility verdict): measuring each class 3/4/5 by its " ++
      "MAXIMAL certifiable spacing modulus (gcd of the class band-residue differences with c; " ++
      "classes read bands 3 / 2 / {1,4}), NO pair in [3, 2000) carries a NONZERO class-3/4/5 " ++
      "fibre with spacing >= 50.  The full off-pin spaced-share regime with nonzero shares is " ++
      "EMPTY in range; the only feasible pairs are the 384 exit-silent ones (where it holds " ++
      "with b = 0).  The b4 = 1 long cycles feed classes 1/2 (the band-4 readers) instead.",
    "THE EXACT DEEP BOUNDARY (proved): the in-tree forced threshold 768*((63+c)/c)*b <= 31*c " ++
      "at b = 1 clears IFF c >= 50 (elcDeepThresholdClears / elcDeepThresholdBlocked: overlap " ++
      "factor 2 on 50..63 needs 1536 <= 31c i.e. c >= 50; overlap 1 from c = 64).  This " ++
      "sharpens both the wave-20 note (c >= 64) and the brief's real-variable estimate (c >= " ++
      "54).",
    "THE SHARE/TILING VERDICT (NEGATIVE at b >= 1): c-spacing + reach containment do NOT " ++
      "imply the b = 1 share c*fibreExit <= 1*totalExit - formal counterexample " ++
      "elcShare_not_from_spacing_alone (weight concentrated on the fibre residue).  The in-tree " ++
      "overlap bound emc2_fibreDevMass_le_overlap bounds the fibre's deviation mass by overlap " ++
      "copies of the fibre's OWN restricted exit mass and cannot compare fibre vs total; at " ++
      "deep scales r >= 63 grows with L so window tiling (r + 1 <= c) eventually fails for " ++
      "every fixed c.  The share IS the equidistribution content; at the 10 certified pairs the " ++
      "class-1/2 spacing is PROVED (elcSpacing_of_band4Cert) and the residual is EXACTLY share " ++
      "+ per-context numeric regime (elcDatum_of_band4Cert).",
    "CONDITIONAL CAPS AT THE NEW PAIRS: per pair, the class-2 (tower) corrected cap " ++
      "elcClass2Cap_<q>_<K0> and the class-1 CORRECTED ABSORPTION shape " ++
      "elcClass1Absorption_<q>_<K0> (card*Y <= (cStar*xi/6)*X via " ++
      "routedClassMass_one_eq_card_mul_Y + emcCap_eq_corrected) - the first " ++
      "deep-threshold-clearing certified spaced-share parameters (every sreClass1ThresholdTable " ++
      "row overshoots: emcDeepProportionalClearedPairs_eq_nil), and class-1 absorption coverage " ++
      "at q >= 200 territory the survivor table does not enumerate.  Hypotheses kept honest: " ++
      "share + regime only.",
    "WIRING (additive, v19/v20 shapes): ElcSilentCtx (datum in the 384-row table " ++
      "elcExitSilentTable) -> off-pin caps unconditional (elcOffPin_at_silent); " ++
      "ElcOffPinUncoveredResidual (the demand at deep pin-free NON-silent contexts) -> " ++
      "ExitMassControlOffPin (elcOffPin_of_uncoveredResidual) -> with DeepOrbitPinVoiding the " ++
      "FULL ExitMassControlCore (elcCore_of_uncoveredResidual_and_voiding), keystone form " ++
      "elcKeystoneCore_of_uncoveredResidual via Erdos260KeystoneResidual.deepOrbitPin.  The " ++
      "off-pin demand is thus REDUCED: the exit-silent stratum is carved out unconditionally, " ++
      "shrinking the wave-19 regime residual.",
    "HONEST RESIDUAL: (i) ElcOffPinUncoveredResidual - deep pin-free contexts at " ++
      "non-exit-silent data; (ii) at the certified b4 = 1 pairs, the share c*fibreExit <= " ++
      "totalExit and the ctx numeric regime (both genuinely open - no in-tree equidistribution " ++
      "atom); (iii) pairs beyond q = 2000 are unscanned; (iv) the b4 = 1 caps cover classes 1/2 " ++
      "only - classes 3/4/5 at nonzero bands have NO certifiable spacing in range (Outcome 3).",
    "HYGIENE: additive only - ONE new module, no existing file edited, NOT root-wired (built " ++
      "standalone as Erdos260.ExitLightCycleCertificates); no sorry / admit / new axiom / " ++
      "native_decide (decide only on small closed Fin / list-literal goals); every key " ++
      "declaration passes #print axioms within [propext, Classical.choice, Quot.sound]." ]

/-- The status ledger is non-empty (honest, non-vacuous). -/
theorem exitLightCycleCertificatesStatus_nonempty :
    exitLightCycleCertificatesStatus ≠ [] := by
  simp [exitLightCycleCertificatesStatus]

/-! ## Part 6.  Axiom-cleanliness audit
Expected axioms `[propext, Classical.choice, Quot.sound]` or fewer. -/

#print axioms elcDvd_of_residue_eq
#print axioms elcRouteZero_of_deepCert
#print axioms elcFibreEmpty_of_deepCert
#print axioms elcMassCap_of_empty
#print axioms elcDatum_of_empty
#print axioms elcFibreBand4
#print axioms elcBand4Residue_of_cert
#print axioms elcSpacing_of_band4Cert
#print axioms elcDatum_of_band4Cert
#print axioms elcDeepThresholdClears
#print axioms elcDeepThresholdBlocked
#print axioms elcShare_not_from_spacing_alone
#print axioms elcSilent_31_1
#print axioms elcSilent_31_2
#print axioms elcSilent_31_4
#print axioms elcSilent_31_8
#print axioms elcSilent_31_16
#print axioms elcSilent_63_1
#print axioms elcSilent_63_2
#print axioms elcSilent_63_4
#print axioms elcSilent_63_8
#print axioms elcSilent_63_16
#print axioms elcSilent_63_32
#print axioms elcSilent_93_3
#print axioms elcSilent_93_6
#print axioms elcSilent_93_12
#print axioms elcSilent_93_24
#print axioms elcSilent_93_48
#print axioms elcSilent_127_1
#print axioms elcSilent_127_2
#print axioms elcSilent_127_4
#print axioms elcSilent_127_8
#print axioms elcSilent_127_16
#print axioms elcSilent_127_32
#print axioms elcSilent_127_64
#print axioms elcSilent_155_5
#print axioms elcSilent_155_10
#print axioms elcSilent_155_20
#print axioms elcSilent_155_40
#print axioms elcSilent_155_80
#print axioms elcSilent_189_3
#print axioms elcSilent_189_6
#print axioms elcSilent_189_12
#print axioms elcSilent_189_24
#print axioms elcSilent_189_48
#print axioms elcSilent_189_96
#print axioms elcSilent_217_7
#print axioms elcSilent_217_14
#print axioms elcSilent_217_28
#print axioms elcSilent_217_56
#print axioms elcSilent_217_112
#print axioms elcSilent_255_1
#print axioms elcSilent_255_2
#print axioms elcSilent_255_4
#print axioms elcSilent_255_8
#print axioms elcSilent_255_16
#print axioms elcSilent_255_32
#print axioms elcSilent_255_64
#print axioms elcSilent_255_128
#print axioms elcSilent_279_9
#print axioms elcSilent_279_18
#print axioms elcSilent_279_36
#print axioms elcSilent_279_72
#print axioms elcSilent_279_144
#print axioms elcSilent_315_5
#print axioms elcSilent_315_10
#print axioms elcSilent_315_20
#print axioms elcSilent_315_40
#print axioms elcSilent_315_80
#print axioms elcSilent_315_160
#print axioms elcSilent_341_11
#print axioms elcSilent_341_22
#print axioms elcSilent_341_44
#print axioms elcSilent_341_88
#print axioms elcSilent_341_176
#print axioms elcSilent_381_3
#print axioms elcSilent_381_6
#print axioms elcSilent_381_12
#print axioms elcSilent_381_24
#print axioms elcSilent_381_48
#print axioms elcSilent_381_96
#print axioms elcSilent_381_192
#print axioms elcSilent_403_13
#print axioms elcSilent_403_26
#print axioms elcSilent_403_52
#print axioms elcSilent_403_104
#print axioms elcSilent_403_208
#print axioms elcSilent_441_7
#print axioms elcSilent_441_14
#print axioms elcSilent_441_28
#print axioms elcSilent_441_56
#print axioms elcSilent_441_112
#print axioms elcSilent_441_224
#print axioms elcSilent_465_15
#print axioms elcSilent_465_30
#print axioms elcSilent_465_60
#print axioms elcSilent_465_120
#print axioms elcSilent_465_240
#print axioms elcSilent_511_1
#print axioms elcSilent_511_2
#print axioms elcSilent_511_4
#print axioms elcSilent_511_8
#print axioms elcSilent_511_16
#print axioms elcSilent_511_32
#print axioms elcSilent_511_64
#print axioms elcSilent_511_128
#print axioms elcSilent_511_256
#print axioms elcSilent_527_17
#print axioms elcSilent_527_34
#print axioms elcSilent_527_68
#print axioms elcSilent_527_136
#print axioms elcSilent_527_272
#print axioms elcSilent_567_9
#print axioms elcSilent_567_18
#print axioms elcSilent_567_36
#print axioms elcSilent_567_72
#print axioms elcSilent_567_144
#print axioms elcSilent_567_288
#print axioms elcSilent_589_19
#print axioms elcSilent_589_38
#print axioms elcSilent_589_76
#print axioms elcSilent_589_152
#print axioms elcSilent_589_304
#print axioms elcSilent_635_5
#print axioms elcSilent_635_10
#print axioms elcSilent_635_20
#print axioms elcSilent_635_40
#print axioms elcSilent_635_80
#print axioms elcSilent_635_160
#print axioms elcSilent_635_320
#print axioms elcSilent_651_21
#print axioms elcSilent_651_42
#print axioms elcSilent_651_84
#print axioms elcSilent_651_168
#print axioms elcSilent_651_336
#print axioms elcSilent_693_11
#print axioms elcSilent_693_22
#print axioms elcSilent_693_44
#print axioms elcSilent_693_88
#print axioms elcSilent_693_176
#print axioms elcSilent_693_352
#print axioms elcSilent_713_23
#print axioms elcSilent_713_46
#print axioms elcSilent_713_92
#print axioms elcSilent_713_184
#print axioms elcSilent_713_368
#print axioms elcSilent_765_3
#print axioms elcSilent_765_6
#print axioms elcSilent_765_12
#print axioms elcSilent_765_24
#print axioms elcSilent_765_48
#print axioms elcSilent_765_96
#print axioms elcSilent_765_192
#print axioms elcSilent_765_384
#print axioms elcSilent_775_25
#print axioms elcSilent_775_50
#print axioms elcSilent_775_100
#print axioms elcSilent_775_200
#print axioms elcSilent_775_400
#print axioms elcSilent_819_13
#print axioms elcSilent_819_26
#print axioms elcSilent_819_52
#print axioms elcSilent_819_104
#print axioms elcSilent_819_208
#print axioms elcSilent_819_416
#print axioms elcSilent_837_27
#print axioms elcSilent_837_54
#print axioms elcSilent_837_108
#print axioms elcSilent_837_216
#print axioms elcSilent_837_432
#print axioms elcSilent_889_7
#print axioms elcSilent_889_14
#print axioms elcSilent_889_28
#print axioms elcSilent_889_56
#print axioms elcSilent_889_112
#print axioms elcSilent_889_224
#print axioms elcSilent_889_448
#print axioms elcSilent_899_29
#print axioms elcSilent_899_58
#print axioms elcSilent_899_116
#print axioms elcSilent_899_232
#print axioms elcSilent_899_464
#print axioms elcSilent_945_15
#print axioms elcSilent_945_30
#print axioms elcSilent_945_60
#print axioms elcSilent_945_120
#print axioms elcSilent_945_240
#print axioms elcSilent_945_480
#print axioms elcSilent_961_31
#print axioms elcSilent_961_62
#print axioms elcSilent_961_124
#print axioms elcSilent_961_248
#print axioms elcSilent_961_496
#print axioms elcSilent_1023_1
#print axioms elcSilent_1023_2
#print axioms elcSilent_1023_4
#print axioms elcSilent_1023_8
#print axioms elcSilent_1023_16
#print axioms elcSilent_1023_32
#print axioms elcSilent_1023_33
#print axioms elcSilent_1023_64
#print axioms elcSilent_1023_66
#print axioms elcSilent_1023_128
#print axioms elcSilent_1023_132
#print axioms elcSilent_1023_256
#print axioms elcSilent_1023_264
#print axioms elcSilent_1023_512
#print axioms elcSilent_1023_528
#print axioms elcSilent_1071_17
#print axioms elcSilent_1071_34
#print axioms elcSilent_1071_68
#print axioms elcSilent_1071_136
#print axioms elcSilent_1071_272
#print axioms elcSilent_1071_544
#print axioms elcSilent_1085_35
#print axioms elcSilent_1085_70
#print axioms elcSilent_1085_140
#print axioms elcSilent_1085_280
#print axioms elcSilent_1085_560
#print axioms elcSilent_1143_9
#print axioms elcSilent_1143_18
#print axioms elcSilent_1143_36
#print axioms elcSilent_1143_72
#print axioms elcSilent_1143_144
#print axioms elcSilent_1143_288
#print axioms elcSilent_1143_576
#print axioms elcSilent_1147_37
#print axioms elcSilent_1147_74
#print axioms elcSilent_1147_148
#print axioms elcSilent_1147_296
#print axioms elcSilent_1147_592
#print axioms elcSilent_1197_19
#print axioms elcSilent_1197_38
#print axioms elcSilent_1197_76
#print axioms elcSilent_1197_152
#print axioms elcSilent_1197_304
#print axioms elcSilent_1197_608
#print axioms elcSilent_1209_39
#print axioms elcSilent_1209_78
#print axioms elcSilent_1209_156
#print axioms elcSilent_1209_312
#print axioms elcSilent_1209_624
#print axioms elcSilent_1271_41
#print axioms elcSilent_1271_82
#print axioms elcSilent_1271_164
#print axioms elcSilent_1271_328
#print axioms elcSilent_1271_656
#print axioms elcSilent_1275_5
#print axioms elcSilent_1275_10
#print axioms elcSilent_1275_20
#print axioms elcSilent_1275_40
#print axioms elcSilent_1275_80
#print axioms elcSilent_1275_160
#print axioms elcSilent_1275_320
#print axioms elcSilent_1275_640
#print axioms elcSilent_1323_21
#print axioms elcSilent_1323_42
#print axioms elcSilent_1323_84
#print axioms elcSilent_1323_168
#print axioms elcSilent_1323_336
#print axioms elcSilent_1323_672
#print axioms elcSilent_1333_43
#print axioms elcSilent_1333_86
#print axioms elcSilent_1333_172
#print axioms elcSilent_1333_344
#print axioms elcSilent_1333_688
#print axioms elcSilent_1365_11
#print axioms elcSilent_1365_22
#print axioms elcSilent_1365_43
#print axioms elcSilent_1365_44
#print axioms elcSilent_1365_86
#print axioms elcSilent_1365_88
#print axioms elcSilent_1365_172
#print axioms elcSilent_1365_176
#print axioms elcSilent_1365_344
#print axioms elcSilent_1365_352
#print axioms elcSilent_1365_688
#print axioms elcSilent_1365_704
#print axioms elcSilent_1395_45
#print axioms elcSilent_1395_90
#print axioms elcSilent_1395_180
#print axioms elcSilent_1395_360
#print axioms elcSilent_1395_720
#print axioms elcSilent_1397_11
#print axioms elcSilent_1397_22
#print axioms elcSilent_1397_44
#print axioms elcSilent_1397_88
#print axioms elcSilent_1397_176
#print axioms elcSilent_1397_352
#print axioms elcSilent_1397_704
#print axioms elcSilent_1449_23
#print axioms elcSilent_1449_46
#print axioms elcSilent_1449_92
#print axioms elcSilent_1449_184
#print axioms elcSilent_1449_368
#print axioms elcSilent_1449_736
#print axioms elcSilent_1457_47
#print axioms elcSilent_1457_94
#print axioms elcSilent_1457_188
#print axioms elcSilent_1457_376
#print axioms elcSilent_1457_752
#print axioms elcSilent_1519_49
#print axioms elcSilent_1519_98
#print axioms elcSilent_1519_196
#print axioms elcSilent_1519_392
#print axioms elcSilent_1519_784
#print axioms elcSilent_1533_3
#print axioms elcSilent_1533_6
#print axioms elcSilent_1533_12
#print axioms elcSilent_1533_24
#print axioms elcSilent_1533_48
#print axioms elcSilent_1533_96
#print axioms elcSilent_1533_192
#print axioms elcSilent_1533_384
#print axioms elcSilent_1533_768
#print axioms elcSilent_1575_25
#print axioms elcSilent_1575_50
#print axioms elcSilent_1575_100
#print axioms elcSilent_1575_200
#print axioms elcSilent_1575_400
#print axioms elcSilent_1575_800
#print axioms elcSilent_1581_51
#print axioms elcSilent_1581_102
#print axioms elcSilent_1581_204
#print axioms elcSilent_1581_408
#print axioms elcSilent_1581_816
#print axioms elcSilent_1643_53
#print axioms elcSilent_1643_106
#print axioms elcSilent_1643_212
#print axioms elcSilent_1643_424
#print axioms elcSilent_1643_848
#print axioms elcSilent_1651_13
#print axioms elcSilent_1651_26
#print axioms elcSilent_1651_52
#print axioms elcSilent_1651_104
#print axioms elcSilent_1651_208
#print axioms elcSilent_1651_416
#print axioms elcSilent_1651_832
#print axioms elcSilent_1701_27
#print axioms elcSilent_1701_54
#print axioms elcSilent_1701_108
#print axioms elcSilent_1701_216
#print axioms elcSilent_1701_432
#print axioms elcSilent_1701_864
#print axioms elcSilent_1705_55
#print axioms elcSilent_1705_110
#print axioms elcSilent_1705_220
#print axioms elcSilent_1705_440
#print axioms elcSilent_1705_880
#print axioms elcSilent_1767_57
#print axioms elcSilent_1767_114
#print axioms elcSilent_1767_228
#print axioms elcSilent_1767_456
#print axioms elcSilent_1767_912
#print axioms elcSilent_1785_7
#print axioms elcSilent_1785_14
#print axioms elcSilent_1785_28
#print axioms elcSilent_1785_56
#print axioms elcSilent_1785_112
#print axioms elcSilent_1785_224
#print axioms elcSilent_1785_448
#print axioms elcSilent_1785_896
#print axioms elcSilent_1827_29
#print axioms elcSilent_1827_58
#print axioms elcSilent_1827_116
#print axioms elcSilent_1827_232
#print axioms elcSilent_1827_464
#print axioms elcSilent_1827_928
#print axioms elcSilent_1829_59
#print axioms elcSilent_1829_118
#print axioms elcSilent_1829_236
#print axioms elcSilent_1829_472
#print axioms elcSilent_1829_944
#print axioms elcSilent_1891_61
#print axioms elcSilent_1891_122
#print axioms elcSilent_1891_244
#print axioms elcSilent_1891_488
#print axioms elcSilent_1891_976
#print axioms elcSilent_1905_15
#print axioms elcSilent_1905_30
#print axioms elcSilent_1905_60
#print axioms elcSilent_1905_120
#print axioms elcSilent_1905_240
#print axioms elcSilent_1905_480
#print axioms elcSilent_1905_960
#print axioms elcSilent_1953_31
#print axioms elcSilent_1953_62
#print axioms elcSilent_1953_63
#print axioms elcSilent_1953_124
#print axioms elcSilent_1953_126
#print axioms elcSilent_1953_248
#print axioms elcSilent_1953_252
#print axioms elcSilent_1953_496
#print axioms elcSilent_1953_504
#print axioms elcSilent_1953_992
#print axioms elcSilent_1953_1008
#print axioms elcExitSilentTable_length
#print axioms elcSilentEmpty_of_mem
#print axioms elcOffPinCaps_of_mem
#print axioms elcClass1Empty_of_mem
#print axioms elcDatum_of_mem
#print axioms elcNewPair_303_5
#print axioms elcDeepClear_303_5
#print axioms elcClass2Cap_303_5
#print axioms elcClass1Absorption_303_5
#print axioms elcNewPair_909_15
#print axioms elcDeepClear_909_15
#print axioms elcClass2Cap_909_15
#print axioms elcClass1Absorption_909_15
#print axioms elcNewPair_921_7
#print axioms elcDeepClear_921_7
#print axioms elcClass2Cap_921_7
#print axioms elcClass1Absorption_921_7
#print axioms elcNewPair_931_9
#print axioms elcDeepClear_931_9
#print axioms elcClass2Cap_931_9
#print axioms elcClass1Absorption_931_9
#print axioms elcNewPair_937_17
#print axioms elcDeepClear_937_17
#print axioms elcClass2Cap_937_17
#print axioms elcClass1Absorption_937_17
#print axioms elcNewPair_979_19
#print axioms elcDeepClear_979_19
#print axioms elcClass2Cap_979_19
#print axioms elcClass1Absorption_979_19
#print axioms elcNewPair_987_5
#print axioms elcDeepClear_987_5
#print axioms elcClass2Cap_987_5
#print axioms elcClass1Absorption_987_5
#print axioms elcNewPair_1053_17
#print axioms elcDeepClear_1053_17
#print axioms elcClass2Cap_1053_17
#print axioms elcClass1Absorption_1053_17
#print axioms elcNewPair_1059_31
#print axioms elcDeepClear_1059_31
#print axioms elcClass2Cap_1059_31
#print axioms elcClass1Absorption_1059_31
#print axioms elcNewPair_1065_17
#print axioms elcDeepClear_1065_17
#print axioms elcClass2Cap_1065_17
#print axioms elcClass1Absorption_1065_17
#print axioms elcLongCycleTable_length
#print axioms elcLongCycleModuli_length
#print axioms elcOffPin_at_silent
#print axioms elcOffPin_of_uncoveredResidual
#print axioms elcCore_of_uncoveredResidual_and_voiding
#print axioms elcKeystoneCore_of_uncoveredResidual
#print axioms elcOffPin_of_regime
#print axioms exitLightCycleCertificatesStatus_nonempty

end

end Erdos260
