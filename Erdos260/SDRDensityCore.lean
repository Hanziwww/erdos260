import Erdos260.DensePackLandsShiftCore
import Erdos260.TowerSDRCore
import Erdos260.AppendixK2_FineWilf
import Erdos260.FixedDensity

/-!
# SDR Density Core — the per-start semiperiodic density behind the shared coarea SDR

This module (NEW; it edits no existing file) owns the single deep **density** fact behind the shared
coarea SDR that serves DensePack / Tower / Run:

> *Each class-2/3 high-excess start's descent window carries `≥ ⌊ρ_D·L⌋` of its OWN support hits.*

Concretely this is the inequality `⌊ρ_D L⌋ ≤ |supportWindow(k + r)|` feeding
`densePackEndpointDensity` (`DensePackLandsShiftCore.lean`) **and** the per-block floor
`ρ_D·L ≤ #(idxOwned k)` feeding `Class2IndexSDR.hidx_floor` (`TowerSDRCore.lean`).

## The mechanism (no large run ⟹ semiperiodic ⟹ density `≥ ρ_D`)

A class-2/3 start has **no large run** (`runClsOfShell ≠ 1`); its descent window is therefore
*semiperiodic* with a bounded primitive period.  Read on the binary digit word `d`, the window
`[m, m + len)` is `PeriodicOn d m len p` for some primitive period `p` (this is exactly the
Fine–Wilf common-period output, `AppendixK2_FineWilf.lean`).  The manuscript §24 fixed-period
density (`FixedDensity.lean`, Lemma 24.2) then forces the **period density** `wt(period)/p ≥ ρ_D`,
and a window of `O(L)` positions packs `≥ ρ_D·L` hits.

## What is fully proved here (axiom-clean: no `sorry`/`axiom`/`admit`/`native_decide`)

The genuine analytic atom — the periodic counting + density transfer — is proved unconditionally:

* `windowWeight`, `blockSum` — the hit weight of a window `[start, start + len)` and of the `t`-th
  period block.
* `periodicWindow_count_lower` — **the counting heart**: for a *windowed* `PeriodicOn d start len p`
  (the genuine semiperiodicity, NOT a global period), the hit weight dominates the complete-period
  count: `⌊len/p⌋ · wt(period) ≤ windowWeight d start len`.
* `windowWeight_ge_rhoD_mul_L` — **the real density bound** `ρ_D·L ≤ windowWeight d m len`, from the
  period-density floor `ρ_D·p ≤ wt(period)` and the window-length calibration `L + p ≤ len + 1`.
* `densePackMinHits_le_supportWindow_card` / `densePackEndpointDensity_of_semiperiodicDensity` —
  **the DensePack reduction**: the per-start semiperiodic-window data (containment + periodicity +
  period density + length) yields `densePackEndpointDensity ctx` *exactly*.
* `Class2IndexSDR.ofSemiperiodicDensity` — **the Tower/Run SDR feed**: the same per-start density is
  the `hidx_floor` of `Class2IndexSDR` (built through `Class2IndexSDR.ofIntervals`, with the
  orthogonal landing/disjointness selection taken as inputs).
* `windowWeight_density_floor_of_orbit` / `windowWeight_density_floor_of_primitive` /
  `windowWeight_ge_of_shortSemiperiodic` — **the §24 / Fine–Wilf grounding**: the period-density
  floor `ρ_D·p ≤ wt(period)` is the genuine fixed-period density (Lemma 24.2,
  `fixedDensity_exact_completion_lower`), and the `ShortSemiperiodic` Fine–Wilf output plugs straight
  into the count.

## The honest residual that genuinely remains

`densePackEndpointDensity_of_semiperiodicDensity` (and the SDR builder) reduce the density to the
**existence**, for each class-2/3 start `k`, of a semiperiodic descent window with:

* **periodicity** `PeriodicOn ctx.shell.d (k + r) len (p k)` — the no-large-run ⟹ semiperiodic
  recurrence (manuscript Appendix K.2 / §I.4, via the dirty-crossing classification);
* **period density** `ρ_D·(p k) ≤ wt` — the §24 fixed-period density (proved here from primitivity +
  rational completion);
* **window calibration** `L + p k ≤ len + 1` — the bounded primitive period sits inside the `O(L)`
  window;
* **shell containment** `X < k + r` and `(k + r) + spread ≤ 2X` — the descent endpoint window lies
  inside the dyadic shell `(X, 2X]`.

The density *mechanism* is discharged unconditionally; the surviving residual is purely the
**existence of the semiperiodic structure** (no-large-run ⟹ bounded primitive period), the genuine
manuscript K.2/I.4 content.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

namespace Erdos260

noncomputable section

/-! ## 1.  The hit weight of a window and of a period block

`windowWeight d start len` is the number of hits (`d · = 1`) of the binary word in positions
`[start, start + len)`; `blockSum d start p t` is the hit weight of the `t`-th length-`p` block. -/

/-- The hit weight of the window `[start, start + len)` (number of `d · = 1` positions). -/
def windowWeight (d : ℕ → ℕ) (start len : ℕ) : ℕ :=
  ∑ i ∈ Finset.range len, d (start + i)

/-- The hit weight of the `t`-th length-`p` block, `[start + t·p, start + t·p + p)`. -/
def blockSum (d : ℕ → ℕ) (start p t : ℕ) : ℕ :=
  ∑ j ∈ Finset.range p, d (start + (t * p + j))

/-- The window weight is monotone in the window length (extra terms are nonnegative). -/
theorem windowWeight_mono (d : ℕ → ℕ) (start : ℕ) {a b : ℕ} (hab : a ≤ b) :
    windowWeight d start a ≤ windowWeight d start b := by
  unfold windowWeight
  apply Finset.sum_le_sum_of_subset
  intro x hx
  rw [Finset.mem_range] at hx ⊢
  omega

/-- For a binary word the window weight is exactly the cardinality of the hit set
`{ i < len : d (start + i) = 1 }`. -/
theorem windowWeight_eq_filter_card {d : ℕ → ℕ} (hd : BinaryDigits d) (start len : ℕ) :
    windowWeight d start len
      = ((Finset.range len).filter (fun i => d (start + i) = 1)).card := by
  rw [Finset.card_filter]
  unfold windowWeight
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rcases hd (start + i) with h | h <;> simp [h]

/-- The zeroth block is the first period window. -/
theorem blockSum_zero (d : ℕ → ℕ) (start p : ℕ) :
    blockSum d start p 0 = windowWeight d start p := by
  unfold blockSum windowWeight
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Nat.zero_mul, Nat.zero_add]

/-- **Single block shift (windowed).**  If the word is `PeriodicOn d start len p` and the block
`t + 1` is followed by enough room (`(t + 2)·p ≤ len`), then block `t + 1` has the same hit weight
as block `t`: the windowed recurrence shifts the whole block down by one period. -/
theorem blockSum_succ_eq {d : ℕ → ℕ} {start len p : ℕ}
    (h : PeriodicOn d start len p) {t : ℕ} (ht : (t + 2) * p ≤ len) :
    blockSum d start p (t + 1) = blockSum d start p t := by
  unfold blockSum
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [Finset.mem_range] at hj
  have hexp : (t + 2) * p = t * p + 2 * p := by ring
  have hlt : (t * p + j) + p < len := by omega
  have key := h.2 (t * p + j) hlt
  have hidx : start + ((t + 1) * p + j) = start + (t * p + j) + p := by ring
  rw [hidx]
  exact key

/-- **Telescoped block equality (windowed).**  Every block `t` whose right end fits in the window
(`(t + 1)·p ≤ len`) has the same hit weight as the zeroth block. -/
theorem blockSum_eq_first {d : ℕ → ℕ} {start len p : ℕ}
    (h : PeriodicOn d start len p) :
    ∀ t : ℕ, (t + 1) * p ≤ len → blockSum d start p t = blockSum d start p 0 := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    have ht2 : (t + 2) * p ≤ len := by
      rw [show (t + 2) * p = (t + 1 + 1) * p from by ring]; exact ht
    have hstep : blockSum d start p (t + 1) = blockSum d start p t :=
      blockSum_succ_eq h ht2
    have ht1 : (t + 1) * p ≤ len :=
      le_trans (Nat.mul_le_mul (by omega) (le_refl p)) ht2
    rw [hstep]
    exact ih ht1

/-- **The window splits into period blocks.**  The window of `m` full periods is the sum of the
first `m` block weights. -/
theorem windowWeight_eq_sum_blockSum (d : ℕ → ℕ) (start p : ℕ) :
    ∀ m : ℕ, windowWeight d start (m * p)
      = ∑ t ∈ Finset.range m, blockSum d start p t := by
  intro m
  induction m with
  | zero => simp [windowWeight]
  | succ m ih =>
    have hL : windowWeight d start ((m + 1) * p)
        = windowWeight d start (m * p) + blockSum d start p m := by
      unfold windowWeight
      rw [show (m + 1) * p = m * p + p from by ring, Finset.sum_range_add]
      rfl
    rw [hL, ih, Finset.sum_range_succ]

/-! ## 2.  The counting heart — windowed periodicity packs `⌊len/p⌋` full periods

`periodicWindow_count_lower` is the genuine analytic atom: a *windowed* `PeriodicOn` window of `len`
positions contains at least `⌊len/p⌋` complete period blocks, hence at least `⌊len/p⌋ · wt(period)`
hits.  No global period is assumed — only the recurrence within the window (the Fine–Wilf output). -/

/-- **Periodic-window count lower bound.**  For `PeriodicOn d start len p`, the hit weight of the
window dominates the complete-period count `⌊len/p⌋ · wt(period)`. -/
theorem periodicWindow_count_lower {d : ℕ → ℕ} {start len p : ℕ}
    (h : PeriodicOn d start len p) :
    (len / p) * windowWeight d start p ≤ windowWeight d start len := by
  have hmp_le : (len / p) * p ≤ len := Nat.div_mul_le_self len p
  have hpart := windowWeight_eq_sum_blockSum d start p (len / p)
  have hblocks : ∀ t ∈ Finset.range (len / p),
      blockSum d start p t = blockSum d start p 0 := by
    intro t ht
    rw [Finset.mem_range] at ht
    have hle : (t + 1) * p ≤ len :=
      le_trans (Nat.mul_le_mul (by omega) (le_refl p)) hmp_le
    exact blockSum_eq_first h t hle
  have hsum : ∑ t ∈ Finset.range (len / p), blockSum d start p t
      = (len / p) * blockSum d start p 0 := by
    rw [Finset.sum_congr rfl hblocks, Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hkey : windowWeight d start ((len / p) * p) = (len / p) * windowWeight d start p := by
    rw [hpart, hsum, blockSum_zero]
  calc (len / p) * windowWeight d start p
      = windowWeight d start ((len / p) * p) := hkey.symm
    _ ≤ windowWeight d start len := windowWeight_mono d start hmp_le

/-! ## 3.  The real density bound `ρ_D · L ≤ count`

From the counting heart plus the period-density floor `ρ_D·p ≤ wt(period)` and the window-length
calibration `L + p ≤ len + 1`, the window packs `≥ ρ_D·L` hits.  This single real inequality is the
shared SDR atom: floored it is the DensePack `⌊ρ_D L⌋ ≤ |supportWindow|`, verbatim it is the SDR
`ρ_D·L ≤ #(idxOwned k)`. -/

/-- **The shared semiperiodic-density atom (real form).**  For a windowed `PeriodicOn d m len p`
whose period block has density `≥ ρ_D` (`ρ_D·p ≤ windowWeight d m p`) and whose length comfortably
covers the period (`L + p ≤ len + 1`), the window packs at least `ρ_D·L` hits. -/
theorem windowWeight_ge_rhoD_mul_L {d : ℕ → ℕ} {m p len L : ℕ}
    (hp : 0 < p)
    (hper : PeriodicOn d m len p)
    (hdens : manuscriptRhoD * (p : ℝ) ≤ (windowWeight d m p : ℝ))
    (hlen : L + p ≤ len + 1) :
    manuscriptRhoD * (L : ℝ) ≤ (windowWeight d m len : ℝ) := by
  have hcount : (len / p) * windowWeight d m p ≤ windowWeight d m len :=
    periodicWindow_count_lower hper
  have hmpL : L ≤ (len / p) * p := by
    have hdm : p * (len / p) + len % p = len := Nat.div_add_mod len p
    have hmod : len % p < p := Nat.mod_lt len hp
    have hcomm : (len / p) * p = p * (len / p) := Nat.mul_comm _ _
    omega
  have hρ : (0 : ℝ) ≤ manuscriptRhoD := le_of_lt manuscriptRhoD_pos
  have hmbR : (0 : ℝ) ≤ ((len / p : ℕ) : ℝ) := by positivity
  have step1 :
      ((len / p : ℕ) : ℝ) * (manuscriptRhoD * (p : ℝ))
        ≤ ((len / p : ℕ) : ℝ) * (windowWeight d m p : ℝ) :=
    mul_le_mul_of_nonneg_left hdens hmbR
  have hmpLR : (L : ℝ) ≤ (((len / p) * p : ℕ) : ℝ) := by exact_mod_cast hmpL
  have step2 :
      manuscriptRhoD * (L : ℝ) ≤ manuscriptRhoD * (((len / p) * p : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left hmpLR hρ
  have hcountR :
      (((len / p) * windowWeight d m p : ℕ) : ℝ) ≤ (windowWeight d m len : ℝ) := by
    exact_mod_cast hcount
  calc manuscriptRhoD * (L : ℝ)
      ≤ manuscriptRhoD * (((len / p) * p : ℕ) : ℝ) := step2
    _ = ((len / p : ℕ) : ℝ) * (manuscriptRhoD * (p : ℝ)) := by push_cast; ring
    _ ≤ ((len / p : ℕ) : ℝ) * (windowWeight d m p : ℝ) := step1
    _ = (((len / p) * windowWeight d m p : ℕ) : ℝ) := by push_cast; ring
    _ ≤ (windowWeight d m len : ℝ) := hcountR

/-! ## 4.  The DensePack reduction — `densePackEndpointDensity` from per-start windows

A shell-contained window of hits injects into the DensePack support packet, so the bare hit count
lower-bounds `|supportWindow|`; flooring the real density atom delivers `⌊ρ_D L⌋ ≤ |supportWindow|`,
i.e. exactly `densePackEndpointDensity`. -/

/-- A shell-contained window of hits injects into the DensePack support packet:
`#{ i ≤ spread : d (m + i) = 1 } ≤ |supportWindow(m)|`, when `[m, m + spread] ⊆ (X, 2X]`. -/
theorem windowFilter_card_le_supportWindow
    (shell : FailingDyadicShell) {m : ℕ}
    (hlo : shell.X < m)
    (hhi : m + proofV4DensePackSpread shell ≤ 2 * shell.X) :
    ((Finset.range (proofV4DensePackSpread shell + 1)).filter
        (fun i => shell.d (m + i) = 1)).card
      ≤ (proofV4DensePackSupportWindow shell m).card := by
  refine Finset.card_le_card_of_injOn (fun i => m + i) ?_ ?_
  · intro i hi
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨hi_lt, hi_hit⟩ := hi
    rw [Finset.mem_coe]
    show m + i ∈ proofV4DensePackSupportWindow shell m
    unfold proofV4DensePackSupportWindow
    rw [Finset.mem_filter, mem_supportShell]
    exact ⟨⟨by omega, by omega, hi_hit⟩, by omega, by omega⟩
  · intro i _ j _ hij
    have hij' : m + i = m + j := hij
    omega

/-- **DensePack hit-density from a per-start semiperiodic window.**  The semiperiodic descent window
(containment + windowed periodicity + period density `≥ ρ_D` + length calibration) carries
`⌊ρ_D L⌋ ≤ |supportWindow(m)|` — the bare K.1 coarea hit-density at the descent endpoint `m`. -/
theorem densePackMinHits_le_supportWindow_card
    (shell : FailingDyadicShell) {m p : ℕ}
    (hlo : shell.X < m)
    (hhi : m + proofV4DensePackSpread shell ≤ 2 * shell.X)
    (hp : 0 < p)
    (hper : PeriodicOn shell.d m (proofV4DensePackSpread shell + 1) p)
    (hdens : manuscriptRhoD * (p : ℝ) ≤ (windowWeight shell.d m p : ℝ))
    (hlen : Classical.choose shell.hXdyadic + p ≤ proofV4DensePackSpread shell + 2) :
    proofV4DensePackMinHits shell ≤ (proofV4DensePackSupportWindow shell m).card := by
  have hρ : (0 : ℝ) ≤ manuscriptRhoD := le_of_lt manuscriptRhoD_pos
  have hreal := windowWeight_ge_rhoD_mul_L (d := shell.d) (m := m) (p := p)
      (len := proofV4DensePackSpread shell + 1) (L := Classical.choose shell.hXdyadic)
      hp hper hdens (by omega)
  have hfloor : proofV4DensePackMinHits shell
      ≤ windowWeight shell.d m (proofV4DensePackSpread shell + 1) := by
    have hcast : (proofV4DensePackMinHits shell : ℝ)
        ≤ (windowWeight shell.d m (proofV4DensePackSpread shell + 1) : ℝ) := by
      unfold proofV4DensePackMinHits
      exact le_trans (Nat.floor_le (mul_nonneg hρ (by positivity))) hreal
    exact_mod_cast hcast
  rw [windowWeight_eq_filter_card shell.hd] at hfloor
  exact le_trans hfloor (windowFilter_card_le_supportWindow shell hlo hhi)

/-- **`densePackEndpointDensity` from the per-start semiperiodic density family.**  If every genuine
densePack tower-exit start `k` has a semiperiodic descent window at `k + r` (shell-contained,
windowed-periodic with period `p k`, period density `≥ ρ_D`, length-calibrated), then
`densePackEndpointDensity ctx` holds.  This is the exact reduction of the DensePack coarea
hit-density residual to the per-start no-large-run semiperiodic structure. -/
theorem densePackEndpointDensity_of_semiperiodicDensity
    (ctx : ActualFailureContext) (p : ℕ → ℕ)
    (hlo : ∀ k ∈ genuineDensePackStarts ctx, ctx.shell.X < k + ctx.n24CarryData.r)
    (hhi : ∀ k ∈ genuineDensePackStarts ctx,
        (k + ctx.n24CarryData.r) + proofV4DensePackSpread ctx.shell ≤ 2 * ctx.shell.X)
    (hp : ∀ k ∈ genuineDensePackStarts ctx, 0 < p k)
    (hper : ∀ k ∈ genuineDensePackStarts ctx,
        PeriodicOn ctx.shell.d (k + ctx.n24CarryData.r)
          (proofV4DensePackSpread ctx.shell + 1) (p k))
    (hdens : ∀ k ∈ genuineDensePackStarts ctx,
        manuscriptRhoD * (p k : ℝ)
          ≤ (windowWeight ctx.shell.d (k + ctx.n24CarryData.r) (p k) : ℝ))
    (hlen : ∀ k ∈ genuineDensePackStarts ctx,
        Classical.choose ctx.shell.hXdyadic + p k ≤ proofV4DensePackSpread ctx.shell + 2) :
    densePackEndpointDensity ctx := by
  intro k hk
  exact densePackMinHits_le_supportWindow_card ctx.shell (hlo k hk) (hhi k hk)
    (hp k hk) (hper k hk) (hdens k hk) (hlen k hk)

/-! ## 5.  §24 / Fine–Wilf grounding of the period-density floor

The period-density floor `ρ_D·p ≤ wt(period)` is the genuine manuscript fixed-period density
(Lemma 24.2): a primitive period whose periodic completion is the rational `P/Q` has density
`≥ 1/(3Q)`.  We re-export it on the shifted window word, and at `Q = 1` it dominates `ρ_D = 1/4`. -/

/-- **Period-density floor from the orbit hypothesis.**  If the period block satisfies the
exact-completion orbit condition `p + 1 ≤ 2·Q·wt`, then its density is `≥ 1/(3Q)`
(`FixedDensity.exactPeriodicCompletion_periodWeight_density_lower_from_orbit`). -/
theorem windowWeight_density_floor_of_orbit (d : ℕ → ℕ) (m : ℕ) {p Q : ℕ}
    (hQ : 0 < Q) (hp : 0 < p)
    (horbit : p + 1 ≤ 2 * Q * windowWeight d m p) :
    (1 : ℝ) / ((3 * Q : ℕ) : ℝ) * (p : ℝ) ≤ (windowWeight d m p : ℝ) := by
  have hpw : periodWeight (fun i => d (m + i)) p = windowWeight d m p := rfl
  have h := exactPeriodicCompletion_periodWeight_density_lower_from_orbit
      (Q := Q) (p := p) (d := fun i => d (m + i)) hQ hp (by rw [hpw]; exact horbit)
  unfold periodDensity at h
  rw [hpw] at h
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  rwa [le_div_iff₀ hpR] at h

/-- **`ρ_D` period-density floor at `Q = 1`.**  At the relevant rational denominator the orbit
density `1/3` dominates `ρ_D = 1/4`, so the period block packs `≥ ρ_D·p` hits. -/
theorem windowWeight_density_floor_rhoD_of_orbit (d : ℕ → ℕ) (m : ℕ) {p : ℕ}
    (hp : 0 < p) (horbit : p + 1 ≤ 2 * windowWeight d m p) :
    manuscriptRhoD * (p : ℝ) ≤ (windowWeight d m p : ℝ) := by
  have h := windowWeight_density_floor_of_orbit d m (Q := 1) (by norm_num) hp (by simpa using horbit)
  have hpR : (0 : ℝ) ≤ (p : ℝ) := by positivity
  have hle : manuscriptRhoD ≤ (1 : ℝ) / ((3 * 1 : ℕ) : ℝ) := by
    unfold manuscriptRhoD; norm_num
  exact le_trans (mul_le_mul_of_nonneg_right hle hpR) h

/-- **Period-density floor from primitivity (manuscript Lemma 24.2).**  A primitive period of the
window word whose periodic completion is the rational `P/Q` (the denominator-drop divisibility
`hdiv`) has density `≥ 1/(3Q)` — the genuine §24 fixed-period density
(`FixedDensity.fixedDensity_exact_completion_lower`). -/
theorem windowWeight_density_floor_of_primitive (d : ℕ → ℕ) (m : ℕ) {p Q : ℕ}
    (hp : 2 ≤ p) (hQ : 0 < Q) (hd : BinaryDigits d)
    (hper : ∀ j, d (m + j + p) = d (m + j))
    (hprim : ∀ s, 0 < s → s < p → ∃ k, d (m + k + s) ≠ d (m + k))
    (hdiv : periodDen p ∣ (Q * p) * periodMask (fun i => d (m + i)) p) :
    (1 : ℝ) / ((3 * Q : ℕ) : ℝ) * (p : ℝ) ≤ (windowWeight d m p : ℝ) := by
  have hg : BinaryDigits (fun i => d (m + i)) := fun i => hd (m + i)
  have hgper : ∀ j, (fun i => d (m + i)) (j + p) = (fun i => d (m + i)) j := by
    intro j
    show d (m + (j + p)) = d (m + j)
    rw [show m + (j + p) = m + j + p from by ring]; exact hper j
  have hgprim : ∀ s, 0 < s → s < p →
      ∃ k, (fun i => d (m + i)) (k + s) ≠ (fun i => d (m + i)) k := by
    intro s hs hsp
    obtain ⟨k, hk⟩ := hprim s hs hsp
    refine ⟨k, ?_⟩
    show d (m + (k + s)) ≠ d (m + k)
    rw [show m + (k + s) = m + k + s from by ring]; exact hk
  have hdens := fixedDensity_exact_completion_lower (d := fun i => d (m + i))
      (p := p) (Q := Q) hp hQ hg hgper hgprim hdiv
  have hpw : periodWeight (fun i => d (m + i)) p = windowWeight d m p := rfl
  unfold periodDensity at hdens
  rw [hpw] at hdens
  have hppos : 0 < p := by omega
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hppos
  rwa [le_div_iff₀ hpR] at hdens

/-- **Fine–Wilf semiperiodicity feeds the count directly.**  A `ShortSemiperiodic` window (the
Fine–Wilf common-period output, `AppendixK2_FineWilf.ShortSemiperiodic.commonPeriod`) whose primitive
period has density `≥ ρ_D` and fits the length calibration packs `≥ ρ_D·L` hits. -/
theorem windowWeight_ge_of_shortSemiperiodic {d : ℕ → ℕ} {m len bound L : ℕ}
    (hsemi : ShortSemiperiodic d m len bound)
    (hdens : ∀ p, PeriodicOn d m len p → p < bound →
        manuscriptRhoD * (p : ℝ) ≤ (windowWeight d m p : ℝ))
    (hlen : ∀ p, p < bound → L + p ≤ len + 1) :
    manuscriptRhoD * (L : ℝ) ≤ (windowWeight d m len : ℝ) := by
  obtain ⟨p, hper, hpb⟩ := hsemi
  exact windowWeight_ge_rhoD_mul_L hper.period_pos hper (hdens p hper hpb) (hlen p hpb)

/-! ## 6.  The Tower/Run SDR feed — the same density IS `Class2IndexSDR.hidx_floor`

The real density atom `ρ_D·L ≤ windowWeight` is exactly the per-block floor of `Class2IndexSDR`.
The builder threads it through `Class2IndexSDR.ofIntervals` (the orthogonal maximal-disjoint
selection — landing and disjointness — is taken as input, being the *other* K.1.3 residual). -/

/-- **`Class2IndexSDR` from the per-start semiperiodic density.**  The descent-window density supplies
the `hidx_floor` (`ρ_D·L ≤ #(idxOwned k)`) for every class-2 start; the maximal-disjoint selection
(`hlands`, `hdisj`) and the `L`-free scalar data are taken as inputs.  This exhibits the per-start
semiperiodic density as the exact density half of the shared SDR. -/
def Class2IndexSDR.ofSemiperiodicDensity
    (ctx : ActualFailureContext)
    (a : ℕ → ℕ) (hainj : Function.Injective a)
    (eps : ℝ) (Lnat : ℕ) (hLpos : 0 < Lnat)
    (hYnn : 0 ≤ ctx.n24CarryData.Y)
    (hcalibE : 2 * ctx.n24CarryData.Y ≤ 2 * eps * (Lnat : ℝ))
    (huniform : 2 * (erdos260Constants.c0 * eps) ≤ erdos260Constants.ξ / 6 * manuscriptRhoD)
    (hbdry : 0 ∉ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2)
    (lo m len p : ℕ → ℕ)
    (hp : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2, 0 < p k)
    (hper : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
        PeriodicOn ctx.shell.d (m k) (len k) (p k))
    (hdens : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
        manuscriptRhoD * (p k : ℝ) ≤ (windowWeight ctx.shell.d (m k) (p k) : ℝ))
    (hlenL : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
        Lnat + p k ≤ len k + 1)
    (hlands : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
        ∀ j ∈ Finset.Ico (lo k) (lo k + windowWeight ctx.shell.d (m k) (len k)),
          a j ∈ supportShell ctx.d ctx.X)
    (hdisj : ∀ j ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2,
        ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 2, j ≠ k →
        Disjoint (Finset.Ico (lo j) (lo j + windowWeight ctx.shell.d (m j) (len j)))
          (Finset.Ico (lo k) (lo k + windowWeight ctx.shell.d (m k) (len k)))) :
    Class2IndexSDR ctx :=
  Class2IndexSDR.ofIntervals ctx a hainj manuscriptRhoD eps (Lnat : ℝ)
    manuscriptRhoD_pos (by exact_mod_cast hLpos) hYnn hcalibE huniform hbdry
    lo (fun k => windowWeight ctx.shell.d (m k) (len k))
    hlands hdisj
    (fun k hk => windowWeight_ge_rhoD_mul_L (hp k hk) (hper k hk) (hdens k hk) (hlenL k hk))

/-! ## 7.  Honest residual inventory -/

/-- The precise status of the per-start semiperiodic density after this module. -/
def sdrDensityCoreResiduals : List String :=
  [ "PROVEN (counting heart) — periodicWindow_count_lower: for a WINDOWED PeriodicOn d start len p " ++
      "(the genuine semiperiodicity, the Fine-Wilf common-period output — NOT a global period), the " ++
      "hit weight windowWeight d start len dominates the complete-period count ⌊len/p⌋·wt(period). " ++
      "Proved by telescoping the per-block weight (blockSum_succ_eq shifts each block down one period " ++
      "within the window; blockSum_eq_first telescopes) and splitting the window into ⌊len/p⌋ blocks " ++
      "(windowWeight_eq_sum_blockSum).",
    "PROVEN (density atom, real) — windowWeight_ge_rhoD_mul_L: from the period-density floor ρ_D·p ≤ " ++
      "wt(period) and the window-length calibration L + p ≤ len + 1, the window packs ρ_D·L ≤ " ++
      "windowWeight d m len. This SINGLE real inequality is the shared SDR atom: floored it is the " ++
      "DensePack ⌊ρ_D L⌋ ≤ |supportWindow|, verbatim it is the SDR ρ_D·L ≤ #(idxOwned k).",
    "PROVEN (DensePack reduction) — densePackEndpointDensity_of_semiperiodicDensity: a per-start " ++
      "semiperiodic descent window (shell containment X < k+r and (k+r)+spread ≤ 2X; windowed " ++
      "PeriodicOn at k+r; period density ≥ ρ_D; length L + p ≤ spread + 2) yields " ++
      "densePackEndpointDensity ctx EXACTLY, via densePackMinHits_le_supportWindow_card " ++
      "(windowFilter_card_le_supportWindow injects the shell-contained window hits into the K.1 " ++
      "support packet; Nat.floor_le floors the real density).",
    "PROVEN (Tower/Run SDR feed) — Class2IndexSDR.ofSemiperiodicDensity: the same density atom IS the " ++
      "hidx_floor (ρ_D·L ≤ #(idxOwned k)) of Class2IndexSDR, built through Class2IndexSDR.ofIntervals. " ++
      "The orthogonal maximal-disjoint selection (hlands landing + hdisj disjointness, the OTHER " ++
      "K.1.3 residual) and the L-free scalar data are taken as inputs.",
    "PROVEN (§24 / Fine-Wilf grounding) — the period-density floor ρ_D·p ≤ wt(period) is the genuine " ++
      "manuscript fixed-period density Lemma 24.2: windowWeight_density_floor_of_primitive derives " ++
      "1/(3Q) ≤ density from primitivity + the rational denominator-drop (fixedDensity_exact_" ++
      "completion_lower); windowWeight_density_floor_of_orbit from the orbit condition; " ++
      "windowWeight_density_floor_rhoD_of_orbit shows 1/3 ≥ ρ_D = 1/4 at Q = 1. " ++
      "windowWeight_ge_of_shortSemiperiodic plugs the Fine-Wilf ShortSemiperiodic output straight " ++
      "into the count.",
    "RESIDUAL (the single irreducible fact) — the EXISTENCE, for each class-2/3 start k, of the " ++
      "semiperiodic descent window: no large run (runClsOfShell ≠ 1) ⟹ PeriodicOn ctx.shell.d (k+r) " ++
      "len (p k) with bounded primitive period p k and density ≥ ρ_D. This is the manuscript Appendix " ++
      "K.2 (oriented semiperiodic overlap / dirty-crossing classification) + §I.4 content; the density " ++
      "MECHANISM is discharged here unconditionally, so the residual is purely the semiperiodic " ++
      "STRUCTURE, not the counting. [WAVE-17 UPDATE] SemiperiodicWindowCore.MatchedDescentWindows now " ++
      "DERIVES the periodicity half of this residual via the §25.1 match-transfer " ++
      "(periodicOn_of_match): a pointwise window-match of the globally non-periodic ctx.shell.d to the " ++
      "PROVABLY periodic residual-center orbit word dyadicDigit q₀ a transports PeriodicOn AND the §24 " ++
      "density floor onto the actual word, so the surviving residual is no longer the full semiperiodic " ++
      "STRUCTURE but SPECIFICALLY the §25.1 cylinder MATCH (MatchedDescentWindows ctx), whose " ++
      "equal-cylinder case is already proved in RunCylinderBridge." ++
      "maskWord_eq_dyadicDigit_of_dyadicCylinder; the true remainder is the two geometric §25.1 inputs " ++
      "(ctx.shell.d is the mask word of its mask point, and that point shares the residual center's " ++
      "depth-n dyadic cylinder over the window).",
    "CALIBRATION (honest constraint, exposed not hidden) — the densePack window has len = spread + 1 ≈ " ++
      "L + carryB Q + 2, so the length calibration L + p ≤ len + 1 forces the primitive period p ≤ " ++
      "carryB Q + 2. The slack between the actual period density (1/3 at Q=1) and ρ_D = 1/4 absorbs a " ++
      "larger boundary loss (p ≤ L/4 suffices with the 1/3 density), available by instantiating hdens " ++
      "with the genuine §24 floor instead of the bare ρ_D.",
    "CALIBRATION (ρ_D Q-dependence — flagged for the .tex/source) — manuscriptRhoD = 1/4 is " ++
      "Q-INDEPENDENT, but proof_v4.tex §I.4 line 2965 states the dense-marker density ρ_D 'depends " ++
      "only on Q' (ρ_0(Q) = 1/(4Q), line 962). The §24 fixed-period floor (fixedDensity_exact_" ++
      "completion_lower) gives ≥ 1/(3Q), which dominates the fixed 1/4 only at Q = 1. The density " ++
      "MECHANISM here is parametric in manuscriptRhoD and stays correct under either calibration; only " ++
      "the §24 grounding of hdens is Q-sensitive (windowWeight_density_floor_of_{orbit,primitive} " ++
      "produce the genuine 1/(3Q) floor; only the _rhoD_of_orbit convenience pins Q = 1).",
    "NON-DEGENERATE — ρ_D = 1/4 > 0 (manuscriptRhoD_pos); the window packs a POSITIVE floor; the " ++
      "periodic count is the genuine telescoped block weight, no empty / zero-floor / vacuous shortcut." ]

theorem sdrDensityCoreResiduals_nonempty : sdrDensityCoreResiduals ≠ [] := by
  simp [sdrDensityCoreResiduals]

/-! ## 8.  Axiom-cleanliness audit -/

#print axioms windowWeight_mono
#print axioms windowWeight_eq_filter_card
#print axioms blockSum_succ_eq
#print axioms blockSum_eq_first
#print axioms windowWeight_eq_sum_blockSum
#print axioms periodicWindow_count_lower
#print axioms windowWeight_ge_rhoD_mul_L
#print axioms windowFilter_card_le_supportWindow
#print axioms densePackMinHits_le_supportWindow_card
#print axioms densePackEndpointDensity_of_semiperiodicDensity
#print axioms windowWeight_density_floor_of_orbit
#print axioms windowWeight_density_floor_rhoD_of_orbit
#print axioms windowWeight_density_floor_of_primitive
#print axioms windowWeight_ge_of_shortSemiperiodic
#print axioms Class2IndexSDR.ofSemiperiodicDensity

end

end Erdos260
