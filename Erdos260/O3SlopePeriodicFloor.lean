import Mathlib
import Erdos260.P1HotspotAudit
import Erdos260.P2TrustBoundary
import Erdos260.RhoDQCalibrationCore

/-!
# O3 fixed-pin voiding: the slope-periodic density-floor contradiction CORE

This module (NEW; it edits no existing file) formalizes the **arithmetic core** of the direct
fixed-pin closure of the Erdős-#260 manuscript:

> **App U, Prop `prop:u-fixed-pins-direct`** (line 9430) — *no retained deep fixed-orbit-pin
> branch survives the sparse shell* — via **Lemma `lem:u-periodic-density-floor`** (U.3, line 9409):
> a branch that agrees with a *nonzero binary word of period `p ≤ 3Q`* throughout a dyadic shell
> `[X,2X]` has at least `X/p ≥ X/(3Q)` one-symbols, contradicting the sparse-shell hypothesis
> `A_S(2X)-A_S(X) < c_* X` because `Convention(constants)` chooses `c_* < 1/(6Q)`.

The bounded period `p ≤ 3Q` is the **slope bound** of §24 / App AM / App AR:
* **Lemma 24.1** (`lemma-24.1.-binary-orbit-digit-density`, line 1466): `q` odd, `(a,q)=1`,
  `t = ord_q(2)`, residues `r_j ≡ 2^j a (mod q)` are `t` **distinct positive** integers summing
  to `qk`, so `qk ≥ t(t+1)/2`, i.e. `k ≥ (t+1)/(2C)` when `q ≤ Ct`.
* **Lemma `lem:fixed-slope-exact-completion`** (24.7, line 1603) / **AR.0** (line 12459): the
  slope-fixed gap word `w_g = 10^{g-1}` has one hit per period, density `1/g`, and the exact
  periodic completion forces `1/g ≥ 1/(3Q)`, hence **`g ≤ 3Q`**.
* **Prop `prop:am-o3-discharged`** (App AM, line 11864): every retained deep fixed-pin branch is
  confined to a nonzero periodic window word of period at most `3Q`.

The §24 floor `1/(3Q)` is exactly the `rhoDQ`-calibrated floor (`rhoDQ q = 1/(4q) ≤ 1/(3q)`,
`Prop 24.3` / `prop:tier3-q-calibration`, line 1533).  The numeric "fire-budget" form (`17g ≤ 2^24`,
line 8060; `g = 986891`; `1/3 > 17/2^24`, line 9508; the representative `2^19 < 2^24/17`) is verified
in §6 below.

## HOW THIS PROOF AVOIDS THE FRACTIONAL-TAIL PITFALL  (read this — it once held a real bug)

The historical error (`CarryRecurrence21.carry_fract_doubling`: `(R_{N+1}/Q) ≡ 2(R_N/Q) (mod 1)`)
was to read the digit `d_{n+1}` off the fractional orbit `(R_n/Q) mod 1`.  That orbit *doubles
independently of the emitted digit* — it is provably **digit-blind / gap-blind** — so no digit-level
or density-level fact may be derived from it (manuscript lines 1600, 9361, 11790, 12450 `AR.-1`).

Every density fact in this file is read off the **actual spatial gap word**, never off a fractional
orbit:
* `nonzeroPeriodic_hitCount_ge` (Core A, the U.3 heart) counts ones of the **actual word `d : ℕ → ℕ`**
  via the hypothesis `hblk` that each *spatial* period block `[start+jp, start+(j+1)p)` contains an
  actual hit `d i ≥ 1`.  This is the structure of `w_g = 10^{g-1}` (AM.3 / AR.2), i.e. consecutive
  hits separated by the same actual gap `g` — **not** a quotient `⌊2·{R_n/Q}⌋`.
* The `1/(3Q)` floor itself (`sec24_slope_gap_le_threeQ`, Core B) comes from the **distinct residues**
  `r_j ≡ 2^j a (mod q)` being `t` distinct positive integers (injectivity of the doubling orbit,
  `o3_doubling_orbit_injective`, reused in `doubling_orbit_card`) whose super-linear triangular sum
  `≥ t(t+1)/2` forces `g+1 ≤ 2Q` (`o3_triangular`, `o3_density_floor_arith`).  This is a *counting*
  fact about residues, with **no per-digit extraction** anywhere.

So the chain is `distinct residues ⇒ g ≤ 3Q ⇒ (spatial gap word) density ≥ 1/(3Q) ⇒ sparse-cap
contradiction`, with the digit-blind fractional orbit never entering.

## What is PROVED here (no `sorry`/`axiom`/`admit`/`native_decide`)

* `nonzeroPeriodic_hitCount_ge` — Core A: a nonzero `p`-periodic actual word packs `⌊W/p⌋` ones in
  any window of length `W` (the load-bearing count of Lemma U.3).
* `sec24_slope_gap_le_threeQ` — Core B: the §24 distinct-residue density floor (`o3_triangular` +
  `o3_density_floor_arith`) gives `g+1 ≤ 2Q`, hence the slope bound `g ≤ 3Q` (Lemma 24.7 / AR.0).
* `boundedPeriod_sparse_void`, `boundedPeriod_sparse_void_real` — Core C: a bounded period `p ≤ 3Q`
  on a deep window `W ≥ 6Q` cannot meet the sparse cap (density `< 1/(6Q)`); the genuine void.
* `o3_fixedPin_slope_periodic_void` — the capstone: genuine §24 residue data + bounded-period word +
  deep window + sparse cap ⇒ `False` (Prop U / Cor `cor:am-u-fixed-pin-voiding`).
* `doubling_orbit_card` — the distinct-residue count `t = ord_q(2)` (reuses `o3_doubling_orbit_injective`).
* `fixedPin_slope_gap_unique` — gap uniqueness `(2^g-1)μ=1` ⇒ unique `g` (reuses `e6_slope_gap_unique`).
* `rhoDQ_sparse_calibration`, `sparseCap_below_sec24_floor` — the constant hierarchy
  `c_* < 1/(6Q) < rhoDQ Q = 1/(4Q) ≤ 1/(3Q)` (reuses `rhoDQ`, `rhoDQ_le_third`, `o3_floor_above_cap`).
* `fixedPin_fire_budget_instance`, `twoPow19_lt_fireBudget`, `oneThird_gt_seventeen_fireBudget`,
  `boundedPeriod_within_fireBudget` — the exact numeric fire-budget constants.
-/

namespace Erdos260.O3SlopePeriodicFloor

open Finset

set_option linter.unusedVariables false

/-! ## 0.  The one-count of an actual nonzero periodic word (Core A — the U.3 heart) -/

/-- Number of one-symbols (hits, `d i ≥ 1`) of the actual word `d : ℕ → ℕ` in the spatial window
`[start, start + W)`.  This is the genuine `A_S`-increment of Lemma U.3 read off the **actual** word,
never off the digit-blind fractional orbit `(R_n/Q) mod 1`. -/
def hitCount (d : ℕ → ℕ) (start W : ℕ) : ℕ :=
  ((Finset.Ico start (start + W)).filter (fun i => 1 ≤ d i)).card

/-- **Core A — Lemma U.3 one-count floor.**  If the actual word `d` is *nonzero `p`-periodic* on the
window in the sense that every spatial period block `[start + j·p, start + (j+1)·p)` (for the blocks
that fit, `j < W/p`) carries a hit `d i ≥ 1`, then the window `[start, start+W)` contains at least
`⌊W/p⌋` hits.  This is exactly "a nonzero binary word of period `p` has ≥ one symbol `1` in each
period block, so the shell contains at least `X/p - O(L+p)` ones" (proof of `lem:u-periodic-density-floor`).
The hits are recovered from the **actual spatial gap word** `w_g = 10^{g-1}`, NOT from any fractional
tail. -/
theorem nonzeroPeriodic_hitCount_ge
    (d : ℕ → ℕ) (start p W : ℕ) (hp : 0 < p)
    (hblk : ∀ j, j < W / p → ∃ i, start + j * p ≤ i ∧ i < start + (j + 1) * p ∧ 1 ≤ d i) :
    W / p ≤ hitCount d start W := by
  classical
  have hex : ∀ j : ℕ, ∃ i : ℕ,
      j < W / p → (start + j * p ≤ i ∧ i < start + (j + 1) * p ∧ 1 ≤ d i) := by
    intro j
    by_cases hj : j < W / p
    · obtain ⟨i, hi⟩ := hblk j hj; exact ⟨i, fun _ => hi⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose f hf using hex
  have hmaps : ∀ j ∈ Finset.range (W / p), f j ∈
      (Finset.Ico start (start + W)).filter (fun i => 1 ≤ d i) := by
    intro j hj
    rw [Finset.mem_range] at hj
    obtain ⟨hlo, hhi, hd⟩ := hf j hj
    rw [Finset.mem_filter, Finset.mem_Ico]
    have hjp : (j + 1) * p ≤ W := by
      have h1 : (j + 1) * p ≤ (W / p) * p := Nat.mul_le_mul (by omega) (le_refl p)
      exact le_trans h1 (Nat.div_mul_le_self W p)
    exact ⟨⟨le_trans (Nat.le_add_right start (j * p)) hlo, by omega⟩, hd⟩
  have hinj : Set.InjOn f ↑(Finset.range (W / p)) := by
    intro j hj k hk hjk
    simp only [Finset.mem_coe, Finset.mem_range] at hj hk
    obtain ⟨hlo_j, hhi_j, _⟩ := hf j hj
    obtain ⟨hlo_k, hhi_k, _⟩ := hf k hk
    by_contra hne
    rcases Nat.lt_or_ge j k with hlt | hge
    · have hmul : (j + 1) * p ≤ k * p := Nat.mul_le_mul (by omega) (le_refl p)
      have hck : start + k * p ≤ f j := by rw [hjk]; exact hlo_k
      omega
    · have hmul : (k + 1) * p ≤ j * p := Nat.mul_le_mul (by omega) (le_refl p)
      have hcj : start + j * p ≤ f k := by rw [← hjk]; exact hlo_j
      omega
  have key := Finset.card_le_card_of_injOn f hmaps hinj
  rwa [Finset.card_range] at key

/-! ## 1.  The §24 distinct-residue density floor and the slope bound `g ≤ 3Q` (Core B)

This is the genuine Lemma 24.1 → Lemma 24.7 / AR.0 chain.  The distinctness of the residues
`r_j ≡ 2^j a (mod q)` is the injectivity of the doubling orbit (`o3_doubling_orbit_injective`,
reused in `doubling_orbit_card`); their super-linear sum is `o3_triangular`; the density step is
`o3_density_floor_arith`.  The slope-fixed gap word `w_g = 10^{g-1}` has exactly one hit per period
(`k = wt(w_g) = 1`), giving `g + 1 ≤ 2Q`, hence `g ≤ 3Q`. -/

/-- **The doubling orbit has `t = ord_q(2)` distinct elements** (the distinct-residue count behind
Lemma 24.1).  Reuses `o3_doubling_orbit_injective`.  This is what guarantees the `g` residues `r_j`
are genuinely distinct, so the residue `Finset` fed to Core B has cardinality `t`.  Nothing here
reads a digit off `(R_n/Q) mod 1`. -/
theorem doubling_orbit_card {q : ℕ} [NeZero q] (u a : (ZMod q)ˣ) :
    ((Finset.range (orderOf u)).image (fun j => u ^ j * a)).card = orderOf u := by
  have hinj : Set.InjOn (fun j => u ^ j * a) ↑(Finset.range (orderOf u)) := by
    intro j hj k hk h
    simp only [Finset.coe_range, Set.mem_Iio] at hj hk
    exact Erdos260.P2TrustBoundary.o3_doubling_orbit_injective u a
      (Set.mem_Iio.mpr hj) (Set.mem_Iio.mpr hk) h
  rw [Finset.card_image_of_injOn hinj, Finset.card_range]

/-- **Core B — the §24 slope bound `g ≤ 3Q` (Lemma 24.1 / Lemma 24.7 / AR.0).**  Let `S` be the
`g` distinct positive residues `r_j` of the slope-fixed gap word (`S.card = g`, all `≥ 1`), summing
to `q` (the carry long-division identity `∑ r_j = q·k` with `k = wt(w_g) = 1`), with the §24
denominator bound `q ≤ Q·g` (`q ≤ Qp`).  Then `g + 1 ≤ 2Q`, hence the slope bound `g ≤ 3Q`
(equivalently the density `1/g ≥ 1/(3Q)`).  Built directly from `o3_triangular` (distinct positives
sum to `≥ g(g+1)/2`) and `o3_density_floor_arith`. -/
theorem sec24_slope_gap_le_threeQ
    (Q q g : ℕ) (S : Finset ℕ) (hg : 1 ≤ g) (hcard : S.card = g)
    (hpos : ∀ x ∈ S, 1 ≤ x) (hsum : ∑ x ∈ S, x = q) (hqQg : q ≤ Q * g) :
    g + 1 ≤ 2 * Q ∧ g ≤ 3 * Q := by
  have htri0 := Erdos260.P2TrustBoundary.o3_triangular S.card S rfl hpos
  rw [hcard, hsum] at htri0
  have htri : g * (g + 1) ≤ 2 * (q * 1) := by rw [Nat.mul_one]; exact htri0
  have h := Erdos260.P1HotspotAudit.o3_density_floor_arith q g 1 Q hg htri hqQg
  refine ⟨by omega, by omega⟩

/-! ## 2.  The void: a bounded period cannot meet the sparse cap (Core C) -/

/-- **Core C (integer density form).**  A bounded period `p ≤ 3Q` on a deep window `W ≥ 6Q`, with the
nonzero-periodic supply `hblk`, packs strictly more than the sparse density `1/(6Q)` allows:
the hypothesis `6Q · hitCount < W` (i.e. density `< 1/(6Q)`, the integer form of `A_S(2X)-A_S(X)
< c_* X` with `c_* < 1/(6Q)`) is contradictory.  Combines Core A (`⌊W/p⌋ ≤ hitCount`) with
`p ≤ 3Q`. -/
theorem boundedPeriod_sparse_void
    (d : ℕ → ℕ) (Q start p W : ℕ)
    (hQ : 1 ≤ Q) (hp : 0 < p) (hpb : p ≤ 3 * Q) (hW : 6 * Q ≤ W)
    (hblk : ∀ j, j < W / p → ∃ i, start + j * p ≤ i ∧ i < start + (j + 1) * p ∧ 1 ≤ d i)
    (hcap : 6 * Q * hitCount d start W < W) :
    False := by
  have hA : W / p ≤ hitCount d start W := nonzeroPeriodic_hitCount_ge d start p W hp hblk
  have hdm : p * (W / p) + W % p = W := Nat.div_add_mod W p
  have hmod : W % p < p := Nat.mod_lt W hp
  have hle : p * (W / p) ≤ 3 * Q * hitCount d start W :=
    le_trans (Nat.mul_le_mul (le_refl p) hA) (Nat.mul_le_mul hpb (le_refl _))
  have h4 : 2 * (3 * Q * hitCount d start W) < W := by
    have e : 6 * Q * hitCount d start W = 2 * (3 * Q * hitCount d start W) := by ring
    omega
  omega

/-- **Core C (real / manuscript form).**  Faithful to `lem:u-periodic-density-floor`: the sparse-shell
hypothesis `hitCount < c_* · W` with `c_* < 1/(6Q)` (Convention(constants)) is contradicted by a
bounded period `p ≤ 3Q` on a deep window `W ≥ 6Q`.  Reduces to `boundedPeriod_sparse_void`. -/
theorem boundedPeriod_sparse_void_real
    (d : ℕ → ℕ) (Q start p W : ℕ) (cstar : ℝ)
    (hQ : 1 ≤ Q) (hp : 0 < p) (hpb : p ≤ 3 * Q) (hW : 6 * Q ≤ W)
    (hblk : ∀ j, j < W / p → ∃ i, start + j * p ≤ i ∧ i < start + (j + 1) * p ∧ 1 ≤ d i)
    (hcstar : cstar < 1 / (6 * (Q : ℝ)))
    (hsparse : (hitCount d start W : ℝ) < cstar * (W : ℝ)) :
    False := by
  have hQpos : (0 : ℝ) < 6 * (Q : ℝ) := by positivity
  have hWnn : (0 : ℝ) ≤ (W : ℝ) := by positivity
  have hstep : (hitCount d start W : ℝ) < (1 / (6 * (Q : ℝ))) * (W : ℝ) :=
    lt_of_lt_of_le hsparse (mul_le_mul_of_nonneg_right (le_of_lt hcstar) hWnn)
  have hkey : (6 * (Q : ℝ)) * (hitCount d start W : ℝ) < (W : ℝ) := by
    have h := mul_lt_mul_of_pos_left hstep hQpos
    have e : (6 * (Q : ℝ)) * ((1 / (6 * (Q : ℝ))) * (W : ℝ)) = (W : ℝ) := by
      rw [← mul_assoc, mul_one_div, div_self (ne_of_gt hQpos), one_mul]
    rwa [e] at h
  have hnat : 6 * Q * hitCount d start W < W := by
    have hc : ((6 * Q * hitCount d start W : ℕ) : ℝ) < ((W : ℕ) : ℝ) := by
      have hcast : ((6 * Q * hitCount d start W : ℕ) : ℝ)
          = (6 * (Q : ℝ)) * (hitCount d start W : ℝ) := by push_cast; ring
      rw [hcast]; exact hkey
    exact_mod_cast hc
  exact boundedPeriod_sparse_void d Q start p W hQ hp hpb hW hblk hnat

/-! ## 3.  The capstone: direct fixed-pin voiding (Prop U / Cor AM) -/

/-- **CAPSTONE — direct fixed-pin voiding** (`prop:u-fixed-pins-direct`, line 9430; reproved through
`cor:am-u-fixed-pin-voiding`, line 11882).  Given:

* the **genuine §24 distinct-residue data** (`S` = the `g` distinct positive residues `r_j` of the
  slope-fixed gap word, `S.card = g`, `∑ r_j = q`, with `q ≤ Q·g`) ⇒ the slope bound `g ≤ 3Q`;
* the **bounded-period continuation supply** `hblk` (the retained branch agrees with the nonzero
  period-`g` word `w_g = 10^{g-1}` on every spatial block of the deep window — *kernel-style
  hypothesis*, the "periodic continuation" of `lem:u-fixed-pin-periodic-continuation`);
* a **deep window** `W ≥ 6Q` and the **sparse-shell hypothesis** `hitCount < c_* · W` with
  `c_* < 1/(6Q)`,

there is a contradiction: no retained deep fixed-orbit-pin branch survives the sparse shell.  The
density floor is the genuine §24 period-density `1/g ≥ 1/(3Q)` read off the *actual gap word*; the
digit-blind fractional orbit `(R_n/Q) mod 1` is never used. -/
theorem o3_fixedPin_slope_periodic_void
    (d : ℕ → ℕ) (Q q g start W : ℕ) (cstar : ℝ) (S : Finset ℕ)
    (hQ : 1 ≤ Q) (hg : 1 ≤ g) (hcard : S.card = g)
    (hpos : ∀ x ∈ S, 1 ≤ x) (hsum : ∑ x ∈ S, x = q) (hqQg : q ≤ Q * g)
    (hW : 6 * Q ≤ W)
    (hblk : ∀ j, j < W / g → ∃ i, start + j * g ≤ i ∧ i < start + (j + 1) * g ∧ 1 ≤ d i)
    (hcstar : cstar < 1 / (6 * (Q : ℝ)))
    (hsparse : (hitCount d start W : ℝ) < cstar * (W : ℝ)) :
    False :=
  boundedPeriod_sparse_void_real d Q start g W cstar hQ hg
    (sec24_slope_gap_le_threeQ Q q g S hg hcard hpos hsum hqQg).2 hW hblk hcstar hsparse

/-! ## 4.  Slope-gap uniqueness (E.6 / AR.0) -/

/-- **Slope-gap uniqueness** (`lem:ar-fixed-pin-recognition-table`, line 12459: "`g` is unique because
the intervals `(2^{-g}, 2^{1-g})` are disjoint").  A retained fixed pin has slope `μ = 1/(2^g - 1)`,
i.e. `(2^g - 1)μ = 1`; for `g ≥ 2` this forces `1 < 2^g μ < 2`, so `g` is determined by `μ` via
`e6_slope_gap_unique`. -/
theorem fixedPin_slope_gap_unique (g g' : ℕ) (hg : 2 ≤ g) (hg' : 2 ≤ g')
    (μ : ℝ) (hμ : 0 < μ)
    (heq : ((2 : ℝ) ^ g - 1) * μ = 1) (heq' : ((2 : ℝ) ^ g' - 1) * μ = 1) :
    g = g' := by
  have hpow : ∀ m : ℕ, 2 ≤ m → (4 : ℝ) ≤ 2 ^ m := by
    intro m hm
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := by apply pow_le_pow_right₀ (by norm_num) hm
  have hμlt : μ < 1 := by
    have h4 : (4 : ℝ) ≤ 2 ^ g := hpow g hg
    nlinarith [heq, h4, hμ, mul_nonneg (show (0 : ℝ) ≤ 2 ^ g - 4 by linarith [h4]) (le_of_lt hμ)]
  have e : (2 : ℝ) ^ g * μ = 1 + μ := by linear_combination heq
  have e' : (2 : ℝ) ^ g' * μ = 1 + μ := by linear_combination heq'
  exact Erdos260.P2TrustBoundary.e6_slope_gap_unique μ hμ g g'
    ⟨by rw [e]; linarith, by rw [e]; linarith⟩
    ⟨by rw [e']; linarith, by rw [e']; linarith⟩

/-! ## 5.  The constant hierarchy `c_* < 1/(6Q) < rhoDQ Q = 1/(4Q) ≤ 1/(3Q)` (reuses `rhoDQ`) -/

/-- **The sparse cap lies below the genuine §24 floor** (`o3_floor_above_cap`, Convention(constants)
vs the §24 floor): `c_* < 1/(6Q)` ⇒ `c_* < 1/(3Q)`.  This is the exact margin that makes the void
strict; reused directly from `P1HotspotAudit.o3_floor_above_cap`. -/
theorem sparseCap_below_sec24_floor (Q : ℕ) (hQ : 1 ≤ Q) (cstar : ℚ)
    (hc : cstar < 1 / (6 * Q)) : cstar < 1 / (3 * Q) :=
  Erdos260.P1HotspotAudit.o3_floor_above_cap Q hQ cstar hc

/-- **Full constant calibration** (`prop:tier3-q-calibration`, line 1533): the sparse cap sits
strictly below the DensePack floor `ρ_D(Q) = rhoDQ Q = 1/(4Q)`, which in turn never exceeds the
genuine §24 fixed-period density floor `1/(3Q)`.  Reuses `rhoDQ` and `rhoDQ_le_third`. -/
theorem rhoDQ_sparse_calibration {Q : ℕ} (hQ : 1 ≤ Q) (cstar : ℝ)
    (hc : cstar < 1 / (6 * (Q : ℝ))) :
    cstar < Erdos260.rhoDQ Q ∧ Erdos260.rhoDQ Q ≤ (1 : ℝ) / ((3 * Q : ℕ) : ℝ) := by
  have hQR : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have h6 : (0 : ℝ) < 6 * (Q : ℝ) := by positivity
  have h4 : (0 : ℝ) < 4 * (Q : ℝ) := by positivity
  have h1 : (1 : ℝ) / (6 * (Q : ℝ)) < Erdos260.rhoDQ Q := by
    unfold Erdos260.rhoDQ
    rw [div_lt_div_iff₀ h6 h4]
    nlinarith [hQR]
  exact ⟨lt_trans hc h1, Erdos260.rhoDQ_le_third (by omega)⟩

/-! ## 6.  The exact numeric "fire-budget" constants (`17g ≤ 2^24`; the `2^19 < 2^24/17` style) -/

/-- The manuscript's sharp gap `g = 493443 + 493445 + 3 = 986891` (line 8056). -/
theorem manuscript_fixed_gap_value : (493443 + 493445 + 3 : ℕ) = 986891 := by norm_num

/-- **The exact fire-budget instance** (line 8060): `17·986891 = 16777147 < 16777216 = 2^24`. -/
theorem fixedPin_fire_budget_instance :
    17 * 986891 = 16777147 ∧ 16777147 < (2 : ℕ) ^ 24 := by
  refine ⟨by norm_num, by norm_num⟩

/-- **The representative `2^19 < 2^24/17`** of the task, in cleared-denominator form: `17·2^19 < 2^24`
(`17·524288 = 8912896 < 16777216`).  A period `p ≤ 2^19` lies strictly inside the fire budget. -/
theorem twoPow19_lt_fireBudget : 17 * (2 : ℕ) ^ 19 < (2 : ℕ) ^ 24 := by norm_num

/-- A bounded period `p ≤ 2^19` lies strictly inside the sharp fire budget `17p < 2^24`
(`p < 2^24/17`). -/
theorem boundedPeriod_within_fireBudget {p : ℕ} (hp : p ≤ 2 ^ 19) :
    17 * p < (2 : ℕ) ^ 24 :=
  lt_of_le_of_lt (Nat.mul_le_mul (le_refl 17) hp) twoPow19_lt_fireBudget

/-- **The density comparison `1/3 > 17/2^24`** (line 9508, behind the cycle-persistent-seventh
voiding): `(17 : ℝ)/2^24 < 1/3` (equivalently `51 < 2^24`). -/
theorem oneThird_gt_seventeen_fireBudget : (17 : ℝ) / 2 ^ 24 < 1 / 3 := by norm_num

/-! ## 7.  Honest residual / status inventory -/

/-- The precise status of the O3 slope-periodic density-floor contradiction core. -/
def o3SlopePeriodicFloorResiduals : List String :=
  [ "GOAL — formalize the App-U direct fixed-pin voiding (prop:u-fixed-pins-direct, line 9430) via " ++
      "the periodic density floor (lem:u-periodic-density-floor, U.3, line 9409): a nonzero word of " ++
      "period p ≤ 3Q over a deep dyadic shell packs ≥ X/(3Q) ones, contradicting the sparse cap " ++
      "A_S(2X)-A_S(X) < c_*X with c_* < 1/(6Q).",
    "CLOSED (Core A) — nonzeroPeriodic_hitCount_ge: ⌊W/p⌋ ≤ hitCount d start W for a nonzero " ++
      "p-periodic ACTUAL word (each spatial block carries a hit). The U.3 one-count, read off the " ++
      "actual spatial gap word w_g = 10^{g-1}, NEVER off the fractional orbit (R_n/Q) mod 1.",
    "CLOSED (Core B) — sec24_slope_gap_le_threeQ: the §24 distinct-residue density floor (o3_triangular " ++
      "+ o3_density_floor_arith; distinctness = o3_doubling_orbit_injective via doubling_orbit_card) " ++
      "gives g+1 ≤ 2Q, hence the slope bound g ≤ 3Q (Lemma 24.1 / 24.7 / AR.0). k = wt(w_g) = 1.",
    "CLOSED (Core C) — boundedPeriod_sparse_void(_real): a bounded period p ≤ 3Q on a deep window " ++
      "W ≥ 6Q cannot satisfy the sparse cap (density < 1/(6Q)); the genuine density-floor void.",
    "CLOSED (capstone) — o3_fixedPin_slope_periodic_void: genuine §24 residue data + bounded-period " ++
      "continuation supply + deep window + sparse cap ⇒ False (Prop U / Cor cor:am-u-fixed-pin-voiding).",
    "CLOSED (uniqueness) — fixedPin_slope_gap_unique: (2^g-1)μ=1 with g ≥ 2 determines g (E.6 / AR.0 " ++
      "disjoint slope intervals; reuses e6_slope_gap_unique).",
    "CLOSED (calibration) — rhoDQ_sparse_calibration / sparseCap_below_sec24_floor: " ++
      "c_* < 1/(6Q) < rhoDQ Q = 1/(4Q) ≤ 1/(3Q) (reuses rhoDQ, rhoDQ_le_third, o3_floor_above_cap).",
    "CLOSED (numerics) — fixedPin_fire_budget_instance (17·986891 = 16777147 < 2^24), " ++
      "twoPow19_lt_fireBudget (17·2^19 < 2^24), oneThird_gt_seventeen_fireBudget (17/2^24 < 1/3): " ++
      "the exact fire-budget constants of lines 8060 / 9508 and the task's 2^19 < 2^24/17 style.",
    "TRUST BOUNDARY (kernel-style hypotheses, as permitted) — the periodic-continuation supply (hblk), " ++
      "the carry long-division residue-sum identity ∑ r_j = q (hsum), the denominator bound q ≤ Q·g " ++
      "(hqQg), and the sparse-shell hypothesis (hsparse) are taken as inputs; they are the structural " ++
      "facts of Appendices AR/AM/E and the stopped recurrence, NOT discharged here.",
    "PITFALL-FREE — every density fact is read off the actual word d (Core A) or off distinct residues " ++
      "(Core B); the digit-blind fractional orbit (R_n/Q) mod 1 (CarryRecurrence21.carry_fract_doubling) " ++
      "is never used to extract a digit or a density. No empty/zero-floor/vacuous shortcut." ]

theorem o3SlopePeriodicFloorResiduals_nonempty : o3SlopePeriodicFloorResiduals ≠ [] := by
  simp [o3SlopePeriodicFloorResiduals]

end Erdos260.O3SlopePeriodicFloor
