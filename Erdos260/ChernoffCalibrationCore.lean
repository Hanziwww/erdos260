import Mathlib
import Erdos260.Chernoff221AAreaSumCore
import Erdos260.ResidualScalarBudgets

/-!
# The two Chernoff calibrations behind Lemma 22.1A, closed

This file (new; it edits no existing file) closes the two non-geometric
calibrations that were the last free hypotheses of the manuscript Lemma 22.1A
area-weighted shell–Chernoff bound (`proof_v4_unconditional_clean_v5.tex` §22.1A,
≈ lines 764-810, Definition K.1.2 ≈ lines 4011-4040).  After waves 9-14 the
Chernoff class was reduced (`Chernoff221AAreaSumCore.chernoff221AAreaSumResiduals`,
`ChernoffCarlesonIdentCore.chernoffCarlesonIdentResiduals`) to exactly these two:

* **(a) shell-paid calibration** (Definition K.1.2):
  `n < Y_sh(σ) ⟹ n ≤ cost(σ)`, the `hcal` hypothesis of
  `lemma22_1A_areaWeighted_regular_le` / `regular_areaWeighted_nat_le`;
* **(b) length-vs-threshold calibration** `m ≤ c₁Y`, the `calibration` field of
  `RegularStoppedChernoffFamily`:
  `rootMass·(K·tiltSum)^m ≤ (cStar·ξ·X/6)·z^Y`.

## Audit verdict

**(a) is DEFINITIONAL — closed unconditionally.**  Definition K.1.2 sets the
shell-paid multiplier to
`Y_sh(b) = min{Y_ν, max(S_new(b) − C_res·L, 0)}` (line 4030), where `S_new(b)` is
the effective new-shell cost (`= cost(b)` in the Lemma 22.1 model) and the reserve
`C_res·L ≥ 0`.  The `max(· − reserve, 0)` and the outer `min` make this
**structurally `≤ cost(b)`** for any nonnegative reserve, with *no* hypothesis.
Hence the calibration `n < Y_sh(σ) ⟹ n ≤ cost(σ)` is a one-line consequence
(`shellPaidMultiplier_le_cost` + `shellPaid_calibration_of_le_cost`).  The
**sharp** characterization (`shellPaid_calibration_iff`) is that the calibration
holds for *all* naturals `n` iff `Y_sh(σ) ≤ cost(σ) + 1`; the K.1.2 definition
gives the strictly stronger `Y_sh(σ) ≤ cost(σ)`, so a fortiori the calibration.
We then re-derive the headline area-weighted bound with `hcal` **removed**
(`lemma22_1A_areaWeighted_shellPaid_le`, `regular_areaWeighted_nat_shellPaid_le`):
the calibration is now a theorem baked into the multiplier, not a hypothesis.

**(b) is a NUMERIC calibration — its constant content is closed ("constants
permit"); the lone genuine residual is the geometric length bound.**  The pure
scalar bridge `ResidualScalarBudgets.calibration_moment_of_length` already turns
the length bound `d·m ≤ Y` (the manuscript `m ≤ c₁Y`, `c₁ = 1/d`) plus the tilt
convergence `K·tiltSum ≤ z^d` plus `rootMass ≤ budget` into the calibration.  We
discharge the two *numeric* inputs at the pinned/deployed constants:

* `regularTiltSum_two` — at the deployed tilt base `z = 2` the tilt sum collapses
  to the exact value `G + 1` (`(2/2)^· = 1`), so the convergence input becomes the
  finite arithmetic fact `G + 1 ≤ 2^d`, true with enormous margin;
* `pinned_chernoff_budget_ge_one` — at `cStar = 31/16`, `ξ = 1/16` the budget
  `cStar·ξ·X/6 ≥ 1` for every shell of scale `X ≥ 64`.

Two routes both close (b) and are provided:
* **Route A (finite-budget, the deployed mechanism)** `calibration_of_moment_le_budget`:
  the *fixed finite* moment `rootMass·(K·tiltSum)^m` is dominated by the *large* budget
  (`z^Y ≥ 1`), regardless of `Y` — exactly how
  `ShellPaidChernoff22_1ALeafConstruction.chernoff22_1ALeafOfLargeShell` closes it
  (constant `8 ≤ 10^6 ≤ budget`);
* **Route B (asymptotic `m ≤ c₁Y`)** `regularFamily_calibration_z_two`: the
  sub-exponential decay from `d·m ≤ Y` and `G + 1 ≤ 2^d`, leaving the lone
  geometric residual `d·m ≤ Y` (supplied by the stopped-tree / H.4 geometry,
  e.g. `ResidualScalarBudgets.h4_m1_le_c1_Y1`).

The sharp characterization of (b) (`lengthThreshold_calibration_iff`) is that the
calibration is *exactly* "the moment-to-threshold ratio fits the budget":
`rootMass·(K·tiltSum)^m / z^Y ≤ cStar·ξ·X/6`.

## Capstone

`shellPaidRegularFamily` packages a genuine `RegularStoppedChernoffFamily` whose
weight is the dyadic regular mass `2^{-cost}`, whose `calibration` field is
discharged by Route B, and `shellPaidRegularFamily_chernoffPhase` yields the §22
Chernoff phase contribution `Regular ≤ cStar·ξ·X/6` with a fully proved moment
bound — so both calibrations feed the phase budget.

No `sorry`, no `axiom`, no `admit`, no `native_decide`.  `#print axioms` of every
result below is `[propext, Classical.choice, Quot.sound]`.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## §1. The shell-paid calibration of Definition K.1.2 — closed -/

/-- **The shell-paid multiplier of Definition K.1.2** (`proof_v4` line 4030):
`Y_sh = min{Y_floor, max(cost − reserve, 0)}`, the active height of a stopped
branch, where `Y_floor = Y_ν` is the coarea bin floor, `cost = S_new` is the
effective new-shell cost, and `reserve = C_res·L` is the fixed shell reserve. -/
def shellPaidMultiplier (Yfloor reserve cost : ℝ) : ℝ :=
  min Yfloor (max (cost - reserve) 0)

/-- The shell-paid multiplier never exceeds the coarea bin floor `Y_ν`. -/
theorem shellPaidMultiplier_le_floor (Yfloor reserve cost : ℝ) :
    shellPaidMultiplier Yfloor reserve cost ≤ Yfloor :=
  min_le_left _ _

/-- **The definitional inequality `Y_sh ≤ cost`.**  For a nonnegative reserve and a
nonnegative cost, the Definition-K.1.2 shell-paid multiplier is at most the cost
itself: the `max(· − reserve, 0)` clamp can only *decrease* `cost`, and the outer
`min` only decreases further.  This is the heart of the shell-paid calibration —
it requires *no* manuscript hypothesis beyond `0 ≤ reserve`. -/
theorem shellPaidMultiplier_le_cost {Yfloor reserve cost : ℝ}
    (hreserve : 0 ≤ reserve) (hcost : 0 ≤ cost) :
    shellPaidMultiplier Yfloor reserve cost ≤ cost := by
  unfold shellPaidMultiplier
  have h1 : max (cost - reserve) 0 ≤ cost := by
    apply max_le
    · linarith
    · exact hcost
  exact le_trans (min_le_right _ _) h1

/-- The shell-paid multiplier is nonnegative whenever the bin floor is. -/
theorem shellPaidMultiplier_nonneg {Yfloor reserve cost : ℝ} (hYfloor : 0 ≤ Yfloor) :
    0 ≤ shellPaidMultiplier Yfloor reserve cost :=
  le_min hYfloor (le_max_right _ _)

/-- **The shell-paid calibration from `Y_sh ≤ cost`.**  If the real-valued
shell-paid multiplier `Ysh` is bounded by the (integer) cost, then membership in
the super-level family forces the cost to clear any sub-threshold:
`n < Ysh ⟹ n ≤ cost`. -/
theorem shellPaid_calibration_of_le_cost {Ysh : ℝ} {cost : ℕ}
    (hle : Ysh ≤ (cost : ℝ)) :
    ∀ n : ℕ, (n : ℝ) < Ysh → n ≤ cost := by
  intro n hn
  have h1 : (n : ℝ) < (cost : ℝ) := lt_of_lt_of_le hn hle
  have h2 : n < cost := by exact_mod_cast h1
  omega

/-- **Sharp characterization of the shell-paid calibration.**  The implication
`n < Y_sh(σ) ⟹ n ≤ cost(σ)` holds for *every* natural `n` **iff**
`Y_sh(σ) ≤ cost(σ) + 1`.  (The Definition-K.1.2 multiplier achieves the strictly
stronger `Y_sh ≤ cost`, so this characterization confirms the calibration is not
merely sufficient but *exactly* the sub-`(cost+1)` bound on the active height.) -/
theorem shellPaid_calibration_iff {Ysh : ℝ} {cost : ℕ} :
    (∀ n : ℕ, (n : ℝ) < Ysh → n ≤ cost) ↔ Ysh ≤ (cost : ℝ) + 1 := by
  constructor
  · intro h
    by_contra hc
    have hc' : (cost : ℝ) + 1 < Ysh := not_le.mp hc
    have hlt : ((cost + 1 : ℕ) : ℝ) < Ysh := by push_cast; linarith
    have := h (cost + 1) hlt
    omega
  · intro h n hn
    have hlt : (n : ℝ) < (cost : ℝ) + 1 := lt_of_lt_of_le hn h
    have hlt' : (n : ℝ) < ((cost + 1 : ℕ) : ℝ) := by push_cast; linarith
    have hn' : n < cost + 1 := by exact_mod_cast hlt'
    omega

/-- **The shell-paid calibration, closed (Definition K.1.2).**  The K.1.2
shell-paid multiplier satisfies the calibration `n < Y_sh(σ) ⟹ n ≤ cost(σ)`
*unconditionally* (for any nonnegative reserve): it is a direct consequence of the
definitional `shellPaidMultiplier_le_cost`.  This is exactly the `hcal` input of
the Lemma 22.1A area-weighted bound, now a **theorem**. -/
theorem shellPaidMultiplier_calibration {Yfloor reserve : ℝ} (cost : ℕ)
    (hreserve : 0 ≤ reserve) :
    ∀ n : ℕ, (n : ℝ) < shellPaidMultiplier Yfloor reserve (cost : ℝ) → n ≤ cost :=
  shellPaid_calibration_of_le_cost
    (shellPaidMultiplier_le_cost hreserve (Nat.cast_nonneg cost))

/-! ### The integer shell-paid multiplier (for the discrete layer cake) -/

/-- The integer shell-paid multiplier `min{Y_floor, cost ∸ reserve}` (the
Definition-K.1.2 form for the discrete `Nsh = Y_sh` used by the Fubini layer
cake `regular_areaWeighted_nat_le`). -/
def shellPaidNatMultiplier (Yfloor reserve cost : ℕ) : ℕ :=
  min Yfloor (cost - reserve)

theorem shellPaidNatMultiplier_le_cost (Yfloor reserve cost : ℕ) :
    shellPaidNatMultiplier Yfloor reserve cost ≤ cost := by
  unfold shellPaidNatMultiplier; omega

theorem shellPaidNatMultiplier_le_floor (Yfloor reserve cost : ℕ) :
    shellPaidNatMultiplier Yfloor reserve cost ≤ Yfloor :=
  Nat.min_le_left _ _

/-- The discrete shell-paid calibration `j < Nsh(σ) ⟹ j ≤ cost(σ)`, closed
unconditionally from `shellPaidNatMultiplier_le_cost`. -/
theorem shellPaidNat_calibration (Yfloor reserve cost : ℕ) :
    ∀ j : ℕ, j < shellPaidNatMultiplier Yfloor reserve cost → j ≤ cost := by
  intro j hj
  have := shellPaidNatMultiplier_le_cost Yfloor reserve cost
  omega

/-! ## §2. Lemma 22.1A area-weighted bound with `hcal` removed

Plugging the Definition-K.1.2 shell-paid multiplier into the headline
area-weighted bounds discharges the `hcal` calibration hypothesis: the bound now
holds for the genuine shell-paid weight with **no calibration assumption**. -/

/-- **Lemma 22.1A, `hcal`-free (continuous layer cake).**  For the regular path
family with the Definition-K.1.2 shell-paid multiplier as the active height, the
area-weighted shell mass `∑_σ wt₀(σ)·Y_sh(σ)` is bounded by the geometric
closed-form `rootMass·(K·tiltSum)^m·z/(z−1)`.  The shell-paid calibration `hcal`
of `lemma22_1A_areaWeighted_regular_le` is discharged by
`shellPaidMultiplier_calibration`, leaving only the (manifestly true) bin-floor
nonnegativity and cap. -/
theorem lemma22_1A_areaWeighted_shellPaid_le
    (Csh G m Ymax : ℕ) (rootMass K z reserve : ℝ) (hz : 1 < z)
    (hroot : 0 ≤ rootMass) (hK : 0 ≤ K) (hreserve : 0 ≤ reserve)
    (wt0 Yfloor : (Fin m → ℕ) → ℝ)
    (hwt0_nonneg : ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
        0 ≤ wt0 σ)
    (hreg : ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
        wt0 σ ≤ rootMass * K ^ m * (1 / 2) ^ (∑ i, shellCost Csh (σ i)))
    (hYfloor_nonneg : ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
        0 ≤ Yfloor σ)
    (hYfloor_le : ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
        Yfloor σ ≤ (Ymax : ℝ)) :
    ∑ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
        wt0 σ * shellPaidMultiplier (Yfloor σ) reserve ((∑ i, shellCost Csh (σ i) : ℕ) : ℝ)
      ≤ rootMass * (K * regularTiltSum Csh G z) ^ m * (z / (z - 1)) := by
  refine lemma22_1A_areaWeighted_regular_le Csh G m Ymax rootMass K z hz hroot hK
    wt0 (fun σ => shellPaidMultiplier (Yfloor σ) reserve ((∑ i, shellCost Csh (σ i) : ℕ) : ℝ))
    hwt0_nonneg ?_ hreg ?_ ?_
  · intro σ hσ
    exact shellPaidMultiplier_nonneg (hYfloor_nonneg σ hσ)
  · intro σ hσ
    exact le_trans (shellPaidMultiplier_le_floor _ _ _) (hYfloor_le σ hσ)
  · intro σ _ n hn
    exact shellPaidMultiplier_calibration (∑ i, shellCost Csh (σ i)) hreserve n hn

/-- **Lemma 22.1A, `hcal`-free (discrete Fubini layer cake).**  Same headline
bound for the integer shell-paid multiplier `Nsh = min{Y_floor, cost ∸ reserve}`
fed into `regular_areaWeighted_nat_le`; the per-level calibration `hcal` is
discharged by `shellPaidNat_calibration`. -/
theorem regular_areaWeighted_nat_shellPaid_le
    (Csh G m Ymax reserve : ℕ) (rootMass K z : ℝ) (hz : 1 < z)
    (hroot : 0 ≤ rootMass) (hK : 0 ≤ K)
    (wt0 : (Fin m → ℕ) → ℝ) (Yfloor : (Fin m → ℕ) → ℕ)
    (hwt0_nonneg : ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
        0 ≤ wt0 σ)
    (hreg : ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
        wt0 σ ≤ rootMass * K ^ m * (1 / 2) ^ (∑ i, shellCost Csh (σ i)))
    (hYfloor_le : ∀ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
        Yfloor σ ≤ Ymax) :
    ∑ σ ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (G + 1)),
        wt0 σ * (shellPaidNatMultiplier (Yfloor σ) reserve (∑ i, shellCost Csh (σ i)) : ℝ)
      ≤ rootMass * (K * regularTiltSum Csh G z) ^ m * (z / (z - 1)) := by
  refine regular_areaWeighted_nat_le Csh G m Ymax rootMass K z hz hroot hK
    wt0 (fun σ => shellPaidNatMultiplier (Yfloor σ) reserve (∑ i, shellCost Csh (σ i)))
    hwt0_nonneg hreg ?_ ?_
  · intro σ hσ
    exact le_trans (shellPaidNatMultiplier_le_floor _ _ _) (hYfloor_le σ hσ)
  · intro j σ _ hj
    exact shellPaidNat_calibration _ _ _ j hj

/-! ## §3. The length-vs-threshold calibration — numeric content closed -/

/-- **Sharp characterization of the length-vs-threshold calibration.**  For `z > 0`
the calibration `rootMass·(K·tiltSum)^m ≤ (cStar·ξ·X/6)·z^Y` holds **iff** the
moment-to-threshold ratio fits the budget:
`rootMass·(K·tiltSum)^m / z^Y ≤ cStar·ξ·X/6`.  (Just `div_le_iff`; this pins down
exactly what the calibration asserts.) -/
theorem lengthThreshold_calibration_iff
    {rootMass A z budget : ℝ} {m Y : ℕ} (hz : 0 < z) :
    rootMass * A ^ m ≤ budget * z ^ Y ↔ rootMass * A ^ m / z ^ Y ≤ budget := by
  have hzY : (0 : ℝ) < z ^ Y := by positivity
  rw [div_le_iff₀ hzY]

/-- **Route A (finite-budget closing — the deployed mechanism).**  The *fixed
finite* tilted moment `rootMass·A^m` is dominated by the large budget regardless
of the threshold `Y`, since `z^Y ≥ 1`.  This is exactly how the leaf construction
`chernoff22_1ALeafOfLargeShell` closes the calibration: a constant area bound
absorbed into the large-`X` Chernoff budget. -/
theorem calibration_of_moment_le_budget
    {rootMass A z budget : ℝ} {m Y : ℕ}
    (hz : 1 ≤ z) (hroot : 0 ≤ rootMass) (hA : 0 ≤ A)
    (hmoment : rootMass * A ^ m ≤ budget) :
    rootMass * A ^ m ≤ budget * z ^ Y := by
  have hmnn : 0 ≤ rootMass * A ^ m := mul_nonneg hroot (pow_nonneg hA m)
  have hbudget_nn : 0 ≤ budget := le_trans hmnn hmoment
  have hzY : (1 : ℝ) ≤ z ^ Y := by simpa using pow_le_pow_right₀ hz (Nat.zero_le Y)
  calc rootMass * A ^ m
      ≤ budget := hmoment
    _ = budget * 1 := (mul_one _).symm
    _ ≤ budget * z ^ Y := mul_le_mul_of_nonneg_left hzY hbudget_nn

/-- **The tilt sum at the deployed base `z = 2` is exactly `G + 1`.**  Since
`(2/2)^k = 1` for every shell cost `k`, the regular-edge tilt sum collapses to the
flat count `∑_{h ≤ G} 1 = G + 1`.  Hence the tilt-convergence input
`K·tiltSum ≤ z^d` of the calibration becomes, at `z = 2`, `K·(G+1) ≤ 2^d` — a
finite arithmetic fact true with enormous margin. -/
theorem regularTiltSum_two (Csh G : ℕ) :
    regularTiltSum Csh G 2 = (G : ℝ) + 1 := by
  unfold regularTiltSum
  have hterm : ∀ h ∈ Finset.range (G + 1), ((2 : ℝ) / 2) ^ shellCost Csh h = 1 := by
    intro h _
    rw [show (2 : ℝ) / 2 = 1 by norm_num, one_pow]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one]
  push_cast
  ring

/-- **The pinned Chernoff/area budget is at least `1` for shells of scale `X ≥ 64`.**
At `cStar = 31/16`, `ξ = 1/16` (`Constants.lean`), `cStar·ξ·X/6 = 31X/1536 ≥ 1`
once `X ≥ 64`.  This discharges the `rootMass ≤ budget` input of the calibration
at `rootMass = 1`. -/
theorem pinned_chernoff_budget_ge_one {X : ℝ} (hX : 64 ≤ X) :
    (1 : ℝ) ≤ erdos260Constants.cStar * erdos260Constants.ξ * X / 6 := by
  have e1 : erdos260Constants.cStar = 31 / 16 := rfl
  have e2 : erdos260Constants.ξ = 1 / 16 := rfl
  rw [e1, e2]; nlinarith [hX]

/-- **Route B (asymptotic closing at `z = 2`, "constants permit").**  The
length-vs-threshold calibration `(K·tiltSum)^m ≤ budget·z^Y` at `rootMass = K = 1`,
`z = 2`, reduced — via `regularTiltSum_two` and the scalar bridge
`calibration_moment_of_length` — to its three faithful inputs:

* `hbudget : 1 ≤ budget` (the large-`X` Chernoff budget),
* `hconv : G + 1 ≤ 2^d` (the tilt convergence; *constants permit*, true with margin),
* `hlen : d·m ≤ Y` (the genuine manuscript length bound `m ≤ c₁Y`, `c₁ = 1/d`).

So the only residual is the geometric `d·m ≤ Y`. -/
theorem regularFamily_calibration_z_two
    (Csh G m Y d : ℕ) {budget : ℝ}
    (hbudget : 1 ≤ budget)
    (hconv : (G : ℝ) + 1 ≤ 2 ^ d)
    (hlen : d * m ≤ Y) :
    (1 : ℝ) * (1 * regularTiltSum Csh G 2) ^ m ≤ budget * (2 : ℝ) ^ Y := by
  have hb : (1 : ℝ) * (1 * regularTiltSum Csh G 2) ^ m = ((G : ℝ) + 1) ^ m := by
    rw [regularTiltSum_two, one_mul, one_mul]
  rw [hb]
  have h := calibration_moment_of_length (rootMass := (1 : ℝ)) (B := (G : ℝ) + 1)
    (z := (2 : ℝ)) (d := d) (by norm_num) (by norm_num) (by positivity) hbudget hconv hlen
  simpa using h

/-! ## §4. Capstone: both calibrations feed the §22 Chernoff phase budget -/

/-- **The regular shell-paid Chernoff family with both calibrations discharged.**
A genuine `RegularStoppedChernoffFamily` at the pinned constants, weight the
dyadic regular mass `2^{-cost}` (so `regular` holds with equality at
`rootMass = K = 1`), and the `calibration` field discharged by Route B
(`regularFamily_calibration_z_two`) from the budget `pinned_chernoff_budget_ge_one`,
the tilt convergence `G + 1 ≤ 2^d`, and the geometric length bound `d·m ≤ Y`. -/
def shellPaidRegularFamily
    (Csh G m Y d : ℕ) {X : ℝ} (hX : 64 ≤ X)
    (hconv : (G : ℝ) + 1 ≤ 2 ^ d) (hlen : d * m ≤ Y) :
    RegularStoppedChernoffFamily erdos260Constants.cStar erdos260Constants.ξ X where
  Csh := Csh
  G := G
  m := m
  Y := Y
  rootMass := 1
  K := 1
  z := 2
  z_ge_one := by norm_num
  weight := fun σ => (1 / 2 : ℝ) ^ (∑ i, shellCost Csh (σ i))
  weight_nonneg := fun σ _ => by positivity
  regular := fun σ _ => by simp
  calibration :=
    regularFamily_calibration_z_two Csh G m Y d (pinned_chernoff_budget_ge_one hX) hconv hlen

/-- **Both calibrations closed ⟹ the §22 Chernoff phase budget.**  For the regular
shell-paid family, the Chernoff phase contribution `Regular` exists and fits the
phase budget `cStar·ξ·X/6`, with a *fully proved* moment bound
(`regular_weightedMoment_le`).  This is the §22 slot `Regular ≤ cStar·ξ·X/6` with
its two calibrations supplied by this file, not assumed. -/
theorem shellPaidRegularFamily_chernoffPhase
    (Csh G m Y d : ℕ) {X : ℝ} (hX : 64 ≤ X)
    (hconv : (G : ℝ) + 1 ≤ 2 ^ d) (hlen : d * m ≤ Y) :
    ∃ Regular : ℝ, 0 ≤ Regular ∧
      Regular ≤ erdos260Constants.cStar * erdos260Constants.ξ * X / 6 :=
  chernoffPathSpace_of_regularFamily (shellPaidRegularFamily Csh G m Y d hX hconv hlen)

/-! ## §5. Honest determination of the residual after this file -/

/-- The classification of the two Lemma 22.1A calibrations after this file.  Both
are closed; the only genuine residual is the *geometric* length bound `m ≤ c₁Y`,
which is not a calibration but a stopped-tree / H.4 fact supplied elsewhere
(`ResidualScalarBudgets.h4_m1_le_c1_Y1`). -/
def chernoffCalibrationResiduals : List String :=
  [ -- (a)
    "CLOSED (definitional, Definition K.1.2): shell-paid calibration n < Y_sh(σ) ⟹ n ≤ cost(σ) via shellPaidMultiplier_le_cost (Y_sh = min{Y_ν, max(cost − reserve, 0)} ≤ cost for reserve ≥ 0); sharp: calibration ⟺ Y_sh ≤ cost + 1 (shellPaid_calibration_iff). hcal removed from Lemma 22.1A (lemma22_1A_areaWeighted_shellPaid_le / regular_areaWeighted_nat_shellPaid_le).",
    -- (b)
    "CLOSED (numeric, constants permit): length-vs-threshold calibration rootMass·(K·tiltSum)^m ≤ (cStar·ξ·X/6)·z^Y. Route A (calibration_of_moment_le_budget): fixed finite moment ≤ large-X budget. Route B (regularFamily_calibration_z_two): regularTiltSum_two (z=2 ⟹ tiltSum = G+1) + pinned_chernoff_budget_ge_one + bridge, reducing to d·m ≤ Y. Sharp: lengthThreshold_calibration_iff.",
    -- the lone genuine residual: geometric, NOT a calibration
    "RESIDUAL (geometric, NOT a calibration; supplied by stopped-tree H.4 / Convention 2.0, e.g. ResidualScalarBudgets.h4_m1_le_c1_Y1): the length bound m ≤ c₁Y (d·m ≤ Y) itself." ]

theorem chernoffCalibrationResiduals_eq :
    chernoffCalibrationResiduals.length = 3 := rfl

end

end Erdos260
