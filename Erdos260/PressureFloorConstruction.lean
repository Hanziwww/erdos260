import Mathlib
import Erdos260.CarryAllocation
import Erdos260.CarryDataFactory
import Erdos260.Constants
import Erdos260.Pressure

/-!
# Lemma 21.1 pressure floor: constructing the carry data and closing `hAlloc`

This file is the *engine* assembly for Lemma 21.1 of `proof_v2.tex`.  The pure
content of the pressure floor

  `cPr · X · (r + 1) ≤ highExcessMass (highExcessStarts …) …`

is already proved in the library (`CarryDataFromFailure.highExcessMass_lower`,
which itself chains the *entropy/counting* window-sum lower bound
`windowSumLower_proof`, the low-excess upper bound `lowExcessUpper_KY_bound`, and
the pure algebra `lemma21_1_pressureLowerBound`).  But that theorem *consumes* a
`CarryDataFromFailure`, whose construction requires the **numerical allocation
inequality** `hAlloc`.  Until now `hAlloc` was an unconditional external
obligation in *every* constructor of `CarryDataFromFailure`; the elementary
budget pieces needed to discharge it were proved separately in
`CarryAllocation.lean` but never composed nor fed to a constructor.

This file finishes that loop:

* `hAlloc_manuscript_strict` — composes the four `CarryAllocation` budget lemmas
  (`hThresholdBudget_from_kappa_floor`, `hErrorBudget_from_carry_growth`,
  `hDominate_from_threshold_and_error_budget`, `hAlloc_from_kBound`) into a
  *single proof* of the K-form `hAlloc`, for any pressure constant `cPr ≤ 1/2`,
  any window order `r` in the regime `κ·L ≤ r+1 ≤ L`, sufficiently large dyadic
  scale (`B + 25 ≤ L`), and any failure constant in the K.4-small regime
  (`c0 ≤ κ/16`).  This is the genuine analytic numerical input, now **proved**.

* `carryDataPinned` — **actually constructs** a `CarryDataFromFailure shell
  erdos260Constants.cPr` from a failing dyadic shell, at the manuscript-pinned
  constants, discharging `hAlloc` via `hAlloc_manuscript_strict` (with the
  manuscript-robust choice `r = L`, `κ` replaced by `1`, which works for *every*
  failing shell since `c0 < κ < 1/16`).  This discharges the `carryData`
  residual atom for every sufficiently large, sufficiently rich failing shell.

* `pressureFloorPinned` — the **headline pressure floor**
  `cPr · X ≤ highExcessMass (highExcessStarts …) …` obtained from the
  constructed carry data and `highExcessMass_lower`, scaled by `r + 1 ≥ 1`.

## Honest residual

The construction is closed down to exactly these *structural* shell-window
inputs (no analytic inequality remains hidden):

* `hX_eq : shell.X = 2 ^ L` — the dyadic scale (always available from
  `shell.hXdyadic`; here named for the explicit `L`);
* `hB : shell.Q * 4 ≤ 2 ^ B` — the `Q`-dependent dyadic gap constant (a choice
  of `B`, always satisfiable);
* `hL : B + 25 ≤ L` — **"sufficiently large dyadic scale"** (the asymptotic
  qualifier inherent in Lemma 21.1);
* `hKr : L + 1 ≤ (supportShell shell.d shell.X).card` — **shell richness**: the
  shell `(X, 2X]` carries at least `L + 1` hits (the manuscript's window order
  needs at least `r + 1` hits; we use the order `r = L`).  The manuscript's
  smaller order `r ≈ κL` would relax this to `K ≥ κL` at the cost of requiring
  the tighter K.4 smallness `c0 ≤ κ/16` — see `hAlloc_manuscript_strict`.
* `h_supportCount_pos : 1 ≤ supportCount shell.d shell.X` — there is at least one
  hit in `[1, X]`.

Everything else — the entropy/counting lower bound, the low-excess upper bound,
the threshold/boundary/pressure budgeting, and the `2^L`-beats-polynomial growth
— is fully proved.  No `sorry`, no `admit`, no new `axiom`.
-/

namespace Erdos260

open Finset

noncomputable section

/-- `erdos260Constants.cPr = 1/2 ≤ 1/2` (the pinned manuscript pressure constant). -/
theorem erdos260Constants_cPr_le_half : erdos260Constants.cPr ≤ (1 / 2 : ℝ) :=
  le_of_eq manuscriptCpr_eq_half

/--
**Composed numerical allocation `hAlloc` (manuscript-strict, K-form).**

Chains the four budget lemmas of `CarryAllocation.lean` into a single proof of
the K-form allocation inequality consumed by
`CarryDataFromFailure.ofShellAndSupportCount`:

  `cPr·X·(r+1) + K·Y + K·T + (r+1)²·(L+B+1) ≤ (r+1)·X`,

valid whenever

* `cPr ≤ 1/2` (the pinned pressure constant pays at most half of `(r+1)X`),
* `X = 2^L` and `B + 25 ≤ L` (sufficiently large dyadic scale — the boundary
  gap error `(r+1)²(L+B+1)` is paid by `2^L`-beats-polynomial growth),
* `r ≤ L` (window order below the dyadic exponent),
* `0 ≤ κ`, `c0 ≤ κ/16`, `Y + T ≤ 4L`, `κ·L ≤ r+1` (the threshold contribution
  `K·(Y+T) ≤ c0·X·(Y+T)` is paid by a quarter of `(r+1)X`), and
* `K ≤ c0·X` (the failure hypothesis).

This is the genuine analytic numerical input of Lemma 21.1, now proved.
-/
theorem hAlloc_manuscript_strict
    {X K L B r : Nat} {T Y cPr c0 kappa : ℝ}
    (hcPr : cPr ≤ 1 / 2)
    (hX : X = 2 ^ L)
    (hr : r ≤ L)
    (hL : B + 25 ≤ L)
    (hkappa_nonneg : 0 ≤ kappa)
    (hc0_small : c0 ≤ kappa / 16)
    (hY_nn : 0 ≤ Y)
    (hT_nn : 0 ≤ T)
    (hYT : Y + T ≤ 4 * (L : ℝ))
    (hOrder : kappa * (L : ℝ) ≤ (r : ℝ) + 1)
    (hK_le : (K : ℝ) ≤ c0 * (X : ℝ)) :
    cPr * (X : ℝ) * ((r : ℝ) + 1) + (K : ℝ) * Y + (K : ℝ) * T +
        ((r : ℝ) + 1) ^ 2 * ((L : ℝ) + (B : ℝ) + 1) ≤
      ((r : ℝ) + 1) * (X : ℝ) := by
  have hYT_nn : 0 ≤ Y + T := by linarith
  have hThreshold :=
    hThresholdBudget_from_kappa_floor (X := X) (L := L) (r := r)
      (Y := Y) (T := T) (c0 := c0) (kappa := kappa)
      hkappa_nonneg hc0_small hYT_nn hYT hOrder
  have hError :=
    hErrorBudget_from_carry_growth (X := X) (L := L) (B := B) (r := r) hX hr hL
  have hDom :=
    hDominate_from_threshold_and_error_budget (X := X) (L := L) (B := B) (r := r)
      (T := T) (Y := Y) (cPr := cPr) (c0 := c0) hcPr hThreshold hError
  exact hAlloc_from_kBound (X := X) (K := K) (L := L) (B := B) (r := r)
    (T := T) (Y := Y) (cPr := cPr) (cQ := c0) hY_nn hT_nn hK_le hDom

/--
**Construction of the Lemma 21.1 carry data from a failing dyadic shell.**

At the manuscript-pinned constants (`cPr = erdos260Constants.cPr = 1/2`), using
the robust window order `r = L`, the manuscript threshold `T₀ = 2L + 1` and
floor `Y = εL = L/64`, this constructs a genuine `CarryDataFromFailure`.  The
numerical allocation `hAlloc` is discharged by `hAlloc_manuscript_strict` with
`κ := 1`, which is valid for *every* failing shell because the structural bound
`c0 < manuscriptKappa < 1/16` gives `c0 ≤ 1/16 = (1)/16`.

See the module doc-comment for the precise residual structural hypotheses.
-/
def carryDataPinned
    (shell : FailingDyadicShell) (L B : Nat)
    (hX_eq : shell.X = 2 ^ L)
    (hB : shell.Q * 4 ≤ 2 ^ B)
    (hL : B + 25 ≤ L)
    (hKr : L + 1 ≤ (supportShell shell.d shell.X).card)
    (h_supportCount_pos : 1 ≤ supportCount shell.d shell.X) :
    CarryDataFromFailure shell erdos260Constants.cPr :=
  CarryDataFromFailure.ofShellAndSupportCount shell erdos260Constants.cPr
    shell.hrational.choose L B L (2 * (L : ℝ) + 1) ((L : ℝ) / 64)
    (by positivity)
    shell.hrational.choose_spec
    hX_eq shell.X_pos hB hKr h_supportCount_pos
    (by
      have hc0_le : shell.c0 ≤ (1 / 16 : ℝ) :=
        le_of_lt (lt_trans shell.hc0_lt_kappa manuscriptKappa_lt_one_sixteenth)
      have hL25 : (25 : ℝ) ≤ (L : ℝ) := by
        have h : 25 ≤ L := by omega
        exact_mod_cast h
      refine hAlloc_manuscript_strict (kappa := 1) (c0 := shell.c0)
        ?_ hX_eq (le_refl L) hL ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · exact erdos260Constants_cPr_le_half
      · norm_num
      · linarith [hc0_le]
      · positivity
      · positivity
      · linarith [hL25]
      · simp only [one_mul]; linarith
      · exact le_of_lt shell.hfailure)

/--
**Manuscript-faithful order construction of the Lemma 21.1 carry data.**

The same construction as `carryDataPinned`, but with the *manuscript window
order* `r ≈ κL` exposed as a parameter (any `r` with `κ·L ≤ r+1 ≤ L`).  This
relaxes the shell-richness requirement to `r + 1 ≤ |supportShell|` (manuscript:
`K ≳ κL` hits suffice — far weaker than `K ≥ L+1`), at the price of the tighter
K.4 smallness `c0 ≤ κ/16` on the failure constant.  The pinned global failure
constant `manuscriptC0 = κ/64 ≤ κ/16` satisfies this (`manuscriptC0_le_kappa_div_sixteen`),
so this route applies to the canonical pinned shells with the manuscript order.
-/
def carryDataManuscriptOrder
    (shell : FailingDyadicShell) (L B r : Nat)
    (hX_eq : shell.X = 2 ^ L)
    (hB : shell.Q * 4 ≤ 2 ^ B)
    (hL : B + 25 ≤ L)
    (hr_le : r ≤ L)
    (hr_order : manuscriptKappa * (L : ℝ) ≤ (r : ℝ) + 1)
    (hc0_small : shell.c0 ≤ manuscriptKappa / 16)
    (hKr : r + 1 ≤ (supportShell shell.d shell.X).card)
    (h_supportCount_pos : 1 ≤ supportCount shell.d shell.X) :
    CarryDataFromFailure shell erdos260Constants.cPr :=
  CarryDataFromFailure.ofShellAndSupportCount shell erdos260Constants.cPr
    shell.hrational.choose L B r (2 * (L : ℝ) + 1) ((L : ℝ) / 64)
    (by positivity)
    shell.hrational.choose_spec
    hX_eq shell.X_pos hB hKr h_supportCount_pos
    (by
      have hL25 : (25 : ℝ) ≤ (L : ℝ) := by
        have h : 25 ≤ L := by omega
        exact_mod_cast h
      refine hAlloc_manuscript_strict (kappa := manuscriptKappa) (c0 := shell.c0)
        ?_ hX_eq hr_le hL ?_ hc0_small ?_ ?_ ?_ hr_order (le_of_lt shell.hfailure)
      · exact erdos260Constants_cPr_le_half
      · exact manuscriptKappa_pos.le
      · positivity
      · positivity
      · linarith [hL25])

/--
**Scaled pressure floor for any carry data.**

From `CarryDataFromFailure.highExcessMass_lower` (`cPr·X·(r+1) ≤ highExcessMass`)
and `0 ≤ cPr`, the unscaled floor `cPr·X ≤ highExcessMass` follows since
`r + 1 ≥ 1`.  This is the exact form consumed by the v5 contradiction engine
(`RoutedHighExcessChargeDataOldRes.refutes_failingShell`).
-/
theorem carryData_pressureFloor
    {shell : FailingDyadicShell} {cPr : ℝ}
    (hcPr : 0 ≤ cPr) (data : CarryDataFromFailure shell cPr) :
    cPr * (shell.X : ℝ) ≤
      highExcessMass
        (highExcessStarts data.starts (hitGap data.a) data.r data.T data.Y)
        (hitGap data.a) data.r data.T := by
  have hX : (0 : ℝ) ≤ (shell.X : ℝ) := shell.X_nonneg_real
  have hfloor := data.highExcessMass_lower
  have hbase : 0 ≤ cPr * (shell.X : ℝ) := mul_nonneg hcPr hX
  have hone : (1 : ℝ) ≤ (data.r : ℝ) + 1 := by
    have hr0 : (0 : ℝ) ≤ (data.r : ℝ) := Nat.cast_nonneg _
    linarith
  have hscale :
      cPr * (shell.X : ℝ) ≤ cPr * (shell.X : ℝ) * ((data.r : ℝ) + 1) := by
    calc cPr * (shell.X : ℝ) = cPr * (shell.X : ℝ) * 1 := by ring
      _ ≤ cPr * (shell.X : ℝ) * ((data.r : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hone hbase
  linarith [hscale, hfloor]

/--
**Lemma 21.1 pressure floor (manuscript-pinned, closed modulo structural inputs).**

For every failing dyadic shell of sufficiently large dyadic scale (`B + 25 ≤ L`)
that is sufficiently rich (`L + 1 ≤ |supportShell|`, `1 ≤ supportCount`), there
is a genuinely-constructed `CarryDataFromFailure` for which the unscaled
pressure floor

  `erdos260Constants.cPr · X ≤ highExcessMass (highExcessStarts …) …`

holds.  This closes the engine of Lemma 21.1's proof-by-contradiction down to
the structural shell-window hypotheses: the numerical allocation `hAlloc` — the
genuine analytic input — is **proved**, not assumed.
-/
theorem pressureFloorPinned
    (shell : FailingDyadicShell) (L B : Nat)
    (hX_eq : shell.X = 2 ^ L)
    (hB : shell.Q * 4 ≤ 2 ^ B)
    (hL : B + 25 ≤ L)
    (hKr : L + 1 ≤ (supportShell shell.d shell.X).card)
    (h_supportCount_pos : 1 ≤ supportCount shell.d shell.X) :
    ∃ data : CarryDataFromFailure shell erdos260Constants.cPr,
      erdos260Constants.cPr * (shell.X : ℝ) ≤
        highExcessMass
          (highExcessStarts data.starts (hitGap data.a) data.r data.T data.Y)
          (hitGap data.a) data.r data.T :=
  ⟨carryDataPinned shell L B hX_eq hB hL hKr h_supportCount_pos,
   carryData_pressureFloor erdos260Constants.cPr_pos.le _⟩

/--
**Lemma 21.1 pressure floor at the manuscript window order.**

The manuscript-faithful counterpart of `pressureFloorPinned`: for a failing
dyadic shell in the K.4-small regime (`c0 ≤ κ/16`), of sufficiently large scale,
carrying at least `r + 1` hits for a window order `r` in `[κL, L]`, the unscaled
pressure floor `cPr · X ≤ highExcessMass` holds.  This is the floor with the
manuscript order `r ≈ κL`, requiring only `K ≳ κL` shell hits.
-/
theorem pressureFloorManuscriptOrder
    (shell : FailingDyadicShell) (L B r : Nat)
    (hX_eq : shell.X = 2 ^ L)
    (hB : shell.Q * 4 ≤ 2 ^ B)
    (hL : B + 25 ≤ L)
    (hr_le : r ≤ L)
    (hr_order : manuscriptKappa * (L : ℝ) ≤ (r : ℝ) + 1)
    (hc0_small : shell.c0 ≤ manuscriptKappa / 16)
    (hKr : r + 1 ≤ (supportShell shell.d shell.X).card)
    (h_supportCount_pos : 1 ≤ supportCount shell.d shell.X) :
    ∃ data : CarryDataFromFailure shell erdos260Constants.cPr,
      erdos260Constants.cPr * (shell.X : ℝ) ≤
        highExcessMass
          (highExcessStarts data.starts (hitGap data.a) data.r data.T data.Y)
          (hitGap data.a) data.r data.T :=
  ⟨carryDataManuscriptOrder shell L B r hX_eq hB hL hr_le hr_order hc0_small hKr
      h_supportCount_pos,
   carryData_pressureFloor erdos260Constants.cPr_pos.le _⟩

end

end Erdos260
