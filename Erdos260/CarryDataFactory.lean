import Mathlib
import Erdos260.CarryPressureFactory
import Erdos260.CarryWindowLower
import Erdos260.Constants

/-!
# Carry data from a failing shell

This file names the precise carry-side data that must be constructed from a
failing dyadic shell before the pressure bridge can be used.  The arithmetic
from `CarryRecurrenceData` to the Lemma 21.1 lower bound is already proved in
`PressureLower.lean`; the remaining work is to build the fields below from the
rational binary input and the low-density failure hypothesis.
-/

namespace Erdos260

open Finset

noncomputable section

/-- The input hypotheses of one failing dyadic shell.

**Round Α2 (manuscript-strict)**: split the single failure constant
into two distinct manuscript constants:

* `cQ` — the target positive-density constant (`c_Q ≈ 1/8` in the manuscript).
* `c0` — the **failure** threshold (`c_0 ≪ κ` in the manuscript), strictly
  smaller than `κ`.  All quantitative failure analysis (low-excess,
  K.4 chains) uses `c0` rather than `cQ`.

We require:
- `hc0_pos : 0 < c0`
- `hc0_lt_kappa : c0 < manuscriptKappa`
- `hc0_le_cQ : c0 ≤ cQ` (so the weak `K < cQ · X` bound is still derivable;
  see `hfailure_cQ` below)
- `hfailure : K < c0 · X` (manuscript-strict tight bound)
-/
structure FailingDyadicShell where
  cQ : ℝ
  c0 : ℝ
  Q : Nat
  d : Nat -> Nat
  X : Nat
  hQ : 0 < Q
  hd : BinaryDigits d
  hnonterm : ¬ EventuallyZero d
  hrational :
    ∃ P : Int, realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ)
  hXdyadic : Dyadic X
  hc0_pos : 0 < c0
  hc0_lt_kappa : c0 < manuscriptKappa
  hc0_le_cQ : c0 ≤ cQ
  hfailure : ((supportShell d X).card : ℝ) < c0 * (X : ℝ)

/-- Derived: the manuscript-weak failure bound `K < cQ · X` follows from
`K < c0 · X` and `c0 ≤ cQ` (with `X ≥ 0`).  Existing carry / pressure
proofs that use `cQ` continue to compile through this projection. -/
theorem FailingDyadicShell.hfailure_cQ (shell : FailingDyadicShell) :
    ((supportShell shell.d shell.X).card : ℝ) < shell.cQ * (shell.X : ℝ) := by
  have h_strict := shell.hfailure
  have h_c0_le := shell.hc0_le_cQ
  have hX_nn : (0 : ℝ) ≤ (shell.X : ℝ) := by exact_mod_cast Nat.zero_le _
  have h_mul : shell.c0 * (shell.X : ℝ) ≤ shell.cQ * (shell.X : ℝ) :=
    mul_le_mul_of_nonneg_right h_c0_le hX_nn
  linarith

/-- A failing dyadic shell has positive dyadic scale. -/
theorem FailingDyadicShell.X_pos (shell : FailingDyadicShell) :
    1 ≤ shell.X := by
  rcases shell.hXdyadic with ⟨L, hL⟩
  rw [hL]
  exact Nat.one_le_two_pow

/-- Real-valued nonnegativity of the dyadic scale. -/
theorem FailingDyadicShell.X_nonneg_real (shell : FailingDyadicShell) :
    0 ≤ (shell.X : ℝ) := by
  exact_mod_cast Nat.zero_le shell.X

/-- Real-valued positivity of the dyadic scale. -/
theorem FailingDyadicShell.X_pos_real (shell : FailingDyadicShell) :
    0 < (shell.X : ℝ) := by
  exact_mod_cast shell.X_pos

/-- Build the failing-shell record from the global constants.

**Round Α2**: now requires the manuscript-strict failure `K < c0 · X` and
the three c₀-side hypotheses (`c0 > 0`, `c0 < κ`, `c0 ≤ cQ`). -/
def FailingDyadicShell.ofGlobalConstants
    (constants : Erdos260Constants)
    (Q : Nat) (d : Nat -> Nat) (X : Nat)
    (hQ : 0 < Q) (hd : BinaryDigits d)
    (hnonterm : ¬ EventuallyZero d)
    (hrational :
      ∃ P : Int, realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ))
    (hXdyadic : Dyadic X)
    (c0 : ℝ)
    (hc0_pos : 0 < c0)
    (hc0_lt_kappa : c0 < manuscriptKappa)
    (hc0_le_cQ : c0 ≤ constants.cQ)
    (hfailure : ((supportShell d X).card : ℝ) < c0 * (X : ℝ)) :
    FailingDyadicShell where
  cQ := constants.cQ
  c0 := c0
  Q := Q
  d := d
  X := X
  hQ := hQ
  hd := hd
  hnonterm := hnonterm
  hrational := hrational
  hXdyadic := hXdyadic
  hc0_pos := hc0_pos
  hc0_lt_kappa := hc0_lt_kappa
  hc0_le_cQ := hc0_le_cQ
  hfailure := hfailure

/-- **Manuscript-strict convenience** — at the pinned manuscript constants
(`cQ = 1/8`), the c₀-side hypotheses simplify since `c0 < κ < 1/16 < 1/8`
automatically gives `c0 ≤ cQ`. -/
def FailingDyadicShell.ofManuscriptConstants
    (Q : Nat) (d : Nat -> Nat) (X : Nat)
    (hQ : 0 < Q) (hd : BinaryDigits d)
    (hnonterm : ¬ EventuallyZero d)
    (hrational :
      ∃ P : Int, realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ))
    (hXdyadic : Dyadic X)
    (c0 : ℝ)
    (hc0_pos : 0 < c0)
    (hc0_lt_kappa : c0 < manuscriptKappa)
    (hfailure : ((supportShell d X).card : ℝ) < c0 * (X : ℝ)) :
    FailingDyadicShell :=
  FailingDyadicShell.ofGlobalConstants erdos260Constants
    Q d X hQ hd hnonterm hrational hXdyadic
    c0 hc0_pos hc0_lt_kappa
    (by
      have h_kappa_lt_eighth : manuscriptKappa < (1 / 8 : ℝ) := by
        have := manuscriptKappa_lt_one_sixteenth
        linarith
      have h_cQ_eq : erdos260Constants.cQ = (1 / 8 : ℝ) := rfl
      linarith)
    hfailure

/--
Carry-side data extracted from one failing dyadic shell.

This is the focused target for the carry recurrence formalization: construct a
hit sequence, the selected start window, the low-excess estimate, and the
numerical allocation inequality.
-/
structure CarryDataFromFailure (shell : FailingDyadicShell) (cPr : ℝ) where
  a : Nat -> Nat
  r : Nat
  L : Nat
  starts : Finset Nat
  T : ℝ
  Y : ℝ
  carry : CarryRecurrenceData shell.d a r shell.X L starts T Y
  hAlloc :
    cPr * (shell.X : ℝ) * ((r : ℝ) + 1) + carry.lowExcessBound +
        (starts.card : ℝ) * T + carry.gapBoundError <=
      ((r : ℝ) + 1) * (shell.X : ℝ)

/--
**Constructor of `CarryDataFromFailure` from the shell and manuscript bounds.**

Given a failing dyadic shell and the manuscript-supplied window-sum lower bound,
low-excess upper bound, and numerical allocation inequality (each expressed in
the canonical universally-quantified form over `HitSequence shell.d a`), the
hit enumeration `a` is constructed internally via
`exists_hitSequence_of_nonterminating`.

This replaces the previous interface where `a` was an external field of
`CarryDataFromFailure`.  The remaining external content is exactly the three
manuscript estimates `windowSumLower`, `lowExcessUpper`, and `hAlloc`.
-/
def CarryDataFromFailure.ofShellAndBounds
    (shell : FailingDyadicShell) (cPr : ℝ)
    (r L : Nat) (starts : Finset Nat) (T Y : ℝ)
    (gapBoundError : ℝ) (lowExcessBound : ℝ)
    (lowExcessBound_nonneg : 0 <= lowExcessBound)
    (windowSumLower :
      ∀ {a : Nat → Nat}, HitSequence shell.d a →
      ((r : ℝ) + 1) * (shell.X : ℝ) - gapBoundError <=
        ∑ k ∈ starts, ((a (k + r + 1) - a k : Nat) : ℝ))
    (lowExcessUpper :
      ∀ {a : Nat → Nat}, HitSequence shell.d a →
      highExcessMass
        (starts \ highExcessStarts starts (hitGap a) r T Y)
        (hitGap a) r T <= lowExcessBound)
    (hAlloc :
      cPr * (shell.X : ℝ) * ((r : ℝ) + 1) + lowExcessBound +
          (starts.card : ℝ) * T + gapBoundError <=
        ((r : ℝ) + 1) * (shell.X : ℝ)) :
    CarryDataFromFailure shell cPr :=
  let h := exists_hitSequence_of_nonterminating shell.hd shell.hnonterm
  { a := h.choose
    r := r
    L := L
    starts := starts
    T := T
    Y := Y
    carry :=
      { hits := h.choose_spec
        gapBoundError := gapBoundError
        windowSumLower := windowSumLower h.choose_spec
        lowExcessBound := lowExcessBound
        lowExcessBound_nonneg := lowExcessBound_nonneg
        lowExcessUpper := lowExcessUpper h.choose_spec }
    hAlloc := hAlloc }

/--
**Upgraded constructor: window-sum lower bound is now provided by
`windowSumLower_proof`** (manuscript Lemma 21.1).

Given a failing dyadic shell, the user only supplies the geometric
hypotheses needed by `windowSumLower_proof` (in universally-quantified
form over `HitSequence shell.d a`), together with the remaining two
manuscript estimates `lowExcessUpper` and `hAlloc`.  The window-sum
lower bound is then constructed internally via `windowSumLower_proof`
applied to the canonical hit enumeration.

`starts` is fixed to `Finset.Ico i (i + K)` where
`i = hseq.firstIndexAbove shell.X`, and `gapBoundError` is fixed to
`(r + 1)^2 * maxGap`.
-/
def CarryDataFromFailure.ofShellAndLowExcess
    (shell : FailingDyadicShell) (cPr : ℝ)
    (r L maxGap K : Nat) (T Y : ℝ)
    (hKr : r + 1 ≤ K)
    (h_first_pos :
      ∀ {a : Nat → Nat} (hseq : HitSequence shell.d a),
        1 ≤ hseq.firstIndexAbove shell.X)
    (h_a_im1_le :
      ∀ {a : Nat → Nat} (hseq : HitSequence shell.d a),
        a (hseq.firstIndexAbove shell.X - 1) ≤ shell.X)
    (h_a_iK_gt :
      ∀ {a : Nat → Nat} (hseq : HitSequence shell.d a),
        2 * shell.X + 1 ≤ a (hseq.firstIndexAbove shell.X + K))
    (h_gap_le :
      ∀ {a : Nat → Nat} (hseq : HitSequence shell.d a) (k : Nat),
        hseq.firstIndexAbove shell.X - 1 ≤ k →
        k < hseq.firstIndexAbove shell.X + r →
        hitGap a k ≤ maxGap)
    (lowExcessBound : ℝ) (lowExcessBound_nonneg : 0 ≤ lowExcessBound)
    (lowExcessUpper :
      ∀ {a : Nat → Nat} (hseq : HitSequence shell.d a),
      highExcessMass
        (Finset.Ico (hseq.firstIndexAbove shell.X)
                    (hseq.firstIndexAbove shell.X + K) \
         highExcessStarts
            (Finset.Ico (hseq.firstIndexAbove shell.X)
                        (hseq.firstIndexAbove shell.X + K))
            (hitGap a) r T Y)
        (hitGap a) r T ≤ lowExcessBound)
    (hAlloc :
      cPr * (shell.X : ℝ) * ((r : ℝ) + 1) + lowExcessBound +
          (K : ℝ) * T +
          ((r : ℝ) + 1) ^ 2 * (maxGap : ℝ) ≤
        ((r : ℝ) + 1) * (shell.X : ℝ)) :
    CarryDataFromFailure shell cPr :=
  let h := exists_hitSequence_of_nonterminating shell.hd shell.hnonterm
  let hseq := h.choose_spec
  let i := hseq.firstIndexAbove shell.X
  { a := h.choose
    r := r
    L := L
    starts := Finset.Ico i (i + K)
    T := T
    Y := Y
    carry :=
      { hits := hseq
        gapBoundError := ((r : ℝ) + 1) ^ 2 * (maxGap : ℝ)
        windowSumLower :=
          windowSumLower_proof hseq hKr (h_first_pos hseq)
            (h_a_im1_le hseq) (h_a_iK_gt hseq) (h_gap_le hseq)
        lowExcessBound := lowExcessBound
        lowExcessBound_nonneg := lowExcessBound_nonneg
        lowExcessUpper := lowExcessUpper hseq }
    hAlloc := by
      have h_card_nat :
          (Finset.Ico i (i + K)).card = K := by
        rw [Nat.card_Ico]; omega
      have h_card :
          ((Finset.Ico i (i + K)).card : ℝ) = (K : ℝ) := by
        exact_mod_cast h_card_nat
      rw [h_card]
      exact hAlloc }

/--
**Upgraded constructor: geometric hypotheses are now provided automatically.**

Building on `ofShellAndLowExcess`, this constructor discharges the three
shell-window geometric hypotheses (`h_a_im1_le`, `h_a_iK_gt`, `h_gap_le`)
internally, using the dyadic structure (`shell.X = 2 ^ L`) and the
carry/dyadic constants (`Q · 4 ≤ 2 ^ B`) together with the
`HitSequence`-level lemmas
`a_firstIndexAbove_add_card_gt`, `a_le_two_mul_of_lt_add_card`,
`hitGap_le_of_shell_window`.

Only one geometric hypothesis remains external: `h_first_pos`, which says
the shell starts strictly after the first hit (`1 ≤ firstIndexAbove X`).
This holds whenever `shell.X` is at least the first hit `a 0`, and is
manuscript-level "sufficiently large `X`" content.

The shell-window length `K` is fixed to `|supportShell shell.d shell.X|`
and the per-gap bound `maxGap` is fixed to `L + B + 1`.
-/
def CarryDataFromFailure.ofShellAndCarryParams
    (shell : FailingDyadicShell) (cPr : ℝ)
    (P : Int) (L B r : Nat) (T Y : ℝ)
    (hP :
      realWeightedValue (natBinaryAsReal shell.d) =
        (P : ℝ) / (shell.Q : ℝ))
    (hX_eq : shell.X = 2 ^ L)
    (hX_pos : 1 ≤ shell.X)
    (hB : shell.Q * 4 ≤ 2 ^ B)
    (hKr : r + 1 ≤ (supportShell shell.d shell.X).card)
    (h_first_pos :
      ∀ {a : Nat → Nat} (hseq : HitSequence shell.d a),
        1 ≤ hseq.firstIndexAbove shell.X)
    (lowExcessBound : ℝ) (lowExcessBound_nonneg : 0 ≤ lowExcessBound)
    (lowExcessUpper :
      ∀ {a : Nat → Nat} (hseq : HitSequence shell.d a),
      highExcessMass
        (Finset.Ico (hseq.firstIndexAbove shell.X)
                    (hseq.firstIndexAbove shell.X +
                      (supportShell shell.d shell.X).card) \
         highExcessStarts
            (Finset.Ico (hseq.firstIndexAbove shell.X)
                        (hseq.firstIndexAbove shell.X +
                          (supportShell shell.d shell.X).card))
            (hitGap a) r T Y)
        (hitGap a) r T ≤ lowExcessBound)
    (hAlloc :
      cPr * (shell.X : ℝ) * ((r : ℝ) + 1) + lowExcessBound +
          ((supportShell shell.d shell.X).card : ℝ) * T +
          ((r : ℝ) + 1) ^ 2 * ((L : ℝ) + (B : ℝ) + 1) ≤
        ((r : ℝ) + 1) * (shell.X : ℝ)) :
    CarryDataFromFailure shell cPr :=
  CarryDataFromFailure.ofShellAndLowExcess shell cPr
    r L (L + B + 1) (supportShell shell.d shell.X).card T Y
    hKr
    (fun {_a} hseq => h_first_pos hseq)
    (fun {_a} hseq => by
      apply hseq.lt_firstIndexAbove shell.X
      have h_fp := h_first_pos hseq
      omega)
    (fun {_a} hseq => by
      have h := hseq.a_firstIndexAbove_add_card_gt shell.X
      omega)
    (fun {_a} hseq k _hk_lo hk_hi =>
      hseq.hitGap_le_of_shell_window shell.hd shell.hQ hP hX_eq hX_pos hB
        hKr hk_hi)
    lowExcessBound lowExcessBound_nonneg
    lowExcessUpper
    (by push_cast; linarith [hAlloc])

/--
**Cleanest constructor**: `lowExcessUpper` is now provided automatically.

Building on `ofShellAndCarryParams`, this constructor fixes
`lowExcessBound = K · Y` (where `K = |supportShell shell.d shell.X|`)
and discharges the universally-quantified `lowExcessUpper` hypothesis
using `lowExcessUpper_KY_bound`.

Only **three** manuscript-level external obligations remain:

- `h_first_pos` (the shell starts after the first hit, manuscript-natural
  for sufficiently large `shell.X`);
- `hY` (`0 ≤ Y`, manuscript-natural);
- `hAlloc` (the K.4 numerical allocation inequality, restated with
  `K · Y` in place of an abstract `lowExcessBound`).

All four shell-window geometric facts and the universally-quantified
low-excess upper bound are now proved theorems.
-/
def CarryDataFromFailure.ofShellAndCarryParamsClean
    (shell : FailingDyadicShell) (cPr : ℝ)
    (P : Int) (L B r : Nat) (T Y : ℝ)
    (hY : 0 ≤ Y)
    (hP :
      realWeightedValue (natBinaryAsReal shell.d) =
        (P : ℝ) / (shell.Q : ℝ))
    (hX_eq : shell.X = 2 ^ L)
    (hX_pos : 1 ≤ shell.X)
    (hB : shell.Q * 4 ≤ 2 ^ B)
    (hKr : r + 1 ≤ (supportShell shell.d shell.X).card)
    (h_first_pos :
      ∀ {a : Nat → Nat} (hseq : HitSequence shell.d a),
        1 ≤ hseq.firstIndexAbove shell.X)
    (hAlloc :
      cPr * (shell.X : ℝ) * ((r : ℝ) + 1) +
          ((supportShell shell.d shell.X).card : ℝ) * Y +
          ((supportShell shell.d shell.X).card : ℝ) * T +
          ((r : ℝ) + 1) ^ 2 * ((L : ℝ) + (B : ℝ) + 1) ≤
        ((r : ℝ) + 1) * (shell.X : ℝ)) :
    CarryDataFromFailure shell cPr :=
  CarryDataFromFailure.ofShellAndCarryParams shell cPr P L B r T Y
    hP hX_eq hX_pos hB hKr h_first_pos
    ((supportShell shell.d shell.X).card * Y)
    (mul_nonneg (by exact_mod_cast Nat.zero_le _) hY)
    (fun {a} hseq =>
      lowExcessUpper_KY_bound (a := a) (hseq.firstIndexAbove shell.X)
        (supportShell shell.d shell.X).card r T Y hY)
    hAlloc

/--
**Even cleaner constructor**: `h_first_pos` is now discharged from
`1 ≤ supportCount shell.d shell.X` (a single Nat-level manuscript-natural
hypothesis), via `HitSequence.firstIndexAbove_pos_of_supportCount_pos`.

Only **three** manuscript-level external obligations remain:

- `h_supportCount_pos : 1 ≤ supportCount shell.d shell.X`
  (the shell has at least one hit in `[1, X]`; equivalent to `a 0 ≤ X`).
- `hY : 0 ≤ Y` (manuscript-natural).
- `hAlloc`: the K.4 numerical allocation inequality (still abstract here;
  Phase A2 will discharge under pinned constants and `X ≥ X₀`).
-/
def CarryDataFromFailure.ofShellAndSupportCount
    (shell : FailingDyadicShell) (cPr : ℝ)
    (P : Int) (L B r : Nat) (T Y : ℝ)
    (hY : 0 ≤ Y)
    (hP :
      realWeightedValue (natBinaryAsReal shell.d) =
        (P : ℝ) / (shell.Q : ℝ))
    (hX_eq : shell.X = 2 ^ L)
    (hX_pos : 1 ≤ shell.X)
    (hB : shell.Q * 4 ≤ 2 ^ B)
    (hKr : r + 1 ≤ (supportShell shell.d shell.X).card)
    (h_supportCount_pos : 1 ≤ supportCount shell.d shell.X)
    (hAlloc :
      cPr * (shell.X : ℝ) * ((r : ℝ) + 1) +
          ((supportShell shell.d shell.X).card : ℝ) * Y +
          ((supportShell shell.d shell.X).card : ℝ) * T +
          ((r : ℝ) + 1) ^ 2 * ((L : ℝ) + (B : ℝ) + 1) ≤
        ((r : ℝ) + 1) * (shell.X : ℝ)) :
    CarryDataFromFailure shell cPr :=
  CarryDataFromFailure.ofShellAndCarryParamsClean shell cPr P L B r T Y
    hY hP hX_eq hX_pos hB hKr
    (fun {_a} hseq =>
      hseq.firstIndexAbove_pos_of_supportCount_pos h_supportCount_pos)
    hAlloc

/--
Strict-failure constructor using the manuscript low-excess scale
`c₀ * X * Y` directly.

The coarse constructor above sets `lowExcessBound = K * Y`; under the strict
failure hypothesis carried by `FailingDyadicShell`, `K < c₀ * X`, so the
low-excess upper bound is available at the sharper proof-v4 scale.
-/
def CarryDataFromFailure.ofShellAndSupportCountFailureBound
    (shell : FailingDyadicShell) (cPr : ℝ)
    (P : Int) (L B r : Nat) (T Y : ℝ)
    (hY : 0 ≤ Y)
    (hP :
      realWeightedValue (natBinaryAsReal shell.d) =
        (P : ℝ) / (shell.Q : ℝ))
    (hX_eq : shell.X = 2 ^ L)
    (hX_pos : 1 ≤ shell.X)
    (hB : shell.Q * 4 ≤ 2 ^ B)
    (hKr : r + 1 ≤ (supportShell shell.d shell.X).card)
    (h_supportCount_pos : 1 ≤ supportCount shell.d shell.X)
    (hAlloc :
      cPr * (shell.X : ℝ) * ((r : ℝ) + 1) +
          shell.c0 * (shell.X : ℝ) * Y +
          ((supportShell shell.d shell.X).card : ℝ) * T +
          ((r : ℝ) + 1) ^ 2 * ((L : ℝ) + (B : ℝ) + 1) ≤
        ((r : ℝ) + 1) * (shell.X : ℝ)) :
    CarryDataFromFailure shell cPr :=
  CarryDataFromFailure.ofShellAndCarryParams shell cPr P L B r T Y
    hP hX_eq hX_pos hB hKr
    (fun {_a} hseq =>
      hseq.firstIndexAbove_pos_of_supportCount_pos h_supportCount_pos)
    (shell.c0 * (shell.X : ℝ) * Y)
    (by
      have hc0_nonneg : 0 ≤ shell.c0 := le_of_lt shell.hc0_pos
      have hX_nonneg : 0 ≤ (shell.X : ℝ) := by exact_mod_cast Nat.zero_le shell.X
      exact mul_nonneg (mul_nonneg hc0_nonneg hX_nonneg) hY)
    (fun {a} hseq =>
      lowExcessUpper_failure_bound (a := a)
        (hseq.firstIndexAbove shell.X)
        (supportShell shell.d shell.X).card r T Y shell.c0 (shell.X : ℝ)
        hY (le_of_lt shell.hfailure))
    hAlloc

theorem CarryDataFromFailure.highExcessMass_lower
    {shell : FailingDyadicShell} {cPr : ℝ}
    (data : CarryDataFromFailure shell cPr) :
    cPr * (shell.X : ℝ) * ((data.r : ℝ) + 1) <=
      highExcessMass
        (highExcessStarts data.starts (hitGap data.a) data.r data.T data.Y)
        (hitGap data.a) data.r data.T :=
  pressureLowerBound_from_carry data.carry data.hAlloc

/--
Provider for the carry recurrence data on all sufficiently large failing
shells.  This is the exact target for the carry/gap part of the manuscript.
-/
structure CarryDataProvider where
  constants : Erdos260Constants
  data :
    ∀ shell : FailingDyadicShell,
      shell.cQ = constants.cQ ->
        CarryDataFromFailure shell constants.cPr

/-- **Round Α2**: `dataOfGlobalShell` now takes the c₀-side hypotheses
in addition to the original arguments. -/
def CarryDataProvider.dataOfGlobalShell
    (provider : CarryDataProvider)
    {Q : Nat} {d : Nat -> Nat} {X : Nat}
    (hQ : 0 < Q) (hd : BinaryDigits d)
    (hnonterm : ¬ EventuallyZero d)
    (hrational :
      ∃ P : Int, realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ))
    (hXdyadic : Dyadic X)
    (c0 : ℝ)
    (hc0_pos : 0 < c0)
    (hc0_lt_kappa : c0 < manuscriptKappa)
    (hc0_le_cQ : c0 ≤ provider.constants.cQ)
    (hfailure : ((supportShell d X).card : ℝ) < c0 * (X : ℝ)) :
    CarryDataFromFailure
      (FailingDyadicShell.ofGlobalConstants provider.constants Q d X
        hQ hd hnonterm hrational hXdyadic
        c0 hc0_pos hc0_lt_kappa hc0_le_cQ hfailure)
      provider.constants.cPr :=
  provider.data
    (FailingDyadicShell.ofGlobalConstants provider.constants Q d X
      hQ hd hnonterm hrational hXdyadic
      c0 hc0_pos hc0_lt_kappa hc0_le_cQ hfailure)
    rfl

/--
Once the carry-side data and the charged high-excess decomposition are known,
construct the full `CarryPressureBridge`.
-/
def CarryDataFromFailure.toBridge
    {shell : FailingDyadicShell} {cPr cStar ξ : ℝ}
    {phaseData : ClosurePhaseData cStar ξ (shell.X : ℝ)}
    (data : CarryDataFromFailure shell cPr)
    (highExcess_le_phaseMass :
      highExcessMass
          (highExcessStarts data.starts (hitGap data.a) data.r data.T data.Y)
          (hitGap data.a) data.r data.T <=
        ClosurePhaseMass phaseData) :
    CarryPressureBridge cPr shell.X phaseData where
  d := shell.d
  a := data.a
  r := data.r
  L := data.L
  starts := data.starts
  T := data.T
  Y := data.Y
  carry := data.carry
  hAlloc := data.hAlloc
  highExcess_le_phaseMass := highExcess_le_phaseMass

end

end Erdos260
