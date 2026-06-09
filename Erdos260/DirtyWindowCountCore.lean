import Mathlib
import Erdos260.DirtyFibreBoundCore
import Erdos260.Erdos260ReducedToCoresV2

/-!
# The Dirty K.2.5 window run-scale count: the genuine combinatorial core

This module attacks the single residual exposed by `DirtyFibreBoundCore`, namely

> `WindowRunScaleCountBound ctx CM` :
>   `∀ a, #{ n ∈ dirtyShellWindow ctx | windowRunScale ctx n = a } ≤ (log* L) ^ CM`,

the **pure digit-sequence count**: how many positions of the stopped support
window `(X, 2X]` carry a forward `1`-run whose dyadic scale `log₂(run length)`
equals a fixed `a`.  It is the field `dirtyWindow` of `Erdos260PhaseCoresV2`
(through `dirtyLeafFibreBound_of_window`, `diagonalFibre_card_eq`).

## The honest finding (confirmed and made precise here)

The Phase-2 `dirtyFamilyOfShell` model collapses *arm = period = forward run
length* (`DirtyFibreBoundCore.dirtyFamily_scale_diagonal`), so the K.2.5 fibre
count is the genuinely **one-dimensional** interval count above: positions of a
fixed run-scale `a` inside a length-`L` window.  On this collapsed model the
count is **`Θ(window)` in the worst case** and therefore *cannot* be bounded by
`(log* L)^C` for an absolute constant `C`:

* `runLengthFrom_const` + `allOnes_window_count_eq_card` exhibit the obstruction
  concretely.  For the constant-`1` digit sequence the forward run length is
  fuel-saturated (`= 2X`) at **every** window position, so all `X = #window`
  window positions share the single scale `a₀ = log₂(2X)`; the level-set count
  for `a₀` equals the entire window cardinality `X` (`= 2^L`-large), while
  `(log* L)^C = (log₂ log₂ L)^C` is only poly-`log log L`.

So the manuscript's absolute `(log* L)^C` is genuinely a property of the *full*
J.4 D1–D7 cleaning / anchored-priority / non-separation structure, which has been
collapsed away in the Lean model.  We therefore deliver option (b) of the task:

1. **`WindowRunScaleCountBound` is fully discharged with a concrete ctx-dependent
   constant** — `dirtyCMWindow ctx := (dirtyShellWindow ctx).card` — closing the
   `dirtyWindow` field of `Erdos260PhaseCoresV2`
   (`windowRunScaleCountBound_window_card`, `dirtyLeafFibreBound_window`).  This
   is green, axiom-clean, `sorry`-free, and the constant is **essentially sharp**
   by the all-ones obstruction.  It is *not* the manuscript's absolute `C`
   (documented honestly).

2. **The genuine sharp "few-runs" combinatorics** is proved as named lemmas: the
   forward run length is locally exact (`runLengthFrom_add_of_run`,
   `runLengthFrom_eq_of_clean`), so positions sharing one *clean (uncapped)* run
   length are `v`-separated (`runLengthFrom_clean_sep`) and a `g`-separated subset
   of a length-`L` window has `≤ L/g + 1` elements (`card_le_of_gapSeparated`,
   the constant-gap analogue of the `IsLiftChain.card_le` tower bound).  These
   combine to the **sharp `≤ X/v + 1` bound for a fixed clean run length**
   (`windowExactRunCount_le_of_clean`) — the honest realization of the
   manuscript's "positions of length-`2^a` runs are `≤ L/2^a`".  Summing this over
   the `2^a` exact lengths of a scale reintroduces the `Θ(L)` count, which is
   precisely why no absolute `C` survives the collapse.

No `sorry`, `axiom`, or `admit`.
-/

namespace Erdos260

open Finset

/-! ## Part A — forward run-length combinatorics (the local structure)

`runLengthFrom d val fuel n` (from `DirtyLeafFromShell`) is the forward maximal
`val`-run starting at `n`, capped by `fuel` steps.  The following lemmas pin down
its exact local behaviour. -/

/-- The defining successor recursion of `runLengthFrom` (definitional). -/
theorem runLengthFrom_succ (d : Nat → Nat) (val fuel n : Nat) :
    runLengthFrom d val (fuel + 1) n
      = if d n = val then runLengthFrom d val fuel (n + 1) + 1 else 0 := rfl

/-- The run length never exceeds the fuel. -/
theorem runLengthFrom_le_fuel (d : Nat → Nat) (val : Nat) :
    ∀ (fuel n : Nat), runLengthFrom d val fuel n ≤ fuel := by
  intro fuel
  induction fuel with
  | zero => intro n; have h0 : runLengthFrom d val 0 n = 0 := rfl; omega
  | succ f ih =>
    intro n
    rw [runLengthFrom_succ]
    by_cases hd : d n = val
    · rw [if_pos hd]; have := ih (n + 1); omega
    · rw [if_neg hd]; omega

/-- Every position strictly inside the counted run carries the run value: if
`i < runLengthFrom d val fuel n` then `d (n + i) = val`. -/
theorem runLengthFrom_digit_within (d : Nat → Nat) (val : Nat) :
    ∀ (fuel n i : Nat), i < runLengthFrom d val fuel n → d (n + i) = val := by
  intro fuel
  induction fuel with
  | zero => intro n i hi; have h0 : runLengthFrom d val 0 n = 0 := rfl; omega
  | succ f ih =>
    intro n i hi
    rw [runLengthFrom_succ] at hi
    by_cases hd : d n = val
    · rw [if_pos hd] at hi
      cases i with
      | zero => simpa using hd
      | succ j =>
        have hj : j < runLengthFrom d val f (n + 1) := by omega
        have hd2 := ih (n + 1) j hj
        rw [show n + (j + 1) = (n + 1) + j by omega]
        exact hd2
    · rw [if_neg hd] at hi
      exact absurd hi (Nat.not_lt_zero i)

/-- **Additivity along a known run.**  If the first `j` positions from `n` all
carry `val` (and `j ≤ fuel`), then the count splits exactly:
`runLengthFrom d val fuel n = j + runLengthFrom d val (fuel - j) (n + j)`.
This is the local "decrease by one per step inside a run" law. -/
theorem runLengthFrom_add_of_run (d : Nat → Nat) (val : Nat) :
    ∀ (j fuel n : Nat), j ≤ fuel → (∀ i, i < j → d (n + i) = val) →
      runLengthFrom d val fuel n = j + runLengthFrom d val (fuel - j) (n + j) := by
  intro j
  induction j with
  | zero => intro fuel n _ _; simp
  | succ k ih =>
    intro fuel n hjf hrun
    have hd : d n = val := by
      have h0 := hrun 0 (by omega)
      simpa using h0
    cases fuel with
    | zero => exact absurd hjf (by omega)
    | succ f =>
      rw [runLengthFrom_succ, if_pos hd]
      have hkf : k ≤ f := by omega
      have hrun' : ∀ i, i < k → d ((n + 1) + i) = val := by
        intro i hi
        have hmem := hrun (i + 1) (by omega)
        rw [show n + (i + 1) = (n + 1) + i by omega] at hmem
        exact hmem
      rw [ih f (n + 1) hkf hrun']
      rw [show (n + 1) + k = n + (k + 1) by omega]
      rw [show f + 1 - (k + 1) = f - k by omega]
      omega

/-- **Exactness for a clean (uncapped) run.**  If positions `n, …, n+ℓ-1` all
carry `val`, position `n+ℓ` does *not*, and there is enough fuel (`ℓ < fuel`),
then the run length is exactly `ℓ`. -/
theorem runLengthFrom_eq_of_clean (d : Nat → Nat) (val : Nat) (ℓ n fuel : Nat)
    (hrun : ∀ i, i < ℓ → d (n + i) = val) (hend : d (n + ℓ) ≠ val) (hfuel : ℓ < fuel) :
    runLengthFrom d val fuel n = ℓ := by
  rw [runLengthFrom_add_of_run d val ℓ fuel n (le_of_lt hfuel) hrun]
  have hz : runLengthFrom d val (fuel - ℓ) (n + ℓ) = 0 := by
    obtain ⟨g, hg⟩ : ∃ g, fuel - ℓ = g + 1 := ⟨fuel - ℓ - 1, by omega⟩
    rw [hg, runLengthFrom_succ, if_neg hend]
  rw [hz, Nat.add_zero]

/-- **`v`-separation of equal clean run lengths.**  If `m` starts a *clean*
(uncapped) run of length `v ≥ 1` and `n > m` also has forward run length `v`,
then `n` is past the end of `m`'s run: `m + v ≤ n`.  (Two positions inside the
same run have strictly different forward run lengths.) -/
theorem runLengthFrom_clean_sep (d : Nat → Nat) (val : Nat) {m n v F F' : Nat}
    (hm : runLengthFrom d val F m = v)
    (hclean : d (m + v) ≠ val) (hmn : m < n)
    (hn : runLengthFrom d val F' n = v) :
    m + v ≤ n := by
  by_contra hlt
  simp only [not_le] at hlt
  have hrun_m : ∀ i, i < v → d (m + i) = val := by
    intro i hi
    exact runLengthFrom_digit_within d val F m i (by rw [hm]; exact hi)
  set j := n - m with hjdef
  have hj1 : 1 ≤ j := by omega
  have hjv : j < v := by omega
  have hneq : n = m + j := by omega
  have hrun_n : ∀ i, i < v - j → d (n + i) = val := by
    intro i hi
    rw [hneq, show m + j + i = m + (j + i) by omega]
    exact hrun_m (j + i) (by omega)
  have hend_n : d (n + (v - j)) ≠ val := by
    rw [hneq, show m + j + (v - j) = m + v by omega]
    exact hclean
  have hF' : v - j < F' := by
    have hle : v ≤ F' := by
      have hb := runLengthFrom_le_fuel d val F' n
      rw [hn] at hb; exact hb
    omega
  have he := runLengthFrom_eq_of_clean d val (v - j) n F' hrun_n hend_n hF'
  rw [hn] at he
  omega

/-! ## Part B — the constant-gap separated-set cardinality bound

The constant-gap analogue of `Erdos260.IsLiftChain.card_le` (from
`ReturnM2J4Core`): a `g`-separated subset of an interval `[lo, M]` has at most
`(M - lo)/g + 1` elements.  The proof injects `x ↦ (x - lo)/g` into a range. -/

/-- A `g`-separated (`x < y ⇒ x + g ≤ y`) subset of `[lo, M]` has cardinality at
most `(M - lo)/g + 1`. -/
theorem card_le_of_gapSeparated {S : Finset ℕ} {lo M g : ℕ} (hg : 0 < g)
    (hlo : ∀ x ∈ S, lo ≤ x) (hM : ∀ x ∈ S, x ≤ M)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x < y → x + g ≤ y) :
    S.card ≤ (M - lo) / g + 1 := by
  have hmem : ∀ x ∈ S, (x - lo) / g ∈ Finset.range ((M - lo) / g + 1) := by
    intro x hx
    rw [Finset.mem_range]
    have hxlo := hlo x hx
    have hxM := hM x hx
    have hle : (x - lo) / g ≤ (M - lo) / g := Nat.div_le_div_right (by omega)
    omega
  have hinj : Set.InjOn (fun x => (x - lo) / g) (S : Set ℕ) := by
    intro x hx y hy hxy
    rw [Finset.mem_coe] at hx hy
    have hxy' : (x - lo) / g = (y - lo) / g := hxy
    rcases lt_trichotomy x y with h | h | h
    · exfalso
      have hsep' := hsep x hx y hy h
      have hstep : (x - lo) + g ≤ y - lo := by have := hlo x hx; omega
      have hd : (x - lo) / g + 1 ≤ (y - lo) / g := by
        have h1 : ((x - lo) + g) / g ≤ (y - lo) / g := Nat.div_le_div_right hstep
        rwa [Nat.add_div_right (x - lo) hg] at h1
      rw [hxy'] at hd
      exact absurd hd (by omega)
    · exact h
    · exfalso
      have hsep' := hsep y hy x hx h
      have hstep : (y - lo) + g ≤ x - lo := by have := hlo y hy; omega
      have hd : (y - lo) / g + 1 ≤ (x - lo) / g := by
        have h1 : ((y - lo) + g) / g ≤ (x - lo) / g := Nat.div_le_div_right hstep
        rwa [Nat.add_div_right (y - lo) hg] at h1
      rw [hxy'] at hd
      exact absurd hd (by omega)
  calc S.card ≤ (Finset.range ((M - lo) / g + 1)).card :=
        Finset.card_le_card_of_injOn (fun x => (x - lo) / g) hmem hinj
    _ = (M - lo) / g + 1 := Finset.card_range _

/-! ## Part C — the all-ones obstruction (no absolute constant) -/

/-- For the constant-`val` digit sequence the forward run length is fully
fuel-saturated: it equals the fuel. -/
theorem runLengthFrom_const (val : Nat) :
    ∀ (fuel n : Nat), runLengthFrom (fun _ => val) val fuel n = fuel := by
  intro fuel
  induction fuel with
  | zero => intro n; rfl
  | succ f ih =>
    intro n
    rw [runLengthFrom_succ, ih]
    simp

/-- The all-ones support window `(X, 2X]` has cardinality `X`. -/
theorem allOnes_supportIn (M : Nat) : supportIn (fun _ => 1) M = Finset.Icc 1 M := by
  unfold supportIn
  apply Finset.filter_true_of_mem
  intro n _
  rfl

theorem allOnes_window_card (X : Nat) :
    (supportShell (fun _ => 1) X).card = X := by
  have hset : supportShell (fun _ => 1) X = Finset.Ioc X (2 * X) := by
    rw [supportShell, allOnes_supportIn, allOnes_supportIn]
    ext n
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hset, Nat.card_Ioc]
  omega

/-- **The honest obstruction to an absolute constant.**  For the constant-`1`
digit sequence, *every* window position shares the single run-scale
`a₀ = log₂(2X)`, so the level-set count for `a₀` equals the **entire window
cardinality** `X`.  Since `X` is `2^L`-large while `(log* L)^C` is only
poly-`log log L`, no absolute exponent `C` can bound this collapsed
one-dimensional count. -/
theorem allOnes_window_count_eq_card (X : Nat) :
    ((supportShell (fun _ => 1) X).filter
        (fun n => Nat.log 2 (runLengthFrom (fun _ => 1) 1 (2 * X) n) = Nat.log 2 (2 * X))).card
      = (supportShell (fun _ => 1) X).card := by
  have hfilter : (supportShell (fun _ => 1) X).filter
      (fun n => Nat.log 2 (runLengthFrom (fun _ => 1) 1 (2 * X) n) = Nat.log 2 (2 * X))
        = supportShell (fun _ => 1) X := by
    apply Finset.filter_true_of_mem
    intro n _
    show Nat.log 2 (runLengthFrom (fun _ => 1) 1 (2 * X) n) = Nat.log 2 (2 * X)
    rw [runLengthFrom_const]
  rw [hfilter]

/-! ## Part D — discharging `dirtyWindow` with a concrete (sharp) constant -/

/-- Elementary growth fact `n < 2 ^ n` (version-robust; `nat_lt_two_pow` is
private in `DirtyFibreBoundCore`). -/
private theorem nat_lt_two_pow (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    have hpow : 2 ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
    omega

noncomputable section

/-- The concrete window fibre constant: the size of the stopped support window.
Pins `dirtyCM` to a genuine natural number for each shell. -/
def dirtyCMWindow (ctx : ActualFailureContext) : ℕ :=
  (dirtyShellWindow ctx).card

/-- **`WindowRunScaleCountBound` discharged with a concrete constant.**

Each run-scale level set is a subset of the finite window, of size
`m := dirtyCMWindow ctx = #window`; since `2 ≤ log* L` (`logStarOfShell_ge_two`)
we have `m < 2 ^ m ≤ (log* L) ^ m`, so every level set has at most `(log* L) ^ m`
elements.  No `sorry`/`axiom`/`admit`.

This inhabits the residual field `dirtyWindow` of `Erdos260PhaseCoresV2` (choose
`dirtyCM := dirtyCMWindow`).  The constant grows with the shell, so — exactly as
flagged by `dirtyLeafFibreBound_card` — it is *not* the manuscript's absolute
`C`; the all-ones obstruction (`allOnes_window_count_eq_card`) shows the count
genuinely saturates `#window`, so no absolute `C` is available on this collapsed
model. -/
theorem windowRunScaleCountBound_window_card (ctx : ActualFailureContext) :
    WindowRunScaleCountBound ctx (dirtyCMWindow ctx) := by
  have h2 := logStarOfShell_ge_two ctx
  intro a
  refine le_trans (Finset.card_filter_le _ _) ?_
  show (dirtyShellWindow ctx).card
      ≤ (logStarOfShell (Classical.choose ctx.shell.hXdyadic)) ^ (dirtyShellWindow ctx).card
  exact le_of_lt (lt_of_lt_of_le (nat_lt_two_pow _) (Nat.pow_le_pow_left h2 _))

/-- **The full K.2.5 per-dyadic-pair fibre bound, closed through the window
route.**  Combining the window count bound with the faithful reduction
`dirtyLeafFibreBound_of_window` (off-diagonal scales closed unconditionally,
diagonal scales reduced to the window run-length count) closes
`DirtyLeafFibreBound ctx (dirtyCMWindow ctx)`.  This is precisely the content the
`Erdos260PhaseCoresV2.toPhaseCores` field `dirtyFibre` builds from
`dirtyCM`/`dirtyWindow`, so it confirms the `dirtyWindow` field is discharged. -/
theorem dirtyLeafFibreBound_window (ctx : ActualFailureContext) :
    DirtyLeafFibreBound ctx (dirtyCMWindow ctx) :=
  dirtyLeafFibreBound_of_window ctx (dirtyCMWindow ctx)
    (windowRunScaleCountBound_window_card ctx)

/-- **Machine-checked discharge of the `dirtyWindow` residual.**

Given any `Erdos260PhaseCoresV2` residual surface, its two Dirty fields
`dirtyCM` / `dirtyWindow` are replaceable by the window-card core: this
substitution typechecks *only because* `dirtyCMWindow` and
`windowRunScaleCountBound_window_card` have exactly the field types required
(`dirtyWindow`'s type depends on `dirtyCM`, so the update is dependent).  Hence
the genuine residual `Erdos260PhaseCoresV2.dirtyWindow` is fully dischargeable
from this module (with `dirtyCM := dirtyCMWindow`), modulo the documented
caveat that the constant is ctx-dependent, not the manuscript absolute `C`. -/
def Erdos260PhaseCoresV2.withWindowDirty (h : Erdos260PhaseCoresV2) :
    Erdos260PhaseCoresV2 :=
  { h with
    dirtyCM := dirtyCMWindow
    dirtyWindow := windowRunScaleCountBound_window_card }

/-! ## Part E — the sharp per-clean-run-length window bound (`≤ X/v + 1`)

The genuine "few-runs" content: for a fixed run length `v`, if every window
position attaining it has a *clean* (uncapped) run, those positions are
`v`-separated, hence number at most `X/v + 1`.  This is the honest realization
of the manuscript's "positions of length-`2^a` runs are `≤ L/2^a`".  Summing
over the `2^a` exact lengths comprising a scale `a` reintroduces the `Θ(X)`
count, which is exactly why the absolute `(log* L)^C` fails after the collapse. -/

/-- **Sharp bound for a fixed clean run length.**  If every window position with
forward run length exactly `v ≥ 1` ends its run cleanly (`d (n+v) ≠ 1`), then at
most `X/v + 1` window positions have run length `v`. -/
theorem windowExactRunCount_le_of_clean (ctx : ActualFailureContext) {v : ℕ} (hv : 0 < v)
    (hclean : ∀ n ∈ (dirtyShellWindow ctx).filter
        (fun n => runLengthFrom ctx.shell.d 1 (2 * ctx.shell.X) n = v),
        ctx.shell.d (n + v) ≠ 1) :
    ((dirtyShellWindow ctx).filter
        (fun n => runLengthFrom ctx.shell.d 1 (2 * ctx.shell.X) n = v)).card
      ≤ ctx.shell.X / v + 1 := by
  have hcard : ((dirtyShellWindow ctx).filter
      (fun n => runLengthFrom ctx.shell.d 1 (2 * ctx.shell.X) n = v)).card
      ≤ (2 * ctx.shell.X - (ctx.shell.X + 1)) / v + 1 := by
    apply card_le_of_gapSeparated (lo := ctx.shell.X + 1) (M := 2 * ctx.shell.X) hv
    · intro x hx
      have hx1 : x ∈ dirtyShellWindow ctx := (Finset.mem_filter.mp hx).1
      have hx2 := (mem_supportShell ctx.shell.d ctx.shell.X x).mp hx1
      omega
    · intro x hx
      have hx1 : x ∈ dirtyShellWindow ctx := (Finset.mem_filter.mp hx).1
      have hx2 := (mem_supportShell ctx.shell.d ctx.shell.X x).mp hx1
      omega
    · intro x hx y hy hxy
      have hxv := (Finset.mem_filter.mp hx).2
      have hyv := (Finset.mem_filter.mp hy).2
      exact runLengthFrom_clean_sep ctx.shell.d 1 hxv (hclean x hx) hxy hyv
  refine le_trans hcard ?_
  have hdiv : (2 * ctx.shell.X - (ctx.shell.X + 1)) / v ≤ ctx.shell.X / v :=
    Nat.div_le_div_right (by omega)
  omega

end

/-! ## Axiom audit -/

#print axioms windowRunScaleCountBound_window_card
#print axioms dirtyLeafFibreBound_window
#print axioms Erdos260PhaseCoresV2.withWindowDirty
#print axioms windowExactRunCount_le_of_clean
#print axioms allOnes_window_count_eq_card
#print axioms card_le_of_gapSeparated

end Erdos260
