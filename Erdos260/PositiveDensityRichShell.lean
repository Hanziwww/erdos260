import Mathlib
import Erdos260.GlobalCarryShellAssembly
import Erdos260.GlobalClosureAssembly

/-!
# Positive-density rich dyadic shells (manuscript Theorem A.1 / `positive-dyadic-density`)

This module proves the *rich shell* fact that the carry-window / pressure-floor
reduction isolated as its remaining honest input.

Recall the manuscript Theorem `positive-dyadic-density` (A.1): under the failure
hypothesis (the weighted binary series `∑ n dₙ 2⁻ⁿ` is *rational* and the support is
infinite), every sufficiently large dyadic shell `(X, 2X]` carries a *positive density*
of support hits, `A_S(2X) − A_S(X) ≥ c_Q X`.

The pressure-floor consumer (`ShellWindowInputs.hKr` / the `hKr` argument of
`carryDataPinned` in `PressureFloorConstruction.lean`) does not need the full
exponential density bound; it needs the *linear* richness

```
L + 1 ≤ |supportShell d X|     (X = 2^L).
```

## What is genuine here (no `sorry`, no new axioms)

The analytic heart of A.1 is already formalized in the carry layer: rationality of the
weighted series forces the gap between consecutive support hits at a dyadic scale to be
*logarithmic*.  Concretely `Erdos260.hitGap_le_of_left_dyadic_scale`
(in `GlobalCarryShellAssembly.lean`) shows that any adjacent hit gap whose **left**
endpoint is `≤ 2X` is at most `L + B + 1` (`B = carryB Q`), via the integer-carry growth
inequality `nat_pow_two_le_of_zero_gap`.  This is the §I.1 carry-recurrence content; it
crucially bounds the gap from the *left* endpoint, which is exactly what removes the
circularity in counting hits inside `(X, 2X]`.

Feeding this logarithmic gap bound into the combinator
`HitSequence.supportShell_card_ge_of_previous_gap_bound` with window length `N = L + 1`
yields `L + 1 ≤ |supportShell d X|`, provided the window fits inside the shell, i.e.
`(L+1)(L+B+1) ≤ 2^L`.  That last inequality is the elementary polynomial-vs-exponential
bound `manuscript_carry_growth` (already proved).

The existing `ManuscriptCarrySupportSupplyData` only exposed the *manuscript-order* richness
`⌊κL⌋ + 1 ≤ |supportShell|`; here we push the same machinery to the full `L + 1` that
`ShellWindowInputs` demands.

## Honest status

`richShell_of_startThreshold_le` is **CLOSED**: from the genuine manuscript "sufficiently
large dyadic `X`" hypothesis `appendixNChainCompressionStartThreshold ≤ X` (the very
threshold the global pipeline pins `startThreshold` to), it derives `L + 1 ≤ |supportShell|`
with no further assumptions.  That threshold simultaneously supplies the carry scale
(`carryB Q + 25 ≤ L`) and a support hit at or below `X` (`1 ≤ supportCount d X`).

`richShell_of_failure_large` uses the slightly weaker gate `aboveCarryThreshold`
(`carryThreshold (carryB Q + 19) ≤ X`).  That gate alone gives the carry scale but *not*
the "`X` is past the first hit" condition — indeed a nonterminating shell whose first hit
sits beyond `X` has `|supportShell d X| = 0`, so the richness genuinely cannot hold without
it.  We therefore carry the precise, non-vacuous side input
`hSupportBefore : 1 ≤ supportCount d X`, which is exactly the `ShellWindowInputs`
companion field `h_supportCount_pos`.

No `sorry` / `admit` / `native_decide` / new `axiom`; the module is axiom-clean
(`propext`, `Classical.choice`, `Quot.sound` only).
-/

namespace Erdos260

noncomputable section

open ManuscriptCarrySupportSupplyData

/-- Elementary window-fit bound: the linear shell window `(L+1)` gaps of logarithmic
length `L + B + 1` fit inside a dyadic shell `2^L`, i.e. `(L+1)(L+B+1) ≤ 2^L`, once
`B + 25 ≤ L`.  This is the polynomial-vs-exponential bound `manuscript_carry_growth`. -/
theorem windowLen_succ_le {L B : Nat} (hL : B + 25 ≤ L) :
    (L + 1) * (L + B + 1) ≤ 2 ^ L := by
  have hg : 1024 * (L + 1) ^ 3 + 8 * (L + 1) ^ 2 * B ≤ 2 ^ L :=
    manuscript_carry_growth L B hL
  have hbase : (1 : Nat) ≤ L + 1 := Nat.le_add_left 1 L
  have hpow23 : (L + 1) ^ 2 ≤ (L + 1) ^ 3 :=
    Nat.pow_le_pow_right hbase (by norm_num)
  have hpow12 : (L + 1) ^ 1 ≤ (L + 1) ^ 2 :=
    Nat.pow_le_pow_right hbase (by norm_num)
  have hpow1 : (L + 1) ^ 1 = L + 1 := pow_one _
  have h2 : (L + 1) ^ 2 ≤ 1024 * (L + 1) ^ 3 := by omega
  have h3 : (L + 1) * B ≤ 8 * (L + 1) ^ 2 * B := by
    have hle : L + 1 ≤ 8 * (L + 1) ^ 2 := by omega
    exact Nat.mul_le_mul_right B hle
  calc (L + 1) * (L + B + 1)
      = (L + 1) ^ 2 + (L + 1) * B := by ring
    _ ≤ 1024 * (L + 1) ^ 3 + 8 * (L + 1) ^ 2 * B := Nat.add_le_add h2 h3
    _ ≤ 2 ^ L := hg

/-- **Finite rational-gap window bound (full linear window).**

For a failing dyadic shell with a hit at or below `X` (`hSupportBefore`) and the carry
scale `carryB Q + 25 ≤ L` (`hCarryLarge`), if a window of `N` adjacent gaps fits inside the
shell (`N · (L+B+1) ≤ X`), then each of those `N` gaps after the shell's left endpoint is
at most `L + B + 1`.

This is the `N`-parametric version of `proofV4FiniteGapBound_of_carryLarge`
(which fixed `N = ⌊κL⌋ + 1`); the proof is the same strong induction over the window,
bounding each hit by the cumulative logarithmic gaps and invoking the left-endpoint carry
gap bound `hitGap_le_of_left_dyadic_scale`. -/
theorem rationalGap_window_bound {shell : FailingDyadicShell}
    (hSupportBefore : 1 ≤ supportCount shell.d shell.X)
    (hCarryLarge : carryB shell.Q + 25 ≤ Classical.choose shell.hXdyadic)
    {N : Nat}
    (hLarge : N * (Classical.choose shell.hXdyadic + carryB shell.Q + 1) ≤ shell.X)
    {a : Nat → Nat} (hseq : HitSequence shell.d a) (k : Nat)
    (hk_lo : hseq.firstIndexAbove shell.X - 1 ≤ k)
    (hk_hi : k < hseq.firstIndexAbove shell.X + N) :
    hitGap a k ≤ Classical.choose shell.hXdyadic + carryB shell.Q + 1 := by
  set M := Classical.choose shell.hXdyadic + carryB shell.Q + 1 with hM_eq
  set i := hseq.firstIndexAbove shell.X with hi_eq
  have hi_pos : 1 ≤ i := by
    rw [hi_eq]
    exact hseq.firstIndexAbove_pos_of_supportCount_pos hSupportBefore
  have hap_le : a (i - 1) ≤ shell.X := by
    apply hseq.lt_firstIndexAbove shell.X
    omega
  have hmain :
      ∀ t : Nat, ∀ j : Nat,
        j - (i - 1) = t → i - 1 ≤ j → j < i + N → hitGap a j ≤ M := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro j hjt hij hj_hi
      have hprev : ∀ g : Nat, i - 1 ≤ g → g < j → hitGap a g ≤ M := by
        intro g hpg hgj
        exact ih (g - (i - 1)) (by omega) g rfl hpg (by omega)
      have hcum : a j ≤ a (i - 1) + (j - (i - 1)) * M := by
        have hraw :=
          hseq.a_add_le_of_hitGap_le (i := i - 1) (r := j - (i - 1)) (M := M)
            (fun g hg_lo hg_hi => hprev g hg_lo (by omega))
        rwa [Nat.add_sub_of_le hij] at hraw
      have hmul : (j - (i - 1)) * M ≤ N * M := Nat.mul_le_mul_right M (by omega)
      have hleft : a j ≤ 2 * shell.X := by omega
      rw [hM_eq]
      exact hitGap_le_of_left_dyadic_scale (shell := shell) hseq hleft hCarryLarge
  exact hmain (k - (i - 1)) k rfl (by omega) hk_hi

/-- **Shell richness from a finite gap window.**

If a window of `N` short adjacent gaps fits inside the dyadic shell
(`N · (L+B+1) ≤ X`), then the dyadic shell `(X, 2X]` carries at least `N` support hits.
This packages `rationalGap_window_bound` through the supply combinator
`HitSequence.supportShell_card_ge_of_previous_gap_bound`. -/
theorem rationalShell_card_ge {shell : FailingDyadicShell}
    (hSupportBefore : 1 ≤ supportCount shell.d shell.X)
    (hCarryLarge : carryB shell.Q + 25 ≤ Classical.choose shell.hXdyadic)
    {N : Nat}
    (hLarge : N * (Classical.choose shell.hXdyadic + carryB shell.Q + 1) ≤ shell.X) :
    N ≤ (supportShell shell.d shell.X).card := by
  obtain ⟨a, hseq⟩ := exists_hitSequence_of_nonterminating shell.hd shell.hnonterm
  refine hseq.supportShell_card_ge_of_previous_gap_bound
    (X := shell.X) (i := hseq.firstIndexAbove shell.X)
    (N := N) (M := Classical.choose shell.hXdyadic + carryB shell.Q + 1)
    rfl
    (hseq.firstIndexAbove_pos_of_supportCount_pos hSupportBefore)
    (fun k hk_lo hk_hi =>
      rationalGap_window_bound hSupportBefore hCarryLarge hLarge hseq k hk_lo hk_hi)
    hLarge

/-- **Linear shell richness at the dyadic exponent (core form).**

From the genuine carry/rationality content this derives the full linear richness
`L + 1 ≤ |supportShell d X|` (with `L = log₂ X`), strictly stronger than the
manuscript-order `⌊κL⌋ + 1` recorded in `ManuscriptCarrySupportSupplyData`.

The two inputs are the non-vacuous side conditions the pressure-floor consumer already
carries: a support hit at or below `X`, and the dyadic carry scale `carryB Q + 25 ≤ L`. -/
theorem richShell_card_choose {shell : FailingDyadicShell}
    (hSupportBefore : 1 ≤ supportCount shell.d shell.X)
    (hCarryLarge : carryB shell.Q + 25 ≤ Classical.choose shell.hXdyadic) :
    Classical.choose shell.hXdyadic + 1 ≤ (supportShell shell.d shell.X).card := by
  have hLarge :
      (Classical.choose shell.hXdyadic + 1) *
        (Classical.choose shell.hXdyadic + carryB shell.Q + 1) ≤ shell.X :=
    le_of_le_of_eq (windowLen_succ_le hCarryLarge)
      (Classical.choose_spec shell.hXdyadic).symm
  exact rationalShell_card_ge hSupportBefore hCarryLarge hLarge

/-- Internal bridge: the dyadic exponent `Classical.choose shell.hXdyadic` chosen for
`shell.X` equals any `L` with `shell.X = 2^L`. -/
theorem choose_hXdyadic_eq {shell : FailingDyadicShell} {L : Nat}
    (hX_eq : shell.X = 2 ^ L) : Classical.choose shell.hXdyadic = L := by
  have hspec : shell.X = 2 ^ Classical.choose shell.hXdyadic :=
    Classical.choose_spec shell.hXdyadic
  have hpow : (2 : Nat) ^ Classical.choose shell.hXdyadic = 2 ^ L := by
    rw [← hspec, hX_eq]
  exact Nat.pow_right_injective (by norm_num) hpow

/-- **Rich shell from the `aboveCarryThreshold` gate (manuscript A.1 consumable form).**

For a failing dyadic shell `shell.X = 2^L` that is `aboveCarryThreshold` (the manuscript
"sufficiently large dyadic `X`" scale) and has a support hit at or below `X`
(`hSupportBefore`, i.e. the `ShellWindowInputs.h_supportCount_pos` companion), the shell is
rich: `L + 1 ≤ |supportShell d X|`.

This is exactly the `hKr` argument of `carryDataPinned` / the `ShellWindowInputs.hKr`
field, derived (not assumed) from the rationality-driven carry gap bound. -/
theorem richShell_of_failure_large
    (shell : FailingDyadicShell) {L : Nat}
    (hX_eq : shell.X = 2 ^ L)
    (hSupportBefore : 1 ≤ supportCount shell.d shell.X)
    (hlarge : shell.aboveCarryThreshold) :
    L + 1 ≤ (supportShell shell.d shell.X).card := by
  have hChoose : Classical.choose shell.hXdyadic = L := choose_hXdyadic_eq hX_eq
  have hlarge' : carryThreshold (carryB shell.Q + 19) ≤ shell.X := hlarge
  have hCarryLarge : carryB shell.Q + 25 ≤ Classical.choose shell.hXdyadic :=
    carryLarge_of_carryThreshold_le (Classical.choose_spec shell.hXdyadic) hlarge'
  have h := richShell_card_choose hSupportBefore hCarryLarge
  rwa [hChoose] at h

/-- **Rich shell from the manuscript start threshold — fully CLOSED.**

For a failing dyadic shell `shell.X = 2^L` beyond the combined
`appendixNChainCompressionStartThreshold` (the genuine manuscript "sufficiently large
dyadic `X`", which the global pipeline pins `startThreshold` to), the shell is rich:
`L + 1 ≤ |supportShell d X|`.

The combined threshold simultaneously discharges both side conditions of
`richShell_of_failure_large`: the carry scale `carryB Q + 25 ≤ L` and the support hit
`1 ≤ supportCount d X`.  Hence this statement has **no** residual hypothesis beyond
"sufficiently large", and is the honest closed form of the rich-shell input. -/
theorem richShell_of_startThreshold_le
    (shell : FailingDyadicShell) {L : Nat}
    (hX_eq : shell.X = 2 ^ L)
    (hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd shell.hnonterm
        ≤ shell.X) :
    L + 1 ≤ (supportShell shell.d shell.X).card := by
  have hChoose : Classical.choose shell.hXdyadic = L := choose_hXdyadic_eq hX_eq
  have hSupportBefore : 1 ≤ supportCount shell.d shell.X :=
    supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge
  have hCarryLarge : carryB shell.Q + 25 ≤ Classical.choose shell.hXdyadic :=
    carryLarge_of_appendixNChainCompressionStartThreshold_le hXge
  have h := richShell_card_choose hSupportBefore hCarryLarge
  rwa [hChoose] at h

end

end Erdos260
