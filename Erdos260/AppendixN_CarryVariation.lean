import Mathlib
import Erdos260.AppendixN_Variation
import Erdos260.CarryDataFactory
import Erdos260.HitSequence

/-!
# Grounding the rolling-window variation in the carry recurrence

`Erdos260.AppendixN_Variation` proves the rolling-window variation bound
`V_s ≤ 2 M·|𝒦|` (eq N.13) for an abstract gap function with a *windowed* bound
`g_k ≤ M` (`windowVariation_of_windowBound`).  This file **discharges** that
windowed bound for the actual **hit-gap sequence** using the dyadic-scale gap
bound `HitSequence.hitGap_le_of_shell_window`
(`hitGap a k ≤ L + B + 1` on the shell window `k < firstIndexAbove X + r`).

Hence the manuscript's N.13 rolling-window total variation is realized
**for the real carry-recurrence gap sequence** with no abstract gap hypothesis:
the only inputs are the failing-shell carry data already proved in
`HitSequence`.  This is a genuine grounding (not a conditional reduction): the
gap bound is the real `hitGap_le_of_shell_window`, and the variation assembly is
the faithful `windowVariation_of_windowBound`.

No `sorry`, `axiom`, or `admit`.
-/

namespace Erdos260

open MeasureTheory Finset

/-- **Rolling-window variation for the real hit-gap sequence (eq N.13, grounded).**

For the order-`s` window sums of the actual hit-gap sequence `hitGap a`, the
total variation over an edge set `K` contained in the shell window
(`k + 1 < firstIndexAbove X + r` for every `k ∈ K`) is bounded by
`2 (L + B + 1) |𝒦|`.

The dyadic-scale gap bound `hitGap a k ≤ L + B + 1`
(`HitSequence.hitGap_le_of_shell_window`) is discharged on every index the
order-`s` windows touch (`k - s` and `k + 1`); the variation assembly is the
faithful `AppendixN.windowVariation_of_windowBound`.  No abstract gap hypothesis
remains — only the real failing-shell carry data. -/
theorem windowVariation_hitGap
    {Q B X L : Nat} {P : Int} {d a : Nat → Nat}
    (hd : BinaryDigits d) (hseq : HitSequence d a)
    (hQ : 0 < Q)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ))
    (hX_eq : X = 2 ^ L) (hX_pos : 1 ≤ X)
    (hB : Q * 4 ≤ 2 ^ B)
    {r : Nat} (hKr : r + 1 ≤ (supportShell d X).card)
    (s : ℕ) (K : Finset ℕ)
    (hK : ∀ k ∈ K, s ≤ k)
    (hKwin : ∀ k ∈ K, k + 1 < hseq.firstIndexAbove X + r) :
    AppendixN.Vs K (AppendixN.windowSum (fun n => (hitGap a n : ℝ)) s)
      ≤ 2 * ((L + B + 1 : ℕ) : ℝ) * (K.card : ℝ) := by
  refine AppendixN.windowVariation_of_windowBound
    (fun n => (hitGap a n : ℝ)) s K ((L + B + 1 : ℕ) : ℝ)
    (fun n => Nat.cast_nonneg _) hK ?_ ?_
  · -- `g (k - s) = hitGap a (k - s) ≤ L + B + 1` on the shell window
    intro k hk
    have hlt : k - s < hseq.firstIndexAbove X + r := by
      have := hKwin k hk; omega
    have hbound := hseq.hitGap_le_of_shell_window hd hQ heta hX_eq hX_pos hB hKr hlt
    show (hitGap a (k - s) : ℝ) ≤ ((L + B + 1 : ℕ) : ℝ)
    exact_mod_cast hbound
  · -- `g (k + 1) = hitGap a (k + 1) ≤ L + B + 1` on the shell window
    intro k hk
    have hbound :=
      hseq.hitGap_le_of_shell_window hd hQ heta hX_eq hX_pos hB hKr (hKwin k hk)
    show (hitGap a (k + 1) : ℝ) ≤ ((L + B + 1 : ℕ) : ℝ)
    exact_mod_cast hbound

/-- **Window-drop estimate for the real hit-gap sequence (eq N.18 / 2.3v, grounded).**

Composing the grounded variation bound `windowVariation_hitGap` with the abstract
window-drop estimate `AppendixN.varDrop_le` gives an **explicit** drop bound for
the actual hit-gap sequence:
`VarDrop ≤ C_Q · Y · 2 (L + B + 1) |𝒦|`.

Both the coarea step (eq N.15) and the gap bound (eq N.13) are now faithful for
the real sequence; the only remaining conditional input is the fibre-measure
first inequality `h1` (`VarDrop ≤ C_Q Y ∫_A N_{T+Y}`, the N.2.2 per-fibre
integration / multiplicity step). -/
theorem varDrop_le_hitGap
    {Q B X L : Nat} {P : Int} {d a : Nat → Nat}
    (hd : BinaryDigits d) (hseq : HitSequence d a)
    (hQ : 0 < Q)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ))
    (hX_eq : X = 2 ^ L) (hX_pos : 1 ≤ X)
    (hB : Q * 4 ≤ 2 ^ B)
    {r : Nat} (hKr : r + 1 ≤ (supportShell d X).card)
    (s : ℕ) (K : Finset ℕ)
    (hK : ∀ k ∈ K, s ≤ k)
    (hKwin : ∀ k ∈ K, k + 1 < hseq.firstIndexAbove X + r)
    (VarDrop CQ Y : ℝ) (A : Set ℝ)
    (hCQY : 0 ≤ CQ * Y)
    (h1 : VarDrop ≤ CQ * Y *
      ∫ T in A, AppendixN.crossingCountReal (T + Y)
        (AppendixN.windowSum (fun n => (hitGap a n : ℝ)) s) K ∂MeasureTheory.volume) :
    VarDrop ≤ CQ * Y * (2 * ((L + B + 1 : ℕ) : ℝ) * (K.card : ℝ)) := by
  have hVs :
      AppendixN.Vs K (AppendixN.windowSum (fun n => (hitGap a n : ℝ)) s)
        ≤ 2 * ((L + B + 1 : ℕ) : ℝ) * (K.card : ℝ) :=
    windowVariation_hitGap hd hseq hQ heta hX_eq hX_pos hB hKr s K hK hKwin
  have hdrop :
      VarDrop ≤ CQ * Y *
        AppendixN.Vs K (AppendixN.windowSum (fun n => (hitGap a n : ℝ)) s) :=
    AppendixN.varDrop_le VarDrop CQ Y
      (AppendixN.windowSum (fun n => (hitGap a n : ℝ)) s) K A hCQY h1
  exact hdrop.trans (mul_le_mul_of_nonneg_left hVs hCQY)

/--
**Scaled N.13 bound for the real hit-gap sequence.**

This is the multiplier form used by N.2.2 and the later phase-mass bridge:
`C · Y · V_s(hitGap) ≤ C · Y · 2(L+B+1)|𝒦|`.
-/
theorem scaled_windowTerm_le_hitGap
    {Q B X L : Nat} {P : Int} {d a : Nat → Nat}
    (hd : BinaryDigits d) (hseq : HitSequence d a)
    (hQ : 0 < Q)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ))
    (hX_eq : X = 2 ^ L) (hX_pos : 1 ≤ X)
    (hB : Q * 4 ≤ 2 ^ B)
    {r : Nat} (hKr : r + 1 ≤ (supportShell d X).card)
    (s : ℕ) (K : Finset ℕ)
    (hK : ∀ k ∈ K, s ≤ k)
    (hKwin : ∀ k ∈ K, k + 1 < hseq.firstIndexAbove X + r)
    (C Y : ℝ) (hCY : 0 ≤ C * Y) :
    C * Y * AppendixN.Vs K (AppendixN.windowSum (fun n => (hitGap a n : ℝ)) s)
      ≤ C * Y * (2 * ((L + B + 1 : ℕ) : ℝ) * (K.card : ℝ)) :=
  mul_le_mul_of_nonneg_left
    (windowVariation_hitGap hd hseq hQ heta hX_eq hX_pos hB hKr s K hK hKwin)
    hCY

/--
**Rolling-window variation from carry-packaged hit-gap data.**

This is `windowVariation_hitGap` with the binary word, hit sequence, shell size,
and recurrence length read from `shell` and `carryData`.
-/
theorem windowVariation_carryHitGap
    {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr)
    {B : Nat} {P : Int}
    (hP :
      realWeightedValue (natBinaryAsReal shell.d) =
        (P : ℝ) / (shell.Q : ℝ))
    (hX_eq : shell.X = 2 ^ carryData.L)
    (hX_pos : 1 ≤ shell.X)
    (hB : shell.Q * 4 ≤ 2 ^ B)
    (hKr : carryData.r + 1 ≤ (supportShell shell.d shell.X).card)
    (s : ℕ) (K : Finset ℕ)
    (hK : ∀ k ∈ K, s ≤ k)
    (hKwin : ∀ k ∈ K,
      k + 1 < carryData.carry.hits.firstIndexAbove shell.X + carryData.r) :
    AppendixN.Vs K
        (AppendixN.windowSum (fun n => (hitGap carryData.a n : ℝ)) s)
      ≤ 2 * ((carryData.L + B + 1 : ℕ) : ℝ) * (K.card : ℝ) :=
  windowVariation_hitGap shell.hd carryData.carry.hits shell.hQ hP hX_eq
    hX_pos hB hKr s K hK hKwin

/--
**Scaled N.13 bound from carry-packaged hit-gap data.**
-/
theorem scaled_windowTerm_le_carryHitGap
    {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr)
    {B : Nat} {P : Int}
    (hP :
      realWeightedValue (natBinaryAsReal shell.d) =
        (P : ℝ) / (shell.Q : ℝ))
    (hX_eq : shell.X = 2 ^ carryData.L)
    (hX_pos : 1 ≤ shell.X)
    (hB : shell.Q * 4 ≤ 2 ^ B)
    (hKr : carryData.r + 1 ≤ (supportShell shell.d shell.X).card)
    (s : ℕ) (K : Finset ℕ)
    (hK : ∀ k ∈ K, s ≤ k)
    (hKwin : ∀ k ∈ K,
      k + 1 < carryData.carry.hits.firstIndexAbove shell.X + carryData.r)
    (C Y : ℝ) (hCY : 0 ≤ C * Y) :
    C * Y *
        AppendixN.Vs K
          (AppendixN.windowSum (fun n => (hitGap carryData.a n : ℝ)) s)
      ≤ C * Y *
          (2 * ((carryData.L + B + 1 : ℕ) : ℝ) * (K.card : ℝ)) :=
  mul_le_mul_of_nonneg_left
    (windowVariation_carryHitGap carryData hP hX_eq hX_pos hB hKr s K hK hKwin)
    hCY

/--
**Scaled drop-density window drop from carry-packaged hit-gap data.**
-/
theorem varDrop_le_from_scaled_dropDensity_bound_carryHitGap
    {shell : FailingDyadicShell} {cPr : ℝ}
    (carryData : CarryDataFromFailure shell cPr)
    {B : Nat} {P : Int}
    (hP :
      realWeightedValue (natBinaryAsReal shell.d) =
        (P : ℝ) / (shell.Q : ℝ))
    (hX_eq : shell.X = 2 ^ carryData.L)
    (hX_pos : 1 ≤ shell.X)
    (hB : shell.Q * 4 ≤ 2 ^ B)
    (hKr : carryData.r + 1 ≤ (supportShell shell.d shell.X).card)
    (s : ℕ) (K : Finset ℕ)
    (hK : ∀ k ∈ K, s ≤ k)
    (hKwin : ∀ k ∈ K,
      k + 1 < carryData.carry.hits.firstIndexAbove shell.X + carryData.r)
    (VarDrop Cmul Cfiber Y : ℝ) (dropDensity : ℝ → ℝ) (A : Set ℝ)
    (hCmulY : 0 ≤ Cmul * Y)
    (hCfiber : 0 ≤ Cfiber)
    (hA : MeasurableSet A)
    (hdrop_int : IntegrableOn dropDensity A volume)
    (hvar :
      VarDrop ≤ Cmul * Y * ∫ T in A, dropDensity T ∂volume)
    (hpoint :
      ∀ T ∈ A,
        dropDensity T ≤
          Cfiber *
            AppendixN.crossingCountReal (T + Y)
              (AppendixN.windowSum (fun n => (hitGap carryData.a n : ℝ)) s) K) :
    VarDrop ≤ (Cmul * Cfiber) * Y *
      (2 * ((carryData.L + B + 1 : ℕ) : ℝ) * (K.card : ℝ)) := by
  have hdrop :
      VarDrop ≤ (Cmul * Cfiber) * Y *
        AppendixN.Vs K
          (AppendixN.windowSum (fun n => (hitGap carryData.a n : ℝ)) s) :=
    AppendixN.varDrop_le_from_scaled_dropDensity_bound VarDrop Cmul Cfiber Y
      dropDensity (AppendixN.windowSum (fun n => (hitGap carryData.a n : ℝ)) s)
      K A hCmulY hCfiber hA hdrop_int hvar hpoint
  have htotal : 0 ≤ (Cmul * Cfiber) * Y := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using mul_nonneg hCfiber hCmulY
  exact hdrop.trans
    (scaled_windowTerm_le_carryHitGap carryData hP hX_eq hX_pos hB hKr s K hK
      hKwin (Cmul * Cfiber) Y htotal)

/--
**Scaled drop-density window drop for the real hit-gap sequence.**

This composes the scaled first inequality, coarea, and the grounded hit-gap
variation estimate.  It is the hit-gap-specialized version of
`AppendixN.varDrop_le_from_scaled_dropDensity_bound_explicitWindow`.
-/
theorem varDrop_le_from_scaled_dropDensity_bound_hitGap
    {Q B X L : Nat} {P : Int} {d a : Nat → Nat}
    (hd : BinaryDigits d) (hseq : HitSequence d a)
    (hQ : 0 < Q)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ))
    (hX_eq : X = 2 ^ L) (hX_pos : 1 ≤ X)
    (hB : Q * 4 ≤ 2 ^ B)
    {r : Nat} (hKr : r + 1 ≤ (supportShell d X).card)
    (s : ℕ) (K : Finset ℕ)
    (hK : ∀ k ∈ K, s ≤ k)
    (hKwin : ∀ k ∈ K, k + 1 < hseq.firstIndexAbove X + r)
    (VarDrop Cmul Cfiber Y : ℝ) (dropDensity : ℝ → ℝ) (A : Set ℝ)
    (hCmulY : 0 ≤ Cmul * Y)
    (hCfiber : 0 ≤ Cfiber)
    (hA : MeasurableSet A)
    (hdrop_int : IntegrableOn dropDensity A volume)
    (hvar :
      VarDrop ≤ Cmul * Y * ∫ T in A, dropDensity T ∂volume)
    (hpoint :
      ∀ T ∈ A,
        dropDensity T ≤
          Cfiber *
            AppendixN.crossingCountReal (T + Y)
              (AppendixN.windowSum (fun n => (hitGap a n : ℝ)) s) K) :
    VarDrop ≤ (Cmul * Cfiber) * Y *
      (2 * ((L + B + 1 : ℕ) : ℝ) * (K.card : ℝ)) := by
  have hdrop :
      VarDrop ≤ (Cmul * Cfiber) * Y *
        AppendixN.Vs K (AppendixN.windowSum (fun n => (hitGap a n : ℝ)) s) :=
    AppendixN.varDrop_le_from_scaled_dropDensity_bound VarDrop Cmul Cfiber Y
      dropDensity (AppendixN.windowSum (fun n => (hitGap a n : ℝ)) s) K A
      hCmulY hCfiber hA hdrop_int hvar hpoint
  have htotal : 0 ≤ (Cmul * Cfiber) * Y := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using mul_nonneg hCfiber hCmulY
  exact hdrop.trans
    (scaled_windowTerm_le_hitGap hd hseq hQ heta hX_eq hX_pos hB hKr s K hK
      hKwin (Cmul * Cfiber) Y htotal)

end Erdos260
