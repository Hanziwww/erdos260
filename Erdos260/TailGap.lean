import Mathlib
import Erdos260.HitSequence

/-!
# Tail support gaps for the DeepMind-indexed sequence

This file packages the first target-side bridge: a superlinear strictly
increasing integer exponent sequence has a positive natural tail whose support
is enumerated by `tailDigit`, and the existing hit-gap estimates apply to that
tail.
-/

namespace Erdos260

noncomputable section

theorem strictMono_nat_id_le {a : Nat -> Nat} (ha : StrictMono a) :
    ∀ k : Nat, k <= a k := by
  intro k
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
      have hsucc : a k + 1 <= a (k + 1) := Nat.succ_le_of_lt (ha (Nat.lt_succ_self k))
      omega

theorem HitSequence.nonterminating {d a : Nat -> Nat} (hseq : HitSequence d a) :
    Nonterminating d := by
  intro N
  exact ⟨a N, strictMono_nat_id_le hseq.strict N, hseq.hit N⟩

theorem exists_tailDigit_hitSequence_of_ratio_tendsto_atTop {a : Nat -> Int}
    (ha : StrictMono a)
    (hratio : Filter.Tendsto (fun n : Nat => (a n : ℝ) / (n : ℝ)) Filter.atTop Filter.atTop) :
    ∃ N : Nat,
      (∀ n : Nat, N <= n -> 0 < a n) ∧
        HitSequence (tailDigit a N) (fun k : Nat => (a (k + N)).toNat) := by
  rcases exists_eventual_pos_of_ratio_tendsto_atTop hratio with ⟨N, hpos⟩
  have hstrict := strictMono_toNat_tail_of_eventually_pos ha hpos
  exact ⟨N, hpos, tailDigit_hitSequence hstrict⟩

theorem tailDigit_nonterminating_of_eventually_pos {a : Nat -> Int} {N : Nat}
    (ha : StrictMono a) (hpos : ∀ n : Nat, N <= n -> 0 < a n) :
    Nonterminating (tailDigit a N) := by
  have hstrict := strictMono_toNat_tail_of_eventually_pos ha hpos
  exact (tailDigit_hitSequence hstrict).nonterminating

theorem tailDigit_hitGap_le_dyadic_scale {a : Nat -> Int} {N Q C B X L k : Nat} {P : Int}
    (ha : StrictMono a) (hpos : ∀ n : Nat, N <= n -> 0 < a n)
    (hQ : 0 < Q)
    (heta : realWeightedValue (natBinaryAsReal (tailDigit a N)) = (P : ℝ) / (Q : ℝ))
    (hX : X = 2 ^ L)
    (hscale : (a (k + 1 + N)).toNat + 1 <= C * X)
    (hconst : Q * C <= 2 ^ B) :
    hitGap (fun j : Nat => (a (j + N)).toNat) k <= L + B + 1 := by
  have hstrict := strictMono_toNat_tail_of_eventually_pos ha hpos
  have hseq := tailDigit_hitSequence hstrict
  exact hseq.hitGap_le_dyadic_scale (tailDigit_binary a N) k hQ heta hX hscale hconst

theorem tailDigit_hitGap_le_of_dyadic_scale {a : Nat -> Int} {N Q C B X k : Nat} {P : Int}
    (ha : StrictMono a) (hpos : ∀ n : Nat, N <= n -> 0 < a n)
    (hQ : 0 < Q)
    (heta : realWeightedValue (natBinaryAsReal (tailDigit a N)) = (P : ℝ) / (Q : ℝ))
    (hX : Dyadic X)
    (hscale : (a (k + 1 + N)).toNat + 1 <= C * X)
    (hconst : Q * C <= 2 ^ B) :
    ∃ L : Nat, X = 2 ^ L ∧ hitGap (fun j : Nat => (a (j + N)).toNat) k <= L + B + 1 := by
  rcases hX with ⟨L, hL⟩
  exact ⟨L, hL, tailDigit_hitGap_le_dyadic_scale ha hpos hQ heta hL hscale hconst⟩

theorem tailDigit_supportCount_le_index_of_lt {a : Nat -> Int} {N X K : Nat}
    (ha : StrictMono a) (hpos : ∀ n : Nat, N <= n -> 0 < a n)
    (hbound : X < (a (K + N)).toNat) :
    supportCount (tailDigit a N) X <= K := by
  have hstrict := strictMono_toNat_tail_of_eventually_pos ha hpos
  have hseq := tailDigit_hitSequence hstrict
  exact hseq.supportCount_le_index_of_lt hbound

theorem tailDigit_supportCount_ge_succ_of_le {a : Nat -> Int} {N X K : Nat}
    (ha : StrictMono a) (hpos : ∀ n : Nat, N <= n -> 0 < a n)
    (hbound : (a (K + N)).toNat <= X) :
    K + 1 <= supportCount (tailDigit a N) X := by
  have hstrict := strictMono_toNat_tail_of_eventually_pos ha hpos
  have hseq := tailDigit_hitSequence hstrict
  exact hseq.supportCount_ge_succ_of_le
    (hpos := fun k hk => by
      have hkN : N <= k + N := by omega
      have hkpos : 0 < a (k + N) := hpos (k + N) hkN
      have hnatInt : (0 : Int) < ((a (k + N)).toNat : Nat) := by
        rw [Int.toNat_of_nonneg hkpos.le]
        exact hkpos
      exact_mod_cast hnatInt)
    hbound

theorem tailDigit_supportShell_card_le_index_of_lt {a : Nat -> Int} {N X K : Nat}
    (ha : StrictMono a) (hpos : ∀ n : Nat, N <= n -> 0 < a n)
    (hbound : 2 * X < (a (K + N)).toNat) :
    (supportShell (tailDigit a N) X).card <= K := by
  have hshell :=
    supportShell_card_le_supportCount_two_mul (tailDigit a N) X
  have hcount :=
    tailDigit_supportCount_le_index_of_lt ha hpos (X := 2 * X) (K := K) hbound
  exact hshell.trans hcount

theorem tailDigit_supportShell_card_ge_count_index_window
    {a : Nat -> Int} {N i M X : Nat}
    (ha : StrictMono a) (hpos : ∀ n : Nat, N <= n -> 0 < a n)
    (hlo : ∀ k : Nat, i <= k -> k < i + M -> X < (a (k + N)).toNat)
    (hhi : ∀ k : Nat, i <= k -> k < i + M -> (a (k + N)).toNat <= 2 * X) :
    M <= (supportShell (tailDigit a N) X).card := by
  have hstrict := strictMono_toNat_tail_of_eventually_pos ha hpos
  have hseq := tailDigit_hitSequence hstrict
  exact hseq.supportShell_card_ge_count_index_window
    (hlo := hlo) (hhi := hhi)

theorem eventually_mul_lt_toNat_of_ratio_tendsto_atTop {a : Nat -> Int}
    (hratio :
      Filter.Tendsto (fun n : Nat => (a n : ℝ) / (n : ℝ)) Filter.atTop Filter.atTop)
    (R : Nat) :
    ∀ᶠ n : Nat in Filter.atTop, R * n < (a n).toNat := by
  filter_upwards
    [hratio.eventually (Filter.eventually_gt_atTop (R : ℝ)),
      Filter.eventually_gt_atTop (0 : Nat)]
    with n hgt hn
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmulReal : ((R * n : Nat) : ℝ) < (a n : ℝ) := by
    have hmul := mul_lt_mul_of_pos_right hgt hnreal
    have hne : (n : ℝ) ≠ 0 := ne_of_gt hnreal
    rw [div_mul_cancel₀ _ hne] at hmul
    simpa [Nat.cast_mul] using hmul
  have hmulInt : ((R * n : Nat) : Int) < a n := by
    exact_mod_cast hmulReal
  have hleftNonneg : (0 : Int) <= ((R * n : Nat) : Int) := by
    exact_mod_cast Nat.zero_le (R * n)
  have hanonneg : 0 <= a n := le_trans hleftNonneg hmulInt.le
  have hcast : (((a n).toNat : Nat) : Int) = a n := Int.toNat_of_nonneg hanonneg
  have hnatInt : ((R * n : Nat) : Int) < (((a n).toNat : Nat) : Int) := by
    rwa [hcast]
  exact_mod_cast hnatInt

theorem eventually_tail_mul_lt_toNat_of_ratio_tendsto_atTop {a : Nat -> Int}
    (hratio :
      Filter.Tendsto (fun n : Nat => (a n : ℝ) / (n : ℝ)) Filter.atTop Filter.atTop)
    (R N : Nat) :
    ∀ᶠ k : Nat in Filter.atTop, R * (k + N) < (a (k + N)).toNat :=
  (Filter.tendsto_add_atTop_nat N).eventually
    (eventually_mul_lt_toNat_of_ratio_tendsto_atTop hratio R)

theorem exists_pow_scale_of_pos {c : ℝ} (hc : 0 < c) :
    ∃ m : Nat, (1 : ℝ) < c * (2 : ℝ) ^ m := by
  rcases exists_nat_gt ((1 : ℝ) / c) with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  have hm_pow : ((1 : ℝ) / c) < (2 : ℝ) ^ m := by
    have hnat : (m : ℝ) < (2 : ℝ) ^ m := by
      exact_mod_cast (Nat.lt_two_pow_self (n := m))
    exact hm.trans hnat
  have hmul := mul_lt_mul_of_pos_left hm_pow hc
  field_simp [hc.ne'] at hmul
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmul

theorem eventually_tailDigit_supportShell_pow_lt_of_ratio_with_scale {a : Nat -> Int}
    {N m : Nat} {c : ℝ}
    (ha : StrictMono a) (hpos : ∀ n : Nat, N <= n -> 0 < a n)
    (hratio :
      Filter.Tendsto (fun n : Nat => (a n : ℝ) / (n : ℝ)) Filter.atTop Filter.atTop)
    (hscale : (1 : ℝ) < c * (2 : ℝ) ^ m) :
    ∀ᶠ L : Nat in Filter.atTop,
      ((supportShell (tailDigit a N) (2 ^ L)).card : ℝ) <
        c * ((2 ^ L : Nat) : ℝ) := by
  let R : Nat := 2 ^ (m + 2)
  rcases Filter.eventually_atTop.1
      (eventually_tail_mul_lt_toNat_of_ratio_tendsto_atTop hratio R N) with
    ⟨K0, hK0⟩
  refine Filter.eventually_atTop.2 ⟨K0 + m, ?_⟩
  intro L hL
  let t := L - m
  let K := 2 ^ t
  have hLm : m <= L := by omega
  have hL_eq : L = m + t := by
    dsimp [t]
    omega
  have hL_eq' : L = m + (L - m) := by omega
  have hK0t : K0 <= t := by
    dsimp [t]
    omega
  have hK0K : K0 <= K := by
    have htK : t <= K := Nat.le_of_lt Nat.lt_two_pow_self
    exact hK0t.trans htK
  have htail : R * (K + N) < (a (K + N)).toNat := hK0 K hK0K
  have hRK : R * K = 4 * 2 ^ L := by
    dsimp [R, K, t]
    rw [hL_eq', pow_add, pow_add]
    have hsub : m + (L - m) - m = L - m := by omega
    rw [hsub]
    ring_nf
  have hbound : 2 * 2 ^ L < (a (K + N)).toNat := by
    have hpowpos : 0 < 2 ^ L := by positivity
    have htwo_four : 2 * 2 ^ L < 4 * 2 ^ L := by nlinarith
    have hmono : R * K <= R * (K + N) := Nat.mul_le_mul_left R (Nat.le_add_right K N)
    have hfour_le : 4 * 2 ^ L <= R * (K + N) := by
      rw [← hRK]
      exact hmono
    exact (htwo_four.trans_le hfour_le).trans htail
  have hcardNat :
      (supportShell (tailDigit a N) (2 ^ L)).card <= K :=
    tailDigit_supportShell_card_le_index_of_lt ha hpos hbound
  have hcardReal :
      ((supportShell (tailDigit a N) (2 ^ L)).card : ℝ) <= (K : ℝ) := by
    exact_mod_cast hcardNat
  have hKlt : (K : ℝ) < c * ((2 ^ L : Nat) : ℝ) := by
    have htpos : 0 < (2 : ℝ) ^ t := by positivity
    have hmul := mul_lt_mul_of_pos_right hscale htpos
    calc
      (K : ℝ) = (2 : ℝ) ^ t := by simp [K]
      _ = (1 : ℝ) * (2 : ℝ) ^ t := by ring
      _ < (c * (2 : ℝ) ^ m) * (2 : ℝ) ^ t := hmul
      _ = c * (2 : ℝ) ^ L := by
        rw [hL_eq, pow_add]
        ring
      _ = c * ((2 ^ L : Nat) : ℝ) := by norm_num
  exact hcardReal.trans_lt hKlt

theorem eventually_tailDigit_supportShell_pow_lt_of_ratio {a : Nat -> Int}
    {N : Nat} {c : ℝ}
    (ha : StrictMono a) (hpos : ∀ n : Nat, N <= n -> 0 < a n)
    (hratio :
      Filter.Tendsto (fun n : Nat => (a n : ℝ) / (n : ℝ)) Filter.atTop Filter.atTop)
    (hc : 0 < c) :
    ∀ᶠ L : Nat in Filter.atTop,
      ((supportShell (tailDigit a N) (2 ^ L)).card : ℝ) <
        c * ((2 ^ L : Nat) : ℝ) := by
  rcases exists_pow_scale_of_pos hc with ⟨m, hm⟩
  exact eventually_tailDigit_supportShell_pow_lt_of_ratio_with_scale ha hpos hratio hm

theorem tailDigit_dyadicShellSublinearReal_of_ratio {a : Nat -> Int}
    {N : Nat}
    (ha : StrictMono a) (hpos : ∀ n : Nat, N <= n -> 0 < a n)
    (hratio :
      Filter.Tendsto (fun n : Nat => (a n : ℝ) / (n : ℝ)) Filter.atTop Filter.atTop) :
    DyadicShellSublinearReal (tailDigit a N) := by
  intro eps heps
  exact eventually_tailDigit_supportShell_pow_lt_of_ratio ha hpos hratio heps

theorem tailDigit_no_positiveDyadicShellDensityReal_of_ratio {a : Nat -> Int}
    {N : Nat}
    (ha : StrictMono a) (hpos : ∀ n : Nat, N <= n -> 0 < a n)
    (hratio :
      Filter.Tendsto (fun n : Nat => (a n : ℝ) / (n : ℝ)) Filter.atTop Filter.atTop) :
    ¬ ∃ c : ℝ, PositiveDyadicShellDensityReal (tailDigit a N) c := by
  intro hdens
  exact positiveDyadicShellDensityReal_not_sublinear hdens
    (tailDigit_dyadicShellSublinearReal_of_ratio ha hpos hratio)

end

end Erdos260
