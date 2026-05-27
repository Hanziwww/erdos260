import Mathlib
import Erdos260.SupportGap
import Erdos260.Target

/-!
# Enumerating support hits

This file connects abstract adjacent support gaps with a strictly increasing
enumeration of all hit positions.
-/

namespace Erdos260

noncomputable section

/-- A strictly increasing enumeration of exactly the support of `d`. -/
structure HitSequence (d : Nat -> Nat) (a : Nat -> Nat) : Prop where
  strict : StrictMono a
  hit : ∀ k : Nat, d (a k) = 1
  complete : ∀ n : Nat, d n = 1 -> ∃ k : Nat, a k = n

/-- The gap between consecutive hit positions in an enumerating sequence. -/
def hitGap (a : Nat -> Nat) (k : Nat) : Nat :=
  a (k + 1) - a k

theorem HitSequence.adjacent {d a : Nat -> Nat} (hd : BinaryDigits d)
    (hseq : HitSequence d a) (k : Nat) :
    AdjacentHits d (a k) (a (k + 1)) := by
  refine ⟨hseq.strict (Nat.lt_succ_self k), hseq.hit k, hseq.hit (k + 1), ?_⟩
  intro j haj hjb
  by_cases hj : d j = 1
  · rcases hseq.complete j hj with ⟨l, hl⟩
    by_cases hlk : l <= k
    · have hle : a l <= a k := hseq.strict.monotone hlk
      omega
    · have hk1l : k + 1 <= l := by omega
      have hle : a (k + 1) <= a l := hseq.strict.monotone hk1l
      omega
  · rcases hd j with hzero | hone
    · exact hzero
    · contradiction

theorem HitSequence.hitGap_le_dyadic_scale {Q C B X L : Nat} {P : Int}
    {d a : Nat -> Nat} (hd : BinaryDigits d) (hseq : HitSequence d a) (k : Nat)
    (hQ : 0 < Q)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ))
    (hX : X = 2 ^ L)
    (hscale : a (k + 1) + 1 <= C * X)
    (hconst : Q * C <= 2 ^ B) :
    hitGap a k <= L + B + 1 := by
  exact adjacent_hit_gap_len_le_dyadic_scale hQ hd heta (hseq.adjacent hd k) hX hscale hconst

theorem HitSequence.hitGap_le_of_dyadic_scale {Q C B X : Nat} {P : Int}
    {d a : Nat -> Nat} (hd : BinaryDigits d) (hseq : HitSequence d a) (k : Nat)
    (hQ : 0 < Q)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ))
    (hX : Dyadic X)
    (hscale : a (k + 1) + 1 <= C * X)
    (hconst : Q * C <= 2 ^ B) :
    ∃ L : Nat, X = 2 ^ L ∧ hitGap a k <= L + B + 1 := by
  rcases hX with ⟨L, hL⟩
  exact ⟨L, hL, hseq.hitGap_le_dyadic_scale hd k hQ heta hL hscale hconst⟩

theorem HitSequence.hit_mem_supportIn {d a : Nat -> Nat}
    (hseq : HitSequence d a) {k X : Nat}
    (hpos : 0 < a k) (hle : a k <= X) :
    a k ∈ supportIn d X := by
  rw [mem_supportIn]
  exact ⟨Nat.succ_le_of_lt hpos, hle, hseq.hit k⟩

theorem HitSequence.hit_mem_supportShell {d a : Nat -> Nat}
    (hseq : HitSequence d a) {k X : Nat}
    (hlo : X < a k) (hhi : a k <= 2 * X) :
    a k ∈ supportShell d X := by
  rw [mem_supportShell]
  exact ⟨hlo, hhi, hseq.hit k⟩

theorem HitSequence.supportCount_ge_succ_of_le {d a : Nat -> Nat}
    (hseq : HitSequence d a) {K X : Nat}
    (hpos : ∀ k : Nat, k <= K -> 0 < a k)
    (hbound : a K <= X) :
    K + 1 <= supportCount d X := by
  classical
  let hits : Finset Nat := (Finset.range (K + 1)).image a
  have hhits_subset : hits ⊆ supportIn d X := by
    intro n hn
    rcases Finset.mem_image.1 hn with ⟨k, hk, rfl⟩
    have hk_le : k <= K := by
      rw [Finset.mem_range] at hk
      omega
    have hak_le : a k <= a K := hseq.strict.monotone hk_le
    exact hseq.hit_mem_supportIn (hpos k hk_le) (hak_le.trans hbound)
  have hcard : hits.card = K + 1 := by
    dsimp [hits]
    rw [Finset.card_image_of_injOn]
    · simp
    · intro i hi j hj hij
      exact hseq.strict.injective hij
  have hle : hits.card <= (supportIn d X).card :=
    Finset.card_le_card hhits_subset
  simpa [supportCount, hcard] using hle

theorem HitSequence.supportShell_card_ge_count_index_window {d a : Nat -> Nat}
    (hseq : HitSequence d a) {i N X : Nat}
    (hlo : ∀ k : Nat, i <= k -> k < i + N -> X < a k)
    (hhi : ∀ k : Nat, i <= k -> k < i + N -> a k <= 2 * X) :
    N <= (supportShell d X).card := by
  classical
  let hits : Finset Nat := (Finset.Ico i (i + N)).image a
  have hhits_subset : hits ⊆ supportShell d X := by
    intro n hn
    rcases Finset.mem_image.1 hn with ⟨k, hk, rfl⟩
    rw [Finset.mem_Ico] at hk
    exact hseq.hit_mem_supportShell (hlo k hk.1 hk.2) (hhi k hk.1 hk.2)
  have hcard : hits.card = N := by
    dsimp [hits]
    rw [Finset.card_image_of_injOn]
    · simp
    · intro k hk l hl hkl
      exact hseq.strict.injective hkl
  have hle : hits.card <= (supportShell d X).card :=
    Finset.card_le_card hhits_subset
  simpa [hcard] using hle

theorem HitSequence.hasSum_erdosNatTerm {d a : Nat -> Nat}
    (hd : BinaryDigits d) (hseq : HitSequence d a)
    (hpos : ∀ k : Nat, 0 < a k) :
    HasSum (erdosNatTerm a) (realWeightedValue (natBinaryAsReal d)) := by
  let f : Nat -> ℝ := realWeightedTerm (natBinaryAsReal d)
  let g : Nat -> Nat := fun k => a k - 1
  have hginj : Function.Injective g := by
    intro i j hij
    have hai : 0 < a i := hpos i
    have haj : 0 < a j := hpos j
    have haeq : a i = a j := by
      dsimp [g] at hij
      omega
    exact hseq.strict.injective haeq
  have hzero : ∀ i : Nat, i ∉ Set.range g -> f i = 0 := by
    intro i hi
    have hdi : d (i + 1) = 0 := by
      rcases hd (i + 1) with h | h
      · exact h
      · exfalso
        rcases hseq.complete (i + 1) h with ⟨k, hk⟩
        apply hi
        refine ⟨k, ?_⟩
        dsimp [g]
        omega
    simp [f, realWeightedTerm, natBinaryAsReal, hdi]
  have hvalue :
      HasSum (f ∘ g) (realWeightedValue (natBinaryAsReal d)) :=
    (hginj.hasSum_iff hzero).2
      (realWeightedValue_hasSum_of_binary (natBinaryAsReal_digits hd))
  convert hvalue using 1
  ext k
  have hpred : a k - 1 + 1 = a k := Nat.sub_add_cancel (hpos k)
  simp [f, g, erdosNatTerm, realWeightedTerm, natBinaryAsReal, hpred, hseq.hit k]

theorem HitSequence.supportCount_le_index_of_lt {d a : Nat -> Nat}
    (hseq : HitSequence d a) {X K : Nat} (hbound : X < a K) :
    supportCount d X <= K := by
  classical
  let indexOf : Nat -> Nat := fun n =>
    if h : d n = 1 then Classical.choose (hseq.complete n h) else 0
  have hindex_spec : ∀ {n : Nat}, d n = 1 -> a (indexOf n) = n := by
    intro n hn
    dsimp [indexOf]
    rw [dif_pos hn]
    exact Classical.choose_spec (hseq.complete n hn)
  unfold supportCount
  have hle : (supportIn d X).card <= (Finset.range K).card := by
    refine Finset.card_le_card_of_injOn indexOf ?_ ?_
    · intro n hn
      have hn' : 1 <= n ∧ n <= X ∧ d n = 1 := by
        exact (mem_supportIn d X n).1 (by simpa using hn)
      have hidx := hindex_spec hn'.2.2
      by_contra hnot
      have hKle : K <= indexOf n := by
        rw [Finset.mem_coe, Finset.mem_range] at hnot
        exact Nat.le_of_not_gt hnot
      have hale : a K <= a (indexOf n) := hseq.strict.monotone hKle
      have hlt : indexOf n < K := by omega
      exact hnot (by simpa using hlt)
    · intro n hn m hm hnm
      have hn' : 1 <= n ∧ n <= X ∧ d n = 1 := by
        exact (mem_supportIn d X n).1 (by simpa using hn)
      have hm' : 1 <= m ∧ m <= X ∧ d m = 1 := by
        exact (mem_supportIn d X m).1 (by simpa using hm)
      have hnidx := hindex_spec hn'.2.2
      have hmidx := hindex_spec hm'.2.2
      calc
        n = a (indexOf n) := hnidx.symm
        _ = a (indexOf m) := by rw [hnm]
        _ = m := hmidx
  simpa using hle

theorem tailDigit_hitSequence {a : Nat -> Int} {N : Nat}
    (hstrict : StrictMono (fun k : Nat => (a (k + N)).toNat)) :
    HitSequence (tailDigit a N) (fun k : Nat => (a (k + N)).toNat) := by
  refine ⟨hstrict, ?_, ?_⟩
  · intro k
    rw [tailDigit_eq_one_iff]
    exact ⟨k, rfl⟩
  · intro n hn
    rwa [tailDigit_eq_one_iff] at hn

end

end Erdos260
