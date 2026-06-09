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

/-! ### Existence of HitSequence from non-termination

The following lemmas show that every binary digit sequence which is not
eventually zero admits a `HitSequence`.  This removes the need to supply the
hit enumeration externally in downstream factory data.
-/

/--
From a binary digit sequence that is not eventually zero, every starting
threshold `N` admits a hit at or above `N`.  This is the positive form of
`¬ EventuallyZero d`.
-/
theorem nonterminating_of_not_eventuallyZero {d : Nat → Nat}
    (hd : BinaryDigits d) (hnonterm : ¬ EventuallyZero d) :
    ∀ N : Nat, ∃ n : Nat, N ≤ n ∧ d n = 1 := by
  intro N
  by_contra h
  apply hnonterm
  refine ⟨N, ?_⟩
  intro n hn
  rcases hd n with hzero | hone
  · exact hzero
  · exfalso
    exact h ⟨n, hn, hone⟩

/--
The k-th smallest position with `d · = 1`, defined recursively via a nested
`Nat.find`.  `noncomputable` since `Nat.find` chooses a minimum from an
existential.
-/
noncomputable def hitEnumeration (d : Nat → Nat)
    (hnontermPos : ∀ N : Nat, ∃ n : Nat, N ≤ n ∧ d n = 1) :
    Nat → Nat
  | 0 => Nat.find (hnontermPos 0)
  | k + 1 => Nat.find (hnontermPos (hitEnumeration d hnontermPos k + 1))

@[simp] theorem hitEnumeration_zero (d : Nat → Nat)
    (hnontermPos : ∀ N : Nat, ∃ n : Nat, N ≤ n ∧ d n = 1) :
    hitEnumeration d hnontermPos 0 = Nat.find (hnontermPos 0) := rfl

@[simp] theorem hitEnumeration_succ (d : Nat → Nat)
    (hnontermPos : ∀ N : Nat, ∃ n : Nat, N ≤ n ∧ d n = 1) (k : Nat) :
    hitEnumeration d hnontermPos (k + 1) =
      Nat.find (hnontermPos (hitEnumeration d hnontermPos k + 1)) := rfl

/-- Each enumerated position is a hit of `d`. -/
theorem hitEnumeration_hit (d : Nat → Nat)
    (hnontermPos : ∀ N : Nat, ∃ n : Nat, N ≤ n ∧ d n = 1) (k : Nat) :
    d (hitEnumeration d hnontermPos k) = 1 := by
  cases k with
  | zero =>
    show d (Nat.find (hnontermPos 0)) = 1
    exact (Nat.find_spec (hnontermPos 0)).2
  | succ k =>
    show d (Nat.find (hnontermPos (hitEnumeration d hnontermPos k + 1))) = 1
    exact (Nat.find_spec (hnontermPos (hitEnumeration d hnontermPos k + 1))).2

/-- The successor of an enumerated position is strictly larger. -/
theorem hitEnumeration_lt_succ (d : Nat → Nat)
    (hnontermPos : ∀ N : Nat, ∃ n : Nat, N ≤ n ∧ d n = 1) (k : Nat) :
    hitEnumeration d hnontermPos k < hitEnumeration d hnontermPos (k + 1) := by
  show hitEnumeration d hnontermPos k <
      Nat.find (hnontermPos (hitEnumeration d hnontermPos k + 1))
  have h := (Nat.find_spec (hnontermPos (hitEnumeration d hnontermPos k + 1))).1
  omega

/-- `hitEnumeration` is strictly monotone in the index. -/
theorem hitEnumeration_strictMono (d : Nat → Nat)
    (hnontermPos : ∀ N : Nat, ∃ n : Nat, N ≤ n ∧ d n = 1) :
    StrictMono (hitEnumeration d hnontermPos) :=
  strictMono_nat_of_lt_succ (hitEnumeration_lt_succ d hnontermPos)

/-- Helper: the `Finset` of hits strictly below `n`. -/
def priorHits (d : Nat → Nat) (n : Nat) : Finset Nat :=
  (Finset.range n).filter (fun m => d m = 1)

theorem mem_priorHits {d : Nat → Nat} {n m : Nat} :
    m ∈ priorHits d n ↔ m < n ∧ d m = 1 := by
  classical
  simp [priorHits]

/--
Completeness: every hit `n` of `d` is the `(priorHits d n).card`-th enumerated
value.  Strong induction on `n`.

`BinaryDigits` is not needed in the proof (we only use `d n = 1`); we keep it
as a parameter so the public completeness lemma below has a uniform signature.
-/
theorem hitEnumeration_eq_of_count (d : Nat → Nat) (_hd : BinaryDigits d)
    (hnontermPos : ∀ N : Nat, ∃ n : Nat, N ≤ n ∧ d n = 1) :
    ∀ n : Nat, d n = 1 →
      hitEnumeration d hnontermPos (priorHits d n).card = n := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hempty : (priorHits d n).card = 0
    · -- Base: there is no hit strictly below `n`, so `n` is the smallest hit.
      rw [hempty]
      show Nat.find (hnontermPos 0) = n
      apply le_antisymm
      · exact Nat.find_le ⟨Nat.zero_le n, hn⟩
      · by_contra hlt
        have hfind_lt : Nat.find (hnontermPos 0) < n := not_le.mp hlt
        have hfind_d : d (Nat.find (hnontermPos 0)) = 1 :=
          (Nat.find_spec (hnontermPos 0)).2
        have hcard_pos : 0 < (priorHits d n).card := by
          refine Finset.card_pos.mpr ?_
          exact ⟨Nat.find (hnontermPos 0), mem_priorHits.mpr ⟨hfind_lt, hfind_d⟩⟩
        omega
    · -- Inductive step: split priorHits into priorHits_m ∪ {m} where m = max.
      have h_ne_empty : (priorHits d n) ≠ ∅ := by
        intro h
        rw [h] at hempty
        simp at hempty
      have h_nonempty : (priorHits d n).Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr h_ne_empty
      set m := (priorHits d n).max' h_nonempty with hm_def
      have hm_mem : m ∈ priorHits d n := (priorHits d n).max'_mem h_nonempty
      have hm_lt : m < n := (mem_priorHits.mp hm_mem).1
      have hm_d : d m = 1 := (mem_priorHits.mp hm_mem).2
      have h_ih : hitEnumeration d hnontermPos (priorHits d m).card = m :=
        ih m hm_lt hm_d
      have h_priorN_eq : priorHits d n = insert m (priorHits d m) := by
        ext l
        rw [Finset.mem_insert, mem_priorHits, mem_priorHits]
        constructor
        · rintro ⟨hl_lt, hl_d⟩
          by_cases hlm : l = m
          · exact Or.inl hlm
          · refine Or.inr ⟨?_, hl_d⟩
            have hl_in : l ∈ priorHits d n := mem_priorHits.mpr ⟨hl_lt, hl_d⟩
            have hle : l ≤ m := (priorHits d n).le_max' l hl_in
            omega
        · rintro (rfl | ⟨hl_lt, hl_d⟩)
          · exact ⟨hm_lt, hm_d⟩
          · exact ⟨lt_trans hl_lt hm_lt, hl_d⟩
      have h_m_notin : m ∉ priorHits d m := by
        intro h
        have := (mem_priorHits.mp h).1
        omega
      have h_card : (priorHits d n).card = (priorHits d m).card + 1 := by
        rw [h_priorN_eq, Finset.card_insert_of_notMem h_m_notin]
      rw [h_card]
      show Nat.find
          (hnontermPos (hitEnumeration d hnontermPos (priorHits d m).card + 1)) = n
      rw [h_ih]
      apply le_antisymm
      · exact Nat.find_le ⟨Nat.succ_le_of_lt hm_lt, hn⟩
      · by_contra hlt
        have hfind_lt : Nat.find (hnontermPos (m + 1)) < n := not_le.mp hlt
        have hfind_spec := Nat.find_spec (hnontermPos (m + 1))
        have hfind_ge : m + 1 ≤ Nat.find (hnontermPos (m + 1)) := hfind_spec.1
        have hfind_d : d (Nat.find (hnontermPos (m + 1))) = 1 := hfind_spec.2
        have hin : Nat.find (hnontermPos (m + 1)) ∈ priorHits d n :=
          mem_priorHits.mpr ⟨hfind_lt, hfind_d⟩
        have hle : Nat.find (hnontermPos (m + 1)) ≤ m :=
          (priorHits d n).le_max' _ hin
        omega

/-- Every hit position `n` appears in the enumeration. -/
theorem hitEnumeration_complete (d : Nat → Nat) (hd : BinaryDigits d)
    (hnontermPos : ∀ N : Nat, ∃ n : Nat, N ≤ n ∧ d n = 1) :
    ∀ n : Nat, d n = 1 → ∃ k : Nat, hitEnumeration d hnontermPos k = n := by
  intro n hn
  exact ⟨(priorHits d n).card, hitEnumeration_eq_of_count d hd hnontermPos n hn⟩

/--
**Main existence theorem.**  Every binary digit sequence that is not eventually
zero admits a `HitSequence`.  The witness is the recursive `Nat.find`
enumeration of positions with `d · = 1`.
-/
theorem exists_hitSequence_of_nonterminating {d : Nat → Nat}
    (hd : BinaryDigits d) (hnonterm : ¬ EventuallyZero d) :
    ∃ a : Nat → Nat, HitSequence d a := by
  let hnp := nonterminating_of_not_eventuallyZero hd hnonterm
  refine ⟨hitEnumeration d hnp, ?_, ?_, ?_⟩
  · exact hitEnumeration_strictMono d hnp
  · exact hitEnumeration_hit d hnp
  · exact hitEnumeration_complete d hd hnp

/-! ### Uniqueness of `HitSequence`

Any two `HitSequence d a` are pointwise equal, since each enumerates the same
strictly increasing set of positions with `d · = 1`.  We give the proof by
identifying every `HitSequence` with the canonical recursive `Nat.find`
enumeration `hitEnumeration`.
-/

/--
For any `HitSequence d a`, the zeroth position `a 0` is the smallest hit of
`d` (here packaged as `Nat.find` of an existential with the trivial bound
`0 ≤ n`, matching the shape used by `hitEnumeration`).
-/
theorem HitSequence.zero_eq_find {d : Nat → Nat} {a : Nat → Nat}
    (hseq : HitSequence d a) (hex : ∃ n : Nat, 0 ≤ n ∧ d n = 1) :
    a 0 = Nat.find hex := by
  classical
  apply le_antisymm
  · -- `a 0` is no larger than any other hit `Nat.find hex`.
    have hfind_d : d (Nat.find hex) = 1 := (Nat.find_spec hex).2
    obtain ⟨m, hm⟩ := hseq.complete (Nat.find hex) hfind_d
    rw [← hm]
    exact hseq.strict.monotone (Nat.zero_le m)
  · -- `Nat.find hex` is no larger than `a 0`, since `a 0` is a hit.
    exact Nat.find_le ⟨Nat.zero_le (a 0), hseq.hit 0⟩

/--
For any `HitSequence d a` and index `k`, the next position `a (k + 1)` is the
smallest hit strictly above `a k`.
-/
theorem HitSequence.succ_eq_find {d : Nat → Nat} {a : Nat → Nat}
    (hseq : HitSequence d a) (k : Nat)
    (hex : ∃ n : Nat, a k + 1 ≤ n ∧ d n = 1) :
    a (k + 1) = Nat.find hex := by
  classical
  apply le_antisymm
  · -- `a (k + 1)` is no larger than `Nat.find hex`.
    have hfind_spec := Nat.find_spec hex
    have hfind_d : d (Nat.find hex) = 1 := hfind_spec.2
    obtain ⟨m, hm⟩ := hseq.complete (Nat.find hex) hfind_d
    have hak_lt : a k < a m := by
      rw [hm]; exact hfind_spec.1
    have hk_lt_m : k < m := hseq.strict.lt_iff_lt.mp hak_lt
    rw [← hm]
    exact hseq.strict.monotone hk_lt_m
  · -- `Nat.find hex` is no larger than `a (k + 1)`, since the latter is a
    -- hit strictly above `a k`.
    exact Nat.find_le ⟨hseq.strict (Nat.lt_succ_self k), hseq.hit (k + 1)⟩

/--
Any `HitSequence d a` equals the canonical `Nat.find`-based enumeration
`hitEnumeration d (nonterminating_of_not_eventuallyZero hd hnonterm)`.
-/
theorem HitSequence.eq_hitEnumeration
    {d : Nat → Nat} {a : Nat → Nat}
    (hd : BinaryDigits d) (hnonterm : ¬ EventuallyZero d)
    (hseq : HitSequence d a) (k : Nat) :
    a k = hitEnumeration d
      (nonterminating_of_not_eventuallyZero hd hnonterm) k := by
  set hnp := nonterminating_of_not_eventuallyZero hd hnonterm with hnp_def
  induction k with
  | zero =>
    show a 0 = Nat.find (hnp 0)
    exact hseq.zero_eq_find (hnp 0)
  | succ k ih =>
    show a (k + 1) = Nat.find (hnp (hitEnumeration d hnp k + 1))
    rw [← ih]
    exact hseq.succ_eq_find k (hnp (a k + 1))

/--
Uniqueness of `HitSequence`: any two enumerations of the support of a
non-terminating binary digit sequence are equal as functions.
-/
theorem HitSequence.unique {d : Nat → Nat}
    (hd : BinaryDigits d) (hnonterm : ¬ EventuallyZero d)
    {a₁ a₂ : Nat → Nat}
    (h₁ : HitSequence d a₁) (h₂ : HitSequence d a₂) :
    a₁ = a₂ := by
  funext k
  rw [h₁.eq_hitEnumeration hd hnonterm k, h₂.eq_hitEnumeration hd hnonterm k]

/-! ### First index above a threshold

For any `HitSequence d a` and any threshold `X`, there is a (smallest) index `i`
with `X < a i`.  This follows from strict monotonicity of `a` alone, since
strictly monotone sequences `Nat → Nat` are unbounded.
-/

/--
Strictly monotone `a : Nat → Nat` are unbounded: for every `X`, there is some
index `i` with `X < a i`.
-/
theorem HitSequence.exists_index_above {d a : Nat → Nat}
    (hseq : HitSequence d a) (X : Nat) :
    ∃ i : Nat, X < a i := by
  refine ⟨X + 1, ?_⟩
  have h_id : ∀ n : Nat, n ≤ a n := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
      have h_step : a n < a (n + 1) := hseq.strict (Nat.lt_succ_self n)
      omega
  have := h_id (X + 1)
  omega

/--
The smallest index whose hit is strictly above `X`.
-/
noncomputable def HitSequence.firstIndexAbove {d a : Nat → Nat}
    (hseq : HitSequence d a) (X : Nat) : Nat :=
  Nat.find (hseq.exists_index_above X)

/-- `a (firstIndexAbove X)` is strictly above `X`. -/
theorem HitSequence.firstIndexAbove_spec {d a : Nat → Nat}
    (hseq : HitSequence d a) (X : Nat) :
    X < a (hseq.firstIndexAbove X) :=
  Nat.find_spec (hseq.exists_index_above X)

/-- Indices strictly below `firstIndexAbove X` produce hits at most `X`. -/
theorem HitSequence.lt_firstIndexAbove {d a : Nat → Nat}
    (hseq : HitSequence d a) (X : Nat)
    {k : Nat} (hk : k < hseq.firstIndexAbove X) :
    a k ≤ X := by
  by_contra h
  exact Nat.find_min (hseq.exists_index_above X) hk (not_le.mp h)

/--
**Monotonicity of `firstIndexAbove`**: larger thresholds delay the first hit.
-/
theorem HitSequence.firstIndexAbove_mono {d a : Nat → Nat}
    (hseq : HitSequence d a) {X Y : Nat} (hXY : X ≤ Y) :
    hseq.firstIndexAbove X ≤ hseq.firstIndexAbove Y := by
  apply Nat.find_le
  have h := hseq.firstIndexAbove_spec Y
  omega

/--
**`h_first_pos` discharge from `supportCount ≥ 1`.**

If the support of `d` contains at least one hit in `[1, X]`, then the
shell start index `firstIndexAbove X` is at least `1`.

Proof: pick `n ∈ supportIn d X`; by `complete`, `n = a k` for some `k`,
hence `a k ≤ X`.  By contradiction, if `firstIndexAbove X = 0`, then
`X < a 0 ≤ a k ≤ X` (strict monotonicity), absurd.
-/
theorem HitSequence.firstIndexAbove_pos_of_supportCount_pos
    {d a : Nat → Nat} (hseq : HitSequence d a)
    {X : Nat} (h : 1 ≤ supportCount d X) :
    1 ≤ hseq.firstIndexAbove X := by
  have h_card : 0 < (supportIn d X).card := h
  rw [Finset.card_pos] at h_card
  obtain ⟨n, hn⟩ := h_card
  rw [mem_supportIn] at hn
  obtain ⟨_hn_pos, hn_le, hn_hit⟩ := hn
  obtain ⟨k, hk⟩ := hseq.complete n hn_hit
  rw [← hk] at hn_le
  by_contra hi
  have h_fi : hseq.firstIndexAbove X = 0 := by omega
  have h_spec := hseq.firstIndexAbove_spec X
  rw [h_fi] at h_spec
  have h_mono : a 0 ≤ a k := hseq.strict.monotone (Nat.zero_le k)
  omega

/-! ### Shell-window geometry -/

/--
**Key identity for the dyadic shell window**:

`firstIndexAbove (2X) = firstIndexAbove X + |supportShell d X|`.

Proof: the map `j ↦ a j` sends the index interval
`[firstIndexAbove X, firstIndexAbove (2X))` bijectively to the support
shell `(X, 2X] ∩ supp(d)`.
-/
theorem HitSequence.firstIndexAbove_two_mul_eq {d a : Nat → Nat}
    (hseq : HitSequence d a) (X : Nat) :
    hseq.firstIndexAbove (2 * X) =
      hseq.firstIndexAbove X + (supportShell d X).card := by
  classical
  set i := hseq.firstIndexAbove X with hi_def
  set J := hseq.firstIndexAbove (2 * X) with hJ_def
  have h_iJ : i ≤ J := hseq.firstIndexAbove_mono (by omega : X ≤ 2 * X)
  have h_image_subset :
      (Finset.Ico i J).image a ⊆ supportShell d X := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨j, hj_mem, rfl⟩
    rw [Finset.mem_Ico] at hj_mem
    apply hseq.hit_mem_supportShell
    · have h_a_i : X < a i := hseq.firstIndexAbove_spec X
      have h_mono : a i ≤ a j := hseq.strict.monotone hj_mem.1
      omega
    · exact hseq.lt_firstIndexAbove (2 * X) hj_mem.2
  have h_image_supset :
      supportShell d X ⊆ (Finset.Ico i J).image a := by
    intro n hn
    rw [mem_supportShell] at hn
    obtain ⟨hXn, h2Xn, hn_hit⟩ := hn
    rcases hseq.complete n hn_hit with ⟨k, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨k, ?_, rfl⟩
    rw [Finset.mem_Ico]
    refine ⟨?_, ?_⟩
    · by_contra hk_lt
      have hk_lt' : k < i := Nat.lt_of_not_ge hk_lt
      have h_a_le : a k ≤ X := hseq.lt_firstIndexAbove X hk_lt'
      omega
    · by_contra hkJ
      have hkJ' : J ≤ k := Nat.le_of_not_gt hkJ
      have h_a_J : 2 * X < a J := hseq.firstIndexAbove_spec (2 * X)
      have h_mono : a J ≤ a k := hseq.strict.monotone hkJ'
      omega
  have h_image_eq : (Finset.Ico i J).image a = supportShell d X :=
    Finset.Subset.antisymm h_image_subset h_image_supset
  have h_card_image :
      ((Finset.Ico i J).image a).card = (Finset.Ico i J).card := by
    apply Finset.card_image_of_injOn
    intro x _ y _ hxy
    exact hseq.strict.injective hxy
  have h_card_Ico : (Finset.Ico i J).card = J - i := by
    rw [Nat.card_Ico]
  have h_card_supp : J - i = (supportShell d X).card := by
    rw [← h_card_Ico, ← h_card_image, h_image_eq]
  omega

/--
**`a (i + K) > 2 X`**: the first hit after the shell window
`Ico i (i + K)` strictly exceeds `2 X`, where `i = firstIndexAbove X`
and `K = |supportShell d X|`.
-/
theorem HitSequence.a_firstIndexAbove_add_card_gt
    {d a : Nat → Nat} (hseq : HitSequence d a) (X : Nat) :
    2 * X < a (hseq.firstIndexAbove X + (supportShell d X).card) := by
  rw [← hseq.firstIndexAbove_two_mul_eq]
  exact hseq.firstIndexAbove_spec (2 * X)

/--
**Every hit in the shell window is `≤ 2 X`**: indices strictly below
`i + K = firstIndexAbove X + |supportShell d X|` produce hits at most `2 X`.
-/
theorem HitSequence.a_le_two_mul_of_lt_add_card
    {d a : Nat → Nat} (hseq : HitSequence d a) (X : Nat)
    {k : Nat}
    (hk : k < hseq.firstIndexAbove X + (supportShell d X).card) :
    a k ≤ 2 * X := by
  apply hseq.lt_firstIndexAbove (2 * X)
  rw [hseq.firstIndexAbove_two_mul_eq]
  exact hk

/--
**Hit-gap bound on the shell window.**

If `k < firstIndexAbove X + r` and `r + 1 ≤ |supportShell d X|`, then
`a (k + 1) ≤ 2 X`, hence (with `C = 4`, `X ≥ 1`) the dyadic-scale
gap bound `hitGap a k ≤ L + B + 1` applies.
-/
theorem HitSequence.hitGap_le_of_shell_window
    {Q B X L : Nat} {P : Int} {d a : Nat → Nat}
    (hd : BinaryDigits d) (hseq : HitSequence d a)
    (hQ : 0 < Q)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ))
    (hX_eq : X = 2 ^ L) (hX_pos : 1 ≤ X)
    (hB : Q * 4 ≤ 2 ^ B)
    {r : Nat} (hKr : r + 1 ≤ (supportShell d X).card)
    {k : Nat}
    (hk_hi : k < hseq.firstIndexAbove X + r) :
    hitGap a k ≤ L + B + 1 := by
  have h_a_le : a (k + 1) ≤ 2 * X := by
    apply hseq.a_le_two_mul_of_lt_add_card
    omega
  have h_scale : a (k + 1) + 1 ≤ 4 * X := by omega
  exact hseq.hitGap_le_dyadic_scale hd k hQ heta hX_eq h_scale hB

/-! ### Cumulative gap identities -/

/--
Telescoping identity: `a (i + r) − a i = ∑_{l < r} hitGap a (i + l)` for any
strictly monotone enumeration of the support.
-/
theorem HitSequence.a_add_eq_sum_hitGap {d a : Nat → Nat}
    (hseq : HitSequence d a) (i r : Nat) :
    a (i + r) - a i = ∑ l ∈ Finset.range r, hitGap a (i + l) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, ← ih]
    have h_mono : a i ≤ a (i + r) :=
      hseq.strict.monotone (Nat.le_add_right i r)
    have h_idx_eq : i + (r + 1) = i + r + 1 := by ring
    rw [h_idx_eq]
    have h_step : a (i + r) ≤ a (i + r + 1) :=
      hseq.strict.monotone (Nat.le_succ _)
    unfold hitGap
    omega

/--
Cumulative gap upper bound: if every hit gap in `[i, i + r)` is at most `M`,
then `a (i + r) ≤ a i + r · M`.
-/
theorem HitSequence.a_add_le_of_hitGap_le {d a : Nat → Nat}
    (hseq : HitSequence d a) {i r M : Nat}
    (h : ∀ k, i ≤ k → k < i + r → hitGap a k ≤ M) :
    a (i + r) ≤ a i + r * M := by
  have h_eq := hseq.a_add_eq_sum_hitGap i r
  have h_each : ∀ l ∈ Finset.range r, hitGap a (i + l) ≤ M := by
    intro l hl
    rw [Finset.mem_range] at hl
    exact h (i + l) (Nat.le_add_right i l) (by omega)
  have h_const : (∑ _l ∈ Finset.range r, M) = r * M := by
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have h_sum_le :
      ∑ l ∈ Finset.range r, hitGap a (i + l) ≤ r * M := by
    calc ∑ l ∈ Finset.range r, hitGap a (i + l)
        ≤ ∑ _l ∈ Finset.range r, M := Finset.sum_le_sum h_each
      _ = r * M := h_const
  have h_mono : a i ≤ a (i + r) :=
    hseq.strict.monotone (Nat.le_add_right i r)
  omega

/--
If the hit immediately before the dyadic shell exists, and the next `N` adjacent
hit gaps are each at most `M`, then `N * M ≤ X` forces at least `N` support hits
inside `(X, 2X]`.

This is the finite shell-supply form of the manuscript dyadic gap principle:
starting from the last hit at or before `X`, a run of short adjacent gaps cannot
skip the shell before producing `N` hits.
-/
theorem HitSequence.supportShell_card_ge_of_previous_gap_bound
    {d a : Nat → Nat} (hseq : HitSequence d a) {X i N M : Nat}
    (hi : i = hseq.firstIndexAbove X)
    (hi_pos : 1 ≤ i)
    (hGap : ∀ k, i - 1 ≤ k → k < i + N → hitGap a k ≤ M)
    (hLarge : N * M ≤ X) :
    N ≤ (supportShell d X).card := by
  apply hseq.supportShell_card_ge_count_index_window (i := i) (N := N)
  · intro k hik _hk
    have hfirst : X < a i := by
      simpa [hi] using hseq.firstIndexAbove_spec X
    have hai_le : a i ≤ a k := hseq.strict.monotone hik
    omega
  · intro k hik hk
    let p := i - 1
    have hp_lt_i : p < i := by omega
    have hp_lt_first : p < hseq.firstIndexAbove X := by
      simpa [p, hi] using hp_lt_i
    have hap_le : a p ≤ X := hseq.lt_firstIndexAbove X hp_lt_first
    have hp_le_k : p ≤ k := by omega
    have hadd : p + (k - p) = k := Nat.add_sub_of_le hp_le_k
    have hcum :
        a k ≤ a p + (k - p) * M := by
      have hraw :=
        hseq.a_add_le_of_hitGap_le (i := p) (r := k - p) (M := M)
          (fun g hg_lo hg_hi => by
            apply hGap g
            · exact hg_lo
            · have hg_hi' : g < k := by
                simpa [hadd] using hg_hi
              omega)
      simpa [hadd] using hraw
    have hsteps : k - p ≤ N := by omega
    have hmul : (k - p) * M ≤ N * M := Nat.mul_le_mul_right M hsteps
    omega

end

end Erdos260
