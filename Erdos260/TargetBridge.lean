import Erdos260.TailGap

/-!
# Target-side rational bridge

This file closes the summation bridge from the DeepMind-indexed sequence to the
binary digit sequence attached to a positive tail.  If the original series has a
rational value, then the tail digit value is also an explicitly rational
`P / Q`, which is the input shape needed by `TheoremAStatement`.
-/

namespace Erdos260

noncomputable section

theorem tailDigit_hasSum_erdosNatTerm_of_eventually_pos {a : Nat -> Int} {N : Nat}
    (ha : StrictMono a) (hpos : ∀ n : Nat, N <= n -> 0 < a n) :
    HasSum (erdosNatTerm (fun k : Nat => (a (k + N)).toNat))
      (realWeightedValue (natBinaryAsReal (tailDigit a N))) := by
  have hstrict := strictMono_toNat_tail_of_eventually_pos ha hpos
  have hseq := tailDigit_hitSequence hstrict
  exact HitSequence.hasSum_erdosNatTerm (tailDigit_binary a N) hseq fun k => by
    have hkpos : 0 < a (k + N) := hpos (k + N) (by omega)
    have hcast : (0 : Int) < (((a (k + N)).toNat : Nat) : Int) := by
      rw [Int.toNat_of_nonneg hkpos.le]
      exact hkpos
    exact_mod_cast hcast

theorem tailDigit_realWeightedValue_eq_tail_sum {a : Nat -> Int} {N : Nat} {s : ℝ}
    (ha : StrictMono a) (hpos : ∀ n : Nat, N <= n -> 0 < a n)
    (hsum : HasSum (fun n : Nat => erdosTerm a n) s) :
    realWeightedValue (natBinaryAsReal (tailDigit a N)) = s - erdosFinitePrefix a N := by
  have htail :
      HasSum (fun k : Nat => erdosTerm a (k + N)) (s - erdosFinitePrefix a N) := by
    simpa [erdosFinitePrefix] using hasSum_nat_tail hsum N
  have htailNat :
      HasSum (erdosNatTerm (fun k : Nat => (a (k + N)).toNat))
        (s - erdosFinitePrefix a N) := by
    have hfun :
        erdosNatTerm (fun j : Nat => (a (j + N)).toNat) =
          fun k : Nat => erdosTerm a (k + N) := by
      funext k
      exact (erdosTerm_tail_eq_natTerm_of_eventually_pos hpos k).symm
    rwa [hfun]
  exact (tailDigit_hasSum_erdosNatTerm_of_eventually_pos ha hpos).unique htailNat

theorem exists_rat_of_not_irrational {x : ℝ} (hx : ¬ Irrational x) :
    ∃ q : Rat, x = (q : ℝ) := by
  classical
  have hxmem : x ∈ Set.range (fun q : Rat => (q : ℝ)) := by
    simpa [Irrational] using Classical.not_not.mp hx
  rcases hxmem with ⟨q, hq⟩
  exact ⟨q, hq.symm⟩

theorem tailDigit_realWeightedValue_rat_of_rat_sum {a : Nat -> Int} {N : Nat} {s : ℝ}
    (ha : StrictMono a) (hpos : ∀ n : Nat, N <= n -> 0 < a n)
    (hsum : HasSum (fun n : Nat => erdosTerm a n) s)
    (hsrat : ∃ q : Rat, s = (q : ℝ)) :
    ∃ q : Rat, realWeightedValue (natBinaryAsReal (tailDigit a N)) = (q : ℝ) := by
  rcases hsrat with ⟨qs, hqs⟩
  rcases erdosFinitePrefix_rational a N with ⟨qp, hqp⟩
  refine ⟨qs - qp, ?_⟩
  rw [tailDigit_realWeightedValue_eq_tail_sum ha hpos hsum, hqs, hqp]
  simp

theorem rat_real_as_int_div_nat (q : Rat) :
    ∃ Q : Nat, 0 < Q ∧ ∃ P : Int, (q : ℝ) = (P : ℝ) / (Q : ℝ) := by
  refine ⟨q.den, q.den_pos, q.num, ?_⟩
  rw [Rat.cast_def]

theorem exists_int_nat_div_of_rat_real {x : ℝ} (hx : ∃ q : Rat, x = (q : ℝ)) :
    ∃ Q : Nat, 0 < Q ∧ ∃ P : Int, x = (P : ℝ) / (Q : ℝ) := by
  rcases hx with ⟨q, hq⟩
  rcases rat_real_as_int_div_nat q with ⟨Q, hQ, P, hP⟩
  exact ⟨Q, hQ, P, by rw [hq, hP]⟩

theorem exists_tailDigit_rational_data_of_rational_sum {a : Nat -> Int} {s : ℝ}
    (ha : StrictMono a)
    (hratio :
      Filter.Tendsto (fun n : Nat => (a n : ℝ) / (n : ℝ)) Filter.atTop Filter.atTop)
    (hsum : HasSum (fun n : Nat => erdosTerm a n) s)
    (hsrat : ∃ q : Rat, s = (q : ℝ)) :
    ∃ N Q : Nat, ∃ P : Int,
      0 < Q ∧
        (∀ n : Nat, N <= n -> 0 < a n) ∧
          BinaryDigits (tailDigit a N) ∧
            ¬ EventuallyZero (tailDigit a N) ∧
              realWeightedValue (natBinaryAsReal (tailDigit a N)) =
                (P : ℝ) / (Q : ℝ) := by
  rcases exists_eventual_pos_of_ratio_tendsto_atTop hratio with ⟨N, hpos⟩
  have hd : BinaryDigits (tailDigit a N) := tailDigit_binary a N
  have hnon : Nonterminating (tailDigit a N) :=
    tailDigit_nonterminating_of_eventually_pos ha hpos
  have hnot : ¬ EventuallyZero (tailDigit a N) :=
    (not_eventuallyZero_iff_nonterminating hd).2 hnon
  have hrat :
      ∃ q : Rat, realWeightedValue (natBinaryAsReal (tailDigit a N)) = (q : ℝ) :=
    tailDigit_realWeightedValue_rat_of_rat_sum ha hpos hsum hsrat
  rcases exists_int_nat_div_of_rat_real hrat with ⟨Q, hQ, P, hP⟩
  exact ⟨N, Q, P, hQ, hpos, hd, hnot, hP⟩

theorem exists_tailDigit_rational_data_of_not_irrational_sum {a : Nat -> Int} {s : ℝ}
    (ha : StrictMono a)
    (hratio :
      Filter.Tendsto (fun n : Nat => (a n : ℝ) / (n : ℝ)) Filter.atTop Filter.atTop)
    (hsum : HasSum (fun n : Nat => erdosTerm a n) s) (hsrat : ¬ Irrational s) :
    ∃ N Q : Nat, ∃ P : Int,
      0 < Q ∧
        (∀ n : Nat, N <= n -> 0 < a n) ∧
          BinaryDigits (tailDigit a N) ∧
            ¬ EventuallyZero (tailDigit a N) ∧
              realWeightedValue (natBinaryAsReal (tailDigit a N)) =
                (P : ℝ) / (Q : ℝ) :=
  exists_tailDigit_rational_data_of_rational_sum ha hratio hsum
    (exists_rat_of_not_irrational hsrat)

theorem theoremA_contradicts_nonirrational_erdos_sum
    (hA : TheoremAStatement) {a : Nat -> Int} {s : ℝ}
    (ha : StrictMono a)
    (hratio :
      Filter.Tendsto (fun n : Nat => (a n : ℝ) / (n : ℝ)) Filter.atTop Filter.atTop)
    (hsum : HasSum (fun n : Nat => erdosTerm a n) s) (hsrat : ¬ Irrational s) :
    False := by
  rcases exists_tailDigit_rational_data_of_not_irrational_sum ha hratio hsum hsrat with
    ⟨N, Q, P, hQ, hpos, hd, hnot, hvalue⟩
  exact theoremA_contradicts_sublinear_rational_digit hA hQ hd hnot
    ⟨P, hvalue⟩
    (tailDigit_dyadicShellSublinearReal_of_ratio ha hpos hratio)

theorem erdos260Statement_of_theoremA (hA : TheoremAStatement) :
    Erdos260Statement := by
  intro a s ha hratio hsum
  by_contra hsrat
  exact theoremA_contradicts_nonirrational_erdos_sum hA ha hratio hsum hsrat

end

end Erdos260
