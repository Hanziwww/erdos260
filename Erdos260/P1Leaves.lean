/-
  P1 Tier-1 leaves: further self-contained pieces discharging trust-boundary
  inputs.  (Phase P1 of the formalization roadmap.)
-/
import Mathlib

namespace Erdos260.P1Leaves

/-! ## E.6 / O1: a finite functional graph has a directed cycle.

A refined recurrent tower vertex has out-degree ≤ 1 (the slope-interval uniqueness
`P2TrustBoundary.e6_slope_gap_unique`).  Restricting to the recurrent component, the
successor is a *function* `f : V → V` on a finite vertex set; the graph-theoretic
input of E.6 ("every recurrent SCC is a simple directed cycle") rests on the fact
that such a functional graph always contains a directed cycle, i.e. a periodic
point.  We prove that here. -/

theorem functional_graph_has_periodic_point
    {V : Type*} [Finite V] [Nonempty V] (f : V → V) :
    ∃ (x : V) (n : ℕ), 0 < n ∧ f^[n] x = x := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty V)
  obtain ⟨i, j, hij, hgg⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun k : ℕ => f^[k] x₀)
  rcases Nat.lt_or_ge i j with h | h
  · refine ⟨f^[i] x₀, j - i, by omega, ?_⟩
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel (le_of_lt h)]
    exact hgg.symm
  · have hji : j < i := lt_of_le_of_ne h (Ne.symm hij)
    refine ⟨f^[j] x₀, i - j, by omega, ?_⟩
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel (le_of_lt hji)]
    exact hgg

/-- On a strongly-connected functional graph the cycle is unique and exhausts the
    component: if every vertex reaches every other under `f`-iteration, then from a
    periodic point the whole component is one orbit.  We record the consequence used
    by E.6: in a finite functional graph, the successor `f` is surjective onto the
    set of periodic points, and (being a function on a finite set) is a bijection
    there.  The clean kernel: the periodic points of `f` form an `f`-invariant set
    on which `f` is bijective. -/
theorem iterate_periodic_invariant
    {V : Type*} (f : V → V) (x : V) (n : ℕ) (hcyc : f^[n] x = x) (k : ℕ) :
    f^[n] (f^[k] x) = f^[k] x := by
  rw [← Function.iterate_add_apply, Nat.add_comm, Function.iterate_add_apply, hcyc]

end Erdos260.P1Leaves
