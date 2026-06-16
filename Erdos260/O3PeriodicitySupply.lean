import Mathlib
import Erdos260.P1Leaves
import Erdos260.P2TrustBoundary
import Erdos260.O3SlopePeriodicFloor

/-!
# O3 periodicity SUPPLY side: out-degree-1 forces a bounded-period clean continuation

This module (NEW; it edits no existing file) formalizes the **supply side** of the Erdős-#260
fixed-pin confinement — the genuine trust boundary behind App U
`lem:u-fixed-pin-periodic-continuation` (line 9387) — namely that the **E.6 outgoing-uniqueness**
(App E.6, line 2196: *"a fixed refined tower state has at most one recurrent outgoing visible
gap"*, i.e. **out-degree ≤ 1**) forces every retained fixed-pin branch into an **eventually
periodic clean continuation with bounded period**, which is exactly the `p ≤ 3Q` (U.2, line 9393)
input *consumed* by the already-proved VOID core `Erdos260.O3SlopePeriodicFloor`.

## The graph-theoretic heart (App E.6, lines 2230–2237)

> *"Let `𝒞` be a recurrent strongly connected component. … By the outgoing uniqueness just
> proved, it has exactly one such edge. **A finite directed graph in which every vertex has
> exactly one outgoing edge contains a directed cycle; strong connectivity forces every vertex
> of `𝒞` to lie on that cycle.** Therefore every recurrent SCC … is a simple directed cycle."*

E.6 out-degree-1 says the successor on the recurrent component is a *function* `f : V → V`
(a **functional graph**).  The supply statement we discharge here is the clean Mathlib-able heart:

* **Task 1 — every point of a finite functional graph is EVENTUALLY PERIODIC**
  (`eventuallyPeriodic_of_fintype`), with explicit bounds `μ ≤ card V` and `p ≤ card V`
  (pre-period and period bounded by the state-space size), proved by **pigeonhole** on
  `f^[0..card V] x`.  This is *"the clean continuation is eventually periodic with bounded
  period"* (U.1/U.2, lines 9369–9398; AM.3, line 9799-region; AR.1–AR.3, lines 12519–12555).
* **Task 2 — bounded period from a bounded state space** (`fixedPin_period_le_card`,
  `fixedPin_period_within_fireBudget`, `o3_fixedPin_supply_void`): if the continuation's state
  lives in a finite set of size `≤ M` then the period is `≤ M`; instantiating `M = 2^19`
  (App U fire budget, line 9508 / the `2^19 < 2^24/17` representative) gives `p ≤ 2^19`, and
  with `M ≤ 3Q` the period feeds directly into `O3SlopePeriodicFloor.boundedPeriod_sparse_void`
  — connecting the **SUPPLY** to the already-proved **VOID**, closing the O3 chain modulo the
  single residual hypothesis that the continuation's state space *is* the bounded slope-row set.
* **Task 3 — nonzero/clean continuation invariance** (`iterate_lap_invariant`,
  `cycle_nonzero_persists`, `cycle_block_supply`): reusing `P1Leaves.iterate_periodic_invariant`,
  the periodic continuation stays in the retained nonzero class along the cycle — a hit at one
  phase recurs every lap — which produces exactly the per-block hit supply (`hblk`) consumed by
  the void.

## Pitfall-freedom

Faithful to AR.-1 (line 12450): nothing here reads a digit off the digit-blind fractional orbit
`(R_n/Q) mod 1`.  The word fed to the void is `n ↦ D (f^[n] y)`, the **actual** state-indexed
digit read off the orbit of the functional graph, with periodicity inherited from the cycle
`f^[p] y = y` (App AM.1 `w_g = 10^{g-1}`, line 11805).

## What is PROVED here (no `sorry`/`axiom`/`admit`/`native_decide`)

* `eventuallyPeriodic_of_fintype` — Task 1, the supply core (pigeonhole, `μ,p ≤ card V`).
* `fixedPin_period_le_card` — the cycle-entry corollary: `x` reaches a periodic point of period
  `p ≤ card V` after `μ ≤ card V` steps.
* `iterate_lap_invariant`, `cycle_nonzero_persists` — Task 3 (reuse `iterate_periodic_invariant`).
* `cycle_block_supply` — the per-block hit supply (`hblk`) produced from a nonzero cycle.
* `o3_fixedPin_supply_void`, `o3_fixedPin_supply_void_int` — Task 2 bridge: cycle + nonzero hit +
  bounded period `p ≤ 3Q` ⇒ the `O3SlopePeriodicFloor` void fires (`False`).
* `fixedPin_period_le_threeQ`, `fixedPin_period_within_fireBudget` — the `p ≤ 3Q` and `p ≤ 2^19`
  instantiations (the latter with the explicit `17p < 2^24` fire budget).
* `o3_fixedPin_supply_void_of_boundedStateSpace` — the assembled capstone: bounded state space
  (`card V ≤ 3Q`) + nonzero-continuation/sparse-shell supply ⇒ `False`.
-/

namespace Erdos260.O3PeriodicitySupply

open Erdos260

set_option linter.unusedVariables false

/-! ## 1.  Task 1 — eventually periodic from out-degree 1 (the SUPPLY core)

A functional graph is exactly the E.6 out-degree-1 successor `f : V → V`.  On a finite vertex
set every point is eventually periodic, by pigeonhole on the first `card V + 1` iterates. -/

/-- **Task 1 — every point of a finite functional graph is eventually periodic, with bounds.**
For a finite type `V` (the slope-row state space) and any `f : V → V` (the E.6 out-degree-1
successor) and any `x`, there are a pre-period `μ ≤ card V` and a period `0 < p ≤ card V` with
`f^[n+p] x = f^[n] x` for all `n ≥ μ`.

Proof: among the `card V + 1` iterates `f^[0] x, …, f^[card V] x` two must coincide
(`Finset.exists_ne_map_eq_of_card_lt_of_maps_to`), say `f^[i] x = f^[j] x` with `i < j ≤ card V`;
take `μ = i`, `p = j - i`.  This is the formal content of "the retained fixed-pin clean
continuation is eventually periodic" (App U.1/U.2, App E.6's finite functional-graph argument). -/
theorem eventuallyPeriodic_of_fintype {V : Type*} [Fintype V] (f : V → V) (x : V) :
    ∃ μ p : ℕ, 0 < p ∧ μ ≤ Fintype.card V ∧ p ≤ Fintype.card V ∧
      ∀ n, μ ≤ n → f^[n + p] x = f^[n] x := by
  classical
  obtain ⟨a, ha, b, hb, hab, hgab⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := Finset.range (Fintype.card V + 1)) (t := (Finset.univ : Finset V))
      (f := fun k => f^[k] x)
      (by rw [Finset.card_univ, Finset.card_range]; omega)
      (fun a _ => Finset.mem_univ _)
  rw [Finset.mem_range] at ha hb
  rcases Nat.lt_or_ge a b with hlt | hge
  · refine ⟨a, b - a, by omega, by omega, by omega, ?_⟩
    intro n hn
    have key : f^[a + (b - a)] x = f^[a] x := by
      rw [Nat.add_sub_cancel' (le_of_lt hlt)]; exact hgab.symm
    have e1 : (n - a) + (a + (b - a)) = n + (b - a) := by omega
    have e2 : (n - a) + a = n := by omega
    calc f^[n + (b - a)] x
        = f^[(n - a) + (a + (b - a))] x := by rw [e1]
      _ = f^[n - a] (f^[a + (b - a)] x) := by rw [Function.iterate_add_apply]
      _ = f^[n - a] (f^[a] x) := by rw [key]
      _ = f^[(n - a) + a] x := by rw [← Function.iterate_add_apply]
      _ = f^[n] x := by rw [e2]
  · have hba : b < a := lt_of_le_of_ne hge (Ne.symm hab)
    refine ⟨b, a - b, by omega, by omega, by omega, ?_⟩
    intro n hn
    have key : f^[b + (a - b)] x = f^[b] x := by
      rw [Nat.add_sub_cancel' (le_of_lt hba)]; exact hgab
    have e1 : (n - b) + (b + (a - b)) = n + (a - b) := by omega
    have e2 : (n - b) + b = n := by omega
    calc f^[n + (a - b)] x
        = f^[(n - b) + (b + (a - b))] x := by rw [e1]
      _ = f^[n - b] (f^[b + (a - b)] x) := by rw [Function.iterate_add_apply]
      _ = f^[n - b] (f^[b] x) := by rw [key]
      _ = f^[(n - b) + b] x := by rw [← Function.iterate_add_apply]
      _ = f^[n] x := by rw [e2]

/-- **Cycle entry with bounded period.**  The eventual-periodicity of `eventuallyPeriodic_of_fintype`
upgrades to a genuine periodic point: after `μ ≤ card V` steps the orbit reaches `y = f^[μ] x` with
`f^[p] y = y` and `0 < p ≤ card V`.  This is exactly App E.6's *"every vertex of the recurrent SCC
lies on the cycle"* (line 2235): the retained fixed-pin branch enters its periodic clean
continuation of bounded period. -/
theorem fixedPin_period_le_card {V : Type*} [Fintype V] (f : V → V) (x : V) :
    ∃ (μ p : ℕ), 0 < p ∧ μ ≤ Fintype.card V ∧ p ≤ Fintype.card V ∧
      f^[p] (f^[μ] x) = f^[μ] x := by
  obtain ⟨μ, p, hp, hμ, hpc, hper⟩ := eventuallyPeriodic_of_fintype f x
  refine ⟨μ, p, hp, hμ, hpc, ?_⟩
  have h := hper μ (le_refl μ)
  calc f^[p] (f^[μ] x)
      = f^[p + μ] x := (Function.iterate_add_apply f p μ x).symm
    _ = f^[μ + p] x := by rw [Nat.add_comm]
    _ = f^[μ] x := h

/-! ## 2.  Task 3 — nonzero/clean continuation invariance along the cycle

Reusing `P1Leaves.iterate_periodic_invariant`, a point on the cycle stays on the cycle and a hit
at one phase recurs every lap.  This is the "clean continuation stays in the retained nonzero
class" content (App AM.3 / AR.3: consecutive hits separated by the same actual gap `g`,
`x_{n+1} = x_n + g`), and it is precisely the per-block hit supply consumed by the void. -/

/-- **Lap invariance** (reuses `iterate_periodic_invariant`).  On a cycle `f^[p] y = y`, advancing
by any whole number `ℓ` of laps returns to the same phase: `f^[k + ℓ·p] y = f^[k] y`. -/
theorem iterate_lap_invariant {V : Type*} (f : V → V) (y : V) (p : ℕ) (hcyc : f^[p] y = y)
    (ℓ k : ℕ) : f^[k + ℓ * p] y = f^[k] y := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
    have e : k + (ℓ + 1) * p = p + (k + ℓ * p) := by ring
    rw [e, Function.iterate_add_apply,
      Erdos260.P1Leaves.iterate_periodic_invariant f y p hcyc (k + ℓ * p)]
    exact ih

/-- **Nonzero class persists along the cycle.**  If the state-indexed digit map `D` has a hit
(`1 ≤ D (f^[k₀] y)`) at some phase `k₀` on the cycle `f^[p] y = y`, then that hit recurs at every
lap `k₀ + ℓ·p`.  This is the slope-fixed word `w_g = 10^{g-1}` being nonzero on every period
(App AM, line 11859; AR.2, line 12529: "the row is nonzero because the phase `a = 0` occurs once
in every complete lap"). -/
theorem cycle_nonzero_persists {V : Type*} (f : V → V) (y : V) (p : ℕ) (hcyc : f^[p] y = y)
    (D : V → ℕ) (k₀ : ℕ) (hhit : 1 ≤ D (f^[k₀] y)) (ℓ : ℕ) :
    1 ≤ D (f^[k₀ + ℓ * p] y) := by
  rw [iterate_lap_invariant f y p hcyc ℓ k₀]; exact hhit

/-- **Per-block hit supply from a nonzero cycle.**  With a nonzero hit at phase `k₀ < p` on the
cycle, every spatial period block `[j·p, (j+1)·p)` of the orbit-indexed word `n ↦ D (f^[n] y)`
carries a hit.  This is exactly the `hblk` hypothesis of
`O3SlopePeriodicFloor.boundedPeriod_sparse_void` (Lemma U.3, line 9423: "a nonzero binary word of
period `p` has at least one symbol `1` in each period block"). -/
theorem cycle_block_supply {V : Type*} (f : V → V) (y : V) (D : V → ℕ) (p : ℕ) (hp : 0 < p)
    (hcyc : f^[p] y = y) (k₀ : ℕ) (hk₀ : k₀ < p) (hhit : 1 ≤ D (f^[k₀] y)) (W : ℕ) :
    ∀ j, j < W / p → ∃ i, 0 + j * p ≤ i ∧ i < 0 + (j + 1) * p ∧
      1 ≤ (fun n => D (f^[n] y)) i := by
  intro j hj
  refine ⟨k₀ + j * p, by omega, ?_, ?_⟩
  · have e : (j + 1) * p = j * p + p := by ring
    omega
  · show 1 ≤ D (f^[k₀ + j * p] y)
    rw [iterate_lap_invariant f y p hcyc j k₀]; exact hhit

/-! ## 3.  Task 2 — bridge the SUPPLY to the already-proved VOID

The cycle + nonzero hit + bounded period `p ≤ 3Q` produce the `hblk` of the void core, so
`O3SlopePeriodicFloor.boundedPeriod_sparse_void(_real)` fires: no retained fixed-pin branch
survives the sparse shell. -/

/-- **SUPPLY → VOID bridge (real / manuscript form).**  A retained fixed-pin branch sitting on a
cycle `f^[p] y = y` of bounded period `p ≤ 3Q`, nonzero (hit at phase `k₀`), whose orbit-indexed
word `n ↦ D (f^[n] y)` satisfies the sparse-shell cap on a deep window `W ≥ 6Q`, is impossible.
Composes the supply (`cycle_block_supply`) into `O3SlopePeriodicFloor.boundedPeriod_sparse_void_real`
(Prop U `prop:u-fixed-pins-direct`, line 9430 / Cor `cor:am-u-fixed-pin-voiding`, line 11882). -/
theorem o3_fixedPin_supply_void {V : Type*} (f : V → V) (y : V) (D : V → ℕ)
    (Q W p k₀ : ℕ) (cstar : ℝ)
    (hQ : 1 ≤ Q) (hp : 0 < p) (hpb : p ≤ 3 * Q)
    (hcyc : f^[p] y = y) (hk₀ : k₀ < p) (hhit : 1 ≤ D (f^[k₀] y))
    (hW : 6 * Q ≤ W)
    (hcstar : cstar < 1 / (6 * (Q : ℝ)))
    (hsparse : (O3SlopePeriodicFloor.hitCount (fun n => D (f^[n] y)) 0 W : ℝ)
        < cstar * (W : ℝ)) :
    False :=
  O3SlopePeriodicFloor.boundedPeriod_sparse_void_real
    (fun n => D (f^[n] y)) Q 0 p W cstar hQ hp hpb hW
    (cycle_block_supply f y D p hp hcyc k₀ hk₀ hhit W) hcstar hsparse

/-- **SUPPLY → VOID bridge (integer density form).**  The integer-form sparse cap
`6Q · hitCount < W` (density `< 1/(6Q)`) is contradicted by the bounded-period nonzero
continuation.  Composes the supply into `O3SlopePeriodicFloor.boundedPeriod_sparse_void`. -/
theorem o3_fixedPin_supply_void_int {V : Type*} (f : V → V) (y : V) (D : V → ℕ)
    (Q W p k₀ : ℕ)
    (hQ : 1 ≤ Q) (hp : 0 < p) (hpb : p ≤ 3 * Q)
    (hcyc : f^[p] y = y) (hk₀ : k₀ < p) (hhit : 1 ≤ D (f^[k₀] y))
    (hW : 6 * Q ≤ W)
    (hcap : 6 * Q * O3SlopePeriodicFloor.hitCount (fun n => D (f^[n] y)) 0 W < W) :
    False :=
  O3SlopePeriodicFloor.boundedPeriod_sparse_void
    (fun n => D (f^[n] y)) Q 0 p W hQ hp hpb hW
    (cycle_block_supply f y D p hp hcyc k₀ hk₀ hhit W) hcap

/-! ## 4.  Bounded-period instantiations: `p ≤ 3Q` and the `2^19` fire budget -/

/-- **Bounded period from a `3Q`-bounded state space** (App U.2, line 9393).  If the fixed-pin
continuation's slope-row state space has size `≤ 3Q`, then the period it falls into is `≤ 3Q`. -/
theorem fixedPin_period_le_threeQ {V : Type*} [Fintype V] (Q : ℕ)
    (hcard : Fintype.card V ≤ 3 * Q) (f : V → V) (x : V) :
    ∃ (μ p : ℕ), 0 < p ∧ p ≤ 3 * Q ∧ f^[p] (f^[μ] x) = f^[μ] x := by
  obtain ⟨μ, p, hp, _, hpc, hcyc⟩ := fixedPin_period_le_card f x
  exact ⟨μ, p, hp, le_trans hpc hcard, hcyc⟩

/-- **Bounded period inside the App-U fire budget** (line 9508; the `2^19 < 2^24/17` representative
of the task).  Instantiating the slope-row state-space bound at `M = 2^19`, the fixed-pin
continuation enters a cycle of period `p ≤ 2^19`, which lies strictly inside the sharp fire budget
`17·p < 2^24` (`O3SlopePeriodicFloor.boundedPeriod_within_fireBudget`). -/
theorem fixedPin_period_within_fireBudget {V : Type*} [Fintype V]
    (hcard : Fintype.card V ≤ 2 ^ 19) (f : V → V) (x : V) :
    ∃ (μ p : ℕ), 0 < p ∧ p ≤ 2 ^ 19 ∧ 17 * p < (2 : ℕ) ^ 24 ∧
      f^[p] (f^[μ] x) = f^[μ] x := by
  obtain ⟨μ, p, hp, _, hpc, hcyc⟩ := fixedPin_period_le_card f x
  have hp19 : p ≤ 2 ^ 19 := le_trans hpc hcard
  exact ⟨μ, p, hp, hp19, O3SlopePeriodicFloor.boundedPeriod_within_fireBudget hp19, hcyc⟩

/-! ## 5.  Assembled capstone: bounded state space ⇒ void (the O3 chain, modulo identification) -/

/-- **ASSEMBLED CAPSTONE — the O3 supply chain closed modulo one residual hypothesis.**

Given the **bounded state space** of the fixed-pin slope-row continuation (`card V ≤ 3Q`, App U.2 /
AR.0, the residual identification of the continuation's state space with the bounded slope-row set),
and the **structural supply** `hsupply` for whichever bounded cycle the branch reaches — that the
clean continuation is *nonzero* (a hit `1 ≤ D (f^[k₀] y)` at some phase, App AM.1/AR.2 `w_g`) and
satisfies the *sparse-shell cap* (App U.3, `A_S(2X)-A_S(X) < c_*X`, `c_* < 1/(6Q)`) — there is a
contradiction: **no retained deep fixed-orbit-pin branch survives the sparse shell**
(`prop:u-fixed-pins-direct`, line 9430).

This wires the SUPPLY (`fixedPin_period_le_card`, from E.6 out-degree-1) directly into the proved
VOID (`O3SlopePeriodicFloor`).  The only residual content is `hcard` and the structural facts
packaged in `hsupply`; the eventual-periodicity, the bounded-period entry, the lap invariance, and
the density-floor void are all discharged. -/
theorem o3_fixedPin_supply_void_of_boundedStateSpace {V : Type*} [Fintype V]
    (f : V → V) (x : V) (D : V → ℕ) (Q W : ℕ) (cstar : ℝ)
    (hQ : 1 ≤ Q) (hcard : Fintype.card V ≤ 3 * Q) (hW : 6 * Q ≤ W)
    (hcstar : cstar < 1 / (6 * (Q : ℝ)))
    (hsupply : ∀ (y : V) (p : ℕ), 0 < p → p ≤ Fintype.card V → f^[p] y = y →
        (∃ k₀, k₀ < p ∧ 1 ≤ D (f^[k₀] y)) ∧
        ((O3SlopePeriodicFloor.hitCount (fun n => D (f^[n] y)) 0 W : ℝ) < cstar * (W : ℝ))) :
    False := by
  obtain ⟨μ, p, hp, _, hpc, hcyc⟩ := fixedPin_period_le_card f x
  obtain ⟨⟨k₀, hk₀, hhit⟩, hsparse⟩ := hsupply (f^[μ] x) p hp hpc hcyc
  exact o3_fixedPin_supply_void f (f^[μ] x) D Q W p k₀ cstar hQ hp
    (le_trans hpc hcard) hcyc hk₀ hhit hW hcstar hsparse

/-! ## 6.  Honest residual / status inventory -/

/-- The precise status of the O3 periodicity-supply side. -/
def o3PeriodicitySupplyResiduals : List String :=
  [ "GOAL — discharge the periodicity-SUPPLY hypothesis behind App U " ++
      "lem:u-fixed-pin-periodic-continuation (line 9387): E.6 outgoing-uniqueness (out-degree 1, " ++
      "line 2196) forces a retained fixed-pin branch into an eventually-periodic clean continuation " ++
      "of bounded period p ≤ 3Q (U.2, line 9393), the input consumed by O3SlopePeriodicFloor.",
    "CLOSED (Task 1, core) — eventuallyPeriodic_of_fintype: every point of a finite functional " ++
      "graph f : V → V is eventually periodic with μ ≤ card V and p ≤ card V (pigeonhole on the " ++
      "first card V + 1 iterates). This is the finite functional-graph heart of App E.6 (line 2234).",
    "CLOSED (Task 1) — fixedPin_period_le_card: the branch reaches a genuine periodic point " ++
      "f^[p] (f^[μ] x) = f^[μ] x with μ, p ≤ card V (E.6: every vertex of the recurrent SCC lies " ++
      "on the cycle, line 2235).",
    "CLOSED (Task 3) — iterate_lap_invariant / cycle_nonzero_persists (reuse " ++
      "P1Leaves.iterate_periodic_invariant): a hit at one phase recurs every lap, so the clean " ++
      "continuation stays in the retained nonzero class along the cycle (AM.3 / AR.2/AR.3).",
    "CLOSED (Task 3 → supply) — cycle_block_supply: a nonzero bounded cycle supplies a hit in every " ++
      "spatial period block, i.e. the hblk hypothesis of O3SlopePeriodicFloor.boundedPeriod_sparse_void.",
    "CLOSED (Task 2 bridge) — o3_fixedPin_supply_void(_int): cycle + nonzero hit + bounded period " ++
      "p ≤ 3Q + deep window + sparse cap ⇒ False, by composing the supply into the proved VOID " ++
      "core (Prop U line 9430 / Cor AM line 11882).",
    "CLOSED (Task 2 instantiation) — fixedPin_period_le_threeQ (p ≤ 3Q) and " ++
      "fixedPin_period_within_fireBudget (card V ≤ 2^19 ⇒ p ≤ 2^19 and 17p < 2^24, the App-U fire " ++
      "budget of line 9508 / the task's 2^19 < 2^24/17).",
    "CLOSED (assembled) — o3_fixedPin_supply_void_of_boundedStateSpace: bounded state space " ++
      "card V ≤ 3Q + structural nonzero/sparse supply ⇒ False; the O3 chain closed end to end.",
    "RESIDUAL (single trust boundary, as permitted) — the identification of the fixed-pin " ++
      "continuation's state space with the bounded slope-row set: i.e. the Fintype V with " ++
      "card V ≤ 3Q (resp. ≤ 2^19), that the emitted digit is the state function n ↦ D (f^[n] y), " ++
      "that the cycle is nonzero, and the sparse-shell cap. These are the App AR/AM/E structural " ++
      "facts (hsupply / hcard), NOT discharged here.",
    "PITFALL-FREE — the word fed to the void is the actual state-indexed orbit word n ↦ D (f^[n] y) " ++
      "with periodicity inherited from the cycle f^[p] y = y; the digit-blind fractional orbit " ++
      "(R_n/Q) mod 1 (AR.-1, line 12450) is never used. No vacuous/empty shortcut." ]

theorem o3PeriodicitySupplyResiduals_nonempty : o3PeriodicitySupplyResiduals ≠ [] := by
  simp [o3PeriodicitySupplyResiduals]

end Erdos260.O3PeriodicitySupply
