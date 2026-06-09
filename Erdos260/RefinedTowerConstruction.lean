import Mathlib
import Erdos260.RefinedTower
import Erdos260.TowerFactory

/-!
# Appendix E.2–E.4: constructing a coherent recurrent SCC from carry-fibre data

This file pushes the *construction* of the input `RefinedRecurrentSCC.Coherent`
to Theorem E.6 (`theoremE6_recurrentSCCSimpleCycle`) from more primitive
**carry-fibre cycle data**.

The manuscript builds the refined terminal-labelled tower graph (Appendix E.1)
and then, on a *common AP subfibre* (E.2–E.3) with the *target-label stability*
of E.4 and the *slope transition* of E.5, observes that a recurrent strongly
connected component is a finite directed graph in which every vertex has
exactly one outgoing edge whose target stays in the component.  The
genuinely-deep arithmetic input — that the carry orbit on a common AP subfibre
actually closes into such a finite recurrent cycle — is packaged here as the
hypothesis structure `CarryFibreCycleData`.

Everything *structural* downstream of that hypothesis is then a real theorem:

* `CarryFibreCycleData.toSCC` builds a genuine `RefinedRecurrentSCC` with a
  real vertex set (the `n` cyclically-arranged refined vertices), a real edge
  relation (`i → i+1 mod n`), real edge gaps, and the slope transition on every
  edge;
* `CarryFibreCycleData.coherent` discharges **all** of the `Coherent`
  conjuncts: the common AP subfibre / layer / fibre / terminal label, the
  existence of an outgoing edge at every vertex, and genuine edge-path strong
  connectivity (built by iterating the cyclic successor and using the closed
  form of its orbit);
* `CarryFibreCycleData.isSimpleCycle` feeds the constructed coherent SCC to the
  faithful `theoremE6_recurrentSCCSimpleCycle`, yielding a real simple directed
  cycle;
* `CarryFibreCycleData.cycleData` packages the construction as the standalone
  coherent SCC witness `∃ S, RefinedTowerCycleData S`.

The construction is **non-vacuous**: explicit inhabitants
(`oneCycleExample`, a genuine fixed point of the slope recurrence, and
`twoCycleExample`, a genuine two-vertex recurrent cycle) are exhibited at the
end, and their simple cycles are derived.
-/

namespace Erdos260

open Finset
open Classical

noncomputable section

/--
**Primitive carry-fibre cycle data (Appendix E.2–E.4 hypothesis).**

This is the manuscript-level input on the recurrent SCC living on a common AP
subfibre.  It records:

* a positive number `n` of cyclically-arranged recurrent tower vertices;
* the *common* AP subfibre, threshold layer, fibre, and terminal label (E.2–E.4);
* per-vertex slopes `slope i ∈ (0,1)` (the refined open-slope condition of E.6);
* per-edge first visible gaps `gap i`, satisfying the slope transition E.13
  `μ_{i+1} = 2^{g_i} μ_i − 1` between consecutive vertices `i → (i+1) mod n`;
* injectivity of the slopes, so the `n` vertices are genuinely distinct.

The *only* assumption is that this finite cyclic shape exists; all structural
consequences (assembling a coherent recurrent SCC and feeding Theorem E.6) are
proved below.
-/
structure CarryFibreCycleData where
  /-- Number of vertices on the recurrent cycle. -/
  n : Nat
  /-- The cycle is nonempty. -/
  hn : 0 < n
  /-- Common AP subfibre of every vertex (E.2–E.3). -/
  apSubfibre : Nat
  /-- Common threshold layer of every vertex. -/
  layer : Nat
  /-- Common fibre coordinate of every vertex. -/
  fibre : Nat
  /-- Common terminal label of every vertex (E.4). -/
  terminal : Option TerminalLabel
  /-- Normalized slope `μ_i` of the `i`-th vertex. -/
  slope : Fin n → ℝ
  /-- First visible gap `g_i` of the edge `i → (i+1) mod n`. -/
  gap : Fin n → Nat
  /-- Every slope is open: `0 < μ_i < 1` (E.6). -/
  slope_open : ∀ i, 0 < slope i ∧ slope i < 1
  /-- Slope transition E.13 along the cyclic edge `i → (i+1) mod n`. -/
  slope_trans : ∀ i : Fin n,
    slope ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩ = (2 : ℝ) ^ gap i * slope i - 1
  /-- The slopes (hence the vertices) are distinct. -/
  slope_inj : Function.Injective slope

namespace CarryFibreCycleData

variable (D : CarryFibreCycleData)

/-- The cyclic successor index `i ↦ (i+1) mod n`. -/
def succIdx (i : Fin D.n) : Fin D.n := ⟨(i.val + 1) % D.n, Nat.mod_lt _ D.hn⟩

/-- The refined tower vertex sitting at cycle index `i`. -/
def vertexAt (i : Fin D.n) : RefinedVertex where
  fibre := D.fibre
  layer := D.layer
  terminal := D.terminal
  apSubfibre := D.apSubfibre
  slope := D.slope i

/-- The vertex set of the constructed SCC: the `n` cyclically-arranged vertices. -/
def vertices : Finset RefinedVertex :=
  (Finset.univ : Finset (Fin D.n)).image D.vertexAt

/-- The cyclic edge relation `vertexAt i → vertexAt (succIdx i)`. -/
def Edge (v w : RefinedVertex) : Prop :=
  ∃ i : Fin D.n, v = D.vertexAt i ∧ w = D.vertexAt (D.succIdx i)

open Classical in
/-- The gap attached to a cyclic edge, recovered from a witnessing index. -/
def edgeGap (v w : RefinedVertex) : Nat :=
  if h : ∃ i : Fin D.n, v = D.vertexAt i ∧ w = D.vertexAt (D.succIdx i) then
    D.gap (Classical.choose h)
  else 0

@[simp] theorem vertexAt_apSubfibre (i : Fin D.n) :
    (D.vertexAt i).apSubfibre = D.apSubfibre := rfl
@[simp] theorem vertexAt_slope (i : Fin D.n) :
    (D.vertexAt i).slope = D.slope i := rfl
@[simp] theorem vertexAt_layer (i : Fin D.n) :
    (D.vertexAt i).layer = D.layer := rfl
@[simp] theorem vertexAt_fibre (i : Fin D.n) :
    (D.vertexAt i).fibre = D.fibre := rfl
@[simp] theorem vertexAt_terminal (i : Fin D.n) :
    (D.vertexAt i).terminal = D.terminal := rfl

theorem vertexAt_mem (i : Fin D.n) : D.vertexAt i ∈ D.vertices :=
  Finset.mem_image_of_mem _ (Finset.mem_univ _)

theorem mem_vertices_iff {v : RefinedVertex} :
    v ∈ D.vertices ↔ ∃ i : Fin D.n, D.vertexAt i = v := by
  unfold CarryFibreCycleData.vertices
  simp [Finset.mem_image]

/-- Closed form of the cyclic-successor orbit: `succIdx^[k] i` has value
`(i + k) mod n`. -/
theorem succIdx_iterate_val (i : Fin D.n) (k : Nat) :
    (D.succIdx^[k] i).val = (i.val + k) % D.n := by
  induction k with
  | zero => simp [Nat.mod_eq_of_lt i.isLt]
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    show ((D.succIdx^[k] i).val + 1) % D.n = (i.val + (k + 1)) % D.n
    rw [ih, show i.val + (k + 1) = (i.val + k) + 1 from by ring]
    exact (Nat.mod_modEq (i.val + k) D.n).add_right 1

theorem vertexAt_injective : Function.Injective D.vertexAt := by
  intro a b hab
  apply D.slope_inj
  have h := congrArg RefinedVertex.slope hab
  simpa using h

theorem card_vertices : D.vertices.card = D.n := by
  unfold CarryFibreCycleData.vertices
  rw [Finset.card_image_of_injective _ D.vertexAt_injective, Finset.card_univ,
      Fintype.card_fin]

/-- The edge gap recovered from any witnessing index of an edge equals the
prescribed gap at that index (using that distinct vertices have distinct
indices). -/
theorem edgeGap_eq {v w : RefinedVertex} (i : Fin D.n)
    (hv : v = D.vertexAt i) (hw : w = D.vertexAt (D.succIdx i)) :
    D.edgeGap v w = D.gap i := by
  have hex : ∃ k : Fin D.n, v = D.vertexAt k ∧ w = D.vertexAt (D.succIdx k) :=
    ⟨i, hv, hw⟩
  have hchoose : Classical.choose hex = i :=
    D.vertexAt_injective ((Classical.choose_spec hex).1.symm.trans hv)
  unfold CarryFibreCycleData.edgeGap
  rw [dif_pos hex, hchoose]

/-- **Assembly of the recurrent SCC from carry-fibre data.**

A genuine `RefinedRecurrentSCC`: `n` distinct refined vertices on a common AP
subfibre, the cyclic edge relation, the per-edge gap, the slope transition on
every edge, open slopes, and abstract reachability. -/
def toSCC : RefinedRecurrentSCC where
  vertices := D.vertices
  edge := D.Edge
  edgeGap := D.edgeGap
  edgeSlopeTransition := by
    intro v w hvw
    obtain ⟨i, hv, hw⟩ := hvw
    rw [D.edgeGap_eq i hv hw]
    subst hv
    subst hw
    refine ⟨?_, ?_⟩
    · simp
    · simp only [vertexAt_slope]
      exact D.slope_trans i
  slope_open := by
    intro v hv
    rw [mem_vertices_iff] at hv
    obtain ⟨i, hi⟩ := hv
    rw [← hi]
    exact D.slope_open i
  reachable := by
    intro v _ w _
    exact ⟨[v, w], by simp, by simp⟩

@[simp] theorem toSCC_vertices : D.toSCC.vertices = D.vertices := rfl
@[simp] theorem toSCC_edge : D.toSCC.edge = D.Edge := rfl
@[simp] theorem toSCC_edgeGap : D.toSCC.edgeGap = D.edgeGap := rfl

/-- **Coherence of the constructed SCC.**

Every `Coherent` conjunct is discharged from the carry-fibre data: the common
AP subfibre / layer / fibre / terminal label, the existence of an outgoing edge
at each vertex, and genuine edge-path strong connectivity obtained by iterating
the cyclic successor (using `succIdx_iterate_val`). -/
theorem coherent : D.toSCC.Coherent where
  nonempty := by
    rw [toSCC_vertices]
    exact ⟨D.vertexAt ⟨0, D.hn⟩, D.vertexAt_mem _⟩
  commonSubfibre := by
    refine ⟨D.apSubfibre, ?_⟩
    intro v hv
    rw [toSCC_vertices, mem_vertices_iff] at hv
    obtain ⟨i, hi⟩ := hv
    subst hi
    exact D.vertexAt_apSubfibre i
  commonLayer := by
    refine ⟨D.layer, ?_⟩
    intro v hv
    rw [toSCC_vertices, mem_vertices_iff] at hv
    obtain ⟨i, hi⟩ := hv
    subst hi
    exact D.vertexAt_layer i
  commonFibre := by
    refine ⟨D.fibre, ?_⟩
    intro v hv
    rw [toSCC_vertices, mem_vertices_iff] at hv
    obtain ⟨i, hi⟩ := hv
    subst hi
    exact D.vertexAt_fibre i
  commonTerminal := by
    refine ⟨D.terminal, ?_⟩
    intro v hv
    rw [toSCC_vertices, mem_vertices_iff] at hv
    obtain ⟨i, hi⟩ := hv
    subst hi
    exact D.vertexAt_terminal i
  outEdge := by
    intro v hv
    rw [toSCC_vertices, mem_vertices_iff] at hv
    obtain ⟨i, hi⟩ := hv
    refine ⟨D.vertexAt (D.succIdx i), ?_, ?_⟩
    · rw [toSCC_vertices]; exact D.vertexAt_mem _
    · rw [toSCC_edge]; exact ⟨i, hi.symm, rfl⟩
  succReachable := by
    intro v w
    obtain ⟨i, hi⟩ := (D.mem_vertices_iff).mp v.2
    obtain ⟨j, hj⟩ := (D.mem_vertices_iff).mp w.2
    refine ⟨j.val + D.n - i.val,
      fun l => ⟨D.vertexAt (D.succIdx^[l.val] i), by
        rw [toSCC_vertices]; exact D.vertexAt_mem _⟩, ?_, ?_, ?_⟩
    · apply Subtype.ext
      simp only [Fin.val_zero, Function.iterate_zero_apply]
      exact hi
    · apply Subtype.ext
      have hk : D.succIdx^[j.val + D.n - i.val] i = j := by
        apply Fin.ext
        rw [D.succIdx_iterate_val]
        have h1 : i.val + (j.val + D.n - i.val) = j.val + D.n := by
          have := i.isLt; omega
        rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]
      simp only [Fin.val_last]
      rw [hk]; exact hj
    · intro l
      rw [toSCC_edge]
      show D.Edge (D.vertexAt (D.succIdx^[(l.castSucc).val] i))
                  (D.vertexAt (D.succIdx^[(l.succ).val] i))
      refine ⟨D.succIdx^[(l.castSucc).val] i, rfl, ?_⟩
      congr 1
      rw [Fin.val_succ, Fin.val_castSucc, Function.iterate_succ_apply']

/-- **Theorem E.6 applied to the construction.**  The constructed coherent
recurrent SCC is a simple directed cycle. -/
theorem isSimpleCycle : D.toSCC.IsSimpleCycle :=
  theoremE6_recurrentSCCSimpleCycle D.toSCC D.coherent

include D in
/-- The construction packaged as a standalone coherent SCC witness. -/
theorem cycleData : ∃ S : RefinedRecurrentSCC, RefinedTowerCycleData S :=
  ⟨D.toSCC, D.coherent⟩

end CarryFibreCycleData

/-! ### Non-vacuity: explicit genuine recurrent cycles

The construction is not vacuous.  We exhibit explicit inhabitants of
`CarryFibreCycleData` and derive their simple cycles via Theorem E.6. -/

/--
A genuine **length-one** recurrent cycle: a single refined vertex whose slope
`μ = 1/3` is a real fixed point of the slope recurrence `μ = 2² μ − 1`, with the
recurrent self-edge `μ → μ`.  This witnesses that `CarryFibreCycleData` is
non-vacuous. -/
def oneCycleExample : CarryFibreCycleData where
  n := 1
  hn := Nat.one_pos
  apSubfibre := 0
  layer := 0
  fibre := 0
  terminal := none
  slope := fun _ => 1 / 3
  gap := fun _ => 2
  slope_open := by intro i; norm_num
  slope_trans := by intro i; norm_num
  slope_inj := fun a b _ => Subsingleton.elim a b

/--
A genuine **two-vertex** recurrent cycle with distinct slopes `3/5 → 1/5 → 3/5`
and first visible gaps `1, 3`, satisfying the slope transition
`μ_{next} = 2^g μ − 1` on both directed edges.  This is a real recurrent SCC
with two distinct vertices on a common AP subfibre. -/
def twoCycleExample : CarryFibreCycleData where
  n := 2
  hn := by norm_num
  apSubfibre := 0
  layer := 0
  fibre := 0
  terminal := none
  slope := fun i => if i.val = 0 then (3 : ℝ) / 5 else 1 / 5
  gap := fun i => if i.val = 0 then 1 else 3
  slope_open := by intro i; fin_cases i <;> norm_num
  slope_trans := by intro i; fin_cases i <;> norm_num
  slope_inj := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> first
      | rfl
      | (exfalso; norm_num at hab)

/-- The one-vertex example yields a genuine simple directed cycle via E.6. -/
theorem oneCycleExample_isSimpleCycle : oneCycleExample.toSCC.IsSimpleCycle :=
  oneCycleExample.isSimpleCycle

/-- The two-vertex example yields a genuine simple directed cycle via E.6. -/
theorem twoCycleExample_isSimpleCycle : twoCycleExample.toSCC.IsSimpleCycle :=
  twoCycleExample.isSimpleCycle

/-- The two-vertex example has a genuine two-element vertex set. -/
theorem twoCycleExample_card : twoCycleExample.vertices.card = 2 :=
  twoCycleExample.card_vertices

end

end Erdos260
