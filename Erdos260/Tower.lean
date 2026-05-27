import Mathlib

/-!
# Terminal-labelled tower primitives

This file contains the finite deterministic-tower vocabulary used by Appendix E
of `proof_v2.tex`: terminal labels, common fibres, deterministic transitions,
label/fibre stability, and the elementary no-return consequence of strict layer
increase.
-/

namespace Erdos260

open Finset

noncomputable section

/-- A terminal label attached to a tower vertex. -/
structure TerminalLabel where
  id : Nat
deriving DecidableEq, Repr

/-- A refined tower vertex with a fibre, threshold layer, and optional terminal label. -/
structure TowerVertex where
  fibre : Nat
  layer : Nat
  terminal : Option TerminalLabel
deriving DecidableEq, Repr

/-- A directed transition between tower vertices. -/
structure TowerEdge where
  source : TowerVertex
  target : TowerVertex
deriving DecidableEq, Repr

/-- A finite vertex family lies on a common fibre. -/
def CommonFibre (vertices : Finset TowerVertex) : Prop :=
  ∃ fibre : Nat, ∀ v ∈ vertices, v.fibre = fibre

/-- A finite vertex family has one common optional terminal label. -/
def CommonTerminal (vertices : Finset TowerVertex) : Prop :=
  ∃ terminal : Option TerminalLabel, ∀ v ∈ vertices, v.terminal = terminal

/-- A transition map preserves terminal labels. -/
def TerminalLabelStable (step : TowerVertex -> Option TowerVertex) : Prop :=
  ∀ v w : TowerVertex, step v = some w -> w.terminal = v.terminal

/-- A transition map preserves common fibres. -/
def FibreStable (step : TowerVertex -> Option TowerVertex) : Prop :=
  ∀ v w : TowerVertex, step v = some w -> w.fibre = v.fibre

/-- A transition map strictly increases threshold layers. -/
def LayerIncreasing (step : TowerVertex -> Option TowerVertex) : Prop :=
  ∀ v w : TowerVertex, step v = some w -> v.layer < w.layer

/-- A transition map is single-valued on each source. -/
def DeterministicTransition (step : TowerVertex -> Option TowerVertex) : Prop :=
  ∀ v w₁ w₂ : TowerVertex, step v = some w₁ -> step v = some w₂ -> w₁ = w₂

theorem deterministicTransition_of_function (step : TowerVertex -> Option TowerVertex) :
    DeterministicTransition step := by
  intro v w₁ w₂ h₁ h₂
  rw [h₁] at h₂
  exact Option.some.inj h₂

theorem CommonFibre.mono_subset {s t : Finset TowerVertex}
    (ht : CommonFibre t) (hst : s ⊆ t) :
    CommonFibre s := by
  rcases ht with ⟨fibre, hfibre⟩
  exact ⟨fibre, fun v hv => hfibre v (hst hv)⟩

theorem commonFibre_empty : CommonFibre (∅ : Finset TowerVertex) := by
  exact ⟨0, by simp⟩

theorem commonFibre_singleton (v : TowerVertex) :
    CommonFibre ({v} : Finset TowerVertex) := by
  exact ⟨v.fibre, by simp⟩

theorem CommonTerminal.mono_subset {s t : Finset TowerVertex}
    (ht : CommonTerminal t) (hst : s ⊆ t) :
    CommonTerminal s := by
  rcases ht with ⟨terminal, hterminal⟩
  exact ⟨terminal, fun v hv => hterminal v (hst hv)⟩

theorem commonTerminal_empty : CommonTerminal (∅ : Finset TowerVertex) := by
  exact ⟨none, by simp⟩

theorem commonTerminal_singleton (v : TowerVertex) :
    CommonTerminal ({v} : Finset TowerVertex) := by
  exact ⟨v.terminal, by simp⟩

/-- One-step image of a finite vertex family under a partial tower transition. -/
def stepImage (step : TowerVertex -> Option TowerVertex)
    (vertices : Finset TowerVertex) : Finset TowerVertex :=
  vertices.biUnion fun v =>
    match step v with
    | some w => {w}
    | none => ∅

@[simp]
theorem stepImage_empty (step : TowerVertex -> Option TowerVertex) :
    stepImage step ∅ = ∅ := by
  simp [stepImage]

theorem mem_stepImage {step : TowerVertex -> Option TowerVertex}
    {vertices : Finset TowerVertex} {w : TowerVertex} :
    w ∈ stepImage step vertices ↔
      ∃ v ∈ vertices, step v = some w := by
  constructor
  · intro hw
    rcases mem_biUnion.1 hw with ⟨v, hv, hwv⟩
    cases hstep : step v with
    | none =>
        simp [hstep] at hwv
    | some u =>
        simp [hstep] at hwv
        exact ⟨v, hv, by simpa [hwv] using hstep⟩
  · intro hw
    rcases hw with ⟨v, hv, hstep⟩
    exact mem_biUnion.2 ⟨v, hv, by simp [hstep]⟩

theorem stepImage_card_le (step : TowerVertex -> Option TowerVertex)
    (vertices : Finset TowerVertex) :
    (stepImage step vertices).card <= vertices.card := by
  calc
    (stepImage step vertices).card
        <= ∑ v ∈ vertices,
            (match step v with | some w => ({w} : Finset TowerVertex) | none => ∅).card := by
          simpa [stepImage] using
            (card_biUnion_le (s := vertices)
              (t := fun v =>
                match step v with
                | some w => ({w} : Finset TowerVertex)
                | none => ∅))
    _ <= ∑ _v ∈ vertices, 1 := by
          exact sum_le_sum fun v _ => by
            cases step v <;> simp
    _ = vertices.card := by
          simp

theorem stepImage_mono {step : TowerVertex -> Option TowerVertex}
    {vertices₁ vertices₂ : Finset TowerVertex}
    (h : vertices₁ ⊆ vertices₂) :
    stepImage step vertices₁ ⊆ stepImage step vertices₂ := by
  intro w hw
  rcases mem_stepImage.1 hw with ⟨v, hv, hstep⟩
  exact mem_stepImage.2 ⟨v, h hv, hstep⟩

theorem CommonFibre.stepImage_of_fibreStable
    {step : TowerVertex -> Option TowerVertex}
    (hstable : FibreStable step) {vertices : Finset TowerVertex}
    (hcommon : CommonFibre vertices) :
    CommonFibre (stepImage step vertices) := by
  rcases hcommon with ⟨fibre, hfibre⟩
  refine ⟨fibre, ?_⟩
  intro w hw
  rcases mem_stepImage.1 hw with ⟨v, hv, hstep⟩
  exact (hstable v w hstep).trans (hfibre v hv)

theorem CommonTerminal.stepImage_of_terminalStable
    {step : TowerVertex -> Option TowerVertex}
    (hstable : TerminalLabelStable step) {vertices : Finset TowerVertex}
    (hcommon : CommonTerminal vertices) :
    CommonTerminal (stepImage step vertices) := by
  rcases hcommon with ⟨terminal, hterminal⟩
  refine ⟨terminal, ?_⟩
  intro w hw
  rcases mem_stepImage.1 hw with ⟨v, hv, hstep⟩
  exact (hstable v w hstep).trans (hterminal v hv)

/-- Iterating a partial deterministic tower transition. -/
def iterateStep? (step : TowerVertex -> Option TowerVertex) :
    Nat -> TowerVertex -> Option TowerVertex
  | 0, v => some v
  | n + 1, v => (iterateStep? step n v).bind step

@[simp]
theorem iterateStep?_zero (step : TowerVertex -> Option TowerVertex)
    (v : TowerVertex) :
    iterateStep? step 0 v = some v := rfl

theorem iterateStep?_succ (step : TowerVertex -> Option TowerVertex)
    (n : Nat) (v : TowerVertex) :
    iterateStep? step (n + 1) v = (iterateStep? step n v).bind step := rfl

/-- Image of a finite vertex family after `n` partial transition steps. -/
def iteratedImage (step : TowerVertex -> Option TowerVertex) (n : Nat)
    (vertices : Finset TowerVertex) : Finset TowerVertex :=
  vertices.biUnion fun v =>
    match iterateStep? step n v with
    | some w => {w}
    | none => ∅

@[simp]
theorem iteratedImage_empty (step : TowerVertex -> Option TowerVertex) (n : Nat) :
    iteratedImage step n ∅ = ∅ := by
  simp [iteratedImage]

theorem mem_iteratedImage {step : TowerVertex -> Option TowerVertex}
    {n : Nat} {vertices : Finset TowerVertex} {w : TowerVertex} :
    w ∈ iteratedImage step n vertices ↔
      ∃ v ∈ vertices, iterateStep? step n v = some w := by
  constructor
  · intro hw
    rcases mem_biUnion.1 hw with ⟨v, hv, hwv⟩
    cases hit : iterateStep? step n v with
    | none =>
        simp [hit] at hwv
    | some u =>
        simp [hit] at hwv
        exact ⟨v, hv, by simpa [hwv] using hit⟩
  · intro hw
    rcases hw with ⟨v, hv, hit⟩
    exact mem_biUnion.2 ⟨v, hv, by simp [hit]⟩

theorem iteratedImage_card_le (step : TowerVertex -> Option TowerVertex)
    (n : Nat) (vertices : Finset TowerVertex) :
    (iteratedImage step n vertices).card <= vertices.card := by
  calc
    (iteratedImage step n vertices).card
        <= ∑ v ∈ vertices,
            (match iterateStep? step n v with
              | some w => ({w} : Finset TowerVertex)
              | none => ∅).card := by
          simpa [iteratedImage] using
            (card_biUnion_le (s := vertices)
              (t := fun v =>
                match iterateStep? step n v with
                | some w => ({w} : Finset TowerVertex)
                | none => ∅))
    _ <= ∑ _v ∈ vertices, 1 := by
          exact sum_le_sum fun v _ => by
            cases iterateStep? step n v <;> simp
    _ = vertices.card := by
          simp

theorem iteratedImage_zero (step : TowerVertex -> Option TowerVertex)
    (vertices : Finset TowerVertex) :
    iteratedImage step 0 vertices = vertices := by
  ext w
  constructor
  · intro hw
    rcases mem_iteratedImage.1 hw with ⟨v, hv, hit⟩
    exact Option.some.inj hit ▸ hv
  · intro hw
    exact mem_iteratedImage.2 ⟨w, hw, rfl⟩

theorem iteratedImage_succ (step : TowerVertex -> Option TowerVertex)
    (n : Nat) (vertices : Finset TowerVertex) :
    iteratedImage step (n + 1) vertices =
      stepImage step (iteratedImage step n vertices) := by
  ext w
  constructor
  · intro hw
    rcases mem_iteratedImage.1 hw with ⟨v, hv, hit⟩
    rw [iterateStep?_succ] at hit
    cases hprev : iterateStep? step n v with
    | none =>
        simp [hprev] at hit
    | some u =>
        have hstep : step u = some w := by
          simpa [hprev] using hit
        exact mem_stepImage.2
          ⟨u, mem_iteratedImage.2 ⟨v, hv, hprev⟩, hstep⟩
  · intro hw
    rcases mem_stepImage.1 hw with ⟨u, hu, hstep⟩
    rcases mem_iteratedImage.1 hu with ⟨v, hv, hprev⟩
    exact mem_iteratedImage.2 ⟨v, hv, by simp [iterateStep?_succ, hprev, hstep]⟩

theorem iteratedImage_mono {step : TowerVertex -> Option TowerVertex}
    {n : Nat} {vertices₁ vertices₂ : Finset TowerVertex}
    (h : vertices₁ ⊆ vertices₂) :
    iteratedImage step n vertices₁ ⊆ iteratedImage step n vertices₂ := by
  intro w hw
  rcases mem_iteratedImage.1 hw with ⟨v, hv, hit⟩
  exact mem_iteratedImage.2 ⟨v, h hv, hit⟩

theorem TerminalLabelStable.iterate {step : TowerVertex -> Option TowerVertex}
    (hstable : TerminalLabelStable step) {n : Nat} {v w : TowerVertex}
    (hit : iterateStep? step n v = some w) :
    w.terminal = v.terminal := by
  induction n generalizing v w with
  | zero =>
      have hvw : v = w := Option.some.inj hit
      cases hvw
      rfl
  | succ n ih =>
      rw [iterateStep?_succ] at hit
      cases hprev : iterateStep? step n v with
      | none =>
          simp [hprev] at hit
      | some u =>
          have hstep : step u = some w := by
            simpa [hprev] using hit
          have hw_u := hstable u w hstep
          have hu_v := ih hprev
          exact hw_u.trans hu_v

theorem FibreStable.iterate {step : TowerVertex -> Option TowerVertex}
    (hstable : FibreStable step) {n : Nat} {v w : TowerVertex}
    (hit : iterateStep? step n v = some w) :
    w.fibre = v.fibre := by
  induction n generalizing v w with
  | zero =>
      have hvw : v = w := Option.some.inj hit
      cases hvw
      rfl
  | succ n ih =>
      rw [iterateStep?_succ] at hit
      cases hprev : iterateStep? step n v with
      | none =>
          simp [hprev] at hit
      | some u =>
          have hstep : step u = some w := by
            simpa [hprev] using hit
          have hw_u := hstable u w hstep
          have hu_v := ih hprev
          exact hw_u.trans hu_v

theorem CommonFibre.iteratedImage_of_fibreStable
    {step : TowerVertex -> Option TowerVertex}
    (hstable : FibreStable step) {n : Nat} {vertices : Finset TowerVertex}
    (hcommon : CommonFibre vertices) :
    CommonFibre (iteratedImage step n vertices) := by
  rcases hcommon with ⟨fibre, hfibre⟩
  refine ⟨fibre, ?_⟩
  intro w hw
  rcases mem_iteratedImage.1 hw with ⟨v, hv, hit⟩
  exact (hstable.iterate hit).trans (hfibre v hv)

theorem CommonTerminal.iteratedImage_of_terminalStable
    {step : TowerVertex -> Option TowerVertex}
    (hstable : TerminalLabelStable step) {n : Nat}
    {vertices : Finset TowerVertex}
    (hcommon : CommonTerminal vertices) :
    CommonTerminal (iteratedImage step n vertices) := by
  rcases hcommon with ⟨terminal, hterminal⟩
  refine ⟨terminal, ?_⟩
  intro w hw
  rcases mem_iteratedImage.1 hw with ⟨v, hv, hit⟩
  exact (hstable.iterate hit).trans (hterminal v hv)

theorem LayerIncreasing.iterate_succ_layer_lt
    {step : TowerVertex -> Option TowerVertex}
    (hinc : LayerIncreasing step) {n : Nat} {v w : TowerVertex}
    (hit : iterateStep? step (n + 1) v = some w) :
    v.layer < w.layer := by
  induction n generalizing v w with
  | zero =>
      rw [iterateStep?_succ] at hit
      have hstep : step v = some w := by
        simpa using hit
      exact hinc v w hstep
  | succ n ih =>
      rw [iterateStep?_succ] at hit
      cases hprev : iterateStep? step (n + 1) v with
      | none =>
          simp [hprev] at hit
      | some u =>
          have hstep : step u = some w := by
            simpa [hprev] using hit
          exact (ih hprev).trans (hinc u w hstep)

theorem LayerIncreasing.iterate_layer_le
    {step : TowerVertex -> Option TowerVertex}
    (hinc : LayerIncreasing step) {n : Nat} {v w : TowerVertex}
    (hit : iterateStep? step n v = some w) :
    v.layer <= w.layer := by
  cases n with
  | zero =>
      have hvw : v = w := Option.some.inj hit
      cases hvw
      rfl
  | succ n =>
      exact (hinc.iterate_succ_layer_lt hit).le

theorem LayerIncreasing.iterate_succ_ne
    {step : TowerVertex -> Option TowerVertex}
    (hinc : LayerIncreasing step) {n : Nat} {v w : TowerVertex}
    (hit : iterateStep? step (n + 1) v = some w) :
    w ≠ v := by
  intro hwv
  have hlt := hinc.iterate_succ_layer_lt hit
  rw [hwv] at hlt
  exact (lt_irrefl v.layer) hlt

theorem LayerIncreasing.no_nontrivial_return
    {step : TowerVertex -> Option TowerVertex}
    (hinc : LayerIncreasing step) {n : Nat} {v : TowerVertex}
    (hreturn : iterateStep? step (n + 1) v = some v) :
    False := by
  have hlt := hinc.iterate_succ_layer_lt hreturn
  exact (lt_irrefl v.layer) hlt

end

end Erdos260
