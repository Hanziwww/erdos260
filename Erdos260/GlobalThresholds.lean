import Mathlib
import Erdos260.CarryDataFactory
import Erdos260.CarryAllocation

/-!
# Global threshold bookkeeping

The manuscript repeatedly says that estimates hold for sufficiently large
dyadic shells.  This file packages those local lower bounds into one explicit
`Nat` threshold used by the global closure assembly.
-/

namespace Erdos260

noncomputable section

/-- Per-instance lower bounds for all local estimates used by the closure. -/
structure PerInstanceThresholds where
  carry : Nat
  chernoff : Nat
  cnl : Nat
  densePack : Nat
  tower : Nat
  highExcessCharge : Nat

/-- The single start threshold dominates all local thresholds. -/
def PerInstanceThresholds.startThreshold (T : PerInstanceThresholds) : Nat :=
  T.carry + T.chernoff + T.cnl + T.densePack + T.tower + T.highExcessCharge

theorem PerInstanceThresholds.carry_le_start (T : PerInstanceThresholds) :
    T.carry <= T.startThreshold := by
  unfold startThreshold
  omega

theorem PerInstanceThresholds.chernoff_le_start (T : PerInstanceThresholds) :
    T.chernoff <= T.startThreshold := by
  unfold startThreshold
  omega

theorem PerInstanceThresholds.cnl_le_start (T : PerInstanceThresholds) :
    T.cnl <= T.startThreshold := by
  unfold startThreshold
  omega

theorem PerInstanceThresholds.densePack_le_start (T : PerInstanceThresholds) :
    T.densePack <= T.startThreshold := by
  unfold startThreshold
  omega

theorem PerInstanceThresholds.tower_le_start (T : PerInstanceThresholds) :
    T.tower <= T.startThreshold := by
  unfold startThreshold
  omega

theorem PerInstanceThresholds.highExcessCharge_le_start (T : PerInstanceThresholds) :
    T.highExcessCharge <= T.startThreshold := by
  unfold startThreshold
  omega

/--
Global provider of per-instance thresholds.  Inhabiting this structure is the
place where all “large enough” choices are made compatible.
-/
structure GlobalThresholdData where
  constants : Erdos260Constants
  thresholds :
    ∀ (Q : Nat) (d : Nat -> Nat),
      0 < Q -> BinaryDigits d -> ¬ EventuallyZero d ->
      (∃ P : Int, realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ)) ->
        PerInstanceThresholds

def GlobalThresholdData.startThreshold
    (data : GlobalThresholdData)
    (Q : Nat) (d : Nat -> Nat)
    (hQ : 0 < Q) (hd : BinaryDigits d)
    (hnonterm : ¬ EventuallyZero d)
    (hrational :
      ∃ P : Int, realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ)) :
    Nat :=
  (data.thresholds Q d hQ hd hnonterm hrational).startThreshold

/-- Uniform per-instance thresholds: every local estimate uses the same bound
`n`.  Useful for a single global "sufficiently large `X`" choice once all local
thresholds are dominated by one value. -/
def PerInstanceThresholds.uniform (n : Nat) : PerInstanceThresholds where
  carry := n
  chernoff := n
  cnl := n
  densePack := n
  tower := n
  highExcessCharge := n

theorem PerInstanceThresholds.uniform_startThreshold (n : Nat) :
    (PerInstanceThresholds.uniform n).startThreshold = 6 * n := by
  simp only [PerInstanceThresholds.startThreshold, PerInstanceThresholds.uniform]
  ring

/-- The canonical threshold package used by the core global assembly interface.

The current provider layer supplies every per-shell datum for every failing
dyadic shell, so the threshold bookkeeping itself carries no remaining analytic
content.  We still package it explicitly to feed the older `GlobalAssemblyInputs`
interface and the final closure certificate. -/
def PerInstanceThresholds.zero : PerInstanceThresholds :=
  PerInstanceThresholds.uniform 0

@[simp] theorem PerInstanceThresholds.zero_startThreshold :
    PerInstanceThresholds.zero.startThreshold = 0 := by
  rw [PerInstanceThresholds.zero, PerInstanceThresholds.uniform_startThreshold]

/-- Canonical per-instance thresholds for the provider-strong assembly layer. -/
def canonicalThresholds :
    ∀ (Q : Nat) (d : Nat -> Nat),
      0 < Q -> BinaryDigits d -> ¬ EventuallyZero d ->
      (∃ P : Int, realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ)) ->
        PerInstanceThresholds :=
  fun _ _ _ _ _ _ => PerInstanceThresholds.zero

/-- Canonical global threshold provider, with the pinned manuscript constants. -/
def canonicalGlobalThresholdData : GlobalThresholdData where
  constants := erdos260Constants
  thresholds := canonicalThresholds

@[simp] theorem canonicalGlobalThresholdData_startThreshold
    (Q : Nat) (d : Nat -> Nat)
    (hQ : 0 < Q) (hd : BinaryDigits d)
    (hnonterm : ¬ EventuallyZero d)
    (hrational :
      ∃ P : Int, realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ)) :
    canonicalGlobalThresholdData.startThreshold Q d hQ hd hnonterm hrational = 0 := by
  simp [GlobalThresholdData.startThreshold, canonicalGlobalThresholdData,
    canonicalThresholds]

/-- Every local threshold of a `PerInstanceThresholds` is dominated by its single
`startThreshold`.  This is the combined "one global threshold suffices" fact. -/
theorem PerInstanceThresholds.all_le_start (T : PerInstanceThresholds) :
    T.carry <= T.startThreshold ∧ T.chernoff <= T.startThreshold ∧
      T.cnl <= T.startThreshold ∧ T.densePack <= T.startThreshold ∧
      T.tower <= T.startThreshold ∧ T.highExcessCharge <= T.startThreshold :=
  ⟨T.carry_le_start, T.chernoff_le_start, T.cnl_le_start, T.densePack_le_start,
    T.tower_le_start, T.highExcessCharge_le_start⟩

/-! ### Manuscript carry threshold -/

/--
`B(Q) = Nat.log 2 (Q * 4) + 1`: a constructive choice of `B` satisfying
`Q * 4 ≤ 2 ^ B(Q)`.
-/
def carryB (Q : Nat) : Nat := Nat.log 2 (Q * 4) + 1

theorem carryB_spec {Q : Nat} (_hQ : 0 < Q) : Q * 4 ≤ 2 ^ carryB Q := by
  unfold carryB
  have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (Q * 4)
  omega

/--
**Monotonicity bridge**: if a dyadic `X = 2 ^ L` exceeds the cardinal
carry threshold `carryThreshold B = 2 ^ (B + 6)`, then `L ≥ B + 6`.
-/
theorem L_ge_carryLogThreshold_of_X_ge {X L B : Nat}
    (hX : X = 2 ^ L) (h : carryThreshold B ≤ X) :
    carryLogThreshold B ≤ L := by
  unfold carryThreshold carryLogThreshold at *
  rw [hX] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h

end

end Erdos260
