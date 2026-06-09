import Mathlib
import Erdos260.Density
import Erdos260.AppendixK2_FineWilf
import Erdos260.GlobalChernoffAssembly
import Erdos260.GlobalCNLAssembly
import Erdos260.GlobalDensePackAssembly
import Erdos260.GlobalTowerAssembly

/-!
# Shell-grounded carry assembly

This module removes another layer of explicit carry bookkeeping from the
current strongest global interface.  The rational numerator `P`, dyadic exponent
`L`, shell positivity, and the canonical carry denominator exponent `B` are
recovered from the `FailingDyadicShell` itself.
-/

namespace Erdos260

open MeasureTheory

noncomputable section

/-- The first positive support position used as a per-instance largeness threshold. -/
def firstPositiveSupportThreshold
    (d : Nat -> Nat) (hd : BinaryDigits d) (hnonterm : Not (EventuallyZero d)) :
    Nat :=
  Classical.choose (nonterminating_of_not_eventuallyZero hd hnonterm 1)

theorem firstPositiveSupportThreshold_spec
    (d : Nat -> Nat) (hd : BinaryDigits d) (hnonterm : Not (EventuallyZero d)) :
    1 <= firstPositiveSupportThreshold d hd hnonterm /\
      d (firstPositiveSupportThreshold d hd hnonterm) = 1 := by
  exact Classical.choose_spec (nonterminating_of_not_eventuallyZero hd hnonterm 1)

/-- If `X` is beyond the first positive support threshold, then `[1, X]`
contains a support point. -/
theorem supportCount_pos_of_firstPositiveSupportThreshold_le
    {d : Nat -> Nat} {X : Nat}
    (hd : BinaryDigits d) (hnonterm : Not (EventuallyZero d))
    (hXge : firstPositiveSupportThreshold d hd hnonterm <= X) :
    1 <= supportCount d X := by
  have hspec := firstPositiveSupportThreshold_spec d hd hnonterm
  unfold supportCount
  exact Nat.succ_le_of_lt <| Finset.card_pos.mpr ⟨
    firstPositiveSupportThreshold d hd hnonterm, by
    rw [mem_supportIn]
    exact ⟨hspec.1, hXge, hspec.2⟩⟩

theorem erdos260Constants_cPr_le_half :
    erdos260Constants.cPr <= (1 / 2 : Real) := by
  rw [show erdos260Constants.cPr = manuscriptCpr by rfl, manuscriptCpr_eq_half]

theorem erdos260Constants_c0_le_kappa_div_sixteen :
    erdos260Constants.c0 <= manuscriptKappa / 16 := by
  change manuscriptC0 <= manuscriptKappa / 16
  exact manuscriptC0_le_kappa_div_sixteen

/--
Carry local data with shell-derived rational/dyadic bookkeeping.

Compared with `GroundedCarryLocalData`, this structure no longer asks for:
`P`, `L`, `B`, `hP`, `hX_eq`, `hX_pos`, or `hB`.  They are obtained from
`shell.hrational`, `shell.hXdyadic`, `dyadic_pos`, and `carryB_spec`.
-/
structure ShellGroundedCarryLocalData (shell : FailingDyadicShell) (cPr : Real) where
  r : Nat
  T : Real
  Y : Real
  hY : 0 <= Y
  hKr : r + 1 <= (supportShell shell.d shell.X).card
  h_supportCount_pos : 1 <= supportCount shell.d shell.X
  hAlloc :
    cPr * (shell.X : Real) * ((r : Real) + 1)
        + ((supportShell shell.d shell.X).card : Real) * Y
        + ((supportShell shell.d shell.X).card : Real) * T
        + ((r : Real) + 1) ^ 2 *
          (((Classical.choose shell.hXdyadic : Nat) : Real) +
            (carryB shell.Q : Real) + 1)
      <= ((r : Real) + 1) * (shell.X : Real)

/-- Expand shell-derived carry data to the existing grounded carry package. -/
def ShellGroundedCarryLocalData.toGroundedCarryLocalData
    {shell : FailingDyadicShell} {cPr : Real}
    (data : ShellGroundedCarryLocalData shell cPr) :
    GroundedCarryLocalData shell cPr where
  P := Classical.choose shell.hrational
  L := Classical.choose shell.hXdyadic
  B := carryB shell.Q
  r := data.r
  T := data.T
  Y := data.Y
  hY := data.hY
  hP := Classical.choose_spec shell.hrational
  hX_eq := Classical.choose_spec shell.hXdyadic
  hX_pos := Nat.succ_le_of_lt (dyadic_pos shell.hXdyadic)
  hB := carryB_spec shell.hQ
  hKr := data.hKr
  h_supportCount_pos := data.h_supportCount_pos
  hAlloc := data.hAlloc

/-- Build the carry package directly from shell-grounded carry data. -/
def ShellGroundedCarryLocalData.toCarryData
    {shell : FailingDyadicShell} {cPr : Real}
    (data : ShellGroundedCarryLocalData shell cPr) :
    CarryDataFromFailure shell cPr :=
  data.toGroundedCarryLocalData.toCarryData

/--
Shell carry data whose support-count start condition is supplied by the global
largeness threshold rather than by the carry provider.
-/
structure ThresholdShellGroundedCarryLocalData (shell : FailingDyadicShell)
    (cPr : Real) where
  r : Nat
  T : Real
  Y : Real
  hY : 0 <= Y
  hKr : r + 1 <= (supportShell shell.d shell.X).card
  hAlloc :
    cPr * (shell.X : Real) * ((r : Real) + 1)
        + ((supportShell shell.d shell.X).card : Real) * Y
        + ((supportShell shell.d shell.X).card : Real) * T
        + ((r : Real) + 1) ^ 2 *
          (((Classical.choose shell.hXdyadic : Nat) : Real) +
            (carryB shell.Q : Real) + 1)
      <= ((r : Real) + 1) * (shell.X : Real)

/-- Reinsert the support-count fact once the global threshold has provided it. -/
def ThresholdShellGroundedCarryLocalData.toShellGroundedCarryLocalData
    {shell : FailingDyadicShell} {cPr : Real}
    (data : ThresholdShellGroundedCarryLocalData shell cPr)
    (h_supportCount_pos : 1 <= supportCount shell.d shell.X) :
    ShellGroundedCarryLocalData shell cPr where
  r := data.r
  T := data.T
  Y := data.Y
  hY := data.hY
  hKr := data.hKr
  h_supportCount_pos := h_supportCount_pos
  hAlloc := data.hAlloc

/-- Expand threshold-shell carry data to the grounded carry package. -/
def ThresholdShellGroundedCarryLocalData.toGroundedCarryLocalData
    {shell : FailingDyadicShell} {cPr : Real}
    (data : ThresholdShellGroundedCarryLocalData shell cPr)
    (h_supportCount_pos : 1 <= supportCount shell.d shell.X) :
    GroundedCarryLocalData shell cPr :=
  (data.toShellGroundedCarryLocalData h_supportCount_pos).toGroundedCarryLocalData

/-- Build carry data after the global threshold supplies the support-count fact. -/
def ThresholdShellGroundedCarryLocalData.toCarryData
    {shell : FailingDyadicShell} {cPr : Real}
    (data : ThresholdShellGroundedCarryLocalData shell cPr)
    (h_supportCount_pos : 1 <= supportCount shell.d shell.X) :
    CarryDataFromFailure shell cPr :=
  (data.toGroundedCarryLocalData h_supportCount_pos).toCarryData

/--
Threshold-shell carry data whose allocation inequality is stated in the
manuscript K.4 form after replacing the shell count `K` by the failure bound
`K <= c_Q X`.
-/
structure FailureBoundedThresholdShellGroundedCarryLocalData
    (shell : FailingDyadicShell) (cPr : Real) where
  r : Nat
  T : Real
  Y : Real
  hY : 0 <= Y
  hT : 0 <= T
  hKr : r + 1 <= (supportShell shell.d shell.X).card
  hDominate :
    cPr * (shell.X : Real) * ((r : Real) + 1)
        + shell.cQ * (shell.X : Real) * (Y + T)
        + ((r : Real) + 1) ^ 2 *
          (((Classical.choose shell.hXdyadic : Nat) : Real) +
            (carryB shell.Q : Real) + 1)
      <= ((r : Real) + 1) * (shell.X : Real)

/-- Recover the raw `hAlloc` field from the shell failure bound. -/
def FailureBoundedThresholdShellGroundedCarryLocalData.toThresholdShellGroundedCarryLocalData
    {shell : FailingDyadicShell} {cPr : Real}
    (data : FailureBoundedThresholdShellGroundedCarryLocalData shell cPr) :
    ThresholdShellGroundedCarryLocalData shell cPr where
  r := data.r
  T := data.T
  Y := data.Y
  hY := data.hY
  hKr := data.hKr
  hAlloc :=
    hAlloc_from_kBound
      (X := shell.X)
      (K := (supportShell shell.d shell.X).card)
      (L := Classical.choose shell.hXdyadic)
      (B := carryB shell.Q)
      (r := data.r)
      (T := data.T)
      (Y := data.Y)
      (cPr := cPr)
      (cQ := shell.cQ)
      data.hY data.hT
      (le_of_lt shell.hfailure_cQ)
      data.hDominate

/-- Expand failure-bounded threshold-shell data to the grounded carry package. -/
def FailureBoundedThresholdShellGroundedCarryLocalData.toGroundedCarryLocalData
    {shell : FailingDyadicShell} {cPr : Real}
    (data : FailureBoundedThresholdShellGroundedCarryLocalData shell cPr)
    (h_supportCount_pos : 1 <= supportCount shell.d shell.X) :
    GroundedCarryLocalData shell cPr :=
  data.toThresholdShellGroundedCarryLocalData.toGroundedCarryLocalData h_supportCount_pos

/-- Build carry data from the failure-bounded threshold-shell allocation form. -/
def FailureBoundedThresholdShellGroundedCarryLocalData.toCarryData
    {shell : FailingDyadicShell} {cPr : Real}
    (data : FailureBoundedThresholdShellGroundedCarryLocalData shell cPr)
    (h_supportCount_pos : 1 <= supportCount shell.d shell.X) :
    CarryDataFromFailure shell cPr :=
  (data.toGroundedCarryLocalData h_supportCount_pos).toCarryData

/--
Strict proof-v4 failure-bounded carry data: the allocation dominate inequality
uses the manuscript failure constant `c_0`, not the weaker density constant
`c_Q`.
-/
structure StrictFailureBoundedThresholdShellGroundedCarryLocalData
    (shell : FailingDyadicShell) (cPr : Real) where
  r : Nat
  T : Real
  Y : Real
  hY : 0 <= Y
  hT : 0 <= T
  hKr : r + 1 <= (supportShell shell.d shell.X).card
  hDominate :
    cPr * (shell.X : Real) * ((r : Real) + 1)
        + shell.c0 * (shell.X : Real) * (Y + T)
        + ((r : Real) + 1) ^ 2 *
          (((Classical.choose shell.hXdyadic : Nat) : Real) +
            (carryB shell.Q : Real) + 1)
      <= ((r : Real) + 1) * (shell.X : Real)

/-- Recover the raw `hAlloc` field from the strict failure bound `K < c_0 X`. -/
def StrictFailureBoundedThresholdShellGroundedCarryLocalData.toThresholdShellGroundedCarryLocalData
    {shell : FailingDyadicShell} {cPr : Real}
    (data : StrictFailureBoundedThresholdShellGroundedCarryLocalData shell cPr) :
    ThresholdShellGroundedCarryLocalData shell cPr where
  r := data.r
  T := data.T
  Y := data.Y
  hY := data.hY
  hKr := data.hKr
  hAlloc :=
    hAlloc_from_kBound
      (X := shell.X)
      (K := (supportShell shell.d shell.X).card)
      (L := Classical.choose shell.hXdyadic)
      (B := carryB shell.Q)
      (r := data.r)
      (T := data.T)
      (Y := data.Y)
      (cPr := cPr)
      (cQ := shell.c0)
      data.hY data.hT
      (le_of_lt shell.hfailure)
      data.hDominate

/-- Expand strict-failure-bounded threshold-shell data to grounded carry data. -/
def StrictFailureBoundedThresholdShellGroundedCarryLocalData.toGroundedCarryLocalData
    {shell : FailingDyadicShell} {cPr : Real}
    (data : StrictFailureBoundedThresholdShellGroundedCarryLocalData shell cPr)
    (h_supportCount_pos : 1 <= supportCount shell.d shell.X) :
    GroundedCarryLocalData shell cPr :=
  data.toThresholdShellGroundedCarryLocalData.toGroundedCarryLocalData h_supportCount_pos

/-- Build carry data from the strict-failure allocation form. -/
def StrictFailureBoundedThresholdShellGroundedCarryLocalData.toCarryData
    {shell : FailingDyadicShell} {cPr : Real}
    (data : StrictFailureBoundedThresholdShellGroundedCarryLocalData shell cPr)
    (h_supportCount_pos : 1 <= supportCount shell.d shell.X) :
    CarryDataFromFailure shell cPr :=
  CarryDataFromFailure.ofShellAndSupportCountFailureBound shell cPr
    (Classical.choose shell.hrational)
    (Classical.choose shell.hXdyadic)
    (carryB shell.Q)
    data.r data.T data.Y
    data.hY
    (Classical.choose_spec shell.hrational)
    (Classical.choose_spec shell.hXdyadic)
    (Nat.succ_le_of_lt (dyadic_pos shell.hXdyadic))
    (carryB_spec shell.hQ)
    data.hKr
    h_supportCount_pos
    (by
      have hKT :
          ((supportShell shell.d shell.X).card : Real) * data.T <=
            shell.c0 * (shell.X : Real) * data.T := by
        exact mul_le_mul_of_nonneg_right (le_of_lt shell.hfailure) data.hT
      have hDom := data.hDominate
      ring_nf at hDom ⊢
      nlinarith)

/--
Budgeted strict carry data.  This exposes the two K.4 payments used in
proof-v4 separately: the threshold term and the boundary gap-error term.
-/
structure BudgetedStrictFailureBoundedThresholdShellGroundedCarryLocalData
    (shell : FailingDyadicShell) (cPr : Real) where
  r : Nat
  T : Real
  Y : Real
  hY : 0 <= Y
  hT : 0 <= T
  hKr : r + 1 <= (supportShell shell.d shell.X).card
  hThresholdBudget :
    shell.c0 * (shell.X : Real) * (Y + T) <=
      ((r : Real) + 1) * (shell.X : Real) / 4
  hErrorBudget :
    ((r : Real) + 1) ^ 2 *
      (((Classical.choose shell.hXdyadic : Nat) : Real) +
        (carryB shell.Q : Real) + 1)
      <= ((r : Real) + 1) * (shell.X : Real) / 4

/-- Combine the two K.4 budget inequalities into the strict dominate form. -/
def BudgetedStrictFailureBoundedThresholdShellGroundedCarryLocalData.toStrictFailureBoundedThresholdShellGroundedCarryLocalData
    {shell : FailingDyadicShell} {cPr : Real}
    (data :
      BudgetedStrictFailureBoundedThresholdShellGroundedCarryLocalData shell cPr)
    (hcPr : cPr <= (1 / 2 : Real)) :
    StrictFailureBoundedThresholdShellGroundedCarryLocalData shell cPr where
  r := data.r
  T := data.T
  Y := data.Y
  hY := data.hY
  hT := data.hT
  hKr := data.hKr
  hDominate :=
    hDominate_from_threshold_and_error_budget
      (X := shell.X)
      (L := Classical.choose shell.hXdyadic)
      (B := carryB shell.Q)
      (r := data.r)
      (T := data.T)
      (Y := data.Y)
      (cPr := cPr)
      (c0 := shell.c0)
      hcPr data.hThresholdBudget data.hErrorBudget

/-- Expand budgeted strict carry data to grounded carry data. -/
def BudgetedStrictFailureBoundedThresholdShellGroundedCarryLocalData.toGroundedCarryLocalData
    {shell : FailingDyadicShell} {cPr : Real}
    (data :
      BudgetedStrictFailureBoundedThresholdShellGroundedCarryLocalData shell cPr)
    (hcPr : cPr <= (1 / 2 : Real))
    (h_supportCount_pos : 1 <= supportCount shell.d shell.X) :
    GroundedCarryLocalData shell cPr :=
  StrictFailureBoundedThresholdShellGroundedCarryLocalData.toGroundedCarryLocalData
    (data.toStrictFailureBoundedThresholdShellGroundedCarryLocalData hcPr)
    h_supportCount_pos

/-- Build carry data from the two-budget strict failure allocation form. -/
def BudgetedStrictFailureBoundedThresholdShellGroundedCarryLocalData.toCarryData
    {shell : FailingDyadicShell} {cPr : Real}
    (data :
      BudgetedStrictFailureBoundedThresholdShellGroundedCarryLocalData shell cPr)
    (hcPr : cPr <= (1 / 2 : Real))
    (h_supportCount_pos : 1 <= supportCount shell.d shell.X) :
    CarryDataFromFailure shell cPr :=
  (data.toStrictFailureBoundedThresholdShellGroundedCarryLocalData hcPr).toCarryData
    h_supportCount_pos

/--
Strict carry data with the boundary gap-error budget derived from the dyadic
largeness condition `B + 25 <= L`.
-/
structure ErrorBudgetedStrictFailureBoundedThresholdShellGroundedCarryLocalData
    (shell : FailingDyadicShell) (cPr : Real) where
  r : Nat
  T : Real
  Y : Real
  hY : 0 <= Y
  hT : 0 <= T
  hKr : r + 1 <= (supportShell shell.d shell.X).card
  hRleL : r <= Classical.choose shell.hXdyadic
  hCarryLarge : carryB shell.Q + 25 <= Classical.choose shell.hXdyadic
  hThresholdBudget :
    shell.c0 * (shell.X : Real) * (Y + T) <=
      ((r : Real) + 1) * (shell.X : Real) / 4

/-- Recover the two-budget strict carry form by proving the gap-error budget. -/
def ErrorBudgetedStrictFailureBoundedThresholdShellGroundedCarryLocalData.toBudgetedStrictFailureBoundedThresholdShellGroundedCarryLocalData
    {shell : FailingDyadicShell} {cPr : Real}
    (data :
      ErrorBudgetedStrictFailureBoundedThresholdShellGroundedCarryLocalData shell cPr) :
    BudgetedStrictFailureBoundedThresholdShellGroundedCarryLocalData shell cPr where
  r := data.r
  T := data.T
  Y := data.Y
  hY := data.hY
  hT := data.hT
  hKr := data.hKr
  hThresholdBudget := data.hThresholdBudget
  hErrorBudget :=
    hErrorBudget_from_carry_growth
      (X := shell.X)
      (L := Classical.choose shell.hXdyadic)
      (B := carryB shell.Q)
      (r := data.r)
      (Classical.choose_spec shell.hXdyadic)
      data.hRleL
      data.hCarryLarge

/-- Expand error-budgeted strict carry data to grounded carry data. -/
def ErrorBudgetedStrictFailureBoundedThresholdShellGroundedCarryLocalData.toGroundedCarryLocalData
    {shell : FailingDyadicShell} {cPr : Real}
    (data :
      ErrorBudgetedStrictFailureBoundedThresholdShellGroundedCarryLocalData shell cPr)
    (hcPr : cPr <= (1 / 2 : Real))
    (h_supportCount_pos : 1 <= supportCount shell.d shell.X) :
    GroundedCarryLocalData shell cPr :=
  BudgetedStrictFailureBoundedThresholdShellGroundedCarryLocalData.toGroundedCarryLocalData
    data.toBudgetedStrictFailureBoundedThresholdShellGroundedCarryLocalData
    hcPr h_supportCount_pos

/-- Build carry data after deriving the gap-error budget from large `L`. -/
def ErrorBudgetedStrictFailureBoundedThresholdShellGroundedCarryLocalData.toCarryData
    {shell : FailingDyadicShell} {cPr : Real}
    (data :
      ErrorBudgetedStrictFailureBoundedThresholdShellGroundedCarryLocalData shell cPr)
    (hcPr : cPr <= (1 / 2 : Real))
    (h_supportCount_pos : 1 <= supportCount shell.d shell.X) :
    CarryDataFromFailure shell cPr :=
  data.toBudgetedStrictFailureBoundedThresholdShellGroundedCarryLocalData.toCarryData
    hcPr h_supportCount_pos

/--
Carry data with the threshold budget derived from the K.4 scale inequalities
`Y + T <= 4L` and `κL <= r+1`.
-/
structure ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
    (shell : FailingDyadicShell) (cPr : Real) where
  r : Nat
  T : Real
  Y : Real
  hY : 0 <= Y
  hT : 0 <= T
  hKr : r + 1 <= (supportShell shell.d shell.X).card
  hRleL : r <= Classical.choose shell.hXdyadic
  hCarryLarge : carryB shell.Q + 25 <= Classical.choose shell.hXdyadic
  hYT :
    Y + T <= 4 * ((Classical.choose shell.hXdyadic : Nat) : Real)
  hOrder :
    manuscriptKappa * ((Classical.choose shell.hXdyadic : Nat) : Real) <=
      (r : Real) + 1

/-- Recover the error-budgeted form by proving the threshold budget. -/
def ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData.toErrorBudgetedStrictFailureBoundedThresholdShellGroundedCarryLocalData
    {shell : FailingDyadicShell} {cPr : Real}
    (data :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell cPr)
    (hc0Small : shell.c0 <= manuscriptKappa / 16) :
    ErrorBudgetedStrictFailureBoundedThresholdShellGroundedCarryLocalData
      shell cPr where
  r := data.r
  T := data.T
  Y := data.Y
  hY := data.hY
  hT := data.hT
  hKr := data.hKr
  hRleL := data.hRleL
  hCarryLarge := data.hCarryLarge
  hThresholdBudget := by
    exact hThresholdBudget_from_kappa_floor
      (X := shell.X)
      (L := Classical.choose shell.hXdyadic)
      (r := data.r)
      (Y := data.Y)
      (T := data.T)
      (c0 := shell.c0)
      (kappa := manuscriptKappa)
      (le_of_lt manuscriptKappa_pos)
      hc0Small
      (by linarith [data.hY, data.hT])
      data.hYT
      data.hOrder

/-- Expand threshold-controlled strict carry data to grounded carry data. -/
def ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData.toGroundedCarryLocalData
    {shell : FailingDyadicShell} {cPr : Real}
    (data :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell cPr)
    (hcPr : cPr <= (1 / 2 : Real))
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (h_supportCount_pos : 1 <= supportCount shell.d shell.X) :
    GroundedCarryLocalData shell cPr :=
  ErrorBudgetedStrictFailureBoundedThresholdShellGroundedCarryLocalData.toGroundedCarryLocalData
    (data.toErrorBudgetedStrictFailureBoundedThresholdShellGroundedCarryLocalData
      hc0Small)
    hcPr h_supportCount_pos

/-- Build carry data after deriving both K.4 budget inequalities. -/
def ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData.toCarryData
    {shell : FailingDyadicShell} {cPr : Real}
    (data :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell cPr)
    (hcPr : cPr <= (1 / 2 : Real))
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (h_supportCount_pos : 1 <= supportCount shell.d shell.X) :
    CarryDataFromFailure shell cPr :=
  (data.toErrorBudgetedStrictFailureBoundedThresholdShellGroundedCarryLocalData
    hc0Small).toCarryData hcPr h_supportCount_pos

/-- Proof-v4 positive-density order `r = floor(kappa L)`. -/
def proofV4CarryOrder (shell : FailingDyadicShell) : Nat :=
  Nat.floor
    (manuscriptKappa * ((Classical.choose shell.hXdyadic : Nat) : Real))

/-- Since `kappa < 1`, the manuscript order `floor(kappa L)` is at most `L`. -/
theorem proofV4CarryOrder_le_L (shell : FailingDyadicShell) :
    proofV4CarryOrder shell <= Classical.choose shell.hXdyadic := by
  unfold proofV4CarryOrder
  refine Nat.floor_le_of_le ?_
  have hLnonneg : 0 <= ((Classical.choose shell.hXdyadic : Nat) : Real) := by
    exact_mod_cast Nat.zero_le (Classical.choose shell.hXdyadic)
  have hk : manuscriptKappa <= 1 := le_of_lt manuscriptKappa_lt_one
  calc
    manuscriptKappa * ((Classical.choose shell.hXdyadic : Nat) : Real)
        <= 1 * ((Classical.choose shell.hXdyadic : Nat) : Real) := by
          exact mul_le_mul_of_nonneg_right hk hLnonneg
    _ = ((Classical.choose shell.hXdyadic : Nat) : Real) := by ring

/-- The floor order satisfies the K.4 budget inequality `kappa L <= r+1`. -/
theorem proofV4CarryOrder_order (shell : FailingDyadicShell) :
    manuscriptKappa * ((Classical.choose shell.hXdyadic : Nat) : Real) <=
      (proofV4CarryOrder shell : Real) + 1 := by
  have hlt :
      manuscriptKappa * ((Classical.choose shell.hXdyadic : Nat) : Real) <
        (proofV4CarryOrder shell : Real) + 1 := by
    unfold proofV4CarryOrder
    exact Nat.lt_floor_add_one
      (manuscriptKappa * ((Classical.choose shell.hXdyadic : Nat) : Real))
  exact le_of_lt hlt

/--
Proof-v4 K.4 carry input with the order normalized to the manuscript choice
`r = floor(kappa L)`.
-/
structure ManuscriptThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
    (shell : FailingDyadicShell) (cPr : Real) where
  T : Real
  Y : Real
  hY : 0 <= Y
  hT : 0 <= T
  hKr : proofV4CarryOrder shell + 1 <= (supportShell shell.d shell.X).card
  hCarryLarge : carryB shell.Q + 25 <= Classical.choose shell.hXdyadic
  hYT :
    Y + T <= 4 * ((Classical.choose shell.hXdyadic : Nat) : Real)

/--
Forget the manuscript floor normalization and recover the threshold-controlled
carry package used by the existing carry pipeline.
-/
def ManuscriptThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData.toThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
    {shell : FailingDyadicShell} {cPr : Real}
    (data :
      ManuscriptThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell cPr) :
    ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
      shell cPr where
  r := proofV4CarryOrder shell
  T := data.T
  Y := data.Y
  hY := data.hY
  hT := data.hT
  hKr := data.hKr
  hRleL := proofV4CarryOrder_le_L shell
  hCarryLarge := data.hCarryLarge
  hYT := data.hYT
  hOrder := proofV4CarryOrder_order shell

/--
Proof-v4 K.4 active carry budget range.  The threshold height `T` and active
floor `Y` are nonnegative by type, and the K.4 allocation proof only needs the
combined short-range bound `Y + T <= 4L`.
-/
structure ManuscriptCarryActiveBudgetData (shell : FailingDyadicShell) where
  T : {T : Real // 0 <= T}
  Y : {Y : Real // 0 <= Y}
  hYT :
    (Y : Real) + (T : Real) <=
      4 * ((Classical.choose shell.hXdyadic : Nat) : Real)

namespace ManuscriptCarryActiveBudgetData

def TReal {shell : FailingDyadicShell}
    (data : ManuscriptCarryActiveBudgetData shell) : Real :=
  data.T

def YReal {shell : FailingDyadicShell}
    (data : ManuscriptCarryActiveBudgetData shell) : Real :=
  data.Y

theorem hT {shell : FailingDyadicShell}
    (data : ManuscriptCarryActiveBudgetData shell) :
    0 <= data.TReal :=
  data.T.property

theorem hY {shell : FailingDyadicShell}
    (data : ManuscriptCarryActiveBudgetData shell) :
    0 <= data.YReal :=
  data.Y.property

theorem range {shell : FailingDyadicShell}
    (data : ManuscriptCarryActiveBudgetData shell) :
    data.YReal + data.TReal <=
      4 * ((Classical.choose shell.hXdyadic : Nat) : Real) :=
  data.hYT

/-- Proof-v4 first active threshold `T₀ = 2L + C_Q`. -/
def proofV4FirstActiveThreshold (shell : FailingDyadicShell) : Real :=
  2 * ((Classical.choose shell.hXdyadic : Nat) : Real) +
    ((manuscriptCQ_T : Nat) : Real)

/-- Proof-v4 first active excess floor `Y = εL`. -/
def proofV4FirstActiveExcess (shell : FailingDyadicShell) : Real :=
  manuscriptEps * ((Classical.choose shell.hXdyadic : Nat) : Real)

theorem proofV4FirstActiveThreshold_nonneg (shell : FailingDyadicShell) :
    0 <= proofV4FirstActiveThreshold shell := by
  unfold proofV4FirstActiveThreshold
  positivity

theorem proofV4FirstActiveExcess_nonneg (shell : FailingDyadicShell) :
    0 <= proofV4FirstActiveExcess shell := by
  unfold proofV4FirstActiveExcess
  exact mul_nonneg (le_of_lt manuscriptEps_pos)
    (by exact_mod_cast Nat.zero_le (Classical.choose shell.hXdyadic))

/--
The proof-v4 first-layer active range is short: `εL + (2L+C_Q) <= 4L`.
The large-carry threshold supplies the harmless `L >= 1` needed to absorb
the pinned `C_Q = 1`.
-/
theorem proofV4FirstActiveBudget_range {shell : FailingDyadicShell}
    (hCarryLarge : carryB shell.Q + 25 <= Classical.choose shell.hXdyadic) :
    proofV4FirstActiveExcess shell + proofV4FirstActiveThreshold shell <=
      4 * ((Classical.choose shell.hXdyadic : Nat) : Real) := by
  have hLge : (1 : Nat) <= Classical.choose shell.hXdyadic := by
    omega
  have hLgeReal : (1 : Real) <=
      ((Classical.choose shell.hXdyadic : Nat) : Real) := by
    exact_mod_cast hLge
  unfold proofV4FirstActiveExcess proofV4FirstActiveThreshold
  unfold manuscriptEps manuscriptCQ_T
  nlinarith

/-- Canonical proof-v4 first-layer active carry budget. -/
def ofProofV4FirstLayer {shell : FailingDyadicShell}
    (hCarryLarge : carryB shell.Q + 25 <= Classical.choose shell.hXdyadic) :
    ManuscriptCarryActiveBudgetData shell where
  T := ⟨proofV4FirstActiveThreshold shell,
    proofV4FirstActiveThreshold_nonneg shell⟩
  Y := ⟨proofV4FirstActiveExcess shell,
    proofV4FirstActiveExcess_nonneg shell⟩
  hYT := proofV4FirstActiveBudget_range hCarryLarge

end ManuscriptCarryActiveBudgetData

/--
Proof-v4 K.4 support supply at the manuscript carry order
`r = floor(kappa L)`.  This is the positive-density input needed to take the
first `r+1` shell hits; it is kept separate from the active `T,Y` budget.
-/
structure ManuscriptCarrySupportSupplyData (shell : FailingDyadicShell) where
  hKr : proofV4CarryOrder shell + 1 <= (supportShell shell.d shell.X).card

/--
The remaining proof-v4 K.4 carry scale data once floor arithmetic and the
large-shell inequality `B(Q)+25 <= L` are supplied by global theorems.
-/
structure ManuscriptCarryScaleInputData (shell : FailingDyadicShell) where
  budget : ManuscriptCarryActiveBudgetData shell
  support : ManuscriptCarrySupportSupplyData shell

/-- Add the large-shell inequality to recover the manuscript floor carry input. -/
def ManuscriptCarryScaleInputData.toManuscriptThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
    {shell : FailingDyadicShell} {cPr : Real}
    (data : ManuscriptCarryScaleInputData shell)
    (hCarryLarge : carryB shell.Q + 25 <= Classical.choose shell.hXdyadic) :
    ManuscriptThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
      shell cPr where
  T := data.budget.TReal
  Y := data.budget.YReal
  hY := data.budget.hY
  hT := data.budget.hT
  hKr := data.support.hKr
  hCarryLarge := hCarryLarge
  hYT := data.budget.range

/-- Add the large-shell inequality and project directly to the carry pipeline. -/
def ManuscriptCarryScaleInputData.toThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
    {shell : FailingDyadicShell} {cPr : Real}
    (data : ManuscriptCarryScaleInputData shell)
    (hCarryLarge : carryB shell.Q + 25 <= Classical.choose shell.hXdyadic) :
    ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
      shell cPr :=
  (data.toManuscriptThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
    hCarryLarge).toThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData

namespace ManuscriptCarrySupportSupplyData

/--
The manuscript carry order is bounded by the dyadic exponent, including the
successor needed by the `r + 1` support-window condition.
-/
theorem proofV4CarryOrder_add_one_le_L_add_one (shell : FailingDyadicShell) :
    proofV4CarryOrder shell + 1 <= Classical.choose shell.hXdyadic + 1 := by
  exact Nat.succ_le_succ (proofV4CarryOrder_le_L shell)

/--
If the positive shell-density lower bound covers `L + 1`, then it covers the
manuscript carry order `floor(kappa L) + 1`.
-/
theorem orderCovered_of_L_add_one
    {shell : FailingDyadicShell} {c : Real}
    (hL :
      ((Classical.choose shell.hXdyadic + 1 : Nat) : Real) <=
        c * (shell.X : Real)) :
    ((proofV4CarryOrder shell + 1 : Nat) : Real) <=
      c * (shell.X : Real) := by
  have hNat := proofV4CarryOrder_add_one_le_L_add_one shell
  have hReal :
      ((proofV4CarryOrder shell + 1 : Nat) : Real) <=
        ((Classical.choose shell.hXdyadic + 1 : Nat) : Real) := by
    exact_mod_cast hNat
  exact hReal.trans hL

/--
The elementary growth fact needed by the density-to-carry bridge:
`(L+1)/2^L -> 0`.
-/
theorem tendsto_L_add_one_div_two_pow :
    Filter.Tendsto
      (fun L : Nat => (((L + 1 : Nat) : Real) / ((2 : Real) ^ L)))
      Filter.atTop (nhds 0) := by
  have hshift :
      Filter.Tendsto
        (fun L : Nat => (((L + 1 : Nat) : Real) / ((2 : Real) ^ (L + 1))))
        Filter.atTop (nhds 0) := by
    convert
      (tendsto_pow_const_div_const_pow_of_one_lt 1
          (r := (2 : Real)) one_lt_two).comp
        (Filter.tendsto_add_atTop_nat 1) using 1
    ext L
    simp
  have hscaled := hshift.const_mul (2 : Real)
  convert hscaled using 1
  ext L
  rw [pow_succ]
  field_simp
  ring_nf

/--
For every positive density constant `c`, sufficiently large dyadic exponents
satisfy `L+1 <= c * 2^L`.
-/
theorem exists_orderCoverageLogThreshold (c : Real) (hc : 0 < c) :
    ∃ L0 : Nat, ∀ L : Nat, L0 <= L ->
      (((L + 1 : Nat) : Real) <= c * (((2 ^ L : Nat) : Real))) := by
  have heventually :
      ∀ᶠ L : Nat in Filter.atTop,
        (((L + 1 : Nat) : Real) / ((2 : Real) ^ L) < c) :=
    (tendsto_order.1 tendsto_L_add_one_div_two_pow).2 c hc
  rcases Filter.eventually_atTop.1 heventually with ⟨L0, hL0⟩
  refine ⟨L0, ?_⟩
  intro L hL
  have hlt := hL0 L hL
  have hpowpos : 0 < ((2 : Real) ^ L) := pow_pos (by norm_num) L
  have hmul :
      (((L + 1 : Nat) : Real) < c * ((2 : Real) ^ L)) := by
    exact (div_lt_iff₀ hpowpos).mp hlt
  have hcast : (((2 ^ L : Nat) : Real)) = (2 : Real) ^ L := by
    exact Nat.cast_pow 2 L
  exact le_of_lt (by simpa [hcast] using hmul)

/-- A chosen dyadic-exponent threshold for `L+1 <= c * 2^L`. -/
def orderCoverageLogThreshold (c : Real) (hc : 0 < c) : Nat :=
  Classical.choose (exists_orderCoverageLogThreshold c hc)

theorem orderCovered_of_orderCoverageLogThreshold
    {shell : FailingDyadicShell} {c : Real} (hc : 0 < c)
    (hL :
      orderCoverageLogThreshold c hc <=
        Classical.choose shell.hXdyadic) :
    ((proofV4CarryOrder shell + 1 : Nat) : Real) <=
      c * (shell.X : Real) := by
  have hcoverL :=
    Classical.choose_spec (exists_orderCoverageLogThreshold c hc)
      (Classical.choose shell.hXdyadic) hL
  have hX :
      (((2 ^ Classical.choose shell.hXdyadic : Nat) : Real)) =
        (shell.X : Real) := by
    exact_mod_cast (Classical.choose_spec shell.hXdyadic).symm
  exact orderCovered_of_L_add_one (shell := shell) (c := c)
    (by simpa [hX] using hcoverL)

/-- The K.4 large-carry dyadic threshold makes the finite rational-gap window
fit inside one dyadic shell. -/
theorem proofV4CarryWindowLength_le_of_carryLarge
    {shell : FailingDyadicShell}
    (hCarryLarge : carryB shell.Q + 25 <= Classical.choose shell.hXdyadic) :
    (proofV4CarryOrder shell + 1) *
        (Classical.choose shell.hXdyadic + carryB shell.Q + 1) <= shell.X := by
  let L := Classical.choose shell.hXdyadic
  let B := carryB shell.Q
  have hr : proofV4CarryOrder shell <= L := by
    simpa [L] using proofV4CarryOrder_le_L shell
  have hErr :=
    hErrorBudget_from_carry_growth
      (X := shell.X)
      (L := L)
      (B := B)
      (r := proofV4CarryOrder shell)
      (by simpa [L] using Classical.choose_spec shell.hXdyadic)
      hr
      (by simpa [L, B] using hCarryLarge)
  have hReal :
      (((proofV4CarryOrder shell + 1) *
        (Classical.choose shell.hXdyadic + carryB shell.Q + 1) : Nat) : Real) <=
        (shell.X : Real) := by
    have hRpos : 0 < (proofV4CarryOrder shell : Real) + 1 := by positivity
    have hErr' :
        ((proofV4CarryOrder shell : Real) + 1) *
            (((proofV4CarryOrder shell + 1) *
              (Classical.choose shell.hXdyadic + carryB shell.Q + 1) : Nat) : Real)
          <= ((proofV4CarryOrder shell : Real) + 1) * (shell.X : Real) / 4 := by
      calc
        ((proofV4CarryOrder shell : Real) + 1) *
            (((proofV4CarryOrder shell + 1) *
              (Classical.choose shell.hXdyadic + carryB shell.Q + 1) : Nat) : Real)
            =
          ((proofV4CarryOrder shell : Real) + 1) *
            ((proofV4CarryOrder shell : Real) + 1) *
              (((Classical.choose shell.hXdyadic : Nat) : Real) +
                (carryB shell.Q : Real) + 1) := by
              push_cast
              ring
        _ <= ((proofV4CarryOrder shell : Real) + 1) * (shell.X : Real) / 4 := by
          simpa [L, B, pow_two] using hErr
    nlinarith
  exact_mod_cast hReal

/-- Rational carry gap bound from a left dyadic scale.

This is the self-contained version of the manuscript's dyadic gap bound used
before one already knows that the right endpoint of the adjacent gap lies in the
same shell.  If the left hit is at most `2X`, then the zero-gap carry growth
inequality and `L >= B(Q)+25` force the adjacent gap to be at most `L+B(Q)+1`.
-/
theorem hitGap_le_of_left_dyadic_scale
    {shell : FailingDyadicShell} {a : Nat -> Nat}
    (hseq : HitSequence shell.d a) {k : Nat}
    (hleft : a k <= 2 * shell.X)
    (hCarryLarge : carryB shell.Q + 25 <= Classical.choose shell.hXdyadic) :
    hitGap a k <= Classical.choose shell.hXdyadic + carryB shell.Q + 1 := by
  let L := Classical.choose shell.hXdyadic
  let B := carryB shell.Q
  let g := hitGap a k
  by_contra hnot
  have hgt : L + B + 1 < g := by
    simpa [L, B, g] using Nat.lt_of_not_ge hnot
  let m := g - (L + B + 1)
  have hmpos : 0 < m := by omega
  have hg_eq : g = L + B + 1 + m := by omega
  have hgm1 : g - 1 = L + B + m := by omega
  have hB_le_L : B <= L := by
    simpa [L, B] using (by omega : carryB shell.Q <= Classical.choose shell.hXdyadic)
  have hL6 : 6 <= L := by
    simpa [L, B] using (by omega : 6 <= Classical.choose shell.hXdyadic)
  have hQ4 : shell.Q * 4 <= 2 ^ B := by
    simpa [B] using carryB_spec shell.hQ
  have hXeq : shell.X = 2 ^ L := by
    simpa [L] using Classical.choose_spec shell.hXdyadic
  have hRpos : 0 < integerCarry shell.Q (Classical.choose shell.hrational) shell.d (a k) := by
    exact integerCarry_pos_of_later_one
      (Q := shell.Q)
      (P := Classical.choose shell.hrational)
      (d := shell.d)
      (N := a k)
      (M := a (k + 1))
      shell.hQ shell.hd (Classical.choose_spec shell.hrational)
      (hseq.strict (Nat.lt_succ_self k))
      (hseq.hit (k + 1))
  have hzero :
      forall j : Nat, a k < j -> j <= a k + (g - 1) -> shell.d j = 0 := by
    simpa [g, hitGap] using (hseq.adjacent shell.hd k).zero_gap_condition
  have hpow :=
    nat_pow_two_le_of_zero_gap
      (Q := shell.Q)
      (P := Classical.choose shell.hrational)
      (d := shell.d)
      (N := a k)
      (h := g - 1)
      shell.hQ shell.hd (Classical.choose_spec shell.hrational)
      hRpos hzero
  have harg :
      a k + (g - 1) + 2 = a k + (g + 1) := by omega
  rw [harg] at hpow
  have hpow' :
      2 ^ (g - 1) <= shell.Q * (a k + (g + 1)) := by
    simpa using hpow
  have hleftTerm :
      2 * (shell.Q * a k) <= 2 ^ (g - 1) := by
    calc
      2 * (shell.Q * a k)
          <= 2 * (shell.Q * (2 * shell.X)) := by
            exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left shell.Q hleft)
      _ = (shell.Q * 4) * 2 ^ L := by
            rw [hXeq]
            ring
      _ <= (2 ^ B) * 2 ^ L := by
            exact Nat.mul_le_mul_right (2 ^ L) hQ4
      _ <= (2 ^ B) * 2 ^ (L + m) := by
            exact Nat.mul_le_mul_left (2 ^ B)
              (Nat.pow_le_pow_right (by norm_num : 1 <= 2) (by omega : L <= L + m))
      _ = 2 ^ (g - 1) := by
            rw [← pow_add]
            congr
            omega
  have hgap_linear : g + 1 <= 2 ^ (L + m) := by
    have h8 := eight_mul_add_four_le_two_pow (L := L + m) (by omega : 6 <= L + m)
    have h3 : g + 1 <= 3 * (L + m) := by omega
    omega
  have hgapTerm :
      4 * (shell.Q * (g + 1)) <= 2 ^ (g - 1) := by
    calc
      4 * (shell.Q * (g + 1))
          = (shell.Q * 4) * (g + 1) := by ring
      _ <= (2 ^ B) * 2 ^ (L + m) := by
            exact Nat.mul_le_mul hQ4 hgap_linear
      _ = 2 ^ (g - 1) := by
            rw [← pow_add]
            congr
            omega
  have hsum_lt :
      shell.Q * a k + shell.Q * (g + 1) < 2 ^ (g - 1) := by
    have hpos : 0 < 2 ^ (g - 1) := by positivity
    nlinarith [hleftTerm, hgapTerm, hpos]
  have hdist :
      shell.Q * (a k + (g + 1)) =
        shell.Q * a k + shell.Q * (g + 1) := by
    ring
  omega

/-- The proof-v4 finite rational-gap window needed for carry support supply. -/
theorem proofV4FiniteGapBound_of_carryLarge
    {shell : FailingDyadicShell}
    (hSupportBefore : 1 <= supportCount shell.d shell.X)
    (hCarryLarge : carryB shell.Q + 25 <= Classical.choose shell.hXdyadic) :
    forall {a : Nat -> Nat} (hseq : HitSequence shell.d a) (k : Nat),
      hseq.firstIndexAbove shell.X - 1 <= k ->
      k < hseq.firstIndexAbove shell.X + (proofV4CarryOrder shell + 1) ->
      hitGap a k <= Classical.choose shell.hXdyadic + carryB shell.Q + 1 := by
  intro a hseq
  let i := hseq.firstIndexAbove shell.X
  let p := i - 1
  let N := proofV4CarryOrder shell + 1
  let M := Classical.choose shell.hXdyadic + carryB shell.Q + 1
  have hi_pos : 1 <= i := by
    simpa [i] using hseq.firstIndexAbove_pos_of_supportCount_pos hSupportBefore
  have hp_lt_first : p < hseq.firstIndexAbove shell.X := by
    simp [p, i]
    omega
  have hap_le : a p <= shell.X := hseq.lt_firstIndexAbove shell.X hp_lt_first
  have hLarge : N * M <= shell.X := by
    simpa [N, M] using proofV4CarryWindowLength_le_of_carryLarge (shell := shell) hCarryLarge
  have hmain :
      forall t : Nat, forall k : Nat,
        k - p = t -> p <= k -> k < i + N -> hitGap a k <= M := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
      intro k hkt hpk hk_hi
      have hprev :
          forall g : Nat, p <= g -> g < k -> hitGap a g <= M := by
        intro g hpg hgk
        exact ih (g - p) (by omega) g rfl hpg (by omega)
      have hcum :
          a k <= a p + (k - p) * M := by
        have hraw :=
          hseq.a_add_le_of_hitGap_le (i := p) (r := k - p) (M := M)
            (fun g hg_lo hg_hi => by
              apply hprev g hg_lo
              have hadd : p + (k - p) = k := Nat.add_sub_of_le hpk
              simpa [hadd] using hg_hi)
        have hadd : p + (k - p) = k := Nat.add_sub_of_le hpk
        simpa [hadd] using hraw
      have hsteps : k - p <= N := by omega
      have hmul : (k - p) * M <= N * M := Nat.mul_le_mul_right M hsteps
      have hleft : a k <= 2 * shell.X := by omega
      simpa [M] using
        hitGap_le_of_left_dyadic_scale (shell := shell) hseq hleft hCarryLarge
  intro k hk_lo hk_hi
  exact hmain (k - p) k rfl (by simpa [p, i] using hk_lo) (by simpa [i, N] using hk_hi)

/--
The precise density-side data needed to close the proof-v4 carry support
supply.  This is deliberately stronger than mere nontermination: it records the
manuscript density bridge and the large-shell inequality that makes the linear
lower bound dominate the logarithmic carry order.
-/
structure DensityData (shell : FailingDyadicShell) where
  c : Real
  density : PositiveDyadicShellDensityReal shell.d c
  hDensityLarge :
    Classical.choose (positiveDyadicShellDensityReal_eventual density) <= shell.X
  hOrderLarge :
    orderCoverageLogThreshold c density.1 <=
      Classical.choose shell.hXdyadic

namespace DensityData

/-- Project the density-side bridge to the existing carry support supply. -/
def toManuscriptCarrySupportSupplyData
    {shell : FailingDyadicShell} (data : DensityData shell) :
    ManuscriptCarrySupportSupplyData shell where
  hKr := by
    have hDensity :=
      Classical.choose_spec
        (positiveDyadicShellDensityReal_eventual data.density)
        shell.X shell.hXdyadic data.hDensityLarge
    have hReal :
        ((proofV4CarryOrder shell + 1 : Nat) : Real) <=
          ((supportShell shell.d shell.X).card : Real) :=
      (orderCovered_of_orderCoverageLogThreshold data.density.1
          data.hOrderLarge).trans hDensity
    exact_mod_cast hReal

end DensityData

/-- Add the canonical first-layer budget and recover the carry-scale package. -/
def toManuscriptCarryScaleInputData {shell : FailingDyadicShell}
    (data : ManuscriptCarrySupportSupplyData shell)
    (hCarryLarge : carryB shell.Q + 25 <= Classical.choose shell.hXdyadic) :
    ManuscriptCarryScaleInputData shell where
  budget := ManuscriptCarryActiveBudgetData.ofProofV4FirstLayer hCarryLarge
  support := data

/-- Project directly to the carry pipeline using the canonical first-layer
budget and the supplied large-carry threshold. -/
def toThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
    {shell : FailingDyadicShell} {cPr : Real}
    (data : ManuscriptCarrySupportSupplyData shell)
    (hCarryLarge : carryB shell.Q + 25 <= Classical.choose shell.hXdyadic) :
    ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
      shell cPr :=
  (data.toManuscriptCarryScaleInputData hCarryLarge)
    |>.toThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
      hCarryLarge

namespace DensityData

/-- Convenience projection to the carry pipeline with the canonical first-layer
budget once the large-carry dyadic bound is available. -/
def toThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
    {shell : FailingDyadicShell} {cPr : Real}
    (data : DensityData shell)
    (hCarryLarge : carryB shell.Q + 25 <= Classical.choose shell.hXdyadic) :
    ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
      shell cPr :=
  data.toManuscriptCarrySupportSupplyData
    |>.toThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
      hCarryLarge

end DensityData

/--
Gap-side support supply for proof-v4 K.4.  This is the manuscript-shaped
alternative to the density bridge: once the shell has a hit before its left
endpoint, the rational carry gap bound controls the next
`proofV4CarryOrder shell + 1` adjacent gaps, and the large-shell scale makes
those hits land inside `(X, 2X]`.
-/
structure GapData (shell : FailingDyadicShell) where
  hGap :
    forall {a : Nat -> Nat} (hseq : HitSequence shell.d a) (k : Nat),
      hseq.firstIndexAbove shell.X - 1 <= k ->
      k < hseq.firstIndexAbove shell.X + (proofV4CarryOrder shell + 1) ->
      hitGap a k <= Classical.choose shell.hXdyadic + carryB shell.Q + 1

namespace GapData

/-- Canonical rational-gap support supply from the start-threshold facts. -/
def ofCarryLarge
    {shell : FailingDyadicShell}
    (hSupportBefore : 1 <= supportCount shell.d shell.X)
    (hCarryLarge : carryB shell.Q + 25 <= Classical.choose shell.hXdyadic) :
    GapData shell where
  hGap := proofV4FiniteGapBound_of_carryLarge hSupportBefore hCarryLarge

/-- Project rational gap-side shell supply to the raw `hKr` support condition. -/
def toManuscriptCarrySupportSupplyData
    {shell : FailingDyadicShell} (data : GapData shell)
    (hSupportBefore : 1 <= supportCount shell.d shell.X)
    (hCarryLarge : carryB shell.Q + 25 <= Classical.choose shell.hXdyadic) :
    ManuscriptCarrySupportSupplyData shell where
  hKr := by
    rcases exists_hitSequence_of_nonterminating shell.hd shell.hnonterm with
      ⟨a, hseq⟩
    exact hseq.supportShell_card_ge_of_previous_gap_bound
      (X := shell.X)
      (i := hseq.firstIndexAbove shell.X)
      (N := proofV4CarryOrder shell + 1)
      (M := Classical.choose shell.hXdyadic + carryB shell.Q + 1)
      rfl
      (hseq.firstIndexAbove_pos_of_supportCount_pos hSupportBefore)
      (fun k hk_lo hk_hi => data.hGap hseq k hk_lo hk_hi)
      (proofV4CarryWindowLength_le_of_carryLarge hCarryLarge)

/-- Convenience projection from rational gap-side supply to the carry pipeline. -/
def toThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
    {shell : FailingDyadicShell} {cPr : Real}
    (data : GapData shell)
    (hSupportBefore : 1 <= supportCount shell.d shell.X)
    (hCarryLarge : carryB shell.Q + 25 <= Classical.choose shell.hXdyadic) :
    ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
      shell cPr :=
  data.toManuscriptCarrySupportSupplyData hSupportBefore hCarryLarge
    |>.toThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
      hCarryLarge

end GapData

end ManuscriptCarrySupportSupplyData

/-- The Appendix N threshold also enforces the K.4 carry-large dyadic bound. -/
def appendixNChainCompressionStartThreshold
    (Q : Nat) (d : Nat -> Nat)
    (hd : BinaryDigits d) (hnonterm : Not (EventuallyZero d)) : Nat :=
  firstPositiveSupportThreshold d hd hnonterm +
    carryThreshold (carryB Q + 19)

theorem firstPositiveSupportThreshold_le_appendixNChainCompressionStartThreshold
    {Q : Nat} {d : Nat -> Nat} {hd : BinaryDigits d}
    {hnonterm : Not (EventuallyZero d)} :
    firstPositiveSupportThreshold d hd hnonterm <=
      appendixNChainCompressionStartThreshold Q d hd hnonterm := by
  unfold appendixNChainCompressionStartThreshold
  omega

theorem carryThreshold_le_appendixNChainCompressionStartThreshold
    {Q : Nat} {d : Nat -> Nat} {hd : BinaryDigits d}
    {hnonterm : Not (EventuallyZero d)} :
    carryThreshold (carryB Q + 19) <=
      appendixNChainCompressionStartThreshold Q d hd hnonterm := by
  unfold appendixNChainCompressionStartThreshold
  omega

theorem carryLarge_of_carryThreshold_le
    {X L B : Nat} (hX : X = 2 ^ L)
    (h : carryThreshold (B + 19) <= X) :
    B + 25 <= L := by
  have hlog :
      carryLogThreshold (B + 19) <= L :=
    L_ge_carryLogThreshold_of_X_ge hX h
  unfold carryLogThreshold at hlog
  omega

/-- The Appendix N start threshold canonically supplies a nonempty initial
support prefix for the carry/chain-compression consumer. -/
theorem supportCount_pos_of_appendixNChainCompressionStartThreshold_le
    {shell : FailingDyadicShell}
    (hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
          shell.hnonterm <= shell.X) :
    1 <= supportCount shell.d shell.X := by
  exact supportCount_pos_of_firstPositiveSupportThreshold_le shell.hd
    shell.hnonterm
    (le_trans firstPositiveSupportThreshold_le_appendixNChainCompressionStartThreshold
      hXge)

/-- The Appendix N start threshold canonically supplies the K.4 large-carry
dyadic inequality. -/
theorem carryLarge_of_appendixNChainCompressionStartThreshold_le
    {shell : FailingDyadicShell}
    (hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
          shell.hnonterm <= shell.X) :
    carryB shell.Q + 25 <= Classical.choose shell.hXdyadic := by
  have h_carryThreshold :
      carryThreshold (carryB shell.Q + 19) <= shell.X := by
    exact le_trans carryThreshold_le_appendixNChainCompressionStartThreshold
      hXge
  exact carryLarge_of_carryThreshold_le
    (B := carryB shell.Q)
    (X := shell.X)
    (L := Classical.choose shell.hXdyadic)
    (Classical.choose_spec shell.hXdyadic)
    h_carryThreshold

/--
Current strongest global interface with the carry bookkeeping derived from each
failing shell.
-/
structure GlobalAssemblyCoreShellGroundedCurrentInputs where
  carry :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        ShellGroundedCarryLocalData shell erdos260Constants.cPr
  chernoff :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedChernoffLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  cnl :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedCNLLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  densePack :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedDensePackLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  tower :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedTowerLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  returnPkg :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedReturnLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  run :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedRunLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  highExcess :
    forall (shell : FailingDyadicShell)
      (hcQ : shell.cQ = erdos260Constants.cQ)
      (phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real)),
        GroundedHighExcessLocalData phases ((carry shell hcQ).toCarryData)

/-- Forget the shell-grounded carry interface to the previous grounded-current interface. -/
def GlobalAssemblyCoreShellGroundedCurrentInputs.toGroundedAllCurrentInputs
    (data : GlobalAssemblyCoreShellGroundedCurrentInputs) :
    GlobalAssemblyCoreGroundedAllCurrentInputs where
  carry := by
    intro shell hcQ
    exact (data.carry shell hcQ).toGroundedCarryLocalData
  chernoff := data.chernoff
  cnl := data.cnl
  densePack := data.densePack
  tower := data.tower
  returnPkg := data.returnPkg
  run := data.run
  highExcess := by
    intro shell hcQ phases
    exact data.highExcess shell hcQ phases

/--
Erdos 260 from the current strongest global interface, with rational/dyadic
carry bookkeeping recovered from each failing shell.
-/
theorem erdos260_final_core_shell_grounded_current
    (data : GlobalAssemblyCoreShellGroundedCurrentInputs) :
    Erdos260Statement :=
  erdos260_final_core_grounded_current data.toGroundedAllCurrentInputs

/--
Current global interface with both carry bookkeeping and the support-count
start condition grounded in the failing shell plus the global largeness
threshold.
-/
structure GlobalAssemblyCoreThresholdShellGroundedCurrentInputs where
  carry :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        ThresholdShellGroundedCarryLocalData shell erdos260Constants.cPr
  chernoff :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedChernoffLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  cnl :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedCNLLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  densePack :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedDensePackLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  tower :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedTowerLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  returnPkg :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedReturnLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  run :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedRunLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  highExcess :
    forall (shell : FailingDyadicShell)
      (hcQ : shell.cQ = erdos260Constants.cQ)
      (h_supportCount_pos : 1 <= supportCount shell.d shell.X)
      (phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real)),
        GroundedHighExcessLocalData phases
          ((carry shell hcQ).toCarryData h_supportCount_pos)

/-- Convert the threshold-shell interface directly to global per-failure assembly. -/
def GlobalAssemblyCoreThresholdShellGroundedCurrentInputs.toGlobalPerFailureAssembly
    (data : GlobalAssemblyCoreThresholdShellGroundedCurrentInputs) :
    GlobalPerFailureAssembly where
  constants := erdos260Constants
  startThreshold := by
    intro _Q d _hQ hd hnonterm _hrational
    exact firstPositiveSupportThreshold d hd hnonterm
  perFailureAssembly := by
    intro Q d hQ hd hnonterm hrational X hXdyadic hXge hfailure
    let shell :=
      FailingDyadicShell.ofGlobalConstants erdos260Constants Q d X
        hQ hd hnonterm hrational hXdyadic
        erdos260Constants.c0 erdos260Constants.c0_pos
        manuscriptC0_lt_kappa erdos260Constants.c0_le_cQ hfailure
    have hcQ : shell.cQ = erdos260Constants.cQ := rfl
    have h_supportCount_pos : 1 <= supportCount shell.d shell.X := by
      exact supportCount_pos_of_firstPositiveSupportThreshold_le hd hnonterm hXge
    let carryData := (data.carry shell hcQ).toCarryData h_supportCount_pos
    let phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
        (X : Real) := {
      chernoff := (data.chernoff shell hcQ).toChernoffPathData
      cnl := (data.cnl shell hcQ).toCNLClusterEncodingData
      tower := (data.tower shell hcQ).toTowerTransientFactoryData
      densePack := (data.densePack shell hcQ).toDensePackFactoryData
      returnPkg := (data.returnPkg shell hcQ).toReturnFactoryData
      run := (data.run shell hcQ).toRunFactoryData }
    exact
      PerFailureAssemblyData.ofHighExcessCharge phases
        carryData
        ((data.highExcess shell hcQ h_supportCount_pos phases).toHighExcessChargeData)

/--
Erdos 260 from the strongest current interface, where the support-count start
condition is recovered from the global sufficiently-large threshold.
-/
theorem erdos260_final_core_threshold_shell_grounded_current
    (data : GlobalAssemblyCoreThresholdShellGroundedCurrentInputs) :
    Erdos260Statement :=
  erdos260Statement_of_globalPerFailureAssembly data.toGlobalPerFailureAssembly

/--
Strongest current global interface: carry bookkeeping, support-count start, and
the `K <= c_Q X` allocation reduction are all discharged from the failing shell
and the global threshold.
-/
structure GlobalAssemblyCoreFailureBoundedThresholdShellGroundedCurrentInputs where
  carry :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        FailureBoundedThresholdShellGroundedCarryLocalData shell erdos260Constants.cPr
  chernoff :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedChernoffLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  cnl :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedCNLLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  densePack :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedDensePackLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  tower :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedTowerLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  returnPkg :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedReturnLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  run :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedRunLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  highExcess :
    forall (shell : FailingDyadicShell)
      (hcQ : shell.cQ = erdos260Constants.cQ)
      (h_supportCount_pos : 1 <= supportCount shell.d shell.X)
      (phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real)),
        GroundedHighExcessLocalData phases
          ((carry shell hcQ).toCarryData h_supportCount_pos)

/-- Convert the failure-bounded threshold-shell interface to per-failure assembly. -/
def GlobalAssemblyCoreFailureBoundedThresholdShellGroundedCurrentInputs.toGlobalPerFailureAssembly
    (data : GlobalAssemblyCoreFailureBoundedThresholdShellGroundedCurrentInputs) :
    GlobalPerFailureAssembly where
  constants := erdos260Constants
  startThreshold := by
    intro _Q d _hQ hd hnonterm _hrational
    exact firstPositiveSupportThreshold d hd hnonterm
  perFailureAssembly := by
    intro Q d hQ hd hnonterm hrational X hXdyadic hXge hfailure
    let shell :=
      FailingDyadicShell.ofGlobalConstants erdos260Constants Q d X
        hQ hd hnonterm hrational hXdyadic
        erdos260Constants.c0 erdos260Constants.c0_pos
        manuscriptC0_lt_kappa erdos260Constants.c0_le_cQ hfailure
    have hcQ : shell.cQ = erdos260Constants.cQ := rfl
    have h_supportCount_pos : 1 <= supportCount shell.d shell.X := by
      exact supportCount_pos_of_firstPositiveSupportThreshold_le hd hnonterm hXge
    let phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
        (X : Real) := {
      chernoff := (data.chernoff shell hcQ).toChernoffPathData
      cnl := (data.cnl shell hcQ).toCNLClusterEncodingData
      tower := (data.tower shell hcQ).toTowerTransientFactoryData
      densePack := (data.densePack shell hcQ).toDensePackFactoryData
      returnPkg := (data.returnPkg shell hcQ).toReturnFactoryData
      run := (data.run shell hcQ).toRunFactoryData }
    exact
      PerFailureAssemblyData.ofHighExcessCharge phases
        ((data.carry shell hcQ).toCarryData h_supportCount_pos)
        ((data.highExcess shell hcQ h_supportCount_pos phases).toHighExcessChargeData)

/--
Erdos 260 from the current carry interface whose allocation is derived from the
failure bound `K <= c_Q X`.
-/
theorem erdos260_final_core_failure_bounded_threshold_shell_grounded_current
    (data : GlobalAssemblyCoreFailureBoundedThresholdShellGroundedCurrentInputs) :
    Erdos260Statement :=
  erdos260Statement_of_globalPerFailureAssembly data.toGlobalPerFailureAssembly

/--
Strict strongest current global interface: the carry allocation is derived
directly from the manuscript-strict failure bound `K < c_0 X`.
-/
structure GlobalAssemblyCoreStrictFailureBoundedThresholdShellGroundedCurrentInputs where
  carry :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        StrictFailureBoundedThresholdShellGroundedCarryLocalData shell erdos260Constants.cPr
  chernoff :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedChernoffLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  cnl :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedCNLLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  densePack :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedDensePackLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  tower :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedTowerLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  returnPkg :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedReturnLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  run :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedRunLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  highExcess :
    forall (shell : FailingDyadicShell)
      (hcQ : shell.cQ = erdos260Constants.cQ)
      (h_supportCount_pos : 1 <= supportCount shell.d shell.X)
      (phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real)),
        GroundedHighExcessLocalData phases
          ((carry shell hcQ).toCarryData h_supportCount_pos)

/-- Convert the strict-failure-bounded threshold-shell interface to assembly. -/
def GlobalAssemblyCoreStrictFailureBoundedThresholdShellGroundedCurrentInputs.toGlobalPerFailureAssembly
    (data : GlobalAssemblyCoreStrictFailureBoundedThresholdShellGroundedCurrentInputs) :
    GlobalPerFailureAssembly where
  constants := erdos260Constants
  startThreshold := by
    intro _Q d _hQ hd hnonterm _hrational
    exact firstPositiveSupportThreshold d hd hnonterm
  perFailureAssembly := by
    intro Q d hQ hd hnonterm hrational X hXdyadic hXge hfailure
    let shell :=
      FailingDyadicShell.ofGlobalConstants erdos260Constants Q d X
        hQ hd hnonterm hrational hXdyadic
        erdos260Constants.c0 erdos260Constants.c0_pos
        manuscriptC0_lt_kappa erdos260Constants.c0_le_cQ hfailure
    have hcQ : shell.cQ = erdos260Constants.cQ := rfl
    have h_supportCount_pos : 1 <= supportCount shell.d shell.X := by
      exact supportCount_pos_of_firstPositiveSupportThreshold_le hd hnonterm hXge
    let phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
        (X : Real) := {
      chernoff := (data.chernoff shell hcQ).toChernoffPathData
      cnl := (data.cnl shell hcQ).toCNLClusterEncodingData
      tower := (data.tower shell hcQ).toTowerTransientFactoryData
      densePack := (data.densePack shell hcQ).toDensePackFactoryData
      returnPkg := (data.returnPkg shell hcQ).toReturnFactoryData
      run := (data.run shell hcQ).toRunFactoryData }
    exact
      PerFailureAssemblyData.ofHighExcessCharge phases
        ((data.carry shell hcQ).toCarryData h_supportCount_pos)
        ((data.highExcess shell hcQ h_supportCount_pos phases).toHighExcessChargeData)

/--
Erdos 260 from the current interface where the allocation bridge uses the
strict proof-v4 failure constant `c_0`.
-/
theorem erdos260_final_core_strict_failure_bounded_threshold_shell_grounded_current
    (data : GlobalAssemblyCoreStrictFailureBoundedThresholdShellGroundedCurrentInputs) :
    Erdos260Statement :=
  erdos260Statement_of_globalPerFailureAssembly data.toGlobalPerFailureAssembly

/--
Budgeted strict strongest current global interface: the K.4 allocation is
exposed as separate threshold and boundary-error budgets, matching the proof-v4
pressure paragraph.
-/
structure GlobalAssemblyCoreBudgetedStrictFailureBoundedThresholdShellGroundedCurrentInputs where
  carry :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        BudgetedStrictFailureBoundedThresholdShellGroundedCarryLocalData
          shell erdos260Constants.cPr
  chernoff :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedChernoffLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  cnl :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedCNLLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  densePack :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedDensePackLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  tower :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedTowerLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  returnPkg :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedReturnLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  run :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedRunLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  highExcess :
    forall (shell : FailingDyadicShell)
      (hcQ : shell.cQ = erdos260Constants.cQ)
      (h_supportCount_pos : 1 <= supportCount shell.d shell.X)
      (phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real)),
        GroundedHighExcessLocalData phases
          ((carry shell hcQ).toCarryData erdos260Constants_cPr_le_half
            h_supportCount_pos)

/-- Convert the budgeted strict-failure interface to per-failure assembly. -/
def GlobalAssemblyCoreBudgetedStrictFailureBoundedThresholdShellGroundedCurrentInputs.toGlobalPerFailureAssembly
    (data :
      GlobalAssemblyCoreBudgetedStrictFailureBoundedThresholdShellGroundedCurrentInputs) :
    GlobalPerFailureAssembly where
  constants := erdos260Constants
  startThreshold := by
    intro _Q d _hQ hd hnonterm _hrational
    exact firstPositiveSupportThreshold d hd hnonterm
  perFailureAssembly := by
    intro Q d hQ hd hnonterm hrational X hXdyadic hXge hfailure
    let shell :=
      FailingDyadicShell.ofGlobalConstants erdos260Constants Q d X
        hQ hd hnonterm hrational hXdyadic
        erdos260Constants.c0 erdos260Constants.c0_pos
        manuscriptC0_lt_kappa erdos260Constants.c0_le_cQ hfailure
    have hcQ : shell.cQ = erdos260Constants.cQ := rfl
    have h_supportCount_pos : 1 <= supportCount shell.d shell.X := by
      exact supportCount_pos_of_firstPositiveSupportThreshold_le hd hnonterm hXge
    let phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
        (X : Real) := {
      chernoff := (data.chernoff shell hcQ).toChernoffPathData
      cnl := (data.cnl shell hcQ).toCNLClusterEncodingData
      tower := (data.tower shell hcQ).toTowerTransientFactoryData
      densePack := (data.densePack shell hcQ).toDensePackFactoryData
      returnPkg := (data.returnPkg shell hcQ).toReturnFactoryData
      run := (data.run shell hcQ).toRunFactoryData }
    exact
      PerFailureAssemblyData.ofHighExcessCharge phases
        ((data.carry shell hcQ).toCarryData erdos260Constants_cPr_le_half
          h_supportCount_pos)
        ((data.highExcess shell hcQ h_supportCount_pos phases).toHighExcessChargeData)

/--
Erdos 260 from the current interface whose strict K.4 allocation is split into
the proof-v4 threshold and boundary-error budgets.
-/
theorem erdos260_final_core_budgeted_strict_failure_bounded_threshold_shell_grounded_current
    (data :
      GlobalAssemblyCoreBudgetedStrictFailureBoundedThresholdShellGroundedCurrentInputs) :
    Erdos260Statement :=
  erdos260Statement_of_globalPerFailureAssembly data.toGlobalPerFailureAssembly

/--
Current strongest interface with the gap-error budget derived from large dyadic
scale, leaving only the threshold budget as K.4 carry-side numerical content.
-/
structure GlobalAssemblyCoreErrorBudgetedStrictFailureBoundedThresholdShellGroundedCurrentInputs where
  carry :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        ErrorBudgetedStrictFailureBoundedThresholdShellGroundedCarryLocalData
          shell erdos260Constants.cPr
  chernoff :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedChernoffLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  cnl :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedCNLLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  densePack :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedDensePackLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  tower :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedTowerLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  returnPkg :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedReturnLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  run :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedRunLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  highExcess :
    forall (shell : FailingDyadicShell)
      (hcQ : shell.cQ = erdos260Constants.cQ)
      (h_supportCount_pos : 1 <= supportCount shell.d shell.X)
      (phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real)),
        GroundedHighExcessLocalData phases
          ((carry shell hcQ).toCarryData erdos260Constants_cPr_le_half
            h_supportCount_pos)

/-- Convert the error-budgeted strict-failure interface to per-failure assembly. -/
def GlobalAssemblyCoreErrorBudgetedStrictFailureBoundedThresholdShellGroundedCurrentInputs.toGlobalPerFailureAssembly
    (data :
      GlobalAssemblyCoreErrorBudgetedStrictFailureBoundedThresholdShellGroundedCurrentInputs) :
    GlobalPerFailureAssembly where
  constants := erdos260Constants
  startThreshold := by
    intro _Q d _hQ hd hnonterm _hrational
    exact firstPositiveSupportThreshold d hd hnonterm
  perFailureAssembly := by
    intro Q d hQ hd hnonterm hrational X hXdyadic hXge hfailure
    let shell :=
      FailingDyadicShell.ofGlobalConstants erdos260Constants Q d X
        hQ hd hnonterm hrational hXdyadic
        erdos260Constants.c0 erdos260Constants.c0_pos
        manuscriptC0_lt_kappa erdos260Constants.c0_le_cQ hfailure
    have hcQ : shell.cQ = erdos260Constants.cQ := rfl
    have h_supportCount_pos : 1 <= supportCount shell.d shell.X := by
      exact supportCount_pos_of_firstPositiveSupportThreshold_le hd hnonterm hXge
    let phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
        (X : Real) := {
      chernoff := (data.chernoff shell hcQ).toChernoffPathData
      cnl := (data.cnl shell hcQ).toCNLClusterEncodingData
      tower := (data.tower shell hcQ).toTowerTransientFactoryData
      densePack := (data.densePack shell hcQ).toDensePackFactoryData
      returnPkg := (data.returnPkg shell hcQ).toReturnFactoryData
      run := (data.run shell hcQ).toRunFactoryData }
    exact
      PerFailureAssemblyData.ofHighExcessCharge phases
        ((data.carry shell hcQ).toCarryData erdos260Constants_cPr_le_half
          h_supportCount_pos)
        ((data.highExcess shell hcQ h_supportCount_pos phases).toHighExcessChargeData)

/--
Erdos 260 from the current carry interface whose boundary gap-error budget is
proved from the dyadic growth threshold.
-/
theorem erdos260_final_core_error_budgeted_strict_failure_bounded_threshold_shell_grounded_current
    (data :
      GlobalAssemblyCoreErrorBudgetedStrictFailureBoundedThresholdShellGroundedCurrentInputs) :
    Erdos260Statement :=
  erdos260Statement_of_globalPerFailureAssembly data.toGlobalPerFailureAssembly

/--
Current strongest interface with both K.4 budget inequalities derived from
scale conditions.  The carry provider supplies the order/threshold scale
comparisons instead of either budget inequality.
-/
structure GlobalAssemblyCoreThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs where
  carry :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        shell.c0 <= manuscriptKappa / 16 ->
          ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
            shell erdos260Constants.cPr
  chernoff :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedChernoffLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  cnl :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedCNLLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  densePack :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedDensePackLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  tower :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedTowerLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  returnPkg :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedReturnLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  run :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedRunLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  highExcess :
    forall (shell : FailingDyadicShell)
      (hcQ : shell.cQ = erdos260Constants.cQ)
      (hc0Small : shell.c0 <= manuscriptKappa / 16)
      (h_supportCount_pos : 1 <= supportCount shell.d shell.X)
      (phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real)),
        GroundedHighExcessLocalData phases
          ((carry shell hcQ hc0Small).toCarryData erdos260Constants_cPr_le_half
            hc0Small h_supportCount_pos)

/-- Convert the threshold-controlled interface to per-failure assembly. -/
def GlobalAssemblyCoreThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs.toGlobalPerFailureAssembly
    (data :
      GlobalAssemblyCoreThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs) :
    GlobalPerFailureAssembly where
  constants := erdos260Constants
  startThreshold := by
    intro _Q d _hQ hd hnonterm _hrational
    exact firstPositiveSupportThreshold d hd hnonterm
  perFailureAssembly := by
    intro Q d hQ hd hnonterm hrational X hXdyadic hXge hfailure
    let shell :=
      FailingDyadicShell.ofGlobalConstants erdos260Constants Q d X
        hQ hd hnonterm hrational hXdyadic
        erdos260Constants.c0 erdos260Constants.c0_pos
        manuscriptC0_lt_kappa erdos260Constants.c0_le_cQ hfailure
    have hcQ : shell.cQ = erdos260Constants.cQ := rfl
    have hc0Small : shell.c0 <= manuscriptKappa / 16 := by
      exact erdos260Constants_c0_le_kappa_div_sixteen
    have h_supportCount_pos : 1 <= supportCount shell.d shell.X := by
      exact supportCount_pos_of_firstPositiveSupportThreshold_le hd hnonterm hXge
    let phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
        (X : Real) := {
      chernoff := (data.chernoff shell hcQ).toChernoffPathData
      cnl := (data.cnl shell hcQ).toCNLClusterEncodingData
      tower := (data.tower shell hcQ).toTowerTransientFactoryData
      densePack := (data.densePack shell hcQ).toDensePackFactoryData
      returnPkg := (data.returnPkg shell hcQ).toReturnFactoryData
      run := (data.run shell hcQ).toRunFactoryData }
    exact
      PerFailureAssemblyData.ofHighExcessCharge phases
        ((data.carry shell hcQ hc0Small).toCarryData erdos260Constants_cPr_le_half
          hc0Small h_supportCount_pos)
        ((data.highExcess shell hcQ hc0Small h_supportCount_pos phases).toHighExcessChargeData)

/--
Erdos 260 from the current carry interface whose K.4 threshold and gap-error
budgets are both derived from scale conditions.
-/
theorem erdos260_final_core_threshold_controlled_strict_failure_bounded_threshold_shell_grounded_current
    (data :
      GlobalAssemblyCoreThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs) :
    Erdos260Statement :=
  erdos260Statement_of_globalPerFailureAssembly data.toGlobalPerFailureAssembly

/--
Current strongest interface with the K.4 carry budgets derived from scale
conditions and the I.9 high-excess branch-mass reindexing made definitional.
-/
structure GlobalAssemblyCoreI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs where
  carry :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        shell.c0 <= manuscriptKappa / 16 ->
          ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
            shell erdos260Constants.cPr
  chernoff :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedChernoffLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  cnl :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedCNLLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  densePack :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedDensePackLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  tower :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedTowerLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  returnPkg :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedReturnLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  run :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedRunLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  highExcess :
    forall (shell : FailingDyadicShell)
      (hcQ : shell.cQ = erdos260Constants.cQ)
      (hc0Small : shell.c0 <= manuscriptKappa / 16)
      (h_supportCount_pos : 1 <= supportCount shell.d shell.X)
      (phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real)),
        BranchMassGroundedHighExcessLocalData phases
          ((carry shell hcQ hc0Small).toCarryData erdos260Constants_cPr_le_half
            hc0Small h_supportCount_pos)

/-- Forget the I.9-normalized high-excess interface to the threshold-controlled one. -/
def GlobalAssemblyCoreI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs.toThresholdControlledInputs
    (data :
      GlobalAssemblyCoreI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs) :
    GlobalAssemblyCoreThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs where
  carry := data.carry
  chernoff := data.chernoff
  cnl := data.cnl
  densePack := data.densePack
  tower := data.tower
  returnPkg := data.returnPkg
  run := data.run
  highExcess := by
    intro shell hcQ hc0Small h_supportCount_pos phases
    exact
      (data.highExcess shell hcQ hc0Small h_supportCount_pos phases).toGroundedHighExcessLocalData

/--
Erdos 260 from the current proof-v4 interface: K.4 carry budgets are derived
from scale conditions, and I.9 branch-mass reindexing is no longer an input
field of the high-excess package.
-/
theorem erdos260_final_core_i9_threshold_controlled_strict_failure_bounded_threshold_shell_grounded_current
    (data :
      GlobalAssemblyCoreI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs) :
    Erdos260Statement :=
  erdos260_final_core_threshold_controlled_strict_failure_bounded_threshold_shell_grounded_current
    data.toThresholdControlledInputs

/--
I.9 high-excess local data with shell/carry bookkeeping removed from the input.

Compared with `BranchMassGroundedHighExcessLocalData`, this structure no longer
asks the high-excess provider for `P`, `B`, `hP`, `hX_eq`, `hX_pos`, `hB`, or
`hKr`.  They are recovered from the failing shell and the
threshold-controlled carry package.
-/
structure ShellBookedBranchMassGroundedHighExcessLocalData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : Real))
    (carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (h_supportCount_pos : 1 <= supportCount shell.d shell.X) where
  Branch : Type
  Labels : Type
  instBranch : DecidableEq Branch
  instLabels : DecidableEq Labels
  instFintypeLabels : Fintype Labels
  Q : Nat
  instQ : NeZero Q
  VarDrop : Real
  Cmul : Real
  Y : Real
  D : Real -> AppendixN.FirstCrossingRecordData Branch Q Labels
  branches : Finset Branch
  dropDensity : Real -> Real
  dropMass : Real -> Branch -> Nat -> Real
  hdrop_nonneg : forall T b e, 0 <= dropMass T b e
  crossingIndic : Real -> Nat -> Real
  hindic_nonneg : forall T e, 0 <= crossingIndic T e
  hlift_le : forall T b e, dropMass T b e <= crossingIndic T e
  support : Real -> Nat -> Finset Branch
  hsupp : forall T e, support T e ⊆branches
  hzero : forall T e, forall b, b ∈ branches -> b ∉ support T e -> dropMass T b e = 0
  hle : forall T e, (D T).loIdx e <= (D T).hiIdx e
  hinj :
    forall T (e : Nat), forall b, b ∈ support T e -> forall b', b' ∈ support T e ->
      (D T).record e b = (D T).record e b' ->
        (D T).startResidue b = (D T).startResidue b' -> b = b'
  s : Nat
  K : Finset Nat
  A : Set Real
  termMass : Real
  absorbedBound : Real
  densePackClass : Finset Nat
  hDensePackClass :
    densePackClass ⊆phases.toClosurePhaseData.densePack.densePackPoints
  chernoffClass : Finset phases.toClosurePhaseData.chernoff.α
  hChernoffClass :
    chernoffClass ⊆      highCostSet phases.toClosurePhaseData.chernoff.paths
        phases.toClosurePhaseData.chernoff.cost phases.toClosurePhaseData.chernoff.Y
  towerClass : Finset TowerExit
  hTowerClass : towerClass ⊆phases.toClosurePhaseData.tower.entryExitSet
  O_E : Real
  O_CNL : Real
  O_V : Real
  hsplit :
    groundedHighExcessBranchMass
      (carryLocal.toCarryData erdos260Constants_cPr_le_half
        hc0Small h_supportCount_pos) = termMass + VarDrop
  hterm : termMass <= absorbedBound
  hK : forall k, k ∈ K -> s <= k
  hKwin :
    forall k, k ∈ K ->
      k + 1 <
        (carryLocal.toCarryData erdos260Constants_cPr_le_half
          hc0Small h_supportCount_pos).carry.hits.firstIndexAbove shell.X +
          (carryLocal.toCarryData erdos260Constants_cPr_le_half
            hc0Small h_supportCount_pos).r
  hCmulY : 0 <= Cmul * Y
  hA : MeasurableSet A
  hdrop_int : IntegrableOn dropDensity A volume
  hvar : VarDrop <= Cmul * Y * ∫ T in A, dropDensity T ∂volume
  hdensity :
    forall T, T ∈ A -> dropDensity T = ∑ e ∈ K, ∑ b ∈ branches, dropMass T b e
  hindic :
    forall T, T ∈ A -> forall e,
      crossingIndic T e =
        AppendixN.crossingIndicator (T + Y)
          (AppendixN.windowSum
            (fun n =>
              (hitGap
                (carryLocal.toCarryData erdos260Constants_cPr_le_half
                  hc0Small h_supportCount_pos).a n : Real)) s) e
  hAbsorbed :
    absorbedBound <=
      (densePackClass.card : Real)
        + weightedMass chernoffClass phases.toClosurePhaseData.chernoff.weight
        + O_E + O_CNL
        + (∑ b ∈ towerClass, phases.toClosurePhaseData.tower.chargedWeight b)
  hWindow :
    Cmul * ((Q * Fintype.card Labels * Q : Nat) : Real) * Y *
        (2 * (((Classical.choose shell.hXdyadic : Nat) + carryB shell.Q + 1 : Nat) : Real) *
          (K.card : Real)) <= O_V
  hE : O_E <= termReturn phases.toClosurePhaseData
  hCNL : O_CNL <= termCnl phases.toClosurePhaseData
  hV : O_V <= termRun phases.toClosurePhaseData

/-- Restore the old I.9-normalized data by filling shell/carry bookkeeping canonically. -/
def ShellBookedBranchMassGroundedHighExcessLocalData.toBranchMassGroundedHighExcessLocalData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      ShellBookedBranchMassGroundedHighExcessLocalData phases carryLocal
        hc0Small h_supportCount_pos) :
    BranchMassGroundedHighExcessLocalData phases
      (carryLocal.toCarryData erdos260Constants_cPr_le_half
        hc0Small h_supportCount_pos) where
  Branch := data.Branch
  Labels := data.Labels
  instBranch := data.instBranch
  instLabels := data.instLabels
  instFintypeLabels := data.instFintypeLabels
  Q := data.Q
  instQ := data.instQ
  B := carryB shell.Q
  P := Classical.choose shell.hrational
  hP := Classical.choose_spec shell.hrational
  hX_eq := by
    exact Classical.choose_spec shell.hXdyadic
  hX_pos := Nat.succ_le_of_lt (dyadic_pos shell.hXdyadic)
  hB := carryB_spec shell.hQ
  hKr := carryLocal.hKr
  VarDrop := data.VarDrop
  Cmul := data.Cmul
  Y := data.Y
  D := data.D
  branches := data.branches
  dropDensity := data.dropDensity
  dropMass := data.dropMass
  hdrop_nonneg := data.hdrop_nonneg
  crossingIndic := data.crossingIndic
  hindic_nonneg := data.hindic_nonneg
  hlift_le := data.hlift_le
  support := data.support
  hsupp := data.hsupp
  hzero := data.hzero
  hle := data.hle
  hinj := data.hinj
  s := data.s
  K := data.K
  A := data.A
  termMass := data.termMass
  absorbedBound := data.absorbedBound
  densePackClass := data.densePackClass
  hDensePackClass := data.hDensePackClass
  chernoffClass := data.chernoffClass
  hChernoffClass := data.hChernoffClass
  towerClass := data.towerClass
  hTowerClass := data.hTowerClass
  O_E := data.O_E
  O_CNL := data.O_CNL
  O_V := data.O_V
  hsplit := data.hsplit
  hterm := data.hterm
  hK := data.hK
  hKwin := data.hKwin
  hCmulY := data.hCmulY
  hA := data.hA
  hdrop_int := data.hdrop_int
  hvar := data.hvar
  hdensity := data.hdensity
  hindic := data.hindic
  hAbsorbed := data.hAbsorbed
  hWindow := data.hWindow
  hE := data.hE
  hCNL := data.hCNL
  hV := data.hV

/--
Current strongest interface: K.4 budgets, I.9 branch mass, and shell/carry
bookkeeping for the high-excess route are all discharged by wrappers.
-/
structure GlobalAssemblyCoreShellBookedI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs where
  carry :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        shell.c0 <= manuscriptKappa / 16 ->
          ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
            shell erdos260Constants.cPr
  chernoff :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedChernoffLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  cnl :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedCNLLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  densePack :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedDensePackLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  tower :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedTowerLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  returnPkg :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedReturnLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  run :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedRunLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  highExcess :
    forall (shell : FailingDyadicShell)
      (hcQ : shell.cQ = erdos260Constants.cQ)
      (hc0Small : shell.c0 <= manuscriptKappa / 16)
      (h_supportCount_pos : 1 <= supportCount shell.d shell.X)
      (phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real)),
        ShellBookedBranchMassGroundedHighExcessLocalData phases
          (carry shell hcQ hc0Small) hc0Small h_supportCount_pos

/-- Forget the shell-booked high-excess interface to the previous I.9-normalized one. -/
def GlobalAssemblyCoreShellBookedI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs.toI9ThresholdControlledInputs
    (data :
      GlobalAssemblyCoreShellBookedI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs) :
    GlobalAssemblyCoreI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs where
  carry := data.carry
  chernoff := data.chernoff
  cnl := data.cnl
  densePack := data.densePack
  tower := data.tower
  returnPkg := data.returnPkg
  run := data.run
  highExcess := by
    intro shell hcQ hc0Small h_supportCount_pos phases
    exact
      (data.highExcess shell hcQ hc0Small h_supportCount_pos phases).toBranchMassGroundedHighExcessLocalData

/--
Erdos 260 from the shell-booked, I.9-normalized, threshold-controlled current
interface.
-/
theorem erdos260_final_core_shell_booked_i9_threshold_controlled_strict_failure_bounded_threshold_shell_grounded_current
    (data :
      GlobalAssemblyCoreShellBookedI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs) :
    Erdos260Statement :=
  erdos260_final_core_i9_threshold_controlled_strict_failure_bounded_threshold_shell_grounded_current
    data.toI9ThresholdControlledInputs

/--
Shell-booked high-excess data with the first-crossing modulus fixed to the
shell denominator.  This matches proof-v4's "fixed denominator Q" convention:
the provider no longer chooses a separate `Q` or supplies `NeZero Q`.
-/
structure DenominatorBookedShellI9HighExcessLocalData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : Real))
    (carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (h_supportCount_pos : 1 <= supportCount shell.d shell.X) where
  Branch : Type
  Labels : Type
  instBranch : DecidableEq Branch
  instLabels : DecidableEq Labels
  instFintypeLabels : Fintype Labels
  VarDrop : Real
  Cmul : Real
  Y : Real
  D : Real -> AppendixN.FirstCrossingRecordData Branch shell.Q Labels
  branches : Finset Branch
  dropDensity : Real -> Real
  dropMass : Real -> Branch -> Nat -> Real
  hdrop_nonneg : forall T b e, 0 <= dropMass T b e
  crossingIndic : Real -> Nat -> Real
  hindic_nonneg : forall T e, 0 <= crossingIndic T e
  hlift_le : forall T b e, dropMass T b e <= crossingIndic T e
  support : Real -> Nat -> Finset Branch
  hsupp : forall T e, support T e ⊆branches
  hzero : forall T e, forall b, b ∈ branches -> b ∉ support T e -> dropMass T b e = 0
  hle : forall T e, (D T).loIdx e <= (D T).hiIdx e
  hinj :
    forall T (e : Nat), forall b, b ∈ support T e -> forall b', b' ∈ support T e ->
      (D T).record e b = (D T).record e b' ->
        (D T).startResidue b = (D T).startResidue b' -> b = b'
  s : Nat
  K : Finset Nat
  A : Set Real
  termMass : Real
  absorbedBound : Real
  densePackClass : Finset Nat
  hDensePackClass :
    densePackClass ⊆phases.toClosurePhaseData.densePack.densePackPoints
  chernoffClass : Finset phases.toClosurePhaseData.chernoff.α
  hChernoffClass :
    chernoffClass ⊆      highCostSet phases.toClosurePhaseData.chernoff.paths
        phases.toClosurePhaseData.chernoff.cost phases.toClosurePhaseData.chernoff.Y
  towerClass : Finset TowerExit
  hTowerClass : towerClass ⊆phases.toClosurePhaseData.tower.entryExitSet
  O_E : Real
  O_CNL : Real
  O_V : Real
  hsplit :
    groundedHighExcessBranchMass
      (carryLocal.toCarryData erdos260Constants_cPr_le_half
        hc0Small h_supportCount_pos) = termMass + VarDrop
  hterm : termMass <= absorbedBound
  hK : forall k, k ∈ K -> s <= k
  hKwin :
    forall k, k ∈ K ->
      k + 1 <
        (carryLocal.toCarryData erdos260Constants_cPr_le_half
          hc0Small h_supportCount_pos).carry.hits.firstIndexAbove shell.X +
          (carryLocal.toCarryData erdos260Constants_cPr_le_half
            hc0Small h_supportCount_pos).r
  hCmulY : 0 <= Cmul * Y
  hA : MeasurableSet A
  hdrop_int : IntegrableOn dropDensity A volume
  hvar : VarDrop <= Cmul * Y * ∫ T in A, dropDensity T ∂volume
  hdensity :
    forall T, T ∈ A -> dropDensity T = ∑ e ∈ K, ∑ b ∈ branches, dropMass T b e
  hindic :
    forall T, T ∈ A -> forall e,
      crossingIndic T e =
        AppendixN.crossingIndicator (T + Y)
          (AppendixN.windowSum
            (fun n =>
              (hitGap
                (carryLocal.toCarryData erdos260Constants_cPr_le_half
                  hc0Small h_supportCount_pos).a n : Real)) s) e
  hAbsorbed :
    absorbedBound <=
      (densePackClass.card : Real)
        + weightedMass chernoffClass phases.toClosurePhaseData.chernoff.weight
        + O_E + O_CNL
        + (∑ b ∈ towerClass, phases.toClosurePhaseData.tower.chargedWeight b)
  hWindow :
    Cmul * ((shell.Q * Fintype.card Labels * shell.Q : Nat) : Real) * Y *
        (2 * (((Classical.choose shell.hXdyadic : Nat) + carryB shell.Q + 1 : Nat) : Real) *
          (K.card : Real)) <= O_V
  hE : O_E <= termReturn phases.toClosurePhaseData
  hCNL : O_CNL <= termCnl phases.toClosurePhaseData
  hV : O_V <= termRun phases.toClosurePhaseData

/-- Restore shell-booked high-excess data by using the shell denominator as `Q`. -/
def DenominatorBookedShellI9HighExcessLocalData.toShellBookedBranchMassGroundedHighExcessLocalData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      DenominatorBookedShellI9HighExcessLocalData phases carryLocal
        hc0Small h_supportCount_pos) :
    ShellBookedBranchMassGroundedHighExcessLocalData phases carryLocal
      hc0Small h_supportCount_pos where
  Branch := data.Branch
  Labels := data.Labels
  instBranch := data.instBranch
  instLabels := data.instLabels
  instFintypeLabels := data.instFintypeLabels
  Q := shell.Q
  instQ := NeZero.of_pos shell.hQ
  VarDrop := data.VarDrop
  Cmul := data.Cmul
  Y := data.Y
  D := data.D
  branches := data.branches
  dropDensity := data.dropDensity
  dropMass := data.dropMass
  hdrop_nonneg := data.hdrop_nonneg
  crossingIndic := data.crossingIndic
  hindic_nonneg := data.hindic_nonneg
  hlift_le := data.hlift_le
  support := data.support
  hsupp := data.hsupp
  hzero := data.hzero
  hle := data.hle
  hinj := data.hinj
  s := data.s
  K := data.K
  A := data.A
  termMass := data.termMass
  absorbedBound := data.absorbedBound
  densePackClass := data.densePackClass
  hDensePackClass := data.hDensePackClass
  chernoffClass := data.chernoffClass
  hChernoffClass := data.hChernoffClass
  towerClass := data.towerClass
  hTowerClass := data.hTowerClass
  O_E := data.O_E
  O_CNL := data.O_CNL
  O_V := data.O_V
  hsplit := data.hsplit
  hterm := data.hterm
  hK := data.hK
  hKwin := data.hKwin
  hCmulY := data.hCmulY
  hA := data.hA
  hdrop_int := data.hdrop_int
  hvar := data.hvar
  hdensity := data.hdensity
  hindic := data.hindic
  hAbsorbed := data.hAbsorbed
  hWindow := data.hWindow
  hE := data.hE
  hCNL := data.hCNL
  hV := data.hV

/--
Current strongest interface with the Appendix N first-crossing modulus fixed to
the failing shell denominator.
-/
structure GlobalAssemblyCoreDenominatorBookedShellI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs where
  carry :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        shell.c0 <= manuscriptKappa / 16 ->
          ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
            shell erdos260Constants.cPr
  chernoff :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedChernoffLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  cnl :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedCNLLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  densePack :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedDensePackLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  tower :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedTowerLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  returnPkg :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedReturnLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  run :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedRunLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  highExcess :
    forall (shell : FailingDyadicShell)
      (hcQ : shell.cQ = erdos260Constants.cQ)
      (hc0Small : shell.c0 <= manuscriptKappa / 16)
      (h_supportCount_pos : 1 <= supportCount shell.d shell.X)
      (phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real)),
        DenominatorBookedShellI9HighExcessLocalData phases
          (carry shell hcQ hc0Small) hc0Small h_supportCount_pos

/-- Forget the denominator-booked high-excess interface to the shell-booked one. -/
def GlobalAssemblyCoreDenominatorBookedShellI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs.toShellBookedI9Inputs
    (data :
      GlobalAssemblyCoreDenominatorBookedShellI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs) :
    GlobalAssemblyCoreShellBookedI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs where
  carry := data.carry
  chernoff := data.chernoff
  cnl := data.cnl
  densePack := data.densePack
  tower := data.tower
  returnPkg := data.returnPkg
  run := data.run
  highExcess := by
    intro shell hcQ hc0Small h_supportCount_pos phases
    exact
      (data.highExcess shell hcQ hc0Small h_supportCount_pos phases).toShellBookedBranchMassGroundedHighExcessLocalData

/-- Erdos 260 from the denominator-booked current interface. -/
theorem erdos260_final_core_denominator_booked_shell_i9_threshold_controlled_strict_failure_bounded_threshold_shell_grounded_current
    (data :
      GlobalAssemblyCoreDenominatorBookedShellI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs) :
    Erdos260Statement :=
  erdos260_final_core_shell_booked_i9_threshold_controlled_strict_failure_bounded_threshold_shell_grounded_current
    data.toShellBookedI9Inputs

/--
Denominator-booked high-excess data with the Appendix N threshold height fixed
to the carry package's `Y`.

The previous interface still let the N.2 drop-density package choose a separate
`Y`.  In proof-v4 the same threshold height drives both the selected
high-excess starts and the rolling-window first-crossing estimate, so this
wrapper removes that extra free parameter.
-/
structure CarryYBookedDenominatorShellI9HighExcessLocalData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : Real))
    (carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (h_supportCount_pos : 1 <= supportCount shell.d shell.X) where
  Branch : Type
  Labels : Type
  instBranch : DecidableEq Branch
  instLabels : DecidableEq Labels
  instFintypeLabels : Fintype Labels
  VarDrop : Real
  Cmul : Real
  D : Real -> AppendixN.FirstCrossingRecordData Branch shell.Q Labels
  branches : Finset Branch
  dropDensity : Real -> Real
  dropMass : Real -> Branch -> Nat -> Real
  hdrop_nonneg : forall T b e, 0 <= dropMass T b e
  crossingIndic : Real -> Nat -> Real
  hindic_nonneg : forall T e, 0 <= crossingIndic T e
  hlift_le : forall T b e, dropMass T b e <= crossingIndic T e
  support : Real -> Nat -> Finset Branch
  hsupp : forall T e, support T e ⊆branches
  hzero : forall T e, forall b, b ∈ branches -> b ∉ support T e -> dropMass T b e = 0
  hle : forall T e, (D T).loIdx e <= (D T).hiIdx e
  hinj :
    forall T (e : Nat), forall b, b ∈ support T e -> forall b', b' ∈ support T e ->
      (D T).record e b = (D T).record e b' ->
        (D T).startResidue b = (D T).startResidue b' -> b = b'
  s : Nat
  K : Finset Nat
  A : Set Real
  termMass : Real
  absorbedBound : Real
  densePackClass : Finset Nat
  hDensePackClass :
    densePackClass ⊆phases.toClosurePhaseData.densePack.densePackPoints
  chernoffClass : Finset phases.toClosurePhaseData.chernoff.α
  hChernoffClass :
    chernoffClass ⊆      highCostSet phases.toClosurePhaseData.chernoff.paths
        phases.toClosurePhaseData.chernoff.cost phases.toClosurePhaseData.chernoff.Y
  towerClass : Finset TowerExit
  hTowerClass : towerClass ⊆phases.toClosurePhaseData.tower.entryExitSet
  O_E : Real
  O_CNL : Real
  O_V : Real
  hsplit :
    groundedHighExcessBranchMass
      (carryLocal.toCarryData erdos260Constants_cPr_le_half
        hc0Small h_supportCount_pos) = termMass + VarDrop
  hterm : termMass <= absorbedBound
  hK : forall k, k ∈ K -> s <= k
  hKwin :
    forall k, k ∈ K ->
      k + 1 <
        (carryLocal.toCarryData erdos260Constants_cPr_le_half
          hc0Small h_supportCount_pos).carry.hits.firstIndexAbove shell.X +
          (carryLocal.toCarryData erdos260Constants_cPr_le_half
            hc0Small h_supportCount_pos).r
  hCmulY : 0 <= Cmul * carryLocal.Y
  hA : MeasurableSet A
  hdrop_int : IntegrableOn dropDensity A volume
  hvar : VarDrop <= Cmul * carryLocal.Y * ∫ T in A, dropDensity T ∂volume
  hdensity :
    forall T, T ∈ A -> dropDensity T = ∑ e ∈ K, ∑ b ∈ branches, dropMass T b e
  hindic :
    forall T, T ∈ A -> forall e,
      crossingIndic T e =
        AppendixN.crossingIndicator (T + carryLocal.Y)
          (AppendixN.windowSum
            (fun n =>
              (hitGap
                (carryLocal.toCarryData erdos260Constants_cPr_le_half
                  hc0Small h_supportCount_pos).a n : Real)) s) e
  hAbsorbed :
    absorbedBound <=
      (densePackClass.card : Real)
        + weightedMass chernoffClass phases.toClosurePhaseData.chernoff.weight
        + O_E + O_CNL
        + (∑ b ∈ towerClass, phases.toClosurePhaseData.tower.chargedWeight b)
  hWindow :
    Cmul * ((shell.Q * Fintype.card Labels * shell.Q : Nat) : Real) * carryLocal.Y *
        (2 * (((Classical.choose shell.hXdyadic : Nat) + carryB shell.Q + 1 : Nat) : Real) *
          (K.card : Real)) <= O_V
  hE : O_E <= termReturn phases.toClosurePhaseData
  hCNL : O_CNL <= termCnl phases.toClosurePhaseData
  hV : O_V <= termRun phases.toClosurePhaseData

/-- Restore denominator-booked high-excess data by taking `Y := carryLocal.Y`. -/
def CarryYBookedDenominatorShellI9HighExcessLocalData.toDenominatorBookedShellI9HighExcessLocalData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      CarryYBookedDenominatorShellI9HighExcessLocalData phases carryLocal
        hc0Small h_supportCount_pos) :
    DenominatorBookedShellI9HighExcessLocalData phases carryLocal
      hc0Small h_supportCount_pos where
  Branch := data.Branch
  Labels := data.Labels
  instBranch := data.instBranch
  instLabels := data.instLabels
  instFintypeLabels := data.instFintypeLabels
  VarDrop := data.VarDrop
  Cmul := data.Cmul
  Y := carryLocal.Y
  D := data.D
  branches := data.branches
  dropDensity := data.dropDensity
  dropMass := data.dropMass
  hdrop_nonneg := data.hdrop_nonneg
  crossingIndic := data.crossingIndic
  hindic_nonneg := data.hindic_nonneg
  hlift_le := data.hlift_le
  support := data.support
  hsupp := data.hsupp
  hzero := data.hzero
  hle := data.hle
  hinj := data.hinj
  s := data.s
  K := data.K
  A := data.A
  termMass := data.termMass
  absorbedBound := data.absorbedBound
  densePackClass := data.densePackClass
  hDensePackClass := data.hDensePackClass
  chernoffClass := data.chernoffClass
  hChernoffClass := data.hChernoffClass
  towerClass := data.towerClass
  hTowerClass := data.hTowerClass
  O_E := data.O_E
  O_CNL := data.O_CNL
  O_V := data.O_V
  hsplit := data.hsplit
  hterm := data.hterm
  hK := data.hK
  hKwin := data.hKwin
  hCmulY := data.hCmulY
  hA := data.hA
  hdrop_int := data.hdrop_int
  hvar := data.hvar
  hdensity := data.hdensity
  hindic := data.hindic
  hAbsorbed := data.hAbsorbed
  hWindow := data.hWindow
  hE := data.hE
  hCNL := data.hCNL
  hV := data.hV

/-- Current strongest interface with the N.2 height `Y` identified with carry `Y`. -/
structure GlobalAssemblyCoreCarryYBookedDenominatorShellI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs where
  carry :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        shell.c0 <= manuscriptKappa / 16 ->
          ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
            shell erdos260Constants.cPr
  chernoff :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedChernoffLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  cnl :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedCNLLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  densePack :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedDensePackLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  tower :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedTowerLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  returnPkg :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedReturnLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  run :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedRunLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  highExcess :
    forall (shell : FailingDyadicShell)
      (hcQ : shell.cQ = erdos260Constants.cQ)
      (hc0Small : shell.c0 <= manuscriptKappa / 16)
      (h_supportCount_pos : 1 <= supportCount shell.d shell.X)
      (phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real)),
        CarryYBookedDenominatorShellI9HighExcessLocalData phases
          (carry shell hcQ hc0Small) hc0Small h_supportCount_pos

/-- Forget the carry-`Y`-booked interface to the denominator-booked one. -/
def GlobalAssemblyCoreCarryYBookedDenominatorShellI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs.toDenominatorBookedInputs
    (data :
      GlobalAssemblyCoreCarryYBookedDenominatorShellI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs) :
    GlobalAssemblyCoreDenominatorBookedShellI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs where
  carry := data.carry
  chernoff := data.chernoff
  cnl := data.cnl
  densePack := data.densePack
  tower := data.tower
  returnPkg := data.returnPkg
  run := data.run
  highExcess := by
    intro shell hcQ hc0Small h_supportCount_pos phases
    exact
      (data.highExcess shell hcQ hc0Small h_supportCount_pos phases).toDenominatorBookedShellI9HighExcessLocalData

/-- Erdos 260 from the carry-`Y`-booked current interface. -/
theorem erdos260_final_core_carry_y_booked_denominator_shell_i9_threshold_controlled_strict_failure_bounded_threshold_shell_grounded_current
    (data :
      GlobalAssemblyCoreCarryYBookedDenominatorShellI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs) :
    Erdos260Statement :=
  erdos260_final_core_denominator_booked_shell_i9_threshold_controlled_strict_failure_bounded_threshold_shell_grounded_current
    data.toDenominatorBookedInputs

/--
Carry-`Y`-booked high-excess data with the active edge window and the
coarea-multiplicity constant exposed in proof-v4 form.

Compared with `CarryYBookedDenominatorShellI9HighExcessLocalData`, this wrapper
does not ask separately for `hK`, `hKwin`, or `hCmulY`.  The finite edge set is
registered as a subset of the admissible rolling-window interval, and the
coarea multiplicity constant is a natural number, so `0 <= Cmul * Y` is
recovered from type-level nonnegativity and the carry package's `hY`.
-/
structure WindowCmulBookedCarryYDenominatorShellI9HighExcessLocalData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : Real))
    (carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (h_supportCount_pos : 1 <= supportCount shell.d shell.X) where
  Branch : Type
  Labels : Type
  instBranch : DecidableEq Branch
  instLabels : DecidableEq Labels
  instFintypeLabels : Fintype Labels
  VarDrop : Real
  Cmul : Nat
  D : Real -> AppendixN.FirstCrossingRecordData Branch shell.Q Labels
  branches : Finset Branch
  dropDensity : Real -> Real
  dropMass : Real -> Branch -> Nat -> Real
  hdrop_nonneg : forall T b e, 0 <= dropMass T b e
  crossingIndic : Real -> Nat -> Real
  hindic_nonneg : forall T e, 0 <= crossingIndic T e
  hlift_le : forall T b e, dropMass T b e <= crossingIndic T e
  support : Real -> Nat -> Finset Branch
  hsupp : forall T e, support T e ⊆branches
  hzero : forall T e, forall b, b ∈ branches -> b ∉ support T e -> dropMass T b e = 0
  hle : forall T e, (D T).loIdx e <= (D T).hiIdx e
  hinj :
    forall T (e : Nat), forall b, b ∈ support T e -> forall b', b' ∈ support T e ->
      (D T).record e b = (D T).record e b' ->
        (D T).startResidue b = (D T).startResidue b' -> b = b'
  s : Nat
  K : Finset Nat
  hK_window :
    K ⊆      Finset.Ico s
        ((carryLocal.toCarryData erdos260Constants_cPr_le_half
          hc0Small h_supportCount_pos).carry.hits.firstIndexAbove shell.X +
          (carryLocal.toCarryData erdos260Constants_cPr_le_half
            hc0Small h_supportCount_pos).r - 1)
  A : Set Real
  termMass : Real
  absorbedBound : Real
  densePackClass : Finset Nat
  hDensePackClass :
    densePackClass ⊆phases.toClosurePhaseData.densePack.densePackPoints
  chernoffClass : Finset phases.toClosurePhaseData.chernoff.α
  hChernoffClass :
    chernoffClass ⊆      highCostSet phases.toClosurePhaseData.chernoff.paths
        phases.toClosurePhaseData.chernoff.cost phases.toClosurePhaseData.chernoff.Y
  towerClass : Finset TowerExit
  hTowerClass : towerClass ⊆phases.toClosurePhaseData.tower.entryExitSet
  O_E : Real
  O_CNL : Real
  O_V : Real
  hsplit :
    groundedHighExcessBranchMass
      (carryLocal.toCarryData erdos260Constants_cPr_le_half
        hc0Small h_supportCount_pos) = termMass + VarDrop
  hterm : termMass <= absorbedBound
  hA : MeasurableSet A
  hdrop_int : IntegrableOn dropDensity A volume
  hvar : VarDrop <= (Cmul : Real) * carryLocal.Y * ∫ T in A, dropDensity T ∂volume
  hdensity :
    forall T, T ∈ A -> dropDensity T = ∑ e ∈ K, ∑ b ∈ branches, dropMass T b e
  hindic :
    forall T, T ∈ A -> forall e,
      crossingIndic T e =
        AppendixN.crossingIndicator (T + carryLocal.Y)
          (AppendixN.windowSum
            (fun n =>
              (hitGap
                (carryLocal.toCarryData erdos260Constants_cPr_le_half
                  hc0Small h_supportCount_pos).a n : Real)) s) e
  hAbsorbed :
    absorbedBound <=
      (densePackClass.card : Real)
        + weightedMass chernoffClass phases.toClosurePhaseData.chernoff.weight
        + O_E + O_CNL
        + (∑ b ∈ towerClass, phases.toClosurePhaseData.tower.chargedWeight b)
  hWindow :
    (Cmul : Real) * ((shell.Q * Fintype.card Labels * shell.Q : Nat) : Real) * carryLocal.Y *
        (2 * (((Classical.choose shell.hXdyadic : Nat) + carryB shell.Q + 1 : Nat) : Real) *
          (K.card : Real)) <= O_V
  hE : O_E <= termReturn phases.toClosurePhaseData
  hCNL : O_CNL <= termCnl phases.toClosurePhaseData
  hV : O_V <= termRun phases.toClosurePhaseData

/-- Restore the previous carry-`Y`-booked interface from window/Cmul-booked data. -/
def WindowCmulBookedCarryYDenominatorShellI9HighExcessLocalData.toCarryYBookedDenominatorShellI9HighExcessLocalData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      WindowCmulBookedCarryYDenominatorShellI9HighExcessLocalData phases
        carryLocal hc0Small h_supportCount_pos) :
    CarryYBookedDenominatorShellI9HighExcessLocalData phases carryLocal
      hc0Small h_supportCount_pos where
  Branch := data.Branch
  Labels := data.Labels
  instBranch := data.instBranch
  instLabels := data.instLabels
  instFintypeLabels := data.instFintypeLabels
  VarDrop := data.VarDrop
  Cmul := (data.Cmul : Real)
  D := data.D
  branches := data.branches
  dropDensity := data.dropDensity
  dropMass := data.dropMass
  hdrop_nonneg := data.hdrop_nonneg
  crossingIndic := data.crossingIndic
  hindic_nonneg := data.hindic_nonneg
  hlift_le := data.hlift_le
  support := data.support
  hsupp := data.hsupp
  hzero := data.hzero
  hle := data.hle
  hinj := data.hinj
  s := data.s
  K := data.K
  A := data.A
  termMass := data.termMass
  absorbedBound := data.absorbedBound
  densePackClass := data.densePackClass
  hDensePackClass := data.hDensePackClass
  chernoffClass := data.chernoffClass
  hChernoffClass := data.hChernoffClass
  towerClass := data.towerClass
  hTowerClass := data.hTowerClass
  O_E := data.O_E
  O_CNL := data.O_CNL
  O_V := data.O_V
  hsplit := data.hsplit
  hterm := data.hterm
  hK := by
    intro k hk
    exact (Finset.mem_Ico.mp (data.hK_window hk)).1
  hKwin := by
    intro k hk
    have hklt :
        k <
          (carryLocal.toCarryData erdos260Constants_cPr_le_half
            hc0Small h_supportCount_pos).carry.hits.firstIndexAbove shell.X +
            (carryLocal.toCarryData erdos260Constants_cPr_le_half
              hc0Small h_supportCount_pos).r - 1 :=
      (Finset.mem_Ico.mp (data.hK_window hk)).2
    omega
  hCmulY := by
    exact mul_nonneg (by exact_mod_cast Nat.zero_le data.Cmul) carryLocal.hY
  hA := data.hA
  hdrop_int := data.hdrop_int
  hvar := data.hvar
  hdensity := data.hdensity
  hindic := data.hindic
  hAbsorbed := data.hAbsorbed
  hWindow := data.hWindow
  hE := data.hE
  hCNL := data.hCNL
  hV := data.hV

/-- Strongest interface with the N.2 window and multiplier bookkeeping normalized. -/
structure GlobalAssemblyCoreWindowCmulBookedCarryYDenominatorShellI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs where
  carry :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        shell.c0 <= manuscriptKappa / 16 ->
          ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
            shell erdos260Constants.cPr
  chernoff :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedChernoffLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  cnl :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedCNLLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  densePack :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedDensePackLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  tower :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedTowerLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  returnPkg :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedReturnLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  run :
    forall shell : FailingDyadicShell,
      shell.cQ = erdos260Constants.cQ ->
        GroundedRunLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  highExcess :
    forall (shell : FailingDyadicShell)
      (hcQ : shell.cQ = erdos260Constants.cQ)
      (hc0Small : shell.c0 <= manuscriptKappa / 16)
      (h_supportCount_pos : 1 <= supportCount shell.d shell.X)
      (phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real)),
        WindowCmulBookedCarryYDenominatorShellI9HighExcessLocalData phases
          (carry shell hcQ hc0Small) hc0Small h_supportCount_pos

/-- Forget the window/Cmul-booked interface to the carry-`Y`-booked one. -/
def GlobalAssemblyCoreWindowCmulBookedCarryYDenominatorShellI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs.toCarryYBookedDenominatorInputs
    (data :
      GlobalAssemblyCoreWindowCmulBookedCarryYDenominatorShellI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs) :
    GlobalAssemblyCoreCarryYBookedDenominatorShellI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs where
  carry := data.carry
  chernoff := data.chernoff
  cnl := data.cnl
  densePack := data.densePack
  tower := data.tower
  returnPkg := data.returnPkg
  run := data.run
  highExcess := by
    intro shell hcQ hc0Small h_supportCount_pos phases
    exact
      (data.highExcess shell hcQ hc0Small h_supportCount_pos phases).toCarryYBookedDenominatorShellI9HighExcessLocalData

/-- Erdos 260 from the window/Cmul-booked current interface. -/
theorem erdos260_final_core_window_cmul_booked_carry_y_denominator_shell_i9_threshold_controlled_strict_failure_bounded_threshold_shell_grounded_current
    (data :
      GlobalAssemblyCoreWindowCmulBookedCarryYDenominatorShellI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs) :
    Erdos260Statement :=
  erdos260_final_core_carry_y_booked_denominator_shell_i9_threshold_controlled_strict_failure_bounded_threshold_shell_grounded_current
    data.toCarryYBookedDenominatorInputs

/-- Convert the window/Cmul-booked local package all the way to high-excess charge data. -/
def WindowCmulBookedCarryYDenominatorShellI9HighExcessLocalData.toHighExcessChargeData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      WindowCmulBookedCarryYDenominatorShellI9HighExcessLocalData phases
        carryLocal hc0Small h_supportCount_pos) :
    HighExcessChargeData phases
      (carryLocal.toCarryData erdos260Constants_cPr_le_half
        hc0Small h_supportCount_pos) :=
  data.toCarryYBookedDenominatorShellI9HighExcessLocalData
    |>.toDenominatorBookedShellI9HighExcessLocalData
    |>.toShellBookedBranchMassGroundedHighExcessLocalData
    |>.toBranchMassGroundedHighExcessLocalData
    |>.toHighExcessChargeData

/-- Shells produced by the pinned manuscript constants in the global assembly. -/
structure PinnedManuscriptShell (shell : FailingDyadicShell) : Prop where
  hcQ : shell.cQ = erdos260Constants.cQ
  hc0 : shell.c0 = erdos260Constants.c0

theorem PinnedManuscriptShell.hc0Small
    {shell : FailingDyadicShell} (pin : PinnedManuscriptShell shell) :
    shell.c0 <= manuscriptKappa / 16 := by
  rw [pin.hc0]
  exact erdos260Constants_c0_le_kappa_div_sixteen

/--
Pinned-constant current interface.

This is the same window/Cmul-booked local proof surface, but the global provider
is only asked to handle shells with both manuscript constants pinned.  The
per-failure assembly constructs exactly such shells, so the old free
`hc0Small` argument disappears from the provider boundary.
-/
structure GlobalAssemblyCorePinnedWindowCmulBookedCarryYDenominatorShellI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs where
  carry :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
          shell erdos260Constants.cPr
  chernoff :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        GroundedChernoffLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  cnl :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        GroundedCNLLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  densePack :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        GroundedDensePackLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  tower :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        GroundedTowerLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  returnPkg :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        GroundedReturnLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  run :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        GroundedRunLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  highExcess :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (h_supportCount_pos : 1 <= supportCount shell.d shell.X)
      (phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real)),
        WindowCmulBookedCarryYDenominatorShellI9HighExcessLocalData phases
          (carry shell pin) pin.hc0Small h_supportCount_pos

/-- Assemble a global per-failure provider from the pinned-constant interface. -/
def GlobalAssemblyCorePinnedWindowCmulBookedCarryYDenominatorShellI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs.toGlobalPerFailureAssembly
    (data :
      GlobalAssemblyCorePinnedWindowCmulBookedCarryYDenominatorShellI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs) :
    GlobalPerFailureAssembly where
  constants := erdos260Constants
  startThreshold := by
    intro _Q d _hQ hd hnonterm _hrational
    exact firstPositiveSupportThreshold d hd hnonterm
  perFailureAssembly := by
    intro Q d hQ hd hnonterm hrational X hXdyadic hXge hfailure
    let shell :=
      FailingDyadicShell.ofGlobalConstants erdos260Constants Q d X
        hQ hd hnonterm hrational hXdyadic
        erdos260Constants.c0 erdos260Constants.c0_pos
        manuscriptC0_lt_kappa erdos260Constants.c0_le_cQ hfailure
    let pin : PinnedManuscriptShell shell := { hcQ := rfl, hc0 := rfl }
    have h_supportCount_pos : 1 <= supportCount shell.d shell.X := by
      exact supportCount_pos_of_firstPositiveSupportThreshold_le hd hnonterm hXge
    let carryLocal := data.carry shell pin
    let carryData :=
      carryLocal.toCarryData erdos260Constants_cPr_le_half
        pin.hc0Small h_supportCount_pos
    let phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
        (X : Real) := {
      chernoff := (data.chernoff shell pin).toChernoffPathData
      cnl := (data.cnl shell pin).toCNLClusterEncodingData
      tower := (data.tower shell pin).toTowerTransientFactoryData
      densePack := (data.densePack shell pin).toDensePackFactoryData
      returnPkg := (data.returnPkg shell pin).toReturnFactoryData
      run := (data.run shell pin).toRunFactoryData }
    exact
      PerFailureAssemblyData.ofHighExcessCharge phases carryData
        ((data.highExcess shell pin h_supportCount_pos phases).toHighExcessChargeData)

/-- Erdos 260 from the pinned-constant window/Cmul-booked current interface. -/
theorem erdos260_final_core_pinned_window_cmul_booked_carry_y_denominator_shell_i9_threshold_controlled_strict_failure_bounded_threshold_shell_grounded_current
    (data :
      GlobalAssemblyCorePinnedWindowCmulBookedCarryYDenominatorShellI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs) :
    Erdos260Statement :=
  erdos260Statement_of_globalPerFailureAssembly data.toGlobalPerFailureAssembly

/--
High-excess data with Appendix N.2.2 supplied as a bundled
`WindowDropEstimateData`.

This is closer to proof-v4's Lemma N.2.2 statement: the first-crossing density,
fixed-edge multiplicity, and coarea first inequality are no longer separate
fields of the global high-excess interface.  The bundle is still tied to the
real carry package by requiring the same `Y`, the real hit-gap window sequence,
and an admissible rolling-window edge set.
-/
structure BundledWindowDropCarryYDenominatorShellI9HighExcessLocalData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : Real))
    (carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (h_supportCount_pos : 1 <= supportCount shell.d shell.X) where
  drop : AppendixN.WindowDropEstimateData
  s : Nat
  hDropY : drop.Y = carryLocal.Y
  hDropW :
    drop.W =
      AppendixN.windowSum
        (fun n =>
          (hitGap
            (carryLocal.toCarryData erdos260Constants_cPr_le_half
              hc0Small h_supportCount_pos).a n : Real)) s
  hDropK_window :
    drop.K ⊆      Finset.Ico s
        ((carryLocal.toCarryData erdos260Constants_cPr_le_half
          hc0Small h_supportCount_pos).carry.hits.firstIndexAbove shell.X +
          (carryLocal.toCarryData erdos260Constants_cPr_le_half
            hc0Small h_supportCount_pos).r - 1)
  termMass : Real
  absorbedBound : Real
  densePackClass : Finset Nat
  hDensePackClass :
    densePackClass ⊆phases.toClosurePhaseData.densePack.densePackPoints
  chernoffClass : Finset phases.toClosurePhaseData.chernoff.α
  hChernoffClass :
    chernoffClass ⊆      highCostSet phases.toClosurePhaseData.chernoff.paths
        phases.toClosurePhaseData.chernoff.cost phases.toClosurePhaseData.chernoff.Y
  towerClass : Finset TowerExit
  hTowerClass : towerClass ⊆phases.toClosurePhaseData.tower.entryExitSet
  O_E : Real
  O_CNL : Real
  O_V : Real
  hsplit :
    groundedHighExcessBranchMass
      (carryLocal.toCarryData erdos260Constants_cPr_le_half
        hc0Small h_supportCount_pos) = termMass + drop.varDrop
  hterm : termMass <= absorbedBound
  hAbsorbed :
    absorbedBound <=
      (densePackClass.card : Real)
        + weightedMass chernoffClass phases.toClosurePhaseData.chernoff.weight
        + O_E + O_CNL
        + (∑ b ∈ towerClass, phases.toClosurePhaseData.tower.chargedWeight b)
  hWindow :
    drop.CQ * carryLocal.Y *
        (2 *
          (((carryLocal.toCarryData erdos260Constants_cPr_le_half
            hc0Small h_supportCount_pos).L + carryB shell.Q + 1 : Nat) : Real) *
            (drop.K.card : Real)) <= O_V
  hE : O_E <= termReturn phases.toClosurePhaseData
  hCNL : O_CNL <= termCnl phases.toClosurePhaseData
  hV : O_V <= termRun phases.toClosurePhaseData

/-- Convert bundled N.2.2 high-excess data directly to the central charge package. -/
def BundledWindowDropCarryYDenominatorShellI9HighExcessLocalData.toHighExcessChargeData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      BundledWindowDropCarryYDenominatorShellI9HighExcessLocalData phases
        carryLocal hc0Small h_supportCount_pos) :
    HighExcessChargeData phases
      (carryLocal.toCarryData erdos260Constants_cPr_le_half
        hc0Small h_supportCount_pos) := by
  let carryData :=
    carryLocal.toCarryData erdos260Constants_cPr_le_half
      hc0Small h_supportCount_pos
  have hK : forall k, k ∈ data.drop.K -> data.s <= k := by
    intro k hk
    exact (Finset.mem_Ico.mp (data.hDropK_window hk)).1
  have hKwin :
      forall k, k ∈ data.drop.K ->
        k + 1 < carryData.carry.hits.firstIndexAbove shell.X + carryData.r := by
    intro k hk
    have hklt :
        k <
          carryData.carry.hits.firstIndexAbove shell.X + carryData.r - 1 :=
      (Finset.mem_Ico.mp (data.hDropK_window hk)).2
    omega
  have hWindowVs :
      data.drop.CQ * data.drop.Y * AppendixN.Vs data.drop.K data.drop.W <= data.O_V := by
    rw [data.hDropW]
    have hscaled :
        data.drop.CQ * data.drop.Y *
            AppendixN.Vs data.drop.K
              (AppendixN.windowSum (fun n => (hitGap carryData.a n : Real)) data.s)
          <=
            data.drop.CQ * data.drop.Y *
              (2 * ((carryData.L + carryB shell.Q + 1 : Nat) : Real) *
                (data.drop.K.card : Real)) :=
      scaled_windowTerm_le_carryHitGap carryData
        (P := Classical.choose shell.hrational)
        (B := carryB shell.Q)
        (Classical.choose_spec shell.hrational)
        (by
          change shell.X = 2 ^ Classical.choose shell.hXdyadic
          exact Classical.choose_spec shell.hXdyadic)
        (Nat.succ_le_of_lt (dyadic_pos shell.hXdyadic))
        (carryB_spec shell.hQ)
        carryLocal.hKr data.s data.drop.K hK hKwin
        data.drop.CQ data.drop.Y data.drop.CQY_nonneg
    have hExplicit :
        data.drop.CQ * data.drop.Y *
            (2 * ((carryData.L + carryB shell.Q + 1 : Nat) : Real) *
              (data.drop.K.card : Real)) <= data.O_V := by
      rw [data.hDropY]
      exact data.hWindow
    exact hscaled.trans hExplicit
  exact
    HighExcessChargeData.ofC1VDClosure_grounded_windowDrop_branchMass
      phases carryData data.drop
      (groundedHighExcessBranchMass carryData) data.termMass data.absorbedBound
      data.hDensePackClass data.hChernoffClass data.hTowerClass
      rfl data.hsplit data.hterm data.hAbsorbed hWindowVs
      data.hE data.hCNL data.hV

/-- Strongest pinned interface with Appendix N.2.2 supplied as a bundled theorem. -/
structure GlobalAssemblyCorePinnedBundledWindowDropCarryYDenominatorShellI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs where
  carry :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
          shell erdos260Constants.cPr
  chernoff :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        GroundedChernoffLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  cnl :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        GroundedCNLLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  densePack :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        GroundedDensePackLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  tower :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        GroundedTowerLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  returnPkg :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        GroundedReturnLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  run :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        GroundedRunLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  highExcess :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (h_supportCount_pos : 1 <= supportCount shell.d shell.X)
      (phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real)),
        BundledWindowDropCarryYDenominatorShellI9HighExcessLocalData phases
          (carry shell pin) pin.hc0Small h_supportCount_pos

/-- Assemble per-failure data from the pinned bundled-window-drop interface. -/
def GlobalAssemblyCorePinnedBundledWindowDropCarryYDenominatorShellI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs.toGlobalPerFailureAssembly
    (data :
      GlobalAssemblyCorePinnedBundledWindowDropCarryYDenominatorShellI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs) :
    GlobalPerFailureAssembly where
  constants := erdos260Constants
  startThreshold := by
    intro _Q d _hQ hd hnonterm _hrational
    exact firstPositiveSupportThreshold d hd hnonterm
  perFailureAssembly := by
    intro Q d hQ hd hnonterm hrational X hXdyadic hXge hfailure
    let shell :=
      FailingDyadicShell.ofGlobalConstants erdos260Constants Q d X
        hQ hd hnonterm hrational hXdyadic
        erdos260Constants.c0 erdos260Constants.c0_pos
        manuscriptC0_lt_kappa erdos260Constants.c0_le_cQ hfailure
    let pin : PinnedManuscriptShell shell := { hcQ := rfl, hc0 := rfl }
    have h_supportCount_pos : 1 <= supportCount shell.d shell.X := by
      exact supportCount_pos_of_firstPositiveSupportThreshold_le hd hnonterm hXge
    let carryLocal := data.carry shell pin
    let carryData :=
      carryLocal.toCarryData erdos260Constants_cPr_le_half
        pin.hc0Small h_supportCount_pos
    let phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
        (X : Real) := {
      chernoff := (data.chernoff shell pin).toChernoffPathData
      cnl := (data.cnl shell pin).toCNLClusterEncodingData
      tower := (data.tower shell pin).toTowerTransientFactoryData
      densePack := (data.densePack shell pin).toDensePackFactoryData
      returnPkg := (data.returnPkg shell pin).toReturnFactoryData
      run := (data.run shell pin).toRunFactoryData }
    exact
      PerFailureAssemblyData.ofHighExcessCharge phases carryData
        ((data.highExcess shell pin h_supportCount_pos phases).toHighExcessChargeData)

/-- Erdos 260 from the pinned bundled-window-drop current interface. -/
theorem erdos260_final_core_pinned_bundled_window_drop_carry_y_denominator_shell_i9_threshold_controlled_strict_failure_bounded_threshold_shell_grounded_current
    (data :
      GlobalAssemblyCorePinnedBundledWindowDropCarryYDenominatorShellI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs) :
    Erdos260Statement :=
  erdos260Statement_of_globalPerFailureAssembly data.toGlobalPerFailureAssembly

/--
High-excess data with the N.24 aggregate absorption exposed as one theorem.

Compared with `BundledWindowDropCarryYDenominatorShellI9HighExcessLocalData`,
this no longer exposes the five terminal output classes or the auxiliary
`O_E/O_CNL/O_V` comparisons.  Those are exactly the internal content of
proof-v4 Lemma N.3.3 / equation N.24, represented here by `hN24`.
-/
structure N24BookedBundledWindowDropCarryYDenominatorShellI9HighExcessLocalData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : Real))
    (carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (h_supportCount_pos : 1 <= supportCount shell.d shell.X) where
  drop : AppendixN.WindowDropEstimateData
  s : Nat
  hDropY : drop.Y = carryLocal.Y
  hDropW :
    drop.W =
      AppendixN.windowSum
        (fun n =>
          (hitGap
            (carryLocal.toCarryData erdos260Constants_cPr_le_half
              hc0Small h_supportCount_pos).a n : Real)) s
  hDropK_window :
    drop.K ⊆      Finset.Ico s
        ((carryLocal.toCarryData erdos260Constants_cPr_le_half
          hc0Small h_supportCount_pos).carry.hits.firstIndexAbove shell.X +
          (carryLocal.toCarryData erdos260Constants_cPr_le_half
            hc0Small h_supportCount_pos).r - 1)
  termMass : Real
  absorbedBound : Real
  hsplit :
    groundedHighExcessBranchMass
      (carryLocal.toCarryData erdos260Constants_cPr_le_half
        hc0Small h_supportCount_pos) = termMass + drop.varDrop
  hterm : termMass <= absorbedBound
  hN24 :
    absorbedBound + drop.CQ * drop.Y * AppendixN.Vs drop.K drop.W <=
      ClosurePhaseMass phases.toClosurePhaseData

/-- Convert N.24-booked data directly to the central high-excess charge package. -/
def N24BookedBundledWindowDropCarryYDenominatorShellI9HighExcessLocalData.toHighExcessChargeData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      N24BookedBundledWindowDropCarryYDenominatorShellI9HighExcessLocalData phases
        carryLocal hc0Small h_supportCount_pos) :
    HighExcessChargeData phases
      (carryLocal.toCarryData erdos260Constants_cPr_le_half
        hc0Small h_supportCount_pos) := by
  let carryData :=
    carryLocal.toCarryData erdos260Constants_cPr_le_half
      hc0Small h_supportCount_pos
  exact
    HighExcessChargeData.ofC1VDClosure_windowDrop_branchMass
      phases carryData data.drop
      (groundedHighExcessBranchMass carryData) data.termMass data.absorbedBound
      rfl data.hsplit data.hterm data.hN24

/--
N.24-booked high-excess data whose N.2.2 window-drop bundle is generated from
the reduced lower-label first-crossing record interface.

This exposes the remaining proof-v4 N.2.1/N.2.2 data directly instead of taking
`AppendixN.WindowDropEstimateData` as an opaque input.
-/
structure LowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9HighExcessLocalData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : Real))
    (carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (h_supportCount_pos : 1 <= supportCount shell.d shell.X) where
  Branch : Type
  Labels : Type
  decBranch : DecidableEq Branch
  decLabels : DecidableEq Labels
  fintypeLabels : Fintype Labels
  recordQ : Nat
  recordQ_neZero : NeZero recordQ
  VarDrop : Real
  Cmul : Real
  Y : Real
  D : Real -> AppendixN.FirstCrossingRecordData Branch recordQ Labels
  branches : Finset Branch
  dropDensity : Real -> Real
  dropMass : Real -> Branch -> Nat -> Real
  hdrop_nonneg : forall T b e, 0 <= dropMass T b e
  crossingIndic : Real -> Nat -> Real
  hindic_nonneg : forall T e, 0 <= crossingIndic T e
  hlift_le : forall T b e, dropMass T b e <= crossingIndic T e
  support : Real -> Nat -> Finset Branch
  hsupp : forall T e, support T e ⊆branches
  hzero : forall T e, forall b, b ∈ branches -> b ∉ support T e -> dropMass T b e = 0
  hle : forall T e, (D T).loIdx e <= (D T).hiIdx e
  hinj :
    forall T (e : Nat), forall b, b ∈ support T e -> forall b', b' ∈ support T e ->
      (D T).record e b = (D T).record e b' ->
        (D T).startResidue b = (D T).startResidue b' -> b = b'
  K : Finset Nat
  W : Nat -> Real
  A : Set Real
  hCmulY : 0 <= Cmul * Y
  hA : MeasurableSet A
  hdrop_int : IntegrableOn dropDensity A volume
  hvar : VarDrop <= Cmul * Y * ∫ T in A, dropDensity T ∂volume
  hdensity :
    forall T, T ∈ A -> dropDensity T = ∑ e ∈ K, ∑ b ∈ branches, dropMass T b e
  hindic :
    forall T, T ∈ A -> forall e,
      crossingIndic T e = AppendixN.crossingIndicator (T + Y) W e
  s : Nat
  hDropY : Y = carryLocal.Y
  hDropW :
    W =
      AppendixN.windowSum
        (fun n =>
          (hitGap
            (carryLocal.toCarryData erdos260Constants_cPr_le_half
              hc0Small h_supportCount_pos).a n : Real)) s
  hDropK_window :
    K ⊆      Finset.Ico s
        ((carryLocal.toCarryData erdos260Constants_cPr_le_half
          hc0Small h_supportCount_pos).carry.hits.firstIndexAbove shell.X +
          (carryLocal.toCarryData erdos260Constants_cPr_le_half
            hc0Small h_supportCount_pos).r - 1)
  termMass : Real
  absorbedBound : Real
  hsplit :
    groundedHighExcessBranchMass
      (carryLocal.toCarryData erdos260Constants_cPr_le_half
        hc0Small h_supportCount_pos) = termMass + VarDrop
  hterm : termMass <= absorbedBound
  hN24 :
    absorbedBound +
        (Cmul * (((recordQ * (@Fintype.card Labels fintypeLabels) * recordQ : Nat) : Real))) *
          Y * AppendixN.Vs K W <=
      ClosurePhaseMass phases.toClosurePhaseData

/--
Generate the N.24-booked high-excess package from reduced lower-label record
data, discharging the `WindowDropEstimateData` constructor internally.
-/
def LowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9HighExcessLocalData.toN24BookedData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      LowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9HighExcessLocalData
        phases carryLocal hc0Small h_supportCount_pos) :
    N24BookedBundledWindowDropCarryYDenominatorShellI9HighExcessLocalData
      phases carryLocal hc0Small h_supportCount_pos := by
  letI := data.decBranch
  letI := data.decLabels
  letI := data.fintypeLabels
  letI := data.recordQ_neZero
  let drop :=
    AppendixN.WindowDropEstimateData.ofLowerLabelRecordPriorityOfRecordDensity
      data.VarDrop data.Cmul data.Y data.D data.branches data.dropDensity
      data.dropMass data.hdrop_nonneg data.crossingIndic data.hindic_nonneg
      data.hlift_le data.support data.hsupp data.hzero data.hle data.hinj
      data.K data.W data.A data.hCmulY data.hA data.hdrop_int data.hvar
      data.hdensity data.hindic
  exact {
    drop := drop
    s := data.s
    hDropY := by
      simpa [drop, AppendixN.WindowDropEstimateData.ofLowerLabelRecordPriorityOfRecordDensity,
        AppendixN.WindowDropEstimateData.ofScaledDropDensityBound] using data.hDropY
    hDropW := by
      simpa [drop, AppendixN.WindowDropEstimateData.ofLowerLabelRecordPriorityOfRecordDensity,
        AppendixN.WindowDropEstimateData.ofScaledDropDensityBound] using data.hDropW
    hDropK_window := by
      simpa [drop, AppendixN.WindowDropEstimateData.ofLowerLabelRecordPriorityOfRecordDensity,
        AppendixN.WindowDropEstimateData.ofScaledDropDensityBound] using data.hDropK_window
    termMass := data.termMass
    absorbedBound := data.absorbedBound
    hsplit := by
      simpa [drop, AppendixN.WindowDropEstimateData.ofLowerLabelRecordPriorityOfRecordDensity,
        AppendixN.WindowDropEstimateData.ofScaledDropDensityBound] using data.hsplit
    hterm := data.hterm
    hN24 := by
      simpa [drop, AppendixN.WindowDropEstimateData.ofLowerLabelRecordPriorityOfRecordDensity,
        AppendixN.WindowDropEstimateData.ofScaledDropDensityBound] using data.hN24 }

/-- Convert reduced-record N.24-booked data directly to central high-excess data. -/
def LowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9HighExcessLocalData.toHighExcessChargeData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      LowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9HighExcessLocalData
        phases carryLocal hc0Small h_supportCount_pos) :
    HighExcessChargeData phases
      (carryLocal.toCarryData erdos260Constants_cPr_le_half
        hc0Small h_supportCount_pos) :=
  data.toN24BookedData.toHighExcessChargeData

/--
Lower-label-record N.24 high-excess data with the N.13 real hit-gap variation
bound already applied.

The window sequence is fixed to the carry hit-gap window, and the N.24 input is
the explicit proof-v4 bound `C_Q Y * 2(L+B+1)|K|`.
-/
structure CarryHitGapLowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9HighExcessLocalData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : Real))
    (carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (h_supportCount_pos : 1 <= supportCount shell.d shell.X) where
  Branch : Type
  Labels : Type
  decBranch : DecidableEq Branch
  decLabels : DecidableEq Labels
  fintypeLabels : Fintype Labels
  recordQ : Nat
  recordQ_neZero : NeZero recordQ
  VarDrop : Real
  Cmul : Real
  Y : Real
  D : Real -> AppendixN.FirstCrossingRecordData Branch recordQ Labels
  branches : Finset Branch
  dropDensity : Real -> Real
  dropMass : Real -> Branch -> Nat -> Real
  hdrop_nonneg : forall T b e, 0 <= dropMass T b e
  crossingIndic : Real -> Nat -> Real
  hindic_nonneg : forall T e, 0 <= crossingIndic T e
  hlift_le : forall T b e, dropMass T b e <= crossingIndic T e
  support : Real -> Nat -> Finset Branch
  hsupp : forall T e, support T e ⊆branches
  hzero : forall T e, forall b, b ∈ branches -> b ∉ support T e -> dropMass T b e = 0
  hle : forall T e, (D T).loIdx e <= (D T).hiIdx e
  hinj :
    forall T (e : Nat), forall b, b ∈ support T e -> forall b', b' ∈ support T e ->
      (D T).record e b = (D T).record e b' ->
        (D T).startResidue b = (D T).startResidue b' -> b = b'
  s : Nat
  K : Finset Nat
  A : Set Real
  hDropY : Y = carryLocal.Y
  hDropK_window :
    K ⊆      Finset.Ico s
        ((carryLocal.toCarryData erdos260Constants_cPr_le_half
          hc0Small h_supportCount_pos).carry.hits.firstIndexAbove shell.X +
          (carryLocal.toCarryData erdos260Constants_cPr_le_half
            hc0Small h_supportCount_pos).r - 1)
  hCmulY : 0 <= Cmul * Y
  hA : MeasurableSet A
  hdrop_int : IntegrableOn dropDensity A volume
  hvar : VarDrop <= Cmul * Y * ∫ T in A, dropDensity T ∂volume
  hdensity :
    forall T, T ∈ A -> dropDensity T = ∑ e ∈ K, ∑ b ∈ branches, dropMass T b e
  hindic :
    forall T, T ∈ A -> forall e,
      crossingIndic T e =
        AppendixN.crossingIndicator (T + Y)
          (AppendixN.windowSum
            (fun n =>
              (hitGap
                (carryLocal.toCarryData erdos260Constants_cPr_le_half
                  hc0Small h_supportCount_pos).a n : Real)) s) e
  termMass : Real
  absorbedBound : Real
  hsplit :
    groundedHighExcessBranchMass
      (carryLocal.toCarryData erdos260Constants_cPr_le_half
        hc0Small h_supportCount_pos) = termMass + VarDrop
  hterm : termMass <= absorbedBound
  hN24Explicit :
    absorbedBound +
        (Cmul * (((recordQ * (@Fintype.card Labels fintypeLabels) * recordQ : Nat) : Real))) *
          Y *
            (2 *
              (((carryLocal.toCarryData erdos260Constants_cPr_le_half
                hc0Small h_supportCount_pos).L + carryB shell.Q + 1 : Nat) : Real) *
                (K.card : Real)) <=
      ClosurePhaseMass phases.toClosurePhaseData

/--
Convert explicit carry-hitGap reduced-record data to the previous lower-label
record package by applying the grounded N.13 variation estimate.
-/
def CarryHitGapLowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9HighExcessLocalData.toLowerLabelRecordData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      CarryHitGapLowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9HighExcessLocalData
        phases carryLocal hc0Small h_supportCount_pos) :
    LowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9HighExcessLocalData
      phases carryLocal hc0Small h_supportCount_pos := by
  let carryData :=
    carryLocal.toCarryData erdos260Constants_cPr_le_half
      hc0Small h_supportCount_pos
  letI := data.decBranch
  letI := data.decLabels
  letI := data.fintypeLabels
  letI := data.recordQ_neZero
  let W := AppendixN.windowSum (fun n => (hitGap carryData.a n : Real)) data.s
  have hK : forall k, k ∈ data.K -> data.s <= k := by
    intro k hk
    exact (Finset.mem_Ico.mp (data.hDropK_window hk)).1
  have hKwin :
      forall k, k ∈ data.K ->
        k + 1 < carryData.carry.hits.firstIndexAbove shell.X + carryData.r := by
    intro k hk
    have hklt :
        k <
          carryData.carry.hits.firstIndexAbove shell.X + carryData.r - 1 :=
      (Finset.mem_Ico.mp (data.hDropK_window hk)).2
    omega
  let Cfiber : Real :=
    (((data.recordQ * (@Fintype.card data.Labels data.fintypeLabels) *
      data.recordQ : Nat) : Real))
  have hCfiber : 0 <= Cfiber := by
    dsimp [Cfiber]
    exact_mod_cast Nat.zero_le
      (data.recordQ * (@Fintype.card data.Labels data.fintypeLabels) * data.recordQ)
  have htotal : 0 <= (data.Cmul * Cfiber) * data.Y := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using mul_nonneg hCfiber data.hCmulY
  have hVs :
      (data.Cmul * Cfiber) * data.Y * AppendixN.Vs data.K W <=
        (data.Cmul * Cfiber) * data.Y *
          (2 * ((carryData.L + carryB shell.Q + 1 : Nat) : Real) *
            (data.K.card : Real)) := by
    dsimp [W]
    exact
      scaled_windowTerm_le_carryHitGap carryData
        (P := Classical.choose shell.hrational)
        (B := carryB shell.Q)
        (Classical.choose_spec shell.hrational)
        (by
          change shell.X = 2 ^ Classical.choose shell.hXdyadic
          exact Classical.choose_spec shell.hXdyadic)
        (Nat.succ_le_of_lt (dyadic_pos shell.hXdyadic))
        (carryB_spec shell.hQ)
        carryLocal.hKr data.s data.K hK hKwin
        (data.Cmul * Cfiber) data.Y htotal
  exact {
    Branch := data.Branch
    Labels := data.Labels
    decBranch := data.decBranch
    decLabels := data.decLabels
    fintypeLabels := data.fintypeLabels
    recordQ := data.recordQ
    recordQ_neZero := data.recordQ_neZero
    VarDrop := data.VarDrop
    Cmul := data.Cmul
    Y := data.Y
    D := data.D
    branches := data.branches
    dropDensity := data.dropDensity
    dropMass := data.dropMass
    hdrop_nonneg := data.hdrop_nonneg
    crossingIndic := data.crossingIndic
    hindic_nonneg := data.hindic_nonneg
    hlift_le := data.hlift_le
    support := data.support
    hsupp := data.hsupp
    hzero := data.hzero
    hle := data.hle
    hinj := data.hinj
    K := data.K
    W := W
    A := data.A
    hCmulY := data.hCmulY
    hA := data.hA
    hdrop_int := data.hdrop_int
    hvar := data.hvar
    hdensity := data.hdensity
    hindic := by
      intro T hT e
      exact data.hindic T hT e
    s := data.s
    hDropY := data.hDropY
    hDropW := rfl
    hDropK_window := data.hDropK_window
    termMass := data.termMass
    absorbedBound := data.absorbedBound
    hsplit := data.hsplit
    hterm := data.hterm
    hN24 := by
      have hAdd :
          data.absorbedBound +
              (data.Cmul * Cfiber) * data.Y * AppendixN.Vs data.K W <=
            data.absorbedBound +
              (data.Cmul * Cfiber) * data.Y *
                (2 * ((carryData.L + carryB shell.Q + 1 : Nat) : Real) *
                  (data.K.card : Real)) := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right hVs data.absorbedBound
      exact hAdd.trans data.hN24Explicit }

/-- Convert explicit carry-hitGap reduced-record data directly to high-excess data. -/
def CarryHitGapLowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9HighExcessLocalData.toHighExcessChargeData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      CarryHitGapLowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9HighExcessLocalData
        phases carryLocal hc0Small h_supportCount_pos) :
    HighExcessChargeData phases
      (carryLocal.toCarryData erdos260Constants_cPr_le_half
        hc0Small h_supportCount_pos) :=
  data.toLowerLabelRecordData.toHighExcessChargeData

/-- Proof-v4 Lemma N.3.3 terminal non-drop aggregate absorption data. -/
structure TerminalNonDropAggregateAbsorptionData (termMass absorbedBound : Real) where
  massD : Real
  massP : Real
  massE : Real
  massCNL : Real
  massBdd : Real
  densePackTerm : Real
  shellTerm : Real
  remTerm : Real
  shellCNL : Real
  shellBdd : Real
  remP : Real
  remE : Real
  remCNL : Real
  remBdd : Real
  htermSplit : termMass <= massD + massP + massE + massCNL + massBdd
  hD : massD <= densePackTerm
  hP : massP <= remP
  hE : massE <= remE
  hCNL : massCNL <= shellCNL + remCNL
  hBdd : massBdd <= shellBdd + remBdd
  hshell : shellCNL + shellBdd <= shellTerm
  hrem : remP + remE + remCNL + remBdd <= remTerm
  haggregateBound : densePackTerm + shellTerm + remTerm <= absorbedBound

/-- Convert the proof-v4 N.3.3 aggregate data into the terminal absorption bound. -/
def TerminalNonDropAggregateAbsorptionData.toHterm
    {termMass absorbedBound : Real}
    (data : TerminalNonDropAggregateAbsorptionData termMass absorbedBound) :
    termMass <= absorbedBound :=
  data.htermSplit.trans
    ((AppendixN.aggregateAbsorption
      data.massD data.massP data.massE data.massCNL data.massBdd
      data.densePackTerm data.shellTerm data.remTerm
      data.shellCNL data.shellBdd data.remP data.remE data.remCNL data.remBdd
      data.hD data.hP data.hE data.hCNL data.hBdd data.hshell data.hrem).trans
        data.haggregateBound)

/-- Five-class upper accounting for the absorbed terminal non-drop bound. -/
structure FiveClassAbsorbedBoundData
    (absorbedBound O_D O_P O_E O_CNL O_bdd : Real) where
  absorbedD : Real
  absorbedP : Real
  absorbedE : Real
  absorbedCNL : Real
  absorbedBdd : Real
  hsplit : absorbedBound <= absorbedD + absorbedP + absorbedE + absorbedCNL + absorbedBdd
  hD : absorbedD <= O_D
  hP : absorbedP <= O_P
  hE : absorbedE <= O_E
  hCNL : absorbedCNL <= O_CNL
  hBdd : absorbedBdd <= O_bdd

/-- Collapse five-class absorbed-bound data to the N.24 absorbed comparison. -/
def FiveClassAbsorbedBoundData.toHAbsorbed
    {absorbedBound O_D O_P O_E O_CNL O_bdd : Real}
    (data : FiveClassAbsorbedBoundData absorbedBound O_D O_P O_E O_CNL O_bdd) :
    absorbedBound <= O_D + O_P + O_E + O_CNL + O_bdd := by
  exact data.hsplit.trans (by
    linarith [data.hD, data.hP, data.hE, data.hCNL, data.hBdd])

/--
Proof-v4 N.3.3 terminal non-drop absorption with no intermediate
`absorbedBound`: the aggregate terminal contribution is paid directly by the
five non-drop output classes of N.24.

The data is now recorded in the same shape as the manuscript: a finite family of
terminal output objects, each routed to one of the five non-drop classes by
N.1.0/N.5e, with class-restricted masses bounded by the five phase outputs.  The
old real decomposition `massD + massP + ...` is derived below from
`AppendixN.terminalMassV4_nonDrop_eq`.
-/
structure DirectFiveClassTerminalAbsorptionData
    (termMass O_D O_P O_E O_CNL O_bdd : Real) where
  terminalOutputs : Finset OutputObjectV4
  terminalWeight : OutputObjectV4 -> Real
  hterm :
    termMass <= ∑ O ∈ terminalOutputs, terminalWeight O
  hnonDrop :
    forall O, O ∈ terminalOutputs -> O.cls ≠ OutputClassV4.varDrop
  hD :
    AppendixN.classMassV4 terminalOutputs terminalWeight OutputClassV4.densePack <= O_D
  hP :
    AppendixN.classMassV4 terminalOutputs terminalWeight OutputClassV4.progress <= O_P
  hE :
    AppendixN.classMassV4 terminalOutputs terminalWeight OutputClassV4.endpoint <= O_E
  hCNL :
    AppendixN.classMassV4 terminalOutputs terminalWeight OutputClassV4.cnl <= O_CNL
  hBdd :
    AppendixN.classMassV4 terminalOutputs terminalWeight OutputClassV4.bdd <= O_bdd

/--
Build the direct terminal package from an explicit N.5e table-routed output
family.  In this form the `hnonDrop` field is not an input: every output object
has class `(row omega).outputClass`, and the routing table proves by cases that
this is never `O_V`.
-/
def DirectFiveClassTerminalAbsorptionData.ofTableRouted
    {sigma iota : Type} [DecidableEq sigma] [LinearOrder iota]
    (E : AppendixN.EventFibre sigma iota) (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat) (terminalWeight : OutputObjectV4 -> Real)
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (hterm :
      termMass <=
        ∑ O ∈           (E.atoms.image
            (fun omega =>
              (⟨(row omega).outputClass, supp omega, thr omega⟩ :
                OutputObjectV4))),
          terminalWeight O)
    (hD :
      AppendixN.classMassV4
          (E.atoms.image
            (fun omega =>
              (⟨(row omega).outputClass, supp omega, thr omega⟩ :
                OutputObjectV4)))
          terminalWeight OutputClassV4.densePack <= O_D)
    (hP :
      AppendixN.classMassV4
          (E.atoms.image
            (fun omega =>
              (⟨(row omega).outputClass, supp omega, thr omega⟩ :
                OutputObjectV4)))
          terminalWeight OutputClassV4.progress <= O_P)
    (hE :
      AppendixN.classMassV4
          (E.atoms.image
            (fun omega =>
              (⟨(row omega).outputClass, supp omega, thr omega⟩ :
                OutputObjectV4)))
          terminalWeight OutputClassV4.endpoint <= O_E)
    (hCNL :
      AppendixN.classMassV4
          (E.atoms.image
            (fun omega =>
              (⟨(row omega).outputClass, supp omega, thr omega⟩ :
                OutputObjectV4)))
          terminalWeight OutputClassV4.cnl <= O_CNL)
    (hBdd :
      AppendixN.classMassV4
          (E.atoms.image
            (fun omega =>
              (⟨(row omega).outputClass, supp omega, thr omega⟩ :
                OutputObjectV4)))
          terminalWeight OutputClassV4.bdd <= O_bdd) :
    DirectFiveClassTerminalAbsorptionData termMass O_D O_P O_E O_CNL O_bdd where
  terminalOutputs :=
    E.atoms.image
      (fun omega =>
        (⟨(row omega).outputClass, supp omega, thr omega⟩ : OutputObjectV4))
  terminalWeight := terminalWeight
  hterm := hterm
  hnonDrop := by
    intro O hO
    rw [Finset.mem_image] at hO
    obtain ⟨omega, _homega, rfl⟩ := hO
    exact (row omega).outputClass_ne_varDrop
  hD := hD
  hP := hP
  hE := hE
  hCNL := hCNL
  hBdd := hBdd

/--
N.3.3 class-bound certificate for a terminal family produced by the finite
Appendix N routing table.

The output family is definitionally the table image.  The remaining inputs are
exactly the terminal mass domination and the five class-restricted estimates
used in the manuscript's aggregate terminal non-drop absorption.
-/
structure TableRoutedTerminalClassBoundsData
    {sigma iota : Type} [DecidableEq sigma] [LinearOrder iota]
    (E : AppendixN.EventFibre sigma iota) (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat) (terminalWeight : OutputObjectV4 -> Real)
    (termMass O_D O_P O_E O_CNL O_bdd : Real) where
  hterm :
    termMass <=
      ∑ O ∈         E.atoms.image
          (fun omega =>
            (⟨(row omega).outputClass, supp omega, thr omega⟩ :
              OutputObjectV4)),
        terminalWeight O
  hD :
    AppendixN.classMassV4
      (E.atoms.image
        (fun omega =>
          (⟨(row omega).outputClass, supp omega, thr omega⟩ :
            OutputObjectV4)))
      terminalWeight
      OutputClassV4.densePack <= O_D
  hP :
    AppendixN.classMassV4
      (E.atoms.image
        (fun omega =>
          (⟨(row omega).outputClass, supp omega, thr omega⟩ :
            OutputObjectV4)))
      terminalWeight
      OutputClassV4.progress <= O_P
  hE :
    AppendixN.classMassV4
      (E.atoms.image
        (fun omega =>
          (⟨(row omega).outputClass, supp omega, thr omega⟩ :
            OutputObjectV4)))
      terminalWeight
      OutputClassV4.endpoint <= O_E
  hCNL :
    AppendixN.classMassV4
      (E.atoms.image
        (fun omega =>
          (⟨(row omega).outputClass, supp omega, thr omega⟩ :
            OutputObjectV4)))
      terminalWeight
      OutputClassV4.cnl <= O_CNL
  hBdd :
    AppendixN.classMassV4
      (E.atoms.image
        (fun omega =>
          (⟨(row omega).outputClass, supp omega, thr omega⟩ :
            OutputObjectV4)))
      terminalWeight
      OutputClassV4.bdd <= O_bdd

namespace TableRoutedTerminalClassBoundsData

/-- The table-routed terminal family splits into the five non-drop classes. -/
theorem termMass_le_classMasses
    {sigma iota : Type} [DecidableEq sigma] [LinearOrder iota]
    {E : AppendixN.EventFibre sigma iota} {row : iota -> AppendixN.TerminalRow}
    {supp thr : iota -> Nat} {terminalWeight : OutputObjectV4 -> Real}
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (data :
      TableRoutedTerminalClassBoundsData E row supp thr terminalWeight
        termMass O_D O_P O_E O_CNL O_bdd) :
    termMass <=
      AppendixN.classMassV4
          (E.atoms.image
            (fun omega =>
              (⟨(row omega).outputClass, supp omega, thr omega⟩ :
                OutputObjectV4)))
          terminalWeight OutputClassV4.densePack +
        AppendixN.classMassV4
          (E.atoms.image
            (fun omega =>
              (⟨(row omega).outputClass, supp omega, thr omega⟩ :
                OutputObjectV4)))
          terminalWeight OutputClassV4.progress +
        AppendixN.classMassV4
          (E.atoms.image
            (fun omega =>
              (⟨(row omega).outputClass, supp omega, thr omega⟩ :
                OutputObjectV4)))
          terminalWeight OutputClassV4.endpoint +
        AppendixN.classMassV4
          (E.atoms.image
            (fun omega =>
              (⟨(row omega).outputClass, supp omega, thr omega⟩ :
                OutputObjectV4)))
          terminalWeight OutputClassV4.cnl +
        AppendixN.classMassV4
          (E.atoms.image
            (fun omega =>
              (⟨(row omega).outputClass, supp omega, thr omega⟩ :
                OutputObjectV4)))
          terminalWeight OutputClassV4.bdd := by
  refine data.hterm.trans (le_of_eq ?_)
  exact
    AppendixN.terminalMassV4_nonDrop_eq
      (E.atoms.image
        (fun omega =>
          (⟨(row omega).outputClass, supp omega, thr omega⟩ :
            OutputObjectV4)))
      terminalWeight
      (by
        intro O hO
        rw [Finset.mem_image] at hO
        obtain ⟨omega, _homega, rfl⟩ := hO
        exact (row omega).outputClass_ne_varDrop)

/-- The table-routed class-bound certificate pays terminal mass by the five
declared phase-class quantities. -/
theorem termMass_le_classes
    {sigma iota : Type} [DecidableEq sigma] [LinearOrder iota]
    {E : AppendixN.EventFibre sigma iota} {row : iota -> AppendixN.TerminalRow}
    {supp thr : iota -> Nat} {terminalWeight : OutputObjectV4 -> Real}
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (data :
      TableRoutedTerminalClassBoundsData E row supp thr terminalWeight
        termMass O_D O_P O_E O_CNL O_bdd) :
    termMass <= O_D + O_P + O_E + O_CNL + O_bdd := by
  linarith [data.termMass_le_classMasses, data.hD, data.hP, data.hE,
    data.hCNL, data.hBdd]

end TableRoutedTerminalClassBoundsData

/-- Table-routed N.3.3 terminal-mass domination input. -/
structure TableRoutedTerminalMassInputData
    {sigma iota : Type} [DecidableEq sigma] [LinearOrder iota]
    (E : AppendixN.EventFibre sigma iota) (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat) (terminalWeight : OutputObjectV4 -> Real)
    (termMass : Real) where
  hterm :
    termMass <=
      ∑ O ∈         E.atoms.image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }),
        terminalWeight O

/-- Raw N.3.1-to-N.3.3 terminal-mass certificate for a table-routed family.

Here `terminalCharge O` is the already grouped quantity `sum_b wt_O(b)` for the
terminal output object `O`.  The two fields separate the bookkeeping split
`termMass <= sum_O terminalCharge O` from the per-output N.3.1 compression
`terminalCharge O <= terminalWeight O`. -/
structure TableRoutedTerminalMassCompressionInputData
    {sigma iota : Type} [DecidableEq sigma] [LinearOrder iota]
    (E : AppendixN.EventFibre sigma iota) (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat) (terminalWeight : OutputObjectV4 -> Real)
    (termMass : Real) where
  terminalCharge : OutputObjectV4 -> Real
  hterm_raw :
    termMass <=
      Finset.sum
        (E.atoms.image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }))
        terminalCharge
  hcompression :
    ∀ O,
      O ∈
        E.atoms.image
          (fun omega =>
            { cls := (row omega).outputClass
              supportId := supp omega
              thresholdLayer := thr omega }) ->
      terminalCharge O <= terminalWeight O

namespace TableRoutedTerminalMassCompressionInputData

/-- Project the grouped N.3.1 compression certificate to the N.3.3 terminal-mass
input consumed by the table-routed terminal leaf. -/
def toTableRoutedTerminalMassInputData
    {sigma iota : Type} [DecidableEq sigma] [LinearOrder iota]
    {E : AppendixN.EventFibre sigma iota} {row : iota -> AppendixN.TerminalRow}
    {supp thr : iota -> Nat} {terminalWeight : OutputObjectV4 -> Real}
    {termMass : Real}
    (data :
      TableRoutedTerminalMassCompressionInputData E row supp thr terminalWeight
        termMass) :
    TableRoutedTerminalMassInputData E row supp thr terminalWeight termMass where
  hterm := data.hterm_raw.trans (Finset.sum_le_sum data.hcompression)

end TableRoutedTerminalMassCompressionInputData

/-- Table-routed N.3.3 DensePack-class bound input. -/
structure TableRoutedDensePackClassInputData
    {sigma iota : Type} [DecidableEq sigma] [LinearOrder iota]
    (E : AppendixN.EventFibre sigma iota) (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat) (terminalWeight : OutputObjectV4 -> Real)
    (O_D : Real) where
  hD :
    AppendixN.classMassV4
      (E.atoms.image
        (fun omega =>
          { cls := (row omega).outputClass
            supportId := supp omega
            thresholdLayer := thr omega }))
      terminalWeight
      OutputClassV4.densePack <= O_D

/-- Proof-v4 DensePack class-bound provider for the table-routed N.3.3 leaf.

The dense class is paid by identifying the routed dense outputs with a
subfamily of the fixed-layer DensePack point set.  The provider supplies the
point map, its injectivity on the dense class, and the unit-weight domination
needed to turn the class mass into a cardinality bound; the K.1.1 cardinal
comparison to the DensePack phase term is then generated here. -/
structure TableRoutedDensePackClassSupportInputData
    {sigma iota : Type} [DecidableEq sigma] [LinearOrder iota]
    (E : AppendixN.EventFibre sigma iota) (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat) (terminalWeight : OutputObjectV4 -> Real)
    {cStar xi X : Real} (O_D : Real) where
  phase : ClosurePhaseData cStar xi X
  pointOf : OutputObjectV4 -> Nat
  hpoint_mem :
    forall O,
      O ∈
          (E.atoms.image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega })).filter
            (fun O => O.cls = OutputClassV4.densePack) ->
        pointOf O ∈ phase.densePack.densePackPoints
  hinj :
    forall O₁,
      O₁ ∈
          (E.atoms.image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega })).filter
            (fun O => O.cls = OutputClassV4.densePack) ->
      forall O₂,
        O₂ ∈
            (E.atoms.image
              (fun omega =>
                { cls := (row omega).outputClass
                  supportId := supp omega
                  thresholdLayer := thr omega })).filter
              (fun O => O.cls = OutputClassV4.densePack) ->
        pointOf O₁ = pointOf O₂ -> O₁ = O₂
  hweight_le_one :
    forall O,
      O ∈
          (E.atoms.image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega })).filter
            (fun O => O.cls = OutputClassV4.densePack) ->
        terminalWeight O <= 1
  hbudget_le_output : termDensePack phase <= O_D

namespace TableRoutedDensePackClassSupportInputData

/-- Forget the DensePack support explanation to the raw N.3.3 dense-class
input. -/
def toTableRoutedDensePackClassInputData
    {sigma iota : Type} [DecidableEq sigma] [LinearOrder iota]
    {E : AppendixN.EventFibre sigma iota} {row : iota -> AppendixN.TerminalRow}
    {supp thr : iota -> Nat} {terminalWeight : OutputObjectV4 -> Real}
    {cStar xi X O_D : Real}
    (data :
      TableRoutedDensePackClassSupportInputData E row supp thr terminalWeight
        (cStar := cStar) (xi := xi) (X := X) O_D) :
    TableRoutedDensePackClassInputData E row supp thr terminalWeight O_D where
  hD := by
    let objects : Finset OutputObjectV4 :=
      E.atoms.image
        (fun omega =>
          { cls := (row omega).outputClass
            supportId := supp omega
            thresholdLayer := thr omega })
    let denseObjects : Finset OutputObjectV4 :=
      objects.filter (fun O => O.cls = OutputClassV4.densePack)
    have hsum_le_card :
        (∑ O ∈ denseObjects, terminalWeight O) <= (denseObjects.card : Real) := by
      calc
        (∑ O ∈ denseObjects, terminalWeight O)
            <= ∑ O ∈ denseObjects, (1 : Real) := by
              exact Finset.sum_le_sum (fun O hO => data.hweight_le_one O hO)
        _ = (denseObjects.card : Real) := by simp
    have hcard_le :
        denseObjects.card <= data.phase.densePack.densePackPoints.card := by
      let f :
          {O : OutputObjectV4 // O ∈ denseObjects} ->
            {x : Nat // x ∈ data.phase.densePack.densePackPoints} :=
        fun O => ⟨data.pointOf O.1, data.hpoint_mem O.1 O.2⟩
      have hf : Function.Injective f := by
        intro a b h
        apply Subtype.ext
        apply data.hinj a.1 a.2 b.1 b.2
        have hval : (f a).1 = (f b).1 := congrArg Subtype.val h
        simpa [f] using hval
      have hcard := Fintype.card_le_of_injective f hf
      simpa [f] using hcard
    have hcard_real :
        (denseObjects.card : Real) <= termDensePack data.phase := by
      change (denseObjects.card : Real) <=
        (data.phase.densePack.densePackPoints.card : Real)
      exact_mod_cast hcard_le
    unfold AppendixN.classMassV4
    change (∑ O ∈ denseObjects, terminalWeight O) <= O_D
    exact hsum_le_card.trans (hcard_real.trans data.hbudget_le_output)

end TableRoutedDensePackClassSupportInputData

/-- Table-routed N.3.3 progress-class bound input. -/
structure TableRoutedProgressClassInputData
    {sigma iota : Type} [DecidableEq sigma] [LinearOrder iota]
    (E : AppendixN.EventFibre sigma iota) (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat) (terminalWeight : OutputObjectV4 -> Real)
    (O_P : Real) where
  hP :
    AppendixN.classMassV4
      (E.atoms.image
        (fun omega =>
          { cls := (row omega).outputClass
            supportId := supp omega
            thresholdLayer := thr omega }))
      terminalWeight
      OutputClassV4.progress <= O_P

/-- Proof-v4 progress-class provider for the table-routed N.3.3 leaf.

Progress outputs are paid by embedding them into the Chernoff high-cost
subfamily.  The provider supplies the path map, high-cost membership,
injectivity on routed progress outputs, and pointwise weight domination; the
projection below performs the finite weighted-sum comparison. -/
structure TableRoutedProgressClassChernoffInputData
    {sigma iota : Type} [DecidableEq sigma] [LinearOrder iota]
    (E : AppendixN.EventFibre sigma iota) (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat) (terminalWeight : OutputObjectV4 -> Real)
    {cStar xi X : Real} (O_P : Real) where
  phase : ClosurePhaseData cStar xi X
  pathDecEq : DecidableEq phase.chernoff.α
  pathOf : OutputObjectV4 -> phase.chernoff.α
  hpath_mem :
    forall O,
      O ∈
          (E.atoms.image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega })).filter
            (fun O => O.cls = OutputClassV4.progress) ->
        pathOf O ∈
          highCostSet phase.chernoff.paths phase.chernoff.cost phase.chernoff.Y
  hinj :
    forall O₁,
      O₁ ∈
          (E.atoms.image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega })).filter
            (fun O => O.cls = OutputClassV4.progress) ->
      forall O₂,
        O₂ ∈
            (E.atoms.image
              (fun omega =>
                { cls := (row omega).outputClass
                  supportId := supp omega
                  thresholdLayer := thr omega })).filter
              (fun O => O.cls = OutputClassV4.progress) ->
        pathOf O₁ = pathOf O₂ -> O₁ = O₂
  hweight_le_path :
    forall O,
      O ∈
          (E.atoms.image
            (fun omega =>
              { cls := (row omega).outputClass
                supportId := supp omega
                thresholdLayer := thr omega })).filter
            (fun O => O.cls = OutputClassV4.progress) ->
        terminalWeight O <= phase.chernoff.weight (pathOf O)
  hbudget_le_output : termChernoff phase <= O_P

namespace TableRoutedProgressClassChernoffInputData

/-- Forget the Chernoff high-cost explanation to the raw N.3.3 progress-class
input. -/
def toTableRoutedProgressClassInputData
    {sigma iota : Type} [DecidableEq sigma] [LinearOrder iota]
    {E : AppendixN.EventFibre sigma iota} {row : iota -> AppendixN.TerminalRow}
    {supp thr : iota -> Nat} {terminalWeight : OutputObjectV4 -> Real}
    {cStar xi X O_P : Real}
    (data :
      TableRoutedProgressClassChernoffInputData E row supp thr terminalWeight
        (cStar := cStar) (xi := xi) (X := X) O_P) :
    TableRoutedProgressClassInputData E row supp thr terminalWeight O_P where
  hP := by
    letI : DecidableEq data.phase.chernoff.α := data.pathDecEq
    let objects : Finset OutputObjectV4 :=
      E.atoms.image
        (fun omega =>
          { cls := (row omega).outputClass
            supportId := supp omega
            thresholdLayer := thr omega })
    let progressObjects : Finset OutputObjectV4 :=
      objects.filter (fun O => O.cls = OutputClassV4.progress)
    let progressPaths : Finset data.phase.chernoff.α :=
      progressObjects.image data.pathOf
    have hsum_le_paths :
        (∑ O ∈ progressObjects, terminalWeight O) <=
          ∑ O ∈ progressObjects, data.phase.chernoff.weight (data.pathOf O) := by
      exact Finset.sum_le_sum (fun O hO => data.hweight_le_path O hO)
    have hsum_image :
        (∑ p ∈ progressPaths, data.phase.chernoff.weight p) =
          ∑ O ∈ progressObjects, data.phase.chernoff.weight (data.pathOf O) := by
      dsimp [progressPaths]
      rw [Finset.sum_image]
      intro a ha b hb h
      exact data.hinj a ha b hb h
    have hpaths_subset :
        progressPaths ⊆
          highCostSet data.phase.chernoff.paths data.phase.chernoff.cost
            data.phase.chernoff.Y := by
      intro p hp
      dsimp [progressPaths] at hp
      rw [Finset.mem_image] at hp
      obtain ⟨O, hO, rfl⟩ := hp
      exact data.hpath_mem O hO
    have hpaths_le :
        weightedMass progressPaths data.phase.chernoff.weight <=
          termChernoff data.phase := by
      show weightedMass progressPaths data.phase.chernoff.weight <=
        weightedMass
          (highCostSet data.phase.chernoff.paths data.phase.chernoff.cost
            data.phase.chernoff.Y)
          data.phase.chernoff.weight
      refine weightedMass_mono_subset hpaths_subset ?_
      intro p hp
      exact data.phase.chernoff.weight_nonneg p (mem_highCostSet.1 hp).1
    unfold AppendixN.classMassV4
    change (∑ O ∈ progressObjects, terminalWeight O) <= O_P
    calc
      (∑ O ∈ progressObjects, terminalWeight O)
          <= ∑ O ∈ progressObjects,
              data.phase.chernoff.weight (data.pathOf O) := hsum_le_paths
      _ = weightedMass progressPaths data.phase.chernoff.weight := by
        unfold weightedMass
        exact hsum_image.symm
      _ <= termChernoff data.phase := hpaths_le
      _ <= O_P := data.hbudget_le_output

end TableRoutedProgressClassChernoffInputData

/-- Table-routed N.3.3 endpoint-class bound input. -/
structure TableRoutedEndpointClassInputData
    {sigma iota : Type} [DecidableEq sigma] [LinearOrder iota]
    (E : AppendixN.EventFibre sigma iota) (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat) (terminalWeight : OutputObjectV4 -> Real)
    (O_E : Real) where
  hE :
    AppendixN.classMassV4
      (E.atoms.image
        (fun omega =>
          { cls := (row omega).outputClass
            supportId := supp omega
            thresholdLayer := thr omega }))
      terminalWeight
      OutputClassV4.endpoint <= O_E

/-- Proof-v4 endpoint-class provider for the table-routed N.3.3 leaf.

Endpoint outputs are paid by the Return/OLC leakage summand.  The provider
identifies the table-routed endpoint class mass with the OLC return summand;
the projection proves the bookkeeping comparison from that summand to
`termReturn` using the nonnegativity of the other return pieces. -/
structure TableRoutedEndpointClassReturnInputData
    {sigma iota : Type} [DecidableEq sigma] [LinearOrder iota]
    (E : AppendixN.EventFibre sigma iota) (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat) (terminalWeight : OutputObjectV4 -> Real)
    {cStar xi X : Real} (O_E : Real) where
  phase : ClosurePhaseData cStar xi X
  hclass_le_olc :
    AppendixN.classMassV4
      (E.atoms.image
        (fun omega =>
          { cls := (row omega).outputClass
            supportId := supp omega
            thresholdLayer := thr omega }))
      terminalWeight
      OutputClassV4.endpoint <= phase.returnPkg.olc
  hOrdinaryShort_nonneg : 0 <= phase.returnPkg.ordinaryShort
  hSemiperiodic_nonneg : 0 <= phase.returnPkg.semiperiodic
  hNonlocalLong_nonneg : 0 <= phase.returnPkg.nonlocalLong
  hbudget_le_output : termReturn phase <= O_E

namespace TableRoutedEndpointClassReturnInputData

/-- Forget the Return/OLC explanation to the raw N.3.3 endpoint-class input. -/
def toTableRoutedEndpointClassInputData
    {sigma iota : Type} [DecidableEq sigma] [LinearOrder iota]
    {E : AppendixN.EventFibre sigma iota} {row : iota -> AppendixN.TerminalRow}
    {supp thr : iota -> Nat} {terminalWeight : OutputObjectV4 -> Real}
    {cStar xi X O_E : Real}
    (data :
      TableRoutedEndpointClassReturnInputData E row supp thr terminalWeight
        (cStar := cStar) (xi := xi) (X := X) O_E) :
    TableRoutedEndpointClassInputData E row supp thr terminalWeight O_E where
  hE := by
    have holc_le_return : data.phase.returnPkg.olc <= termReturn data.phase := by
      show data.phase.returnPkg.olc <=
        data.phase.returnPkg.ordinaryShort + data.phase.returnPkg.semiperiodic +
          data.phase.returnPkg.olc + data.phase.returnPkg.nonlocalLong
      linarith [data.hOrdinaryShort_nonneg, data.hSemiperiodic_nonneg,
        data.hNonlocalLong_nonneg]
    exact data.hclass_le_olc.trans (holc_le_return.trans data.hbudget_le_output)

end TableRoutedEndpointClassReturnInputData

/-- Table-routed N.3.3 clean-CNL-class bound input. -/
structure TableRoutedCNLClassInputData
    {sigma iota : Type} [DecidableEq sigma] [LinearOrder iota]
    (E : AppendixN.EventFibre sigma iota) (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat) (terminalWeight : OutputObjectV4 -> Real)
    (O_CNL : Real) where
  hCNL :
    AppendixN.classMassV4
      (E.atoms.image
        (fun omega =>
          { cls := (row omega).outputClass
            supportId := supp omega
            thresholdLayer := thr omega }))
      terminalWeight
      OutputClassV4.cnl <= O_CNL

/-- Proof-v4 CNL class-bound provider for the table-routed N.3.3 leaf.

The CNL class is not meant to be paid by a naked `hCNL` inequality.  The
manuscript route first identifies the table-routed CNL class mass with a clean
CNL contribution, then pays that contribution by the L.1.2/G.35 weighted-Kraft
shell leaf, and finally compares the displayed CNL budget with the target
class quantity `O_CNL`. -/
structure TableRoutedCNLClassKraftInputData
    {sigma iota : Type} [DecidableEq sigma] [LinearOrder iota]
    (E : AppendixN.EventFibre sigma iota) (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat) (terminalWeight : OutputObjectV4 -> Real)
    {shell : FailingDyadicShell} {cStar xi : Real}
    (O_CNL : Real) where
  cnlLeaf : CNLStandardWeightedKraftShellInputData shell cStar xi
  cleanTerm : Real
  hclass_le_clean :
    AppendixN.classMassV4
      (E.atoms.image
        (fun omega =>
          { cls := (row omega).outputClass
            supportId := supp omega
            thresholdLayer := thr omega }))
      terminalWeight
      OutputClassV4.cnl <= cleanTerm
  hclean_bound :
    0 <= cleanTerm /\ cleanTerm <= cStar * xi * (shell.X : Real) / 6
  hbudget_le_output :
    cStar * xi * (shell.X : Real) / 6 <= O_CNL

namespace TableRoutedCNLClassKraftInputData

/-- Forget the proof-v4 CNL explanation to the raw N.3.3 CNL class input. -/
def toTableRoutedCNLClassInputData
    {sigma iota : Type} [DecidableEq sigma] [LinearOrder iota]
    {E : AppendixN.EventFibre sigma iota} {row : iota -> AppendixN.TerminalRow}
    {supp thr : iota -> Nat} {terminalWeight : OutputObjectV4 -> Real}
    {shell : FailingDyadicShell} {cStar xi O_CNL : Real}
    (data :
      TableRoutedCNLClassKraftInputData E row supp thr terminalWeight
        (shell := shell) (cStar := cStar) (xi := xi) O_CNL) :
    TableRoutedCNLClassInputData E row supp thr terminalWeight O_CNL where
  hCNL := data.hclass_le_clean.trans
    (data.hclean_bound.2.trans data.hbudget_le_output)

end TableRoutedCNLClassKraftInputData

/-- Table-routed N.3.3 bounded-dirty-return-class bound input. -/
structure TableRoutedBddClassInputData
    {sigma iota : Type} [DecidableEq sigma] [LinearOrder iota]
    (E : AppendixN.EventFibre sigma iota) (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat) (terminalWeight : OutputObjectV4 -> Real)
    (O_bdd : Real) where
  hBdd :
    AppendixN.classMassV4
      (E.atoms.image
        (fun omega =>
          { cls := (row omega).outputClass
            supportId := supp omega
            thresholdLayer := thr omega }))
      terminalWeight
      OutputClassV4.bdd <= O_bdd

/-- Table-routed N.3.3 five non-drop class-bound input. -/
structure TableRoutedTerminalFiveClassInputData
    {sigma iota : Type} [DecidableEq sigma] [LinearOrder iota]
    (E : AppendixN.EventFibre sigma iota) (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat) (terminalWeight : OutputObjectV4 -> Real)
    (O_D O_P O_E O_CNL O_bdd : Real) where
  densePack :
    TableRoutedDensePackClassInputData E row supp thr terminalWeight O_D
  progress :
    TableRoutedProgressClassInputData E row supp thr terminalWeight O_P
  endpoint :
    TableRoutedEndpointClassInputData E row supp thr terminalWeight O_E
  cnl :
    TableRoutedCNLClassInputData E row supp thr terminalWeight O_CNL
  bdd :
    TableRoutedBddClassInputData E row supp thr terminalWeight O_bdd

/--
Table-routed N.1.0/N.5e terminal absorption data.

This is the manuscript-shaped version of the direct five-class terminal package:
the terminal output family is explicitly the image of an Appendix N event fibre
under the finite routing table.  Consequently the non-drop fact is not a
provider field; it is derived from `TerminalRow.outputClass_ne_varDrop` in
`toDirect`.
-/
structure TableRoutedDirectFiveClassTerminalAbsorptionData
    (termMass O_D O_P O_E O_CNL O_bdd : Real) where
  sigma : Type
  iota : Type
  decSigma : DecidableEq sigma
  linIota : LinearOrder iota
  E : @AppendixN.EventFibre sigma iota decSigma linIota
  row : iota -> AppendixN.TerminalRow
  supp : iota -> Nat
  thr : iota -> Nat
  terminalWeight : OutputObjectV4 -> Real
  bounds_input :
    @TableRoutedTerminalClassBoundsData sigma iota decSigma linIota E row supp
      thr terminalWeight termMass O_D O_P O_E O_CNL O_bdd

namespace TableRoutedDirectFiveClassTerminalAbsorptionData

/-- Project the table-routed terminal-mass input. -/
def terminalMass
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (data :
      TableRoutedDirectFiveClassTerminalAbsorptionData
        termMass O_D O_P O_E O_CNL O_bdd) :
    @TableRoutedTerminalMassInputData data.sigma data.iota data.decSigma data.linIota
      data.E data.row data.supp data.thr data.terminalWeight termMass := by
  letI : DecidableEq data.sigma := data.decSigma
  letI : LinearOrder data.iota := data.linIota
  exact { hterm := data.bounds_input.hterm }

/-- Project the table-routed five-class-bound input. -/
def classBounds
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (data :
      TableRoutedDirectFiveClassTerminalAbsorptionData
        termMass O_D O_P O_E O_CNL O_bdd) :
    @TableRoutedTerminalFiveClassInputData data.sigma data.iota data.decSigma data.linIota
      data.E data.row data.supp data.thr data.terminalWeight
      O_D O_P O_E O_CNL O_bdd := by
  letI : DecidableEq data.sigma := data.decSigma
  letI : LinearOrder data.iota := data.linIota
  exact {
    densePack := { hD := data.bounds_input.hD }
    progress := { hP := data.bounds_input.hP }
    endpoint := { hE := data.bounds_input.hE }
    cnl := { hCNL := data.bounds_input.hCNL }
    bdd := { hBdd := data.bounds_input.hBdd } }

/-- Bundle the table-routed terminal mass and five class estimates into the
N.3.3 class-bound certificate. -/
def bounds
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (data :
      TableRoutedDirectFiveClassTerminalAbsorptionData
        termMass O_D O_P O_E O_CNL O_bdd) :
    @TableRoutedTerminalClassBoundsData data.sigma data.iota data.decSigma data.linIota
      data.E data.row data.supp data.thr data.terminalWeight
      termMass O_D O_P O_E O_CNL O_bdd := by
  letI : DecidableEq data.sigma := data.decSigma
  letI : LinearOrder data.iota := data.linIota
  exact data.bounds_input

/-- The table-routed package forgets to the older direct package, deriving
`hnonDrop` from the finite Appendix N routing table rather than requesting it as
an input. -/
def toDirect
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (data :
      TableRoutedDirectFiveClassTerminalAbsorptionData
        termMass O_D O_P O_E O_CNL O_bdd) :
    DirectFiveClassTerminalAbsorptionData termMass O_D O_P O_E O_CNL O_bdd := by
  letI : DecidableEq data.sigma := data.decSigma
  letI : LinearOrder data.iota := data.linIota
  exact {
    terminalOutputs :=
      data.E.atoms.image
        (fun omega =>
          (⟨(data.row omega).outputClass, data.supp omega, data.thr omega⟩ :
            OutputObjectV4))
    terminalWeight := data.terminalWeight
    hterm := data.bounds.hterm
    hnonDrop := by
      intro O hO
      rw [Finset.mem_image] at hO
      obtain ⟨omega, _homega, rfl⟩ := hO
      exact (data.row omega).outputClass_ne_varDrop
    hD := data.bounds.hD
    hP := data.bounds.hP
    hE := data.bounds.hE
    hCNL := data.bounds.hCNL
    hBdd := data.bounds.hBdd }

end TableRoutedDirectFiveClassTerminalAbsorptionData

/--
Table-routed N.1.0/N.5e terminal absorption data with the event-state
decidability chosen internally.  This is the same manuscript data as
`TableRoutedDirectFiveClassTerminalAbsorptionData`, but the strongest
canonical-Y endpoint no longer asks the provider to supply the Lean-only
`DecidableEq sigma` instance.
-/
structure ClassicalTableRoutedDirectFiveClassTerminalAbsorptionData
    (termMass O_D O_P O_E O_CNL O_bdd : Real) where
  sigma : Type
  iota : Type
  linIota : LinearOrder iota
  E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) linIota
  row : iota -> AppendixN.TerminalRow
  supp : iota -> Nat
  thr : iota -> Nat
  terminalWeight : OutputObjectV4 -> Real
  bounds_input :
    @TableRoutedTerminalClassBoundsData sigma iota (Classical.decEq sigma)
      linIota E row supp thr terminalWeight
      termMass O_D O_P O_E O_CNL O_bdd

/-- Assemble the internally-decidable N.3.3 terminal package from the finite
table-routed terminal family and its five class-bound certificate. -/
def ClassicalTableRoutedDirectFiveClassTerminalAbsorptionData.ofClosedN33
    {sigma iota : Type} [LinearOrder iota]
    (E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) inferInstance)
    (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat)
    (terminalWeight : OutputObjectV4 -> Real)
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (bounds_input :
      @TableRoutedTerminalClassBoundsData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight
        termMass O_D O_P O_E O_CNL O_bdd) :
    ClassicalTableRoutedDirectFiveClassTerminalAbsorptionData
      termMass O_D O_P O_E O_CNL O_bdd where
  sigma := sigma
  iota := iota
  linIota := inferInstance
  E := E
  row := row
  supp := supp
  thr := thr
  terminalWeight := terminalWeight
  bounds_input := bounds_input

/--
N.3.3 terminal absorption leaf before the table-routed terminal package is
packed: the terminal-mass input and the five class-bound inputs are kept
separate, matching the final summation step of proof_v4.
-/
structure ClassicalTerminalN33LeafData
    (termMass O_D O_P O_E O_CNL O_bdd : Real) where
  sigma : Type
  iota : Type
  linIota : LinearOrder iota
  E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) linIota
  row : iota -> AppendixN.TerminalRow
  supp : iota -> Nat
  thr : iota -> Nat
  terminalWeight : OutputObjectV4 -> Real
  terminalMass :
    @TableRoutedTerminalMassInputData sigma iota (Classical.decEq sigma)
      linIota E row supp thr terminalWeight termMass
  classBounds :
    @TableRoutedTerminalFiveClassInputData sigma iota (Classical.decEq sigma)
      linIota E row supp thr terminalWeight O_D O_P O_E O_CNL O_bdd

/--
N.3.3 terminal absorption leaf with the terminal-mass input and all five
non-drop class estimates kept as separate proof-v4 inputs.
-/
structure ClassicalTerminalN33SeparatedLeafData
    (termMass O_D O_P O_E O_CNL O_bdd : Real) where
  sigma : Type
  iota : Type
  linIota : LinearOrder iota
  E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) linIota
  row : iota -> AppendixN.TerminalRow
  supp : iota -> Nat
  thr : iota -> Nat
  terminalWeight : OutputObjectV4 -> Real
  terminalMass :
    @TableRoutedTerminalMassInputData sigma iota (Classical.decEq sigma)
      linIota E row supp thr terminalWeight termMass
  densePack :
    @TableRoutedDensePackClassInputData sigma iota (Classical.decEq sigma)
      linIota E row supp thr terminalWeight O_D
  progress :
    @TableRoutedProgressClassInputData sigma iota (Classical.decEq sigma)
      linIota E row supp thr terminalWeight O_P
  endpoint :
    @TableRoutedEndpointClassInputData sigma iota (Classical.decEq sigma)
      linIota E row supp thr terminalWeight O_E
  cnl :
    @TableRoutedCNLClassInputData sigma iota (Classical.decEq sigma)
      linIota E row supp thr terminalWeight O_CNL
  bdd :
    @TableRoutedBddClassInputData sigma iota (Classical.decEq sigma)
      linIota E row supp thr terminalWeight O_bdd

namespace ClassicalTerminalN33LeafData

/-- Bundle the separated N.3.3 terminal-mass and five-class leaves. -/
def toClassicalTableRoutedDirectFiveClassTerminalAbsorptionData
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (data :
      ClassicalTerminalN33LeafData termMass O_D O_P O_E O_CNL O_bdd) :
    ClassicalTableRoutedDirectFiveClassTerminalAbsorptionData
      termMass O_D O_P O_E O_CNL O_bdd := by
  letI : DecidableEq data.sigma := Classical.decEq data.sigma
  letI : LinearOrder data.iota := data.linIota
  exact
    ClassicalTableRoutedDirectFiveClassTerminalAbsorptionData.ofClosedN33
      data.E data.row data.supp data.thr data.terminalWeight
      { hterm := data.terminalMass.hterm
        hD := data.classBounds.densePack.hD
        hP := data.classBounds.progress.hP
        hE := data.classBounds.endpoint.hE
        hCNL := data.classBounds.cnl.hCNL
        hBdd := data.classBounds.bdd.hBdd }

end ClassicalTerminalN33LeafData

namespace ClassicalTerminalN33SeparatedLeafData

/-- Assemble the fully separated N.3.3 terminal leaf from the table-routed
terminal family, the terminal-mass domination input, and the five class-bound
inputs. -/
def ofClosedN33
    {sigma iota : Type} [LinearOrder iota]
    (E : @AppendixN.EventFibre sigma iota (Classical.decEq sigma) inferInstance)
    (row : iota -> AppendixN.TerminalRow)
    (supp thr : iota -> Nat)
    (terminalWeight : OutputObjectV4 -> Real)
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (terminalMass :
      @TableRoutedTerminalMassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight termMass)
    (densePack :
      @TableRoutedDensePackClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_D)
    (progress :
      @TableRoutedProgressClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_P)
    (endpoint :
      @TableRoutedEndpointClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_E)
    (cnl :
      @TableRoutedCNLClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_CNL)
    (bdd :
      @TableRoutedBddClassInputData sigma iota (Classical.decEq sigma)
        inferInstance E row supp thr terminalWeight O_bdd) :
    ClassicalTerminalN33SeparatedLeafData
      termMass O_D O_P O_E O_CNL O_bdd where
  sigma := sigma
  iota := iota
  linIota := inferInstance
  E := E
  row := row
  supp := supp
  thr := thr
  terminalWeight := terminalWeight
  terminalMass := terminalMass
  densePack := densePack
  progress := progress
  endpoint := endpoint
  cnl := cnl
  bdd := bdd

/-- Bundle the fully separated N.3.3 terminal leaf into the existing terminal
mass/five-class leaf. -/
def toClassicalTerminalN33LeafData
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (data :
      ClassicalTerminalN33SeparatedLeafData
        termMass O_D O_P O_E O_CNL O_bdd) :
    ClassicalTerminalN33LeafData termMass O_D O_P O_E O_CNL O_bdd := by
  letI : DecidableEq data.sigma := Classical.decEq data.sigma
  letI : LinearOrder data.iota := data.linIota
  exact {
    sigma := data.sigma
    iota := data.iota
    linIota := data.linIota
    E := data.E
    row := data.row
    supp := data.supp
    thr := data.thr
    terminalWeight := data.terminalWeight
    terminalMass := data.terminalMass
    classBounds := {
      densePack := data.densePack
      progress := data.progress
      endpoint := data.endpoint
      cnl := data.cnl
      bdd := data.bdd } }

/-- Bundle the fully separated N.3.3 leaf into the internally-decidable
table-routed terminal package. -/
def toClassicalTableRoutedDirectFiveClassTerminalAbsorptionData
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (data :
      ClassicalTerminalN33SeparatedLeafData
        termMass O_D O_P O_E O_CNL O_bdd) :
    ClassicalTableRoutedDirectFiveClassTerminalAbsorptionData
      termMass O_D O_P O_E O_CNL O_bdd :=
  data.toClassicalTerminalN33LeafData.toClassicalTableRoutedDirectFiveClassTerminalAbsorptionData

/-- The fully separated N.3.3 leaf pays terminal non-drop mass into the five
non-drop classes. -/
theorem termMass_le_classes
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (data :
      ClassicalTerminalN33SeparatedLeafData
        termMass O_D O_P O_E O_CNL O_bdd) :
    termMass <= O_D + O_P + O_E + O_CNL + O_bdd := by
  letI : DecidableEq data.sigma := Classical.decEq data.sigma
  letI : LinearOrder data.iota := data.linIota
  let bounds :
      @TableRoutedTerminalClassBoundsData data.sigma data.iota
        (Classical.decEq data.sigma) data.linIota data.E data.row data.supp
        data.thr data.terminalWeight termMass O_D O_P O_E O_CNL O_bdd := {
    hterm := data.terminalMass.hterm
    hD := data.densePack.hD
    hP := data.progress.hP
    hE := data.endpoint.hE
    hCNL := data.cnl.hCNL
    hBdd := data.bdd.hBdd }
  exact bounds.termMass_le_classes

end ClassicalTerminalN33SeparatedLeafData

namespace ClassicalTableRoutedDirectFiveClassTerminalAbsorptionData

/-- Project the internally-decidable terminal package to the older table-routed
interface. -/
def toTableRoutedDirectFiveClassTerminalAbsorptionData
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (data :
      ClassicalTableRoutedDirectFiveClassTerminalAbsorptionData
        termMass O_D O_P O_E O_CNL O_bdd) :
    TableRoutedDirectFiveClassTerminalAbsorptionData
      termMass O_D O_P O_E O_CNL O_bdd where
  sigma := data.sigma
  iota := data.iota
  decSigma := Classical.decEq data.sigma
  linIota := data.linIota
  E := data.E
  row := data.row
  supp := data.supp
  thr := data.thr
  terminalWeight := data.terminalWeight
  bounds_input := data.bounds_input

/-- Project the table-routed terminal-mass input. -/
def terminalMass
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (data :
      ClassicalTableRoutedDirectFiveClassTerminalAbsorptionData
        termMass O_D O_P O_E O_CNL O_bdd) :
    @TableRoutedTerminalMassInputData data.sigma data.iota
      (Classical.decEq data.sigma) data.linIota data.E data.row data.supp
      data.thr data.terminalWeight termMass :=
  data.toTableRoutedDirectFiveClassTerminalAbsorptionData.terminalMass

/-- Project the table-routed five-class-bound input. -/
def classBounds
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (data :
      ClassicalTableRoutedDirectFiveClassTerminalAbsorptionData
        termMass O_D O_P O_E O_CNL O_bdd) :
    @TableRoutedTerminalFiveClassInputData data.sigma data.iota
      (Classical.decEq data.sigma) data.linIota data.E data.row data.supp
      data.thr data.terminalWeight O_D O_P O_E O_CNL O_bdd :=
  data.toTableRoutedDirectFiveClassTerminalAbsorptionData.classBounds

/-- Bundle the table-routed terminal mass and five class estimates into the
N.3.3 class-bound certificate. -/
def bounds
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (data :
      ClassicalTableRoutedDirectFiveClassTerminalAbsorptionData
        termMass O_D O_P O_E O_CNL O_bdd) :
    @TableRoutedTerminalClassBoundsData data.sigma data.iota
      (Classical.decEq data.sigma) data.linIota data.E data.row data.supp
      data.thr data.terminalWeight termMass O_D O_P O_E O_CNL O_bdd :=
  data.toTableRoutedDirectFiveClassTerminalAbsorptionData.bounds

/-- Forget the internally-decidable table-routed package to the older direct
package, deriving non-drop from the Appendix N routing table. -/
def toDirect
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (data :
      ClassicalTableRoutedDirectFiveClassTerminalAbsorptionData
        termMass O_D O_P O_E O_CNL O_bdd) :
    DirectFiveClassTerminalAbsorptionData termMass O_D O_P O_E O_CNL O_bdd :=
  data.toTableRoutedDirectFiveClassTerminalAbsorptionData.toDirect

end ClassicalTableRoutedDirectFiveClassTerminalAbsorptionData

/-- The routed terminal output family splits into the five non-drop class masses. -/
theorem DirectFiveClassTerminalAbsorptionData.termMass_le_classMasses
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (data : DirectFiveClassTerminalAbsorptionData termMass O_D O_P O_E O_CNL O_bdd) :
    termMass <=
      AppendixN.classMassV4 data.terminalOutputs data.terminalWeight OutputClassV4.densePack +
        AppendixN.classMassV4 data.terminalOutputs data.terminalWeight OutputClassV4.progress +
        AppendixN.classMassV4 data.terminalOutputs data.terminalWeight OutputClassV4.endpoint +
        AppendixN.classMassV4 data.terminalOutputs data.terminalWeight OutputClassV4.cnl +
        AppendixN.classMassV4 data.terminalOutputs data.terminalWeight OutputClassV4.bdd := by
  exact data.hterm.trans (le_of_eq
    (AppendixN.terminalMassV4_nonDrop_eq
      data.terminalOutputs data.terminalWeight data.hnonDrop))

/-- Collapse direct five-class terminal absorption to the old aggregate package. -/
def DirectFiveClassTerminalAbsorptionData.toTerminalAbsorption
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (data : DirectFiveClassTerminalAbsorptionData termMass O_D O_P O_E O_CNL O_bdd) :
    TerminalNonDropAggregateAbsorptionData termMass
      (O_D + O_P + O_E + O_CNL + O_bdd) := {
  massD :=
    AppendixN.classMassV4 data.terminalOutputs data.terminalWeight
      OutputClassV4.densePack
  massP :=
    AppendixN.classMassV4 data.terminalOutputs data.terminalWeight
      OutputClassV4.progress
  massE :=
    AppendixN.classMassV4 data.terminalOutputs data.terminalWeight
      OutputClassV4.endpoint
  massCNL :=
    AppendixN.classMassV4 data.terminalOutputs data.terminalWeight
      OutputClassV4.cnl
  massBdd :=
    AppendixN.classMassV4 data.terminalOutputs data.terminalWeight
      OutputClassV4.bdd
  densePackTerm := O_D
  shellTerm := 0
  remTerm := O_P + O_E + O_CNL + O_bdd
  shellCNL := 0
  shellBdd := 0
  remP := O_P
  remE := O_E
  remCNL := O_CNL
  remBdd := O_bdd
  htermSplit := data.termMass_le_classMasses
  hD := data.hD
  hP := data.hP
  hE := data.hE
  hCNL := by simpa using data.hCNL
  hBdd := by simpa using data.hBdd
  hshell := by norm_num
  hrem := by linarith
  haggregateBound := by
    show O_D + (0 : Real) + (O_P + O_E + O_CNL + O_bdd)
        <= O_D + O_P + O_E + O_CNL + O_bdd
    ring_nf
    exact le_rfl }

/-- The direct five-class target has trivial absorbed-bound accounting. -/
def DirectFiveClassTerminalAbsorptionData.toFiveClassAbsorbedBoundData
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (_data : DirectFiveClassTerminalAbsorptionData termMass O_D O_P O_E O_CNL O_bdd) :
    FiveClassAbsorbedBoundData
      (O_D + O_P + O_E + O_CNL + O_bdd) O_D O_P O_E O_CNL O_bdd := {
  absorbedD := O_D
  absorbedP := O_P
  absorbedE := O_E
  absorbedCNL := O_CNL
  absorbedBdd := O_bdd
  hsplit := le_rfl
  hD := le_rfl
  hP := le_rfl
  hE := le_rfl
  hCNL := le_rfl
  hBdd := le_rfl }

/-- Direct N.3.3/N.24 terminal absorption gives the five-class terminal bound. -/
def DirectFiveClassTerminalAbsorptionData.toHtermFiveClass
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (data : DirectFiveClassTerminalAbsorptionData termMass O_D O_P O_E O_CNL O_bdd) :
    termMass <= O_D + O_P + O_E + O_CNL + O_bdd :=
  data.toTerminalAbsorption.toHterm

/-- The current direct N.3.3 terminal package pays the terminal non-drop mass
into the five non-drop classes. -/
theorem DirectFiveClassTerminalAbsorptionData.termMass_le_classes
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (data : DirectFiveClassTerminalAbsorptionData termMass O_D O_P O_E O_CNL O_bdd) :
    termMass <= O_D + O_P + O_E + O_CNL + O_bdd :=
  data.toHtermFiveClass

/-- Table-routed terminal absorption gives the five-class terminal bound. -/
theorem TableRoutedDirectFiveClassTerminalAbsorptionData.termMass_le_classes
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (data :
      TableRoutedDirectFiveClassTerminalAbsorptionData
        termMass O_D O_P O_E O_CNL O_bdd) :
    termMass <= O_D + O_P + O_E + O_CNL + O_bdd :=
  data.toDirect.termMass_le_classes

/-- Internally-decidable table-routed terminal absorption gives the five-class
terminal bound. -/
theorem ClassicalTableRoutedDirectFiveClassTerminalAbsorptionData.termMass_le_classes
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (data :
      ClassicalTableRoutedDirectFiveClassTerminalAbsorptionData
        termMass O_D O_P O_E O_CNL O_bdd) :
    termMass <= O_D + O_P + O_E + O_CNL + O_bdd :=
  data.toDirect.termMass_le_classes

namespace ClassicalTerminalN33LeafData

/-- Project the table-routed terminal-mass input from the N.3.3 leaf. -/
def terminalMassInput
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (data :
      ClassicalTerminalN33LeafData termMass O_D O_P O_E O_CNL O_bdd) :
    @TableRoutedTerminalMassInputData data.sigma data.iota
      (Classical.decEq data.sigma) data.linIota data.E data.row data.supp
      data.thr data.terminalWeight termMass :=
  by
    letI : DecidableEq data.sigma := Classical.decEq data.sigma
    letI : LinearOrder data.iota := data.linIota
    exact data.terminalMass

/-- Project the five non-drop class-bound inputs from the N.3.3 leaf. -/
def classBoundsInput
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (data :
      ClassicalTerminalN33LeafData termMass O_D O_P O_E O_CNL O_bdd) :
    @TableRoutedTerminalFiveClassInputData data.sigma data.iota
      (Classical.decEq data.sigma) data.linIota data.E data.row data.supp
      data.thr data.terminalWeight O_D O_P O_E O_CNL O_bdd :=
  by
    letI : DecidableEq data.sigma := Classical.decEq data.sigma
    letI : LinearOrder data.iota := data.linIota
    exact data.classBounds

/-- Bundle the separated N.3.3 terminal-mass and class-bound leaf inputs. -/
def bounds
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (data :
      ClassicalTerminalN33LeafData termMass O_D O_P O_E O_CNL O_bdd) :
    @TableRoutedTerminalClassBoundsData data.sigma data.iota
      (Classical.decEq data.sigma) data.linIota data.E data.row data.supp
      data.thr data.terminalWeight termMass O_D O_P O_E O_CNL O_bdd := by
  letI : DecidableEq data.sigma := Classical.decEq data.sigma
  letI : LinearOrder data.iota := data.linIota
  exact {
    hterm := data.terminalMass.hterm
    hD := data.classBounds.densePack.hD
    hP := data.classBounds.progress.hP
    hE := data.classBounds.endpoint.hE
    hCNL := data.classBounds.cnl.hCNL
    hBdd := data.classBounds.bdd.hBdd }

/-- Forget the N.3.3 leaf to the direct five-class terminal package. -/
def toDirect
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (data :
      ClassicalTerminalN33LeafData termMass O_D O_P O_E O_CNL O_bdd) :
    DirectFiveClassTerminalAbsorptionData termMass O_D O_P O_E O_CNL O_bdd :=
  data.toClassicalTableRoutedDirectFiveClassTerminalAbsorptionData.toDirect

/-- The N.3.3 leaf pays terminal non-drop mass into the five non-drop classes. -/
theorem termMass_le_classes
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (data :
      ClassicalTerminalN33LeafData termMass O_D O_P O_E O_CNL O_bdd) :
    termMass <= O_D + O_P + O_E + O_CNL + O_bdd :=
  data.toClassicalTableRoutedDirectFiveClassTerminalAbsorptionData.termMass_le_classes

end ClassicalTerminalN33LeafData

namespace ClassicalTableRoutedDirectFiveClassTerminalAbsorptionData

/-- Recover the separated N.3.3 terminal leaf carried by the table-routed
terminal absorption package. -/
def toTerminalN33LeafData
    {termMass O_D O_P O_E O_CNL O_bdd : Real}
    (data :
      ClassicalTableRoutedDirectFiveClassTerminalAbsorptionData
        termMass O_D O_P O_E O_CNL O_bdd) :
    ClassicalTerminalN33LeafData termMass O_D O_P O_E O_CNL O_bdd where
  sigma := data.sigma
  iota := data.iota
  linIota := data.linIota
  E := data.E
  row := data.row
  supp := data.supp
  thr := data.thr
  terminalWeight := data.terminalWeight
  terminalMass := data.terminalMass
  classBounds := data.classBounds

end ClassicalTableRoutedDirectFiveClassTerminalAbsorptionData

/--
Carry-hitGap lower-label-record data with the final N.24 phase-mass comparison
exposed in the manuscript six-class form.

Compared with
`CarryHitGapLowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9HighExcessLocalData`,
this replaces the aggregate `hN24Explicit` field by the five terminal non-drop
class bound, the variation-drop class bound, and the six class-to-phase
comparisons used in proof-v4 equation N.24.
-/
structure PhaseMassCarryHitGapLowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9HighExcessLocalData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : Real))
    (carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (h_supportCount_pos : 1 <= supportCount shell.d shell.X) where
  Branch : Type
  Labels : Type
  decBranch : DecidableEq Branch
  decLabels : DecidableEq Labels
  fintypeLabels : Fintype Labels
  recordQ : Nat
  recordQ_neZero : NeZero recordQ
  VarDrop : Real
  Cmul : Real
  Y : Real
  D : Real -> AppendixN.FirstCrossingRecordData Branch recordQ Labels
  branches : Finset Branch
  dropDensity : Real -> Real
  dropMass : Real -> Branch -> Nat -> Real
  hdrop_nonneg : forall T b e, 0 <= dropMass T b e
  crossingIndic : Real -> Nat -> Real
  hindic_nonneg : forall T e, 0 <= crossingIndic T e
  hlift_le : forall T b e, dropMass T b e <= crossingIndic T e
  support : Real -> Nat -> Finset Branch
  hsupp : forall T e, support T e ⊆branches
  hzero : forall T e, forall b, b ∈ branches -> b ∉ support T e -> dropMass T b e = 0
  hle : forall T e, (D T).loIdx e <= (D T).hiIdx e
  hinj :
    forall T (e : Nat), forall b, b ∈ support T e -> forall b', b' ∈ support T e ->
      (D T).record e b = (D T).record e b' ->
        (D T).startResidue b = (D T).startResidue b' -> b = b'
  s : Nat
  K : Finset Nat
  A : Set Real
  hDropY : Y = carryLocal.Y
  hDropK_window :
    K ⊆      Finset.Ico s
        ((carryLocal.toCarryData erdos260Constants_cPr_le_half
          hc0Small h_supportCount_pos).carry.hits.firstIndexAbove shell.X +
          (carryLocal.toCarryData erdos260Constants_cPr_le_half
            hc0Small h_supportCount_pos).r - 1)
  hCmulY : 0 <= Cmul * Y
  hA : MeasurableSet A
  hdrop_int : IntegrableOn dropDensity A volume
  hvar : VarDrop <= Cmul * Y * ∫ T in A, dropDensity T ∂volume
  hdensity :
    forall T, T ∈ A -> dropDensity T = ∑ e ∈ K, ∑ b ∈ branches, dropMass T b e
  hindic :
    forall T, T ∈ A -> forall e,
      crossingIndic T e =
        AppendixN.crossingIndicator (T + Y)
          (AppendixN.windowSum
            (fun n =>
              (hitGap
                (carryLocal.toCarryData erdos260Constants_cPr_le_half
                  hc0Small h_supportCount_pos).a n : Real)) s) e
  termMass : Real
  absorbedBound : Real
  O_D : Real
  O_P : Real
  O_E : Real
  O_CNL : Real
  O_bdd : Real
  O_V : Real
  hsplit :
    groundedHighExcessBranchMass
      (carryLocal.toCarryData erdos260Constants_cPr_le_half
        hc0Small h_supportCount_pos) = termMass + VarDrop
  hterm : termMass <= absorbedBound
  hAbsorbed : absorbedBound <= O_D + O_P + O_E + O_CNL + O_bdd
  hWindow :
    (Cmul * (((recordQ * (@Fintype.card Labels fintypeLabels) * recordQ : Nat) : Real))) *
        Y *
          (2 *
            (((carryLocal.toCarryData erdos260Constants_cPr_le_half
              hc0Small h_supportCount_pos).L + carryB shell.Q + 1 : Nat) : Real) *
              (K.card : Real)) <= O_V
  hD : O_D <= termDensePack phases.toClosurePhaseData
  hP : O_P <= termChernoff phases.toClosurePhaseData
  hE : O_E <= termReturn phases.toClosurePhaseData
  hCNL : O_CNL <= termCnl phases.toClosurePhaseData
  hbdd : O_bdd <= termTower phases.toClosurePhaseData
  hV : O_V <= termRun phases.toClosurePhaseData

/--
Convert manuscript six-class phase-mass data to the aggregate carry-hitGap N.24
package by faithful phase-mass summation.
-/
def PhaseMassCarryHitGapLowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9HighExcessLocalData.toCarryHitGapData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      PhaseMassCarryHitGapLowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9HighExcessLocalData
        phases carryLocal hc0Small h_supportCount_pos) :
    CarryHitGapLowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9HighExcessLocalData
      phases carryLocal hc0Small h_supportCount_pos := {
  Branch := data.Branch
  Labels := data.Labels
  decBranch := data.decBranch
  decLabels := data.decLabels
  fintypeLabels := data.fintypeLabels
  recordQ := data.recordQ
  recordQ_neZero := data.recordQ_neZero
  VarDrop := data.VarDrop
  Cmul := data.Cmul
  Y := data.Y
  D := data.D
  branches := data.branches
  dropDensity := data.dropDensity
  dropMass := data.dropMass
  hdrop_nonneg := data.hdrop_nonneg
  crossingIndic := data.crossingIndic
  hindic_nonneg := data.hindic_nonneg
  hlift_le := data.hlift_le
  support := data.support
  hsupp := data.hsupp
  hzero := data.hzero
  hle := data.hle
  hinj := data.hinj
  s := data.s
  K := data.K
  A := data.A
  hDropY := data.hDropY
  hDropK_window := data.hDropK_window
  hCmulY := data.hCmulY
  hA := data.hA
  hdrop_int := data.hdrop_int
  hvar := data.hvar
  hdensity := data.hdensity
  hindic := data.hindic
  termMass := data.termMass
  absorbedBound := data.absorbedBound
  hsplit := data.hsplit
  hterm := data.hterm
  hN24Explicit :=
    habsorb_ofC1VDClosure phases
      data.hAbsorbed data.hWindow data.hD data.hP data.hE data.hCNL
      data.hbdd data.hV }

/-- Convert six-class phase-mass data directly to central high-excess data. -/
def PhaseMassCarryHitGapLowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9HighExcessLocalData.toHighExcessChargeData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      PhaseMassCarryHitGapLowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9HighExcessLocalData
        phases carryLocal hc0Small h_supportCount_pos) :
    HighExcessChargeData phases
      (carryLocal.toCarryData erdos260Constants_cPr_le_half
        hc0Small h_supportCount_pos) :=
  data.toCarryHitGapData.toHighExcessChargeData

/--
Phase-mass/carry-hitGap high-excess data with Lemma N.3.3 aggregate terminal
absorption expanded instead of supplied as a single `hterm` hypothesis.
-/
structure TerminalAggregatePhaseMassCarryHitGapLowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9HighExcessLocalData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : Real))
    (carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (h_supportCount_pos : 1 <= supportCount shell.d shell.X) where
  Branch : Type
  Labels : Type
  decBranch : DecidableEq Branch
  decLabels : DecidableEq Labels
  fintypeLabels : Fintype Labels
  recordQ : Nat
  recordQ_neZero : NeZero recordQ
  VarDrop : Real
  Cmul : Real
  Y : Real
  D : Real -> AppendixN.FirstCrossingRecordData Branch recordQ Labels
  branches : Finset Branch
  dropDensity : Real -> Real
  dropMass : Real -> Branch -> Nat -> Real
  hdrop_nonneg : forall T b e, 0 <= dropMass T b e
  crossingIndic : Real -> Nat -> Real
  hindic_nonneg : forall T e, 0 <= crossingIndic T e
  hlift_le : forall T b e, dropMass T b e <= crossingIndic T e
  support : Real -> Nat -> Finset Branch
  hsupp : forall T e, support T e ⊆branches
  hzero : forall T e, forall b, b ∈ branches -> b ∉ support T e -> dropMass T b e = 0
  hle : forall T e, (D T).loIdx e <= (D T).hiIdx e
  hinj :
    forall T (e : Nat), forall b, b ∈ support T e -> forall b', b' ∈ support T e ->
      (D T).record e b = (D T).record e b' ->
        (D T).startResidue b = (D T).startResidue b' -> b = b'
  s : Nat
  K : Finset Nat
  A : Set Real
  hDropY : Y = carryLocal.Y
  hDropK_window :
    K ⊆      Finset.Ico s
        ((carryLocal.toCarryData erdos260Constants_cPr_le_half
          hc0Small h_supportCount_pos).carry.hits.firstIndexAbove shell.X +
          (carryLocal.toCarryData erdos260Constants_cPr_le_half
            hc0Small h_supportCount_pos).r - 1)
  hCmulY : 0 <= Cmul * Y
  hA : MeasurableSet A
  hdrop_int : IntegrableOn dropDensity A volume
  hvar : VarDrop <= Cmul * Y * ∫ T in A, dropDensity T ∂volume
  hdensity :
    forall T, T ∈ A -> dropDensity T = ∑ e ∈ K, ∑ b ∈ branches, dropMass T b e
  hindic :
    forall T, T ∈ A -> forall e,
      crossingIndic T e =
        AppendixN.crossingIndicator (T + Y)
          (AppendixN.windowSum
            (fun n =>
              (hitGap
                (carryLocal.toCarryData erdos260Constants_cPr_le_half
                  hc0Small h_supportCount_pos).a n : Real)) s) e
  termMass : Real
  absorbedBound : Real
  O_D : Real
  O_P : Real
  O_E : Real
  O_CNL : Real
  O_bdd : Real
  O_V : Real
  hsplit :
    groundedHighExcessBranchMass
      (carryLocal.toCarryData erdos260Constants_cPr_le_half
        hc0Small h_supportCount_pos) = termMass + VarDrop
  terminalAbsorption : TerminalNonDropAggregateAbsorptionData termMass absorbedBound
  hAbsorbed : absorbedBound <= O_D + O_P + O_E + O_CNL + O_bdd
  hWindow :
    (Cmul * (((recordQ * (@Fintype.card Labels fintypeLabels) * recordQ : Nat) : Real))) *
        Y *
          (2 *
            (((carryLocal.toCarryData erdos260Constants_cPr_le_half
              hc0Small h_supportCount_pos).L + carryB shell.Q + 1 : Nat) : Real) *
              (K.card : Real)) <= O_V
  hD : O_D <= termDensePack phases.toClosurePhaseData
  hP : O_P <= termChernoff phases.toClosurePhaseData
  hE : O_E <= termReturn phases.toClosurePhaseData
  hCNL : O_CNL <= termCnl phases.toClosurePhaseData
  hbdd : O_bdd <= termTower phases.toClosurePhaseData
  hV : O_V <= termRun phases.toClosurePhaseData

/-- Collapse the expanded N.3.3 terminal aggregate data to the phase-mass package. -/
def TerminalAggregatePhaseMassCarryHitGapLowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9HighExcessLocalData.toPhaseMassData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      TerminalAggregatePhaseMassCarryHitGapLowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9HighExcessLocalData
        phases carryLocal hc0Small h_supportCount_pos) :
    PhaseMassCarryHitGapLowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9HighExcessLocalData
      phases carryLocal hc0Small h_supportCount_pos := {
  Branch := data.Branch
  Labels := data.Labels
  decBranch := data.decBranch
  decLabels := data.decLabels
  fintypeLabels := data.fintypeLabels
  recordQ := data.recordQ
  recordQ_neZero := data.recordQ_neZero
  VarDrop := data.VarDrop
  Cmul := data.Cmul
  Y := data.Y
  D := data.D
  branches := data.branches
  dropDensity := data.dropDensity
  dropMass := data.dropMass
  hdrop_nonneg := data.hdrop_nonneg
  crossingIndic := data.crossingIndic
  hindic_nonneg := data.hindic_nonneg
  hlift_le := data.hlift_le
  support := data.support
  hsupp := data.hsupp
  hzero := data.hzero
  hle := data.hle
  hinj := data.hinj
  s := data.s
  K := data.K
  A := data.A
  hDropY := data.hDropY
  hDropK_window := data.hDropK_window
  hCmulY := data.hCmulY
  hA := data.hA
  hdrop_int := data.hdrop_int
  hvar := data.hvar
  hdensity := data.hdensity
  hindic := data.hindic
  termMass := data.termMass
  absorbedBound := data.absorbedBound
  O_D := data.O_D
  O_P := data.O_P
  O_E := data.O_E
  O_CNL := data.O_CNL
  O_bdd := data.O_bdd
  O_V := data.O_V
  hsplit := data.hsplit
  hterm := data.terminalAbsorption.toHterm
  hAbsorbed := data.hAbsorbed
  hWindow := data.hWindow
  hD := data.hD
  hP := data.hP
  hE := data.hE
  hCNL := data.hCNL
  hbdd := data.hbdd
  hV := data.hV }

/-- Convert expanded N.3.3 data directly to central high-excess data. -/
def TerminalAggregatePhaseMassCarryHitGapLowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9HighExcessLocalData.toHighExcessChargeData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      TerminalAggregatePhaseMassCarryHitGapLowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9HighExcessLocalData
        phases carryLocal hc0Small h_supportCount_pos) :
    HighExcessChargeData phases
      (carryLocal.toCarryData erdos260Constants_cPr_le_half
        hc0Small h_supportCount_pos) :=
  data.toPhaseMassData.toHighExcessChargeData

/--
Terminal-aggregate high-excess data with the absorbed five-class comparison
itself split into five class components.
-/
structure FiveClassTerminalAggregatePhaseMassCarryHitGapLowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9HighExcessLocalData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : Real))
    (carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (h_supportCount_pos : 1 <= supportCount shell.d shell.X) where
  Branch : Type
  Labels : Type
  decBranch : DecidableEq Branch
  decLabels : DecidableEq Labels
  fintypeLabels : Fintype Labels
  recordQ : Nat
  recordQ_neZero : NeZero recordQ
  VarDrop : Real
  Cmul : Real
  Y : Real
  D : Real -> AppendixN.FirstCrossingRecordData Branch recordQ Labels
  branches : Finset Branch
  dropDensity : Real -> Real
  dropMass : Real -> Branch -> Nat -> Real
  hdrop_nonneg : forall T b e, 0 <= dropMass T b e
  crossingIndic : Real -> Nat -> Real
  hindic_nonneg : forall T e, 0 <= crossingIndic T e
  hlift_le : forall T b e, dropMass T b e <= crossingIndic T e
  support : Real -> Nat -> Finset Branch
  hsupp : forall T e, support T e ⊆branches
  hzero : forall T e, forall b, b ∈ branches -> b ∉ support T e -> dropMass T b e = 0
  hle : forall T e, (D T).loIdx e <= (D T).hiIdx e
  hinj :
    forall T (e : Nat), forall b, b ∈ support T e -> forall b', b' ∈ support T e ->
      (D T).record e b = (D T).record e b' ->
        (D T).startResidue b = (D T).startResidue b' -> b = b'
  s : Nat
  K : Finset Nat
  A : Set Real
  hDropY : Y = carryLocal.Y
  hDropK_window :
    K ⊆      Finset.Ico s
        ((carryLocal.toCarryData erdos260Constants_cPr_le_half
          hc0Small h_supportCount_pos).carry.hits.firstIndexAbove shell.X +
          (carryLocal.toCarryData erdos260Constants_cPr_le_half
            hc0Small h_supportCount_pos).r - 1)
  hCmulY : 0 <= Cmul * Y
  hA : MeasurableSet A
  hdrop_int : IntegrableOn dropDensity A volume
  hvar : VarDrop <= Cmul * Y * ∫ T in A, dropDensity T ∂volume
  hdensity :
    forall T, T ∈ A -> dropDensity T = ∑ e ∈ K, ∑ b ∈ branches, dropMass T b e
  hindic :
    forall T, T ∈ A -> forall e,
      crossingIndic T e =
        AppendixN.crossingIndicator (T + Y)
          (AppendixN.windowSum
            (fun n =>
              (hitGap
                (carryLocal.toCarryData erdos260Constants_cPr_le_half
                  hc0Small h_supportCount_pos).a n : Real)) s) e
  termMass : Real
  absorbedBound : Real
  O_D : Real
  O_P : Real
  O_E : Real
  O_CNL : Real
  O_bdd : Real
  O_V : Real
  hsplit :
    groundedHighExcessBranchMass
      (carryLocal.toCarryData erdos260Constants_cPr_le_half
        hc0Small h_supportCount_pos) = termMass + VarDrop
  terminalAbsorption : TerminalNonDropAggregateAbsorptionData termMass absorbedBound
  absorbedAccounting : FiveClassAbsorbedBoundData absorbedBound O_D O_P O_E O_CNL O_bdd
  hWindow :
    (Cmul * (((recordQ * (@Fintype.card Labels fintypeLabels) * recordQ : Nat) : Real))) *
        Y *
          (2 *
            (((carryLocal.toCarryData erdos260Constants_cPr_le_half
              hc0Small h_supportCount_pos).L + carryB shell.Q + 1 : Nat) : Real) *
              (K.card : Real)) <= O_V
  hD : O_D <= termDensePack phases.toClosurePhaseData
  hP : O_P <= termChernoff phases.toClosurePhaseData
  hE : O_E <= termReturn phases.toClosurePhaseData
  hCNL : O_CNL <= termCnl phases.toClosurePhaseData
  hbdd : O_bdd <= termTower phases.toClosurePhaseData
  hV : O_V <= termRun phases.toClosurePhaseData

/-- Collapse five-class absorbed accounting to the terminal-aggregate package. -/
def FiveClassTerminalAggregatePhaseMassCarryHitGapLowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9HighExcessLocalData.toTerminalAggregateData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      FiveClassTerminalAggregatePhaseMassCarryHitGapLowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9HighExcessLocalData
        phases carryLocal hc0Small h_supportCount_pos) :
    TerminalAggregatePhaseMassCarryHitGapLowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9HighExcessLocalData
      phases carryLocal hc0Small h_supportCount_pos := {
  Branch := data.Branch
  Labels := data.Labels
  decBranch := data.decBranch
  decLabels := data.decLabels
  fintypeLabels := data.fintypeLabels
  recordQ := data.recordQ
  recordQ_neZero := data.recordQ_neZero
  VarDrop := data.VarDrop
  Cmul := data.Cmul
  Y := data.Y
  D := data.D
  branches := data.branches
  dropDensity := data.dropDensity
  dropMass := data.dropMass
  hdrop_nonneg := data.hdrop_nonneg
  crossingIndic := data.crossingIndic
  hindic_nonneg := data.hindic_nonneg
  hlift_le := data.hlift_le
  support := data.support
  hsupp := data.hsupp
  hzero := data.hzero
  hle := data.hle
  hinj := data.hinj
  s := data.s
  K := data.K
  A := data.A
  hDropY := data.hDropY
  hDropK_window := data.hDropK_window
  hCmulY := data.hCmulY
  hA := data.hA
  hdrop_int := data.hdrop_int
  hvar := data.hvar
  hdensity := data.hdensity
  hindic := data.hindic
  termMass := data.termMass
  absorbedBound := data.absorbedBound
  O_D := data.O_D
  O_P := data.O_P
  O_E := data.O_E
  O_CNL := data.O_CNL
  O_bdd := data.O_bdd
  O_V := data.O_V
  hsplit := data.hsplit
  terminalAbsorption := data.terminalAbsorption
  hAbsorbed := data.absorbedAccounting.toHAbsorbed
  hWindow := data.hWindow
  hD := data.hD
  hP := data.hP
  hE := data.hE
  hCNL := data.hCNL
  hbdd := data.hbdd
  hV := data.hV }

/-- Convert five-class absorbed accounting data directly to central high-excess data. -/
def FiveClassTerminalAggregatePhaseMassCarryHitGapLowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9HighExcessLocalData.toHighExcessChargeData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      FiveClassTerminalAggregatePhaseMassCarryHitGapLowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9HighExcessLocalData
        phases carryLocal hc0Small h_supportCount_pos) :
    HighExcessChargeData phases
      (carryLocal.toCarryData erdos260Constants_cPr_le_half
        hc0Small h_supportCount_pos) :=
  data.toTerminalAggregateData.toHighExcessChargeData

/-- Short alias for the five-class terminal-aggregate high-excess package. -/
abbrev FiveClassTerminalAggregateHighExcessLocalData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : Real))
    (carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (h_supportCount_pos : 1 <= supportCount shell.d shell.X) :=
  FiveClassTerminalAggregatePhaseMassCarryHitGapLowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9HighExcessLocalData
    phases carryLocal hc0Small h_supportCount_pos

/-- Short-name bridge from five-class terminal data to central high-excess data. -/
def fiveClassToHighExcessData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      FiveClassTerminalAggregateHighExcessLocalData
        phases carryLocal hc0Small h_supportCount_pos) :
    HighExcessChargeData phases
      (carryLocal.toCarryData erdos260Constants_cPr_le_half
        hc0Small h_supportCount_pos) :=
  data.toTerminalAggregateData.toHighExcessChargeData

/--
Five-class terminal-aggregate high-excess data with N.3.3/N.24 supplied as a
direct terminal absorption into the five non-drop classes, rather than through
an intermediate `absorbedBound`.
-/
structure DirectFiveClassTerminalAggregateHighExcessLocalData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : Real))
    (carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (h_supportCount_pos : 1 <= supportCount shell.d shell.X) where
  Branch : Type
  Labels : Type
  decBranch : DecidableEq Branch
  decLabels : DecidableEq Labels
  fintypeLabels : Fintype Labels
  recordQ : Nat
  recordQ_neZero : NeZero recordQ
  VarDrop : Real
  Cmul : Real
  Y : Real
  D : Real -> AppendixN.FirstCrossingRecordData Branch recordQ Labels
  branches : Finset Branch
  dropDensity : Real -> Real
  dropMass : Real -> Branch -> Nat -> Real
  hdrop_nonneg : forall T b e, 0 <= dropMass T b e
  crossingIndic : Real -> Nat -> Real
  hindic_nonneg : forall T e, 0 <= crossingIndic T e
  hlift_le : forall T b e, dropMass T b e <= crossingIndic T e
  support : Real -> Nat -> Finset Branch
  hsupp : forall T e, support T e ⊆branches
  hzero : forall T e, forall b, b ∈ branches -> b ∉ support T e -> dropMass T b e = 0
  hle : forall T e, (D T).loIdx e <= (D T).hiIdx e
  hinj :
    forall T (e : Nat), forall b, b ∈ support T e -> forall b', b' ∈ support T e ->
      (D T).record e b = (D T).record e b' ->
        (D T).startResidue b = (D T).startResidue b' -> b = b'
  s : Nat
  K : Finset Nat
  A : Set Real
  hDropY : Y = carryLocal.Y
  hDropK_window :
    K ⊆      Finset.Ico s
        ((carryLocal.toCarryData erdos260Constants_cPr_le_half
          hc0Small h_supportCount_pos).carry.hits.firstIndexAbove shell.X +
          (carryLocal.toCarryData erdos260Constants_cPr_le_half
            hc0Small h_supportCount_pos).r - 1)
  hCmulY : 0 <= Cmul * Y
  hA : MeasurableSet A
  hdrop_int : IntegrableOn dropDensity A volume
  hvar : VarDrop <= Cmul * Y * ∫ T in A, dropDensity T ∂volume
  hdensity :
    forall T, T ∈ A -> dropDensity T = ∑ e ∈ K, ∑ b ∈ branches, dropMass T b e
  hindic :
    forall T, T ∈ A -> forall e,
      crossingIndic T e =
        AppendixN.crossingIndicator (T + Y)
          (AppendixN.windowSum
            (fun n =>
              (hitGap
                (carryLocal.toCarryData erdos260Constants_cPr_le_half
                  hc0Small h_supportCount_pos).a n : Real)) s) e
  termMass : Real
  O_D : Real
  O_P : Real
  O_E : Real
  O_CNL : Real
  O_bdd : Real
  O_V : Real
  hsplit :
    groundedHighExcessBranchMass
      (carryLocal.toCarryData erdos260Constants_cPr_le_half
        hc0Small h_supportCount_pos) = termMass + VarDrop
  terminalAbsorption :
    DirectFiveClassTerminalAbsorptionData termMass O_D O_P O_E O_CNL O_bdd
  hWindow :
    (Cmul * (((recordQ * (@Fintype.card Labels fintypeLabels) * recordQ : Nat) : Real))) *
        Y *
          (2 *
            (((carryLocal.toCarryData erdos260Constants_cPr_le_half
              hc0Small h_supportCount_pos).L + carryB shell.Q + 1 : Nat) : Real) *
              (K.card : Real)) <= O_V
  hD : O_D <= termDensePack phases.toClosurePhaseData
  hP : O_P <= termChernoff phases.toClosurePhaseData
  hE : O_E <= termReturn phases.toClosurePhaseData
  hCNL : O_CNL <= termCnl phases.toClosurePhaseData
  hbdd : O_bdd <= termTower phases.toClosurePhaseData
  hV : O_V <= termRun phases.toClosurePhaseData

/-- Collapse direct five-class terminal absorption to the previous five-class package. -/
def directFiveClassLocalToFiveClassData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      DirectFiveClassTerminalAggregateHighExcessLocalData
        phases carryLocal hc0Small h_supportCount_pos) :
    FiveClassTerminalAggregateHighExcessLocalData
      phases carryLocal hc0Small h_supportCount_pos := {
  Branch := data.Branch
  Labels := data.Labels
  decBranch := data.decBranch
  decLabels := data.decLabels
  fintypeLabels := data.fintypeLabels
  recordQ := data.recordQ
  recordQ_neZero := data.recordQ_neZero
  VarDrop := data.VarDrop
  Cmul := data.Cmul
  Y := data.Y
  D := data.D
  branches := data.branches
  dropDensity := data.dropDensity
  dropMass := data.dropMass
  hdrop_nonneg := data.hdrop_nonneg
  crossingIndic := data.crossingIndic
  hindic_nonneg := data.hindic_nonneg
  hlift_le := data.hlift_le
  support := data.support
  hsupp := data.hsupp
  hzero := data.hzero
  hle := data.hle
  hinj := data.hinj
  s := data.s
  K := data.K
  A := data.A
  hDropY := data.hDropY
  hDropK_window := data.hDropK_window
  hCmulY := data.hCmulY
  hA := data.hA
  hdrop_int := data.hdrop_int
  hvar := data.hvar
  hdensity := data.hdensity
  hindic := data.hindic
  termMass := data.termMass
  absorbedBound := data.O_D + data.O_P + data.O_E + data.O_CNL + data.O_bdd
  O_D := data.O_D
  O_P := data.O_P
  O_E := data.O_E
  O_CNL := data.O_CNL
  O_bdd := data.O_bdd
  O_V := data.O_V
  hsplit := data.hsplit
  terminalAbsorption := data.terminalAbsorption.toTerminalAbsorption
  absorbedAccounting := data.terminalAbsorption.toFiveClassAbsorbedBoundData
  hWindow := data.hWindow
  hD := data.hD
  hP := data.hP
  hE := data.hE
  hCNL := data.hCNL
  hbdd := data.hbdd
  hV := data.hV }

/-- Direct five-class terminal data gives central high-excess data. -/
def directFiveClassToHighExcessData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      DirectFiveClassTerminalAggregateHighExcessLocalData
        phases carryLocal hc0Small h_supportCount_pos) :
    HighExcessChargeData phases
      (carryLocal.toCarryData erdos260Constants_cPr_le_half
        hc0Small h_supportCount_pos) :=
  fiveClassToHighExcessData (directFiveClassLocalToFiveClassData data)

/-- N.2.2 regularity certificate for the variation-drop density integral. -/
structure CarryHitGapDropDensityRegularityData
    (dropDensity : Real -> Real) (A : Set Real) where
  hA : MeasurableSet A
  hdrop_int : IntegrableOn dropDensity A volume

/-- N.2.2 first variation-drop integral inequality. -/
structure CarryHitGapDropDensityFirstIneqData
    (dropDensity : Real -> Real) (VarDrop Cmul Y : Real) (A : Set Real) where
  hvar : VarDrop <= Cmul * Y * ∫ T in A, dropDensity T ∂volume

/-- N.2.2 integral domination certificate for the variation-drop density. -/
structure CarryHitGapDropDensityIntegralData
    (dropDensity : Real -> Real) (VarDrop Cmul Y : Real) (A : Set Real) where
  regularity : CarryHitGapDropDensityRegularityData dropDensity A
  firstIneq : CarryHitGapDropDensityFirstIneqData dropDensity VarDrop Cmul Y A

/-- Canonical fixed-threshold drop density: the finite sum over crossing
edges and active branches. -/
def carryHitGapDropDensity
    {Branch : Type} (branches : Finset Branch)
    (dropMass : Real -> Branch -> Nat -> Real) (K : Finset Nat) :
    Real -> Real :=
  fun T => ∑ e ∈ K, ∑ b ∈ branches, dropMass T b e

/-- N.2.2 first-crossing density expansion certificate at fixed threshold. -/
structure CarryHitGapDropDensityExpansionData
    {Branch : Type} (branches : Finset Branch)
    (dropDensity : Real -> Real)
    (dropMass : Real -> Branch -> Nat -> Real)
    (K : Finset Nat) (A : Set Real) where
  hdensity :
    forall T, T ∈ A -> dropDensity T = ∑ e ∈ K, ∑ b ∈ branches, dropMass T b e

/--
Appendix N.2.1/N.2.2/N.13 variation-drop data, with N.2.2 split into its
integral-domination and fixed-threshold density-expansion certificates.
-/
structure CarryHitGapDropDensityData
    {Branch : Type} (branches : Finset Branch)
    (dropDensity : Real -> Real)
    (dropMass : Real -> Branch -> Nat -> Real)
    (VarDrop Cmul Y : Real) (K : Finset Nat) (A : Set Real) where
  regularity :
    CarryHitGapDropDensityRegularityData dropDensity A
  firstIneq :
    CarryHitGapDropDensityFirstIneqData dropDensity VarDrop Cmul Y A
  expansion :
    CarryHitGapDropDensityExpansionData branches dropDensity dropMass K A

/-- Canonical N.2.2 drop-density data.  The expansion leaf is no longer a
provider condition: the integrand is definitionally the finite branch/edge
sum. -/
structure CarryHitGapCanonicalDropDensityData
    {Branch : Type} (branches : Finset Branch)
    (dropMass : Real -> Branch -> Nat -> Real)
    (VarDrop Cmul Y : Real) (K : Finset Nat) (A : Set Real) where
  regularity :
    CarryHitGapDropDensityRegularityData
      (carryHitGapDropDensity branches dropMass K) A
  firstIneq :
    CarryHitGapDropDensityFirstIneqData
      (carryHitGapDropDensity branches dropMass K) VarDrop Cmul Y A

/-- Forget the canonical N.2.2 density package to the older split package. -/
def CarryHitGapCanonicalDropDensityData.toDropDensityData
    {Branch : Type} {branches : Finset Branch}
    {dropMass : Real -> Branch -> Nat -> Real}
    {VarDrop Cmul Y : Real} {K : Finset Nat} {A : Set Real}
    (data :
      CarryHitGapCanonicalDropDensityData branches dropMass VarDrop Cmul Y
        K A) :
    CarryHitGapDropDensityData branches
      (carryHitGapDropDensity branches dropMass K) dropMass VarDrop Cmul Y
      K A where
  regularity := data.regularity
  firstIneq := data.firstIneq
  expansion := {
    hdensity := by
      intro T _hT
      rfl }

/-- Measurability of the threshold set carried by canonical density data. -/
theorem CarryHitGapCanonicalDropDensityData.hA
    {Branch : Type} {branches : Finset Branch}
    {dropMass : Real -> Branch -> Nat -> Real}
    {VarDrop Cmul Y : Real} {K : Finset Nat} {A : Set Real}
    (data :
      CarryHitGapCanonicalDropDensityData branches dropMass VarDrop Cmul Y
        K A) :
    MeasurableSet A :=
  data.regularity.hA

/-- Integrability of the canonical drop-density integrand. -/
theorem CarryHitGapCanonicalDropDensityData.hdrop_int
    {Branch : Type} {branches : Finset Branch}
    {dropMass : Real -> Branch -> Nat -> Real}
    {VarDrop Cmul Y : Real} {K : Finset Nat} {A : Set Real}
    (data :
      CarryHitGapCanonicalDropDensityData branches dropMass VarDrop Cmul Y
        K A) :
    IntegrableOn (carryHitGapDropDensity branches dropMass K) A volume :=
  data.regularity.hdrop_int

/-- The N.2.2 first variation-drop inequality carried by canonical density data. -/
theorem CarryHitGapCanonicalDropDensityData.hvar
    {Branch : Type} {branches : Finset Branch}
    {dropMass : Real -> Branch -> Nat -> Real}
    {VarDrop Cmul Y : Real} {K : Finset Nat} {A : Set Real}
    (data :
      CarryHitGapCanonicalDropDensityData branches dropMass VarDrop Cmul Y
        K A) :
    VarDrop <=
      Cmul * Y * ∫ T in A, carryHitGapDropDensity branches dropMass K T ∂volume :=
  data.firstIneq.hvar

/-- The canonical fixed-threshold drop-density expansion. -/
theorem CarryHitGapCanonicalDropDensityData.hdensity
    {Branch : Type} {branches : Finset Branch}
    {dropMass : Real -> Branch -> Nat -> Real}
    {VarDrop Cmul Y : Real} {K : Finset Nat} {A : Set Real}
    (_data :
      CarryHitGapCanonicalDropDensityData branches dropMass VarDrop Cmul Y
        K A) :
    forall T, T ∈ A ->
      carryHitGapDropDensity branches dropMass K T =
        ∑ e ∈ K, ∑ b ∈ branches, dropMass T b e := by
  intro T _hT
  rfl

/-- The N.2.2 first variation-drop inequality carried by canonical density data. -/
theorem CarryHitGapCanonicalDropDensityData.var_bound
    {Branch : Type} {branches : Finset Branch}
    {dropMass : Real -> Branch -> Nat -> Real}
    {VarDrop Cmul Y : Real} {K : Finset Nat} {A : Set Real}
    (data :
      CarryHitGapCanonicalDropDensityData branches dropMass VarDrop Cmul Y
        K A) :
    VarDrop <=
      Cmul * Y * ∫ T in A, carryHitGapDropDensity branches dropMass K T ∂volume :=
  data.hvar

/-- The N.2.2 drop-density expansion is definitional for canonical density data. -/
theorem CarryHitGapCanonicalDropDensityData.density_expansion
    {Branch : Type} {branches : Finset Branch}
    {dropMass : Real -> Branch -> Nat -> Real}
    {VarDrop Cmul Y : Real} {K : Finset Nat} {A : Set Real}
    (data :
      CarryHitGapCanonicalDropDensityData branches dropMass VarDrop Cmul Y
        K A) :
    forall T, T ∈ A ->
      carryHitGapDropDensity branches dropMass K T =
        ∑ e ∈ K, ∑ b ∈ branches, dropMass T b e :=
  data.hdensity

/-- Reassemble the N.2.2 integral certificate from regularity and first inequality. -/
def CarryHitGapDropDensityData.integral
    {Branch : Type} {branches : Finset Branch}
    {dropDensity : Real -> Real}
    {dropMass : Real -> Branch -> Nat -> Real}
    {VarDrop Cmul Y : Real} {K : Finset Nat} {A : Set Real}
    (data :
      CarryHitGapDropDensityData branches dropDensity dropMass VarDrop Cmul Y
        K A) :
    CarryHitGapDropDensityIntegralData dropDensity VarDrop Cmul Y A where
  regularity := data.regularity
  firstIneq := data.firstIneq

/-- Measurability of the threshold set carried by the integral certificate. -/
theorem CarryHitGapDropDensityData.hA
    {Branch : Type} {branches : Finset Branch}
    {dropDensity : Real -> Real}
    {dropMass : Real -> Branch -> Nat -> Real}
    {VarDrop Cmul Y : Real} {K : Finset Nat} {A : Set Real}
    (data :
      CarryHitGapDropDensityData branches dropDensity dropMass VarDrop Cmul Y
        K A) :
    MeasurableSet A :=
  data.integral.regularity.hA

/-- Integrability of the drop-density integrand carried by the integral certificate. -/
theorem CarryHitGapDropDensityData.hdrop_int
    {Branch : Type} {branches : Finset Branch}
    {dropDensity : Real -> Real}
    {dropMass : Real -> Branch -> Nat -> Real}
    {VarDrop Cmul Y : Real} {K : Finset Nat} {A : Set Real}
    (data :
      CarryHitGapDropDensityData branches dropDensity dropMass VarDrop Cmul Y
        K A) :
    IntegrableOn dropDensity A volume :=
  data.integral.regularity.hdrop_int

/-- The N.2.2 first variation-drop inequality carried by the integral certificate. -/
theorem CarryHitGapDropDensityData.hvar
    {Branch : Type} {branches : Finset Branch}
    {dropDensity : Real -> Real}
    {dropMass : Real -> Branch -> Nat -> Real}
    {VarDrop Cmul Y : Real} {K : Finset Nat} {A : Set Real}
    (data :
      CarryHitGapDropDensityData branches dropDensity dropMass VarDrop Cmul Y
        K A) :
    VarDrop <= Cmul * Y * ∫ T in A, dropDensity T ∂volume :=
  data.integral.firstIneq.hvar

/-- The fixed-threshold drop-density expansion carried by the expansion certificate. -/
theorem CarryHitGapDropDensityData.hdensity
    {Branch : Type} {branches : Finset Branch}
    {dropDensity : Real -> Real}
    {dropMass : Real -> Branch -> Nat -> Real}
    {VarDrop Cmul Y : Real} {K : Finset Nat} {A : Set Real}
    (data :
      CarryHitGapDropDensityData branches dropDensity dropMass VarDrop Cmul Y
        K A) :
    forall T, T ∈ A -> dropDensity T = ∑ e ∈ K, ∑ b ∈ branches, dropMass T b e :=
  data.expansion.hdensity

/-- The N.2.2 first variation-drop inequality carried by the density certificate. -/
theorem CarryHitGapDropDensityData.var_bound
    {Branch : Type} {branches : Finset Branch}
    {dropDensity : Real -> Real}
    {dropMass : Real -> Branch -> Nat -> Real}
    {VarDrop Cmul Y : Real} {K : Finset Nat} {A : Set Real}
    (data :
      CarryHitGapDropDensityData branches dropDensity dropMass VarDrop Cmul Y
        K A) :
    VarDrop <= Cmul * Y * ∫ T in A, dropDensity T ∂volume :=
  data.hvar

/-- The N.2.2 drop-density expansion carried by the density certificate. -/
theorem CarryHitGapDropDensityData.density_expansion
    {Branch : Type} {branches : Finset Branch}
    {dropDensity : Real -> Real}
    {dropMass : Real -> Branch -> Nat -> Real}
    {VarDrop Cmul Y : Real} {K : Finset Nat} {A : Set Real}
    (data :
      CarryHitGapDropDensityData branches dropDensity dropMass VarDrop Cmul Y
        K A) :
    forall T, T ∈ A -> dropDensity T = ∑ e ∈ K, ∑ b ∈ branches, dropMass T b e :=
  data.hdensity

/-- N.2.1 finite support certificate for variation-drop fibres. -/
structure CarryHitGapSupportData
    {Branch : Type} (branches : Finset Branch) where
  decBranch : DecidableEq Branch
  support : Real -> Nat -> Finset Branch
  hsupp : forall T e, support T e ⊆branches

/-- N.2.1 lift bound from variation-drop mass to the crossing indicator. -/
structure CarryHitGapLiftBoundData
    {Branch : Type}
    (dropMass : Real -> Branch -> Nat -> Real)
    (crossingIndic : Real -> Nat -> Real) where
  hlift_le : forall T b e, dropMass T b e <= crossingIndic T e

/-- N.2.1 zero contribution outside the selected fixed-edge support. -/
structure CarryHitGapZeroOutsideSupportData
    {Branch : Type} (branches : Finset Branch)
    (dropMass : Real -> Branch -> Nat -> Real)
    (support : Real -> Nat -> Finset Branch) where
  hzero : forall T e, forall b, b ∈ branches -> b ∉ support T e -> dropMass T b e = 0

/-- N.2.1 lift/support certificate for variation-drop fibres. -/
structure CarryHitGapLiftSupportData
    {Branch : Type} (branches : Finset Branch)
    (dropMass : Real -> Branch -> Nat -> Real)
    (crossingIndic : Real -> Nat -> Real) where
  supportData : CarryHitGapSupportData branches
  liftBound : CarryHitGapLiftBoundData dropMass crossingIndic
  zeroOutside : CarryHitGapZeroOutsideSupportData branches dropMass supportData.support

namespace CarryHitGapLiftSupportData

/-- Decidable equality on the branch type supplied by the support certificate. -/
@[reducible]
def decBranch
    {Branch : Type} {branches : Finset Branch}
    {dropMass : Real -> Branch -> Nat -> Real}
    {crossingIndic : Real -> Nat -> Real}
    (data : CarryHitGapLiftSupportData branches dropMass crossingIndic) :
    DecidableEq Branch :=
  data.supportData.decBranch

/-- Selected support on a fixed threshold and edge. -/
def support
    {Branch : Type} {branches : Finset Branch}
    {dropMass : Real -> Branch -> Nat -> Real}
    {crossingIndic : Real -> Nat -> Real}
    (data : CarryHitGapLiftSupportData branches dropMass crossingIndic) :
    Real -> Nat -> Finset Branch :=
  data.supportData.support

/-- Lift bound from variation-drop mass to the crossing indicator. -/
theorem hlift_le
    {Branch : Type} {branches : Finset Branch}
    {dropMass : Real -> Branch -> Nat -> Real}
    {crossingIndic : Real -> Nat -> Real}
    (data : CarryHitGapLiftSupportData branches dropMass crossingIndic) :
    forall T b e, dropMass T b e <= crossingIndic T e :=
  data.liftBound.hlift_le

/-- The selected support lies in the ambient branch family. -/
theorem hsupp
    {Branch : Type} {branches : Finset Branch}
    {dropMass : Real -> Branch -> Nat -> Real}
    {crossingIndic : Real -> Nat -> Real}
    (data : CarryHitGapLiftSupportData branches dropMass crossingIndic) :
    forall T e, data.support T e ⊆branches :=
  data.supportData.hsupp

/-- Branches outside the selected support contribute zero drop mass. -/
theorem hzero
    {Branch : Type} {branches : Finset Branch}
    {dropMass : Real -> Branch -> Nat -> Real}
    {crossingIndic : Real -> Nat -> Real}
    (data : CarryHitGapLiftSupportData branches dropMass crossingIndic) :
    forall T e, forall b, b ∈ branches -> b ∉ data.support T e ->
      dropMass T b e = 0 :=
  data.zeroOutside.hzero

end CarryHitGapLiftSupportData

/-- N.2.1 finite priority-label universe for the first-crossing record. -/
structure CarryHitGapPriorityLabelData (Labels : Type) where
  decLabels : DecidableEq Labels
  fintypeLabels : Fintype Labels

/-- N.2.0 first-crossing record family and ordered-window legality. -/
structure CarryHitGapFirstCrossingRecordFamilyData
    {Branch Labels : Type} (recordQ : Nat) where
  recordQ_neZero : NeZero recordQ
  D : Real -> AppendixN.FirstCrossingRecordData Branch recordQ Labels
  hle : forall T e, (D T).loIdx e <= (D T).hiIdx e

/-- N.2.1 priority-injectivity certificate on each fixed edge and record. -/
structure CarryHitGapPriorityInjectivityData
    {Branch Labels : Type} {recordQ : Nat}
    (support : Real -> Nat -> Finset Branch)
    (D : Real -> AppendixN.FirstCrossingRecordData Branch recordQ Labels) where
  hinj :
    forall T (e : Nat), forall b, b ∈ support T e -> forall b', b' ∈ support T e ->
      (D T).record e b = (D T).record e b' ->
        (D T).startResidue b = (D T).startResidue b' -> b = b'

/-- N.2.0/N.2.1 finite first-crossing record and priority-injectivity certificate. -/
structure CarryHitGapPriorityRecordData
    {Branch Labels : Type} (recordQ : Nat)
    (support : Real -> Nat -> Finset Branch) where
  labels : CarryHitGapPriorityLabelData Labels
  recordFamily :
    CarryHitGapFirstCrossingRecordFamilyData (Branch := Branch) (Labels := Labels)
      recordQ
  injectivity :
    CarryHitGapPriorityInjectivityData support recordFamily.D

namespace CarryHitGapPriorityRecordData

/-- Decidable equality on the finite priority-label universe. -/
@[reducible]
def decLabels
    {Branch Labels : Type} {recordQ : Nat}
    {support : Real -> Nat -> Finset Branch}
    (data :
      CarryHitGapPriorityRecordData (Branch := Branch) (Labels := Labels)
        recordQ support) :
    DecidableEq Labels :=
  data.labels.decLabels

/-- Finiteness of the priority-label universe. -/
@[reducible]
def fintypeLabels
    {Branch Labels : Type} {recordQ : Nat}
    {support : Real -> Nat -> Finset Branch}
    (data :
      CarryHitGapPriorityRecordData (Branch := Branch) (Labels := Labels)
        recordQ support) :
    Fintype Labels :=
  data.labels.fintypeLabels

/-- Nonzero denominator for the residue part of the first-crossing record. -/
@[reducible]
def recordQ_neZero
    {Branch Labels : Type} {recordQ : Nat}
    {support : Real -> Nat -> Finset Branch}
    (data :
      CarryHitGapPriorityRecordData (Branch := Branch) (Labels := Labels)
        recordQ support) :
    NeZero recordQ :=
  data.recordFamily.recordQ_neZero

/-- The first-crossing record family. -/
def D
    {Branch Labels : Type} {recordQ : Nat}
    {support : Real -> Nat -> Finset Branch}
    (data :
      CarryHitGapPriorityRecordData (Branch := Branch) (Labels := Labels)
        recordQ support) :
    Real -> AppendixN.FirstCrossingRecordData Branch recordQ Labels :=
  data.recordFamily.D

/-- Ordered-window legality for the first-crossing record. -/
theorem hle
    {Branch Labels : Type} {recordQ : Nat}
    {support : Real -> Nat -> Finset Branch}
    (data :
      CarryHitGapPriorityRecordData (Branch := Branch) (Labels := Labels)
        recordQ support) :
    forall T e, (data.D T).loIdx e <= (data.D T).hiIdx e :=
  data.recordFamily.hle

/-- Priority injectivity on a fixed support fibre. -/
theorem hinj
    {Branch Labels : Type} {recordQ : Nat}
    {support : Real -> Nat -> Finset Branch}
    (data :
      CarryHitGapPriorityRecordData (Branch := Branch) (Labels := Labels)
        recordQ support) :
    forall T (e : Nat), forall b, b ∈ support T e ->
      forall b', b' ∈ support T e ->
        (data.D T).record e b = (data.D T).record e b' ->
          (data.D T).startResidue b = (data.D T).startResidue b' -> b = b' :=
  data.injectivity.hinj

end CarryHitGapPriorityRecordData

/-- Canonical finite-label version of the N.2.0/N.2.1 first-crossing record.

The finite label universe is no longer a provider leaf: it is `Fin labelCount`,
so decidable equality and finiteness are automatic.  The remaining inputs are
the first-crossing record family itself and the priority-injectivity/carry
determinacy certificate. -/
structure CarryHitGapCanonicalPriorityRecordData
    {Branch : Type} (recordQ : Nat)
    (support : Real -> Nat -> Finset Branch) where
  labelCount : Nat
  recordFamily :
    CarryHitGapFirstCrossingRecordFamilyData
      (Branch := Branch) (Labels := Fin labelCount) recordQ
  injectivity :
    CarryHitGapPriorityInjectivityData support recordFamily.D

namespace CarryHitGapCanonicalPriorityRecordData

/-- The canonical finite priority-label universe. -/
@[reducible]
def Labels
    {Branch : Type} {recordQ : Nat}
    {support : Real -> Nat -> Finset Branch}
    (data :
      CarryHitGapCanonicalPriorityRecordData (Branch := Branch) recordQ
        support) : Type :=
  Fin data.labelCount

/-- Decidable equality on canonical priority labels. -/
@[reducible]
def decLabels
    {Branch : Type} {recordQ : Nat}
    {support : Real -> Nat -> Finset Branch}
    (data :
      CarryHitGapCanonicalPriorityRecordData (Branch := Branch) recordQ
        support) :
    DecidableEq data.Labels :=
  inferInstance

/-- Finiteness of canonical priority labels. -/
@[reducible]
def fintypeLabels
    {Branch : Type} {recordQ : Nat}
    {support : Real -> Nat -> Finset Branch}
    (data :
      CarryHitGapCanonicalPriorityRecordData (Branch := Branch) recordQ
        support) :
    Fintype data.Labels :=
  inferInstance

/-- The generic finite-label certificate induced by the canonical label type. -/
def labelData
    {Branch : Type} {recordQ : Nat}
    {support : Real -> Nat -> Finset Branch}
    (data :
      CarryHitGapCanonicalPriorityRecordData (Branch := Branch) recordQ
        support) :
    CarryHitGapPriorityLabelData data.Labels where
  decLabels := data.decLabels
  fintypeLabels := data.fintypeLabels

/-- Nonzero denominator for the residue part of the first-crossing record. -/
@[reducible]
def recordQ_neZero
    {Branch : Type} {recordQ : Nat}
    {support : Real -> Nat -> Finset Branch}
    (data :
      CarryHitGapCanonicalPriorityRecordData (Branch := Branch) recordQ
        support) :
    NeZero recordQ :=
  data.recordFamily.recordQ_neZero

/-- The canonical first-crossing record family. -/
def D
    {Branch : Type} {recordQ : Nat}
    {support : Real -> Nat -> Finset Branch}
    (data :
      CarryHitGapCanonicalPriorityRecordData (Branch := Branch) recordQ
        support) :
    Real -> AppendixN.FirstCrossingRecordData Branch recordQ data.Labels :=
  data.recordFamily.D

/-- Ordered-window legality for the canonical first-crossing record. -/
theorem hle
    {Branch : Type} {recordQ : Nat}
    {support : Real -> Nat -> Finset Branch}
    (data :
      CarryHitGapCanonicalPriorityRecordData (Branch := Branch) recordQ
        support) :
    forall T e, (data.D T).loIdx e <= (data.D T).hiIdx e :=
  data.recordFamily.hle

/-- Priority injectivity on a fixed support fibre. -/
theorem hinj
    {Branch : Type} {recordQ : Nat}
    {support : Real -> Nat -> Finset Branch}
    (data :
      CarryHitGapCanonicalPriorityRecordData (Branch := Branch) recordQ
        support) :
    forall T (e : Nat), forall b, b ∈ support T e ->
      forall b', b' ∈ support T e ->
        (data.D T).record e b = (data.D T).record e b' ->
          (data.D T).startResidue b = (data.D T).startResidue b' -> b = b' :=
  data.injectivity.hinj

/-- Forget the canonical finite-label record to the generic priority record. -/
def toPriorityRecordData
    {Branch : Type} {recordQ : Nat}
    {support : Real -> Nat -> Finset Branch}
    (data :
      CarryHitGapCanonicalPriorityRecordData (Branch := Branch) recordQ
        support) :
    CarryHitGapPriorityRecordData (Branch := Branch) (Labels := data.Labels)
      recordQ support where
  labels := data.labelData
  recordFamily := data.recordFamily
  injectivity := data.injectivity

end CarryHitGapCanonicalPriorityRecordData

/-- First-crossing record family in the strongest route.

The denominator is the actual shell denominator `shell.Q`, and each threshold
record is typed as an ordered first-crossing record.  Thus nonzeroness is
recovered from `shell.hQ`, and the old `hle` legality field is projected from
the subtype when forgetting to the older generic record family. -/
structure CarryHitGapShellQFirstCrossingRecordFamilyData
    {Branch Labels : Type} (shell : FailingDyadicShell) where
  DOrdered :
    Real ->
      {D : AppendixN.FirstCrossingRecordData Branch shell.Q Labels //
        forall e, D.loIdx e <= D.hiIdx e}

namespace CarryHitGapShellQFirstCrossingRecordFamilyData

/-- Forget the ordered-record subtype to the first-crossing record family. -/
def D
    {Branch Labels : Type} {shell : FailingDyadicShell}
    (data :
      CarryHitGapShellQFirstCrossingRecordFamilyData
        (Branch := Branch) (Labels := Labels) shell) :
    Real -> AppendixN.FirstCrossingRecordData Branch shell.Q Labels :=
  fun T => (data.DOrdered T).1

/-- Ordered-window legality is carried by the ordered-record subtype. -/
theorem hle
    {Branch Labels : Type} {shell : FailingDyadicShell}
    (data :
      CarryHitGapShellQFirstCrossingRecordFamilyData
        (Branch := Branch) (Labels := Labels) shell) :
    forall T e, (data.D T).loIdx e <= (data.D T).hiIdx e := by
  intro T e
  exact (data.DOrdered T).2 e

/-- Project the shell-denominator record family to the older generic shape. -/
def toFirstCrossingRecordFamilyData
    {Branch Labels : Type} {shell : FailingDyadicShell}
    (data :
      CarryHitGapShellQFirstCrossingRecordFamilyData
        (Branch := Branch) (Labels := Labels) shell) :
    CarryHitGapFirstCrossingRecordFamilyData
      (Branch := Branch) (Labels := Labels) shell.Q where
  recordQ_neZero := NeZero.of_pos shell.hQ
  D := data.D
  hle := data.hle

end CarryHitGapShellQFirstCrossingRecordFamilyData

/-- Canonical finite-label priority record with denominator fixed to `shell.Q`.

Compared with `CarryHitGapCanonicalPriorityRecordData`, the provider no longer
supplies the proof-only `NeZero shell.Q`; it is projected from `shell.hQ`. -/
structure CarryHitGapShellQCanonicalPriorityRecordData
    {Branch : Type} (shell : FailingDyadicShell)
    (support : Real -> Nat -> Finset Branch) where
  labelCount : Nat
  recordFamily :
    CarryHitGapShellQFirstCrossingRecordFamilyData
      (Branch := Branch) (Labels := Fin labelCount) shell
  injectivity :
    CarryHitGapPriorityInjectivityData support recordFamily.D

namespace CarryHitGapShellQCanonicalPriorityRecordData

/-- The canonical finite priority-label universe. -/
@[reducible]
def Labels
    {Branch : Type} {shell : FailingDyadicShell}
    {support : Real -> Nat -> Finset Branch}
    (data :
      CarryHitGapShellQCanonicalPriorityRecordData (Branch := Branch) shell
        support) : Type :=
  Fin data.labelCount

/-- Decidable equality on canonical priority labels. -/
@[reducible]
def decLabels
    {Branch : Type} {shell : FailingDyadicShell}
    {support : Real -> Nat -> Finset Branch}
    (data :
      CarryHitGapShellQCanonicalPriorityRecordData (Branch := Branch) shell
        support) :
    DecidableEq data.Labels :=
  inferInstance

/-- Finiteness of canonical priority labels. -/
@[reducible]
def fintypeLabels
    {Branch : Type} {shell : FailingDyadicShell}
    {support : Real -> Nat -> Finset Branch}
    (data :
      CarryHitGapShellQCanonicalPriorityRecordData (Branch := Branch) shell
        support) :
    Fintype data.Labels :=
  inferInstance

/-- The shell denominator is nonzero. -/
@[reducible]
def recordQ_neZero
    {Branch : Type} {shell : FailingDyadicShell}
    {support : Real -> Nat -> Finset Branch}
    (_data :
      CarryHitGapShellQCanonicalPriorityRecordData (Branch := Branch) shell
        support) :
    NeZero shell.Q :=
  NeZero.of_pos shell.hQ

/-- The canonical first-crossing record family. -/
def D
    {Branch : Type} {shell : FailingDyadicShell}
    {support : Real -> Nat -> Finset Branch}
    (data :
      CarryHitGapShellQCanonicalPriorityRecordData (Branch := Branch) shell
        support) :
    Real -> AppendixN.FirstCrossingRecordData Branch shell.Q data.Labels :=
  data.recordFamily.D

/-- Ordered-window legality for the canonical first-crossing record. -/
theorem hle
    {Branch : Type} {shell : FailingDyadicShell}
    {support : Real -> Nat -> Finset Branch}
    (data :
      CarryHitGapShellQCanonicalPriorityRecordData (Branch := Branch) shell
        support) :
    forall T e, (data.D T).loIdx e <= (data.D T).hiIdx e :=
  data.recordFamily.hle

/-- Priority injectivity on a fixed support fibre. -/
theorem hinj
    {Branch : Type} {shell : FailingDyadicShell}
    {support : Real -> Nat -> Finset Branch}
    (data :
      CarryHitGapShellQCanonicalPriorityRecordData (Branch := Branch) shell
        support) :
    forall T (e : Nat), forall b, b ∈ support T e ->
      forall b', b' ∈ support T e ->
        (data.D T).record e b = (data.D T).record e b' ->
          (data.D T).startResidue b = (data.D T).startResidue b' -> b = b' :=
  data.injectivity.hinj

/-- Forget the shell-denominator record to the generic canonical priority
record. -/
def toCanonicalPriorityRecordData
    {Branch : Type} {shell : FailingDyadicShell}
    {support : Real -> Nat -> Finset Branch}
    (data :
      CarryHitGapShellQCanonicalPriorityRecordData (Branch := Branch) shell
        support) :
    CarryHitGapCanonicalPriorityRecordData (Branch := Branch) shell.Q
      support where
  labelCount := data.labelCount
  recordFamily := data.recordFamily.toFirstCrossingRecordFamilyData
  injectivity := data.injectivity

end CarryHitGapShellQCanonicalPriorityRecordData

/-- Canonical N.2 variation input: the N.2.1 first-crossing priority record
and the N.2.2 canonical drop-density integral certificate are carried as one
proof-v4 variation package. -/
structure CarryHitGapCanonicalVariationInputData
    {Branch : Type} [DecidableEq Branch] (recordQ : Nat)
    (branches : Finset Branch)
    (dropMass : Real -> Branch -> Nat -> Real)
    (VarDrop Cmul Y : Real) (K : Finset Nat) (A : Set Real) where
  priority :
    CarryHitGapCanonicalPriorityRecordData (Branch := Branch) recordQ
      (fun T e => branches.filter fun b => dropMass T b e ≠0)
  density :
    CarryHitGapCanonicalDropDensityData branches dropMass VarDrop Cmul Y K A

/-- Canonical N.2 variation input for the strongest shell-grounded route, with
the first-crossing denominator fixed to the actual shell denominator. -/
structure CarryHitGapShellQCanonicalVariationInputData
    {Branch : Type} [DecidableEq Branch] (shell : FailingDyadicShell)
    (branches : Finset Branch)
    (dropMass : Real -> Branch -> Nat -> Real)
    (VarDrop Cmul Y : Real) (K : Finset Nat) (A : Set Real) where
  priority :
    CarryHitGapShellQCanonicalPriorityRecordData (Branch := Branch) shell
      (fun T e => branches.filter fun b => dropMass T b e ≠0)
  density :
    CarryHitGapCanonicalDropDensityData branches dropMass VarDrop Cmul Y K A

namespace CarryHitGapShellQCanonicalVariationInputData

/-- Project the shell-denominator N.2 input to the older generic shape. -/
def toCanonicalVariationInputData
    {Branch : Type} [DecidableEq Branch] {shell : FailingDyadicShell}
    {branches : Finset Branch}
    {dropMass : Real -> Branch -> Nat -> Real}
    {VarDrop Cmul Y : Real} {K : Finset Nat} {A : Set Real}
    (data :
      CarryHitGapShellQCanonicalVariationInputData shell branches dropMass
        VarDrop Cmul Y K A) :
    CarryHitGapCanonicalVariationInputData shell.Q branches dropMass VarDrop
      Cmul Y K A where
  priority := data.priority.toCanonicalPriorityRecordData
  density := data.density

end CarryHitGapShellQCanonicalVariationInputData

/-- N.2.1 fixed-crossing-edge package, split into its lift/support and
finite-priority-record inputs. -/
structure CarryHitGapMultiplicityData
    {Branch Labels : Type} (recordQ : Nat) (branches : Finset Branch)
    (dropMass : Real -> Branch -> Nat -> Real)
    (crossingIndic : Real -> Nat -> Real) where
  liftSupport :
    CarryHitGapLiftSupportData branches dropMass crossingIndic
  priority :
    CarryHitGapPriorityRecordData (Branch := Branch) (Labels := Labels)
      recordQ liftSupport.support

/-- Decidable equality on the branch type supplied by the lift/support certificate. -/
@[reducible]
def CarryHitGapMultiplicityData.decBranch
    {Branch Labels : Type} {recordQ : Nat} {branches : Finset Branch}
    {dropMass : Real -> Branch -> Nat -> Real}
    {crossingIndic : Real -> Nat -> Real}
    (data :
      CarryHitGapMultiplicityData (Branch := Branch) (Labels := Labels)
        recordQ branches dropMass crossingIndic) :
    DecidableEq Branch :=
  data.liftSupport.decBranch

/-- Decidable equality on finite priority labels supplied by the priority record. -/
@[reducible]
def CarryHitGapMultiplicityData.decLabels
    {Branch Labels : Type} {recordQ : Nat} {branches : Finset Branch}
    {dropMass : Real -> Branch -> Nat -> Real}
    {crossingIndic : Real -> Nat -> Real}
    (data :
      CarryHitGapMultiplicityData (Branch := Branch) (Labels := Labels)
        recordQ branches dropMass crossingIndic) :
    DecidableEq Labels :=
  data.priority.decLabels

/-- Finiteness of the priority label type supplied by the priority record. -/
@[reducible]
def CarryHitGapMultiplicityData.fintypeLabels
    {Branch Labels : Type} {recordQ : Nat} {branches : Finset Branch}
    {dropMass : Real -> Branch -> Nat -> Real}
    {crossingIndic : Real -> Nat -> Real}
    (data :
      CarryHitGapMultiplicityData (Branch := Branch) (Labels := Labels)
        recordQ branches dropMass crossingIndic) :
    Fintype Labels :=
  data.priority.fintypeLabels

/-- The shell denominator is nonzero in the priority record. -/
@[reducible]
def CarryHitGapMultiplicityData.recordQ_neZero
    {Branch Labels : Type} {recordQ : Nat} {branches : Finset Branch}
    {dropMass : Real -> Branch -> Nat -> Real}
    {crossingIndic : Real -> Nat -> Real}
    (data :
      CarryHitGapMultiplicityData (Branch := Branch) (Labels := Labels)
        recordQ branches dropMass crossingIndic) :
    NeZero recordQ :=
  data.priority.recordQ_neZero

/-- The first-crossing record family carried by the priority certificate. -/
def CarryHitGapMultiplicityData.D
    {Branch Labels : Type} {recordQ : Nat} {branches : Finset Branch}
    {dropMass : Real -> Branch -> Nat -> Real}
    {crossingIndic : Real -> Nat -> Real}
    (data :
      CarryHitGapMultiplicityData (Branch := Branch) (Labels := Labels)
        recordQ branches dropMass crossingIndic) :
    Real -> AppendixN.FirstCrossingRecordData Branch recordQ Labels :=
  data.priority.D

/-- The support family carried by the lift/support certificate. -/
def CarryHitGapMultiplicityData.support
    {Branch Labels : Type} {recordQ : Nat} {branches : Finset Branch}
    {dropMass : Real -> Branch -> Nat -> Real}
    {crossingIndic : Real -> Nat -> Real}
    (data :
      CarryHitGapMultiplicityData (Branch := Branch) (Labels := Labels)
        recordQ branches dropMass crossingIndic) :
    Real -> Nat -> Finset Branch :=
  data.liftSupport.support

/-- The canonical lift/support inequality carried by the N.2.1 certificate. -/
theorem CarryHitGapMultiplicityData.lift_bound
    {Branch Labels : Type} {recordQ : Nat} {branches : Finset Branch}
    {dropMass : Real -> Branch -> Nat -> Real}
    {crossingIndic : Real -> Nat -> Real}
    (data :
      CarryHitGapMultiplicityData (Branch := Branch) (Labels := Labels)
        recordQ branches dropMass crossingIndic) :
    forall T b e, dropMass T b e <= crossingIndic T e :=
  data.liftSupport.hlift_le

/-- The canonical lift/support inequality, named as the field projected into
the Appendix N fibre-counting bridge. -/
theorem CarryHitGapMultiplicityData.hlift_le
    {Branch Labels : Type} {recordQ : Nat} {branches : Finset Branch}
    {dropMass : Real -> Branch -> Nat -> Real}
    {crossingIndic : Real -> Nat -> Real}
    (data :
      CarryHitGapMultiplicityData (Branch := Branch) (Labels := Labels)
        recordQ branches dropMass crossingIndic) :
    forall T b e, dropMass T b e <= crossingIndic T e :=
  data.liftSupport.hlift_le

/-- The support family stays inside the active branch family. -/
theorem CarryHitGapMultiplicityData.hsupp
    {Branch Labels : Type} {recordQ : Nat} {branches : Finset Branch}
    {dropMass : Real -> Branch -> Nat -> Real}
    {crossingIndic : Real -> Nat -> Real}
    (data :
      CarryHitGapMultiplicityData (Branch := Branch) (Labels := Labels)
        recordQ branches dropMass crossingIndic) :
    forall T e, data.support T e ⊆branches := by
  simpa [CarryHitGapMultiplicityData.support] using data.liftSupport.hsupp

/-- Drop mass vanishes off the support family. -/
theorem CarryHitGapMultiplicityData.hzero
    {Branch Labels : Type} {recordQ : Nat} {branches : Finset Branch}
    {dropMass : Real -> Branch -> Nat -> Real}
    {crossingIndic : Real -> Nat -> Real}
    (data :
      CarryHitGapMultiplicityData (Branch := Branch) (Labels := Labels)
        recordQ branches dropMass crossingIndic) :
    forall T e, forall b, b ∈ branches -> b ∉ data.support T e -> dropMass T b e = 0 := by
  simpa [CarryHitGapMultiplicityData.support] using data.liftSupport.hzero

/-- The first-crossing record endpoints are ordered. -/
theorem CarryHitGapMultiplicityData.hle
    {Branch Labels : Type} {recordQ : Nat} {branches : Finset Branch}
    {dropMass : Real -> Branch -> Nat -> Real}
    {crossingIndic : Real -> Nat -> Real}
    (data :
      CarryHitGapMultiplicityData (Branch := Branch) (Labels := Labels)
        recordQ branches dropMass crossingIndic) :
    forall T e, (data.D T).loIdx e <= (data.D T).hiIdx e := by
  simpa [CarryHitGapMultiplicityData.D] using data.priority.hle

/-- The priority-injectivity input carried by the N.2.1 certificate. -/
theorem CarryHitGapMultiplicityData.priority_injective
    {Branch Labels : Type} {recordQ : Nat} {branches : Finset Branch}
    {dropMass : Real -> Branch -> Nat -> Real}
    {crossingIndic : Real -> Nat -> Real}
    (data :
      CarryHitGapMultiplicityData (Branch := Branch) (Labels := Labels)
        recordQ branches dropMass crossingIndic) :
    forall T (e : Nat), forall b, b ∈ data.support T e ->
      forall b', b' ∈ data.support T e ->
        (data.D T).record e b = (data.D T).record e b' ->
          (data.D T).startResidue b = (data.D T).startResidue b' -> b = b' :=
  by
    simpa [CarryHitGapMultiplicityData.support, CarryHitGapMultiplicityData.D] using
      data.priority.hinj

/-- The priority-injectivity input carried by the N.2.1 certificate. -/
theorem CarryHitGapMultiplicityData.hinj
    {Branch Labels : Type} {recordQ : Nat} {branches : Finset Branch}
    {dropMass : Real -> Branch -> Nat -> Real}
    {crossingIndic : Real -> Nat -> Real}
    (data :
      CarryHitGapMultiplicityData (Branch := Branch) (Labels := Labels)
        recordQ branches dropMass crossingIndic) :
    forall T (e : Nat), forall b, b ∈ data.support T e ->
      forall b', b' ∈ data.support T e ->
        (data.D T).record e b = (data.D T).record e b' ->
          (data.D T).startResidue b = (data.D T).startResidue b' -> b = b' := by
  simpa [CarryHitGapMultiplicityData.support, CarryHitGapMultiplicityData.D] using
    data.priority.hinj

structure CarryHitGapVariationClassData
    {shell : FailingDyadicShell}
    (carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (h_supportCount_pos : 1 <= supportCount shell.d shell.X)
    (O_V : Real) where
  Branch : Type
  VarDrop : Real
  Cmul : Real
  Y : Real
  s : Nat
  branches : Finset Branch
  decBranch : DecidableEq Branch
  dropMass :
    (T : Real) -> Branch -> (e : Nat) ->
      {x : Real // 0 <= x ∧
        x <=
          AppendixN.crossingIndicator (T + Y)
            (AppendixN.windowSum
              (fun n =>
              (hitGap
                  (carryLocal.toCarryData erdos260Constants_cPr_le_half
                    hc0Small h_supportCount_pos).a n : Real)) s) e}
  K : Finset Nat
  A : Set Real
  variation_input :
    letI : DecidableEq Branch := decBranch
    CarryHitGapCanonicalVariationInputData shell.Q branches
      (fun T b e => (dropMass T b e : Real)) VarDrop Cmul Y K A
  hDropY : Y = carryLocal.Y
  hDropK_window :
    K ⊆      Finset.Ico s
        ((carryLocal.toCarryData erdos260Constants_cPr_le_half
          hc0Small h_supportCount_pos).carry.hits.firstIndexAbove shell.X +
          (carryLocal.toCarryData erdos260Constants_cPr_le_half
            hc0Small h_supportCount_pos).r - 1)
  hCmulY : 0 <= Cmul * Y
  hWindow :
    (Cmul *
        (((shell.Q *
          (@Fintype.card variation_input.priority.Labels
            variation_input.priority.fintypeLabels) *
          shell.Q : Nat) : Real))) *
        Y *
          (2 *
            (((carryLocal.toCarryData erdos260Constants_cPr_le_half
              hc0Small h_supportCount_pos).L + carryB shell.Q + 1 : Nat) : Real) *
          (K.card : Real)) <= O_V

/-- The admissible N.2 rolling-window edge interval for the real carry hit-gap
sequence. -/
def carryHitGapAdmissibleEdgeWindow
    {shell : FailingDyadicShell}
    (carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (h_supportCount_pos : 1 <= supportCount shell.d shell.X)
    (s : Nat) : Finset Nat :=
  Finset.Ico s
    ((carryLocal.toCarryData erdos260Constants_cPr_le_half
      hc0Small h_supportCount_pos).carry.hits.firstIndexAbove shell.X +
      (carryLocal.toCarryData erdos260Constants_cPr_le_half
        hc0Small h_supportCount_pos).r - 1)

/-- Forget window-typed N.2 edges back to ordinary natural-number edges. -/
def carryHitGapWindowEdgeSet
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (s : Nat)
    (K :
      Finset {e : Nat //
        e ∈ carryHitGapAdmissibleEdgeWindow carryLocal hc0Small
          h_supportCount_pos s}) :
    Finset Nat :=
  K.image Subtype.val

/-- Window-typed N.2 edges are automatically in the admissible edge interval. -/
theorem carryHitGapWindowEdgeSet_subset
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {s : Nat}
    (K :
      Finset {e : Nat //
        e ∈ carryHitGapAdmissibleEdgeWindow carryLocal hc0Small
          h_supportCount_pos s}) :
    carryHitGapWindowEdgeSet s K ⊆
      carryHitGapAdmissibleEdgeWindow carryLocal hc0Small
        h_supportCount_pos s := by
  intro e he
  rcases Finset.mem_image.mp he with ⟨edge, _hedge, hedge⟩
  simpa [hedge] using edge.property

/--
Variation-drop package with the active excess floor canonicalized to the carry
package's `Y`, the coarea multiplier kept as a natural number, and active drop
edges typed as members of the admissible rolling-window interval.  The N.2.1
first-crossing record is carried in shell-`Q` ordered form, and branch
decidability is recovered classically when projecting to older interfaces.  This
removes the proof-only equality field `hDropY`, the bookkeeping nonnegativity
field `hCmulY`, the window-subset field `hDropK_window`, denominator
nonzeroness, the ordered-window `hle` field, and the Lean-only `decBranch`
instance from the provider surface.
-/
structure CarryHitGapCanonicalYVariationClassData
    {shell : FailingDyadicShell}
    (carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (h_supportCount_pos : 1 <= supportCount shell.d shell.X)
    (O_V : Real) where
  Branch : Type
  VarDrop : Real
  Cmul : Nat
  s : Nat
  branches : Finset Branch
  dropMass :
    (T : Real) -> Branch -> (e : Nat) ->
      {x : Real // 0 <= x ∧
        x <=
          AppendixN.crossingIndicator (T + carryLocal.Y)
            (AppendixN.windowSum
              (fun n =>
              (hitGap
              (carryLocal.toCarryData erdos260Constants_cPr_le_half
                    hc0Small h_supportCount_pos).a n : Real)) s) e}
  K :
    Finset {e : Nat //
      e ∈ carryHitGapAdmissibleEdgeWindow carryLocal hc0Small
        h_supportCount_pos s}
  A : Set Real
  variation_input :
    letI : DecidableEq Branch := Classical.decEq Branch
    CarryHitGapShellQCanonicalVariationInputData shell branches
      (fun T b e => (dropMass T b e : Real)) VarDrop (Cmul : Real)
      carryLocal.Y (carryHitGapWindowEdgeSet s K) A
  hWindow :
    letI : DecidableEq Branch := Classical.decEq Branch
    ((Cmul : Real) *
        (((shell.Q * variation_input.priority.labelCount * shell.Q : Nat) : Real))) *
        carryLocal.Y *
          (2 *
            (((carryLocal.toCarryData erdos260Constants_cPr_le_half
          hc0Small h_supportCount_pos).L + carryB shell.Q + 1 : Nat) : Real) *
              ((carryHitGapWindowEdgeSet s K).card : Real)) <= O_V

/-- Assemble the canonical-`Y` variation class from the proof-v4 N.2.1
priority-record data and N.2.2 canonical drop-density data. -/
def CarryHitGapCanonicalYVariationClassData.ofClosedN21N22
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    {Branch : Type}
    (VarDrop : Real)
    (Cmul : Nat)
    (s : Nat)
    (branches : Finset Branch)
    (dropMass :
      (T : Real) -> Branch -> (e : Nat) ->
        {x : Real // 0 <= x ∧
          x <=
            AppendixN.crossingIndicator (T + carryLocal.Y)
              (AppendixN.windowSum
                (fun n =>
                (hitGap
                (carryLocal.toCarryData erdos260Constants_cPr_le_half
                      hc0Small h_supportCount_pos).a n : Real)) s) e})
    (K :
      Finset {e : Nat //
        e ∈ carryHitGapAdmissibleEdgeWindow carryLocal hc0Small
          h_supportCount_pos s})
    (A : Set Real)
    (priority :
      letI : DecidableEq Branch := Classical.decEq Branch
      CarryHitGapShellQCanonicalPriorityRecordData (Branch := Branch) shell
        (fun T e => branches.filter fun b => (dropMass T b e : Real) ≠ 0))
    (density :
      CarryHitGapCanonicalDropDensityData branches
        (fun T b e => (dropMass T b e : Real)) VarDrop (Cmul : Real)
        carryLocal.Y (carryHitGapWindowEdgeSet s K) A)
    (hWindow :
      letI : DecidableEq Branch := Classical.decEq Branch
      ((Cmul : Real) *
          (((shell.Q * priority.labelCount * shell.Q : Nat) : Real))) *
          carryLocal.Y *
            (2 *
              (((carryLocal.toCarryData erdos260Constants_cPr_le_half
                hc0Small h_supportCount_pos).L + carryB shell.Q + 1 : Nat) : Real) *
                ((carryHitGapWindowEdgeSet s K).card : Real)) <= O_V) :
    CarryHitGapCanonicalYVariationClassData carryLocal hc0Small
      h_supportCount_pos O_V where
  Branch := Branch
  VarDrop := VarDrop
  Cmul := Cmul
  s := s
  branches := branches
  dropMass := dropMass
  K := K
  A := A
  variation_input := by
    letI : DecidableEq Branch := Classical.decEq Branch
    exact {
      priority := priority
      density := density }
  hWindow := by
    letI : DecidableEq Branch := Classical.decEq Branch
    exact hWindow

set_option linter.unusedVariables false in
/--
N.2 canonical-`Y` variation leaf before it is packed as
`CarryHitGapCanonicalYVariationClassData`: N.2.1 supplies the priority record,
N.2.2 supplies the canonical drop-density package, and `hWindow` is the final
window/phase budget comparison.
-/
structure CarryHitGapCanonicalYVariationLeafData
    {shell : FailingDyadicShell}
    (carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (h_supportCount_pos : 1 <= supportCount shell.d shell.X)
    (O_V : Real) where
  Branch : Type
  VarDrop : Real
  Cmul : Nat
  s : Nat
  branches : Finset Branch
  dropMass :
    (T : Real) -> Branch -> (e : Nat) ->
      {x : Real // 0 <= x ∧
        x <=
          AppendixN.crossingIndicator (T + carryLocal.Y)
            (AppendixN.windowSum
              (fun n =>
              (hitGap
              (carryLocal.toCarryData erdos260Constants_cPr_le_half
                    hc0Small h_supportCount_pos).a n : Real)) s) e}
  K :
    Finset {e : Nat //
      e ∈ carryHitGapAdmissibleEdgeWindow carryLocal hc0Small
        h_supportCount_pos s}
  A : Set Real
  priority :
    letI : DecidableEq Branch := Classical.decEq Branch
    CarryHitGapShellQCanonicalPriorityRecordData (Branch := Branch) shell
      (fun T e => branches.filter fun b => (dropMass T b e : Real) ≠ 0)
  density :
    CarryHitGapCanonicalDropDensityData branches
      (fun T b e => (dropMass T b e : Real)) VarDrop (Cmul : Real)
      carryLocal.Y (carryHitGapWindowEdgeSet s K) A
  hWindow :
    letI : DecidableEq Branch := Classical.decEq Branch
    ((Cmul : Real) *
        (((shell.Q * priority.labelCount * shell.Q : Nat) : Real))) *
        carryLocal.Y *
          (2 *
            (((carryLocal.toCarryData erdos260Constants_cPr_le_half
              hc0Small h_supportCount_pos).L + carryB shell.Q + 1 : Nat) : Real) *
                ((carryHitGapWindowEdgeSet s K).card : Real)) <= O_V

namespace CarryHitGapCanonicalYVariationLeafData

/-- Assemble the N.2 canonical-`Y` variation leaf from the manuscript
N.2.1 priority record, the N.2.2 drop-density certificate, and the final
window/phase budget comparison. -/
def ofClosedN21N22
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    {Branch : Type}
    (VarDrop : Real)
    (Cmul : Nat)
    (s : Nat)
    (branches : Finset Branch)
    (dropMass :
      (T : Real) -> Branch -> (e : Nat) ->
        {x : Real // 0 <= x ∧
          x <=
            AppendixN.crossingIndicator (T + carryLocal.Y)
              (AppendixN.windowSum
                (fun n =>
                (hitGap
                (carryLocal.toCarryData erdos260Constants_cPr_le_half
                      hc0Small h_supportCount_pos).a n : Real)) s) e})
    (K :
      Finset {e : Nat //
        e ∈ carryHitGapAdmissibleEdgeWindow carryLocal hc0Small
          h_supportCount_pos s})
    (A : Set Real)
    (priority :
      letI : DecidableEq Branch := Classical.decEq Branch
      CarryHitGapShellQCanonicalPriorityRecordData (Branch := Branch) shell
        (fun T e => branches.filter fun b => (dropMass T b e : Real) ≠ 0))
    (density :
      CarryHitGapCanonicalDropDensityData branches
        (fun T b e => (dropMass T b e : Real)) VarDrop (Cmul : Real)
        carryLocal.Y (carryHitGapWindowEdgeSet s K) A)
    (hWindow :
      letI : DecidableEq Branch := Classical.decEq Branch
      ((Cmul : Real) *
          (((shell.Q * priority.labelCount * shell.Q : Nat) : Real))) *
          carryLocal.Y *
            (2 *
              (((carryLocal.toCarryData erdos260Constants_cPr_le_half
                hc0Small h_supportCount_pos).L + carryB shell.Q + 1 : Nat) : Real) *
                ((carryHitGapWindowEdgeSet s K).card : Real)) <= O_V) :
    CarryHitGapCanonicalYVariationLeafData carryLocal hc0Small
      h_supportCount_pos O_V where
  Branch := Branch
  VarDrop := VarDrop
  Cmul := Cmul
  s := s
  branches := branches
  dropMass := dropMass
  K := K
  A := A
  priority := by
    letI : DecidableEq Branch := Classical.decEq Branch
    exact priority
  density := density
  hWindow := by
    letI : DecidableEq Branch := Classical.decEq Branch
    exact hWindow

/-- Pack the N.2.1/N.2.2 canonical-`Y` variation leaf. -/
def toVariationClassData
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    (data :
      CarryHitGapCanonicalYVariationLeafData carryLocal hc0Small
        h_supportCount_pos O_V) :
    CarryHitGapCanonicalYVariationClassData carryLocal hc0Small
      h_supportCount_pos O_V :=
  CarryHitGapCanonicalYVariationClassData.ofClosedN21N22
    data.VarDrop data.Cmul data.s data.branches data.dropMass data.K data.A
    data.priority data.density data.hWindow

end CarryHitGapCanonicalYVariationLeafData

/-- Forget the canonical `Y = carryLocal.Y` choice to the older variation
package. -/
def CarryHitGapCanonicalYVariationClassData.toVariationClassData
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    (data :
      CarryHitGapCanonicalYVariationClassData carryLocal hc0Small
        h_supportCount_pos O_V) :
    CarryHitGapVariationClassData carryLocal hc0Small h_supportCount_pos O_V where
  Branch := data.Branch
  VarDrop := data.VarDrop
  Cmul := (data.Cmul : Real)
  Y := carryLocal.Y
  s := data.s
  branches := data.branches
  decBranch := Classical.decEq data.Branch
  dropMass := data.dropMass
  K := carryHitGapWindowEdgeSet data.s data.K
  A := data.A
  variation_input := by
    letI : DecidableEq data.Branch := Classical.decEq data.Branch
    exact data.variation_input.toCanonicalVariationInputData
  hDropY := rfl
  hDropK_window := by
    simpa [carryHitGapAdmissibleEdgeWindow] using
      carryHitGapWindowEdgeSet_subset data.K
  hCmulY := by
    exact mul_nonneg (by exact_mod_cast Nat.zero_le data.Cmul) carryLocal.hY
  hWindow := by
    letI : DecidableEq data.Branch := Classical.decEq data.Branch
    have hcard :
        Fintype.card (Fin data.variation_input.priority.labelCount) =
          data.variation_input.priority.labelCount := by
      simp
    change
      ((data.Cmul : Real) *
          (((shell.Q *
            (Fintype.card (Fin data.variation_input.priority.labelCount)) *
            shell.Q : Nat) : Real))) *
          carryLocal.Y *
            (2 *
              (((carryLocal.toCarryData erdos260Constants_cPr_le_half
                hc0Small h_supportCount_pos).L + carryB shell.Q + 1 : Nat) : Real) *
                ((carryHitGapWindowEdgeSet data.s data.K).card : Real)) <= O_V
    simpa [hcard] using data.hWindow

/-- Canonical N.2.1 priority-record input carried by the current variation package. -/
def CarryHitGapVariationClassData.priority
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    (data :
      CarryHitGapVariationClassData carryLocal hc0Small h_supportCount_pos
        O_V) :
    letI : DecidableEq data.Branch := data.decBranch
    CarryHitGapCanonicalPriorityRecordData (Branch := data.Branch) shell.Q
      (fun T e => data.branches.filter fun b => (data.dropMass T b e : Real) ≠0) := by
  letI : DecidableEq data.Branch := data.decBranch
  exact data.variation_input.priority

/-- Canonical N.2.2 drop-density input carried by the current variation package. -/
def CarryHitGapVariationClassData.density
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    (data :
      CarryHitGapVariationClassData carryLocal hc0Small h_supportCount_pos
        O_V) :
    CarryHitGapCanonicalDropDensityData data.branches
      (fun T b e => (data.dropMass T b e : Real)) data.VarDrop data.Cmul data.Y
      data.K data.A := by
  letI : DecidableEq data.Branch := data.decBranch
  exact data.variation_input.density

/-- Canonical priority-label type for the current variation package. -/
@[reducible]
def CarryHitGapVariationClassData.Labels
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    (data :
      CarryHitGapVariationClassData carryLocal hc0Small h_supportCount_pos
        O_V) : Type :=
  data.priority.Labels

/-- Decidable equality on canonical priority labels. -/
@[reducible]
def CarryHitGapVariationClassData.decLabels
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    (data :
      CarryHitGapVariationClassData carryLocal hc0Small h_supportCount_pos
        O_V) :
    DecidableEq data.Labels :=
  data.priority.decLabels

/-- Finiteness of canonical priority labels. -/
@[reducible]
def CarryHitGapVariationClassData.fintypeLabels
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    (data :
      CarryHitGapVariationClassData carryLocal hc0Small h_supportCount_pos
        O_V) :
    Fintype data.Labels :=
  data.priority.fintypeLabels

/-- Canonical carry hit-gap crossing indicator used by the variation package. -/
def CarryHitGapVariationClassData.crossingIndic
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    (data :
      CarryHitGapVariationClassData carryLocal hc0Small h_supportCount_pos
        O_V) :
    Real -> Nat -> Real :=
  fun T e =>
    AppendixN.crossingIndicator (T + data.Y)
      (AppendixN.windowSum
        (fun n =>
          (hitGap
            (carryLocal.toCarryData erdos260Constants_cPr_le_half
              hc0Small h_supportCount_pos).a n : Real)) data.s) e

/-- Canonical fixed-edge support: branches with nonzero drop mass. -/
def CarryHitGapVariationClassData.support
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    (data :
      CarryHitGapVariationClassData carryLocal hc0Small h_supportCount_pos
        O_V) :
    Real -> Nat -> Finset data.Branch := by
  letI : DecidableEq data.Branch := data.decBranch
  exact fun T e => data.branches.filter fun b => (data.dropMass T b e : Real) ≠0

/-- Canonical N.2.1 lift/support package from nonzero support and bounded drop mass. -/
def CarryHitGapVariationClassData.liftSupport
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    (data :
      CarryHitGapVariationClassData carryLocal hc0Small h_supportCount_pos
        O_V) :
    CarryHitGapLiftSupportData data.branches
      (fun T b e => (data.dropMass T b e : Real)) data.crossingIndic := by
  letI : DecidableEq data.Branch := data.decBranch
  exact {
    supportData := {
      decBranch := data.decBranch
      support := data.support
      hsupp := by
        intro T e b hb
        exact (Finset.mem_filter.mp hb).1 }
    liftBound := {
      hlift_le := by
        intro T b e
        simpa [CarryHitGapVariationClassData.crossingIndic] using
          (data.dropMass T b e).property.2 }
    zeroOutside := {
      hzero := by
        intro T e b hb hnot
        by_contra hne
        exact hnot (Finset.mem_filter.mpr ⟨hb, hne⟩) } }

/-- N.2.1 multiplicity data with lift/support closed canonically. -/
def CarryHitGapVariationClassData.multiplicity
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    (data :
      CarryHitGapVariationClassData carryLocal hc0Small h_supportCount_pos
        O_V) :
    CarryHitGapMultiplicityData (Branch := data.Branch) (Labels := data.Labels)
      shell.Q data.branches (fun T b e => (data.dropMass T b e : Real))
      data.crossingIndic where
  liftSupport := data.liftSupport
  priority := by
    letI : DecidableEq data.Branch := data.decBranch
    simpa [CarryHitGapVariationClassData.support] using
      data.priority.toPriorityRecordData

/-- The explicit carry-hitGap N.13 window bound attached to a variation package. -/
def CarryHitGapVariationClassData.windowBound
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
  (data :
      CarryHitGapVariationClassData carryLocal hc0Small h_supportCount_pos
        O_V) : Real :=
  (data.Cmul *
      (((shell.Q * data.priority.labelCount * shell.Q : Nat) : Real))) *
    data.Y *
      (2 *
        ((((carryLocal.toCarryData erdos260Constants_cPr_le_half
          hc0Small h_supportCount_pos).L + carryB shell.Q + 1 : Nat) : Real)) *
          (data.K.card : Real))

/-- The first-crossing record denominator in the final variation package is the
actual shell denominator `Q`, not a free auxiliary parameter. -/
def CarryHitGapVariationClassData.recordDenominator
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    (_data :
      CarryHitGapVariationClassData carryLocal hc0Small h_supportCount_pos
        O_V) : Nat :=
  shell.Q

/-- The final N.2.1/N.2.2 variation package is pinned to the shell denominator. -/
theorem CarryHitGapVariationClassData.recordDenominator_eq_shellQ
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    (data :
      CarryHitGapVariationClassData carryLocal hc0Small h_supportCount_pos
        O_V) :
    data.recordDenominator = shell.Q :=
  rfl

/-- The real-valued variation-drop mass underlying the nonnegative mass data. -/
def CarryHitGapVariationClassData.dropMassReal
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    (data :
      CarryHitGapVariationClassData carryLocal hc0Small h_supportCount_pos
        O_V) :
    Real -> data.Branch -> Nat -> Real :=
  fun T b e => data.dropMass T b e

/-- Canonical N.2.2 drop density for the current variation package. -/
def CarryHitGapVariationClassData.dropDensity
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    (data :
      CarryHitGapVariationClassData carryLocal hc0Small h_supportCount_pos
        O_V) :
    Real -> Real :=
  carryHitGapDropDensity data.branches data.dropMassReal data.K

/-- Variation-drop masses are nonnegative by type. -/
theorem CarryHitGapVariationClassData.hdrop_nonneg
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    (data :
      CarryHitGapVariationClassData carryLocal hc0Small h_supportCount_pos
        O_V) :
    forall T b e, 0 <= data.dropMassReal T b e := by
  intro T b e
  exact (data.dropMass T b e).property.1

/-- The N.2.1 lift/support certificate, specialized to the canonical hit-gap
crossing indicator used by the variation package. -/
theorem CarryHitGapVariationClassData.hlift_le
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    (data :
      CarryHitGapVariationClassData carryLocal hc0Small h_supportCount_pos
        O_V) :
    forall T b e,
      data.dropMassReal T b e <=
        AppendixN.crossingIndicator (T + data.Y)
          (AppendixN.windowSum
            (fun n =>
              (hitGap
                (carryLocal.toCarryData erdos260Constants_cPr_le_half
                  hc0Small h_supportCount_pos).a n : Real)) data.s) e :=
  data.multiplicity.hlift_le

/-- The canonical carry hit-gap crossing indicator used by the variation package
is nonnegative; this is closed by the Appendix N crossing-indicator theorem. -/
theorem CarryHitGapVariationClassData.crossingIndicator_nonneg
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    (data :
      CarryHitGapVariationClassData carryLocal hc0Small h_supportCount_pos
        O_V) :
    forall T e,
      0 <=
        AppendixN.crossingIndicator (T + data.Y)
          (AppendixN.windowSum
            (fun n =>
              (hitGap
                (carryLocal.toCarryData erdos260Constants_cPr_le_half
                  hc0Small h_supportCount_pos).a n : Real)) data.s) e := by
  intro T e
  exact
    AppendixN.crossingIndicator_nonneg (T + data.Y)
      (AppendixN.windowSum
        (fun n =>
          (hitGap
            (carryLocal.toCarryData erdos260Constants_cPr_le_half
              hc0Small h_supportCount_pos).a n : Real)) data.s) e

/-- Pointwise N.2.1-to-N.2.2 bridge for the real carry hit-gap window:
the drop-density integrand is bounded by the first-crossing count with the
reduced-record multiplicity constant. -/
theorem CarryHitGapVariationClassData.dropDensity_le_crossingCount
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    (data :
      CarryHitGapVariationClassData carryLocal hc0Small h_supportCount_pos
        O_V) :
    forall T, T ∈ data.A ->
      data.dropDensity T <=
        (((shell.Q *
            (@Fintype.card data.Labels data.multiplicity.fintypeLabels) *
          shell.Q : Nat) : Real)) *
          AppendixN.crossingCountReal (T + data.Y)
            (AppendixN.windowSum
              (fun n =>
                (hitGap
                  (carryLocal.toCarryData erdos260Constants_cPr_le_half
                    hc0Small h_supportCount_pos).a n : Real)) data.s) data.K := by
  intro T hT
  let carryData :=
    carryLocal.toCarryData erdos260Constants_cPr_le_half
      hc0Small h_supportCount_pos
  letI : DecidableEq data.Branch := data.multiplicity.decBranch
  letI : DecidableEq data.Labels := data.multiplicity.decLabels
  letI : Fintype data.Labels := data.multiplicity.fintypeLabels
  letI : NeZero shell.Q := data.multiplicity.recordQ_neZero
  exact
    AppendixN.dropDensity_le_count_of_lowerLabelRecordPriorityOfRecord
      data.multiplicity.D data.branches data.dropDensity data.dropMassReal
      data.hdrop_nonneg
      (fun T e =>
        AppendixN.crossingIndicator (T + data.Y)
          (AppendixN.windowSum
            (fun n => (hitGap carryData.a n : Real)) data.s) e)
      (fun T e => by
        simpa [carryData] using data.crossingIndicator_nonneg T e)
      data.multiplicity.hlift_le data.multiplicity.support
      data.multiplicity.hsupp data.multiplicity.hzero data.multiplicity.hle
      data.multiplicity.hinj data.K data.Y
      (AppendixN.windowSum
        (fun n => (hitGap carryData.a n : Real)) data.s)
      data.A
      (by
        simpa [CarryHitGapVariationClassData.dropMassReal] using
          data.density.hdensity)
      (by intro T _hT e; rfl) hT

/-- Bundle the real carry-hitGap drop-density certificate into Appendix N's
`WindowDropEstimateData` first-inequality package. -/
def CarryHitGapVariationClassData.toWindowDropEstimateData
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    (data :
      CarryHitGapVariationClassData carryLocal hc0Small h_supportCount_pos
        O_V) :
    AppendixN.WindowDropEstimateData :=
  AppendixN.WindowDropEstimateData.ofScaledDropDensityBound
    data.VarDrop data.Cmul
    ((((shell.Q *
        (@Fintype.card data.Labels data.multiplicity.fintypeLabels) *
      shell.Q : Nat) : Real)))
    data.Y data.dropDensity
    (AppendixN.windowSum
      (fun n =>
        (hitGap
          (carryLocal.toCarryData erdos260Constants_cPr_le_half
            hc0Small h_supportCount_pos).a n : Real)) data.s)
    data.K data.A data.hCmulY
    (by
      exact_mod_cast
        Nat.zero_le
          (shell.Q *
            (@Fintype.card data.Labels data.multiplicity.fintypeLabels) *
              shell.Q))
    data.density.hA data.density.hdrop_int data.density.hvar
    data.dropDensity_le_crossingCount

/-- Bundled N.2.2 window-drop first inequality for the real carry-hitGap
variation package. -/
theorem CarryHitGapVariationClassData.windowDropEstimate_bound
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    (data :
      CarryHitGapVariationClassData carryLocal hc0Small h_supportCount_pos
        O_V) :
    data.VarDrop <=
      (data.Cmul *
          (((shell.Q *
              (@Fintype.card data.Labels data.multiplicity.fintypeLabels) *
            shell.Q : Nat) : Real))) *
        data.Y *
          AppendixN.Vs data.K
            (AppendixN.windowSum
              (fun n =>
                (hitGap
                  (carryLocal.toCarryData erdos260Constants_cPr_le_half
                    hc0Small h_supportCount_pos).a n : Real)) data.s) := by
  simpa [CarryHitGapVariationClassData.toWindowDropEstimateData] using
    (data.toWindowDropEstimateData.bound)

/-- Appendix N.2/N.13, specialized to the real carry hit-gap window. -/
theorem CarryHitGapVariationClassData.varDrop_le_windowBound
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    (data :
      CarryHitGapVariationClassData carryLocal hc0Small h_supportCount_pos
        O_V) :
    data.VarDrop <= data.windowBound := by
  let carryData :=
    carryLocal.toCarryData erdos260Constants_cPr_le_half
      hc0Small h_supportCount_pos
  letI : DecidableEq data.Branch := data.multiplicity.decBranch
  letI : DecidableEq data.Labels := data.multiplicity.decLabels
  letI : Fintype data.Labels := data.multiplicity.fintypeLabels
  letI : NeZero shell.Q := data.multiplicity.recordQ_neZero
  have hK : forall k, k ∈ data.K -> data.s <= k := by
    intro k hk
    exact (Finset.mem_Ico.mp (data.hDropK_window hk)).1
  have hKwin :
      forall k, k ∈ data.K ->
        k + 1 < carryData.carry.hits.firstIndexAbove shell.X + carryData.r := by
    intro k hk
    have hklt :
        k <
          carryData.carry.hits.firstIndexAbove shell.X + carryData.r - 1 :=
      (Finset.mem_Ico.mp (data.hDropK_window hk)).2
    omega
  have hcard :
      @Fintype.card data.Labels data.multiplicity.fintypeLabels =
        data.priority.labelCount := by
    change Fintype.card (Fin data.priority.labelCount) = data.priority.labelCount
    exact Fintype.card_fin data.priority.labelCount
  dsimp [CarryHitGapVariationClassData.windowBound, carryData]
  simpa [CarryHitGapVariationClassData.Labels,
    CarryHitGapCanonicalPriorityRecordData.Labels, hcard] using
        AppendixN.varDrop_le_from_lowerLabelRecordPriorityOfRecord_density_carryHitGap
      (carryLocal.toCarryData erdos260Constants_cPr_le_half
        hc0Small h_supportCount_pos)
      (P := Classical.choose shell.hrational)
      (B := carryB shell.Q)
      (Classical.choose_spec shell.hrational)
      (by
        change shell.X = 2 ^ Classical.choose shell.hXdyadic
        exact Classical.choose_spec shell.hXdyadic)
      (Nat.succ_le_of_lt (dyadic_pos shell.hXdyadic))
      (carryB_spec shell.hQ)
      carryLocal.hKr
      data.VarDrop data.Cmul data.Y data.multiplicity.D data.branches data.dropDensity
      data.dropMassReal data.hdrop_nonneg
      (fun T e =>
        AppendixN.crossingIndicator (T + data.Y)
          (AppendixN.windowSum
            (fun n => (hitGap carryData.a n : Real)) data.s) e)
      (fun T e => by
        simpa [carryData] using data.crossingIndicator_nonneg T e)
      data.multiplicity.hlift_le data.multiplicity.support
      data.multiplicity.hsupp data.multiplicity.hzero data.multiplicity.hle
      data.multiplicity.hinj
      data.s data.K data.A hK hKwin data.hCmulY data.density.hA
      data.density.hdrop_int data.density.hvar
      (by
        simpa [CarryHitGapVariationClassData.dropMassReal] using
          data.density.hdensity)
      (by intro T _hT e; rfl)

/-- The explicit carry-hitGap window bound is assigned to the variation class. -/
theorem CarryHitGapVariationClassData.windowBound_le_class
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
  (data :
      CarryHitGapVariationClassData carryLocal hc0Small h_supportCount_pos
        O_V) :
    data.windowBound <= O_V := by
  simpa [CarryHitGapVariationClassData.windowBound] using data.hWindow

/-- The current N.2/N.13 variation package pays its VarDrop mass into the
variation phase class. -/
theorem CarryHitGapVariationClassData.varDrop_le_class
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    (data :
      CarryHitGapVariationClassData carryLocal hc0Small h_supportCount_pos
        O_V) :
    data.VarDrop <= O_V :=
  data.varDrop_le_windowBound.trans data.windowBound_le_class

/-- Canonical-Y N.2.1 priority-record input carried by the canonical variation
package. -/
def CarryHitGapCanonicalYVariationClassData.priority
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    (data :
      CarryHitGapCanonicalYVariationClassData carryLocal hc0Small
        h_supportCount_pos O_V) :
    letI : DecidableEq data.Branch := Classical.decEq data.Branch
    CarryHitGapShellQCanonicalPriorityRecordData (Branch := data.Branch) shell
      (fun T e => data.branches.filter fun b => (data.dropMass T b e : Real) ≠ 0) := by
  letI : DecidableEq data.Branch := Classical.decEq data.Branch
  exact data.variation_input.priority

/-- Canonical-Y N.2.2 drop-density input carried by the canonical variation
package. -/
def CarryHitGapCanonicalYVariationClassData.density
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    (data :
      CarryHitGapCanonicalYVariationClassData carryLocal hc0Small
        h_supportCount_pos O_V) :
    CarryHitGapCanonicalDropDensityData data.branches
      (fun T b e => (data.dropMass T b e : Real)) data.VarDrop (data.Cmul : Real)
      carryLocal.Y (carryHitGapWindowEdgeSet data.s data.K) data.A := by
  letI : DecidableEq data.Branch := Classical.decEq data.Branch
  exact data.variation_input.density

/-- The canonical-Y variation package satisfies the reduced-record N.2/N.13
window bound after projecting to the current variation-class shape. -/
theorem CarryHitGapCanonicalYVariationClassData.varDrop_le_projected_windowBound
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    (data :
      CarryHitGapCanonicalYVariationClassData carryLocal hc0Small
        h_supportCount_pos O_V) :
    data.VarDrop <= data.toVariationClassData.windowBound :=
  data.toVariationClassData.varDrop_le_windowBound

/-- The canonical-Y N.2/N.13 variation package pays its VarDrop mass into the
variation phase class. -/
theorem CarryHitGapCanonicalYVariationClassData.varDrop_le_class
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    (data :
      CarryHitGapCanonicalYVariationClassData carryLocal hc0Small
        h_supportCount_pos O_V) :
    data.VarDrop <= O_V :=
  data.toVariationClassData.varDrop_le_class

namespace CarryHitGapCanonicalYVariationLeafData

/-- Project the N.2.1 shell-`Q` priority record from the canonical-`Y` leaf. -/
def priorityRecord
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    (data :
      CarryHitGapCanonicalYVariationLeafData carryLocal hc0Small
        h_supportCount_pos O_V) :
    letI : DecidableEq data.Branch := Classical.decEq data.Branch
    CarryHitGapShellQCanonicalPriorityRecordData (Branch := data.Branch) shell
      (fun T e => data.branches.filter fun b => (data.dropMass T b e : Real) ≠ 0) := by
  letI : DecidableEq data.Branch := Classical.decEq data.Branch
  exact data.priority

/-- Project the N.2.2 canonical drop-density data from the canonical-`Y` leaf. -/
def densityData
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    (data :
      CarryHitGapCanonicalYVariationLeafData carryLocal hc0Small
        h_supportCount_pos O_V) :
    CarryHitGapCanonicalDropDensityData data.branches
      (fun T b e => (data.dropMass T b e : Real)) data.VarDrop (data.Cmul : Real)
      carryLocal.Y (carryHitGapWindowEdgeSet data.s data.K) data.A := by
  letI : DecidableEq data.Branch := Classical.decEq data.Branch
  exact data.density

/-- Project the Appendix N.2.2 window-drop estimate from the canonical-`Y` leaf. -/
def toWindowDropEstimateData
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    (data :
      CarryHitGapCanonicalYVariationLeafData carryLocal hc0Small
        h_supportCount_pos O_V) :
    AppendixN.WindowDropEstimateData :=
  CarryHitGapVariationClassData.toWindowDropEstimateData
    (CarryHitGapCanonicalYVariationClassData.toVariationClassData
      data.toVariationClassData)

/-- The canonical-`Y` leaf satisfies the N.2/N.13 projected window bound. -/
theorem varDrop_le_projected_windowBound
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    (data :
      CarryHitGapCanonicalYVariationLeafData carryLocal hc0Small
        h_supportCount_pos O_V) :
    data.VarDrop <=
      (CarryHitGapCanonicalYVariationClassData.toVariationClassData
        data.toVariationClassData).windowBound :=
  CarryHitGapCanonicalYVariationClassData.varDrop_le_projected_windowBound
    data.toVariationClassData

/-- The canonical-`Y` leaf pays its variation-drop mass into the `O_V` class. -/
theorem varDrop_le_class
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    (data :
      CarryHitGapCanonicalYVariationLeafData carryLocal hc0Small
        h_supportCount_pos O_V) :
    data.VarDrop <= O_V :=
  CarryHitGapCanonicalYVariationClassData.varDrop_le_class data.toVariationClassData

end CarryHitGapCanonicalYVariationLeafData

/-- Recover the N.2.1/N.2.2 canonical-`Y` variation leaf carried by the
canonical variation-class package. -/
def CarryHitGapCanonicalYVariationClassData.toLeafData
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    (data :
      CarryHitGapCanonicalYVariationClassData carryLocal hc0Small
        h_supportCount_pos O_V) :
    CarryHitGapCanonicalYVariationLeafData carryLocal hc0Small
      h_supportCount_pos O_V where
  Branch := data.Branch
  VarDrop := data.VarDrop
  Cmul := data.Cmul
  s := data.s
  branches := data.branches
  dropMass := data.dropMass
  K := data.K
  A := data.A
  priority := data.priority
  density := data.density
  hWindow := by
    letI : DecidableEq data.Branch := Classical.decEq data.Branch
    simpa using data.hWindow

/--
Direct five-class high-excess data with the variation-drop side bundled as the
proof-v4 N.2/N.13 variation-class package.
-/
structure VariationStructuredDirectFiveClassHighExcessLocalData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : Real))
    (carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (h_supportCount_pos : 1 <= supportCount shell.d shell.X) where
  termMass : Real
  O_D : Real
  O_P : Real
  O_E : Real
  O_CNL : Real
  O_bdd : Real
  O_V : Real
  variation :
    CarryHitGapVariationClassData carryLocal hc0Small h_supportCount_pos O_V
  hsplit :
    groundedHighExcessBranchMass
      (carryLocal.toCarryData erdos260Constants_cPr_le_half
        hc0Small h_supportCount_pos) = termMass + variation.VarDrop
  terminalAbsorption :
    DirectFiveClassTerminalAbsorptionData termMass O_D O_P O_E O_CNL O_bdd
  hD : O_D <= termDensePack phases.toClosurePhaseData
  hP : O_P <= termChernoff phases.toClosurePhaseData
  hE : O_E <= termReturn phases.toClosurePhaseData
  hCNL : O_CNL <= termCnl phases.toClosurePhaseData
  hbdd : O_bdd <= termTower phases.toClosurePhaseData
  hV : O_V <= termRun phases.toClosurePhaseData

/-- Forget the bundled variation-class package to the direct five-class package. -/
def variationStructuredDirectToDirectFiveClassData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      VariationStructuredDirectFiveClassHighExcessLocalData
        phases carryLocal hc0Small h_supportCount_pos) :
    DirectFiveClassTerminalAggregateHighExcessLocalData
      phases carryLocal hc0Small h_supportCount_pos := {
  Branch := data.variation.Branch
  Labels := data.variation.Labels
  decBranch := data.variation.multiplicity.decBranch
  decLabels := data.variation.multiplicity.decLabels
  fintypeLabels := data.variation.multiplicity.fintypeLabels
  recordQ := shell.Q
  recordQ_neZero := data.variation.multiplicity.recordQ_neZero
  VarDrop := data.variation.VarDrop
  Cmul := data.variation.Cmul
  Y := data.variation.Y
  D := data.variation.multiplicity.D
  branches := data.variation.branches
  dropDensity := data.variation.dropDensity
  dropMass := data.variation.dropMassReal
  hdrop_nonneg := data.variation.hdrop_nonneg
  crossingIndic :=
    fun T e =>
      AppendixN.crossingIndicator (T + data.variation.Y)
        (AppendixN.windowSum
          (fun n =>
            (hitGap
              (carryLocal.toCarryData erdos260Constants_cPr_le_half
                hc0Small h_supportCount_pos).a n : Real)) data.variation.s) e
  hindic_nonneg :=
    fun T e =>
      AppendixN.crossingIndicator_nonneg (T + data.variation.Y)
        (AppendixN.windowSum
          (fun n =>
            (hitGap
              (carryLocal.toCarryData erdos260Constants_cPr_le_half
                hc0Small h_supportCount_pos).a n : Real)) data.variation.s) e
  hlift_le := data.variation.multiplicity.hlift_le
  support := data.variation.multiplicity.support
  hsupp := data.variation.multiplicity.hsupp
  hzero := data.variation.multiplicity.hzero
  hle := data.variation.multiplicity.hle
  hinj := data.variation.multiplicity.hinj
  s := data.variation.s
  K := data.variation.K
  A := data.variation.A
  hDropY := data.variation.hDropY
  hDropK_window := data.variation.hDropK_window
  hCmulY := data.variation.hCmulY
  hA := data.variation.density.hA
  hdrop_int := data.variation.density.hdrop_int
  hvar := data.variation.density.hvar
  hdensity := data.variation.density.hdensity
  hindic := by intro T _hT e; rfl
  termMass := data.termMass
  O_D := data.O_D
  O_P := data.O_P
  O_E := data.O_E
  O_CNL := data.O_CNL
  O_bdd := data.O_bdd
  O_V := data.O_V
  hsplit := data.hsplit
  terminalAbsorption := data.terminalAbsorption
  hWindow := data.variation.hWindow
  hD := data.hD
  hP := data.hP
  hE := data.hE
  hCNL := data.hCNL
  hbdd := data.hbdd
  hV := data.hV }

/-- Bundled variation-class direct data gives central high-excess data. -/
def variationStructuredDirectToHighExcessData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      VariationStructuredDirectFiveClassHighExcessLocalData
        phases carryLocal hc0Small h_supportCount_pos) :
    HighExcessChargeData phases
      (carryLocal.toCarryData erdos260Constants_cPr_le_half
        hc0Small h_supportCount_pos) :=
  directFiveClassToHighExcessData
    (variationStructuredDirectToDirectFiveClassData data)

/-- The six N.24 output classes booked against the six closure phase terms. -/
structure PhaseClassAccountingData
    {cStar ξ X : Real} (phases : SixPhaseFactoryData cStar ξ X) where
  O_D : Real
  O_P : Real
  O_E : Real
  O_CNL : Real
  O_bdd : Real
  O_V : Real
  hD : O_D <= termDensePack phases.toClosurePhaseData
  hP : O_P <= termChernoff phases.toClosurePhaseData
  hE : O_E <= termReturn phases.toClosurePhaseData
  hCNL : O_CNL <= termCnl phases.toClosurePhaseData
  hbdd : O_bdd <= termTower phases.toClosurePhaseData
  hV : O_V <= termRun phases.toClosurePhaseData

/-- The N.24 six-class accounting inequality in reusable package form. -/
theorem PhaseClassAccountingData.absorbed_window_le_phaseMass
    {cStar ξ X : Real} {phases : SixPhaseFactoryData cStar ξ X}
    (data : PhaseClassAccountingData phases)
    {absorbedBound windowBound : Real}
    (hAbsorbed :
      absorbedBound <=
        data.O_D + data.O_P + data.O_E + data.O_CNL + data.O_bdd)
    (hWindow : windowBound <= data.O_V) :
    absorbedBound + windowBound <= ClosurePhaseMass phases.toClosurePhaseData :=
  habsorb_ofC1VDClosure phases hAbsorbed hWindow
    data.hD data.hP data.hE data.hCNL data.hbdd data.hV

/--
The proof-v4 C1-VD/I.9 mass split, tied to the actual grounded branch mass and
the Appendix N variation-drop package.
-/
structure GroundedC1VDSplitData
    {shell : FailingDyadicShell}
    (carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (h_supportCount_pos : 1 <= supportCount shell.d shell.X)
    {O_V : Real}
    (variation :
      CarryHitGapVariationClassData carryLocal hc0Small h_supportCount_pos O_V) where
  termMass : Real
  hsplit :
    groundedHighExcessBranchMass
      (carryLocal.toCarryData erdos260Constants_cPr_le_half
        hc0Small h_supportCount_pos) = termMass + variation.VarDrop

namespace GroundedC1VDSplitData

/-- Canonical C1-VD split: define terminal mass as the complement of the
variation drop in the grounded branch mass. -/
def ofVariation
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    (variation :
      CarryHitGapVariationClassData carryLocal hc0Small h_supportCount_pos O_V) :
    GroundedC1VDSplitData carryLocal hc0Small h_supportCount_pos variation where
  termMass :=
    groundedHighExcessBranchMass
      (carryLocal.toCarryData erdos260Constants_cPr_le_half
        hc0Small h_supportCount_pos) - variation.VarDrop
  hsplit := by ring

@[simp] theorem ofVariation_termMass
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_V : Real}
    (variation :
      CarryHitGapVariationClassData carryLocal hc0Small h_supportCount_pos O_V) :
    (ofVariation variation).termMass =
      groundedHighExcessBranchMass
        (carryLocal.toCarryData erdos260Constants_cPr_le_half
          hc0Small h_supportCount_pos) - variation.VarDrop := by
  rfl

end GroundedC1VDSplitData

/--
High-excess data with proof-v4 N.24 class-to-phase accounting isolated from
the N.2 variation package and the direct N.3.3 terminal absorption package.
-/
structure PhaseAccountedVariationStructuredHighExcessLocalData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : Real))
    (carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (h_supportCount_pos : 1 <= supportCount shell.d shell.X) where
  termMass : Real
  accounting : PhaseClassAccountingData phases
  variation :
    CarryHitGapVariationClassData carryLocal hc0Small h_supportCount_pos
      accounting.O_V
  hsplit :
    groundedHighExcessBranchMass
      (carryLocal.toCarryData erdos260Constants_cPr_le_half
        hc0Small h_supportCount_pos) = termMass + variation.VarDrop
  terminalAbsorption :
    DirectFiveClassTerminalAbsorptionData termMass
      accounting.O_D accounting.O_P accounting.O_E accounting.O_CNL
      accounting.O_bdd

/-- Forget isolated phase accounting to the previous variation-structured package. -/
def phaseAccountedToVariationStructuredData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      PhaseAccountedVariationStructuredHighExcessLocalData
        phases carryLocal hc0Small h_supportCount_pos) :
    VariationStructuredDirectFiveClassHighExcessLocalData
      phases carryLocal hc0Small h_supportCount_pos := {
  termMass := data.termMass
  O_D := data.accounting.O_D
  O_P := data.accounting.O_P
  O_E := data.accounting.O_E
  O_CNL := data.accounting.O_CNL
  O_bdd := data.accounting.O_bdd
  O_V := data.accounting.O_V
  variation := data.variation
  hsplit := data.hsplit
  terminalAbsorption := data.terminalAbsorption
  hD := data.accounting.hD
  hP := data.accounting.hP
  hE := data.accounting.hE
  hCNL := data.accounting.hCNL
  hbdd := data.accounting.hbdd
  hV := data.accounting.hV }

/-- Phase-accounted high-excess data gives central high-excess data. -/
def phaseAccountedToHighExcessData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      PhaseAccountedVariationStructuredHighExcessLocalData
        phases carryLocal hc0Small h_supportCount_pos) :
    HighExcessChargeData phases
      (carryLocal.toCarryData erdos260Constants_cPr_le_half
        hc0Small h_supportCount_pos) :=
  variationStructuredDirectToHighExcessData
    (phaseAccountedToVariationStructuredData data)

/--
Phase-accounted high-excess data whose C1-VD/I.9 split is an explicit package,
separate from phase accounting, variation-drop density, and terminal absorption.
-/
structure SplitPhaseAccountedVariationStructuredHighExcessLocalData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : Real))
    (carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (h_supportCount_pos : 1 <= supportCount shell.d shell.X) where
  accounting : PhaseClassAccountingData phases
  variation :
    CarryHitGapVariationClassData carryLocal hc0Small h_supportCount_pos
      accounting.O_V
  split :
    GroundedC1VDSplitData carryLocal hc0Small h_supportCount_pos variation
  terminalAbsorption :
    DirectFiveClassTerminalAbsorptionData split.termMass
      accounting.O_D accounting.O_P accounting.O_E accounting.O_CNL
      accounting.O_bdd

/-- The explicit-split package inherits the shell-denominator first-crossing
record from its variation-drop component. -/
theorem SplitPhaseAccountedVariationStructuredHighExcessLocalData.recordDenominator_eq_shellQ
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      SplitPhaseAccountedVariationStructuredHighExcessLocalData
        phases carryLocal hc0Small h_supportCount_pos) :
    data.variation.recordDenominator = shell.Q :=
  data.variation.recordDenominator_eq_shellQ

/-- The current explicit-split high-excess package exposes N.3.3 as a direct
terminal-mass-to-five-classes bound. -/
theorem SplitPhaseAccountedVariationStructuredHighExcessLocalData.terminalMass_le_classes
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      SplitPhaseAccountedVariationStructuredHighExcessLocalData
        phases carryLocal hc0Small h_supportCount_pos) :
    data.split.termMass <=
      data.accounting.O_D + data.accounting.O_P + data.accounting.O_E +
        data.accounting.O_CNL + data.accounting.O_bdd :=
  data.terminalAbsorption.termMass_le_classes

/-- The current local proof-v4 high-excess package pays its branch mass by the six phases. -/
theorem SplitPhaseAccountedVariationStructuredHighExcessLocalData.branchMass_le_phaseMass
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      SplitPhaseAccountedVariationStructuredHighExcessLocalData
        phases carryLocal hc0Small h_supportCount_pos) :
    groundedHighExcessBranchMass
        (carryLocal.toCarryData erdos260Constants_cPr_le_half
          hc0Small h_supportCount_pos)
      <= ClosurePhaseMass phases.toClosurePhaseData := by
  rw [data.split.hsplit]
  have hPhase :
      data.split.termMass + data.variation.windowBound <=
        ClosurePhaseMass phases.toClosurePhaseData :=
    data.accounting.absorbed_window_le_phaseMass
      data.terminalAbsorption.toHtermFiveClass
      data.variation.windowBound_le_class
  have hVar := data.variation.varDrop_le_windowBound
  linarith

/-- Direct central bridge statement for the explicit-C1-VD-split local package. -/
theorem SplitPhaseAccountedVariationStructuredHighExcessLocalData.highExcess_le_phaseMass
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      SplitPhaseAccountedVariationStructuredHighExcessLocalData
        phases carryLocal hc0Small h_supportCount_pos) :
    let carryData :=
      carryLocal.toCarryData erdos260Constants_cPr_le_half
        hc0Small h_supportCount_pos
    highExcessMass
        (highExcessStarts carryData.starts (hitGap carryData.a)
          carryData.r carryData.T carryData.Y)
        (hitGap carryData.a) carryData.r carryData.T <=
      ClosurePhaseMass phases.toClosurePhaseData := by
  dsimp
  let carryData :=
    carryLocal.toCarryData erdos260Constants_cPr_le_half
      hc0Small h_supportCount_pos
  rw [carryData.highExcessMass_eq_branchWeightedMass]
  change groundedHighExcessBranchMass carryData <=
    ClosurePhaseMass phases.toClosurePhaseData
  exact data.branchMass_le_phaseMass

/-- Forget the explicit C1-VD split package to the previous phase-accounted data. -/
def splitPhaseAccountedToPhaseAccountedData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      SplitPhaseAccountedVariationStructuredHighExcessLocalData
        phases carryLocal hc0Small h_supportCount_pos) :
    PhaseAccountedVariationStructuredHighExcessLocalData
      phases carryLocal hc0Small h_supportCount_pos := {
  termMass := data.split.termMass
  accounting := data.accounting
  variation := data.variation
  hsplit := data.split.hsplit
  terminalAbsorption := data.terminalAbsorption }

/-- Explicit-split phase-accounted data gives central high-excess data. -/
def splitPhaseAccountedToHighExcessData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      SplitPhaseAccountedVariationStructuredHighExcessLocalData
        phases carryLocal hc0Small h_supportCount_pos) :
    HighExcessChargeData phases
      (carryLocal.toCarryData erdos260Constants_cPr_le_half
        hc0Small h_supportCount_pos) :=
  { highExcess_le_phaseMass := data.highExcess_le_phaseMass }

/--
N.24 local input package: the variation-drop certificate, the C1-VD/I.9 split,
and the table-routed terminal non-drop absorption used together in the final
N.24 phase accounting step.
-/
structure CarryHitGapN24TerminalVariationInputData
    {shell : FailingDyadicShell}
    (carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (h_supportCount_pos : 1 <= supportCount shell.d shell.X)
    (O_D O_P O_E O_CNL O_bdd O_V : Real) where
  variation :
    CarryHitGapVariationClassData carryLocal hc0Small h_supportCount_pos O_V
  split :
    GroundedC1VDSplitData carryLocal hc0Small h_supportCount_pos variation
  terminalAbsorption :
    TableRoutedDirectFiveClassTerminalAbsorptionData split.termMass
      O_D O_P O_E O_CNL O_bdd

/--
N.24 local input package with the C1-VD/I.9 split made canonical: terminal
mass is defined as `branchMass - VarDrop`, so the provider supplies only the
variation-drop certificate and the terminal absorption estimate for that
canonical remainder.
-/
structure CarryHitGapN24CanonicalSplitInputData
    {shell : FailingDyadicShell}
    (carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (h_supportCount_pos : 1 <= supportCount shell.d shell.X)
    (O_D O_P O_E O_CNL O_bdd O_V : Real) where
  variation :
    CarryHitGapVariationClassData carryLocal hc0Small h_supportCount_pos O_V
  terminalAbsorption :
    TableRoutedDirectFiveClassTerminalAbsorptionData
      (GroundedC1VDSplitData.ofVariation variation).termMass
      O_D O_P O_E O_CNL O_bdd

namespace CarryHitGapN24CanonicalSplitInputData

/-- The canonical C1-VD/I.9 split projected from the N.24 package. -/
def split
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_D O_P O_E O_CNL O_bdd O_V : Real}
    (data :
      CarryHitGapN24CanonicalSplitInputData carryLocal hc0Small
        h_supportCount_pos O_D O_P O_E O_CNL O_bdd O_V) :
    GroundedC1VDSplitData carryLocal hc0Small h_supportCount_pos
      data.variation :=
  GroundedC1VDSplitData.ofVariation data.variation

/-- Forget the canonical split choice to the older explicit-split N.24 input. -/
def toTerminalVariationInputData
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_D O_P O_E O_CNL O_bdd O_V : Real}
    (data :
      CarryHitGapN24CanonicalSplitInputData carryLocal hc0Small
        h_supportCount_pos O_D O_P O_E O_CNL O_bdd O_V) :
    CarryHitGapN24TerminalVariationInputData carryLocal hc0Small
      h_supportCount_pos O_D O_P O_E O_CNL O_bdd O_V where
  variation := data.variation
  split := data.split
  terminalAbsorption := data.terminalAbsorption

end CarryHitGapN24CanonicalSplitInputData

/--
N.24 local input package with both the active `Y` and the C1-VD/I.9 split
canonicalized.  The variation package uses `carryLocal.Y` directly, and the
terminal event-state decidability is projected classically rather than supplied
as provider data.
-/
structure CarryHitGapN24CanonicalYInputData
    {shell : FailingDyadicShell}
    (carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (h_supportCount_pos : 1 <= supportCount shell.d shell.X)
    (O_D O_P O_E O_CNL O_bdd O_V : Real) where
  variation :
    CarryHitGapCanonicalYVariationClassData carryLocal hc0Small
      h_supportCount_pos O_V
  terminalAbsorption :
    ClassicalTableRoutedDirectFiveClassTerminalAbsorptionData
      (GroundedC1VDSplitData.ofVariation
        variation.toVariationClassData).termMass
      O_D O_P O_E O_CNL O_bdd

namespace CarryHitGapN24CanonicalYInputData

/-- Assemble the canonical-`Y` N.24 local input from the closed N.2 variation
package and the N.3.3/N.24 terminal absorption package. -/
def ofClosedN2N3
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_D O_P O_E O_CNL O_bdd O_V : Real}
    (variation :
      CarryHitGapCanonicalYVariationClassData carryLocal hc0Small
        h_supportCount_pos O_V)
    (terminalAbsorption :
      ClassicalTableRoutedDirectFiveClassTerminalAbsorptionData
        (GroundedC1VDSplitData.ofVariation
          variation.toVariationClassData).termMass
        O_D O_P O_E O_CNL O_bdd) :
    CarryHitGapN24CanonicalYInputData carryLocal hc0Small
      h_supportCount_pos O_D O_P O_E O_CNL O_bdd O_V where
  variation := variation
  terminalAbsorption := terminalAbsorption

/-- Assemble the canonical-`Y` N.24 local input from the N.2 leaf and the fully
separated N.3.3 terminal leaf. -/
def ofClosedN2N3Leaves
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_D O_P O_E O_CNL O_bdd O_V : Real}
    (variation :
      CarryHitGapCanonicalYVariationLeafData carryLocal hc0Small
        h_supportCount_pos O_V)
    (terminalAbsorption :
      ClassicalTerminalN33SeparatedLeafData
        (GroundedC1VDSplitData.ofVariation
          variation.toVariationClassData.toVariationClassData).termMass
        O_D O_P O_E O_CNL O_bdd) :
    CarryHitGapN24CanonicalYInputData carryLocal hc0Small
      h_supportCount_pos O_D O_P O_E O_CNL O_bdd O_V :=
  CarryHitGapN24CanonicalYInputData.ofClosedN2N3
    variation.toVariationClassData
    terminalAbsorption.toClassicalTableRoutedDirectFiveClassTerminalAbsorptionData

/-- Project the canonical-`Y` variation package to the older variation shape. -/
def variationClass
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_D O_P O_E O_CNL O_bdd O_V : Real}
    (data :
      CarryHitGapN24CanonicalYInputData carryLocal hc0Small
        h_supportCount_pos O_D O_P O_E O_CNL O_bdd O_V) :
    CarryHitGapVariationClassData carryLocal hc0Small h_supportCount_pos O_V :=
  data.variation.toVariationClassData

/-- Forget the canonical `Y` choice to the canonical-split N.24 input. -/
def toCanonicalSplitInputData
    {shell : FailingDyadicShell}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    {O_D O_P O_E O_CNL O_bdd O_V : Real}
    (data :
      CarryHitGapN24CanonicalYInputData carryLocal hc0Small
        h_supportCount_pos O_D O_P O_E O_CNL O_bdd O_V) :
    CarryHitGapN24CanonicalSplitInputData carryLocal hc0Small
      h_supportCount_pos O_D O_P O_E O_CNL O_bdd O_V where
  variation := data.variationClass
  terminalAbsorption :=
    data.terminalAbsorption.toTableRoutedDirectFiveClassTerminalAbsorptionData

end CarryHitGapN24CanonicalYInputData

/--
The current split/phase-accounted high-excess package with N.1.0 terminal
outputs required in table-routed form.  This removes `hnonDrop` from the
provider surface: no-drop is obtained from the Appendix N routing table.
-/
structure TableRoutedSplitPhaseAccountedVariationStructuredHighExcessLocalData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    (phases : SixPhaseFactoryData cStar ξ (shell.X : Real))
    (carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (h_supportCount_pos : 1 <= supportCount shell.d shell.X) where
  accounting : PhaseClassAccountingData phases
  n24_input :
    CarryHitGapN24TerminalVariationInputData carryLocal hc0Small
      h_supportCount_pos accounting.O_D accounting.O_P accounting.O_E
      accounting.O_CNL accounting.O_bdd accounting.O_V


/-- Project the N.2 variation-drop package from the N.24 local input. -/
def TableRoutedSplitPhaseAccountedVariationStructuredHighExcessLocalData.variation
    {shell : FailingDyadicShell} {cStar xi : Real}
    {phases : SixPhaseFactoryData cStar xi (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      TableRoutedSplitPhaseAccountedVariationStructuredHighExcessLocalData
        phases carryLocal hc0Small h_supportCount_pos) :
    CarryHitGapVariationClassData carryLocal hc0Small h_supportCount_pos
      data.accounting.O_V :=
  data.n24_input.variation

/-- Project the C1-VD/I.9 split from the N.24 local input. -/
def TableRoutedSplitPhaseAccountedVariationStructuredHighExcessLocalData.split
    {shell : FailingDyadicShell} {cStar xi : Real}
    {phases : SixPhaseFactoryData cStar xi (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      TableRoutedSplitPhaseAccountedVariationStructuredHighExcessLocalData
        phases carryLocal hc0Small h_supportCount_pos) :
    GroundedC1VDSplitData carryLocal hc0Small h_supportCount_pos
      data.variation :=
  data.n24_input.split

/-- Project the table-routed N.3.3 terminal absorption package from the N.24 input. -/
def TableRoutedSplitPhaseAccountedVariationStructuredHighExcessLocalData.terminalAbsorption
    {shell : FailingDyadicShell} {cStar xi : Real}
    {phases : SixPhaseFactoryData cStar xi (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      TableRoutedSplitPhaseAccountedVariationStructuredHighExcessLocalData
        phases carryLocal hc0Small h_supportCount_pos) :
    TableRoutedDirectFiveClassTerminalAbsorptionData data.split.termMass
      data.accounting.O_D data.accounting.O_P data.accounting.O_E
      data.accounting.O_CNL data.accounting.O_bdd :=
  data.n24_input.terminalAbsorption

/-- The table-routed strongest local endpoint still uses the shell denominator
for the N.2.1 first-crossing record. -/
theorem TableRoutedSplitPhaseAccountedVariationStructuredHighExcessLocalData.recordDenominator_eq_shellQ
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      TableRoutedSplitPhaseAccountedVariationStructuredHighExcessLocalData
        phases carryLocal hc0Small h_supportCount_pos) :
    data.variation.recordDenominator = shell.Q :=
  data.variation.recordDenominator_eq_shellQ

/-- Forget table-routed terminal data to the older direct split package. -/
def tableRoutedSplitPhaseAccountedToSplitPhaseAccountedData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      TableRoutedSplitPhaseAccountedVariationStructuredHighExcessLocalData
        phases carryLocal hc0Small h_supportCount_pos) :
    SplitPhaseAccountedVariationStructuredHighExcessLocalData
      phases carryLocal hc0Small h_supportCount_pos := {
  accounting := data.accounting
  variation := data.variation
  split := data.split
  terminalAbsorption := data.terminalAbsorption.toDirect }

/-- Table-routed split high-excess data gives central high-excess data. -/
def tableRoutedSplitPhaseAccountedToHighExcessData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phases : SixPhaseFactoryData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      TableRoutedSplitPhaseAccountedVariationStructuredHighExcessLocalData
        phases carryLocal hc0Small h_supportCount_pos) :
    HighExcessChargeData phases
      (carryLocal.toCarryData erdos260Constants_cPr_le_half
        hc0Small h_supportCount_pos) :=
  splitPhaseAccountedToHighExcessData
    (tableRoutedSplitPhaseAccountedToSplitPhaseAccountedData data)

/-- Strongest pinned interface with N.24 aggregate absorption booked as one proof. -/
structure GlobalAssemblyCorePinnedN24BookedBundledWindowDropCarryYDenominatorShellI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs where
  carry :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
          shell erdos260Constants.cPr
  chernoff :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        GroundedChernoffLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  cnl :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        GroundedCNLLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  densePack :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        GroundedDensePackLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  tower :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        GroundedTowerLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  returnPkg :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        GroundedReturnLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  run :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        GroundedRunLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  highExcess :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (h_supportCount_pos : 1 <= supportCount shell.d shell.X)
      (phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real)),
        N24BookedBundledWindowDropCarryYDenominatorShellI9HighExcessLocalData phases
          (carry shell pin) pin.hc0Small h_supportCount_pos

/-- Assemble per-failure data from the pinned N.24-booked bundled-window-drop interface. -/
def GlobalAssemblyCorePinnedN24BookedBundledWindowDropCarryYDenominatorShellI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs.toGlobalPerFailureAssembly
    (data :
      GlobalAssemblyCorePinnedN24BookedBundledWindowDropCarryYDenominatorShellI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs) :
    GlobalPerFailureAssembly where
  constants := erdos260Constants
  startThreshold := by
    intro _Q d _hQ hd hnonterm _hrational
    exact firstPositiveSupportThreshold d hd hnonterm
  perFailureAssembly := by
    intro Q d hQ hd hnonterm hrational X hXdyadic hXge hfailure
    let shell :=
      FailingDyadicShell.ofGlobalConstants erdos260Constants Q d X
        hQ hd hnonterm hrational hXdyadic
        erdos260Constants.c0 erdos260Constants.c0_pos
        manuscriptC0_lt_kappa erdos260Constants.c0_le_cQ hfailure
    let pin : PinnedManuscriptShell shell := { hcQ := rfl, hc0 := rfl }
    have h_supportCount_pos : 1 <= supportCount shell.d shell.X := by
      exact supportCount_pos_of_firstPositiveSupportThreshold_le hd hnonterm hXge
    let carryLocal := data.carry shell pin
    let carryData :=
      carryLocal.toCarryData erdos260Constants_cPr_le_half
        pin.hc0Small h_supportCount_pos
    let phases : SixPhaseFactoryData erdos260Constants.cStar erdos260Constants.ξ
        (X : Real) := {
      chernoff := (data.chernoff shell pin).toChernoffPathData
      cnl := (data.cnl shell pin).toCNLClusterEncodingData
      tower := (data.tower shell pin).toTowerTransientFactoryData
      densePack := (data.densePack shell pin).toDensePackFactoryData
      returnPkg := (data.returnPkg shell pin).toReturnFactoryData
      run := (data.run shell pin).toRunFactoryData }
    exact
      PerFailureAssemblyData.ofHighExcessCharge phases carryData
        ((data.highExcess shell pin h_supportCount_pos phases).toHighExcessChargeData)

/-- Erdos 260 from the pinned N.24-booked current interface. -/
theorem erdos260_final_core_pinned_n24_booked_bundled_window_drop_carry_y_denominator_shell_i9_threshold_controlled_strict_failure_bounded_threshold_shell_grounded_current
    (data :
      GlobalAssemblyCorePinnedN24BookedBundledWindowDropCarryYDenominatorShellI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs) :
    Erdos260Statement :=
  erdos260Statement_of_globalPerFailureAssembly data.toGlobalPerFailureAssembly

/-- Proof-v4 Return--Run--Tower local package used by the same-threshold TRT
closure/compression step. -/
structure GroundedTRTLocalPackageInputData (cStar ξ X : Real) where
  tower : GroundedTowerLocalData cStar ξ X
  returnPkg : GroundedReturnLocalData cStar ξ X
  run : GroundedRunLocalData cStar ξ X

/-- Assemble the proof-v4 TRT local package from its Tower/Return/Run
subpackages. -/
def GroundedTRTLocalPackageInputData.ofClosedTowerReturnRun
    {cStar xi X : Real}
    (tower : GroundedTowerLocalData cStar xi X)
    (returnPkg : GroundedReturnLocalData cStar xi X)
    (run : GroundedRunLocalData cStar xi X) :
    GroundedTRTLocalPackageInputData cStar xi X where
  tower := tower
  returnPkg := returnPkg
  run := run

/-- Final L.3 tower bound projected from the proof-v4 TRT package. -/
theorem GroundedTRTLocalPackageInputData.tower_bound
    {cStar xi X : Real} (data : GroundedTRTLocalPackageInputData cStar xi X) :
    Finset.sum data.tower.entryExitSet (fun b => data.tower.chargedWeightReal b) <=
      cStar * xi * X / 6 :=
  data.tower.tower_bound

/-- Final Proposition 23.1 / I.5.1 return bound projected from the proof-v4
TRT package. -/
theorem GroundedTRTLocalPackageInputData.return_bound
    {cStar xi X : Real} (data : GroundedTRTLocalPackageInputData cStar xi X) :
    data.returnPkg.ordinaryShort + data.returnPkg.semiperiodic +
        data.returnPkg.olc + data.returnPkg.nonlocalLong <=
      cStar * xi * X / 6 :=
  data.returnPkg.nonRunReturn_bound

/-- Final Proposition I.5.2 run bound projected from the proof-v4 TRT package. -/
theorem GroundedTRTLocalPackageInputData.run_bound
    {cStar xi X : Real} (data : GroundedTRTLocalPackageInputData cStar xi X) :
    data.run.runMass <= cStar * xi * X / 6 :=
  data.run.run_bound

/-- Proof-v4 Appendix K/M local-geometry package.  This carries the remaining
DensePack support and dirty-multiplicity inputs as one local-geometry boundary.
The M.3 anchored patch placement is consumed explicitly by
`GroundedKMLocalGeometryInputData.anchoredPatch` rather than asserted for every
valid semiperiodic patch. -/
structure GroundedKMLocalGeometryInputData (cStar ξ X : Real) where
  densePack : GroundedDensePackLocalData cStar ξ X
  dirtyMultiplicity : DirtyMultiplicityData

/-- Assemble the proof-v4 K/M local-geometry package from DensePack support and
the K.2.5 dirty-multiplicity certificate. -/
def GroundedKMLocalGeometryInputData.ofClosedLocalGeometry
    {cStar xi X : Real}
    (densePack : GroundedDensePackLocalData cStar xi X)
    (dirtyMultiplicity : DirtyMultiplicityData) :
    GroundedKMLocalGeometryInputData cStar xi X where
  densePack := densePack
  dirtyMultiplicity := dirtyMultiplicity

/-- K.2.1 continuation in the degenerate closed priority form: choosing the
failure datum to be the target itself makes "target is earlier than failure"
impossible by irreflexivity of the finite anchored priority order. -/
def orientedSemiperiodicOverlapContinuation_self
    {w : Nat -> Nat} (B₁ B₂ : SemiperiodicBlock)
    (O : IntervalBlock) (Merged : Prop)
    (target : AnchoredFirstDirtyDatum) :
    OrientedSemiperiodicOverlapContinuationData (w := w)
      B₁ B₂ O Merged target where
  failure := target
  continuation := by
    intro _commonPeriod
    exact Or.inr (by simp [AnchoredFirstDirtyDatum.Earlier])

/-- Project the K.1 grounded DensePack phase from the K/M package. -/
def GroundedKMLocalGeometryInputData.densePackData
    {cStar ξ X : Real} (data : GroundedKMLocalGeometryInputData cStar ξ X) :
    GroundedDensePackLocalData cStar ξ X :=
  data.densePack

/-- Project the K.1 neighbourhood-cover statement from the K/M package. -/
theorem GroundedKMLocalGeometryInputData.cover
    {cStar ξ X : Real} (data : GroundedKMLocalGeometryInputData cStar ξ X) :
    forall x, x ∈ data.densePack.densePackPoints ->
      ∃ m, m ∈ data.densePack.markers.markers ∧
        Nat.dist x m <= data.densePack.spread :=
  data.densePack.cover

/-- Build the K.2.1 overlap alternative from the K/M continuation input. -/
def GroundedKMLocalGeometryInputData.orientedAlternative
    {cStar ξ X : Real} (_data : GroundedKMLocalGeometryInputData cStar ξ X)
    {w : Nat -> Nat} (B₁ B₂ : SemiperiodicBlock)
    (O : IntervalBlock) (Merged : Prop)
    (target : AnchoredFirstDirtyDatum) :
    OrientedSemiperiodicOverlapAlternativeData (w := w)
      B₁ B₂ O Merged target where
  continuation := orientedSemiperiodicOverlapContinuation_self
    B₁ B₂ O Merged target

/-- Project the K.2.5 dirty-multiplicity package from the K/M input. -/
def GroundedKMLocalGeometryInputData.dirtyMultiplicityData
    {cStar ξ X : Real} (data : GroundedKMLocalGeometryInputData cStar ξ X) :
    DirtyMultiplicityData :=
  data.dirtyMultiplicity

/-- Build an M.3 anchored surviving-patch certificate from explicit placement. -/
def GroundedKMLocalGeometryInputData.anchoredPatch
    {cStar ξ X : Real} (_data : GroundedKMLocalGeometryInputData cStar ξ X)
    {datum : AnchoredFirstDirtyDatum} {w : Nat -> Nat}
    {patch : SemiperiodicBlock} (hvalid : patch.Valid w)
    (placement : AnchoredCorePlacement datum patch.block) :
    AnchoredSemiperiodicPatch datum w patch where
  valid := hvalid
  corePlacement_input := AnchoredCorePlacement.contains placement

/-- The six-phase data before the Appendix N chain-compression package supplies
the Return--Run--Tower component. -/
structure GroundedPreTRTSixPhaseLocalData (cStar ξ X : Real) where
  chernoff : GroundedChernoffLocalData cStar ξ X
  cnl : GroundedCNLLocalData cStar ξ X
  km_input : GroundedKMLocalGeometryInputData cStar ξ X

/-- Assemble the proof-v4 pre-TRT phase core from Chernoff, CNL, and K/M local
geometry subpackages. -/
def GroundedPreTRTSixPhaseLocalData.ofClosedSubpackages
    {cStar xi X : Real}
    (chernoff : GroundedChernoffLocalData cStar xi X)
    (cnl : GroundedCNLLocalData cStar xi X)
    (km_input : GroundedKMLocalGeometryInputData cStar xi X) :
    GroundedPreTRTSixPhaseLocalData cStar xi X where
  chernoff := chernoff
  cnl := cnl
  km_input := km_input

/-- Assemble the proof-v4 pre-TRT phase core directly from the four explicit
Chernoff/CNL/DensePack/dirty-multiplicity subpackages. -/
def GroundedPreTRTSixPhaseLocalData.ofClosedLocalGeometry
    {cStar xi X : Real}
    (chernoff : GroundedChernoffLocalData cStar xi X)
    (cnl : GroundedCNLLocalData cStar xi X)
    (densePack : GroundedDensePackLocalData cStar xi X)
    (dirtyMultiplicity : DirtyMultiplicityData) :
    GroundedPreTRTSixPhaseLocalData cStar xi X :=
  GroundedPreTRTSixPhaseLocalData.ofClosedSubpackages chernoff cnl
    (GroundedKMLocalGeometryInputData.ofClosedLocalGeometry densePack dirtyMultiplicity)

/-- Project the DensePack phase from the pre-TRT K/M local-geometry package. -/
def GroundedPreTRTSixPhaseLocalData.densePack
    {cStar ξ X : Real} (data : GroundedPreTRTSixPhaseLocalData cStar ξ X) :
    GroundedDensePackLocalData cStar ξ X :=
  data.km_input.densePack

/-- Lemma 22.1 shell-Chernoff input projected directly from the pre-TRT core. -/
def GroundedPreTRTSixPhaseLocalData.chernoffInput
    {cStar xi X : Real} (data : GroundedPreTRTSixPhaseLocalData cStar xi X) :
    ChernoffShellBudgetData data.chernoff.paths data.chernoff.weightReal
      data.chernoff.cost (data.chernoff.z : Real) data.chernoff.root
      data.chernoff.A data.chernoff.B data.chernoff.m data.chernoff.Y
      cStar xi X := by
  simpa [GroundedChernoffLocalData.weightReal] using data.chernoff.chernoff_input

/-- Final Lemma 22.1 shell-Chernoff bound projected from the pre-TRT core. -/
theorem GroundedPreTRTSixPhaseLocalData.chernoff_bound
    {cStar xi X : Real} (data : GroundedPreTRTSixPhaseLocalData cStar xi X) :
    Exists fun Regular : Real =>
      And (0 <= Regular) (Regular <= cStar * xi * X / 6) :=
  data.chernoff.chernoff_bound

/-- The selected-transition weighted CNL input projected directly from the
pre-TRT core. -/
def GroundedPreTRTSixPhaseLocalData.cnlEncodingInput
    {cStar xi X : Real} (data : GroundedPreTRTSixPhaseLocalData cStar xi X) :
    GroundedCNLWeightedEncodingInput
      (selectedTransitions data.cnl.selector.transitions) data.cnl.BNDHeight
      (data.cnl.c : Real) (data.cnl.CQ : Real) (data.cnl.shellFactor : Real)
      X (data.cnl.Ij : Real) cStar xi data.cnl.M :=
  data.cnl.encoding_input

/-- Final G.6/L.1 selected-transition CNL entropy bound projected from the
pre-TRT core. -/
theorem GroundedPreTRTSixPhaseLocalData.cnl_bound
    {cStar xi X : Real} (data : GroundedPreTRTSixPhaseLocalData cStar xi X)
    (hX_nonneg : 0 <= X) :
    Exists fun CleanTerm : Real =>
      And (0 <= CleanTerm) (CleanTerm <= cStar * xi * X / 6) :=
  data.cnl.cnl_bound hX_nonneg

/-- K.1 DensePack smallness projected from the pre-TRT core. -/
theorem GroundedPreTRTSixPhaseLocalData.densePack_bound
    {cStar xi X : Real} (data : GroundedPreTRTSixPhaseLocalData cStar xi X) :
    (data.densePack.densePackPoints.card : Real) <= cStar * xi * X / 6 :=
  data.densePack.densePack_bound

/-- K.2.5 dirty-multiplicity package projected from the pre-TRT core. -/
def GroundedPreTRTSixPhaseLocalData.dirtyMultiplicityData
    {cStar xi X : Real} (data : GroundedPreTRTSixPhaseLocalData cStar xi X) :
    DirtyMultiplicityData :=
  data.km_input.dirtyMultiplicityData

/-- K.1 neighbourhood-cover statement projected from the pre-TRT core. -/
theorem GroundedPreTRTSixPhaseLocalData.cover
    {cStar xi X : Real} (data : GroundedPreTRTSixPhaseLocalData cStar xi X) :
    forall x, x ∈ data.densePack.densePackPoints ->
      ∃ m, m ∈ data.densePack.markers.markers ∧
        Nat.dist x m <= data.densePack.spread :=
  data.km_input.cover

/-- K.2.1 oriented overlap alternative projected from the pre-TRT core. -/
def GroundedPreTRTSixPhaseLocalData.orientedAlternative
    {cStar xi X : Real} (data : GroundedPreTRTSixPhaseLocalData cStar xi X)
    {w : Nat -> Nat} (B₁ B₂ : SemiperiodicBlock)
    (O : IntervalBlock) (Merged : Prop)
    (target : AnchoredFirstDirtyDatum) :
    OrientedSemiperiodicOverlapAlternativeData (w := w)
      B₁ B₂ O Merged target :=
  data.km_input.orientedAlternative B₁ B₂ O Merged target

/-- M.3 anchored surviving-patch certificate projected from the pre-TRT core
once explicit anchored placement is supplied. -/
def GroundedPreTRTSixPhaseLocalData.anchoredPatch
    {cStar xi X : Real} (data : GroundedPreTRTSixPhaseLocalData cStar xi X)
    {datum : AnchoredFirstDirtyDatum} {w : Nat -> Nat}
    {patch : SemiperiodicBlock} (hvalid : patch.Valid w)
    (placement : AnchoredCorePlacement datum patch.block) :
    AnchoredSemiperiodicPatch datum w patch :=
  data.km_input.anchoredPatch hvalid placement

/-- Proof-v4 phase package: the current grounded phase witnesses bundled as
the single factory object used by the closure bridge.  The TRT phases are carried
as one package, matching the Return--Run--Tower closure in proof-v4; K/M local
geometry is carried as one package before projecting DensePack. -/
structure GroundedSixPhaseLocalData (cStar ξ X : Real) where
  chernoff : GroundedChernoffLocalData cStar ξ X
  cnl : GroundedCNLLocalData cStar ξ X
  km_input : GroundedKMLocalGeometryInputData cStar ξ X
  trt_input : GroundedTRTLocalPackageInputData cStar ξ X

/-- Project the DensePack phase from the proof-v4 K/M local-geometry package. -/
def GroundedSixPhaseLocalData.densePack
    {cStar ξ X : Real} (data : GroundedSixPhaseLocalData cStar ξ X) :
    GroundedDensePackLocalData cStar ξ X :=
  data.km_input.densePack

/-- Project the Tower phase from the proof-v4 TRT local package. -/
def GroundedSixPhaseLocalData.tower
    {cStar ξ X : Real} (data : GroundedSixPhaseLocalData cStar ξ X) :
    GroundedTowerLocalData cStar ξ X :=
  data.trt_input.tower

/-- Project the Return phase from the proof-v4 TRT local package. -/
def GroundedSixPhaseLocalData.returnPkg
    {cStar ξ X : Real} (data : GroundedSixPhaseLocalData cStar ξ X) :
    GroundedReturnLocalData cStar ξ X :=
  data.trt_input.returnPkg

/-- Project the Run phase from the proof-v4 TRT local package. -/
def GroundedSixPhaseLocalData.run
    {cStar ξ X : Real} (data : GroundedSixPhaseLocalData cStar ξ X) :
    GroundedRunLocalData cStar ξ X :=
  data.trt_input.run

/-- Forget the Appendix N TRT completion and recover the pre-TRT phase core. -/
def GroundedSixPhaseLocalData.toPreTRT
    {cStar ξ X : Real} (data : GroundedSixPhaseLocalData cStar ξ X) :
    GroundedPreTRTSixPhaseLocalData cStar ξ X where
  chernoff := data.chernoff
  cnl := data.cnl
  km_input := data.km_input

/-- Complete pre-TRT phase data with the Appendix N chain-compression TRT
package. -/
def GroundedPreTRTSixPhaseLocalData.withTRT
    {cStar ξ X : Real} (data : GroundedPreTRTSixPhaseLocalData cStar ξ X)
    (trt : GroundedTRTLocalPackageInputData cStar ξ X) :
    GroundedSixPhaseLocalData cStar ξ X where
  chernoff := data.chernoff
  cnl := data.cnl
  km_input := data.km_input
  trt_input := trt

@[simp] theorem GroundedSixPhaseLocalData.toPreTRT_withTRT
    {cStar ξ X : Real} (data : GroundedSixPhaseLocalData cStar ξ X) :
    data.toPreTRT.withTRT data.trt_input = data := by
  cases data
  rfl

/-- Convert the bundled grounded six-phase package to the central factory data. -/
def GroundedSixPhaseLocalData.toSixPhaseFactoryData
    {cStar ξ X : Real} (data : GroundedSixPhaseLocalData cStar ξ X) :
    SixPhaseFactoryData cStar ξ X where
  chernoff := data.chernoff.toChernoffPathData
  cnl := data.cnl.toCNLClusterEncodingData
  tower := data.tower.toTowerTransientFactoryData
  densePack := data.densePack.toDensePackFactoryData
  returnPkg := data.returnPkg.toReturnFactoryData
  run := data.run.toRunFactoryData

/-- Proof-v4 Appendix N chain-compression package.  It supplies both the TRT
local successor package and the N.24 variation/terminal accounting package for
the same shell/carry/phase context. -/
structure AppendixNTRTChainCompressionInputData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    (phaseCore : GroundedPreTRTSixPhaseLocalData cStar ξ (shell.X : Real))
    (carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (h_supportCount_pos : 1 <= supportCount shell.d shell.X) where
  trt : GroundedTRTLocalPackageInputData cStar ξ (shell.X : Real)
  n24_input :
    CarryHitGapN24TerminalVariationInputData carryLocal hc0Small
      h_supportCount_pos
      (termDensePack ((phaseCore.withTRT trt).toSixPhaseFactoryData).toClosurePhaseData)
      (termChernoff ((phaseCore.withTRT trt).toSixPhaseFactoryData).toClosurePhaseData)
      (termReturn ((phaseCore.withTRT trt).toSixPhaseFactoryData).toClosurePhaseData)
      (termCnl ((phaseCore.withTRT trt).toSixPhaseFactoryData).toClosurePhaseData)
      (termTower ((phaseCore.withTRT trt).toSixPhaseFactoryData).toClosurePhaseData)
      (termRun ((phaseCore.withTRT trt).toSixPhaseFactoryData).toClosurePhaseData)

/-- The complete six-phase data projected from the Appendix N chain package. -/
def AppendixNTRTChainCompressionInputData.phases
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phaseCore : GroundedPreTRTSixPhaseLocalData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      AppendixNTRTChainCompressionInputData phaseCore carryLocal
        hc0Small h_supportCount_pos) :
    GroundedSixPhaseLocalData cStar ξ (shell.X : Real) :=
  phaseCore.withTRT data.trt

@[simp] theorem AppendixNTRTChainCompressionInputData.phases_toPreTRT
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phaseCore : GroundedPreTRTSixPhaseLocalData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      AppendixNTRTChainCompressionInputData phaseCore carryLocal
        hc0Small h_supportCount_pos) :
    data.phases.toPreTRT = phaseCore := by
  cases phaseCore
  rfl

@[simp] theorem AppendixNTRTChainCompressionInputData.phases_trt_input
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phaseCore : GroundedPreTRTSixPhaseLocalData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      AppendixNTRTChainCompressionInputData phaseCore carryLocal
        hc0Small h_supportCount_pos) :
    data.phases.trt_input = data.trt := by
  rfl

/-- Project the N.2 variation-drop package from the Appendix N
chain-compression boundary. -/
def AppendixNTRTChainCompressionInputData.variation
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phaseCore : GroundedPreTRTSixPhaseLocalData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      AppendixNTRTChainCompressionInputData phaseCore carryLocal
        hc0Small h_supportCount_pos) :
    CarryHitGapVariationClassData carryLocal hc0Small h_supportCount_pos
      (termRun data.phases.toSixPhaseFactoryData.toClosurePhaseData) :=
  data.n24_input.variation

/-- Project the C1-VD/I.9 split package from the Appendix N
chain-compression boundary. -/
def AppendixNTRTChainCompressionInputData.split
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phaseCore : GroundedPreTRTSixPhaseLocalData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      AppendixNTRTChainCompressionInputData phaseCore carryLocal
        hc0Small h_supportCount_pos) :
    GroundedC1VDSplitData carryLocal hc0Small h_supportCount_pos
      data.variation :=
  data.n24_input.split

/-- Project the table-routed N.3.3 terminal absorption package from the
Appendix N chain-compression boundary. -/
def AppendixNTRTChainCompressionInputData.terminalAbsorption
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phaseCore : GroundedPreTRTSixPhaseLocalData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      AppendixNTRTChainCompressionInputData phaseCore carryLocal
        hc0Small h_supportCount_pos) :
    TableRoutedDirectFiveClassTerminalAbsorptionData data.split.termMass
      (termDensePack data.phases.toSixPhaseFactoryData.toClosurePhaseData)
      (termChernoff data.phases.toSixPhaseFactoryData.toClosurePhaseData)
      (termReturn data.phases.toSixPhaseFactoryData.toClosurePhaseData)
      (termCnl data.phases.toSixPhaseFactoryData.toClosurePhaseData)
      (termTower data.phases.toSixPhaseFactoryData.toClosurePhaseData) :=
  data.n24_input.terminalAbsorption

/-- The class-to-phase accounting is definitional for the strongest Appendix N
package: each output class is booked directly against its target phase term. -/
def AppendixNTRTChainCompressionInputData.accounting
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phaseCore : GroundedPreTRTSixPhaseLocalData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      AppendixNTRTChainCompressionInputData phaseCore carryLocal
        hc0Small h_supportCount_pos) :
    PhaseClassAccountingData data.phases.toSixPhaseFactoryData where
  O_D := termDensePack data.phases.toSixPhaseFactoryData.toClosurePhaseData
  O_P := termChernoff data.phases.toSixPhaseFactoryData.toClosurePhaseData
  O_E := termReturn data.phases.toSixPhaseFactoryData.toClosurePhaseData
  O_CNL := termCnl data.phases.toSixPhaseFactoryData.toClosurePhaseData
  O_bdd := termTower data.phases.toSixPhaseFactoryData.toClosurePhaseData
  O_V := termRun data.phases.toSixPhaseFactoryData.toClosurePhaseData
  hD := le_rfl
  hP := le_rfl
  hE := le_rfl
  hCNL := le_rfl
  hbdd := le_rfl
  hV := le_rfl

/-- Convert the Appendix N chain-compression package to the table-routed
high-excess local data consumed by the current strongest closure bridge. -/
def AppendixNTRTChainCompressionInputData.toTableRoutedHighExcessData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phaseCore : GroundedPreTRTSixPhaseLocalData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      AppendixNTRTChainCompressionInputData phaseCore carryLocal
        hc0Small h_supportCount_pos) :
    TableRoutedSplitPhaseAccountedVariationStructuredHighExcessLocalData
      data.phases.toSixPhaseFactoryData carryLocal hc0Small h_supportCount_pos where
  accounting := data.accounting
  n24_input := data.n24_input

/--
Appendix N chain-compression package with the C1-VD/I.9 split canonicalized.
The provider supplies the TRT local package, the variation-drop package, and
terminal absorption for the canonical terminal remainder.
-/
structure AppendixNTRTChainCompressionCanonicalSplitInputData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    (phaseCore : GroundedPreTRTSixPhaseLocalData cStar ξ (shell.X : Real))
    (carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (h_supportCount_pos : 1 <= supportCount shell.d shell.X) where
  trt : GroundedTRTLocalPackageInputData cStar ξ (shell.X : Real)
  n24_input :
    CarryHitGapN24CanonicalSplitInputData carryLocal hc0Small
      h_supportCount_pos
      (termDensePack ((phaseCore.withTRT trt).toSixPhaseFactoryData).toClosurePhaseData)
      (termChernoff ((phaseCore.withTRT trt).toSixPhaseFactoryData).toClosurePhaseData)
      (termReturn ((phaseCore.withTRT trt).toSixPhaseFactoryData).toClosurePhaseData)
      (termCnl ((phaseCore.withTRT trt).toSixPhaseFactoryData).toClosurePhaseData)
      (termTower ((phaseCore.withTRT trt).toSixPhaseFactoryData).toClosurePhaseData)
      (termRun ((phaseCore.withTRT trt).toSixPhaseFactoryData).toClosurePhaseData)

/-- Forget the canonical split choice to the older explicit-split Appendix N
chain-compression package. -/
def AppendixNTRTChainCompressionCanonicalSplitInputData.toChainCompressionInputData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phaseCore : GroundedPreTRTSixPhaseLocalData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      AppendixNTRTChainCompressionCanonicalSplitInputData phaseCore carryLocal
        hc0Small h_supportCount_pos) :
    AppendixNTRTChainCompressionInputData phaseCore carryLocal
      hc0Small h_supportCount_pos where
  trt := data.trt
  n24_input := data.n24_input.toTerminalVariationInputData

/-- Complete six-phase data projected from the canonical-split chain package. -/
def AppendixNTRTChainCompressionCanonicalSplitInputData.phases
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phaseCore : GroundedPreTRTSixPhaseLocalData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      AppendixNTRTChainCompressionCanonicalSplitInputData phaseCore carryLocal
        hc0Small h_supportCount_pos) :
    GroundedSixPhaseLocalData cStar ξ (shell.X : Real) :=
  data.toChainCompressionInputData.phases

@[simp] theorem AppendixNTRTChainCompressionCanonicalSplitInputData.phases_toPreTRT
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phaseCore : GroundedPreTRTSixPhaseLocalData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      AppendixNTRTChainCompressionCanonicalSplitInputData phaseCore carryLocal
        hc0Small h_supportCount_pos) :
    data.phases.toPreTRT = phaseCore := by
  exact data.toChainCompressionInputData.phases_toPreTRT

@[simp] theorem AppendixNTRTChainCompressionCanonicalSplitInputData.phases_trt_input
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phaseCore : GroundedPreTRTSixPhaseLocalData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      AppendixNTRTChainCompressionCanonicalSplitInputData phaseCore carryLocal
        hc0Small h_supportCount_pos) :
    data.phases.trt_input = data.trt := by
  exact data.toChainCompressionInputData.phases_trt_input

/--
Appendix N chain-compression package with canonical carry `Y` and canonical
C1-VD/I.9 split.  The N.24 terminal event-state decidability is projected
internally by the canonical-Y terminal wrapper.
-/
structure AppendixNTRTChainCompressionCanonicalYInputData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    (phaseCore : GroundedPreTRTSixPhaseLocalData cStar ξ (shell.X : Real))
    (carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (h_supportCount_pos : 1 <= supportCount shell.d shell.X) where
  trt : GroundedTRTLocalPackageInputData cStar ξ (shell.X : Real)
  n24_input :
    CarryHitGapN24CanonicalYInputData carryLocal hc0Small
      h_supportCount_pos
      (termDensePack ((phaseCore.withTRT trt).toSixPhaseFactoryData).toClosurePhaseData)
      (termChernoff ((phaseCore.withTRT trt).toSixPhaseFactoryData).toClosurePhaseData)
      (termReturn ((phaseCore.withTRT trt).toSixPhaseFactoryData).toClosurePhaseData)
      (termCnl ((phaseCore.withTRT trt).toSixPhaseFactoryData).toClosurePhaseData)
      (termTower ((phaseCore.withTRT trt).toSixPhaseFactoryData).toClosurePhaseData)
      (termRun ((phaseCore.withTRT trt).toSixPhaseFactoryData).toClosurePhaseData)

/-- Assemble the canonical-`Y` Appendix N chain-compression package from the
TRT local package and the canonical N.24 variation/terminal package. -/
def AppendixNTRTChainCompressionCanonicalYInputData.ofClosedN24
    {shell : FailingDyadicShell} {cStar xi : Real}
    {phaseCore : GroundedPreTRTSixPhaseLocalData cStar xi (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (trt : GroundedTRTLocalPackageInputData cStar xi (shell.X : Real))
    (n24_input :
      CarryHitGapN24CanonicalYInputData carryLocal hc0Small
        h_supportCount_pos
        (termDensePack ((phaseCore.withTRT trt).toSixPhaseFactoryData).toClosurePhaseData)
        (termChernoff ((phaseCore.withTRT trt).toSixPhaseFactoryData).toClosurePhaseData)
        (termReturn ((phaseCore.withTRT trt).toSixPhaseFactoryData).toClosurePhaseData)
        (termCnl ((phaseCore.withTRT trt).toSixPhaseFactoryData).toClosurePhaseData)
        (termTower ((phaseCore.withTRT trt).toSixPhaseFactoryData).toClosurePhaseData)
        (termRun ((phaseCore.withTRT trt).toSixPhaseFactoryData).toClosurePhaseData)) :
    AppendixNTRTChainCompressionCanonicalYInputData phaseCore carryLocal
      hc0Small h_supportCount_pos where
  trt := trt
  n24_input := n24_input

/-- Assemble the canonical-`Y` Appendix N chain-compression package directly
from TRT, the N.2 variation package, and the N.3.3/N.24 terminal package. -/
def AppendixNTRTChainCompressionCanonicalYInputData.ofClosedTRTN2N3
    {shell : FailingDyadicShell} {cStar xi : Real}
    {phaseCore : GroundedPreTRTSixPhaseLocalData cStar xi (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (trt : GroundedTRTLocalPackageInputData cStar xi (shell.X : Real))
    (variation :
      CarryHitGapCanonicalYVariationClassData carryLocal hc0Small
        h_supportCount_pos
        (termRun ((phaseCore.withTRT trt).toSixPhaseFactoryData).toClosurePhaseData))
    (terminalAbsorption :
      ClassicalTableRoutedDirectFiveClassTerminalAbsorptionData
        (GroundedC1VDSplitData.ofVariation
          variation.toVariationClassData).termMass
        (termDensePack ((phaseCore.withTRT trt).toSixPhaseFactoryData).toClosurePhaseData)
        (termChernoff ((phaseCore.withTRT trt).toSixPhaseFactoryData).toClosurePhaseData)
        (termReturn ((phaseCore.withTRT trt).toSixPhaseFactoryData).toClosurePhaseData)
        (termCnl ((phaseCore.withTRT trt).toSixPhaseFactoryData).toClosurePhaseData)
        (termTower ((phaseCore.withTRT trt).toSixPhaseFactoryData).toClosurePhaseData)) :
    AppendixNTRTChainCompressionCanonicalYInputData phaseCore carryLocal
      hc0Small h_supportCount_pos :=
  AppendixNTRTChainCompressionCanonicalYInputData.ofClosedN24 trt
    (CarryHitGapN24CanonicalYInputData.ofClosedN2N3 variation terminalAbsorption)

/-- Assemble the canonical-`Y` Appendix N chain-compression package directly
from the TRT local package, the N.2 leaf, and the fully separated N.3.3 leaf. -/
def AppendixNTRTChainCompressionCanonicalYInputData.ofClosedTRTLeafN2N3
    {shell : FailingDyadicShell} {cStar xi : Real}
    {phaseCore : GroundedPreTRTSixPhaseLocalData cStar xi (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (trt : GroundedTRTLocalPackageInputData cStar xi (shell.X : Real))
    (variation :
      CarryHitGapCanonicalYVariationLeafData carryLocal hc0Small
        h_supportCount_pos
        (termRun ((phaseCore.withTRT trt).toSixPhaseFactoryData).toClosurePhaseData))
    (terminalAbsorption :
      ClassicalTerminalN33SeparatedLeafData
        (GroundedC1VDSplitData.ofVariation
          variation.toVariationClassData.toVariationClassData).termMass
        (termDensePack ((phaseCore.withTRT trt).toSixPhaseFactoryData).toClosurePhaseData)
        (termChernoff ((phaseCore.withTRT trt).toSixPhaseFactoryData).toClosurePhaseData)
        (termReturn ((phaseCore.withTRT trt).toSixPhaseFactoryData).toClosurePhaseData)
        (termCnl ((phaseCore.withTRT trt).toSixPhaseFactoryData).toClosurePhaseData)
        (termTower ((phaseCore.withTRT trt).toSixPhaseFactoryData).toClosurePhaseData)) :
    AppendixNTRTChainCompressionCanonicalYInputData phaseCore carryLocal
      hc0Small h_supportCount_pos :=
  AppendixNTRTChainCompressionCanonicalYInputData.ofClosedN24 trt
    (CarryHitGapN24CanonicalYInputData.ofClosedN2N3Leaves
      variation terminalAbsorption)

/-- Forget the canonical `Y` choice to the canonical-split Appendix N package. -/
def AppendixNTRTChainCompressionCanonicalYInputData.toCanonicalSplitInputData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phaseCore : GroundedPreTRTSixPhaseLocalData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      AppendixNTRTChainCompressionCanonicalYInputData phaseCore carryLocal
        hc0Small h_supportCount_pos) :
    AppendixNTRTChainCompressionCanonicalSplitInputData phaseCore carryLocal
      hc0Small h_supportCount_pos where
  trt := data.trt
  n24_input := data.n24_input.toCanonicalSplitInputData

/-- Forget the canonical `Y` and canonical split choices all the way to the
older explicit-split chain-compression package. -/
def AppendixNTRTChainCompressionCanonicalYInputData.toChainCompressionInputData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phaseCore : GroundedPreTRTSixPhaseLocalData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      AppendixNTRTChainCompressionCanonicalYInputData phaseCore carryLocal
        hc0Small h_supportCount_pos) :
    AppendixNTRTChainCompressionInputData phaseCore carryLocal
      hc0Small h_supportCount_pos :=
  data.toCanonicalSplitInputData.toChainCompressionInputData

/-- Complete six-phase data projected from the canonical-`Y` chain package. -/
def AppendixNTRTChainCompressionCanonicalYInputData.phases
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phaseCore : GroundedPreTRTSixPhaseLocalData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      AppendixNTRTChainCompressionCanonicalYInputData phaseCore carryLocal
        hc0Small h_supportCount_pos) :
    GroundedSixPhaseLocalData cStar ξ (shell.X : Real) :=
  data.toCanonicalSplitInputData.phases

@[simp] theorem AppendixNTRTChainCompressionCanonicalYInputData.phases_toPreTRT
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phaseCore : GroundedPreTRTSixPhaseLocalData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      AppendixNTRTChainCompressionCanonicalYInputData phaseCore carryLocal
        hc0Small h_supportCount_pos) :
    data.phases.toPreTRT = phaseCore := by
  exact data.toCanonicalSplitInputData.phases_toPreTRT

@[simp] theorem AppendixNTRTChainCompressionCanonicalYInputData.phases_trt_input
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phaseCore : GroundedPreTRTSixPhaseLocalData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      AppendixNTRTChainCompressionCanonicalYInputData phaseCore carryLocal
        hc0Small h_supportCount_pos) :
    data.phases.trt_input = data.trt := by
  exact data.toCanonicalSplitInputData.phases_trt_input

/-- Project the proof-v4 TRT local package from the canonical-`Y`
chain-compression boundary. -/
def AppendixNTRTChainCompressionCanonicalYInputData.trtInput
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phaseCore : GroundedPreTRTSixPhaseLocalData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      AppendixNTRTChainCompressionCanonicalYInputData phaseCore carryLocal
        hc0Small h_supportCount_pos) :
    GroundedTRTLocalPackageInputData cStar ξ (shell.X : Real) :=
  data.trt

/-- Project the canonical-`Y` N.24 variation/terminal package from the
canonical-`Y` chain-compression boundary. -/
def AppendixNTRTChainCompressionCanonicalYInputData.n24Input
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phaseCore : GroundedPreTRTSixPhaseLocalData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      AppendixNTRTChainCompressionCanonicalYInputData phaseCore carryLocal
        hc0Small h_supportCount_pos) :
    CarryHitGapN24CanonicalYInputData carryLocal hc0Small
      h_supportCount_pos
      (termDensePack ((phaseCore.withTRT data.trt).toSixPhaseFactoryData).toClosurePhaseData)
      (termChernoff ((phaseCore.withTRT data.trt).toSixPhaseFactoryData).toClosurePhaseData)
      (termReturn ((phaseCore.withTRT data.trt).toSixPhaseFactoryData).toClosurePhaseData)
      (termCnl ((phaseCore.withTRT data.trt).toSixPhaseFactoryData).toClosurePhaseData)
      (termTower ((phaseCore.withTRT data.trt).toSixPhaseFactoryData).toClosurePhaseData)
      (termRun ((phaseCore.withTRT data.trt).toSixPhaseFactoryData).toClosurePhaseData) :=
  data.n24_input

/-- Project the canonical-`Y` N.2 variation package from the chain-compression
boundary. -/
def AppendixNTRTChainCompressionCanonicalYInputData.canonicalVariation
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phaseCore : GroundedPreTRTSixPhaseLocalData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      AppendixNTRTChainCompressionCanonicalYInputData phaseCore carryLocal
        hc0Small h_supportCount_pos) :
    CarryHitGapCanonicalYVariationClassData carryLocal hc0Small
      h_supportCount_pos
      (termRun ((phaseCore.withTRT data.trt).toSixPhaseFactoryData).toClosurePhaseData) :=
  data.n24_input.variation

/-- Project the older variation-class shape from the canonical-`Y`
chain-compression boundary. -/
def AppendixNTRTChainCompressionCanonicalYInputData.variation
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phaseCore : GroundedPreTRTSixPhaseLocalData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      AppendixNTRTChainCompressionCanonicalYInputData phaseCore carryLocal
        hc0Small h_supportCount_pos) :
    CarryHitGapVariationClassData carryLocal hc0Small h_supportCount_pos
      (termRun ((phaseCore.withTRT data.trt).toSixPhaseFactoryData).toClosurePhaseData) :=
  data.n24_input.variationClass

/-- Project the canonical C1-VD/I.9 split induced by the canonical-`Y`
variation package. -/
def AppendixNTRTChainCompressionCanonicalYInputData.split
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phaseCore : GroundedPreTRTSixPhaseLocalData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      AppendixNTRTChainCompressionCanonicalYInputData phaseCore carryLocal
        hc0Small h_supportCount_pos) :
    GroundedC1VDSplitData carryLocal hc0Small h_supportCount_pos
      data.variation :=
  GroundedC1VDSplitData.ofVariation data.variation

/-- Project the table-routed N.3.3 terminal absorption package from the
canonical-`Y` chain-compression boundary. -/
def AppendixNTRTChainCompressionCanonicalYInputData.terminalAbsorption
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phaseCore : GroundedPreTRTSixPhaseLocalData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      AppendixNTRTChainCompressionCanonicalYInputData phaseCore carryLocal
        hc0Small h_supportCount_pos) :
    ClassicalTableRoutedDirectFiveClassTerminalAbsorptionData
      (GroundedC1VDSplitData.ofVariation data.n24_input.variation.toVariationClassData).termMass
      (termDensePack ((phaseCore.withTRT data.trt).toSixPhaseFactoryData).toClosurePhaseData)
      (termChernoff ((phaseCore.withTRT data.trt).toSixPhaseFactoryData).toClosurePhaseData)
      (termReturn ((phaseCore.withTRT data.trt).toSixPhaseFactoryData).toClosurePhaseData)
      (termCnl ((phaseCore.withTRT data.trt).toSixPhaseFactoryData).toClosurePhaseData)
      (termTower ((phaseCore.withTRT data.trt).toSixPhaseFactoryData).toClosurePhaseData) :=
  data.n24_input.terminalAbsorption

/-- Final L.3 tower bound projected from the canonical-`Y`
chain-compression boundary. -/
theorem AppendixNTRTChainCompressionCanonicalYInputData.tower_bound
    {shell : FailingDyadicShell} {cStar xi : Real}
    {phaseCore : GroundedPreTRTSixPhaseLocalData cStar xi (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      AppendixNTRTChainCompressionCanonicalYInputData phaseCore carryLocal
        hc0Small h_supportCount_pos) :
    Finset.sum data.trt.tower.entryExitSet
        (fun b => data.trt.tower.chargedWeightReal b) <=
      cStar * xi * (shell.X : Real) / 6 :=
  data.trt.tower_bound

/-- Final Proposition 23.1 / I.5.1 return bound projected from the
canonical-`Y` chain-compression boundary. -/
theorem AppendixNTRTChainCompressionCanonicalYInputData.return_bound
    {shell : FailingDyadicShell} {cStar xi : Real}
    {phaseCore : GroundedPreTRTSixPhaseLocalData cStar xi (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      AppendixNTRTChainCompressionCanonicalYInputData phaseCore carryLocal
        hc0Small h_supportCount_pos) :
    data.trt.returnPkg.ordinaryShort + data.trt.returnPkg.semiperiodic +
        data.trt.returnPkg.olc + data.trt.returnPkg.nonlocalLong <=
      cStar * xi * (shell.X : Real) / 6 :=
  data.trt.return_bound

/-- Final Proposition I.5.2 run bound projected from the canonical-`Y`
chain-compression boundary. -/
theorem AppendixNTRTChainCompressionCanonicalYInputData.run_bound
    {shell : FailingDyadicShell} {cStar xi : Real}
    {phaseCore : GroundedPreTRTSixPhaseLocalData cStar xi (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      AppendixNTRTChainCompressionCanonicalYInputData phaseCore carryLocal
        hc0Small h_supportCount_pos) :
    data.trt.run.runMass <= cStar * xi * (shell.X : Real) / 6 :=
  data.trt.run_bound

/-- The N.2/N.13 variation class bound projected from the canonical-`Y`
chain-compression boundary. -/
theorem AppendixNTRTChainCompressionCanonicalYInputData.varDrop_le_class
    {shell : FailingDyadicShell} {cStar xi : Real}
    {phaseCore : GroundedPreTRTSixPhaseLocalData cStar xi (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      AppendixNTRTChainCompressionCanonicalYInputData phaseCore carryLocal
        hc0Small h_supportCount_pos) :
    data.canonicalVariation.VarDrop <=
      termRun ((phaseCore.withTRT data.trt).toSixPhaseFactoryData).toClosurePhaseData :=
  data.canonicalVariation.varDrop_le_class

/-- The N.3.3/N.24 terminal five-class bound projected from the canonical-`Y`
chain-compression boundary. -/
theorem AppendixNTRTChainCompressionCanonicalYInputData.terminal_bound
    {shell : FailingDyadicShell} {cStar xi : Real}
    {phaseCore : GroundedPreTRTSixPhaseLocalData cStar xi (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      AppendixNTRTChainCompressionCanonicalYInputData phaseCore carryLocal
        hc0Small h_supportCount_pos) :
    (GroundedC1VDSplitData.ofVariation
        data.n24_input.variation.toVariationClassData).termMass <=
      termDensePack ((phaseCore.withTRT data.trt).toSixPhaseFactoryData).toClosurePhaseData +
        termChernoff ((phaseCore.withTRT data.trt).toSixPhaseFactoryData).toClosurePhaseData +
        termReturn ((phaseCore.withTRT data.trt).toSixPhaseFactoryData).toClosurePhaseData +
        termCnl ((phaseCore.withTRT data.trt).toSixPhaseFactoryData).toClosurePhaseData +
        termTower ((phaseCore.withTRT data.trt).toSixPhaseFactoryData).toClosurePhaseData :=
  data.n24_input.terminalAbsorption.termMass_le_classes

/-- Direct high-excess package projected from the canonical-`Y` Appendix N
chain-compression input. -/
def AppendixNTRTChainCompressionCanonicalYInputData.toTableRoutedHighExcessData
    {shell : FailingDyadicShell} {cStar ξ : Real}
    {phaseCore : GroundedPreTRTSixPhaseLocalData cStar ξ (shell.X : Real)}
    {carryLocal :
      ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        shell erdos260Constants.cPr}
    {hc0Small : shell.c0 <= manuscriptKappa / 16}
    {h_supportCount_pos : 1 <= supportCount shell.d shell.X}
    (data :
      AppendixNTRTChainCompressionCanonicalYInputData phaseCore carryLocal
        hc0Small h_supportCount_pos) :
    TableRoutedSplitPhaseAccountedVariationStructuredHighExcessLocalData
      data.phases.toSixPhaseFactoryData carryLocal hc0Small h_supportCount_pos := by
  simpa [AppendixNTRTChainCompressionCanonicalYInputData.phases,
    AppendixNTRTChainCompressionCanonicalYInputData.toChainCompressionInputData]
    using data.toChainCompressionInputData.toTableRoutedHighExcessData

/--
Strongest pinned interface with the six phase witnesses bundled before the
N.24 aggregate high-excess closure is supplied.
-/
structure GlobalAssemblyCorePinnedSixPhaseN24BookedBundledWindowDropCarryYDenominatorShellI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs where
  carry :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
          shell erdos260Constants.cPr
  phases :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        GroundedSixPhaseLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  highExcess :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (h_supportCount_pos : 1 <= supportCount shell.d shell.X),
        N24BookedBundledWindowDropCarryYDenominatorShellI9HighExcessLocalData
          ((phases shell pin).toSixPhaseFactoryData)
          (carry shell pin) pin.hc0Small h_supportCount_pos

/-- Assemble per-failure data from the pinned six-phase/N.24-booked interface. -/
def GlobalAssemblyCorePinnedSixPhaseN24BookedBundledWindowDropCarryYDenominatorShellI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs.toGlobalPerFailureAssembly
    (data :
      GlobalAssemblyCorePinnedSixPhaseN24BookedBundledWindowDropCarryYDenominatorShellI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs) :
    GlobalPerFailureAssembly where
  constants := erdos260Constants
  startThreshold := by
    intro _Q d _hQ hd hnonterm _hrational
    exact firstPositiveSupportThreshold d hd hnonterm
  perFailureAssembly := by
    intro Q d hQ hd hnonterm hrational X hXdyadic hXge hfailure
    let shell :=
      FailingDyadicShell.ofGlobalConstants erdos260Constants Q d X
        hQ hd hnonterm hrational hXdyadic
        erdos260Constants.c0 erdos260Constants.c0_pos
        manuscriptC0_lt_kappa erdos260Constants.c0_le_cQ hfailure
    let pin : PinnedManuscriptShell shell := { hcQ := rfl, hc0 := rfl }
    have h_supportCount_pos : 1 <= supportCount shell.d shell.X := by
      exact supportCount_pos_of_firstPositiveSupportThreshold_le hd hnonterm hXge
    let carryLocal := data.carry shell pin
    let carryData :=
      carryLocal.toCarryData erdos260Constants_cPr_le_half
        pin.hc0Small h_supportCount_pos
    let phases := (data.phases shell pin).toSixPhaseFactoryData
    exact
      PerFailureAssemblyData.ofHighExcessCharge phases carryData
        ((data.highExcess shell pin h_supportCount_pos).toHighExcessChargeData)

/-- Erdos 260 from the pinned six-phase/N.24-booked current interface. -/
theorem erdos260_final_core_pinned_six_phase_n24_booked_bundled_window_drop_carry_y_denominator_shell_i9_threshold_controlled_strict_failure_bounded_threshold_shell_grounded_current
    (data :
      GlobalAssemblyCorePinnedSixPhaseN24BookedBundledWindowDropCarryYDenominatorShellI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs) :
    Erdos260Statement :=
  erdos260Statement_of_globalPerFailureAssembly data.toGlobalPerFailureAssembly

/--
Strongest pinned interface whose high-excess field exposes the reduced
lower-label record data that generates the N.2.2 window-drop bundle.
-/
structure GlobalAssemblyCorePinnedSixPhaseLowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs where
  carry :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
          shell erdos260Constants.cPr
  phases :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        GroundedSixPhaseLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  highExcess :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (h_supportCount_pos : 1 <= supportCount shell.d shell.X),
        LowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9HighExcessLocalData
          ((phases shell pin).toSixPhaseFactoryData)
          (carry shell pin) pin.hc0Small h_supportCount_pos

/--
Assemble per-failure data from the pinned six-phase lower-label-record/N.24
interface.
-/
def GlobalAssemblyCorePinnedSixPhaseLowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs.toGlobalPerFailureAssembly
    (data :
      GlobalAssemblyCorePinnedSixPhaseLowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs) :
    GlobalPerFailureAssembly where
  constants := erdos260Constants
  startThreshold := by
    intro _Q d _hQ hd hnonterm _hrational
    exact firstPositiveSupportThreshold d hd hnonterm
  perFailureAssembly := by
    intro Q d hQ hd hnonterm hrational X hXdyadic hXge hfailure
    let shell :=
      FailingDyadicShell.ofGlobalConstants erdos260Constants Q d X
        hQ hd hnonterm hrational hXdyadic
        erdos260Constants.c0 erdos260Constants.c0_pos
        manuscriptC0_lt_kappa erdos260Constants.c0_le_cQ hfailure
    let pin : PinnedManuscriptShell shell := { hcQ := rfl, hc0 := rfl }
    have h_supportCount_pos : 1 <= supportCount shell.d shell.X := by
      exact supportCount_pos_of_firstPositiveSupportThreshold_le hd hnonterm hXge
    let carryLocal := data.carry shell pin
    let carryData :=
      carryLocal.toCarryData erdos260Constants_cPr_le_half
        pin.hc0Small h_supportCount_pos
    let phases := (data.phases shell pin).toSixPhaseFactoryData
    exact
      PerFailureAssemblyData.ofHighExcessCharge phases carryData
        ((data.highExcess shell pin h_supportCount_pos).toHighExcessChargeData)

/--
Erdos 260 from the pinned six-phase lower-label-record/N.24 current interface.
-/
theorem erdos260_final_core_pinned_six_phase_lower_label_record_n24_booked_bundled_window_drop_carry_y_denominator_shell_i9_threshold_controlled_strict_failure_bounded_threshold_shell_grounded_current
    (data :
      GlobalAssemblyCorePinnedSixPhaseLowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs) :
    Erdos260Statement :=
  erdos260Statement_of_globalPerFailureAssembly data.toGlobalPerFailureAssembly

/--
Strongest pinned interface whose high-excess field exposes the lower-label
record data and the explicit carry-hitGap N.13 window-variation bound.
-/
structure GlobalAssemblyCorePinnedSixPhaseCarryHitGapLowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs where
  carry :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
          shell erdos260Constants.cPr
  phases :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        GroundedSixPhaseLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  highExcess :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (h_supportCount_pos : 1 <= supportCount shell.d shell.X),
        CarryHitGapLowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9HighExcessLocalData
          ((phases shell pin).toSixPhaseFactoryData)
          (carry shell pin) pin.hc0Small h_supportCount_pos

/--
Assemble per-failure data from the pinned six-phase carry-hitGap
lower-label-record/N.24 interface.
-/
def GlobalAssemblyCorePinnedSixPhaseCarryHitGapLowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs.toGlobalPerFailureAssembly
    (data :
      GlobalAssemblyCorePinnedSixPhaseCarryHitGapLowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs) :
    GlobalPerFailureAssembly where
  constants := erdos260Constants
  startThreshold := by
    intro _Q d _hQ hd hnonterm _hrational
    exact firstPositiveSupportThreshold d hd hnonterm
  perFailureAssembly := by
    intro Q d hQ hd hnonterm hrational X hXdyadic hXge hfailure
    let shell :=
      FailingDyadicShell.ofGlobalConstants erdos260Constants Q d X
        hQ hd hnonterm hrational hXdyadic
        erdos260Constants.c0 erdos260Constants.c0_pos
        manuscriptC0_lt_kappa erdos260Constants.c0_le_cQ hfailure
    let pin : PinnedManuscriptShell shell := { hcQ := rfl, hc0 := rfl }
    have h_supportCount_pos : 1 <= supportCount shell.d shell.X := by
      exact supportCount_pos_of_firstPositiveSupportThreshold_le hd hnonterm hXge
    let carryLocal := data.carry shell pin
    let carryData :=
      carryLocal.toCarryData erdos260Constants_cPr_le_half
        pin.hc0Small h_supportCount_pos
    let phases := (data.phases shell pin).toSixPhaseFactoryData
    exact
      PerFailureAssemblyData.ofHighExcessCharge phases carryData
        ((data.highExcess shell pin h_supportCount_pos).toHighExcessChargeData)

/--
Erdos 260 from the pinned six-phase carry-hitGap lower-label-record/N.24
current interface.
-/
theorem erdos260_final_core_pinned_six_phase_carry_hit_gap_lower_label_record_n24_booked_bundled_window_drop_carry_y_denominator_shell_i9_threshold_controlled_strict_failure_bounded_threshold_shell_grounded_current
    (data :
      GlobalAssemblyCorePinnedSixPhaseCarryHitGapLowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs) :
    Erdos260Statement :=
  erdos260Statement_of_globalPerFailureAssembly data.toGlobalPerFailureAssembly

/--
Strongest pinned interface whose high-excess field exposes N.24 in the
six-class phase-mass form.
-/
structure GlobalAssemblyCorePinnedSixPhasePhaseMassCarryHitGapLowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs where
  carry :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
          shell erdos260Constants.cPr
  phases :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        GroundedSixPhaseLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  highExcess :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (h_supportCount_pos : 1 <= supportCount shell.d shell.X),
        PhaseMassCarryHitGapLowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9HighExcessLocalData
          ((phases shell pin).toSixPhaseFactoryData)
          (carry shell pin) pin.hc0Small h_supportCount_pos

/--
Assemble per-failure data from the pinned six-phase phase-mass/carry-hitGap
lower-label-record/N.24 interface.
-/
def GlobalAssemblyCorePinnedSixPhasePhaseMassCarryHitGapLowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs.toGlobalPerFailureAssembly
    (data :
      GlobalAssemblyCorePinnedSixPhasePhaseMassCarryHitGapLowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs) :
    GlobalPerFailureAssembly where
  constants := erdos260Constants
  startThreshold := by
    intro _Q d _hQ hd hnonterm _hrational
    exact firstPositiveSupportThreshold d hd hnonterm
  perFailureAssembly := by
    intro Q d hQ hd hnonterm hrational X hXdyadic hXge hfailure
    let shell :=
      FailingDyadicShell.ofGlobalConstants erdos260Constants Q d X
        hQ hd hnonterm hrational hXdyadic
        erdos260Constants.c0 erdos260Constants.c0_pos
        manuscriptC0_lt_kappa erdos260Constants.c0_le_cQ hfailure
    let pin : PinnedManuscriptShell shell := { hcQ := rfl, hc0 := rfl }
    have h_supportCount_pos : 1 <= supportCount shell.d shell.X := by
      exact supportCount_pos_of_firstPositiveSupportThreshold_le hd hnonterm hXge
    let carryLocal := data.carry shell pin
    let carryData :=
      carryLocal.toCarryData erdos260Constants_cPr_le_half
        pin.hc0Small h_supportCount_pos
    let phases := (data.phases shell pin).toSixPhaseFactoryData
    exact
      PerFailureAssemblyData.ofHighExcessCharge phases carryData
        ((data.highExcess shell pin h_supportCount_pos).toHighExcessChargeData)

/--
Erdos 260 from the pinned six-phase phase-mass/carry-hitGap
lower-label-record/N.24 current interface.
-/
theorem erdos260_final_core_pinned_six_phase_phase_mass_carry_hit_gap_lower_label_record_n24_booked_bundled_window_drop_carry_y_denominator_shell_i9_threshold_controlled_strict_failure_bounded_threshold_shell_grounded_current
    (data :
      GlobalAssemblyCorePinnedSixPhasePhaseMassCarryHitGapLowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs) :
    Erdos260Statement :=
  erdos260Statement_of_globalPerFailureAssembly data.toGlobalPerFailureAssembly

/--
Strongest pinned interface whose high-excess field exposes the N.3.3 terminal
aggregate absorption data before the N.24 phase-mass accounting.
-/
structure GlobalAssemblyCorePinnedSixPhaseTerminalAggregatePhaseMassCarryHitGapLowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs where
  carry :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
          shell erdos260Constants.cPr
  phases :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        GroundedSixPhaseLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  highExcess :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (h_supportCount_pos : 1 <= supportCount shell.d shell.X),
        TerminalAggregatePhaseMassCarryHitGapLowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9HighExcessLocalData
          ((phases shell pin).toSixPhaseFactoryData)
          (carry shell pin) pin.hc0Small h_supportCount_pos

/--
Assemble per-failure data from the pinned six-phase terminal-aggregate
phase-mass/carry-hitGap lower-label-record/N.24 interface.
-/
def GlobalAssemblyCorePinnedSixPhaseTerminalAggregatePhaseMassCarryHitGapLowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs.toGlobalPerFailureAssembly
    (data :
      GlobalAssemblyCorePinnedSixPhaseTerminalAggregatePhaseMassCarryHitGapLowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs) :
    GlobalPerFailureAssembly where
  constants := erdos260Constants
  startThreshold := by
    intro _Q d _hQ hd hnonterm _hrational
    exact firstPositiveSupportThreshold d hd hnonterm
  perFailureAssembly := by
    intro Q d hQ hd hnonterm hrational X hXdyadic hXge hfailure
    let shell :=
      FailingDyadicShell.ofGlobalConstants erdos260Constants Q d X
        hQ hd hnonterm hrational hXdyadic
        erdos260Constants.c0 erdos260Constants.c0_pos
        manuscriptC0_lt_kappa erdos260Constants.c0_le_cQ hfailure
    let pin : PinnedManuscriptShell shell := { hcQ := rfl, hc0 := rfl }
    have h_supportCount_pos : 1 <= supportCount shell.d shell.X := by
      exact supportCount_pos_of_firstPositiveSupportThreshold_le hd hnonterm hXge
    let carryLocal := data.carry shell pin
    let carryData :=
      carryLocal.toCarryData erdos260Constants_cPr_le_half
        pin.hc0Small h_supportCount_pos
    let phases := (data.phases shell pin).toSixPhaseFactoryData
    exact
      PerFailureAssemblyData.ofHighExcessCharge phases carryData
        ((data.highExcess shell pin h_supportCount_pos).toHighExcessChargeData)

/--
Erdos 260 from the pinned six-phase terminal-aggregate phase-mass/carry-hitGap
lower-label-record/N.24 current interface.
-/
theorem erdos260_final_core_pinned_six_phase_terminal_aggregate_phase_mass_carry_hit_gap_lower_label_record_n24_booked_bundled_window_drop_carry_y_denominator_shell_i9_threshold_controlled_strict_failure_bounded_threshold_shell_grounded_current
    (data :
      GlobalAssemblyCorePinnedSixPhaseTerminalAggregatePhaseMassCarryHitGapLowerLabelRecordN24BookedBundledWindowDropCarryYDenominatorShellI9ThresholdControlledStrictFailureBoundedThresholdShellGroundedCurrentInputs) :
    Erdos260Statement :=
  erdos260Statement_of_globalPerFailureAssembly data.toGlobalPerFailureAssembly

/--
Strongest pinned interface whose high-excess field exposes the terminal
aggregate absorption step with its absorbed bound split into the five N.24
classes.
-/
structure GlobalFiveClassTerminalAggregateCurrentInputs where
  carry :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
          shell erdos260Constants.cPr
  phases :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        GroundedSixPhaseLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  highExcess :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (h_supportCount_pos : 1 <= supportCount shell.d shell.X),
        FiveClassTerminalAggregateHighExcessLocalData
          ((phases shell pin).toSixPhaseFactoryData)
          (carry shell pin) pin.hc0Small h_supportCount_pos

/--
Assemble per-failure data from the pinned six-phase five-class
terminal-aggregate phase-mass/carry-hitGap lower-label-record/N.24 interface.
-/
def fiveClassGlobalToAssembly
    (data : GlobalFiveClassTerminalAggregateCurrentInputs) :
    GlobalPerFailureAssembly where
  constants := erdos260Constants
  startThreshold := by
    intro _Q d _hQ hd hnonterm _hrational
    exact firstPositiveSupportThreshold d hd hnonterm
  perFailureAssembly := by
    intro Q d hQ hd hnonterm hrational X hXdyadic hXge hfailure
    let shell :=
      FailingDyadicShell.ofGlobalConstants erdos260Constants Q d X
        hQ hd hnonterm hrational hXdyadic
        erdos260Constants.c0 erdos260Constants.c0_pos
        manuscriptC0_lt_kappa erdos260Constants.c0_le_cQ hfailure
    let pin : PinnedManuscriptShell shell := { hcQ := rfl, hc0 := rfl }
    have h_supportCount_pos : 1 <= supportCount shell.d shell.X := by
      exact supportCount_pos_of_firstPositiveSupportThreshold_le hd hnonterm hXge
    let carryLocal := data.carry shell pin
    let carryData :=
      carryLocal.toCarryData erdos260Constants_cPr_le_half
        pin.hc0Small h_supportCount_pos
    let phases := (data.phases shell pin).toSixPhaseFactoryData
    exact
      PerFailureAssemblyData.ofHighExcessCharge phases carryData
        (fiveClassToHighExcessData
          (data.highExcess shell pin h_supportCount_pos))

/--
Erdos 260 from the pinned six-phase five-class terminal-aggregate
phase-mass/carry-hitGap lower-label-record/N.24 current interface.
-/
theorem erdos260_final_core_pinned_six_phase_five_class_terminal_aggregate_phase_mass_carry_hit_gap_lower_label_record_n24_booked_bundled_window_drop_carry_y_denominator_shell_i9_threshold_controlled_strict_failure_bounded_threshold_shell_grounded_current
    (data : GlobalFiveClassTerminalAggregateCurrentInputs) :
    Erdos260Statement :=
  erdos260Statement_of_globalPerFailureAssembly
    (fiveClassGlobalToAssembly data)

/--
Strongest pinned interface whose high-excess field uses the direct
five-class N.3.3/N.24 terminal absorption package.
-/
structure GlobalDirectFiveClassTerminalAggregateCurrentInputs where
  carry :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
          shell erdos260Constants.cPr
  phases :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        GroundedSixPhaseLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  highExcess :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (h_supportCount_pos : 1 <= supportCount shell.d shell.X),
        DirectFiveClassTerminalAggregateHighExcessLocalData
          ((phases shell pin).toSixPhaseFactoryData)
          (carry shell pin) pin.hc0Small h_supportCount_pos

/--
Assemble per-failure data from the pinned six-phase direct five-class
terminal-aggregate phase-mass/carry-hitGap lower-label-record/N.24 interface.
-/
def directFiveClassCurrentToAssembly
    (data : GlobalDirectFiveClassTerminalAggregateCurrentInputs) :
    GlobalPerFailureAssembly where
  constants := erdos260Constants
  startThreshold := by
    intro _Q d _hQ hd hnonterm _hrational
    exact firstPositiveSupportThreshold d hd hnonterm
  perFailureAssembly := by
    intro Q d hQ hd hnonterm hrational X hXdyadic hXge hfailure
    let shell :=
      FailingDyadicShell.ofGlobalConstants erdos260Constants Q d X
        hQ hd hnonterm hrational hXdyadic
        erdos260Constants.c0 erdos260Constants.c0_pos
        manuscriptC0_lt_kappa erdos260Constants.c0_le_cQ hfailure
    let pin : PinnedManuscriptShell shell := { hcQ := rfl, hc0 := rfl }
    have h_supportCount_pos : 1 <= supportCount shell.d shell.X := by
      exact supportCount_pos_of_firstPositiveSupportThreshold_le hd hnonterm hXge
    let carryLocal := data.carry shell pin
    let carryData :=
      carryLocal.toCarryData erdos260Constants_cPr_le_half
        pin.hc0Small h_supportCount_pos
    let phases := (data.phases shell pin).toSixPhaseFactoryData
    exact
      PerFailureAssemblyData.ofHighExcessCharge phases carryData
        (directFiveClassToHighExcessData
          (data.highExcess shell pin h_supportCount_pos))

/--
Erdos 260 from the pinned six-phase direct five-class terminal-aggregate
phase-mass/carry-hitGap lower-label-record/N.24 current interface.
-/
theorem erdos260_final_core_pinned_six_phase_direct_five_class_terminal_aggregate_phase_mass_carry_hit_gap_lower_label_record_n24_booked_bundled_window_drop_carry_y_denominator_shell_i9_threshold_controlled_strict_failure_bounded_threshold_shell_grounded_current
    (data : GlobalDirectFiveClassTerminalAggregateCurrentInputs) :
    Erdos260Statement :=
  erdos260Statement_of_globalPerFailureAssembly
    (directFiveClassCurrentToAssembly data)

/--
Strongest pinned interface whose high-excess field separates the proof-v4
N.2/N.13 variation-class package from the direct N.3.3/N.24 terminal package.
-/
structure GlobalVariationStructuredDirectCurrentInputs where
  carry :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
          shell erdos260Constants.cPr
  phases :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        GroundedSixPhaseLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  highExcess :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (h_supportCount_pos : 1 <= supportCount shell.d shell.X),
        VariationStructuredDirectFiveClassHighExcessLocalData
          ((phases shell pin).toSixPhaseFactoryData)
          (carry shell pin) pin.hc0Small h_supportCount_pos

/--
Assemble per-failure data from the pinned six-phase endpoint whose high-excess
side is structured into variation and direct terminal absorption packages.
-/
def variationStructuredDirectCurrentToAssembly
    (data : GlobalVariationStructuredDirectCurrentInputs) :
    GlobalPerFailureAssembly where
  constants := erdos260Constants
  startThreshold := by
    intro _Q d _hQ hd hnonterm _hrational
    exact firstPositiveSupportThreshold d hd hnonterm
  perFailureAssembly := by
    intro Q d hQ hd hnonterm hrational X hXdyadic hXge hfailure
    let shell :=
      FailingDyadicShell.ofGlobalConstants erdos260Constants Q d X
        hQ hd hnonterm hrational hXdyadic
        erdos260Constants.c0 erdos260Constants.c0_pos
        manuscriptC0_lt_kappa erdos260Constants.c0_le_cQ hfailure
    let pin : PinnedManuscriptShell shell := { hcQ := rfl, hc0 := rfl }
    have h_supportCount_pos : 1 <= supportCount shell.d shell.X := by
      exact supportCount_pos_of_firstPositiveSupportThreshold_le hd hnonterm hXge
    let carryLocal := data.carry shell pin
    let carryData :=
      carryLocal.toCarryData erdos260Constants_cPr_le_half
        pin.hc0Small h_supportCount_pos
    let phases := (data.phases shell pin).toSixPhaseFactoryData
    exact
      PerFailureAssemblyData.ofHighExcessCharge phases carryData
        (variationStructuredDirectToHighExcessData
          (data.highExcess shell pin h_supportCount_pos))

/--
Erdos 260 from the pinned six-phase variation-structured direct five-class
terminal-aggregate current interface.
-/
theorem erdos260_final_core_pinned_six_phase_variation_structured_direct_five_class_terminal_aggregate_phase_mass_carry_hit_gap_lower_label_record_n24_booked_bundled_window_drop_carry_y_denominator_shell_i9_threshold_controlled_strict_failure_bounded_threshold_shell_grounded_current
    (data : GlobalVariationStructuredDirectCurrentInputs) :
    Erdos260Statement :=
  erdos260Statement_of_globalPerFailureAssembly
    (variationStructuredDirectCurrentToAssembly data)

/--
Strongest pinned interface whose high-excess field separates N.24 phase-class
accounting from the N.2 variation package and direct terminal absorption.
-/
structure GlobalPhaseAccountedCurrentInputs where
  carry :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
          shell erdos260Constants.cPr
  phases :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        GroundedSixPhaseLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  highExcess :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (h_supportCount_pos : 1 <= supportCount shell.d shell.X),
        PhaseAccountedVariationStructuredHighExcessLocalData
          ((phases shell pin).toSixPhaseFactoryData)
          (carry shell pin) pin.hc0Small h_supportCount_pos

/-- Assemble per-failure data from the phase-accounted strongest interface. -/
def phaseAccountedCurrentToAssembly
    (data : GlobalPhaseAccountedCurrentInputs) :
    GlobalPerFailureAssembly where
  constants := erdos260Constants
  startThreshold := by
    intro _Q d _hQ hd hnonterm _hrational
    exact firstPositiveSupportThreshold d hd hnonterm
  perFailureAssembly := by
    intro Q d hQ hd hnonterm hrational X hXdyadic hXge hfailure
    let shell :=
      FailingDyadicShell.ofGlobalConstants erdos260Constants Q d X
        hQ hd hnonterm hrational hXdyadic
        erdos260Constants.c0 erdos260Constants.c0_pos
        manuscriptC0_lt_kappa erdos260Constants.c0_le_cQ hfailure
    let pin : PinnedManuscriptShell shell := { hcQ := rfl, hc0 := rfl }
    have h_supportCount_pos : 1 <= supportCount shell.d shell.X := by
      exact supportCount_pos_of_firstPositiveSupportThreshold_le hd hnonterm hXge
    let carryLocal := data.carry shell pin
    let carryData :=
      carryLocal.toCarryData erdos260Constants_cPr_le_half
        pin.hc0Small h_supportCount_pos
    let phases := (data.phases shell pin).toSixPhaseFactoryData
    exact
      PerFailureAssemblyData.ofHighExcessCharge phases carryData
        (phaseAccountedToHighExcessData
          (data.highExcess shell pin h_supportCount_pos))

/--
Erdos 260 from the pinned six-phase phase-accounted variation-structured
direct five-class terminal-aggregate current interface.
-/
theorem erdos260_final_core_pinned_six_phase_phase_accounted_variation_structured_direct_five_class_terminal_aggregate_phase_mass_carry_hit_gap_lower_label_record_n24_booked_bundled_window_drop_carry_y_denominator_shell_i9_threshold_controlled_strict_failure_bounded_threshold_shell_grounded_current
    (data : GlobalPhaseAccountedCurrentInputs) :
    Erdos260Statement :=
  erdos260Statement_of_globalPerFailureAssembly
    (phaseAccountedCurrentToAssembly data)

/--
Strongest pinned interface whose high-excess field also packages the C1-VD/I.9
branch-mass split as a separate local proof object.
-/
structure GlobalSplitPhaseAccountedCurrentInputs where
  carry :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
          shell erdos260Constants.cPr
  phases :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        GroundedSixPhaseLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  highExcess :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (h_supportCount_pos : 1 <= supportCount shell.d shell.X),
        SplitPhaseAccountedVariationStructuredHighExcessLocalData
          ((phases shell pin).toSixPhaseFactoryData)
          (carry shell pin) pin.hc0Small h_supportCount_pos

/-- Assemble per-failure data from the explicit-split phase-accounted interface. -/
def splitPhaseAccountedCurrentToAssembly
    (data : GlobalSplitPhaseAccountedCurrentInputs) :
    GlobalPerFailureAssembly where
  constants := erdos260Constants
  startThreshold := by
    intro _Q d _hQ hd hnonterm _hrational
    exact firstPositiveSupportThreshold d hd hnonterm
  perFailureAssembly := by
    intro Q d hQ hd hnonterm hrational X hXdyadic hXge hfailure
    let shell :=
      FailingDyadicShell.ofGlobalConstants erdos260Constants Q d X
        hQ hd hnonterm hrational hXdyadic
        erdos260Constants.c0 erdos260Constants.c0_pos
        manuscriptC0_lt_kappa erdos260Constants.c0_le_cQ hfailure
    let pin : PinnedManuscriptShell shell := { hcQ := rfl, hc0 := rfl }
    have h_supportCount_pos : 1 <= supportCount shell.d shell.X := by
      exact supportCount_pos_of_firstPositiveSupportThreshold_le hd hnonterm hXge
    let carryLocal := data.carry shell pin
    let carryData :=
      carryLocal.toCarryData erdos260Constants_cPr_le_half
        pin.hc0Small h_supportCount_pos
    let phases := (data.phases shell pin).toSixPhaseFactoryData
    exact
      PerFailureAssemblyData.ofHighExcessCharge phases carryData
        (splitPhaseAccountedToHighExcessData
          (data.highExcess shell pin h_supportCount_pos))

/--
Erdos 260 from the pinned six-phase explicit-C1-VD-split phase-accounted
variation-structured direct five-class terminal-aggregate current interface.
-/
theorem erdos260_final_core_pinned_six_phase_c1_vd_split_phase_accounted_variation_structured_direct_five_class_terminal_aggregate_phase_mass_carry_hit_gap_lower_label_record_n24_booked_bundled_window_drop_carry_y_denominator_shell_i9_threshold_controlled_strict_failure_bounded_threshold_shell_grounded_current
    (data : GlobalSplitPhaseAccountedCurrentInputs) :
    Erdos260Statement :=
  erdos260Statement_of_globalPerFailureAssembly
    (splitPhaseAccountedCurrentToAssembly data)

/--
Strongest current endpoint with the terminal N.1.0/N.5e package in
table-routed form.
-/
structure GlobalTableRoutedSplitPhaseAccountedCurrentInputs where
  carry :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
          shell erdos260Constants.cPr
  phases :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        GroundedSixPhaseLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  highExcess :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (h_supportCount_pos : 1 <= supportCount shell.d shell.X),
        TableRoutedSplitPhaseAccountedVariationStructuredHighExcessLocalData
          ((phases shell pin).toSixPhaseFactoryData)
          (carry shell pin) pin.hc0Small h_supportCount_pos

/-- Assemble per-failure data from the table-routed explicit-split endpoint. -/
def tableRoutedSplitPhaseAccountedCurrentToAssembly
    (data : GlobalTableRoutedSplitPhaseAccountedCurrentInputs) :
    GlobalPerFailureAssembly where
  constants := erdos260Constants
  startThreshold := by
    intro _Q d _hQ hd hnonterm _hrational
    exact firstPositiveSupportThreshold d hd hnonterm
  perFailureAssembly := by
    intro Q d hQ hd hnonterm hrational X hXdyadic hXge hfailure
    let shell :=
      FailingDyadicShell.ofGlobalConstants erdos260Constants Q d X
        hQ hd hnonterm hrational hXdyadic
        erdos260Constants.c0 erdos260Constants.c0_pos
        manuscriptC0_lt_kappa erdos260Constants.c0_le_cQ hfailure
    let pin : PinnedManuscriptShell shell := { hcQ := rfl, hc0 := rfl }
    have h_supportCount_pos : 1 <= supportCount shell.d shell.X := by
      exact supportCount_pos_of_firstPositiveSupportThreshold_le hd hnonterm hXge
    let carryLocal := data.carry shell pin
    let carryData :=
      carryLocal.toCarryData erdos260Constants_cPr_le_half
        pin.hc0Small h_supportCount_pos
    let phases := (data.phases shell pin).toSixPhaseFactoryData
    exact
      PerFailureAssemblyData.ofHighExcessCharge phases carryData
        (tableRoutedSplitPhaseAccountedToHighExcessData
          (data.highExcess shell pin h_supportCount_pos))

/--
Erdos 260 from the table-routed explicit-C1-VD-split phase-accounted endpoint.
-/
theorem erdos260_final_core_pinned_six_phase_table_routed_c1_vd_split_phase_accounted_variation_structured_direct_five_class_terminal_aggregate_current
    (data : GlobalTableRoutedSplitPhaseAccountedCurrentInputs) :
    Erdos260Statement :=
  erdos260Statement_of_globalPerFailureAssembly
    (tableRoutedSplitPhaseAccountedCurrentToAssembly data)

/--
Strongest current endpoint with the proof-v4 Appendix N chain-compression
package supplying both the TRT local package and the N.24 variation/terminal
package.
-/
structure GlobalAppendixNChainCompressionCurrentInputs where
  carry :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
          shell erdos260Constants.cPr
  phaseCore :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        GroundedPreTRTSixPhaseLocalData erdos260Constants.cStar
          erdos260Constants.ξ (shell.X : Real)
  chainCompression :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (h_supportCount_pos : 1 <= supportCount shell.d shell.X),
        AppendixNTRTChainCompressionInputData (phaseCore shell pin)
          (carry shell pin) pin.hc0Small h_supportCount_pos

/-- Assemble per-failure data from the Appendix N chain-compression endpoint. -/
def appendixNChainCompressionCurrentToAssembly
    (data : GlobalAppendixNChainCompressionCurrentInputs) :
    GlobalPerFailureAssembly where
  constants := erdos260Constants
  startThreshold := by
    intro _Q d _hQ hd hnonterm _hrational
    exact firstPositiveSupportThreshold d hd hnonterm
  perFailureAssembly := by
    intro Q d hQ hd hnonterm hrational X hXdyadic hXge hfailure
    let shell :=
      FailingDyadicShell.ofGlobalConstants erdos260Constants Q d X
        hQ hd hnonterm hrational hXdyadic
        erdos260Constants.c0 erdos260Constants.c0_pos
        manuscriptC0_lt_kappa erdos260Constants.c0_le_cQ hfailure
    let pin : PinnedManuscriptShell shell := { hcQ := rfl, hc0 := rfl }
    have h_supportCount_pos : 1 <= supportCount shell.d shell.X := by
      exact supportCount_pos_of_firstPositiveSupportThreshold_le hd hnonterm hXge
    let carryLocal := data.carry shell pin
    let carryData :=
      carryLocal.toCarryData erdos260Constants_cPr_le_half
        pin.hc0Small h_supportCount_pos
    let chain := data.chainCompression shell pin h_supportCount_pos
    let phases := chain.phases.toSixPhaseFactoryData
    exact
      PerFailureAssemblyData.ofHighExcessCharge phases carryData
        (tableRoutedSplitPhaseAccountedToHighExcessData
          chain.toTableRoutedHighExcessData)

/-- Erdos 260 from the Appendix N chain-compression current endpoint. -/
theorem erdos260_final_core_appendix_n_chain_compression_current
    (data : GlobalAppendixNChainCompressionCurrentInputs) :
    Erdos260Statement :=
  erdos260Statement_of_globalPerFailureAssembly
    (appendixNChainCompressionCurrentToAssembly data)

/--
Appendix N chain-compression endpoint with the carry provider narrowed to the
manuscript order `r = floor(kappa L)`.
-/
structure GlobalAppendixNChainCompressionManuscriptCarryInputs where
  carry :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        ManuscriptThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
          shell erdos260Constants.cPr
  phaseCore :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        GroundedPreTRTSixPhaseLocalData erdos260Constants.cStar
          erdos260Constants.ξ (shell.X : Real)
  chainCompression :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (h_supportCount_pos : 1 <= supportCount shell.d shell.X),
        AppendixNTRTChainCompressionInputData (phaseCore shell pin)
          (ManuscriptThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData.toThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
            (carry shell pin))
          pin.hc0Small h_supportCount_pos

/-- The manuscript-carry endpoint is a strict refinement of the current one. -/
def GlobalAppendixNChainCompressionManuscriptCarryInputs.toCurrent
    (data : GlobalAppendixNChainCompressionManuscriptCarryInputs) :
    GlobalAppendixNChainCompressionCurrentInputs where
  carry := fun shell pin =>
    ManuscriptThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData.toThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
      (data.carry shell pin)
  phaseCore := data.phaseCore
  chainCompression := fun shell pin h_supportCount_pos =>
    data.chainCompression shell pin h_supportCount_pos

/--
Assemble per-failure data from the Appendix N endpoint with manuscript floor
carry.
-/
def appendixNChainCompressionManuscriptCarryToAssembly
    (data : GlobalAppendixNChainCompressionManuscriptCarryInputs) :
    GlobalPerFailureAssembly :=
  appendixNChainCompressionCurrentToAssembly data.toCurrent

/--
Erdos 260 from the Appendix N chain-compression endpoint with manuscript floor
carry.
-/
theorem erdos260_final_core_appendix_n_chain_compression_manuscript_carry
    (data : GlobalAppendixNChainCompressionManuscriptCarryInputs) :
    Erdos260Statement :=
  erdos260Statement_of_globalPerFailureAssembly
    (appendixNChainCompressionManuscriptCarryToAssembly data)

/--
Appendix N chain-compression endpoint where the carry provider no longer
contains the large-shell inequality `B(Q)+25 <= L`; that inequality is supplied
by the global start threshold below.
-/
structure GlobalAppendixNChainCompressionLargeThresholdInputs where
  carry :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        ManuscriptCarryScaleInputData shell
  phaseCore :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        GroundedPreTRTSixPhaseLocalData erdos260Constants.cStar
          erdos260Constants.ξ (shell.X : Real)
  chainCompression :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (h_supportCount_pos : 1 <= supportCount shell.d shell.X)
      (hCarryLarge : carryB shell.Q + 25 <= Classical.choose shell.hXdyadic),
        AppendixNTRTChainCompressionInputData (phaseCore shell pin)
          ((carry shell pin).toThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
            hCarryLarge)
          pin.hc0Small h_supportCount_pos

/--
Assemble per-failure data from the Appendix N endpoint whose carry-large
inequality is closed by the start threshold.
-/
def appendixNChainCompressionLargeThresholdToAssembly
    (data : GlobalAppendixNChainCompressionLargeThresholdInputs) :
    GlobalPerFailureAssembly where
  constants := erdos260Constants
  startThreshold := by
    intro Q d _hQ hd hnonterm _hrational
    exact appendixNChainCompressionStartThreshold Q d hd hnonterm
  perFailureAssembly := by
    intro Q d hQ hd hnonterm hrational X hXdyadic hXge hfailure
    let shell :=
      FailingDyadicShell.ofGlobalConstants erdos260Constants Q d X
        hQ hd hnonterm hrational hXdyadic
        erdos260Constants.c0 erdos260Constants.c0_pos
        manuscriptC0_lt_kappa erdos260Constants.c0_le_cQ hfailure
    let pin : PinnedManuscriptShell shell := { hcQ := rfl, hc0 := rfl }
    have h_supportThreshold :
        firstPositiveSupportThreshold d hd hnonterm <= X := by
      exact le_trans
        firstPositiveSupportThreshold_le_appendixNChainCompressionStartThreshold
        hXge
    have h_supportCount_pos : 1 <= supportCount shell.d shell.X := by
      exact supportCount_pos_of_firstPositiveSupportThreshold_le hd hnonterm
        h_supportThreshold
    have h_carryThreshold :
        carryThreshold (carryB Q + 19) <= X := by
      exact le_trans
        carryThreshold_le_appendixNChainCompressionStartThreshold
        hXge
    have hCarryLargeQ :
        carryB Q + 25 <= Classical.choose shell.hXdyadic := by
      exact carryLarge_of_carryThreshold_le
        (B := carryB Q)
        (X := X)
        (L := Classical.choose shell.hXdyadic)
        (Classical.choose_spec shell.hXdyadic)
        h_carryThreshold
    have hCarryLarge :
        carryB shell.Q + 25 <= Classical.choose shell.hXdyadic := by
      exact hCarryLargeQ
    let carryLocal :=
      (data.carry shell pin).toThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        (cPr := erdos260Constants.cPr)
        hCarryLarge
    let carryData :=
      carryLocal.toCarryData erdos260Constants_cPr_le_half
        pin.hc0Small h_supportCount_pos
    let chain := data.chainCompression shell pin h_supportCount_pos hCarryLarge
    let phases := chain.phases.toSixPhaseFactoryData
    exact
      PerFailureAssemblyData.ofHighExcessCharge phases carryData
        (tableRoutedSplitPhaseAccountedToHighExcessData
          chain.toTableRoutedHighExcessData)

/--
Erdos 260 from the Appendix N chain-compression endpoint with carry-large
closed by the global threshold.
-/
theorem erdos260_final_core_appendix_n_chain_compression_large_threshold
    (data : GlobalAppendixNChainCompressionLargeThresholdInputs) :
    Erdos260Statement :=
  erdos260Statement_of_globalPerFailureAssembly
    (appendixNChainCompressionLargeThresholdToAssembly data)

/--
Appendix N chain-compression endpoint where both proof-only prerequisites of the
chain package, `supportCount_pos` and `B(Q)+25 <= L`, are supplied canonically
from the strengthened global start threshold.
-/
structure GlobalAppendixNChainCompressionStartThresholdInputs where
  carry :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        ManuscriptCarryScaleInputData shell
  phaseCore :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        GroundedPreTRTSixPhaseLocalData erdos260Constants.cStar
          erdos260Constants.ξ (shell.X : Real)
  chainCompression :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        AppendixNTRTChainCompressionInputData (phaseCore shell pin)
          ((carry shell pin).toThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
            (carryLarge_of_appendixNChainCompressionStartThreshold_le hXge))
          pin.hc0Small
          (supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge)

/--
Assemble per-failure data from the Appendix N endpoint whose proof-only local
premises are closed by the start threshold.
-/
def appendixNChainCompressionStartThresholdToAssembly
    (data : GlobalAppendixNChainCompressionStartThresholdInputs) :
    GlobalPerFailureAssembly where
  constants := erdos260Constants
  startThreshold := by
    intro Q d _hQ hd hnonterm _hrational
    exact appendixNChainCompressionStartThreshold Q d hd hnonterm
  perFailureAssembly := by
    intro Q d hQ hd hnonterm hrational X hXdyadic hXge hfailure
    let shell :=
      FailingDyadicShell.ofGlobalConstants erdos260Constants Q d X
        hQ hd hnonterm hrational hXdyadic
        erdos260Constants.c0 erdos260Constants.c0_pos
        manuscriptC0_lt_kappa erdos260Constants.c0_le_cQ hfailure
    let pin : PinnedManuscriptShell shell := { hcQ := rfl, hc0 := rfl }
    have hXgeShell :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X := by
      simpa using hXge
    let h_supportCount_pos :=
      supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXgeShell
    let hCarryLarge :=
      carryLarge_of_appendixNChainCompressionStartThreshold_le hXgeShell
    let carryLocal :=
      (data.carry shell pin).toThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        (cPr := erdos260Constants.cPr)
        hCarryLarge
    let carryData :=
      carryLocal.toCarryData erdos260Constants_cPr_le_half
        pin.hc0Small h_supportCount_pos
    let chain := data.chainCompression shell pin hXgeShell
    let phases := chain.phases.toSixPhaseFactoryData
    exact
      PerFailureAssemblyData.ofHighExcessCharge phases carryData
        (tableRoutedSplitPhaseAccountedToHighExcessData
          chain.toTableRoutedHighExcessData)

/--
Erdos 260 from the Appendix N chain-compression endpoint with proof-only local
premises closed by the global start threshold.
-/
theorem erdos260_final_core_appendix_n_chain_compression_start_threshold
    (data : GlobalAppendixNChainCompressionStartThresholdInputs) :
    Erdos260Statement :=
  erdos260Statement_of_globalPerFailureAssembly
    (appendixNChainCompressionStartThresholdToAssembly data)

/--
Appendix N chain-compression endpoint where the K.4 active `T,Y` budget is
closed by the proof-v4 first-layer choice `T₀=2L+C_Q`, `Y=εL`.  The carry
provider now supplies only the positive-density shell support needed for
`r=floor(kappa L)`.
-/
structure GlobalAppendixNChainCompressionCanonicalCarryInputs where
  carry :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        ManuscriptCarrySupportSupplyData shell
  phaseCore :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        GroundedPreTRTSixPhaseLocalData erdos260Constants.cStar
          erdos260Constants.ξ (shell.X : Real)
  chainCompression :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        AppendixNTRTChainCompressionInputData (phaseCore shell pin)
          ((carry shell pin).toThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
            (carryLarge_of_appendixNChainCompressionStartThreshold_le hXge))
          pin.hc0Small
          (supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge)

/--
Assemble per-failure data from the Appendix N endpoint with canonical K.4
first-layer carry budget.
-/
def appendixNChainCompressionCanonicalCarryToAssembly
    (data : GlobalAppendixNChainCompressionCanonicalCarryInputs) :
    GlobalPerFailureAssembly where
  constants := erdos260Constants
  startThreshold := by
    intro Q d _hQ hd hnonterm _hrational
    exact appendixNChainCompressionStartThreshold Q d hd hnonterm
  perFailureAssembly := by
    intro Q d hQ hd hnonterm hrational X hXdyadic hXge hfailure
    let shell :=
      FailingDyadicShell.ofGlobalConstants erdos260Constants Q d X
        hQ hd hnonterm hrational hXdyadic
        erdos260Constants.c0 erdos260Constants.c0_pos
        manuscriptC0_lt_kappa erdos260Constants.c0_le_cQ hfailure
    let pin : PinnedManuscriptShell shell := { hcQ := rfl, hc0 := rfl }
    have hXgeShell :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X := by
      simpa using hXge
    let h_supportCount_pos :=
      supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXgeShell
    let hCarryLarge :=
      carryLarge_of_appendixNChainCompressionStartThreshold_le hXgeShell
    let carryLocal :=
      (data.carry shell pin).toThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        (cPr := erdos260Constants.cPr)
        hCarryLarge
    let carryData :=
      carryLocal.toCarryData erdos260Constants_cPr_le_half
        pin.hc0Small h_supportCount_pos
    let chain := data.chainCompression shell pin hXgeShell
    let phases := chain.phases.toSixPhaseFactoryData
    exact
      PerFailureAssemblyData.ofHighExcessCharge phases carryData
        (tableRoutedSplitPhaseAccountedToHighExcessData
          chain.toTableRoutedHighExcessData)

/--
Erdos 260 from the Appendix N chain-compression endpoint with canonical K.4
first-layer carry budget.
-/
theorem erdos260_final_core_appendix_n_chain_compression_canonical_carry
    (data : GlobalAppendixNChainCompressionCanonicalCarryInputs) :
    Erdos260Statement :=
  erdos260Statement_of_globalPerFailureAssembly
    (appendixNChainCompressionCanonicalCarryToAssembly data)

/--
Appendix N chain-compression endpoint where the carry budget and the C1-VD/I.9
mass split are both canonical.  The chain provider no longer supplies the
algebraic split equality `branchMass = termMass + VarDrop`.
-/
structure GlobalAppendixNChainCompressionCanonicalSplitInputs where
  carry :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        ManuscriptCarrySupportSupplyData shell
  phaseCore :
    forall shell : FailingDyadicShell,
      PinnedManuscriptShell shell ->
        GroundedPreTRTSixPhaseLocalData erdos260Constants.cStar
          erdos260Constants.ξ (shell.X : Real)
  chainCompression :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        AppendixNTRTChainCompressionCanonicalSplitInputData (phaseCore shell pin)
          ((carry shell pin).toThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
            (carryLarge_of_appendixNChainCompressionStartThreshold_le hXge))
          pin.hc0Small
          (supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge)

/--
Assemble per-failure data from the Appendix N endpoint with canonical carry
budget and canonical C1-VD/I.9 split.
-/
def appendixNChainCompressionCanonicalSplitToAssembly
    (data : GlobalAppendixNChainCompressionCanonicalSplitInputs) :
    GlobalPerFailureAssembly where
  constants := erdos260Constants
  startThreshold := by
    intro Q d _hQ hd hnonterm _hrational
    exact appendixNChainCompressionStartThreshold Q d hd hnonterm
  perFailureAssembly := by
    intro Q d hQ hd hnonterm hrational X hXdyadic hXge hfailure
    let shell :=
      FailingDyadicShell.ofGlobalConstants erdos260Constants Q d X
        hQ hd hnonterm hrational hXdyadic
        erdos260Constants.c0 erdos260Constants.c0_pos
        manuscriptC0_lt_kappa erdos260Constants.c0_le_cQ hfailure
    let pin : PinnedManuscriptShell shell := { hcQ := rfl, hc0 := rfl }
    have hXgeShell :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X := by
      simpa using hXge
    let h_supportCount_pos :=
      supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXgeShell
    let hCarryLarge :=
      carryLarge_of_appendixNChainCompressionStartThreshold_le hXgeShell
    let carryLocal :=
      (data.carry shell pin).toThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        (cPr := erdos260Constants.cPr)
        hCarryLarge
    let carryData :=
      carryLocal.toCarryData erdos260Constants_cPr_le_half
        pin.hc0Small h_supportCount_pos
    let chain := data.chainCompression shell pin hXgeShell
    let chainExplicit := chain.toChainCompressionInputData
    let phases := chainExplicit.phases.toSixPhaseFactoryData
    exact
      PerFailureAssemblyData.ofHighExcessCharge phases carryData
        (tableRoutedSplitPhaseAccountedToHighExcessData
          chainExplicit.toTableRoutedHighExcessData)

/--
Erdos 260 from the Appendix N chain-compression endpoint with canonical carry
budget and canonical C1-VD/I.9 split.
-/
theorem erdos260_final_core_appendix_n_chain_compression_canonical_split
    (data : GlobalAppendixNChainCompressionCanonicalSplitInputs) :
    Erdos260Statement :=
  erdos260Statement_of_globalPerFailureAssembly
    (appendixNChainCompressionCanonicalSplitToAssembly data)

/--
Appendix N chain-compression endpoint where the carry budget, active variation
floor `Y`, and C1-VD/I.9 split are canonical.
-/
structure GlobalAppendixNChainCompressionCanonicalYInputs where
  carry :
    forall shell : FailingDyadicShell,
      ManuscriptCarrySupportSupplyData shell
  phaseCore :
    forall shell : FailingDyadicShell,
        GroundedPreTRTSixPhaseLocalData erdos260Constants.cStar
          erdos260Constants.ξ (shell.X : Real)
  chainCompression :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        AppendixNTRTChainCompressionCanonicalYInputData (phaseCore shell)
          ((carry shell).toThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
            (carryLarge_of_appendixNChainCompressionStartThreshold_le hXge))
          pin.hc0Small
          (supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge)

/--
Density-flavored version of the canonical-Y endpoint.  The carry support
condition is supplied by a dyadic shell-density bridge rather than by the raw
`hKr` inequality; the projection to `GlobalAppendixNChainCompressionCanonicalYInputs`
is proved below.
-/
structure GlobalAppendixNChainCompressionDensityCanonicalYInputs where
  carryDensity :
    forall shell : FailingDyadicShell,
      ManuscriptCarrySupportSupplyData.DensityData shell
  phaseCore :
    forall shell : FailingDyadicShell,
        GroundedPreTRTSixPhaseLocalData erdos260Constants.cStar
          erdos260Constants.ξ (shell.X : Real)
  chainCompression :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        AppendixNTRTChainCompressionCanonicalYInputData (phaseCore shell)
          ((carryDensity shell).toThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
            (carryLarge_of_appendixNChainCompressionStartThreshold_le hXge))
          pin.hc0Small
          (supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge)

/--
Gap-flavored version of the canonical-Y endpoint.  This matches proof-v4 H.5:
the carry support condition is supplied by the rational dyadic gap bound, not by
the positive-density conclusion that the global contradiction is proving.
-/
structure GlobalAppendixNChainCompressionGapCanonicalYInputs where
  phaseCore :
    forall shell : FailingDyadicShell,
        GroundedPreTRTSixPhaseLocalData erdos260Constants.cStar
          erdos260Constants.ξ (shell.X : Real)
  chainCompression :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        AppendixNTRTChainCompressionCanonicalYInputData (phaseCore shell)
          ((ManuscriptCarrySupportSupplyData.GapData.ofCarryLarge
            (supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge)
            (carryLarge_of_appendixNChainCompressionStartThreshold_le hXge)
            |>.toThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
              (supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge)
              (carryLarge_of_appendixNChainCompressionStartThreshold_le hXge)))
          pin.hc0Small
          (supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge)

/-- The canonical rational-gap carry-local package, factored out so dependent
endpoint fields can refer to it without expanding the proof term. -/
def appendixNGapCanonicalYCarryLocalAt
    (shell : FailingDyadicShell)
    (hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
          shell.hnonterm <= shell.X) :
    ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
      shell erdos260Constants.cPr :=
  let gapData :=
    ManuscriptCarrySupportSupplyData.GapData.ofCarryLarge
      (supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge)
      (carryLarge_of_appendixNChainCompressionStartThreshold_le hXge)
  gapData.toThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
    (supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge)
    (carryLarge_of_appendixNChainCompressionStartThreshold_le hXge)

/-- The concrete carry/failure data used by the rational-gap Appendix N endpoint
at the pinned small-large shell. -/
def appendixNGapCanonicalYCarryDataAt
    (shell : FailingDyadicShell)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
          shell.hnonterm <= shell.X) :
    CarryDataFromFailure shell erdos260Constants.cPr :=
  (appendixNGapCanonicalYCarryLocalAt shell hXge).toCarryData
    erdos260Constants_cPr_le_half hc0Small
    (supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge)

/-- The concrete canonical-Y carry data used by Appendix N has nonnegative
active floor, inherited from the threshold-controlled carry local package. -/
theorem appendixNGapCanonicalYCarryDataAt_Y_nonneg
    (shell : FailingDyadicShell)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
          shell.hnonterm <= shell.X) :
    0 <= (appendixNGapCanonicalYCarryDataAt shell hc0Small hXge).Y := by
  dsimp [appendixNGapCanonicalYCarryDataAt,
    ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData.toCarryData,
    ErrorBudgetedStrictFailureBoundedThresholdShellGroundedCarryLocalData.toCarryData,
    ErrorBudgetedStrictFailureBoundedThresholdShellGroundedCarryLocalData.toBudgetedStrictFailureBoundedThresholdShellGroundedCarryLocalData,
    BudgetedStrictFailureBoundedThresholdShellGroundedCarryLocalData.toCarryData,
    BudgetedStrictFailureBoundedThresholdShellGroundedCarryLocalData.toStrictFailureBoundedThresholdShellGroundedCarryLocalData,
    StrictFailureBoundedThresholdShellGroundedCarryLocalData.toCarryData,
    CarryDataFromFailure.ofShellAndSupportCountFailureBound,
    CarryDataFromFailure.ofShellAndCarryParams,
    CarryDataFromFailure.ofShellAndLowExcess,
    CarryDataFromFailure.ofShellAndBounds]
  exact (appendixNGapCanonicalYCarryLocalAt shell hXge).hY

/-- The concrete canonical-Y carry data used by Appendix N has nonnegative
active threshold, inherited from the threshold-controlled carry local package. -/
theorem appendixNGapCanonicalYCarryDataAt_T_nonneg
    (shell : FailingDyadicShell)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
          shell.hnonterm <= shell.X) :
    0 <= (appendixNGapCanonicalYCarryDataAt shell hc0Small hXge).T := by
  dsimp [appendixNGapCanonicalYCarryDataAt,
    ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData.toCarryData,
    ErrorBudgetedStrictFailureBoundedThresholdShellGroundedCarryLocalData.toCarryData,
    ErrorBudgetedStrictFailureBoundedThresholdShellGroundedCarryLocalData.toBudgetedStrictFailureBoundedThresholdShellGroundedCarryLocalData,
    BudgetedStrictFailureBoundedThresholdShellGroundedCarryLocalData.toCarryData,
    BudgetedStrictFailureBoundedThresholdShellGroundedCarryLocalData.toStrictFailureBoundedThresholdShellGroundedCarryLocalData,
    StrictFailureBoundedThresholdShellGroundedCarryLocalData.toCarryData,
    CarryDataFromFailure.ofShellAndSupportCountFailureBound,
    CarryDataFromFailure.ofShellAndCarryParams,
    CarryDataFromFailure.ofShellAndLowExcess,
    CarryDataFromFailure.ofShellAndBounds]
  exact (appendixNGapCanonicalYCarryLocalAt shell hXge).hT

/-- At the Appendix N canonical carry data, the Chernoff high-cost tail at
`floor Y` is exactly the stopped-branch family produced by the high-excess
selector. -/
theorem appendixNGapCanonicalYCarryDataAt_highBranchCostSet_floorY_eq_stoppedBranches
    (shell : FailingDyadicShell)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
          shell.hnonterm <= shell.X) :
    highBranchCostSet
        (appendixNGapCanonicalYCarryDataAt shell hc0Small hXge).stoppedBranches
        (Nat.floor (appendixNGapCanonicalYCarryDataAt shell hc0Small hXge).Y)
      =
        (appendixNGapCanonicalYCarryDataAt shell hc0Small hXge).stoppedBranches := by
  exact
    CarryDataFromFailure.highBranchCostSet_floorY_eq_stoppedBranches
      (appendixNGapCanonicalYCarryDataAt shell hc0Small hXge)
      (appendixNGapCanonicalYCarryDataAt_T_nonneg shell hc0Small hXge)
      (appendixNGapCanonicalYCarryDataAt_Y_nonneg shell hc0Small hXge)

/--
Large-shell version of the rational-gap endpoint.  The final global assembly
only evaluates the local phase core on shells satisfying the Appendix N start
threshold, so this interface records that actual usage boundary explicitly.
-/
structure GlobalAppendixNChainCompressionGapCanonicalYLargeShellInputs where
  phaseCore :
    forall (shell : FailingDyadicShell)
      (_hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        GroundedPreTRTSixPhaseLocalData erdos260Constants.cStar
          erdos260Constants.ξ (shell.X : Real)
  chainCompression :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        (AppendixNTRTChainCompressionCanonicalYInputData (phaseCore shell hXge)
          (appendixNGapCanonicalYCarryLocalAt shell hXge)
          pin.hc0Small
          (supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge))

/--
Small-large-shell version of the rational-gap endpoint.  The final assembly uses
the pre-TRT phase core only after constructing the pinned manuscript shell, so
the local hypotheses available there are exactly the small-failure constant
`hc0Small` and the Appendix N start-threshold largeness.
-/
structure GlobalAppendixNChainCompressionGapCanonicalYSmallLargeShellInputs where
  phaseCore :
    forall (shell : FailingDyadicShell)
      (_hc0Small : shell.c0 <= manuscriptKappa / 16)
      (_hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        GroundedPreTRTSixPhaseLocalData erdos260Constants.cStar
          erdos260Constants.ξ (shell.X : Real)
  chainCompression :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        (AppendixNTRTChainCompressionCanonicalYInputData
          (phaseCore shell pin.hc0Small hXge)
          (appendixNGapCanonicalYCarryLocalAt shell hXge)
          pin.hc0Small
          (supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge))

namespace GlobalAppendixNChainCompressionGapCanonicalYLargeShellInputs

/-- A large-shell endpoint restricts to the still weaker small-large endpoint by
ignoring the smallness proof. -/
def toSmallLargeShellInputs
    (data : GlobalAppendixNChainCompressionGapCanonicalYLargeShellInputs) :
    GlobalAppendixNChainCompressionGapCanonicalYSmallLargeShellInputs where
  phaseCore := fun shell _hc0Small hXge => data.phaseCore shell hXge
  chainCompression := by
    intro shell pin hXge
    exact data.chainCompression shell pin hXge

end GlobalAppendixNChainCompressionGapCanonicalYLargeShellInputs

namespace GlobalAppendixNChainCompressionGapCanonicalYInputs

/-- The original all-shell endpoint implies the large-shell endpoint by
restriction to the shells actually used by the final global assembly. -/
def toLargeShellInputs
    (data : GlobalAppendixNChainCompressionGapCanonicalYInputs) :
    GlobalAppendixNChainCompressionGapCanonicalYLargeShellInputs where
  phaseCore := fun shell _hXge => data.phaseCore shell
  chainCompression := by
    intro shell pin hXge
    exact data.chainCompression shell pin hXge

end GlobalAppendixNChainCompressionGapCanonicalYInputs

/-- The canonical carry-local package used by the rational-gap version of the
Appendix N chain-compression endpoint. -/
def appendixNGapCanonicalYCarryLocal
    (shell : FailingDyadicShell)
    (hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
          shell.hnonterm <= shell.X) :
    ThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
      shell erdos260Constants.cPr :=
  (ManuscriptCarrySupportSupplyData.GapData.ofCarryLarge
    (supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge)
    (carryLarge_of_appendixNChainCompressionStartThreshold_le hXge)
    |>.toThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
      (supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge)
      (carryLarge_of_appendixNChainCompressionStartThreshold_le hXge))

set_option linter.unusedVariables false in
/-- Assemble the rational-gap pre-TRT phase core from the explicit proof-v4
subpackages. -/
def appendixNGapCanonicalYSubpackagePhaseCore
    (chernoff :
      forall shell : FailingDyadicShell,
        GroundedChernoffLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real))
    (cnl :
      forall shell : FailingDyadicShell,
        GroundedCNLLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real))
    (densePack :
      forall shell : FailingDyadicShell,
        GroundedDensePackLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real))
    (dirtyMultiplicity :
      forall shell : FailingDyadicShell, DirtyMultiplicityData)
    (shell : FailingDyadicShell) :
    GroundedPreTRTSixPhaseLocalData erdos260Constants.cStar erdos260Constants.ξ
      (shell.X : Real) :=
  GroundedPreTRTSixPhaseLocalData.ofClosedLocalGeometry
    (chernoff shell) (cnl shell) (densePack shell) (dirtyMultiplicity shell)

set_option linter.unusedVariables false in
/-- Add the TRT package to the rational-gap proof-v4 phase core. -/
def appendixNGapCanonicalYSubpackageSixPhase
    (chernoff :
      forall shell : FailingDyadicShell,
        GroundedChernoffLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real))
    (cnl :
      forall shell : FailingDyadicShell,
        GroundedCNLLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real))
    (densePack :
      forall shell : FailingDyadicShell,
        GroundedDensePackLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real))
    (dirtyMultiplicity :
      forall shell : FailingDyadicShell, DirtyMultiplicityData)
    (trt :
      forall (shell : FailingDyadicShell)
        (pin : PinnedManuscriptShell shell)
        (hXge :
          appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
              shell.hnonterm <= shell.X),
          GroundedTRTLocalPackageInputData erdos260Constants.cStar
            erdos260Constants.ξ (shell.X : Real))
    (shell : FailingDyadicShell)
    (pin : PinnedManuscriptShell shell)
    (hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
          shell.hnonterm <= shell.X) :
    GroundedSixPhaseLocalData erdos260Constants.cStar erdos260Constants.ξ
      (shell.X : Real) :=
  (appendixNGapCanonicalYSubpackagePhaseCore chernoff cnl densePack
      dirtyMultiplicity shell).withTRT (trt shell pin hXge)

set_option linter.unusedVariables false in
/-- Closure-phase data induced by the rational-gap proof-v4 subpackages. -/
def appendixNGapCanonicalYSubpackageClosurePhaseData
    (chernoff :
      forall shell : FailingDyadicShell,
        GroundedChernoffLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real))
    (cnl :
      forall shell : FailingDyadicShell,
        GroundedCNLLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real))
    (densePack :
      forall shell : FailingDyadicShell,
        GroundedDensePackLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real))
    (dirtyMultiplicity :
      forall shell : FailingDyadicShell, DirtyMultiplicityData)
    (trt :
      forall (shell : FailingDyadicShell)
        (pin : PinnedManuscriptShell shell)
        (hXge :
          appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
              shell.hnonterm <= shell.X),
          GroundedTRTLocalPackageInputData erdos260Constants.cStar
            erdos260Constants.ξ (shell.X : Real))
    (shell : FailingDyadicShell)
    (pin : PinnedManuscriptShell shell)
    (hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
          shell.hnonterm <= shell.X) :
    ClosurePhaseData erdos260Constants.cStar erdos260Constants.ξ
      (shell.X : Real) :=
  (appendixNGapCanonicalYSubpackageSixPhase chernoff cnl densePack
      dirtyMultiplicity trt shell pin hXge).toSixPhaseFactoryData.toClosurePhaseData

set_option linter.unusedVariables false in
/-- Assemble the small-large rational-gap pre-TRT phase core from the explicit
proof-v4 subpackages.  This is the same constructor as
`appendixNGapCanonicalYSubpackagePhaseCore`, but restricted to the final pinned
large-shell context where `hc0Small` and the Appendix N start threshold are
already available. -/
def appendixNGapCanonicalYSmallLargeSubpackagePhaseCore
    (chernoff :
      forall (shell : FailingDyadicShell)
        (_hc0Small : shell.c0 <= manuscriptKappa / 16)
        (_hXge :
          appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
              shell.hnonterm <= shell.X),
          GroundedChernoffLocalData erdos260Constants.cStar erdos260Constants.ξ
            (shell.X : Real))
    (cnl :
      forall (shell : FailingDyadicShell)
        (_hc0Small : shell.c0 <= manuscriptKappa / 16)
        (_hXge :
          appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
              shell.hnonterm <= shell.X),
          GroundedCNLLocalData erdos260Constants.cStar erdos260Constants.ξ
            (shell.X : Real))
    (densePack :
      forall (shell : FailingDyadicShell)
        (_hc0Small : shell.c0 <= manuscriptKappa / 16)
        (_hXge :
          appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
              shell.hnonterm <= shell.X),
          GroundedDensePackLocalData erdos260Constants.cStar erdos260Constants.ξ
            (shell.X : Real))
    (dirtyMultiplicity :
      forall (shell : FailingDyadicShell)
        (_hc0Small : shell.c0 <= manuscriptKappa / 16)
        (_hXge :
          appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
              shell.hnonterm <= shell.X),
          DirtyMultiplicityData)
    (shell : FailingDyadicShell)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
          shell.hnonterm <= shell.X) :
    GroundedPreTRTSixPhaseLocalData erdos260Constants.cStar erdos260Constants.ξ
      (shell.X : Real) :=
  GroundedPreTRTSixPhaseLocalData.ofClosedLocalGeometry
    (chernoff shell hc0Small hXge) (cnl shell hc0Small hXge)
    (densePack shell hc0Small hXge) (dirtyMultiplicity shell hc0Small hXge)

set_option linter.unusedVariables false in
/-- Add the TRT package to the small-large rational-gap proof-v4 phase core. -/
def appendixNGapCanonicalYSmallLargeSubpackageSixPhase
    (chernoff :
      forall (shell : FailingDyadicShell)
        (_hc0Small : shell.c0 <= manuscriptKappa / 16)
        (_hXge :
          appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
              shell.hnonterm <= shell.X),
          GroundedChernoffLocalData erdos260Constants.cStar erdos260Constants.ξ
            (shell.X : Real))
    (cnl :
      forall (shell : FailingDyadicShell)
        (_hc0Small : shell.c0 <= manuscriptKappa / 16)
        (_hXge :
          appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
              shell.hnonterm <= shell.X),
          GroundedCNLLocalData erdos260Constants.cStar erdos260Constants.ξ
            (shell.X : Real))
    (densePack :
      forall (shell : FailingDyadicShell)
        (_hc0Small : shell.c0 <= manuscriptKappa / 16)
        (_hXge :
          appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
              shell.hnonterm <= shell.X),
          GroundedDensePackLocalData erdos260Constants.cStar erdos260Constants.ξ
            (shell.X : Real))
    (dirtyMultiplicity :
      forall (shell : FailingDyadicShell)
        (_hc0Small : shell.c0 <= manuscriptKappa / 16)
        (_hXge :
          appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
              shell.hnonterm <= shell.X),
          DirtyMultiplicityData)
    (trt :
      forall (shell : FailingDyadicShell)
        (pin : PinnedManuscriptShell shell)
        (hXge :
          appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
              shell.hnonterm <= shell.X),
          GroundedTRTLocalPackageInputData erdos260Constants.cStar
            erdos260Constants.ξ (shell.X : Real))
    (shell : FailingDyadicShell)
    (pin : PinnedManuscriptShell shell)
    (hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
          shell.hnonterm <= shell.X) :
    GroundedSixPhaseLocalData erdos260Constants.cStar erdos260Constants.ξ
      (shell.X : Real) :=
  (appendixNGapCanonicalYSmallLargeSubpackagePhaseCore chernoff cnl densePack
      dirtyMultiplicity shell pin.hc0Small hXge).withTRT
    (trt shell pin hXge)

set_option linter.unusedVariables false in
/-- Closure-phase data induced by the small-large rational-gap proof-v4
subpackages. -/
def appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
    (chernoff :
      forall (shell : FailingDyadicShell)
        (_hc0Small : shell.c0 <= manuscriptKappa / 16)
        (_hXge :
          appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
              shell.hnonterm <= shell.X),
          GroundedChernoffLocalData erdos260Constants.cStar erdos260Constants.ξ
            (shell.X : Real))
    (cnl :
      forall (shell : FailingDyadicShell)
        (_hc0Small : shell.c0 <= manuscriptKappa / 16)
        (_hXge :
          appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
              shell.hnonterm <= shell.X),
          GroundedCNLLocalData erdos260Constants.cStar erdos260Constants.ξ
            (shell.X : Real))
    (densePack :
      forall (shell : FailingDyadicShell)
        (_hc0Small : shell.c0 <= manuscriptKappa / 16)
        (_hXge :
          appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
              shell.hnonterm <= shell.X),
          GroundedDensePackLocalData erdos260Constants.cStar erdos260Constants.ξ
            (shell.X : Real))
    (dirtyMultiplicity :
      forall (shell : FailingDyadicShell)
        (_hc0Small : shell.c0 <= manuscriptKappa / 16)
        (_hXge :
          appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
              shell.hnonterm <= shell.X),
          DirtyMultiplicityData)
    (trt :
      forall (shell : FailingDyadicShell)
        (pin : PinnedManuscriptShell shell)
        (hXge :
          appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
              shell.hnonterm <= shell.X),
          GroundedTRTLocalPackageInputData erdos260Constants.cStar
            erdos260Constants.ξ (shell.X : Real))
    (shell : FailingDyadicShell)
    (pin : PinnedManuscriptShell shell)
    (hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
          shell.hnonterm <= shell.X) :
    ClosurePhaseData erdos260Constants.cStar erdos260Constants.ξ
      (shell.X : Real) :=
  (appendixNGapCanonicalYSmallLargeSubpackageSixPhase chernoff cnl densePack
      dirtyMultiplicity trt shell pin hXge).toSixPhaseFactoryData.toClosurePhaseData

set_option linter.unusedVariables false in
/-- Convert Lemma 22.1 stopped-tree leaves into grounded Chernoff local data for
the rational-gap endpoint. -/
def appendixNGapCanonicalYLeafChernoff
    (chernoff :
      forall shell : FailingDyadicShell,
        ChernoffStoppedTreeInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)) :
    forall shell : FailingDyadicShell,
      GroundedChernoffLocalData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real) :=
  fun shell => (chernoff shell).toGroundedChernoffLocalData

set_option linter.unusedVariables false in
/-- Convert G.6/L.1 selector-budget leaves into grounded CNL local data for the
rational-gap endpoint. -/
def appendixNGapCanonicalYLeafCNL
    (cnl :
      forall shell : FailingDyadicShell,
        CNLSelectorBudgetInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)) :
    forall shell : FailingDyadicShell,
      GroundedCNLLocalData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real) :=
  fun shell => (cnl shell).toGroundedCNLLocalData

set_option linter.unusedVariables false in
/-- Convert K.1 DensePack support leaves into grounded DensePack local data for
the rational-gap endpoint. -/
def appendixNGapCanonicalYLeafDensePack
    (densePack :
      forall shell : FailingDyadicShell,
        DensePackSupportInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)) :
    forall shell : FailingDyadicShell,
      GroundedDensePackLocalData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real) :=
  fun shell => (densePack shell).toGroundedDensePackLocalData

set_option linter.unusedVariables false in
/-- Convert K.2.5 dirty scale/fibre leaves into grounded dirty multiplicity data. -/
def appendixNGapCanonicalYLeafDirtyMultiplicity
    (dirtyMultiplicity :
      forall shell : FailingDyadicShell, DirtyMultiplicityInputData) :
    forall shell : FailingDyadicShell, DirtyMultiplicityData :=
  fun shell => (dirtyMultiplicity shell).toDirtyMultiplicityData

set_option linter.unusedVariables false in
/-- Convert the Tower/Return/Run leaves into the grounded TRT package for the
rational-gap endpoint. -/
def appendixNGapCanonicalYLeafTRT
    (tower :
      forall (shell : FailingDyadicShell)
        (pin : PinnedManuscriptShell shell)
        (hXge :
          appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
              shell.hnonterm <= shell.X),
          GroundedTowerLocalData erdos260Constants.cStar erdos260Constants.ξ
            (shell.X : Real))
    (returnPkg :
      forall (shell : FailingDyadicShell)
        (pin : PinnedManuscriptShell shell)
        (hXge :
          appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
              shell.hnonterm <= shell.X),
          GroundedReturnLocalData erdos260Constants.cStar erdos260Constants.ξ
            (shell.X : Real))
    (run :
      forall (shell : FailingDyadicShell)
        (pin : PinnedManuscriptShell shell)
        (hXge :
          appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
              shell.hnonterm <= shell.X),
          GroundedRunLocalData erdos260Constants.cStar erdos260Constants.ξ
            (shell.X : Real)) :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        GroundedTRTLocalPackageInputData erdos260Constants.cStar
          erdos260Constants.ξ (shell.X : Real) :=
  fun shell pin hXge =>
    GroundedTRTLocalPackageInputData.ofClosedTowerReturnRun
      (tower shell pin hXge) (returnPkg shell pin hXge) (run shell pin hXge)

set_option linter.unusedVariables false in
/-- Convert separated Tower/Return/Run local leaves into the grounded TRT
package for the rational-gap endpoint. -/
def appendixNGapCanonicalYTRTLocalLeaves
    (tower :
      forall (shell : FailingDyadicShell)
        (pin : PinnedManuscriptShell shell)
        (hXge :
          appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
              shell.hnonterm <= shell.X),
          TowerLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
            (shell.X : Real))
    (returnPkg :
      forall (shell : FailingDyadicShell)
        (pin : PinnedManuscriptShell shell)
        (hXge :
          appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
              shell.hnonterm <= shell.X),
          ReturnLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
            (shell.X : Real))
    (run :
      forall (shell : FailingDyadicShell)
        (pin : PinnedManuscriptShell shell)
        (hXge :
          appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
              shell.hnonterm <= shell.X),
          RunLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
            (shell.X : Real)) :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        GroundedTRTLocalPackageInputData erdos260Constants.cStar
          erdos260Constants.ξ (shell.X : Real) :=
  appendixNGapCanonicalYLeafTRT
    (fun shell pin hXge => (tower shell pin hXge).toGroundedTowerLocalData)
    (fun shell pin hXge => (returnPkg shell pin hXge).toGroundedReturnLocalData)
    (fun shell pin hXge => (run shell pin hXge).toGroundedRunLocalData)

set_option linter.unusedVariables false in
/--
Subpackage-flavored rational-gap endpoint.  This replaces the two remaining
black-box package fields by the proof-v4 subpackages that construct them:
Chernoff, CNL, DensePack, K.2.5 dirty multiplicity, TRT, and canonical-Y N.24.
-/
structure GlobalAppendixNChainCompressionGapCanonicalYSubpackageInputs where
  chernoff :
    forall shell : FailingDyadicShell,
      GroundedChernoffLocalData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real)
  cnl :
    forall shell : FailingDyadicShell,
      GroundedCNLLocalData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real)
  densePack :
    forall shell : FailingDyadicShell,
      GroundedDensePackLocalData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real)
  dirtyMultiplicity :
    forall shell : FailingDyadicShell, DirtyMultiplicityData
  trt :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        GroundedTRTLocalPackageInputData erdos260Constants.cStar
          erdos260Constants.ξ (shell.X : Real)
  n24 :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
      CarryHitGapN24CanonicalYInputData
        (appendixNGapCanonicalYCarryLocal shell hXge)
        pin.hc0Small
        (supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge)
        (termDensePack
          (((GroundedPreTRTSixPhaseLocalData.ofClosedLocalGeometry
                (chernoff shell) (cnl shell) (densePack shell)
                (dirtyMultiplicity shell)).withTRT
              (trt shell pin hXge)).toSixPhaseFactoryData).toClosurePhaseData)
        (termChernoff
          (((GroundedPreTRTSixPhaseLocalData.ofClosedLocalGeometry
                (chernoff shell) (cnl shell) (densePack shell)
                (dirtyMultiplicity shell)).withTRT
              (trt shell pin hXge)).toSixPhaseFactoryData).toClosurePhaseData)
        (termReturn
          (((GroundedPreTRTSixPhaseLocalData.ofClosedLocalGeometry
                (chernoff shell) (cnl shell) (densePack shell)
                (dirtyMultiplicity shell)).withTRT
              (trt shell pin hXge)).toSixPhaseFactoryData).toClosurePhaseData)
        (termCnl
          (((GroundedPreTRTSixPhaseLocalData.ofClosedLocalGeometry
                (chernoff shell) (cnl shell) (densePack shell)
                (dirtyMultiplicity shell)).withTRT
              (trt shell pin hXge)).toSixPhaseFactoryData).toClosurePhaseData)
        (termTower
          (((GroundedPreTRTSixPhaseLocalData.ofClosedLocalGeometry
                (chernoff shell) (cnl shell) (densePack shell)
                (dirtyMultiplicity shell)).withTRT
              (trt shell pin hXge)).toSixPhaseFactoryData).toClosurePhaseData)
        (termRun
          (((GroundedPreTRTSixPhaseLocalData.ofClosedLocalGeometry
                (chernoff shell) (cnl shell) (densePack shell)
                (dirtyMultiplicity shell)).withTRT
              (trt shell pin hXge)).toSixPhaseFactoryData).toClosurePhaseData)

namespace GlobalAppendixNChainCompressionGapCanonicalYSubpackageInputs

/-- Assemble the pre-TRT phase core from the explicit proof-v4 subpackages. -/
def phaseCore
    (data : GlobalAppendixNChainCompressionGapCanonicalYSubpackageInputs)
    (shell : FailingDyadicShell) :
    GroundedPreTRTSixPhaseLocalData erdos260Constants.cStar erdos260Constants.ξ
      (shell.X : Real) :=
  GroundedPreTRTSixPhaseLocalData.ofClosedLocalGeometry
    (data.chernoff shell) (data.cnl shell) (data.densePack shell)
    (data.dirtyMultiplicity shell)

/-- Convert the subpackage-flavored endpoint to the existing two-package
rational-gap endpoint. -/
def toGapCanonicalYInputs
    (data : GlobalAppendixNChainCompressionGapCanonicalYSubpackageInputs) :
    GlobalAppendixNChainCompressionGapCanonicalYInputs where
  phaseCore := data.phaseCore
  chainCompression := by
    intro shell pin hXge
    exact
      AppendixNTRTChainCompressionCanonicalYInputData.ofClosedN24
        (data.trt shell pin hXge) (data.n24 shell pin hXge)

end GlobalAppendixNChainCompressionGapCanonicalYSubpackageInputs

set_option linter.unusedVariables false in
/--
Small-large-shell subpackage endpoint.  This is the direct proof-v4 repair path
for the current two-boundary residual: all local package inputs are requested
only at the pinned large shells where the final recurrence uses them.
-/
structure GlobalAppendixNChainCompressionGapCanonicalYSmallLargeSubpackageInputs where
  chernoff :
    forall (shell : FailingDyadicShell)
      (_hc0Small : shell.c0 <= manuscriptKappa / 16)
      (_hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        GroundedChernoffLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  cnl :
    forall (shell : FailingDyadicShell)
      (_hc0Small : shell.c0 <= manuscriptKappa / 16)
      (_hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        GroundedCNLLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  densePack :
    forall (shell : FailingDyadicShell)
      (_hc0Small : shell.c0 <= manuscriptKappa / 16)
      (_hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        GroundedDensePackLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  dirtyMultiplicity :
    forall (shell : FailingDyadicShell)
      (_hc0Small : shell.c0 <= manuscriptKappa / 16)
      (_hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        DirtyMultiplicityData
  trt :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        GroundedTRTLocalPackageInputData erdos260Constants.cStar
          erdos260Constants.ξ (shell.X : Real)
  n24 :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
      CarryHitGapN24CanonicalYInputData
        (appendixNGapCanonicalYCarryLocalAt shell hXge)
        pin.hc0Small
        (supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge)
        (termDensePack
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            chernoff cnl densePack dirtyMultiplicity trt shell pin hXge))
        (termChernoff
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            chernoff cnl densePack dirtyMultiplicity trt shell pin hXge))
        (termReturn
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            chernoff cnl densePack dirtyMultiplicity trt shell pin hXge))
        (termCnl
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            chernoff cnl densePack dirtyMultiplicity trt shell pin hXge))
        (termTower
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            chernoff cnl densePack dirtyMultiplicity trt shell pin hXge))
        (termRun
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            chernoff cnl densePack dirtyMultiplicity trt shell pin hXge))

namespace GlobalAppendixNChainCompressionGapCanonicalYSmallLargeSubpackageInputs

/-- Assemble the small-large pre-TRT phase core from explicit proof-v4
subpackages. -/
def phaseCore
    (data : GlobalAppendixNChainCompressionGapCanonicalYSmallLargeSubpackageInputs)
    (shell : FailingDyadicShell)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
          shell.hnonterm <= shell.X) :
    GroundedPreTRTSixPhaseLocalData erdos260Constants.cStar erdos260Constants.ξ
      (shell.X : Real) :=
  appendixNGapCanonicalYSmallLargeSubpackagePhaseCore data.chernoff data.cnl
    data.densePack data.dirtyMultiplicity shell hc0Small hXge

/-- Convert the small-large subpackage endpoint to the current small-large
two-boundary endpoint. -/
def toSmallLargeShellInputs
    (data : GlobalAppendixNChainCompressionGapCanonicalYSmallLargeSubpackageInputs) :
    GlobalAppendixNChainCompressionGapCanonicalYSmallLargeShellInputs where
  phaseCore := data.phaseCore
  chainCompression := by
    intro shell pin hXge
    exact
      AppendixNTRTChainCompressionCanonicalYInputData.ofClosedN24
        (data.trt shell pin hXge) (data.n24 shell pin hXge)

end GlobalAppendixNChainCompressionGapCanonicalYSmallLargeSubpackageInputs

set_option linter.unusedVariables false in
/--
Small-large TRT-local-leaf endpoint.  This is the finest proof-v4 leaf surface
for the two current small-large residual fields: Lemma 22.1, G.6/L.1, K.1,
K.2.5, Tower/Return/Run, N.2, and N.3.3 are all requested only in the pinned
large-shell context used by the final recurrence.
-/
structure GlobalAppendixNChainCompressionGapCanonicalYSmallLargeTRTLocalLeafTerminalVariationKMN2N3Inputs where
  chernoff :
    forall (shell : FailingDyadicShell)
      (_hc0Small : shell.c0 <= manuscriptKappa / 16)
      (_hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        ChernoffStoppedTreeInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  cnl :
    forall (shell : FailingDyadicShell)
      (_hc0Small : shell.c0 <= manuscriptKappa / 16)
      (_hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        CNLSelectorBudgetInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  densePack :
    forall (shell : FailingDyadicShell)
      (_hc0Small : shell.c0 <= manuscriptKappa / 16)
      (_hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        DensePackSupportInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  dirtyMultiplicity :
    forall (shell : FailingDyadicShell)
      (_hc0Small : shell.c0 <= manuscriptKappa / 16)
      (_hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        DirtyMultiplicityInputData
  tower :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        TowerLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  returnPkg :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        ReturnLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  run :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        RunLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  variation :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
      CarryHitGapCanonicalYVariationLeafData
        (appendixNGapCanonicalYCarryLocalAt shell hXge)
        pin.hc0Small
        (supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge)
        (termRun
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))
  terminalAbsorption :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
      ClassicalTerminalN33LeafData
        (GroundedC1VDSplitData.ofVariation
          (variation shell pin hXge).toVariationClassData.toVariationClassData).termMass
        (termDensePack
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))
        (termChernoff
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))
        (termReturn
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))
        (termCnl
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))
        (termTower
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))

namespace GlobalAppendixNChainCompressionGapCanonicalYSmallLargeTRTLocalLeafTerminalVariationKMN2N3Inputs

/-- Convert the small-large finest leaf endpoint to the small-large subpackage
endpoint. -/
def toSmallLargeSubpackageInputs
    (data :
      GlobalAppendixNChainCompressionGapCanonicalYSmallLargeTRTLocalLeafTerminalVariationKMN2N3Inputs) :
    GlobalAppendixNChainCompressionGapCanonicalYSmallLargeSubpackageInputs where
  chernoff := fun shell hc0Small hXge =>
    (data.chernoff shell hc0Small hXge).toGroundedChernoffLocalData
  cnl := fun shell hc0Small hXge =>
    (data.cnl shell hc0Small hXge).toGroundedCNLLocalData
  densePack := fun shell hc0Small hXge =>
    (data.densePack shell hc0Small hXge).toGroundedDensePackLocalData
  dirtyMultiplicity := fun shell hc0Small hXge =>
    (data.dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData
  trt := appendixNGapCanonicalYTRTLocalLeaves data.tower data.returnPkg data.run
  n24 := by
    intro shell pin hXge
    exact
      CarryHitGapN24CanonicalYInputData.ofClosedN2N3
        (data.variation shell pin hXge).toVariationClassData
        ((data.terminalAbsorption shell pin hXge).toClassicalTableRoutedDirectFiveClassTerminalAbsorptionData)

/-- Convert the small-large finest leaf endpoint to the current small-large
two-boundary endpoint. -/
def toSmallLargeShellInputs
    (data :
      GlobalAppendixNChainCompressionGapCanonicalYSmallLargeTRTLocalLeafTerminalVariationKMN2N3Inputs) :
    GlobalAppendixNChainCompressionGapCanonicalYSmallLargeShellInputs :=
  data.toSmallLargeSubpackageInputs.toSmallLargeShellInputs

end GlobalAppendixNChainCompressionGapCanonicalYSmallLargeTRTLocalLeafTerminalVariationKMN2N3Inputs

set_option linter.unusedVariables false in
/--
Small-large finest leaf endpoint with Chernoff tied to the actual carry stopped
tree.  Compared with
`GlobalAppendixNChainCompressionGapCanonicalYSmallLargeTRTLocalLeafTerminalVariationKMN2N3Inputs`,
the Chernoff field is no longer an arbitrary stopped-tree input: it is a Lemma
22.1 budget on the concrete `CarryDataFromFailure` generated by the rational-gap
carry local package at this shell.
-/
structure GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffTRTLocalLeafTerminalVariationKMN2N3Inputs where
  chernoff :
    forall (shell : FailingDyadicShell)
      (hc0Small : shell.c0 <= manuscriptKappa / 16)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        RegularShellPaidChernoff22_1AInputData
          erdos260Constants.cStar erdos260Constants.ξ (shell.X : Real)
  cnl :
    forall (shell : FailingDyadicShell)
      (_hc0Small : shell.c0 <= manuscriptKappa / 16)
      (_hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        CNLSelectorBudgetInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  densePack :
    forall (shell : FailingDyadicShell)
      (_hc0Small : shell.c0 <= manuscriptKappa / 16)
      (_hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        DensePackSupportInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  dirtyMultiplicity :
    forall (shell : FailingDyadicShell)
      (_hc0Small : shell.c0 <= manuscriptKappa / 16)
      (_hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        DirtyMultiplicityInputData
  tower :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        TowerLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  returnPkg :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        ReturnLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  run :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        RunLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  variation :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
      CarryHitGapCanonicalYVariationLeafData
        (appendixNGapCanonicalYCarryLocalAt shell hXge)
        pin.hc0Small
        (supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge)
        (termRun
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))
  terminalAbsorption :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
      ClassicalTerminalN33LeafData
        (GroundedC1VDSplitData.ofVariation
          (variation shell pin hXge).toVariationClassData.toVariationClassData).termMass
        (termDensePack
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))
        (termChernoff
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))
        (termReturn
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))
        (termCnl
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))
        (termTower
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))

namespace GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffTRTLocalLeafTerminalVariationKMN2N3Inputs

/-- Forget the carry-specific Chernoff skeleton to the stopped-tree leaf endpoint. -/
def toSmallLargeTRTLocalLeafTerminalVariationKMN2N3Inputs
    (data :
      GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffTRTLocalLeafTerminalVariationKMN2N3Inputs) :
    GlobalAppendixNChainCompressionGapCanonicalYSmallLargeTRTLocalLeafTerminalVariationKMN2N3Inputs where
  chernoff := fun shell hc0Small hXge =>
    (data.chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData
  cnl := data.cnl
  densePack := data.densePack
  dirtyMultiplicity := data.dirtyMultiplicity
  tower := data.tower
  returnPkg := data.returnPkg
  run := data.run
  variation := data.variation
  terminalAbsorption := data.terminalAbsorption

/-- Convert the carry-specific Chernoff leaf endpoint to the current small-large
two-boundary endpoint. -/
def toSmallLargeShellInputs
    (data :
      GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffTRTLocalLeafTerminalVariationKMN2N3Inputs) :
    GlobalAppendixNChainCompressionGapCanonicalYSmallLargeShellInputs :=
  data.toSmallLargeTRTLocalLeafTerminalVariationKMN2N3Inputs.toSmallLargeShellInputs

end GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffTRTLocalLeafTerminalVariationKMN2N3Inputs

set_option linter.unusedVariables false in
/--
Carry-specific Chernoff endpoint with the Lemma 22.1 budget split into
pointwise/moment and scalar tail-smallness pieces.
-/
structure GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSplitTRTLocalLeafTerminalVariationKMN2N3Inputs where
  chernoff :
    forall (shell : FailingDyadicShell)
      (hc0Small : shell.c0 <= manuscriptKappa / 16)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        RegularShellPaidChernoff22_1AInputData
          erdos260Constants.cStar erdos260Constants.ξ (shell.X : Real)
  cnl :
    forall (shell : FailingDyadicShell)
      (_hc0Small : shell.c0 <= manuscriptKappa / 16)
      (_hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        CNLSelectorBudgetInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  densePack :
    forall (shell : FailingDyadicShell)
      (_hc0Small : shell.c0 <= manuscriptKappa / 16)
      (_hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        DensePackSupportInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  dirtyMultiplicity :
    forall (shell : FailingDyadicShell)
      (_hc0Small : shell.c0 <= manuscriptKappa / 16)
      (_hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        DirtyMultiplicityInputData
  tower :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        TowerLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  returnPkg :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        ReturnLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  run :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        RunLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  variation :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
      CarryHitGapCanonicalYVariationLeafData
        (appendixNGapCanonicalYCarryLocalAt shell hXge)
        pin.hc0Small
        (supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge)
        (termRun
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))
  terminalAbsorption :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
      ClassicalTerminalN33LeafData
        (GroundedC1VDSplitData.ofVariation
          (variation shell pin hXge).toVariationClassData.toVariationClassData).termMass
        (termDensePack
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))
        (termChernoff
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))
        (termReturn
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))
        (termCnl
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))
        (termTower
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))

namespace GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSplitTRTLocalLeafTerminalVariationKMN2N3Inputs

/-- Merge the split Chernoff fields and project to the carry-specific Chernoff
endpoint. -/
def toSmallLargeCarryChernoffTRTLocalLeafTerminalVariationKMN2N3Inputs
    (data :
      GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSplitTRTLocalLeafTerminalVariationKMN2N3Inputs) :
    GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffTRTLocalLeafTerminalVariationKMN2N3Inputs where
  chernoff := data.chernoff
  cnl := data.cnl
  densePack := data.densePack
  dirtyMultiplicity := data.dirtyMultiplicity
  tower := data.tower
  returnPkg := data.returnPkg
  run := data.run
  variation := data.variation
  terminalAbsorption := data.terminalAbsorption

/-- Convert the split carry-Chernoff endpoint to the current small-large
two-boundary endpoint. -/
def toSmallLargeShellInputs
    (data :
      GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSplitTRTLocalLeafTerminalVariationKMN2N3Inputs) :
    GlobalAppendixNChainCompressionGapCanonicalYSmallLargeShellInputs :=
  data.toSmallLargeCarryChernoffTRTLocalLeafTerminalVariationKMN2N3Inputs.toSmallLargeShellInputs

end GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSplitTRTLocalLeafTerminalVariationKMN2N3Inputs

set_option linter.unusedVariables false in
/--
Carry-specific Chernoff endpoint with Lemma 22.1 split into its three
proof-v4 leaves: pointwise tilt, aggregate moment budget, and scalar
tail-smallness.
-/
structure GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs where
  chernoff :
    forall (shell : FailingDyadicShell)
      (hc0Small : shell.c0 <= manuscriptKappa / 16)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        RegularShellPaidChernoff22_1AInputData
          erdos260Constants.cStar erdos260Constants.ξ (shell.X : Real)
  cnl :
    forall (shell : FailingDyadicShell)
      (_hc0Small : shell.c0 <= manuscriptKappa / 16)
      (_hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        CNLSelectorBudgetInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  densePack :
    forall (shell : FailingDyadicShell)
      (_hc0Small : shell.c0 <= manuscriptKappa / 16)
      (_hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        DensePackSupportInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  dirtyMultiplicity :
    forall (shell : FailingDyadicShell)
      (_hc0Small : shell.c0 <= manuscriptKappa / 16)
      (_hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        DirtyMultiplicityInputData
  tower :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        TowerLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  returnPkg :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        ReturnLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  run :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        RunLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  variation :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
      CarryHitGapCanonicalYVariationLeafData
        (appendixNGapCanonicalYCarryLocalAt shell hXge)
        pin.hc0Small
        (supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge)
        (termRun
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))
  terminalAbsorption :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
      ClassicalTerminalN33LeafData
        (GroundedC1VDSplitData.ofVariation
          (variation shell pin hXge).toVariationClassData.toVariationClassData).termMass
        (termDensePack
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))
        (termChernoff
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))
        (termReturn
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))
        (termCnl
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))
        (termTower
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))

namespace GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs

/-- Merge the three Chernoff leaves and project to the split carry-Chernoff
endpoint. -/
def toSmallLargeCarryChernoffSplitTRTLocalLeafTerminalVariationKMN2N3Inputs
    (data :
      GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs) :
    GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSplitTRTLocalLeafTerminalVariationKMN2N3Inputs where
  chernoff := data.chernoff
  cnl := data.cnl
  densePack := data.densePack
  dirtyMultiplicity := data.dirtyMultiplicity
  tower := data.tower
  returnPkg := data.returnPkg
  run := data.run
  variation := data.variation
  terminalAbsorption := data.terminalAbsorption

/-- Convert the separated carry-Chernoff endpoint to the current small-large
two-boundary endpoint. -/
def toSmallLargeShellInputs
    (data :
      GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs) :
    GlobalAppendixNChainCompressionGapCanonicalYSmallLargeShellInputs :=
  data.toSmallLargeCarryChernoffSplitTRTLocalLeafTerminalVariationKMN2N3Inputs.toSmallLargeShellInputs

end GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs

set_option linter.unusedVariables false in
/--
Small-large endpoint with carry-Chernoff split into the three Lemma 22.1 leaves
and CNL split into the L.1.1 clean-visible selector input plus the L.1.2
cluster-encoding budget.
-/
structure GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorTRTLocalLeafTerminalVariationKMN2N3Inputs where
  chernoff :
    forall (shell : FailingDyadicShell)
      (hc0Small : shell.c0 <= manuscriptKappa / 16)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        RegularShellPaidChernoff22_1AInputData
          erdos260Constants.cStar erdos260Constants.ξ (shell.X : Real)
  cnl :
    forall (shell : FailingDyadicShell)
      (_hc0Small : shell.c0 <= manuscriptKappa / 16)
      (_hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        CNLSelectorEncodingInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  densePack :
    forall (shell : FailingDyadicShell)
      (_hc0Small : shell.c0 <= manuscriptKappa / 16)
      (_hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        DensePackSupportInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  dirtyMultiplicity :
    forall (shell : FailingDyadicShell)
      (_hc0Small : shell.c0 <= manuscriptKappa / 16)
      (_hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        DirtyMultiplicityInputData
  tower :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        TowerLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  returnPkg :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        ReturnLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  run :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        RunLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  variation :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
      CarryHitGapCanonicalYVariationLeafData
        (appendixNGapCanonicalYCarryLocalAt shell hXge)
        pin.hc0Small
        (supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge)
        (termRun
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))
  terminalAbsorption :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
      ClassicalTerminalN33LeafData
        (GroundedC1VDSplitData.ofVariation
          (variation shell pin hXge).toVariationClassData.toVariationClassData).termMass
        (termDensePack
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))
        (termChernoff
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))
        (termReturn
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))
        (termCnl
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))
        (termTower
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))

namespace GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorTRTLocalLeafTerminalVariationKMN2N3Inputs

/-- Merge the separated CNL selector/encoding leaf and project to the endpoint
where CNL is still carried as one selector-budget record. -/
def toSmallLargeCarryChernoffSeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs
    (data :
      GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorTRTLocalLeafTerminalVariationKMN2N3Inputs) :
    GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs where
  chernoff := data.chernoff
  cnl := fun shell hc0Small hXge =>
    (data.cnl shell hc0Small hXge).toSelectorBudgetInputData
  densePack := data.densePack
  dirtyMultiplicity := data.dirtyMultiplicity
  tower := data.tower
  returnPkg := data.returnPkg
  run := data.run
  variation := data.variation
  terminalAbsorption := data.terminalAbsorption

/-- Convert the separated Chernoff/CNL endpoint to the current small-large
two-boundary endpoint. -/
def toSmallLargeShellInputs
    (data :
      GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorTRTLocalLeafTerminalVariationKMN2N3Inputs) :
    GlobalAppendixNChainCompressionGapCanonicalYSmallLargeShellInputs :=
  data.toSmallLargeCarryChernoffSeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs.toSmallLargeShellInputs

end GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorTRTLocalLeafTerminalVariationKMN2N3Inputs

set_option linter.unusedVariables false in
/--
Small-large endpoint with carry-Chernoff and CNL separated as above, and the
K.2.5 dirty multiplicity leaf reduced to a Fin-labelled per-scale fibre
certificate; the range count is closed by the target `Fin ((log L)^4)`.
-/
structure GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorDirtySeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs where
  chernoff :
    forall (shell : FailingDyadicShell)
      (hc0Small : shell.c0 <= manuscriptKappa / 16)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        RegularShellPaidChernoff22_1AInputData
          erdos260Constants.cStar erdos260Constants.ξ (shell.X : Real)
  cnl :
    forall (shell : FailingDyadicShell)
      (_hc0Small : shell.c0 <= manuscriptKappa / 16)
      (_hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        CNLSelectorEncodingInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  densePack :
    forall (shell : FailingDyadicShell)
      (_hc0Small : shell.c0 <= manuscriptKappa / 16)
      (_hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        DensePackSupportInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  dirtyMultiplicity :
    forall (shell : FailingDyadicShell)
      (_hc0Small : shell.c0 <= manuscriptKappa / 16)
      (_hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        DirtyMultiplicityFinFibreInputData
  tower :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        TowerLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  returnPkg :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        ReturnLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  run :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        RunLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  variation :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
      CarryHitGapCanonicalYVariationLeafData
        (appendixNGapCanonicalYCarryLocalAt shell hXge)
        pin.hc0Small
        (supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge)
        (termRun
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))
  terminalAbsorption :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
      ClassicalTerminalN33LeafData
        (GroundedC1VDSplitData.ofVariation
          (variation shell pin hXge).toVariationClassData.toVariationClassData).termMass
        (termDensePack
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))
        (termChernoff
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))
        (termReturn
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))
        (termCnl
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))
        (termTower
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))

namespace GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorDirtySeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs

/-- Bundle the Fin-labelled dirty fibre leaf and project to the previous
small-large endpoint. -/
def toSmallLargeCarryChernoffSeparatedCNLSelectorTRTLocalLeafTerminalVariationKMN2N3Inputs
    (data :
      GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorDirtySeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs) :
    GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorTRTLocalLeafTerminalVariationKMN2N3Inputs where
  chernoff := data.chernoff
  cnl := data.cnl
  densePack := data.densePack
  dirtyMultiplicity := fun shell hc0Small hXge =>
    (data.dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityInputData
  tower := data.tower
  returnPkg := data.returnPkg
  run := data.run
  variation := data.variation
  terminalAbsorption := data.terminalAbsorption

/-- Convert the separated dirty K.2.5 endpoint to the current small-large
two-boundary endpoint. -/
def toSmallLargeShellInputs
    (data :
      GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorDirtySeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs) :
    GlobalAppendixNChainCompressionGapCanonicalYSmallLargeShellInputs :=
  data.toSmallLargeCarryChernoffSeparatedCNLSelectorTRTLocalLeafTerminalVariationKMN2N3Inputs.toSmallLargeShellInputs

end GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorDirtySeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs

set_option linter.unusedVariables false in
/--
Small-large endpoint with DensePack K.1 split into neighbourhood cover,
shell-packing marker count, and scalar smallness leaves, while the
carry-Chernoff, CNL, and dirty K.2.5 leaves remain at their already separated
boundaries.
-/
structure GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorDensePackSeparatedDirtySeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs where
  chernoff :
    forall (shell : FailingDyadicShell)
      (hc0Small : shell.c0 <= manuscriptKappa / 16)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        RegularShellPaidChernoff22_1AInputData
          erdos260Constants.cStar erdos260Constants.ξ (shell.X : Real)
  cnl :
    forall (shell : FailingDyadicShell)
      (_hc0Small : shell.c0 <= manuscriptKappa / 16)
      (_hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        CNLSelectorEncodingInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  densePack :
    forall (shell : FailingDyadicShell)
      (_hc0Small : shell.c0 <= manuscriptKappa / 16)
      (_hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        DensePackShellSeparatedSupportInputData shell erdos260Constants.cStar
          erdos260Constants.ξ
  dirtyMultiplicity :
    forall (shell : FailingDyadicShell)
      (_hc0Small : shell.c0 <= manuscriptKappa / 16)
      (_hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        DirtyMultiplicityFinFibreInputData
  tower :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        TowerLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  returnPkg :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        ReturnLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  run :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        RunLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  variation :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
      CarryHitGapCanonicalYVariationLeafData
        (appendixNGapCanonicalYCarryLocalAt shell hXge)
        pin.hc0Small
        (supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge)
        (termRun
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))
  terminalAbsorption :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
      ClassicalTerminalN33LeafData
        (GroundedC1VDSplitData.ofVariation
          (variation shell pin hXge).toVariationClassData.toVariationClassData).termMass
        (termDensePack
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))
        (termChernoff
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))
        (termReturn
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))
        (termCnl
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))
        (termTower
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))

namespace GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorDensePackSeparatedDirtySeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs

/-- Bundle the separated DensePack K.1 leaf and project to the previous
small-large endpoint. -/
def toSmallLargeCarryChernoffSeparatedCNLSelectorDirtySeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs
    (data :
      GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorDensePackSeparatedDirtySeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs) :
    GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorDirtySeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs where
  chernoff := data.chernoff
  cnl := data.cnl
  densePack := fun shell hc0Small hXge =>
    (data.densePack shell hc0Small hXge).toDensePackSupportInputData
  dirtyMultiplicity := data.dirtyMultiplicity
  tower := data.tower
  returnPkg := data.returnPkg
  run := data.run
  variation := data.variation
  terminalAbsorption := data.terminalAbsorption

/-- Convert the separated DensePack K.1 endpoint to the current small-large
two-boundary endpoint. -/
def toSmallLargeShellInputs
    (data :
      GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorDensePackSeparatedDirtySeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs) :
    GlobalAppendixNChainCompressionGapCanonicalYSmallLargeShellInputs :=
  data.toSmallLargeCarryChernoffSeparatedCNLSelectorDirtySeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs.toSmallLargeShellInputs

end GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorDensePackSeparatedDirtySeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs

set_option linter.unusedVariables false in
/--
Small-large endpoint with the Tower L.3 leaf split into recurrent-cycle,
routing, routed-output absorption, and scalar smallness certificates.
-/
structure GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorDensePackSeparatedDirtySeparatedTowerSeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs where
  chernoff :
    forall (shell : FailingDyadicShell)
      (hc0Small : shell.c0 <= manuscriptKappa / 16)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        RegularShellPaidChernoff22_1AInputData
          erdos260Constants.cStar erdos260Constants.ξ (shell.X : Real)
  cnl :
    forall (shell : FailingDyadicShell)
      (_hc0Small : shell.c0 <= manuscriptKappa / 16)
      (_hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        CNLSelectorEncodingInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  densePack :
    forall (shell : FailingDyadicShell)
      (_hc0Small : shell.c0 <= manuscriptKappa / 16)
      (_hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        DensePackShellSeparatedSupportInputData shell erdos260Constants.cStar
          erdos260Constants.ξ
  dirtyMultiplicity :
    forall (shell : FailingDyadicShell)
      (_hc0Small : shell.c0 <= manuscriptKappa / 16)
      (_hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        DirtyMultiplicityFinFibreInputData
  tower :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        TowerSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  returnPkg :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        ReturnLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  run :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        RunLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  variation :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
      CarryHitGapCanonicalYVariationLeafData
        (appendixNGapCanonicalYCarryLocalAt shell hXge)
        pin.hc0Small
        (supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge)
        (termRun
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves
              (fun shell pin hXge =>
                (tower shell pin hXge).toTowerLocalLeafInputData)
              returnPkg run)
            shell pin hXge))
  terminalAbsorption :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
      ClassicalTerminalN33LeafData
        (GroundedC1VDSplitData.ofVariation
          (variation shell pin hXge).toVariationClassData.toVariationClassData).termMass
        (termDensePack
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves
              (fun shell pin hXge =>
                (tower shell pin hXge).toTowerLocalLeafInputData)
              returnPkg run)
            shell pin hXge))
        (termChernoff
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves
              (fun shell pin hXge =>
                (tower shell pin hXge).toTowerLocalLeafInputData)
              returnPkg run)
            shell pin hXge))
        (termReturn
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves
              (fun shell pin hXge =>
                (tower shell pin hXge).toTowerLocalLeafInputData)
              returnPkg run)
            shell pin hXge))
        (termCnl
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves
              (fun shell pin hXge =>
                (tower shell pin hXge).toTowerLocalLeafInputData)
              returnPkg run)
            shell pin hXge))
        (termTower
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves
              (fun shell pin hXge =>
                (tower shell pin hXge).toTowerLocalLeafInputData)
              returnPkg run)
            shell pin hXge))

namespace GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorDensePackSeparatedDirtySeparatedTowerSeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs

/-- Bundle the separated Tower L.3 leaf and project to the previous small-large
endpoint. -/
def toSmallLargeCarryChernoffSeparatedCNLSelectorDensePackSeparatedDirtySeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs
    (data :
      GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorDensePackSeparatedDirtySeparatedTowerSeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs) :
    GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorDensePackSeparatedDirtySeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs where
  chernoff := data.chernoff
  cnl := data.cnl
  densePack := data.densePack
  dirtyMultiplicity := data.dirtyMultiplicity
  tower := fun shell pin hXge =>
    (data.tower shell pin hXge).toTowerLocalLeafInputData
  returnPkg := data.returnPkg
  run := data.run
  variation := data.variation
  terminalAbsorption := data.terminalAbsorption

/-- Convert the separated Tower L.3 endpoint to the current small-large
two-boundary endpoint. -/
def toSmallLargeShellInputs
    (data :
      GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorDensePackSeparatedDirtySeparatedTowerSeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs) :
    GlobalAppendixNChainCompressionGapCanonicalYSmallLargeShellInputs :=
  data.toSmallLargeCarryChernoffSeparatedCNLSelectorDensePackSeparatedDirtySeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs.toSmallLargeShellInputs

end GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorDensePackSeparatedDirtySeparatedTowerSeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs

set_option linter.unusedVariables false in
/--
Small-large endpoint with the Return M.2/Prop. 23.1 leaf split into its
four-piece return package and final scalar smallness certificate.
-/
structure GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorDensePackSeparatedDirtySeparatedTowerSeparatedReturnSeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs where
  chernoff :
    forall (shell : FailingDyadicShell)
      (hc0Small : shell.c0 <= manuscriptKappa / 16)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        RegularShellPaidChernoff22_1AInputData
          erdos260Constants.cStar erdos260Constants.ξ (shell.X : Real)
  cnl :
    forall (shell : FailingDyadicShell)
      (_hc0Small : shell.c0 <= manuscriptKappa / 16)
      (_hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        CNLSelectorEncodingInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  densePack :
    forall (shell : FailingDyadicShell)
      (_hc0Small : shell.c0 <= manuscriptKappa / 16)
      (_hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        DensePackShellSeparatedSupportInputData shell erdos260Constants.cStar
          erdos260Constants.ξ
  dirtyMultiplicity :
    forall (shell : FailingDyadicShell)
      (_hc0Small : shell.c0 <= manuscriptKappa / 16)
      (_hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        DirtyMultiplicityFinFibreInputData
  tower :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        TowerSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  returnPkg :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        ReturnSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  run :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        RunLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  variation :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
      CarryHitGapCanonicalYVariationLeafData
        (appendixNGapCanonicalYCarryLocalAt shell hXge)
        pin.hc0Small
        (supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge)
        (termRun
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves
              (fun shell pin hXge =>
                (tower shell pin hXge).toTowerLocalLeafInputData)
              (fun shell pin hXge =>
                (returnPkg shell pin hXge).toReturnLocalLeafInputData)
              run)
            shell pin hXge))
  terminalAbsorption :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
      ClassicalTerminalN33LeafData
        (GroundedC1VDSplitData.ofVariation
          (variation shell pin hXge).toVariationClassData.toVariationClassData).termMass
        (termDensePack
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves
              (fun shell pin hXge =>
                (tower shell pin hXge).toTowerLocalLeafInputData)
              (fun shell pin hXge =>
                (returnPkg shell pin hXge).toReturnLocalLeafInputData)
              run)
            shell pin hXge))
        (termChernoff
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves
              (fun shell pin hXge =>
                (tower shell pin hXge).toTowerLocalLeafInputData)
              (fun shell pin hXge =>
                (returnPkg shell pin hXge).toReturnLocalLeafInputData)
              run)
            shell pin hXge))
        (termReturn
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves
              (fun shell pin hXge =>
                (tower shell pin hXge).toTowerLocalLeafInputData)
              (fun shell pin hXge =>
                (returnPkg shell pin hXge).toReturnLocalLeafInputData)
              run)
            shell pin hXge))
        (termCnl
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves
              (fun shell pin hXge =>
                (tower shell pin hXge).toTowerLocalLeafInputData)
              (fun shell pin hXge =>
                (returnPkg shell pin hXge).toReturnLocalLeafInputData)
              run)
            shell pin hXge))
        (termTower
          (appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
            (fun shell hc0Small hXge =>
              (chernoff shell hc0Small hXge).toChernoffStoppedTreeInputData.toGroundedChernoffLocalData)
            (fun shell hc0Small hXge =>
              (cnl shell hc0Small hXge).toGroundedCNLLocalData)
            (fun shell hc0Small hXge =>
              (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
            (fun shell hc0Small hXge =>
              (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
            (appendixNGapCanonicalYTRTLocalLeaves
              (fun shell pin hXge =>
                (tower shell pin hXge).toTowerLocalLeafInputData)
              (fun shell pin hXge =>
                (returnPkg shell pin hXge).toReturnLocalLeafInputData)
              run)
            shell pin hXge))

namespace GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorDensePackSeparatedDirtySeparatedTowerSeparatedReturnSeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs

/-- Bundle the separated Return M.2/Prop. 23.1 leaf and project to the previous
small-large endpoint. -/
def toSmallLargeCarryChernoffSeparatedCNLSelectorDensePackSeparatedDirtySeparatedTowerSeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs
    (data :
      GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorDensePackSeparatedDirtySeparatedTowerSeparatedReturnSeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs) :
    GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorDensePackSeparatedDirtySeparatedTowerSeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs where
  chernoff := data.chernoff
  cnl := data.cnl
  densePack := data.densePack
  dirtyMultiplicity := data.dirtyMultiplicity
  tower := data.tower
  returnPkg := fun shell pin hXge =>
    (data.returnPkg shell pin hXge).toReturnLocalLeafInputData
  run := data.run
  variation := data.variation
  terminalAbsorption := data.terminalAbsorption

/-- Convert the separated Return endpoint to the current small-large
two-boundary endpoint. -/
def toSmallLargeShellInputs
    (data :
      GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorDensePackSeparatedDirtySeparatedTowerSeparatedReturnSeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs) :
    GlobalAppendixNChainCompressionGapCanonicalYSmallLargeShellInputs :=
  data.toSmallLargeCarryChernoffSeparatedCNLSelectorDensePackSeparatedDirtySeparatedTowerSeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs.toSmallLargeShellInputs

end GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorDensePackSeparatedDirtySeparatedTowerSeparatedReturnSeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs

/-- Convert the Lemma 22.1A regular/shell-paid Chernoff leaf at a small-large
shell to the grounded Chernoff package used by the phase core. -/
def appendixNGapCanonicalYRegularShellPaidChernoffToGrounded
    (shell : FailingDyadicShell)
    (_hc0Small : shell.c0 <= manuscriptKappa / 16)
    (_hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
          shell.hnonterm <= shell.X)
    (data :
      RegularShellPaidChernoff22_1AInputData
        erdos260Constants.cStar erdos260Constants.ξ (shell.X : Real)) :
    GroundedChernoffLocalData erdos260Constants.cStar erdos260Constants.ξ
      (shell.X : Real) :=
  data.toGroundedChernoffLocalData

set_option linter.unusedVariables false in
/--
Small-large endpoint with Tower L.3, Return M.2/Prop. 23.1, and Run
L.4.1/L.4.2 all split into their proof-v4 separated leaves.
-/
structure GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorDensePackSeparatedDirtySeparatedTowerSeparatedReturnSeparatedRunSeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs where
  chernoff :
    forall (shell : FailingDyadicShell)
      (hc0Small : shell.c0 <= manuscriptKappa / 16)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        RegularShellPaidChernoff22_1AInputData
          erdos260Constants.cStar erdos260Constants.ξ (shell.X : Real)
  cnl :
    forall (shell : FailingDyadicShell)
      (_hc0Small : shell.c0 <= manuscriptKappa / 16)
      (_hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        CNLSelectorEncodingInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  densePack :
    forall (shell : FailingDyadicShell)
      (_hc0Small : shell.c0 <= manuscriptKappa / 16)
      (_hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        DensePackShellSeparatedSupportInputData shell erdos260Constants.cStar
          erdos260Constants.ξ
  dirtyMultiplicity :
    forall (shell : FailingDyadicShell)
      (_hc0Small : shell.c0 <= manuscriptKappa / 16)
      (_hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        DirtyMultiplicityFinFibreInputData
  tower :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        TowerSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  returnPkg :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        ReturnSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  run :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        RunSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  variation :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
      let phases :=
        appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
          (fun shell hc0Small hXge =>
            (chernoff shell hc0Small hXge).toGroundedChernoffLocalData)
          (fun shell hc0Small hXge =>
            (cnl shell hc0Small hXge).toGroundedCNLLocalData)
          (fun shell hc0Small hXge =>
            (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
          (fun shell hc0Small hXge =>
            (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
          (appendixNGapCanonicalYTRTLocalLeaves
            (fun shell pin hXge =>
              (tower shell pin hXge).toTowerLocalLeafInputData)
            (fun shell pin hXge =>
              (returnPkg shell pin hXge).toReturnLocalLeafInputData)
            (fun shell pin hXge =>
              (run shell pin hXge).toRunLocalLeafInputData))
          shell pin hXge
      CarryHitGapCanonicalYVariationLeafData
        (appendixNGapCanonicalYCarryLocalAt shell hXge)
        pin.hc0Small
        (supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge)
        (termRun phases)
  terminalAbsorption :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
      let phases :=
        appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
          (fun shell hc0Small hXge =>
            (chernoff shell hc0Small hXge).toGroundedChernoffLocalData)
          (fun shell hc0Small hXge =>
            (cnl shell hc0Small hXge).toGroundedCNLLocalData)
          (fun shell hc0Small hXge =>
            (densePack shell hc0Small hXge).toGroundedDensePackLocalData)
          (fun shell hc0Small hXge =>
            (dirtyMultiplicity shell hc0Small hXge).toDirtyMultiplicityData)
          (appendixNGapCanonicalYTRTLocalLeaves
            (fun shell pin hXge =>
              (tower shell pin hXge).toTowerLocalLeafInputData)
            (fun shell pin hXge =>
              (returnPkg shell pin hXge).toReturnLocalLeafInputData)
            (fun shell pin hXge =>
              (run shell pin hXge).toRunLocalLeafInputData))
          shell pin hXge
      ClassicalTerminalN33LeafData
        (GroundedC1VDSplitData.ofVariation
          (variation shell pin hXge).toVariationClassData.toVariationClassData).termMass
        (termDensePack phases)
        (termChernoff phases)
        (termReturn phases)
        (termCnl phases)
        (termTower phases)

namespace GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorDensePackSeparatedDirtySeparatedTowerSeparatedReturnSeparatedRunSeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs

/-- Bundle the separated Run L.4.1/L.4.2 leaf and project to the previous
small-large endpoint. -/
def toSmallLargeCarryChernoffSeparatedCNLSelectorDensePackSeparatedDirtySeparatedTowerSeparatedReturnSeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs
    (data :
      GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorDensePackSeparatedDirtySeparatedTowerSeparatedReturnSeparatedRunSeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs) :
    GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorDensePackSeparatedDirtySeparatedTowerSeparatedReturnSeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs where
  chernoff := data.chernoff
  cnl := data.cnl
  densePack := data.densePack
  dirtyMultiplicity := data.dirtyMultiplicity
  tower := data.tower
  returnPkg := data.returnPkg
  run := fun shell pin hXge =>
    (data.run shell pin hXge).toRunLocalLeafInputData
  variation := data.variation
  terminalAbsorption := data.terminalAbsorption

/-- Convert the separated Run endpoint to the current small-large
two-boundary endpoint. -/
def toSmallLargeShellInputs
    (data :
      GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorDensePackSeparatedDirtySeparatedTowerSeparatedReturnSeparatedRunSeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs) :
    GlobalAppendixNChainCompressionGapCanonicalYSmallLargeShellInputs :=
  data.toSmallLargeCarryChernoffSeparatedCNLSelectorDensePackSeparatedDirtySeparatedTowerSeparatedReturnSeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs.toSmallLargeShellInputs

end GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorDensePackSeparatedDirtySeparatedTowerSeparatedReturnSeparatedRunSeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs

/-- Convert the canonical-`Y`, fixed-`z` Chernoff layer-cake leaf at a
small-large shell to the grounded Chernoff package used by the phase core. -/
def appendixNGapCanonicalYFixedZChernoffToGrounded
    (shell : FailingDyadicShell)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
          shell.hnonterm <= shell.X)
    (data :
      @CarryChernoffCanonicalYFixedZTailSmallInputData shell
        erdos260Constants.cPr erdos260Constants.cStar erdos260Constants.ξ
        (appendixNGapCanonicalYCarryDataAt shell hc0Small hXge)) :
    GroundedChernoffLocalData erdos260Constants.cStar erdos260Constants.ξ
      (shell.X : Real) :=
  (data.toCarryChernoffCanonicalYFixedZLayerCakeTailInputData
    |>.toChernoffStoppedTreeInputData
    (appendixNGapCanonicalYCarryDataAt_Y_nonneg shell hc0Small hXge)).toGroundedChernoffLocalData

/-- Convert the canonical actual-support DensePack construction to the
grounded package used by the phase core.  This removes the final endpoint's
need for a separate K.1 scalar DensePack provider. -/
noncomputable def appendixNGapCanonicalYActualDensePackToGrounded
    (shell : FailingDyadicShell)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
          shell.hnonterm <= shell.X) :=
  (DensePackProofV4ShellGreedyInputData.ofActualSupportWindows shell)
    |>.toGroundedDensePackLocalData
      hc0Small
      (carryLarge_of_appendixNChainCompressionStartThreshold_le hXge)

set_option linter.unusedVariables false in
/--
Small-large endpoint with the N.3.3 terminal leaf split into terminal mass plus
the five non-drop class estimates, after the separated TRT leaves.
-/
structure GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorDensePackSeparatedDirtySeparatedTowerSeparatedReturnSeparatedRunSeparatedTerminalSeparatedTRTLocalLeafVariationKMN2N3Inputs where
  chernoff :
    forall (shell : FailingDyadicShell)
      (hc0Small : shell.c0 <= manuscriptKappa / 16)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        RegularShellPaidChernoff22_1AInputData
          erdos260Constants.cStar erdos260Constants.ξ (shell.X : Real)
  cnl :
    forall (shell : FailingDyadicShell)
      (_hc0Small : shell.c0 <= manuscriptKappa / 16)
      (_hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        CNLStandardWeightedKraftShellInputData shell
          erdos260Constants.cStar erdos260Constants.ξ
  dirtyMultiplicity :
    forall (shell : FailingDyadicShell)
      (_hc0Small : shell.c0 <= manuscriptKappa / 16)
      (_hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        DirtyMultiplicityProofV4ShellFibreInputData shell
  tower :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        TowerSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  returnPkg :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        ReturnSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  run :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        RunSeparatedLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  variation :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
      let phases :=
        appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
          (fun shell hc0Small hXge =>
            (chernoff shell hc0Small hXge).toGroundedChernoffLocalData)
          (fun shell hc0Small hXge =>
            (cnl shell hc0Small hXge).toGroundedCNLLocalData)
          (fun shell hc0Small hXge =>
            appendixNGapCanonicalYActualDensePackToGrounded shell hc0Small hXge)
          (fun shell hc0Small hXge =>
            DirtyMultiplicityProofV4ShellFibreInputData.toDirtyMultiplicityData
              (dirtyMultiplicity shell hc0Small hXge))
          (appendixNGapCanonicalYTRTLocalLeaves
            (fun shell pin hXge =>
              (tower shell pin hXge).toTowerLocalLeafInputData)
            (fun shell pin hXge =>
              (returnPkg shell pin hXge).toReturnLocalLeafInputData)
            (fun shell pin hXge =>
              (run shell pin hXge).toRunLocalLeafInputData))
          shell pin hXge
      CarryHitGapCanonicalYVariationLeafData
        (appendixNGapCanonicalYCarryLocalAt shell hXge)
        pin.hc0Small
        (supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge)
        (termRun phases)
  terminalAbsorption :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
      let phases :=
        appendixNGapCanonicalYSmallLargeSubpackageClosurePhaseData
          (fun shell hc0Small hXge =>
            (chernoff shell hc0Small hXge).toGroundedChernoffLocalData)
          (fun shell hc0Small hXge =>
            (cnl shell hc0Small hXge).toGroundedCNLLocalData)
          (fun shell hc0Small hXge =>
            appendixNGapCanonicalYActualDensePackToGrounded shell hc0Small hXge)
          (fun shell hc0Small hXge =>
            DirtyMultiplicityProofV4ShellFibreInputData.toDirtyMultiplicityData
              (dirtyMultiplicity shell hc0Small hXge))
          (appendixNGapCanonicalYTRTLocalLeaves
            (fun shell pin hXge =>
              (tower shell pin hXge).toTowerLocalLeafInputData)
            (fun shell pin hXge =>
              (returnPkg shell pin hXge).toReturnLocalLeafInputData)
            (fun shell pin hXge =>
              (run shell pin hXge).toRunLocalLeafInputData))
          shell pin hXge
      ClassicalTerminalN33SeparatedLeafData
        (GroundedC1VDSplitData.ofVariation
          (variation shell pin hXge).toVariationClassData.toVariationClassData).termMass
        (termDensePack phases)
        (termChernoff phases)
        (termReturn phases)
        (termCnl phases)
        (termTower phases)

namespace GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorDensePackSeparatedDirtySeparatedTowerSeparatedReturnSeparatedRunSeparatedTerminalSeparatedTRTLocalLeafVariationKMN2N3Inputs

/-- Assemble the proof-v4 pre-TRT phase core at a fixed small-large shell from
the separated Chernoff, CNL, DensePack, and dirty-multiplicity leaves. -/
def phaseCoreAt
    (data :
      GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorDensePackSeparatedDirtySeparatedTowerSeparatedReturnSeparatedRunSeparatedTerminalSeparatedTRTLocalLeafVariationKMN2N3Inputs)
    (shell : FailingDyadicShell)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
          shell.hnonterm <= shell.X) :
    GroundedPreTRTSixPhaseLocalData erdos260Constants.cStar erdos260Constants.ξ
      (shell.X : Real) :=
  appendixNGapCanonicalYSmallLargeSubpackagePhaseCore
    (fun shell hc0Small hXge =>
      (data.chernoff shell hc0Small hXge).toGroundedChernoffLocalData)
    (fun shell hc0Small hXge =>
      (data.cnl shell hc0Small hXge).toGroundedCNLLocalData)
    (fun shell hc0Small hXge =>
      appendixNGapCanonicalYActualDensePackToGrounded shell hc0Small hXge)
    (fun shell hc0Small hXge =>
      DirtyMultiplicityProofV4ShellFibreInputData.toDirtyMultiplicityData
        (data.dirtyMultiplicity shell hc0Small hXge))
    shell hc0Small hXge

/-- Assemble the canonical-`Y` Appendix N chain-compression input at a fixed
small-large shell directly from the proof-v4 leaf packages. -/
def canonicalYChainCompressionAt
    (data :
      GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorDensePackSeparatedDirtySeparatedTowerSeparatedReturnSeparatedRunSeparatedTerminalSeparatedTRTLocalLeafVariationKMN2N3Inputs)
    (shell : FailingDyadicShell)
    (pin : PinnedManuscriptShell shell)
    (hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
          shell.hnonterm <= shell.X) :
    AppendixNTRTChainCompressionCanonicalYInputData
      (appendixNGapCanonicalYSmallLargeSubpackagePhaseCore
        (fun shell hc0Small hXge =>
          (data.chernoff shell hc0Small hXge).toGroundedChernoffLocalData)
        (fun shell hc0Small hXge =>
          (data.cnl shell hc0Small hXge).toGroundedCNLLocalData)
        (fun shell hc0Small hXge =>
          appendixNGapCanonicalYActualDensePackToGrounded shell hc0Small hXge)
        (fun shell hc0Small hXge =>
          DirtyMultiplicityProofV4ShellFibreInputData.toDirtyMultiplicityData
            (data.dirtyMultiplicity shell hc0Small hXge))
        shell pin.hc0Small hXge)
      (appendixNGapCanonicalYCarryLocalAt shell hXge)
      pin.hc0Small
      (supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge) :=
  AppendixNTRTChainCompressionCanonicalYInputData.ofClosedTRTLeafN2N3
    (appendixNGapCanonicalYTRTLocalLeaves
      (fun shell pin hXge =>
        (data.tower shell pin hXge).toTowerLocalLeafInputData)
      (fun shell pin hXge =>
        (data.returnPkg shell pin hXge).toReturnLocalLeafInputData)
      (fun shell pin hXge =>
        (data.run shell pin hXge).toRunLocalLeafInputData)
      shell pin hXge)
    (data.variation shell pin hXge)
    (data.terminalAbsorption shell pin hXge)

/-- Project the fixed-spread proof-v4 DensePack leaf back to the older
shell-separated K.1 interface used by compatibility endpoints. -/
def densePackShellSeparatedAt
    (_data :
      GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorDensePackSeparatedDirtySeparatedTowerSeparatedReturnSeparatedRunSeparatedTerminalSeparatedTRTLocalLeafVariationKMN2N3Inputs)
    (shell : FailingDyadicShell)
    (hc0Small : shell.c0 <= manuscriptKappa / 16)
    (hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
          shell.hnonterm <= shell.X) :
    DensePackShellSeparatedSupportInputData shell erdos260Constants.cStar
      erdos260Constants.ξ :=
  let hCarryLarge :=
    carryLarge_of_appendixNChainCompressionStartThreshold_le hXge
  (((DensePackProofV4ShellGreedyInputData.ofActualSupportWindows shell)
    |>.toDensePackFixedShellSupportInputData
      hc0Small hCarryLarge).toDensePackCanonicalShellSupportInputData
      hCarryLarge).toDensePackShellSeparatedSupportInputData

/-- Bundle the fully separated N.3.3 terminal leaf and project to the previous
small-large endpoint. -/
def toSmallLargeCarryChernoffSeparatedCNLSelectorDensePackSeparatedDirtySeparatedTowerSeparatedReturnSeparatedRunSeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs
    (data :
      GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorDensePackSeparatedDirtySeparatedTowerSeparatedReturnSeparatedRunSeparatedTerminalSeparatedTRTLocalLeafVariationKMN2N3Inputs) :
    GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorDensePackSeparatedDirtySeparatedTowerSeparatedReturnSeparatedRunSeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs where
  chernoff := data.chernoff
  cnl := fun shell hc0Small hXge =>
    (data.cnl shell hc0Small hXge).toCNLSelectorEncodingInputData
  densePack := fun shell hc0Small hXge =>
    data.densePackShellSeparatedAt shell hc0Small hXge
  dirtyMultiplicity := fun shell hc0Small hXge =>
    DirtyMultiplicityProofV4ShellFibreInputData.toDirtyMultiplicityFinFibreInputData
      (data.dirtyMultiplicity shell hc0Small hXge)
  tower := data.tower
  returnPkg := data.returnPkg
  run := data.run
  variation := data.variation
  terminalAbsorption := fun shell pin hXge =>
    (data.terminalAbsorption shell pin hXge).toClassicalTerminalN33LeafData

/-- Convert the fully separated N.3.3 endpoint to the current small-large
two-boundary endpoint. -/
def toSmallLargeShellInputs
    (data :
      GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorDensePackSeparatedDirtySeparatedTowerSeparatedReturnSeparatedRunSeparatedTerminalSeparatedTRTLocalLeafVariationKMN2N3Inputs) :
    GlobalAppendixNChainCompressionGapCanonicalYSmallLargeShellInputs where
  phaseCore := fun shell hc0Small hXge =>
    data.phaseCoreAt shell hc0Small hXge
  chainCompression := fun shell pin hXge =>
    data.canonicalYChainCompressionAt shell pin hXge

end GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorDensePackSeparatedDirtySeparatedTowerSeparatedReturnSeparatedRunSeparatedTerminalSeparatedTRTLocalLeafVariationKMN2N3Inputs

set_option linter.unusedVariables false in
/--
N2/N3-flavored rational-gap endpoint.  This keeps the proof-v4 phase-core
subpackages explicit and splits canonical-Y N.24 into its two manuscript pieces:
N.2.1/N.2.2 variation and N.3.3 terminal absorption.
-/
structure GlobalAppendixNChainCompressionGapCanonicalYN2N3Inputs where
  chernoff :
    forall shell : FailingDyadicShell,
      GroundedChernoffLocalData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real)
  cnl :
    forall shell : FailingDyadicShell,
      GroundedCNLLocalData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real)
  densePack :
    forall shell : FailingDyadicShell,
      GroundedDensePackLocalData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real)
  dirtyMultiplicity :
    forall shell : FailingDyadicShell, DirtyMultiplicityData
  trt :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        GroundedTRTLocalPackageInputData erdos260Constants.cStar
          erdos260Constants.ξ (shell.X : Real)
  variation :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
      CarryHitGapCanonicalYVariationClassData
        (appendixNGapCanonicalYCarryLocal shell hXge)
        pin.hc0Small
        (supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge)
        (termRun
          (appendixNGapCanonicalYSubpackageClosurePhaseData
            chernoff cnl densePack dirtyMultiplicity trt shell pin hXge))
  terminalAbsorption :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
      ClassicalTableRoutedDirectFiveClassTerminalAbsorptionData
        (GroundedC1VDSplitData.ofVariation
          (variation shell pin hXge).toVariationClassData).termMass
        (termDensePack
          (appendixNGapCanonicalYSubpackageClosurePhaseData
            chernoff cnl densePack dirtyMultiplicity trt shell pin hXge))
        (termChernoff
          (appendixNGapCanonicalYSubpackageClosurePhaseData
            chernoff cnl densePack dirtyMultiplicity trt shell pin hXge))
        (termReturn
          (appendixNGapCanonicalYSubpackageClosurePhaseData
            chernoff cnl densePack dirtyMultiplicity trt shell pin hXge))
        (termCnl
          (appendixNGapCanonicalYSubpackageClosurePhaseData
            chernoff cnl densePack dirtyMultiplicity trt shell pin hXge))
        (termTower
          (appendixNGapCanonicalYSubpackageClosurePhaseData
            chernoff cnl densePack dirtyMultiplicity trt shell pin hXge))

namespace GlobalAppendixNChainCompressionGapCanonicalYN2N3Inputs

/-- Assemble the pre-TRT phase core from the explicit proof-v4 subpackages. -/
def phaseCore
    (data : GlobalAppendixNChainCompressionGapCanonicalYN2N3Inputs)
    (shell : FailingDyadicShell) :
    GroundedPreTRTSixPhaseLocalData erdos260Constants.cStar erdos260Constants.ξ
      (shell.X : Real) :=
  appendixNGapCanonicalYSubpackagePhaseCore data.chernoff data.cnl data.densePack
    data.dirtyMultiplicity shell

/-- Assemble canonical-Y N.24 from the N.2 variation and N.3.3 terminal pieces. -/
def n24
    (data : GlobalAppendixNChainCompressionGapCanonicalYN2N3Inputs)
    (shell : FailingDyadicShell)
    (pin : PinnedManuscriptShell shell)
    (hXge :
      appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
          shell.hnonterm <= shell.X) :
    CarryHitGapN24CanonicalYInputData
      (appendixNGapCanonicalYCarryLocal shell hXge)
      pin.hc0Small
      (supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge)
      (termDensePack
        (appendixNGapCanonicalYSubpackageClosurePhaseData
          data.chernoff data.cnl data.densePack data.dirtyMultiplicity
          data.trt shell pin hXge))
      (termChernoff
        (appendixNGapCanonicalYSubpackageClosurePhaseData
          data.chernoff data.cnl data.densePack data.dirtyMultiplicity
          data.trt shell pin hXge))
      (termReturn
        (appendixNGapCanonicalYSubpackageClosurePhaseData
          data.chernoff data.cnl data.densePack data.dirtyMultiplicity
          data.trt shell pin hXge))
      (termCnl
        (appendixNGapCanonicalYSubpackageClosurePhaseData
          data.chernoff data.cnl data.densePack data.dirtyMultiplicity
          data.trt shell pin hXge))
      (termTower
        (appendixNGapCanonicalYSubpackageClosurePhaseData
          data.chernoff data.cnl data.densePack data.dirtyMultiplicity
          data.trt shell pin hXge))
      (termRun
        (appendixNGapCanonicalYSubpackageClosurePhaseData
          data.chernoff data.cnl data.densePack data.dirtyMultiplicity
          data.trt shell pin hXge)) :=
  CarryHitGapN24CanonicalYInputData.ofClosedN2N3
    (data.variation shell pin hXge) (data.terminalAbsorption shell pin hXge)

/-- Convert the N2/N3-flavored endpoint to the N.24-subpackage endpoint. -/
def toSubpackageInputs
    (data : GlobalAppendixNChainCompressionGapCanonicalYN2N3Inputs) :
    GlobalAppendixNChainCompressionGapCanonicalYSubpackageInputs where
  chernoff := data.chernoff
  cnl := data.cnl
  densePack := data.densePack
  dirtyMultiplicity := data.dirtyMultiplicity
  trt := data.trt
  n24 := data.n24

/-- Convert the N2/N3-flavored endpoint to the existing two-package endpoint. -/
def toGapCanonicalYInputs
    (data : GlobalAppendixNChainCompressionGapCanonicalYN2N3Inputs) :
    GlobalAppendixNChainCompressionGapCanonicalYInputs :=
  data.toSubpackageInputs.toGapCanonicalYInputs

end GlobalAppendixNChainCompressionGapCanonicalYN2N3Inputs

set_option linter.unusedVariables false in
/--
Leaf-N2/N3 rational-gap endpoint.  This expands the Pcore Chernoff and CNL
fields to the proof-v4 stopped-tree and selected-transition selector/budget
leaves, while keeping the existing DensePack, dirty-multiplicity, TRT, and
N.2/N.3 canonical-Y leaves explicit.
-/
structure GlobalAppendixNChainCompressionGapCanonicalYLeafN2N3Inputs where
  chernoff :
    forall shell : FailingDyadicShell,
      ChernoffStoppedTreeInputData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real)
  cnl :
    forall shell : FailingDyadicShell,
      CNLSelectorBudgetInputData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real)
  densePack :
    forall shell : FailingDyadicShell,
      GroundedDensePackLocalData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real)
  dirtyMultiplicity :
    forall shell : FailingDyadicShell, DirtyMultiplicityData
  trt :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        GroundedTRTLocalPackageInputData erdos260Constants.cStar
          erdos260Constants.ξ (shell.X : Real)
  variation :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
      CarryHitGapCanonicalYVariationClassData
        (appendixNGapCanonicalYCarryLocal shell hXge)
        pin.hc0Small
        (supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge)
        (termRun
          (appendixNGapCanonicalYSubpackageClosurePhaseData
            (appendixNGapCanonicalYLeafChernoff chernoff)
            (appendixNGapCanonicalYLeafCNL cnl)
            densePack dirtyMultiplicity trt shell pin hXge))
  terminalAbsorption :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
      ClassicalTableRoutedDirectFiveClassTerminalAbsorptionData
        (GroundedC1VDSplitData.ofVariation
          (variation shell pin hXge).toVariationClassData).termMass
        (termDensePack
          (appendixNGapCanonicalYSubpackageClosurePhaseData
            (appendixNGapCanonicalYLeafChernoff chernoff)
            (appendixNGapCanonicalYLeafCNL cnl)
            densePack dirtyMultiplicity trt shell pin hXge))
        (termChernoff
          (appendixNGapCanonicalYSubpackageClosurePhaseData
            (appendixNGapCanonicalYLeafChernoff chernoff)
            (appendixNGapCanonicalYLeafCNL cnl)
            densePack dirtyMultiplicity trt shell pin hXge))
        (termReturn
          (appendixNGapCanonicalYSubpackageClosurePhaseData
            (appendixNGapCanonicalYLeafChernoff chernoff)
            (appendixNGapCanonicalYLeafCNL cnl)
            densePack dirtyMultiplicity trt shell pin hXge))
        (termCnl
          (appendixNGapCanonicalYSubpackageClosurePhaseData
            (appendixNGapCanonicalYLeafChernoff chernoff)
            (appendixNGapCanonicalYLeafCNL cnl)
            densePack dirtyMultiplicity trt shell pin hXge))
        (termTower
          (appendixNGapCanonicalYSubpackageClosurePhaseData
            (appendixNGapCanonicalYLeafChernoff chernoff)
            (appendixNGapCanonicalYLeafCNL cnl)
            densePack dirtyMultiplicity trt shell pin hXge))

namespace GlobalAppendixNChainCompressionGapCanonicalYLeafN2N3Inputs

/-- Convert the leaf-N2/N3 endpoint to the existing N2/N3 endpoint. -/
def toN2N3Inputs
    (data : GlobalAppendixNChainCompressionGapCanonicalYLeafN2N3Inputs) :
    GlobalAppendixNChainCompressionGapCanonicalYN2N3Inputs where
  chernoff := appendixNGapCanonicalYLeafChernoff data.chernoff
  cnl := appendixNGapCanonicalYLeafCNL data.cnl
  densePack := data.densePack
  dirtyMultiplicity := data.dirtyMultiplicity
  trt := data.trt
  variation := data.variation
  terminalAbsorption := data.terminalAbsorption

/-- Convert the leaf-N2/N3 endpoint to the existing two-package endpoint. -/
def toGapCanonicalYInputs
    (data : GlobalAppendixNChainCompressionGapCanonicalYLeafN2N3Inputs) :
    GlobalAppendixNChainCompressionGapCanonicalYInputs :=
  data.toN2N3Inputs.toGapCanonicalYInputs

end GlobalAppendixNChainCompressionGapCanonicalYLeafN2N3Inputs

set_option linter.unusedVariables false in
/--
Leaf-TRT/N2/N3 rational-gap endpoint.  This further expands the TRT package
into its Tower, Return, and Run proof-v4 local packages while retaining the
Chernoff/CNL leaf inputs and the N.2/N.3 canonical-Y split.
-/
structure GlobalAppendixNChainCompressionGapCanonicalYLeafTRTN2N3Inputs where
  chernoff :
    forall shell : FailingDyadicShell,
      ChernoffStoppedTreeInputData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real)
  cnl :
    forall shell : FailingDyadicShell,
      CNLSelectorBudgetInputData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real)
  densePack :
    forall shell : FailingDyadicShell,
      GroundedDensePackLocalData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real)
  dirtyMultiplicity :
    forall shell : FailingDyadicShell, DirtyMultiplicityData
  tower :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        GroundedTowerLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  returnPkg :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        GroundedReturnLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  run :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        GroundedRunLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  variation :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
      CarryHitGapCanonicalYVariationClassData
        (appendixNGapCanonicalYCarryLocal shell hXge)
        pin.hc0Small
        (supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge)
        (termRun
          (appendixNGapCanonicalYSubpackageClosurePhaseData
            (appendixNGapCanonicalYLeafChernoff chernoff)
            (appendixNGapCanonicalYLeafCNL cnl)
            densePack dirtyMultiplicity
            (appendixNGapCanonicalYLeafTRT tower returnPkg run)
            shell pin hXge))
  terminalAbsorption :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
      ClassicalTableRoutedDirectFiveClassTerminalAbsorptionData
        (GroundedC1VDSplitData.ofVariation
          (variation shell pin hXge).toVariationClassData).termMass
        (termDensePack
          (appendixNGapCanonicalYSubpackageClosurePhaseData
            (appendixNGapCanonicalYLeafChernoff chernoff)
            (appendixNGapCanonicalYLeafCNL cnl)
            densePack dirtyMultiplicity
            (appendixNGapCanonicalYLeafTRT tower returnPkg run)
            shell pin hXge))
        (termChernoff
          (appendixNGapCanonicalYSubpackageClosurePhaseData
            (appendixNGapCanonicalYLeafChernoff chernoff)
            (appendixNGapCanonicalYLeafCNL cnl)
            densePack dirtyMultiplicity
            (appendixNGapCanonicalYLeafTRT tower returnPkg run)
            shell pin hXge))
        (termReturn
          (appendixNGapCanonicalYSubpackageClosurePhaseData
            (appendixNGapCanonicalYLeafChernoff chernoff)
            (appendixNGapCanonicalYLeafCNL cnl)
            densePack dirtyMultiplicity
            (appendixNGapCanonicalYLeafTRT tower returnPkg run)
            shell pin hXge))
        (termCnl
          (appendixNGapCanonicalYSubpackageClosurePhaseData
            (appendixNGapCanonicalYLeafChernoff chernoff)
            (appendixNGapCanonicalYLeafCNL cnl)
            densePack dirtyMultiplicity
            (appendixNGapCanonicalYLeafTRT tower returnPkg run)
            shell pin hXge))
        (termTower
          (appendixNGapCanonicalYSubpackageClosurePhaseData
            (appendixNGapCanonicalYLeafChernoff chernoff)
            (appendixNGapCanonicalYLeafCNL cnl)
            densePack dirtyMultiplicity
            (appendixNGapCanonicalYLeafTRT tower returnPkg run)
            shell pin hXge))

namespace GlobalAppendixNChainCompressionGapCanonicalYLeafTRTN2N3Inputs

/-- Convert the leaf-TRT/N2/N3 endpoint to the leaf-N2/N3 endpoint. -/
def toLeafN2N3Inputs
    (data : GlobalAppendixNChainCompressionGapCanonicalYLeafTRTN2N3Inputs) :
    GlobalAppendixNChainCompressionGapCanonicalYLeafN2N3Inputs where
  chernoff := data.chernoff
  cnl := data.cnl
  densePack := data.densePack
  dirtyMultiplicity := data.dirtyMultiplicity
  trt := appendixNGapCanonicalYLeafTRT data.tower data.returnPkg data.run
  variation := data.variation
  terminalAbsorption := data.terminalAbsorption

/-- Convert the leaf-TRT/N2/N3 endpoint to the existing two-package endpoint. -/
def toGapCanonicalYInputs
    (data : GlobalAppendixNChainCompressionGapCanonicalYLeafTRTN2N3Inputs) :
    GlobalAppendixNChainCompressionGapCanonicalYInputs :=
  data.toLeafN2N3Inputs.toGapCanonicalYInputs

end GlobalAppendixNChainCompressionGapCanonicalYLeafTRTN2N3Inputs

set_option linter.unusedVariables false in
/--
K/M-leaf TRT/N2/N3 rational-gap endpoint.  This is the current finest
proof-v4 provider surface for the two residual packages: Chernoff, CNL,
DensePack, dirty multiplicity, TRT, and N.24 are all exposed through their
named leaf interfaces.
-/
structure GlobalAppendixNChainCompressionGapCanonicalYKMLeafTRTN2N3Inputs where
  chernoff :
    forall shell : FailingDyadicShell,
      ChernoffStoppedTreeInputData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real)
  cnl :
    forall shell : FailingDyadicShell,
      CNLSelectorBudgetInputData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real)
  densePack :
    forall shell : FailingDyadicShell,
      DensePackSupportInputData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real)
  dirtyMultiplicity :
    forall shell : FailingDyadicShell, DirtyMultiplicityInputData
  tower :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        GroundedTowerLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  returnPkg :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        GroundedReturnLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  run :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        GroundedRunLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  variation :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
      CarryHitGapCanonicalYVariationClassData
        (appendixNGapCanonicalYCarryLocal shell hXge)
        pin.hc0Small
        (supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge)
        (termRun
          (appendixNGapCanonicalYSubpackageClosurePhaseData
            (appendixNGapCanonicalYLeafChernoff chernoff)
            (appendixNGapCanonicalYLeafCNL cnl)
            (appendixNGapCanonicalYLeafDensePack densePack)
            (appendixNGapCanonicalYLeafDirtyMultiplicity dirtyMultiplicity)
            (appendixNGapCanonicalYLeafTRT tower returnPkg run)
            shell pin hXge))
  terminalAbsorption :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
      ClassicalTableRoutedDirectFiveClassTerminalAbsorptionData
        (GroundedC1VDSplitData.ofVariation
          (variation shell pin hXge).toVariationClassData).termMass
        (termDensePack
          (appendixNGapCanonicalYSubpackageClosurePhaseData
            (appendixNGapCanonicalYLeafChernoff chernoff)
            (appendixNGapCanonicalYLeafCNL cnl)
            (appendixNGapCanonicalYLeafDensePack densePack)
            (appendixNGapCanonicalYLeafDirtyMultiplicity dirtyMultiplicity)
            (appendixNGapCanonicalYLeafTRT tower returnPkg run)
            shell pin hXge))
        (termChernoff
          (appendixNGapCanonicalYSubpackageClosurePhaseData
            (appendixNGapCanonicalYLeafChernoff chernoff)
            (appendixNGapCanonicalYLeafCNL cnl)
            (appendixNGapCanonicalYLeafDensePack densePack)
            (appendixNGapCanonicalYLeafDirtyMultiplicity dirtyMultiplicity)
            (appendixNGapCanonicalYLeafTRT tower returnPkg run)
            shell pin hXge))
        (termReturn
          (appendixNGapCanonicalYSubpackageClosurePhaseData
            (appendixNGapCanonicalYLeafChernoff chernoff)
            (appendixNGapCanonicalYLeafCNL cnl)
            (appendixNGapCanonicalYLeafDensePack densePack)
            (appendixNGapCanonicalYLeafDirtyMultiplicity dirtyMultiplicity)
            (appendixNGapCanonicalYLeafTRT tower returnPkg run)
            shell pin hXge))
        (termCnl
          (appendixNGapCanonicalYSubpackageClosurePhaseData
            (appendixNGapCanonicalYLeafChernoff chernoff)
            (appendixNGapCanonicalYLeafCNL cnl)
            (appendixNGapCanonicalYLeafDensePack densePack)
            (appendixNGapCanonicalYLeafDirtyMultiplicity dirtyMultiplicity)
            (appendixNGapCanonicalYLeafTRT tower returnPkg run)
            shell pin hXge))
        (termTower
          (appendixNGapCanonicalYSubpackageClosurePhaseData
            (appendixNGapCanonicalYLeafChernoff chernoff)
            (appendixNGapCanonicalYLeafCNL cnl)
            (appendixNGapCanonicalYLeafDensePack densePack)
            (appendixNGapCanonicalYLeafDirtyMultiplicity dirtyMultiplicity)
            (appendixNGapCanonicalYLeafTRT tower returnPkg run)
            shell pin hXge))

namespace GlobalAppendixNChainCompressionGapCanonicalYKMLeafTRTN2N3Inputs

/-- Convert the K/M-leaf endpoint to the leaf-TRT/N2/N3 endpoint. -/
def toLeafTRTN2N3Inputs
    (data : GlobalAppendixNChainCompressionGapCanonicalYKMLeafTRTN2N3Inputs) :
    GlobalAppendixNChainCompressionGapCanonicalYLeafTRTN2N3Inputs where
  chernoff := data.chernoff
  cnl := data.cnl
  densePack := appendixNGapCanonicalYLeafDensePack data.densePack
  dirtyMultiplicity :=
    appendixNGapCanonicalYLeafDirtyMultiplicity data.dirtyMultiplicity
  tower := data.tower
  returnPkg := data.returnPkg
  run := data.run
  variation := data.variation
  terminalAbsorption := data.terminalAbsorption

/-- Convert the K/M-leaf endpoint to the existing two-package endpoint. -/
def toGapCanonicalYInputs
    (data : GlobalAppendixNChainCompressionGapCanonicalYKMLeafTRTN2N3Inputs) :
    GlobalAppendixNChainCompressionGapCanonicalYInputs :=
  data.toLeafTRTN2N3Inputs.toGapCanonicalYInputs

end GlobalAppendixNChainCompressionGapCanonicalYKMLeafTRTN2N3Inputs

set_option linter.unusedVariables false in
/--
Variation-leaf K/M TRT endpoint.  This refines the N.2 side of N.24 by exposing
the N.2.1 priority-record and N.2.2 canonical drop-density inputs before they
are packed as `CarryHitGapCanonicalYVariationClassData`.
-/
structure GlobalAppendixNChainCompressionGapCanonicalYVariationLeafKMTRTN2N3Inputs where
  chernoff :
    forall shell : FailingDyadicShell,
      ChernoffStoppedTreeInputData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real)
  cnl :
    forall shell : FailingDyadicShell,
      CNLSelectorBudgetInputData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real)
  densePack :
    forall shell : FailingDyadicShell,
      DensePackSupportInputData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real)
  dirtyMultiplicity :
    forall shell : FailingDyadicShell, DirtyMultiplicityInputData
  tower :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        GroundedTowerLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  returnPkg :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        GroundedReturnLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  run :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        GroundedRunLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  variation :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
      CarryHitGapCanonicalYVariationLeafData
        (appendixNGapCanonicalYCarryLocal shell hXge)
        pin.hc0Small
        (supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge)
        (termRun
          (appendixNGapCanonicalYSubpackageClosurePhaseData
            (appendixNGapCanonicalYLeafChernoff chernoff)
            (appendixNGapCanonicalYLeafCNL cnl)
            (appendixNGapCanonicalYLeafDensePack densePack)
            (appendixNGapCanonicalYLeafDirtyMultiplicity dirtyMultiplicity)
            (appendixNGapCanonicalYLeafTRT tower returnPkg run)
            shell pin hXge))
  terminalAbsorption :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
      ClassicalTableRoutedDirectFiveClassTerminalAbsorptionData
        (GroundedC1VDSplitData.ofVariation
          (variation shell pin hXge).toVariationClassData.toVariationClassData).termMass
        (termDensePack
          (appendixNGapCanonicalYSubpackageClosurePhaseData
            (appendixNGapCanonicalYLeafChernoff chernoff)
            (appendixNGapCanonicalYLeafCNL cnl)
            (appendixNGapCanonicalYLeafDensePack densePack)
            (appendixNGapCanonicalYLeafDirtyMultiplicity dirtyMultiplicity)
            (appendixNGapCanonicalYLeafTRT tower returnPkg run)
            shell pin hXge))
        (termChernoff
          (appendixNGapCanonicalYSubpackageClosurePhaseData
            (appendixNGapCanonicalYLeafChernoff chernoff)
            (appendixNGapCanonicalYLeafCNL cnl)
            (appendixNGapCanonicalYLeafDensePack densePack)
            (appendixNGapCanonicalYLeafDirtyMultiplicity dirtyMultiplicity)
            (appendixNGapCanonicalYLeafTRT tower returnPkg run)
            shell pin hXge))
        (termReturn
          (appendixNGapCanonicalYSubpackageClosurePhaseData
            (appendixNGapCanonicalYLeafChernoff chernoff)
            (appendixNGapCanonicalYLeafCNL cnl)
            (appendixNGapCanonicalYLeafDensePack densePack)
            (appendixNGapCanonicalYLeafDirtyMultiplicity dirtyMultiplicity)
            (appendixNGapCanonicalYLeafTRT tower returnPkg run)
            shell pin hXge))
        (termCnl
          (appendixNGapCanonicalYSubpackageClosurePhaseData
            (appendixNGapCanonicalYLeafChernoff chernoff)
            (appendixNGapCanonicalYLeafCNL cnl)
            (appendixNGapCanonicalYLeafDensePack densePack)
            (appendixNGapCanonicalYLeafDirtyMultiplicity dirtyMultiplicity)
            (appendixNGapCanonicalYLeafTRT tower returnPkg run)
            shell pin hXge))
        (termTower
          (appendixNGapCanonicalYSubpackageClosurePhaseData
            (appendixNGapCanonicalYLeafChernoff chernoff)
            (appendixNGapCanonicalYLeafCNL cnl)
            (appendixNGapCanonicalYLeafDensePack densePack)
            (appendixNGapCanonicalYLeafDirtyMultiplicity dirtyMultiplicity)
            (appendixNGapCanonicalYLeafTRT tower returnPkg run)
            shell pin hXge))

namespace GlobalAppendixNChainCompressionGapCanonicalYVariationLeafKMTRTN2N3Inputs

/-- Convert the variation-leaf endpoint to the K/M-leaf endpoint. -/
def toKMLeafTRTN2N3Inputs
    (data :
      GlobalAppendixNChainCompressionGapCanonicalYVariationLeafKMTRTN2N3Inputs) :
    GlobalAppendixNChainCompressionGapCanonicalYKMLeafTRTN2N3Inputs where
  chernoff := data.chernoff
  cnl := data.cnl
  densePack := data.densePack
  dirtyMultiplicity := data.dirtyMultiplicity
  tower := data.tower
  returnPkg := data.returnPkg
  run := data.run
  variation := fun shell pin hXge =>
    (data.variation shell pin hXge).toVariationClassData
  terminalAbsorption := data.terminalAbsorption

/-- Convert the variation-leaf endpoint to the existing two-package endpoint. -/
def toGapCanonicalYInputs
    (data :
      GlobalAppendixNChainCompressionGapCanonicalYVariationLeafKMTRTN2N3Inputs) :
    GlobalAppendixNChainCompressionGapCanonicalYInputs :=
  data.toKMLeafTRTN2N3Inputs.toGapCanonicalYInputs

end GlobalAppendixNChainCompressionGapCanonicalYVariationLeafKMTRTN2N3Inputs

set_option linter.unusedVariables false in
/--
Terminal-leaf variation/KM/TRT endpoint.  This refines N.3.3 by exposing the
terminal-mass leaf and the five table-routed class-bound leaves before they are
packed as the classical terminal absorption package.
-/
structure GlobalAppendixNChainCompressionGapCanonicalYTerminalLeafVariationKMTRTN2N3Inputs where
  chernoff :
    forall shell : FailingDyadicShell,
      ChernoffStoppedTreeInputData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real)
  cnl :
    forall shell : FailingDyadicShell,
      CNLSelectorBudgetInputData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real)
  densePack :
    forall shell : FailingDyadicShell,
      DensePackSupportInputData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real)
  dirtyMultiplicity :
    forall shell : FailingDyadicShell, DirtyMultiplicityInputData
  tower :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        GroundedTowerLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  returnPkg :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        GroundedReturnLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  run :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        GroundedRunLocalData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  variation :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
      CarryHitGapCanonicalYVariationLeafData
        (appendixNGapCanonicalYCarryLocal shell hXge)
        pin.hc0Small
        (supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge)
        (termRun
          (appendixNGapCanonicalYSubpackageClosurePhaseData
            (appendixNGapCanonicalYLeafChernoff chernoff)
            (appendixNGapCanonicalYLeafCNL cnl)
            (appendixNGapCanonicalYLeafDensePack densePack)
            (appendixNGapCanonicalYLeafDirtyMultiplicity dirtyMultiplicity)
            (appendixNGapCanonicalYLeafTRT tower returnPkg run)
            shell pin hXge))
  terminalAbsorption :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
      ClassicalTerminalN33LeafData
        (GroundedC1VDSplitData.ofVariation
          (variation shell pin hXge).toVariationClassData.toVariationClassData).termMass
        (termDensePack
          (appendixNGapCanonicalYSubpackageClosurePhaseData
            (appendixNGapCanonicalYLeafChernoff chernoff)
            (appendixNGapCanonicalYLeafCNL cnl)
            (appendixNGapCanonicalYLeafDensePack densePack)
            (appendixNGapCanonicalYLeafDirtyMultiplicity dirtyMultiplicity)
            (appendixNGapCanonicalYLeafTRT tower returnPkg run)
            shell pin hXge))
        (termChernoff
          (appendixNGapCanonicalYSubpackageClosurePhaseData
            (appendixNGapCanonicalYLeafChernoff chernoff)
            (appendixNGapCanonicalYLeafCNL cnl)
            (appendixNGapCanonicalYLeafDensePack densePack)
            (appendixNGapCanonicalYLeafDirtyMultiplicity dirtyMultiplicity)
            (appendixNGapCanonicalYLeafTRT tower returnPkg run)
            shell pin hXge))
        (termReturn
          (appendixNGapCanonicalYSubpackageClosurePhaseData
            (appendixNGapCanonicalYLeafChernoff chernoff)
            (appendixNGapCanonicalYLeafCNL cnl)
            (appendixNGapCanonicalYLeafDensePack densePack)
            (appendixNGapCanonicalYLeafDirtyMultiplicity dirtyMultiplicity)
            (appendixNGapCanonicalYLeafTRT tower returnPkg run)
            shell pin hXge))
        (termCnl
          (appendixNGapCanonicalYSubpackageClosurePhaseData
            (appendixNGapCanonicalYLeafChernoff chernoff)
            (appendixNGapCanonicalYLeafCNL cnl)
            (appendixNGapCanonicalYLeafDensePack densePack)
            (appendixNGapCanonicalYLeafDirtyMultiplicity dirtyMultiplicity)
            (appendixNGapCanonicalYLeafTRT tower returnPkg run)
            shell pin hXge))
        (termTower
          (appendixNGapCanonicalYSubpackageClosurePhaseData
            (appendixNGapCanonicalYLeafChernoff chernoff)
            (appendixNGapCanonicalYLeafCNL cnl)
            (appendixNGapCanonicalYLeafDensePack densePack)
            (appendixNGapCanonicalYLeafDirtyMultiplicity dirtyMultiplicity)
            (appendixNGapCanonicalYLeafTRT tower returnPkg run)
            shell pin hXge))

namespace GlobalAppendixNChainCompressionGapCanonicalYTerminalLeafVariationKMTRTN2N3Inputs

/-- Convert the terminal-leaf endpoint to the variation-leaf endpoint. -/
def toVariationLeafKMTRTN2N3Inputs
    (data :
      GlobalAppendixNChainCompressionGapCanonicalYTerminalLeafVariationKMTRTN2N3Inputs) :
    GlobalAppendixNChainCompressionGapCanonicalYVariationLeafKMTRTN2N3Inputs where
  chernoff := data.chernoff
  cnl := data.cnl
  densePack := data.densePack
  dirtyMultiplicity := data.dirtyMultiplicity
  tower := data.tower
  returnPkg := data.returnPkg
  run := data.run
  variation := data.variation
  terminalAbsorption := fun shell pin hXge =>
    (data.terminalAbsorption shell pin hXge).toClassicalTableRoutedDirectFiveClassTerminalAbsorptionData

/-- Convert the terminal-leaf endpoint to the existing two-package endpoint. -/
def toGapCanonicalYInputs
    (data :
      GlobalAppendixNChainCompressionGapCanonicalYTerminalLeafVariationKMTRTN2N3Inputs) :
    GlobalAppendixNChainCompressionGapCanonicalYInputs :=
  data.toVariationLeafKMTRTN2N3Inputs.toGapCanonicalYInputs

end GlobalAppendixNChainCompressionGapCanonicalYTerminalLeafVariationKMTRTN2N3Inputs

set_option linter.unusedVariables false in
/--
TRT-local-leaf terminal/variation/KM endpoint.  This refines the TRT side by
exposing Tower L.3/E.2-E.4, Return Prop. 23.1/M.2, and Run L.4.1/L.4.2 leaves
before they are packed as grounded local data.
-/
structure GlobalAppendixNChainCompressionGapCanonicalYTRTLocalLeafTerminalVariationKMN2N3Inputs where
  chernoff :
    forall shell : FailingDyadicShell,
      ChernoffStoppedTreeInputData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real)
  cnl :
    forall shell : FailingDyadicShell,
      CNLSelectorBudgetInputData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real)
  densePack :
    forall shell : FailingDyadicShell,
      DensePackSupportInputData erdos260Constants.cStar erdos260Constants.ξ
        (shell.X : Real)
  dirtyMultiplicity :
    forall shell : FailingDyadicShell, DirtyMultiplicityInputData
  tower :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        TowerLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  returnPkg :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        ReturnLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  run :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
        RunLocalLeafInputData erdos260Constants.cStar erdos260Constants.ξ
          (shell.X : Real)
  variation :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
      CarryHitGapCanonicalYVariationLeafData
        (appendixNGapCanonicalYCarryLocal shell hXge)
        pin.hc0Small
        (supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXge)
        (termRun
          (appendixNGapCanonicalYSubpackageClosurePhaseData
            (appendixNGapCanonicalYLeafChernoff chernoff)
            (appendixNGapCanonicalYLeafCNL cnl)
            (appendixNGapCanonicalYLeafDensePack densePack)
            (appendixNGapCanonicalYLeafDirtyMultiplicity dirtyMultiplicity)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))
  terminalAbsorption :
    forall (shell : FailingDyadicShell)
      (pin : PinnedManuscriptShell shell)
      (hXge :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X),
      ClassicalTerminalN33LeafData
        (GroundedC1VDSplitData.ofVariation
          (variation shell pin hXge).toVariationClassData.toVariationClassData).termMass
        (termDensePack
          (appendixNGapCanonicalYSubpackageClosurePhaseData
            (appendixNGapCanonicalYLeafChernoff chernoff)
            (appendixNGapCanonicalYLeafCNL cnl)
            (appendixNGapCanonicalYLeafDensePack densePack)
            (appendixNGapCanonicalYLeafDirtyMultiplicity dirtyMultiplicity)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))
        (termChernoff
          (appendixNGapCanonicalYSubpackageClosurePhaseData
            (appendixNGapCanonicalYLeafChernoff chernoff)
            (appendixNGapCanonicalYLeafCNL cnl)
            (appendixNGapCanonicalYLeafDensePack densePack)
            (appendixNGapCanonicalYLeafDirtyMultiplicity dirtyMultiplicity)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))
        (termReturn
          (appendixNGapCanonicalYSubpackageClosurePhaseData
            (appendixNGapCanonicalYLeafChernoff chernoff)
            (appendixNGapCanonicalYLeafCNL cnl)
            (appendixNGapCanonicalYLeafDensePack densePack)
            (appendixNGapCanonicalYLeafDirtyMultiplicity dirtyMultiplicity)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))
        (termCnl
          (appendixNGapCanonicalYSubpackageClosurePhaseData
            (appendixNGapCanonicalYLeafChernoff chernoff)
            (appendixNGapCanonicalYLeafCNL cnl)
            (appendixNGapCanonicalYLeafDensePack densePack)
            (appendixNGapCanonicalYLeafDirtyMultiplicity dirtyMultiplicity)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))
        (termTower
          (appendixNGapCanonicalYSubpackageClosurePhaseData
            (appendixNGapCanonicalYLeafChernoff chernoff)
            (appendixNGapCanonicalYLeafCNL cnl)
            (appendixNGapCanonicalYLeafDensePack densePack)
            (appendixNGapCanonicalYLeafDirtyMultiplicity dirtyMultiplicity)
            (appendixNGapCanonicalYTRTLocalLeaves tower returnPkg run)
            shell pin hXge))

namespace GlobalAppendixNChainCompressionGapCanonicalYTRTLocalLeafTerminalVariationKMN2N3Inputs

/-- Convert the TRT-local-leaf endpoint to the terminal-leaf endpoint. -/
def toTerminalLeafVariationKMTRTN2N3Inputs
    (data :
      GlobalAppendixNChainCompressionGapCanonicalYTRTLocalLeafTerminalVariationKMN2N3Inputs) :
    GlobalAppendixNChainCompressionGapCanonicalYTerminalLeafVariationKMTRTN2N3Inputs where
  chernoff := data.chernoff
  cnl := data.cnl
  densePack := data.densePack
  dirtyMultiplicity := data.dirtyMultiplicity
  tower := fun shell pin hXge => (data.tower shell pin hXge).toGroundedTowerLocalData
  returnPkg := fun shell pin hXge =>
    (data.returnPkg shell pin hXge).toGroundedReturnLocalData
  run := fun shell pin hXge => (data.run shell pin hXge).toGroundedRunLocalData
  variation := data.variation
  terminalAbsorption := data.terminalAbsorption

/-- Convert the TRT-local-leaf endpoint to the existing two-package endpoint. -/
def toGapCanonicalYInputs
    (data :
      GlobalAppendixNChainCompressionGapCanonicalYTRTLocalLeafTerminalVariationKMN2N3Inputs) :
    GlobalAppendixNChainCompressionGapCanonicalYInputs :=
  data.toTerminalLeafVariationKMTRTN2N3Inputs.toGapCanonicalYInputs

end GlobalAppendixNChainCompressionGapCanonicalYTRTLocalLeafTerminalVariationKMN2N3Inputs

/-- Split the current two-boundary rational-gap endpoint back into the finest
proof-v4 leaf endpoint.  This is a lossless projection: each leaf is recovered
from the corresponding grounded package already stored in `phaseCore` or
`chainCompression`. -/
def GlobalAppendixNChainCompressionGapCanonicalYInputs.toTRTLocalLeafTerminalVariationKMN2N3Inputs
    (data : GlobalAppendixNChainCompressionGapCanonicalYInputs) :
    GlobalAppendixNChainCompressionGapCanonicalYTRTLocalLeafTerminalVariationKMN2N3Inputs where
  chernoff := fun shell =>
    (data.phaseCore shell).chernoff.toStoppedTreeInputData
  cnl := fun shell =>
    (data.phaseCore shell).cnl.toSelectorBudgetInputData
  densePack := fun shell =>
    (data.phaseCore shell).densePack.toSupportInputData
  dirtyMultiplicity := fun shell =>
    (data.phaseCore shell).dirtyMultiplicityData.toInputData
  tower := fun shell pin hXge =>
    (data.chainCompression shell pin hXge).trt.tower.toLocalLeafInputData
  returnPkg := fun shell pin hXge =>
    (data.chainCompression shell pin hXge).trt.returnPkg.toLocalLeafInputData
  run := fun shell pin hXge =>
    (data.chainCompression shell pin hXge).trt.run.toLocalLeafInputData
  variation := fun shell pin hXge =>
    (data.chainCompression shell pin hXge).canonicalVariation.toLeafData
  terminalAbsorption := fun shell pin hXge =>
    (data.chainCompression shell pin hXge).terminalAbsorption.toTerminalN33LeafData

/-- Forget the density bridge after projecting it to the raw carry support
supply expected by the original canonical-Y endpoint. -/
def GlobalAppendixNChainCompressionDensityCanonicalYInputs.toCanonicalYInputs
    (data : GlobalAppendixNChainCompressionDensityCanonicalYInputs) :
    GlobalAppendixNChainCompressionCanonicalYInputs where
  carry := fun shell =>
    (data.carryDensity shell).toManuscriptCarrySupportSupplyData
  phaseCore := data.phaseCore
  chainCompression := by
    intro shell pin hXge
    exact data.chainCompression shell pin hXge

/--
Assemble per-failure data from the Appendix N endpoint with canonical carry
budget, variation `Y`, C1-VD/I.9 split, and internally projected terminal
event-state decidability.
-/
def appendixNChainCompressionCanonicalYToAssembly
    (data : GlobalAppendixNChainCompressionCanonicalYInputs) :
    GlobalPerFailureAssembly where
  constants := erdos260Constants
  startThreshold := by
    intro Q d _hQ hd hnonterm _hrational
    exact appendixNChainCompressionStartThreshold Q d hd hnonterm
  perFailureAssembly := by
    intro Q d hQ hd hnonterm hrational X hXdyadic hXge hfailure
    let shell :=
      FailingDyadicShell.ofGlobalConstants erdos260Constants Q d X
        hQ hd hnonterm hrational hXdyadic
        erdos260Constants.c0 erdos260Constants.c0_pos
        manuscriptC0_lt_kappa erdos260Constants.c0_le_cQ hfailure
    let pin : PinnedManuscriptShell shell := { hcQ := rfl, hc0 := rfl }
    have hXgeShell :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X := by
      simpa using hXge
    let h_supportCount_pos :=
      supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXgeShell
    let hCarryLarge :=
      carryLarge_of_appendixNChainCompressionStartThreshold_le hXgeShell
    let carryLocal :=
      (data.carry shell).toThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        (cPr := erdos260Constants.cPr)
        hCarryLarge
    let carryData :=
      carryLocal.toCarryData erdos260Constants_cPr_le_half
        pin.hc0Small h_supportCount_pos
    let chain := data.chainCompression shell pin hXgeShell
    let phases := chain.phases.toSixPhaseFactoryData
    exact
      PerFailureAssemblyData.ofHighExcessCharge phases carryData
        (tableRoutedSplitPhaseAccountedToHighExcessData
          chain.toTableRoutedHighExcessData)

/--
Erdos 260 from the Appendix N chain-compression endpoint with canonical carry
budget, variation `Y`, and C1-VD/I.9 split.
-/
theorem erdos260_final_core_appendix_n_chain_compression_canonical_y
    (data : GlobalAppendixNChainCompressionCanonicalYInputs) :
    Erdos260Statement :=
  erdos260Statement_of_globalPerFailureAssembly
    (appendixNChainCompressionCanonicalYToAssembly data)

/--
Erdos 260 from the density-flavored Appendix N endpoint.  This is the strict
Lean bridge for the planned `Pcarry` reduction: dyadic shell density plus the
large-shell domination condition produces the existing carry support supply.
-/
theorem erdos260_final_core_appendix_n_chain_compression_density_canonical_y
    (data : GlobalAppendixNChainCompressionDensityCanonicalYInputs) :
    Erdos260Statement :=
  erdos260_final_core_appendix_n_chain_compression_canonical_y
    data.toCanonicalYInputs

/-- Assemble per-failure data from the rational-gap-flavored Appendix N endpoint. -/
def appendixNChainCompressionGapCanonicalYToAssembly
    (data : GlobalAppendixNChainCompressionGapCanonicalYInputs) :
    GlobalPerFailureAssembly where
  constants := erdos260Constants
  startThreshold := by
    intro Q d _hQ hd hnonterm _hrational
    exact appendixNChainCompressionStartThreshold Q d hd hnonterm
  perFailureAssembly := by
    intro Q d hQ hd hnonterm hrational X hXdyadic hXge hfailure
    let shell :=
      FailingDyadicShell.ofGlobalConstants erdos260Constants Q d X
        hQ hd hnonterm hrational hXdyadic
        erdos260Constants.c0 erdos260Constants.c0_pos
        manuscriptC0_lt_kappa erdos260Constants.c0_le_cQ hfailure
    let pin : PinnedManuscriptShell shell := { hcQ := rfl, hc0 := rfl }
    have hXgeShell :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X := by
      simpa using hXge
    let h_supportCount_pos :=
      supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXgeShell
    let hCarryLarge :=
      carryLarge_of_appendixNChainCompressionStartThreshold_le hXgeShell
    let carryGap :=
      ManuscriptCarrySupportSupplyData.GapData.ofCarryLarge
        h_supportCount_pos hCarryLarge
    let carryLocal :=
      carryGap.toThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        (cPr := erdos260Constants.cPr)
        h_supportCount_pos
        hCarryLarge
    let carryData :=
      carryLocal.toCarryData erdos260Constants_cPr_le_half
        pin.hc0Small h_supportCount_pos
    let chain := data.chainCompression shell pin hXgeShell
    let phases := chain.phases.toSixPhaseFactoryData
    exact
      PerFailureAssemblyData.ofHighExcessCharge phases carryData
        (tableRoutedSplitPhaseAccountedToHighExcessData
          chain.toTableRoutedHighExcessData)

/--
Assemble per-failure data from the large-shell rational-gap endpoint.  This is
the same final assembly as `appendixNChainCompressionGapCanonicalYToAssembly`,
but it only asks for the pre-TRT phase core at shells satisfying the global
Appendix N start threshold.
-/
def appendixNChainCompressionGapCanonicalYLargeShellToAssembly
    (data : GlobalAppendixNChainCompressionGapCanonicalYLargeShellInputs) :
    GlobalPerFailureAssembly where
  constants := erdos260Constants
  startThreshold := by
    intro Q d _hQ hd hnonterm _hrational
    exact appendixNChainCompressionStartThreshold Q d hd hnonterm
  perFailureAssembly := by
    intro Q d hQ hd hnonterm hrational X hXdyadic hXge hfailure
    let shell :=
      FailingDyadicShell.ofGlobalConstants erdos260Constants Q d X
        hQ hd hnonterm hrational hXdyadic
        erdos260Constants.c0 erdos260Constants.c0_pos
        manuscriptC0_lt_kappa erdos260Constants.c0_le_cQ hfailure
    let pin : PinnedManuscriptShell shell := { hcQ := rfl, hc0 := rfl }
    have hXgeShell :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X := by
      simpa using hXge
    let h_supportCount_pos :=
      supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXgeShell
    let hCarryLarge :=
      carryLarge_of_appendixNChainCompressionStartThreshold_le hXgeShell
    let carryGap :=
      ManuscriptCarrySupportSupplyData.GapData.ofCarryLarge
        h_supportCount_pos hCarryLarge
    let carryLocal :=
      carryGap.toThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        (cPr := erdos260Constants.cPr)
        h_supportCount_pos
        hCarryLarge
    let carryData :=
      carryLocal.toCarryData erdos260Constants_cPr_le_half
        pin.hc0Small h_supportCount_pos
    let chain := data.chainCompression shell pin hXgeShell
    let phases := chain.phases.toSixPhaseFactoryData
    exact
      PerFailureAssemblyData.ofHighExcessCharge phases carryData
        (tableRoutedSplitPhaseAccountedToHighExcessData
          chain.toTableRoutedHighExcessData)

/--
Assemble per-failure data from the small-large-shell rational-gap endpoint.
This is the exact final shell context: the phase core is requested only after
the pinned shell has supplied `hc0Small` and the global start threshold.
-/
def appendixNChainCompressionGapCanonicalYSmallLargeShellToAssembly
    (data : GlobalAppendixNChainCompressionGapCanonicalYSmallLargeShellInputs) :
    GlobalPerFailureAssembly where
  constants := erdos260Constants
  startThreshold := by
    intro Q d _hQ hd hnonterm _hrational
    exact appendixNChainCompressionStartThreshold Q d hd hnonterm
  perFailureAssembly := by
    intro Q d hQ hd hnonterm hrational X hXdyadic hXge hfailure
    let shell :=
      FailingDyadicShell.ofGlobalConstants erdos260Constants Q d X
        hQ hd hnonterm hrational hXdyadic
        erdos260Constants.c0 erdos260Constants.c0_pos
        manuscriptC0_lt_kappa erdos260Constants.c0_le_cQ hfailure
    let pin : PinnedManuscriptShell shell := { hcQ := rfl, hc0 := rfl }
    have hXgeShell :
        appendixNChainCompressionStartThreshold shell.Q shell.d shell.hd
            shell.hnonterm <= shell.X := by
      simpa using hXge
    let h_supportCount_pos :=
      supportCount_pos_of_appendixNChainCompressionStartThreshold_le hXgeShell
    let hCarryLarge :=
      carryLarge_of_appendixNChainCompressionStartThreshold_le hXgeShell
    let carryGap :=
      ManuscriptCarrySupportSupplyData.GapData.ofCarryLarge
        h_supportCount_pos hCarryLarge
    let carryLocal :=
      carryGap.toThresholdControlledStrictFailureBoundedThresholdShellGroundedCarryLocalData
        (cPr := erdos260Constants.cPr)
        h_supportCount_pos
        hCarryLarge
    let carryData :=
      carryLocal.toCarryData erdos260Constants_cPr_le_half
        pin.hc0Small h_supportCount_pos
    let chain := data.chainCompression shell pin hXgeShell
    let phases := chain.phases.toSixPhaseFactoryData
    exact
      PerFailureAssemblyData.ofHighExcessCharge phases carryData
        (tableRoutedSplitPhaseAccountedToHighExcessData
          chain.toTableRoutedHighExcessData)

/--
Erdos 260 from the rational-gap-flavored Appendix N endpoint.  This is the
proof-v4-aligned `Pcarry` reduction: finite shell support supply is projected
from the carry gap bound and large-shell scale.
-/
theorem erdos260_final_core_appendix_n_chain_compression_gap_canonical_y
    (data : GlobalAppendixNChainCompressionGapCanonicalYInputs) :
    Erdos260Statement :=
  erdos260Statement_of_globalPerFailureAssembly
    (appendixNChainCompressionGapCanonicalYToAssembly data)

/--
Erdos 260 from the large-shell rational-gap Appendix N endpoint.  This is the
same proof-v4 assembly, but the `phaseCore` provider is only required on shells
that satisfy the start threshold actually imposed by the global contradiction.
-/
theorem erdos260_final_core_appendix_n_chain_compression_gap_canonical_y_large_shell
    (data : GlobalAppendixNChainCompressionGapCanonicalYLargeShellInputs) :
    Erdos260Statement :=
  erdos260Statement_of_globalPerFailureAssembly
    (appendixNChainCompressionGapCanonicalYLargeShellToAssembly data)

/--
Erdos 260 from the small-large-shell rational-gap Appendix N endpoint.  The
pre-TRT phase core is requested only with the small-failure constant proof and
large-shell threshold available in the final proof context.
-/
theorem erdos260_final_core_appendix_n_chain_compression_gap_canonical_y_small_large_shell
    (data : GlobalAppendixNChainCompressionGapCanonicalYSmallLargeShellInputs) :
    Erdos260Statement :=
  erdos260Statement_of_globalPerFailureAssembly
    (appendixNChainCompressionGapCanonicalYSmallLargeShellToAssembly data)

/-- Erdos 260 from the small-large rational-gap endpoint with the final two
package boundaries expanded into the local proof-v4 subpackages. -/
theorem erdos260_final_core_appendix_n_chain_compression_gap_canonical_y_small_large_subpackages
    (data :
      GlobalAppendixNChainCompressionGapCanonicalYSmallLargeSubpackageInputs) :
    Erdos260Statement :=
  erdos260_final_core_appendix_n_chain_compression_gap_canonical_y_small_large_shell
    data.toSmallLargeShellInputs

/-- Erdos 260 from the small-large rational-gap endpoint with all remaining
local packages expanded to their proof-v4 leaf inputs. -/
theorem erdos260_final_core_appendix_n_chain_compression_gap_canonical_y_small_large_trt_local_leaf_terminal_variation_km_n2n3
    (data :
      GlobalAppendixNChainCompressionGapCanonicalYSmallLargeTRTLocalLeafTerminalVariationKMN2N3Inputs) :
    Erdos260Statement :=
  erdos260_final_core_appendix_n_chain_compression_gap_canonical_y_small_large_shell
    data.toSmallLargeShellInputs

/-- Erdos 260 from the small-large finest leaf endpoint with Chernoff attached
to the concrete carry stopped-tree skeleton. -/
theorem erdos260_final_core_appendix_n_chain_compression_gap_canonical_y_small_large_carry_chernoff_trt_local_leaf_terminal_variation_km_n2n3
    (data :
      GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffTRTLocalLeafTerminalVariationKMN2N3Inputs) :
    Erdos260Statement :=
  erdos260_final_core_appendix_n_chain_compression_gap_canonical_y_small_large_shell
    data.toSmallLargeShellInputs

/-- Erdos 260 from the small-large finest leaf endpoint with carry-specific
Chernoff split into pointwise/moment and scalar tail budget pieces. -/
theorem erdos260_final_core_appendix_n_chain_compression_gap_canonical_y_small_large_carry_chernoff_split_trt_local_leaf_terminal_variation_km_n2n3
    (data :
      GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSplitTRTLocalLeafTerminalVariationKMN2N3Inputs) :
    Erdos260Statement :=
  erdos260_final_core_appendix_n_chain_compression_gap_canonical_y_small_large_shell
    data.toSmallLargeShellInputs

/-- Erdos 260 from the small-large finest leaf endpoint with carry-specific
Chernoff split into pointwise tilt, aggregate moment, and scalar tail budget
pieces. -/
theorem erdos260_final_core_appendix_n_chain_compression_gap_canonical_y_small_large_carry_chernoff_separated_trt_local_leaf_terminal_variation_km_n2n3
    (data :
      GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs) :
    Erdos260Statement :=
  erdos260_final_core_appendix_n_chain_compression_gap_canonical_y_small_large_shell
    data.toSmallLargeShellInputs

/-- Erdos 260 from the small-large finest leaf endpoint with carry-specific
Chernoff separated into the three Lemma 22.1 leaves and CNL separated into the
L.1.1 selector and L.1.2 encoding/budget leaves. -/
theorem erdos260_final_core_appendix_n_chain_compression_gap_canonical_y_small_large_carry_chernoff_separated_cnl_selector_trt_local_leaf_terminal_variation_km_n2n3
    (data :
      GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorTRTLocalLeafTerminalVariationKMN2N3Inputs) :
    Erdos260Statement :=
  erdos260_final_core_appendix_n_chain_compression_gap_canonical_y_small_large_shell
    data.toSmallLargeShellInputs

/-- Erdos 260 from the small-large finest leaf endpoint with carry-specific
Chernoff separated, CNL selector/encoding separated, and K.2.5 dirty
multiplicity split into range-count and per-scale fibre leaves. -/
theorem erdos260_final_core_appendix_n_chain_compression_gap_canonical_y_small_large_carry_chernoff_separated_cnl_selector_dirty_separated_trt_local_leaf_terminal_variation_km_n2n3
    (data :
      GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorDirtySeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs) :
    Erdos260Statement :=
  erdos260_final_core_appendix_n_chain_compression_gap_canonical_y_small_large_shell
    data.toSmallLargeShellInputs

/-- Erdos 260 from the small-large finest leaf endpoint with DensePack K.1
split into cover, shell-packing marker count, and scalar smallness leaves,
alongside the already separated carry-Chernoff/CNL leaves and the Fin-labelled
dirty K.2.5 fibre leaf. -/
theorem erdos260_final_core_appendix_n_chain_compression_gap_canonical_y_small_large_carry_chernoff_separated_cnl_selector_dense_pack_separated_dirty_separated_trt_local_leaf_terminal_variation_km_n2n3
    (data :
      GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorDensePackSeparatedDirtySeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs) :
    Erdos260Statement :=
  erdos260_final_core_appendix_n_chain_compression_gap_canonical_y_small_large_shell
    data.toSmallLargeShellInputs

/-- Erdos 260 from the small-large finest leaf endpoint with Tower L.3 split
into recurrent-cycle, routed-exit, absorption, and scalar smallness leaves. -/
theorem erdos260_final_core_appendix_n_chain_compression_gap_canonical_y_small_large_carry_chernoff_separated_cnl_selector_dense_pack_separated_dirty_separated_tower_separated_trt_local_leaf_terminal_variation_km_n2n3
    (data :
      GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorDensePackSeparatedDirtySeparatedTowerSeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs) :
    Erdos260Statement :=
  erdos260_final_core_appendix_n_chain_compression_gap_canonical_y_small_large_shell
    data.toSmallLargeShellInputs

/-- Erdos 260 from the small-large finest leaf endpoint with Tower L.3 and
Return M.2/Prop. 23.1 both split into their proof-v4 separated leaves. -/
theorem erdos260_final_core_appendix_n_chain_compression_gap_canonical_y_small_large_carry_chernoff_separated_cnl_selector_dense_pack_separated_dirty_separated_tower_separated_return_separated_trt_local_leaf_terminal_variation_km_n2n3
    (data :
      GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorDensePackSeparatedDirtySeparatedTowerSeparatedReturnSeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs) :
    Erdos260Statement :=
  erdos260_final_core_appendix_n_chain_compression_gap_canonical_y_small_large_shell
    data.toSmallLargeShellInputs

/-- Erdos 260 from the small-large finest leaf endpoint with Tower, Return, and
Run all split into their proof-v4 separated leaves. -/
theorem erdos260_final_core_appendix_n_chain_compression_gap_canonical_y_small_large_carry_chernoff_separated_cnl_selector_dense_pack_separated_dirty_separated_tower_separated_return_separated_run_separated_trt_local_leaf_terminal_variation_km_n2n3
    (data :
      GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorDensePackSeparatedDirtySeparatedTowerSeparatedReturnSeparatedRunSeparatedTRTLocalLeafTerminalVariationKMN2N3Inputs) :
    Erdos260Statement :=
  erdos260_final_core_appendix_n_chain_compression_gap_canonical_y_small_large_shell
    data.toSmallLargeShellInputs

/-- Erdos 260 from the small-large finest leaf endpoint with Tower/Return/Run
separated and the N.3.3 terminal absorption leaf split into terminal mass plus
the five non-drop class estimates. -/
theorem erdos260_final_core_appendix_n_chain_compression_gap_canonical_y_small_large_carry_chernoff_separated_cnl_selector_dense_pack_separated_dirty_separated_tower_separated_return_separated_run_separated_terminal_separated_trt_local_leaf_variation_km_n2n3
    (data :
      GlobalAppendixNChainCompressionGapCanonicalYSmallLargeCarryChernoffSeparatedCNLSelectorDensePackSeparatedDirtySeparatedTowerSeparatedReturnSeparatedRunSeparatedTerminalSeparatedTRTLocalLeafVariationKMN2N3Inputs) :
    Erdos260Statement :=
  erdos260_final_core_appendix_n_chain_compression_gap_canonical_y_small_large_shell
    data.toSmallLargeShellInputs

/-- The large-shell endpoint restricts to the small-large-shell endpoint. -/
theorem erdos260_final_core_appendix_n_chain_compression_gap_canonical_y_large_shell_from_small_large_restriction
    (data : GlobalAppendixNChainCompressionGapCanonicalYLargeShellInputs) :
    Erdos260Statement :=
  erdos260_final_core_appendix_n_chain_compression_gap_canonical_y_small_large_shell
    data.toSmallLargeShellInputs

/-- The all-shell rational-gap endpoint restricts to the large-shell endpoint. -/
theorem erdos260_final_core_appendix_n_chain_compression_gap_canonical_y_from_large_shell_restriction
    (data : GlobalAppendixNChainCompressionGapCanonicalYInputs) :
    Erdos260Statement :=
  erdos260_final_core_appendix_n_chain_compression_gap_canonical_y_large_shell
    data.toLargeShellInputs

/--
Erdos 260 from the rational-gap endpoint with the last two proof-v4 packages
expanded into their explicit subpackages.
-/
theorem erdos260_final_core_appendix_n_chain_compression_gap_canonical_y_subpackages
    (data : GlobalAppendixNChainCompressionGapCanonicalYSubpackageInputs) :
    Erdos260Statement :=
  erdos260_final_core_appendix_n_chain_compression_gap_canonical_y
    data.toGapCanonicalYInputs

/--
Erdos 260 from the rational-gap endpoint with canonical-Y N.24 split into its
N.2.1/N.2.2 variation and N.3.3 terminal subpackages.
-/
theorem erdos260_final_core_appendix_n_chain_compression_gap_canonical_y_n2n3
    (data : GlobalAppendixNChainCompressionGapCanonicalYN2N3Inputs) :
    Erdos260Statement :=
  erdos260_final_core_appendix_n_chain_compression_gap_canonical_y
    data.toGapCanonicalYInputs

/--
Erdos 260 from the rational-gap endpoint with Chernoff/CNL expanded to their
stopped-tree and selector-budget leaves, and canonical-Y N.24 split into N.2
and N.3.
-/
theorem erdos260_final_core_appendix_n_chain_compression_gap_canonical_y_leaf_n2n3
    (data : GlobalAppendixNChainCompressionGapCanonicalYLeafN2N3Inputs) :
    Erdos260Statement :=
  erdos260_final_core_appendix_n_chain_compression_gap_canonical_y
    data.toGapCanonicalYInputs

/--
Erdos 260 from the rational-gap endpoint with Chernoff/CNL leaves, TRT split
into Tower/Return/Run, and canonical-Y N.24 split into N.2 and N.3.
-/
theorem erdos260_final_core_appendix_n_chain_compression_gap_canonical_y_leaf_trt_n2n3
    (data : GlobalAppendixNChainCompressionGapCanonicalYLeafTRTN2N3Inputs) :
    Erdos260Statement :=
  erdos260_final_core_appendix_n_chain_compression_gap_canonical_y
    data.toGapCanonicalYInputs

/--
Erdos 260 from the rational-gap endpoint with Chernoff/CNL/DensePack/dirty
K/M leaves, TRT split into Tower/Return/Run, and canonical-Y N.24 split into
N.2 and N.3.
-/
theorem erdos260_final_core_appendix_n_chain_compression_gap_canonical_y_km_leaf_trt_n2n3
    (data : GlobalAppendixNChainCompressionGapCanonicalYKMLeafTRTN2N3Inputs) :
    Erdos260Statement :=
  erdos260_final_core_appendix_n_chain_compression_gap_canonical_y
    data.toGapCanonicalYInputs

/--
Erdos 260 from the rational-gap endpoint with N.2.1/N.2.2 variation leaves,
K/M leaves, TRT split into Tower/Return/Run, and canonical-Y N.24 terminal
absorption.
-/
theorem erdos260_final_core_appendix_n_chain_compression_gap_canonical_y_variation_leaf_km_trt_n2n3
    (data :
      GlobalAppendixNChainCompressionGapCanonicalYVariationLeafKMTRTN2N3Inputs) :
    Erdos260Statement :=
  erdos260_final_core_appendix_n_chain_compression_gap_canonical_y
    data.toGapCanonicalYInputs

/--
Erdos 260 from the rational-gap endpoint with N.3.3 terminal-mass/five-class
leaves, N.2 variation leaves, K/M leaves, and TRT split into Tower/Return/Run.
-/
theorem erdos260_final_core_appendix_n_chain_compression_gap_canonical_y_terminal_leaf_variation_km_trt_n2n3
    (data :
      GlobalAppendixNChainCompressionGapCanonicalYTerminalLeafVariationKMTRTN2N3Inputs) :
    Erdos260Statement :=
  erdos260_final_core_appendix_n_chain_compression_gap_canonical_y
    data.toGapCanonicalYInputs

/--
Erdos 260 from the rational-gap endpoint with Tower/Return/Run local leaves,
N.3.3 terminal leaves, N.2 variation leaves, and K/M leaves.
-/
theorem erdos260_final_core_appendix_n_chain_compression_gap_canonical_y_trt_local_leaf_terminal_variation_km_n2n3
    (data :
      GlobalAppendixNChainCompressionGapCanonicalYTRTLocalLeafTerminalVariationKMN2N3Inputs) :
    Erdos260Statement :=
  erdos260_final_core_appendix_n_chain_compression_gap_canonical_y
    data.toGapCanonicalYInputs

end

end Erdos260
