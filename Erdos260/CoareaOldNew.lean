import Mathlib
import Erdos260.CarryRouting

/-!
# Appendix I.0 — the old/new coarea split on the carry windows (faithful)

This file formalises the manuscript's **§I.0 fibrewise old/new coarea split**
(`proof_v4_unconditional_clean_v5.tex`, eqs. I.0a–I.0d) directly on the **carry
windows**, and proves the part of the I.0d pointwise bound and the K.2a
raw-new-excess inequality that is *genuinely derivable* from the **carry
recurrence**

```
  W_k^{(s)} = W_{k-m}^{(s-m)} + (g_{k-m+1} + ⋯ + g_k)            (eq. I.0/§22, K.2a)
```

together with the **definitions** of the coarea bin `B_b` (I.0a) and the old/new
fibre split `B_b = B_b^old ⊔ B_b^new` (I.0b).

## What is genuinely proved here

* **The carry recurrence** `carryWindow_recurrence`.  The manuscript window
  `W_k^{(s)} = g_{k-s} + ⋯ + g_k` is the forward gap sum `gapWindow g (k-s) s`
  of `Pressure.lean`, and the recurrence is exactly the append/telescoping
  identity `Pressure.gapWindow_append` re-indexed.  Nothing is assumed.

* **The additive excess identity** `carryExcess_recurrence`
  (`E(T) = E_old(T) + S_raw`, the real form of the recurrence), and its
  difference form `carryExcess_sub_oldExcess_eq_newGaps`
  (`E(T) − E_old(T) = g_{k-m+1} + ⋯ + g_k ≥ 0`).  Pure arithmetic over `ℝ`.

* **The I.0a/I.0b coarea split as honest definitions.**  `InCoareaBin` (I.0a),
  `IsOldFibre`/`IsNewFibre` (I.0b).  Because `B_b^new` is *defined* with the I.0d
  condition built in (the manuscript: "the assertion (I.0d) is exactly the
  definition of `B_b^new`", proof of Lemma I.0.1), the **I.0d pointwise bound is
  a definitional projection** `isNewFibre_oldExcess_le`, not an assumption.  The
  split is disjoint (`isOldFibre_isNewFibre_disjoint`), exhaustive over the bin
  (`inCoareaBin_isOldFibre_or_isNewFibre`), and `B_b^new = B_b ∖ B_b^old`
  (`isNewFibre_iff`).

* **The K.2a raw-new-excess inequality** `newFibre_rawExcess_ge` /
  `newFibre_newGaps_ge` (manuscript eq. K.2a, used by Definition K.1.2):
  every active new fibre has new-block excess at least `Y_ν − (1−η)Y`.  This is
  exactly "the old/new decomposition written on the coarea bin" (manuscript
  verification of K.2a): bin-lower `E(T) ≥ Y_ν` (I.0a) plus I.0d
  `E_old(T) ≤ (1−η)Y` plus the additive identity.

* **Reuse of the discrete carry-start model** (`CarryRouting.OldNewSplit`):
  `OldNewSplit.newFibre_rawExcess_ge` derives the same K.2a inequality on the
  high-excess *starts* model, reusing — not duplicating — that structure's I.0d
  primitive `newFibre_Eold_le` and its partition bookkeeping
  (`old_new_disjoint` / `old_new_union` / `highExcessMass_eq_old_add_new`).

## The residual faithful primitive

There is **no `sorry` and no `axiom`**.  The only modelling input is the
*definition* `IsNewFibre` — i.e. the choice that the new fibre `B_b^new` is the
sub-bin on which `E_old(T) ≤ (1−η)Y`.  That is the manuscript's own definition of
`B_b^new`, so I.0d holds *by construction* and everything above (K.2a included) is
derived.  In the discrete `OldNewSplit` model the corresponding primitive is the
clearly-labelled structure field `newFibre_Eold_le` already isolated in
`CarryRouting.lean`; we reuse it directly.

The *geometric* content that genuinely remains deep — that a coarea fibre fails
the old condition for the manuscript's spatial reasons — is upstream of this file
and is precisely what the `B_b^new` definition packages.
-/

namespace Erdos260

open Finset

noncomputable section

variable {g : ℕ → ℕ} {k s m : ℕ}

/-! ## 1.  Carry windows and the carry recurrence

The manuscript carry window `W_k^{(s)} = g_{k-s} + ⋯ + g_k` (eq. §22) is the
forward gap sum `gapWindow g (k-s) s` of `Pressure.lean`.  Writing it with the
block start `k - s` lets the recurrence reduce to `gapWindow_append`. -/

/-- **Manuscript carry window** `W_k^{(s)} = g_{k-s} + ⋯ + g_k`.

It is the forward gap window of `s + 1` gaps anchored so that its last gap is
`g_k`.  With `s ≤ k` the block start is the manuscript index `k - s`. -/
def carryWindow (g : ℕ → ℕ) (k s : ℕ) : ℕ := gapWindow g (k - s) s

/-- **Newly exposed gaps** `S_raw = g_{k-m+1} + ⋯ + g_k` (eq. I.0c'', the new
block of the old/new split).  For `1 ≤ m` this is a window of `m` gaps. -/
def newGaps (g : ℕ → ℕ) (k m : ℕ) : ℕ := gapWindow g (k - m + 1) (m - 1)

/-- **Carry-window excess** `E(T) = W_k^{(s)} − T` (eq. I.0c''/K.1.2).  The full
excess uses `(k, s)`; the old excess `E_old(T) = W_{k-m}^{(s-m)} − T` is the same
function at `(k − m, s − m)`. -/
def carryExcess (g : ℕ → ℕ) (k s : ℕ) (T : ℝ) : ℝ := (carryWindow g k s : ℝ) - T

@[simp] theorem carryExcess_def (g : ℕ → ℕ) (k s : ℕ) (T : ℝ) :
    carryExcess g k s T = (carryWindow g k s : ℝ) - T := rfl

/-- **The carry recurrence** (manuscript eq. after §22 / eq. used in K.2a):

```
  W_k^{(s)} = W_{k-m}^{(s-m)} + (g_{k-m+1} + ⋯ + g_k).
```

Genuinely proved: it is `Pressure.gapWindow_append` re-indexed by the block
start `k - s`, with the index identities discharged by `omega`. -/
theorem carryWindow_recurrence (hm : 1 ≤ m) (hms : m ≤ s) (hsk : s ≤ k) :
    carryWindow g k s = carryWindow g (k - m) (s - m) + newGaps g k m := by
  have e1 : k - m - (s - m) = k - s := by omega
  have e2 : (s - m) + (m - 1) + 1 = s := by omega
  have e3 : (k - s) + (s - m) + 1 = k - m + 1 := by omega
  have happend := gapWindow_append g (k - s) (s - m) (m - 1)
  rw [e2, e3] at happend
  unfold carryWindow newGaps
  rw [e1]
  exact happend

/-- The newly exposed gap mass is nonnegative (it is a `Nat` cast). -/
theorem newGaps_nonneg (g : ℕ → ℕ) (k m : ℕ) : (0 : ℝ) ≤ (newGaps g k m : ℝ) :=
  Nat.cast_nonneg _

/-! ## 2.  The additive excess identity `E = E_old + S_raw`

The real form of the carry recurrence: subtracting `T` from both windows turns the
recurrence into `E(T) = E_old(T) + S_raw`. -/

/-- **Additive excess identity** `E(T) = E_old(T) + (g_{k-m+1} + ⋯ + g_k)`
(eq. I.0/K.2a written on the threshold fibre).  Genuinely provable arithmetic:
the carry recurrence cast to `ℝ`, minus `T`. -/
theorem carryExcess_recurrence (hm : 1 ≤ m) (hms : m ≤ s) (hsk : s ≤ k) (T : ℝ) :
    carryExcess g k s T
      = carryExcess g (k - m) (s - m) T + (newGaps g k m : ℝ) := by
  unfold carryExcess
  rw [carryWindow_recurrence hm hms hsk]
  push_cast
  ring

/-- **Difference form** `E(T) − E_old(T) = g_{k-m+1} + ⋯ + g_k = S_raw`. -/
theorem carryExcess_sub_oldExcess_eq_newGaps
    (hm : 1 ≤ m) (hms : m ≤ s) (hsk : s ≤ k) (T : ℝ) :
    carryExcess g k s T - carryExcess g (k - m) (s - m) T = (newGaps g k m : ℝ) := by
  have h := carryExcess_recurrence (g := g) hm hms hsk T
  linarith

/-- The old excess never exceeds the full excess (the new gaps are nonnegative). -/
theorem oldExcess_le_carryExcess
    (hm : 1 ≤ m) (hms : m ≤ s) (hsk : s ≤ k) (T : ℝ) :
    carryExcess g (k - m) (s - m) T ≤ carryExcess g k s T := by
  have h := carryExcess_recurrence (g := g) hm hms hsk T
  have hpos := newGaps_nonneg g k m
  linarith

/-! ## 3.  The I.0a/I.0b coarea bin and old/new fibre split

We model the threshold fibre `T : ℝ` directly, as the manuscript does.  The
old/new decision (I.0b) is a *measurable condition on the threshold fibre*, not a
branch-level one — exactly the manuscript remark following eq. I.0b. -/

/-- **I.0a coarea bin** `B_b = {T : Y_ν ≤ W_k^{(s)} − T < 2 Y_ν}` (membership). -/
def InCoareaBin (g : ℕ → ℕ) (k s : ℕ) (Yν T : ℝ) : Prop :=
  Yν ≤ carryExcess g k s T ∧ carryExcess g k s T < 2 * Yν

/-- **I.0b old fibre** `B_b^old = {T ∈ B_b : W_{k-m}^{(s-m)} − T > (1−η)Y}`. -/
def IsOldFibre (g : ℕ → ℕ) (k s m : ℕ) (η Y Yν T : ℝ) : Prop :=
  InCoareaBin g k s Yν T ∧ (1 - η) * Y < carryExcess g (k - m) (s - m) T

/-- **I.0b new fibre** `B_b^new = B_b ∖ B_b^old = {T ∈ B_b : W_{k-m}^{(s-m)} − T ≤ (1−η)Y}`.

This *is* the manuscript definition of `B_b^new`: the new-block / non-old
condition is the I.0d inequality, so I.0d is built into the definition. -/
def IsNewFibre (g : ℕ → ℕ) (k s m : ℕ) (η Y Yν T : ℝ) : Prop :=
  InCoareaBin g k s Yν T ∧ carryExcess g (k - m) (s - m) T ≤ (1 - η) * Y

/-- The bin lower bound `E(T) ≥ Y_ν` (I.0a, lower half). -/
theorem InCoareaBin.lower {Yν T : ℝ} (h : InCoareaBin g k s Yν T) :
    Yν ≤ carryExcess g k s T := h.1

/-- The bin upper bound `E(T) < 2 Y_ν` (I.0a, upper half). -/
theorem InCoareaBin.upper {Yν T : ℝ} (h : InCoareaBin g k s Yν T) :
    carryExcess g k s T < 2 * Yν := h.2

/-- A new fibre lies in its coarea bin. -/
theorem InCoareaBin.of_isNewFibre {η Y Yν T : ℝ}
    (h : IsNewFibre g k s m η Y Yν T) : InCoareaBin g k s Yν T := h.1

/-- An old fibre lies in its coarea bin. -/
theorem InCoareaBin.of_isOldFibre {η Y Yν T : ℝ}
    (h : IsOldFibre g k s m η Y Yν T) : InCoareaBin g k s Yν T := h.1

/-- **I.0d pointwise bound** `W_{k-m}^{(s-m)} − T ≤ (1−η)Y` on each new fibre.

Manuscript (proof of Lemma I.0.1): "the assertion (I.0d) is exactly the
definition of `B_b^new`".  Here that is literal — I.0d is the second component of
`IsNewFibre`, hence a genuine projection rather than an assumption. -/
theorem isNewFibre_oldExcess_le {η Y Yν T : ℝ}
    (h : IsNewFibre g k s m η Y Yν T) :
    carryExcess g (k - m) (s - m) T ≤ (1 - η) * Y := h.2

/-- **`B_b^new = B_b ∖ B_b^old`** (eq. I.0b): a new fibre is exactly a bin fibre
on which the old condition fails. -/
theorem isNewFibre_iff {η Y Yν T : ℝ} :
    IsNewFibre g k s m η Y Yν T ↔
      InCoareaBin g k s Yν T ∧
        ¬ ((1 - η) * Y < carryExcess g (k - m) (s - m) T) := by
  simp only [IsNewFibre, not_lt]

/-- **I.0b disjointness:** no fibre is simultaneously old and new. -/
theorem isOldFibre_isNewFibre_disjoint {η Y Yν T : ℝ}
    (hold : IsOldFibre g k s m η Y Yν T)
    (hnew : IsNewFibre g k s m η Y Yν T) : False := by
  have h1 := hold.2
  have h2 := hnew.2
  linarith

/-- **I.0b exhaustiveness:** every bin fibre is old or new, `B_b = B_b^old ⊔ B_b^new`. -/
theorem inCoareaBin_isOldFibre_or_isNewFibre {η Y Yν T : ℝ}
    (h : InCoareaBin g k s Yν T) :
    IsOldFibre g k s m η Y Yν T ∨ IsNewFibre g k s m η Y Yν T := by
  rcases le_or_gt (carryExcess g (k - m) (s - m) T) ((1 - η) * Y) with hle | hlt
  · exact Or.inr ⟨h, hle⟩
  · exact Or.inl ⟨h, hlt⟩

/-! ## 4.  The K.2a raw-new-excess inequality (used by Definition K.1.2)

Manuscript K.2a verification: "(K.2a) is only the old/new decomposition
`W_k^{(s)} = W_{k-m}^{(s-m)} + (g_{k-m+1}+⋯+g_k)` written on the coarea bin."  We
prove it exactly that way: bin-lower (I.0a) + I.0d + the additive identity. -/

/-- **Raw-new-excess from the two defining conditions** (the K.2a kernel):
given the bin lower bound `E(T) ≥ Y_ν` (I.0a) and the new-fibre / I.0d condition
`E_old(T) ≤ (1−η)Y`, the raw new excess is at least `Y_ν − (1−η)Y`. -/
theorem rawExcess_ge_of_bin_of_newCond {η Y Yν T : ℝ}
    (hbin : Yν ≤ carryExcess g k s T)
    (hold : carryExcess g (k - m) (s - m) T ≤ (1 - η) * Y) :
    Yν - (1 - η) * Y ≤ carryExcess g k s T - carryExcess g (k - m) (s - m) T := by
  linarith

/-- **K.2a (excess form)** on a new fibre:
`E(T) − E_old(T) ≥ Y_ν − (1−η)Y`. -/
theorem newFibre_rawExcess_ge {η Y Yν T : ℝ}
    (h : IsNewFibre g k s m η Y Yν T) :
    Yν - (1 - η) * Y ≤ carryExcess g k s T - carryExcess g (k - m) (s - m) T :=
  rawExcess_ge_of_bin_of_newCond h.1.1 h.2

/-- **K.2a in `S_raw` form, from the two defining conditions.**  Using the
additive identity, the new-block gap mass obeys
`g_{k-m+1} + ⋯ + g_k ≥ Y_ν − (1−η)Y`. -/
theorem newGaps_ge_of_bin_of_newCond {η Y Yν T : ℝ}
    (hm : 1 ≤ m) (hms : m ≤ s) (hsk : s ≤ k)
    (hbin : Yν ≤ carryExcess g k s T)
    (hold : carryExcess g (k - m) (s - m) T ≤ (1 - η) * Y) :
    Yν - (1 - η) * Y ≤ (newGaps g k m : ℝ) := by
  have hid := carryExcess_sub_oldExcess_eq_newGaps (g := g) hm hms hsk T
  have hraw := rawExcess_ge_of_bin_of_newCond (g := g) hbin hold
  linarith

/-- **K.2a (`S_raw` form) on a new fibre** (manuscript: "every active new fibre
has new-block excess at least `Y_ν − (1−η)Y`"): the newly exposed gaps satisfy
`g_{k-m+1} + ⋯ + g_k ≥ Y_ν − (1−η)Y`. -/
theorem newFibre_newGaps_ge {η Y Yν T : ℝ}
    (hm : 1 ≤ m) (hms : m ≤ s) (hsk : s ≤ k)
    (h : IsNewFibre g k s m η Y Yν T) :
    Yν - (1 - η) * Y ≤ (newGaps g k m : ℝ) :=
  newGaps_ge_of_bin_of_newCond hm hms hsk h.1.1 h.2

/-! ## 5.  Reuse of the discrete carry-start `OldNewSplit` (no duplication)

`CarryRouting.lean` already isolates the I.0 old/new split on the high-excess
*starts* (`OldNewSplit`), carrying the I.0d pointwise bound as the labelled
primitive field `newFibre_Eold_le` and proving the partition bookkeeping
(`old_new_disjoint` / `old_new_union` / `highExcessMass_eq_old_add_new`).  We do
not re-prove any of that; we only *consume* the primitive to obtain the K.2a
raw-new-excess inequality in that model. -/

/-- **K.2a on the discrete carry-start model.**  For a high-excess start `k`
classified as a *new* fibre (`k ∈ sp.newStarts`), the full window excess exceeds
the old-window excess by at least `Y_ν − (1−η)Y` (here the bin floor `Y_ν` is the
high-excess cutoff `carryData.Y`).

Genuinely derived by *reusing* `OldNewSplit.newFibre_Eold_le` (the I.0d primitive)
and the high-excess membership `mem_highExcessStarts` (the bin lower bound). -/
theorem OldNewSplit.newFibre_rawExcess_ge
    {shell : FailingDyadicShell} {cPr η Y : ℝ}
    {carryData : CarryDataFromFailure shell cPr}
    (sp : OldNewSplit carryData η Y) {k : ℕ} (hk : k ∈ sp.newStarts) :
    carryData.Y - (1 - η) * Y ≤
      windowExcess (hitGap carryData.a) k carryData.r carryData.T - sp.Eold k := by
  simp only [OldNewSplit.newStarts, Finset.mem_filter] at hk
  obtain ⟨hkHigh, hkOld⟩ := hk
  have hYle : carryData.Y ≤
      windowExcess (hitGap carryData.a) k carryData.r carryData.T :=
    (mem_highExcessStarts.1 hkHigh).2
  have hEold : sp.Eold k ≤ (1 - η) * Y := sp.newFibre_Eold_le k hkHigh hkOld
  linarith

end

end Erdos260
