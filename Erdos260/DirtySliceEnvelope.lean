import Erdos260.ReturnCaseSplitRebase
import Erdos260.ReturnCarryEndpointCore
import Erdos260.CarryValuationFloor
import Erdos260.DigitSideClosure

/-!
# The dirty-slice envelope: the honest count mechanism for `SliceDirtyEnvelope`
(`DirtySliceEnvelope`)

This module (NEW; it edits no existing file) attacks the single residual left by the case-split
rebase (`ReturnCaseSplitRebase`): **`SliceDirtyEnvelope ctx`** — dirty-classified slices of the
self-referential key obey the (M.1) envelope `|slice| <= liftLevelBound X`.

## Goal 1 — the in-tree carry dynamics of a same-slice member sequence (the KEY observation)

Same-slice members of the self-referential key `k |-> (carryVal2 k, k mod 2^(carryVal2 k))` share
the carry valuation `v = carryVal2` and are `2^v`-spaced (`sliceMembers_carryVal2_eq`,
`sliceMembers_spaced`).  Between ANY two members `x < z` the digits cannot all vanish — a zero-run
would lift the valuation by the gap (`carryVal2_add_zeroRun`), contradicting equality — so **every
gap contains a `1`-digit** (`slice_gap_one_exists`).  Sharper, with the exact valuation
bookkeeping: at the LAST `1`-digit `j` of the gap the valuation sits exactly `z - j` BELOW the
common level (`slice_gap_valuation_drop`: `carryVal2 j + (z - j) = v`), strictly below whenever
`j < z` (`slice_gap_valuation_lt`) — the valuation drops inside the gap and climbs back to exactly
`v` at `z` through the terminal zero-run.  This is the dirty-witness mechanism of
`SliceDirtyWitness`, made quantitative.

## Goal 1 — the M.2.1 count-mechanism verdict (honest)

* **The nesting (lift-congruence) count is EMPTY here**: the manuscript M.2.1 growth
  `delta_{i+1} >= delta_i + 2^{delta_i}` applies to NONSEPARATED levels; same-slice members have
  EQUAL `carryVal2`, so the nested-chain growth never fires
  (`sliceMembers_no_nesting_growth`: the one-step tower growth is REFUTED on every same-slice
  pair).  The envelope cannot come from the nesting count on this key.
* **The crossing-chain (endpoint-pinning) count degenerates to singletons**: any same-slice pair
  IS a carry crossing (`sliceMembers_carryCrossing`: equal valuations are exactly the equal-level
  crossing case), and for any M.3.2-pinned endpoint (`FactorsThroughKey`, the wave-15/16 `hmono`
  atom of `ReturnCarryEndpointCore`) the crossing-chain ordering forces the slice to be a
  SINGLETON (`selfRef_hmono_forces_singleton`).  So the in-tree transcription of the manuscript
  "crossing chains have length O_Q(1) by endpoint pinning" is, at the self-referential key, the
  capstone injectivity itself — NOT a count strictly between singleton and envelope.  The genuine
  K.2.3 `O_Q(1)` bound lives on Fine–Wilf arm-period-separated semiperiodic patches, formalized
  in-tree only for CONSTRUCTED crossing families (`faithfulDirtyFamily`), with no bridge to actual
  `olcSlice` members (the `DirtyWindowCountCore` finding).
* **What remains and IS provable**: the gap `1`-digits of distinct consecutive gaps sit at
  distinct raw positions inside the window index range `(F, F + W)` (members live in `[F, F + W)`
  by `olcFibre_mem_window`), so the slice count is bounded by the window's raw support —
  candidate (i) of the brief, closed below.

## Goal 2 — the sharpest provable bounds (closed here, unconditional)

* `gapOnes_card_bound` — the counting engine: a finite set inside `[lo, hi)` whose consecutive
  gaps each contain a `1`-digit has at most `#{ones in (lo, hi)} + 1` members.
* `sliceCard_le_windowOnes_succ` — **for EVERY slice of the self-referential key** (dirty or
  clean, every key value `y`): `|slice| <= |returnWindowOnes ctx| + 1`, where
  `returnWindowOnes ctx` is the set of raw positions in `(F, F + W)` carrying digit `1`.
* `returnWindowOnes_card_le_lowScaleSupport` — window ones are sub-ceiling support:
  `|returnWindowOnes| <= supportCount d (F + W)` (`lowScaleCeiling ctx := F + W`); hence the
  headline absolute count `sliceCard_le_lowScaleSupport_succ`:
  `|slice| <= supportCount d (F + W) + 1`.
* `returnWindowOnes_card_le_width_pred` — the trivial interval cap `|returnWindowOnes| <= W - 1`
  (so `|slice| <= W`), the too-big-but-unconditional fallback.
* `returnWindowOnes_subX_hitIndex_lt` — sub-`X` window ones are hits of index `< F` (the wave-10
  localization, quantitative form).

## Goal 2 — the comparison against `liftLevelBound X` and the honest residual atom

`liftLevelBound X <= L + 1` (`returnLiftLevelBound_le`), so the envelope demands `|slice| <= L+1`
while the provable count delivers `supportCount d (F+W) + 1`.  **No in-tree fact bounds
`supportCount` at the low scale `F + W ~ supportCount(X) + W` by `L`**: the failing-shell sparsity
is per-shell `(X, 2X]`; sparsity at lower scales comes only from the all-large-scales bridge
(`counterexample_shellsAtAllLargeScales`, `MultiScaleRigidity`) whose onset is UNCONTROLLED, and
the formalized descent (`DescentDepth*`, `DescentAllDepths`) governs the §25.1 canonical-centre
window matches, not lower-shell support counts.  The gap is therefore packaged as the NEW named
atoms, strictly about sub-shell raw support:

* `ReturnWindowOnesBound ctx` (sharpest): `|returnWindowOnes ctx| + 1 <= liftLevelBound X`;
* `LowScaleSupportBound ctx` (support form, implies the former):
  `supportCount d (F + W) + 1 <= liftLevelBound X`.

Either implies the FULL rebased demand `SliceDirtyEnvelope ctx`
(`sliceDirtyEnvelope_of_windowOnesBound`, `sliceDirtyEnvelope_of_lowScaleSupport`) — indeed the
envelope on ALL slices, not only dirty ones.  Honest placement of the atom:
`lowScaleSupportBound_forces_le_depth` (it demands `supportCount(F+W) <= L`) and
`lowScaleSupportBound_tight_of_ceiling_ge` (if the ceiling reaches `X` the atom pins
`supportCount(F+W) = L` exactly — the carry-rigidity floor; the atom genuinely lives in the
sub-`X` regime).  Complementarity with the wave-8 guard: window-cleanliness makes the bound free
(`returnWindowOnesBound_of_indexWindowClean`), matching the `¬ReturnIndexWindowClean` gate of
`ReturnDirtyEnvelopeQOddField`.

## Goal 3 — the wiring (additive only)

`ReturnCaseSplitChargeResidual.ofWindowOnesBound` / `.ofLowScaleSupport` rebuild the FULL rebased
Return/Class-4 charge residual from the new atom (+ the verbatim `class4Interior` and `hnumeric`
fields), landing on the same ledger floor (`returnFloor_of_windowOnesBound`) and the corrected
M.2.1 per-slice count (`perSliceCount_of_windowOnesBound`, direct — no numeric fields needed);
`dirtyEnvelopeQOddField_of_windowOnesBound` / `_of_lowScaleSupport` discharge the named weaker
target `ReturnDirtyEnvelopeQOddField` of the case-split rebase from the atom.

No `sorry`, no `admit`, no new `axiom`, no `native_decide`; additive only — no existing module is
edited.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 0.  The window bookkeeping

`F = firstIndexAbove X` (the first hit index above the shell scale) and `W = |supportShell|`
(the shell width).  Fibre members live in `[F, F + W)` (`olcFibre_mem_window`); the demanded raw
digit positions of the Return lane live in `(F, F + W]` (the wave-8 finding).  The ceiling
`F + W` is the low-scale support scale of this module. -/

/-- **The low-scale ceiling** `F + W`: the right end of the raw window index range — the scale at
which the dirty-slice count reads the support. -/
def lowScaleCeiling (ctx : ActualFailureContext) : ℕ :=
  ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
    + (supportShell ctx.shell.d ctx.shell.X).card

/-- **The window ones**: the raw positions strictly inside the window index range `(F, F + W)`
carrying digit `1` — the only positions a same-slice gap `1`-digit can occupy. -/
def returnWindowOnes (ctx : ActualFailureContext) : Finset ℕ :=
  (Finset.Ioo (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X)
      (lowScaleCeiling ctx)).filter (fun m => ctx.d m = 1)

/-! ## Part 1.  The same-slice gap dynamics (goal 1 — the KEY observation, formalized)

Same-slice members of the self-referential key share `carryVal2` and are `2^v`-spaced; every gap
carries a `1`-digit, and at the LAST gap `1`-digit the valuation sits exactly `z - j` below the
common level — the valuation drops inside the gap and returns to exactly `v` at the right member
through the terminal zero-run. -/

/-- Same-slice members of the self-referential key share the carry valuation. -/
theorem sliceMembers_carryVal2_eq (ctx : ActualFailureContext) {y x z : ℕ}
    (hx : x ∈ olcSlice ctx (returnSelfRefKey ctx) y)
    (hz : z ∈ olcSlice ctx (returnSelfRefKey ctx) y) :
    carryVal2 ctx x = carryVal2 ctx z :=
  carryVal2_eq_of_returnSelfRefKey_eq ctx
    ((key_eq_of_mem_olcSlice hx).trans (key_eq_of_mem_olcSlice hz).symm)

/-- **Same-slice members are `2^v`-spaced** (the self-referential congruence, slice form):
`2^(carryVal2 x) ∣ (z - x)` for same-slice `x < z`. -/
theorem sliceMembers_spaced (ctx : ActualFailureContext) {y x z : ℕ}
    (hx : x ∈ olcSlice ctx (returnSelfRefKey ctx) y)
    (hz : z ∈ olcSlice ctx (returnSelfRefKey ctx) y) (hxz : x < z) :
    2 ^ carryVal2 ctx x ∣ (z - x) :=
  returnSelfRefKey_gapDiv ctx
    ((key_eq_of_mem_olcSlice hx).trans (key_eq_of_mem_olcSlice hz).symm) hxz

/-- **Every same-slice gap contains a `1`-digit** (parity-free; ANY pair, consecutiveness not
needed): a zero-run on `(x, z]` would lift the valuation by `z - x` (`carryVal2_add_zeroRun`),
contradicting the shared valuation. -/
theorem slice_gap_one_exists (ctx : ActualFailureContext) {y x z : ℕ}
    (hx : x ∈ olcSlice ctx (returnSelfRefKey ctx) y)
    (hz : z ∈ olcSlice ctx (returnSelfRefKey ctx) y) (hxz : x < z) :
    ∃ j, x < j ∧ j ≤ z ∧ ctx.d j = 1 := by
  by_contra h
  have hrun : ∀ j, x < j → j ≤ z → ctx.d j = 0 := by
    intro j h1 h2
    rcases ctx.hd j with h0 | h1'
    · exact h0
    · exact absurd ⟨j, h1, h2, h1'⟩ h
  exact caseSplit_selfRefKey_zeroRun_refuted ctx
    ((key_eq_of_mem_olcSlice hx).trans (key_eq_of_mem_olcSlice hz).symm) hxz hrun

/-- **The gap valuation bookkeeping (exact)**: at the LAST `1`-digit `j` of a same-slice gap the
carry valuation satisfies `carryVal2 j + (z - j) = carryVal2 x` — the valuation sits exactly
`z - j` below the common slice level `v` and climbs back to exactly `v` at `z` through the
terminal zero-run (each `0`-digit lifts the valuation by one). -/
theorem slice_gap_valuation_drop (ctx : ActualFailureContext) {y x z : ℕ}
    (hx : x ∈ olcSlice ctx (returnSelfRefKey ctx) y)
    (hz : z ∈ olcSlice ctx (returnSelfRefKey ctx) y) (hxz : x < z) :
    ∃ j, x < j ∧ j ≤ z ∧ ctx.d j = 1 ∧
      carryVal2 ctx j + (z - j) = carryVal2 ctx x := by
  classical
  obtain ⟨j₀, hj₀x, hj₀z, hj₀1⟩ := slice_gap_one_exists ctx hx hz hxz
  set T : Finset ℕ := (Finset.Ioc x z).filter (fun m => ctx.d m = 1) with hTdef
  have hTne : T.Nonempty :=
    ⟨j₀, Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hj₀x, hj₀z⟩, hj₀1⟩⟩
  obtain ⟨j, hjT, hjmax⟩ : ∃ j, j ∈ T ∧ ∀ i ∈ T, i ≤ j :=
    ⟨T.max' hTne, T.max'_mem hTne, fun i hi => Finset.le_max' T i hi⟩
  have hjmem := Finset.mem_filter.mp hjT
  have hjIoc := Finset.mem_Ioc.mp hjmem.1
  have htail : ∀ i, j < i → i ≤ j + (z - j) → ctx.d i = 0 := by
    intro i h1 h2
    rcases ctx.hd i with h0 | h1'
    · exact h0
    · exfalso
      have hiT : i ∈ T := Finset.mem_filter.mpr
        ⟨Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, h1'⟩
      have hle := hjmax i hiT
      omega
  have hadd := carryVal2_add_zeroRun ctx j (z - j) htail
  rw [show j + (z - j) = z from by omega] at hadd
  have hveq : carryVal2 ctx x = carryVal2 ctx z := sliceMembers_carryVal2_eq ctx hx hz
  exact ⟨j, hjIoc.1, hjIoc.2, hjmem.2, by omega⟩

/-- **The valuation drop, order form**: the gap `1`-digit has valuation at most the slice level,
STRICTLY below it whenever the `1`-digit is interior (`j < z`) — the valuation genuinely drops
inside the gap. -/
theorem slice_gap_valuation_lt (ctx : ActualFailureContext) {y x z : ℕ}
    (hx : x ∈ olcSlice ctx (returnSelfRefKey ctx) y)
    (hz : z ∈ olcSlice ctx (returnSelfRefKey ctx) y) (hxz : x < z) :
    ∃ j, x < j ∧ j ≤ z ∧ ctx.d j = 1 ∧ carryVal2 ctx j ≤ carryVal2 ctx x ∧
      (j < z → carryVal2 ctx j < carryVal2 ctx x) := by
  obtain ⟨j, h1, h2, h3, h4⟩ := slice_gap_valuation_drop ctx hx hz hxz
  exact ⟨j, h1, h2, h3, by omega, fun hjz => by omega⟩

/-! ## Part 2.  The M.2.1 count-mechanism verdict (goal 1 — formalized)

The two manuscript counting mechanisms for the (M.1) envelope, evaluated honestly at the
self-referential key: the nesting (lift-congruence) growth is EMPTY (equal levels), and the
crossing-chain endpoint-pinning bound degenerates to the singleton demand (= the capstone
injectivity), because every same-slice pair IS an equal-level carry crossing while a pinned
endpoint is constant on the slice. -/

/-- **The M.2.1 nesting growth is EMPTY on same-slice members**: the nonseparated-level step
`delta_{i+1} >= delta_i + 2^(delta_i)` of the manuscript nested-chain count is REFUTED on every
same-slice pair — the levels are equal, so the nesting mechanism counts nothing here. -/
theorem sliceMembers_no_nesting_growth (ctx : ActualFailureContext) {y x z : ℕ}
    (hx : x ∈ olcSlice ctx (returnSelfRefKey ctx) y)
    (hz : z ∈ olcSlice ctx (returnSelfRefKey ctx) y) :
    ¬ (carryVal2 ctx x + 2 ^ carryVal2 ctx x ≤ carryVal2 ctx z) := by
  have heq := sliceMembers_carryVal2_eq ctx hx hz
  have hpos : 0 < 2 ^ carryVal2 ctx x := pow_pos (by norm_num : (0 : ℕ) < 2) _
  omega

/-- **Every same-slice pair is an equal-level carry crossing**: same-slice members share the
valuation, so any ordered pair realizes `CarryCrossing` (`carryVal2 z ≤ carryVal2 x`) — the
manuscript's equal-level crossing-chain case is the WHOLE of a multi-member slice. -/
theorem sliceMembers_carryCrossing (ctx : ActualFailureContext) {y x z : ℕ}
    (hx : x ∈ olcSlice ctx (returnSelfRefKey ctx) y)
    (hz : z ∈ olcSlice ctx (returnSelfRefKey ctx) y) (hxz : x < z) :
    CarryCrossing ctx (returnSelfRefKey ctx) y x z :=
  ⟨hx, hz, hxz, le_of_eq (sliceMembers_carryVal2_eq ctx hz hx)⟩

/-- **The endpoint-pinned crossing-chain bound IS the singleton demand at the self-referential
key**: for ANY M.3.2-pinned endpoint (`FactorsThroughKey`), the wave-15/16 crossing-chain
ordering `hmono` forces the slice to a singleton.  The manuscript "crossing chains have length
`O_Q(1)` by endpoint pinning" therefore cannot land strictly between singletons and the envelope
on this key: its in-tree transcription is the capstone injectivity restated, and the genuine
K.2.3 `O_Q(1)` count (Fine–Wilf arm-period separation) exists in-tree only for constructed
crossing families, with no bridge to actual slices. -/
theorem selfRef_hmono_forces_singleton (ctx : ActualFailureContext) {y : ℕ} {endpt : ℕ → ℕ}
    (hfix : FactorsThroughKey (returnSelfRefKey ctx) endpt)
    (hmono : ∀ x z, CarryCrossing ctx (returnSelfRefKey ctx) y x z → endpt x < endpt z) :
    (olcSlice ctx (returnSelfRefKey ctx) y).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  by_contra hne
  rcases Nat.lt_trichotomy a b with hab | hab | hab
  · have hlt := hmono a b (sliceMembers_carryCrossing ctx ha hb hab)
    have heq := pinned_of_factorsThroughKey hfix ctx y a ha b hb
    omega
  · exact hne hab
  · have hlt := hmono b a (sliceMembers_carryCrossing ctx hb ha hab)
    have heq := pinned_of_factorsThroughKey hfix ctx y b hb a ha
    omega

/-! ## Part 3.  The gap-one counting engine (goal 2, candidate (i) — PROVED)

A finite set inside `[lo, hi)` whose consecutive gaps each contain a `1`-digit has at most
`#{ones in (lo, hi)} + 1` members: peel the maximum, charge its gap `1`-digit (which sits at or
above `pred + 1`, outside the recursive window `(lo, pred + 1)`), and recurse. -/

/-- **The counting engine**: consecutive-gap `1`-digits bound the count by the window ones plus
one.  Stated for an arbitrary digit word `d`; the gap hypothesis is demanded only on CONSECUTIVE
pairs. -/
theorem gapOnes_card_bound (d : ℕ → ℕ) :
    ∀ n : ℕ, ∀ S : Finset ℕ, ∀ lo hi : ℕ,
      S.card ≤ n →
      (∀ k ∈ S, lo ≤ k ∧ k < hi) →
      (∀ x ∈ S, ∀ z ∈ S, x < z → (∀ c ∈ S, x < c → z ≤ c) →
        ∃ j, x < j ∧ j ≤ z ∧ d j = 1) →
      S.card ≤ ((Finset.Ioo lo hi).filter (fun m => d m = 1)).card + 1 := by
  intro n
  induction n with
  | zero =>
    intro S lo hi hcard _ _
    omega
  | succ n ih =>
    intro S lo hi hcard hmem hgap
    by_cases hsmall : S.card ≤ 1
    · omega
    · have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
      set M := S.max' hSne with hMdef
      have hMS : M ∈ S := S.max'_mem hSne
      set S' := S.erase M with hS'def
      have hS'card : S'.card = S.card - 1 := Finset.card_erase_of_mem hMS
      have hS'ne : S'.Nonempty := Finset.card_pos.mp (by omega)
      set P := S'.max' hS'ne with hPdef
      have hPS' : P ∈ S' := S'.max'_mem hS'ne
      have hPS : P ∈ S := Finset.mem_of_mem_erase hPS'
      have hPneM : P ≠ M := (Finset.mem_erase.mp hPS').1
      have hPleM : P ≤ M := Finset.le_max' S P hPS
      have hPM : P < M := lt_of_le_of_ne hPleM hPneM
      have hloP : lo ≤ P := (hmem P hPS).1
      have hMhi : M < hi := (hmem M hMS).2
      have hcons : ∀ c ∈ S, P < c → M ≤ c := by
        intro c hcS hPc
        by_cases hcM : c = M
        · exact le_of_eq hcM.symm
        · have hcP : c ≤ P := Finset.le_max' S' c (Finset.mem_erase.mpr ⟨hcM, hcS⟩)
          omega
      obtain ⟨j, hjP, hjM, hj1⟩ := hgap P hPS M hMS hPM hcons
      have hmem' : ∀ k ∈ S', lo ≤ k ∧ k < P + 1 := by
        intro k hk
        have h1 := (hmem k (Finset.mem_of_mem_erase hk)).1
        have h2 : k ≤ P := Finset.le_max' S' k hk
        omega
      have hgap' : ∀ x ∈ S', ∀ z ∈ S', x < z →
          (∀ c ∈ S', x < c → z ≤ c) →
          ∃ j', x < j' ∧ j' ≤ z ∧ d j' = 1 := by
        intro x hx z hz hxz hcons'
        refine hgap x (Finset.mem_of_mem_erase hx) z (Finset.mem_of_mem_erase hz) hxz ?_
        intro c hcS hxc
        by_cases hcM : c = M
        · have hzP := (hmem' z hz).2
          omega
        · exact hcons' c (Finset.mem_erase.mpr ⟨hcM, hcS⟩) hxc
      have hIH := ih S' lo (P + 1) (by omega) hmem' hgap'
      have hjnot : j ∉ (Finset.Ioo lo (P + 1)).filter (fun m => d m = 1) := by
        intro hjmem
        have h2 := (Finset.mem_Ioo.mp (Finset.mem_filter.mp hjmem).1).2
        omega
      have hsub : insert j ((Finset.Ioo lo (P + 1)).filter (fun m => d m = 1))
          ⊆ (Finset.Ioo lo hi).filter (fun m => d m = 1) := by
        intro m hm
        rcases Finset.mem_insert.mp hm with rfl | hm'
        · exact Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨by omega, by omega⟩, hj1⟩
        · obtain ⟨hmIoo, hmd⟩ := Finset.mem_filter.mp hm'
          obtain ⟨hm1, hm2⟩ := Finset.mem_Ioo.mp hmIoo
          exact Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨hm1, by omega⟩, hmd⟩
      have hcardins := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hjnot] at hcardins
      omega

/-! ## Part 4.  The slice count against the window ones (goal 2 — the headline, PROVED)

Every slice of the self-referential key — dirty or clean, at every key value — has at most
`|returnWindowOnes| + 1` members: members live in `[F, F + W)`, gaps carry `1`-digits at distinct
raw positions in `(F, F + W)`. -/

/-- **THE PROVABLE PER-SLICE COUNT**: `|slice| <= #{raw ones in (F, F + W)} + 1`, for EVERY slice
of the self-referential key (no dirtiness or parity hypothesis). -/
theorem sliceCard_le_windowOnes_succ (ctx : ActualFailureContext) (y : ℕ) :
    (olcSlice ctx (returnSelfRefKey ctx) y).card ≤ (returnWindowOnes ctx).card + 1 := by
  refine gapOnes_card_bound ctx.d (olcSlice ctx (returnSelfRefKey ctx) y).card
    (olcSlice ctx (returnSelfRefKey ctx) y)
    (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X)
    (lowScaleCeiling ctx) le_rfl ?_ ?_
  · intro k hk
    have h := olcFibre_mem_window ctx (mem_olcFibre_of_mem_olcSlice hk)
    exact ⟨h.1, h.2⟩
  · intro x hx z hz hxz _
    exact slice_gap_one_exists ctx hx hz hxz

/-! ## Part 5.  The window ones against the low-scale support (goal 2 — localization) -/

/-- Window ones are support elements at the low-scale ceiling: raw positions in `(F, F + W)` with
digit `1` lie in `supportIn d (F + W)`. -/
theorem returnWindowOnes_subset_supportIn (ctx : ActualFailureContext) :
    returnWindowOnes ctx ⊆ supportIn ctx.shell.d (lowScaleCeiling ctx) := by
  intro m hm
  obtain ⟨hmIoo, hmd⟩ := Finset.mem_filter.mp hm
  obtain ⟨h1, h2⟩ := Finset.mem_Ioo.mp hmIoo
  rw [mem_supportIn]
  exact ⟨by omega, by omega, hmd⟩

/-- **The window-ones count is a low-scale support count**:
`|returnWindowOnes| <= supportCount d (F + W)`. -/
theorem returnWindowOnes_card_le_lowScaleSupport (ctx : ActualFailureContext) :
    (returnWindowOnes ctx).card ≤ supportCount ctx.shell.d (lowScaleCeiling ctx) :=
  Finset.card_le_card (returnWindowOnes_subset_supportIn ctx)

/-- The trivial interval cap: `|returnWindowOnes| <= W - 1` (the window has `W - 1` interior
positions) — the unconditional but too-big fallback (`|slice| <= W`). -/
theorem returnWindowOnes_card_le_width_pred (ctx : ActualFailureContext) :
    (returnWindowOnes ctx).card ≤ (supportShell ctx.shell.d ctx.shell.X).card - 1 := by
  have h1 : (returnWindowOnes ctx).card
      ≤ (Finset.Ioo (ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X)
          (lowScaleCeiling ctx)).card :=
    Finset.card_filter_le _ _
  rw [Nat.card_Ioo] at h1
  have hceil : lowScaleCeiling ctx
      = ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
        + (supportShell ctx.shell.d ctx.shell.X).card := rfl
  omega

/-- **The sub-`X` localization (wave-10, quantitative)**: a window one at a position `m <= X` is
a genuine hit of index `< F` — the window ones inject into the pre-window hit indices whenever
the ceiling stays sub-`X`. -/
theorem returnWindowOnes_subX_hitIndex_lt (ctx : ActualFailureContext) {m : ℕ}
    (hm : m ∈ returnWindowOnes ctx) (hmX : m ≤ ctx.shell.X) :
    ∃ j, j < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X ∧
      ctx.n24CarryData.a j = m := by
  obtain ⟨_, hmd⟩ := Finset.mem_filter.mp hm
  obtain ⟨j, hj⟩ := (digitSide_eq_one_iff ctx m).mp hmd
  exact ⟨j, digitSide_hit_index_lt_first ctx hmX hj, hj⟩

/-- The ceiling against the sub-`X` support: `F + W <= supportCount d X + W + 1` — with the
failure sparsity `W < c0 X` this places the ceiling far below `X` unless the sub-`X` support is
nearly full (the wave-8 overflow dichotomy). -/
theorem lowScaleCeiling_le_supportCount_add (ctx : ActualFailureContext) :
    lowScaleCeiling ctx ≤ supportCount ctx.shell.d ctx.shell.X
      + (supportShell ctx.shell.d ctx.shell.X).card + 1 := by
  have h := digitSide_firstIndexAbove_le ctx
  have hceil : lowScaleCeiling ctx
      = ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
        + (supportShell ctx.shell.d ctx.shell.X).card := rfl
  omega

/-- **The headline absolute count (goal 2, closed)**: every slice of the self-referential key has
at most `supportCount d (F + W) + 1` members — the dirty-slice size is bounded by the raw support
at the low scale `F + W`, unconditionally. -/
theorem sliceCard_le_lowScaleSupport_succ (ctx : ActualFailureContext) (y : ℕ) :
    (olcSlice ctx (returnSelfRefKey ctx) y).card
      ≤ supportCount ctx.shell.d (lowScaleCeiling ctx) + 1 := by
  have h1 := sliceCard_le_windowOnes_succ ctx y
  have h2 := returnWindowOnes_card_le_lowScaleSupport ctx
  omega

/-! ## Part 6.  The residual atom and the envelope (goal 2 — the honest conditional)

The provable count delivers `supportCount(F+W) + 1`; the envelope demands `liftLevelBound X`
(`<= L + 1`).  No in-tree fact bounds the low-scale support by `L` (low-scale sparsity has
uncontrolled onset — the all-large-scales bridge; the formalized descent governs window matches,
not lower-shell support).  The gap is the NEW named atom below; either form implies the FULL
rebased demand. -/

/-- **The sharpest residual atom**: the raw window ones fit under the inverse-tower envelope,
`|returnWindowOnes| + 1 <= liftLevelBound X`.  Strictly about sub-shell raw support — no slice,
key, or carry content. -/
def ReturnWindowOnesBound (ctx : ActualFailureContext) : Prop :=
  (returnWindowOnes ctx).card + 1 ≤ liftLevelBound ctx.shell.X

/-- **The support-form residual atom**: the low-scale support count fits under the inverse-tower
envelope, `supportCount d (F + W) + 1 <= liftLevelBound X`.  Implies `ReturnWindowOnesBound`. -/
def LowScaleSupportBound (ctx : ActualFailureContext) : Prop :=
  supportCount ctx.shell.d (lowScaleCeiling ctx) + 1 ≤ liftLevelBound ctx.shell.X

/-- The support-form atom implies the window-ones atom. -/
theorem returnWindowOnesBound_of_lowScaleSupport (ctx : ActualFailureContext)
    (h : LowScaleSupportBound ctx) : ReturnWindowOnesBound ctx := by
  have h1 := returnWindowOnes_card_le_lowScaleSupport ctx
  unfold LowScaleSupportBound at h
  unfold ReturnWindowOnesBound
  omega

/-- **The envelope from the window-ones atom (goal 2, the closure)**: `ReturnWindowOnesBound`
implies the FULL rebased Return-zero demand `SliceDirtyEnvelope` — indeed the (M.1) envelope on
EVERY slice, dirty or clean. -/
theorem sliceDirtyEnvelope_of_windowOnesBound (ctx : ActualFailureContext)
    (h : ReturnWindowOnesBound ctx) : SliceDirtyEnvelope ctx := by
  intro y _ _
  exact le_trans (sliceCard_le_windowOnes_succ ctx y) h

/-- The envelope from the support-form atom. -/
theorem sliceDirtyEnvelope_of_lowScaleSupport (ctx : ActualFailureContext)
    (h : LowScaleSupportBound ctx) : SliceDirtyEnvelope ctx :=
  sliceDirtyEnvelope_of_windowOnesBound ctx (returnWindowOnesBound_of_lowScaleSupport ctx h)

/-- **Honest placement of the atom, I**: the support-form atom demands
`supportCount d (F + W) <= L` (via `liftLevelBound X <= L + 1`). -/
theorem lowScaleSupportBound_forces_le_depth (ctx : ActualFailureContext)
    (h : LowScaleSupportBound ctx) :
    supportCount ctx.shell.d (lowScaleCeiling ctx) ≤ shellLadderDepth ctx := by
  have h1 := returnLiftLevelBound_le ctx
  unfold LowScaleSupportBound at h
  omega

/-- **Honest placement of the atom, II**: if the ceiling reaches the shell scale `X`, the atom
pins the low-scale support to EXACTLY the carry-rigidity floor `L`
(`carryFloor_supportCount_ge_of_le_depth`) — so the atom genuinely lives in the sub-`X` regime,
where no in-tree sparsity controls it (the uncontrolled-onset finding). -/
theorem lowScaleSupportBound_tight_of_ceiling_ge (ctx : ActualFailureContext)
    (h : LowScaleSupportBound ctx) (hge : ctx.shell.X ≤ lowScaleCeiling ctx) :
    supportCount ctx.shell.d (lowScaleCeiling ctx) = shellLadderDepth ctx := by
  have hub := lowScaleSupportBound_forces_le_depth ctx h
  have hlb : shellLadderDepth ctx ≤ supportCount ctx.shell.d (lowScaleCeiling ctx) :=
    le_trans (carryFloor_supportCount_ge_of_le_depth ctx le_rfl)
      (supportCount_mono ctx.shell.d hge)
  omega

/-- Window-cleanliness empties the window ones: under the wave-8 separation guard
`ReturnIndexWindowClean` there are NO raw ones in `(F, F + W)`. -/
theorem returnWindowOnes_eq_empty_of_indexWindowClean (ctx : ActualFailureContext)
    (h : ReturnIndexWindowClean ctx) : returnWindowOnes ctx = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro m hm
  obtain ⟨hmIoo, hmd⟩ := Finset.mem_filter.mp hm
  obtain ⟨h1, h2⟩ := Finset.mem_Ioo.mp hmIoo
  have hceil : lowScaleCeiling ctx
      = ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
        + (supportShell ctx.shell.d ctx.shell.X).card := rfl
  have h0 := h m h1 (by omega)
  omega

/-- **Complementarity with the wave-8 guard**: window-cleanliness makes the window-ones atom
FREE (`one_le_liftLevelBound`) — the atom is demanded only where the dirty field's
`¬ReturnIndexWindowClean` gate already places the context. -/
theorem returnWindowOnesBound_of_indexWindowClean (ctx : ActualFailureContext)
    (h : ReturnIndexWindowClean ctx) : ReturnWindowOnesBound ctx := by
  unfold ReturnWindowOnesBound
  rw [returnWindowOnes_eq_empty_of_indexWindowClean ctx h, Finset.card_empty]
  simpa using one_le_liftLevelBound ctx.shell.X

/-! ## Part 7.  The wiring into the charge interface (goal 3 — additive only)

The new atom rebuilds the FULL rebased Return/Class-4 charge residual of the case-split rebase,
landing on the same ledger floor and the corrected M.2.1 per-slice count; the named weaker target
`ReturnDirtyEnvelopeQOddField` discharges from the atom. -/

/-- **The rebased charge residual from the window-ones atom**: `ReturnWindowOnesBound` plus the
verbatim `class4Interior` / `hnumeric` fields rebuild `ReturnCaseSplitChargeResidual` — the whole
dirty-envelope field is supplied by the gap-one count. -/
def ReturnCaseSplitChargeResidual.ofWindowOnesBound (ctx : ActualFailureContext)
    (hones : ReturnWindowOnesBound ctx)
    (hInterior : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4,
      k + ctx.n24CarryData.r + 1
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card)
    (hnumeric : (((olcFibre ctx).image (returnSelfRefKey ctx)).card : ℝ)
        * (liftLevelBound ctx.shell.X : ℝ) * returnDyadicMult ctx
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    ReturnCaseSplitChargeResidual ctx where
  dirtyEnvelope := sliceDirtyEnvelope_of_windowOnesBound ctx hones
  class4Interior := hInterior
  hnumeric := hnumeric

/-- The rebased charge residual from the support-form atom. -/
def ReturnCaseSplitChargeResidual.ofLowScaleSupport (ctx : ActualFailureContext)
    (hlow : LowScaleSupportBound ctx)
    (hInterior : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4,
      k + ctx.n24CarryData.r + 1
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card)
    (hnumeric : (((olcFibre ctx).image (returnSelfRefKey ctx)).card : ℝ)
        * (liftLevelBound ctx.shell.X : ℝ) * returnDyadicMult ctx
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    ReturnCaseSplitChargeResidual ctx :=
  ReturnCaseSplitChargeResidual.ofWindowOnesBound ctx
    (returnWindowOnesBound_of_lowScaleSupport ctx hlow) hInterior hnumeric

/-- **The Return capacity floor from the atom** — the SAME class-4 ledger contribution the (Z)
route delivers, now from the gap-one count plus the residual atom. -/
theorem returnFloor_of_windowOnesBound (ctx : ActualFailureContext)
    (hones : ReturnWindowOnesBound ctx)
    (hInterior : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4,
      k + ctx.n24CarryData.r + 1
        < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
            + (supportShell ctx.shell.d ctx.shell.X).card)
    (hnumeric : (((olcFibre ctx).image (returnSelfRefKey ctx)).card : ℝ)
        * (liftLevelBound ctx.shell.X : ℝ) * returnDyadicMult ctx
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 4
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  (ReturnCaseSplitChargeResidual.ofWindowOnesBound ctx hones hInterior hnumeric).returnFloor

/-- **The corrected M.2.1 per-slice count from the atom alone** (no numeric or interior fields):
`|fibre| <= #keys * liftLevelBound X`. -/
theorem perSliceCount_of_windowOnesBound (ctx : ActualFailureContext)
    (hones : ReturnWindowOnesBound ctx) :
    (olcFibre ctx).card
      ≤ ((olcFibre ctx).image (returnSelfRefKey ctx)).card * liftLevelBound ctx.shell.X :=
  routedFibre4_card_le_of_slices ctx (returnSelfRefKey ctx)
    (caseSplitSlices ctx (sliceDirtyEnvelope_of_windowOnesBound ctx hones))

/-- **The named weaker target of the case-split rebase, discharged from the atom**: a per-context
window-ones bound (at Q odd) yields `ReturnDirtyEnvelopeQOddField`. -/
theorem dirtyEnvelopeQOddField_of_windowOnesBound
    (h : ∀ ctx : ActualFailureContext, ctx.Q % 2 = 1 → ReturnWindowOnesBound ctx) :
    ReturnDirtyEnvelopeQOddField :=
  fun ctx _hA _hB _hC _hD hQ => sliceDirtyEnvelope_of_windowOnesBound ctx (h ctx hQ)

/-- The named weaker target from the support-form atom. -/
theorem dirtyEnvelopeQOddField_of_lowScaleSupport
    (h : ∀ ctx : ActualFailureContext, ctx.Q % 2 = 1 → LowScaleSupportBound ctx) :
    ReturnDirtyEnvelopeQOddField :=
  fun ctx _hA _hB _hC _hD hQ => sliceDirtyEnvelope_of_lowScaleSupport ctx (h ctx hQ)

/-! ## Part 8.  Machine-readable status (honest) -/

/-- Honest machine-readable status of the dirty-slice envelope pass. -/
def dirtySliceEnvelopeStatus : List String :=
  [ "SUBJECT: SliceDirtyEnvelope (ReturnCaseSplitRebase) - dirty-classified slices of the " ++
      "self-referential key obey the (M.1) envelope |slice| <= liftLevelBound X.  This module " ++
      "formalizes the honest count mechanism and reduces the envelope to a NEW named atom " ++
      "strictly about sub-shell raw support.",
    "GOAL 1 CLOSED (the in-tree gap dynamics): same-slice members share carryVal2 " ++
      "(sliceMembers_carryVal2_eq) and are 2^v-spaced (sliceMembers_spaced); EVERY same-slice " ++
      "gap contains a 1-digit (slice_gap_one_exists, parity-free, any pair); at the LAST gap " ++
      "1-digit the valuation sits exactly z-j below the slice level and returns to exactly v " ++
      "at the right member through the terminal zero-run (slice_gap_valuation_drop: " ++
      "carryVal2 j + (z-j) = v; strict drop for interior j, slice_gap_valuation_lt).",
    "GOAL 1 VERDICT (the M.2.1 count mechanisms, honest): (a) the nested-chain lift-congruence " ++
      "growth delta' >= delta + 2^delta is EMPTY on same-slice members - equal levels refute " ++
      "the step outright (sliceMembers_no_nesting_growth); (b) every same-slice pair IS an " ++
      "equal-level carry crossing (sliceMembers_carryCrossing), and for ANY M.3.2-pinned " ++
      "endpoint the wave-15/16 crossing-chain ordering hmono forces SINGLETONS " ++
      "(selfRef_hmono_forces_singleton) - the in-tree endpoint-pinning transcription of the " ++
      "manuscript's O_Q(1) crossing-chain bound (K.2.3, M.2.1 remark) is the capstone " ++
      "injectivity restated at this key, NOT a count strictly between singleton and envelope; " ++
      "the genuine K.2.3 O_Q(1) needs Fine-Wilf arm-period separation on real semiperiodic " ++
      "patches, in-tree only for CONSTRUCTED families (faithfulDirtyFamily) with no bridge to " ++
      "actual olcSlice members (the DirtyWindowCountCore finding).",
    "GOAL 2 CLOSED (the sharpest provable bounds, unconditional): the counting engine " ++
      "gapOnes_card_bound (consecutive-gap 1-digits inject into window ones); " ++
      "sliceCard_le_windowOnes_succ: |slice| <= |returnWindowOnes| + 1 for EVERY slice of the " ++
      "self-referential key (returnWindowOnes = raw 1-positions in (F, F+W), F = " ++
      "firstIndexAbove X, W = |supportShell|; members live in [F, F+W) by olcFibre_mem_window); " ++
      "returnWindowOnes_card_le_lowScaleSupport: window ones <= supportCount d (F+W) " ++
      "(lowScaleCeiling); HEADLINE sliceCard_le_lowScaleSupport_succ: |slice| <= " ++
      "supportCount d (F+W) + 1; fallback returnWindowOnes_card_le_width_pred: <= W - 1 " ++
      "(too big: W ~ c0 X); sub-X localization returnWindowOnes_subX_hitIndex_lt (window ones " ++
      "at positions <= X are hits of index < F).",
    "GOAL 2 RESIDUAL (the honest conditional): comparing against liftLevelBound X <= L + 1 " ++
      "(returnLiftLevelBound_le) requires supportCount d (F+W) <= L, which NO in-tree fact " ++
      "supplies - the failing-shell sparsity is per-shell (X, 2X]; lower scales are covered " ++
      "only by the all-large-scales bridge (counterexample_shellsAtAllLargeScales, " ++
      "MultiScaleRigidity) with UNCONTROLLED onset, and the formalized descent " ++
      "(DescentDepth*/DescentAllDepths) governs the 25.1 canonical-centre window matches, not " ++
      "lower-shell support.  NEW NAMED ATOMS: ReturnWindowOnesBound (sharpest: " ++
      "|returnWindowOnes| + 1 <= liftLevelBound X) and LowScaleSupportBound (support form: " ++
      "supportCount d (F+W) + 1 <= liftLevelBound X); either implies the FULL rebased demand " ++
      "(sliceDirtyEnvelope_of_windowOnesBound / _of_lowScaleSupport - on ALL slices, not only " ++
      "dirty).  Honest placement: the atom demands supportCount(F+W) <= L " ++
      "(lowScaleSupportBound_forces_le_depth), pins it to EXACTLY the carry-rigidity floor L " ++
      "if the ceiling reaches X (lowScaleSupportBound_tight_of_ceiling_ge) - the atom lives in " ++
      "the sub-X regime; window-cleanliness makes it free " ++
      "(returnWindowOnesBound_of_indexWindowClean), matching the not-IndexWindowClean gate of " ++
      "the dirty field.",
    "GOAL 3 WIRED (additive only): ReturnCaseSplitChargeResidual.ofWindowOnesBound / " ++
      ".ofLowScaleSupport rebuild the FULL rebased Return/Class-4 charge residual from the " ++
      "atom + verbatim class4Interior + hnumeric; same ledger floor " ++
      "(returnFloor_of_windowOnesBound: routedClassMassOf ... 4 <= cStar*xi*X/6) and the " ++
      "corrected M.2.1 per-slice count from the atom alone (perSliceCount_of_windowOnesBound); " ++
      "the case-split rebase's named weaker target discharges from the atom " ++
      "(dirtyEnvelopeQOddField_of_windowOnesBound / _of_lowScaleSupport).",
    "WHAT RESISTS (honest): SliceDirtyEnvelope itself remains open - the gap-one mechanism " ++
      "counts raw window support, which on a failing shell has no in-tree absolute bound at " ++
      "low scales; the manuscript counts the dirty slices by K.2.3 chain / Fine-Wilf " ++
      "arm-period separation at the anchored (e,tau,P) keys, where same-slice members need " ++
      "not share carryVal2 - the formalized self-referential key collapses that geometry to " ++
      "equal-level crossings, where pinning gives singletons (= the capstone demand) and " ++
      "nothing weaker.  The honest residual after this pass: ReturnWindowOnesBound (or any " ++
      "sub-shell support bound supportCount(F+W) <= L), a strictly support-side statement " ++
      "with NO remaining slice/key/carry content.",
    "HYGIENE: additive only - no existing module edited; no sorry / admit / new axiom / " ++
      "native_decide; all #print axioms in [propext, Classical.choice, Quot.sound] or fewer." ]

theorem dirtySliceEnvelopeStatus_nonempty : dirtySliceEnvelopeStatus ≠ [] := by
  simp [dirtySliceEnvelopeStatus]

/-! ## Part 9.  Axiom-cleanliness audit -/

#print axioms sliceMembers_carryVal2_eq
#print axioms sliceMembers_spaced
#print axioms slice_gap_one_exists
#print axioms slice_gap_valuation_drop
#print axioms slice_gap_valuation_lt
#print axioms sliceMembers_no_nesting_growth
#print axioms sliceMembers_carryCrossing
#print axioms selfRef_hmono_forces_singleton
#print axioms gapOnes_card_bound
#print axioms sliceCard_le_windowOnes_succ
#print axioms returnWindowOnes_subset_supportIn
#print axioms returnWindowOnes_card_le_lowScaleSupport
#print axioms returnWindowOnes_card_le_width_pred
#print axioms returnWindowOnes_subX_hitIndex_lt
#print axioms lowScaleCeiling_le_supportCount_add
#print axioms sliceCard_le_lowScaleSupport_succ
#print axioms returnWindowOnesBound_of_lowScaleSupport
#print axioms sliceDirtyEnvelope_of_windowOnesBound
#print axioms sliceDirtyEnvelope_of_lowScaleSupport
#print axioms lowScaleSupportBound_forces_le_depth
#print axioms lowScaleSupportBound_tight_of_ceiling_ge
#print axioms returnWindowOnes_eq_empty_of_indexWindowClean
#print axioms returnWindowOnesBound_of_indexWindowClean
#print axioms ReturnCaseSplitChargeResidual.ofWindowOnesBound
#print axioms ReturnCaseSplitChargeResidual.ofLowScaleSupport
#print axioms returnFloor_of_windowOnesBound
#print axioms perSliceCount_of_windowOnesBound
#print axioms dirtyEnvelopeQOddField_of_windowOnesBound
#print axioms dirtyEnvelopeQOddField_of_lowScaleSupport
#print axioms dirtySliceEnvelopeStatus_nonempty

end

end Erdos260
