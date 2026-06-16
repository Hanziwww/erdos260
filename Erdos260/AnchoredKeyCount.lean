import Erdos260.Erdos260ChargeCapstone

/-!
# The anchored-key count: the manuscript M.2.1 mechanism at an anchored key, and the
charge-junction closure of the Return lane (`AnchoredKeyCount`)

This module (NEW; it edits no existing file) closes the Return counting lane the MANUSCRIPT's
way (Lemma M.2.1 of `proof_v4_unconditional_clean_v5.tex`): the per-slice ordinary-local-long
count is performed at an ANCHORED key — a key whose same-slice members may carry DIFFERENT
carry valuations, so the Erdos–Szekeres nesting dimension is alive — instead of the
self-referential key `k ↦ (carryVal2 k, k mod 2^{carryVal2 k})`, where wave 13 proved the
clean branch collapses to singletons and the whole count lands on the dirty residual
`SliceDirtyEnvelope`.

## Goal 1 — the verdict on the in-tree Erdos–Szekeres alternative (mapped, confirmed)

* The NESTING bound is fully formalized: `liftLevel` is the tower `δ ↦ δ + 2^δ` and
  `liftLevelBound L` its inverse (`ReturnM2J4Core`) — THE DICTIONARY HOLDS: `liftLevelBound X`
  IS the maximal length of a chain `δ_{i+1} ≥ δ_i + 2^{δ_i}` below `X`, and the chain bound is
  the proved `IsLiftChain.card_le`.  What was missing in-tree is a key at which actual fibre
  slices REALIZE a lift chain: at `returnSelfRefKey` same-slice members share `carryVal2`
  (equal-level only), so the growth never fires (`sliceMembers_no_nesting_growth`,
  `DirtySliceEnvelope`).
* The CROSSING bound (endpoint pinning) is an input in-tree: `OlcSliceData.ofAnchoredKey`
  consumes the `hmono` atom (`∀ x z, CarryCrossing → e x < e z`, `ReturnAnchoredCrossingCore` /
  `ReturnCarryEndpointCore`), and at the self-referential key it forces singletons
  (`selfRef_hmono_forces_singleton`).  It is NOT proved for actual fibre slices.
* The (Z) routing-predicate case split `sliceCaseSplit` (`ReturnCaseSplitRebase`) is
  KEY-GENERIC: every slice of EVERY key is (Z)-clean or carries a dirty crossing datum.

## Goal 2 — what is PROVED here (the M.2.1 mechanism at the anchored residue key)

The anchored key chosen is `anchoredResidueKey ctx : k ↦ k mod 2^{carryVal2 k}` — the
self-referential key with the level coordinate DELETED, i.e. the position-residue anchor.
Same-slice members may have different `carryVal2`: the nesting dimension is alive.  On
(Z)-CLEAN slices of this key, with NO further hypothesis:

* `sliceZClean_pair_zeroRun` / `sliceZClean_carryVal2_add` (any key): consecutive-pair
  cleanness propagates to ALL pairs, and the carry valuation telescopes,
  `carryVal2 z = carryVal2 x + (z − x)` — the zero-run lift identity, all-pairs form.
* `anchoredClean_crossingFree`: clean anchored slices are CROSSING-FREE — the M.2.1 crossing
  exclusion is a THEOREM at this key (no `hmono` atom, no endpoint-pinning input): cleanness
  itself pins the endpoint.  Sharper than the manuscript's `O_Q(1)`: the crossing chain has
  length exactly 1.
* `anchoredClean_gapDiv`: the gap divisibility `2^{carryVal2 x} ∣ (z − x)` — the cousin of
  `returnSelfRefKey_gapDiv`, derived from residue matching at unequal levels.
* `anchoredClean_lift_congruence`: **the manuscript's self-referential lift congruence
  `δ_{i+1} ≡ δ_i (mod 2^{δ_i})`** — `2^{carryVal2 x} ∣ (carryVal2 z − carryVal2 x)` — derived
  (not assumed) from the carry machinery: the valuation gap EQUALS the position gap, which the
  key pins to a multiple of `2^{δ_x}`.
* `anchoredClean_nesting_growth`: hence `carryVal2 x + 2^{carryVal2 x} ≤ carryVal2 z` — the
  M.2.1 tower growth, GENUINELY MULTI-MEMBER (refuted at the self-referential key by wave 13).
* `anchoredCleanSliceCard_le` — **THE M.2.1 NESTING COUNT, PROVED**: every (Z)-clean slice of
  the anchored residue key obeys the (M.1) envelope `|slice| ≤ liftLevelBound X`.  Engine:
  the translated member positions `k − min` form an `IsLiftChain` bounded by the window width
  `W − 1 < W ≤ X` (`supportShell_card_le_length`), so `IsLiftChain.card_le` applies.

## Goal 2 — the honest residual at the anchored key

`AnchoredSliceDirtyEnvelope ctx`: dirty-classified slices of the anchored residue key obey the
(M.1) envelope.  As at the self-referential key, the dirty branch is NOT closed in-tree (the
`DirtyWindowCountCore` finding: the dirty package counts constructed crossing families, not
actual fibre slices).  With the atom, ALL anchored slices obey the envelope
(`anchoredSliceCard_le`), the per-slice charge rebuilds at the anchored key
(`Class4ReturnPerSliceCharge.ofAnchoredEnvelope`), and — NEW — the atom IMPLIES the wave-13
self-referential atom (`sliceDirtyEnvelope_of_anchoredEnvelope`): a dirty self-referential
slice has ≥ 2 equal-level members, its enclosing anchored slice cannot be clean (cleanness
forces strictly increasing levels), so the anchored envelope covers it.  Field form:
`returnDirtyEnvelopeField_of_anchoredField`.  (No converse, and no derivation of the anchored
atom from `ReturnKeyInjOn`: self-referential key injectivity says nothing about multi-level
anchored slices — the two demands are incomparable; only this direction holds.)

## Goal 3 — THE JUNCTION COLLAPSE: the Return lane CLOSES at the charge junction

The decisive finding: `Class4ReturnPerSliceCharge` carries its slice key as a FIELD, and the
ENTIRE in-tree numeric bridge is KEY-GENERIC — `return_hnumeric_of_fibre_card_le ctx key`
needs only the fibre population bound `|olcFibre| ≤ r + 1`, which the KEPT capstone field
`returnGates` supplies at every context (`class4FibreSmall_of_gates`, the K.1 boundary-band
bound).  Taking the MAXIMALLY REFINED anchored key `k ↦ k` (each return start is its own
anchor class — the degenerate limit of the manuscript's exact-endpoint anchor split, in which
the oriented endpoint coordinate determines the member), every slice is a SINGLETON BY
DEFINITION (`refinedAnchoredKey_slice_card_le_one`), `OlcSliceData.ofCardLe` applies with
`1 ≤ liftLevelBound X`, and the FULL charge rebuilds from the counts alone
(`Class4ReturnPerSliceCharge.ofCountsOnly`) — NO envelope field, NO digit field, NO clean-step
field, NO key-injectivity, NO dirty-slice demand.  The manuscript's per-slice `(log* L)^{C_Q}`
envelope is needed when the anchor classes are few and the fibre is large; the formalized
class-4 fibre is already gated to `≤ r + 1` members, so the slice-key bookkeeping factor
`#sliceKeys ≤ |olcFibre| ≤ r + 1` is absorbed by the proved budget
`return_hnumeric_of_key_card_le_succ_r` (the `(r+1)·(L+1)·(r+1)·(L+B+1) ≤ 31·2^L/1536`
master inequality).  CONSEQUENCE: the capstone surface field `returnDirtyEnvelope` of
`Erdos260ReturnChargeResidual` is BYPASSED — the successor surface
`Erdos260AnchoredCountResidual` (12 fields: the same surface minus `returnDirtyEnvelope`)
reaches `Erdos260Statement` (`erdos260_of_anchoredCount`), with the Return lane carried by
`returnGates` + `returnInterior` ONLY — fields every capstone surface since wave 3 demands.
THE RETURN-ZERO / ENVELOPE LANE CLOSES UNCONDITIONALLY.

## Hygiene

No `sorry`, no `admit`, no new `axiom`, no `native_decide`; additive only — no existing module
is edited.  All key declarations audited at the end of the file.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 0.  Finite-set helper: the consecutive successor inside a slice -/

/-- Every member strictly above `x` refines to the CONSECUTIVE successor of `x` in `S`. -/
private theorem anchoredKeyCount_exists_succ {S : Finset ℕ} {x z : ℕ}
    (hz : z ∈ S) (hxz : x < z) :
    ∃ u ∈ S, x < u ∧ ∀ c ∈ S, x < c → u ≤ c := by
  have hne : (S.filter (fun c => x < c)).Nonempty := ⟨z, Finset.mem_filter.mpr ⟨hz, hxz⟩⟩
  have hmem := Finset.min'_mem _ hne
  rw [Finset.mem_filter] at hmem
  exact ⟨_, hmem.1, hmem.2, fun c hc hxc => Finset.min'_le _ c (Finset.mem_filter.mpr ⟨hc, hxc⟩)⟩

/-! ## Part 1.  The anchored residue key and the clean-slice carry geometry

The anchored residue key deletes the level coordinate from the self-referential key: it
records ONLY the position residue `k mod 2^{carryVal2 k}`.  Same-slice members may carry
different `carryVal2` — the nesting dimension of M.2.1 is alive at this key. -/

/-- **The anchored residue key**: the position-residue anchor `k ↦ k mod 2^{carryVal2 k}` —
the self-referential key with the level coordinate deleted.  Same-slice members need NOT share
`carryVal2`. -/
def anchoredResidueKey (ctx : ActualFailureContext) : ℕ → ℕ :=
  fun k => k % 2 ^ carryVal2 ctx k

/-- The anchored residue key COARSENS the self-referential key: equal self-referential keys
have equal residue keys (the residue is the second pair component). -/
theorem anchoredResidueKey_coarsens_selfRef (ctx : ActualFailureContext) {x z : ℕ}
    (h : returnSelfRefKey ctx x = returnSelfRefKey ctx z) :
    anchoredResidueKey ctx x = anchoredResidueKey ctx z := by
  simp only [returnSelfRefKey] at h
  simp only [anchoredResidueKey]
  exact (Nat.pair_eq_pair.mp h).2

/-- **The all-pairs zero-run upgrade (ANY key)**: consecutive-pair (Z)-cleanness propagates to
EVERY ordered pair of the slice — the consecutive gaps tile the whole interval.  Induction on
the gap length through the consecutive successor. -/
theorem sliceZClean_pair_zeroRun (ctx : ActualFailureContext) (key : ℕ → ℕ) (y : ℕ)
    (h : SliceZClean ctx key y) :
    ∀ x ∈ olcSlice ctx key y, ∀ z ∈ olcSlice ctx key y, x < z →
      ∀ j, x < j → j ≤ z → ctx.d j = 0 := by
  suffices H : ∀ n : ℕ, ∀ x ∈ olcSlice ctx key y, ∀ z ∈ olcSlice ctx key y, x < z →
      z - x ≤ n → ∀ j, x < j → j ≤ z → ctx.d j = 0 by
    intro x hx z hz hxz
    exact H (z - x) x hx z hz hxz le_rfl
  intro n
  induction n with
  | zero =>
    intro x hx z hz hxz hle j hjx hjz
    omega
  | succ n ih =>
    intro x hx z hz hxz hle j hjx hjz
    obtain ⟨u, huS, hxu, hcons⟩ := anchoredKeyCount_exists_succ hz hxz
    by_cases hju : j ≤ u
    · exact h x hx u huS hxu hcons j hjx hju
    · have huz : u ≤ z := hcons z hz hxz
      have huzlt : u < z := by omega
      exact ih u huS z hz huzlt (by omega) j (by omega) hjz

/-- **The all-pairs valuation telescoping (ANY key)**: on a (Z)-clean slice the carry
valuation grows by EXACTLY the position gap, `carryVal2 z = carryVal2 x + (z − x)` — the
zero-run lift identity (`carryVal2_add_zeroRun`), all-pairs form. -/
theorem sliceZClean_carryVal2_add (ctx : ActualFailureContext) (key : ℕ → ℕ) (y : ℕ)
    (h : SliceZClean ctx key y) :
    ∀ x ∈ olcSlice ctx key y, ∀ z ∈ olcSlice ctx key y, x < z →
      carryVal2 ctx z = carryVal2 ctx x + (z - x) := by
  intro x hx z hz hxz
  have hrun : ∀ j, x < j → j ≤ x + (z - x) → ctx.d j = 0 := by
    intro j h1 h2
    exact sliceZClean_pair_zeroRun ctx key y h x hx z hz hxz j h1 (by omega)
  have hadd := carryVal2_add_zeroRun ctx x (z - x) hrun
  rw [show x + (z - x) = z from by omega] at hadd
  exact hadd

/-- **Crossing-freeness is a THEOREM on clean anchored slices (ANY key)**: the carry valuation
strictly increases along the slice — the M.2.1 crossing exclusion with NO `hmono` atom and NO
endpoint-pinning input (cleanness itself pins the endpoint). -/
theorem anchoredClean_crossingFree (ctx : ActualFailureContext) (key : ℕ → ℕ) (y : ℕ)
    (h : SliceZClean ctx key y) :
    ∀ x ∈ olcSlice ctx key y, ∀ z ∈ olcSlice ctx key y, x < z →
      carryVal2 ctx x < carryVal2 ctx z := by
  intro x hx z hz hxz
  have := sliceZClean_carryVal2_add ctx key y h x hx z hz hxz
  omega

/-- **The gap divisibility at the anchored residue key (clean slices)**:
`2^{carryVal2 x} ∣ (z − x)` — the anchored cousin of `returnSelfRefKey_gapDiv`.  The key pins
both residues; cleanness orders the levels, so the higher-level residue reduces to the
lower-level modulus. -/
theorem anchoredClean_gapDiv (ctx : ActualFailureContext) (y : ℕ)
    (h : SliceZClean ctx (anchoredResidueKey ctx) y) :
    ∀ x ∈ olcSlice ctx (anchoredResidueKey ctx) y,
      ∀ z ∈ olcSlice ctx (anchoredResidueKey ctx) y, x < z →
        2 ^ carryVal2 ctx x ∣ (z - x) := by
  intro x hx z hz hxz
  have hvz : carryVal2 ctx z = carryVal2 ctx x + (z - x) :=
    sliceZClean_carryVal2_add ctx (anchoredResidueKey ctx) y h x hx z hz hxz
  have hle : carryVal2 ctx x ≤ carryVal2 ctx z := by omega
  have hdvd : (2 : ℕ) ^ carryVal2 ctx x ∣ 2 ^ carryVal2 ctx z := pow_dvd_pow 2 hle
  have hkx := key_eq_of_mem_olcSlice hx
  have hkz := key_eq_of_mem_olcSlice hz
  simp only [anchoredResidueKey] at hkx hkz
  have hy : y % 2 ^ carryVal2 ctx x = y := by
    rw [← hkx]
    exact Nat.mod_mod_of_dvd x (dvd_refl _)
  have hmod : x % 2 ^ carryVal2 ctx x = z % 2 ^ carryVal2 ctx x := by
    rw [hkx, ← Nat.mod_mod_of_dvd z hdvd, hkz, hy]
  exact (Nat.modEq_iff_dvd' (le_of_lt hxz)).mp hmod

/-- **THE SELF-REFERENTIAL LIFT CONGRUENCE, DERIVED (manuscript M.2.1)**: on a clean anchored
slice, `δ_{i+1} ≡ δ_i (mod 2^{δ_i})` — `2^{carryVal2 x} ∣ (carryVal2 z − carryVal2 x)` for
EVERY ordered pair.  The valuation gap equals the position gap (telescoping), and the key pins
the position gap to a multiple of `2^{δ_x}`. -/
theorem anchoredClean_lift_congruence (ctx : ActualFailureContext) (y : ℕ)
    (h : SliceZClean ctx (anchoredResidueKey ctx) y) :
    ∀ x ∈ olcSlice ctx (anchoredResidueKey ctx) y,
      ∀ z ∈ olcSlice ctx (anchoredResidueKey ctx) y, x < z →
        2 ^ carryVal2 ctx x ∣ (carryVal2 ctx z - carryVal2 ctx x) := by
  intro x hx z hz hxz
  have hvz : carryVal2 ctx z = carryVal2 ctx x + (z - x) :=
    sliceZClean_carryVal2_add ctx (anchoredResidueKey ctx) y h x hx z hz hxz
  have hgap := anchoredClean_gapDiv ctx y h x hx z hz hxz
  have heq : carryVal2 ctx z - carryVal2 ctx x = z - x := by omega
  rw [heq]
  exact hgap

/-- **THE M.2.1 NESTING GROWTH, GENUINELY MULTI-MEMBER**: on a clean anchored slice,
`carryVal2 x + 2^{carryVal2 x} ≤ carryVal2 z` for every ordered pair — the tower step the
manuscript extracts from the lift congruence (`δ_{i+1} ≥ δ_i + 2^{δ_i}`).  At the
self-referential key this growth is REFUTED on every same-slice pair (wave 13); at the
anchored residue key it FIRES. -/
theorem anchoredClean_nesting_growth (ctx : ActualFailureContext) (y : ℕ)
    (h : SliceZClean ctx (anchoredResidueKey ctx) y) :
    ∀ x ∈ olcSlice ctx (anchoredResidueKey ctx) y,
      ∀ z ∈ olcSlice ctx (anchoredResidueKey ctx) y, x < z →
        carryVal2 ctx x + 2 ^ carryVal2 ctx x ≤ carryVal2 ctx z := by
  intro x hx z hz hxz
  have hvz : carryVal2 ctx z = carryVal2 ctx x + (z - x) :=
    sliceZClean_carryVal2_add ctx (anchoredResidueKey ctx) y h x hx z hz hxz
  have hgap := anchoredClean_gapDiv ctx y h x hx z hz hxz
  have hge : 2 ^ carryVal2 ctx x ≤ z - x := Nat.le_of_dvd (by omega) hgap
  omega

/-! ## Part 2.  The clean anchored count — the M.2.1 nesting bound on actual fibre slices

The translated member positions `k − min` of a clean slice form a self-referential lift chain
(`IsLiftChain`) bounded by the window width `W − 1 < W ≤ X`, so the PROVED chain bound
`IsLiftChain.card_le` delivers the (M.1) envelope `|slice| ≤ liftLevelBound X` — with no
hypothesis beyond cleanness. -/

/-- **The generic chain-count engine**: a finite set of positions whose level function
telescopes by gaps (`lvl b = lvl a + (b − a)`) and whose pairwise gaps dominate `2^{lvl a}`,
with pairwise width ≤ `X`, has at most `liftLevelBound X` members.  Engine: the translated
positions `k − min` are an `IsLiftChain` bounded by `X`. -/
private theorem anchoredKeyCount_chain_engine {S : Finset ℕ} {X : ℕ} (lvl : ℕ → ℕ)
    (hwidth : ∀ a ∈ S, ∀ b ∈ S, a ≤ b → b - a ≤ X)
    (hlvl : ∀ a ∈ S, ∀ b ∈ S, a < b → lvl b = lvl a + (b - a))
    (hgap : ∀ a ∈ S, ∀ b ∈ S, a < b → 2 ^ lvl a ≤ b - a) :
    S.card ≤ liftLevelBound X := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  · have hm : S.min' hne ∈ S := S.min'_mem hne
    have hinj : Set.InjOn (fun k => k - S.min' hne) ↑S := by
      intro a ha b hb hab
      have ha' : a ∈ S := Finset.mem_coe.mp ha
      have hb' : b ∈ S := Finset.mem_coe.mp hb
      have hma : S.min' hne ≤ a := S.min'_le a ha'
      have hmb : S.min' hne ≤ b := S.min'_le b hb'
      have hab' : a - S.min' hne = b - S.min' hne := hab
      omega
    have hchain : IsLiftChain (S.image (fun k => k - S.min' hne)) := by
      intro u' hu' v' hv' huv
      rw [Finset.mem_image] at hu' hv'
      obtain ⟨u, hu, rfl⟩ := hu'
      obtain ⟨v, hv, rfl⟩ := hv'
      have huv2 : u - S.min' hne < v - S.min' hne := huv
      have hmu : S.min' hne ≤ u := S.min'_le u hu
      have hmv : S.min' hne ≤ v := S.min'_le v hv
      have huvlt : u < v := by omega
      have hgapuv : 2 ^ lvl u ≤ v - u := hgap u hu v hv huvlt
      have hlu : u - S.min' hne ≤ lvl u := by
        rcases Nat.eq_or_lt_of_le hmu with heq | hlt
        · omega
        · have := hlvl _ hm u hu hlt
          omega
      have hpow : 2 ^ (u - S.min' hne) ≤ 2 ^ lvl u :=
        Nat.pow_le_pow_right (by norm_num) hlu
      show u - S.min' hne + 2 ^ (u - S.min' hne) ≤ v - S.min' hne
      omega
    have hbound : ∀ t ∈ S.image (fun k => k - S.min' hne), t ≤ X := by
      intro t ht
      rw [Finset.mem_image] at ht
      obtain ⟨k, hk, rfl⟩ := ht
      exact hwidth _ hm k hk (S.min'_le k hk)
    have hcard : (S.image (fun k => k - S.min' hne)).card = S.card :=
      Finset.card_image_of_injOn hinj
    have hle := hchain.card_le hbound
    omega

/-- **THE M.2.1 NESTING COUNT, PROVED ON ACTUAL FIBRE SLICES**: every (Z)-clean slice of the
anchored residue key obeys the (M.1) envelope `|slice| ≤ liftLevelBound X` — the manuscript's
`O(log* L)` bound on nonseparated nested levels, realized on the formalized class-4 fibre with
NO hypothesis beyond cleanness.  Members live in the window `[F, F + W)`
(`olcFibre_mem_window`) with `W ≤ X` (`supportShell_card_le_length`), the translated positions
form a lift chain (gap divisibility + telescoping), and `IsLiftChain.card_le` counts. -/
theorem anchoredCleanSliceCard_le (ctx : ActualFailureContext) (y : ℕ)
    (h : SliceZClean ctx (anchoredResidueKey ctx) y) :
    (olcSlice ctx (anchoredResidueKey ctx) y).card ≤ liftLevelBound ctx.shell.X := by
  apply anchoredKeyCount_chain_engine (carryVal2 ctx)
  · intro a ha b hb hab
    have h1 := olcFibre_mem_window ctx (mem_olcFibre_of_mem_olcSlice ha)
    have h2 := olcFibre_mem_window ctx (mem_olcFibre_of_mem_olcSlice hb)
    have hW : (supportShell ctx.shell.d ctx.shell.X).card ≤ ctx.shell.X :=
      supportShell_card_le_length ctx.shell.d ctx.shell.X
    omega
  · exact fun a ha b hb hab =>
      sliceZClean_carryVal2_add ctx (anchoredResidueKey ctx) y h a ha b hb hab
  · intro a ha b hb hab
    exact Nat.le_of_dvd (by omega) (anchoredClean_gapDiv ctx y h a ha b hb hab)

/-! ## Part 3.  The dirty atom, the full anchored count, and the bridge to wave 13

The case split `sliceCaseSplit` is key-generic: every anchored slice is clean (counted by
Part 2) or carries a dirty crossing datum (routed to the dirty package — the honest residual,
exactly as the manuscript's M.2 remark prescribes). -/

/-- **The anchored dirty-slice envelope (the honest residual at the anchored key)**: slices of
the anchored residue key carrying a dirty crossing datum obey the (M.1) envelope.  The clean
branch is a THEOREM (`anchoredCleanSliceCard_le`); this atom is the dirty-package count that
the in-tree dirty modules do not deliver for actual fibre slices (the `DirtyWindowCountCore`
finding). -/
def AnchoredSliceDirtyEnvelope (ctx : ActualFailureContext) : Prop :=
  ∀ y ∈ (olcFibre ctx).image (anchoredResidueKey ctx),
    SliceHasDirtyDatum ctx (anchoredResidueKey ctx) y →
    (olcSlice ctx (anchoredResidueKey ctx) y).card ≤ liftLevelBound ctx.shell.X

/-- **The full anchored count from the dirty atom**: EVERY slice of the anchored residue key
obeys the (M.1) envelope — clean slices by the proved nesting count, dirty slices by the
atom; the case split is exhaustive by definition (`sliceCaseSplit`, key-generic). -/
theorem anchoredSliceCard_le (ctx : ActualFailureContext)
    (henv : AnchoredSliceDirtyEnvelope ctx) :
    ∀ y ∈ (olcFibre ctx).image (anchoredResidueKey ctx),
      (olcSlice ctx (anchoredResidueKey ctx) y).card ≤ liftLevelBound ctx.shell.X := by
  intro y hy
  rcases sliceCaseSplit ctx (anchoredResidueKey ctx) y with hclean | hdirty
  · exact anchoredCleanSliceCard_le ctx y hclean
  · exact henv y hy hdirty

/-- **The bridge to the wave-13 atom**: the anchored dirty envelope IMPLIES the
self-referential `SliceDirtyEnvelope`.  A dirty self-referential slice has ≥ 2 members of
EQUAL `carryVal2`; the anchored slice containing it therefore cannot be (Z)-clean (cleanness
forces strictly increasing levels), so the full anchored count covers it, and the
self-referential slice is a subset.  (No converse: the anchored envelope bounds multi-level
unions the self-referential envelope never sees.) -/
theorem sliceDirtyEnvelope_of_anchoredEnvelope (ctx : ActualFailureContext)
    (henv : AnchoredSliceDirtyEnvelope ctx) : SliceDirtyEnvelope ctx := by
  intro y hy hdirty
  obtain ⟨W⟩ := hdirty
  have hleft : W.left ∈ olcSlice ctx (returnSelfRefKey ctx) y := W.left_mem
  have hlf : W.left ∈ olcFibre ctx := mem_olcFibre_of_mem_olcSlice hleft
  have hlkey : returnSelfRefKey ctx W.left = y := key_eq_of_mem_olcSlice hleft
  have hsub : olcSlice ctx (returnSelfRefKey ctx) y
      ⊆ olcSlice ctx (anchoredResidueKey ctx) (anchoredResidueKey ctx W.left) := by
    intro k hk
    have hkkey : returnSelfRefKey ctx k = y := key_eq_of_mem_olcSlice hk
    have hkf : k ∈ olcFibre ctx := mem_olcFibre_of_mem_olcSlice hk
    rw [olcSlice_def]
    exact Finset.mem_filter.mpr
      ⟨hkf, anchoredResidueKey_coarsens_selfRef ctx (hkkey.trans hlkey.symm)⟩
  refine le_trans (Finset.card_le_card hsub) ?_
  exact anchoredSliceCard_le ctx henv _ (Finset.mem_image_of_mem _ hlf)

/-- **The anchored dirty-envelope field**: the anchored atom under the VERBATIM wave-8 guards
of the charge capstone's `ReturnDirtyEnvelopeField` (band-2-free datum, spaced `b2 = 1` datum,
the small-carry regime, index-window separation; no parity hypothesis). -/
def AnchoredDirtyEnvelopeField : Prop :=
  ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    (∃ k ∈ olcFibre ctx,
      2 ^ carryVal2 ctx k < (supportShell ctx.shell.d ctx.shell.X).card) →
    ¬ ReturnIndexWindowClean ctx →
    AnchoredSliceDirtyEnvelope ctx

/-- The anchored field discharges the capstone's envelope field (field-level bridge). -/
theorem returnDirtyEnvelopeField_of_anchoredField
    (h : AnchoredDirtyEnvelopeField) : ReturnDirtyEnvelopeField :=
  fun ctx hA hB hC hD => sliceDirtyEnvelope_of_anchoredEnvelope ctx (h ctx hA hB hC hD)

/-! ## Part 4.  The per-slice charge rebuilt at the anchored residue key

`Class4ReturnPerSliceCharge` is key-generic; with the anchored count the charge rebuilds at
the anchored residue key from the counts alone — `OlcSliceData.ofCardLe` per slice, the
window/interior machinery, and the key-generic numeric bridge. -/

/-- **The V3 Return/Class-4 charge at the ANCHORED key**: the anchored dirty atom + the K.1
interior + the fibre population bound rebuild the full per-slice charge with the slice data
manufactured from the anchored counts (clean slices by THEOREM, dirty by the atom). -/
def Class4ReturnPerSliceCharge.ofAnchoredEnvelope (ctx : ActualFailureContext)
    (henv : AnchoredSliceDirtyEnvelope ctx)
    (hInterior : ReturnInteriorBody ctx)
    (hfibre : (olcFibre ctx).card ≤ ctx.n24CarryData.r + 1) :
    Class4ReturnPerSliceCharge ctx :=
  Class4ReturnPerSliceCharge.ofSlicesWindow ctx (anchoredResidueKey ctx)
    (fun y hy => OlcSliceData.ofCardLe ctx (anchoredResidueKey ctx) y
      (anchoredSliceCard_le ctx henv y hy))
    (returnWindowReach ctx)
    (returnWindowReach_add_one_le ctx)
    (returnClass4Contain_ofInterior ctx hInterior)
    (return_hnumeric_of_fibre_card_le ctx (anchoredResidueKey ctx) hfibre)

/-! ## Part 5.  THE JUNCTION COLLAPSE — the maximally refined anchored key

The manuscript splits into EXACT anchor classes (oriented endpoint coordinate, margin class,
side, copy index); the maximal refinement makes the anchor determine the member.  Formally:
the key `k ↦ k`.  Every slice is a singleton BY DEFINITION, so the per-slice (M.1) envelope is
free, and the WHOLE charge follows from the kept capstone fields — the slice-key bookkeeping
factor `#sliceKeys ≤ |olcFibre| ≤ r + 1` is absorbed by the PROVED key-generic budget
`return_hnumeric_of_fibre_card_le`. -/

/-- Slices of the maximally refined anchored key `k ↦ k` are singletons by definition. -/
theorem refinedAnchoredKey_slice_card_le_one (ctx : ActualFailureContext) (y : ℕ) :
    (olcSlice ctx (fun k => k) y).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun a ha b hb => ?_
  have h1 : a = y := key_eq_of_mem_olcSlice ha
  have h2 : b = y := key_eq_of_mem_olcSlice hb
  omega

/-- **THE UNCONDITIONAL CHARGE (the junction collapse)**: the full
`Class4ReturnPerSliceCharge` from the K.1 interior and the fibre population bound ALONE — no
envelope field, no digit field, no clean-step field, no key-injectivity, no dirty-slice
demand.  The maximally refined anchored key has singleton slices by definition;
`OlcSliceData.ofCardLe` applies with `1 ≤ liftLevelBound X`; the numeric bridge is
key-generic. -/
def Class4ReturnPerSliceCharge.ofCountsOnly (ctx : ActualFailureContext)
    (hInterior : ReturnInteriorBody ctx)
    (hfibre : (olcFibre ctx).card ≤ ctx.n24CarryData.r + 1) :
    Class4ReturnPerSliceCharge ctx :=
  Class4ReturnPerSliceCharge.ofSlicesWindow ctx (fun k => k)
    (fun y hy => OlcSliceData.ofCardLe ctx (fun k => k) y
      (le_trans (refinedAnchoredKey_slice_card_le_one ctx y)
        (one_le_liftLevelBound ctx.shell.X)))
    (returnWindowReach ctx)
    (returnWindowReach_add_one_le ctx)
    (returnClass4Contain_ofInterior ctx hInterior)
    (return_hnumeric_of_fibre_card_le ctx (fun k => k) hfibre)

/-! ## Part 6.  The successor surface and the endpoint — the Return lane CLOSED

`Erdos260AnchoredCountResidual` is `Erdos260ReturnChargeResidual` with the
`returnDirtyEnvelope` field DELETED (12 fields, all verbatim).  The Return slot of the budget
is carried by the unconditional charge `Class4ReturnPerSliceCharge.ofCountsOnly`, with the
interior and population inputs from the KEPT fields `returnInterior` and `returnGates` —
exactly the suppliers the charge capstone already used for `class4Interior`/`hnumeric`.  The
non-Return lanes walk the same public per-lane discharges as `Erdos260ReturnChargeResidual`. -/

/-- **The anchored-count capstone surface**: the charge capstone surface
(`Erdos260ReturnChargeResidual`) with the `returnDirtyEnvelope` field DELETED — the Return
lane is carried by `returnGates` + `returnInterior` only.  12 fields, all verbatim wave-12
shapes. -/
structure Erdos260AnchoredCountResidual where
  /-- Tower / class 2 - enumerated part (`q < 107`), with the free aperiodicity guard. -/
  towerEnumLow : ∀ ctx : ActualFailureContext,
    TowerModulusEnumEscapeV2 ctx → (class1SlopeDatum ctx).q < 107 →
    (ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx) →
    Class2CycleInequality ctx
  /-- Tower / class 2 - tail (`107 ≤ q`), with the free aperiodicity guard. -/
  towerEnumTail : ∀ ctx : ActualFailureContext,
    TowerModulusEnumEscapeV2 ctx →
    107 ≤ (class1SlopeDatum ctx).q →
    (ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx) →
    (((Nat.log 2 (class1SlopeDatum ctx).q + 1) * shellWidth ctx
        < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
            (class1SlopeDatum ctx).K₀)))
        ∧ TowerBand4Budget ctx)
      ∨ Class2CycleInequality ctx
  /-- Run / class 5 - enumerated part (`q < 64`); verbatim field. -/
  runNumericLow : ∀ ctx : ActualFailureContext,
    (class1SlopeDatum ctx).q < 64 →
    Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx
  /-- Run / class 5 - tail (`64 ≤ q`); verbatim field. -/
  runNumericTail : ∀ ctx : ActualFailureContext,
    64 ≤ (class1SlopeDatum ctx).q →
    ((Nat.log 2 (class1SlopeDatum ctx).q + 1)
        * (supportShell ctx.shell.d ctx.shell.X).card
      < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
          (class1SlopeDatum ctx).K₀)))
      ∧ RunBandBudget ctx
    ∨ Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx
  /-- Return / class 4 count gates - verbatim field (the `hnumeric` supplier of the charge,
  through `class4FibreSmall_of_gates`; with `returnInterior` it now carries the WHOLE Return
  lane). -/
  returnGates : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    2 * (129 * shellLadderDepth ctx + 64)
      ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
    ReturnGatesBodyUngated ctx
  /-- Return / class 4 K.1 interior - verbatim field (the `class4Interior` supplier of the
  charge). -/
  returnInterior : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx
  /-- Chernoff / class 0 survivors - verbatim field. -/
  class0Survivor : ∀ ctx : ActualFailureContext, Class0DatumSurvivor ctx →
    Class0SurvivorResidueMiss ctx
  /-- Chernoff / class 0 mid band - verbatim field. -/
  class0Mid : ∀ ctx : ActualFailureContext, 48 ≤ (class1SlopeDatum ctx).q →
    (class1SlopeDatum ctx).q < 96 → Class0CycleMeetsShallow ctx →
    Class0WindowCycleCheck ctx
  /-- Chernoff / class 0 large moduli (`96 ≤ q`) - verbatim field. -/
  class0BigOrder : ∀ ctx : ActualFailureContext, 96 ≤ (class1SlopeDatum ctx).q →
    (∃ C, ((Nat.log 2 (class1SlopeDatum ctx).q + 1) * C
          < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
              (class1SlopeDatum ctx).K₀)))
        ∧ ∃ c, C < c ∧ c ≤ (class1SlopeDatum ctx).q
            ∧ (∀ m, 1 ≤ m →
                slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
                  = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
            ∧ ∀ k ∈ ctx.n24CarryData.starts,
                129 * shellLadderDepth ctx + 64
                    ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
                (class1SlopeDatum ctx).q
                  < 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀
                      (cycleRep c k))
    ∨ Class0WindowCycleCheck ctx
  /-- CNL / class 1 - enumerated deep part (`q < 101`), with the free aperiodicity guard. -/
  class1DeepLow : ∀ ctx : ActualFailureContext,
    64 ∣ shellLadderDepth ctx →
    9 ≤ (class1SlopeDatum ctx).q →
    ((class1SlopeDatum ctx).q ≤ 15 ∨ 25 ≤ (class1SlopeDatum ctx).q) →
    (class1SlopeDatum ctx).q ∉ class1ClosedModuli →
    ¬ Class1DatumClosed ctx →
    ¬ Class1GcdWindowMiss ctx →
    (class1SlopeDatum ctx).q < 101 →
    (ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx) →
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅
  /-- CNL / class 1 - tail (`101 ≤ q`); verbatim field. -/
  class1DeepTail : ∀ ctx : ActualFailureContext,
    101 ≤ (class1SlopeDatum ctx).q →
    Class1Band4FreePeriod ctx
    ∨ (64 ∣ shellLadderDepth ctx →
        9 ≤ (class1SlopeDatum ctx).q →
        ((class1SlopeDatum ctx).q ≤ 15 ∨ 25 ≤ (class1SlopeDatum ctx).q) →
        (class1SlopeDatum ctx).q ∉ class1ClosedModuli →
        ¬ Class1DatumClosed ctx →
        ¬ Class1GcdWindowMiss ctx →
        routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅)
  /-- DensePack / class 3 - verbatim field. -/
  densePackUngated : DensePackUngatedClosureResidual

namespace Erdos260AnchoredCountResidual

/-- Tower lane — the wave-5 enumeration residual (verbatim charge-capstone walk). -/
def towerEnum (R : Erdos260AnchoredCountResidual) : TowerModulusEnumerationResidual := by
  intro ctx _hdeep hesc
  have hescV2 : TowerModulusEnumEscapeV2 ctx :=
    (towerModulusEnumEscape_iff_v2 ctx).mp hesc
  have haper : ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx := fun hu7 hwp =>
    thirdsLever_windowPeriodic_void_of_oddpartQ_le_seven ctx hu7 hwp
  rcases Nat.lt_or_ge (class1SlopeDatum ctx).q 107 with hlt | hge
  · exact R.towerEnumLow ctx hescV2 hlt haper
  · cases R.towerEnumTail ctx hescV2 hge haper with
    | inl ho => exact towerTail_of_order_gt ctx ho.1 ho.2
    | inr hineq => exact hineq

/-- Run lane — the wave-5 settlement hypothesis (verbatim charge-capstone walk). -/
def runNumeric (R : Erdos260AnchoredCountResidual) : RunCycleNumericSettlementHyp := by
  intro ctx _hr
  rcases Nat.lt_or_ge (class1SlopeDatum ctx).q 64 with hlt | hge
  · exact R.runNumericLow ctx hlt
  · cases R.runNumericTail ctx hge with
    | inl ho => exact Or.inr (runTail_of_order_gt ctx ho.1 ho.2)
    | inr hrun => exact hrun

/-- Class-0 lane — the wave-3 windowed cycle check (verbatim charge-capstone walk). -/
def class0Cycle (R : Erdos260AnchoredCountResidual) :
    ∀ ctx : ActualFailureContext, Class0WindowCycleCheck ctx :=
  class0Cycle_of_survivor_residue_split R.class0Survivor R.class0Mid
    (fun ctx h96 => by
      cases R.class0BigOrder ctx h96 with
      | inl hcert =>
          obtain ⟨C, horder, hcheck⟩ := hcert
          exact class0Tail_of_order_gt ctx C horder hcheck
      | inr hwin => exact hwin)

/-- Class-1 lane — the wave-3 deep residual (verbatim charge-capstone walk). -/
def class1Deep (R : Erdos260AnchoredCountResidual) : Class1DeepResidual :=
  class1DeepResidual_of_pairResidual (class1PairResidual_of_deepOnly
    (fun ctx _hr hdvd h9 hwin hcl hdc hgcd => by
      have haper : ordCompl[2] ctx.Q ≤ 7 → ¬ WindowPeriodic ctx := fun hu7 hwp =>
        thirdsLever_windowPeriodic_void_of_oddpartQ_le_seven ctx hu7 hwp
      rcases Nat.lt_or_ge (class1SlopeDatum ctx).q 101 with hlt | hge
      · exact R.class1DeepLow ctx hdvd h9 hwin hcl hdc hgcd hlt haper
      · cases R.class1DeepTail ctx hge with
        | inl hfree => exact class1Tail_of_band4FreePeriod ctx hfree
        | inr hdeep => exact hdeep hdvd h9 hwin hcl hdc hgcd))

/-- The wave-3 4-way gate disjunction from the surface gates field (verbatim walk). -/
def returnGatesCycle (R : Erdos260AnchoredCountResidual) :
    ∀ ctx : ActualFailureContext, ReturnGatesBody ctx := fun ctx => by
  by_cases hfree : ReturnB2FreeDatum ctx
  · exact (returnCtxAllFour_of_b2FreeDatum ctx hfree).1
  · by_cases hone : ReturnB2OneSpacedDatum ctx
    · exact (returnGatesZeroCard_of_b2OneSpacedDatum ctx hone).1
    · by_cases hnum : 64 * (((supportShell ctx.shell.d ctx.shell.X).card
            + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1))
          < 2 * (129 * shellLadderDepth ctx + 64)
      · exact returnGatesBody_of_reach_numeric ctx hnum
      · exact (returnGatesBody_iff_ungated ctx).mpr
          (R.returnGates ctx hfree hone (not_lt.mp hnum))

/-- The class-4 population bound `|olcFibre| ≤ r + 1` from the gates — the `hnumeric`
supplier of the unconditional charge. -/
theorem fibreSmall (R : Erdos260AnchoredCountResidual) : Class4FibreSmall :=
  class4FibreSmall_of_gates R.returnGatesCycle

/-- The per-ctx K.1 interior: the band-2-free regime closed by the chain's own closure, the
rest from the surface field (verbatim charge-capstone walk). -/
def interiorAt (R : Erdos260AnchoredCountResidual) (ctx : ActualFailureContext) :
    ReturnInteriorBody ctx := by
  by_cases hfree : ReturnB2FreeDatum ctx
  · exact (returnCtxAllFour_of_b2FreeDatum ctx hfree).2.2.2
  · exact R.returnInterior ctx hfree

/-- **THE SPLICE — the Return slot with the Return lane CLOSED**: the V3 Return charge from
the counts alone (`Class4ReturnPerSliceCharge.ofCountsOnly`): interior from `returnInterior`,
population from `returnGates`, NO envelope demand, NO digit demand. -/
def returnCharge (R : Erdos260AnchoredCountResidual) :
    ∀ ctx : ActualFailureContext, Class4ReturnPerSliceCharge ctx :=
  fun ctx => Class4ReturnPerSliceCharge.ofCountsOnly ctx (R.interiorAt ctx) (R.fibreSmall ctx)

/-- The Return capacity floor — the SAME class-4 ledger contribution every predecessor route
delivers, now from the kept fields alone. -/
theorem returnFloor (R : Erdos260AnchoredCountResidual) (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 4
      ≤ erdos260Constants.cStar * erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  (R.returnCharge ctx).returnFloor

/-- The V3 tower count of the budget (verbatim charge-capstone walk). -/
def towerCountV3 (R : Erdos260AnchoredCountResidual) :
    ∀ ctx : ActualFailureContext, Class2ActiveFloorCount ctx :=
  p9V3TowerCount_ofShallowDeep
    (towerDeepResidual_ofCountBound (towerCountBound_of_modulusEnumeration R.towerEnum))

/-- The Run max-core family of the budget (verbatim charge-capstone walk). -/
def runCore (R : Erdos260AnchoredCountResidual) :
    ∀ ctx : ActualFailureContext, RunClass5LeafSupportMaxCoreResidual ctx :=
  fun ctx => (runSplitOfNumeric (runCycleNumericField_settled R.runNumeric) ctx).toCore

/-- The V3 run chain of the budget (verbatim charge-capstone walk). -/
def runChain (R : Erdos260AnchoredCountResidual) :
    ∀ ctx : ActualFailureContext, RunClass5StageChain ctx :=
  p9V3RunChainOfResidual (runClass5LeafResidual_ofSupportMaxCoreResidual R.runCore)

/-- **The anchored-count budget** — `v3Budget` with the Return slot carried by the
unconditional charge. -/
def budget (R : Erdos260AnchoredCountResidual) :
    ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx :=
  v3Budget R.towerCountV3 R.runChain R.returnCharge

/-- Class-0 routed emptiness at the anchored-count budget (budget-generic bridge). -/
theorem class0Empty (R : Erdos260AnchoredCountResidual) : Class0FibreEmpty R.budget :=
  class0FibreEmpty_of_genuineRoute_pinned R.budget (fun _ => rfl)
    (class0Pinned_field_iff_windowCycleCheck.mpr R.class0Cycle)

/-- Class-1 routed emptiness at the anchored-count budget (charge-family-generic bridge). -/
theorem class1Empty (R : Erdos260AnchoredCountResidual) : Class1FibreEmpty R.budget :=
  class1FibreEmpty_of_pinned_arithmetic_sharp R.towerCountV3 R.runChain R.returnCharge
    (class1Pinned_of_deepResidual R.class1Deep)

/-- The corrected DensePack residue at the anchored-count budget (budget-generic walk). -/
def densePackCorrected (R : Erdos260AnchoredCountResidual) :
    DensePackCorrectedResidue R.budget :=
  (R.densePackUngated.toGatedClosure.toDatumSplit.toCycleSplit.toRegimeSplit R.budget).toCorrected

/-- **The ctx-pinned P9 ledger from the anchored-count surface** — exactly the charge
capstone's `toLedger`, with the Return slot carried by the unconditional charge. -/
def toLedger (R : Erdos260AnchoredCountResidual) : P9CtxPinnedLedgerResidual where
  budget := R.budget
  hChernoff :=
    (ChernoffGenuineAreaKraftSmallResidual.ofClass0FibreEmpty R.budget
      R.class0Empty).hChernoffField
  hCnl := (hCnlField_iff_class1FibreEmpty R.budget).mpr R.class1Empty
  hDensePack := R.densePackCorrected.hDensePackField (fun _ => rfl)
  hTRT := seedHTRT R.budget
  hOldRes := fun ctx => by
    show routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 6
        ≤ ∑ k ∈ oldResIdxVal ctx, oldResAtVal ctx k
    rw [genuineChargeRoute_routed6_zero ctx]
    exact oldResL65_branchMass_nonneg ctx

/-- The final statement from the anchored-count surface. Composition only. -/
theorem toStatement (R : Erdos260AnchoredCountResidual) : Erdos260Statement :=
  R.toLedger.toStatement

end Erdos260AnchoredCountResidual

/-- **THE ANCHORED-COUNT ENDPOINT — the Return lane CLOSED**: `Erdos260Statement` from the
12-field surface with NO Return-zero / envelope / digit / key-injectivity field of any kind.
The Return lane is carried by `returnGates` (population) and `returnInterior` (K.1 boundary)
alone — fields every capstone surface since wave 3 demands verbatim. -/
theorem erdos260_of_anchoredCount (R : Erdos260AnchoredCountResidual) :
    Erdos260Statement :=
  R.toStatement

/-- **The weakening witness**: the charge-capstone surface yields the anchored-count surface
by DELETING the `returnDirtyEnvelope` field (12 fields verbatim).  The new surface demands
strictly less. -/
def anchoredCountResidual_of_returnChargeResidual (R : Erdos260ReturnChargeResidual) :
    Erdos260AnchoredCountResidual where
  towerEnumLow := R.towerEnumLow
  towerEnumTail := R.towerEnumTail
  runNumericLow := R.runNumericLow
  runNumericTail := R.runNumericTail
  returnGates := R.returnGates
  returnInterior := R.returnInterior
  class0Survivor := R.class0Survivor
  class0Mid := R.class0Mid
  class0BigOrder := R.class0BigOrder
  class1DeepLow := R.class1DeepLow
  class1DeepTail := R.class1DeepTail
  densePackUngated := R.densePackUngated

/-- The converse reconstruction REQUIRES the anchored dirty atom: the anchored-count surface
plus `AnchoredDirtyEnvelopeField` rebuilds the full charge-capstone surface (through the
anchored-to-self-referential bridge).  Recorded for the comparison; the endpoint above never
needs it. -/
def returnChargeResidual_of_anchoredCount (R : Erdos260AnchoredCountResidual)
    (henv : AnchoredDirtyEnvelopeField) : Erdos260ReturnChargeResidual where
  towerEnumLow := R.towerEnumLow
  towerEnumTail := R.towerEnumTail
  runNumericLow := R.runNumericLow
  runNumericTail := R.runNumericTail
  returnGates := R.returnGates
  returnDirtyEnvelope := returnDirtyEnvelopeField_of_anchoredField henv
  returnInterior := R.returnInterior
  class0Survivor := R.class0Survivor
  class0Mid := R.class0Mid
  class0BigOrder := R.class0BigOrder
  class1DeepLow := R.class1DeepLow
  class1DeepTail := R.class1DeepTail
  densePackUngated := R.densePackUngated

/-- Nonempty transport from the charge surface (one direction; the converse needs no
transport — the new surface is reached by deletion). -/
theorem nonempty_anchoredCountResidual_of_returnCharge
    (h : Nonempty Erdos260ReturnChargeResidual) :
    Nonempty Erdos260AnchoredCountResidual :=
  h.elim fun R => ⟨anchoredCountResidual_of_returnChargeResidual R⟩

/-! ## Part 7.  Machine-readable status (honest) -/

/-- Honest machine-readable status of the anchored-key count pass. -/
def anchoredKeyCountStatus : List String :=
  [ "DICTIONARY VERDICT (confirmed): liftLevelBound X IS the manuscript log* envelope - " ++
      "liftLevel is the tower delta -> delta + 2^delta (ReturnM2J4Core), liftLevelBound L " ++
      "the least k with L < liftLevel k, and IsLiftChain.card_le is the PROVED chain bound: " ++
      "any finite set pairwise separated by x + 2^x <= y and bounded by L has card <= " ++
      "liftLevelBound L.  The manuscript M_L per-slice count is exactly the maximal " ++
      "nesting-chain length below the scale.",
    "ANCHORED KEY CHOSEN: anchoredResidueKey ctx = k % 2^(carryVal2 k) - the " ++
      "self-referential key (carryVal2 k, k % 2^(carryVal2 k)) with the LEVEL coordinate " ++
      "deleted (anchoredResidueKey_coarsens_selfRef).  Same-slice members may carry " ++
      "DIFFERENT carryVal2 - the M.2.1 nesting dimension is ALIVE at this key, unlike the " ++
      "self-referential key where wave 13 proved equal levels kill the growth.",
    "NESTING CONGRUENCE LINK (PROVED, goal 2): on (Z)-clean anchored slices the manuscript " ++
      "lift congruence delta_{i+1} = delta_i mod 2^(delta_i) is DERIVED from the carry " ++
      "machinery - all-pairs zero-runs (sliceZClean_pair_zeroRun, key-generic), valuation " ++
      "telescoping carryVal2 z = carryVal2 x + (z - x) (sliceZClean_carryVal2_add, the lift " ++
      "identity all-pairs form), gap divisibility 2^(carryVal2 x) | (z - x) " ++
      "(anchoredClean_gapDiv, the anchored cousin of returnSelfRefKey_gapDiv), hence " ++
      "anchoredClean_lift_congruence AND the tower growth carryVal2 x + 2^(carryVal2 x) <= " ++
      "carryVal2 z (anchoredClean_nesting_growth) on every ordered pair.",
    "CROSSING BOUND LINK (PROVED on the clean class, goal 2): clean anchored slices are " ++
      "crossing-FREE (anchoredClean_crossingFree) - the M.2.1 endpoint-pinning content is a " ++
      "THEOREM at this key, with no hmono atom (the ReturnCarryEndpointCore / " ++
      "OlcSliceData.ofAnchoredKey input) consumed; cleanness itself pins the endpoint.  " ++
      "Dirty-slice crossings route to the dirty package, as the manuscript (Z) " ++
      "routing-predicate remark prescribes.",
    "THE CLEAN COUNT (PROVED - the headline): anchoredCleanSliceCard_le - every (Z)-clean " ++
      "slice of the anchored residue key obeys the (M.1) envelope |slice| <= liftLevelBound " ++
      "X, unconditionally: translated member positions k - min form an IsLiftChain bounded " ++
      "by the window width W - 1 < W <= X (olcFibre_mem_window + " ++
      "supportShell_card_le_length), and IsLiftChain.card_le counts.  This is the genuine " ++
      "multi-member M.2.1 nesting count on actual fibre slices - the first in-tree " ++
      "realization (wave 13: the self-referential clean count is singletons; the in-tree " ++
      "nesting/crossing constructors all consumed unproved slice inputs).",
    "DIRTY EXHAUSTION (atom + bridge): AnchoredSliceDirtyEnvelope (dirty anchored slices " ++
      "obey the envelope) remains the honest residual of the manuscript-faithful route - " ++
      "the in-tree dirty package counts constructed crossing families, not actual fibre " ++
      "slices (DirtyWindowCountCore finding; unchanged).  With the atom: ALL anchored " ++
      "slices counted (anchoredSliceCard_le), the charge rebuilds at the anchored key " ++
      "(Class4ReturnPerSliceCharge.ofAnchoredEnvelope), and the atom IMPLIES the wave-13 " ++
      "self-referential atom (sliceDirtyEnvelope_of_anchoredEnvelope: a dirty selfRef slice " ++
      "has >= 2 equal-level members, so its enclosing anchored slice is not clean; field " ++
      "form returnDirtyEnvelopeField_of_anchoredField).  NO converse, and NO derivation " ++
      "from ReturnKeyInjOn: selfRef injectivity says nothing about multi-level anchored " ++
      "slices - the demands are incomparable.",
    "THE JUNCTION COLLAPSE (the big finding - the Return lane CLOSES): " ++
      "Class4ReturnPerSliceCharge carries its key as a FIELD and the numeric bridge " ++
      "return_hnumeric_of_fibre_card_le is KEY-GENERIC, consuming only |olcFibre| <= r + 1 " ++
      "(Class4FibreSmall, supplied by the KEPT returnGates field via " ++
      "class4FibreSmall_of_gates).  At the maximally refined anchored key k -> k (each " ++
      "return start its own exact anchor class) every slice is a singleton BY DEFINITION " ++
      "(refinedAnchoredKey_slice_card_le_one), OlcSliceData.ofCardLe applies with 1 <= " ++
      "liftLevelBound X, and the FULL charge rebuilds from the counts alone " ++
      "(Class4ReturnPerSliceCharge.ofCountsOnly) - no envelope, no digit, no clean-step, " ++
      "no key-injectivity, no dirty demand.  The manuscript needs the per-slice log* " ++
      "envelope because its anchor classes are few against an O(X)-sized family; the " ++
      "formalized class-4 fibre is gated to <= r + 1 members, so the slice-key bookkeeping " ++
      "factor #sliceKeys <= r + 1 is absorbed by the proved budget " ++
      "return_hnumeric_of_key_card_le_succ_r ((r+1)(L+1)(r+1)(L+B+1) <= 31*2^L/1536 on " ++
      "every failure shell).",
    "THE ENDPOINT (DELIVERED): Erdos260AnchoredCountResidual = Erdos260ReturnChargeResidual " ++
      "with the returnDirtyEnvelope field DELETED (12 fields, all verbatim wave-12 shapes); " ++
      "erdos260_of_anchoredCount : Erdos260AnchoredCountResidual -> Erdos260Statement.  The " ++
      "Return lane of the capstone surface is carried by returnGates + returnInterior " ++
      "ONLY - fields every capstone surface since wave 3 demands.  The Return-zero / " ++
      "envelope / digit lane (returnZero -> returnKeyInjective -> returnDirtyEnvelope, " ++
      "waves 1..14) is CLOSED UNCONDITIONALLY at the charge junction.  Weakening witness " ++
      "anchoredCountResidual_of_returnChargeResidual (field deletion); converse " ++
      "returnChargeResidual_of_anchoredCount needs the anchored atom (recorded; the " ++
      "endpoint never consumes it).",
    "HONEST ACCOUNTING of what did NOT close: (a) AnchoredSliceDirtyEnvelope - the " ++
      "dirty-slice (M.1) count at the anchored residue key - remains an atom on the " ++
      "manuscript-faithful (non-refined-key) route; it is BYPASSED by the junction " ++
      "collapse, not proved.  (b) The crossing O_Q(1) bound on DIRTY slices (the hmono " ++
      "endpoint-pinning atom of ReturnCarryEndpointCore) remains an input in-tree; this " ++
      "route never consumes it.  (c) The remaining demanded fields of the endpoint surface " ++
      "are the unchanged non-Return lanes (tower enum tails, run numerics, class-0 cycle " ++
      "checks, class-1 deep emptiness, densePack ungated fields) plus returnGates / " ++
      "returnInterior.",
    "HYGIENE: new module, additive only - no existing file edited, root import untouched " ++
      "(module builds standalone as Erdos260.AnchoredKeyCount); no sorry / admit / new " ++
      "axiom / native_decide; all key declarations in #print axioms blocks reporting " ++
      "[propext, Classical.choice, Quot.sound] or fewer." ]

theorem anchoredKeyCountStatus_nonempty : anchoredKeyCountStatus ≠ [] := by
  simp [anchoredKeyCountStatus]

/-! ## Part 8.  Axiom-cleanliness audit -/

#print axioms anchoredResidueKey
#print axioms anchoredResidueKey_coarsens_selfRef
#print axioms sliceZClean_pair_zeroRun
#print axioms sliceZClean_carryVal2_add
#print axioms anchoredClean_crossingFree
#print axioms anchoredClean_gapDiv
#print axioms anchoredClean_lift_congruence
#print axioms anchoredClean_nesting_growth
#print axioms anchoredCleanSliceCard_le
#print axioms AnchoredSliceDirtyEnvelope
#print axioms anchoredSliceCard_le
#print axioms sliceDirtyEnvelope_of_anchoredEnvelope
#print axioms AnchoredDirtyEnvelopeField
#print axioms returnDirtyEnvelopeField_of_anchoredField
#print axioms Class4ReturnPerSliceCharge.ofAnchoredEnvelope
#print axioms refinedAnchoredKey_slice_card_le_one
#print axioms Class4ReturnPerSliceCharge.ofCountsOnly
#print axioms Erdos260AnchoredCountResidual.towerEnum
#print axioms Erdos260AnchoredCountResidual.runNumeric
#print axioms Erdos260AnchoredCountResidual.class0Cycle
#print axioms Erdos260AnchoredCountResidual.class1Deep
#print axioms Erdos260AnchoredCountResidual.returnGatesCycle
#print axioms Erdos260AnchoredCountResidual.fibreSmall
#print axioms Erdos260AnchoredCountResidual.interiorAt
#print axioms Erdos260AnchoredCountResidual.returnCharge
#print axioms Erdos260AnchoredCountResidual.returnFloor
#print axioms Erdos260AnchoredCountResidual.budget
#print axioms Erdos260AnchoredCountResidual.class0Empty
#print axioms Erdos260AnchoredCountResidual.class1Empty
#print axioms Erdos260AnchoredCountResidual.toLedger
#print axioms Erdos260AnchoredCountResidual.toStatement
#print axioms erdos260_of_anchoredCount
#print axioms anchoredCountResidual_of_returnChargeResidual
#print axioms returnChargeResidual_of_anchoredCount
#print axioms nonempty_anchoredCountResidual_of_returnCharge
#print axioms anchoredKeyCountStatus_nonempty

end

end Erdos260
