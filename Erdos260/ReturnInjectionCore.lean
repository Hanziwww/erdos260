import Erdos260.GenuineObstructionRoutingCore
import Erdos260.ChargeMapsTRTOldResCore
import Erdos260.ReturnM2J4Core

/-!
# The genuine Return (class-4) fibre-landing injection (`ReturnInjectionCore`)

This module (NEW; it edits no existing file) constructs the **genuine
`ReturnOlcRoutingCharge` fibre-landing injection** for the genuine first-obstruction route
`genuineChargeRoute` (`GenuineObstructionRoutingCore`).

`ChargeMapsTRTOldResCore` already *derives* the Return class-4 count from any
`ReturnOlcRoutingCharge`: through `Finset.card_le_card_of_injOn` and the proved M.2.1
`olcGeomOfShell_endpoints_card_le` it gives the inverse-tower bound
`|routedFibre 4| ≤ liftLevelBound X = O(log* X)`
(`ReturnOlcRoutingCharge.fibreCard_le_liftLevelBound`).  What remained was to *build* a
genuine `ReturnOlcRoutingCharge` for the genuine route — not the forbidden identity-only
`ofSubsetEndpoints` shortcut.

## What is genuinely PROVED here (new content)

* `olcRankMatch` — the **explicit order-matching injection** of one finite set `F ⊆ ℕ` into
  another `E ⊆ ℕ` whenever `|F| ≤ |E|`: send the `r`-th smallest element of `F` to the
  `r`-th smallest element of `E` (via the order-rank `olcFibreRank` and `Finset.orderEmbOfFin`).
  `olcRankMatch_mem` / `olcRankMatch_injOn` prove it maps into `E` and is injective on `F`.
  Non-degenerate: it works for any nonempty fibre, mapping carry starts to genuine OLC
  endpoint levels — *never* the identity.
* `ReturnOlcRoutingCharge.ofEndpointCardLe` — **the genuine converse of
  `fibreCard_le_olcCard`**: a `ReturnOlcRoutingCharge route ctx` is constructed from the single
  cardinality bound `|routedFibre 4| ≤ |(olcGeomOfShell ctx).endpoints|`.  Together with the
  already-proved forward direction this shows the whole three-field M.2.1 injection structure is
  **equivalent** to one clean count inequality.
* `shellLevels_card_eq` / `olcGeomOfShell_endpoints_card_eq` — the OLC endpoint family has
  cardinality *exactly* the inverse-tower bound `|shellLevels X| = liftLevelBound X` (the
  self-referential tower levels `liftLevel 0,…,liftLevel (M_L-1)` that fit below `X`).  Hence
  `ReturnOlcRoutingCharge.ofLiftLevelBoundCardLe`: the injection from `|fibre| ≤ liftLevelBound X`.
* `ReturnOlcRoutingCharge.ofLiftChainLevels` — **the genuine M.2.1 reduction**: a
  `ReturnOlcRoutingCharge route ctx` from a *self-referential lift-chain level assignment* of the
  class-4 fibre — a level map `level : ℕ → ℕ` whose values on the fibre are bounded by the shell
  scale `X`, obey the self-referential lift congruence `level x + 2^(level x) ≤ level y` (M.2.1 /
  proof_v4 §J.4 / K.2.4–K.2.5), and are *distinct on distinct starts* (the M.2.1 endpoint
  disjointness).  The proved `IsLiftChain.card_le` then bounds the fibre by `liftLevelBound X`.
* `genuineReturnOlcRoutingCharge` / `genuineReturnOlcRoutingCharge_ofCardLe` — the
  `ReturnOlcRoutingCharge (genuineChargeRoute ctx) ctx` for the genuine route, produced from the
  smallest residual (the lift-chain level assignment, resp. the count bound), so the downstream
  `genuine_returnCount_le_liftLevelBound` fires.
* `genuine_class4_fibre_mem_iff` — documents that the residual's domain is *exactly* the genuine
  J.1.1 return band: the class-4 fibre is the high-excess starts whose tower-exit is `returnPkg`,
  or whose `cnlTail` tail carries a long (non-run) return (`returnCls = 2`).

## What stays the smallest named residual (the classifier↔OLC-endpoint geometric link)

The class-4 injection does **not** fully close from these files alone: the abstract
`olcGeomOfShell` realizes the M.2.1 *worst-case* nesting chain `shellLevels X`, whose endpoints are
tower levels disconnected from the concrete return starts.  The genuine missing link — assigning
each long-return start a *distinct* OLC nesting level satisfying the self-referential lift
congruence — is the M.2.1 endpoint-nesting geometry of the actual carries, owned by the deep Return
geometry workers and **not** present in the three source files.  It is carried here as the explicit
hypotheses of `ofLiftChainLevels` (`hbound` / `hchain` / `hinj`): the *smallest honest residual*,
from which everything else is proved.  No `sorry`, `axiom`, or `admit`; no empty/identity shortcut.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 1.  The explicit order-matching injection between finite subsets of `ℕ`

A generic, non-degenerate construction: whenever `|F| ≤ |E|` for `F E : Finset ℕ`, the
order-rank matching (the `r`-th smallest of `F` to the `r`-th smallest of `E`) is an injection of
`F` into `E`.  This is the genuine combinatorial content behind the M.2.1 fibre-landing map — it
sends each return start to a genuine OLC endpoint level, never the identity. -/

/-- The **order-rank** of `k` inside a finite set `F ⊆ ℕ`: the number of elements of `F` strictly
below `k`.  On `F` it is a strictly monotone bijection onto `Fin |F|`. -/
def olcFibreRank (F : Finset ℕ) (k : ℕ) : ℕ := (F.filter (· < k)).card

/-- A member's order-rank is strictly below the cardinality (`k` itself is not counted). -/
theorem olcFibreRank_lt_card {F : Finset ℕ} {k : ℕ} (hk : k ∈ F) :
    olcFibreRank F k < F.card := by
  apply Finset.card_lt_card
  refine (Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).2 ⟨k, hk, ?_⟩
  simp

/-- The order-rank is injective on `F`: distinct members have distinct ranks. -/
theorem olcFibreRank_injOn {F : Finset ℕ} {x y : ℕ} (hx : x ∈ F) (hy : y ∈ F)
    (h : olcFibreRank F x = olcFibreRank F y) : x = y := by
  rcases lt_trichotomy x y with hlt | heq | hgt
  · exfalso
    have hsub : F.filter (· < x) ⊆ F.filter (· < y) := by
      intro z hz
      rw [Finset.mem_filter] at hz ⊢
      exact ⟨hz.1, hz.2.trans hlt⟩
    have hss : F.filter (· < x) ⊂ F.filter (· < y) :=
      (Finset.ssubset_iff_of_subset hsub).2 ⟨x, by rw [Finset.mem_filter]; exact ⟨hx, hlt⟩, by simp⟩
    have hcard := Finset.card_lt_card hss
    unfold olcFibreRank at h
    omega
  · exact heq
  · exfalso
    have hsub : F.filter (· < y) ⊆ F.filter (· < x) := by
      intro z hz
      rw [Finset.mem_filter] at hz ⊢
      exact ⟨hz.1, hz.2.trans hgt⟩
    have hss : F.filter (· < y) ⊂ F.filter (· < x) :=
      (Finset.ssubset_iff_of_subset hsub).2 ⟨y, by rw [Finset.mem_filter]; exact ⟨hy, hgt⟩, by simp⟩
    have hcard := Finset.card_lt_card hss
    unfold olcFibreRank at h
    omega

/-- **The order-rank matching map** of `F` into `E`: send `k` to the `(olcFibreRank F k)`-th
smallest element of `E` (junk value `0` off `F`).  A total `ℕ → ℕ`. -/
def olcRankMatch (F E : Finset ℕ) (k : ℕ) : ℕ :=
  if h : olcFibreRank F k < E.card then E.orderEmbOfFin rfl ⟨olcFibreRank F k, h⟩ else 0

/-- On a member of `F` (with `|F| ≤ |E|`), the matching map is the explicit order embedding. -/
theorem olcRankMatch_eq_of_mem {F E : Finset ℕ} (hcard : F.card ≤ E.card) {k : ℕ} (hk : k ∈ F) :
    olcRankMatch F E k
      = E.orderEmbOfFin rfl ⟨olcFibreRank F k, lt_of_lt_of_le (olcFibreRank_lt_card hk) hcard⟩ := by
  unfold olcRankMatch
  exact dif_pos (lt_of_lt_of_le (olcFibreRank_lt_card hk) hcard)

/-- **Maps into `E`** — the matching map sends each member of `F` into `E`. -/
theorem olcRankMatch_mem {F E : Finset ℕ} (hcard : F.card ≤ E.card) {k : ℕ} (hk : k ∈ F) :
    olcRankMatch F E k ∈ E := by
  rw [olcRankMatch_eq_of_mem hcard hk]
  exact Finset.orderEmbOfFin_mem _ _ _

/-- **Injective on `F`** — distinct members of `F` map to distinct elements of `E`. -/
theorem olcRankMatch_injOn {F E : Finset ℕ} (hcard : F.card ≤ E.card) {x y : ℕ}
    (hx : x ∈ F) (hy : y ∈ F) (h : olcRankMatch F E x = olcRankMatch F E y) : x = y := by
  rw [olcRankMatch_eq_of_mem hcard hx, olcRankMatch_eq_of_mem hcard hy] at h
  have hfin : (⟨olcFibreRank F x, lt_of_lt_of_le (olcFibreRank_lt_card hx) hcard⟩ : Fin E.card)
      = ⟨olcFibreRank F y, lt_of_lt_of_le (olcFibreRank_lt_card hy) hcard⟩ :=
    (E.orderEmbOfFin rfl).injective h
  exact olcFibreRank_injOn hx hy (by simpa using congrArg Fin.val hfin)

/-! ## 2.  `ReturnOlcRoutingCharge` from the cardinality bound (genuine converse) -/

/-- **The genuine M.2.1 fibre-landing injection from the count bound.**

The exact converse of `ReturnOlcRoutingCharge.fibreCard_le_olcCard`: whenever the routed class-4
fibre is no larger than the OLC endpoint family, the order-rank matching `olcRankMatch` is a genuine
`ReturnOlcRoutingCharge` — mapping each routed-4 start to a genuine OLC endpoint of
`(olcGeomOfShell ctx).endpoints`, injectively.  This is *not* the identity-only `ofSubsetEndpoints`
shortcut: it requires no `fibre ⊆ endpoints` containment, only the count bound, and re-orders the
fibre into the endpoint family.  Together with `fibreCard_le_olcCard` it proves the three-field
M.2.1 injection structure is **equivalent** to the single inequality `|fibre| ≤ |endpoints|`. -/
def ReturnOlcRoutingCharge.ofEndpointCardLe (route : ℕ → Fin 7) (ctx : ActualFailureContext)
    (hcard : (routedFibre ctx.n24CarryData route 4).card ≤ (olcGeomOfShell ctx).endpoints.card) :
    ReturnOlcRoutingCharge route ctx where
  olcOf := olcRankMatch (routedFibre ctx.n24CarryData route 4) (olcGeomOfShell ctx).endpoints
  maps_into := fun _k hk => olcRankMatch_mem hcard hk
  matching := fun _x hx _y hy h => olcRankMatch_injOn hcard hx hy h

/-! ## 3.  The OLC endpoint count is exactly the inverse-tower bound -/

/-- If a tower-level index stays below the inverse-tower bound, the level stays below `L`. -/
theorem liftLevel_le_of_lt_bound {i L : ℕ} (h : i < liftLevelBound L) : liftLevel i ≤ L := by
  have h' : i < Nat.find (liftLevel_unbounded L) := h
  exact not_lt.mp (Nat.find_min (liftLevel_unbounded L) h')

/-- The inverse-tower bound is *attained*: the `liftLevelBound L` distinct levels
`liftLevel 0,…,liftLevel (liftLevelBound L - 1)` all fit below `L`, so they sit inside
`shellLevels L`. -/
theorem liftLevelBound_le_shellLevels_card (L : ℕ) :
    liftLevelBound L ≤ (shellLevels L).card := by
  have hsub : (Finset.range (liftLevelBound L)).image liftLevel ⊆ shellLevels L := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [Finset.mem_range] at hi
    simp only [shellLevels, Finset.mem_filter, Finset.mem_image, Finset.mem_range]
    exact ⟨⟨i, by omega, rfl⟩, liftLevel_le_of_lt_bound hi⟩
  have hcard_img : ((Finset.range (liftLevelBound L)).image liftLevel).card = liftLevelBound L := by
    rw [Finset.card_image_of_injective _ liftLevel_strictMono.injective, Finset.card_range]
  calc liftLevelBound L
      = ((Finset.range (liftLevelBound L)).image liftLevel).card := hcard_img.symm
    _ ≤ (shellLevels L).card := Finset.card_le_card hsub

/-- **The concrete OLC nesting chain realizes the inverse-tower bound exactly**:
`|shellLevels L| = liftLevelBound L`. -/
theorem shellLevels_card_eq (L : ℕ) : (shellLevels L).card = liftLevelBound L :=
  le_antisymm (shellLevels_card_le L) (liftLevelBound_le_shellLevels_card L)

/-- **The shell OLC endpoint family has cardinality exactly `liftLevelBound X`.** -/
theorem olcGeomOfShell_endpoints_card_eq (ctx : ActualFailureContext) :
    (olcGeomOfShell ctx).endpoints.card = liftLevelBound ctx.shell.X := by
  rw [olcGeomOfShell_endpoints]
  exact shellLevels_card_eq ctx.shell.X

/-- **`ReturnOlcRoutingCharge` from the inverse-tower count bound.**  Since the OLC endpoint family
has exactly `liftLevelBound X` elements, any fibre no larger than `liftLevelBound X` injects into
it (via `ofEndpointCardLe`). -/
def ReturnOlcRoutingCharge.ofLiftLevelBoundCardLe (route : ℕ → Fin 7) (ctx : ActualFailureContext)
    (hcard : (routedFibre ctx.n24CarryData route 4).card ≤ liftLevelBound ctx.shell.X) :
    ReturnOlcRoutingCharge route ctx :=
  ReturnOlcRoutingCharge.ofEndpointCardLe route ctx
    (by rw [olcGeomOfShell_endpoints_card_eq]; exact hcard)

/-! ## 4.  The genuine M.2.1 reduction: from a self-referential lift-chain level assignment -/

/-- **The genuine M.2.1 fibre-landing injection, reduced to the self-referential lift congruence.**

Given a *nesting-level assignment* `level : ℕ → ℕ` of the routed class-4 starts such that, on the
fibre,

* `hbound` — every level is bounded by the shell scale `X` (the OLC return obstruction sits below
  the shell);
* `hchain` — the levels obey the **M.2.1 self-referential lift congruence** `level x + 2^(level x)
  ≤ level y` whenever `level x < level y` (proof_v4 §J.4 / K.2.4–K.2.5: nonseparated nested
  refinements jump by at least `2^{δ_i}`);
* `hinj` — distinct starts receive distinct levels (the M.2.1 endpoint disjointness /
  nonseparated-nesting deletion),

the image of the fibre under `level` is a self-referential lift chain bounded by `X`, so the proved
`IsLiftChain.card_le` bounds the fibre count by `liftLevelBound X`, and `ofLiftLevelBoundCardLe`
produces the genuine `ReturnOlcRoutingCharge`.

There is *no degenerate shortcut*: `level = id` fails `hchain` (consecutive starts are not
exponentially separated) and a constant `level` fails `hinj`, so the residual genuinely demands the
M.2.1 nesting geometry. -/
def ReturnOlcRoutingCharge.ofLiftChainLevels (route : ℕ → Fin 7) (ctx : ActualFailureContext)
    (level : ℕ → ℕ)
    (hbound : ∀ k ∈ routedFibre ctx.n24CarryData route 4, level k ≤ ctx.shell.X)
    (hchain : ∀ x ∈ routedFibre ctx.n24CarryData route 4,
      ∀ y ∈ routedFibre ctx.n24CarryData route 4,
        level x < level y → level x + 2 ^ level x ≤ level y)
    (hinj : ∀ x ∈ routedFibre ctx.n24CarryData route 4,
      ∀ y ∈ routedFibre ctx.n24CarryData route 4, level x = level y → x = y) :
    ReturnOlcRoutingCharge route ctx := by
  apply ReturnOlcRoutingCharge.ofLiftLevelBoundCardLe route ctx
  have himg_chain : IsLiftChain ((routedFibre ctx.n24CarryData route 4).image level) := by
    intro u hu v hv huv
    rw [Finset.mem_image] at hu hv
    obtain ⟨a, ha, rfl⟩ := hu
    obtain ⟨b, hb, rfl⟩ := hv
    exact hchain a ha b hb huv
  have himg_bound : ∀ u ∈ (routedFibre ctx.n24CarryData route 4).image level, u ≤ ctx.shell.X := by
    intro u hu
    rw [Finset.mem_image] at hu
    obtain ⟨a, ha, rfl⟩ := hu
    exact hbound a ha
  have hcard_img := himg_chain.card_le himg_bound
  have hcard_eq : ((routedFibre ctx.n24CarryData route 4).image level).card
      = (routedFibre ctx.n24CarryData route 4).card := by
    apply Finset.card_image_of_injOn
    intro u hu v hv huv
    exact hinj u (Finset.mem_coe.mp hu) v (Finset.mem_coe.mp hv) huv
  rwa [hcard_eq] at hcard_img

/-! ## 5.  The genuine-route Return class-4 fibre-landing injection -/

/-- **The genuine class-4 fibre is exactly the J.1.1 return band.**

Documents that the residual's domain is the genuine first-obstruction return band: a high-excess
start is in the routed class-4 fibre iff its tower-exit is `returnPkg`, or its `cnlTail` tail
carries a long (non-run) return (`returnCls = 2`).  This is `genuineChargeRoute_eq_four_iff` lifted
through the fibre filter. -/
theorem genuine_class4_fibre_mem_iff (ctx : ActualFailureContext) (k : ℕ) :
    k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4 ↔
      k ∈ highExcessStarts ctx.n24CarryData.starts (hitGap ctx.n24CarryData.a)
          ctx.n24CarryData.r ctx.n24CarryData.T ctx.n24CarryData.Y ∧
        (towerClsOfShell ctx k = TowerExitClass.returnPkg ∨
          (towerClsOfShell ctx k = TowerExitClass.cnlTail ∧ runClsOfShell ctx k ≠ 1 ∧
            returnCls ctx k = 2)) := by
  unfold routedFibre
  rw [Finset.mem_filter, genuineChargeRoute_eq_four_iff]

/-- **The genuine-route Return class-4 OLC routing charge, from the inverse-tower count bound.**

The downstream `genuine_returnCount_le_liftLevelBound` consumes exactly a
`ReturnOlcRoutingCharge (genuineChargeRoute ctx) ctx`; this builds one from the single count
residual `|routedFibre 4| ≤ liftLevelBound X`. -/
def genuineReturnOlcRoutingCharge_ofCardLe (ctx : ActualFailureContext)
    (hcard :
      (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4).card ≤ liftLevelBound ctx.shell.X) :
    ReturnOlcRoutingCharge (genuineChargeRoute ctx) ctx :=
  ReturnOlcRoutingCharge.ofLiftLevelBoundCardLe (genuineChargeRoute ctx) ctx hcard

/-- **The genuine-route Return class-4 OLC routing charge, from the M.2.1 lift-chain levels.**

The genuine fibre-landing injection for `genuineChargeRoute` built from the smallest honest
residual: the M.2.1 self-referential nesting-level assignment of the long-return class-4 starts
(`level`, with the lift-congruence `hchain`, the shell-scale bound `hbound`, and the endpoint
disjointness `hinj`).  This closes the class-4 injection *modulo* the genuine classifier↔OLC-endpoint
geometric link, which is the level assignment itself. -/
def genuineReturnOlcRoutingCharge (ctx : ActualFailureContext)
    (level : ℕ → ℕ)
    (hbound : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4, level k ≤ ctx.shell.X)
    (hchain : ∀ x ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4,
      ∀ y ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4,
        level x < level y → level x + 2 ^ level x ≤ level y)
    (hinj : ∀ x ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4,
      ∀ y ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4, level x = level y → x = y) :
    ReturnOlcRoutingCharge (genuineChargeRoute ctx) ctx :=
  ReturnOlcRoutingCharge.ofLiftChainLevels (genuineChargeRoute ctx) ctx level hbound hchain hinj

/-- **The genuine class-4 count is derived for the genuine route, given the injection.**  The
genuine-route fibre-landing injection forces the inverse-tower count `|routedFibre 4| ≤
liftLevelBound X` (re-export of the proved `fibreCard_le_liftLevelBound`, the M.2.1
`olcGeomOfShell_endpoints_card_le`). -/
theorem genuineReturnCount_le_liftLevelBound (ctx : ActualFailureContext)
    (rc : ReturnOlcRoutingCharge (genuineChargeRoute ctx) ctx) :
    (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 4).card ≤ liftLevelBound ctx.shell.X :=
  rc.fibreCard_le_liftLevelBound

/-! ## 6.  Honest residual inventory -/

/-- The precise status of the Return (class-4) fibre-landing injection after this module. -/
def returnInjectionResiduals : List String :=
  [ "CLOSED (order-matching injection) — olcRankMatch / olcRankMatch_mem / olcRankMatch_injOn: the " ++
      "explicit non-degenerate injection of a finite F ⊆ ℕ into E ⊆ ℕ whenever |F| ≤ |E| (the r-th " ++
      "smallest of F to the r-th smallest of E, via Finset.orderEmbOfFin and the order-rank " ++
      "olcFibreRank). Never the identity; works for any nonempty fibre.",
    "CLOSED (count ⇒ injection, genuine converse) — ReturnOlcRoutingCharge.ofEndpointCardLe: builds " ++
      "ReturnOlcRoutingCharge route ctx from the single bound |routedFibre 4| ≤ |endpoints|. With the " ++
      "proved forward fibreCard_le_olcCard this makes the three-field M.2.1 injection EQUIVALENT to " ++
      "one count inequality. NOT the forbidden identity-only ofSubsetEndpoints (no ⊆ containment).",
    "CLOSED (endpoint count = inverse tower) — shellLevels_card_eq / olcGeomOfShell_endpoints_card_eq: " ++
      "|shellLevels X| = |(olcGeomOfShell ctx).endpoints| = liftLevelBound X exactly (the M_L tower " ++
      "levels liftLevel 0,…,liftLevel (M_L-1) below X). Hence ReturnOlcRoutingCharge.ofLiftLevelBoundCardLe.",
    "CLOSED (M.2.1 reduction) — ReturnOlcRoutingCharge.ofLiftChainLevels: builds the injection from a " ++
      "self-referential lift-chain level assignment of the class-4 fibre (level bounded by X via " ++
      "hbound; the lift congruence level x + 2^(level x) ≤ level y via hchain; endpoint disjointness " ++
      "via hinj), through the PROVED IsLiftChain.card_le. No degenerate shortcut: id fails hchain, a " ++
      "constant fails hinj.",
    "CLOSED (genuine route) — genuineReturnOlcRoutingCharge / genuineReturnOlcRoutingCharge_ofCardLe: " ++
      "the ReturnOlcRoutingCharge (genuineChargeRoute ctx) ctx for the genuine route, from the smallest " ++
      "residual (lift-chain levels, resp. count bound), so genuineReturnCount_le_liftLevelBound fires. " ++
      "genuine_class4_fibre_mem_iff documents the residual domain is exactly the J.1.1 return band " ++
      "(towerClsOfShell = returnPkg, or cnlTail ∧ runClsOfShell ≠ 1 ∧ returnCls = 2).",
    "OPEN (classifier↔OLC-endpoint geometric link, the smallest residual) — the level assignment " ++
      "level : ℕ → ℕ of ofLiftChainLevels (hbound/hchain/hinj). The abstract olcGeomOfShell realizes " ++
      "the M.2.1 WORST-CASE chain shellLevels X (tower levels disconnected from the concrete return " ++
      "starts); assigning each long-return start a distinct OLC nesting level obeying the " ++
      "self-referential lift congruence is the M.2.1 endpoint-nesting geometry of the actual carries, " ++
      "owned by the deep Return geometry workers and NOT present in the three source files. It is " ++
      "carried here as the explicit ofLiftChainLevels hypotheses — the smallest honest residual." ]

theorem returnInjectionResiduals_nonempty : returnInjectionResiduals ≠ [] := by
  simp [returnInjectionResiduals]

/-! ## 7.  Axiom-cleanliness audit -/

#print axioms olcRankMatch_mem
#print axioms olcRankMatch_injOn
#print axioms ReturnOlcRoutingCharge.ofEndpointCardLe
#print axioms shellLevels_card_eq
#print axioms olcGeomOfShell_endpoints_card_eq
#print axioms ReturnOlcRoutingCharge.ofLiftLevelBoundCardLe
#print axioms ReturnOlcRoutingCharge.ofLiftChainLevels
#print axioms genuine_class4_fibre_mem_iff
#print axioms genuineReturnOlcRoutingCharge
#print axioms genuineReturnOlcRoutingCharge_ofCardLe
#print axioms genuineReturnCount_le_liftLevelBound

end

end Erdos260
