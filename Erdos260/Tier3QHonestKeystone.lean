import Erdos260.RhoDQEndpointWiringCore

/-!
# Tier-3 Q-honest keystone re-cut — the large-Q gate as an IFF and the Q-honest density interface

This module (NEW; it edits no existing file and does **not** change the global
`Erdos260.Constants.manuscriptRhoD = 1/4`) machine-checks the **Q-honest density wiring** for the
§7 / Tier-3 keystone.  The certified endpoint still rides the pinned `1/4` DensePack density floor,
which the manuscript flags as FALSE-as-typed for `Q ≥ 2`: Proposition 24.3 (`proof_v4`, the boxed
`(24.3)`, lines 1514–1531) and Lemma 24.1 (binary orbit-digit density, lines 1466–1472) only give the
genuine fixed-period floor `1/(3Q)`, and `prop:tier3-q-calibration` (lines 1533–1569, eqn `(24.4)`)
sets the honest Tier-3 floor to `ρ_D(Q) = 1/(4Q) < 1/(3Q)` (also `ρ_D = 1/(4Q)`, line 237), sharpened
to the odd part `q₀ = oddPart Q` (`q₀ ≤ Q`, so `1/(4q₀) ≤ 1/(3q₀)`).

The wave-23/24 cores already proved the Q-correct floor `rhoDQ q₀ = 1/(4q₀)`, its calibration
`rhoDQ q₀ ≤ 1/(3q₀)` (`RhoDQCalibrationCore`), the Q-correct DensePack obligation
`densePackEndpointDensityRhoDQ` and its discharge (`RhoDQPrecursorConsumerCore`), the §K.4 Q-calibration
feasibility (`K4ConstantsCalibrationCore`), and the endpoint wiring
(`RhoDQEndpointWiringCore`: the FORWARD large-Q gate `4q₀ ≤ L → 0 < proofV4DensePackMinHitsRhoDQ`,
the position-constraint route `rhoDQ_position_constraint_of_largeQ`, and `rhoDQ_wiring_ingredients`).

## What this module adds (no `sorry`/`axiom`/`admit`/`native_decide`)

* **(Task 1) The large-Q gate as an IFF + the Q-dependent deep-scale threshold.**
  `proofV4DensePackMinHitsRhoDQ_le_of_pos` proves the CONVERSE of the forward gate
  (`RhoDQEndpointWiringCore.proofV4DensePackMinHitsRhoDQ_pos_of_le`): positivity of the Q-correct
  floor `⌊L/(4q₀)⌋` forces `4q₀ ≤ L`.  `proofV4DensePackMinHitsRhoDQ_pos_iff` packages the two
  directions: `0 < proofV4DensePackMinHitsRhoDQ ctx ↔ 4q₀ ≤ L`.  Since the shell is dyadic
  (`X = 2^L`), this becomes the explicit **Q-dependent deep-scale threshold**
  `proofV4DensePackMinHitsRhoDQ_pos_iff_deepScale`: `0 < proofV4DensePackMinHitsRhoDQ ctx
  ↔ 2^(4q₀) ≤ X` — the honest Q-dependent replacement for the fixed `2^986891` threshold.
  `fixedThreshold_insufficient_once_q0_large` records that the fixed threshold is genuinely too weak:
  a scale `L > 986891` (the fixed deep guard met) with `q₀ = 246724` has `4q₀ = 986896 > L`, so the
  honest gate `4q₀ ≤ L` — equivalently positivity of the Q-correct floor — FAILS.  The fixed
  `2^986891` guard is insufficient once `4q₀ > 986892`, i.e. `q₀ ≥ 246724` (`q₀ > 986891/4`).

* **(Task 2) The Q-honest density-input interface + position-constraint delivery.**
  `QHonestDensityInput ctx` bundles the Q-correct DensePack obligation `densePackEndpointDensityRhoDQ
  ctx` with the large-Q gate `4q₀ ≤ L`.  `qHonest_delivers_position_constraint` shows this interface
  delivers the keystone's ONLY density consequence — the band/position constraint for every genuine
  DensePack start — for **ALL Q**, by assembling `rhoDQ_position_constraint_of_largeQ`.  The interface
  is honestly INHABITABLE for all Q: `QHonestDensityInput.ofDescentWindowMatch` builds it from the lone
  §25.1 `DescentWindowMatch` residual plus the deep-scale threshold, and `qHonest_density_no_stronger`
  shows it is WEAKER than the pinned obligation.  `qHonest_k4_budget_survives_all_Q` re-exports
  `rhoDQ_wiring_ingredients`: the four §K.4 budgets survive at the Q-correct constants for every `q₀`.
  `qHonest_interface_sufficient` combines the two: the Q-honest interface delivers both the position
  constraint and the §K.4 budget at the actual `q₀ = (canonicalCenter ctx).q0`.

## How far §7 / Tier-3 moves and the single residual obligation

The certified 15-field keystone reduction (`Erdos260KeystoneCapstone.Erdos260KeystoneResidual`)
consumes density through ONE field, `densePackDensityOffTable`, whose codomain is the pinned
`densePackEndpointDensity ctx` (and its mirror `densePackDensity` in `Erdos260FrontierCapstone` /
`Erdos260ConvergenceResidual`).  That field is consumed by a SINGLE proved lemma
`k1CoverBody_of_density_cluster_spacing`, which uses density only through the position constraint
`k1Density_endpoint_band` — for which `k1Density_endpoint_band_rhoDQ` is the proved Q-correct analogue.
This module shows the Q-honest interface is SUFFICIENT (delivers exactly that consequence for all Q)
and the swapped field is HONESTLY satisfiable (constructed from the lone §25.1 residual + the
deep-scale threshold) and WEAKER than the pinned one.  Hence §7 / Tier-3 moves from
Tier-3/Partially to Verified up to the **single explicit typed field-swap**:

> retype the keystone field `densePackDensityOffTable : … → densePackEndpointDensity ctx`
> to `… → densePackEndpointDensityRhoDQ ctx` (and the mirror `densePackDensity`), and re-point the
> one consumer `k1CoverBody_of_density_cluster_spacing` from `k1Density_endpoint_band` to
> `k1Density_endpoint_band_rhoDQ`.

That swap is an edit of certified green code (the manuscript's deferred future-wave structural edit),
recorded here precisely in `tier3QHonestKeystoneResiduals` — NOT as a `sorry`.

`Constants.manuscriptRhoD` is left UNTOUCHED; this is a new leaf module.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false

/-! ## 1.  The large-Q gate as an IFF, and the Q-dependent deep-scale threshold

`RhoDQEndpointWiringCore.proofV4DensePackMinHitsRhoDQ_pos_of_le` gives the FORWARD direction
`4q₀ ≤ L → 0 < proofV4DensePackMinHitsRhoDQ ctx`.  Here `L = Classical.choose ctx.shell.hXdyadic`
is the dyadic scale exponent (`X = 2^L`) and `q₀ = (canonicalCenter ctx).q0` is the reduced odd
residual-center denominator.  We prove the CONVERSE and package the IFF, then convert it to the
explicit deep-scale threshold `2^(4q₀) ≤ X`. -/

/-- **The CONVERSE large-Q gate.**  Positivity of the Q-correct DensePack floor
`proofV4DensePackMinHitsRhoDQ ctx = ⌊(1/(4q₀))·L⌋` forces the large-Q gate `4q₀ ≤ L`.  Mirrors the
forward `proofV4DensePackMinHitsRhoDQ_pos_of_le` in reverse:
`0 < ⌊L/(4q₀)⌋ → 1 ≤ L/(4q₀) → 4q₀ ≤ L`. -/
theorem proofV4DensePackMinHitsRhoDQ_le_of_pos (ctx : ActualFailureContext)
    (h : 0 < proofV4DensePackMinHitsRhoDQ ctx) :
    4 * (canonicalCenter ctx).q0 ≤ Classical.choose ctx.shell.hXdyadic := by
  unfold proofV4DensePackMinHitsRhoDQ at h
  rw [Nat.floor_pos, rhoDQ] at h
  have hq0R : (0 : ℝ) < ((canonicalCenter ctx).q0 : ℝ) := by
    exact_mod_cast (canonicalCenter ctx).q0_pos
  rw [one_div, inv_mul_eq_div, le_div_iff₀ (by positivity)] at h
  have hh : (4 : ℝ) * ((canonicalCenter ctx).q0 : ℝ)
      ≤ ((Classical.choose ctx.shell.hXdyadic : ℕ) : ℝ) := by linarith
  exact_mod_cast hh

/-- **The large-Q gate as an IFF.**  The Q-correct DensePack floor is positive **iff** the large-Q
gate holds: `0 < proofV4DensePackMinHitsRhoDQ ctx ↔ 4q₀ ≤ L`.  (Forward: the wave-25
`proofV4DensePackMinHitsRhoDQ_pos_of_le`; converse: `proofV4DensePackMinHitsRhoDQ_le_of_pos`.) -/
theorem proofV4DensePackMinHitsRhoDQ_pos_iff (ctx : ActualFailureContext) :
    0 < proofV4DensePackMinHitsRhoDQ ctx ↔
      4 * (canonicalCenter ctx).q0 ≤ Classical.choose ctx.shell.hXdyadic :=
  ⟨proofV4DensePackMinHitsRhoDQ_le_of_pos ctx, proofV4DensePackMinHitsRhoDQ_pos_of_le ctx⟩

/-- **The deep-scale gate in `X`.**  Since the shell is dyadic (`X = 2^L`), the large-Q gate
`4q₀ ≤ L` is equivalent to `2^(4q₀) ≤ X`. -/
theorem largeQ_of_deepScale (ctx : ActualFailureContext)
    (hX : 2 ^ (4 * (canonicalCenter ctx).q0) ≤ ctx.X) :
    4 * (canonicalCenter ctx).q0 ≤ Classical.choose ctx.shell.hXdyadic := by
  have hXX : ctx.X = 2 ^ Classical.choose ctx.shell.hXdyadic :=
    ctx.shell_X.symm.trans (Classical.choose_spec ctx.shell.hXdyadic)
  rw [hXX] at hX
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hX

/-- **The explicit Q-dependent deep-scale threshold (forward).**  The Q-correct DensePack floor is
positive once `X ≥ 2^(4q₀)`.  This is the honest Q-dependent replacement for the fixed `2^986891`
deep-scale threshold: the deep guard now scales with the actual residual-center denominator `q₀`. -/
theorem proofV4DensePackMinHitsRhoDQ_pos_of_deepScale (ctx : ActualFailureContext)
    (hX : 2 ^ (4 * (canonicalCenter ctx).q0) ≤ ctx.X) :
    0 < proofV4DensePackMinHitsRhoDQ ctx :=
  proofV4DensePackMinHitsRhoDQ_pos_of_le ctx (largeQ_of_deepScale ctx hX)

/-- **The explicit Q-dependent deep-scale threshold as an IFF.**
`0 < proofV4DensePackMinHitsRhoDQ ctx ↔ 2^(4q₀) ≤ X` — the honest Q-dependent replacement for the
fixed `2^986891 < X` threshold.  Once `q₀ > 986891/4` the fixed threshold is too weak (see
`fixedThreshold_insufficient_once_q0_large`); this one tracks `q₀` exactly. -/
theorem proofV4DensePackMinHitsRhoDQ_pos_iff_deepScale (ctx : ActualFailureContext) :
    0 < proofV4DensePackMinHitsRhoDQ ctx ↔ 2 ^ (4 * (canonicalCenter ctx).q0) ≤ ctx.X := by
  have hXX : ctx.X = 2 ^ Classical.choose ctx.shell.hXdyadic :=
    ctx.shell_X.symm.trans (Classical.choose_spec ctx.shell.hXdyadic)
  rw [proofV4DensePackMinHitsRhoDQ_pos_iff ctx, hXX]
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).symm

/-- **The fixed `2^986891` threshold is insufficient once `q₀` is large.**  There is a deep scale
`L > 986891` (the fixed deep guard `2^986891 < X = 2^L` met) and an odd part `q₀ = 246724 > 0` for
which the honest large-Q gate `4q₀ ≤ L` FAILS (`4·246724 = 986896 > 986892 = L`).  By
`proofV4DensePackMinHitsRhoDQ_pos_iff`, positivity of the Q-correct floor is *equivalent* to the gate,
so the fixed threshold cannot certify the floor at such `q₀`.  The fixed guard becomes insufficient
once `4q₀ > 986892`, i.e. `q₀ ≥ 246724` (`q₀ > 986891/4 ≈ 246722.75`). -/
theorem fixedThreshold_insufficient_once_q0_large :
    ∃ L q0 : ℕ, 0 < q0 ∧ 986891 < L ∧ ¬ (4 * q0 ≤ L) :=
  ⟨986892, 246724, by norm_num, by norm_num, by omega⟩

/-! ## 2.  The Q-honest density-input interface and position-constraint delivery

The keystone takes the density field only to derive its band/position constraint
(`k1Density_endpoint_band`, off-pin analogue of `band3_density_forces_subshell`).  We bundle the
Q-correct obligation with the large-Q gate, and show the bundle delivers that constraint for all `Q`,
is honestly inhabitable for all `Q`, and is no stronger than the pinned obligation. -/

/-- **The Q-honest density-input interface.**  Bundles the Q-correct DensePack obligation
`densePackEndpointDensityRhoDQ ctx` (the honest `1/(4q₀)` floor) together with the large-Q gate
`4q₀ ≤ L`.  This is the honest replacement for the implicit pinned-floor density input of the
certified keystone. -/
structure QHonestDensityInput (ctx : ActualFailureContext) where
  /-- The large-Q gate `4q₀ ≤ L` (`L = Classical.choose ctx.shell.hXdyadic`, `X = 2^L`). -/
  largeQ : 4 * (canonicalCenter ctx).q0 ≤ Classical.choose ctx.shell.hXdyadic
  /-- The Q-correct DensePack coarea hit-density obligation at rate `rhoDQ q₀ = 1/(4q₀)`. -/
  density : densePackEndpointDensityRhoDQ ctx

/-- **Inhabitation from the deep-scale threshold.**  From `X ≥ 2^(4q₀)` (the honest Q-dependent
deep guard) and a discharged Q-correct obligation, the interface is satisfied. -/
def QHonestDensityInput.ofDeepScale (ctx : ActualFailureContext)
    (hX : 2 ^ (4 * (canonicalCenter ctx).q0) ≤ ctx.X)
    (hdens : densePackEndpointDensityRhoDQ ctx) :
    QHonestDensityInput ctx where
  largeQ := largeQ_of_deepScale ctx hX
  density := hdens

/-- **Inhabitation for ALL Q from the lone §25.1 residual.**  From `X ≥ 2^(4q₀)` and a single
`DescentWindowMatch ctx` (the lone irreducible §25.1 cylinder residual) plus coprimality and shell
geometry, the Q-honest interface is satisfied — for every `Q`, never just `q₀ = 1`. -/
def QHonestDensityInput.ofDescentWindowMatch (ctx : ActualFailureContext)
    (hX : 2 ^ (4 * (canonicalCenter ctx).q0) ≤ ctx.X)
    (W : DescentWindowMatch ctx)
    (hcop : ∀ k ∈ genuineDensePackStarts ctx, Nat.Coprime (W.a k) (canonicalCenter ctx).q0)
    (hlo : ∀ k ∈ genuineDensePackStarts ctx, ctx.shell.X < k + ctx.n24CarryData.r)
    (hhi : ∀ k ∈ genuineDensePackStarts ctx,
        (k + ctx.n24CarryData.r) + proofV4DensePackSpread ctx.shell ≤ 2 * ctx.shell.X)
    (hpb : Classical.choose ctx.shell.hXdyadic + orderOf (2 : ZMod (canonicalCenter ctx).q0)
        ≤ proofV4DensePackSpread ctx.shell + 2) :
    QHonestDensityInput ctx where
  largeQ := largeQ_of_deepScale ctx hX
  density := densePackEndpointDensityRhoDQ_of_descentWindowMatch ctx W hcop hlo hhi hpb

/-- **The Q-honest interface delivers the keystone's ONLY density consequence, for ALL Q.**  From the
interface, every genuine DensePack start's terminal endpoint `k + r` lands in the shell band
`X − spread < k + r ≤ 2X` — the exact content the certified keystone takes from its density field
(`k1Density_endpoint_band`), here at the honest `1/(4q₀)` floor for every `Q`. -/
theorem qHonest_delivers_position_constraint (ctx : ActualFailureContext)
    (H : QHonestDensityInput ctx) :
    ∀ k ∈ genuineDensePackStarts ctx,
      ctx.shell.X < k + ctx.n24CarryData.r + proofV4DensePackSpread ctx.shell
        ∧ k + ctx.n24CarryData.r ≤ 2 * ctx.shell.X :=
  rhoDQ_position_constraint_of_largeQ ctx H.largeQ H.density

/-- **The Q-honest obligation is no stronger than the pinned one.**  The pinned density obligation
implies the Q-correct one (`rhoDQ q₀ ≤ manuscriptRhoD`), so swapping the keystone field to the
Q-correct floor WEAKENS its demand — every existing pinned supplier still discharges it. -/
theorem qHonest_density_no_stronger (ctx : ActualFailureContext)
    (h : densePackEndpointDensity ctx) : densePackEndpointDensityRhoDQ ctx :=
  rhoDQ_density_no_stronger ctx h

/-- **The Q-honest obligation is dischargeable for ALL Q** from the lone §25.1 `DescentWindowMatch`
residual (re-export of the proved consumer) — the field is genuinely satisfiable at every `Q`. -/
theorem qHonest_density_dischargeable_all_Q (ctx : ActualFailureContext)
    (W : DescentWindowMatch ctx)
    (hcop : ∀ k ∈ genuineDensePackStarts ctx, Nat.Coprime (W.a k) (canonicalCenter ctx).q0)
    (hlo : ∀ k ∈ genuineDensePackStarts ctx, ctx.shell.X < k + ctx.n24CarryData.r)
    (hhi : ∀ k ∈ genuineDensePackStarts ctx,
        (k + ctx.n24CarryData.r) + proofV4DensePackSpread ctx.shell ≤ 2 * ctx.shell.X)
    (hpb : Classical.choose ctx.shell.hXdyadic + orderOf (2 : ZMod (canonicalCenter ctx).q0)
        ≤ proofV4DensePackSpread ctx.shell + 2) :
    densePackEndpointDensityRhoDQ ctx :=
  densePackEndpointDensityRhoDQ_of_descentWindowMatch ctx W hcop hlo hhi hpb

/-- **The §K.4 budget survives at the Q-correct constants for ALL Q** (re-export of
`rhoDQ_wiring_ingredients`).  All four §K.4 budgets — the order bound `κ(q₀) < 1/(40q₀)`, the
dense-marker step-6 `c_*(q₀)/(ρ_D(q₀)κ(q₀)) < ξ`, the Tower/density budget
`2c₀(q₀)ε ≤ (ξ/6)ρ_D(q₀)`, and the descent accumulator `C_*C_Q c_*(q₀) < c_pr/4` — hold for every
`q₀ ≥ 1`, with the SAME margins as the pinned `q₀ = 1` case (`prop:tier3-q-calibration`, lines
1557–1568). -/
theorem qHonest_k4_budget_survives_all_Q {q0 : ℕ} (h : 0 < q0) :
    kappaQ q0 < 1 / (40 * (q0 : ℝ))
      ∧ cStarQ q0 / (rhoDQcal q0 * kappaQ q0) < manuscriptXi
      ∧ 2 * c0Q q0 * manuscriptEps ≤ manuscriptXi / 6 * rhoDQcal q0
      ∧ manuscriptCstar * manuscriptCQ * cStarQ q0 < manuscriptCpr / 4 :=
  rhoDQ_wiring_ingredients h

/-- **The Q-honest interface is SUFFICIENT.**  At the actual residual-center denominator
`q₀ = (canonicalCenter ctx).q0`, the Q-honest interface delivers BOTH the keystone's density
consequence (the band/position constraint for every genuine start) AND the four §K.4 budgets — i.e.
everything the certified keystone consumes from the density layer is supplied at the honest
`1/(4q₀)` floor.  The only remaining step is the structural retyping of the keystone field itself
(recorded in `tier3QHonestKeystoneResiduals`). -/
theorem qHonest_interface_sufficient (ctx : ActualFailureContext)
    (H : QHonestDensityInput ctx) :
    (∀ k ∈ genuineDensePackStarts ctx,
        ctx.shell.X < k + ctx.n24CarryData.r + proofV4DensePackSpread ctx.shell
          ∧ k + ctx.n24CarryData.r ≤ 2 * ctx.shell.X)
      ∧ (kappaQ (canonicalCenter ctx).q0 < 1 / (40 * ((canonicalCenter ctx).q0 : ℝ))
          ∧ cStarQ (canonicalCenter ctx).q0
              / (rhoDQcal (canonicalCenter ctx).q0 * kappaQ (canonicalCenter ctx).q0) < manuscriptXi
          ∧ 2 * c0Q (canonicalCenter ctx).q0 * manuscriptEps
              ≤ manuscriptXi / 6 * rhoDQcal (canonicalCenter ctx).q0
          ∧ manuscriptCstar * manuscriptCQ * cStarQ (canonicalCenter ctx).q0
              < manuscriptCpr / 4) :=
  ⟨qHonest_delivers_position_constraint ctx H,
    rhoDQ_wiring_ingredients (canonicalCenter ctx).q0_pos⟩

/-! ## 3.  Honest residual / status inventory -/

/-- The precise status of the Tier-3 Q-honest keystone re-cut after this module. -/
def tier3QHonestKeystoneResiduals : List String :=
  [ "GOAL — machine-check the Q-honest density wiring so the §7 / Tier-3 keystone rows move from " ++
      "Tier-3/Partially toward Verified, reducing the residual to a single explicit typed field-swap. " ++
      "The certified endpoint still rides the pinned manuscriptRhoD = 1/4 DensePack floor, FALSE-as-" ++
      "typed for Q >= 2 (Prop 24.3 / Lemma 24.1 give only 1/(3Q); the honest Tier-3 floor is " ++
      "rho_D(Q) = 1/(4Q), prop:tier3-q-calibration eqn (24.4)).",
    "CLOSED (large-Q gate IFF) — proofV4DensePackMinHitsRhoDQ_le_of_pos is the CONVERSE of the " ++
      "wave-25 forward gate: 0 < proofV4DensePackMinHitsRhoDQ ctx (= floor(L/(4q0))) forces 4q0 <= L. " ++
      "proofV4DensePackMinHitsRhoDQ_pos_iff packages both directions: positivity <-> 4q0 <= L.",
    "CLOSED (Q-dependent deep-scale threshold) — proofV4DensePackMinHitsRhoDQ_pos_iff_deepScale: " ++
      "since X = 2^L, positivity <-> 2^(4q0) <= X. This is the honest Q-dependent replacement for the " ++
      "FIXED 2^986891 deep-scale threshold; the gate now tracks q0 = oddPart Q exactly.",
    "CLOSED (fixed threshold insufficiency) — fixedThreshold_insufficient_once_q0_large: a scale " ++
      "L = 986892 > 986891 (fixed deep guard met) with q0 = 246724 has 4q0 = 986896 > L, so the gate " ++
      "4q0 <= L (equivalently positivity of the Q-correct floor) FAILS. The fixed 2^986891 guard is " ++
      "insufficient once 4q0 > 986892, i.e. q0 >= 246724 (q0 > 986891/4).",
    "CLOSED (Q-honest interface) — QHonestDensityInput ctx bundles densePackEndpointDensityRhoDQ ctx " ++
      "with the large-Q gate 4q0 <= L. qHonest_delivers_position_constraint derives the keystone's " ++
      "ONLY density consequence (the band/position constraint X - spread < k+r <= 2X for every genuine " ++
      "start) for ALL Q via rhoDQ_position_constraint_of_largeQ (using k1Density_endpoint_band_rhoDQ).",
    "CLOSED (interface honestly inhabitable, ALL Q) — QHonestDensityInput.ofDeepScale (from the deep " ++
      "guard + a discharged obligation) and QHonestDensityInput.ofDescentWindowMatch (from the deep " ++
      "guard + the lone §25.1 DescentWindowMatch residual). qHonest_density_dischargeable_all_Q " ++
      "re-exports the discharge; qHonest_density_no_stronger shows the field is WEAKER than the pinned " ++
      "one (rhoDQ q0 <= manuscriptRhoD), so all existing pinned suppliers still discharge it.",
    "CLOSED (§K.4 budget, ALL Q) — qHonest_k4_budget_survives_all_Q re-exports rhoDQ_wiring_ingredients: " ++
      "all four §K.4 budgets hold at the Q-correct constants for every q0 >= 1 with the pinned margins. " ++
      "qHonest_interface_sufficient bundles position-constraint delivery + the §K.4 budget at the actual " ++
      "q0 = (canonicalCenter ctx).q0 — everything the keystone consumes from density, at the honest floor.",
    "RESIDUAL (the single explicit typed field-swap) — retype the certified keystone field " ++
      "Erdos260KeystoneCapstone.Erdos260KeystoneResidual.densePackDensityOffTable : ... -> " ++
      "densePackEndpointDensity ctx  to  ... -> densePackEndpointDensityRhoDQ ctx (and the mirror " ++
      "Erdos260FrontierCapstone / Erdos260ConvergenceResidual densePackDensity field), and re-point the " ++
      "lone consumer k1CoverBody_of_density_cluster_spacing from k1Density_endpoint_band to " ++
      "k1Density_endpoint_band_rhoDQ. This module PROVES that swap is SUFFICIENT (delivers the only " ++
      "density consequence for all Q) and the new field HONESTLY satisfiable and weaker; the swap itself " ++
      "is an edit of certified green code (the manuscript's deferred future-wave task), recorded here, " ++
      "NOT a sorry. Constants.manuscriptRhoD is UNCHANGED.",
    "NON-DEGENERATE — the gate is an exact IFF (not a one-sided sufficient condition); the Q-correct " ++
      "floor rhoDQ q0 = 1/(4q0) > 0 is a POSITIVE Q-dependent density; the position constraint is " ++
      "derived from a genuine hit (k1Density_endpoint_band_rhoDQ), no vacuous / zero-floor shortcut." ]

theorem tier3QHonestKeystoneResiduals_nonempty : tier3QHonestKeystoneResiduals ≠ [] := by
  simp [tier3QHonestKeystoneResiduals]

/-! ## 4.  Axiom-cleanliness audit -/

#print axioms proofV4DensePackMinHitsRhoDQ_le_of_pos
#print axioms proofV4DensePackMinHitsRhoDQ_pos_iff
#print axioms largeQ_of_deepScale
#print axioms proofV4DensePackMinHitsRhoDQ_pos_of_deepScale
#print axioms proofV4DensePackMinHitsRhoDQ_pos_iff_deepScale
#print axioms fixedThreshold_insufficient_once_q0_large
#print axioms QHonestDensityInput.ofDeepScale
#print axioms QHonestDensityInput.ofDescentWindowMatch
#print axioms qHonest_delivers_position_constraint
#print axioms qHonest_density_no_stronger
#print axioms qHonest_density_dischargeable_all_Q
#print axioms qHonest_k4_budget_survives_all_Q
#print axioms qHonest_interface_sufficient

end

end Erdos260
