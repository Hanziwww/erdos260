import Erdos260.Erdos260V30Endpoint
import Erdos260.RhoDQPrecursorConsumerCore
import Erdos260.K4ConstantsCalibrationCore

/-!
# Wiring the Q-correct `ρ_D` chain into the V30 endpoint (sorry-free)

This module imports the V30 endpoint together with the full `ρ_D(Q)` chain
(`RhoDQPrecursorConsumerCore` ⊇ `RhoDQCalibrationCore`) and the K.4 Q-calibration
(`K4ConstantsCalibrationCore`).  Its successful build shows the `RhoDQ` chain coexists
with the endpoint with no clash and no import cycle.

It collects the machine-checked facts that the genuine Q-dependent density floor
`ρ_D(q₀) = 1/(4 q₀)` (the pinned `manuscriptRhoD = 1/4` is honest only at `Q = 1`) can
replace the pinned floor everywhere the endpoint actually uses density:

1. the Q-correct density obligation is no stronger than the pinned one and is
   dischargeable for every `Q` from the lone §25.1 descent-window residual;
2. the K.4 smallness budget survives the floor swap for every `Q`;
3. the Q-correct floor delivers the keystone's only density consequence (the position
   constraint), under the explicit large-Q gate `4 q₀ ≤ L` (proved arithmetically here).

The one step NOT formalized is the structural edit of the certified 15-field
keystone/convergence reduction to consume the Q-correct floor field; that is an unbounded
refactor of green proved code (the manuscript's deferred future-wave task) and is recorded
as a review target in `ERDOS260_REVIEW_TARGETS.md`, not as a `sorry`.
-/

namespace Erdos260

noncomputable section

/-! ## 1. The Q-correct density obligation -/

/-- The Q-correct density obligation is no stronger than the pinned one:
    the pinned floor `⌊(1/4)L⌋` dominates the Q-correct floor `⌊(1/(4q₀))L⌋`. -/
theorem rhoDQ_density_no_stronger (ctx : ActualFailureContext)
    (h : densePackEndpointDensity ctx) : densePackEndpointDensityRhoDQ ctx :=
  densePackEndpointDensityRhoDQ_of_pinned ctx h

/-- The Q-correct density obligation is dischargeable for every `Q` from the lone §25.1
    descent-window residual (re-export of the proved consumer). -/
theorem rhoDQ_density_dischargeable_of_descentWindowMatch (ctx : ActualFailureContext)
    (W : DescentWindowMatch ctx)
    (hcop : ∀ k ∈ genuineDensePackStarts ctx, Nat.Coprime (W.a k) (canonicalCenter ctx).q0)
    (hlo : ∀ k ∈ genuineDensePackStarts ctx, ctx.shell.X < k + ctx.n24CarryData.r)
    (hhi : ∀ k ∈ genuineDensePackStarts ctx,
        (k + ctx.n24CarryData.r) + proofV4DensePackSpread ctx.shell ≤ 2 * ctx.shell.X)
    (hpb : Classical.choose ctx.shell.hXdyadic + orderOf (2 : ZMod (canonicalCenter ctx).q0)
        ≤ proofV4DensePackSpread ctx.shell + 2) :
    densePackEndpointDensityRhoDQ ctx :=
  densePackEndpointDensityRhoDQ_of_descentWindowMatch ctx W hcop hlo hhi hpb

/-! ## 2. The K.4 budget at the Q-correct floor -/

/-- The dense-marker compatibility (K.4 step 6) holds at the Q-correct floor for every
    `q₀ ≥ 1` — the swap `ρ_D ↦ ρ_D/q₀`, `κ ↦ κ/q₀`, `c_* ↦ c_*/q₀²` keeps the SAME margin. -/
theorem k4_budget_at_rhoDQ_floor {q0 : ℕ} (h : 0 < q0) :
    cStarQ q0 / (rhoDQcal q0 * kappaQ q0) < manuscriptXi :=
  densePackCompatibleQ h

/-- All four K.4 budgets hold simultaneously at the Q-correct constants, for every `q₀`. -/
theorem rhoDQ_wiring_ingredients {q0 : ℕ} (h : 0 < q0) :
    kappaQ q0 < 1 / (40 * (q0 : ℝ))
      ∧ cStarQ q0 / (rhoDQcal q0 * kappaQ q0) < manuscriptXi
      ∧ 2 * c0Q q0 * manuscriptEps ≤ manuscriptXi / 6 * rhoDQcal q0
      ∧ manuscriptCstar * manuscriptCQ * cStarQ q0 < manuscriptCpr / 4 :=
  k4_calibration_feasible_all_Q h

/-! ## 3. The Q-correct floor delivers the keystone's only density consequence

   The keystone consumes the density field ONLY for its position constraint
   (`k1Density_endpoint_band`: every genuine endpoint `k+r` lands in the shell band),
   whose proof uses only floor positivity plus one hit — never the floor value.  Hence the
   Q-correct floor delivers it, under the large-Q gate `4 q₀ ≤ L` discharged below. -/

/-- Q-correct analogue of `k1Density_endpoint_band`: one hit in the Q-correct support
    window forces the endpoint into the shell band. -/
theorem k1Density_endpoint_band_rhoDQ (ctx : ActualFailureContext) {k : ℕ}
    (hpos : 0 < proofV4DensePackMinHitsRhoDQ ctx)
    (hdk : proofV4DensePackMinHitsRhoDQ ctx
      ≤ (proofV4DensePackSupportWindow ctx.shell (k + ctx.n24CarryData.r)).card) :
    ctx.shell.X < k + ctx.n24CarryData.r + proofV4DensePackSpread ctx.shell
      ∧ k + ctx.n24CarryData.r ≤ 2 * ctx.shell.X := by
  have hwpos : 0 < (proofV4DensePackSupportWindow ctx.shell (k + ctx.n24CarryData.r)).card :=
    lt_of_lt_of_le hpos hdk
  obtain ⟨n, hn⟩ := Finset.card_pos.mp hwpos
  have hn' := Finset.mem_filter.mp hn
  obtain ⟨hX1, hX2, _⟩ := (mem_supportShell ctx.shell.d ctx.shell.X n).mp hn'.1
  obtain ⟨hmn, hns⟩ := hn'.2
  omega

/-- The large-Q gate, discharged arithmetically: the Q-correct floor `⌊L/(4q₀)⌋` is
    positive precisely when `L ≥ 4 q₀`.  This is what the shell gate `carryB Q + 25 ≤ L`
    fails to give once `q₀` is large. -/
theorem proofV4DensePackMinHitsRhoDQ_pos_of_le (ctx : ActualFailureContext)
    (h : 4 * (canonicalCenter ctx).q0 ≤ Classical.choose ctx.shell.hXdyadic) :
    0 < proofV4DensePackMinHitsRhoDQ ctx := by
  unfold proofV4DensePackMinHitsRhoDQ
  rw [Nat.floor_pos, rhoDQ]
  have hq0R : (0 : ℝ) < ((canonicalCenter ctx).q0 : ℝ) := by
    exact_mod_cast (canonicalCenter ctx).q0_pos
  have hL : (4 * ((canonicalCenter ctx).q0 : ℝ))
      ≤ ((Classical.choose ctx.shell.hXdyadic : ℕ) : ℝ) := by exact_mod_cast h
  rw [one_div, inv_mul_eq_div, le_div_iff₀ (by positivity)]
  linarith

/-- Under the large-Q gate `4 q₀ ≤ L`, the Q-correct density obligation delivers the
    keystone's position constraint — the only content the keystone takes from the density
    field.  Everything except the structural edit of the certified keystone is machine
    checked. -/
theorem rhoDQ_position_constraint_of_largeQ (ctx : ActualFailureContext)
    (hlarge : 4 * (canonicalCenter ctx).q0 ≤ Classical.choose ctx.shell.hXdyadic)
    (hd : densePackEndpointDensityRhoDQ ctx) :
    ∀ k ∈ genuineDensePackStarts ctx,
      ctx.shell.X < k + ctx.n24CarryData.r + proofV4DensePackSpread ctx.shell
        ∧ k + ctx.n24CarryData.r ≤ 2 * ctx.shell.X :=
  fun k hk =>
    k1Density_endpoint_band_rhoDQ ctx (proofV4DensePackMinHitsRhoDQ_pos_of_le ctx hlarge) (hd k hk)

end

end Erdos260
