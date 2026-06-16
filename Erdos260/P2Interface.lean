/-
  P2 + trust-boundary formalization: the ARCHITECTURE (conditional reduction).

  What is genuinely formalizable without rebuilding the whole construction:
    (1) the top-level assembly engine of H.5 / the main theorem
        (pressure lower bound  vs  assembled package upper bound  ⟹  contradiction);
    (2) the constant-choosability of Convention 2.0f;
    (3) an explicit `ResidualInterface` whose FIELDS are exactly the P2 / structural
        trust boundaries, with the GLUE (interface ⟹ contradiction) machine-checked.

  What is NOT here, and cannot be without the construction: the proofs of the
  individual interface fields (the package caps L.2/N, the off-pin cap, the class-1
  cap, π_st injectivity, the ledger audit R^{H5}_1=1_{Δ_B≠0}, …).  Those are the
  construction-dependent statements; building a term of type `ResidualInterface`
  is precisely the remaining (multi-month) analytic + formalization work.

  No `sorry`, no custom `axiom`: every theorem below is unconditional Lean, and the
  trust boundary is exactly the hypotheses/fields of `ResidualInterface`.
-/
import Mathlib
import Erdos260.P1HotspotAudit
import Erdos260.P2TrustBoundary

namespace Erdos260.P2Interface

/-! ## Top-level contradiction engine (H.5 / main theorem)

The positive-density theorem is proved by contradiction: the area-pressure lemma
(21.1) gives `area ≥ c_pr · M` with `M = r·X·|I_j| > 0`, while the charged
recurrence (I.2.1) + package estimates (L.2/N) + DensePack smallness + old-residual
absorption (L.6.5) assemble to `area ≤ pkgP + densePack + oldRes + err`, and the
constants are chosen (Convention 2.0f) so the total package budget is `< c_pr·M`. -/

theorem main_contradiction
    {M cpr pkgP densePack oldRes err area : ℝ}
    (hM : 0 < M) (hcpr : 0 < cpr)
    (pressure_low : cpr * M ≤ area)
    (assembly : area ≤ pkgP + densePack + oldRes + err)
    (h1 : pkgP ≤ cpr * M / 4)
    (h2 : densePack ≤ cpr * M / 4)
    (h3 : oldRes ≤ cpr * M / 4)
    (h4 : err ≤ cpr * M / 8) :
    False := by
  have hcM : 0 < cpr * M := mul_pos hcpr hM
  linarith

/-! ## Convention 2.0f: the constants can be chosen consistently

Each package cap has the form `pkg ≤ K · M` with `K` a product of the calibration
constants (e.g. `C·ξ`, `C_*·c_*`).  Convention chooses `ξ`, then `c_*`, small enough
that each `K ≤ c_pr/4` (resp. `/8`).  The point is only that such positive choices
exist; this is the elementary content of (2.0e)/(2.0f). -/

theorem cap_constant_choosable (C cpr : ℝ) (hC : 0 < C) (hcpr : 0 < cpr) :
    ∃ ξ : ℝ, 0 < ξ ∧ C * ξ ≤ cpr / 4 := by
  refine ⟨cpr / (8 * C), by positivity, ?_⟩
  have hCne : C ≠ 0 := ne_of_gt hC
  have e : C * (cpr / (8 * C)) = cpr / 8 := by field_simp
  rw [e]; linarith

/-- The two ξ/c_* budgets used in (2.0f) are simultaneously satisfiable: there is a
    common positive scale making both `C·ξ ≤ cpr/4` and `C'·c_* ≤ cpr/4`. -/
theorem two_cap_constants_choosable (C C' cpr : ℝ) (hC : 0 < C) (hC' : 0 < C')
    (hcpr : 0 < cpr) :
    ∃ ξ c : ℝ, 0 < ξ ∧ 0 < c ∧ C * ξ ≤ cpr / 4 ∧ C' * c ≤ cpr / 4 := by
  obtain ⟨ξ, hξ, hξle⟩ := cap_constant_choosable C cpr hC hcpr
  obtain ⟨c, hc, hcle⟩ := cap_constant_choosable C' cpr hC' hcpr
  exact ⟨ξ, c, hξ, hc, hξle, hcle⟩

/-! ## The residual interface = the trust boundary, made machine-explicit

Each field below is a TRUST BOUNDARY: a statement the construction must supply.
The marginal comments give the manuscript origin (and, where relevant, which
already-verified kernel from `P1HotspotAudit` / `P2TrustBoundary` would discharge
the corresponding per-row/finite fact, leaving only the geometric input).  The
theorem `ResidualInterface.contradiction` is the machine-checked GLUE. -/

structure ResidualInterface where
  /-- `M = r·X·|I_j| > 0`. -/
  M : ℝ
  /-- pressure constant from Lemma 21.1. -/
  cpr : ℝ
  /-- assembled area at the active scale. -/
  area : ℝ
  pkgP : ℝ        -- Return+Run+Tower mass  (L.2.2–L.2.4, N variation-drop)
  densePack : ℝ   -- DensePack mass         (K.1.4/K.1.5, I.4)
  oldRes : ℝ      -- old-residual leakage    (L.6.5 under low-density)
  err : ℝ         -- aggregate o(M) error    (collars, incomplete laps; O1.A high-support)
  M_pos : 0 < M
  cpr_pos : 0 < cpr
  /-- Lemma 21.1 (area pressure). -/
  pressure_low : cpr * M ≤ area
  /-- I.2.1 charged recurrence + H.5 assembly (off-pin cap C1, class-1 cap R2 feed in). -/
  assembly : area ≤ pkgP + densePack + oldRes + err
  /-- L.2/N package cap at the chosen constants (Conv 2.0f). -/
  pkgP_small : pkgP ≤ cpr * M / 4
  /-- DensePack smallness under the contradiction hypothesis. -/
  densePack_small : densePack ≤ cpr * M / 4
  /-- old-residual absorption (Lemma L.6.5). -/
  oldRes_small : oldRes ≤ cpr * M / 4
  /-- aggregate boundary/error is `o(M)`, in particular `≤ cpr·M/8` eventually. -/
  err_small : err ≤ cpr * M / 8

/-- GLUE (machine-checked): the residual interface yields the positive-density
    contradiction.  This is the Lean form of "H.5 ⟹ Theorem A by contradiction":
    everything mathematical is in the fields (the trust boundary); the assembly is
    correct. -/
theorem ResidualInterface.contradiction (I : ResidualInterface) : False :=
  main_contradiction I.M_pos I.cpr_pos I.pressure_low I.assembly
    I.pkgP_small I.densePack_small I.oldRes_small I.err_small

/-! ## Connection to the verified kernels

The finite/arithmetic content behind several interface fields is already
machine-checked, so building those fields reduces to the GEOMETRIC input only:

* `err` (boundary/incomplete-lap, O1.A): the count is `Σ c_λ ≤ N/R` by
  `P1HotspotAudit.o1_high_support_count`; remaining input = phases tower-high &
  disjoint (O2 faithful indexing).
* `pkgP` off-pin share: `P1HotspotAudit.o1_ambient_domination` gives
  `ExitMass ≤ (b/c) M_tot`; remaining input = the complete-lap atlas (O1).
* class-1 cap feeding `assembly`: the floor `ϑ₁=1` and the descent are
  `P1HotspotAudit.o4_excess_exposes_nonzero` / `o4_descent_no_atom`; remaining
  input = `R^{H5}_1 = 1_{Δ_B≠0}` (ledger audit) + priority heredity.
* fixed-pin voiding (a `densePack`/value-axis input): O3 is END-TO-END verified by
  `P2TrustBoundary.o3_density_floor_fully_discharged` + `e6_slope_gap_unique`.
* general-`Q` constants: `cap_constant_choosable` / `two_cap_constants_choosable`
  here, matching `P2TrustBoundary` / Prop tier3.

We record this linkage as a trivial reachability check (the kernels are in scope). -/

theorem kernels_in_scope :
    (∀ (Atom : ℕ → Prop), ¬ Atom 0 → (∀ v, Atom (v+1) → Atom v) → ∀ v, ¬ Atom v)
    ∧ (∀ (μ : ℝ), 0 < μ → ∀ g g' : ℕ,
        (1 < 2 ^ g * μ ∧ 2 ^ g * μ < 2) → (1 < 2 ^ g' * μ ∧ 2 ^ g' * μ < 2) → g = g') :=
  ⟨P1HotspotAudit.o4_descent_no_atom, P2TrustBoundary.e6_slope_gap_unique⟩

end Erdos260.P2Interface
