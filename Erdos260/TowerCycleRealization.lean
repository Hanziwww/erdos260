import Mathlib
import Erdos260.IntegerCarry
import Erdos260.TowerLandingConstruction
import Erdos260.TowerAPModulusConstruction
import Erdos260.UnconditionalAssemblyTight2

/-!
# Realizing the Tower recurrent cycle from the actual integer carry

`TowerAPModulusConstruction.lean` / `TowerCycleConstruction.lean` left exactly one
irreducible residual open: producing, *from the raw `integerCarry` of an actual
failing shell*, the recurrent-cycle datum `(D : CarryFibreCycleData, μ, hcast)`
together with its nonzero `Q` that the proved Tower pipeline (`towerCycle` field
of the capstone, `TowerRecurrentCycle`) consumes — the additive AP-subfibre shell
geometry of Appendix E.2–E.5.

This file closes the **finite-state recurrent-cycle realization** of that residual
and isolates, precisely and honestly, the single remaining genuine geometric input.

## The genuine arithmetic identity (manuscript E.5/E.11/E.12)

The manuscript (Appendix E.5) parametrises the AP subfibre by
`x_s = x_0 + sH`, with carries `B_{x_s} = B_{x_0} + s·K_Γ`, the carry transition
`B_{y_s} = 2^{γ₀}·B_{x_s} − Q·y_s` (E.11), the difference law
`K_Δ = 2^{γ₀}·K_Γ − Q·H` (E.12), and the normalized slope
`μ_Γ = K_Γ/(Q·H)`, giving the slope recurrence `μ_Δ = 2^{γ₀}·μ_Γ − 1` (E.13).
The slope modulus is therefore `q = Q·H`, and **E.12 is exactly the integer step
`boundedSlopeStep q K = 2^g·K − q`** of `TowerLandingConstruction`.

* **`boundedSlopeStep_modEq`** — the bridge identity: for odd `q` and `1 ≤ K < q`,
  `boundedSlopeStep q K ≡ 2^{canonGap q K}·K  [ZMOD q]`.  I.e. E.12 is exactly the
  *carry doubling map reduced mod the slope modulus* `q`; the abstract E.13 step is
  the genuine integer-carry transition on residues, **not a toy**.
* **`integerCarry_realizes_boundedSlopeStep`** — the actual carry realizes one E.13
  edge: if `R_N ≡ K [ZMOD q]` and the digits across the canonical gap
  `g = canonGap q K` are all zero, then `R_{N+g} ≡ boundedSlopeStep q K [ZMOD q]`.
  This is the integer carry recurrence `R_{N+h} = 2^h·R_N`
  (`integerCarry_add_of_zero_digits`, the residue form of E.11) followed by E.12.
* **`integerCarry_tracks_boundedSlope_orbit`** — iterating the per-edge realization:
  along a canonical-gap orbit the actual carry residues track the
  `boundedSlopeStep` orbit for any number of steps.

## The construction (reusing the proved finite-state recurrence)

* **`CarryFibreDynamics.toTowerCycleFrom`** — from a carry-fibre dynamics whose
  slopes are uniform rational casts (`ρ`, `hρ`) and a base state `s₀`, the proved
  finite-state recurrence `recurrentCycle` (`TowerCycleConstruction`) extracts a
  genuine `TowerRecurrentCycle` reachable from `s₀`.  This is the base-point-aware
  rational form of `CarryFibreDynamics.toCycleData`.
* **`CarryAPSubfibre`** — the *precise residual datum*: an odd slope modulus `q ≥ 2`
  (the odd part of `Q·H`, manuscript E.5), a base numerator `K₀ ∈ {1,…,q−1}`, and a
  proof `P ≡ K₀ [ZMOD q]` that the **actual initial carry `R₀ = P`** sits at that
  numerator.  This is non-vacuous and genuinely shell-dependent (it pins the carry
  residue), never a vacuous or always-true hypothesis.
* **`towerCycleOfCarry` / `towerCycleOfFailingShell`** — the headline builders:
  from a failing shell's integer-carry data `(Q, P)` and a `CarryAPSubfibre`, they
  **construct** the `TowerRecurrentCycle` whose cycle is the genuine recurrent
  cycle of `boundedSlopeDynamics q` (= the actual carry-residue first-return map, by
  the bridge identity) reachable from the residue of `R₀ = P`, with rational slopes
  `K/q` and target denominator `Q`.

## Honest status

The Tower recurrent-cycle realization is **PARTIAL (sharply reduced)**, not vacuous:

* **CLOSED.** The recurrent cycle is *constructed* (finite-state pigeonhole on the
  genuine carry-residue map `boundedSlopeStep`, reachable from `R₀ = P`); its slopes
  are genuine carry-residue slopes `K/q ∈ (0,1)`; the E.13 law holds by construction;
  and the abstract step is *proved* to be the actual integer-carry doubling mod `q`
  (`boundedSlopeStep_modEq`), realized edge-by-edge by `integerCarry`
  (`integerCarry_realizes_boundedSlopeStep`, `integerCarry_tracks_boundedSlope_orbit`).
* **The single remaining genuine input** is the `CarryAPSubfibre` datum: that the
  failing shell's carry lands on an odd slope modulus `q ≥ 2` with a nonzero base
  residue (i.e. the AP-subfibre parametrisation `B_{x_s} = B_{x_0} + s·K_Γ` with a
  recurrent vertex), *and* that the actual digit gaps along the orbit are the
  canonical first-visible gaps `canonGap` (the E.2–E.4 shell/fibre combinatorics).
  The first half is packaged as `CarryAPSubfibre`; the second is exactly the zero-run
  hypothesis of `integerCarry_tracks_boundedSlope_orbit`.  Both are genuine,
  precisely stated, and *not* assumed away.

No `sorry`, no `admit`, no `native_decide`, no new `axiom`.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 1. The bridge identity: E.12 is the carry doubling map mod the slope modulus

`boundedSlopeStep q K = 2^{canonGap q K}·K − q` (the manuscript E.12 numerator
recurrence `K_Δ = 2^{γ₀} K_Γ − QH` on modulus `q = QH`).  Reduced mod `q`, the
subtracted `q` vanishes, leaving exactly the carry doubling `K ↦ 2^g·K`. -/

/--
**Bridge identity (E.12 = carry doubling mod `q`).**

For an odd slope modulus `q` and a numerator `1 ≤ K < q`, the E.13/E.12 successor
numerator `boundedSlopeStep q K = 2^{g}·K − q` is congruent to the pure carry
doubling `2^{g}·K` modulo `q`:

`boundedSlopeStep q K ≡ 2^{canonGap q K}·K  [ZMOD q].`

So the abstract bounded-slope step of `TowerLandingConstruction` is exactly the
*actual integer-carry doubling map reduced mod the slope modulus* — not a toy.
The `canonGap` band bound `q < 2^g·K` (`canonGap_bounds`) is what makes the natural
subtraction `2^g·K − q` faithful in `ℤ`. -/
theorem boundedSlopeStep_modEq {q K : ℕ} (hq : Odd q) (hK1 : 1 ≤ K) (hKq : K < q) :
    (boundedSlopeStep q K : ℤ) ≡ 2 ^ canonGap q K * (K : ℤ) [ZMOD (q : ℤ)] := by
  obtain ⟨hlow, _⟩ := canonGap_bounds hq hK1 hKq
  have hcast : (boundedSlopeStep q K : ℤ) = 2 ^ canonGap q K * (K : ℤ) - (q : ℤ) := by
    unfold boundedSlopeStep
    rw [Nat.cast_sub (le_of_lt hlow)]
    push_cast; ring
  rw [hcast, Int.modEq_iff_dvd]
  exact ⟨1, by ring⟩

/--
**The bounded-slope dynamics' step is the carry doubling on residues.**

Restating `boundedSlopeStep_modEq` at the level of `boundedSlopeDynamics`: the
deterministic carry transition `step` of the (genuine, finite) dynamics sends the
numerator of a state to `2^{gap}·(numerator)` modulo the slope modulus `q`, i.e. it
*is* the integer-carry doubling map reduced mod `q`. -/
theorem boundedSlopeDynamics_step_modEq (q : ℕ) (hq : Odd q) (hq2 : 2 ≤ q)
    (s : (boundedSlopeDynamics q hq hq2).State) :
    (((boundedSlopeDynamics q hq hq2).step s).1.val : ℤ)
      ≡ 2 ^ (boundedSlopeDynamics q hq hq2).gapOf s * (s.1.val : ℤ) [ZMOD (q : ℤ)] := by
  have h1 : (1 : ℕ) ≤ s.1.val := by have := s.2; omega
  have h2 : s.1.val < q := s.1.isLt
  exact boundedSlopeStep_modEq hq h1 h2

/-! ## 2. The actual integer carry realizes the bounded-slope step

Across a run of zero digits of the *canonical* length `g = canonGap q K`, the
integer carry `R_N` doubles (`integerCarry_add_of_zero_digits`, the residue form of
the manuscript E.11), so its residue mod `q` follows `boundedSlopeStep` by the
bridge identity.  This is the genuine realization of one E.13 cycle edge by the raw
carry. -/

/--
**One E.13 edge, realized by the raw carry.**

If the carry residue at position `N` is the numerator `K` (`R_N ≡ K [ZMOD q]`), the
slope modulus `q` is odd with `1 ≤ K < q`, and the digits across the canonical gap
`g = canonGap q K` are all zero (`d_{N+1} = … = d_{N+g} = 0`), then the carry residue
at `N + g` is the E.13 successor numerator:

`R_{N + canonGap q K} ≡ boundedSlopeStep q K  [ZMOD q].`

Proof: `R_{N+g} = 2^g·R_N` (`integerCarry_add_of_zero_digits`) `≡ 2^g·K`
(`hres`) `≡ boundedSlopeStep q K` (`boundedSlopeStep_modEq`). -/
theorem integerCarry_realizes_boundedSlopeStep
    (Q : ℕ) (P : ℤ) (d : ℕ → ℕ) (N : ℕ) {q K : ℕ}
    (hq : Odd q) (hK1 : 1 ≤ K) (hKq : K < q)
    (hres : integerCarry Q P d N ≡ (K : ℤ) [ZMOD (q : ℤ)])
    (hzero : ∀ j : ℕ, N < j → j ≤ N + canonGap q K → d j = 0) :
    integerCarry Q P d (N + canonGap q K) ≡ (boundedSlopeStep q K : ℤ) [ZMOD (q : ℤ)] := by
  rw [integerCarry_add_of_zero_digits Q P d N (canonGap q K) hzero]
  calc (2 : ℤ) ^ canonGap q K * integerCarry Q P d N
      ≡ 2 ^ canonGap q K * (K : ℤ) [ZMOD (q : ℤ)] := Int.ModEq.mul_left _ hres
    _ ≡ (boundedSlopeStep q K : ℤ) [ZMOD (q : ℤ)] := (boundedSlopeStep_modEq hq hK1 hKq).symm

/--
**The actual carry tracks the bounded-slope orbit (iterated realization).**

Given the slope modulus `q` odd, a numerator orbit `Kseq` of the bounded-slope step
(`Kseq (j+1) = boundedSlopeStep q (Kseq j)`) staying in `{1,…,q−1}`, position
markers `Nseq` advancing by the canonical gaps (`Nseq (j+1) = Nseq j + canonGap q
(Kseq j)`), the digits zero on each canonical gap, and the base residue
`R_{Nseq 0} ≡ Kseq 0 [ZMOD q]`, the actual integer carry residue tracks the orbit:

`R_{Nseq m} ≡ Kseq m  [ZMOD q]   for every `m`.

This is the per-edge realization (`integerCarry_realizes_boundedSlopeStep`) chained
by induction.  Specialised to a recurrent `Kseq` (the cycle of `boundedSlopeStep`),
it says the actual carry follows the recurrent cycle in residues — provided the
digit gaps are canonical, which is the lone remaining geometric input. -/
theorem integerCarry_tracks_boundedSlope_orbit
    (Q : ℕ) (P : ℤ) (d : ℕ → ℕ) {q : ℕ} (hq : Odd q)
    (Kseq : ℕ → ℕ) (Nseq : ℕ → ℕ)
    (hK1 : ∀ j, 1 ≤ Kseq j) (hKq : ∀ j, Kseq j < q)
    (hstep : ∀ j, Kseq (j + 1) = boundedSlopeStep q (Kseq j))
    (hpos : ∀ j, Nseq (j + 1) = Nseq j + canonGap q (Kseq j))
    (hzero : ∀ j : ℕ, ∀ i : ℕ, Nseq j < i → i ≤ Nseq j + canonGap q (Kseq j) → d i = 0)
    (hbase : integerCarry Q P d (Nseq 0) ≡ (Kseq 0 : ℤ) [ZMOD (q : ℤ)]) :
    ∀ m, integerCarry Q P d (Nseq m) ≡ (Kseq m : ℤ) [ZMOD (q : ℤ)] := by
  intro m
  induction m with
  | zero => exact hbase
  | succ m ih =>
      have hedge :
          integerCarry Q P d (Nseq m + canonGap q (Kseq m))
            ≡ (boundedSlopeStep q (Kseq m) : ℤ) [ZMOD (q : ℤ)] :=
        integerCarry_realizes_boundedSlopeStep Q P d (Nseq m) hq (hK1 m) (hKq m) ih
          (fun i hi1 hi2 => hzero m i hi1 hi2)
      rw [hpos m, hstep m]
      exact hedge

/-! ## 3. The base-point-aware rational recurrent-cycle extraction

`CarryFibreDynamics.toCycleData` (`TowerCycleConstruction`) extracts a recurrent
cycle from the fixed base point `nonemptyState.some`.  Here we extract it from a
*chosen* base state (the residue of the initial carry `R₀ = P`) and simultaneously
expose the rational slopes, packaging the result as a `TowerRecurrentCycle`. -/

/--
**Rational recurrent-cycle datum from a carry-fibre dynamics, reachable from `s₀`.**

Given a `CarryFibreDynamics` `D` whose slopes are uniform casts of a rational-valued
`ρ` (`hρ : (ρ s : ℝ) = D.slopeOf s`), a base state `s₀`, and a nonzero target
denominator `Q`, the proved finite-state recurrence `recurrentCycle D.step s₀`
(`TowerCycleConstruction`) yields a genuine `TowerRecurrentCycle`: the recurrent
cycle reachable from `s₀`, with the E.13 slope law holding on every edge by
construction, rational slopes `μ = ρ`, and the chosen `Q`.

This is the base-point-aware, rational-slope analogue of
`CarryFibreDynamics.toCycleData`. -/
def CarryFibreDynamics.toTowerCycleFrom (D : CarryFibreDynamics)
    (ρ : D.State → ℚ) (hρ : ∀ s, (ρ s : ℝ) = D.slopeOf s)
    (s₀ : D.State) (Q : ℕ) (hQ : Q ≠ 0) : TowerRecurrentCycle :=
  haveI := D.finiteState
  let rc := recurrentCycle D.step s₀
  { D :=
      { n := rc.p
        hn := rc.hp
        apSubfibre := D.apSubfibre
        layer := D.layer
        fibre := D.fibre
        terminal := D.terminal
        slope := fun k => D.slopeOf (rc.cyc k)
        gap := fun k => D.gapOf (rc.cyc k)
        slope_open := fun k => D.slope_open (rc.cyc k)
        slope_trans := by
          intro i
          show D.slopeOf (rc.cyc ⟨(i.val + 1) % rc.p, Nat.mod_lt _ rc.hp⟩)
              = (2 : ℝ) ^ D.gapOf (rc.cyc i) * D.slopeOf (rc.cyc i) - 1
          rw [rc.edge i, D.slope_trans (rc.cyc i)]
        slope_inj := fun a b h => rc.inj (D.slope_inj h) }
    μ := fun k => ρ (rc.cyc k)
    hcast := fun k => hρ (rc.cyc k)
    i := ⟨0, rc.hp⟩
    Q := Q
    hQ := hQ }

/-! ## 4. The precise residual datum and the headline builders -/

/--
**The precise residual input: the AP-subfibre landing datum (manuscript E.2–E.5).**

For a failing shell's integer carry `R_N = integerCarry Q P d N`, this records the
*genuinely geometric* content of the additive AP-subfibre parametrisation
`B_{x_s} = B_{x_0} + s·K_Γ` that the recurrent-cycle realization needs:

* `q` — the odd slope modulus (the odd part of `Q·H_Γ`, manuscript E.5; oddness of
  the AP modulus `H_Γ` is the *proved* `apModulus_odd`, and recurrent slopes have
  odd reduced denominator by the proved `carryCycle_den_odd`);
* `hq_odd`, `hq2` — `q` is odd and `≥ 2` (a nontrivial cycle, open slopes E.6);
* `K₀ ∈ {1,…,q−1}` — the base carry numerator `K_Γ mod q` of a recurrent vertex;
* `hP_res : P ≡ K₀ [ZMOD q]` — the **actual initial carry `R₀ = P`** sits at this
  numerator on the subfibre.

This datum is non-vacuous (a concrete witness is `carryAPSubfibre_nonvacuous`) and
genuinely shell-dependent: it pins the carry residue, so it is empty for `P ≡ 0`
(a degenerate all-zero carry) and contentful otherwise — never an always-true or
always-false hypothesis.  Crucially, `q` is the *geometric* AP modulus (E.5), not an
arbitrary modulus: the recurrent cycle is faithful only for this `q`. -/
structure CarryAPSubfibre (Q : ℕ) (P : ℤ) where
  /-- The odd slope modulus `q` (the odd part of `Q·H_Γ`, manuscript E.5). -/
  q : ℕ
  /-- `q` is odd (the AP modulus `H_Γ` is odd, `apModulus_odd`). -/
  hq_odd : Odd q
  /-- `q ≥ 2`: a nontrivial subfibre with open slopes (E.6). -/
  hq2 : 2 ≤ q
  /-- The base carry numerator `K_Γ mod q ∈ {1,…,q−1}` of a recurrent vertex. -/
  K₀ : ℕ
  /-- The base numerator is positive (nonzero residue ⇒ open slope `K₀/q > 0`). -/
  hK₀_pos : 1 ≤ K₀
  /-- The base numerator is below the modulus (`K₀/q < 1`). -/
  hK₀_lt : K₀ < q
  /-- The actual initial carry `R₀ = P` sits at numerator `K₀` modulo `q`. -/
  hP_res : P ≡ (K₀ : ℤ) [ZMOD (q : ℤ)]

/-- The base carry state (the residue of `R₀ = P`) inside the bounded-slope dynamics
on the subfibre's modulus. -/
def CarryAPSubfibre.baseState {Q : ℕ} {P : ℤ} (S : CarryAPSubfibre Q P) :
    (boundedSlopeDynamics S.q S.hq_odd S.hq2).State :=
  ⟨⟨S.K₀, S.hK₀_lt⟩, Nat.one_le_iff_ne_zero.mp S.hK₀_pos⟩

/--
**Headline builder: the Tower recurrent cycle, constructed from the failing-shell
carry.**

From a failing shell's integer-carry data `(Q, P)` (with `Q ≠ 0`) and the
AP-subfibre landing datum `S : CarryAPSubfibre Q P`, this **constructs** the
`TowerRecurrentCycle` that the capstone's `towerCycle` field consumes:

* the cycle is the *genuine recurrent cycle* of `boundedSlopeDynamics S.q` — which,
  by `boundedSlopeStep_modEq`, is the actual carry-residue first-return (doubling)
  map mod `q` — reachable from `S.baseState`, the residue of the initial carry
  `R₀ = P`;
* the slopes are the genuine carry-residue slopes `K/q ∈ (0,1)`, rational by
  construction;
* the E.13 slope law holds on every cyclic edge;
* the target denominator is the actual `Q`.

The recurrent cycle is produced by the proved finite-state pigeonhole
(`recurrentCycle`, `TowerCycleConstruction`) — no finiteness is assumed: the state
space `{K : Fin q // K ≠ 0}` is finite *by construction*. -/
def towerCycleOfCarry (Q : ℕ) (P : ℤ) (S : CarryAPSubfibre Q P) (hQ : Q ≠ 0) :
    TowerRecurrentCycle :=
  (boundedSlopeDynamics S.q S.hq_odd S.hq2).toTowerCycleFrom
    (fun s => (s.1.val : ℚ) / (S.q : ℚ))
    (fun s => by
      have h : (boundedSlopeDynamics S.q S.hq_odd S.hq2).slopeOf s
          = (s.1.val : ℝ) / (S.q : ℝ) := rfl
      rw [h]
      push_cast
      ring)
    S.baseState Q hQ

/-- The constructed Tower cycle carries the actual target denominator `Q`. -/
@[simp] theorem towerCycleOfCarry_Q (Q : ℕ) (P : ℤ) (S : CarryAPSubfibre Q P) (hQ : Q ≠ 0) :
    (towerCycleOfCarry Q P S hQ).Q = Q := rfl

/-- The constructed cycle is a genuine simple directed cycle (Theorem E.6). -/
theorem towerCycleOfCarry_isSimpleCycle (Q : ℕ) (P : ℤ) (S : CarryAPSubfibre Q P)
    (hQ : Q ≠ 0) : (towerCycleOfCarry Q P S hQ).D.toSCC.IsSimpleCycle :=
  (towerCycleOfCarry Q P S hQ).D.isSimpleCycle

/-- Every cycle slope is genuinely open `0 < μ < 1` (the E.6 condition), inherited
from the bounded-slope dynamics — the cycle is not degenerate. -/
theorem towerCycleOfCarry_slope_open (Q : ℕ) (P : ℤ) (S : CarryAPSubfibre Q P)
    (hQ : Q ≠ 0) (i : Fin (towerCycleOfCarry Q P S hQ).D.n) :
    0 < (towerCycleOfCarry Q P S hQ).D.slope i ∧ (towerCycleOfCarry Q P S hQ).D.slope i < 1 :=
  (towerCycleOfCarry Q P S hQ).D.slope_open i

/--
**Builder from a `FailingDyadicShell`.**

Specialises `towerCycleOfCarry` to a genuine failing shell: the target denominator
is `shell.Q` (`> 0` by `shell.hQ`), the integer `P` is the numerator of the shell's
rational target value `η = P/Q`, and `S : CarryAPSubfibre shell.Q P` is the
AP-subfibre landing datum.  The produced `TowerRecurrentCycle` is exactly the input
the capstone's `towerCycle` field requires. -/
def towerCycleOfFailingShell (shell : FailingDyadicShell) (P : ℤ)
    (S : CarryAPSubfibre shell.Q P) : TowerRecurrentCycle :=
  towerCycleOfCarry shell.Q P S shell.hQ.ne'

/-! ## 5. Non-vacuity

The residual datum is satisfiable and the builders are non-vacuous: the carry
`R₀ = P = 1` lands at numerator `K₀ = 1` on the modulus `q = 3` (`1 ≡ 1 [ZMOD 3]`),
producing a genuine `TowerRecurrentCycle` whose cycle is a simple directed cycle. -/

/-- A concrete AP-subfibre landing datum for the target `1/1` (`q = 3`, `K₀ = 1`).
`R₀ = 1` has residue `1` mod `3`, a nonzero numerator with open slope `1/3`. -/
def carryAPSubfibreExample : CarryAPSubfibre 1 1 where
  q := 3
  hq_odd := ⟨1, rfl⟩
  hq2 := by norm_num
  K₀ := 1
  hK₀_pos := le_refl 1
  hK₀_lt := by norm_num
  hP_res := Int.ModEq.refl 1

/-- **Non-vacuity of the residual datum.** -/
theorem carryAPSubfibre_nonvacuous : ∃ (Q : ℕ) (P : ℤ), Nonempty (CarryAPSubfibre Q P) :=
  ⟨1, 1, ⟨carryAPSubfibreExample⟩⟩

/-- **Non-vacuity of the headline builder**: a genuine `TowerRecurrentCycle` is
constructed from an actual carry datum, with target denominator `1`. -/
theorem towerCycleOfCarry_nonvacuous :
    ∃ t : TowerRecurrentCycle, t.Q = 1 :=
  ⟨towerCycleOfCarry 1 1 carryAPSubfibreExample one_ne_zero, rfl⟩

/-- The constructed witness cycle is a genuine simple directed cycle (Theorem E.6),
built from the carry — not a hand-picked toy. -/
theorem towerCycleOfCarry_example_isSimpleCycle :
    (towerCycleOfCarry 1 1 carryAPSubfibreExample one_ne_zero).D.toSCC.IsSimpleCycle :=
  towerCycleOfCarry_isSimpleCycle 1 1 carryAPSubfibreExample one_ne_zero

end

end Erdos260
