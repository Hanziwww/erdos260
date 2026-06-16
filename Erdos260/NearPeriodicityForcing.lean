import Erdos260.DensityBootstrap
import Erdos260.DescentDepthAgreementCore
import Erdos260.SemiperiodicWindowCore
import Erdos260.DigitSideClosure

/-!
# Near-periodicity forcing: what supplies `WindowPeriodic`, and what provably cannot

This module (NEW; it edits no existing file) formalizes the forcing mechanism the wave-7
density bootstrap (`DensityBootstrap`) recorded as its honest missing input: nothing in the
model yet forces window periodicity of the failing digit word.  The manuscript sources are
section 25.1 (dyadic cylinder reduction, `proof_v4_unconditional_clean_v5.tex` ~line 1110:
"a prefix ... agrees exactly with a binary segment of a rational number of denominator
<= Qp"), 25.2 (small-denominator segment density), 25.3 (residual singular squares), and the
M.3/M.4 semiperiodic window machinery.

## Part 1: the conditional bridge (the section 25.1 match, promoted to the tail)

The tree's section 25.1 match primitives are FINITE-WINDOW objects
(`MatchesCompletion d s n q0 a`, `WindowMatch d (dyadicDigit q0 a) s len`,
`MatchedDescentWindows`): they pin the word on `[s, s+n)` only, so they CANNOT supply
`WindowPeriodic` (which demands `d (n+p) = d n` for ALL `n > x`).  The exact strengthening
needed is the ALL-LENGTHS match, here named `TailMatch d x q0 a` ("the tail after `x` is the
binary completion of `a/q0`"); it is literally the conjunction over `len` of the existing
primitives (`tailMatch_of_windowMatch_all`, `tailMatch_of_matchesCompletion_all`), and it is
non-vacuous (`tailMatch_nonvacuous`).  Because the rational completion is EXACTLY periodic
with period `ord_{q0}(2)` (`dyadicDigit_period`, no hypotheses), a tail match transports
that period to the actual word (`tailMatch_eventually_periodic`) and lands in the
bootstrap's stratum (`windowPeriodic_of_tailMatch`).  Composition: every pinned family is
void at the matched contexts (`pinnedValue_tailMatch_void`), the four deep tail-match
props discharge the four bootstrap periodicity props
(`deepDyadicWindowPeriodicity_of_tailMatch` etc.), the full wave-5/6 levers follow
(`dyadicValueLever_of_tailMatch`, `towerFifthValueLever_of_tailMatch`,
`towerThirdsValueLever_of_tailMatch`, `fixedFamilyHit_void_of_tailMatch`), and the endpoint
is `erdos260_of_dyadicTailMatch`.

## Part 2: the unconditional finite-state carry (the autonomy is a THEOREM - and it is blind)

Writing `Q = u*2^t`, the carry mod `u` is the pure doubling orbit of `P`:
`u | R_N - 2^N P` (`oddpart_dvd_integerCarry_sub_pow_mul`).  Hence the mod-`u` trajectory is
EXACTLY periodic - not merely eventually, no pigeonhole needed - with any period `e` such
that `u | 2^e - 1` (`integerCarry_mod_oddpart_periodic`), and the pinned odd parts
`u in {1,3,5,7}` all have such an `e <= 4` (`pinned_oddpart_period_le_four`,
`pinned_carry_mod_oddpart_periodic`: ord = 1,2,4,3).  Adding the 2-adic part, the full
mod-`Q` trajectory is eventually exactly periodic after onset `t`
(`integerCarry_mod_Q_eventually_periodic`).  So the suggested finite-state autonomous
system `(R_N mod u, N mod ord)` IS autonomous and IS periodic - as a theorem.

THE HONEST REFUTATION of the unconditional supply through this route: the mod-`Q` state is
DIGIT-BLIND.  For ANY two digit words `d, d'` (same `P`), the trajectories agree mod `Q` at
every index (`integerCarry_mod_Q_digit_blind`, `integerCarry_mod_oddpart_digit_blind`):
the entire residue datum is a function of `(P, N)` alone, so no finite-state pigeonhole on
it can distinguish a periodic word from an aperiodic one, let alone force `WindowPeriodic`.
The digit lives strictly ABOVE the modulus: it is recovered from the carry PAIR by dividing
by `Q*(N+1)` (`integerCarry_digit_recover`), i.e. from the quotient, never the residue.

## Part 3: where the digit IS pinned (the two genuine unconditional forcings)

* **One level above the 2-part** (mod `2^{t+1}`, not mod `Q`): after onset `t` the reduced
  carry `rho_N = R_N / 2^t` is an integer (`reducedCarry_spec`) obeying
  `rho_{N+1} = 2 rho_N - u (N+1) d_{N+1}` (`reducedCarry_succ`), and at ODD positions
  `N+1` (where `u*(N+1)` is odd) its PARITY is the digit:
  `2 | rho_{N+1} - d_{N+1}` (`digit_parity_at_odd_position`), so the digit at every odd
  position past the onset is a FUNCTION of the reduced-carry value there
  (`digit_eq_parity_at_odd_position`).  At even positions `N+1 = 2^v m` the same mechanism
  needs the carry pair mod `2^{t+v+1}`; the odd case is the clean formal core.
* **Envelope tightness** (the value-pinned two-sided bound `0 <= R_N <= Q(N+2)`): the digit
  is FORCED outside the central band -
  `d_{N+1} = 1` when `Q(N+3) < 2 R_N` (`digit_forced_one_of_carry_high`),
  `d_{N+1} = 0` when `2 R_N < Q(N+1)` (`digit_forced_zero_of_carry_low`),
  and the converses (`carry_lower_of_digit_one`, `carry_upper_of_digit_zero`) show the free
  band is EXACTLY `Q(N+1) <= 2 R_N <= Q(N+3)` - width `2Q` out of a state range `~2Q(N+2)`,
  i.e. the digit is determined at all carry states except a `~1/(N+2)` fraction.
  Neither forcing is autonomous-periodic in itself: the band moves with `N` and the parity
  trajectory consumes the digits it reports.  They shrink WHERE a periodicity supply must
  act, they do not replace it.

## Part 4: the digit-side window (the goal-3 wiring, both directions, honest)

`ReturnIndexWindowClean ctx` (DigitSideClosure) demands `d = 0` on `(F, F+W]`.
* Positive (conditional): if the carry stays in the LOW band across the window, the
  envelope forcing delivers the cleanliness (`returnIndexWindowClean_of_carry_low`).
* Negative (a THEOREM modulo one explicit arithmetic gate): cleanliness on `(F, F+W]` is a
  `W`-length zero gap, which doubles the (positive, by nontermination) carry `2^W`-fold
  against the linear envelope; so whenever `Q*(F+W+2) < 2^W` the window CANNOT be clean
  (`not_returnIndexWindowClean_of_support_large`).  The low band cannot persist: a zero
  digit doubles the carry, so the forced-zero regime self-destructs in `~log` steps - the
  envelope forcing genuinely does NOT reach the full demanded interval unconditionally,
  and for support counts past the log threshold the clean-window route is provably dead.

No `sorry`, `admit`, new `axiom`, or `native_decide`.
-/

namespace Erdos260

set_option linter.unusedVariables false

/-! ## Part 1.  The tail match and the bridge into `WindowPeriodic` -/

/-- **The section 25.1 match, promoted to the tail**: every digit after the onset `x` is the
corresponding digit of the binary completion of `a/q0`.  This is the ALL-LENGTHS form of the
tree's finite-window primitives (`MatchesCompletion` / `WindowMatch`), and the exact
strengthening under which the section 25.1 cylinder-reduction output feeds the wave-7
density bootstrap. -/
def TailMatch (d : ℕ → ℕ) (x q0 a : ℕ) : Prop :=
  ∀ i : ℕ, d (x + 1 + i) = dyadicDigit q0 a i

/-- The tail match is exactly the all-depths `MatchesCompletion` at onset `x + 1`. -/
theorem tailMatch_of_matchesCompletion_all {d : ℕ → ℕ} {x q0 a : ℕ}
    (h : ∀ n : ℕ, MatchesCompletion d (x + 1) n q0 a) : TailMatch d x q0 a :=
  fun i => h (i + 1) i (Nat.lt_succ_self i)

/-- The tail match is exactly the all-lengths `WindowMatch` against the completion word. -/
theorem tailMatch_of_windowMatch_all {d : ℕ → ℕ} {x q0 a : ℕ}
    (h : ∀ len : ℕ, WindowMatch d (dyadicDigit q0 a) (x + 1) len) : TailMatch d x q0 a :=
  fun i => h (i + 1) i (Nat.lt_succ_self i)

/-- Conversely the tail match restricts to every finite depth. -/
theorem matchesCompletion_of_tailMatch {d : ℕ → ℕ} {x q0 a : ℕ}
    (h : TailMatch d x q0 a) (n : ℕ) : MatchesCompletion d (x + 1) n q0 a :=
  fun i _ => h i

/-- **Non-vacuity**: the completion itself (placed after the onset) realizes the tail match. -/
theorem tailMatch_nonvacuous (x q0 a : ℕ) :
    TailMatch (fun n => dyadicDigit q0 a (n - (x + 1))) x q0 a := by
  intro i
  simp only
  congr 1
  omega

/-- **Periodicity transport** (the heart of the bridge): a tail match makes the actual word
eventually periodic with the completion's period `ord_{q0}(2)` (`dyadicDigit_period`, which
needs no hypothesis), with onset `x`. -/
theorem tailMatch_eventually_periodic {d : ℕ → ℕ} {x q0 a : ℕ}
    (h : TailMatch d x q0 a) :
    ∀ n, x < n → d (n + orderOf (2 : ZMod q0)) = d n := by
  intro n hn
  have h1 : d (x + 1 + ((n - x - 1) + orderOf (2 : ZMod q0)))
      = dyadicDigit q0 a ((n - x - 1) + orderOf (2 : ZMod q0)) := h _
  have hn1 : x + 1 + ((n - x - 1) + orderOf (2 : ZMod q0))
      = n + orderOf (2 : ZMod q0) := by omega
  rw [hn1] at h1
  have h2 : d (x + 1 + (n - x - 1)) = dyadicDigit q0 a (n - x - 1) := h _
  have hn2 : x + 1 + (n - x - 1) = n := by omega
  rw [hn2] at h2
  rw [h1, h2]
  exact dyadicDigit_period q0 a (n - x - 1)

/-- **The bridge**: a tail match with window-compatible onset (`x <= X`) and period
(`2*ord_{q0}(2) <= X`) puts the failing context in the bootstrap's window-periodic stratum. -/
theorem windowPeriodic_of_tailMatch (ctx : ActualFailureContext) {x q0 a : ℕ}
    (hq0 : 1 < q0) (hodd : Odd q0) (hx : x ≤ ctx.X)
    (hord : 2 * orderOf (2 : ZMod q0) ≤ ctx.X)
    (h : TailMatch ctx.d x q0 a) : WindowPeriodic ctx :=
  ⟨x, orderOf (2 : ZMod q0), hx,
    orderOf_pos_iff.mpr (isOfFinOrder_two_zmod hq0 hodd), hord,
    fun n hn => tailMatch_eventually_periodic h n hn⟩

/-- **Composed master voiding**: NO pinned-value context (`value = P/(u*2^t)`, `u <= 7`)
admits a window-compatible tail match to a small-denominator completion - at EVERY scale.
(The section 25.1 match residual composed with the wave-7 bootstrap.) -/
theorem pinnedValue_tailMatch_void (ctx : ActualFailureContext)
    {u t : ℕ} {P : ℤ} (hupos : 0 < u) (hu7 : u ≤ 7)
    (heta : realWeightedValue (natBinaryAsReal ctx.d)
      = (P : ℝ) / ((u * 2 ^ t : ℕ) : ℝ))
    {x q0 a : ℕ} (hq0 : 1 < q0) (hodd : Odd q0) (hx : x ≤ ctx.X)
    (hord : 2 * orderOf (2 : ZMod q0) ≤ ctx.X)
    (hm : TailMatch ctx.d x q0 a) : False :=
  pinnedValue_windowPeriodic_void ctx hupos hu7 heta
    (windowPeriodic_of_tailMatch ctx hq0 hodd hx hord hm)

/-! ## Part 2.  The deep tail-match props and the additive wiring into the bootstrap -/

/-- **Deep dyadic tail match** (the section 25.1 residual in endpoint shape): every deep
dyadic-value failing context carries a window-compatible tail match. -/
def DeepDyadicTailMatch : Prop :=
  ∀ ctx : ActualFailureContext, 2 ^ 493443 < ctx.X → ShellValueDyadic ctx →
    ∃ x q0 a : ℕ, 1 < q0 ∧ Odd q0 ∧ x ≤ ctx.X ∧
      2 * orderOf (2 : ZMod q0) ≤ ctx.X ∧ TailMatch ctx.d x q0 a

/-- The deep dyadic tail match discharges the bootstrap's dyadic periodicity prop. -/
theorem deepDyadicWindowPeriodicity_of_tailMatch (h : DeepDyadicTailMatch) :
    DeepDyadicWindowPeriodicity := by
  intro ctx hX hdy
  obtain ⟨x, q0, a, hq0, hodd, hx, hord, hm⟩ := h ctx hX hdy
  exact windowPeriodic_of_tailMatch ctx hq0 hodd hx hord hm

/-- The deep dyadic tail match discharges the FULL dyadic-value lever. -/
theorem dyadicValueLever_of_tailMatch (h : DeepDyadicTailMatch) : DyadicValueLever :=
  dyadicValueLever_of_windowPeriodicity (deepDyadicWindowPeriodicity_of_tailMatch h)

/-- Deep fifth-value tail match. -/
def DeepFifthTailMatch : Prop :=
  ∀ ctx : ActualFailureContext, 2 ^ 493443 < ctx.X →
    (∃ t : ℕ, realWeightedValue (natBinaryAsReal ctx.shell.d) = 1 / (5 * 2 ^ t)) →
    ∃ x q0 a : ℕ, 1 < q0 ∧ Odd q0 ∧ x ≤ ctx.X ∧
      2 * orderOf (2 : ZMod q0) ≤ ctx.X ∧ TailMatch ctx.d x q0 a

/-- The fifth tail match discharges the bootstrap's fifth periodicity prop. -/
theorem deepFifthWindowPeriodicity_of_tailMatch (h : DeepFifthTailMatch) :
    DeepFifthWindowPeriodicity := by
  intro ctx hX hval
  obtain ⟨x, q0, a, hq0, hodd, hx, hord, hm⟩ := h ctx hX hval
  exact windowPeriodic_of_tailMatch ctx hq0 hodd hx hord hm

/-- The fifth tail match discharges the full fifth-value lever. -/
theorem towerFifthValueLever_of_tailMatch (h : DeepFifthTailMatch) :
    TowerFifthValueLever :=
  towerFifthValueLever_of_windowPeriodicity (deepFifthWindowPeriodicity_of_tailMatch h)

/-- Deep thirds-value tail match. -/
def DeepThirdsTailMatch : Prop :=
  ∀ ctx : ActualFailureContext, 2 ^ 493443 < ctx.X →
    (∃ t : ℕ, realWeightedValue (natBinaryAsReal ctx.shell.d) = 2 / (3 * 2 ^ t)) →
    ∃ x q0 a : ℕ, 1 < q0 ∧ Odd q0 ∧ x ≤ ctx.X ∧
      2 * orderOf (2 : ZMod q0) ≤ ctx.X ∧ TailMatch ctx.d x q0 a

/-- The thirds tail match discharges the bootstrap's thirds periodicity prop. -/
theorem deepThirdsWindowPeriodicity_of_tailMatch (h : DeepThirdsTailMatch) :
    DeepThirdsWindowPeriodicity := by
  intro ctx hX hval
  obtain ⟨x, q0, a, hq0, hodd, hx, hord, hm⟩ := h ctx hX hval
  exact windowPeriodic_of_tailMatch ctx hq0 hodd hx hord hm

/-- The thirds tail match discharges the full thirds-value lever. -/
theorem towerThirdsValueLever_of_tailMatch (h : DeepThirdsTailMatch) :
    TowerThirdsValueLever :=
  towerThirdsValueLever_of_windowPeriodicity (deepThirdsWindowPeriodicity_of_tailMatch h)

/-- Deep fixed-family tail match (one Prop for all five surviving families). -/
def DeepFixedFamilyTailMatch : Prop :=
  ∀ ctx : ActualFailureContext, 2 ^ 493443 < ctx.X → FixedFamilyHit ctx →
    ∃ x q0 a : ℕ, 1 < q0 ∧ Odd q0 ∧ x ≤ ctx.X ∧
      2 * orderOf (2 : ZMod q0) ≤ ctx.X ∧ TailMatch ctx.d x q0 a

/-- The family tail match discharges the bootstrap's family periodicity prop. -/
theorem deepFixedFamilyWindowPeriodicity_of_tailMatch (h : DeepFixedFamilyTailMatch) :
    DeepFixedFamilyWindowPeriodicity := by
  intro ctx hX hhit
  obtain ⟨x, q0, a, hq0, hodd, hx, hord, hm⟩ := h ctx hX hhit
  exact windowPeriodic_of_tailMatch ctx hq0 hodd hx hord hm

/-- The family tail match voids ALL five fixed families at EVERY context. -/
theorem fixedFamilyHit_void_of_tailMatch (h : DeepFixedFamilyTailMatch)
    (ctx : ActualFailureContext) : ¬ FixedFamilyHit ctx :=
  fixedFamilyHit_void_of_windowPeriodicity
    (deepFixedFamilyWindowPeriodicity_of_tailMatch h) ctx

/-- **The endpoint through the tail match**: `Erdos260Statement` from the deep dyadic
section 25.1 tail match plus the lever-shrunk wave-5 surfaces. -/
theorem erdos260_of_dyadicTailMatch (h : DeepDyadicTailMatch)
    (surfaces : DyadicValueLever → Erdos260DyadicLeverResidual) : Erdos260Statement :=
  erdos260_of_dyadicWindowPeriodicity (deepDyadicWindowPeriodicity_of_tailMatch h) surfaces

/-! ## Part 3.  The finite-state mod-`u` carry: exact periodicity, and digit blindness -/

/-- The carry mod the odd part is the pure doubling orbit of `P`: `u | R_N - 2^N P`. -/
theorem oddpart_dvd_integerCarry_sub_pow_mul (u t : ℕ) (P : ℤ) (d : ℕ → ℕ) (N : ℕ) :
    (u : ℤ) ∣ integerCarry (u * 2 ^ t) P d N - 2 ^ N * P := by
  have hu : (u : ℤ) ∣ ((u * 2 ^ t : ℕ) : ℤ) := ⟨(2 : ℤ) ^ t, by push_cast; ring⟩
  exact hu.trans (dvd_integerCarry_sub_pow_mul (u * 2 ^ t) P d N)

/-- **The finite-state autonomy is a theorem, in EXACT form**: with `u | 2^e - 1` the carry
trajectory mod `u` is periodic with period `e` at EVERY index (no pigeonhole, no onset):
`u | R_{N+e} - R_N`.  This is the `(R_N mod u, N mod ord)` autonomous system's periodicity. -/
theorem integerCarry_mod_oddpart_periodic (u t : ℕ) (P : ℤ) (d : ℕ → ℕ) {e : ℕ}
    (he : (u : ℤ) ∣ 2 ^ e - 1) (N : ℕ) :
    (u : ℤ) ∣ integerCarry (u * 2 ^ t) P d (N + e) - integerCarry (u * 2 ^ t) P d N := by
  have h1 := oddpart_dvd_integerCarry_sub_pow_mul u t P d (N + e)
  have h2 := oddpart_dvd_integerCarry_sub_pow_mul u t P d N
  have h3 : (u : ℤ) ∣ 2 ^ N * (2 ^ e - 1) * P := (he.mul_left ((2 : ℤ) ^ N)).mul_right P
  have key : integerCarry (u * 2 ^ t) P d (N + e) - integerCarry (u * 2 ^ t) P d N
      = (integerCarry (u * 2 ^ t) P d (N + e) - 2 ^ (N + e) * P)
        - (integerCarry (u * 2 ^ t) P d N - 2 ^ N * P) + 2 ^ N * (2 ^ e - 1) * P := by
    rw [pow_add]; ring
  rw [key]
  exact dvd_add (dvd_sub h1 h2) h3

/-- **Mod-`Q` eventual exact periodicity**: past the 2-adic onset `t`, the FULL carry
trajectory mod `Q = u*2^t` is exactly periodic with any period `e` such that `u | 2^e - 1`. -/
theorem integerCarry_mod_Q_eventually_periodic (u t : ℕ) (P : ℤ) (d : ℕ → ℕ) {e : ℕ}
    (he : (u : ℤ) ∣ 2 ^ e - 1) {N : ℕ} (htN : t ≤ N) :
    ((u * 2 ^ t : ℕ) : ℤ)
      ∣ integerCarry (u * 2 ^ t) P d (N + e) - integerCarry (u * 2 ^ t) P d N := by
  have h1 := dvd_integerCarry_sub_pow_mul (u * 2 ^ t) P d (N + e)
  have h2 := dvd_integerCarry_sub_pow_mul (u * 2 ^ t) P d N
  obtain ⟨c, hc⟩ := he
  have hsplit : (2 : ℤ) ^ N = 2 ^ t * 2 ^ (N - t) := by
    rw [← pow_add]
    congr 1
    omega
  have h3 : ((u * 2 ^ t : ℕ) : ℤ) ∣ 2 ^ N * (2 ^ e - 1) * P := by
    refine ⟨2 ^ (N - t) * c * P, ?_⟩
    rw [hc, hsplit]
    push_cast
    ring
  have key : integerCarry (u * 2 ^ t) P d (N + e) - integerCarry (u * 2 ^ t) P d N
      = (integerCarry (u * 2 ^ t) P d (N + e) - 2 ^ (N + e) * P)
        - (integerCarry (u * 2 ^ t) P d N - 2 ^ N * P) + 2 ^ N * (2 ^ e - 1) * P := by
    rw [pow_add]; ring
  rw [key]
  exact dvd_add (dvd_sub h1 h2) h3

/-- **THE DIGIT BLINDNESS (the honest refutation of the autonomous-pigeonhole route)**:
the carry trajectories of ANY two digit words agree mod `Q` at EVERY index.  The complete
mod-`Q` residue datum is a function of `(P, N)` alone - it contains ZERO bits of digit
information, so no finite-state argument on it can force word periodicity. -/
theorem integerCarry_mod_Q_digit_blind (Q : ℕ) (P : ℤ) (d d' : ℕ → ℕ) (N : ℕ) :
    (Q : ℤ) ∣ integerCarry Q P d N - integerCarry Q P d' N := by
  have h1 := dvd_integerCarry_sub_pow_mul Q P d N
  have h2 := dvd_integerCarry_sub_pow_mul Q P d' N
  have key : integerCarry Q P d N - integerCarry Q P d' N
      = (integerCarry Q P d N - 2 ^ N * P) - (integerCarry Q P d' N - 2 ^ N * P) := by
    ring
  rw [key]
  exact dvd_sub h1 h2

/-- Digit blindness at the odd part: the finite-state mod-`u` system in particular pins
NO digit of the word. -/
theorem integerCarry_mod_oddpart_digit_blind (u t : ℕ) (P : ℤ) (d d' : ℕ → ℕ) (N : ℕ) :
    (u : ℤ) ∣ integerCarry (u * 2 ^ t) P d N - integerCarry (u * 2 ^ t) P d' N := by
  have hu : (u : ℤ) ∣ ((u * 2 ^ t : ℕ) : ℤ) := ⟨(2 : ℤ) ^ t, by push_cast; ring⟩
  exact hu.trans (integerCarry_mod_Q_digit_blind (u * 2 ^ t) P d d' N)

/-- The pinned odd parts `u in {1,3,5,7}` have Mersenne periods `e <= 4`
(ord = 1, 2, 4, 3 respectively): the finite state space of the mod-`u` system. -/
theorem pinned_oddpart_period_le_four {u : ℕ} (hu : u = 1 ∨ u = 3 ∨ u = 5 ∨ u = 7) :
    ∃ e : ℕ, 0 < e ∧ e ≤ 4 ∧ (u : ℤ) ∣ 2 ^ e - 1 := by
  rcases hu with h | h | h | h <;> subst h
  · exact ⟨1, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨4, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, by norm_num, by norm_num, by norm_num⟩

/-- **The pinned-family finite-state periodicity, packaged**: for every pinned odd part the
carry mod `u` is exactly periodic with an explicit period `<= 4`, at every index, for every
digit word.  (And, by `integerCarry_mod_oddpart_digit_blind`, this trajectory is the same
for every digit word - periodic AND blind.) -/
theorem pinned_carry_mod_oddpart_periodic {u : ℕ} (hu : u = 1 ∨ u = 3 ∨ u = 5 ∨ u = 7)
    (t : ℕ) (P : ℤ) (d : ℕ → ℕ) :
    ∃ e : ℕ, 0 < e ∧ e ≤ 4 ∧ ∀ N : ℕ,
      (u : ℤ) ∣ integerCarry (u * 2 ^ t) P d (N + e) - integerCarry (u * 2 ^ t) P d N := by
  obtain ⟨e, he0, he4, hdvd⟩ := pinned_oddpart_period_le_four hu
  exact ⟨e, he0, he4, fun N => integerCarry_mod_oddpart_periodic u t P d hdvd N⟩

/-! ## Part 4.  The reduced carry and the 2-adic digit recovery at odd positions -/

/-- The reduced carry `rho_N = R_N / 2^t` (exact integer division past the onset `t`). -/
def reducedCarry (u t : ℕ) (P : ℤ) (d : ℕ → ℕ) (N : ℕ) : ℤ :=
  integerCarry (u * 2 ^ t) P d N / 2 ^ t

/-- Past the onset the reduction is exact: `2^t * rho_N = R_N`. -/
theorem reducedCarry_spec (u t : ℕ) (P : ℤ) (d : ℕ → ℕ) {N : ℕ} (htN : t ≤ N) :
    2 ^ t * reducedCarry u t P d N = integerCarry (u * 2 ^ t) P d N := by
  have hdvd : (2 : ℤ) ^ t ∣ integerCarry (u * 2 ^ t) P d N :=
    two_pow_dvd_integerCarry (Q := u * 2 ^ t) (u := u) (t := t) rfl P d htN
  rw [reducedCarry, mul_comm]
  exact Int.ediv_mul_cancel hdvd

/-- **The reduced recursion**: past the onset, `rho_{N+1} = 2 rho_N - u (N+1) d_{N+1}` -
the `2^t` part of the denominator is gone, the step coefficient is `u*(N+1)`. -/
theorem reducedCarry_succ (u t : ℕ) (P : ℤ) (d : ℕ → ℕ) {N : ℕ} (htN : t ≤ N) :
    reducedCarry u t P d (N + 1)
      = 2 * reducedCarry u t P d N - (u : ℤ) * ((N + 1 : ℕ) : ℤ) * (d (N + 1) : ℤ) := by
  have h2t : ((2 : ℤ) ^ t) ≠ 0 := by positivity
  apply mul_left_cancel₀ h2t
  have hN := reducedCarry_spec u t P d htN
  rw [reducedCarry_spec u t P d (Nat.le_succ_of_le htN), integerCarry_succ]
  push_cast
  push_cast at hN
  linear_combination (-2 : ℤ) * hN

/-- **The parity recovery at odd positions** (the digit pinned ONE level above the 2-part):
for odd `u` and odd position `N+1` past the onset, the parity of the reduced carry IS the
emitted digit: `2 | rho_{N+1} - d_{N+1}`.  (Mod `2^{t+1}` of the carry pair, where the step
coefficient `u*2^t*(N+1)` has 2-adic valuation exactly `t`.) -/
theorem digit_parity_at_odd_position {u : ℕ} (hu : Odd u) (t : ℕ) (P : ℤ) (d : ℕ → ℕ)
    {N : ℕ} (htN : t ≤ N) (hodd : Odd (N + 1)) :
    (2 : ℤ) ∣ reducedCarry u t P d (N + 1) - (d (N + 1) : ℤ) := by
  rw [reducedCarry_succ u t P d htN]
  obtain ⟨k, hk⟩ := hu.mul hodd
  have hcast : ((u * (N + 1) : ℕ) : ℤ) = 2 * (k : ℤ) + 1 := by exact_mod_cast hk
  refine ⟨reducedCarry u t P d N - (k : ℤ) * (d (N + 1) : ℤ) - (d (N + 1) : ℤ), ?_⟩
  push_cast at hcast ⊢
  linear_combination -(d (N + 1) : ℤ) * hcast

/-- **The digit at every odd position past the onset is a FUNCTION of the reduced-carry
value there**: `d_{N+1} = 0` iff `rho_{N+1}` is even.  This is the genuine (but
non-autonomous: the trajectory consumes the digits it reports) digit content of the
2-adic level `t+1`. -/
theorem digit_eq_parity_at_odd_position {u : ℕ} (hu : Odd u) (t : ℕ) (P : ℤ) {d : ℕ → ℕ}
    (hd : BinaryDigits d) {N : ℕ} (htN : t ≤ N) (hodd : Odd (N + 1)) :
    d (N + 1) = if (2 : ℤ) ∣ reducedCarry u t P d (N + 1) then 0 else 1 := by
  have hpar := digit_parity_at_odd_position hu t P d htN hodd
  by_cases hdvd : (2 : ℤ) ∣ reducedCarry u t P d (N + 1)
  · rw [if_pos hdvd]
    rcases hd (N + 1) with h0 | h1
    · exact h0
    · exfalso
      rw [h1] at hpar
      push_cast at hpar
      have h2 : (2 : ℤ) ∣ reducedCarry u t P d (N + 1)
          - (reducedCarry u t P d (N + 1) - 1) := dvd_sub hdvd hpar
      have h3 : reducedCarry u t P d (N + 1)
          - (reducedCarry u t P d (N + 1) - 1) = 1 := by ring
      rw [h3] at h2
      norm_num at h2
  · rw [if_neg hdvd]
    rcases hd (N + 1) with h0 | h1
    · exfalso
      rw [h0] at hpar
      push_cast at hpar
      exact hdvd (by simpa using hpar)
    · exact h1

/-! ## Part 5.  The envelope forcing: the digit is pinned outside the central carry band -/

/-- **Forced one**: if the carry exceeds the upper band edge (`Q(N+3) < 2 R_N`), the next
digit MUST be `1` - a zero step would double past the envelope `R_{N+1} <= Q(N+3)`. -/
theorem digit_forced_one_of_carry_high {Q : ℕ} {P : ℤ} {d : ℕ → ℕ}
    (hQ : 0 < Q) (hd : BinaryDigits d)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ)) {N : ℕ}
    (hhigh : (Q : ℤ) * ((N + 3 : ℕ) : ℤ) < 2 * integerCarry Q P d N) :
    d (N + 1) = 1 := by
  rcases hd (N + 1) with h0 | h1
  · exfalso
    have hb := (integerCarry_bounds_of_rational_value
      (Q := Q) (P := P) (d := d) (N + 1) hQ hd heta).2
    rw [integerCarry_succ, h0] at hb
    push_cast at hb hhigh
    linarith
  · exact h1

/-- **Forced zero**: if the carry is below the lower band edge (`2 R_N < Q(N+1)`), the next
digit MUST be `0` - a one step would drive the carry negative. -/
theorem digit_forced_zero_of_carry_low {Q : ℕ} {P : ℤ} {d : ℕ → ℕ}
    (hQ : 0 < Q) (hd : BinaryDigits d)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ)) {N : ℕ}
    (hlow : 2 * integerCarry Q P d N < (Q : ℤ) * ((N + 1 : ℕ) : ℤ)) :
    d (N + 1) = 0 := by
  rcases hd (N + 1) with h0 | h1
  · exact h0
  · exfalso
    have hb := (integerCarry_bounds_of_rational_value
      (Q := Q) (P := P) (d := d) (N + 1) hQ hd heta).1
    rw [integerCarry_succ, h1] at hb
    push_cast at hb hlow
    linarith

/-- Converse: a one step certifies the lower band edge `Q(N+1) <= 2 R_N`. -/
theorem carry_lower_of_digit_one {Q : ℕ} {P : ℤ} {d : ℕ → ℕ}
    (hQ : 0 < Q) (hd : BinaryDigits d)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ)) {N : ℕ}
    (h1 : d (N + 1) = 1) :
    (Q : ℤ) * ((N + 1 : ℕ) : ℤ) ≤ 2 * integerCarry Q P d N := by
  have hb := (integerCarry_bounds_of_rational_value
    (Q := Q) (P := P) (d := d) (N + 1) hQ hd heta).1
  rw [integerCarry_succ, h1] at hb
  push_cast at hb ⊢
  linarith

/-- Converse: a zero step certifies the upper band edge `2 R_N <= Q(N+3)`.  Together with
the two forcings, the digit-free band is EXACTLY `Q(N+1) <= 2 R_N <= Q(N+3)` - width `2Q`
inside the state range `[0, 2Q(N+2)]`: the digit is determined at all but a `~1/(N+2)`
fraction of carry states. -/
theorem carry_upper_of_digit_zero {Q : ℕ} {P : ℤ} {d : ℕ → ℕ}
    (hQ : 0 < Q) (hd : BinaryDigits d)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ)) {N : ℕ}
    (h0 : d (N + 1) = 0) :
    2 * integerCarry Q P d N ≤ (Q : ℤ) * ((N + 3 : ℕ) : ℤ) := by
  have hb := (integerCarry_bounds_of_rational_value
    (Q := Q) (P := P) (d := d) (N + 1) hQ hd heta).2
  rw [integerCarry_succ, h0] at hb
  push_cast at hb ⊢
  linarith

/-! ## Part 6.  The digit-side window `(F, F+W]`: both directions of the goal-3 wiring -/

/-- **Positive (conditional) wiring**: if the carry stays in the LOW band across the raw
index window, the envelope forcing closes `ReturnIndexWindowClean` outright - and with it
both remaining digit fields of the digit-side residual (`returnZeroBody_of_indexWindowClean`,
`returnMaxCleanBody_of_indexWindowClean`). -/
theorem returnIndexWindowClean_of_carry_low (ctx : ActualFailureContext) {P : ℤ}
    (heta : realWeightedValue (natBinaryAsReal ctx.d) = (P : ℝ) / (ctx.Q : ℝ))
    (hlow : ∀ n : ℕ,
      ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X ≤ n →
      n < ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
          + (supportShell ctx.shell.d ctx.shell.X).card →
      2 * integerCarry ctx.Q P ctx.d n < (ctx.Q : ℤ) * ((n + 1 : ℕ) : ℤ)) :
    ReturnIndexWindowClean ctx := by
  intro n hn1 hn2
  have h1n : 1 ≤ n := by omega
  have hl := hlow (n - 1) (by omega) (by omega)
  have hz := digit_forced_zero_of_carry_low ctx.hQ ctx.hd heta (N := n - 1) hl
  rwa [show n - 1 + 1 = n from by omega] at hz

/-- **Negative threshold (the honest verdict on reaching `(F, F+W]`)**: whenever the support
count `W` beats the logarithmic gate `Q*(F+W+2) < 2^W`, the index window CANNOT be clean -
cleanliness is a `W`-length zero gap, which doubles the positive carry `2^W`-fold against
the linear envelope.  So in this regime the digit-side residual genuinely fires on
`¬ ReturnIndexWindowClean` contexts; no unconditional forcing closes the window positively
(the low band self-destructs: each forced zero doubles the carry out of it in `~log` steps). -/
theorem not_returnIndexWindowClean_of_support_large (ctx : ActualFailureContext) {P : ℤ}
    (heta : realWeightedValue (natBinaryAsReal ctx.d) = (P : ℝ) / (ctx.Q : ℝ))
    (hbig : (ctx.Q : ℤ) * ((ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X
        + (supportShell ctx.shell.d ctx.shell.X).card + 2 : ℕ) : ℤ)
      < 2 ^ (supportShell ctx.shell.d ctx.shell.X).card) :
    ¬ ReturnIndexWindowClean ctx := by
  intro hclean
  set F := ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X with hF
  set W := (supportShell ctx.shell.d ctx.shell.X).card with hW
  have hpos : 0 < integerCarry ctx.Q P ctx.d F :=
    integerCarry_pos_of_not_eventuallyZero ctx.hQ ctx.hd heta ctx.hnonterm F
  have hzero : ∀ j : ℕ, F < j → j ≤ F + W → ctx.d j = 0 := fun j h1 h2 => hclean j h1 h2
  have hgap := pow_two_le_of_zero_gap (Q := ctx.Q) (P := P) (d := ctx.d) (N := F) (h := W)
    ctx.hQ ctx.hd heta hpos hzero
  exact absurd hgap (not_le.mpr hbig)

/-! ## Part 7.  Machine-readable status (honest) -/

/-- Honest machine-readable status of the near-periodicity forcing module. -/
def nearPeriodicityForcingStatus : List String :=
  [ "INVENTORY FINDING - the tree's sec-25.1 match infrastructure is FINITE-WINDOW only: " ++
      "MatchesCompletion d s n q0 a (DescentDepthAgreementCore; hmatch discharged to " ++
      "(D1) residue-band + (D2) no-large-run in DescentDepthClosureCore), WindowMatch / " ++
      "MatchedSemiperiodicWindow / MatchedDescentWindows (SemiperiodicWindowCore), and the " ++
      "M.3.1 anchored patches (SliceM31*, ReturnStartPlacementCore) all pin the word on a " ++
      "bounded window [s, s+n) only.  WindowPeriodic (DensityBootstrap) demands the FULL " ++
      "tail (all n > x), so NO existing residual bridges to it directly; the exact " ++
      "strengthening is the all-lengths match, formalized here as TailMatch " ++
      "(tailMatch_of_matchesCompletion_all / tailMatch_of_windowMatch_all; nonvacuous by " ++
      "tailMatch_nonvacuous).",
    "CONDITIONAL BRIDGE (composition win, goal i) - windowPeriodic_of_tailMatch: a tail " ++
      "match to a small-denominator completion a/q0 (q0 > 1 odd, onset x <= X, " ++
      "2*ord_{q0}(2) <= X) lands the context in the bootstrap's window-periodic stratum " ++
      "(periodicity of dyadicDigit is FREE, dyadicDigit_period).  Composed endpoints: " ++
      "pinnedValue_tailMatch_void (every pinned family void at matched contexts, every " ++
      "scale), the four deep props DeepDyadicTailMatch / DeepFifthTailMatch / " ++
      "DeepThirdsTailMatch / DeepFixedFamilyTailMatch discharging " ++
      "DeepDyadicWindowPeriodicity etc., the full levers dyadicValueLever_of_tailMatch / " ++
      "towerFifthValueLever_of_tailMatch / towerThirdsValueLever_of_tailMatch / " ++
      "fixedFamilyHit_void_of_tailMatch, and the endpoint erdos260_of_dyadicTailMatch : " ++
      "DeepDyadicTailMatch -> (DyadicValueLever -> Erdos260DyadicLeverResidual) -> " ++
      "Erdos260Statement.",
    "UNCONDITIONAL (the finite-state autonomy IS a theorem, goal ii) - with Q = u*2^t the " ++
      "carry mod u is the pure doubling orbit of P (oddpart_dvd_integerCarry_sub_pow_mul), " ++
      "hence EXACTLY periodic with any period e with u | 2^e - 1, at every index, no " ++
      "pigeonhole (integerCarry_mod_oddpart_periodic); the pinned odd parts u in {1,3,5,7} " ++
      "carry e <= 4 (ord = 1,2,4,3: pinned_oddpart_period_le_four, " ++
      "pinned_carry_mod_oddpart_periodic); and past the onset t the FULL mod-Q trajectory " ++
      "is eventually exactly periodic (integerCarry_mod_Q_eventually_periodic).",
    "REFUTED (the unconditional supply via residue pigeonhole) - the mod-Q state is " ++
      "DIGIT-BLIND: integerCarry_mod_Q_digit_blind / integerCarry_mod_oddpart_digit_blind " ++
      "prove the trajectories of ANY two digit words agree mod Q at every index (the " ++
      "residue datum is a function of (P, N) alone).  A periodic-but-blind finite-state " ++
      "system cannot distinguish periodic words from aperiodic ones, hence cannot force " ++
      "WindowPeriodic.  The digit is recovered only ABOVE the modulus: from the carry pair " ++
      "by dividing by Q*(N+1) (integerCarry_digit_recover, wave 7).",
    "UNCONDITIONAL (partial digit determination, the 2-adic level t+1) - the reduced carry " ++
      "rho_N = R_N / 2^t is exact past the onset (reducedCarry_spec) with recursion " ++
      "rho_{N+1} = 2 rho_N - u(N+1) d_{N+1} (reducedCarry_succ); at ODD positions N+1 the " ++
      "parity of rho_{N+1} IS the digit (digit_parity_at_odd_position, " ++
      "digit_eq_parity_at_odd_position): d is a FUNCTION of the reduced-carry value at " ++
      "every odd position past t.  HONEST LIMIT: the parity trajectory is non-autonomous " ++
      "(it consumes the digits it reports); at even positions N+1 = 2^v m the recovery " ++
      "needs the pair mod 2^{t+v+1}.  No periodicity follows without an input on rho.",
    "UNCONDITIONAL (envelope forcing; the positions where the value-pinned envelope is " ++
      "tight, characterized EXACTLY) - digit_forced_one_of_carry_high (Q(N+3) < 2R_N " ++
      "forces d_{N+1} = 1), digit_forced_zero_of_carry_low (2R_N < Q(N+1) forces " ++
      "d_{N+1} = 0), with converses carry_lower_of_digit_one / carry_upper_of_digit_zero: " ++
      "the free band is exactly Q(N+1) <= 2R_N <= Q(N+3), width 2Q out of the state range " ++
      "2Q(N+2) - the digit is pinned outside a ~1/(N+2) fraction of states.  HONEST " ++
      "LIMIT: the band moves with N and no unconditional invariant confines the actual " ++
      "carry to one side, so this shrinks where a periodicity supply must act; it does " ++
      "not replace one.",
    "GOAL-3 WIRING (ReturnIndexWindowClean, both directions, honest) - positive " ++
      "conditional: returnIndexWindowClean_of_carry_low (carry in the low band across " ++
      "(F, F+W] closes the window, hence both digit fields, via the wave DigitSideClosure " ++
      "bridges).  Negative threshold: not_returnIndexWindowClean_of_support_large - when " ++
      "Q*(F+W+2) < 2^W the window CANNOT be clean (cleanliness = W-length zero gap = " ++
      "2^W-fold doubling against the linear envelope, pow_two_le_of_zero_gap).  So the " ++
      "envelope forcing does NOT reach the demanded interval unconditionally (the " ++
      "forced-zero band self-destructs by doubling in ~log steps), and past the log " ++
      "threshold the clean route is provably dead - the residual genuinely fires on " ++
      "not-clean contexts there.",
    "WHAT RESISTS - the tail match itself.  The sec-25.1 cylinder reduction produces " ++
      "per-window agreement (already reduced in-tree to the centre-free residue band " ++
      "(D1) + no-large-run (D2)); promoting it to the full tail (all depths " ++
      "simultaneously, one centre) is the manuscript's iterated 25.1/25.3 descent and " ++
      "remains the irreducible residual, now in the sharpest endpoint shape " ++
      "DeepDyadicTailMatch (demanded only at X > 2^493443, only for dyadic-value " ++
      "contexts, only with window-compatible onset/period)." ]

theorem nearPeriodicityForcingStatus_nonempty : nearPeriodicityForcingStatus ≠ [] := by
  simp [nearPeriodicityForcingStatus]

/-! ## Audit block: every key declaration, axioms only
`[propext, Classical.choice, Quot.sound]` or fewer. -/

#print axioms tailMatch_of_matchesCompletion_all
#print axioms tailMatch_of_windowMatch_all
#print axioms matchesCompletion_of_tailMatch
#print axioms tailMatch_nonvacuous
#print axioms tailMatch_eventually_periodic
#print axioms windowPeriodic_of_tailMatch
#print axioms pinnedValue_tailMatch_void
#print axioms deepDyadicWindowPeriodicity_of_tailMatch
#print axioms dyadicValueLever_of_tailMatch
#print axioms deepFifthWindowPeriodicity_of_tailMatch
#print axioms towerFifthValueLever_of_tailMatch
#print axioms deepThirdsWindowPeriodicity_of_tailMatch
#print axioms towerThirdsValueLever_of_tailMatch
#print axioms deepFixedFamilyWindowPeriodicity_of_tailMatch
#print axioms fixedFamilyHit_void_of_tailMatch
#print axioms erdos260_of_dyadicTailMatch
#print axioms oddpart_dvd_integerCarry_sub_pow_mul
#print axioms integerCarry_mod_oddpart_periodic
#print axioms integerCarry_mod_Q_eventually_periodic
#print axioms integerCarry_mod_Q_digit_blind
#print axioms integerCarry_mod_oddpart_digit_blind
#print axioms pinned_oddpart_period_le_four
#print axioms pinned_carry_mod_oddpart_periodic
#print axioms reducedCarry_spec
#print axioms reducedCarry_succ
#print axioms digit_parity_at_odd_position
#print axioms digit_eq_parity_at_odd_position
#print axioms digit_forced_one_of_carry_high
#print axioms digit_forced_zero_of_carry_low
#print axioms carry_lower_of_digit_one
#print axioms carry_upper_of_digit_zero
#print axioms returnIndexWindowClean_of_carry_low
#print axioms not_returnIndexWindowClean_of_support_large
#print axioms nearPeriodicityForcingStatus_nonempty

end Erdos260
