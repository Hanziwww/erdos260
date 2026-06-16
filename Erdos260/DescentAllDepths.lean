import Erdos260.TailMatchSupply
import Erdos260.DescentDepthClosureCore

/-!
# Descent at all depths: extending the fixed-depth canonical-centre match (the #1 closing move)

This module (NEW; it edits no existing file) attempts the recorded cheapest closing move
(`Erdos260TrajectoryCapstone` / wave-9 `tailMatchSupplyStatus`): extend the in-tree §25.1
fixed-depth canonical-centre match `DescentWindowMatch ctx` (depth `proofV4DensePackSpread + 1`,
centre `(canonicalCenter ctx).q0`, per-start numerators) to **all** depths `n` at the same start,
so that boundedness is automatic (the canonical `q₀` is fixed) and
`tailMatch_of_perDepth_fixedDenominator` finishes through `erdos260_of_dyadicPerDepthMatch`.

## Provenance of the fixed-depth supply (goal 1, the honest map)

`DescentWindowMatch ctx` (`DescentDepthAgreementCore`) is **open data in-tree** — it is nowhere
proved unconditionally.  Its only in-tree provenance:

* `Erdos260MinimalResidualV4.upperBandSource` (a residual/hypothesis FIELD of the V4 capstone
  record; `Erdos260FinalAssembly` lists it as open obligation "D") supplies an
  `UpperBandMatchSource`, whence `UpperBandMatchData.toDescentWindowMatch` /
  `DescentWindowMatch.ofUpperBandData` (`Erdos260UnconditionalSeedClosureV4`,
  `DescentDepthNoLargeRunCore`);
* constructors from strictly more primitive — but equally open — data:
  `DescentWindowMatch.ofPeriodic` (orbit-period window periodicity + one-period agreement),
  `DescentWindowMatch.ofBoundAndCarry` ((D1) singular-square bound + (D2) carry exclusion;
  `hmatch ⟺ (D1) ∧ (D2)` by `matchesCompletion_iff_singularSquareBound_and_carry`), and
  `DescentWindowMatch.ofResidueBand` (the centre-free upper residue-band membership, where (D2)
  is automatic).

So the extension target is **conditional**, and this module builds the conditional extension
honestly, layer by layer.

## What is genuinely PROVED here (no `sorry`/`axiom`/`admit`/`native_decide`)

### Part 1 — the downward direction is free (manuscript §25.1 cylinder refinement, downward)

* `matchesCompletion_restrict_succ` — a depth-`(n+1)` match restricts to depth `n` (one dyadic
  refinement step); with the in-tree `matchesCompletion_mono`, matches restrict to every smaller
  depth.
* `DescentWindowMatch.matches_of_le` — the in-tree fixed-depth match supplies, unconditionally,
  the per-start agreement at EVERY depth `n ≤ proofV4DensePackSpread + 1` with the SAME
  numerators: the entire bounded-range extension is free downward.

### Part 2 — what `tailMatch_of_perDepth_fixedDenominator` actually needs: cofinal suffices

* `matchesCompletion_exists_of_cofinal` — per-depth existence at a COFINAL set of depths
  (`∀ N, ∃ n ≥ N, …`) already gives per-depth existence at ALL depths (downward restriction).
* `tailMatch_of_cofinal_fixedDenominator` — hence the fixed-denominator promotion fires from
  cofinally many depths.  A range bounded by the shell does NOT suffice: the residual gap is
  matches at depths beyond every bound.
* `perScale_numerators_eq_of_deep` — at any depth `n ≥ 2q₀ + 1` the matching numerator is
  UNIQUE (the §25.3 separation): deep per-depth numerators are forced constant, so the extension
  carries no hidden freedom.

### Part 3 — the per-scale match object and the upward step the in-tree (D1)/(D2) data supports

* `PerScaleDescentWindowMatch ctx` — the depth-quantified strengthening of the in-tree
  `DescentWindowMatch` (depth-indexed numerators `a n k`, same fixed canonical centre, same
  starts).  `toDescentWindowMatch` recovers the in-tree object at depth `spread + 1`;
  `ofEmpty` records its vacuity without a genuine start (why the supply Prop demands one).
* The in-tree (D1)/(D2) discharge lemmas are **scale-generic** (their depth is a free
  parameter); only the bundled in-tree DATA is fixed-scale.  Formalized as per-scale
  constructors, each consuming the per-scale form of an existing fixed-depth route:
  `ofResidueBand` (per-scale upper residue band; (D2) automatic), `ofBoundAndCarry`
  (per-scale (D1) + (D2)), `ofPeriodic` (all-length orbit-period window periodicity + ONE
  one-period agreement — the same numerator then works at every depth), `ofExists`
  (choice from per-depth existence).
* `perScaleMatches_exists_iff_beyond` — given the in-tree fixed-depth match, full per-scale
  existence is EXACTLY existence at depths `n > spread + 1`: the residual gap is precisely the
  depths beyond the shell-calibrated range, nothing below it.

### Part 4 — the conditional chain to the endpoint (compose, not re-prove)

* `PerScaleDescentWindowMatch.tailMatch` — per-scale data at one genuine start (positive onset)
  promotes to the canonical-centre `TailMatch` via the in-tree
  `tailMatch_of_perDepth_fixedDenominator`; boundedness is automatic (`q₀` fixed).
* `CanonicalPerScaleSupply` — the named conditional layer: at every deep dyadic context, a
  per-scale match plus a genuine start with the onset budget `k + r ≤ X + 1` and the order
  budget `2·ord_{q₀}(2) ≤ X`.
* `orderBudget_of_periodCalibration` — the order budget is DERIVED from the in-tree-flagged
  period calibration `hpb` (`L + ord ≤ spread + 2`) plus the proved shell fact
  `carryB Q + 25 ≤ L`: so `canonicalPerScaleSupply_of_calibrated` accepts `hpb` in its place.
* `onsetBudget_forces_shell_edge` — the honest pinch: the §25.3 shell placement `X < k + r`
  (carried as `hlo` by the RhoDQ density layer) plus the onset budget force `k + r = X + 1` —
  only the LEFTMOST shell window can carry the deep tail match.
* `deepDyadicPerDepthMatch_of_canonicalPerScaleSupply` → `DeepDyadicPerDepthMatch`;
  `deepDyadicTailMatch_of_canonicalPerScaleSupply` → `DeepDyadicTailMatch`;
  `erdos260_of_canonicalPerScaleSupply` → `Erdos260Statement` (through the in-tree
  `erdos260_of_dyadicPerDepthMatch`; composition only).

### Part 5 — the honest verdict (no free lunch, transported to the new layer)

* `canonicalPerScaleSupply_iff_lever` — `CanonicalPerScaleSupply ↔ DyadicValueLever`: the
  per-scale supply at dyadic contexts (with its budgets) is logically EQUIVALENT to the voiding
  it feeds (forward: this module's chain + `deepDyadicTailMatch_iff_lever`; backward: the lever
  empties the hypothesis class).  The extension is a genuine reduction surface, not a waypoint.

## What resists (goal 4, precise)

The upward step beyond the calibrated depth.  For `n ≤ spread + 1` the extension is free
(downward restriction, Part 1).  For `n > spread + 1` each new depth needs the §25.1 cylinder
reduction AT THE NEXT SCALE: per-scale upper-band membership
`2ⁿ − q₀ < (M_n·q₀) mod 2ⁿ` of the depth-`n` window value (equivalently per-scale (D1) + (D2)).
No in-tree object supplies any depth beyond `spread + 1`: the in-tree singular-square machinery
is scale-generic in its LEMMAS but fixed-scale in its DATA, and the depth calibration `hpb`
(`L + ord ≤ spread + 2`) ties the certified depth to the shell width.  This per-scale band
membership at unboundedly many scales — manuscript §25.1's iterated refinement run at every
dyadic scale within (and beyond) the shell — is the sharpest open atom; at dyadic-value contexts
it is exactly as strong as the voiding (Part 5), confirming there is no cheaper intermediate.

No `sorry`, `admit`, new `axiom`, or `native_decide`.
-/

namespace Erdos260

noncomputable section

/-! ## Part 1.  The downward direction: cylinder refinement restricts matches for free -/

/-- **One dyadic refinement step, downward** (manuscript §25.1: depth-`(n+1)` cylinders refine
depth-`n` cylinders): a match to depth `n + 1` restricts to a match to depth `n`. -/
theorem matchesCompletion_restrict_succ {d : ℕ → ℕ} {s n q0 a : ℕ}
    (h : MatchesCompletion d s (n + 1) q0 a) : MatchesCompletion d s n q0 a :=
  matchesCompletion_mono (Nat.le_succ n) h

/-- **The unconditional bounded-range extension (downward regime).**  The in-tree fixed-depth
match `DescentWindowMatch ctx` supplies, with NO new input, the per-start descent-depth
agreement at EVERY depth `n ≤ proofV4DensePackSpread + 1`, with the SAME per-start numerators
`W.a k`.  This is the §25.1 iterated-refinement downward direction, and it is free. -/
theorem DescentWindowMatch.matches_of_le {ctx : ActualFailureContext}
    (W : DescentWindowMatch ctx) {n : ℕ} (hn : n ≤ proofV4DensePackSpread ctx.shell + 1) :
    ∀ k ∈ genuineDensePackStarts ctx,
      MatchesCompletion ctx.shell.d (k + ctx.n24CarryData.r) n
        (canonicalCenter ctx).q0 (W.a k) :=
  fun k hk => matchesCompletion_mono hn (W.hmatch k hk)

/-! ## Part 2.  What the promotion needs: ALL depths, but cofinal already suffices -/

/-- **Cofinal depths suffice for per-depth existence** (the downward direction closes the gaps):
if matching numerators exist at a cofinal set of depths, they exist at every depth, by
restriction of a deeper witness. -/
theorem matchesCompletion_exists_of_cofinal {d : ℕ → ℕ} {s q0 : ℕ}
    (hex : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ a : ℕ, a < q0 ∧ MatchesCompletion d s n q0 a) :
    ∀ n : ℕ, ∃ a : ℕ, a < q0 ∧ MatchesCompletion d s n q0 a := by
  intro n
  obtain ⟨m, hm, a, ha, hmatch⟩ := hex n
  exact ⟨a, ha, matchesCompletion_mono hm hmatch⟩

/-- **The fixed-denominator promotion fires from cofinally many depths.**
`tailMatch_of_perDepth_fixedDenominator` demands all depths `n : ℕ` unboundedly; by
`matchesCompletion_exists_of_cofinal` a cofinal supply is enough.  A supply on a range BOUNDED
by the shell is NOT enough — the honest residual gap is depths beyond every bound. -/
theorem tailMatch_of_cofinal_fixedDenominator {d : ℕ → ℕ} {x q0 : ℕ} (hq0 : 0 < q0)
    (hex : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ a : ℕ, a < q0 ∧
      MatchesCompletion d (x + 1) n q0 a) :
    ∃ a : ℕ, a < q0 ∧ TailMatch d x q0 a :=
  tailMatch_of_perDepth_fixedDenominator hq0 (matchesCompletion_exists_of_cofinal hex)

/-- **Deep numerators are forced (no hidden freedom in the extension)**: at any depth
`n ≥ 2q₀ + 1` (the separation depth), two matching numerators at one start coincide — the
§25.3 rational-separation kernel pins the centre once the depth clears the denominator scale. -/
theorem perScale_numerators_eq_of_deep {d : ℕ → ℕ} {s q0 a a' n : ℕ} (hq0 : 0 < q0)
    (ha : a < q0) (ha' : a' < q0) (hn : q0 + q0 + 1 ≤ n)
    (hm : MatchesCompletion d s n q0 a) (hm' : MatchesCompletion d s n q0 a') : a = a' := by
  have hsep : 2 * q0 * q0 ≤ 2 ^ (q0 + q0 + 1) :=
    two_mul_mul_le_two_pow (le_refl q0) (le_refl q0)
  have hval : (a : ℝ) / (q0 : ℝ) = (a' : ℝ) / (q0 : ℝ) :=
    descentCentre_unique_of_matches hq0 hq0 ha ha' hsep
      (matchesCompletion_mono hn hm) (matchesCompletion_mono hn hm')
  exact Nat.eq_of_mul_eq_mul_right hq0 (centre_cross_of_div_eq hq0 hq0 hval)

/-! ## Part 3.  The per-scale match object and its constructors -/

/--
**The per-scale descent-window match — the depth-quantified strengthening of the in-tree
`DescentWindowMatch`.**

Identical shape to `DescentWindowMatch ctx` (same fixed canonical centre
`(canonicalCenter ctx).q0`, same starts `k + r` over the genuine DensePack starts), but with the
depth `n` a free parameter and the per-start numerators allowed to vary with it.  Restricting to
`n = proofV4DensePackSpread + 1` recovers the in-tree object (`toDescentWindowMatch`); the
canonical `q₀` being fixed makes the denominator bound across depths automatic, which is exactly
what `tailMatch_of_perDepth_fixedDenominator` needs.
-/
structure PerScaleDescentWindowMatch (ctx : ActualFailureContext) where
  /-- The per-depth, per-start residual-centre numerator. -/
  a : ℕ → ℕ → ℕ
  /-- Each numerator is a genuine residue mod the canonical `q₀`. -/
  ha : ∀ n : ℕ, ∀ k ∈ genuineDensePackStarts ctx, a n k < (canonicalCenter ctx).q0
  /-- The descent-depth agreement at EVERY depth `n`, at the same start `k + r`. -/
  hmatch : ∀ n : ℕ, ∀ k ∈ genuineDensePackStarts ctx,
    MatchesCompletion ctx.shell.d (k + ctx.n24CarryData.r) n
      (canonicalCenter ctx).q0 (a n k)

/-- Per-scale data restricts to the in-tree fixed-depth object (the downward face). -/
def PerScaleDescentWindowMatch.toDescentWindowMatch {ctx : ActualFailureContext}
    (S : PerScaleDescentWindowMatch ctx) : DescentWindowMatch ctx where
  a := S.a (proofV4DensePackSpread ctx.shell + 1)
  ha := S.ha (proofV4DensePackSpread ctx.shell + 1)
  hmatch := S.hmatch (proofV4DensePackSpread ctx.shell + 1)

/-- **Vacuity guard (honesty)**: with no genuine start the per-scale structure is trivially
constructible and carries no content — which is why the supply layer (`CanonicalPerScaleSupply`)
demands an explicit genuine start. -/
def PerScaleDescentWindowMatch.ofEmpty (ctx : ActualFailureContext)
    (h : genuineDensePackStarts ctx = ∅) : PerScaleDescentWindowMatch ctx where
  a := fun _ _ => 0
  ha := fun _ k hk => absurd hk (by simp [h])
  hmatch := fun _ k hk => absurd hk (by simp [h])

/-- Per-scale data from per-depth EXISTENCE (choice packaging of the existence-level form). -/
def PerScaleDescentWindowMatch.ofExists (ctx : ActualFailureContext)
    (h : ∀ n : ℕ, ∀ k ∈ genuineDensePackStarts ctx,
      ∃ a : ℕ, a < (canonicalCenter ctx).q0 ∧
        MatchesCompletion ctx.shell.d (k + ctx.n24CarryData.r) n
          (canonicalCenter ctx).q0 a) :
    PerScaleDescentWindowMatch ctx where
  a := fun n k =>
    if hk : k ∈ genuineDensePackStarts ctx then Classical.choose (h n k hk) else 0
  ha := fun n k hk => by
    simp only [dif_pos hk]
    exact (Classical.choose_spec (h n k hk)).1
  hmatch := fun n k hk => by
    simp only [dif_pos hk]
    exact (Classical.choose_spec (h n k hk)).2

/--
**The per-scale upward step the in-tree (D1) machinery supports: the residue-band route, run at
every scale.**

`DescentDepthClosureCore.matchesCompletion_of_residue_upper` and `residue_upper_witness_lt` are
scale-GENERIC (their depth is a free parameter); only the bundled in-tree datum
(`DescentWindowMatch.ofResidueBand`) pinned the depth to `spread + 1`.  Here the same route is
iterated: per-scale upper residue-band membership of the depth-`n` window values
(`2ⁿ − q₀ < (M_n·q₀) mod 2ⁿ`) yields per-scale matches, with the (D2) carry exclusion AUTOMATIC
at every scale and the numerators DEFINED as the per-scale floor witnesses.  This is the exact
formal shape of the manuscript §25.1 iterated cylinder reduction at the next scale.
-/
def PerScaleDescentWindowMatch.ofResidueBand (ctx : ActualFailureContext)
    (hband : ∀ n : ℕ, ∀ k ∈ genuineDensePackStarts ctx,
      2 ^ n - (canonicalCenter ctx).q0
        < (windowCylinderValue ctx.shell.d (k + ctx.n24CarryData.r) n
            * (canonicalCenter ctx).q0) % 2 ^ n) :
    PerScaleDescentWindowMatch ctx where
  a := fun n k =>
    (windowCylinderValue ctx.shell.d (k + ctx.n24CarryData.r) n
      * (canonicalCenter ctx).q0) / 2 ^ n + 1
  ha := fun n k hk =>
    residue_upper_witness_lt (fun i => by rcases ctx.shell.hd i with h | h <;> omega)
      (canonicalCenter ctx).q0_pos (hband n k hk)
  hmatch := fun n k hk =>
    matchesCompletion_of_residue_upper (fun i => by rcases ctx.shell.hd i with h | h <;> omega)
      (canonicalCenter ctx).q0_pos (hband n k hk)

/-- **The per-scale (D1) + (D2) route**: per-scale singular-square bounds for the actual window
values plus per-scale carry exclusions yield per-scale matches
(`matchesCompletion_of_singularSquareBound` is scale-generic). -/
def PerScaleDescentWindowMatch.ofBoundAndCarry (ctx : ActualFailureContext)
    (a0 : ℕ → ℕ → ℕ)
    (ha0 : ∀ n : ℕ, ∀ k ∈ genuineDensePackStarts ctx, a0 n k < (canonicalCenter ctx).q0)
    (hbound : ∀ n : ℕ, ∀ k ∈ genuineDensePackStarts ctx,
      SingularSquareBound n
        (windowCylinderValue ctx.shell.d (k + ctx.n24CarryData.r) n)
        (canonicalCenter ctx).q0 (a0 n k))
    (hcarry : ∀ n : ℕ, ∀ k ∈ genuineDensePackStarts ctx,
      cylinderIndex n ((a0 n k : ℝ) / ((canonicalCenter ctx).q0 : ℝ)) + 1
        ≠ windowCylinderValue ctx.shell.d (k + ctx.n24CarryData.r) n) :
    PerScaleDescentWindowMatch ctx where
  a := a0
  ha := ha0
  hmatch := fun n k hk =>
    matchesCompletion_of_singularSquareBound
      (fun i => by rcases ctx.shell.hd i with h | h <;> omega)
      (canonicalCenter ctx).q0_pos (hbound n k hk) (hcarry n k hk)

/-- **The per-scale periodic route** (the K.2/M.3 semiperiodic machinery, run at every length):
if the shell window is `PeriodicOn` at the orbit period for EVERY length `n` (full-tail
periodicity) and agrees with the completion on ONE period, the SAME per-start numerator matches
at every depth (`matchesCompletion_of_periodicOn_orbit` is length-generic). -/
def PerScaleDescentWindowMatch.ofPeriodic (ctx : ActualFailureContext)
    (a0 : ℕ → ℕ)
    (ha0 : ∀ k ∈ genuineDensePackStarts ctx, a0 k < (canonicalCenter ctx).q0)
    (hper : ∀ n : ℕ, ∀ k ∈ genuineDensePackStarts ctx,
      PeriodicOn ctx.shell.d (k + ctx.n24CarryData.r) n
        (orderOf (2 : ZMod (canonicalCenter ctx).q0)))
    (hbase : ∀ k ∈ genuineDensePackStarts ctx, ∀ i,
      i < orderOf (2 : ZMod (canonicalCenter ctx).q0) →
        ctx.shell.d (k + ctx.n24CarryData.r + i)
          = dyadicDigit (canonicalCenter ctx).q0 (a0 k) i) :
    PerScaleDescentWindowMatch ctx where
  a := fun _ k => a0 k
  ha := fun _ k hk => ha0 k hk
  hmatch := fun n k hk =>
    matchesCompletion_of_periodicOn_orbit (hper n k hk) (hbase k hk)

/-- **The exact residual gap, given the in-tree fixed-depth match**: full per-scale existence is
equivalent to existence at the depths `n > proofV4DensePackSpread + 1` ALONE — everything at or
below the calibrated depth is free downward (Part 1).  The upward step beyond the shell-paid
range is the entire content. -/
theorem perScaleMatches_exists_iff_beyond (ctx : ActualFailureContext)
    (W : DescentWindowMatch ctx) :
    (∀ n : ℕ, ∀ k ∈ genuineDensePackStarts ctx,
        ∃ a : ℕ, a < (canonicalCenter ctx).q0 ∧
          MatchesCompletion ctx.shell.d (k + ctx.n24CarryData.r) n
            (canonicalCenter ctx).q0 a)
      ↔ (∀ n : ℕ, proofV4DensePackSpread ctx.shell + 1 < n →
          ∀ k ∈ genuineDensePackStarts ctx,
            ∃ a : ℕ, a < (canonicalCenter ctx).q0 ∧
              MatchesCompletion ctx.shell.d (k + ctx.n24CarryData.r) n
                (canonicalCenter ctx).q0 a) := by
  constructor
  · intro h n _ k hk
    exact h n k hk
  · intro h n k hk
    rcases Nat.lt_or_ge (proofV4DensePackSpread ctx.shell + 1) n with hn | hn
    · exact h n hn k hk
    · exact ⟨W.a k, W.ha k hk, matchesCompletion_mono hn (W.hmatch k hk)⟩

/-! ## Part 4.  The conditional chain to the endpoint -/

/-- **The promotion at a genuine start**: per-scale data plus one genuine start with a positive
onset yields the canonical-centre `TailMatch` at that start — boundedness across depths is
automatic because the canonical `q₀` is fixed, exactly as the wave-9 status predicted, via the
in-tree `tailMatch_of_perDepth_fixedDenominator`. -/
theorem PerScaleDescentWindowMatch.tailMatch {ctx : ActualFailureContext}
    (S : PerScaleDescentWindowMatch ctx) {k : ℕ}
    (hk : k ∈ genuineDensePackStarts ctx) (hpos : 0 < k + ctx.n24CarryData.r) :
    ∃ a : ℕ, a < (canonicalCenter ctx).q0 ∧
      TailMatch ctx.shell.d (k + ctx.n24CarryData.r - 1) (canonicalCenter ctx).q0 a := by
  have hx1 : k + ctx.n24CarryData.r - 1 + 1 = k + ctx.n24CarryData.r := by omega
  refine tailMatch_of_perDepth_fixedDenominator (canonicalCenter ctx).q0_pos ?_
  intro n
  rw [hx1]
  exact ⟨S.a n k, S.ha n k hk, S.hmatch n k hk⟩

/--
**The named conditional supply layer** (the sharpest successor surface of this wave): at every
deep dyadic-value context, a per-scale canonical-centre match together with one genuine DensePack
start carrying the two budgets the deep tail-match props demand — the onset budget
`k + r ≤ X + 1` (so the onset `x = k + r − 1 ≤ X`) and the order budget `2·ord_{q₀}(2) ≤ X`.
The order budget is dischargeable from the in-tree-flagged period calibration
(`canonicalPerScaleSupply_of_calibrated`).
-/
def CanonicalPerScaleSupply : Prop :=
  ∀ ctx : ActualFailureContext, 2 ^ 493443 < ctx.X → ShellValueDyadic ctx →
    ∃ _S : PerScaleDescentWindowMatch ctx, ∃ k ∈ genuineDensePackStarts ctx,
      0 < k + ctx.n24CarryData.r ∧ k + ctx.n24CarryData.r ≤ ctx.X + 1 ∧
      2 * orderOf (2 : ZMod (canonicalCenter ctx).q0) ≤ ctx.X

/-- **The onset pinch (honest calibration fact)**: the §25.3 shell placement `X < k + r` (the
`hlo` hypothesis the RhoDQ density layer carries for genuine starts) combined with the onset
budget `k + r ≤ X + 1` forces `k + r = X + 1` — only the LEFTMOST shell window is compatible
with the deep tail-match onset budget. -/
theorem onsetBudget_forces_shell_edge {X s : ℕ} (hlo : X < s) (hbudget : s ≤ X + 1) :
    s = X + 1 := by omega

/-- **The order budget from the in-tree period calibration.**  The separately-flagged `hpb`
calibration `L + ord_{q₀}(2) ≤ spread + 2` (with `spread = L + carryB Q + 1`) gives
`ord ≤ carryB Q + 3`; the proved shell fact `carryB Q + 25 ≤ L` and `X = 2^L` then dominate:
`2·ord ≤ 2·carryB Q + 6 ≤ 2^(carryB Q + 25) ≤ 2^L = X`. -/
theorem orderBudget_of_periodCalibration (ctx : ActualFailureContext)
    (hpb : Classical.choose ctx.shell.hXdyadic
        + orderOf (2 : ZMod (canonicalCenter ctx).q0)
      ≤ proofV4DensePackSpread ctx.shell + 2) :
    2 * orderOf (2 : ZMod (canonicalCenter ctx).q0) ≤ ctx.X := by
  have hspread : proofV4DensePackSpread ctx.shell
      = Classical.choose ctx.shell.hXdyadic + carryB ctx.shell.Q + 1 := rfl
  rw [hspread] at hpb
  have hord : orderOf (2 : ZMod (canonicalCenter ctx).q0) ≤ carryB ctx.shell.Q + 3 := by
    omega
  have hcl : carryB ctx.shell.Q + 25 ≤ Classical.choose ctx.shell.hXdyadic :=
    ctx.shell_carryLarge
  have h2c : carryB ctx.shell.Q < 2 ^ carryB ctx.shell.Q := Nat.lt_two_pow_self
  have h1c : 1 ≤ 2 ^ carryB ctx.shell.Q := Nat.one_le_two_pow
  have h8 : (8 : ℕ) ≤ 2 ^ 25 := by norm_num
  calc 2 * orderOf (2 : ZMod (canonicalCenter ctx).q0)
      ≤ 2 * (carryB ctx.shell.Q + 3) := by omega
    _ ≤ 8 * 2 ^ carryB ctx.shell.Q := by omega
    _ = 2 ^ carryB ctx.shell.Q * 8 := Nat.mul_comm _ _
    _ ≤ 2 ^ carryB ctx.shell.Q * 2 ^ 25 := Nat.mul_le_mul (le_refl _) h8
    _ = 2 ^ (carryB ctx.shell.Q + 25) := (pow_add 2 (carryB ctx.shell.Q) 25).symm
    _ ≤ 2 ^ Classical.choose ctx.shell.hXdyadic :=
        Nat.pow_le_pow_right (by norm_num) hcl
    _ = ctx.X := (Classical.choose_spec ctx.shell.hXdyadic).symm.trans ctx.shell_X

/-- The supply layer accepts the in-tree-flagged period calibration `hpb` in place of the raw
order budget. -/
theorem canonicalPerScaleSupply_of_calibrated
    (h : ∀ ctx : ActualFailureContext, 2 ^ 493443 < ctx.X → ShellValueDyadic ctx →
      ∃ _S : PerScaleDescentWindowMatch ctx, ∃ k ∈ genuineDensePackStarts ctx,
        0 < k + ctx.n24CarryData.r ∧ k + ctx.n24CarryData.r ≤ ctx.X + 1 ∧
        Classical.choose ctx.shell.hXdyadic
            + orderOf (2 : ZMod (canonicalCenter ctx).q0)
          ≤ proofV4DensePackSpread ctx.shell + 2) :
    CanonicalPerScaleSupply := by
  intro ctx hX hdy
  obtain ⟨S, k, hk, hpos, hbound, hpb⟩ := h ctx hX hdy
  exact ⟨S, k, hk, hpos, hbound, orderBudget_of_periodCalibration ctx hpb⟩

/-- **The chain fires**: the per-scale supply delivers the wave-9 sharpened successor
`DeepDyadicPerDepthMatch` — fixed canonical denominator (its own bound `B := q₀`), per-depth
numerators from the per-scale data, budgets from the supply layer. -/
theorem deepDyadicPerDepthMatch_of_canonicalPerScaleSupply
    (h : CanonicalPerScaleSupply) : DeepDyadicPerDepthMatch := by
  intro ctx hX hdy
  obtain ⟨S, k, hk, hpos, hbound, hord⟩ := h ctx hX hdy
  refine ⟨k + ctx.n24CarryData.r - 1, (canonicalCenter ctx).q0, by omega, fun n => ?_⟩
  have hx1 : k + ctx.n24CarryData.r - 1 + 1 = k + ctx.n24CarryData.r := by omega
  refine ⟨(canonicalCenter ctx).q0, S.a n k,
    ⟨(canonicalCenter ctx).q0_gt_one, (canonicalCenter ctx).q0_odd, le_refl _,
      S.ha n k hk, hord⟩, ?_⟩
  have hd_eq : ctx.shell.d = ctx.d := rfl
  rw [hx1, ← hd_eq]
  exact S.hmatch n k hk

/-- The per-scale supply delivers the full deep dyadic tail match (composition with the in-tree
promotion `deepDyadicTailMatch_of_perDepthMatch`). -/
theorem deepDyadicTailMatch_of_canonicalPerScaleSupply
    (h : CanonicalPerScaleSupply) : DeepDyadicTailMatch :=
  deepDyadicTailMatch_of_perDepthMatch (deepDyadicPerDepthMatch_of_canonicalPerScaleSupply h)

/-- **The endpoint** (composition only, through the in-tree `erdos260_of_dyadicPerDepthMatch`):
`Erdos260Statement` from the per-scale supply plus the lever-shrunk wave-5 surfaces. -/
theorem erdos260_of_canonicalPerScaleSupply (h : CanonicalPerScaleSupply)
    (surfaces : DyadicValueLever → Erdos260DyadicLeverResidual) : Erdos260Statement :=
  erdos260_of_dyadicPerDepthMatch (deepDyadicPerDepthMatch_of_canonicalPerScaleSupply h)
    surfaces

/-! ## Part 5.  The honest verdict: no free lunch at the new layer either -/

/-- **No free lunch, per-scale form**: the per-scale supply (with its budgets) is logically
EQUIVALENT to the dyadic-value lever it feeds.  Forward: this module's chain plus the in-tree
`deepDyadicTailMatch_iff_lever`.  Backward: the lever empties the hypothesis class.  So
`CanonicalPerScaleSupply` is a genuine reduction surface — supplying it at dyadic contexts IS
the voiding, with no intermediate waypoint. -/
theorem canonicalPerScaleSupply_iff_lever :
    CanonicalPerScaleSupply ↔ DyadicValueLever := by
  constructor
  · intro h
    exact deepDyadicTailMatch_iff_lever.mp (deepDyadicTailMatch_of_canonicalPerScaleSupply h)
  · intro hlever ctx _ hdy
    exact absurd hdy (hlever ctx)

/-! ## Part 6.  Machine-readable status (honest) -/

/-- Honest machine-readable status of the all-depths descent extension. -/
def descentAllDepthsStatus : List String :=
  [ "PROVENANCE (goal 1) - DescentWindowMatch ctx is OPEN DATA in-tree: it is proved " ++
      "unconditionally NOWHERE. Supply routes: (i) Erdos260MinimalResidualV4.upperBandSource " ++
      "(a residual/hypothesis FIELD; Erdos260FinalAssembly lists it as open obligation 'D " ++
      "Sec 25.3 descent') -> UpperBandMatchSource.toUpperBandMatchData -> DescentWindowMatch." ++
      "ofUpperBandData; (ii) constructors from equally-open primitives: ofPeriodic (orbit-" ++
      "period window periodicity + one-period agreement), ofBoundAndCarry (hmatch <-> (D1) " ++
      "singular-square bound AND (D2) carry exclusion, via matchesCompletion_iff_singular" ++
      "SquareBound_and_carry), ofResidueBand (centre-free upper residue band, (D2) automatic). " ++
      "Consumers: DescentDepthClosureCore (D1/D2 routing), DescentDepthNoLargeRunCore, the " ++
      "RhoDQ density layer, Erdos260UnconditionalSeedClosureV4. The extension target is " ++
      "therefore CONDITIONAL, and this module builds the conditional extension.",
    "DOWNWARD REGIME (goal 2, PROVED unconditional) - matchesCompletion_restrict_succ (one " ++
      "dyadic refinement step) + the in-tree matchesCompletion_mono; DescentWindowMatch." ++
      "matches_of_le: the fixed-depth match supplies the per-start agreement at EVERY depth " ++
      "n <= proofV4DensePackSpread+1 with the SAME numerators, free. The manuscript 25.1 " ++
      "refinement (depth n+1 cylinders refine depth n) is the downward direction and costs " ++
      "nothing.",
    "COFINAL SUFFICES (goal 2, PROVED) - tailMatch_of_perDepth_fixedDenominator literally " ++
      "demands ALL n : Nat; matchesCompletion_exists_of_cofinal shows a COFINAL supply " ++
      "(for every N some matched depth n >= N) already closes all gaps by downward " ++
      "restriction, so tailMatch_of_cofinal_fixedDenominator fires from cofinally many " ++
      "depths. A range bounded by the shell does NOT suffice: the residual gap is depths " ++
      "beyond every bound. perScale_numerators_eq_of_deep: at depth >= 2q0+1 the matching " ++
      "numerator is UNIQUE (s25.3 separation), so the extension hides no freedom.",
    "PER-SCALE OBJECT (goal 3i/3ii) - PerScaleDescentWindowMatch ctx: the depth-quantified " ++
      "strengthening of DescentWindowMatch (depth-indexed numerators, fixed canonical " ++
      "centre, same starts). toDescentWindowMatch recovers the in-tree object at depth " ++
      "spread+1; ofEmpty records vacuity without a genuine start. The in-tree (D1)/(D2) " ++
      "discharge LEMMAS are scale-generic (depth a free parameter) - only the bundled DATA " ++
      "was fixed-scale - so the per-scale constructors exist: ofResidueBand (per-scale " ++
      "upper-band membership 2^n - q0 < (M_n q0) mod 2^n, (D2) automatic at every scale, " ++
      "numerators = floor witnesses), ofBoundAndCarry (per-scale (D1)+(D2)), ofPeriodic " ++
      "(all-length orbit-period periodicity + ONE one-period agreement: same numerator at " ++
      "every depth), ofExists (choice packaging). perScaleMatches_exists_iff_beyond: given " ++
      "the fixed-depth match, full per-scale existence IS existence at depths n > spread+1 " ++
      "alone - the precise residual gap.",
    "CONDITIONAL CHAIN (goal 3ii, PROVED, compose-only) - PerScaleDescentWindowMatch." ++
      "tailMatch: per-scale data + one genuine start (positive onset) -> canonical-centre " ++
      "TailMatch via tailMatch_of_perDepth_fixedDenominator (boundedness automatic, q0 " ++
      "fixed). CanonicalPerScaleSupply (the named layer: per-scale match + genuine start + " ++
      "onset budget k+r <= X+1 + order budget 2 ord <= X) -> deepDyadicPerDepthMatch_of_" ++
      "canonicalPerScaleSupply -> DeepDyadicPerDepthMatch -> deepDyadicTailMatch_of_" ++
      "canonicalPerScaleSupply -> DeepDyadicTailMatch -> erdos260_of_canonicalPerScale" ++
      "Supply -> Erdos260Statement (through the in-tree erdos260_of_dyadicPerDepthMatch).",
    "BUDGETS (goal 3iii, the honest tower bookkeeping) - orderBudget_of_periodCalibration: " ++
      "the order budget 2 ord_{q0}(2) <= X is DERIVED from the in-tree-flagged period " ++
      "calibration hpb (L + ord <= spread+2, spread = L + carryB Q + 1) plus the proved " ++
      "shell fact carryB Q + 25 <= L and X = 2^L; canonicalPerScaleSupply_of_calibrated " ++
      "accepts hpb in place of the raw budget. onsetBudget_forces_shell_edge: the s25.3 " ++
      "shell placement X < k+r (the RhoDQ hlo) plus the onset budget k+r <= X+1 force " ++
      "k+r = X+1 - ONLY the leftmost shell window can carry the deep tail match; the " ++
      "onset budget is a genuine selection constraint, not bookkeeping.",
    "FULL CONDITIONAL TOWER (goal 3iii, each layer named) - L0 (open in-tree residual, " ++
      "fixed depth): upperBandSource / DescentWindowMatch.{ofUpperBandData, ofPeriodic, " ++
      "ofBoundAndCarry, ofResidueBand}. L1 (this module, per-scale): PerScaleDescentWindow" ++
      "Match.{ofResidueBand, ofBoundAndCarry, ofPeriodic, ofExists} - conditional on the " ++
      "per-scale form of the same (D1)/(D2)/periodicity data. L2 (supply + budgets): " ++
      "CanonicalPerScaleSupply (or _of_calibrated with the flagged hpb). L3 (endpoint, " ++
      "compose-only): DeepDyadicPerDepthMatch -> DeepDyadicTailMatch -> Erdos260Statement.",
    "VERDICT (goal 4, no free lunch transported) - canonicalPerScaleSupply_iff_lever: " ++
      "CanonicalPerScaleSupply <-> DyadicValueLever. The per-scale supply at dyadic " ++
      "contexts (with its budgets) is logically EQUIVALENT to the voiding it feeds " ++
      "(forward: this module's chain + deepDyadicTailMatch_iff_lever; backward: the lever " ++
      "empties the hypothesis class). The extension is a genuine reduction surface, not a " ++
      "waypoint.",
    "WHAT RESISTS (goal 4, the sharpest open atom) - the upward step BEYOND the calibrated " ++
      "depth. For n <= spread+1 the extension is free (downward). For each n > spread+1 " ++
      "the s25.1 cylinder reduction must run AT THE NEXT SCALE: per-scale upper-band " ++
      "membership 2^n - q0 < (M_n q0) mod 2^n of the depth-n window value (equivalently " ++
      "per-scale (D1)+(D2)). NO in-tree object supplies ANY depth beyond spread+1: the " ++
      "singular-square machinery is scale-generic in its lemmas but fixed-scale in its " ++
      "data, and the depth calibration hpb ties the certified depth to the shell width " ++
      "(L + ord <= spread+2). The manuscript's iterated 25.1/25.3 descent - the same " ++
      "argument at each dyadic scale, with the carry envelope |R_N| <= Q(N+2) " ++
      "(integerCarry_abs_le) converted to the per-window CONSTANT bound < q0 at every " ++
      "scale - is the irreducible analytic input; formal target: the hband argument of " ++
      "PerScaleDescentWindowMatch.ofResidueBand at unboundedly many (equivalently " ++
      "cofinally many) scales, at one genuine start with k+r = X+1.",
    "HYGIENE - additive only (no existing file edited); no sorry / admit / new axiom / " ++
      "native_decide; all #print axioms in [propext, Classical.choice, Quot.sound]." ]

theorem descentAllDepthsStatus_nonempty : descentAllDepthsStatus ≠ [] := by
  simp [descentAllDepthsStatus]

/-! ## Part 7.  Axiom-cleanliness audit
Every key declaration; expected axioms `[propext, Classical.choice, Quot.sound]` or fewer. -/

#print axioms matchesCompletion_restrict_succ
#print axioms DescentWindowMatch.matches_of_le
#print axioms matchesCompletion_exists_of_cofinal
#print axioms tailMatch_of_cofinal_fixedDenominator
#print axioms perScale_numerators_eq_of_deep
#print axioms PerScaleDescentWindowMatch.toDescentWindowMatch
#print axioms PerScaleDescentWindowMatch.ofEmpty
#print axioms PerScaleDescentWindowMatch.ofExists
#print axioms PerScaleDescentWindowMatch.ofResidueBand
#print axioms PerScaleDescentWindowMatch.ofBoundAndCarry
#print axioms PerScaleDescentWindowMatch.ofPeriodic
#print axioms perScaleMatches_exists_iff_beyond
#print axioms PerScaleDescentWindowMatch.tailMatch
#print axioms onsetBudget_forces_shell_edge
#print axioms orderBudget_of_periodCalibration
#print axioms canonicalPerScaleSupply_of_calibrated
#print axioms deepDyadicPerDepthMatch_of_canonicalPerScaleSupply
#print axioms deepDyadicTailMatch_of_canonicalPerScaleSupply
#print axioms erdos260_of_canonicalPerScaleSupply
#print axioms canonicalPerScaleSupply_iff_lever
#print axioms descentAllDepthsStatus_nonempty

end

end Erdos260
