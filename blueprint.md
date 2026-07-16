# Paper-to-Lean blueprint

## Source and audit policy

The mathematical source is version 2 (forthcoming; upload in progress) of
Wang and Grau Ribas, *Positive dyadic density for rational weighted binary
expansions*.  The permanent public record is
[arXiv:2606.24972](https://arxiv.org/abs/2606.24972).  This repository is
self-contained and does not require a local manuscript checkout.

Every row below is checked by `Erdos260/SkeletonAudit.lean`.  A status of
**Proved** means the declaration has a complete proof and its transitive
`#print axioms` audit contains no proof-placeholder axiom.

The “Lean interface” column is quantifier-faithful but uses the notation from
the source files (`H₂`, `mass`, `ScaleFamily`, and so on) to remain readable;
`#check` in `SkeletonAudit.lean` is the exact machine-readable type audit.

## Recorded fidelity repairs

- `EntropyParams` records both
  `kappa/(Caff+1) ≤ 1/2` and `kappa/(Gamma+1) ≤ 1/2`.  The two strict
  entropy-margin inequalities alone do not imply these domain conditions for
  the real extension of binary entropy: for sufficiently large `kappa` the
  entropy value can be negative, while the composition estimates used in the
  initial- and post-exit-prefix counts require the monotone half interval.
- `lem_sparse_cover` needs the conditions `0 < ell` and
  `∀ g ∈ segment.gaps, g ≤ ell`, both implicit in the manuscript use
  `ell = ceil(log₂(4D))`, `q < 2D`.  Without the first, the valid segment
  `Q=3`, slope `1/3`, gaps `[2]`, `B=3`, `ell=0`, `Z=2`, `forward=0`
  produces no completed block and contradicts the claimed half-cover.  With
  only `ell>0`, a single oversized terminal gap gives the same obstruction
  after the forward-reserve filter.
- A dyadic anchor can equal `2X`, so the uniform support-gap estimate is
  `g ≤ L + Cgap + 1`; the `FirstExitRecord.Valid` endpoint bound records this
  explicit `+1` rather than absorbing it into a support-dependent constant.
- Exterior signatures use the actual first exterior state.  Their record is
  computed from that same pre-exit trajectory and is not an arbitrary valid
  four-tuple.
- The deterministic sparse cover retains the maximal completed-block prefix
  with the required forward reserve and then applies the low-gap filter.  The
  theorem also returns the component bound
  `weight ≤ 32 * ceil ((B+1) * ell)` used by the interior mass sum; nonnegative
  partition weights alone would not imply `thm_strict_mass`.
- Exterior counting now uses a genuine `ExteriorSource` carrying the actual
  anchor, selected occurrence line, first-exit word, post-exit word, and the
  original integer parameter.  Injectivity of its source code is proved from
  the strict support enumeration rather than stored as a structure field.

## Label map (39/39)

| # | Paper label and section | Lean declaration | Lean interface | Formalization difference / fidelity repair | Status |
|---:|---|---|---|---|---|
| 1 | `lem:composition-entropy`, [Appendix A][paper-v2] | `lem_composition_entropy` | `h≥2`, `0<α≤1/2`, `rMax≤αh` imply the exact binomial sum is at most `h²·2^(h H₂(α))` | Counts the exact composition sum rather than introducing an uninterpreted counting object. | **Proved** |
| 2 | `lem:lattice-det`, [Appendix A][paper-v2] | `lem_lattice_det` | Two points of `congruenceLattice A M`, `M≥1`, have determinant `M*k` | This is the lattice determinant part; the coset-area consequence is established by a derived helper. | **Proved** |
| 3 | `lem:farey`, [Appendix A][paper-v2] | `lem_farey` | Distinct `a/b,c/d`, with `1≤b,d<2D`, are separated by `1/(4D²)` | Lean proves the stronger statement without assuming the fractions are already reduced. | **Proved** |
| 4 | `lem:word-cylinder`, [Appendix A][paper-v2] | `lem_word_cylinder` | `slopeAfter w μ₀ ∈ (0,1)` puts `μ₀` in the exact open word cylinder | Uses the computed affine multiplier `wordMultiplier`; no abstract cylinder predicate. | **Proved** |
| 5 | `lem:quant-entropy`, [Appendix A][paper-v2] | `lem_quant_entropy` | For fixed `B>2,c,C>0`, sufficiently large `Z` and `D≥c2^Z` imply the entropy-absorption bound | Restores both sufficiently-large `Z` and the dyadic lower band for `D`. | **Proved** |
| 6 | `prop:carry`, [Section 3][paper-v2] | `prop_carry` | Exact recurrence for `carryInt`, together with lower/upper bounds and strict positivity | `RationalSupport` includes positivity, infinitude, and the actual `HasSum` witness. | **Proved** |
| 7 | `lem:gap`, [Section 3][paper-v2] | `lem_gap` | `∀Q>0, ∃Cgap,x₀`, uniformly for every support with denominator `Q`, every large support gap obeys `g≤log₂x+Cgap` | Constants are chosen after `Q` and before the numerator/support. | **Proved** |
| 8 | `def:mass`, [Section 3][paper-v2] | `mass` | Set `lintegral` of `ENNReal.ofReal weight` for counting × Lebesgue measure | Codomain is `ℝ≥0∞`; real conversion requires a finite-mass certificate. | **Complete definition** |
| 9 | `lem:refinement-principle`, [Section 3][paper-v2] | `lem_refinement_principle` | A measurable event and pair-dependent finite label sets with nonnegative weights summing to one preserve `mass` | Adds the measurability hypothesis required by set-lintegral congruence and permits the label set to vary with the pair. | **Proved** |
| 10 | `lem:window-count`, [Section 4][paper-v2] | `lem_window_count` | For fixed `Q,C>0`, uniform `K,L₀` bound `mX` by total window span plus overlap error whenever `s≤CL` | The constant is uniform over numerator, support, and window system. | **Proved** |
| 11 | `prop:pressure`, [Section 4][paper-v2] | `prop_pressure` | For fixed `Q`, structural and entropy parameters, choose `ε,cLower,δLower,L₀`; every coherent sparse system satisfies the lower bound | Explicitly enforces `s=⌊κL⌋` and fixed cross-scale parameters. | **Proved** |
| 12 | `prop:moderate`, [Section 4][paper-v2] | `prop_moderate` | Bounded-pair real mass is at most `Z₀ c_* mX |I_L|` under the dyadic sparsity bound | Uses a proof-carrying finite mass value; no `∞.toReal=0` shortcut is accepted. | **Proved** |
| 13 | `lem:firstdeep-exists`, [Section 5][paper-v2] | `lem_firstdeep_exists` | In one coherent `ScaleFamily`, a uniform `C_Q` gives eventual span and remaining-span bounds for every large pair | Uses the actual first strict-crossing prefix and fixes all cross-scale data. | **Proved** |
| 14 | `lem:firstdeep-count`, [Section 5][paper-v2] | `lem_firstdeep_count` | One error `→0` gives the eventual initial-prefix census | The estimate is eventual in `L`, as required by the rounding terms. | **Proved** |
| 15 | `prop:low-firstdeep`, [Section 5][paper-v2] | `prop_low_firstdeep` | Rare-prefix mass is little-o of `mX|I_L|` | Prefix selection depends only on the anchor, not the threshold. | **Proved** |
| 16 | `lem:ap-locking`, [Section 5][paper-v2] | `lem_ap_locking` | For fixed `Q`, uniform constants put frequent occurrences on a primitive affine line with controlled step | Occurrence lines use the actual post-prefix point and carry coordinate; both constants are selected after `Q`, and the returned raw direction is primitive. | **Proved** |
| 17 | `lem:strict-unique`, [Section 5][paper-v2] | `lem_strict_unique` | For `μ∈(0,1)`, at most one positive gap keeps `2^g μ-1` in `(0,1)` | Direct real-interval statement. | **Proved** |
| 18 | `lem:step-monotone`, [Section 5][paper-v2] | `lem_step_monotone` | The transformed primitive horizontal step divides the original horizontal parameter | Shared-gap transformation retains the original, possibly nonprimitive, integer parameters. | **Proved** |
| 19 | `lem:boundary-stretch`, [Section 5][paper-v2] | `lem_boundary_stretch` | A genuine boundary transition with `length gaps≤m` and `g≤L+Cgap` has `span≤m+2(L+Cgap)` | Adds the missing step-count hypothesis. The Lean proof establishes the stronger `span≤length+(L+Cgap)`. | **Proved** |
| 20 | `lem:dichotomy`, [Section 5][paper-v2] | `lem_dichotomy` | For sufficiently large cutoff and eventually in `L`, every frequent large pair lies in exactly one actual interior/exterior continuation class | Both branches are tied to the same window suffix and shared-gap trajectory; boundary is not exterior. | **Proved** |
| 21 | `lem:stable-segment`, [Section 6][paper-v2] | `lem_stable_segment` | An anchor-only selector returns a valid odd-denominator segment with span/count/step bounds for each interior pair | Prevents threshold-dependent segment selection. | **Proved** |
| 22 | `lem:primitive-direction`, [Section 6][paper-v2] | `lem_primitive_direction` | Primitive `(H,K)` gives `H=q/gcd(q,Q)`, finiteness of the original parameter set, and its explicit `1+4QX/q` bound | Includes the primitive-direction identity together with the original-parameter count used downstream. | **Proved** |
| 23 | `lem:denominator-span`, [Section 6][paper-v2] | `lem_denominator_span` | For fixed `Q>0`, every nonempty valid segment satisfies `cspan·2^(span/count)≤q` | `Valid` contains positive gaps, exact slope trace, odd fixed denominator, odd numerator, and primitive direction. | **Proved** |
| 24 | `lem:sparse-cover`, [Section 6][paper-v2] | `lem_sparse_cover` | Under the dyadic mean-gap, positive logarithmic scale, per-gap logarithmic bound, and long-span hypotheses, deterministic completed greedy blocks cover the segment, split a nonnegative weight exactly, and bound each component by `32·ceil((B+1)ell)` | Adds the two conditions implicit in the paper's `ell=ceil(log₂(4D))`; without them `ell=0` and a single oversized terminal gap give explicit counterexamples. | **Proved** |
| 25 | `lem:signature-entropy`, [Section 6][paper-v2] | `lem_signature_entropy` | For sufficiently large `Z` and `D≥cBand·2^Z`, encoding candidates are finite and satisfy both the census and absorbed `√D` bounds | Restores the large-band hypotheses and entropy-absorb conclusion. | **Proved** |
| 26 | `lem:word-slope`, [Section 6][paper-v2] | `lem_word_slope` | With `B>2,D>0` and the logarithmic long-span condition, the denominator band and word determine at most one rational slope | The missing long low-gap-block condition rules out the empty-word counterexample. | **Proved** |
| 27 | `lem:line-unique`, [Section 6][paper-v2] | `lem_line_unique` | Eventually, for a fixed denominator context and genuine selected source, each valid encoding determines at most one canonical geometric line | The proof reconstructs the primitive direction and shortest actual forward word, uses dyadic intercept monodromy plus the frequency-scale step bound to force a unique integer intercept, then recovers the canonical source line. | **Proved** |
| 28 | `lem:source-fibre`, [Section 6][paper-v2] | `lem_source_fibre` | Eventually, every genuine encoding fibre is finite and bounded by `Q(Cstep+4)mX/D` | Eliminates the former arbitrary-offset fibre; source data now contain exactly one spatial order factor and no threshold coordinate. | **Proved** |
| 29 | `thm:strict-mass`, [Section 6][paper-v2] | `thm_strict_mass` | One nonnegative function `η_Q(Z₀)→0` controls interior mass for every cutoff and eventually every scale | Returns an actual `InteriorRefinement` carrying valid selection, deterministic blocks, Nodup, candidate encodings, and genuine source certificates. | **Proved** |
| 30 | `lem:off-amplify`, [Section 7][paper-v2] | `lem_off_amplify` | Outside `[0,1]`, a positive gap amplifies distance by at least `2^g` | Exact piecewise distance semantics. | **Proved** |
| 31 | `lem:off-corridor`, [Section 7][paper-v2] | `lem_off_corridor` | For fixed `Q>0`, choose one positive `Ccorr`; every exterior affine line has a finite admissible original-parameter corridor with the displayed distance bound | Keeps raw integer parameters and makes the constant uniform after `Q`; the proof takes the uniform value `Ccorr=5`. | **Proved** |
| 32 | `prop:fixed-off-word`, [Section 7][paper-v2] | `prop_fixed_off_word` | For fixed `Q>0`, choose `Coff(Q)`; every positive post-exit word has a finite parameter set bounded by `1+Coff·X·2^{-span}` | Restores positive gaps and the necessary `Q`-dependence. | **Proved** |
| 33 | `lem:seconddeep`, [Section 7][paper-v2] | `lem_seconddeep` | A fixed `C_Q`, one vanishing census error, and eventual finite/count bounds for actual `(exit record,word)` signatures, plus the span/length bounds | The record is definitionally extracted from the same pre-exit trajectory; its gap bound includes the dyadic endpoint `+1`. | **Proved** |
| 34 | `thm:off-mass`, [Section 7][paper-v2] | `thm_off_mass` | Exterior mass is little-o of `mX|I_L|` | Exterior objects retain the original nonprimitive integer parameterization and use the proved first-exit source injection, signature census, corridor count, and post-exit decay. | **Proved** |
| 35 | `prop:uniform-errors`, [Appendix D][paper-v2] | `prop_uniform_errors` | Boundary loss tends to zero; rare/exterior errors are little-o for every cutoff; one interior bound tends to zero in the cutoff and eventually controls every scale | Combines the completed rare, interior, exterior, and boundary estimates. | **Proved** |
| 36 | `prop:exact-source-decomp`, [Section 8][paper-v2] | `prop_exact_source_decomp` | Exact disjoint parent partition, measurability, total finite mass, and a refinement whose interior mass is counted exactly once | All ENNReal-to-real conversions carry finite-mass certificates; each threshold weight is integrated once. | **Proved** |
| 37 | `prop:upper`, [Section 8][paper-v2] | `prop_upper` | For every `θ>0`, choose `Z₀`; uniformly for `c_*∈[0,1]`, eventual sparsity gives an integrated upper bound with one error `→0` | Uses the completed exact partition, dichotomy, and mass estimates. | **Proved** |
| 38 | `thm:main-density`, [Introduction / Section 1][paper-v2] | `thm_main_density` | `∀Q>0, ∃cDensity(Q)>0`, uniformly for all infinite `S` and all `η` with `η.den=Q` and the required `HasSum`, every large dyadic block has positive density | Constructs a true coherent scale family, normalizes support zero, and applies `prop_upper`. | **Proved** |
| 39 | `cor:erdos260`, [Introduction / Section 1][paper-v2] | `cor_erdos260` | Every positive strictly increasing natural sequence with superlinear growth has irrational weighted binary sum | Uses support reindexing and the completed denominator-uniform `thm_main_density`. | **Proved** |

## DeepMind-compatible endpoint

`deepmindStatement` and `erdos_260` have exactly the following RHS, including
the original `n = 0` denominator and integer exponent semantics:

```lean
∀ a : ℕ → ℤ, ∀ s : ℝ,
  StrictMono a →
  Tendsto (fun n => (a n : ℝ) / n) atTop atTop →
  HasSum (fun n => (a n : ℝ) / 2 ^ a n) s →
  Irrational s
```

The local bridge lemmas for eventual positivity, positive-tail monotonicity and
growth, rationality of the finite integer prefix, support reindexing, and
invariance under adding a rational are all proved.  The proof body of
`erdos_260` is complete and has exactly the displayed RHS.  Its transitive
axiom audit is now free of proof-placeholder axioms.

## Current proof count

All 38 labelled paper results have complete proof bodies,
`def:mass` is complete, and no mathematical proof placeholders remain.  The
full build plus 39/39 declaration/type audit are enforced by continuous
integration.

This public blueprint is the audit boundary between the paper and the Lean
interfaces.  Any future fidelity repair must update the affected row together
with its declaration check in `Erdos260/SkeletonAudit.lean`.

[paper-v2]: https://arxiv.org/abs/2606.24972 "Positive dyadic density for rational weighted binary expansions, v2"
