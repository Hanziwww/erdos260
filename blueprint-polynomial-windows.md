# EP260 polynomial-window Lean blueprint

## Scope and immutable inputs

- Upstream baseline: `ba33ea2d16682e5811f15549018795307b97be08`.
- Protected local source: `EP260_v2.tex`; it is not tracked and its SHA-256 is
  `94593A13E7FB568AEAC90969050FE7641F9C3A66C136F5C8DFD02BFF16AA4DB0`.
- Lean/Mathlib toolchain: `v4.32.0`.
- Namespace: `Erdos260.PolynomialWindow`.
- Module chain:
  `Basic -> Polynomial -> Carry -> Windows -> Locking -> {Exterior, Interior} -> Completion`.
- The original dyadic/affine development is retained.  `Erdos260.lean` imports
  both `Erdos260.DeepMind` and the new `PolynomialWindow.Completion` module.

## Public semantics

The public definitions are literal Lean definitions, rather than prose
abbreviations:

```lean
def polyWeightedTerm (b : Nat) (p : Polynomial Rat) (S : Set Nat) (n : Nat) : Real :=
  if n ∈ S then (((p.eval (n : Rat) : Rat) : Real) / (b : Real) ^ n) else 0

def windowCount (S : Set Nat) (N W : Nat) : Nat :=
  ((Finset.Ioc N (N + W)).filter fun n => n ∈ S).card

def lowerDensity (S : Set Nat) : Real :=
  liminf (fun X => (Erdos260.supportCount S X : Real) / X) atTop

def AdmissibleWindow (theta : Real) (N W : Nat) : Prop :=
  0 < N ∧ Real.rpow (N : Real) theta ≤ (W : Real) ∧ W ≤ N

def UniformlyEventually (theta : Real) (P : Nat -> Nat -> Prop) : Prop :=
  ∃ N0, ∀ N W, N0 ≤ N -> AdmissibleWindow theta N W -> P N W
```

## Locked endpoint contracts

The following are repeated as type aliases and assignment examples in
`Erdos260/PolynomialWindow/SkeletonAudit.lean`, so their quantifier order is
checked by Lean rather than only documented here.

```lean
-- The constant c precedes the carry-series numerator, support, and cutoff.
∀ (b Q : Nat), 2 ≤ b -> 0 < Q ->
  ∀ (w : Polynomial Int), w ≠ 0 ->
    0 < w.natDegree -> 0 < w.coeff w.natDegree ->
    ∀ {theta : Real}, 0 < theta -> theta ≤ 1 -> Nat.Coprime b Q ->
      ∃ c : Real, 0 < c ∧ ∀ D : CarrySeries,
        D.base = b -> D.weight = w -> D.denominator = Q ->
        UniformlyEventually theta fun N W =>
          c * W ≤ windowCount D.support N W

∀ (b : Nat), 2 ≤ b ->
  ∀ (p : Polynomial Rat), p ≠ 0 ->
    ∀ (S : Set Nat), S.Infinite ->
      ∀ (eta : Rat), HasSum (polyWeightedTerm b p S) (eta : Real) ->
        ∀ {theta : Real}, 0 < theta -> theta ≤ 1 ->
          ∃ c : Real, 0 < c ∧
            UniformlyEventually theta fun N W =>
              c * W ≤ windowCount S N W

∀ (b : Nat), 2 ≤ b ->
  ∀ (p : Polynomial Rat), p ≠ 0 ->
    ∀ (S : Set Nat), S.Infinite ->
      ∀ (eta : Rat), HasSum (polyWeightedTerm b p S) (eta : Real) ->
        0 < lowerDensity S ∧
        (∃ C x0, ∀ x, x0 ≤ x -> ∀ g, SetSupportGap S x g ->
          g ≤ p.natDegree * Nat.log b x + C) ∧
        (∀ epsilon : Real, 0 < epsilon -> ∃ x0, ∀ x, x0 ≤ x -> ∀ g,
          SetSupportGap S x g -> (g : Real) ≤ Real.rpow (x : Real) epsilon)
```

## Paper-label map (31/31)

`Exact Lean type` names the declaration whose elaborated type is printed by
the corresponding `#check` in `PolynomialWindow/SkeletonAudit.lean`.  The
binder synopsis records all mathematical binders in their Lean order; Lean's
implicit universe and typeclass binders remain visible in that machine audit.
Every `Proved` row has also passed its own `#print axioms` in
`PolynomialWindow/AxiomAudit.lean`; only `propext`, `Classical.choice`, and
`Quot.sound` occur.

### Twelve theorem/proposition labels

| # | TeX label | Exact Lean type and binder order | Formalization note | Status |
|---:|---|---|---|---|
| 1 | `thm:main` | `#check Erdos260.PolynomialWindow.thm_main`; `(b) -> hb -> (p) -> hp -> (S) -> hS -> (eta) -> hsum -> {theta} -> htheta -> hthetaone -> ∃ c, 0 < c ∧ UniformlyEventually theta (fun N W => c*W ≤ windowCount S N W)` | `HasSum` is over `Real`; the window cutoff is explicit inside `UniformlyEventually`. Rational normalization and the finite-prefix bridge are internal. | Proved |
| 2 | `cor:erdos` | `#check Erdos260.PolynomialWindow.cor_erdos`; the same `(b,hb,p,hp,S,hS,eta,hsum)` prefix, followed by `0 < lowerDensity S`, an eventual logarithmic `SetSupportGap` bound, and every-positive-power gap bounds. | Aggregates density and both gap conclusions. Separate irrationality lemmas consume zero lower density or an unbounded enumeration ratio. | Proved |
| 3 | `lem:carries` | `#check Erdos260.PolynomialWindow.CarrySeries.lem_carries`; `(D : CarrySeries) -> recurrence ∧ eventual positivity ∧ polynomial height ∧ ∃ Cgap x0, eventual logarithmic gap bound`. | All four carry facts are bundled; base is arbitrary with `D.base ≥ 2` stored in `CarrySeries`. | Proved |
| 4 | `lem:localscale` | `#check Erdos260.PolynomialWindow.lem_localscale`; `{S} -> (e : SupportEnumeration S) -> {N W m G} -> WindowGeometry e N W m G ->` the window count/gap-scale inequality, forward endpoint bound, and local gap bound. | Paper `O/o` notation is replaced by a finite, explicit `G` contract. | Proved |
| 5 | `lem:windows` | `#check Erdos260.PolynomialWindow.lem_windows`; `{S} -> e -> {N W m G} -> hgeom -> m*W ≤ forwardSpanMass e N W m + m*m*G ∧ ∀ k ∈ windowIndices, forwardSpan e k m ≤ m*G`. | Exact finite window inequality; no asymptotic placeholder. | Proved |
| 11 | `lem:locking` | `#check Erdos260.PolynomialWindow.lem_locking`; `{iota}[Fintype] {d R W B A} -> x -> r -> F -> hx -> hx_interval -> hr -> hFdeg -> hdiv -> hcard -> hlarge -> ∃ G : PolynomialGraph d, G.denominator ≤ W^vandermondeExponent d ∧ ∀ i, eval (x i) G.poly = r i`. | The denominator certificate is data in `PolynomialGraph`; no opaque integer-valued-polynomial object is introduced. | Proved |
| 14 | `lem:dichotomy` | `#check Erdos260.PolynomialWindow.lem_dichotomy`; `{b cap} -> hb -> {gaps} -> hpositive -> hcap -> mu -> hlong -> unique interior continuation ∧ (gaps.span ≤ 4*interiorSpanAlong ... ∨ gaps.span ≤ 4*exteriorSpanAlong ...)`. | Uniqueness and the interior/exterior mass dichotomy are returned together with explicit factor `4`. | Proved |
| 15 | `prop:exterior` | `#check Erdos260.PolynomialWindow.prop_exterior`; `(D) {N W m cap bound} -> hd -> hw -> hgeom -> hpositiveFrom -> pfx -> G -> hfit -> threshold ->` the displayed finite exterior-span census bound using `PreExteriorRecord`, `SelectedExteriorRecord`, the sublevel factor, and `m*cap`. | The paper's exterior error is represented by an explicit finite record count and a quantitative decay term. | Proved |
| 23 | `lem:blocks` | `#check Erdos260.PolynomialWindow.lem_blocks`; `(ell Z) -> (∀ w ∈ retainedBlockWords ell Z, 3*ell ≤ w.span ∧ w.span ≤ 4*ell ∧ w.length ≤ 16*ell/Z) ∧ card ≤ ∑ r ∈ Icc 0 (16*ell/Z), choose (4*ell) r`. | Greedy coverage and its word census are finite combinatorial statements. | Proved |
| 25 | `lem:sampling` | `#check Erdos260.PolynomialWindow.lem_sampling`; `{d U A H K} -> hd -> hU -> f -> hfdeg -> samples -> StrictMono samples -> hsample -> {Y} -> hY -> hval -> {z} -> hz -> P -> hPdeg -> fibre -> StrictMono fibre -> values -> hvalues -> hdiam -> sampling envelope bound ∧ integral-fibre bound`. | Combines the real sampling estimate and rational-integral fibre estimate, with every sample interval explicit. | Proved |
| 27 | `lem:coalescence` | `#check Erdos260.PolynomialWindow.lem_coalescence`; `{d A Hlen b F Q} -> hH -> hb -> G1 -> G2 -> w -> hwdeg -> gaps -> hspan -> samples1 -> samples2 -> both cardinal/interval/value bounds -> hsmall -> G1.poly = G2.poly`. | High-frequency equality follows from proved divisibility plus the explicit sampling smallness inequality. | Proved |
| 29 | `prop:interior` | `#check Erdos260.PolynomialWindow.prop_interior`; `{Source Graph Code}` with decidable equality -> `sources -> graphOf -> codeOf -> endpoint -> {m} -> offset -> span -> blockCap -> endpointCap -> U -> hinjective -> hspan -> hendpoint -> hcoalescence ->` the low-frequency plus high-code census bound for `sum span`. | The generic census accepts a proved injection argument; the concrete source map supplies it through `eq:sourcemap`, rather than storing injectivity as structure data. | Proved |

### Nineteen displayed-formula labels

| # | TeX label | Exact Lean type and binder order | Formalization note | Status |
|---:|---|---|---|---|
| 6 | `eq:short` | `#check Erdos260.PolynomialWindow.eq_short`; `{Window}[DecidableEq] -> windows -> span -> C0 -> L -> m -> W -> {delta} -> hdelta -> hcard -> hm -> sum(short spans) ≤ 2*C0*sqrt(delta)*m*W`. | Generic finite-window form, with every coercion fixed to `Real` by the declaration. | Proved |
| 7 | `eq:prefixspan` | `#check Erdos260.PolynomialWindow.eq_prefixspan`; `word -> bound -> cap -> V -> hcross -> hcap -> hlong -> bound < prefix.span ∧ prefix.span ≤ bound+cap ∧ 3*V ≤ 4*(V-prefix.span)`. | Makes the first-crossing prefix and boundary loss exact in `Nat`. | Proved |
| 8 | `eq:prefixcount` | `#check Erdos260.PolynomialWindow.eq_prefixcount_entropy`; `H -> rMax -> alpha -> hHtwo -> hα0 -> hαhalf -> hratio -> card(boundedPositiveGapWords H rMax) ≤ (H+1)^2 * 2^((H+1)*binaryEntropy alpha)`. | Uses an explicit entropy majorant instead of `N^(epsilon+o(1))`. | Proved |
| 9 | `eq:rare` | `#check Erdos260.PolynomialWindow.eq_rare`; `{Window Prefix}` with decidable equality -> `windows -> prefixOf -> rarePrefixes -> span -> d -> m -> G -> hrare -> hspan -> rare span sum ≤ rarePrefixes.card*(d+1)*(m*G)`. | A reusable finite fibre-counting statement. | Proved |
| 10 | `eq:wordrec` | `#check Erdos260.PolynomialWindow.CarrySeries.eq_wordrec`; `(D) {x gaps} -> D.GapWordAt x gaps -> carry(x+span) + denominator*eval(x+span)(wordCorrection ...) = base^span*carry(x)`. | Exact integer carry unrolling for arbitrary base. | Proved |
| 12 | `eq:graphden` | `#check Erdos260.PolynomialWindow.PolynomialGraph.eq_graphden`; `{d H} -> G -> hden -> 1 ≤ G.denominator ∧ G.denominator ≤ H^vandermondeExponent d ∧ map G.integralPoly = G.denominator • G.poly`. | This is the public denominator certificate of the standard-monomial graph. | Proved |
| 13 | `eq:topmap` | `#check Erdos260.PolynomialWindow.PolynomialGraph.eq_topmap`; `{d} -> G -> b -> Q -> g -> w -> hwdeg -> hA -> normalizedTopState(transform G) = b^g*normalizedTopState G - 1`. | The leading state update is an equality in `Rat`. | Proved |
| 16 | `eq:sublevel` | `#check Erdos260.PolynomialWindow.eq_sublevel`; `{d} -> hd -> f -> hf -> hdeg -> L -> U -> {Y} -> hY -> card(integerSublevelSet f L U Y) ≤ d + 2*d*(Y/abs f.leadingCoeff)^(1/d)`. | Quantitative discrete sublevel bound with explicit constants and `Real.rpow`. | Proved |
| 17 | `eq:denrec` | `#check Erdos260.PolynomialWindow.InteriorNumeratorOrbit.eq_denrec`; `{b q} -> O -> i -> 0 < numerator(i+1) ∧ (b-1)*numerator(i+1) < q ∧ b^(gap i)*numerator i = q+numerator(i+1)`. | Denominator-preserving interior recurrence after removal of the base-primary part. | Proved |
| 18 | `eq:qz` | `#check Erdos260.PolynomialWindow.InteriorNumeratorOrbit.eq_qz`; `{b q} -> O -> gaps≠[] -> b^(span/length) ≤ 2*q ∧ ∀ i, b^(gap i) < 2*q`. | Encodes both mean-gap and pointwise denominator-band consequences. | Proved |
| 19 | `eq:zmin` | `#check Erdos260.PolynomialWindow.eq_zmin`; `{C0 delta L m z Z : Real} -> hdelta -> hL -> hz -> hm -> hspan -> hzBand -> C0/(16*sqrt delta) < Z`. | Pure explicit real inequality used to choose the interior gap band. | Proved |
| 20 | `eq:ellbound` | `#check Erdos260.PolynomialWindow.eq_ellbound`; `{b C Cq D W N L s : Nat} -> hb -> hD -> hW -> hN -> logarithmicBlockScale b C D ≤ Nat.clog b (C*Cq) + s*(L+1)`. | Replaces logarithmic `O(L)` notation by a `Nat.clog` bound. | Proved |
| 21 | `eq:blockspan` | `#check Erdos260.PolynomialWindow.eq_blockspan`; `{ell block} -> GapWord.IsGreedyBlock (3*ell) block -> (∀ g∈block, g≤ell) -> 3*ell ≤ block.span ∧ block.span ≤ 4*ell`. | Exact greedy-block span bounds. | Proved |
| 22 | `eq:cover` | `#check Erdos260.PolynomialWindow.eq_cover`; `{V prefixLoss incompleteLoss filteredLoss retained} -> hdecomp -> 8*prefixLoss≤V -> 8*incompleteLoss≤V -> 4*filteredLoss≤V -> V≤4*retained`. | The retained-mass conclusion records all three losses separately. | Proved |
| 24 | `eq:blockentropy` | `#check Erdos260.PolynomialWindow.eq_blockentropy`; `ell -> Z -> hell -> alpha -> hα0 -> hαhalf -> hratio -> card(retainedBlockWords ell Z) ≤ (4*ell+1)^2 * 2^((4*ell+1)*binaryEntropy alpha)`. | Explicit uniform entropy bound for retained block words. | Proved |
| 26 | `eq:fibre` | `#check Erdos260.PolynomialWindow.eq_fibre`; `{d K H} -> hd -> P -> hdeg -> x -> StrictMono x -> y -> hvalues -> hdiam -> K ≤ d + d*H/leadingDenominatorScale P d`. | The integral-value fibre bound is separated from the sampling conjunction for direct reuse. | Proved |
| 28 | `eq:divisiblegraphs` | `#check Erdos260.PolynomialWindow.eq_divisiblegraphs`; `{d} -> G -> H -> b -> Q -> w -> hwdeg -> gaps -> n -> b^gaps.span ∣ eval n (differenceCertificate(transformWord G, transformWord H)).integralPoly`. | The high-frequency divisibility certificate is a theorem, not a field or axiom. | Proved |
| 30 | `eq:cellcount` | `#check Erdos260.PolynomialWindow.eq_cellcount`; `(Prefix : Type u)[Fintype Prefix] -> m -> bands -> card(InteriorCell Prefix m bands) = card Prefix*m*bands`. | Exact product census for the interior cells. | Proved |
| 31 | `eq:sourcemap` | `#check Erdos260.PolynomialWindow.eq_sourcemap`; `{Block Cell canonicalBlock canonicalCell m} -> endpoint -> Function.Injective endpoint -> Function.Injective (interiorCellSourceMap endpoint)`. | The source-map injection is derived from endpoint injection; it is not assumed in a data structure. | Proved |

## Non-labelled public consequences

- `thm_main_uniform`: denominator-uniform positive-degree kernel with the
  density constant quantified before `CarrySeries`.
- `irrational_of_lowerDensity_eq_zero`: zero lower density contradicts a
  rational value of the polynomial-weighted series.
- `rational_series_enumeration_linear_bound` and
  `irrational_of_enumerationRatioUnbounded`: enumeration-growth form.
- `rational_series_eventual_gap_rpow_bound`: every positive-power eventual
  gap bound.
- Degree zero is handled independently by `degreeZero_window_density`; it is
  not routed through polynomial locking.

## Verification contract

Run one Lean process at a time:

```text
lake build --wfail
lake env lean --trust=0 -j 4 -M 15360 Erdos260/SkeletonAudit.lean
lake env lean --trust=0 -j 4 -M 15360 Erdos260/PolynomialWindow/SpikeAudit.lean
lake env lean --trust=0 -j 4 -M 15360 Erdos260/PolynomialWindow/SkeletonAudit.lean
lake env lean --trust=0 -j 4 -M 15360 Erdos260/PolynomialWindow/AxiomAudit.lean
```

CI additionally rejects `sorry`, `admit`, project-level `axiom`, and
project-level `opaque` declarations; replays every module serially with
Leanchecker; and sends the aggregate environment to Nanoda.  The only allowed
transitive axioms are `propext`, `Classical.choice`, and `Quot.sound`.
