# Erdős Problem 260 — Lean 4 formalization

A Lean 4 / Mathlib formalization of the manuscript

> **Dyadic density of rational binary expansions**
> (Han Wang, José María Grau Ribas)

which concerns Erdős Problem 260: whether $\sum_{n\ge1} a_n 2^{-a_n}$ is irrational for every increasing sequence of positive integers with $a_n/n\to\infty$.

It was produced with large-language-model (LLM) assistance and human-checked. The library builds, and every wired theorem is `sorry`-free on the standard axioms `[propext, Classical.choice, Quot.sound]`.

## Status in one paragraph

The contradiction architecture of the paper is machine-checked. The conditional endpoint

```
erdos260_of_v30Residual : Erdos260V30Residual → Erdos260Statement
```

builds green and is `sorry`-free on `[propext, Classical.choice, Quot.sound]`, and a machine-checked dependency firewall (`v32_dependency_firewall`) certifies that its residual obligations are mutually non-circular (an acyclic rank certificate, with the forbidden reverse edges refuted by `decide`).

**The only mathematically substantive parts that are not machine-checked are the four local analytic inputs identified in the paper**, namely

1. the complete-lap mass balance (RISK c),
2. the total-support bound (RISK b),
3. the fixed-pin confinement, and
4. the class-one realization,

together with the general-`Q` density-floor calibration. Everything else in the development — the carry recurrence, the shell-weighted stopping-time induction, the clean-CNL entropy estimate, the charged package bounds, the Return–Run–Tower compression, and the wave/ledger/convergence machinery — is machine-checked, and the remaining surface obligations are bookkeeping conditional on the four inputs above. Concretely: a reader who grants those four local statements (which the manuscript proves directly, in the appendices) obtains a fully machine-checked proof of Erdős Problem 260.

The same statement appears at the end of the manuscript: in the paper, the only components verified by hand rather than by Lean are those four local analytic inputs.

## The four analytic inputs (the locus of hand-verification)

| Input | Manuscript result(s) | Lean field |
|---|---|---|
| RISK c — measure preservation around a recurrent cycle | `lem:r-cycle-map-preserves-measure` → `prop:r-exit-share-closed` → `cor:ac-offpin-cap-closed` | `offPin` (`V30MeasurePreservation`) |
| RISK b — ambient / total-support mass bound `M_tot ≤ X·|I_j|` | `lem:ad-summed-ambient-support` | `offPin` (`V30AmbientAccounting`) |
| confinement — deep fixed-pin window-periodicity | `prop:u-fixed-pins-direct` (`lem:u-fixed-pin-periodic-continuation`, `lem:u-periodic-density-floor`) | `confinement` (`FixedPinCleanContinuation`) |
| class-one realization | `lem:aa-failure-exposes-row`, `prop:aa-c2-closed`, `cor:aa-r2-closed` | `class1Realize` |
| general-`Q` density floor `ρ_D = 1/(4Q)` | `prop:tier3-q-calibration` | `RhoDQCalibrationCore` (proved; endpoint wiring) |

The first three columns are exactly the statements proved directly in the manuscript; in the formalization they enter as the named hypotheses of the otherwise machine-checked reduction.

## Build

```bash
# Lean toolchain is pinned in lean-toolchain; Mathlib is pinned in lake-manifest.json
lake exe cache get      # fetch Mathlib oleans (optional but recommended)
lake build
```

`Erdos260.lean` is the aggregate root module and `Main.lean` is the executable entry point. To audit the trusted base, run `#print axioms` on the wired theorems — e.g. `erdos260_of_v30Residual`, `erdos260_of_v32Residual`, and `v32_dependency_firewall` — each of which closes over only the standard axioms `[propext, Classical.choice, Quot.sound]`.

## Coverage map

Section / appendix labels follow the manuscript (sections 1–11, appendices A–AG). The Lean module column lists the relevant file(s).

**Key:** Verified = machine-checked, `sorry`-free · Partially verified = machine-checked modulo the four analytic inputs above · Input = one of the four analytic inputs / the calibration · Doc = narrative.

| Section / Appendix | Topic | Coverage | Lean module(s) |
|---|---|---|---|
| §1–§3 Introduction / Method / Preliminaries | Problem, method, notation | Verified / Doc | Constants, HitSequence, IntegerCarry |
| §4 Main theorem + analytic inputs | Reduction (R1)–(R7) → strict core | Partially verified | Erdos260V30Endpoint |
| §5 Carry recurrence | `R_{N+1}=2R_N−Q(N+1)d`, bounds, faithfulness | Verified | CarryRecurrence, CarryFaithfulIndexing |
| §6 Shell-weighted stopping-time induction | Contradiction engine / accounting | Partially verified | Erdos260KeystoneCapstone, Erdos260ConvergenceCapstone |
| §7 Return routing | Return package routing | Partially verified | Return* providers |
| §8 Fixed-density periodic repetition | Density floor `1/(4Q)` | Input | Tier3QHonestKeystone, RhoDQEndpointWiringCore |
| §9 Residual singular-square cleanup | Dyadic cylinder / small-denominator density | Verified | Lemma251Prop253Cylinder, Lemma252SegmentDensity |
| §10 Positive-density run-area | Run-area estimate | Partially verified | RunBaseAreaCore, Run* providers |
| App A | Terminal-labelled common-fibre tower transitions | Verified | P1Leaves |
| App B | Correlated nonseparation ladders (CNL entropy) | Verified | AppendixG_CNLClassifier, AppendixG_Ladder |
| App C | Positive-density recurrence + final theorem | Partially verified | Erdos260ConvergenceCapstone |
| App D | Charged CNL closure / finite descent | Verified | AppendixI_PackageBounds, HighSupportPhaseCount |
| App E | Branch accounting + CNL estimates | Verified | CNL* (KraftCount, FibreBound, …) |
| App F | DensePack support, dirty crossings, CNL normal form | Verified | Tier2SupplyGeometry, Tier2ClusterFloorDensity |
| App G | Auxiliary package estimates | Verified | AppendixL, AppendixI_PackageBounds |
| App H | Local closure lemmas | Verified | (M.* across providers) |
| App I | Rolling-window variation-drop closure (Return–Run–Tower) | Verified | AppendixN_Closure, _Compression, _Descent |
| App J | Residual-case replacements | Doc | — |
| App K–L | Top-band / read-tail / exit-share; DensePack + fixed-pin | Partially verified | Tier2SupplyGeometry, Tier2SpanRarity |
| App M, Z, AD | Fine-fibre complete-lap mass balance / cyclic atlas | **Input (RISK c)** | O1SupplyAtlas, O1MeasurePreservation |
| App N, Q, R | Denominator-seven routing; certified seventh pin drops | Verified | V30PinSeventhsClosure, OrbitPinVoiding |
| App O | Non-circular (R2)/(R3) extraction | Verified (firewall) | v32_dependency_firewall |
| App P, U, AA, AE | Direct fixed-pin closure / confinement | **Input (confinement)** | O3SupplyStateSpace, O3SlopePeriodicFloor |
| App S, T, V, W | Bisection / midpoint closure; exit-mass exposure; unsafe-cycle removal | Verified | V30Class1Realization, V30CycleMassBalance, V30OffPinExitCap, ExitMass*, V30BoundedPeriodRetirement |
| App X, Y | Summed off-pin closure; total-support bound | **Input (RISK b)** | O2SupplyEmbedding, O2AmbientInjection |
| App AB, AC, AF | Class-one realization / corrected accounting | **Input (class-1)** | O4SupplyCarrierMap, O4ClassOneFidelity, V30StructuralAtoms |
| App AG | Assembly of the strict dyadic core | Partially verified | Erdos260V30Endpoint (assembly) |

## License / citation

If you use this formalization, please cite the accompanying paper. See the repository for license details.
