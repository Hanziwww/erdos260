# Erdős Problem 260 — Lean 4 formalization

A Lean 4 / Mathlib formalization of the manuscript

> **Positive dyadic density for rational weighted binary expansions**
> (Han Wang, José María Grau Ribas)

which concerns Erdős Problem 260: whether $\sum_{n\ge1} a_n 2^{-a_n}$ is irrational for every increasing sequence of positive integers with $a_n/n\to\infty$.

This repository is a Lean 4 formalization of that manuscript. It was produced with large-language-model (LLM) assistance and human-checked. The coverage table below maps each section and appendix of the manuscript to the corresponding Lean module(s) and records which components are machine-checked; the library builds, and every wired theorem is `sorry`-free on the standard axioms `[propext, Classical.choice, Quot.sound]`.

## Build

```bash
# Lean toolchain is pinned in lean-toolchain; Mathlib is pinned in lake-manifest.json
lake exe cache get      # fetch Mathlib oleans (optional but recommended)
lake build
```

`Erdos260.lean` is the aggregate root module; `Main.lean` and the `AxiomCheck*.lean` files run `#print axioms` on the wired theorems.

## Coverage map

Section / appendix labels follow the manuscript (sections 1–9, appendices A–AG). The Lean module column lists the relevant file(s).

**Key:** Verified = machine-checked, `sorry`-free · Partially Verified = formalized modulo the manuscript's stated local inputs · Not Verified = not yet formalized / prose only · Tier-3 = proved leaf, not yet wired · Doc = narrative.

| Section / Appendix | Topic | Coverage | Lean module(s) |
|---|---|---|---|
| §1 Introduction | Problem statement, prior methods | Doc | — |
| §2 Preliminaries / notation | Carry, hits, shells; glossary | Verified | Constants, HitSequence, IntegerCarry |
| §3 Main theorem + analytic inputs | Reduction (R1)–(R7) → strict core | Partially Verified | Erdos260V30Endpoint |
| §4 Carry recurrence (§21) | `R_{N+1}=2R_N−Q(N+1)d`, bounds, faithfulness | Verified | CarryRecurrence, CarryRecurrence21, CarryFaithfulIndexing |
| §5 Shell-weighted stopping-time induction | Contradiction engine / accounting | Partially Verified | Erdos260KeystoneCapstone, Erdos260ConvergenceCapstone |
| §6 Return routing at linear order | Return package routing | Partially Verified | Return* providers |
| §7 Fixed-density periodic repetition (§24) | Density floor `1/(4Q)` | Tier-3 | Tier3QHonestKeystone, RhoDQEndpointWiringCore |
| §8 Residual singular-square cleanup (§25) | Dyadic cylinder / small-denominator density | Partially Verified | Lemma251Prop253Cylinder, Lemma252SegmentDensity |
| §9 Positive-density run-area | Run-area estimate | Partially Verified | RunBaseAreaCore, Run* providers |
| App A | Terminal-labelled common-fibre tower transitions | Verified | P1Leaves |
| App B | Correlated nonseparation ladders | Verified | AppendixG_CNLClassifier, AppendixG_Ladder |
| App C | Positive-density recurrence + final theorem | Partially Verified | Erdos260ConvergenceCapstone |
| App D | Charged CNL closure / finite descent | Verified | AppendixI_PackageBounds, HighSupportPhaseCount |
| App E | Branch accounting + CNL estimates | Verified | CNL* (KraftCount, FibreBound, …) |
| App F | DensePack support, dirty crossings, CNL normal form | Partially Verified | Tier2SupplyGeometry, Tier2ClusterFloorDensity |
| App G | Auxiliary package estimates | Verified | AppendixL, AppendixI_PackageBounds |
| App H | Local closure lemmas | Verified | (M.* across providers) |
| App I | Rolling-window variation-drop closure (Return–Run–Tower) | Verified | AppendixN_Closure, _Compression, _Descent |
| App J | Residual-case replacements | Doc | — |
| App K | Top-band, read-tail, exit-share closure | Partially Verified | Tier2SupplyGeometry, Tier2TopBandReadTail |
| App L | DensePack + fixed-pin closure | Partially Verified | Tier2SupplyGeometry, Tier2SpanRarity |
| App M | Fine-fibre complete-lap mass balance | Partially Verified | O1SupplyAtlas, O1MeasurePreservation |
| App N | Denominator-seven routing | Verified | V30PinSeventhsClosure |
| App O | Non-circular (R2)/(R3) extraction | Partially Verified | (v32 dependency firewall) |
| App P | Direct fixed-pin closure + reduced seventh fibre | Partially Verified | O3SupplyStateSpace, O3PeriodicitySupply |
| App Q | Certified seventh pin drops | Verified | V30PinSeventhsClosure |
| App R | Local pin-drop certification | Verified | OrbitPinVoiding |
| App S | Bisection reduction of class-1 atoms | Verified | V30Class1Realization |
| App T | Formal midpoint-priority closure | Verified | V30Class1Realization, O4ClassOneFidelity |
| App U | Faithful class-1 realization | Partially Verified | O4SupplyCarrierMap, O4ClassOneFidelity |
| App V | Exit-mass exposure reduction | Verified | ExitMass* |
| App W | Unsafe-cycle removal | Verified | V30BoundedPeriodRetirement |
| App X | Summed-form consolidation of the V–W off-pin closure | Partially Verified | O2SupplyEmbedding, O2AmbientInjection |
| App Y | The total-support bound | Partially Verified | O2SupplyEmbedding, O2AmbientInjection |
| App Z | Same-carrier fine-fibre cyclic-atlas consequences | Partially Verified | O1SupplyAtlas, HighSupportPhaseCount |
| App AA | Fixed-pin confinement from the slope-fixed carry row | Partially Verified | O3SupplyStateSpace, O3SlopePeriodicFloor |
| App AB | The class-1 realization row partition | Partially Verified | O4SupplyCarrierMap, P1HotspotAudit |
| App AC | Class-1 excess support (corrected accounting) | Partially Verified | O4SupplyCarrierMap, O4ClassOneFidelity |
| App AD | Fine-fibre cyclic-atlas closure (AP1) | Partially Verified | O1SupplyAtlas, P1Leaves |
| App AE | Local closure of the fixed-pin slope row | Partially Verified | O3SupplyStateSpace, O3SlopePeriodicFloor |
| App AF | H.5 class-1 fidelity + corrected accounting (AP3) | Partially Verified | O4ClassOneFidelity, O4SupplyCarrierMap |
| App AG | Assembly of the strict dyadic core | Partially Verified | Erdos260V30Endpoint (assembly) |

## License / citation

If you use this formalization, please cite the accompanying paper. See the repository for license details.
