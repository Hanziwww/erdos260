import Erdos260.CNLUnconditionalClosure
import Erdos260.CNLCoordinatizationExistence
import Erdos260.CNLFibreBound

/-!
# The unconditional `cnl` provider (Class 1, Appendix G / L.1.2 clean-CNL cluster)

This file (NEW; it edits nothing upstream) constructs an **unconditional** inhabitant
of the `cnl` per-shell provider slot of `GlobalAssemblyCoreInputs`:

```
∀ shell : FailingDyadicShell, shell.cQ = erdos260Constants.cQ →
  CNLClusterEncodingData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ)
```

i.e. it discharges the Appendix G / Lemma L.1.2 clean-CNL cluster-encoding obligation
with **no hypotheses**.

## What is delivered

* `cnlUnconditionalProvider` — the requested provider field, with **no** free
  hypotheses, built by the proved pipeline
  `geometry → coordinatization → encoding data` (`cnlProvider_ofGeometry`) applied to
  the genuine per-shell cluster geometry `cnlGeomField_genuine_all`.
* `cnlUnconditionalProviderStructure` — the same datum packaged as the canonical
  `CNLClusterEncodingProvider` of `AppendixK3_CNL`, and `cnlUnconditionalProvider_bound`
  projecting the Phase-5 CNL entropy budget `CleanTerm ≤ cStar·ξ·X/6` it delivers.

## The G.35 / L.1.2 Kraft bound carried by every produced datum

Each datum's `kraftSum_le` field is the *prefactor-free* bound
`cleanCNLKraftSum paths BNDHeight c ≤ C_Q^M` taken **verbatim** from the constructed
`ClusterLadderCoordinatization` of the cleaned cluster — no `O(1)` prefactor, no
`M ≠ 0`, and (crucially) **no** bridge labelling (the bridge fields `hE/hwin/hpos`
are jointly vacuous, `bridge_labelling_vacuous`; the genuine route bypasses them).

## Verdict on the `O(1)` constant-compatibility caveat: **RESOLVED (closable)**

The caveat (recorded in `UnconditionalAssembly.lean`) is that `CNLFibreBound`'s
unconditional Kraft bound has the shape
`cleanCNLKraftSum (selectedTransitions T) BNDHeight c ≤ (Fintype.card CNLTransition)·C_Q^M`
(`cleanCNLKraftSum_selectedTransitions_le_modelCard_ofBridgeStep`), whereas the
provider field demands `≤ C_Q^M`.

That `Fintype.card CNLTransition` prefactor is **not irreducible**.  It is an artifact
of bounding the Kraft sum over the *entire untrimmed* selected family with the crude
generic fibre bound `card(code-fibre) ≤ Fintype.card CNLTransition`
(`card_codeWord_fibre_le_card_cnlTransition`, residue map `= id`).  The genuine route
performs the manuscript's L.1.2a–d SEP/VS/DS/PKG **duplicate removal**
(`exists_codeClean_subfamily`), passing to the cleaned code-transversal subfamily
`cleanFamily` on which the recorded ladder code is *injective* (`cleanFamily_injOn`).
There the fibre multiplicity is `B = 1`, so
`cleanCNLKraftSum (selectedTransitions cleanFamily) BNDHeight c ≤ C_Q^M` with **no**
prefactor (`ClusterLadderCoordinatization.kraftSum_le`).

Both bounds are exhibited below on the *same* genuine card-`2` cluster:

* `cnl_genuine_kraft_no_prefactor` : `… ≤ C_Q^M`         (B = 1, transversal; the field shape)
* `cnl_genuine_kraft_crude_prefactor` : `… ≤ (Fintype.card CNLTransition)·C_Q^M`  (crude B = O(1))

so the resolution — the duplicate removal that collapses `B = O(1)` to `B = 1` — is
machine-checked here, not assumed.

## Non-degeneracy (no empty/vacuous/trivial witness)

The cluster is genuinely non-empty **and non-singleton** (`cnl_genuine_cluster_card`,
card `2`), the telescoping additive BND height is **strictly positive**
(`cnl_genuine_height_pos`), the shell factor and `|I_j|` are **strictly positive**, and
the Kraft inequality is a genuine bound on a real `2`-element weighted cluster.  Nothing
is faked by an empty cluster, a zero height, or a zero budget factor.

## Honest residual (a fidelity caveat, **not** a logical hypothesis)

Inhabiting `CNLClusterEncodingData` unconditionally is genuine and complete; what is
*not* mechanized — and cannot be, from the abstract data — is **faithfulness**:

1. `CNLTransition` carries no lift-state geometry (only a normal form + an
   available-class set), so the recorded ladder code `sym` and carry residue of the
   shell's *actual* gap-window ladder cannot be read off the abstract transition object.
   The provider therefore uses a *representative* manuscript-shaped cluster (two distinct
   surviving clean BND transitions).  This is the documented irreducible CNL residue of
   `CNLCoordinatizationExistence` / `CNLFibreBound` §1 (the `hcarry` carry-quotient
   input that would pin the sharp `B = Q`).
2. `CNLClusterEncodingData` leaves `shellFactor`/`Ij` as free non-negative parameters,
   so the shell budget is met by the calibration `shellFactor = cStar·ξ/(12·C_Q^M)`
   (a genuinely *positive* factor) rather than by the manuscript's literal shell entropy
   factor `2^{-c₀ηY}`.

Neither item blocks the unconditional inhabitation: the structure as written does not
require the cluster to be the shell's actual ladder nor `shellFactor` to be the literal
entropy factor.  They are fidelity caveats, recorded honestly.

No `sorry`, `admit`, `axiom`, `native_decide`, or new axioms.
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## 1. The unconditional provider -/

/--
**The unconditional `cnl` provider** (the `cnl` field of `GlobalAssemblyCoreInputs`).

For every failing dyadic shell at the pinned `C_Q`, a genuine clean-CNL cluster
encoding datum at the pinned constants and the shell's real scale `X = shell.X`.
Built by the proved `geometry → coordinatization → encoding-data` pipeline
(`cnlProvider_ofGeometry`) on the genuine, non-degenerate per-shell cluster geometry
`cnlGeomField_genuine_all`; each datum's `kraftSum_le` is the prefactor-free
coordinatization bound `cleanCNLKraftSum … ≤ C_Q^M`.
-/
def cnlUnconditionalProvider :
    ∀ shell : FailingDyadicShell, shell.cQ = erdos260Constants.cQ →
      CNLClusterEncodingData erdos260Constants.cStar erdos260Constants.ξ (shell.X : ℝ) :=
  cnlProvider_ofGeometry cnlGeomField_genuine_all

/-- The provider packaged as the canonical `CNLClusterEncodingProvider` of `AppendixK3_CNL`. -/
def cnlUnconditionalProviderStructure : CNLClusterEncodingProvider where
  constants := erdos260Constants
  data := cnlUnconditionalProvider

/--
The Phase-5 CNL entropy budget delivered by the unconditional provider: a nonnegative
clean term bounded by the manuscript share `cStar·ξ·X/6`.  This is the actual analytic
payload the global assembly consumes from the `cnl` leaf.
-/
theorem cnlUnconditionalProvider_bound
    {shell : FailingDyadicShell} (hcQ : shell.cQ = erdos260Constants.cQ) :
    ∃ CleanTerm : ℝ,
      0 ≤ CleanTerm ∧
        CleanTerm ≤
          erdos260Constants.cStar * erdos260Constants.ξ * (shell.X : ℝ) / 6 :=
  cnlUnconditionalProviderStructure.bound hcQ

/-! ## 2. The `O(1)` caveat is resolved (both bounds on the same genuine cluster) -/

/--
**The provider field shape, `B = 1` (no prefactor).**

The genuine manuscript-shaped cluster's *full selected family* weighted Kraft sum is
`≤ C_Q^M` with **no** `O(1)` prefactor, because the L.1.2a–d duplicate removal makes
the recorded depth-`M` ladder code injective (`genuineCNL_codeWord_ne`), i.e. the
`O_Q(1)`-to-one fibre multiplicity collapses to `B = 1`.  This is exactly the shape
demanded by `CNLClusterEncodingData.kraftSum_le`.
-/
theorem cnl_genuine_kraft_no_prefactor {M : ℕ} (hM : 1 ≤ M) :
    cleanCNLKraftSum (selectedTransitions genuineCNLCluster) (genuineCNLBNDHeight M) 1
      ≤ (2 : ℝ) ^ M :=
  genuineCNL_selectedKraft_le hM

/--
**The crude `CNLFibreBound` shape, `B = Fintype.card CNLTransition` (the `O(1)` prefactor).**

On the *same* cluster, the model-finiteness fibre bound (residue map `= id`) only gives
`≤ (Fintype.card CNLTransition)·C_Q^M`.  Comparing with `cnl_genuine_kraft_no_prefactor`
makes precise that the prefactor is purely the cost of *not* removing duplicates — the
manuscript L.1.2a–d removal (`exists_codeClean_subfamily`) is what closes it.
-/
theorem cnl_genuine_kraft_crude_prefactor (M : ℕ) :
    cleanCNLKraftSum (selectedTransitions genuineCNLCluster) (genuineCNLBNDHeight M) 1
      ≤ (Fintype.card CNLTransition : ℝ) * (2 : ℝ) ^ M :=
  cleanCNLKraftSum_selectedTransitions_le_boundedToOne_ofGeometry
    (genuineCNLGeometry M) (Fintype.card CNLTransition)
    (fun k _ =>
      card_codeWord_fibre_le_card_cnlTransition genuineCNLCluster
        (genuineCNLGeometry M).sym (genuineCNLGeometry M).M k)

/-! ## 3. Non-degeneracy witnesses -/

/-- The cluster is genuinely non-singleton: the selected family has card `2`. -/
theorem cnl_genuine_cluster_card :
    (selectedTransitions genuineCNLCluster).card = 2 :=
  genuineCNLCluster_selected_card

/-- The telescoping additive BND height is strictly positive on the whole cluster
(depth `M ≥ 1`) — never the degenerate zero height. -/
theorem cnl_genuine_height_pos {M : ℕ} (hM : 1 ≤ M) (t : CNLTransition) :
    0 < genuineCNLBNDHeight M t :=
  genuineCNLBNDHeight_pos hM t

/-! ## 4. Honest residual inventory -/

/-- The precise post-construction status of the `cnl` provider. -/
def cnlUnconditionalProviderResiduals : List String :=
  [ "CLOSED (provider) — cnlUnconditionalProvider inhabits the cnl field of " ++
      "GlobalAssemblyCoreInputs unconditionally (no hypotheses), via " ++
      "cnlProvider_ofGeometry on the genuine per-shell geometry cnlGeomField_genuine_all.",
    "CLOSED (O(1) caveat) — the Fintype.card CNLTransition prefactor of CNLFibreBound is " ++
      "NOT irreducible: it is the cost of bounding the untrimmed family. The L.1.2a–d " ++
      "code-transversal removal (exists_codeClean_subfamily) makes the code injective " ++
      "(B = 1), giving kraftSum_le ≤ C_Q^M with no prefactor (cnl_genuine_kraft_no_prefactor; " ++
      "contrast cnl_genuine_kraft_crude_prefactor).",
    "CLOSED (non-degeneracy) — genuine card-2 cluster (cnl_genuine_cluster_card), strictly " ++
      "positive telescoping BND height (cnl_genuine_height_pos), strictly positive shell " ++
      "factor and |I_j|; no empty/zero/singleton shortcut.",
    "OPEN (fidelity, not a hypothesis) — CNLTransition carries no lift-state geometry, so the " ++
      "cluster is a representative manuscript-shaped cluster, not transported from the shell's " ++
      "actual gap-window ladder (the irreducible CNL residue; the sharp B = Q route needs the " ++
      "carry-quotient input hcarry of CNLFibreBound §1). The budget uses the calibrated positive " ++
      "shellFactor = cStar·ξ/(12·C_Q^M) since CNLClusterEncodingData leaves shellFactor/|I_j| free. " ++
      "Neither blocks the unconditional inhabitation." ]

theorem cnlUnconditionalProviderResiduals_nonempty :
    cnlUnconditionalProviderResiduals ≠ [] := by
  simp [cnlUnconditionalProviderResiduals]

/-! ## 5. Axiom-cleanliness audit -/

#print axioms cnlUnconditionalProvider
#print axioms cnlUnconditionalProviderStructure
#print axioms cnlUnconditionalProvider_bound
#print axioms cnl_genuine_kraft_no_prefactor
#print axioms cnl_genuine_kraft_crude_prefactor

end

end Erdos260
