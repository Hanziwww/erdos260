import Erdos260.TowerShallowDeepUnconditional
import Erdos260.RunSupportMaxCore
import Erdos260.ReturnAnchoredUnconditional
import Erdos260.ChernoffAreaUnconditional
import Erdos260.CNLMultiChargeUnconditional
import Erdos260.DensePackScaleObstruction

/-!
# Erdős 260 — the six-atom capstone on the corrected surface

This module consolidates the 2026-06-10 closure wave.  It defines the single final
residual `Erdos260SixAtomResidual` whose six fields are the sharpest per-atom surfaces
produced by the wave, and proves the endpoint

`erdos260_of_sixAtoms : Erdos260SixAtomResidual → Erdos260Statement`

through the ctx-pinned P9 ledger.  The class-3 slot is carried by the CORRECTED
`DensePackCorrectedResidue` — the deep-shell-false scalar `hScale` of the published
`P9V3RunResidual` surface (refuted on every `r ≥ 1` shell by
`densePack_hScale_fails_of_r_ge_one`) is not consumed anywhere on this route.

The six atoms:

1. **Tower / class 2** — `Class2DeepShellResidual`: deep-shell Hall marginal window
   data; shallow shells (`shellLadderDepth ≤ 328965`) are closed unconditionally.
2. **Run / class 5** — `RunClass5LeafSupportMaxCoreResidual`: I.6S stage map, finite
   L.4.2 half-decrease, and the Section 26 linear max-form support inequality
   (proved equivalent to the sharp `RunClass5LeafResidual`).
3. **Return / class 4** — `ReturnAnchoredZResidual`: the (Z) digit data, clean step,
   M.2.1 gap divisibility, K.1 interior, and the `M_L·X` numeric; equivalent to the
   anchored seed surface, and on gated shells (all `L ≤ 15420`) to `Class4FibreEmpty`.
4. **Chernoff / class 0** — class-0 routed-fibre emptiness at the canonical budget;
   the §22 Kraft datum is a closed theorem and the 22.1A calibration is provably
   equivalent to this emptiness.
5. **CNL / class 1** — `Class1FibreEmpty` at the canonical budget; equivalent to the
   pinned-arithmetic condition, closed outright when `¬(64 ∣ L)` or the orbit modulus
   is `< 9`, and of cardinality `≤ 1` on all `L ≤ 15420`.
6. **DensePack / class 3** — `DensePackCorrectedResidue`: K.1.1 endpoint density,
   K.1 interior containment, and the corrected K.1.2 amortized cover (free on `r = 0`
   shells); no over-strong scalar.

Everything else — carry floor, faithful phases, mass nonnegativity, the class-6
old-residual vacancy, the joint TRT ledger bound, the Kraft sum, the `hne`/`hcard`
counts — is supplied by closed theorems inside `toLedger`.
-/

namespace Erdos260

noncomputable section

/-- The canonical six-atom V3 budget: Tower from the shallow/deep bridge, Run from the
corrected Section 26 max-core residual, Return from the anchored Z-residual family. -/
def sixAtomBudget
    (towerDeep : Class2DeepShellResidual)
    (runCore : ∀ ctx : ActualFailureContext, RunClass5LeafSupportMaxCoreResidual ctx)
    (returnZ : ∀ ctx : ActualFailureContext, ReturnAnchoredZResidual ctx) :
    ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx :=
  v3Budget (p9V3TowerCount_ofShallowDeep towerDeep)
    (p9V3RunChainOfResidual (runClass5LeafResidual_ofSupportMaxCoreResidual runCore))
    (returnChargeOfZResiduals returnZ)

/-- **The final six-atom residual.**  Each field is the sharpest checked surface of its
atom after the 2026-06-10 wave; the class-0/1 fields and the class-3 residue are stated
at the canonical `sixAtomBudget` of the first three fields. -/
structure Erdos260SixAtomResidual where
  /-- Tower / class 2: deep-shell Hall marginal (shallow shells are closed). -/
  towerDeep : Class2DeepShellResidual
  /-- Run / class 5: the corrected Section 26 support max-core residual. -/
  runCore : ∀ ctx : ActualFailureContext, RunClass5LeafSupportMaxCoreResidual ctx
  /-- Return / class 4: the anchored (Z) residual family. -/
  returnZ : ∀ ctx : ActualFailureContext, ReturnAnchoredZResidual ctx
  /-- Chernoff / class 0: the routed class-0 fibre is empty at the canonical budget. -/
  class0Empty : ∀ ctx : ActualFailureContext,
    routedFibre ctx.n24CarryData
      ((sixAtomBudget towerDeep runCore returnZ) ctx).route 0 = ∅
  /-- Clean-CNL / class 1: the routed class-1 fibre is empty at the canonical budget. -/
  class1Empty : Class1FibreEmpty (sixAtomBudget towerDeep runCore returnZ)
  /-- DensePack / class 3: the corrected residue (density + interior + amortized cover). -/
  densePack : DensePackCorrectedResidue (sixAtomBudget towerDeep runCore returnZ)

namespace Erdos260SixAtomResidual

/-- The canonical budget of a six-atom residual. -/
def budget (R : Erdos260SixAtomResidual) :
    ∀ ctx : ActualFailureContext, SeparatedPhaseRoutedBudget ctx :=
  sixAtomBudget R.towerDeep R.runCore R.returnZ

/-- The five ctx-pinned ledger bounds from the six atoms.

* class 0 — through the closed Kraft datum and the empty-fibre kraft/small residual;
* class 1 — through the proved ledger/emptiness equivalence;
* class 3 — through the corrected (no-`hScale`) DensePack bridge;
* classes 2+4+5 — through the joint TRT seed bound of the V3 budget;
* class 6 — through the genuine route's old-residual vacancy. -/
def toLedger (R : Erdos260SixAtomResidual) : P9CtxPinnedLedgerResidual where
  budget := sixAtomBudget R.towerDeep R.runCore R.returnZ
  hChernoff :=
    (ChernoffGenuineAreaKraftSmallResidual.ofClass0FibreEmpty _ R.class0Empty).hChernoffField
  hCnl := (hCnlField_iff_class1FibreEmpty _).mpr R.class1Empty
  hDensePack := R.densePack.hDensePackField (fun _ => rfl)
  hTRT := seedHTRT _
  hOldRes := fun ctx => by
    show routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 6
        ≤ ∑ k ∈ oldResIdxVal ctx, oldResAtVal ctx k
    rw [genuineChargeRoute_routed6_zero ctx]
    exact oldResL65_branchMass_nonneg ctx

/-- The final statement from the six-atom residual, through the ctx-pinned P9 ledger. -/
theorem toStatement (R : Erdos260SixAtomResidual) : Erdos260Statement :=
  R.toLedger.toStatement

end Erdos260SixAtomResidual

/-- **The final six-atom endpoint.**  `Erdos260Statement` from exactly the six sharpest
per-atom residual surfaces, with no over-strong scalar anywhere on the route. -/
theorem erdos260_of_sixAtoms (R : Erdos260SixAtomResidual) : Erdos260Statement :=
  R.toStatement

/-- Machine-readable status of the six-atom capstone. -/
def erdos260SixAtomStatus : List String :=
  [ "FINAL ENDPOINT: erdos260_of_sixAtoms (R : Erdos260SixAtomResidual) : " ++
      "Erdos260Statement, through the ctx-pinned P9 ledger; the deep-shell-false " ++
      "hScale scalar is NOT consumed on this route (corrected class-3 surface).",
    "ATOM Tower/class 2: Class2DeepShellResidual — deep-shell Hall marginal window " ++
      "data (shellLadderDepth > 328965); shallow shells closed unconditionally " ++
      "(class2ActiveFloorCount_ofShallow).",
    "ATOM Run/class 5: RunClass5LeafSupportMaxCoreResidual — I.6S stageOf + finite " ++
      "L.4.2 hhalf + Section 26 linear max-form support bound; equivalent both ways " ++
      "to the sharp RunClass5LeafResidual.",
    "ATOM Return/class 4: ReturnAnchoredZResidual — key/hzero/hcleanStep/hgapDiv/" ++
      "class4Interior/hnumeric; equivalent to the anchored seed surface; on gated " ++
      "shells (all L <= 15420) equivalent to Class4FibreEmpty.",
    "ATOM Chernoff/class 0: routed class-0 fibre emptiness at the canonical budget; " ++
      "kraft (the section 22 antichain datum) is a closed theorem " ++
      "(chernoffClass0KraftFibres / chernoffClass0KraftSum_le_one); small/hdom are " ++
      "provably equivalent to this emptiness (smallExcess_iff_class0FibreEmpty).",
    "ATOM CNL/class 1: Class1FibreEmpty at the canonical budget; equivalent to the " ++
      "pinned-arithmetic condition (v3_class1FibreEmpty_iff_pinned); closed outright " ++
      "when not (64 | L) or orbit modulus < 9; fibre card <= 1 on all L <= 15420.",
    "ATOM DensePack/class 3: DensePackCorrectedResidue — K.1.1 endpoint density + " ++
      "K.1 interior + corrected K.1.2 amortized cover (free on r = 0 shells); " ++
      "replaces the hScale scalar refuted on every r >= 1 shell " ++
      "(densePack_hScale_fails_of_r_ge_one).",
    "CLOSED INSIDE toLedger: carry floor, faithful phases, mass nonnegativity, the " ++
      "class-6 old-residual vacancy, the joint TRT ledger bound, the Kraft sum, and " ++
      "the hne/hcard counts." ]

theorem erdos260SixAtomStatus_nonempty : erdos260SixAtomStatus ≠ [] := by
  simp [erdos260SixAtomStatus]

#print axioms sixAtomBudget
#print axioms Erdos260SixAtomResidual.budget
#print axioms Erdos260SixAtomResidual.toLedger
#print axioms Erdos260SixAtomResidual.toStatement
#print axioms erdos260_of_sixAtoms
#print axioms erdos260SixAtomStatus_nonempty

end

end Erdos260
