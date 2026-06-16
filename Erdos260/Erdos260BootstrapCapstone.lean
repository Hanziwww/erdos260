import Erdos260.ScaleFloorHarvest
import Erdos260.DensityBootstrap

/-!
# Erdős 260 — the wave-7 bootstrap capstone (assembly)

Wave 7 produced two green modules:

* `ScaleFloorHarvest` — the collapsed unconditional surface
  `Erdos260FloorHarvestResidual` (14 fields; dead `1 ≤ r` guards gone, the
  Return gates body 3-way, the densepack gated half gone), endpoint
  `erdos260_of_floorHarvest`, equivalence `nonempty_floorHarvest_iff_rigidity`.
* `DensityBootstrap` — the weighted periodic-tail identity, the master voiding
  `pinnedValue_windowPeriodic_void` (no pinned-value context is window-periodic,
  at EVERY scale), and the conditional successors
  `DeepDyadicWindowPeriodicity` / `DeepFifthWindowPeriodicity` /
  `DeepThirdsWindowPeriodicity` / `DeepFixedFamilyWindowPeriodicity` with
  endpoint `erdos260_of_dyadicWindowPeriodicity`.

This module is the assembly verdict on how the two compose.

## The composition audit (honest): the two surfaces are PARALLEL

1. **No floor-harvest field is lever-touchable.**  None of the 14 fields of
   `Erdos260FloorHarvestResidual` (nor of its `toRigidity` /
   `DigitSideEnumResidual` chain) mentions `ShellValueDyadic`,
   `FixedFamilyHit`, or any pinned value: the fixed-family content lives only
   on the wave-4/5 lever lineage.  There is no fixed-family guard for the
   lever Props to void.
2. **The per-ctx window-periodicity escape is itself VOID.**  The natural
   disjunct candidate — "or this context is window-periodic with a pinned
   value" (`BootstrapPeriodicEscape`) — is refuted OUTRIGHT at every context
   and every scale by the bootstrap's own master voiding
   (`bootstrapPeriodicEscape_void`, from `pinnedValue_windowPeriodic_void`
   via the four per-family voidings).  Adding it to any obligation is dead
   weight (`or_bootstrapEscape_iff` — `P ∨ escape ↔ P`), i.e. exactly the
   kind of provably-dead disjunct the floor harvest just removed from
   `ReturnGatesBody`.  A "relieved" surface built this way would be the same
   surface with extra noise; we refuse to ship it.
3. **The conditional route is PARALLEL, not smaller.**  The window-periodicity
   endpoint `erdos260_of_dyadicWindowPeriodicity` consumes
   `DeepDyadicWindowPeriodicity` (unproven: by the honest obstruction
   inventory, nothing forces eventual periodicity — the carry states
   `~u(2X+2)` exceed the `X+1` window slots,
   `bootstrap_state_count_exceeds_window`) PLUS the wave-5 lever surface
   `DyadicValueLever → Erdos260DyadicLeverResidual`.  That surface has the
   `(3,1)` / `(21,3)` / `(105,7)` family reliefs the lever buys, but it is the
   wave-4/5 SHAPE: it lacks the wave-6 digit-side guards
   (`¬ ReturnIndexWindowClean`, `¬ ReturnB2FreeDatum`), the
   `ModulusTailCriteria` order disjuncts on the tower/run/class-0/class-1
   tails, the deep-only class-1 collapse, and the wave-6.5 K.1-gate and
   densepack collapses.  Neither surface implies the other: PARALLEL routes
   to `Erdos260Statement`.  Forcing them into one structure would demand
   `DeepDyadicWindowPeriodicity` of every unconditional provider — a strictly
   STRONGER surface, an artificial merge.  Not done.

## The deliverable

* `Erdos260BootstrapResidual` — the wave-7 sharp boundary IS the floor-harvest
  14-field surface (reducible alias; nothing hidden, nothing added).
* `erdos260_of_bootstrapResidual : Erdos260BootstrapResidual →
  Erdos260Statement` — composed from `erdos260_of_floorHarvest` alone.
* Weakening witnesses `bootstrapResidual_of_rigidityResidual` /
  `bootstrapResidual_of_digitSideResidual`; equivalences
  `nonempty_bootstrap_iff_floorHarvest` (definitional) and
  `nonempty_bootstrap_iff_rigidity` (wave-6 surface).
* The parallel conditional route re-exported with its wave-7 name:
  `erdos260_bootstrap_periodicity_route`.

Additive only: nothing upstream is touched; only existing public bridges are
consumed.  No `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace Erdos260

noncomputable section

/-! ## Part 1.  The composition audit: the would-be escape disjunct is void -/

/-- **The lever-touchable window-periodic stratum** — the candidate
"window-periodicity alternative" disjunct for the floor-harvest fields: the
context is window-periodic AND carries one of the pinned values the lever
Props would void (dyadic `1/2^t`, a fixed family, fifth `1/(5·2^t)`, thirds
`2/(3·2^t)`). -/
def BootstrapPeriodicEscape (ctx : ActualFailureContext) : Prop :=
  WindowPeriodic ctx ∧
    (ShellValueDyadic ctx
      ∨ FixedFamilyHit ctx
      ∨ (∃ t : ℕ, realWeightedValue (natBinaryAsReal ctx.shell.d) = 1 / (5 * 2 ^ t))
      ∨ (∃ t : ℕ, realWeightedValue (natBinaryAsReal ctx.shell.d) = 2 / (3 * 2 ^ t)))

/-- **The escape is VOID at every context and EVERY scale** (no `2^493443`
floor) — the bootstrap's master voiding `pinnedValue_windowPeriodic_void`
through its four per-family forms.  This is the assembly verdict: the
window-periodicity alternative can never fire, so it relieves nothing. -/
theorem bootstrapPeriodicEscape_void (ctx : ActualFailureContext) :
    ¬ BootstrapPeriodicEscape ctx := by
  rintro ⟨hwp, hdy | hhit | ⟨t, hval⟩ | ⟨t, hval⟩⟩
  · exact shellValueDyadic_void_of_windowPeriodic ctx hwp hdy
  · exact fixedFamilyHit_void_of_windowPeriodic ctx hwp hhit
  · exact towerFifthValue_void_of_windowPeriodic ctx hwp t hval
  · exact towerThirdsValue_void_of_windowPeriodic ctx hwp t hval

/-- **Why no floor-harvest field gains a live disjunct**: adding the
window-periodicity escape to ANY obligation is dead weight — the augmented
field is EQUIVALENT to the verbatim one.  (The same dead-disjunct shape the
floor harvest just removed from `ReturnGatesBody`; we do not re-add it.) -/
theorem or_bootstrapEscape_iff (ctx : ActualFailureContext) (P : Prop) :
    (P ∨ BootstrapPeriodicEscape ctx) ↔ P :=
  ⟨fun h => h.resolve_right (bootstrapPeriodicEscape_void ctx), Or.inl⟩

/-! ## Part 2.  The wave-7 sharp boundary -/

/-- **The wave-7 bootstrap residual** — the floor-harvest 14-field surface
VERBATIM.  Honest: the lever Props touch no floor-harvest field (none carries
a fixed-family/pinned-value obligation), the per-ctx escape disjunct is
provably void (`bootstrapPeriodicEscape_void`), and the conditional
periodicity route is parallel (its surface is the wave-4/5 lever shape) — so
the sharp unconditional boundary after wave 7 IS the floor-harvest surface,
under its wave-7 name. -/
abbrev Erdos260BootstrapResidual : Prop := Erdos260FloorHarvestResidual

/-- **The wave-7 final endpoint.**  `Erdos260Statement` from the bootstrap
residual, composed through `erdos260_of_floorHarvest` (hence through
`toRigidity` into `erdos260_of_rigidityResidual` and the wave-6 `toDigitSide`
chain) with no re-proving anywhere on the route. -/
theorem erdos260_of_bootstrapResidual (H : Erdos260BootstrapResidual) :
    Erdos260Statement :=
  erdos260_of_floorHarvest H

/-- Weakening witness: any wave-6 rigidity provider yields the wave-7
residual (through the floor-harvest witness). -/
def bootstrapResidual_of_rigidityResidual (R : Erdos260RigidityResidual) :
    Erdos260BootstrapResidual :=
  floorHarvestResidual_of_rigidityResidual R

/-- Weakening witness: any wave-6 digit-side provider yields the wave-7
residual. -/
def bootstrapResidual_of_digitSideResidual (R : DigitSideEnumResidual) :
    Erdos260BootstrapResidual :=
  floorHarvestResidual_of_digitSideResidual R

/-- The wave-7 surface is the floor-harvest surface — definitionally. -/
theorem nonempty_bootstrap_iff_floorHarvest :
    Nonempty Erdos260BootstrapResidual ↔ Nonempty Erdos260FloorHarvestResidual :=
  Iff.rfl

/-- The wave-7 surface is equivalent to the wave-6 rigidity surface (through
`nonempty_floorHarvest_iff_rigidity`): the new presentation hides no
strength. -/
theorem nonempty_bootstrap_iff_rigidity :
    Nonempty Erdos260BootstrapResidual ↔ Nonempty Erdos260RigidityResidual :=
  nonempty_floorHarvest_iff_rigidity

/-! ## Part 3.  The parallel conditional route (re-exported, NOT merged) -/

/-- **The wave-7 conditional route** — `Erdos260Statement` from the deep
dyadic window-periodicity successor plus the lever-shrunk wave-5 surfaces
(re-export of `erdos260_of_dyadicWindowPeriodicity` under its wave-7 name).
PARALLEL to `erdos260_of_bootstrapResidual`: its surface
`DyadicValueLever → Erdos260DyadicLeverResidual` is the wave-4/5 shape — it
enjoys the `(3,1)`/`(21,3)`/`(105,7)` family reliefs but lacks the wave-6
digit-side guards, the tail order disjuncts, the deep-only class-1 collapse
and the wave-6.5 gate/densepack collapses.  Neither surface implies the
other; merging would demand the (unproven, obstruction-laden)
`DeepDyadicWindowPeriodicity` of every unconditional provider. -/
theorem erdos260_bootstrap_periodicity_route (h : DeepDyadicWindowPeriodicity)
    (surfaces : DyadicValueLever → Erdos260DyadicLeverResidual) :
    Erdos260Statement :=
  erdos260_of_dyadicWindowPeriodicity h surfaces

/-! ## Part 4.  Machine-readable status (honest) -/

/-- Honest machine-readable status of the wave-7 bootstrap capstone. -/
def erdos260BootstrapCapstoneStatus : List String :=
  [ "MAIN ENDPOINT (wave 7): erdos260_of_bootstrapResidual (H : Erdos260BootstrapResidual) " ++
      ": Erdos260Statement, with Erdos260BootstrapResidual = the floor-harvest 14-field " ++
      "surface Erdos260FloorHarvestResidual VERBATIM (reducible alias), composed through " ++
      "erdos260_of_floorHarvest -> toRigidity -> erdos260_of_rigidityResidual -> the wave-6 " ++
      "toDigitSide chain.  Nothing re-proved; only public bridges consumed.",
    "COMPOSITION VERDICT (the honest answer): the two wave-7 surfaces are PARALLEL, not " ++
      "mergeable.  (a) No field of the floor-harvest surface (or its toRigidity chain) " ++
      "carries a fixed-family or pinned-value obligation, so the lever Props void no guard " ++
      "there.  (b) The candidate disjunct BootstrapPeriodicEscape (window-periodic AND " ++
      "pinned value: dyadic / fixed-family / fifth / thirds) is VOID at every ctx and EVERY " ++
      "scale (bootstrapPeriodicEscape_void, from pinnedValue_windowPeriodic_void), so " ++
      "adding it to any field is dead weight (or_bootstrapEscape_iff: P OR escape IFF P) - " ++
      "the exact dead-disjunct shape wave 6.5 removed from ReturnGatesBody.  (c) The " ++
      "conditional route's surface (DyadicValueLever -> Erdos260DyadicLeverResidual) is the " ++
      "wave-4/5 shape: it has the (3,1)/(21,3)/(105,7) family reliefs but lacks the wave-6 " ++
      "digit-side guards, the ModulusTailCriteria order disjuncts, the deep-only class-1 " ++
      "collapse, and the wave-6.5 K.1-gate/densepack collapses.  Neither implies the other; " ++
      "a merged structure would demand DeepDyadicWindowPeriodicity of every unconditional " ++
      "provider (strictly stronger).  NO artificial merge shipped.",
    "CONDITIONAL ROUTE RE-EXPORTED: erdos260_bootstrap_periodicity_route " ++
      "(h : DeepDyadicWindowPeriodicity) (surfaces : DyadicValueLever -> " ++
      "Erdos260DyadicLeverResidual) : Erdos260Statement = " ++
      "erdos260_of_dyadicWindowPeriodicity.  DeepDyadicWindowPeriodicity remains UNPROVEN " ++
      "and obstruction-laden: nothing forces eventual periodicity (carry states ~u(2X+2) " ++
      "exceed the X+1 window slots, bootstrap_state_count_exceeds_window; the recursion is " ++
      "non-autonomous; the digit is recovered from carry PAIRS, integerCarry_digit_recover).",
    "EQUIVALENCES AND WITNESSES: nonempty_bootstrap_iff_floorHarvest (definitional, " ++
      "Iff.rfl); nonempty_bootstrap_iff_rigidity (= nonempty_floorHarvest_iff_rigidity, so " ++
      "wave 7 = wave 6.5 = wave 6 in strength on the unconditional lane); weakening " ++
      "witnesses bootstrapResidual_of_rigidityResidual and " ++
      "bootstrapResidual_of_digitSideResidual.",
    "THE RESIDUAL SURFACE (14 fields, unchanged from the floor harvest): towerEnumLow / " ++
      "towerEnumTail (deep-shell guard towerShallowDepthBound < L kept honestly: " ++
      "246737 < 328965), runNumericLow / runNumericTail (1 <= r guards gone), returnGates " ++
      "(3-way ungated body), returnZero / returnMaxClean / returnInterior (digit-side " ++
      "guards), class0Survivor / class0Mid / class0BigOrder, class1DeepLow / class1DeepTail " ++
      "(1 <= r gone), densePackUngated (gated half gone).  NEXT MECHANISM: whatever forces " ++
      "near-periodicity on the failure word - the section 25.1/25.3 descent-window match " ++
      "residuals; pushing the scale floor to 2^328965 would kill the last L-guard (r >= 21).",
    "HYGIENE: additive only; no upstream module touched; no sorry / admit / new axiom / " ++
      "native_decide; all #print axioms in [propext, Classical.choice, Quot.sound]." ]

theorem erdos260BootstrapCapstoneStatus_nonempty :
    erdos260BootstrapCapstoneStatus ≠ [] := by
  simp [erdos260BootstrapCapstoneStatus]

/-! ## Part 5.  Axiom-cleanliness audit -/

#print axioms bootstrapPeriodicEscape_void
#print axioms or_bootstrapEscape_iff
#print axioms erdos260_of_bootstrapResidual
#print axioms bootstrapResidual_of_rigidityResidual
#print axioms bootstrapResidual_of_digitSideResidual
#print axioms nonempty_bootstrap_iff_floorHarvest
#print axioms nonempty_bootstrap_iff_rigidity
#print axioms erdos260_bootstrap_periodicity_route
#print axioms erdos260BootstrapCapstoneStatus_nonempty

end

end Erdos260
