import Erdos260.ExitMassFamilyClosure

/-!
# V30 cycle-saturated mass balance (`V30CycleMassBalance`) — LANE B

This module (NEW; it edits no existing file) formalizes the v30 **mass-NORMALIZED
cycle balance** of Appendix R of `proof_v4_repaired_core_v30.tex`
(`appendix-r.-third-unconditional-closure-push`, manuscript lines 9080-9295).  It is
the engine that feeds the off-pin exit-mass cap (C1) of Lane C on the SAFE cone.

## What v30 says, and what this module proves

The v30 manuscript is explicit (O.3 `lem:o-event-count-ledger`, 8493-8518; R
`lem:r-strong-share-not-from-saturation`, 9238) that the PROPORTIONAL exit-event
share is FALSE and unprovable — exactly the Lean negative `emfc_spacedShare_not_covering`
/ the unfeedable `EmcSpacedShareDatum`.  The valid replacement is the weaker
mass-NORMALIZED balance around a recurrent cycle: the cyclic successor map is a
measure-preserving bijection (`lem:r-cycle-map-preserves-measure`, 9110), so every
phase carries equal mass, and the exit mass is the `b/c` SHARE of the **total phase
mass** `M_tot` (NOT of the total exit mass):

* `prop:r-exit-share-closed` (9203):  `ExitMass(F) ≤ (b/c)·M_tot + o(X|I_j|)`.

This module delivers:

1. **Word-level measure preservation** (in-tree, reuses the `emcT_*` drift calculus
   and the binary gap-deviation classification): the recurrent-cycle successor
   preserves the event-indexed window excess when the gap word is `c`-periodic
   (`cmb_gapWindow_cyclic`, `cmb_windowExcess_cyclic`), with the two-sided per-step
   drift bracket `cmb_windowExcess_drift_bracket` (= `emcT_windowExcess_drift` /
   `_rev`).  The binary classification (`mdc_nonExit_weight_eq_zero`) gives the
   conservation leg "clean in-cycle motion is uncharged": interior (band-following)
   indices carry zero exit charge (`cmb_interior_devContent_zero`,
   `cmb_exits_carry_all`).

2. **The phase-mass balance** (`CycleMassDatum`): from the measure-preservation
   hypothesis `preserved` (the ONE residual atom of Lane B; = `lem:r-cycle-map-preserves-measure`),
   every phase carries equal mass (`CycleMassDatum.uniform`), so
   * **conservation / partition** `total = exit + interior`
     (`CycleMassDatum.conservation`) — entry mass = exit mass + interior contribution;
   * the **exact integer balance** `c·ExitMass = b·M_F` (`CycleMassDatum.balance`,
     the integer form of `(R.1b)`), and the (R.2′) ambient form
     `c·ExitMass ≤ b·M_tot` (`CycleMassDatum.exitMass_le_ambient`); plus the faithful
     real form with the single aggregate `o`-collar `ε`
     (`CycleMassDatum.exitMass_le_share`).

3. **The safe-cone per-class cap for Lane C** (`cmb_safeCone_nat`,
   `cmb_offPin_safeCone_nat`, `cmb_offPin_safeCone_cap`): on a safe-cone cell
   `1536·h·b ≤ 31·c` (`prop:ab-safe-cone-closed-summed`) with the disjoint-cell
   ambient bound `M_tot ≤ X` (`lem:ab-ambient-support-bound-summed`), the normalized
   exposure `NExitMass = h(c)·ExitMass` (`def:ab-normalized-exposure`, with
   `h(c) = ⌊(r+c)/c⌋`) clears the corrected per-class capacity
   `1536·NExitMass ≤ 31·X`, i.e. `NExitMass ≤ emcCap = (31/1536)·X` — the exact (C1)
   shape, with `M_tot` on the right (mass-normalized), NOT the false total-exit share.

## Cone-locality and residual atoms (the brief's question 3)

The balance is CONE-LOCAL and provable from conservation alone: it does NOT use the
unsafe-core emptiness (Lane D) or (C1).  The genuine residual atoms it abstracts are:

* `CycleMassDatum.preserved` — measure preservation around the recurrent cycle
  (RISK c; `lem:r-cycle-map-preserves-measure`, the Appendix E terminal-labelled
  transition is a measure-preserving bijection on interior fibres).
* the `hambient` hypothesis `M_tot ≤ X` — the disjoint-cell ambient-mass accounting
  (RISK b; `lem:ab-ambient-support-bound-summed` / `lem:ad-summed-ambient-support`),
  Lane C's job to sum over disjoint cells.
* the `hsafe` hypothesis `1536·h·b ≤ 31·c` — the safe-cone cell condition (Appendix
  AB), the cell classification supplied by Lane C.

The unsafe core (`b=1, c≥64, 1536·h(c) > 31·c`) is OUT of scope here: it is EMPTY by
Lane D (`prop:ac-unsafe-core-empty`), not capped by balance.  Lane B supplies only the
safe-cone balance.

No `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192

/-! ## Part 1.  Word-level measure preservation around a recurrent cycle

The word shadow of `lem:r-cycle-map-preserves-measure` (9110): on a recurrent cycle
the gap word is `c`-periodic, so a full cyclic step preserves the event-indexed
window excess.  Reuses the `emcT_*` per-step drift calculus and the binary
gap-deviation classification ("clean in-cycle motion is uncharged"). -/

/-- **Cyclic invariance of the gap window**: when the gap word is `c`-periodic over a
descent window (the defining property of a recurrent terminal-labelled tower cycle),
one full cyclic shift `k ↦ k + c` leaves the gap window unchanged. -/
theorem cmb_gapWindow_cyclic (g : ℕ → ℕ) (k r c : ℕ)
    (hper : ∀ i, i ≤ r → g (k + c + i) = g (k + i)) :
    gapWindow g (k + c) r = gapWindow g k r := by
  unfold gapWindow
  refine Finset.sum_congr rfl (fun i hi => ?_)
  exact hper i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))

/-- **Word-level measure preservation** (`lem:r-cycle-map-preserves-measure`, word
form): the recurrent-cycle successor preserves the event-indexed window excess —
`windowExcess` is invariant under the full cyclic step `k ↦ k + c`. -/
theorem cmb_windowExcess_cyclic (g : ℕ → ℕ) (k r c : ℕ) (T : ℝ)
    (hper : ∀ i, i ≤ r → g (k + c + i) = g (k + i)) :
    windowExcess g (k + c) r T = windowExcess g k r T := by
  unfold windowExcess
  rw [cmb_gapWindow_cyclic g k r c hper]

/-- **The per-step drift bracket** (= `emcT_windowExcess_drift` / `_rev`): even
WITHOUT periodicity, a cyclic step `c = s+1` changes the window excess by at most the
`s+1` boundary gaps on each side — the in-cycle motion is charged the boundary gaps
ALONE, never the full window.  When those boundary gaps vanish-deviate (the cycle is
saturated) the bracket collapses to `cmb_windowExcess_cyclic`. -/
theorem cmb_windowExcess_drift_bracket (g : ℕ → ℕ) (k r s : ℕ) (T : ℝ) :
    windowExcess g (k + (s + 1)) r T
        ≤ windowExcess g k r T + ((gapWindow g (k + r + 1) s : ℕ) : ℝ)
      ∧ windowExcess g k r T
        ≤ windowExcess g (k + (s + 1)) r T + ((gapWindow g k s : ℕ) : ℝ) :=
  ⟨emcT_windowExcess_drift g k r s T, emcT_windowExcess_drift_rev g k r s T⟩

/-- **Interior is uncharged** (binary gap-deviation classification, I.3 "clean
in-cycle motion is not charged"): a fully band-following (persistent / interior)
stretch carries exactly zero exit charge — every non-exit gap deviates by exactly `0`
(`mdc_nonExit_weight_eq_zero`). -/
theorem cmb_interior_devContent_zero (ctx : ActualFailureContext) (S : Finset ℕ)
    (hint : ∀ j ∈ S, hitGap ctx.n24CarryData.a j = fixedFamilyRecurrentBand ctx) :
    ∑ j ∈ S, emExitWeight ctx j = 0 :=
  Finset.sum_eq_zero (fun j hj => mdc_nonExit_weight_eq_zero ctx (hint j hj))

/-- **All deviation lives at exits**: restricting the deviation content to the EXIT
indices (positive exit weight) loses nothing — the interior contributes `0`.  This is
the conservation "entries = exits + interior" with interior ≡ 0 on the exit charge. -/
theorem cmb_exits_carry_all (ctx : ActualFailureContext) (S : Finset ℕ) :
    ∑ j ∈ S.filter (fun j => emExitWeight ctx j ≠ 0), emExitWeight ctx j
      = ∑ j ∈ S, emExitWeight ctx j :=
  Finset.sum_filter_of_ne (fun j _ h => h)

/-! ## Part 2.  The cycle-saturated phase-mass balance

The abstract carrier of `lem:r-global-phase-error` (9162) and
`prop:r-exit-share-closed` (9203).  `CycleMassDatum.preserved` is the measure-
preservation hypothesis; the balance is PROVED from it. -/

/-- A **cycle mass datum**: the event-indexed phase mass of a recurrent
terminal-labelled tower cycle of length `c`, phases `ℤ/cℤ`.  `w a` is the
event-indexed mass at phase `a` (the residual output weight of Definition J.1.2 /
Appendix N restricted to phase `a`); `E ⊆ range c` is the exit-phase set, `b = #E`.

The field `preserved` is the **measure-preservation hypothesis** — the discrete
consequence of `lem:r-cycle-map-preserves-measure` (the successor map `τ_a` is a
mass-preserving bijection between adjacent interior phases, so adjacent phases carry
equal mass).  This is the ONE residual atom of Lane B (RISK c); everything below is
PROVED from it. -/
structure CycleMassDatum where
  /-- Cycle length `c`. -/
  c : ℕ
  /-- The cycle is nonempty. -/
  hc : 1 ≤ c
  /-- Event-indexed phase mass `w a` at phase `a`. -/
  w : ℕ → ℕ
  /-- Exit-phase set `E`, with `b = #E`. -/
  E : Finset ℕ
  /-- Exit phases are genuine phases. -/
  hE : E ⊆ Finset.range c
  /-- **Measure preservation**: the successor map preserves phase mass. -/
  preserved : ∀ a, a + 1 < c → w (a + 1) = w a

/-- **Phase-mass uniformity**: measure preservation forces every phase to carry the
same mass `w 0` — the discrete form of "each phase has mass `c⁻¹·Σ`" (proof of
`lem:r-global-phase-error`). -/
theorem CycleMassDatum.uniform (D : CycleMassDatum) :
    ∀ a, a < D.c → D.w a = D.w 0 := by
  intro a
  induction a with
  | zero => intro _; rfl
  | succ n ih =>
      intro ha
      rw [D.preserved n ha, ih (by omega)]

/-- The total phase mass `M_F = Σ_a μ_F(a)`. -/
def CycleMassDatum.totalMass (D : CycleMassDatum) : ℕ :=
  ∑ a ∈ Finset.range D.c, D.w a

/-- The exit mass `Σ_{a ∈ E} μ_F(a)`. -/
def CycleMassDatum.exitMass (D : CycleMassDatum) : ℕ :=
  ∑ a ∈ D.E, D.w a

/-- The interior (non-exit / persistent) mass `Σ_{a ∉ E} μ_F(a)`. -/
def CycleMassDatum.interiorMass (D : CycleMassDatum) : ℕ :=
  ∑ a ∈ Finset.range D.c \ D.E, D.w a

/-- At most `c` exit phases: `b = #E ≤ c`. -/
theorem CycleMassDatum.exitPhases_le (D : CycleMassDatum) : D.E.card ≤ D.c := by
  have h := Finset.card_le_card D.hE
  rwa [Finset.card_range] at h

/-- **CONSERVATION (entry = exit + interior)**: the total phase mass present over one
cycle pass partitions into the exit-phase mass plus the interior contribution. -/
theorem CycleMassDatum.conservation (D : CycleMassDatum) :
    D.totalMass = D.exitMass + D.interiorMass := by
  unfold CycleMassDatum.totalMass CycleMassDatum.exitMass CycleMassDatum.interiorMass
  rw [add_comm, Finset.sum_sdiff D.hE]

/-- The total phase mass equals `c·(w 0)` (every phase carries `w 0`). -/
theorem CycleMassDatum.totalMass_eq (D : CycleMassDatum) :
    D.totalMass = D.c * D.w 0 := by
  unfold CycleMassDatum.totalMass
  rw [Finset.sum_congr rfl (fun a ha => D.uniform a (Finset.mem_range.mp ha)),
    Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- The exit mass equals `b·(w 0)` (every exit phase carries `w 0`). -/
theorem CycleMassDatum.exitMass_eq (D : CycleMassDatum) :
    D.exitMass = D.E.card * D.w 0 := by
  unfold CycleMassDatum.exitMass
  rw [Finset.sum_congr rfl (fun a ha => D.uniform a (Finset.mem_range.mp (D.hE ha))),
    Finset.sum_const, smul_eq_mul]

/-- **THE MASS-NORMALIZED BALANCE** (integer form of `(R.1b)`,
`lem:r-global-phase-error`): `c·ExitMass(F) = b·M_F` — the exit mass is the EXACT
`b/c` share of the total PHASE mass.  No collar at the phase-mass level; the
`o(X|I_j|)` collar enters only when relating `M_F` to the in-tree ambient `M_tot`. -/
theorem CycleMassDatum.balance (D : CycleMassDatum) :
    D.c * D.exitMass = D.E.card * D.totalMass := by
  rw [D.exitMass_eq, D.totalMass_eq]; ring

/-- **(R.2′) integer form** (`prop:r-exit-share-closed`, 9203): with the total phase
mass dominated by the ambient phase mass `M_tot` (`M_F ≤ M_tot`, since
`F ⊆ Tot`), the exit mass clears the `b/c` share of `M_tot`:
`c·ExitMass(F) ≤ b·M_tot`.  This is the conclusion ACTUALLY proved by the
cycle-saturation argument — `M_tot` is the total PHASE mass, NOT the total exit
mass; the proof never compares `M_tot` with `ExitMass(Tot)` (so it cannot yield the
false (R1)). -/
theorem CycleMassDatum.exitMass_le_ambient (D : CycleMassDatum) {Mtot : ℕ}
    (hM : D.totalMass ≤ Mtot) :
    D.c * D.exitMass ≤ D.E.card * Mtot := by
  rw [D.balance]; exact Nat.mul_le_mul le_rfl hM

/-- **(R.2′) cross-multiplied real form** (no division): `c·ExitMass(F) ≤ b·M_tot`. -/
theorem CycleMassDatum.exitMass_share_real (D : CycleMassDatum) {Mtot : ℝ}
    (hM : (D.totalMass : ℝ) ≤ Mtot) :
    (D.c : ℝ) * (D.exitMass : ℝ) ≤ (D.E.card : ℝ) * Mtot := by
  have hbal : (D.c : ℝ) * (D.exitMass : ℝ) = (D.E.card : ℝ) * (D.totalMass : ℝ) := by
    exact_mod_cast D.balance
  rw [hbal]
  exact mul_le_mul_of_nonneg_left hM (by positivity)

/-- **(R.1c)/(R.2′) with the single aggregate collar** (real form, the literal
manuscript shape): `ExitMass(F) ≤ (b/c)·M_tot + ε` with ONE aggregate exceptional
mass `ε = o(X|I_j|)` (NOT one error per phase — no factor `c`). -/
theorem CycleMassDatum.exitMass_le_share (D : CycleMassDatum) {Mtot ε : ℝ}
    (hM : (D.totalMass : ℝ) ≤ Mtot) (hε : 0 ≤ ε) :
    (D.exitMass : ℝ) ≤ (D.E.card : ℝ) / (D.c : ℝ) * Mtot + ε := by
  have hcpos : (0 : ℝ) < (D.c : ℝ) := by
    have hc : 0 < D.c := D.hc
    exact_mod_cast hc
  have hcross := D.exitMass_share_real hM
  have hdiv : (D.exitMass : ℝ) ≤ (D.E.card : ℝ) / (D.c : ℝ) * Mtot := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hcpos]
    nlinarith [hcross]
  linarith

/-! ## Part 3.  The safe-cone per-class cap (the Lane C plug)

The deliverable consumed by Lane C: on the SAFE exposure cone the mass-normalized
balance closes the (C1) off-pin exit cap, with `M_tot` (phase mass) on the right. -/

/-- **THE SAFE-CONE PLUG (pure ℕ)** — the arithmetic core Lane C plugs into the
`(31/1536)·X` cap.  Inputs: the mass-normalized balance `c·exit ≤ b·M_tot`
(`(R.2′)`, Lane B), the safe-cone cell condition `1536·h·b ≤ 31·c` (Appendix AB
`prop:ab-safe-cone-closed-summed`), and the disjoint-cell ambient bound `M_tot ≤ X`
(Appendix AB/AD `lem:ab-ambient-support-bound-summed`).  Output: the normalized
exposure `h·exit` clears `1536·(h·exit) ≤ 31·X`. -/
theorem cmb_safeCone_nat (h exit b c Mtot X : ℕ) (hc : 1 ≤ c)
    (hbalance : c * exit ≤ b * Mtot)
    (hsafe : 1536 * (h * b) ≤ 31 * c)
    (hambient : Mtot ≤ X) :
    1536 * (h * exit) ≤ 31 * X := by
  have key : c * (1536 * (h * exit)) ≤ c * (31 * X) := by
    calc c * (1536 * (h * exit))
        = 1536 * h * (c * exit) := by ring
      _ ≤ 1536 * h * (b * Mtot) := Nat.mul_le_mul le_rfl hbalance
      _ = 1536 * (h * b) * Mtot := by ring
      _ ≤ 31 * c * Mtot := Nat.mul_le_mul hsafe le_rfl
      _ = c * (31 * Mtot) := by ring
      _ ≤ c * (31 * X) := Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hambient)
  exact Nat.le_of_mul_le_mul_left key (by omega)

/-- The safe-cone cap, fed directly from a `CycleMassDatum`: on a safe-cone cell with
ambient phase mass `M_tot ≤ X`, the normalized exposure `h·ExitMass` clears the
corrected capacity. -/
theorem CycleMassDatum.safeCone_nat (D : CycleMassDatum) {h Mtot X : ℕ}
    (hsafe : 1536 * (h * D.E.card) ≤ 31 * D.c)
    (hM : D.totalMass ≤ Mtot) (hX : Mtot ≤ X) :
    1536 * (h * D.exitMass) ≤ 31 * X :=
  cmb_safeCone_nat h D.exitMass D.E.card D.c Mtot X D.hc
    (D.exitMass_le_ambient hM) hsafe hX

/-- The overlap factor `h(c) = ⌊(r+c)/c⌋` of `def:ab-normalized-exposure` (11087). -/
def cmbOverlap (ctx : ActualFailureContext) (c : ℕ) : ℕ :=
  (ctx.n24CarryData.r + c) / c

/-- The normalized exposure `NExitMass_i = h(c)·ExitMass_i` of class `i`
(`def:ab-normalized-exposure`), with `ExitMass_i = emcFibreExitMass`. -/
def cmbNormalizedExposure (ctx : ActualFailureContext) (i : Fin 7) (c : ℕ) : ℕ :=
  cmbOverlap ctx c * emcFibreExitMass ctx i

/-- The mass-normalized balance datum bridges to the in-tree fibre exit mass: a
`CycleMassDatum` whose exit mass IS the class-`i` fibre exit mass, with ambient
phase mass `M_tot`, supplies the (R.2′) integer relation
`c·emcFibreExitMass ≤ b·M_tot`. -/
theorem cmb_balance_of_datum (ctx : ActualFailureContext) (i : Fin 7)
    (D : CycleMassDatum) (hexit : D.exitMass = emcFibreExitMass ctx i)
    {Mtot : ℕ} (hM : D.totalMass ≤ Mtot) :
    D.c * emcFibreExitMass ctx i ≤ D.E.card * Mtot := by
  rw [← hexit]; exact D.exitMass_le_ambient hM

/-- **THE OFF-PIN SAFE-CONE CAP (ctx form, ℕ)**: on a safe-cone recurrent cell the
v30 mass-normalized balance closes the (C1) exit cap for class `i` — the normalized
exposure clears `1536·NExitMass ≤ 31·X`.  `hbalance` is the (R.2′) Lane B output;
`hsafe` is the safe-cone cell condition; `hambient` is the disjoint-cell ambient
bound (Lane C / Appendix AD). -/
theorem cmb_offPin_safeCone_nat (ctx : ActualFailureContext) (i : Fin 7) {b c Mtot : ℕ}
    (hc : 1 ≤ c)
    (hbalance : c * emcFibreExitMass ctx i ≤ b * Mtot)
    (hsafe : 1536 * (cmbOverlap ctx c * b) ≤ 31 * c)
    (hambient : Mtot ≤ ctx.shell.X) :
    1536 * cmbNormalizedExposure ctx i c ≤ 31 * ctx.shell.X := by
  unfold cmbNormalizedExposure
  exact cmb_safeCone_nat (cmbOverlap ctx c) (emcFibreExitMass ctx i) b c Mtot
    ctx.shell.X hc hbalance hsafe hambient

/-- **THE OFF-PIN SAFE-CONE CAP (ctx form, real — the (C1) shape)**: the normalized
exposure sits below the corrected per-class capacity `emcCap = (31/1536)·X`.  This is
the exact target `ExitMassControlOffPin` / (C1) demands, on the safe cone, with the
total PHASE mass `M_tot` (mass-normalized) on the right rather than the false total
exit share. -/
theorem cmb_offPin_safeCone_cap (ctx : ActualFailureContext) (i : Fin 7) {b c Mtot : ℕ}
    (hc : 1 ≤ c)
    (hbalance : c * emcFibreExitMass ctx i ≤ b * Mtot)
    (hsafe : 1536 * (cmbOverlap ctx c * b) ≤ 31 * c)
    (hambient : Mtot ≤ ctx.shell.X) :
    (cmbNormalizedExposure ctx i c : ℝ) ≤ emcCap ctx := by
  have hnat := cmb_offPin_safeCone_nat ctx i hc hbalance hsafe hambient
  have hcast : (1536 : ℝ) * (cmbNormalizedExposure ctx i c : ℝ)
      ≤ 31 * (ctx.shell.X : ℝ) := by exact_mod_cast hnat
  unfold emcCap
  linarith

/-! ## Part 4.  Honest machine-readable status -/

/-- Machine-readable, honest status of the Lane B cycle-mass-balance pass. -/
def v30CycleMassBalanceStatus : List String :=
  [ "SUBJECT (PROVED): v30's mass-NORMALIZED cycle balance (Appendix R, " ++
      "prop:r-exit-share-closed 9203), NOT the proportional exit-share that the Lean " ++
      "program proved unfeedable (emfc_spacedShare_not_covering / EmcSpacedShareDatum). " ++
      "Around a recurrent cycle the event-indexed phase mass is conserved/normalized, " ++
      "so per-class exit mass is the b/c share of the TOTAL PHASE MASS M_tot, not of " ++
      "total exit mass.",
    "WORD-LEVEL MEASURE PRESERVATION (PROVED): the recurrent-cycle successor preserves " ++
      "the event-indexed window excess under a full cyclic step k -> k+c when the gap " ++
      "word is c-periodic (cmb_gapWindow_cyclic, cmb_windowExcess_cyclic - the word " ++
      "shadow of lem:r-cycle-map-preserves-measure 9110).  The per-step drift bracket " ++
      "cmb_windowExcess_drift_bracket reuses emcT_windowExcess_drift/_rev: in-cycle " ++
      "motion is charged the boundary gaps ALONE.  The binary gap-deviation " ++
      "classification (mdc_nonExit_weight_eq_zero) gives the interior leg: a " ++
      "band-following stretch carries zero exit charge (cmb_interior_devContent_zero, " ++
      "cmb_exits_carry_all) - 'clean in-cycle motion is uncharged' (I.3).",
    "CONSERVATION / BALANCE (PROVED, exact constants).  From the measure-preservation " ++
      "hypothesis CycleMassDatum.preserved (the ONE residual atom; = " ++
      "lem:r-cycle-map-preserves-measure) every phase carries equal mass " ++
      "(CycleMassDatum.uniform).  Hence: (i) CONSERVATION total = exit + interior " ++
      "(CycleMassDatum.conservation - entry mass = exit mass + interior contribution); " ++
      "(ii) the EXACT integer balance c*ExitMass = b*M_F (CycleMassDatum.balance, " ++
      "integer (R.1b)); (iii) the (R.2') ambient form c*ExitMass <= b*M_tot " ++
      "(CycleMassDatum.exitMass_le_ambient) and the faithful real form " ++
      "ExitMass <= (b/c)*M_tot + eps with ONE aggregate collar eps = o(X|I_j|) " ++
      "(CycleMassDatum.exitMass_le_share - no factor-c blow-up).",
    "SAFE-CONE PER-CLASS CAP FOR LANE C (PROVED).  cmb_safeCone_nat: from the balance " ++
      "c*exit <= b*M_tot, the safe-cone cell 1536*h*b <= 31*c " ++
      "(prop:ab-safe-cone-closed-summed), and the disjoint-cell ambient bound " ++
      "M_tot <= X (lem:ab-ambient-support-bound-summed), the normalized exposure " ++
      "h*exit clears 1536*(h*exit) <= 31*X.  ctx form: cmb_offPin_safeCone_nat / " ++
      "cmb_offPin_safeCone_cap give NExitMass = h(c)*emcFibreExitMass <= emcCap = " ++
      "(31/1536)*X, with h(c) = (r+c)/c (def:ab-normalized-exposure) - the exact (C1) " ++
      "shape, mass-normalized (M_tot on the right).",
    "CONE-LOCALITY / RESIDUAL ATOMS (the brief's question 3).  The balance is " ++
      "cone-local and provable from conservation alone; it does NOT use unsafe-core " ++
      "emptiness (Lane D) or (C1).  Named residuals abstracted as hypotheses: (a) " ++
      "CycleMassDatum.preserved = measure preservation (RISK c, " ++
      "lem:r-cycle-map-preserves-measure); (b) hambient M_tot <= X = disjoint-cell " ++
      "ambient-mass accounting (RISK b, lem:ab-ambient-support-bound-summed / " ++
      "lem:ad-summed-ambient-support, Lane C sums over disjoint cells); (c) hsafe " ++
      "1536*h*b <= 31*c = safe-cone cell classification (Appendix AB, Lane C).  The " ++
      "unsafe core (b=1, c>=64, 1536*h(c) > 31*c) is OUT of scope: EMPTY by Lane D " ++
      "(prop:ac-unsafe-core-empty), not capped by balance.",
    "NO sorry / admit / new axiom / native_decide.  #print axioms on every key " ++
      "declaration prints exactly [propext, Classical.choice, Quot.sound] or fewer." ]

/-- The status list is non-empty. -/
theorem v30CycleMassBalanceStatus_nonempty : v30CycleMassBalanceStatus ≠ [] := by
  unfold v30CycleMassBalanceStatus; simp

/-! ## Part 5.  Axiom audit -/

-- Word-level measure preservation (Part 1).
#print axioms cmb_gapWindow_cyclic
#print axioms cmb_windowExcess_cyclic
#print axioms cmb_windowExcess_drift_bracket
#print axioms cmb_interior_devContent_zero
#print axioms cmb_exits_carry_all
-- The phase-mass balance (Part 2).
#print axioms CycleMassDatum.uniform
#print axioms CycleMassDatum.conservation
#print axioms CycleMassDatum.balance
#print axioms CycleMassDatum.exitMass_le_ambient
#print axioms CycleMassDatum.exitMass_le_share
-- The safe-cone Lane C plug (Part 3).
#print axioms cmb_safeCone_nat
#print axioms CycleMassDatum.safeCone_nat
#print axioms cmb_balance_of_datum
#print axioms cmb_offPin_safeCone_nat
#print axioms cmb_offPin_safeCone_cap
-- Status (Part 4).
#print axioms v30CycleMassBalanceStatus_nonempty

end

end Erdos260
