import Erdos260.DeepCountingClosure
import Erdos260.CarryValuationFloor

/-!
# The class-1 alignment bit — the wave-20 named target
# (`DccClass1AlignedCountSupply v` at `v ≥ 1`)

Wave-20+ worker module on the class-1 aligned-count supplies of
`DeepCountingClosure` (the boosted width-gate interface over the v19 convergence
capstone).

## 1.  THE MECHANISM HUNT (honest verdict, refined)

The class-4 prototype (`carryVal2_ge_dyadicPart`, `sameSlice_gap_dvd_pow_dyadicPart`,
`routedFibre4_card_le_of_carryVal2_congruence`) gets its 2-adic spacing from the
SELF-REFERENTIAL KEY `k ↦ pair(carryVal2 k, k mod 2^{carryVal2 k})`: gap
divisibility is DEFINITIONAL on key-slices (`returnSelfRefKey_gapDiv`), and the
carry recurrence `R_{N+1} = 2R_N − Q(N+1)d_{N+1}` supplies the valuation floors.
The class-1 lane has NO such key in-tree: its only numeric structure is the exact
gap-window pin `64·gapWindow = 129L + 64` (`class1Fibre_gapWindow_eq` — a pin on
`L`, namely `64 ∣ L`, NOT on member positions), and its only position structure is
the residue pin mod an orbit period `c` (the `b4·⌈W/c⌉` count; the `63@10` parity
pin `k % 2 = 0` is its mod-2 shadow).  HOWEVER, the hunt surfaces TWO honest
positive mechanisms:

* **The density-free levels (PROVED, unconditional)**: at any table pair with
  `2^v·b4` strictly below the period `c`, the IN-TREE count `|fibre₁| ≤ b4·⌈W/c⌉`
  already yields the level-`v` pair supply — the residue-count deficit `c − 2^v·b4`
  absorbs every ceiling slack once `W ≥ 83` (in-tree from `r ≥ 82`).
  `c1abSupply_of_ceilCount` is the engine; instances
  `c1abPairSupply_103_51` (level 4!), `c1abPairSupply_107_53` (level 3),
  `c1abPairSupply_101_50` (level 3).  Through `dccClass1Pair_of_boostedAtom` the
  per-pair residuals move to `L > 1274739·2^v`: a genuine in-tree improvement at
  `(103,51)` (`20395824 > T = 17270663`) and `(107,53)` (`10197912 > T = 8172724`);
  at `(101,50)` the level-3 band is subsumed by `T = 10280156` (recorded honestly).
  At `(105,7)` (`c = 1 = b4`) NO level `v ≥ 1` is reachable by density — that pair
  genuinely needs the alignment bit.
* **The Q-even key-local partial (PROVED)**: on the Q-even stratum every pair of
  class-1 members sharing the self-referential key has an EVEN gap
  (`c1abSameKey_gap_even_of_Q_even`, from `carryVal2_pos_of_Q_even` +
  `returnSelfRefKey_gapDiv`).  This is key-local, not residue-local — it does NOT
  by itself produce the supply (the class-1 key count is unbounded in-tree);
  recorded as the honest Q-even fragment of the alignment bit.

No unconditional GLOBAL `v ≥ 1` supply is claimed: the named minimal atom is
`Class1AlignmentBitAtom` (below).

## 2.  THE SLACK FIX (the one-unit window-start slack, settled three ways)

`dccAlignedCount_of_pairwiseSpacing` lands at `W + 2^v − 1`, one unit above the
supply.  Fixed:

* **Window-start pin** (`c1abSpacedCount_le_of_offset`,
  `c1abAlignedCount_of_spacing_pinnedStart`): if every member sits at offset
  `≥ 2^v − 1` past the window start, the count tightens to EXACTLY `2^v·#S ≤ W`.
* **Residue-deficit absorption** (`c1abResidueSpacedCount_le` +
  `c1abSupply_of_residueSpacing`): with members spread over `≤ b` residue classes
  mod `c` and same-class gaps divisible by `c·2^v`, the count is
  `c·2^v·#S ≤ b·(W + c·2^v − 1)`; the pure-ℕ regime `b·(W + c·2^v − 1) ≤ c·W`
  yields the EXACT supply `2^v·#S ≤ W` — no window pin needed.
* **Slack-tolerant gate** (`c1abBoostGateSlack`): `dccBoostGate` itself tolerates
  an additive count slack `s` whenever `520093512·s ≤ 184·W` — the dst margin
  `31·2^24 − 408·1274739 = 184` pays for it, scale-invariantly in `2^v`; ctx form
  `c1abClass1Absorption_of_slackCount`, spacing-only consequence
  `c1abAbsorption_of_spacing_W_floor`.

## 3.  THE NAMED ATOM AND THE CONDITIONAL CHAIN (goal 3)

`Class1AlignmentBitAtom`: on every genuinely deep context (`L ≥ 1274740`,
`r ≥ 82`) SOME orbit period `c` carries (i) the one-alignment-bit spacing —
same-band-4-residue class-1 members have gaps divisible by `c·2` — and (ii) the
pure-ℕ density regime `b4·(W + 2c − 1) ≤ c·W`.  Chain, fully wired:
`c1abSupply_one_of_atom : Atom → DccClass1AlignedCountSupply 1`;
`c1abClass1Deep_field_of_atom : Atom → DccClass1DeepResidual 1 → (v19 class1Deep)`;
**headline** `c1abClass1Absorption_of_atom : Atom → ∀ ctx, L ≤ 2549478 →`
(corrected class-1 absorption) — the closed regime DOUBLES to `L ≤ 2549478`
exactly as the parent note predicted.

## 4.  SECONDARY: the tower/run band-reading tails (goal 4)

The gcd-of-periods lemma (`c1abPeriod_gcd`: orbit periods valid from index 1 are
closed under `Nat.gcd`) strengthens the wave-18 period floors from the WITNESS
period to ANY CERTIFIED period:

* `c1abClass5CycleNumeric_void`: a certified band-{1,4}-reading period `g ≤ 1536`
  voids `Class5CycleNumericCloses` OUTRIGHT (the witness's cycle band carries
  `≥ c/gcd(g,c)` residues, and the `31·2^24` margin kills every `gcd ≤ 1536`) —
  since every certified period in-tree is `≤ 98 ≪ 1537`, the run cycle horn is
  VOID at every certified band-reading pair, at every context.
* `c1abClass5BandHeavy_void`: same with band-1 reading and `g ≤ 6144`.
* `c1abClass2Cycle_block_le_certified`: a certified band-4-reading period `g`
  forces `m₀ ≤ g` on any `Class2CycleInequality` witness — the wave-18
  `m₀ ≤ (witness c)` upgraded to the CERTIFIED period; void form
  `c1abClass2Cycle_void_of_certified_short`.
* Instances at the recorded hard pair `(63,10)` (certified period 2 reading
  band 4): `c1abRunCycle_void_63_10`, `c1abRunLow_reduces_63_10`,
  `c1abTowerCycle_void_63_10`.

The `q ≥ 384` strata and the band-free horns keep their named residuals — the
floors do NOT void band-free closures (count `0` clears them trivially).

No `sorry`, no `admit`, no new `axiom`, no `native_decide`; additive only — no
existing module is edited; built standalone as `Erdos260.Class1AlignmentBit`.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

/-! ## Part 0.  ℕ helpers -/

/-- The ceiling-division covering bound `W ≤ ⌈W/c⌉·c`. -/
private theorem c1abCeil_mul_ge {W c : ℕ} (hc : 1 ≤ c) :
    W ≤ (W + c - 1) / c * c := by
  obtain ⟨m, hm⟩ : ∃ m, (W + c - 1) / c = m := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, (W + c - 1) % c = s := ⟨_, rfl⟩
  have hdm := Nat.div_add_mod (W + c - 1) c
  have hslt : (W + c - 1) % c < c := Nat.mod_lt _ (by omega)
  rw [hm, hs] at hdm
  rw [hs] at hslt
  rw [hm]
  have hcm : m * c = c * m := Nat.mul_comm m c
  omega

/-! ## Part 1.  The slack fix — the window-start pin and the residue-deficit
absorption -/

/-- **The offset-pinned spaced count**: a pairwise `d`-spaced set inside the window
`[F, F + W)` all of whose members sit at offset `≥ s` past the window start has
`d·#S ≤ W + d − 1 − s` — each offset unit pays back one unit of the ceiling
slack of `dccSpacedCount_le`. -/
theorem c1abSpacedCount_le_of_offset {S : Finset ℕ} {F d W s : ℕ} (hd : 1 ≤ d)
    (hwin : ∀ k ∈ S, F ≤ k ∧ k < F + W)
    (hpin : ∀ k ∈ S, F + s ≤ k)
    (hspace : ∀ k ∈ S, ∀ l ∈ S, k ≤ l → d ∣ (l - k)) :
    d * S.card ≤ W + d - 1 - s := by
  rcases Nat.lt_or_ge W s with hWs | hsW
  · have hS : S = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro k hk
      have h1 := (hwin k hk).2
      have h2 := hpin k hk
      omega
    rw [hS, Finset.card_empty, Nat.mul_zero]
    exact Nat.zero_le _
  · have h := dccSpacedCount_le (S := S) (a := F + s) (d := d) (W := W - s) hd
      (fun k hk => ⟨hpin k hk, by have := (hwin k hk).2; omega⟩) hspace
    have he : W - s + d - 1 = W + d - 1 - s := by omega
    rwa [he] at h

/-- **The slack-free aligned count (the one-unit fix, window-pin form)**: members
pinned at offset `≥ d − 1` past the window start give EXACTLY `d·#S ≤ W` — the
window start is pinned to the alignment class, and the `+ d − 1` slack of
`dccSpacedCount_le` vanishes. -/
theorem c1abSpacedCount_le_of_alignedStart {S : Finset ℕ} {F d W : ℕ} (hd : 1 ≤ d)
    (hwin : ∀ k ∈ S, F ≤ k ∧ k < F + W)
    (hpin : ∀ k ∈ S, F + (d - 1) ≤ k)
    (hspace : ∀ k ∈ S, ∀ l ∈ S, k ≤ l → d ∣ (l - k)) :
    d * S.card ≤ W := by
  have h := c1abSpacedCount_le_of_offset hd hwin hpin hspace
  have he : W + d - 1 - (d - 1) = W := by omega
  rwa [he] at h

/-- **The class-1 instance of the window-pin fix**: pairwise `2^v`-spaced fibre
members all at offset `≥ 2^v − 1` past `firstIndexAbove X` give the EXACT aligned
supply `2^v·#fibre₁ ≤ W` — the corrected form of
`dccAlignedCount_of_pairwiseSpacing` (which is one unit short without the pin). -/
theorem c1abAlignedCount_of_spacing_pinnedStart (ctx : ActualFailureContext) (v : ℕ)
    (hspace : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1,
      ∀ l ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1,
      k ≤ l → 2 ^ v ∣ (l - k))
    (hpin : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1,
      ctx.n24CarryData.carry.hits.firstIndexAbove ctx.shell.X + (2 ^ v - 1) ≤ k) :
    2 ^ v * (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (supportShell ctx.shell.d ctx.shell.X).card :=
  c1abSpacedCount_le_of_alignedStart Nat.one_le_two_pow
    (fun k hk => class1Fibre_mem_window ctx hk) hpin hspace

/-- **The residue-classed spaced count**: a set inside a width-`W` window whose
members carry residues `(k−1) % c` confined to `R` and whose SAME-residue gaps are
divisible by `d` has `d·#S ≤ #R·(W + d − 1)` — one `⌈W/d⌉` block count per
inhabited residue class. -/
theorem c1abResidueSpacedCount_le {S R : Finset ℕ} {F W c d : ℕ}
    (hc : 1 ≤ c) (hd : 1 ≤ d)
    (hwin : ∀ k ∈ S, F ≤ k ∧ k < F + W)
    (hres : ∀ k ∈ S, (k - 1) % c ∈ R)
    (hspace : ∀ k ∈ S, ∀ l ∈ S, k ≤ l → (k - 1) % c = (l - 1) % c → d ∣ (l - k)) :
    d * S.card ≤ R.card * (W + d - 1) := by
  classical
  rcases Nat.eq_zero_or_pos W with rfl | hW
  · have hS : S = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro k hk
      have := hwin k hk
      omega
    rw [hS, Finset.card_empty, Nat.mul_zero]
    exact Nat.zero_le _
  · have hmaps : ∀ k ∈ S, ((k - 1) % c, (k - F) / d)
        ∈ R ×ˢ Finset.range ((W + d - 1) / d) := by
      intro k hk
      rw [Finset.mem_product, Finset.mem_range]
      refine ⟨hres k hk, ?_⟩
      obtain ⟨hF, hkW⟩ := hwin k hk
      have he : (W + d - 1) / d = (W - 1) / d + 1 := by
        have h1 : W + d - 1 = (W - 1) + d := by omega
        rw [h1, Nat.add_div_right _ (by omega : 0 < d)]
      have h2 : (k - F) / d ≤ (W - 1) / d := Nat.div_le_div_right (by omega)
      omega
    have hkey : ∀ x ∈ S, ∀ y ∈ S, x ≤ y →
        (x - 1) % c = (y - 1) % c → (x - F) / d = (y - F) / d → x = y := by
      intro x hx y hy hxy hmod hdiv
      obtain ⟨m, hm⟩ := hspace x hx y hy hxy hmod
      have hxF := (hwin x hx).1
      have hyF := (hwin y hy).1
      have hyx : y - F = (x - F) + d * m := by omega
      have hdiv2 : (y - F) / d = (x - F) / d + m := by
        rw [hyx, Nat.add_mul_div_left _ _ (by omega : 0 < d)]
      have hm0 : m = 0 := by omega
      rw [hm0, Nat.mul_zero] at hm
      omega
    have hinj : Set.InjOn (fun k : ℕ => ((k - 1) % c, (k - F) / d)) S := by
      intro x hx y hy heq
      have hx' := Finset.mem_coe.mp hx
      have hy' := Finset.mem_coe.mp hy
      simp only [Prod.mk.injEq] at heq
      obtain ⟨hmod, hdiv⟩ := heq
      rcases le_total x y with hle | hle
      · exact hkey x hx' y hy' hle hmod hdiv
      · exact (hkey y hy' x hx' hle hmod.symm hdiv.symm).symm
    have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
    rw [Finset.card_product, Finset.card_range] at hcard
    calc d * S.card ≤ d * (R.card * ((W + d - 1) / d)) :=
          Nat.mul_le_mul le_rfl hcard
      _ = R.card * ((W + d - 1) / d * d) := by ring
      _ ≤ R.card * (W + d - 1) :=
          Nat.mul_le_mul le_rfl (Nat.div_mul_le_self _ _)

/-- **The class-1 residue-spaced count**: with an orbit period `c` valid from index
`1` and the alignment-bit spacing (same band-4 residue ⟹ gaps divisible by
`c·2^v`), the fibre count is `c·2^v·#fibre₁ ≤ b4·(W + c·2^v − 1)` — the boosted
cycle-density bound. -/
theorem c1abClass1Count_of_residueSpacing (ctx : ActualFailureContext) {c v : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hspace : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1,
      ∀ l ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1,
      k ≤ l → (k - 1) % c = (l - 1) % c → c * 2 ^ v ∣ (l - k)) :
    c * 2 ^ v * (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (class1Band4CycleBand ctx c).card
        * ((supportShell ctx.shell.d ctx.shell.X).card + c * 2 ^ v - 1) := by
  have h2v : 1 ≤ 2 ^ v := Nat.one_le_two_pow
  have hd : 1 ≤ c * 2 ^ v :=
    le_trans hc (Nat.le_mul_of_pos_right c (by omega))
  have hres : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1,
      (k - 1) % c ∈ (class1Band4CycleBand ctx c).image (fun j => j - 1) := by
    intro k hk
    have hk1 : 1 ≤ k := class1Fibre_start_pos ctx hk
    rw [Finset.mem_image]
    refine ⟨(k - 1) % c + 1, ?_, by omega⟩
    rw [mem_class1Band4CycleBand]
    have hmodlt : (k - 1) % c < c := Nat.mod_lt _ (by omega)
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    have heq := slopeOrbit_eq_residue hc hper hk1
    rw [← heq]
    exact class1Fibre_canonGap_eq ctx hk
  have h := c1abResidueSpacedCount_le
    (R := (class1Band4CycleBand ctx c).image (fun j => j - 1)) hc hd
    (fun k hk => class1Fibre_mem_window ctx hk)
    hres hspace
  exact le_trans h (Nat.mul_le_mul_right _ Finset.card_image_le)

/-- **The exact supply from the residue spacing (the slack fix, residue form)**:
the boosted count plus the pure-ℕ density regime `b4·(W + c·2^v − 1) ≤ c·W` give
the EXACT aligned supply `2^v·#fibre₁ ≤ W` — the residue-count deficit `c − b4`
absorbs every ceiling slack, no window pin needed. -/
theorem c1abSupply_of_residueSpacing (ctx : ActualFailureContext) {c v : ℕ}
    (hc : 1 ≤ c)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hspace : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1,
      ∀ l ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1,
      k ≤ l → (k - 1) % c = (l - 1) % c → c * 2 ^ v ∣ (l - k))
    (harith : (class1Band4CycleBand ctx c).card
        * ((supportShell ctx.shell.d ctx.shell.X).card + c * 2 ^ v - 1)
      ≤ c * (supportShell ctx.shell.d ctx.shell.X).card) :
    2 ^ v * (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card
      ≤ (supportShell ctx.shell.d ctx.shell.X).card := by
  have hcount := c1abClass1Count_of_residueSpacing ctx hc hper hspace
  refine Nat.le_of_mul_le_mul_left ?_ (show 0 < c by omega)
  calc c * (2 ^ v * (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card)
      = c * 2 ^ v * (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card := by
        ring
    _ ≤ (class1Band4CycleBand ctx c).card
        * ((supportShell ctx.shell.d ctx.shell.X).card + c * 2 ^ v - 1) := hcount
    _ ≤ c * (supportShell ctx.shell.d ctx.shell.X).card := harith

/-! ## Part 2.  The slack-tolerant boosted gate -/

/-- **The boosted width gate tolerates additive count slack**: `2^v·n ≤ W + s`
still clears the class-1 gate on the whole band `L ≤ 1274739·2^v` provided
`520093512·s ≤ 184·W` — the dst margin `31·2^24 − 408·1274739 = 184` pays for the
slack through the failure cap `2^24·W ≤ 17·X`, scale-invariantly in `2^v`. -/
theorem c1abBoostGateSlack {v n W L X s : ℕ}
    (hn : 2 ^ v * n ≤ W + s) (hW : 16777216 * W ≤ 17 * X)
    (hL : L ≤ 1274739 * 2 ^ v) (hs : 520093512 * s ≤ 184 * W) :
    24 * (n * L) ≤ 31 * X := by
  have hterm1 : 30593736 * (16777216 * W) ≤ 520093512 * X := by
    calc 30593736 * (16777216 * W) ≤ 30593736 * (17 * X) :=
          Nat.mul_le_mul le_rfl hW
      _ = 520093512 * X := by ring
  have hterm2 : 30593736 * (16777216 * s) ≤ 184 * X := by
    refine Nat.le_of_mul_le_mul_left ?_ (show 0 < 17 by norm_num)
    calc 17 * (30593736 * (16777216 * s))
        = 16777216 * (520093512 * s) := by ring
      _ ≤ 16777216 * (184 * W) := Nat.mul_le_mul le_rfl hs
      _ = 184 * (16777216 * W) := by ring
      _ ≤ 184 * (17 * X) := Nat.mul_le_mul le_rfl hW
      _ = 17 * (184 * X) := by ring
  have hpos : 0 < 16777216 * 2 ^ v := by positivity
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  calc (16777216 * 2 ^ v) * (24 * (n * L))
      = 24 * L * (16777216 * (2 ^ v * n)) := by ring
    _ ≤ 24 * L * (16777216 * (W + s)) :=
        Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hn)
    _ ≤ 24 * (1274739 * 2 ^ v) * (16777216 * (W + s)) :=
        Nat.mul_le_mul (Nat.mul_le_mul le_rfl hL) le_rfl
    _ = 2 ^ v * (30593736 * (16777216 * W) + 30593736 * (16777216 * s)) := by ring
    _ ≤ 2 ^ v * (520093512 * X + 184 * X) :=
        Nat.mul_le_mul le_rfl (Nat.add_le_add hterm1 hterm2)
    _ = (16777216 * 2 ^ v) * (31 * X) := by ring

/-- **The slack-count absorption (ctx form)**: a count cap `n` with
`2^v·n ≤ W + s` and the W-floor `520093512·s ≤ 184·W` closes the EXACT corrected
class-1 absorption on the whole band `L ≤ 1274739·2^v`. -/
theorem c1abClass1Absorption_of_slackCount (ctx : ActualFailureContext) {v n s : ℕ}
    (hcard : (routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card ≤ n)
    (hslack : 2 ^ v * n ≤ (supportShell ctx.shell.d ctx.shell.X).card + s)
    (hfloor : 520093512 * s ≤ 184 * (supportShell ctx.shell.d ctx.shell.X).card)
    (hL : shellLadderDepth ctx ≤ 1274739 * 2 ^ v) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hW := em_supportShell_strict ctx
  unfold emW at hW
  exact sreAbsorption_of_nat_gate ctx n hcard
    (c1abBoostGateSlack hslack (le_of_lt hW) hL hfloor)

/-- **Spacing alone + a W-floor close the absorption** — no window pin, no residue
structure: the pairwise-`2^v`-spaced count `2^v·#fibre₁ ≤ W + 2^v − 1`
(`dccAlignedCount_of_pairwiseSpacing`, one unit short of the supply) feeds the
slack gate once `520093512·(2^v − 1) ≤ 184·W`. -/
theorem c1abAbsorption_of_spacing_W_floor (ctx : ActualFailureContext) (v : ℕ)
    (hspace : ∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1,
      ∀ l ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1,
      k ≤ l → 2 ^ v ∣ (l - k))
    (hfloor : 520093512 * (2 ^ v - 1)
      ≤ 184 * (supportShell ctx.shell.d ctx.shell.X).card)
    (hL : shellLadderDepth ctx ≤ 1274739 * 2 ^ v) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  have hcount := dccAlignedCount_of_pairwiseSpacing ctx v hspace
  have hv1 : (1 : ℕ) ≤ 2 ^ v := Nat.one_le_two_pow
  have he : (supportShell ctx.shell.d ctx.shell.X).card + 2 ^ v - 1
      = (supportShell ctx.shell.d ctx.shell.X).card + (2 ^ v - 1) := by omega
  rw [he] at hcount
  exact c1abClass1Absorption_of_slackCount ctx le_rfl hcount hfloor hL

/-! ## Part 3.  The density-free levels — unconditional pair supplies from the
in-tree counts -/

/-- **The free-level engine**: any count cap `n ≤ b·⌈W/c⌉` yields the level-`v`
sparsity `2^v·n ≤ W` under the pure-ℕ density regime `2^v·b·(W + c − 1) ≤ c·W` —
the in-tree cycle-density counts ALREADY carry every level with `2^v·b` below
`c` (up to the explicit `W`-floor). -/
theorem c1abSupply_of_ceilCount {n b c W v : ℕ} (hc : 1 ≤ c)
    (hn : n ≤ b * ((W + c - 1) / c))
    (harith : 2 ^ v * b * (W + c - 1) ≤ c * W) :
    2 ^ v * n ≤ W := by
  refine Nat.le_of_mul_le_mul_left ?_ (show 0 < c by omega)
  calc c * (2 ^ v * n) ≤ c * (2 ^ v * (b * ((W + c - 1) / c))) :=
        Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hn)
    _ = 2 ^ v * b * ((W + c - 1) / c * c) := by ring
    _ ≤ 2 ^ v * b * (W + c - 1) :=
        Nat.mul_le_mul le_rfl (Nat.div_mul_le_self _ _)
    _ ≤ c * W := harith

/-- The pair-local aligned supplies are monotone downward in the level. -/
theorem c1abPairAlignedSupply_mono {qv Kv v v' : ℕ} (hvv : v' ≤ v)
    (h : DccClass1PairAlignedSupply qv Kv v) :
    DccClass1PairAlignedSupply qv Kv v' := by
  intro ctx hq hK hL hr
  have h1 := h ctx hq hK hL hr
  have hpow : 2 ^ v' ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) hvv
  exact le_trans (Nat.mul_le_mul hpow le_rfl) h1

/-- The global aligned supplies are monotone downward in the level. -/
theorem c1abAlignedSupply_mono {v v' : ℕ} (hvv : v' ≤ v)
    (h : DccClass1AlignedCountSupply v) :
    DccClass1AlignedCountSupply v' := by
  intro ctx hL hr
  have h1 := h ctx hL hr
  have hpow : 2 ^ v' ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) hvv
  exact le_trans (Nat.mul_le_mul hpow le_rfl) h1

/-- The in-tree deep-context width floor `W ≥ 83` (from `r ≥ 82` and
`r + 1 ≤ W`). -/
private theorem c1abWidth_ge_83 (ctx : ActualFailureContext)
    (hr : 82 ≤ ctx.n24CarryData.r) :
    83 ≤ (supportShell ctx.shell.d ctx.shell.X).card := by
  have h := cnlMulti_r_add_one_le_width ctx
  omega

/-- **`(101,50)` carries the level-3 supply FREE** (`c = 50`, `b4 = 3`,
`2^3·3 = 24 < 50`; regime `26·W ≥ 1176`, true from `W ≥ 83`). -/
theorem c1abPairSupply_101_50 : DccClass1PairAlignedSupply 101 50 3 := by
  intro ctx hq hK hL hr
  have hW := c1abWidth_ge_83 ctx hr
  refine c1abSupply_of_ceilCount (by norm_num)
    (sreClass1Count_of_datum_101_50 ctx hq hK) ?_
  have h24 : (2 : ℕ) ^ 3 * 3 = 24 := by norm_num
  rw [h24]
  omega

/-- **`(103,51)` carries the level-4 supply FREE** (`c = 28`, `b4 = 1`,
`2^4·1 = 16 < 28`; regime `12·W ≥ 432`, true from `W ≥ 83`). -/
theorem c1abPairSupply_103_51 : DccClass1PairAlignedSupply 103 51 4 := by
  intro ctx hq hK hL hr
  have hW := c1abWidth_ge_83 ctx hr
  refine c1abSupply_of_ceilCount (by norm_num)
    (sreClass1Count_of_datum_103_51 ctx hq hK) ?_
  have h16 : (2 : ℕ) ^ 4 * 1 = 16 := by norm_num
  rw [h16]
  omega

/-- **`(107,53)` carries the level-3 supply FREE** (`c = 53`, `b4 = 4`,
`2^3·4 = 32 < 53`; regime `21·W ≥ 1664`, true from `W ≥ 83` — sharp to three
units: `W ≥ 80` is needed). -/
theorem c1abPairSupply_107_53 : DccClass1PairAlignedSupply 107 53 3 := by
  intro ctx hq hK hL hr
  have hW := c1abWidth_ge_83 ctx hr
  refine c1abSupply_of_ceilCount (by norm_num)
    (sreClass1Count_of_datum_107_53 ctx hq hK) ?_
  have h32 : (2 : ℕ) ^ 3 * 4 = 32 := by norm_num
  rw [h32]
  omega

/-- The alignment bit (level 1) is FREE at `(101,50)`. -/
theorem c1abPairSupply_101_50_one : DccClass1PairAlignedSupply 101 50 1 :=
  c1abPairAlignedSupply_mono (by norm_num) c1abPairSupply_101_50

/-- The alignment bit (level 1) is FREE at `(103,51)`. -/
theorem c1abPairSupply_103_51_one : DccClass1PairAlignedSupply 103 51 1 :=
  c1abPairAlignedSupply_mono (by norm_num) c1abPairSupply_103_51

/-- The alignment bit (level 1) is FREE at `(107,53)`. -/
theorem c1abPairSupply_107_53_one : DccClass1PairAlignedSupply 107 53 1 :=
  c1abPairAlignedSupply_mono (by norm_num) c1abPairSupply_107_53

/-- **The `(103,51)` pair closure now needs ONLY the level-4 boosted atom**
(`L > 1274739·2^4 = 20395824 > T = 17270663` — the residual regime moves a genuine
factor `1.18` beyond the wave-18 table threshold; the supply side is PROVED). -/
theorem c1abPair_103_51_of_boostedAtom
    (hatom : DccClass1DeepPairAtomBoosted 103 51 17270663 4) :
    ∀ ctx : ActualFailureContext,
      (class1SlopeDatum ctx).q = 103 → (class1SlopeDatum ctx).K₀ = 51 →
      ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
          * ctx.n24CarryData.Y
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) :=
  dccClass1Pair_of_boostedAtom (cv := 28) (bv := 1) (by decide)
    c1abPairSupply_103_51 hatom

/-- **The `(107,53)` pair closure now needs ONLY the level-3 boosted atom**
(`L > 1274739·2^3 = 10197912 > T = 8172724` — factor `1.25` beyond the wave-18
threshold; the supply side is PROVED). -/
theorem c1abPair_107_53_of_boostedAtom
    (hatom : DccClass1DeepPairAtomBoosted 107 53 8172724 3) :
    ∀ ctx : ActualFailureContext,
      (class1SlopeDatum ctx).q = 107 → (class1SlopeDatum ctx).K₀ = 53 →
      ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
          * ctx.n24CarryData.Y
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) :=
  dccClass1Pair_of_boostedAtom (cv := 53) (bv := 4) (by decide)
    c1abPairSupply_107_53 hatom

/-- **`(101,50)` honest record**: the proved level-3 supply gives the boosted-atom
closure as well, but its band `1274739·2^3 = 10197912 < T = 10280156` is SUBSUMED
by the SRE table threshold — the residual there stays `L > T` (no in-tree level
`v ≥ 4` exists: `2^4·3 = 48` against `c = 50` demands `W ≥ 1176`, beyond the
in-tree floor `W ≥ 83`). -/
theorem c1abPair_101_50_of_boostedAtom
    (hatom : DccClass1DeepPairAtomBoosted 101 50 10280156 3) :
    ∀ ctx : ActualFailureContext,
      (class1SlopeDatum ctx).q = 101 → (class1SlopeDatum ctx).K₀ = 50 →
      ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
          * ctx.n24CarryData.Y
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) :=
  dccClass1Pair_of_boostedAtom (cv := 50) (bv := 3) (by decide)
    c1abPairSupply_101_50 hatom

/-! ## Part 4.  The named minimal alignment-bit atom and the conditional chain -/

/-- **THE NAMED MINIMAL ATOM (the class-1 alignment bit)**: on every genuinely deep
context (`L ≥ 1274740`, `r ≥ 82`) SOME orbit period `c` valid from index `1`
carries

* the ONE-ALIGNMENT-BIT SPACING — class-1 members in the SAME band-4 residue class
  mod `c` have gaps divisible by `c·2` (one extra bit on top of the residue pin);
* the pure-ℕ density regime `b4·(W + 2c − 1) ≤ c·W` (automatic at every fixed pair
  with `b4 < c` once `W` clears the explicit linear floor — e.g. from `W ≥ 83` for
  all three instance pairs above).

This is exactly what the wave-11/12 carry machinery proves on the class-4 lane
(`sameSlice_gap_dvd_pow_dyadicPart`) and what is MISSING on the class-1 lane. -/
def Class1AlignmentBitAtom : Prop :=
  ∀ ctx : ActualFailureContext,
    1274740 ≤ shellLadderDepth ctx → 82 ≤ ctx.n24CarryData.r →
    ∃ c : ℕ, 1 ≤ c ∧
      (∀ m, 1 ≤ m →
        slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
          = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m) ∧
      (class1Band4CycleBand ctx c).card
          * ((supportShell ctx.shell.d ctx.shell.X).card + c * 2 - 1)
        ≤ c * (supportShell ctx.shell.d ctx.shell.X).card ∧
      (∀ k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1,
        ∀ l ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1,
        k ≤ l → (k - 1) % c = (l - 1) % c → c * 2 ∣ (l - k))

/-- **The atom inhabits the level-1 aligned supply** — the wired first link of the
conditional chain. -/
theorem c1abSupply_one_of_atom (h : Class1AlignmentBitAtom) :
    DccClass1AlignedCountSupply 1 := by
  intro ctx hL hr
  obtain ⟨c, hc, hper, harith, hspace⟩ := h ctx hL hr
  refine c1abSupply_of_residueSpacing ctx (v := 1) hc hper ?_ ?_
  · intro k hk l hl hkl hres
    rw [pow_one]
    exact hspace k hk l hl hkl hres
  · rw [pow_one]
    exact harith

/-- **The atom + the level-1 residual rebuild the EXACT v19 `class1Deep` field** —
the wired second link (through `dccClass1Deep_field_of_boost`). -/
theorem c1abClass1Deep_field_of_atom (h : Class1AlignmentBitAtom)
    (hres : DccClass1DeepResidual 1) :
    ∀ ctx : ActualFailureContext,
      1274740 ≤ shellLadderDepth ctx → 82 ≤ ctx.n24CarryData.r →
      1 ≤ ctx.n24CarryData.r →
      (¬ ∃ cv bv Tv : ℕ,
        ((class1SlopeDatum ctx).q, (class1SlopeDatum ctx).K₀, cv, bv, Tv)
            ∈ sreClass1ThresholdTable
          ∧ shellLadderDepth ctx ≤ Tv) →
      ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
          * ctx.n24CarryData.Y
        ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) :=
  dccClass1Deep_field_of_boost (c1abSupply_one_of_atom h) hres

/-- **THE HEADLINE CONDITIONAL CHAIN (the parent's named target)**: the alignment
bit DOUBLES the closed class-1 regime to `L ≤ 2549478` — shallow contexts
(`L ≤ 1274739`) close parametrically, deep ones through the atom-supplied level-1
sparsity and the boosted gate. -/
theorem c1abClass1Absorption_of_atom (h : Class1AlignmentBitAtom)
    (ctx : ActualFailureContext)
    (hL : shellLadderDepth ctx ≤ 2549478) :
    ((routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1).card : ℝ)
        * ctx.n24CarryData.Y
      ≤ erdos260Constants.cStar * erdos260Constants.ξ / 6 * (ctx.shell.X : ℝ) := by
  rcases Nat.lt_or_ge (shellLadderDepth ctx) 1274740 with hsh | hdeep
  · exact dstClass1Absorption_of_depth_le ctx (by omega)
  · have hr := dstDeepShell_r_ge_82 ctx hdeep
    have hsup := c1abSupply_one_of_atom h ctx hdeep hr
    refine dccClass1Absorption_of_spacedCount ctx le_rfl hsup ?_
    have he : (1274739 : ℕ) * 2 ^ 1 = 2549478 := by norm_num
    omega

/-! ## Part 5.  The Q-even stratum — the key-local alignment bit (proved) -/

/-- **The Q-even key-local alignment bit (PROVED)**: on the Q-even stratum, any two
class-1 members sharing the self-referential M.2.1 key have an EVEN gap — the
carry recurrence forces `carryVal2 ≥ 1` everywhere (`carryVal2_pos_of_Q_even`) and
key equality forces `2^{carryVal2} ∣ gap` (`returnSelfRefKey_gapDiv`).  HONEST:
this is key-local, not residue-local; without an in-tree bound on the class-1 key
count it does NOT yield the level-1 supply — the honest Q-even fragment of the
alignment bit. -/
theorem c1abSameKey_gap_even_of_Q_even (ctx : ActualFailureContext)
    (hQ : 2 ∣ ctx.Q) {k l : ℕ}
    (hk : k ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hl : l ∈ routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1)
    (hkl : k < l)
    (hkey : returnSelfRefKey ctx k = returnSelfRefKey ctx l) :
    2 ∣ (l - k) := by
  have h1 : 1 ≤ carryVal2 ctx k :=
    carryVal2_pos_of_Q_even ctx hQ (class1Fibre_start_pos ctx hk)
  have h2 := returnSelfRefKey_gapDiv ctx hkey hkl
  refine dvd_trans ?_ h2
  calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
    _ ∣ 2 ^ carryVal2 ctx k := pow_dvd_pow 2 h1

/-! ## Part 6.  The tower/run band-reading tails — the certified-period floors

The gcd-of-periods lemma upgrades the wave-18 verdicts from the WITNESS period to
ANY CERTIFIED period: a certified band-reading period `g` forces the witness's
band count up to `c / gcd(g, c)`, and the same `31·2^24` margins then kill every
`gcd ≤ 1536` (run cycle), `gcd ≤ 6144` (run heavy), resp. force `m₀ ≤ g`
(tower). -/

/-- Iterated periods: a period `g` valid from index `1` gives every multiple. -/
private theorem c1abPeriod_iterate {q K₀ g : ℕ}
    (hper : ∀ m, 1 ≤ m → slopeOrbit q K₀ (m + g) = slopeOrbit q K₀ m) :
    ∀ t m, 1 ≤ m → slopeOrbit q K₀ (m + t * g) = slopeOrbit q K₀ m := by
  intro t
  induction t with
  | zero => intro m _; rw [Nat.zero_mul, Nat.add_zero]
  | succ t ih =>
      intro m hm
      have he : m + (t + 1) * g = m + t * g + g := by ring
      rw [he, hper (m + t * g) (by omega), ih m hm]

/-- **Orbit periods valid from index `1` are closed under `Nat.gcd`** — the
subtractive Euclid step: `c % g` is a period whenever `g` and `c` are (push the
argument forward by `(c/g)·g` and pull back by `c`). -/
theorem c1abPeriod_gcd {q K₀ : ℕ} (g c : ℕ) (hg : 1 ≤ g) (hc : 1 ≤ c)
    (hperg : ∀ m, 1 ≤ m → slopeOrbit q K₀ (m + g) = slopeOrbit q K₀ m)
    (hperc : ∀ m, 1 ≤ m → slopeOrbit q K₀ (m + c) = slopeOrbit q K₀ m) :
    ∀ m, 1 ≤ m → slopeOrbit q K₀ (m + Nat.gcd g c) = slopeOrbit q K₀ m := by
  rw [Nat.gcd_rec g c]
  rcases Nat.eq_zero_or_pos (c % g) with h0 | hpos
  · rw [h0, Nat.gcd_zero_left]
    exact hperg
  · have hmodper : ∀ m', 1 ≤ m' →
        slopeOrbit q K₀ (m' + c % g) = slopeOrbit q K₀ m' := by
      intro m' hm'
      calc slopeOrbit q K₀ (m' + c % g)
          = slopeOrbit q K₀ (m' + c % g + c / g * g) :=
            (c1abPeriod_iterate hperg (c / g) (m' + c % g)
              (le_trans hm' (Nat.le_add_right m' _))).symm
        _ = slopeOrbit q K₀ (m' + c) := by
            rw [Nat.add_assoc, Nat.mod_add_div' c g]
        _ = slopeOrbit q K₀ m' := hperc m' hm'
    exact c1abPeriod_gcd (c % g) g hpos hg hmodper hperg
termination_by g
decreasing_by exact Nat.mod_lt c (by omega)

/-- An arithmetic progression of `t` points landing in `B` forces `t ≤ #B`. -/
private theorem c1abAP_card_le {B : Finset ℕ} {j' gd t : ℕ} (hgd : 1 ≤ gd)
    (hmem : ∀ s, s < t → j' + s * gd ∈ B) : t ≤ B.card := by
  classical
  have hinj : Set.InjOn (fun s : ℕ => j' + s * gd) (Finset.range t) := by
    intro s₁ _ s₂ _ he
    have he' : j' + s₁ * gd = j' + s₂ * gd := he
    have hmul : s₁ * gd = s₂ * gd := Nat.add_left_cancel he'
    exact Nat.eq_of_mul_eq_mul_right (by omega) hmul
  have h := Finset.card_le_card_of_injOn _
    (fun s hs => hmem s (Finset.mem_range.mp hs)) hinj
  rwa [Finset.card_range] at h

/-- The split Section 26 run share, numerically: `c⋆·ξ/12 = 31/3072`. -/
private theorem c1abShare12_eq :
    erdos260Constants.cStar * erdos260Constants.ξ / 12 = 31 / 3072 := by
  have h1 : erdos260Constants.cStar = manuscriptCstar := rfl
  have h2 : erdos260Constants.ξ = manuscriptXi := rfl
  rw [h1, h2]
  unfold manuscriptCstar manuscriptXi
  norm_num

/-- The heavy half-share, numerically: `c⋆·ξ/24 = 31/6144`. -/
private theorem c1abShare24_eq :
    erdos260Constants.cStar * erdos260Constants.ξ / 24 = 31 / 6144 := by
  have h1 : erdos260Constants.cStar = manuscriptCstar := rfl
  have h2 : erdos260Constants.ξ = manuscriptXi := rfl
  rw [h1, h2]
  unfold manuscriptCstar manuscriptXi
  norm_num

/-- **The run-cycle horn is VOID at any certified band-{1,4}-reading period
`g ≤ 1536`**: every `Class5CycleNumericCloses` witness period `c` shares the
period `gd = gcd(g, c) ≤ 1536`, its cycle band carries `≥ c/gd` residues, hence
`(count·⌈W/c⌉)·gd ≥ W`, and the `31·2^24` margin
(`17·15297291 = 260053947 > 260046848 = 15.5·2^24`) refutes the scalar — the
wave-18 floor `c ≥ 1537` upgraded from the witness period to the CERTIFIED one. -/
theorem c1abClass5CycleNumeric_void (ctx : ActualFailureContext) {g j₀ : ℕ}
    (hg1 : 1 ≤ g) (hg : g ≤ 1536) (hj1 : 1 ≤ j₀) (hjg : j₀ ≤ g)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + g)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hband : canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j₀) = 1
      ∨ canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j₀) = 4) :
    ¬ Class5CycleNumericCloses ctx := by
  rintro ⟨c, hc, hperc, hineq⟩
  have hgd1 : 0 < Nat.gcd g c := Nat.gcd_pos_of_pos_left c (by omega)
  have hgdg : Nat.gcd g c ≤ g := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left g c)
  have hdvdc : Nat.gcd g c ∣ c := Nat.gcd_dvd_right g c
  have hpergd := c1abPeriod_gcd g c hg1 hc hper hperc
  have hj'1 : 1 ≤ (j₀ - 1) % Nat.gcd g c + 1 := Nat.le_add_left 1 _
  have hj'gd : (j₀ - 1) % Nat.gcd g c + 1 ≤ Nat.gcd g c :=
    Nat.mod_lt _ (by omega)
  have hval := slopeOrbit_eq_residue hgd1 hpergd hj1
  have hcount : c / Nat.gcd g c ≤ (class5CycleBand ctx c).card := by
    refine c1abAP_card_le (j' := (j₀ - 1) % Nat.gcd g c + 1) hgd1 ?_
    intro s hs
    rw [mem_class5CycleBand]
    obtain ⟨t, htc⟩ := hdvdc
    have htdiv : c / Nat.gcd g c = t := Nat.div_eq_of_eq_mul_right (by omega) htc
    rw [htdiv] at hs
    constructor
    · refine ⟨le_trans hj'1 (Nat.le_add_right _ _), ?_⟩
      calc (j₀ - 1) % Nat.gcd g c + 1 + s * Nat.gcd g c
          ≤ Nat.gcd g c + s * Nat.gcd g c := Nat.add_le_add_right hj'gd _
        _ = (s + 1) * Nat.gcd g c := by ring
        _ ≤ t * Nat.gcd g c := Nat.mul_le_mul_right _ (by omega)
        _ = Nat.gcd g c * t := Nat.mul_comm t _
        _ = c := htc.symm
    · have hiter := c1abPeriod_iterate hpergd s ((j₀ - 1) % Nat.gcd g c + 1) hj'1
      rw [hiter, ← hval]
      exact hband
  have hW1 : 1 ≤ (supportShell ctx.shell.d ctx.shell.X).card :=
    le_trans (Nat.le_add_left 1 ctx.n24CarryData.r) (cnlMulti_r_add_one_le_width ctx)
  have hkeyN : (supportShell ctx.shell.d ctx.shell.X).card
      ≤ (class5CycleBand ctx c).card
          * (((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c)
          * Nat.gcd g c := by
    calc (supportShell ctx.shell.d ctx.shell.X).card
        ≤ ((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c * c :=
          c1abCeil_mul_ge hc
      _ = ((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c
            * (c / Nat.gcd g c * Nat.gcd g c) := by
          rw [Nat.div_mul_cancel hdvdc]
      _ = c / Nat.gcd g c
            * (((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c)
            * Nat.gcd g c := by ring
      _ ≤ (class5CycleBand ctx c).card
            * (((supportShell ctx.shell.d ctx.shell.X).card + c - 1) / c)
            * Nat.gcd g c :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hcount)
  rw [carryWord_c0_eq, c1abShare12_eq, ← carryWord_shell_d_eq ctx,
    ← ActualFailureContext.shell_X ctx] at hineq
  have hM : (15297291 : ℝ) ≤ runDyadicMult ctx := by
    have h31 := tfaRunDyadicMult_ge_31L ctx
    have hLg : (493461 : ℝ) ≤ ((shellLadderDepth ctx : ℕ) : ℝ) := by
      exact_mod_cast shellLadderDepth_ge_493461 ctx
    linarith
  have hM0 : (0 : ℝ) ≤ runDyadicMult ctx := runDyadicMult_nonneg ctx
  set W' : ℕ := (supportShell ctx.shell.d ctx.shell.X).card with hW'def
  set NN : ℕ := (class5CycleBand ctx c).card * ((W' + c - 1) / c) with hNNdef
  set gd : ℕ := Nat.gcd g c with hgddef
  have hWR : (1 : ℝ) ≤ (W' : ℝ) := by exact_mod_cast hW1
  have hNgd : (W' : ℝ) ≤ (NN : ℝ) * (gd : ℝ) := by exact_mod_cast hkeyN
  have hgdR : (gd : ℝ) ≤ 1536 := by exact_mod_cast le_trans hgdg hg
  have hgd0 : (0 : ℝ) ≤ (gd : ℝ) := Nat.cast_nonneg _
  have hc0M : (0 : ℝ) ≤ 17 / 16777216 * runDyadicMult ctx :=
    mul_nonneg (by norm_num) hM0
  have h1 : 17 / 16777216 * runDyadicMult ctx * (W' : ℝ)
      ≤ 17 / 16777216 * runDyadicMult ctx * ((NN : ℝ) * (gd : ℝ)) :=
    mul_le_mul_of_nonneg_left hNgd hc0M
  have h2 : 17 / 16777216 * runDyadicMult ctx * ((NN : ℝ) * (gd : ℝ))
      = 17 / 16777216 * (NN : ℝ) * runDyadicMult ctx * (gd : ℝ) := by ring
  have h3 : 17 / 16777216 * (NN : ℝ) * runDyadicMult ctx * (gd : ℝ)
      ≤ 31 / 3072 * (W' : ℝ) * (gd : ℝ) :=
    mul_le_mul_of_nonneg_right hineq hgd0
  have h4 : 31 / 3072 * (W' : ℝ) * (gd : ℝ) ≤ 31 / 3072 * (W' : ℝ) * 1536 :=
    mul_le_mul_of_nonneg_left hgdR
      (mul_nonneg (by norm_num) (by linarith))
  have h5 : 17 / 16777216 * 15297291 * (W' : ℝ)
      ≤ 17 / 16777216 * runDyadicMult ctx * (W' : ℝ) := by
    have hMM : 17 / 16777216 * 15297291 ≤ 17 / 16777216 * runDyadicMult ctx :=
      mul_le_mul_of_nonneg_left hM (by norm_num)
    exact mul_le_mul_of_nonneg_right hMM (by linarith)
  have hfinal : 17 / 16777216 * 15297291 * (W' : ℝ)
      ≤ 31 / 3072 * (W' : ℝ) * 1536 := by
    calc 17 / 16777216 * 15297291 * (W' : ℝ)
        ≤ 17 / 16777216 * runDyadicMult ctx * (W' : ℝ) := h5
      _ ≤ 17 / 16777216 * runDyadicMult ctx * ((NN : ℝ) * (gd : ℝ)) := h1
      _ = 17 / 16777216 * (NN : ℝ) * runDyadicMult ctx * (gd : ℝ) := h2
      _ ≤ 31 / 3072 * (W' : ℝ) * (gd : ℝ) := h3
      _ ≤ 31 / 3072 * (W' : ℝ) * 1536 := h4
  linarith [hfinal, hWR]

/-- **The run band-heavy horn is VOID at any certified band-1-reading period
`g ≤ 6144`**: the witness's band-1 count is `≥ c/gcd(g,c)`, hence
`count·gcd ≥ c`, and the half-density margin
(`2·260053947 = 520107894 > 520093696 = 31·2^24`) refutes the scalar — the
wave-18 floor `c ≥ 6145` upgraded to the CERTIFIED period. -/
theorem c1abClass5BandHeavy_void (ctx : ActualFailureContext) {g j₀ : ℕ}
    (hg1 : 1 ≤ g) (hg : g ≤ 6144) (hj1 : 1 ≤ j₀) (hjg : j₀ ≤ g)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + g)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hband : canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j₀) = 1) :
    ¬ Class5BandHeavyNumericCloses ctx := by
  rintro ⟨c, hc, hperc, hcW, hb1, hheavy⟩
  have hgd1 : 0 < Nat.gcd g c := Nat.gcd_pos_of_pos_left c (by omega)
  have hgdg : Nat.gcd g c ≤ g := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left g c)
  have hdvdc : Nat.gcd g c ∣ c := Nat.gcd_dvd_right g c
  have hpergd := c1abPeriod_gcd g c hg1 hc hper hperc
  have hj'1 : 1 ≤ (j₀ - 1) % Nat.gcd g c + 1 := Nat.le_add_left 1 _
  have hj'gd : (j₀ - 1) % Nat.gcd g c + 1 ≤ Nat.gcd g c :=
    Nat.mod_lt _ (by omega)
  have hval := slopeOrbit_eq_residue hgd1 hpergd hj1
  have hcount : c / Nat.gcd g c ≤ (class5Band1CycleBand ctx c).card := by
    refine c1abAP_card_le (j' := (j₀ - 1) % Nat.gcd g c + 1) hgd1 ?_
    intro s hs
    rw [mem_class5Band1CycleBand]
    obtain ⟨t, htc⟩ := hdvdc
    have htdiv : c / Nat.gcd g c = t := Nat.div_eq_of_eq_mul_right (by omega) htc
    rw [htdiv] at hs
    constructor
    · refine ⟨le_trans hj'1 (Nat.le_add_right _ _), ?_⟩
      calc (j₀ - 1) % Nat.gcd g c + 1 + s * Nat.gcd g c
          ≤ Nat.gcd g c + s * Nat.gcd g c := Nat.add_le_add_right hj'gd _
        _ = (s + 1) * Nat.gcd g c := by ring
        _ ≤ t * Nat.gcd g c := Nat.mul_le_mul_right _ (by omega)
        _ = Nat.gcd g c * t := Nat.mul_comm t _
        _ = c := htc.symm
    · have hiter := c1abPeriod_iterate hpergd s ((j₀ - 1) % Nat.gcd g c + 1) hj'1
      rw [hiter, ← hval]
      exact hband
  have hkeyN : c ≤ (class5Band1CycleBand ctx c).card * Nat.gcd g c := by
    calc c = c / Nat.gcd g c * Nat.gcd g c := (Nat.div_mul_cancel hdvdc).symm
      _ ≤ (class5Band1CycleBand ctx c).card * Nat.gcd g c :=
          Nat.mul_le_mul_right _ hcount
  rw [carryWord_c0_eq, c1abShare24_eq] at hb1
  have hM : (15297291 : ℝ) ≤ runDyadicMult ctx := by
    have h31 := tfaRunDyadicMult_ge_31L ctx
    have hLg : (493461 : ℝ) ≤ ((shellLadderDepth ctx : ℕ) : ℝ) := by
      exact_mod_cast shellLadderDepth_ge_493461 ctx
    linarith
  have hM0 : (0 : ℝ) ≤ runDyadicMult ctx := runDyadicMult_nonneg ctx
  set B1 : ℕ := (class5Band1CycleBand ctx c).card with hB1def
  set gd : ℕ := Nat.gcd g c with hgddef
  have hcR : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  have hBgd : (c : ℝ) ≤ (B1 : ℝ) * (gd : ℝ) := by exact_mod_cast hkeyN
  have hgdR : (gd : ℝ) ≤ 6144 := by exact_mod_cast le_trans hgdg hg
  have hgd0 : (0 : ℝ) ≤ (gd : ℝ) := Nat.cast_nonneg _
  have hc0M : (0 : ℝ) ≤ 2 * (17 / 16777216 * runDyadicMult ctx) :=
    mul_nonneg (by norm_num) (mul_nonneg (by norm_num) hM0)
  have h1 : 2 * (17 / 16777216 * runDyadicMult ctx) * (c : ℝ)
      ≤ 2 * (17 / 16777216 * runDyadicMult ctx) * ((B1 : ℝ) * (gd : ℝ)) :=
    mul_le_mul_of_nonneg_left hBgd hc0M
  have h2 : 2 * (17 / 16777216 * runDyadicMult ctx) * ((B1 : ℝ) * (gd : ℝ))
      = 2 * ((B1 : ℝ) * (17 / 16777216 * runDyadicMult ctx)) * (gd : ℝ) := by ring
  have h3 : 2 * ((B1 : ℝ) * (17 / 16777216 * runDyadicMult ctx)) * (gd : ℝ)
      ≤ 31 / 6144 * (c : ℝ) * (gd : ℝ) :=
    mul_le_mul_of_nonneg_right hb1 hgd0
  have h4 : 31 / 6144 * (c : ℝ) * (gd : ℝ) ≤ 31 / 6144 * (c : ℝ) * 6144 :=
    mul_le_mul_of_nonneg_left hgdR
      (mul_nonneg (by norm_num) (by linarith))
  have h5 : 2 * (17 / 16777216 * 15297291) * (c : ℝ)
      ≤ 2 * (17 / 16777216 * runDyadicMult ctx) * (c : ℝ) := by
    have hMM : 2 * (17 / 16777216 * 15297291)
        ≤ 2 * (17 / 16777216 * runDyadicMult ctx) := by
      have := mul_le_mul_of_nonneg_left hM
        (show (0 : ℝ) ≤ 17 / 16777216 by norm_num)
      linarith
    exact mul_le_mul_of_nonneg_right hMM (by linarith)
  have hfinal : 2 * (17 / 16777216 * 15297291) * (c : ℝ)
      ≤ 31 / 6144 * (c : ℝ) * 6144 := by
    calc 2 * (17 / 16777216 * 15297291) * (c : ℝ)
        ≤ 2 * (17 / 16777216 * runDyadicMult ctx) * (c : ℝ) := h5
      _ ≤ 2 * (17 / 16777216 * runDyadicMult ctx) * ((B1 : ℝ) * (gd : ℝ)) := h1
      _ = 2 * ((B1 : ℝ) * (17 / 16777216 * runDyadicMult ctx)) * (gd : ℝ) := h2
      _ ≤ 31 / 6144 * (c : ℝ) * (gd : ℝ) := h3
      _ ≤ 31 / 6144 * (c : ℝ) * 6144 := h4
  linarith [hfinal, hcR]

/-- **The tower block bound at the CERTIFIED period**: a certified band-4-reading
period `g` forces `m₀ ≤ g` on ANY `Class2CycleInequality` witness — the wave-18
`dstTowerCycle_block_le_period` (`m₀ ≤ witness c`) upgraded through the gcd
period: the witness's band-4 count is `≥ c/gcd(g,c)`, so the density cannot beat
one hit per `gcd ≤ g` indices.  Pure ℕ. -/
theorem c1abClass2Cycle_block_le_certified (ctx : ActualFailureContext) {g j₀ : ℕ}
    (hg1 : 1 ≤ g) (hj1 : 1 ≤ j₀) (hjg : j₀ ≤ g)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + g)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hband : canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j₀) = 4)
    (h : Class2CycleInequality ctx) :
    towerSparsityBlock ctx ≤ g := by
  obtain ⟨c, hc, hperc, hineq⟩ := h
  have hgd1 : 0 < Nat.gcd g c := Nat.gcd_pos_of_pos_left c (by omega)
  have hgdg : Nat.gcd g c ≤ g := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left g c)
  have hdvdc : Nat.gcd g c ∣ c := Nat.gcd_dvd_right g c
  have hpergd := c1abPeriod_gcd g c hg1 hc hper hperc
  have hj'1 : 1 ≤ (j₀ - 1) % Nat.gcd g c + 1 := Nat.le_add_left 1 _
  have hj'gd : (j₀ - 1) % Nat.gcd g c + 1 ≤ Nat.gcd g c :=
    Nat.mod_lt _ (by omega)
  have hval := slopeOrbit_eq_residue hgd1 hpergd hj1
  have hcount : c / Nat.gcd g c
      ≤ towerBand4CycleCount (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ c := by
    unfold towerBand4CycleCount
    refine c1abAP_card_le (j' := (j₀ - 1) % Nat.gcd g c + 1) hgd1 ?_
    intro s hs
    rw [Finset.mem_filter, Finset.mem_Icc]
    obtain ⟨t, htc⟩ := hdvdc
    have htdiv : c / Nat.gcd g c = t := Nat.div_eq_of_eq_mul_right (by omega) htc
    rw [htdiv] at hs
    constructor
    · refine ⟨le_trans hj'1 (Nat.le_add_right _ _), ?_⟩
      calc (j₀ - 1) % Nat.gcd g c + 1 + s * Nat.gcd g c
          ≤ Nat.gcd g c + s * Nat.gcd g c := Nat.add_le_add_right hj'gd _
        _ = (s + 1) * Nat.gcd g c := by ring
        _ ≤ t * Nat.gcd g c := Nat.mul_le_mul_right _ (by omega)
        _ = Nat.gcd g c * t := Nat.mul_comm t _
        _ = c := htc.symm
    · have hiter := c1abPeriod_iterate hpergd s ((j₀ - 1) % Nat.gcd g c + 1) hj'1
      rw [hiter, ← hval]
      exact hband
  have hK1 : 1 ≤ shellWidth ctx := one_le_width ctx
  have hkeyN : shellWidth ctx
      ≤ towerBand4CycleCount (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ c
          * ((shellWidth ctx + c - 1) / c) * Nat.gcd g c := by
    calc shellWidth ctx ≤ (shellWidth ctx + c - 1) / c * c := c1abCeil_mul_ge hc
      _ = (shellWidth ctx + c - 1) / c * (c / Nat.gcd g c * Nat.gcd g c) := by
          rw [Nat.div_mul_cancel hdvdc]
      _ = c / Nat.gcd g c * ((shellWidth ctx + c - 1) / c) * Nat.gcd g c := by ring
      _ ≤ towerBand4CycleCount (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ c
            * ((shellWidth ctx + c - 1) / c) * Nat.gcd g c :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hcount)
  have h1 : towerSparsityBlock ctx * shellWidth ctx
      ≤ shellWidth ctx * Nat.gcd g c := by
    calc towerSparsityBlock ctx * shellWidth ctx
        ≤ towerSparsityBlock ctx
            * (towerBand4CycleCount (class1SlopeDatum ctx).q
                  (class1SlopeDatum ctx).K₀ c
                * ((shellWidth ctx + c - 1) / c) * Nat.gcd g c) :=
          Nat.mul_le_mul le_rfl hkeyN
      _ = towerSparsityBlock ctx
            * (towerBand4CycleCount (class1SlopeDatum ctx).q
                  (class1SlopeDatum ctx).K₀ c
                * ((shellWidth ctx + c - 1) / c)) * Nat.gcd g c := by ring
      _ ≤ shellWidth ctx * Nat.gcd g c := Nat.mul_le_mul_right _ hineq
  have h2 : towerSparsityBlock ctx ≤ Nat.gcd g c := by
    have h3 : towerSparsityBlock ctx * shellWidth ctx
        ≤ Nat.gcd g c * shellWidth ctx := by
      calc towerSparsityBlock ctx * shellWidth ctx
          ≤ shellWidth ctx * Nat.gcd g c := h1
        _ = Nat.gcd g c * shellWidth ctx := Nat.mul_comm _ _
    exact Nat.le_of_mul_le_mul_right h3 (by omega)
  exact le_trans h2 hgdg

/-- **Void form**: a certified band-4-reading period strictly below the sparsity
block kills the tower cycle horn outright. -/
theorem c1abClass2Cycle_void_of_certified_short (ctx : ActualFailureContext)
    {g j₀ : ℕ} (hg1 : 1 ≤ g) (hj1 : 1 ≤ j₀) (hjg : j₀ ≤ g)
    (hper : ∀ m, 1 ≤ m →
      slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + g)
        = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
    (hband : canonGap (class1SlopeDatum ctx).q
        (slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ j₀) = 4)
    (hshort : g < towerSparsityBlock ctx) :
    ¬ Class2CycleInequality ctx := by
  intro h
  have := c1abClass2Cycle_block_le_certified ctx hg1 hj1 hjg hper hband h
  omega

/-! ### The `(63,10)` instances — the recorded hard pair, settled on two lanes -/

/-- `(63,10)`: kernel return collision `K₃ = K₁` (period 2 from index 1,
cycle `17 → 5`). -/
private theorem c1abCycle_63_10 :
    slopeOrbit 63 10 (1 + 2) = slopeOrbit 63 10 1 := by decide

/-- `(63,10)`: index `2` reads band 4 (`K₂ = 5`, `40 ≤ 63 < 80`). -/
private theorem c1abBand_63_10 : canonGap 63 (slopeOrbit 63 10 2) = 4 := by decide

/-- **The run cycle horn is FALSE at every `(63,10)` context** — certified period
`2` reads band 4, and `2 ≤ 1536`. -/
theorem c1abRunCycle_void_63_10 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) (hK : (class1SlopeDatum ctx).K₀ = 10) :
    ¬ Class5CycleNumericCloses ctx := by
  refine c1abClass5CycleNumeric_void ctx (g := 2) (j₀ := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ ?_
  · rw [hq, hK]
    exact slopeOrbit_period_of_return c1abCycle_63_10
  · rw [hq, hK]
    exact Or.inr c1abBand_63_10

/-- **The `(63,10)` run horn reduces to the band-heavy half**: the demanded
`runNumericLow` disjunction collapses — any supply must close
`Class5BandHeavyNumericCloses` there (or refute the context). -/
theorem c1abRunLow_reduces_63_10 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) (hK : (class1SlopeDatum ctx).K₀ = 10)
    (h : Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx) :
    Class5BandHeavyNumericCloses ctx :=
  h.resolve_right (c1abRunCycle_void_63_10 ctx hq hK)

/-- **The tower cycle horn is FALSE at every `(63,10)` context with `m₀ ≥ 3`** —
i.e. on the WHOLE demanded `towerEnumLow` regime (`3 ≤ m₀`): the certified
band-4-reading period `2` caps `m₀ ≤ 2`. -/
theorem c1abTowerCycle_void_63_10 (ctx : ActualFailureContext)
    (hq : (class1SlopeDatum ctx).q = 63) (hK : (class1SlopeDatum ctx).K₀ = 10)
    (hm : 3 ≤ towerSparsityBlock ctx) :
    ¬ Class2CycleInequality ctx := by
  refine c1abClass2Cycle_void_of_certified_short ctx (g := 2) (j₀ := 2)
    (by norm_num) (by norm_num) (by norm_num) ?_ ?_ (by omega)
  · rw [hq, hK]
    exact slopeOrbit_period_of_return c1abCycle_63_10
  · rw [hq, hK]
    exact c1abBand_63_10

/-! ## Part 7.  Honest machine-readable status -/

/-- Honest machine-readable status of the class-1 alignment-bit module. -/
def class1AlignmentBitStatus : List String :=
  [ "SUBJECT (wave-20 named target): the class-1 alignment bit - the aligned " ++
      "count supplies DccClass1AlignedCountSupply v at v >= 1 of " ++
      "DeepCountingClosure (2^v * #fibre1 <= W on deep contexts L >= 1274740, " ++
      "r >= 82), whose level 1 doubles the closed class-1 regime to L <= 2549478.",
    "MECHANISM HUNT VERDICT (goal 1, honest): the class-4 prototype gets its " ++
      "2-adic spacing from the SELF-REFERENTIAL KEY pair(carryVal2 k, k mod " ++
      "2^carryVal2 k) - gap divisibility is definitional on key slices " ++
      "(returnSelfRefKey_gapDiv) and the carry recurrence R_{N+1} = 2 R_N - " ++
      "Q(N+1)d_{N+1} supplies the valuation floors (carryVal2_ge_dyadicPart, " ++
      "carryVal2_pos_of_Q_even).  NO class-1 analogue exists in-tree: the " ++
      "class-1 numeric side is the exact gap-window pin 64*gapWindow = 129L+64 " ++
      "(a pin on L - 64 | L - not on member positions), and the only position " ++
      "structure is the residue pin mod an orbit period c (b4*ceil(W/c); the " ++
      "63@10 parity pin k % 2 = 0 is its mod-2 shadow).  The GLOBAL v >= 1 " ++
      "supply remains conditional: named atom Class1AlignmentBitAtom.",
    "POSITIVE MECHANISM 1 (PROVED, unconditional - the density-free levels): " ++
      "at any table pair with 2^v*b4 strictly below the period c, the IN-TREE " ++
      "count |fibre1| <= b4*ceil(W/c) already yields the level-v pair supply - " ++
      "engine c1abSupply_of_ceilCount (pure N: n <= b*ceil(W/c) and " ++
      "2^v*b*(W+c-1) <= c*W give 2^v*n <= W), with W >= 83 in-tree from r >= 82 " ++
      "(cnlMulti_r_add_one_le_width).  Instances: (103,51) level 4 " ++
      "(c1abPairSupply_103_51, c=28, b4=1), (107,53) level 3 " ++
      "(c1abPairSupply_107_53, c=53, b4=4, sharp to three units: needs W >= 80), " ++
      "(101,50) level 3 (c1abPairSupply_101_50, c=50, b4=3); level-1 forms via " ++
      "c1abPairAlignedSupply_mono.  Through dccClass1Pair_of_boostedAtom the " ++
      "pair closures now need ONLY the boosted atoms: (103,51) residual moves " ++
      "to L > 20395824 > T = 17270663 (c1abPair_103_51_of_boostedAtom, genuine " ++
      "x1.18 gain) and (107,53) to L > 10197912 > T = 8172724 " ++
      "(c1abPair_107_53_of_boostedAtom, x1.25 gain); at (101,50) the level-3 " ++
      "band 10197912 is SUBSUMED by T = 10280156 (recorded honestly, " ++
      "c1abPair_101_50_of_boostedAtom).  At (105,7) (c = 1 = b4, the band-4 " ++
      "fixed point) NO density level v >= 1 exists - that pair genuinely needs " ++
      "the alignment bit.",
    "POSITIVE MECHANISM 2 (PROVED - the Q-even key-local alignment bit): on " ++
      "the Q-even stratum every pair of class-1 members sharing the " ++
      "self-referential key has an EVEN gap (c1abSameKey_gap_even_of_Q_even, " ++
      "from carryVal2_pos_of_Q_even + returnSelfRefKey_gapDiv).  HONEST: " ++
      "key-local, not residue-local - without an in-tree class-1 key-count " ++
      "bound it does NOT produce the supply; the Q-even stratum is NOT closed, " ++
      "only its key-local fragment.",
    "THE SLACK FIX (goal 2, settled three ways): the one-unit gap of " ++
      "dccAlignedCount_of_pairwiseSpacing (W + 2^v - 1 vs W) is closed by " ++
      "(a) the WINDOW-START PIN: members at offset >= 2^v - 1 past " ++
      "firstIndexAbove X give EXACTLY 2^v*#S <= W (c1abSpacedCount_le_of_offset " ++
      "- each offset unit pays back one slack unit - " ++
      "c1abSpacedCount_le_of_alignedStart, ctx form " ++
      "c1abAlignedCount_of_spacing_pinnedStart); (b) the RESIDUE-DEFICIT " ++
      "ABSORPTION: <= b residue classes mod c with same-class gaps divisible " ++
      "by c*2^v give c*2^v*#S <= b*(W + c*2^v - 1) (c1abResidueSpacedCount_le, " ++
      "class-1 form c1abClass1Count_of_residueSpacing), and the pure-N regime " ++
      "b*(W + c*2^v - 1) <= c*W yields the EXACT supply " ++
      "(c1abSupply_of_residueSpacing) - the deficit c - b absorbs all ceiling " ++
      "slacks, no pin needed; (c) the SLACK-TOLERANT GATE: dccBoostGate " ++
      "tolerates 2^v*n <= W + s whenever 520093512*s <= 184*W " ++
      "(c1abBoostGateSlack - the margin 31*2^24 - 408*1274739 = 184 pays, " ++
      "scale-invariantly in 2^v; ctx form c1abClass1Absorption_of_slackCount; " ++
      "spacing-only consequence c1abAbsorption_of_spacing_W_floor).  The " ++
      "supply statement itself needs NO restating.",
    "THE CONDITIONAL CHAIN (goal 3, fully wired): Class1AlignmentBitAtom " ++
      "(named minimal atom - on every deep context SOME period c carries the " ++
      "one-alignment-bit spacing - same band-4 residue class members have gaps " ++
      "divisible by c*2 - plus the pure-N density regime b4*(W + 2c - 1) <= " ++
      "c*W) => DccClass1AlignedCountSupply 1 (c1abSupply_one_of_atom) => the " ++
      "EXACT v19 class1Deep field with the level-1 residual " ++
      "(c1abClass1Deep_field_of_atom, via dccClass1Deep_field_of_boost) and " ++
      "THE HEADLINE: the corrected class-1 absorption closes on the WHOLE " ++
      "doubled regime L <= 2549478 (c1abClass1Absorption_of_atom - shallow " ++
      "via dstClass1Absorption_of_depth_le, deep via the boosted gate).",
    "TAIL REDUCTIONS (goal 4, secondary): the gcd-of-periods lemma " ++
      "(c1abPeriod_gcd - orbit periods valid from index 1 are closed under " ++
      "Nat.gcd, by subtractive Euclid) upgrades the wave-18 period floors from " ++
      "the WITNESS period to ANY CERTIFIED period: " ++
      "(a) c1abClass5CycleNumeric_void - a certified band-{1,4}-reading period " ++
      "g <= 1536 voids Class5CycleNumericCloses outright (witness count >= " ++
      "c/gcd, margin 17*15297291 = 260053947 > 260046848 = 15.5*2^24); since " ++
      "every certified period in-tree is <= 98 << 1537, the run cycle horn is " ++
      "VOID at every certified band-reading pair at every context; " ++
      "(b) c1abClass5BandHeavy_void - same with band-1 reading and g <= 6144 " ++
      "(margin 520107894 > 520093696); (c) c1abClass2Cycle_block_le_certified " ++
      "- a certified band-4-reading period g forces m0 <= g on any " ++
      "Class2CycleInequality witness (pure N; void form " ++
      "c1abClass2Cycle_void_of_certified_short).  Instances at the recorded " ++
      "hard pair (63,10) (certified period 2 reading band 4 at index 2): " ++
      "c1abRunCycle_void_63_10 (the run cycle horn is FALSE at every (63,10) " ++
      "context; runNumericLow there reduces to the band-heavy half, " ++
      "c1abRunLow_reduces_63_10) and c1abTowerCycle_void_63_10 (the tower " ++
      "horn is FALSE on the whole demanded m0 >= 3 regime).  HONEST: the " ++
      "floors do NOT void band-free closures (count 0 clears them trivially); " ++
      "the q >= 384 strata and the band-free horns keep their named residuals; " ++
      "per-pair instantiation across the enumerated tables is mechanical but " ++
      "only the (63,10) lane is instantiated here.",
    "WHAT REMAINS OPEN (the honest core): (a) Class1AlignmentBitAtom itself - " ++
      "no in-tree mechanism pins which c-blocks the class-1 members occupy " ++
      "(the orbit pin fixes residues mod c, the hit-gap pin fixes L mod 64, " ++
      "neither reaches the block parity); (b) the boosted per-pair atoms at " ++
      "L > 1274739*2^v; (c) the (105,7)-type dense pairs (b4 = c) where no " ++
      "density level exists and the atom is the only route; (d) the class-1 " ++
      "key-count bound that would convert the Q-even key-local bit into a " ++
      "supply; (e) the band-heavy horns at band-1-free pairs and everything " ++
      "q >= 384.",
    "HYGIENE: additive only - ONE new module, no existing file edited, not " ++
      "root-wired (built standalone as Erdos260.Class1AlignmentBit); no sorry " ++
      "/ admit / new axiom / native_decide; every key declaration passes " ++
      "#print axioms within [propext, Classical.choice, Quot.sound]." ]

/-- The status ledger is non-empty (honest, non-vacuous). -/
theorem class1AlignmentBitStatus_nonempty :
    class1AlignmentBitStatus ≠ [] := by
  simp [class1AlignmentBitStatus]

/-! ## Part 8.  Axiom-cleanliness audit
Every key declaration; expected axioms `[propext, Classical.choice, Quot.sound]`
or fewer. -/

#print axioms c1abSpacedCount_le_of_offset
#print axioms c1abSpacedCount_le_of_alignedStart
#print axioms c1abAlignedCount_of_spacing_pinnedStart
#print axioms c1abResidueSpacedCount_le
#print axioms c1abClass1Count_of_residueSpacing
#print axioms c1abSupply_of_residueSpacing
#print axioms c1abBoostGateSlack
#print axioms c1abClass1Absorption_of_slackCount
#print axioms c1abAbsorption_of_spacing_W_floor
#print axioms c1abSupply_of_ceilCount
#print axioms c1abPairAlignedSupply_mono
#print axioms c1abAlignedSupply_mono
#print axioms c1abPairSupply_101_50
#print axioms c1abPairSupply_103_51
#print axioms c1abPairSupply_107_53
#print axioms c1abPairSupply_101_50_one
#print axioms c1abPairSupply_103_51_one
#print axioms c1abPairSupply_107_53_one
#print axioms c1abPair_103_51_of_boostedAtom
#print axioms c1abPair_107_53_of_boostedAtom
#print axioms c1abPair_101_50_of_boostedAtom
#print axioms c1abSupply_one_of_atom
#print axioms c1abClass1Deep_field_of_atom
#print axioms c1abClass1Absorption_of_atom
#print axioms c1abSameKey_gap_even_of_Q_even
#print axioms c1abPeriod_gcd
#print axioms c1abClass5CycleNumeric_void
#print axioms c1abClass5BandHeavy_void
#print axioms c1abClass2Cycle_block_le_certified
#print axioms c1abClass2Cycle_void_of_certified_short
#print axioms c1abRunCycle_void_63_10
#print axioms c1abRunLow_reduces_63_10
#print axioms c1abTowerCycle_void_63_10
#print axioms class1AlignmentBitStatus_nonempty

end

end Erdos260
