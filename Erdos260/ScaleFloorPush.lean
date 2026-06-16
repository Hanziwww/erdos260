import Erdos260.Erdos260BootstrapCapstone

/-!
# Erdős 260 — the scale-floor push (wave 8): `X > 2^493460`, the last L-guard killed

Wave 6 (`CarryWordRigidity.lean`) proved the unconditional floor `X > 2^246736` by firing
the carry-rigidity count `X/g ≤ |supportShell|` (gap `g = 2L−25` from `Q < 2^(L−27)`)
against the sparsity `|supportShell| < c0·X`, `c0 = 17/2^24`, through
`supportShell_sparse_contradiction`, whose fire condition was `c0·(2g) ≤ 1`, i.e.
`17·(4L−50) ≤ 2^24`, i.e. `L ≤ 246736`.

## Where the factor of 2 was hiding (the honest audit of the wave-6 chain)

The gap bound itself is NOT loose at the formalized facts:

* **(i) window anchor**: the true product bound is
  `Q·(2X+2) ≤ (2^(L−27)−1)·(2^(L+1)+2) < 2^(2L−26)` — only `+1` over the wave-6
  `g = 2L−25`, NOT a halving to `~L−26`: `log₂(Q·(2X+2)) ≈ (L−27)+(L+1) = 2L−26`,
  and the odd part `u = Q` can genuinely be as large as `2^(L−27)`.  At the sharp fire
  condition below, `g = 2L−26` and `g = 2L−25` give the SAME floor (`L ≤ 493460` both
  ways), so we keep the simpler `g = 2L−25`.
* **(ii) run-start local tail**: `R_N = Q·2^N·(value tail past N)`, and after an all-zero
  run of length `h` the tail past `N` EQUALS the tail past `N+h` — so the "local tail"
  refinement is already exactly the proved chain `R_{N+h} = 2^h·R_N ≤ Q·(N+h+2)`
  (`integerCarry_add_of_zero_digits` + `integerCarry_bounds_of_rational_value`).  No gain
  without a lower bound on `R_N` stronger than the 2-adic `2^t ∣ R_N` + positivity, and
  none is formalized (the congruence `R_N ≡ 2^N·P (mod Q)` pins no usable size).
* **(iii) the carry envelope `R_N ≤ Q·(N+2)`**: it is the all-ones-tail bound
  `Σ_{j>N} j/2^j = (N+2)/2^N`; replacing it by the true (sparse) tail only restates the
  same inequality at the longer run ending at the next support element.  No asymptotic gain.

What IS loose is the **comparison side**: `supportShell_sparse_contradiction` pays a
factor 2 in `c0·(2g) ≤ 1` to absorb the floor division `⌊X/g⌋ ≥ X/(2g)`.  But on a dyadic
shell `X = 2^L` (`L ≥ 24`) the failure threshold `c0·X = 17·2^(L−24)` is an EXACT integer,
so `⌊X/g⌋ ≥ 17·2^(L−24)` holds exactly when `17·g·2^(L−24) ≤ 2^L`, i.e. **`17·g ≤ 2^24`**
(`supportShell_sparse_contradiction_sharp`).  The contradiction region doubles:

* generic gap `g = 2L−25`: fires iff `17·(2L−25) ≤ 2^24` iff `L ≤ 493460`
  (margin at `L = 493460`: `17·986895 = 16777215 ≤ 16777216` — short by exactly 1) —
  **THE PUSHED UNCONDITIONAL FLOOR `X > 2^493460`**
  (`scaleFloorPush_void_of_scale` / `scaleFloorPush_scale_lower` /
  `shellLadderDepth_ge_493461`).  This is the same effect on the floor that a slope-2 gap
  `g ≈ 2L` with the OLD fire condition would have needed `a = 2` for: the target
  `L > 2^24/(34·a) − …` at `a = 2` (`~493447`) is met and slightly exceeded.
* pinned-value gap `g = L+4` (odd part `u ≤ 7`): fires iff `17·(L+4) ≤ 2^24` iff
  `L ≤ 986891` — **the pinned-value floor moves `2^493443 → 2^986891`**
  (`scaleFloorPush_void_of_rep`, `shellValueDyadic_void_of_scale_push`,
  `towerFifthValue_void_of_scale_push`, `towerThirdsValue_void_of_scale_push`,
  `fixedFamilyHit_void_of_scale_push`).

## The harvest (the floor crosses BOTH remaining thresholds)

`493461 > 328966`: the tower shallow/deep threshold is crossed, so the LAST L-guard dies:

1. `n24_r_ge_thirtytwo`: **`r = ⌊κL⌋ ≥ 32` at every actual failure context** (sharp from
   the floor: `⌊17·493461/2^18⌋ = ⌊8388837/262144⌋ = 32`; `r ≥ 33` would need
   `L ≥ 508868`).  A fortiori `r ≥ 21` (`n24_r_ge_twentyone`), the bound the deep-shell
   guard used to buy (`r_ge_21_of_deep`).
2. `towerDeepGuard_unconditional`: **`towerShallowDepthBound = 328965 < L` at EVERY ctx**
   — every shell is deep.  Consequently `m₀ ≥ 2` everywhere
   (`two_le_towerSparsityBlock_everywhere`) and the direct shallow width-cap argument is
   dead at every ctx (`towerShallow_scalar_dead`).
3. The deep-shell guard is stripped everywhere it appears:
   * `Class2DeepShellResidual` ≃ the unguarded `∀ ctx, Class2DeepShellWindowData ctx`
     (`class2DeepShellData_ofResidual` / `class2DeepShellResidual_ofUnguarded` /
     `nonempty_class2Unguarded_iff_deepResidual`; Tower core
     `class2ActiveFloorCount_ofDeepData`, I.4.1 slot `class2TowerSubMass_ofDeepData`);
   * `TowerFixedPointResidual` / `TowerLeverResidual` lose their deep guard
     (`towerFixedPointResidual_iff_unguarded`, `towerLeverResidual_iff_unguarded`);
   * the wave-6 deep-lever guards `2^493443 < X` are now THEOREMS
     (`deepLeverGuard_unconditional`), so `DeepDyadicValueLever` /
     `DeepTowerFifthValueLever` / `DeepTowerThirdsValueLever` / `DeepFixedFamilyVoid`
     collapse onto the FULL levers (`dyadicValueLever_iff_deepScale` etc.); the honest
     successors now live at `2^986891` (`DeepDyadicValueLeverPush` etc., equivalences
     `deepDyadicValueLeverPush_iff` etc., endpoint
     `erdos260_of_deepDyadicValueLeverPush`).
4. **The collapsed successor surface** `Erdos260ScaleFloorPushResidual`: the wave-6.5/7
   `Erdos260FloorHarvestResidual` (= `Erdos260BootstrapResidual`) with the
   `towerShallowDepthBound < L` guards dropped from `towerEnumLow` / `towerEnumTail` —
   the last L-guard on the surface; all modulus-range and digit-side guards are
   floor-independent and stay.  Bridge `Erdos260ScaleFloorPushResidual.toFloorHarvest`,
   endpoint `erdos260_of_scaleFloorPush`, weakening witnesses
   `scaleFloorPushResidual_of_floorHarvestResidual` (= `…_of_bootstrapResidual`) and
   `scaleFloorPushResidual_of_rigidityResidual`, equivalences
   `nonempty_scaleFloorPush_iff_floorHarvest` / `nonempty_scaleFloorPush_iff_bootstrap`.

**What resists (honest)**: at `L ≥ 493461` the rigidity count `⌊X/(2L−25)⌋` drops below
`c0·X = 17·2^(L−24)` (`2^24/17 < 2L−25` there), the sparsity bound is consistent with the
carry rigidity, and the failure structure only guarantees failing shells at arbitrarily
LARGE `X`.  No context with `X > 2^493460` is claimed empty; the pushed deep levers at
`2^986891` remain genuinely open.

Additive only: no existing file is edited; only existing public lemmas are consumed.
No `sorry`, no `admit`, no new `axiom`, no `native_decide`.
-/

namespace Erdos260

noncomputable section

set_option linter.unusedVariables false

/-! ## Part 1.  The sharpened sparsity contradiction — the factor-2 slack removed

The wave-6 `supportShell_sparse_contradiction` demanded `c0·(2g) ≤ 1`.  On a dyadic shell
`X = 2^L` with `L ≥ 24` the threshold `c0·X = (17/2^24)·2^L = 17·2^(L−24)` is an exact
integer, so the count lower bound `⌊X/g⌋ ≤ |supportShell|` contradicts the failure cap
`|supportShell| < c0·X` exactly when `17·2^(L−24)·g ≤ 2^L`, i.e. `17·g ≤ 2^24`. -/

/-- **The sharp collision with the sparsity bound**: count lower bound `X/g` versus
`|supportShell d X| < c0·X` is absurd on the dyadic shell `X = 2^L` (`L ≥ 24`) as soon as
`17·g ≤ 2^24 = 16777216` — the wave-6 fire condition `c0·(2g) ≤ 1` (i.e. `34·g ≤ 2^24`)
carried a factor-2 floor-division slack that the exact integrality of `c0·X = 17·2^(L−24)`
removes. -/
theorem supportShell_sparse_contradiction_sharp {Q u t : ℕ} {P : ℤ} {d : ℕ → ℕ}
    {X g L : ℕ}
    (hQfact : Q = u * 2 ^ t) (hQ : 0 < Q) (hd : BinaryDigits d)
    (hnonterm : ¬ EventuallyZero d)
    (heta : realWeightedValue (natBinaryAsReal d) = (P : ℝ) / (Q : ℝ))
    (htX : t ≤ X) (hg : 0 < g)
    (hwin : (u : ℤ) * ((2 * X + 2 : ℕ) : ℤ) < 2 ^ g)
    (hXpow : X = 2 ^ L) (hL24 : 24 ≤ L)
    (hfire : 17 * g ≤ 16777216)
    (hfailure : ((supportShell d X).card : ℝ) < erdos260Constants.c0 * (X : ℝ)) :
    False := by
  have hlower := supportShell_card_lower_of_gap hQfact hQ hd hnonterm heta htX hg hwin
  have hsplitN : X = 16777216 * 2 ^ (L - 24) := by
    have h24 : (16777216 : ℕ) = 2 ^ 24 := by norm_num
    rw [hXpow, h24, ← pow_add]
    congr 1
    omega
  have hkg : 17 * 2 ^ (L - 24) * g ≤ X := by
    calc 17 * 2 ^ (L - 24) * g = 17 * g * 2 ^ (L - 24) := by ring
      _ ≤ 16777216 * 2 ^ (L - 24) := mul_le_mul_left hfire _
      _ = X := hsplitN.symm
  have hk_card : 17 * 2 ^ (L - 24) ≤ (supportShell d X).card :=
    le_trans ((Nat.le_div_iff_mul_le hg).mpr hkg) hlower
  have hc0X : erdos260Constants.c0 * (X : ℝ) = ((17 * 2 ^ (L - 24) : ℕ) : ℝ) := by
    rw [carryWord_c0_eq, hsplitN]
    push_cast
    ring
  have hcardR : ((17 * 2 ^ (L - 24) : ℕ) : ℝ) ≤ ((supportShell d X).card : ℝ) := by
    exact_mod_cast hk_card
  rw [hc0X] at hfailure
  linarith

/-! ## Part 2.  The pushed unconditional scale floor: `X > 2^493460` -/

/-- **THE PUSHED UNCONDITIONAL SCALE FLOOR**: no failing context exists at scale
`X ≤ 2^493460`.  Same gap `g = 2L−25` as wave 6 (from `Q < 2^(L−27)` and
`2X+2 ≤ 2^(L+2)`), but the SHARP fire condition `17·(2L−25) ≤ 2^24` holds iff
`L ≤ 493460` (margin at `L = 493460`: `17·986895 = 16777215 ≤ 16777216`, short by
exactly 1) — double the wave-6 region `L ≤ 246736`. -/
theorem scaleFloorPush_void_of_scale (ctx : ActualFailureContext)
    (hXle : ctx.X ≤ 2 ^ 493460) : False := by
  obtain ⟨L, hL⟩ := ctx.hXdyadic
  have hL28 : 28 ≤ L := carryWord_L_ge_28 ctx hL
  have hLle : L ≤ 493460 := by
    have h2 : (2 : ℕ) ^ L ≤ 2 ^ 493460 := by rw [← hL]; exact hXle
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2
  have hscale : 2 ^ 27 * ctx.Q < ctx.X := by
    simpa using shell_Q_scale_bound ctx
  have hQlt : ctx.Q < 2 ^ (L - 27) := by
    have hsplit : (2 : ℕ) ^ L = 2 ^ 27 * 2 ^ (L - 27) := by
      rw [← pow_add]
      congr 1
      omega
    have h := hscale
    rw [hL, hsplit] at h
    exact Nat.lt_of_mul_lt_mul_left h
  have hp2 : (2 : ℕ) ^ (L + 2) = 4 * 2 ^ L := by rw [pow_add]; ring
  have h1pow : 1 ≤ (2 : ℕ) ^ L := Nat.one_le_two_pow
  have hstep1 : 2 * ctx.X + 2 ≤ 2 ^ (L + 2) := by rw [hL]; omega
  have hwinN : ctx.Q * (2 * ctx.X + 2) < 2 ^ (2 * L - 25) := by
    calc ctx.Q * (2 * ctx.X + 2) ≤ ctx.Q * 2 ^ (L + 2) :=
          mul_le_mul_right hstep1 ctx.Q
      _ < 2 ^ (L - 27) * 2 ^ (L + 2) :=
          (Nat.mul_lt_mul_right (Nat.two_pow_pos (L + 2))).mpr hQlt
      _ = 2 ^ (2 * L - 25) := by
          rw [← pow_add]
          congr 1
          omega
  have hgpos : 0 < 2 * L - 25 := by omega
  have hfire : 17 * (2 * L - 25) ≤ 16777216 := by omega
  obtain ⟨P, hP⟩ := ctx.hrational
  exact supportShell_sparse_contradiction_sharp (Q := ctx.Q) (u := ctx.Q) (t := 0)
    (P := P) (d := ctx.d) (X := ctx.X) (g := 2 * L - 25) (L := L)
    (by simp) ctx.hQ ctx.hd ctx.hnonterm hP (Nat.zero_le _) hgpos
    (by exact_mod_cast hwinN) hL (by omega) hfire ctx.hfailure

/-- The pushed floor as a lower bound: EVERY failing context has `X > 2^493460`
(unconditional; strictly deeper than the wave-6 `2^246736` AND deeper than the wave-6
pinned-value floor `2^493443`). -/
theorem scaleFloorPush_scale_lower (ctx : ActualFailureContext) :
    2 ^ 493460 < ctx.X := by
  by_contra hcon
  push Not at hcon
  exact scaleFloorPush_void_of_scale ctx hcon

/-- Every failing context has ladder depth `L ≥ 493461` — the dyadic exponent pin from
`scaleFloorPush_scale_lower` (the pushed counterpart of `shellLadderDepth_ge_246737`). -/
theorem shellLadderDepth_ge_493461 (ctx : ActualFailureContext) :
    493461 ≤ shellLadderDepth ctx := by
  have hX := scaleFloorPush_scale_lower ctx
  have hXeq : ctx.shell.X = 2 ^ shellLadderDepth ctx :=
    Classical.choose_spec ctx.shell.hXdyadic
  rw [ActualFailureContext.shell_X] at hXeq
  rw [hXeq] at hX
  have : 493460 < shellLadderDepth ctx :=
    (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 hX
  omega

/-! ## Part 3.  The pushed pinned-value floor: `X > 2^986891` -/

/-- **The pushed pinned-value workhorse**: a value representation `P/(u·2^t)` with small
odd part `u ≤ 7` allows the t-free gap `g = L+4`, and the sharp fire condition
`17·(L+4) ≤ 2^24` holds iff `L ≤ 986891` (margin: `17·986895 = 16777215 ≤ 16777216`):
no such context exists at scale `X ≤ 2^986891` (wave 6 reached only `2^493443`). -/
theorem scaleFloorPush_void_of_rep (ctx : ActualFailureContext)
    {u t : ℕ} {P : ℤ}
    (hu7 : u ≤ 7) (hupos : 0 < u)
    (heta : realWeightedValue (natBinaryAsReal ctx.d)
      = (P : ℝ) / ((u * 2 ^ t : ℕ) : ℝ))
    (htX : t ≤ ctx.X)
    (hXle : ctx.X ≤ 2 ^ 986891) : False := by
  obtain ⟨L, hL⟩ := ctx.hXdyadic
  have hL28 : 28 ≤ L := carryWord_L_ge_28 ctx hL
  have hLle : L ≤ 986891 := by
    have h2 : (2 : ℕ) ^ L ≤ 2 ^ 986891 := by rw [← hL]; exact hXle
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2
  have hp4 : (2 : ℕ) ^ (L + 4) = 16 * 2 ^ L := by rw [pow_add]; norm_num [mul_comm]
  have h32 : 32 ≤ (2 : ℕ) ^ L := by
    calc (32 : ℕ) = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hwinN : u * (2 * ctx.X + 2) < 2 ^ (L + 4) := by
    calc u * (2 * ctx.X + 2) ≤ 7 * (2 * ctx.X + 2) :=
          mul_le_mul_left hu7 _
      _ < 2 ^ (L + 4) := by rw [hL]; omega
  exact supportShell_sparse_contradiction_sharp (Q := u * 2 ^ t) (u := u) (t := t)
    (P := P) (d := ctx.d) (X := ctx.X) (g := L + 4) (L := L)
    rfl (by positivity) ctx.hd ctx.hnonterm heta htX (by omega)
    (by exact_mod_cast hwinN) hL (by omega) (by omega) ctx.hfailure

/-- **The pushed dyadic-value voiding regime**: no failing context with `value = 1/2^t`
exists at scale `X ≤ 2^986891`. -/
theorem shellValueDyadic_void_of_scale_push (ctx : ActualFailureContext)
    (hXle : ctx.X ≤ 2 ^ 986891) : ¬ ShellValueDyadic ctx := by
  rintro ⟨t, hdy⟩
  have hvK := shell_value_eq_K₀_div_Q ctx
  have heq : (1 : ℝ) / 2 ^ t = ((class1SlopeDatum ctx).K₀ : ℝ) / (ctx.Q : ℝ) := by
    have h := hdy.symm.trans hvK
    simpa using h
  have hK1 : (1 : ℝ) ≤ ((class1SlopeDatum ctx).K₀ : ℝ) := by
    exact_mod_cast (class1SlopeDatum ctx).hK₀_pos
  have hQpos : (0 : ℝ) < (ctx.Q : ℝ) := by exact_mod_cast ctx.hQ
  have h2t : (0 : ℝ) < (2 : ℝ) ^ t := by positivity
  rw [div_eq_div_iff (by positivity) hQpos.ne'] at heq
  have hmul : (1 : ℝ) * 2 ^ t ≤ ((class1SlopeDatum ctx).K₀ : ℝ) * 2 ^ t :=
    mul_le_mul_of_nonneg_right hK1 h2t.le
  have hQge : (2 : ℝ) ^ t ≤ (ctx.Q : ℝ) := by linarith
  have hQgeN : 2 ^ t ≤ ctx.Q := by exact_mod_cast hQge
  have htX : t ≤ ctx.X := by
    have hlt : t < 2 ^ t := Nat.lt_two_pow_self
    have hQX : ctx.Q < ctx.X := carryWord_Q_lt_X ctx
    omega
  have heta' : realWeightedValue (natBinaryAsReal ctx.d)
      = ((1 : ℤ) : ℝ) / ((1 * 2 ^ t : ℕ) : ℝ) := by
    rw [show realWeightedValue (natBinaryAsReal ctx.d) = 1 / 2 ^ t from hdy]
    push_cast
    ring
  exact scaleFloorPush_void_of_rep ctx (by norm_num) (by norm_num) heta' htX hXle

/-- The pushed dyadic-value scale floor: any context with exactly-dyadic value has
`X > 2^986891`. -/
theorem shellValueDyadic_scale_lower_push (ctx : ActualFailureContext)
    (h : ShellValueDyadic ctx) : 2 ^ 986891 < ctx.X := by
  by_contra hcon
  push Not at hcon
  exact shellValueDyadic_void_of_scale_push ctx hcon h

/-- **The pushed fifth-value voiding regime**: no failing context with
`value = 1/(5·2^t)` exists at scale `X ≤ 2^986891`. -/
theorem towerFifthValue_void_of_scale_push (ctx : ActualFailureContext)
    (hXle : ctx.X ≤ 2 ^ 986891) (t : ℕ) :
    realWeightedValue (natBinaryAsReal ctx.shell.d) ≠ 1 / (5 * 2 ^ t) := by
  intro hval
  have hvK := shell_value_eq_K₀_div_Q ctx
  have heq : (1 : ℝ) / (5 * 2 ^ t)
      = ((class1SlopeDatum ctx).K₀ : ℝ) / (ctx.Q : ℝ) := by
    have h := hval.symm.trans hvK
    simpa using h
  have hK1 : (1 : ℝ) ≤ ((class1SlopeDatum ctx).K₀ : ℝ) := by
    exact_mod_cast (class1SlopeDatum ctx).hK₀_pos
  have hQpos : (0 : ℝ) < (ctx.Q : ℝ) := by exact_mod_cast ctx.hQ
  have h2t : (0 : ℝ) < (2 : ℝ) ^ t := by positivity
  rw [div_eq_div_iff (by positivity) hQpos.ne'] at heq
  have hmul : (1 : ℝ) * (5 * 2 ^ t)
      ≤ ((class1SlopeDatum ctx).K₀ : ℝ) * (5 * 2 ^ t) :=
    mul_le_mul_of_nonneg_right hK1 (by positivity)
  have hQge : (2 : ℝ) ^ t ≤ (ctx.Q : ℝ) := by linarith
  have hQgeN : 2 ^ t ≤ ctx.Q := by exact_mod_cast hQge
  have htX : t ≤ ctx.X := by
    have hlt : t < 2 ^ t := Nat.lt_two_pow_self
    have hQX : ctx.Q < ctx.X := carryWord_Q_lt_X ctx
    omega
  have heta' : realWeightedValue (natBinaryAsReal ctx.d)
      = ((1 : ℤ) : ℝ) / ((5 * 2 ^ t : ℕ) : ℝ) := by
    rw [show realWeightedValue (natBinaryAsReal ctx.d) = 1 / (5 * 2 ^ t) from hval]
    push_cast
    ring
  exact scaleFloorPush_void_of_rep ctx (by norm_num) (by norm_num) heta' htX hXle

/-- **The pushed thirds-value voiding regime**: no failing context with
`value = 2/(3·2^t)` exists at scale `X ≤ 2^986891`. -/
theorem towerThirdsValue_void_of_scale_push (ctx : ActualFailureContext)
    (hXle : ctx.X ≤ 2 ^ 986891) (t : ℕ) :
    realWeightedValue (natBinaryAsReal ctx.shell.d) ≠ 2 / (3 * 2 ^ t) := by
  intro hval
  have hvK := shell_value_eq_K₀_div_Q ctx
  have heq : (2 : ℝ) / (3 * 2 ^ t)
      = ((class1SlopeDatum ctx).K₀ : ℝ) / (ctx.Q : ℝ) := by
    have h := hval.symm.trans hvK
    simpa using h
  have hK1 : (1 : ℝ) ≤ ((class1SlopeDatum ctx).K₀ : ℝ) := by
    exact_mod_cast (class1SlopeDatum ctx).hK₀_pos
  have hQpos : (0 : ℝ) < (ctx.Q : ℝ) := by exact_mod_cast ctx.hQ
  have h2t : (0 : ℝ) < (2 : ℝ) ^ t := by positivity
  rw [div_eq_div_iff (by positivity) hQpos.ne'] at heq
  have hmul : (1 : ℝ) * (3 * 2 ^ t)
      ≤ ((class1SlopeDatum ctx).K₀ : ℝ) * (3 * 2 ^ t) :=
    mul_le_mul_of_nonneg_right hK1 (by positivity)
  have hQge : (2 : ℝ) ^ t ≤ (ctx.Q : ℝ) := by linarith
  have hQgeN : 2 ^ t ≤ ctx.Q := by exact_mod_cast hQge
  have htX : t ≤ ctx.X := by
    have hlt : t < 2 ^ t := Nat.lt_two_pow_self
    have hQX : ctx.Q < ctx.X := carryWord_Q_lt_X ctx
    omega
  have heta' : realWeightedValue (natBinaryAsReal ctx.d)
      = ((2 : ℤ) : ℝ) / ((3 * 2 ^ t : ℕ) : ℝ) := by
    rw [show realWeightedValue (natBinaryAsReal ctx.d) = 2 / (3 * 2 ^ t) from hval]
    push_cast
    ring
  exact scaleFloorPush_void_of_rep ctx (by norm_num) (by norm_num) heta' htX hXle

/-- **All five fixed families are void at scale `X ≤ 2^986891`** (pushed from the wave-6
`2^493443`): any fixed-family hit pins `oddpart(Q) ∈ {1,3,5,7}`. -/
theorem fixedFamilyHit_void_of_scale_push (ctx : ActualFailureContext)
    (hXle : ctx.X ≤ 2 ^ 986891) : ¬ FixedFamilyHit ctx := by
  intro hhit
  have hmem := fixedFamilyHit_oddpartQ_mem ctx hhit
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hu7 : ordCompl[2] ctx.Q ≤ 7 := by
    have hmem' : ordCompl[2] ctx.Q = 1 ∨ ordCompl[2] ctx.Q = 3
        ∨ ordCompl[2] ctx.Q = 5 ∨ ordCompl[2] ctx.Q = 7 := by simpa using hmem
    omega
  have hupos : 0 < ordCompl[2] ctx.Q := Nat.ordCompl_pos 2 ctx.hQ.ne'
  have hQfact : ctx.Q = ordCompl[2] ctx.Q * 2 ^ ctx.Q.factorization 2 := by
    have h := shell_Q_eq_oddpart_mul_pow ctx
    simpa using h
  obtain ⟨P, hP⟩ := ctx.hrational
  have heta' : realWeightedValue (natBinaryAsReal ctx.d)
      = (P : ℝ) / ((ordCompl[2] ctx.Q * 2 ^ ctx.Q.factorization 2 : ℕ) : ℝ) := by
    rw [← hQfact]
    exact hP
  have htX : ctx.Q.factorization 2 ≤ ctx.X := by
    have h2t : 2 ^ ctx.Q.factorization 2 ≤ ctx.Q := Nat.ordProj_le 2 ctx.hQ.ne'
    have hlt : ctx.Q.factorization 2 < 2 ^ ctx.Q.factorization 2 := Nat.lt_two_pow_self
    have hQX : ctx.Q < ctx.X := carryWord_Q_lt_X ctx
    omega
  exact scaleFloorPush_void_of_rep ctx hu7 hupos heta' htX hXle

/-- The pushed fixed-family scale floor: any of the five fixed families needs
`X > 2^986891`. -/
theorem fixedFamilyHit_scale_lower_push (ctx : ActualFailureContext)
    (h : FixedFamilyHit ctx) : 2 ^ 986891 < ctx.X := by
  by_contra hcon
  push Not at hcon
  exact fixedFamilyHit_void_of_scale_push ctx hcon h

/-! ## Part 4.  The descent-order harvest: `r ≥ 32`, every shell is deep -/

/-- **Every actual failure context has descent order `r ≥ 32`** — the exact arithmetic
of the pushed floor through the `r = ⌊κL⌋` pin: `L ≥ 493461` and `κ = 17/2^18` give
`κ·L ≥ 17·493461/262144 = 8388837/262144 > 32`, so `r = ⌊κL⌋ ≥ 32`.  (Sharp from the
floor: `⌊8388837/262144⌋ = 32`; `r ≥ 33` would need `L ≥ ⌈33·262144/17⌉ = 508868`.)
Strict sharpening of `n24_r_ge_sixteen` (wave 6.5). -/
theorem n24_r_ge_thirtytwo (ctx : ActualFailureContext) :
    32 ≤ ctx.n24CarryData.r := by
  have hL : (493461 : ℝ) ≤ (shellLadderDepth ctx : ℝ) := by
    exact_mod_cast shellLadderDepth_ge_493461 ctx
  have h32 : (32 : ℝ) ≤ manuscriptKappa * (shellLadderDepth ctx : ℝ) := by
    rw [towerKappa_eq]
    linarith
  rw [n24CarryData_r_eq_floor ctx]
  exact Nat.le_floor h32

/-- `r ≥ 21` everywhere — the unconditional form of the bound the tower deep-shell guard
used to buy (`r_ge_21_of_deep` needed `L > 328965`; the floor now supplies it). -/
theorem n24_r_ge_twentyone (ctx : ActualFailureContext) :
    21 ≤ ctx.n24CarryData.r :=
  le_trans (by norm_num) (n24_r_ge_thirtytwo ctx)

/-- **THE LAST L-GUARD IS DEAD**: `towerShallowDepthBound = 328965 < shellLadderDepth ctx`
at EVERY actual failure context (`493461 > 328965`) — every shell is a deep shell. -/
theorem towerDeepGuard_unconditional (ctx : ActualFailureContext) :
    towerShallowDepthBound < shellLadderDepth ctx := by
  have h := shellLadderDepth_ge_493461 ctx
  have hb : towerShallowDepthBound = 328965 := rfl
  omega

/-- The sparsity block is `m₀ ≥ 2` at every ctx (deep-shell consequence, now
unconditional). -/
theorem two_le_towerSparsityBlock_everywhere (ctx : ActualFailureContext) :
    2 ≤ towerSparsityBlock ctx :=
  two_le_towerSparsityBlock_of_deep ctx (towerDeepGuard_unconditional ctx)

/-- The direct shallow width-cap scalar `c₀·(2ε·L) ≤ ξ/6` is FALSE at every actual
failure context — the shallow branch of the tower shallow/deep split is dead weight. -/
theorem towerShallow_scalar_dead (ctx : ActualFailureContext) :
    ¬ erdos260Constants.c0 * (2 * manuscriptEps * (shellLadderDepth ctx : ℝ))
        ≤ erdos260Constants.ξ / 6 := by
  apply towerShallow_scalar_false_of_deep
  have h : (493461 : ℝ) ≤ (shellLadderDepth ctx : ℝ) := by
    exact_mod_cast shellLadderDepth_ge_493461 ctx
  linarith

/-! ## Part 5.  The class-2 deep-shell residual loses its guard -/

/-- Strip the (now-theorem) deep guard from a `Class2DeepShellResidual` provider: window
data at EVERY ctx. -/
def class2DeepShellData_ofResidual (R : Class2DeepShellResidual)
    (ctx : ActualFailureContext) : Class2DeepShellWindowData ctx :=
  R ctx (towerDeepGuard_unconditional ctx)

/-- The unguarded window data rebuilds the guarded residual (weakening witness). -/
def class2DeepShellResidual_ofUnguarded
    (R : ∀ ctx : ActualFailureContext, Class2DeepShellWindowData ctx) :
    Class2DeepShellResidual := fun ctx _ => R ctx

/-- **The guarded and unguarded class-2 deep surfaces are EQUIVALENT** — the deep-shell
guard carries no content at the pushed floor. -/
theorem nonempty_class2Unguarded_iff_deepResidual :
    Nonempty (∀ ctx : ActualFailureContext, Class2DeepShellWindowData ctx)
      ↔ Nonempty Class2DeepShellResidual :=
  ⟨fun ⟨R⟩ => ⟨class2DeepShellResidual_ofUnguarded R⟩,
   fun ⟨R⟩ => ⟨class2DeepShellData_ofResidual R⟩⟩

/-- The full V3/P9 Tower field from the unguarded deep window data alone — the shallow
branch of `class2ActiveFloorCount_ofShallowDeep` never fires at the pushed floor. -/
def class2ActiveFloorCount_ofDeepData
    (R : ∀ ctx : ActualFailureContext, Class2DeepShellWindowData ctx)
    (ctx : ActualFailureContext) : Class2ActiveFloorCount ctx :=
  (R ctx).toActiveFloorCount

/-- The routed I.4.1 class-2 sub-mass slot from the unguarded deep window data. -/
theorem class2TowerSubMass_ofDeepData
    (R : ∀ ctx : ActualFailureContext, Class2DeepShellWindowData ctx)
    (ctx : ActualFailureContext) :
    routedClassMassOf ctx.n24CarryData (genuineChargeRoute ctx) 2
      ≤ erdos260Constants.ξ * (ctx.shell.X : ℝ) / 6 :=
  (class2ActiveFloorCount_ofDeepData R ctx).htowerSubMass

/-! ## Part 6.  The lever-lineage deep guards die too -/

/-- The wave-4 `TowerFixedPointResidual` loses its deep-shell guard: equivalent to the
unguarded escape-to-inequality demand. -/
theorem towerFixedPointResidual_iff_unguarded :
    TowerFixedPointResidual
      ↔ ∀ ctx : ActualFailureContext, TowerEscape ctx → Class2CycleInequality ctx :=
  ⟨fun h ctx => h ctx (towerDeepGuard_unconditional ctx), fun h ctx _ => h ctx⟩

/-- The wave-5 `TowerLeverResidual` loses its deep-shell guard likewise. -/
theorem towerLeverResidual_iff_unguarded :
    TowerLeverResidual
      ↔ ∀ ctx : ActualFailureContext, TowerEscapeLever ctx → Class2CycleInequality ctx :=
  ⟨fun h ctx => h ctx (towerDeepGuard_unconditional ctx), fun h ctx _ => h ctx⟩

/-- The wave-6 deep-lever scale guard `2^493443 < X` is now a THEOREM at every ctx
(`493443 < 493460`). -/
theorem deepLeverGuard_unconditional (ctx : ActualFailureContext) :
    2 ^ 493443 < ctx.X :=
  lt_trans ((Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mpr (by norm_num))
    (scaleFloorPush_scale_lower ctx)

/-- The wave-6 `DeepDyadicValueLever` collapses onto the FULL lever — its scale guard is
dead at the pushed floor. -/
theorem dyadicValueLever_iff_deepScale :
    DyadicValueLever ↔ DeepDyadicValueLever :=
  ⟨fun h ctx _ => h ctx, dyadicValueLever_of_deepScale⟩

/-- The wave-6 `DeepTowerFifthValueLever` collapses onto the full fifth lever. -/
theorem towerFifthValueLever_iff_deepScale :
    TowerFifthValueLever ↔ DeepTowerFifthValueLever :=
  ⟨fun h ctx _ => h ctx, towerFifthValueLever_of_deepScale⟩

/-- The wave-6 `DeepTowerThirdsValueLever` collapses onto the full thirds lever. -/
theorem towerThirdsValueLever_iff_deepScale :
    TowerThirdsValueLever ↔ DeepTowerThirdsValueLever :=
  ⟨fun h ctx _ => h ctx, towerThirdsValueLever_of_deepScale⟩

/-- The wave-6 `DeepFixedFamilyVoid` collapses onto the full family voiding. -/
theorem fixedFamilyVoid_iff_deepScale :
    (∀ ctx : ActualFailureContext, ¬ FixedFamilyHit ctx) ↔ DeepFixedFamilyVoid :=
  ⟨fun h ctx _ => h ctx, fixedFamilyHit_void_of_deepScale⟩

/-! ## Part 7.  The pushed deep levers at `2^986891` -/

/-- **The pushed deep dyadic-value lever** — the residual successor of
`DyadicValueLever` at the PUSHED pinned-value floor: the exclusion is demanded only at
scales `X > 2^986891` (the regime `X ≤ 2^986891` is closed unconditionally by
`shellValueDyadic_void_of_scale_push`). -/
def DeepDyadicValueLeverPush : Prop :=
  ∀ ctx : ActualFailureContext, 2 ^ 986891 < ctx.X → ¬ ShellValueDyadic ctx

/-- The pushed deep lever discharges the full lever. -/
theorem dyadicValueLever_of_deepScalePush (h : DeepDyadicValueLeverPush) :
    DyadicValueLever := by
  intro ctx hdy
  by_cases hX : 2 ^ 986891 < ctx.X
  · exact h ctx hX hdy
  · exact shellValueDyadic_void_of_scale_push ctx (not_lt.mp hX) hdy

/-- The pushed deep lever is EQUIVALENT to the full lever (and hence to the wave-6 deep
lever): only the tail `X > 2^986891` carries content. -/
theorem dyadicValueLever_iff_deepScalePush :
    DyadicValueLever ↔ DeepDyadicValueLeverPush :=
  ⟨fun h ctx _ => h ctx, dyadicValueLever_of_deepScalePush⟩

/-- The pushed and wave-6 deep dyadic levers are equivalent (both collapse onto the full
lever; the pushed one demands strictly less). -/
theorem deepDyadicValueLeverPush_iff :
    DeepDyadicValueLeverPush ↔ DeepDyadicValueLever :=
  ⟨fun h ctx _ => dyadicValueLever_of_deepScalePush h ctx,
   fun h ctx _ => dyadicValueLever_of_deepScale h ctx⟩

/-- The pushed deep fifth-value lever. -/
def DeepTowerFifthValueLeverPush : Prop :=
  ∀ ctx : ActualFailureContext, 2 ^ 986891 < ctx.X →
    ∀ t : ℕ, realWeightedValue (natBinaryAsReal ctx.shell.d) ≠ 1 / (5 * 2 ^ t)

/-- The pushed deep fifth lever discharges the full fifth lever. -/
theorem towerFifthValueLever_of_deepScalePush (h : DeepTowerFifthValueLeverPush) :
    TowerFifthValueLever := by
  intro ctx t hval
  by_cases hX : 2 ^ 986891 < ctx.X
  · exact h ctx hX t hval
  · exact towerFifthValue_void_of_scale_push ctx (not_lt.mp hX) t hval

/-- The pushed deep thirds-value lever. -/
def DeepTowerThirdsValueLeverPush : Prop :=
  ∀ ctx : ActualFailureContext, 2 ^ 986891 < ctx.X →
    ∀ t : ℕ, realWeightedValue (natBinaryAsReal ctx.shell.d) ≠ 2 / (3 * 2 ^ t)

/-- The pushed deep thirds lever discharges the full thirds lever. -/
theorem towerThirdsValueLever_of_deepScalePush (h : DeepTowerThirdsValueLeverPush) :
    TowerThirdsValueLever := by
  intro ctx t hval
  by_cases hX : 2 ^ 986891 < ctx.X
  · exact h ctx hX t hval
  · exact towerThirdsValue_void_of_scale_push ctx (not_lt.mp hX) t hval

/-- The pushed deep family voiding — ONE successor Prop for all five fixed families,
demanded only at `X > 2^986891`. -/
def DeepFixedFamilyVoidPush : Prop :=
  ∀ ctx : ActualFailureContext, 2 ^ 986891 < ctx.X → ¬ FixedFamilyHit ctx

/-- The pushed deep family voiding discharges the FULL family voiding. -/
theorem fixedFamilyHit_void_of_deepScalePush (h : DeepFixedFamilyVoidPush)
    (ctx : ActualFailureContext) : ¬ FixedFamilyHit ctx := by
  by_cases hX : 2 ^ 986891 < ctx.X
  · exact h ctx hX
  · exact fixedFamilyHit_void_of_scale_push ctx (not_lt.mp hX)

/-- The pushed and wave-6 deep family voidings are equivalent. -/
theorem deepFixedFamilyVoidPush_iff :
    DeepFixedFamilyVoidPush ↔ DeepFixedFamilyVoid :=
  ⟨fun h ctx _ => fixedFamilyHit_void_of_deepScalePush h ctx,
   fun h ctx _ => fixedFamilyHit_void_of_deepScale h ctx⟩

/-- **The pushed deep-lever residual**: the deep dyadic-value lever demanded only at
`X > 2^986891` plus the lever-shrunk wave-5 surfaces (successor of the wave-6
`Erdos260DeepLeverResidual`, whose `2^493443` threshold this halves in demand). -/
structure Erdos260DeepLeverPushResidual where
  /-- The pushed deep dyadic-value lever. -/
  deepLever : DeepDyadicValueLeverPush
  /-- The remaining wave-5 surfaces, given the discharged lever. -/
  surfaces : DyadicValueLever → Erdos260DyadicLeverResidual

namespace Erdos260DeepLeverPushResidual

/-- Discharge the pushed deep lever into the wave-5 lever residual. -/
def toLeverResidual (R : Erdos260DeepLeverPushResidual) : Erdos260DyadicLeverResidual :=
  R.surfaces (dyadicValueLever_of_deepScalePush R.deepLever)

/-- The final statement from the pushed deep-lever residual. -/
theorem toStatement (R : Erdos260DeepLeverPushResidual) : Erdos260Statement :=
  R.toLeverResidual.toStatement

end Erdos260DeepLeverPushResidual

/-- **The pushed deep conditional endpoint**: `Erdos260Statement` from the pushed deep
dyadic-value lever plus the lever-shrunk surfaces. -/
theorem erdos260_of_deepDyadicValueLeverPush (R : Erdos260DeepLeverPushResidual) :
    Erdos260Statement :=
  R.toStatement

/-- Weakening witness: any wave-6 deep-lever provider yields the pushed residual. -/
def deepLeverPushResidual_of_deepLeverResidual (R : Erdos260DeepLeverResidual) :
    Erdos260DeepLeverPushResidual where
  deepLever := deepDyadicValueLeverPush_iff.mpr R.deepLever
  surfaces := R.surfaces

/-- Converse witness: the pushed residual rebuilds the wave-6 deep-lever residual. -/
def deepLeverResidual_of_deepLeverPushResidual (R : Erdos260DeepLeverPushResidual) :
    Erdos260DeepLeverResidual where
  deepLever := deepDyadicValueLeverPush_iff.mp R.deepLever
  surfaces := R.surfaces

/-! ## Part 8.  The collapsed successor surface — the last L-guard removed -/

/-- **The wave-8 scale-floor-push residual** — the wave-6.5/7
`Erdos260FloorHarvestResidual` (= `Erdos260BootstrapResidual`) with the LAST L-guard
removed: `towerEnumLow` / `towerEnumTail` lose the deep-shell hypothesis
`towerShallowDepthBound < shellLadderDepth ctx` (a theorem at the pushed floor:
`towerDeepGuard_unconditional`).  All modulus-range guards (`q < 107`, `64 ≤ q`,
`48 ≤ q < 96`, `96 ≤ q`, `101 ≤ q`) and the digit-side guards are floor-independent and
kept verbatim. -/
structure Erdos260ScaleFloorPushResidual where
  /-- Tower / class 2 — enumerated part (`q < 107`); the deep-shell guard is GONE. -/
  towerEnumLow : ∀ ctx : ActualFailureContext,
    TowerModulusEnumEscape ctx → (class1SlopeDatum ctx).q < 107 →
    Class2CycleInequality ctx
  /-- Tower / class 2 — tail (`107 ≤ q`); the deep-shell guard is GONE. -/
  towerEnumTail : ∀ ctx : ActualFailureContext,
    TowerModulusEnumEscape ctx →
    107 ≤ (class1SlopeDatum ctx).q →
    (((Nat.log 2 (class1SlopeDatum ctx).q + 1) * shellWidth ctx
        < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
            (class1SlopeDatum ctx).K₀)))
        ∧ TowerBand4Budget ctx)
      ∨ Class2CycleInequality ctx
  /-- Run / class 5 — enumerated part (`q < 64`); verbatim wave-6.5 field. -/
  runNumericLow : ∀ ctx : ActualFailureContext,
    (class1SlopeDatum ctx).q < 64 →
    Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx
  /-- Run / class 5 — tail (`64 ≤ q`); verbatim wave-6.5 field. -/
  runNumericTail : ∀ ctx : ActualFailureContext,
    64 ≤ (class1SlopeDatum ctx).q →
    ((Nat.log 2 (class1SlopeDatum ctx).q + 1)
        * (supportShell ctx.shell.d ctx.shell.X).card
      < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
          (class1SlopeDatum ctx).K₀)))
      ∧ RunBandBudget ctx
    ∨ Class5BandHeavyNumericCloses ctx ∨ Class5CycleNumericCloses ctx
  /-- Return / class 4 count gates — gate-free 3-way body; verbatim wave-6.5 field. -/
  returnGates : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    2 * (129 * shellLadderDepth ctx + 64)
      ≤ 64 * (((supportShell ctx.shell.d ctx.shell.X).card + ctx.n24CarryData.r)
          * (shellLadderDepth ctx + carryB ctx.shell.Q + 1)) →
    ReturnGatesBodyUngated ctx
  /-- Return / class 4 digit Z — verbatim wave-6.5 field. -/
  returnZero : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnB2OneSpacedDatum ctx →
    (∃ k ∈ olcFibre ctx,
      2 ^ carryVal2 ctx k < (supportShell ctx.shell.d ctx.shell.X).card) →
    ¬ ReturnIndexWindowClean ctx →
    ReturnZeroBody ctx
  /-- Return / class 4 clean step — verbatim wave-6.5 field. -/
  returnMaxClean : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ¬ ReturnIndexWindowClean ctx → ReturnMaxCleanBody ctx
  /-- Return / class 4 K.1 interior — verbatim wave-6.5 field. -/
  returnInterior : ∀ ctx : ActualFailureContext,
    ¬ ReturnB2FreeDatum ctx → ReturnInteriorBody ctx
  /-- Chernoff / class 0 survivors — verbatim wave-6.5 field. -/
  class0Survivor : ∀ ctx : ActualFailureContext, Class0DatumSurvivor ctx →
    Class0SurvivorResidueMiss ctx
  /-- Chernoff / class 0 mid band — verbatim wave-6.5 field. -/
  class0Mid : ∀ ctx : ActualFailureContext, 48 ≤ (class1SlopeDatum ctx).q →
    (class1SlopeDatum ctx).q < 96 → Class0CycleMeetsShallow ctx →
    Class0WindowCycleCheck ctx
  /-- Chernoff / class 0 large moduli (`96 ≤ q`) — verbatim wave-6.5 field. -/
  class0BigOrder : ∀ ctx : ActualFailureContext, 96 ≤ (class1SlopeDatum ctx).q →
    (∃ C, ((Nat.log 2 (class1SlopeDatum ctx).q + 1) * C
          < orderOf (2 : ZMod (orbitOrderModulus (class1SlopeDatum ctx).q
              (class1SlopeDatum ctx).K₀)))
        ∧ ∃ c, C < c ∧ c ≤ (class1SlopeDatum ctx).q
            ∧ (∀ m, 1 ≤ m →
                slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ (m + c)
                  = slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀ m)
            ∧ ∀ k ∈ ctx.n24CarryData.starts,
                129 * shellLadderDepth ctx + 64
                    ≤ 64 * gapWindow (hitGap ctx.n24CarryData.a) k ctx.n24CarryData.r →
                (class1SlopeDatum ctx).q
                  < 16 * slopeOrbit (class1SlopeDatum ctx).q (class1SlopeDatum ctx).K₀
                      (cycleRep c k))
    ∨ Class0WindowCycleCheck ctx
  /-- CNL / class 1 — enumerated deep part (`q < 101`); verbatim wave-6.5 field. -/
  class1DeepLow : ∀ ctx : ActualFailureContext,
    64 ∣ shellLadderDepth ctx →
    9 ≤ (class1SlopeDatum ctx).q →
    ((class1SlopeDatum ctx).q ≤ 15 ∨ 25 ≤ (class1SlopeDatum ctx).q) →
    (class1SlopeDatum ctx).q ∉ class1ClosedModuli →
    ¬ Class1DatumClosed ctx →
    ¬ Class1GcdWindowMiss ctx →
    (class1SlopeDatum ctx).q < 101 →
    routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅
  /-- CNL / class 1 — tail (`101 ≤ q`); verbatim wave-6.5 field. -/
  class1DeepTail : ∀ ctx : ActualFailureContext,
    101 ≤ (class1SlopeDatum ctx).q →
    Class1Band4FreePeriod ctx
    ∨ (64 ∣ shellLadderDepth ctx →
        9 ≤ (class1SlopeDatum ctx).q →
        ((class1SlopeDatum ctx).q ≤ 15 ∨ 25 ≤ (class1SlopeDatum ctx).q) →
        (class1SlopeDatum ctx).q ∉ class1ClosedModuli →
        ¬ Class1DatumClosed ctx →
        ¬ Class1GcdWindowMiss ctx →
        routedFibre ctx.n24CarryData (genuineChargeRoute ctx) 1 = ∅)
  /-- DensePack / class 3 — the collapsed ungated residual; verbatim wave-6.5 field. -/
  densePackUngated : DensePackUngatedClosureResidual

namespace Erdos260ScaleFloorPushResidual

/-- **The bridge into the wave-6.5/7 surface**: the dropped deep-shell guards are
absorbed (their hypotheses are simply ignored); every other field passes verbatim. -/
def toFloorHarvest (H : Erdos260ScaleFloorPushResidual) : Erdos260FloorHarvestResidual where
  towerEnumLow := fun ctx _ => H.towerEnumLow ctx
  towerEnumTail := fun ctx _ => H.towerEnumTail ctx
  runNumericLow := H.runNumericLow
  runNumericTail := H.runNumericTail
  returnGates := H.returnGates
  returnZero := H.returnZero
  returnMaxClean := H.returnMaxClean
  returnInterior := H.returnInterior
  class0Survivor := H.class0Survivor
  class0Mid := H.class0Mid
  class0BigOrder := H.class0BigOrder
  class1DeepLow := H.class1DeepLow
  class1DeepTail := H.class1DeepTail
  densePackUngated := H.densePackUngated

/-- The final statement from the scale-floor-push residual, through the wave-6.5 floor
harvest (hence the wave-6 rigidity capstone and the digit-side chain). -/
theorem toStatement (H : Erdos260ScaleFloorPushResidual) : Erdos260Statement :=
  erdos260_of_floorHarvest H.toFloorHarvest

end Erdos260ScaleFloorPushResidual

/-- **The wave-8 final endpoint.**  `Erdos260Statement` from the collapsed
scale-floor-push surface, with no re-proving anywhere on the route. -/
theorem erdos260_of_scaleFloorPush (H : Erdos260ScaleFloorPushResidual) :
    Erdos260Statement :=
  H.toStatement

/-- **The weakening witness**: any wave-6.5/7 floor-harvest provider yields the pushed
residual — the dropped deep-shell guards are supplied by
`towerDeepGuard_unconditional`.  The new presentation hides no strength. -/
def scaleFloorPushResidual_of_floorHarvestResidual (R : Erdos260FloorHarvestResidual) :
    Erdos260ScaleFloorPushResidual where
  towerEnumLow := fun ctx => R.towerEnumLow ctx (towerDeepGuard_unconditional ctx)
  towerEnumTail := fun ctx => R.towerEnumTail ctx (towerDeepGuard_unconditional ctx)
  runNumericLow := R.runNumericLow
  runNumericTail := R.runNumericTail
  returnGates := R.returnGates
  returnZero := R.returnZero
  returnMaxClean := R.returnMaxClean
  returnInterior := R.returnInterior
  class0Survivor := R.class0Survivor
  class0Mid := R.class0Mid
  class0BigOrder := R.class0BigOrder
  class1DeepLow := R.class1DeepLow
  class1DeepTail := R.class1DeepTail
  densePackUngated := R.densePackUngated

/-- The weakening witness from the wave-7 bootstrap surface (a reducible alias of the
floor-harvest surface). -/
def scaleFloorPushResidual_of_bootstrapResidual (R : Erdos260BootstrapResidual) :
    Erdos260ScaleFloorPushResidual :=
  scaleFloorPushResidual_of_floorHarvestResidual R

/-- The weakening witness from the wave-6 rigidity surface. -/
def scaleFloorPushResidual_of_rigidityResidual (R : Erdos260RigidityResidual) :
    Erdos260ScaleFloorPushResidual :=
  scaleFloorPushResidual_of_floorHarvestResidual
    (floorHarvestResidual_of_rigidityResidual R)

/-- **The two surfaces are EQUIVALENT** — the wave-8 residual is exactly the wave-6.5/7
one with the dead deep-shell guards folded in. -/
theorem nonempty_scaleFloorPush_iff_floorHarvest :
    Nonempty Erdos260ScaleFloorPushResidual ↔ Nonempty Erdos260FloorHarvestResidual :=
  ⟨fun ⟨H⟩ => ⟨H.toFloorHarvest⟩,
   fun ⟨R⟩ => ⟨scaleFloorPushResidual_of_floorHarvestResidual R⟩⟩

/-- Equivalence with the wave-7 bootstrap surface. -/
theorem nonempty_scaleFloorPush_iff_bootstrap :
    Nonempty Erdos260ScaleFloorPushResidual ↔ Nonempty Erdos260BootstrapResidual :=
  nonempty_scaleFloorPush_iff_floorHarvest

/-! ## Part 9.  Machine-readable status (honest) -/

/-- Honest machine-readable status of the wave-8 scale-floor push. -/
def scaleFloorPushStatus : List String :=
  [ "THE SHARPENED CONTRADICTION (proved) - supportShell_sparse_contradiction_sharp: the " ++
      "wave-6 supportShell_sparse_contradiction demanded c0*(2g) <= 1 (i.e. 34*g <= 2^24), " ++
      "paying a factor 2 to absorb floor division.  On a dyadic shell X = 2^L (L >= 24) the " ++
      "failure threshold c0*X = (17/2^24)*2^L = 17*2^(L-24) is an EXACT integer, so " ++
      "floor(X/g) >= c0*X holds exactly when 17*g <= 2^24 = 16777216.  The contradiction " ++
      "region DOUBLES with no change to the gap bound.",
    "THE PUSHED UNCONDITIONAL SCALE FLOOR (the headline) - scaleFloorPush_void_of_scale / " ++
      "scaleFloorPush_scale_lower / shellLadderDepth_ge_493461: every ActualFailureContext " ++
      "has X > 2^493460, i.e. L >= 493461.  Same wave-6 gap g = 2L-25 (Q < 2^(L-27), " ++
      "2X+2 <= 2^(L+2)); sharp fire 17*(2L-25) <= 2^24 iff L <= 493460 (margin at the " ++
      "boundary: 17*986895 = 16777215 <= 16777216, short by exactly 1).  Doubles the wave-6 " ++
      "floor 2^246736 and even passes the wave-6 PINNED-VALUE floor 2^493443.",
    "HONEST AUDIT OF THE GAP-BOUND REFINEMENTS ATTEMPTED: (i) window anchor - the true " ++
      "product bound (2^(L-27)-1)*(2^(L+1)+2) < 2^(2L-26) gains only +1 over g = 2L-25, NOT " ++
      "a halving to ~L-26 (log2(Q*(2X+2)) ~ (L-27)+(L+1) = 2L-26; the odd part u = Q can " ++
      "genuinely reach 2^(L-27)); at the sharp fire condition g = 2L-26 and g = 2L-25 give " ++
      "the SAME floor L <= 493460, so the simpler g is kept.  (ii) run-start local tail - " ++
      "R_N = Q*2^N*(tail past N) and after an all-zero run the tail past N EQUALS the tail " ++
      "past N+h, so the local-tail refinement is already exactly the proved chain R_{N+h} = " ++
      "2^h*R_N <= Q*(N+h+2); no gain without a lower bound on R_N beyond positivity + " ++
      "2^t | R_N, and none is formalized.  (iii) the envelope R_N <= Q*(N+2) is the " ++
      "all-ones-tail bound; the true sparse tail restates the same inequality at the longer " ++
      "run ending at the next support element.  THE GAP g(L) HONESTLY STAYS ~2L; the " ++
      "doubling came from the comparison side - the same effect on the floor the hoped " ++
      "a = 2 slope would have had (target ~493447 at a = 2; delivered 493460).",
    "THE PUSHED PINNED-VALUE FLOOR (proved) - scaleFloorPush_void_of_rep: value pin " ++
      "P/(u*2^t), u <= 7 allows the t-free gap g = L+4; sharp fire 17*(L+4) <= 2^24 iff " ++
      "L <= 986891.  Pushed voidings shellValueDyadic_void_of_scale_push / " ++
      "_scale_lower_push, towerFifthValue_void_of_scale_push, " ++
      "towerThirdsValue_void_of_scale_push, fixedFamilyHit_void_of_scale_push / " ++
      "_scale_lower_push: all five fixed families and the three pinned values are void at " ++
      "X <= 2^986891 (wave 6 reached 2^493443).",
    "THE DESCENT-ORDER HARVEST (proved) - n24_r_ge_thirtytwo: r = floor(kappa*L) >= 32 at " ++
      "EVERY ctx (kappa = 17/2^18; 17*493461 = 8388837 >= 32*262144 = 8388608; SHARP: " ++
      "floor(8388837/262144) = 32, r >= 33 would need L >= 508868).  A fortiori " ++
      "n24_r_ge_twentyone (r >= 21), the bound the deep-shell guard used to buy " ++
      "(r_ge_21_of_deep).  Strict sharpening of wave 6.5's n24_r_ge_sixteen.",
    "THE LAST L-GUARD IS DEAD (proved) - towerDeepGuard_unconditional: " ++
      "towerShallowDepthBound = 328965 < shellLadderDepth ctx at EVERY ctx (493461 > " ++
      "328965) - every shell is deep.  Consequences: m0 >= 2 everywhere " ++
      "(two_le_towerSparsityBlock_everywhere); the direct shallow width-cap scalar is " ++
      "FALSE at every ctx (towerShallow_scalar_dead) - the shallow branch of " ++
      "class2ActiveFloorCount_ofShallowDeep never fires.",
    "GUARDS COLLAPSED (exact list): (1) Class2DeepShellResidual == the unguarded " ++
      "forall ctx, Class2DeepShellWindowData ctx (class2DeepShellData_ofResidual / " ++
      "class2DeepShellResidual_ofUnguarded / nonempty_class2Unguarded_iff_deepResidual; " ++
      "Tower core class2ActiveFloorCount_ofDeepData, I.4.1 slot " ++
      "class2TowerSubMass_ofDeepData).  (2) TowerFixedPointResidual / TowerLeverResidual " ++
      "lose their deep guard (towerFixedPointResidual_iff_unguarded, " ++
      "towerLeverResidual_iff_unguarded).  (3) The wave-6 deep-lever guards 2^493443 < X " ++
      "are theorems (deepLeverGuard_unconditional), so DeepDyadicValueLever / " ++
      "DeepTowerFifthValueLever / DeepTowerThirdsValueLever / DeepFixedFamilyVoid collapse " ++
      "onto the FULL levers (dyadicValueLever_iff_deepScale, " ++
      "towerFifthValueLever_iff_deepScale, towerThirdsValueLever_iff_deepScale, " ++
      "fixedFamilyVoid_iff_deepScale).  (4) The towerEnumLow / towerEnumTail deep guards " ++
      "are dropped from the successor surface.",
    "THE PUSHED DEEP LEVERS (the honest successors, at 2^986891): " ++
      "DeepDyadicValueLeverPush / DeepTowerFifthValueLeverPush / " ++
      "DeepTowerThirdsValueLeverPush / DeepFixedFamilyVoidPush demand the exclusions ONLY " ++
      "at X > 2^986891 and discharge the full levers (dyadicValueLever_of_deepScalePush, " ++
      "towerFifthValueLever_of_deepScalePush, towerThirdsValueLever_of_deepScalePush, " ++
      "fixedFamilyHit_void_of_deepScalePush); equivalences dyadicValueLever_iff_" ++
      "deepScalePush, deepDyadicValueLeverPush_iff, deepFixedFamilyVoidPush_iff.  Residual " ++
      "Erdos260DeepLeverPushResidual with endpoint erdos260_of_deepDyadicValueLeverPush " ++
      "and witnesses deepLeverPushResidual_of_deepLeverResidual / " ++
      "deepLeverResidual_of_deepLeverPushResidual.",
    "THE COLLAPSED SUCCESSOR SURFACE (wave 8) - Erdos260ScaleFloorPushResidual: the " ++
      "wave-6.5/7 Erdos260FloorHarvestResidual (= Erdos260BootstrapResidual) with the " ++
      "towerShallowDepthBound < L guards dropped from towerEnumLow / towerEnumTail - the " ++
      "LAST L-guard on the surface.  Honestly kept: all modulus-range guards (q < 107, " ++
      "64 <= q, 48 <= q < 96, 96 <= q, 101 <= q) and the digit-side guards " ++
      "(ReturnB2FreeDatum / ReturnIndexWindowClean / survivor / datum / gcd) - " ++
      "floor-independent.  Bridge Erdos260ScaleFloorPushResidual.toFloorHarvest; endpoint " ++
      "erdos260_of_scaleFloorPush : Erdos260ScaleFloorPushResidual -> Erdos260Statement; " ++
      "weakening witnesses scaleFloorPushResidual_of_floorHarvestResidual / " ++
      "_of_bootstrapResidual / _of_rigidityResidual; equivalences " ++
      "nonempty_scaleFloorPush_iff_floorHarvest / nonempty_scaleFloorPush_iff_bootstrap.",
    "WHAT RESISTS AND WHY (honest): at L >= 493461 the rigidity count floor(X/(2L-25)) " ++
      "drops below c0*X = 17*2^(L-24) (2^24/17 < 2L-25 there), so the sparsity bound is " ++
      "CONSISTENT with the carry rigidity; the failure structure only produces failing " ++
      "shells at arbitrarily LARGE X.  NO context with X > 2^493460 is claimed empty; the " ++
      "pushed deep levers at 2^986891 remain genuinely open.  Additive only; nothing " ++
      "upstream touched; no sorry / admit / new axiom / native_decide." ]

theorem scaleFloorPushStatus_nonempty : scaleFloorPushStatus ≠ [] := by
  simp [scaleFloorPushStatus]

/-! ## Part 10.  Axiom-cleanliness audit -/

#print axioms supportShell_sparse_contradiction_sharp
#print axioms scaleFloorPush_void_of_scale
#print axioms scaleFloorPush_scale_lower
#print axioms shellLadderDepth_ge_493461
#print axioms scaleFloorPush_void_of_rep
#print axioms shellValueDyadic_void_of_scale_push
#print axioms shellValueDyadic_scale_lower_push
#print axioms towerFifthValue_void_of_scale_push
#print axioms towerThirdsValue_void_of_scale_push
#print axioms fixedFamilyHit_void_of_scale_push
#print axioms fixedFamilyHit_scale_lower_push
#print axioms n24_r_ge_thirtytwo
#print axioms n24_r_ge_twentyone
#print axioms towerDeepGuard_unconditional
#print axioms two_le_towerSparsityBlock_everywhere
#print axioms towerShallow_scalar_dead
#print axioms class2DeepShellData_ofResidual
#print axioms class2DeepShellResidual_ofUnguarded
#print axioms nonempty_class2Unguarded_iff_deepResidual
#print axioms class2ActiveFloorCount_ofDeepData
#print axioms class2TowerSubMass_ofDeepData
#print axioms towerFixedPointResidual_iff_unguarded
#print axioms towerLeverResidual_iff_unguarded
#print axioms deepLeverGuard_unconditional
#print axioms dyadicValueLever_iff_deepScale
#print axioms towerFifthValueLever_iff_deepScale
#print axioms towerThirdsValueLever_iff_deepScale
#print axioms fixedFamilyVoid_iff_deepScale
#print axioms dyadicValueLever_of_deepScalePush
#print axioms dyadicValueLever_iff_deepScalePush
#print axioms deepDyadicValueLeverPush_iff
#print axioms towerFifthValueLever_of_deepScalePush
#print axioms towerThirdsValueLever_of_deepScalePush
#print axioms fixedFamilyHit_void_of_deepScalePush
#print axioms deepFixedFamilyVoidPush_iff
#print axioms Erdos260DeepLeverPushResidual.toLeverResidual
#print axioms Erdos260DeepLeverPushResidual.toStatement
#print axioms erdos260_of_deepDyadicValueLeverPush
#print axioms deepLeverPushResidual_of_deepLeverResidual
#print axioms deepLeverResidual_of_deepLeverPushResidual
#print axioms Erdos260ScaleFloorPushResidual.toFloorHarvest
#print axioms Erdos260ScaleFloorPushResidual.toStatement
#print axioms erdos260_of_scaleFloorPush
#print axioms scaleFloorPushResidual_of_floorHarvestResidual
#print axioms scaleFloorPushResidual_of_bootstrapResidual
#print axioms scaleFloorPushResidual_of_rigidityResidual
#print axioms nonempty_scaleFloorPush_iff_floorHarvest
#print axioms nonempty_scaleFloorPush_iff_bootstrap
#print axioms scaleFloorPushStatus_nonempty

end

end Erdos260
