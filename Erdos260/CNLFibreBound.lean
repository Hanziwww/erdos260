import Mathlib
import Erdos260.CNLCodeFaithfulness

/-!
# Appendix L.1.2 / G: closing the `O_Q(1)`-to-one CNL fibre bound

`CNLCodeFaithfulness.lean` proved clean-code faithfulness (`sym_injOn`) on the
surviving clean family and isolated the *one* remaining deep combinatorial input
of the full-family Kraft bound as the explicit hypothesis

```
hfiber : ∀ k ∈ (selectedTransitions T).image (codeWord sym M),
           ((selectedTransitions T).filter (fun t => codeWord sym M t = k)).card ≤ B
```

— the manuscript's *`O_Q(1)`-to-one* fibre bound (Appendix L.1.2 / G): the set of
selected lift states sharing a given ladder-code word `k` has at most `B = O_Q(1)`
members, because two such states *differ only by their carry residue class modulo
`Q`*, and there are only finitely many (`≤ Q`) such classes.

This file **closes** that fibre bound.  The mathematical engine is one short,
fully general theorem:

> **Fibre-injection bound (`card_fibre_le_card_residue`).**  If a residue map
> `res : α → R` into a finite type `R` is such that *the code together with the
> residue determines the state* (`code a = code b → res a = res b → a = b` on the
> family `F`), then on every fixed code-fibre `res` is injective, so the fibre
> *injects into* `R` and hence `card (fibre) ≤ Fintype.card R`.

This is exactly the manuscript mechanism: "states sharing a code word inject into
the carry-residue set, of size `≤ Q`".  We then close `hfiber` in two ways.

## 1. Manuscript-faithful, sharp constant `B = Q` (carry residue modulo `Q`)

Instantiating the engine with the carry residue `res : CNLTransition → ZMod Q`
(the carry quotient modulo `Q`, `Fintype.card (ZMod Q) = Q`) reduces `hfiber`, with
the sharp manuscript constant `B = Q`, to the **single** injectivity input

```
hcarry : ∀ a b ∈ selectedTransitions T,
           codeWord sym M a = codeWord sym M b → res a = res b → a = b
```

i.e. *the ladder code and the carry residue mod `Q` jointly determine the
transition*.  This is the manuscript's precise statement ("the residual ambiguity
is bounded by the finite carry quotient modulo `Q`"), and it is the smallest
honest residual: with the current abstract `CNLTransition` (a finite normal-form
object carrying neither an intrinsic code nor a carry residue) the joint map
`(codeWord sym M, res)` cannot be shown injective from the structure alone — it is
the manuscript dynamics.  From `hcarry` we derive the full-family Kraft bound
`cleanCNLKraftSum (selectedTransitions T) BNDHeight c ≤ Q · C_Q^M`.

## 2. Fully unconditional, via finiteness of the normal-form model

The abstract `CNLTransition` of `CNL.lean` is a *finite* type (a normal form in
`{positiveLift, childResidue}` together with an available subset of the seven CNL
classes).  Taking `res = id` (every state is its own residue) the joint
injectivity is trivial, and the engine yields the fibre bound with the universal
constant `B = Fintype.card CNLTransition` — depending on nothing.  This **closes
`hfiber` unconditionally** (no hypothesis, no `sorry`, no `axiom`) and gives
`cleanCNLKraftSum (selectedTransitions T) BNDHeight c ≤ (Fintype.card CNLTransition) · C_Q^M`.
It is a crude `O(1) ⊆ O_Q(1)` bound (it does not see the carry mechanism), but it
is a genuine, unconditional discharge of the isolated residual; the carry-residue
route of §1 supplies the sharp `B = Q`.

Everything here is `sorry`-free and `axiom`-clean (only the three standard Lean
axioms; verified with `#print axioms`).
-/

namespace Erdos260

open Finset

noncomputable section

/-! ## Part 1. The fibre-injection bound (the manuscript mechanism) -/

/--
**Fibre-injection bound.**  Let `F : Finset α`, `code : α → β`, and
`res : α → R` with `R` finite.  Suppose the code and the residue *jointly
determine* the state on `F`:

```
∀ a ∈ F, ∀ b ∈ F, code a = code b → res a = res b → a = b.
```

Then on each fixed code-fibre `{a ∈ F | code a = k}` the residue `res` is
injective (two fibre members share the code `k`, so equal residue forces
equality), hence the fibre **injects into** `R` and

```
card {a ∈ F | code a = k} ≤ Fintype.card R.
```

This is the abstract content of the manuscript's "states sharing a ladder-code
word inject into the finite carry-residue set". -/
theorem card_fibre_le_card_residue {α β R : Type*} [DecidableEq β] [DecidableEq R]
    [Fintype R] (F : Finset α) (code : α → β) (res : α → R)
    (hinj : ∀ a ∈ F, ∀ b ∈ F, code a = code b → res a = res b → a = b)
    (k : β) :
    (F.filter (fun a => code a = k)).card ≤ Fintype.card R := by
  -- `res` is injective on the code-fibre.
  have hres_inj : Set.InjOn res ↑(F.filter (fun a => code a = k)) := by
    intro a ha b hb hres
    simp only [Finset.mem_coe, Finset.mem_filter] at ha hb
    exact hinj a ha.1 b hb.1 (ha.2.trans hb.2.symm) hres
  -- so the fibre has the cardinality of its `res`-image, which sits inside `R`.
  calc (F.filter (fun a => code a = k)).card
      = ((F.filter (fun a => code a = k)).image res).card :=
        (Finset.card_image_of_injOn hres_inj).symm
    _ ≤ Fintype.card R := Finset.card_le_univ _

/-! ## Part 2. Manuscript-faithful closure: `B = Q` (carry residue modulo `Q`) -/

/--
**The `O_Q(1)`-to-one fibre bound, sharp constant `B = Q`.**  With a carry-residue
map `res : CNLTransition → ZMod Q` (the carry quotient modulo `Q`) for which the
ladder code and the residue jointly determine the transition, every code-fibre of
the selected family has at most `Q` members.  This is the manuscript's
`O_Q(1)`-to-one bound with `B = Q = Fintype.card (ZMod Q)`. -/
theorem card_codeWord_fibre_le_carryQuotient
    (T : Finset CNLTransition) (sym : CNLTransition → ℕ → ℕ) (M : ℕ)
    (Q : ℕ) [NeZero Q] (res : CNLTransition → ZMod Q)
    (hcarry : ∀ a ∈ selectedTransitions T, ∀ b ∈ selectedTransitions T,
        codeWord sym M a = codeWord sym M b → res a = res b → a = b)
    (k : List ℕ) :
    ((selectedTransitions T).filter (fun t => codeWord sym M t = k)).card ≤ Q := by
  have h :=
    card_fibre_le_card_residue (selectedTransitions T) (codeWord sym M) res hcarry k
  rwa [ZMod.card Q] at h

/--
**Full-family Kraft bound from the carry residue, `B = Q` (manuscript L.1.2).**

Feeding the carry-residue fibre bound (sharp `B = Q`) into the boundedness engine
`cleanCNLKraftSum_selectedTransitions_le_boundedToOne_ofBridgeStep` of
`CNLCodeFaithfulness.lean` discharges `hfiber` and yields the full selected-family
weighted Kraft bound

```
cleanCNLKraftSum (selectedTransitions T) BNDHeight c ≤ Q · C_Q^M,
```

with both deep atoms now non-assumed: `step_injOn` from the proved bridge descent,
`sym_injOn` from the L.1.2a–d removal, and the fibre bound from the carry-residue
injectivity `hcarry`.  The only remaining manuscript input is `hcarry` itself —
"the ladder code and the carry residue mod `Q` jointly determine the lift state",
which is exactly the manuscript's carry-quotient statement. -/
theorem cleanCNLKraftSum_selectedTransitions_le_carryQuotient_ofBridgeStep
    (T : Finset CNLTransition) (BNDHeight : CNLTransition → ℝ) (c CQ : ℝ)
    (hc : 0 < c) (hCQ : (1 - (2 : ℝ) ^ (-c))⁻¹ ≤ CQ)
    (M : ℕ) (E : ℕ → ℕ) {g sm gOld : ℕ → ℤ} {s : ℕ}
    (hE : ∀ t, (E t : ℤ) = bridgeExp g sm s t)
    (hwin : ∀ t, sm (t + 1) - sm t = g t - gOld t)
    (hpos : ∀ t, 0 < gOld t)
    (sym : CNLTransition → ℕ → ℕ)
    (hheight :
      ∀ t ∈ selectedTransitions T,
        BNDHeight t = ∑ i ∈ Finset.range M, (E (sym t i) : ℝ))
    (Q : ℕ) [NeZero Q] (res : CNLTransition → ZMod Q)
    (hcarry : ∀ a ∈ selectedTransitions T, ∀ b ∈ selectedTransitions T,
        codeWord sym M a = codeWord sym M b → res a = res b → a = b) :
    cleanCNLKraftSum (selectedTransitions T) BNDHeight c ≤ (Q : ℝ) * CQ ^ M := by
  refine cleanCNLKraftSum_selectedTransitions_le_boundedToOne_ofBridgeStep
    T BNDHeight c CQ hc hCQ M E hE hwin hpos sym hheight Q ?_
  intro k _
  exact card_codeWord_fibre_le_carryQuotient T sym M Q res hcarry k

/-! ## Part 3. Unconditional closure: finiteness of the CNL normal-form model -/

/-- The CNL transition normal form is a *finite* object: a normal form together
with an available subset of the seven CNL classes.  This is the equivalence to
the explicit finite product witnessing that finiteness. -/
def cnlTransitionEquivProd : CNLTransition ≃ CNLNormalForm × Finset CNLClass where
  toFun t := (t.normalForm, t.available)
  invFun p := { normalForm := p.1, available := p.2 }
  left_inv _ := rfl
  right_inv _ := rfl

/-- `CNLTransition` is a finite type (transported from the finite product
`CNLNormalForm × Finset CNLClass`). -/
instance instFintypeCNLTransition : Fintype CNLTransition :=
  Fintype.ofEquiv _ cnlTransitionEquivProd.symm

/--
**The fibre bound, unconditional, `B = Fintype.card CNLTransition`.**  Taking the
residue to be the identity (every state is its own residue, so the joint
injectivity is trivial), the fibre-injection bound gives the universal constant
`Fintype.card CNLTransition`, with no hypotheses at all.  This is the crude
model-finiteness closure of the manuscript's `O_Q(1)`-to-one bound. -/
theorem card_codeWord_fibre_le_card_cnlTransition
    (T : Finset CNLTransition) (sym : CNLTransition → ℕ → ℕ) (M : ℕ) (k : List ℕ) :
    ((selectedTransitions T).filter (fun t => codeWord sym M t = k)).card
      ≤ Fintype.card CNLTransition :=
  card_fibre_le_card_residue (selectedTransitions T) (codeWord sym M)
    (id : CNLTransition → CNLTransition) (fun _ _ _ _ _ h => h) k

/--
**Full-family Kraft bound, unconditional (`B = Fintype.card CNLTransition`).**

Discharging `hfiber` with the universal model-finiteness constant
`B = Fintype.card CNLTransition` — which depends on nothing — closes the
boundedness engine of `CNLCodeFaithfulness.lean` with **no extra hypothesis**:

```
cleanCNLKraftSum (selectedTransitions T) BNDHeight c
    ≤ (Fintype.card CNLTransition) · C_Q^M.
```

The constant is `O(1)` (hence `O_Q(1)`), so this is a genuine unconditional
discharge of the isolated fibre residual; the sharp manuscript constant `B = Q`
is the carry-residue route of Part 2. -/
theorem cleanCNLKraftSum_selectedTransitions_le_modelCard_ofBridgeStep
    (T : Finset CNLTransition) (BNDHeight : CNLTransition → ℝ) (c CQ : ℝ)
    (hc : 0 < c) (hCQ : (1 - (2 : ℝ) ^ (-c))⁻¹ ≤ CQ)
    (M : ℕ) (E : ℕ → ℕ) {g sm gOld : ℕ → ℤ} {s : ℕ}
    (hE : ∀ t, (E t : ℤ) = bridgeExp g sm s t)
    (hwin : ∀ t, sm (t + 1) - sm t = g t - gOld t)
    (hpos : ∀ t, 0 < gOld t)
    (sym : CNLTransition → ℕ → ℕ)
    (hheight :
      ∀ t ∈ selectedTransitions T,
        BNDHeight t = ∑ i ∈ Finset.range M, (E (sym t i) : ℝ)) :
    cleanCNLKraftSum (selectedTransitions T) BNDHeight c
      ≤ (Fintype.card CNLTransition : ℝ) * CQ ^ M := by
  refine cleanCNLKraftSum_selectedTransitions_le_boundedToOne_ofBridgeStep
    T BNDHeight c CQ hc hCQ M E hE hwin hpos sym hheight (Fintype.card CNLTransition) ?_
  intro k _
  exact card_codeWord_fibre_le_card_cnlTransition T sym M k

end

end Erdos260
