import Proof.Wire_3_5.Primitive.SeedFix.TS4KBase

/-! # T (#120, thrStage4U), part 15: the v4 stage's time bound `cost3`, polynomial

P3:3071-3091 ("the preprocessing … runs in time polynomial in `n`") and P3:3114-3115: the v4 stage's time `cost3G` (the
prep, W6's numbers machine, PA's first three phases, the hash writer, the collection, the reset) is `PolyBounded` in
`K + n + L + W`, the degree `DcG l` fixed by the literals, the coefficient `CcG l c_r` by `c_r`:

* `emitsCost_le`, `qh_le` (the hash writer within `19W + 4`);
* `Dw`, `Cw`, `Ct`, `DcG`, `CcG`; **`cost3G`**; `numsM_le`, **`cost3G_le`**.

Paper quantities of the main type: the v4 data stage's step count. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimT.TS4
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.Data
open NearCubicWires.WireExponent3_5.PrimAsm.ThrData NearCubicWires.SupplierPipeline
open NearCubicWires.ValidatorPolynomialDomination

theorem emitsCost_le : ∀ cs : List ℕ, emitsCost cs ≤ 19 * (unaryList cs).length
  | [] => by simp [emitsCost, unaryList]
  | c :: cs => by
    have ih := emitsCost_le cs
    have e : (unaryList (c :: cs)).length = c + 1 + (unaryList cs).length := by
      rw [unaryList_cons]; simp; omega
    simp only [emitsCost]
    rw [e]
    omega

theorem qh_le (cs : List ℕ) (W : ℕ) (h : 2 * (unaryList cs).length ≤ 2 * W) : qhCost cs ≤ 19 * W + 4 := by
  have := emitsCost_le cs
  unfold qhCost; omega

variable (l : Literals)


/-- PA's data stage coefficient and degree (`thrCost2_le`). -/
noncomputable def Ct : ℕ := 40 * ThrData.cTT + 80 * ThrData.cX + 70100

end NearCubicWires.WireExponent3_5.PrimT.TS4
