import Proof.Wire_3_5.FinalPass.RowE

/-! # `RowW`, part 5a: overwriting three registers

Three writes on distinct registers `a`, `b`, `c`, then three more in the same order, equal the last three
(`chain3b`), for abstract registers, in a module with few open namespaces. Used for the digit weights' loop state.
Main declaration: **`chain3b`**. Paper quantity: none (state bookkeeping of the row program). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.DigsBody
open NearCubicWires.WireExponent3_5.FinalPass.Tm

/-- Three registers written twice in the same order: the second writes win. -/
theorem chain3b {ns nr : ℕ} (s : WState ns nr) (a b c : Fin nr) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (x1 x2 x3 y1 y2 y3 : ℕ) :
    (((((s.setv a x1).setv b x2).setv c x3).setv a y1).setv b y2).setv c y3 = ((s.setv a y1).setv b y2).setv c y3 := by
  refine WState.eq rfl rfl ?_ rfl
  funext y
  simp only [WState.setv_val, Function.update_apply]
  by_cases h1 : y = a
  · subst h1
    simp only [hab, hac, ite_true, ite_false, if_true, if_false]
  by_cases h2 : y = b
  · subst h2
    simp only [Ne.symm hab, hbc, ite_true, ite_false, if_true, if_false]
  by_cases h3 : y = c
  · subst h3
    simp only [Ne.symm hac, Ne.symm hbc, ite_true, ite_false, if_true, if_false]
  simp only [h1, h2, h3, ite_false, if_false]

end NearCubicWires.WireExponent3_5.FinalPass.DigsBody
