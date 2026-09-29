import Proof.Wire_3_5.FinalPass.RowD

/-! # `RowW`, part 4b: collapsing three registers' writes

Six writes on three distinct registers collapse to the last value of each (`chain3`), for abstract registers, in a
module with few open namespaces. Used for the coefficient pass's and the digit weights' loop states. Main
declaration: **`chain3`**. Paper quantity: none (state bookkeeping of the row program). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.DigsBody
open NearCubicWires.WireExponent3_5.FinalPass.Tm

/-- Six writes on three distinct registers, collapsed. -/
theorem chain3 {ns nr : ℕ} (s : WState ns nr) (a b c : Fin nr) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (x1 x2 x3 y3 z1 z2 : ℕ) :
    (((((s.setv a x1).setv b x2).setv c x3).setv c y3).setv a z1).setv b z2 = ((s.setv a z1).setv b z2).setv c y3 := by
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
