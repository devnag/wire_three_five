import Proof.Wire_3_5.FinalPass.RowC

/-! # `RowW`, part 4a: collapsing a chain of register writes

Ten writes on five distinct registers collapse to the last value of each (`chain5`), stated for abstract registers
and proved in a module with few open namespaces (the proof is by cases on the register). Used for the target pass's
loop state. Main declaration: **`chain5`**. Paper quantity: none (state bookkeeping of the row program). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.DigsBody
open NearCubicWires.WireExponent3_5.FinalPass.Tm

/-- Ten register writes on five distinct registers, collapsed. -/
theorem chain5 {ns nr : ℕ} (s : WState ns nr) (a b c d e : Fin nr) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hae : a ≠ e) (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (x1 x2 x3 x4 x5 y5 z1 z2 z3 z4 : ℕ) :
    (((((((((s.setv a x1).setv b x2).setv c x3).setv d x4).setv e x5).setv e y5).setv a z1).setv b z2).setv c
      z3).setv d z4 = ((((s.setv a z1).setv b z2).setv c z3).setv d z4).setv e y5 := by
  refine WState.eq rfl rfl ?_ rfl
  funext y
  simp only [WState.setv_val, Function.update_apply]
  by_cases h1 : y = a
  · subst h1
    simp only [hab, hac, had, hae, ite_true, ite_false, if_true, if_false]
  by_cases h2 : y = b
  · subst h2
    simp only [Ne.symm hab, hbc, hbd, hbe, ite_true, ite_false, if_true, if_false]
  by_cases h3 : y = c
  · subst h3
    simp only [Ne.symm hac, Ne.symm hbc, hcd, hce, ite_true, ite_false, if_true, if_false]
  by_cases h4 : y = d
  · subst h4
    simp only [Ne.symm had, Ne.symm hbd, Ne.symm hcd, hde, ite_true, ite_false, if_true, if_false]
  by_cases h5 : y = e
  · subst h5
    simp only [Ne.symm hae, Ne.symm hbe, Ne.symm hce, Ne.symm hde, ite_true, ite_false, if_true, if_false]
  simp only [h1, h2, h3, h4, h5, ite_false, if_false]

end NearCubicWires.WireExponent3_5.FinalPass.DigsBody
