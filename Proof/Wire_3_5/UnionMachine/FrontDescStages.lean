import Proof.Wire_3_5.UnionMachine.FrontDescLayout

/-! # C6 front, U5: the flag loop's stages

After the eraser (`FrontDescLayout.eraseAll_step`) a round rebuilds the decoder's public words on the erased tapes:
the template `0 1^q 0` and the policies `1^W`, `1^L`, each copied from its reference tape by base's bounded tape copy
(`RecoveryBoundedTapeCopy`, ruler `1^Hd`), padded with `false` (**`copyRef_step`**).
Paper quantity: none (the flag loop's plumbing). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontDescStages
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontLoopKit NearCubicWires.WireExponent3_5.UnionMachine.FrontDescLayout
open NearCubicWires.WireExponent3_5.UnionMachine.FrontAtomRound (install_eq_of dockH_eq_of)
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.Tm

/-! ## A reference word onto a decoder tape -/

/-! ## The loop's own tapes -/

section Own

end Own

/-! ## The raw tape's eraser -/

/-! ## The entry's code onto the raw tape -/

/-! ## The decoder, rewound, on the decoder half -/

/-! ## The verdict: append the flag bit, count the atom off -/

section Tail

end Tail

end NearCubicWires.WireExponent3_5.UnionMachine.FrontDescStages
