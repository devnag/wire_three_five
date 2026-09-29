import Proof.Wire_3_5.UnionMachine.FrontDescStages

/-! # C6 front, U5: one round of the description-flag loop (P3:3670, 3083-3094)

One round checks one grid atom against the description envelope: erase the decoder half (`eraseAll`), rebuild the
template and the policies (`copyRef`), erase the raw tape and copy the entry's code onto it (`eraseRaw`, `copyAt`),
run the Theorem 2.5 repository's decoder at policy `L` and rewind (`decAt`), and append the verdict bit to the flag string (`dtailM`).
**`entry_eq`**: after the rebuild the decoder half is exactly the decoder's padded entry. **`roundD_step`**: the round,
with the flag bit `passedM m q W L p` and the decoder half's invariant restored.
Paper quantity: the description flag `descriptionBits ≤ L` of one guessed atom. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontDescRound
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.UnionMachine.FrontLoopKit NearCubicWires.WireExponent3_5.UnionMachine.FrontDescLayout
open NearCubicWires.WireExponent3_5.UnionMachine.FrontDescStages
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.Tm

/-! ## The round -/

end NearCubicWires.WireExponent3_5.UnionMachine.FrontDescRound
