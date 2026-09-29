import Proof.Wire_3_5.UnionMachine.FrontDescDecoder
import Proof.Wire_3_5.UnionMachine.FrontAtomRound

/-! # C6 front, U5: the description-flag loop's tapes and its eraser

The flag loop reruns the Theorem 2.5 repository's decoder (`FrontDescDecoder.decR`: the decoder, its template head, a full rewind and a
recording log, `1703 + 1` tapes) once per grid atom, at policy `L = (q+1)^descDeg`. A run may reject and then leaves
its tapes unknown, so every round starts by erasing every decoder tape but the raw tape and the driver (base
`RecoveryScratchErase`, ruler `1^Hd`), which the bound of `decR_step` allows.

Tapes: the decoder half `xm` (`1703` decoder tapes `dx`, then the log), then `16` own tapes `ym`: `0` the guess rest,
`1` the copy's cell, `2–4` the copy's registers `PG PT K`, `5` the loop's condition, `6` the count `J`, `7` the flag
string, `8` the ruler `1^Hd`, `9` the eraser's capacity tape, `10` the raw eraser's capacity tape, `11` the template
`0 1^q 0`, `12` the policy `1^W`, `13` the policy `1^L`, `14` the copies' capacity tape, `15` spare.
Main statement: **`eraseAll_step`**. Paper quantity: none (the layout of the flag loop). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontDescLayout
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontLoopKit
open NearCubicWires.WireExponent3_5.UnionMachine.FrontAtomRound (install_eq_of dockH_eq_of)





/-! ## The eraser -/


end NearCubicWires.WireExponent3_5.UnionMachine.FrontDescLayout
