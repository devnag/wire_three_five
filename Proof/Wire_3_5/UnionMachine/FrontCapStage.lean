import Proof.Wire_3_5.UnionMachine.FrontKit
import Proof.CaseAnalysis.CloseoutScheduleMetadata
import Proof.MachineModel.ClockUnarySum
import Proof.CaseAnalysis.ScheduleScale

/-! # C6 front, U3: the restriction's capacity `1^cap` (the G3 entry)

The padded producer (`Transfer.CaseTwoPadG.osourceG_run`, G3) reads, besides the hierarchy word, the raw oracle
descriptor and `1^q`, a unary capacity `1^cap` with `64·(O.size + q + 4) + 1 ≤ cap`. This stage writes
`1^{64·(q + |x|)}` from the framed input `x` and `1^q`, on its own `22` tapes, with base parts only: the input length
as `CompareMachine.word |x|` (base `CloseoutSchedule.Metadata.length_run`), a copy of `1^q` (base
`ClockUnarySum.sum_ready q 0`), and base's fixed scaling (`CloseoutSchedule.Scale.scale_run 64 q |x|`). The capacity
suffices once `O.size + 5 ≤ |x|` (**`cap_enough`**; a decodable oracle of a `⌊N/16⌋`-bit witness has
`O.size ≤ ⌊N/16⌋ + 1`, `FrontSize.size_le_payload`).
Main statement: **`cap_ready`**. Paper quantity: the unary capacity of the restriction program. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontCapStage
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.RepairSource.CloseoutSchedule

/-! ## Layout: `0` input, `1` width; `2–8` the length count; `9–11` the copy; `12–21` the scaling (`20` its result)
-/

abbrev CT : ℕ := 22




end NearCubicWires.WireExponent3_5.UnionMachine.FrontCapStage
