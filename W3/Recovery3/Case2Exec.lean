import W3.Recovery3.Case2Block

/-!
# The Case-2 chain, part 2: proof 1's complete Case-2 execution, generic in the source block

Base `CaseTwoExecution{Layout,}.lean`, restated over an `SBlock`: from the five words of the recovery's Case-2 port
(`w0`, the framed canonical description of `B*_pf`, the framed final address, `1^q`, `1^B`) proof 1's canonical→native
converter (`CloseoutCaseTwo.Cold.converter_run`) writes `frame (descriptor B*_pf)`; the fixed XOR fold of the whole
blocks returns the paper's padded unsigned XOR bit. The hierarchy re-framing of the old
`PreparedFrames` is dropped: the source block reads `w0` as it is.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 120000

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces NearCubicWires.RecoveryPipeline
open NearCubicWires.RepairOrdinary.CloseoutCaseTwo NearCubicWires.OuterPCPRecovery
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)

namespace W3.NearCubicWires.RepairSource.Outer3.Case2

namespace SBlock

noncomputable section



end

end SBlock

end W3.NearCubicWires.RepairSource.Outer3.Case2
