import Codec.Transcode
import Codec.ParityW
import Codec.Unframe

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.WorkerArith

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Codec

/-! ## Helpers -/

/-! ## List loops, parity rows -/

/-! ## The per-circuit costs by the circuit's word length -/

section Circuits
open NearCubicGates.Close.Joins

theorem bitWord_len (b : Bool) : (bitWord b).length = 3 := by cases b <;> rfl

end Circuits

section Wrap
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming NearCubicGates.Close.Joins NearCubicGates.Close.Worker.Format

end Wrap

end NearCubicGates.Close.WorkerArith
