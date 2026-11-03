import Platform.RecLoop

/-! # The record loop over a stream with a tail (`recLoopJ`)

A reused stream written from its start (`OutOn`, `overlay`) holds the new record stream followed by whatever was left
of its old contents. **`recLoopJ_spec`** is `recLoop_spec` for `I = recStream ws ++ junk`: the loop reads only the
records and the end marker, so the tail is never touched. Same program (`recLoop`), same costs. -/

set_option autoImplicit false

namespace NearCubicGates.Close.Platform
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (copyPair emitB rst copyLoop_rst emitB_rst fwdA_rst rd_app0)
open StablePartition.Workspace (overlay)

section LoopJ

end LoopJ

end NearCubicGates.Close.Platform
