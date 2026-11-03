import Setup.PhaseD2

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Setup

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.RepairOrdinary.Streaming NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicGates.Close NearCubicGates.Close.Platform NearCubicGates.Close.CheckedPCPP
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO appendO_st appendO_sh appendO_val appendO_nil)

noncomputable section

/-! ## Transcoding the circuit fields -/

/-! ## The supports record's length -/

/-! ## The I-stream header -/

end

end NearCubicGates.Close.Setup
