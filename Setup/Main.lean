import Setup.PhaseD5
import CheckedPCPP.H2Poly

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.Setup

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.RepairOrdinary.Streaming NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.CanonicalWitnessCodec NearCubicWires.ExecutableInterfaces NearCubicWires.Bindings.CLW20Lemma311
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close NearCubicGates.Close.Platform NearCubicGates.Close.CheckedPCPP
open NearCubicGates.Close.Worker (width pcpp gadgets oracleOK nu PairOK)
open NearCubicGates.Close.Worker.Format (readField)

noncomputable section

/-! ## The set-up data -/

section Data

end Data

/-! ## The program -/

/-! ## Cost bounds -/

section Costs

/-! ## CHECK's cost is monotone in the description length -/

end Costs

/-! ## After phase P -/

section AfterP

end AfterP

/-! ## Branching on ideal states -/

/-! ## The accepting runs -/

section Accept

/-! ## The rejecting runs -/

end Accept

end

end NearCubicGates.Close.Setup
