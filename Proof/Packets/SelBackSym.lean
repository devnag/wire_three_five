import Proof.SourceAssembly.SourceRequestSelBackThrRun

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.SourceRequest.SelBackSym
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open SourceInterfaces RepairSource.VerifierDecoding
open NearCubicWires.ComponentwiseBranchExtraction NearCubicWires.ComponentwisePolynomial
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.SourceRequest.SelFront NearCubicWires.SourceRequest.SelSpec NearCubicWires.SourceRequest.CurSpec
open NearCubicWires.SourceRequest.CurContract NearCubicWires.SourceRequest.CoordBridge NearCubicWires.SourceRequest.TermReader
open NearCubicWires.SourceRequest.SelBack
open NearCubicWires.SourceFactorSel.Modes (kindOf bmOf bitsOf)
noncomputable section

section slots

end slots

section four
variable {n0 : Nat} {circuit : BooleanCircuit n0} {pcpp : PointwisePCPP circuit}

/-- The SYM producer at the admission caps. -/
abbrev PS (da : RepairRepresentation.DecompositionAlgorithm) (Pw W Ld : Nat) := SymSwitch.producer (pcpp := pcpp) da Pw W Ld

end four

section keptS

end keptS

end
end NearCubicWires.SourceRequest.SelBackSym

