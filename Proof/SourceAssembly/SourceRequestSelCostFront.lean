import Proof.SourceAssembly.SourceRequestSelLocalMach

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceRequest.SelLocal
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open NearCubicWires.RepairRepresentation (PCPPRequest PointwisePCPPAlgorithm pcppOutput)
open SourceInterfaces RepairSource.VerifierDecoding
open NearCubicWires.ComponentwiseBranchExtraction
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.SourceRequest.SelFront
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalClause (index negative)
noncomputable section

/-! ## Powers of the size bound -/

/-! ## Front B: the count readers, `word N`, the phase cursor -/

end
end NearCubicWires.SourceRequest.SelLocal

