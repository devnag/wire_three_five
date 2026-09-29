import Proof.SourceAssembly.SourceRequestCurMoment
import Proof.SourceAssembly.SourceRequestSelFrontA
import Proof.SourceAssembly.SourceRequestTermBridge

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceRequest.SelFront
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open SourceInterfaces RecoveryRootRound RepairSource.VerifierDecoding
open NearCubicWires.ComponentwiseBranchExtraction
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.SourceRequest.CurSpec NearCubicWires.SourceRequest.CurContract
open NearCubicWires.SourceRequest.CoordBridge NearCubicWires.SourceRequest.TermReader
noncomputable section

/-! ## Docks -/









end
end NearCubicWires.SourceRequest.SelFront

