import Proof.SourceAssembly.SourceFactorSelCount
import Proof.SourceAssembly.SourceFactorSelDescF
import Proof.SourceAssembly.SourceRequestTermBridge

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceFactorSel.Slot
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding
open NearCubicWires.SourceFactorSel.Desc (Kind gdesc dT flagS flagO)
open NearCubicWires.SourceFactorSel.Count (read_flag wordM word0_step)
open NearCubicWires.SourceRequest.TermReader
noncomputable section

/-! ## The reader's dock -/


/-! ## The descriptor writer's docks -/


/-! ## The machine -/

/-! ## The TERM branch -/

/-! ## The NOT-TERM branch (systematic or absent) -/

/-! ## The slot, mode-generic -/

/-! ## Per mode (the consumer's descriptors) -/

section
open RepairRepresentation SupplierPipeline SourceInterfaces SupplierEstimator NearCubicWires.RepairSource
open NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.SourceRequest

end

end
end NearCubicWires.SourceFactorSel.Slot

