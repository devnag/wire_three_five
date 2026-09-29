import Proof.Assembly.FramingSpec
import Proof.Assembly.Header

/-! A fixed physical row transaction. The header writer and complete descriptor
framer are closed programs. The three remaining stages are shared ordinary
machines, with explicit full-bank joins and their own paid fuel. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
namespace PCJcc051fd4c1bd4540_Row
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtIncidence NearCubicWires.ExtDecompositionBatch
open NearCubicWires.P1Closure NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed
attribute [local irreducible] P1TopDownPaidPayload.tapes
noncomputable section
namespace Frame
end Frame


end
end PCJcc051fd4c1bd4540_Row
