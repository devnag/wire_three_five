import Proof.Assembly.RowFixedPhysicalRealization

/-! The exact external-row family, with one fixed row body and a paid runtime
repeat driver. Each normalized packet family is consumed once; the descriptor
only grows. The terminal and zero-row cases use the existing driver rewind. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
namespace PCJcc051fd4c1bd4540_Family
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtIncidence NearCubicWires.ExtDecompositionBatch
open NearCubicWires.P1Closure NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed
attribute [local irreducible] P1TopDownPaidPayload.tapes
namespace Row
end Row
noncomputable section





end
end PCJcc051fd4c1bd4540_Family
