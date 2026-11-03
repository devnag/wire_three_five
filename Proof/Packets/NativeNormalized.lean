import Proof.Packets.NativeNormalizedData

/-! Complete native-stream to normalized support-bank execution. The same
fixed32-tape machine parses all raw rows, generates their count, returns its
operand cursors, then performs the verified exact ordered normalization. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NativeNormalized
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairOrdinary.RecoveryExecution

noncomputable abbrev normalize := TapeEmbedding.machine 2 NormalizedAddition.machine
noncomputable abbrev machine := Composition.machine prepare normalize

end PCJ9eff70d512234a4c_Fixed.Materializer.NativeNormalized
