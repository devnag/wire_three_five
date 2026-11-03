import Proof.Packets.NormalizerMaterializeData
import Proof.Packets.NormalizerData

/-! Complete cold-entry normalization. Scratch is truly blank initially;
the zero reserves used in internal proofs are removed by the interpreter's
proved padding transport, and flag/count sentinels are written by boot. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NormalizeCold
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.VerifierDecoding

noncomputable def machine := Composition.machine boot Normalize.machine

end PCJ9eff70d512234a4c_Fixed.Materializer.NormalizeCold
