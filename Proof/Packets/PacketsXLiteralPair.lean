import Proof.Packets.PacketsXLiteralPairRecord
import Proof.PCP.PCPPairColdRun
import Proof.Rows.PhysicalFocusBoundary

/-! A cold physical native singleton-pair record from two framed binary
operands. The entire private workspace is produced by executed pair arithmetic;
zero inputs, including Nat.pair 0 0, use the same fixed machine. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.LiteralPairCold
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.RadixSemantics NearCubicWires.RepairOrdinary.SignedSortKey
noncomputable section

def recordSlots : Fin 4→Fin 36 := ![26,31,32,35]
def recordMachine := RecoveryFocus.machine recordSlots LiteralPairRecord.machine
def machine := Composition.machine (TapeEmbedding.machine 1 PCPPairCold.machine) recordMachine

end
end PCJ9eff70d512234a4c_Fixed.Materializer.LiteralPairCold
