import Proof.Packets.CycleArithmeticAllocate
import Proof.Packets.CycleMaskWidth
import Proof.Packets.WindowSeedPrimitives
import Proof.Rows.PhysicalFocusBoundary
import Proof.Packets.PhysicalIndexReload
import Proof.Packets.ReusableNormalizedArithmetic

/-! Actual cold arithmetic bank: allocate all backing from the resident raw
reserve, compute both width templates from the resident C template, and copy
them into the reusable engine. Every other entry tape is empty. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ArithmeticCold
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open Theorem25Completion
noncomputable section

attribute [local irreducible] CycleArithmeticAllocate.machine CycleMaskWidth.machine WindowSeed.copy




end
end PCJ9eff70d512234a4c_Fixed.Materializer.ArithmeticCold
