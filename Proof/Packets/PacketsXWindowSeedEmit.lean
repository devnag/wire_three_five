import Proof.Packets.PacketsXDescendingWindowLoop
import Proof.Packets.WindowSeed
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Sublists
import Mathlib.Tactic
import Proof.CaseAnalysis.RowsModeWindowBinomial
import Proof.Packets.PacketsXNormalizerOperations
import Proof.Supplier.RowTupleSubsets

/-! Complete actual window provider core: cold/reentry seeding followed by
both checked descending runtime enumeration loops. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowSeed
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
noncomputable section

def emit := TapeEmbedding.machine 7 DescendingWindowLoop.machine
def complete := Composition.machine machine emit

end
end PCJ9eff70d512234a4c_Fixed.Materializer.WindowSeed
