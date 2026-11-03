import Proof.Packets.PacketsXDescendingWindowReady
import Proof.Packets.PacketsXDescendingWindowDegree

/-! One complete physical outer-window iteration: paid preparation,
descending inner antidiagonal, then retained binary-degree advance. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.DescendingWindowOuter
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsModeWindowScalar
open DescendingWindowSetup (H A)

noncomputable def machine := Composition.machine
  (Composition.machine DescendingWindowSetup.machine DescendingWindowReady.machine) DescendingWindowDegree.machine

end PCJ9eff70d512234a4c_Fixed.Materializer.DescendingWindowOuter
