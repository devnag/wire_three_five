import Proof.Packets.PacketsXDescendingWindowSetup

/-! Physical advance of the retained outer binary degree. The completed
inner loop's zero unary coordinate is retained and all local heads return. -/
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.DescendingWindowDegree
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open CloseoutRowsModeWindowLayout
open DescendingWindowSetup (H A)
attribute [local irreducible] DescendingWindowCounters.binaryPart

def slots : Fin 3→Fin 61 := ![48,57,51]
noncomputable def machine := RecoveryFocus.machine slots DescendingWindowCounters.binaryPart

end PCJ9eff70d512234a4c_Fixed.Materializer.DescendingWindowDegree
