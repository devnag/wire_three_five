import Proof.Rows.NativeCircuitPrepare

/-! Produce the actual fifth native header's unary circuit count while keeping
the original source cursor at the first circuit. Earlier fields are only skipped. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_CircuitCountAdvance
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open PCJ45bee56da9f34d5a_CircuitCountCopy
noncomputable section
attribute [local irreducible] PCJ45bee56da9f34d5a_TopArity.machine


-- Copy needs its capacity and log at3,4, with the remaining10 fresh reader tapes.

def budget (tag q L target N U : Nat):=
 PCJ45bee56da9f34d5a_CircuitCountCopy.budget tag q L target N+2*PCPPQueryNatural.budget N+8*U+21

end
end PCJ45bee56da9f34d5a_CircuitCountAdvance
