import Proof.Packets.CycleFieldPrimitives

/-! A raw unary capacity physically allocates a fixed block of zero tapes.
The rewind log is also created by execution; no preallocated zero bank is assumed. -/
set_option autoImplicit false
set_option warningAsError true
namespace CycleFields.ZeroAllocate
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryRootRound

def machine (t : Nat):=RecoveryScratchErase.resetMachine t

end CycleFields.ZeroAllocate
