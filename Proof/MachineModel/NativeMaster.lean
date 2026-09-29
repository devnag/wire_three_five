import Proof.MachineModel.NativeShort

/-! All fifteen distinct source words for native initialization are outputs
of one fixed ordinary run over the same measured cache. -/
namespace NearCubicWires.ExtIncidence.NativeMaster
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RepairRepresentation
open RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def fields : Fin 15→Fin 149:=![0,15,27,3,31,57,86,135,4,146,139,143,88,53,141]

end NearCubicWires.ExtIncidence.NativeMaster

