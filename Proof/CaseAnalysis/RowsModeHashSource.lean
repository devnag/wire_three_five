import Proof.CaseAnalysis.RowsModeHashLoop

/-! The complete hash-prefix producer consumes original depth at head zero
and emits the ordered bits of the literal hash of the original seed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeHashSource
open LocalBitMultitape RecoveryRootRound ExtDecompositionBatch RepairSource.VerifierDecoding
open CloseoutRowsModeHashLoop CloseoutRowsModeHashMeaning
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slot : Fin 1→Fin 10:=fun _=>9
noncomputable def start:=RecoveryFocus.machine slot (RowCoordinateIncrement.shift .right)
noncomputable def machine:=Composition.machine start CloseoutRowsModeHashLoop.machine

end NearCubicWires.RepairOrdinary.CloseoutRowsModeHashSource
