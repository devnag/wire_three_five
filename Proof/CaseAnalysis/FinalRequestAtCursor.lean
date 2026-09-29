import Proof.CaseAnalysis.RowsEstimatorParityCounter

/-! A short physical request segment for the existing same-source PCPP cache.
Advance its already allocated unary address, preserving all other cache tapes,
then apply the actual cached clause reader. No PCPP request word or fresh source
call is supplied to the hot path. Cache construction and admission remain in
the existing cold source pipeline and must be connected by the enclosing pre.
-/
namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10RequestAtCursor

open NearCubicWires
open NearCubicWires.LocalBitMultitape
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def indexSlot : Fin 1 → Fin 19 := fun _ => 14
noncomputable def advance := RecoveryFocus.machine indexSlot CloseoutRowsEstimatorParity.Counter.machine


end NearCubicWires.RepairOrdinary.CloseoutFinalC10RequestAtCursor
