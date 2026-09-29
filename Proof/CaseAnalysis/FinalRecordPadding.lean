import Proof.CaseAnalysis.FinalEnvelopeCounter
import Proof.CaseAnalysis.FinalPartsSchedule

namespace NearCubicWires.RepairSource.CloseoutFinal.C10RecordPadding

open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutWitness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerChain (worker)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDock (DockReady joinScalarWidth flag
  result inputTape)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockSeam (phaseRecords)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitShape (EmitEntry)
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline
open C10TailComposeUniform

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## Section 1  The words stage's budget is monotone in the call count -/

/-! ## Section 2  The stage, run at a length-only fuel over the UNPADDED stream -/

/-! ## Section 3  The seam, with the equality replaced by the paper's bound -/

/-! ## Section 4  The producer side: the loop writes its own count, with no hypothesis -/

/-! ## Section 5  The cap, and where it lands on the width schedule -/

/-! ## Section 6  The payoff: `StageReady` at the schedule, with no record-count
hypothesis -/


end NearCubicWires.RepairSource.CloseoutFinal.C10RecordPadding
