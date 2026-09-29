import Proof.CaseAnalysis.FinalComposeWidths

/-! Paper C.10's supplier stage hands the fold its prepared bank. The docked
body acts only on the 218-prefix, so the two retained width words on extension
tapes 274/275 survive definitionally. This is S2's block seam with exactly those
two output equalities added, as authorized in external_in.md section 0.2. -/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10StageWidths

open LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairOrdinary.CloseoutFinalC10WorkerDock
open RepairOrdinary.CloseoutFinalC10WorkerFold
open RepairOrdinary.CloseoutFinalC10WorkerChain
open RepairOrdinary.CloseoutFinalC10WorkerEmitBody
open RepairOrdinary.CloseoutFinalC10WorkerEmitShape
open RepairOrdinary.CloseoutFinalC10WorkerEmitLoader
open RepairOrdinary.CloseoutFinalC10StageSeam
open RepairOrdinary.CloseoutFinalC10StageSeamBlock
open RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream
open C10TailCompose C10BodyWidths
open C10LengthGate

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.RepairSource.CloseoutFinal.C10StageWidths
