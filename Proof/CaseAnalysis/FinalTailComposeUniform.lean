import Proof.CaseAnalysis.FinalStageContracts
/-! Paper C.10: "The machine passes validity only if the first estimated average
is at most 2ζ and all estimated second moments are at most 1+ζ." C.10.1 accepts
only when the estimated acceptance mean is at least (c_p+s_p)/2. This constructor
fuses those tests, the phase realizations, and halting into the same fixed run.
The supplier obligations are precisely S2's stage contract and the semantic
hypotheses of realizes_of_stage; native parity, decoding, copies, and the tail
are constructed here. The approved R3 fallback uses StageData.budget, bounded
by StageBlock.hfuel. A conditional constructor does not inhabit its premises. -/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10TailComposeUniform

open LocalBitMultitape ExtDecompositionBatch ComponentwisePolynomial
open RepairOrdinary RepairOrdinary.CloseoutWitness RepairRepresentation SourceInterfaces SupplierPipeline
open CompetitorRationalGap CloseoutRowsOriginalSchedule
open RepairOrdinary.CloseoutFinalC10Exactness RepairOrdinary.CloseoutFinalC10Realizes
open RepairOrdinary.CloseoutFinalC10WorkerChain RepairOrdinary.CloseoutFinalC10WorkerDock
open RepairOrdinary.CloseoutFinalC10WorkerDockSeam RepairOrdinary.CloseoutFinalC10WorkerFold
open RepairOrdinary.CloseoutFinalC10WorkerEmitLoader RepairOrdinary.CloseoutFinalC10WorkerEmitShape
open RepairOrdinary.CloseoutFinalC10StageSeam RepairOrdinary.CloseoutFinalC10SupplierCalls
open RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry contributions)
open C10Verdict C10LengthGate C10TailCompose C10BodyWidths C10TailComposeVerdict

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (sources : EightSources) (k : ℕ) {gamma : ℝ} (p : Parameters sources gamma)
  (S : StageData sources k p) (hs : StageBlock sources k p S)

def tailStates : ℕ := (C10TailVerdictUniform.tail_uniform_heads (constantsOf sources)).choose

def tailMachine : LocalBitMultitape.Machine C10TailVerdict.tailBank (tailStates sources) :=
  (C10TailVerdictUniform.tail_uniform_heads (constantsOf sources)).choose_spec.choose

end
end NearCubicWires.RepairSource.CloseoutFinal.C10TailComposeUniform
