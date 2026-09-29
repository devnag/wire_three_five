import Proof.CaseAnalysis.FinalGuardedStageConsumer
import Proof.CaseAnalysis.FinalDecidesBridgeUniform

/-! Paper C.10's chosen guarded worker reaches the literal Machine/Theorem2.5
consumers. Data choices precede the physical/semantic requirements. Legal
contradiction witnesses use the unchanged pinned SYM/THR bridges at cap1;
rejected descriptions need no records. The outer onset is independent of the
cold preprocessing cutoff. No physical admission or record run is asserted here. -/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10GuardedMachineConsumer
open LocalBitMultitape RepairOrdinary RepairOrdinary.CloseoutWitness CompetitorRationalGap
open SelectedRecoveryIntegration CloseoutLanguage SourceInterfaces RepairRepresentation SupplierPipeline
open CircuitRestriction CanonicalWitnessCodec RecoveryScheduleEnvelope
open ExtDecompositionBatch CloseoutRowsOriginalSchedule
open C10TotalDecode C10DecidesUniform C10Verdict C10Fusion C10GuardedStageConsumer

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-- All implementation choices are fixed before their proof requirements. -/
structure WorkerData where
  k : ℕ
  clock : OrdinaryClock (fun n => n^(k+2))
  tapes : ℕ
  states : ℕ
  worker : LocalBitMultitape.Machine tapes states
  result : Fin tapes
  fuel : ℕ → ℕ
  onset : ℕ
  passed : (n : ℕ) → BitInput n → List Bool → Bool

end
end NearCubicWires.RepairSource.CloseoutFinal.C10GuardedMachineConsumer
