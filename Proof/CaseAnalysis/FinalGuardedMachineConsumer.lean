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

variable (sources : EightSources) {gamma : ℝ} (p : Parameters sources gamma) (W : WorkerData)

/-- Exactly the header/oracle/size/typed-family premises of the existing pinned
completeness bridges, with their fixed cap1. No semantic [0,1] condition. -/
def LegalWitness (n : ℕ) (x : BitInput n) (bits : List Bool) : Prop :=
  16*bits.length ≤ n ∧ CompetitorWitnessTriple.headerValid bits ∧
  ∃ oracle : BooleanCircuit ((outer sources W.k W.clock).result.pcp.nativeWidth n),
    decodeBooleanCircuit ((outer sources W.k W.clock).result.pcp.nativeWidth n)
      (RadixSemantics.value (BoundedFields.oracle bits)) = some oracle ∧
    oracle.size ≤ oracleSizeBound p.degree ((outer sources W.k W.clock).result.pcp.nativeWidth n) ∧
    ((∃ family : SymFamily sources W.k W.clock p x oracle,
        SumFamily.decode symmetricCircuitCodec NormalizedSymmetricThresholdCircuit.wireCount
          NormalizedSymmetricThresholdCircuit.descriptionBits (symLimits sources W.k W.clock p x oracle)
          (CloseoutWitnessPolicy.variableCount sources W.k W.clock x oracle)
          (RadixSemantics.value (BoundedFields.family bits)) = some family ∧
        BoundedFields.symmetric bits = true) ∨
     (∃ family : ThrFamily sources W.k W.clock p x oracle,
        SumFamily.decode thresholdCircuitCodec NormalizedThresholdThresholdCircuit.wireCount
          NormalizedThresholdThresholdCircuit.descriptionBits (thrLimits sources W.k W.clock p x oracle)
          (CloseoutWitnessPolicy.variableCount sources W.k W.clock x oracle)
          (RadixSemantics.value (BoundedFields.family bits)) = some family ∧
        BoundedFields.symmetric bits = false))

end
end NearCubicWires.RepairSource.CloseoutFinal.C10GuardedMachineConsumer
