import Proof.CaseAnalysis.WitnessNativePipelineDock

/-! The five cold-prefix fields are the same source word, actual raw R/Q,
canonical Q bits and decoded oracle descriptor. Their aliases are disjoint. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdNative
open LocalBitMultitape RecoveryRootRound RecoveryExecution
open RepairRepresentation RepairSource ProjectionNormalization SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
abbrev base (k : ℕ):=GuardedOracle.tapes (ColdOracle.base source k)
def sourceFields (k : ℕ) : Fin 4→Fin (HierarchySelectedSource.tapes source k):=
  Fin.addCases (m:=3) (n:=1) (motive:=fun _=>Fin (HierarchySelectedSource.tapes source k))
    (SelectedStreams.selectedFields source k) (fun _=>SelectedStreams.selectedBits source k 1)
def fields (k : ℕ) : Fin 5→Fin (base source k):=
  Fin.addCases (m:=4) (n:=1) (motive:=fun _=>Fin (base source k))
    (ColdOracle.sourceSlots source k ∘ sourceFields source k)
    (fun _=>GuardedOracle.descriptorSlot (ColdOracle.base source k))


end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdNative
