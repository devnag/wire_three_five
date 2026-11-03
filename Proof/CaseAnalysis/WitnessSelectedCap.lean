import Proof.CaseAnalysis.WitnessOracleCapCall

/-! The actual source and decoded oracle produce the exact size verdict.
The full measured native bank survives for the original node/cache continuation. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SelectedCap
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open RepairSource ProjectionNormalization SourceInterfaces ExecutableInterfaces VerifierDecoding CanonicalWitnessCodec
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
abbrev base (k : ℕ):=SelectedCounters.tapes source k
abbrev tapes (k G : ℕ):=base source k+OracleCap.Call.extra G
def fields (k : ℕ) : Fin 2→Fin (base source k):=
  SelectedCounters.slots source k ∘ (![72,32] : Fin 2→Fin 75)
def old (k G : ℕ) (i : Fin (base source k)) : Fin (tapes source k G):=OracleCap.Call.old G i
def slots (k G : ℕ) (i : Fin 75):=old source k G (SelectedCounters.slots source k i)
def first (k CH Cpad G : ℕ) (code : List Bool):=
  TapeEmbedding.machine (OracleCap.Call.extra G) (SelectedCounters.machine source k CH Cpad code)
def second (k G : ℕ):=OracleCap.Call.machine G (fields source k)
def machine (k CH Cpad G : ℕ) (code : List Bool):=
  Composition.machine (first source k CH Cpad G code) (second source k G)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.SelectedCap
