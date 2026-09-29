import Proof.CaseAnalysis.WitnessSource

/-! The complete cold source/oracle prefix has both physical early exits:
the machine-owned original-N cutoff precedes source construction, and the
actual R<=N comparison precedes cold oracle parsing. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdOracle
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open RepairSource ProjectionNormalization SourceInterfaces ExecutableInterfaces CanonicalWitnessCodec
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
abbrev base (k : ℕ):=ColdSource.tapes source k
def parser (k : ℕ):=ColdSource.old source k ∘ SelectedOracle.fields source k
def first (k CH Cpad cutoff : ℕ) (code : List Bool):=
  RecoveryFocus.machine (@GuardedOracle.old (base source k)) (ColdSource.machine source k CH Cpad cutoff code)
def second (k : ℕ):=GuardedOracle.machine (parser source k) (ColdSource.extra source k 2)
def cutoffSlot (k : ℕ):=GuardedOracle.old (ColdSource.extra source k 6)
def lengthSlot (k : ℕ):=GuardedOracle.old (ColdSource.extra source k 2)
def sourceSlots (k : ℕ) (i : Fin (HierarchySelectedSource.tapes source k)):=GuardedOracle.old (ColdSource.old source k i)
def machine (k CH Cpad cutoff : ℕ) (code : List Bool):=
  CloseoutRowsGateColdPair.machine (first source k CH Cpad cutoff code) (second source k)
    (fun scanned=>scanned (cutoffSlot source k))
def passed (k CH Cpad cutoff : ℕ) (code x bits : List Bool):=
  decide (max 2 cutoff ≤ x.length) && GuardedOracle.passed (SelectedOracle.width source k CH Cpad code x) x bits


end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdOracle
