import Proof.CaseAnalysis.WitnessGuardedOracle

/-! The original framed input is counted once and screened against the
machine-owned finite cutoff. Only the passing branch runs the hierarchy
and the one selected PCP source; its original-N counter remains available. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdSource
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open RepairSource ProjectionNormalization SourceInterfaces ExecutableInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
abbrev base (k : ℕ):=HierarchySelectedSource.tapes source k
def tapes (k : ℕ):=base source k+8
def old (k : ℕ) (i : Fin (base source k)) : Fin (tapes source k):=i.castAdd 8
def extra (k : ℕ) (i : Fin 8) : Fin (tapes source k):=i.natAdd (base source k)
def slots (k : ℕ) (i : Fin 8):=
  if i.val=0 then old source k (SelectedOracle.fields source k 0) else extra source k i
def first (k cutoff : ℕ):=RecoveryFocus.machine (slots source k) (InputGuard.machine (max 2 cutoff))
def second (k CH Cpad : ℕ) (code : List Bool):=
  RecoveryFocus.machine (old source k) (HierarchySelectedSource.machine source k CH Cpad code)
def machine (k CH Cpad cutoff : ℕ) (code : List Bool):=
  CloseoutRowsGateColdPair.machine (first source k cutoff) (second source k CH Cpad code)
    (fun scanned=>scanned (extra source k 6))


end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdSource
