import Proof.CaseAnalysis.WitnessSelectedOracle
import Proof.Hierarchy.HierarchyStreamLayout
import Proof.Amplification.RecoveryFocusDock

/-! One use of the existing complete selected-PCP stream producer. Its
three inputs alias retained source fields and its workspace alone is fresh. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.StreamCall
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open RepairSource ProjectionNormalization SourceInterfaces ExecutableInterfaces VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def old {t : ℕ} (i : Fin t) : Fin (t+48):=i.castAdd 48
def slots {t : ℕ} (fields : Fin 3→Fin t) (i : Fin 48) : Fin (t+48):=
  if i.val=0 then old (fields 0) else if i.val=13 then old (fields 1)
  else if i.val=14 then old (fields 2) else i.natAdd t

def machine {t : ℕ} (fields : Fin 3→Fin t):=RecoveryFocus.machine (slots fields) Streams.machine

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.StreamCall
