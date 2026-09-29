import Proof.CaseAnalysis.RowsCanonicalFlag
import Proof.CaseAnalysis.RowsGateArityCheck
import Proof.CaseAnalysis.WitnessNodeFlag

/-! The outer balanced payload must contain exactly the SAME source's V
sums. The one canonical traversal retains its field stream and count;
an existing count comparison and one flag fold precede any family loop. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyCount
open LocalBitMultitape RecoveryRootRound RadixSemantics
open PCPPNativeCanonicalWalk PCPPNativeCanonicalTree RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def old (i : Fin 174) : Fin 177:=i.castAdd 3
def compareSlots : Fin 4→Fin 177:=![41,174,175,176]
def flagSlots : Fin 2→Fin 177:=![175,172]
def first:=RecoveryFocus.machine old CanonicalTest.machine
def compare:=RecoveryFocus.machine compareSlots CloseoutRowsGateArityCheck.machine
def flag:=RecoveryFocus.machine flagSlots NodeRound.flagMachine
def prefixMachine:=Composition.machine first compare
def machine:=Composition.machine prefixMachine flag
def count (bits : List Bool):=(tree (value bits)).atoms.length
def accepted (bits : List Bool) (V : ℕ):=
  CloseoutRowsCanonicalFlag.flag bits && decide (count bits=V)


end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyCount
