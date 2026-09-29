import Proof.CaseAnalysis.RowsGateHeader
import Proof.CaseAnalysis.WitnessOracleCapCall
import Proof.MachineModel.CanonicalRationalValidationProgram

/-! One tagged-pair reader serves the sum header, a term, and its rational
coefficient. The existing triple fields/classifiers suffice; the third cell
is required to be the literal empty tail. No reserialization is performed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.PairHeader
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open CanonicalBinary CompetitorRationalProducts CompetitorWitnessTriple
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def valid (bits : List Bool) : Prop:=
  field bits 0=1 ∧ field bits 2=1 ∧ field bits 4=0 ∧ node bits 6=0 ∧ field bits 5=0
def codeWord (bits : List Bool) (i : Fin 2):=RecoveryFixedUnpair.leftWord (word bits (2*i.val+1))

def firstSlots (i : Fin 148) : Fin 149:=i.castAdd 1
def fifthSlots : Fin 6→Fin 149:=![118,142,143,144,145,146]
def finishSlots : Fin 6→Fin 149:=![123,128,132,137,142,148]
def first:=RecoveryFocus.machine firstSlots CloseoutRowsGateHeader.machine
def fifth:=RecoveryFocus.machine fifthSlots CompetitorWitnessKind.machine
def finish:=RecoveryFocus.machine finishSlots CompetitorWitnessHeader.gate
def prefixMachine:=Composition.machine first fifth
def machine:=Composition.machine prefixMachine finish


end
end NearCubicWires.RepairOrdinary.CloseoutWitness.PairHeader
