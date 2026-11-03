import Proof.Assembly.AppendOutputFrame
import Proof.SourceAssembly.SourceNativeList

/- The exact packet-index producer: real native header, real count stream,
real retained unary count. Its output cursor is the logical word endpoint. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
namespace PCJ6e421fabe2aa4155_SourceIndexExact
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryExecution RepairOrdinary.RecoveryRootRound RepairRepresentation
open RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
open PCJ6e421fabe2aa4155_SourceNativeList (stream savedFields)
noncomputable section

def copySlots : Fin 4 → Fin 5 := ![3,1,2,4]
def directions (i : Fin 5) : HeadMove := if i=4 then .right else .stay
def header := TapeEmbedding.machine 2 (PCPPQueryField.machine true)
def advance := DecompositionCountPosition.move directions
def copies := RecoveryFocus.machine copySlots PCJ6e421fabe2aa4155_SourceNativeList.machine
def machine := Composition.machine (Composition.machine header advance) copies

def budget (xs : List Nat) := 2*natBitLength xs.length+(stream xs).length+5*xs.length+9

def framed := AppendOutputFrame.machine machine 2

end
end PCJ6e421fabe2aa4155_SourceIndexExact
