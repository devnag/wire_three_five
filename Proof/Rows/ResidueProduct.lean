import Proof.Rows.FinalNativeSignedResidue
import Proof.Amplification.RecoveryRadixInput
import Proof.CaseAnalysis.FinalSelectorLoadMasks
import Proof.Circuits.DecompositionNativeMagnitude
import Proof.Hierarchy.HierarchyAllocation
import Proof.MachineModel.UInputFields
import Proof.Rows.FinalPrimeCoefficientReduce
import Proof.Rows.Plan
import Proof.Hierarchy.HierarchyBinaryMultiply

/-! A paid framed-binary product followed by physical MSB conversion and
modular reduction. The left operand has the actual product width; a caller
must pay ClockScalarFields to widen a shorter residue before this boundary. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_ResidueProduct
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding
open SignedSortKey RadixSemantics
noncomputable section

def extras (W p w cap D : Nat) : Fin 14→List Bool:=
  ![[],[],List.replicate D false,[],[],frame (binary w 0),frame (binary w 0),
    frame (binary w p),[false],List.replicate cap false,CompareMachine.word (2*W),
    frame (binary w 0),[false],List.replicate D false]
def input (W a p w cap D : Nat) (bits : List Bool) : Fin 28→List Bool:=
  Fin.addCases (m:=14) (n:=14) (motive:=fun _=>List Bool)
    (HierarchyMultiplyEntry.input14 W a bits) (extras W p w cap D)

end
end PCJ45bee56da9f34d5a_ResidueProduct
