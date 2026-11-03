import Proof.Amplification.RecoveryListPredecessor
import Proof.CaseAnalysis.RowsModeParityReusable
import Proof.Hierarchy.HierarchyBinaryKernel

/-! Compute the shifted binomial guard from the original offset and shift
fields by actual addition, predecessor and Lucas scans. No binomial scalar
or saturating-zero branch is supplied to the program. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeShift
open LocalBitMultitape RecoveryRootRound SignedSortKey ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def data (w offset b scratch C : Nat) (nonzero guard : Bool) : Fin 6→List Bool:=
  ![frame (binary w offset),frame (binary w b),frame (binary w scratch),[nonzero],[guard],List.replicate C false]
def addSlots : Fin 4→Fin 6:=![0,1,2,5]
def predSlots : Fin 3→Fin 6:=![2,3,5]
def paritySlots : Fin 4→Fin 6:=![2,1,4,5]
noncomputable def add:=RecoveryFocus.machine addSlots BoundaryAdvance.machine
noncomputable def pred:=RecoveryFocus.machine predSlots RecoveryListPredecessor.machine
noncomputable def parity:=RecoveryFocus.machine paritySlots CloseoutRowsModeParityReusable.machine
noncomputable def machine:=Composition.machine (Composition.machine add pred) parity

end NearCubicWires.RepairOrdinary.CloseoutRowsModeShift
