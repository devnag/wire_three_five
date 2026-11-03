import Proof.Rows.FinalNativeSignedResidue
import Proof.Rows.ResidueScaleCell
import Proof.Rows.NativeCircuitCount

/-! Reusable binary final-offset emitter: copy five bounded masters, negate,
append one framed residue without scanning the output, and clear all workers. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 20000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_OffsetEmitter
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.ExtIncidence SignedSortKey
noncomputable section

def palette (p w o :Nat):Fin 5→List Bool:=![frame (binary w 0),frame (binary w 0),frame (binary w p),[false],frame (binary w o)]
def bank (P W :Fin 5→List Bool) (U :Nat) (out :List Bool) (i :Fin 13):List Bool:=
 if h:i.val<5 then P ⟨i.val,h⟩ else
 if h:i.val<10 then W ⟨i.val-5,by omega⟩ else
 if i=10 then List.replicate U true else
 if i=11 then List.replicate (U+1) false else out

def cold (P :Fin 5→List Bool) (U :Nat) (out :List Bool):=bank P (fun _=>List.replicate U false) U out









end
end PCJ45bee56da9f34d5a_OffsetEmitter
