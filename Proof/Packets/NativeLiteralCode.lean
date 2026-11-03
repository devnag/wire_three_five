import Proof.Packets.MaskProductReady
import Proof.MachineModel.Encoding

/-! The literal's unchanged natural-number code is recovered from its actual
native singleton pair record. The source cursor advances over the record;
the produced unary index is returned to head one. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NativeLiteralCode
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.VerifierDecoding

def word (code : Nat) := [true,true]++List.replicate code true++[false,false,false,false]
def machine : Machine 2 7 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==6
  rule:=fun q scan=>
    if q.val=0 then some ⟨1,![none,some false],![.right,.right]⟩
    else if q.val=1 then some ⟨2,fun _=>none,![.right,.stay]⟩
    else if q.val=2 then some (if scan 0 then ⟨2,![none,some true],![.right,.right]⟩
      else ⟨3,fun _=>none,![.right,.stay]⟩)
    else if q.val=3 then some ⟨4,fun _=>none,![.right,.stay]⟩
    else if q.val=4 then some ⟨5,fun _=>none,![.right,.stay]⟩
    else if q.val=5 then some ⟨6,fun _=>none,![.right,.stay]⟩
    else none

def returnSlot : Fin 1→Fin 2 := ![1]
noncomputable def readyMachine := Composition.machine machine
  (RecoveryFocus.machine returnSlot PairCountReady.machine)

end PCJ9eff70d512234a4c_Fixed.Materializer.NativeLiteralCode
