import Proof.MachineModel.Runs

/-! One paid native stream terminator; the append cursor is explicit. -/
set_option autoImplicit false
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NativeTerminator
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch

def machine : Machine 1 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q _=>if q.val=0 then some ⟨1,fun _=>some false,fun _=>.right⟩ else none

end PCJ9eff70d512234a4c_Fixed.Materializer.NativeTerminator
