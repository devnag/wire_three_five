import Proof.Packets.NativeLiteralCode

/-! Direct native singleton emission from the actual unary occurrence index.
No pairing or supplied framed binary code is used. Both the retained counter
and its cursor are restored while every output framing cell is written. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.IdentityCodeRecord
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.VerifierDecoding

def machine : Machine 2 9 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==8
  rule:=fun q scan=>
    if q.val=0 then some ⟨1,![none,some true],![.stay,.right]⟩
    else if q.val=1 then some ⟨2,![none,some true],![.stay,.right]⟩
    else if q.val=2 then some (if scan 0 then ⟨2,![none,some true],![.right,.right]⟩
      else ⟨3,fun _=>none,![.left,.stay]⟩)
    else if q.val=3 then some (if scan 0 then ⟨3,fun _=>none,![.left,.stay]⟩
      else ⟨4,fun _=>none,![.right,.stay]⟩)
    else if q.val=4 then some ⟨5,![none,some false],![.stay,.right]⟩
    else if q.val=5 then some ⟨6,![none,some false],![.stay,.right]⟩
    else if q.val=6 then some ⟨7,![none,some false],![.stay,.right]⟩
    else if q.val=7 then some ⟨8,![none,some false],![.stay,.right]⟩
    else none

end PCJ9eff70d512234a4c_Fixed.Materializer.IdentityCodeRecord
