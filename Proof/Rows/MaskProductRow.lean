import Proof.Packets.PhysicalSupportReturn

/-! One actual Cartesian-product row emits a framed union mask and the two
false record tags, and increments a physical unary result counter. The mask
source may be at any position in its retained bank. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MaskProduct
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution

def cfg {s : Nat} (q : Fin s) (B dh mh : Nat) (left right : List Bool)
    (pos : Nat) (out count : List Bool) : Configuration 5 s :=
  ⟨q,![dh,mh,pos,out.length,count.length],![UnaryTemplate.tape B,left,right,out,count]⟩

def raw : Machine 5 5 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==4
  rule := fun q scan=>if q.val=0 then
    some ⟨if scan 0 then 1 else 2,![none,none,none,some (scan 0),none],
      ![.stay,.stay,.stay,.right,.stay]⟩
    else if q.val=1 then some ⟨0,![none,none,none,some (scan 1 || scan 2),none],
      ![.right,.right,.right,.right,.stay]⟩
    else if q.val=2 then some ⟨3,![none,none,none,some false,none],
      ![.stay,.stay,.stay,.right,.stay]⟩
    else if q.val=3 then some ⟨4,![none,none,none,some false,some true],
      ![.stay,.stay,.stay,.right,.right]⟩
    else none

end PCJ9eff70d512234a4c_Fixed.Materializer.MaskProduct
