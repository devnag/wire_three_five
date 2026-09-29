import Proof.Supplier.EquationWidenLoop

/-! Physical zero scalar emission for the odd right coordinate. The actual
bit-count driver is retained and rewound, and the destination stays at its
global append cursor. No false payload bit is removed as backing storage. -/
namespace NearCubicWires.RepairOrdinary.EquationZeroField
open LocalBitMultitape RecoveryExecution
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 2 4 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==3
  rule := fun q bs =>
    if q.val=0 then some
      (if bs 0 then ⟨1,![none,some true],![.stay,.right]⟩
      else ⟨2,![none,some false],![.left,.right]⟩)
    else if q.val=1 then some ⟨0,![none,some false],![.right,.right]⟩
    else if q.val=2 then some
      (if bs 0 then ⟨2,fun _ => none,![.left,.stay]⟩
      else ⟨3,fun _ => none,![.right,.stay]⟩)
    else none

end NearCubicWires.RepairOrdinary.EquationZeroField
