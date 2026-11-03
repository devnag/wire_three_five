import Proof.MachineModel.Machine
import Proof.MachineModel.ClockUnaryProduct

/-! Fixed physical stream reindexer. Tape 1 is the retained unary displacement
with a leading false sentinel; every address block gets that many new marks.
The next composition supplies that displacement by paid multiplication. -/
namespace NearCubicWires.P1Closure.RawRelabelMachine
open LocalBitMultitape RepairOrdinary RecoveryExecution ExtIncidence
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 3 6 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=5)
  rule:=fun q b=>if q=0 then some
      ⟨if b 0 then 1 else 5,![none,none,some (b 0)],![.right,.stay,.right]⟩
    else if q=1 then some (if b 0 then ⟨2,fun _=>none,fun _=>.stay⟩
      else ⟨0,![none,none,some false],![.right,.stay,.right]⟩)
    else if q=2 then some (if b 1 then
      ⟨2,![none,none,some true],![.stay,.right,.right]⟩
      else ⟨3,fun _=>none,![.stay,.left,.stay]⟩)
    else if q=3 then some (if b 1 then ⟨3,fun _=>none,![.stay,.left,.stay]⟩
      else ⟨4,fun _=>none,![.stay,.right,.stay]⟩)
    else if q=4 then some
      ⟨if b 0 then 4 else 1,![none,none,some (b 0)],![.right,.stay,.right]⟩
    else none

end NearCubicWires.P1Closure.RawRelabelMachine
