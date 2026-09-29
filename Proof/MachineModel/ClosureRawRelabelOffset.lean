import Proof.MachineModel.ClosureRawRelabelMachine
import Proof.MachineModel.Runs

/-! Physically form the runtime offset N*yi+1 from retained unary N and yi.
The offset tape starts empty; the leading sentinel and one are constant bytes.
All four heads return to zero, with the full reset log preserved. -/
namespace NearCubicWires.P1Closure.RawRelabelOffset
open LocalBitMultitape RepairOrdinary RecoveryExecution ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def seed : Machine 3 3 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=2)
  rule:=fun q _=>if q=0 then some ⟨1,![none,none,some false],![.stay,.stay,.right]⟩
    else if q=1 then some ⟨2,![none,none,some true],![.stay,.stay,.right]⟩ else none

def raw:=Composition.machine seed ClockUnaryProduct.raw
def machine:=MaskedReset.machine raw (fun _=>true)

end NearCubicWires.P1Closure.RawRelabelOffset
