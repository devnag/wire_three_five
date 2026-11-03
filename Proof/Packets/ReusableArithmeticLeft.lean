import Proof.Packets.ReusableArithmeticCleanup

/-! Symmetric accumulator transaction for frozen left folds. The operation
still receives (left,right) in its original order; only its output destination
changes. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ReusableArithmetic
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch

noncomputable def machineLeft {s : Nat} (p : Machine 30 s) :=
  Composition.machine (Composition.machine (Composition.machine (worker p)
    (copyMachine 20 25)) (copyMachine 21 28)) eraseMachine

end PCJ9eff70d512234a4c_Fixed.Materializer.ReusableArithmetic
