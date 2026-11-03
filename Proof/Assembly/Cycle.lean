import Proof.Assembly.Family

/-! One source-global preparation/refill program is certified by its actual
normalized-row loop and its two boundary programs. The produced ds is exactly
the caller's fixed dataList, never an arbitrary supplier. All fuel and every
ambient tape/head remain explicit. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
namespace PCJ38fbfed565f64139_Cycle
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtIncidence NearCubicWires.ExtDecompositionBatch
open NearCubicWires.P1Closure NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed
noncomputable section

structure Code {printer : WilliamsAlgorithm} {t : Nat}
    (row : PCJ38fbfed565f64139_Row.Code printer t) (U : Nat) where
  slots : Fin (t+1) → Fin U
  injective : Function.Injective slots
  beforeStates : Nat
  before : Machine U beforeStates
  afterStates : Nat
  after : Machine U afterStates

def machine {printer : WilliamsAlgorithm} {t U : Nat}
    {row : PCJ38fbfed565f64139_Row.Code printer t} (c : Code row U) :=
  Composition.machine c.before
    (Composition.machine (RecoveryFocus.machine c.slots (PCJ38fbfed565f64139_Family.machine printer row)) c.after)

end
end PCJ38fbfed565f64139_Cycle
