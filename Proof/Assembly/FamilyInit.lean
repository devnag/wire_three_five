import Proof.Assembly.Generator

/-! A concrete two-stage generator: descriptor/scalar production followed by
one blank-bank initializer. The initializer is uniform in runtime values.
Its certified physical interface and cost are consumed by the front proof.
No input or execution witness is inserted into the literal theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJ515eaa990d75455b_FamilyInit
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.RecoveryExecution
open PCJ1fef9807c6954e94_Native

/-- Values are runtime data, not parameters of the initializer's code.
The front also physically computes the N*b driver. -/
structure Scalars where
  S : Nat
  R : Nat
  B : Nat
  b : Nat
  v : Nat
  N : Nat

/-- Prefix code starts at the actual nine-word Input bank. Its result carries
semantic fields and its complete physical exit, before initialization. -/
structure PrefixCode where
  printer : WilliamsAlgorithm
  scratch : Nat
  states : Nat
  machine : Machine (PCJf990607ff5714139_Generator.tapes printer (7+scratch)) states
  policy : PCJf990607ff5714139_Generator.Policy
  result : PCJf990607ff5714139_Generator.Input → PCJf990607ff5714139_Generator.Result (PCJf990607ff5714139_Generator.tapes printer (7+scratch))

end PCJ515eaa990d75455b_FamilyInit
