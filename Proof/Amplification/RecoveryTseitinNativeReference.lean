import Proof.Amplification.RecoveryTseitinNativeOperands

/-! Original native node input to actual canonical references. All native
parsing, operand conversion, unary addition and binary reference generation
execute on the fixed ordinary machine; the original source and tag survive. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinNative
open LocalBitMultitape RepairOrdinary RepairRepresentation RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def referencesMachine := Composition.machine operandsMachine
  (RecoveryFocus.machine referenceSlots RecoveryTseitinReferences.coldMachine)
def referencesBudget (arity index tag a b : Nat) :=
  operandsBudget tag a b+1+RecoveryTseitinReferences.coldBudget arity index a b

end NearCubicWires.RepairSource.RecoveryTseitinNative
