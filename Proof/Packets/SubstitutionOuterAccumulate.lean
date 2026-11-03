import Proof.Packets.SubstitutionOuterData

/-! An actual outer-fold transaction: transfer the current monomial product,
add it on the left of the resident sum, save the sum, then restore product one.
The original source, atom table, count drivers, and constant one are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionOuter
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch

noncomputable def transfer := RecoveryFocus.machine accumulatorPorts VectorAccumulator.rightToLeft
noncomputable def add := RecoveryFocus.machine accumulatorPorts VectorAccumulator.machineRight
noncomputable def reset := RecoveryFocus.machine constantPorts VectorAccumulator.loadRight
noncomputable def accumulate := Composition.machine transfer (Composition.machine add reset)

end PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionOuter
