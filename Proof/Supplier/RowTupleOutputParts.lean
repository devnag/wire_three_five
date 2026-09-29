import Proof.Supplier.RowTupleAdvance

/-! The live selected-tuple output shares the binary incrementer's erased
workspace. Appending restores the tuple head and retains its exact bytes. -/
namespace NearCubicWires.RepairOrdinary.RowTupleOutputParts
open LocalBitMultitape RecoveryExecution RecoveryRootRound RowTupleFilterParts SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def candidate := TapeEmbedding.machine 4 RowTupleCandidate.machine
noncomputable def advance := TapeEmbedding.machine 1 RowTupleAdvance.machine

def slots : Fin 3→Fin 18 := ![0,17,16]
noncomputable def append := RecoveryFocus.machine slots PCPSerializerReuse.copyMachine

end NearCubicWires.RepairOrdinary.RowTupleOutputParts
