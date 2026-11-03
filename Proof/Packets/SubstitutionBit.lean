import Proof.Packets.SubstitutionAtom
import Proof.Packets.PhysicalBitCall
import Proof.Packets.VectorCounterDecrement

/-! One literal-mask position is consumed backwards. The actual unary code
counter is decremented, the source cursor moves left, and its actual bit
controls the atom lookup/multiplication call. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionBit
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.VerifierDecoding

def counterSlot : Fin 1→Fin 38 := ![35]
def sourceSlot : Fin 1→Fin 38 := ![37]
noncomputable def decrement := RecoveryFocus.machine counterSlot VectorCounter.decrement
noncomputable def sourceLeft := RecoveryFocus.machine sourceSlot (Completion.PhysicalDriverMoves.machine 1 .left)
noncomputable def atom := TapeEmbedding.machine 1 SubstitutionAtom.machine
noncomputable def conditional := PhysicalBitCall.machine (37 : Fin 38) atom
noncomputable def machine := Composition.machine decrement (Composition.machine sourceLeft conditional)

end PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionBit
