import Proof.Packets.MaskSelect
import Proof.Amplification.RecoveryFocusedMachine

/-! One actual candidate-normalization step. The coefficient is computed from
resident original records, then controls byte emission and the retained counter.
No machine, transition, coefficient bit, or run witness is an input premise. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ParityFilter
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.VerifierDecoding

abbrev scanSize := Fintype.card (RepeatMachine.Control PhysicalParityReuse.size)+2

def boot : Machine 9 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then
    some ⟨1,fun i => if i=3 then some false else none,fun _ => .stay⟩ else none

noncomputable def scan : Machine 9 scanSize := TapeEmbedding.machine 2 PhysicalParityRestore.machine

def slots : Fin 4 → Fin 9 := ![0,7,8,3]

noncomputable def emit : Machine 9 6 := RecoveryFocus.machine slots MaskSelect.machine
noncomputable def tail := Composition.machine scan emit
noncomputable def body := Composition.machine boot tail

end PCJ9eff70d512234a4c_Fixed.Materializer.ParityFilter
