import Proof.PCP.ProjectionNormalizationForwardRules
import Proof.MachineModel.OrdinaryTransitionEvent
import Proof.MachineModel.OrdinaryRewindWorkspace

namespace NearCubicWires.RepairSource.ProjectionNormalization.PhysicalParityProbe
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def boot : Machine 4 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then some ⟨1,![none,none,some true,none],fun _ => .stay⟩ else none
def finish : Machine 4 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q bits => if q.val=0 then some ⟨1,![none,none,none,some (xor (bits 3) (bits 2))],fun _ => .stay⟩ else none
def slots : Fin 3 → Fin 4 := ![0,1,2]
noncomputable def compareProgram := RecoveryFocus.machine slots ClauseEquality.machine
noncomputable def tailProgram := Composition.machine compareProgram finish
noncomputable def raw := Composition.machine boot tailProgram
noncomputable def machine := CursorRestore.machine raw 0

end NearCubicWires.RepairSource.ProjectionNormalization.PhysicalParityProbe
