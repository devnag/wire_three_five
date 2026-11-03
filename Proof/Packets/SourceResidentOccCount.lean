import Proof.Packets.SourceResidentCopies
import Proof.Assembly.Production

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceResident
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryExecution RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
noncomputable section

/-! ## Reading frames and drivers -/

/-! ## The frame counter -/

namespace Cnt

/-- Tape 0 the frames, tape 1 the driver `1^L`, tape 2 the output. State 0 at a marker cell: the driver ended —
write the closing `false` and halt; a `true` marker — skip the pair (state 1); a `false` marker (a frame's end) —
write `true` (state 2 writes the second `true` and steps past it). -/
def machine : Machine 3 4 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 3
  rule := fun q b =>
    if q.val = 0 then some (if b 1 then (if b 0 then ⟨1, ![none, none, none], ![.right, .right, .stay]⟩
        else ⟨2, ![none, none, some true], ![.stay, .stay, .right]⟩)
      else ⟨3, ![none, none, some false], ![.stay, .stay, .stay]⟩)
    else if q.val = 1 then some ⟨0, ![none, none, none], ![.right, .right, .stay]⟩
    else if q.val = 2 then some ⟨0, ![none, none, some true], ![.right, .right, .right]⟩
    else none

end Cnt

def occM := MaskedReset.machine Cnt.machine (fun _ => true)

/-- Its cost (`L` the frames' length, `N` their number). -/
def occCost (L N : ℕ) : ℕ := 2 * (L + N + 1) + 2

end
end NearCubicWires.SourceResident

