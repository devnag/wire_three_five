import Proof.Circuits.DecompositionCachedChildPosition
import Proof.Assembly.AppendOutputLength

/-! Measure the actual native decomposition cache with its existing counted
parser. The source and measured unary mass return to head zero, while the
already decoded arity and child-count templates remain at their sentinels. -/
namespace NearCubicWires.RepairOrdinary.RowCacheMass
open LocalBitMultitape RepairRepresentation RecoveryExecution
open RepairSource.ProjectionNormalization DecompositionSource
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def record := AppendOutputLength.record DecompositionCachedChild.machine 0
def selected (i : Fin 6) : Bool := decide (i=0 ∨ i=5)
noncomputable def machine := MaskedReset.machine record selected
noncomputable def input {n : ℕ} (gs : List (ExactThresholdGate n)) :=
  Rewind.recording (Rewind.recording (DecompositionCachedChild.entry gs gs.length) 0) 0
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) :=
  2*DecompositionCachedChild.budget gs gs.length+2

end NearCubicWires.RepairOrdinary.RowCacheMass
