import Proof.MachineModel.NativeWidth
import Proof.Supplier.RowCommonAllocation

/-! The same measured native cache supplies p and the exact coefficient
allocation F. No width or capacity word is an input to this whole run. -/
namespace NearCubicWires.ExtIncidence.NativeAllocation
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RepairRepresentation
open RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 25→Fin 88:=![39,53,31,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87]
noncomputable def first:=TapeEmbedding.machine 22 NativeWidth.machine
noncomputable def last:=RecoveryFocus.machine slots RowCommonAllocation.machine
noncomputable def machine:=Composition.machine first last
def capacity {n : ℕ} (gs : List (ExactThresholdGate n)) (Q : ℕ):=
  RowCommonBounds.capacity gs (gs.length*Q) (NativeWidth.width gs Q)
noncomputable def heads {n : ℕ} (gs : List (ExactThresholdGate n)) : Fin 88→ℕ:=
  Fin.addCases (m:=66) (n:=22) (motive:=fun _=>ℕ) (NativeWidth.heads gs) (fun _=>0)
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) (Q : ℕ):=
  NativeWidth.budget gs Q+1+RowCommonAllocation.budget (gs.length*Q) (NativeWidth.width gs Q)
    (RowCachedCoordinateBounds.outer gs (RowCachedCoordinateBounds.width gs))

end NearCubicWires.ExtIncidence.NativeAllocation
