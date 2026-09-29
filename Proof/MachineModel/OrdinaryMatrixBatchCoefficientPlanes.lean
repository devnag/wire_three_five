import Proof.MachineModel.OrdinaryMatrixCoefficient

/-! A single original request now produces its signed coefficient bank and
both Boolean matrices. The coefficient pass runs once; the existing whole
matrix producer then runs on the retained original input and fresh work,
preserving the coefficient bank at head zero. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchCoefficientPlanes
open LocalBitMultitape MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 362) : Fin 396 := if i.val=0 then 0 else ⟨i.val+34,by omega⟩
theorem slots_zero : slots 0=0 := rfl
theorem slots_succ (j : Fin 361) : slots j.succ=j.natAdd 35 := by
  apply Fin.ext
  simp [slots]
  omega
theorem slots_injective : Function.Injective slots := by
  intro a b h
  have hv := congrArg Fin.val h
  apply Fin.ext
  simp only [slots] at hv
  split_ifs at hv <;> simp only [Fin.val_zero] at hv <;> omega
noncomputable def first := TapeEmbedding.machine 361 MatrixCoefficientCold.machine
noncomputable def last := RecoveryFocus.machine slots MatrixBatchRightPlane.machine
noncomputable def machine := Composition.machine first last
def input (r : Request) : Fin 396 → List Bool := fun i => if i=0 then physicalInput r else []
noncomputable def budget (r : Request) := MatrixCoefficientCold.budget r+1+MatrixBatchRightPlane.budget r

end NearCubicWires.RepairOrdinary.MatrixBatchCoefficientPlanes
