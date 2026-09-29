import Proof.MachineModel.OrdinaryMatrixWilliamsDimensions
import Proof.MachineModel.OrdinaryMatrixWilliamsFrame

/-! The original raw cut request now physically supplies the exact framed
input of the corrected Williams wrapper for its first signed Boolean plane. -/
namespace NearCubicWires.RepairOrdinary.MatrixWilliamsInput
open LocalBitMultitape MatrixScoreBatch RepairRepresentation WilliamsLoaderForms
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def budget (r : Request) := MatrixWilliamsDimensions.budget r+1+(6*(2*r.d+3)+12*(r.U*r.Capacity)+38)

theorem header_length (r : Request) : (natWord r.U).length=2*r.d+3 := by
  change (natWord (2^r.d)).length=_
  rw [←MatrixPowerHeader.word_eq]
  exact MatrixPowerHeader.word_length r.d

theorem left_length (r : Request) (negative : Bool) (bit : ℕ) :
    (MatrixSignedPlane.plane r negative bit).length=r.U*r.Capacity := by
  simp [MatrixSignedPlane.plane,rowMajorBitMatrix,List.length_flatten,List.map_ofFn,Function.comp_def]

theorem right_length (r : Request) : (MatrixRightPlaneNative.plane r).length=r.U*r.Capacity := by
  simp [MatrixRightPlaneNative.plane,rowMajorBitMatrix,List.length_flatten,List.map_ofFn,Function.comp_def,Nat.mul_comm]

end NearCubicWires.RepairOrdinary.MatrixWilliamsInput
