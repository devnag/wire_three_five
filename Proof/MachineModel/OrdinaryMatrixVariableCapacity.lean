import Proof.MachineModel.OrdinaryMatrixVariableWorkspace
import Proof.MachineModel.OrdinaryMatrixWilliamsProductBounds

/-! The finite clear capacity follows from the original request and the
same executed source-call envelope. Its coefficient/exponent depend only
on the fixed Williams source, before the weak machine is selected.

The request word's header carries the weight count and the columns of `φ` (paper3 `alg:pullback`,
P3:1623-1671; `MatrixScoreBatch.header`), which the coefficient pass's header budget pays for. -/
namespace NearCubicWires.RepairOrdinary.MatrixVariableCapacity
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem input_bound (r : Request) : (physicalInput r).length≤MatrixWilliamsInput.budget r := by
  have hc : (physicalInput r).length≤MatrixCoefficientCold.budget r := by
    have hw : natWord r.d++(natWord r.p++(natWord r.Gates++natWord r.width++MatrixScorePhi.columnsWord r.width r.cols++
        r.cuts.flatMap (cutWord r.p)))=word r := by
      simp only [word,header,List.append_assoc]
    unfold MatrixCoefficientCold.budget MatrixCoefficientCold.forwardBudget MatrixCoefficientHeaders.budget
      MatrixScoreHeaders.budget WilliamsInputHeader.budget
    rw [hw]
    simp only [physicalInput,frame_length]
    omega
  rw [MatrixWilliamsProductBounds.preparation_eq]
  unfold MatrixBatchCoefficientPlanes.budget
  omega


end NearCubicWires.RepairOrdinary.MatrixVariableCapacity
