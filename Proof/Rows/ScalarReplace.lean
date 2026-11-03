import Proof.Rows.NativeScaleEquation
import Proof.MachineModel.OrdinaryMatrixFrameCopy

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 550000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_ScalarReplace
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

theorem run (bits backing : List Bool) (U : Nat) (hb : backing.length ≤ 2*bits.length+1)
    (hU : 4*bits.length+3 ≤ U) :
    Step MatrixFrameCopy.machine (8*bits.length+8) (fun _=>0)
      ![ZeroPadding.pad U (frame bits),ZeroPadding.pad U backing,List.replicate U false,List.replicate U false]
      (fun _=>0)
      ![ZeroPadding.pad U (frame bits),ZeroPadding.pad U (frame bits),List.replicate U false,List.replicate U false] := by
  obtain ⟨r,hr,ht,hh,_⟩ := MatrixFrameCopy.copy_run bits backing hb
  have h := (Step.of_run hr (funext hh) ht).pad (fun _=>U)
  refine (h.congr_in rfl ?_).congr rfl ?_
  all_goals
    funext i;fin_cases i <;>simp only [MatrixFrameCopy.input]
    all_goals first |rfl |(rw [ZeroPadding.pad];simp;omega)
end
end PCJ45bee56da9f34d5a_ScalarReplace
