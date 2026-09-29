import Proof.SourceAssembly.SourceLog

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ6e421fabe2aa4155_SourceLiveCount
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
open PCJ6e421fabe2aa4155_SourceLog SupplierPipeline SupplierEstimator
noncomputable section

theorem product_step (L e : Nat) : Step ClockUnaryProduct.machine (2*(L*(2*e+3)+2)+2)
    (fun _=>0) ![List.replicate L true,CompareMachine.word e,[],[]] (fun _=>0)
    ![List.replicate L true,CompareMachine.word e,List.replicate (L*e) true,List.replicate (L*(2*e+3)+2) false] := by
  obtain ⟨r,hr,h0,h1,h2,h3,hh,hs⟩:=ClockUnaryProduct.product_run L e
  have hi : (Fin.addCases (motive:=fun _ : Fin 4=>List Bool)
      ![List.replicate L true,false::List.replicate e true,[]] (fun _ : Fin 1=>[]))=
      ![List.replicate L true,CompareMachine.word e,[],[]] := by
    funext i;fin_cases i <;>rfl
  rw [hi] at hr
  refine ⟨r,hr,funext hh,?_,hs.le⟩
  funext i;fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3



end
end PCJ6e421fabe2aa4155_SourceLiveCount
