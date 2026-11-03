import Proof.Supplier.RowCommonClear

/-! The exact common-width bank is restored after each executed coefficient.
Only the live output contains the appended common-width signed field. -/
namespace NearCubicWires.RepairOrdinary.RowCommonReusable
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def data {n : ℕ} (gs : List (ExactThresholdGate n)) (j p F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) : Fin 35→List Bool :=
  let w := RowCachedCoordinateBounds.width gs
  let C := RowCachedCoordinateBounds.inner w
  let D := RowCachedCoordinateBounds.outer gs w
  let zC := List.replicate C false
  let zD := List.replicate D false
  let zF := List.replicate F false
  ![exactListWord gs,zC,zC,zC,zC,zC,zC,zC,zC,List.replicate w true,zF,zF,zC,
    List.replicate C true,List.replicate (C+1) false,UnaryTemplate.tape j,zF,zD,UnaryTemplate.tape n,
    zF,zD,List.replicate D true,List.replicate (D+1) false,RowOccurrenceLoop.word indices++tail,
    CompareMachine.word indices.length,zF,zF,zF,zF,CompareMachine.word (p+1),zF,out,zF,
    List.replicate F true,List.replicate (F+1) false]

end NearCubicWires.RepairOrdinary.RowCommonReusable
