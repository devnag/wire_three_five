import Proof.Supplier.RowTupleCursorEquation
import Proof.Supplier.RowTupleFixedCapacity

/-! The exact reusable tuple-store layout: only the coordinate counter,
occurrence stream and count need erasure between adjacent tuples. The
cached last lookup bound remains available and is overwritten by the next
digit read. -/
namespace NearCubicWires.RepairOrdinary.RowTupleCursorLayout
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding RowTupleCommonEquation RowMaskPositionParts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def data {n : ℕ} (gs : List (ExactThresholdGate n)) (j p F w M k : ℕ)
    (rows : List (List Bool)) (tuple out : List Bool) (bound : ℕ) (is : List (Fin gs.length)) : Fin 48→List Bool :=
  Fin.addCases (m:=36) (n:=12) (motive:=fun _=>List Bool)
    (Fin.addCases (m:=35) (n:=1) (motive:=fun _=>List Bool)
      (RowCommonReusable.data gs j p F [] out is) (fun _=>CompareMachine.word (n+1)))
    ![rows.flatten,List.replicate (gs.length+2) false,UnaryTemplate.tape gs.length,
      frame (SignedSortKey.binary w 0),frame (SignedSortKey.binary w bound),[false],
      List.replicate (2*w+1) false,List.replicate (RowMaskLookupReusable.capacity gs.length w M) false,
      tuple,CompareMachine.word w,CompareMachine.word k,
      List.replicate (RowTupleCursorReady.capacity gs.length w M k) false]
def heads (pos : ℕ) (out : List Bool) : Fin 48→ℕ := fun i=>
  if i=31 then out.length else if i=44 then pos else
    if i=15 ∨ i=18 ∨ i=24 ∨ i=35 ∨ i=37 ∨ i=38 ∨ i=45 ∨ i=46 then 1 else 0

end NearCubicWires.RepairOrdinary.RowTupleCursorLayout
