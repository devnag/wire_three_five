import Proof.MachineModel.NativeShort

/-! All fifteen distinct source words for native initialization are outputs
of one fixed ordinary run over the same measured cache. -/
namespace NearCubicWires.ExtIncidence.NativeMaster
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RepairRepresentation
open RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 17→Fin 149:=![3,88,36,135,136,137,138,139,140,141,142,143,144,145,146,147,148]
def fields : Fin 15→Fin 149:=![0,15,27,3,31,57,86,135,4,146,139,143,88,53,141]
def words {n : ℕ} (gs : List (ExactThresholdGate n)) (Q w : ℕ) : Fin 15→List Bool:=
  ![exactListWord gs,List.replicate (RowCachedCoordinateBounds.width gs) true,
    List.replicate (RowCachedCoordinateBounds.inner (RowCachedCoordinateBounds.width gs)) true,
    UnaryTemplate.tape n,
    List.replicate (RowCachedCoordinateBounds.outer gs (RowCachedCoordinateBounds.width gs)) true,
    CompareMachine.word (NativeWidth.width gs Q+1),List.replicate (NativeAllocation.capacity gs Q) true,
    CompareMachine.word (n+1),UnaryTemplate.tape gs.length,frame (SignedSortKey.binary w 0),
    CompareMachine.word w,CompareMachine.word 1,List.replicate w true,
    List.replicate (NativeWidth.width gs Q) true,CompareMachine.word Q]
noncomputable def first:=TapeEmbedding.machine 14 NativeMeasured.machine
noncomputable def last:=RecoveryFocus.machine slots NativeShort.machine
noncomputable def machine:=Composition.machine first last
noncomputable def heads {n : ℕ} (gs : List (ExactThresholdGate n)) : Fin 149→ℕ:=
  Fin.addCases (m:=135) (n:=14) (motive:=fun _=>ℕ) (NativeMeasured.heads gs) (fun _=>0)
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) (Q w : ℕ):=
  NativeMeasured.budget gs Q w+1+NativeShort.budget n w Q

end NearCubicWires.ExtIncidence.NativeMaster

