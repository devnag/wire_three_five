import Proof.MachineModel.NativeCommon
import Proof.Supplier.RowCommonTupleDimensions
import Proof.Supplier.RowTupleFixedCapacity

/-! The actual shared cache and degree driver produce the native occurrence
bound and base coefficient width. The final width still adds Q for constants. -/
namespace NearCubicWires.ExtIncidence.NativeDimensions
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RepairRepresentation
open RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 17→Fin 51:=![15,4,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50]
noncomputable def first:=TapeEmbedding.machine 15 NativeCommon.machine
noncomputable def last:=RecoveryFocus.machine slots RowCommonTupleDimensions.machine
noncomputable def machine:=Composition.machine first last
noncomputable def heads {n : ℕ} (gs : List (ExactThresholdGate n)) : Fin 51→ℕ:=
  Fin.addCases (m:=36) (n:=15) (motive:=fun _=>ℕ) (NativeCommon.heads gs) (fun _=>0)
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) (Q : ℕ):=
  NativeCommon.budget gs+1+RowCommonTupleDimensions.budget (RowCachedCoordinateBounds.width gs) gs.length Q

end NearCubicWires.ExtIncidence.NativeDimensions
