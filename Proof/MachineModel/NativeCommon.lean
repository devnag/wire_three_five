import Proof.MachineModel.NativeMeasure
import Proof.Supplier.RowCommonResources

/-! The measured original cache supplies both actual common capacity words.
These are produced once for the fixed shared native cache. -/
namespace NearCubicWires.ExtIncidence.NativeCommon
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RepairRepresentation
open RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 17→Fin 36:=![15,19,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
noncomputable def first:=TapeEmbedding.machine 15 NativeMeasure.machine
noncomputable def last:=RecoveryFocus.machine slots RowCommonResources.machine
noncomputable def machine:=Composition.machine first last
noncomputable def heads {n : ℕ} (gs : List (ExactThresholdGate n)) : Fin 36→ℕ:=
  Fin.addCases (m:=21) (n:=15) (motive:=fun _=>ℕ) (NativeMeasure.heads gs) (fun _=>0)
def scale {n : ℕ} (gs : List (ExactThresholdGate n)):=RowCommonSize.scale (exactListWord gs).length n gs.length
def budget {n : ℕ} (gs : List (ExactThresholdGate n)):=
  NativeMeasure.budget gs+1+RowCommonResources.budget (RowCachedCoordinateBounds.width gs) (scale gs)

end NearCubicWires.ExtIncidence.NativeCommon
