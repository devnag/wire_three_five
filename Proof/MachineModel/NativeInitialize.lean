import Proof.CaseAnalysis.RowsBankFields
import Proof.MachineModel.NativeFanoutLayout

/-! One whole ordinary run measures the actual cache, produces every static
word and C, then physically initializes the native bank. -/
namespace NearCubicWires.ExtIncidence.NativeInitialize
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch NativeFanoutLayout
open RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extraH (pos : ℕ) (out : List Bool) (i : Fin 128):=
  if i=31 then out.length else if i=113 then pos else 0
noncomputable def first:=TapeEmbedding.machine 128 NativeMaster.machine
noncomputable def machine:=Composition.machine first NativeFanoutLayout.machine
noncomputable def heads {n : ℕ} (gs : List (ExactThresholdGate n)) (pos : ℕ) (out : List Bool):=
  Fin.addCases (m:=149) (n:=128) (motive:=fun _=>ℕ) (NativeMaster.heads gs) (extraH pos out)
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) (Q w : ℕ):=
  NativeMaster.budget gs Q w+1+(2*NativeMeasured.capacity gs Q w+4)

end NearCubicWires.ExtIncidence.NativeInitialize
