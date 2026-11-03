import Proof.MachineModel.NativeCapacity

/-! One measured cache supplies the actual p, F, and full preparation C.
Only the mode's short w and Q are additional inputs to this whole run. -/
namespace NearCubicWires.ExtIncidence.NativeMeasured
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RepairRepresentation
open RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 52→Fin 135:=![3,53,86,88,4,36,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134]
noncomputable def first:=TapeEmbedding.machine 47 NativeAllocation.machine
noncomputable def last:=RecoveryFocus.machine slots NativeCapacity.machine
noncomputable def machine:=Composition.machine first last
noncomputable def heads {n : ℕ} (gs : List (ExactThresholdGate n)) : Fin 135→ℕ:=
  Fin.addCases (m:=88) (n:=47) (motive:=fun _=>ℕ) (NativeAllocation.heads gs) (fun _=>0)
def capacity {n : ℕ} (gs : List (ExactThresholdGate n)) (Q w : ℕ):=
  CloseoutRowsPreparationBounds.capacity n (NativeWidth.width gs Q) (NativeAllocation.capacity gs Q) w gs.length Q
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) (Q w : ℕ):=NativeAllocation.budget gs Q+1+
  NativeCapacity.budget n (NativeWidth.width gs Q) (NativeAllocation.capacity gs Q) w gs.length Q

end NearCubicWires.ExtIncidence.NativeMeasured
