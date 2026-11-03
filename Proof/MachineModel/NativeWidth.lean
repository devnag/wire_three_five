import Proof.MachineModel.NativeDimensions
import Proof.MachineModel.NativeFieldWidth

/-! The complete measured-cache run produces the final p=base+Q word and
signed-field driver, retaining every shared cache/dimension field. -/
namespace NearCubicWires.ExtIncidence.NativeWidth
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RepairRepresentation
open RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 17→Fin 66:=![43,36,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65]
noncomputable def first:=TapeEmbedding.machine 15 NativeDimensions.machine
noncomputable def last:=RecoveryFocus.machine slots NativeFieldWidth.machine
noncomputable def machine:=Composition.machine first last
def width {n : ℕ} (gs : List (ExactThresholdGate n)) (Q : ℕ):=RowTupleFixedCapacity.width gs Q+Q
noncomputable def heads {n : ℕ} (gs : List (ExactThresholdGate n)) : Fin 66→ℕ:=
  Fin.addCases (m:=51) (n:=15) (motive:=fun _=>ℕ) (NativeDimensions.heads gs) (fun _=>0)
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) (Q : ℕ):=
  NativeDimensions.budget gs Q+1+NativeFieldWidth.budget (RowTupleFixedCapacity.width gs Q) Q

end NearCubicWires.ExtIncidence.NativeWidth
