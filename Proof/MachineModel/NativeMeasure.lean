import Proof.MachineModel.Layout
import Proof.Supplier.RowCacheMass
import Proof.Supplier.RowCommonSize
import Proof.Circuits.DecompositionCountPosition
import Proof.PCP.PCPSerializerCapacityFocus

/-! Measure the SAME native child cache and compute its common width and
scale. No decomposition source is called and no byte count is supplied. -/
namespace NearCubicWires.ExtIncidence.NativeMeasure
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RepairRepresentation
open RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 17→Fin 21:=![5,3,4,7,8,9,10,11,12,13,14,15,16,17,18,19,20]
def directions (i : Fin 21) : HeadMove:=if i=3 ∨ i=4 then .left else .stay
noncomputable def measure:=TapeEmbedding.machine 14 RowCacheMass.machine
def position:=DecompositionCountPosition.move directions
noncomputable def first:=Composition.machine measure position
noncomputable def size:=RecoveryFocus.machine slots RowCommonSize.machine
noncomputable def machine:=Composition.machine first size
noncomputable def heads {n : ℕ} (gs : List (ExactThresholdGate n)) : Fin 21→ℕ:=
  Fin.addCases (m:=7) (n:=14) (motive:=fun _=>ℕ) (RowCacheMass.input gs).heads (fun _=>0)
def budget {n : ℕ} (gs : List (ExactThresholdGate n)):=
  RowCacheMass.budget gs+3+RowCommonSize.budget (exactListWord gs).length n gs.length

end NearCubicWires.ExtIncidence.NativeMeasure
