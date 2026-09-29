import Proof.MachineModel.ClosureRawRelabelRun

/-! A.12's complete raw-index family, constructed from the retained lowered
stream by a fixed physical loop. Each iteration calls the checked relabeler
and increments its actual unary assignment index. No row callback is assumed.
The repeat driver and input-derived capacities are explicit retained inputs. -/
namespace NearCubicWires.P1Closure.RawRelabelFamily
open LocalBitMultitape RepairOrdinary RecoveryExecution ExtDecompositionBatch RecoveryRootRound
open ExtIncidence RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def incSlots : Fin 1→Fin 8:=fun _=>2
noncomputable def inc:=RecoveryFocus.machine incSlots RecoveryEraseWidth.incrementMachine

def move (up : Bool) : Machine 8 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=1)
  rule:=fun q _=>if q=0 then some ⟨1,fun _=>none,
    fun i=>if i=2 then (if up then .right else .left) else .stay⟩ else none

noncomputable def increment:=Composition.machine (Composition.machine (move true) inc) (move false)
noncomputable def body:=Composition.machine RawRelabelRun.machine increment
noncomputable def machine:=CloseoutRowsDegreeLoop.machine body




open CanonicalFourfoldRowProgram RepairRepresentation SupplierPipeline
open RepairSource.CloseoutFinal

end
end NearCubicWires.P1Closure.RawRelabelFamily
