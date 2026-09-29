import Proof.MachineModel.OrdinaryMemoryPrepared

/-! The entire actual chronological-memory checker: sort, paid reset,
generate the initial key, paid reset, and sequential validation. All scratch
starts blank, and all retained sorter/reset tapes remain present. -/
namespace NearCubicWires.RepairOrdinary.MemoryChecker
open LocalBitMultitape MemoryLog MemorySort StablePartition RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Request where
  count : ℕ
  indexBits : ℕ
  addressBits : ℕ
  events : Fin count → Event
  positive : 0 < count
  indicesFit : count ≤ 2^indexBits
  cellsFit : ∀ i, cellCode addressBits (events i).cell < 2^(indexBits+2)
  addressesFit : ∀ i, (events i).cell.2 < 2^addressBits
def Request.sortRequest (r : Request) : SortCarrier.Request :=
  request r.indexBits (r.indexBits+2) r.addressBits r.events
def Request.input (r : Request) : List Bool := stream r.sortRequest.records
def Request.result (r : Request) : Bool :=
  (MemoryLog.run (fun _ => false) ((List.finRange r.count).map r.events)).isSome
def layout : Fin 21 ≃ Fin 21 where
  toFun := ![7,8,9,10,11,12,13,0,14,15,16,17,18,19,20,1,2,3,4,5,6]
  invFun := ![7,15,16,17,18,19,20,0,1,2,3,4,5,6,8,9,10,11,12,13,14]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
@[simp] theorem layout_inverse : (layout.symm : Fin 21 → Fin 21) =
    ![7,15,16,17,18,19,20,0,1,2,3,4,5,6,8,9,10,11,12,13,14] := rfl
def sortMachine : Machine 21 88 := TapeEmbedding.machine 14 (Rewind.machine SortCarrier.machine)
def checkMachine : Machine 21 50 :=
  TapeRenaming.machine layout (TapeEmbedding.machine 6 MemoryPrepared.machine)
def machine : Machine 21 138 := Composition.machine sortMachine checkMachine
def checkBudget (req : Request) : ℕ :=
  8*(req.indexBits+2)+4+1+(req.count*(240*(req.indexBits+2)+182)+1)
def rawBudget (req : Request) : ℕ :=
  2*SortCarrier.budget req.sortRequest.records+3+checkBudget req

end NearCubicWires.RepairOrdinary.MemoryChecker
