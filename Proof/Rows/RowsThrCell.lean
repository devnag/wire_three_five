import Proof.Rows.RowsCellReload
import Proof.Rows.RowsCellInput
import Proof.Hierarchy.CompetitorRawScalarAppend
import Proof.Rows.Plan
import Proof.Rows.CountFlags

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.ThrCell
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.RecoveryExecution RadixSemantics SignedSortKey
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.RepairSource.CloseoutFinal
noncomputable section

/-! ## 0. Two arithmetic facts -/

/-! ## 1. Layout -/

abbrev MT : Nat := (257+254)+7

def layout {α : Type} (X : Fin 257 → α) (Y : Fin 254 → α) (Z : Fin 7 → α) : Fin MT → α :=
  Fin.addCases (m:=257+254) (n:=7) (CellReload.layout X Y) Z

def cellP (i : Fin 257) : Fin MT := (CellReload.cellPort i).castAdd 7
def masterP (k : Fin 254) : Fin MT := (CellReload.masterPort k).castAdd 7

@[simp] theorem layout_cell {α : Type} (X : Fin 257 → α) (Y : Fin 254 → α) (Z : Fin 7 → α)
    (i : Fin 257) : layout X Y Z (cellP i) = X i := by
  simp [layout, cellP]
@[simp] theorem layout_master {α : Type} (X : Fin 257 → α) (Y : Fin 254 → α) (Z : Fin 7 → α)
    (k : Fin 254) : layout X Y Z (masterP k) = Y k := by
  simp [layout, masterP]


/-! ## 2. The four stages -/




/-! ## 3. The cell state -/

def aux {q : Nat} (live : Finset (Fin q)) (s C D rowN colN : Nat) (bits : List Bool) :
    Fin 7 → List Bool :=
  ![frame (binary ((s+1)/2) rowN), frame (binary (s/2) colN), bits, List.replicate C false,
    List.replicate D false, CloseoutRowsGateSupport.gateMembers liveᶜ, CompareMachine.word q]

def tapes {q : Nat} (live : Finset (Fin q)) (s R C D rowN colN : Nat) (M : Fin 254 → List Bool)
    (out : List Bool) : Fin MT → List Bool :=
  layout (PCJ45bee56da9f34d5a_VerdictFinish.bank (fun _ => List.replicate R false) R out) M
    (aux live s C D rowN colN (List.replicate R false))

/-! ## 4. Stage lemmas -/

/-! ## 5. One cell -/

end
end RowsConstruction.ThrCell
