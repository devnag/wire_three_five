import Proof.Rows.VerdictFinish
import Proof.MachineModel.NativeFanoutReusable
import Proof.Circuits.DecompositionCountPosition

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.CellReload
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

/-! ## 1. Layout -/

abbrev CT : Nat := 257+254

def cellPort (i : Fin 257) : Fin CT := i.castAdd 254
def masterPort (k : Fin 254) : Fin CT := k.natAdd 257

def layout {α : Type} (X : Fin 257 → α) (Y : Fin 254 → α) : Fin CT → α :=
  Fin.addCases (m:=257) (n:=254) X Y

@[simp] theorem layout_cell {α : Type} (X : Fin 257 → α) (Y : Fin 254 → α) (i : Fin 257) :
    layout X Y (cellPort i) = X i := by
  simp [layout, cellPort]
@[simp] theorem layout_master {α : Type} (X : Fin 257 → α) (Y : Fin 254 → α) (k : Fin 254) :
    layout X Y (masterPort k) = Y k := by
  simp [layout, masterPort]

/-! ## 2. The fanout slots: masters, the 254 cell inputs, the clock (254), the log (255) -/


/-! ## 3. The three stages -/

/-! ## 4. Stage lemmas -/

end
end RowsConstruction.CellReload
