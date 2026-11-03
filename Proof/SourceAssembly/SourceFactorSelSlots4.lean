import Proof.SourceAssembly.SourceFactorSelSlotDock

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceFactorSel.Slots4
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open NearCubicWires.SourceFactorSel.Slot NearCubicWires.SourceFactorSel.SlotDock NearCubicWires.SourceRequest.TermReader
noncomputable section

/-- **The four slot pipelines** (ONE fixed machine given the four docks). -/
def fourM {U : Nat} (sl : Fin 4 → Fin 1121 → Fin U) :=
  Composition.machine (RecoveryFocus.machine (sl 0) slotM)
  (Composition.machine (RecoveryFocus.machine (sl 1) slotM)
  (Composition.machine (RecoveryFocus.machine (sl 2) slotM) (RecoveryFocus.machine (sl 3) slotM)))

section
open RepairRepresentation SupplierPipeline SourceInterfaces SupplierEstimator NearCubicWires.RepairSource
open NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.SourceRequest
open NearCubicWires.SourceFactorSel.Modes (kindOf bmOf bitsOf)

end
end
end NearCubicWires.SourceFactorSel.Slots4

