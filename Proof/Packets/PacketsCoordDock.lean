import Mathlib.Data.List.Dedup
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Induction
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Pairing
import Mathlib.Tactic
import Std.Tactic
import Proof.MachineModel.BlockScrub
import Proof.Packets.MaskSelect
import Proof.Packets.NativeMaskCount
import Proof.Packets.PacketsWriterPlan
import Proof.Packets.PacketsXNormalizedDegreeCore
import Proof.Packets.PhysicalCopyInto
import Proof.Packets.PhysicalRepeatStep
import Proof.Packets.UnaryAffine
import Proof.Rows.SourceDockCore

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction.Residual
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.PacketsConstruction
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
noncomputable section

/-! ## The dock -/

section Dock

end Dock

end
end NearCubicWires.PacketsConstruction.Residual
