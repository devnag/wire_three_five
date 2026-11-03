import Proof.Packets.PacketFamilyParent
import Proof.MachineModel.OrdinarySignedSortKey
import Proof.Amplification.RecoveryCanonicalValues

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.SupplierWalkBridge NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
noncomputable section

/-! ## Key digits -/

/-- The eight digit fields of a key; `none` (after the last row) is the done flag. -/
def keyDigits (a : DecompositionAlgorithm) : ∀ r : Request, Option (rcKey a r) → Fin 8 → ℕ
  | _, none => fun i => if i.val = 7 then 1 else 0
  | .terminal, some k => PEmpty.elim k
  | .sym r _ _ _, some k => fun i =>
      if h : i.val < r.circuits.length then k.offset ⟨i.val, h⟩
      else if i.val = 5 then (canonicalWalkSampleFinEquiv _ _ k.seed).val else 0
  | .thr r _ _ _, some k => fun i =>
      if h : i.val < r.circuits.length then (k.selection ⟨i.val, h⟩).val
      else if i.val = 4 then (primeIndexFinEquiv _ k.prime).val
      else if i.val = 5 then (canonicalWalkSampleFinEquiv _ _ k.seed).val
      else if i.val = 6 then k.residue.val else 0

/-! ## The layout -/

end
end NearCubicWires.PacketsConstruction
