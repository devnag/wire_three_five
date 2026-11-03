import Proof.CaseAnalysis.RowsModeIndexBlock
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Pairing
import Mathlib.Tactic
import Proof.MachineModel.Encoding

/-! The physical writer for one native singleton-pair cache record. It consumes
an actual framed binary code, writes all six framing/boundary cells, and appends
to an arbitrary retained prefix. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.LiteralPairRecord
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairOrdinary.RadixSemantics NearCubicWires.RepairOrdinary.SignedSortKey

noncomputable def machine := Composition.machine
  (Composition.machine (Composition.machine
    (Composition.machine (CloseoutRowsModeIndexBlock.mark true)
      CloseoutRowsModeIndexBlock.machine) (CloseoutRowsModeIndexBlock.mark false))
    (CloseoutRowsModeIndexBlock.mark false)) (CloseoutRowsModeIndexBlock.mark false)

end PCJ9eff70d512234a4c_Fixed.Materializer.LiteralPairRecord
