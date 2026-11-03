import Proof.Packets.PacketFamilyKeys
import Proof.MachineModel.BlockLoop
import Proof.MachineModel.BlockWordFunction
import Proof.MachineModel.OrdinaryZeroUnpadding

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketFamilyParent
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.BlockPlatform
open NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
noncomputable section

/-- The framed-input bank `Program.inputTapes` builds. -/
def inBank (n : ℕ) (w : List Bool) : Fin n → List Bool :=
  fun i => if i.val = 0 then frame w else []

/-! ## The cleanup form consumed here (to be discharged by `Block.scrub`) -/

/-! ## The per-row bank -/

namespace Layout

end Layout

/-! ## The remaining duties, one structure each -/

/-! ## Generic plumbing lemmas -/

/-! ## The parent -/

namespace RowWriterContract

/-! ### Budget: one family-row factor, one fixed power of `smallSize` -/

end RowWriterContract

end
end NearCubicWires.PacketFamilyParent
