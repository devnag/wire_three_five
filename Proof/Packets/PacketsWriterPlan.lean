import Proof.Packets.PacketsLayout

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsConstruction
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent
noncomputable section

/-- The writer's bank shape: three private regions and the scrub width `R`. -/
structure WriterShape (a : DecompositionAlgorithm) where
  w1 : ℕ
  w2 : ℕ
  w3 : ℕ
  R : Request → ℕ
  cR : ℕ
  dR : ℕ
  hR : ∀ r, R r ≤ cR * (r.smallSize a)^dR

namespace WriterShape
variable {a : DecompositionAlgorithm} (X : WriterShape a)

abbrev w : ℕ := 9 + X.w1 + X.w2 + X.w3


/-- The layout's output port, as a closed term. -/
def outPort : Fin (10 + X.w) := ⟨1, Nat.lt_of_lt_of_le (by decide) (Nat.le_add_right 10 _)⟩

@[simp] theorem outPort_val : X.outPort.val = 1 := rfl

end WriterShape


/-! ## The stage contracts (frame form) -/

namespace WriterShape

end WriterShape

/-! ## Assembly -/

namespace WriterStages

end WriterStages

/-! ### Cost: every stage and the relabel loop are fixed powers of `smallSize` -/

namespace WriterStages

end WriterStages

end
end NearCubicWires.PacketsConstruction
