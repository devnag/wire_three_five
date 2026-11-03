import Proof.CaseAnalysis.RowsBankPacket

/-! One actual packet load, head positioning, complete polynomial call and
native clear compose into the reusable enclosing bank body. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsPacketPolynomial
open LocalBitMultitape CloseoutRowsPreparationBounds CloseoutRowsBankPacket
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def data {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F Q w C : ℕ) (rows : List (List Bool)) (out : List Bool) :=
  (CloseoutRowsPolynomial.input gs p F Q w C rows out).tapes
noncomputable def native := Composition.machine (CloseoutRowsBankClear.position true) CloseoutRowsBankPolynomial.machine

noncomputable def last := TapeEmbedding.machine 1 native
noncomputable def machine := Composition.machine CloseoutRowsBankPacket.machine last

end NearCubicWires.RepairOrdinary.CloseoutRowsPacketPolynomial
