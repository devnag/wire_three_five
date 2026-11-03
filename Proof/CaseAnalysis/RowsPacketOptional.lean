import Proof.CaseAnalysis.RowsPacketBranch

/-! One enclosing polynomial packet, including the physical zero-monomial
skip, has a uniform receipt for the outer live-family loop. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsPacketOptional
open LocalBitMultitape CloseoutRowsBankPacket CloseoutRowsPreparationBounds
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def packet {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F Q w C : ℕ) (rows : List (List Bool)) : List Bool :=
  if rows=[] then [false] else
    true::word (CloseoutRowsPacketPolynomial.data gs p F Q w C rows [])
noncomputable def machine :=
  CloseoutRowsPacketBranch.machine (113 : Fin 114) CloseoutRowsPacketPolynomial.machine
def cost (Q C : ℕ) := CloseoutRowsBankPolynomial.budget Q C+110*(3*C+3)+6

end NearCubicWires.RepairOrdinary.CloseoutRowsPacketOptional
