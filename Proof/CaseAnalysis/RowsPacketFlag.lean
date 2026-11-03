import Proof.CaseAnalysis.RowsPacketPolynomial

/-! The packet flag is consumed by one actual transition. It distinguishes
zero monomials from one empty monomial even when the gate pool is empty. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsPacketFlag
open LocalBitMultitape RecoveryExecution CloseoutRowsBankPacket
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine {t : ℕ} (source : Fin t) : Machine t 3 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q != 0
  rule := fun q bits=>if q=0 then
    some ⟨if bits source then 1 else 2,fun _=>none,
      fun i=>if i=source then .right else .stay⟩ else none

end NearCubicWires.RepairOrdinary.CloseoutRowsPacketFlag
