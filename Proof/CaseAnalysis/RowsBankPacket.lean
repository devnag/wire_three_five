import Proof.CaseAnalysis.RowsSourceLoad

/-! The fixed native packet is actually loaded into the erased bank.
The source cursor advances once and the growing cut output is never copied. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsBankPacket
open LocalBitMultitape CloseoutRowsBankPorts CloseoutRowsBankClear
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


end NearCubicWires.RepairOrdinary.CloseoutRowsBankPacket
