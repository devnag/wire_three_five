import Proof.CaseAnalysis.RowsSourceLoad

/-! The fixed native packet is actually loaded into the erased bank.
The source cursor advances once and the growing cut output is never copied. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsBankPacket
open LocalBitMultitape CloseoutRowsBankPorts CloseoutRowsBankClear
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extend {α : Type} (old : Fin 113→α) (fresh : α) : Fin 114→α :=
  Fin.addCases (m:=113) (n:=1) (motive:=fun _=>α) old (fun _ : Fin 1=>fresh)
def fields (data : Fin 113→List Bool) := extend data []
def word (data : Fin 113→List Bool) := CloseoutRowsPacketLoad.stream (fields data) ports
def heads (out : List Bool) (pos : ℕ) := extend (zeroHeads out) pos
def tapes (C : ℕ) (out packet : List Bool) := extend (blank C out) packet
noncomputable def machine := CloseoutRowsPacketLoad.machine (113 : Fin 114) 105 ports
def budget (data : Fin 113→List Bool) := CloseoutRowsPacketLoad.cost (fields data) ports

end NearCubicWires.RepairOrdinary.CloseoutRowsBankPacket
