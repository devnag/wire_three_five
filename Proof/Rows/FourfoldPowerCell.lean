import Proof.Rows.CircuitPowerInput

/-! Four child digits and fixed circuit cursors share the actual reusable
coefficient cell. The only changing prefix tapes are factor28 and output64. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_FourfoldPowerCell
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutFinal SignedSortKey
noncomputable section

def extras (source :List Bool) (digits :Fin 4→Nat) (N v U :Nat):Fin 11→List Bool:=
 ![List.replicate v true,frame (binary v (digits 0)),frame (binary v (digits 1)),
 frame (binary v (digits 2)),frame (binary v (digits 3)),frame source,
 ZeroPadding.pad U (CompareMachine.word 0),ZeroPadding.pad U (CompareMachine.word 1),
 ZeroPadding.pad U (CompareMachine.word 2),ZeroPadding.pad U (CompareMachine.word 3),
 ZeroPadding.pad U (UnaryTemplate.tape N)]
def bank (source :List Bool) (digits :Fin 4→Nat) (N a B p w F U v :Nat) (out :List Bool):Fin 110→List Bool:=
 Fin.addCases (m:=99) (n:=11) (motive:=fun _=>List Bool)
  (fun i=>PCJ45bee56da9f34d5a_CircuitPowerInput.bank a B p w F U v 0 0 source [] out (i.castAdd 4))
  (extras source digits N v U)
def heads (len pos :Nat) (i :Fin 110):=if i=109 then pos else if (105 ≤ i.val ∧ i.val < 109) then 1 else if i=64 then len else 0


end
end PCJ45bee56da9f34d5a_FourfoldPowerCell
