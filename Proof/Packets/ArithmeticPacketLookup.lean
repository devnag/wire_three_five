import Proof.Packets.ReusableNormalizedArithmetic
import Proof.Packets.PacketBankLookup

/-! Actual atom/vector lookup into the reusable left operand. The resident
source, physical index, other operand, and all reserve drivers are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ArithmeticLookup
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.VerifierDecoding

def countMove (move : HeadMove) : Machine 37 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q _=>if q.val=0 then some
    ⟨1,fun _=>none,fun i=>if i=28 then move else .stay⟩ else none


def slots : Fin 6→Fin 37 := ![31,34,25,28,35,36]
noncomputable def focused := RecoveryFocus.machine slots PacketBank.lookup
noncomputable def machine := Composition.machine (countMove .right)
  (Composition.machine focused (countMove .left))



end PCJ9eff70d512234a4c_Fixed.Materializer.ArithmeticLookup
