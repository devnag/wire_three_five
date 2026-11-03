import Proof.Rows.ResidueScaleCell
import Proof.Rows.FinalNativeResidueCallback

/-! The native signed field is physically reduced into the product emitter's
right-operand master. The source cursor advances and the native reader returns
its exact next canonical bank. The emitted row prefix stays outside both banks. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_NativeScaleInput
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairRepresentation
open SignedSortKey
noncomputable section

def main (a p w U : Nat) (out coefficient : List Bool) (i : Fin 65):=
  if i=0 then coefficient else PCJ45bee56da9f34d5a_ResidueScaleCell.cold
    (PCJ45bee56da9f34d5a_ResidueScaleCell.palette a 0 p w) U out i
def extraIndex (i : Fin 26) : Fin 27:=if h:i.val<22 then ⟨i.val,by omega⟩ else ⟨i.val+1,by omega⟩
def extras (F w p : Nat) (source : List Bool) (i : Fin 26):=
  C10NativeResidueCallback.bank F w p source [] (extraIndex i)
def bank (a p w F U : Nat) (source out coefficient : List Bool) : Fin 91→List Bool:=
  Fin.addCases (m:=65) (n:=26) (motive:=fun _=>List Bool) (main a p w U out coefficient) (extras F w p source)

end
end PCJ45bee56da9f34d5a_NativeScaleInput
