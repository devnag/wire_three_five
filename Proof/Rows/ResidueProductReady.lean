import Proof.Rows.ResidueProduct
import Proof.MachineModel.ClockScalarFields

/-! Paid width conversion closes the product consumer's wider-left-operand seam.
Both factors enter as their actual original framed binary words. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_ResidueProductReady
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding
open SignedSortKey RadixSemantics
noncomputable section

def input (W a p w cap D : Nat) (bits : List Bool) : Fin 31→List Bool:=
  Fin.addCases (m:=28) (n:=3) (motive:=fun _=>List Bool)
    (Function.update (PCJ45bee56da9f34d5a_ResidueProduct.input W a p w cap D bits) 8 [])
    (![frame (binary w a),[],[]] : Fin 3→List Bool)

end
end PCJ45bee56da9f34d5a_ResidueProductReady
