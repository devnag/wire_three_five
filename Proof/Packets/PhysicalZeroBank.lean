import Proof.Packets.MaskConstant
import Proof.Packets.PhysicalRepeatStep
import Proof.Rows.MaskProductBack
import Proof.Rows.MaskSeek
import Proof.Rows.PhysicalFocusBoundary

/-! Dense packet-table allocation by actual writes. Given only physical R
and N drivers, write N all-false two-R-bit entries into an empty bank and
return its cursor. No prefilled table is part of the input. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalZeroBank
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def zeroSlots : Fin 2→Fin 3 := ![0,1]
def zero := RecoveryFocus.machine zeroSlots MaskConstant.maskMachine
def chunk := Composition.machine zero MaskSeek.body
def packet := Composition.machine chunk chunk
def loop := RepeatMachine.machine packet (fun _ _=>true)
def machine := Composition.machine loop (Composition.machine MaskBack.machine MaskBack.machine)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalZeroBank
