import Proof.Packets.WindowProviderPorts
import Proof.Amplification.RecoveryScratchErase

/-! Physical allocation or erasure of all private native-normalizer, raw
renaming and normalized-substitution words. Both reset logs are the already
produced arithmetic logs; each ordinary sweep retains its raw reserve. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider.Workspace
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch

def workSlots (j : Fin 51) : Fin 256 :=
  if j.val<29 then ⟨j.val+96,by omega⟩ else
  if j.val<32 then ⟨j.val+97,by omega⟩ else
  if j.val<42 then ⟨j.val+98,by omega⟩ else ⟨j.val+99,by have h:=j.isLt;omega⟩
def slots : Fin 53→Fin 256 := Fin.addCases (m:=51) (n:=2) workSlots ![32,33]
noncomputable def machine := RecoveryFocus.machine slots (RecoveryScratchErase.resetMachine 51)

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider.Workspace
