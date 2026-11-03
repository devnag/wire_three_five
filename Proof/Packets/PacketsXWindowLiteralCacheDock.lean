import Proof.Packets.PacketsXLiteralCacheTransaction
import Proof.Packets.WindowProviderPorts

/-! Physical reflected-code cache production from the retained actual tag,
population, and reserve masters in the fixed provider arena. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open Theorem25Completion.CycleLiteralPairCost

def literalPorts (i : Fin 68) : Fin 256 :=
  if i=2 then 186 else if i=59 then 32 else if i=60 then 33 else if i=62 then 31
  else if i=64 then 187 else if i=65 then 184 else ⟨i.val+188,by have h:=i.isLt;omega⟩
noncomputable def buildLiteralCache := RecoveryFocus.machine literalPorts LiteralCacheTransaction.machine

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
