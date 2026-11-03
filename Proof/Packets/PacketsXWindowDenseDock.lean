import Proof.Packets.PacketsXDenseAtomBoundary
import Proof.Packets.WindowProviderPorts

/-! The actual dense literal-table machine in the fixed provider arena.
It changes only the dense bank, retaining both physical source caches. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open CloseoutRowsRawPairSeek (Pair)
open Theorem25Completion.CycleBounds Theorem25Completion.CycleDenseAtomCost

attribute [local irreducible] DenseAtomBoundary.machine DenseAtomBoundary.cold

def densePorts : Fin 46→Fin 256 := Fin.addCases (m:=36) (n:=10) nativePorts
  (![125,130,131,124,186,126,140,127,128,129] : Fin 10→Fin 256)
noncomputable def buildDense := RecoveryFocus.machine densePorts DenseAtomBoundary.machine

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
