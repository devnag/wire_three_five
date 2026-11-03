import Proof.Packets.PacketsXWindowRawDock
import Proof.Packets.PacketsXWindowPositionalBounds
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Pairing
import Mathlib.Tactic
import Proof.MachineModel.Encoding
import Proof.Packets.NativeNormalized
import Proof.Packets.PacketsXNormalizedFiniteTransport

/-! The actual reflected singleton-cache lookup has exactly the frozen
literal-window meaning, including both polynomial and monomial list order. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.CanonicalFourfoldRowProgram
open CloseoutRowsRawPairSeek (Pair cacheWord)
open NormalizedFiniteTransport WindowNativeOrder

def literalPairs (codes : List Nat) : List Pair := codes.reverse.map (fun c=>([[c]],[]))

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
