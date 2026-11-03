import Proof.Packets.PacketsXWalkTranscriptRewindJoined
import Proof.Packets.VectorCounter

/-! The initial walk arena is built by physical fanout from fifteen retained
palette words and empty destination tapes. Its population counter is incremented
for the forthcoming transcript allocation. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkLiteralCold
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
open VectorBottomUp CloseoutRowsModeCache
noncomputable section

def select (i : Fin 299) : Option (Fin 15) :=
  if i=31 then some 2 else if i=297 then some 14 else none

def boot := Composition.machine (NativeFanout.machine select) paletteRaise

def increment := RecoveryFocus.machine (fun _ : Fin 1=>(312 : Fin 316)) VectorCounter.increment

def paletteMachine := Composition.machine boot increment

end
end Theorem25Completion.WalkLiteralCold
