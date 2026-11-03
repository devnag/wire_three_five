import Proof.Packets.NativePairCapture
import Proof.Packets.ReusableNativeNormalize

/-! An actual resident atom pair is copied, normalized, and retained as a
ready packet. The cache cursor advances while the reusable normalizer's
source and private work are physically cleared. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NativePairNormalize
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open CloseoutRowsRawPairSeek (Pair word)

def heads (pos : Nat) (i : Fin 40) : Nat := Fin.addCases (m:=36) (n:=4) (motive:=fun _=>Nat) ReusableNative.heads (![pos,0,0,0] : Fin 4→Nat) i
def extras (R : Nat) (source : List Bool) : Fin 4→List Bool :=
  ![source,List.replicate R false,List.replicate R false,List.replicate R false]
def result (C R : Nat) (source : List Bool) (raw : List (List Bool)) (i : Fin 40) : List Bool :=
  Fin.addCases (m:=36) (n:=4) (motive:=fun _=>List Bool) (ReusableNative.ready C R raw) (extras R source) i
def captureSlots : Fin 6→Fin 40 := ![37,36,30,38,39,32]
noncomputable def capture := RecoveryFocus.machine captureSlots NativePairCapture.machine
noncomputable def machine := Composition.machine capture (TapeEmbedding.machine 4 ReusableNative.normalize)

end PCJ9eff70d512234a4c_Fixed.Materializer.NativePairNormalize
