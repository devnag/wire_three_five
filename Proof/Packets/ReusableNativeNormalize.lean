import Proof.Packets.ReusableNativeCleanup
import Proof.Packets.NativeNormalized
import Proof.Packets.NormalizedAdditionData
import Proof.Packets.NormalizerCold

/-! Reusable executed native normalization. After actual parsing and parity
normalization the packet is copied to its ready right operand, while the
native source and all private work are physically cleared to retained R-cell
backing. Only the two actual width masters survive beside the result. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ReusableNative
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

def readyData (C R : Nat) (raw : List (List Bool)) (i : Fin 32) : List Bool :=
  if i=13 then ZeroPadding.pad R (UnaryTemplate.tape (2*C+3))
  else if i=24 then ZeroPadding.pad R (UnaryTemplate.tape C)
  else if i=26 then ZeroPadding.pad R raw.flatten
  else if i=27 then ZeroPadding.pad R (CompareMachine.word raw.length)
  else List.replicate R false
def ready (C R : Nat) (raw : List (List Bool)) := bank R (readyData C R raw)
noncomputable def normalize := machine NativeNormalized.machine

end PCJ9eff70d512234a4c_Fixed.Materializer.ReusableNative
