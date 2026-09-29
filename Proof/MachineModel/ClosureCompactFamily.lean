import Proof.MachineModel.ClosureCompactNativeInitialize

/-! One fixed ordinary program computes the compact metadata, initializes
the bank, then emits the full raw-index family. The source cache, runtime
dimension words, raw family and its loop count remain explicit inputs.
No retained metadata premise survives this composition. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.CompactColdFamily
open LocalBitMultitape RepairOrdinary RepairRepresentation ExtIncidence ExtDecompositionBatch
open RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding

def loopSlots (i : Fin 278) : Fin 440 := i.castAdd 162
noncomputable def last := RecoveryFocus.machine loopSlots P1CompactNativeFamily.machine
noncomputable def machine := Composition.machine CompactNativeInitialize.machine last

variable {l r : Nat} (gs : List (ExactThresholdGate (l+r))) [P1Radix gs] (Q w : Nat)
  (ps : List (List (List (Fin gs.length)))) (out pre tail : List Bool)

def source := pre++ps.flatMap P1CompactNativeFamily.rawWord++tail
noncomputable def ambient := CompactNativeInitialize.output gs Q w ps.length (source gs ps pre tail) out
def ambientH := CompactNativeInitialize.heads pre.length out
noncomputable def H : Fin 277 → Nat := ambientH out pre ∘ CompactNativeInitialize.native
noncomputable def A : Fin 277 → List Bool := ambient gs Q w ps out pre tail ∘ CompactNativeInitialize.native
def budget := CompactNativeInitialize.budget gs Q w+1+P1CompactNativeFamily.budget gs Q w ps
noncomputable def finalConfig := RepeatMachine.cfg 3
  (P1CompactNativeFamily.entry gs Q w ps pre tail (H out pre) (A gs Q w ps out pre tail) ps.length
    (out++ps.flatMap (P1CompactNativeFamily.emit gs Q w))) ps.length 1
noncomputable def finalHeads := dockH loopSlots (ambientH out pre) (finalConfig gs Q w ps out pre tail).heads
noncomputable def finalTapes := install loopSlots (ambient gs Q w ps out pre tail)
  (finalConfig gs Q w ps out pre tail).tapes

end NearCubicWires.P1Closure.CompactColdFamily
