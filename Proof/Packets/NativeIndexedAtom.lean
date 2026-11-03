import Proof.Packets.NativeAtomTransaction
import Proof.Packets.NativePairSeekReady
import Proof.Packets.DescendingWindowCounters
import Proof.Packets.PhysicalBoundedLeftRewind

/-! Actual descending atom iteration over the unchanged ascending native
pair cache: seek by the physical occurrence counter, materialize/store the
atom at its parsed sparse code, rewind the cache, then decrement occurrence.
The dense-bank and cache words remain on their original tapes. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NativeIndexedAtom
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsRawPairSeek (Pair word cacheWord)

def heads (pairPos codePos : Nat) (i : Fin 45) : Nat :=
  Fin.addCases (m:=44) (n:=1) (motive:=fun _=>Nat) (NativeAtomStore.heads pairPos codePos 0) (fun _=>1) i
def data (C R : Nat) (pairs codes bank : List Bool) (index : Nat) (i : Fin 45) : List Bool :=
  Fin.addCases (m:=44) (n:=1) (motive:=fun _=>List Bool)
    (NativeAtomStore.data C R pairs codes bank [] 0)
    (fun _=>ZeroPadding.pad R (CompareMachine.word index)) i

def seekSlots : Fin 2→Fin 45 := ![44,36]
def backSlots : Fin 2→Fin 45 := ![33,36]
def indexSlot : Fin 1→Fin 45 := ![44]
noncomputable def seek := RecoveryFocus.machine seekSlots NativePairSeekReady.machine
noncomputable def back := RecoveryFocus.machine backSlots Completion.PhysicalBoundedLeftRewind.machine
noncomputable def decrement := RecoveryFocus.machine indexSlot VectorCounter.decrement
noncomputable def machine := Composition.machine seek
  (Composition.machine (TapeEmbedding.machine 1 NativeAtomStore.transaction)
    (Composition.machine back decrement))

end PCJ9eff70d512234a4c_Fixed.Materializer.NativeIndexedAtom
