import Proof.Packets.DenseAtomLoop
import Proof.Packets.PhysicalCounterCopy
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Pairing
import Mathlib.Tactic
import Proof.MachineModel.Encoding

/-! Reusable atom-table pass from the actual resident atom/code caches and
count master. It physically initializes the descending occurrence index,
executes every dense write, and returns both cache cursors to zero. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.DenseAtomMaterialize
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsRawPairSeek (Pair cacheWord)
open PacketVector (Packet)
open DenseAtomProgram (table codes codePrefix)

def H (pos : Nat) (i : Fin 46) : Nat :=
  Fin.addCases (m:=45) (n:=1) (motive:=fun _=>Nat) (NativeIndexedAtom.heads 0 pos) (fun _=>1) i
def A (C R tag : Nat) (cs : List Pair) (ps : List Packet) (index : Nat) (i : Fin 46) : List Bool :=
  Fin.addCases (m:=45) (n:=1) (motive:=fun _=>List Bool)
    (NativeIndexedAtom.data C R (cacheWord cs) (codes tag cs) (PacketVector.bank R ps) index)
    (fun _=>ZeroPadding.pad R (CompareMachine.word cs.length)) i

def indexSlot : Fin 1→Fin 46 := ![44]
def backSlots : Fin 2→Fin 46 := ![33,40]
noncomputable def copy := PhysicalCounterCopy.machine (t:=46) 33 45 44
noncomputable def decrement := RecoveryFocus.machine indexSlot VectorCounter.decrement
noncomputable def back := RecoveryFocus.machine backSlots Completion.PhysicalBoundedLeftRewind.machine
noncomputable def machine := Composition.machine copy
  (Composition.machine decrement (Composition.machine DenseAtomProgram.machine back))


end PCJ9eff70d512234a4c_Fixed.Materializer.DenseAtomMaterialize
