import Proof.Packets.NativePairNormalize
import Proof.Packets.NativeLiteralCode
import Proof.Packets.PacketBankWrite

/-! The sparse literal code is read from the actually generated singleton
record and selects the resident dense packet-bank entry. No decoded index
or normalized result is supplied to the machine. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NativeAtomStore
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

def heads (pairPos codePos indexPos : Nat) (i : Fin 44) : Nat :=
  Fin.addCases (m:=40) (n:=4) (motive:=fun _=>Nat) (NativePairNormalize.heads pairPos) (![codePos,indexPos,0,0] : Fin 4→Nat) i
def data (C R : Nat) (pairs codes bank : List Bool) (raw : List (List Bool)) (index : Nat) (i : Fin 44) : List Bool :=
  Fin.addCases (m:=40) (n:=4) (motive:=fun _=>List Bool) (NativePairNormalize.result C R pairs raw)
    (![codes,ZeroPadding.pad R (CompareMachine.word index),bank,List.replicate R false] : Fin 4→List Bool) i
def parseSlots : Fin 2→Fin 44 := ![40,41]
def storeSlots : Fin 6→Fin 44 := ![33,42,26,27,41,43]
noncomputable def parse := RecoveryFocus.machine parseSlots NativeLiteralCode.readyMachine
noncomputable def store := RecoveryFocus.machine storeSlots PacketBank.storeSelectedZero

end PCJ9eff70d512234a4c_Fixed.Materializer.NativeAtomStore
