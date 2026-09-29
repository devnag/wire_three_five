import Proof.MachineModel.Layout

/-! Fixed tape-order loading from a retained physical stream. Every frame is
read by the existing raw-field loader; targets reuse resident false backing. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDownPaidReloadStream
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RecoveryRootRound RecoveryExecution

def slots {t : Nat} (i : Fin t) : Fin 3→Fin (t+2) := ![(0 : Fin 2).natAdd t,i.castAdd 2,(1 : Fin 2).natAdd t]
noncomputable def field {t : Nat} (i : Fin t) := RecoveryFocus.machine (slots i) CloseoutRowsRawLoad.machine

def states {t : Nat} : List (Fin t)→Nat
  | []=>1
  | _::xs=>4+states xs
def stop (t : Nat) : Machine (t+2) 1 where
  descriptionBits:=0
  start:=0
  halted:=fun _=>true
  rule:=fun _ _=>none
noncomputable def machine {t : Nat} : (xs : List (Fin t))→Machine (t+2) (states xs)
  | []=>stop t
  | i::xs=>Composition.machine (field i) (machine xs)
def stream {t : Nat} (words : Fin t→List Bool) (xs : List (Fin t)) := xs.flatMap (fun i=>frame (words i))

end NearCubicWires.P1TopDownPaidReloadStream
