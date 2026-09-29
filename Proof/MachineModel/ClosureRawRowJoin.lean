import Proof.MachineModel.ClosureRowPayloadReusable

/-! Consume a real row-printing Step, then physically produce the raw scalar
required by the external-row loop and clear the bounded record buffer.
The program is fixed before the row, its coefficient, width, or answer.
Only the row producer's original input words and paid blank workspace enter.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.P1Closure.RawRowJoin
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RecoveryRootRound
open CloseoutRowsEstimatorCoefficients SignedSortKey

def bank {t : Nat} (A : Fin t → List Bool) (R B : Nat) (out : List Bool) :
    Fin (t+1+2) → List Bool :=
  Fin.addCases (Fin.addCases A (fun _ : Fin 1 => List.replicate R false))
    (![out,List.replicate B true] : Fin 2 → List Bool)
def heads (t : Nat) (out : List Bool) : Fin (t+1+2) → Nat :=
  Fin.addCases (Fin.addCases (fun _ : Fin t => 0) (fun _ : Fin 1 => 0))
    (![out.length,0] : Fin 2 → Nat)
def slots {t : Nat} (port : Fin t) : Fin 4 → Fin (t+1+2) :=
  ![(port.castAdd 1).castAdd 2,(0 : Fin 2).natAdd (t+1),
    ((0 : Fin 1).natAdd t).castAdd 2,(1 : Fin 2).natAdd (t+1)]

noncomputable def first {t s : Nat} (p : Machine t s) :=
  TapeEmbedding.machine 2 (MaskedReset.machine p (fun _ => true))
noncomputable def last {t : Nat} (port : Fin t) :=
  RecoveryFocus.machine (slots port) RowPayloadReusable.machine
noncomputable def machine {t s : Nat} (p : Machine t s) (port : Fin t) :=
  Composition.machine (first p) (last port)
def budget (fuel b B : Nat) := 2*fuel+2+1+RowPayloadReusable.budget b B

end NearCubicWires.P1Closure.RawRowJoin
