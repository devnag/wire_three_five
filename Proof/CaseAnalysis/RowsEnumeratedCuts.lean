import Proof.Supplier.RowTupleCutList

/-! The actual binary subset producer hands its rewound tuple stream to the
complete signed-cut consumer. One coefficient is retained for the whole
degree; coordinates and threshold are followed by that coefficient. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEnumeratedCuts
open LocalBitMultitape RepairRepresentation RecoveryExecution
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def enumSlots : Fin 41 → Fin 89 :=
  ![49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,44,66,67,68,
    69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88]
def rowSlots (i : Fin 49) : Fin 89 := i.castAdd 40
noncomputable def first := RecoveryFocus.machine enumSlots RowTupleEnumerationReady.machine
noncomputable def last := RecoveryFocus.machine rowSlots RowTupleCutList.machine
noncomputable def machine := Composition.machine first last

def core {s n : ℕ} (q : Fin s) (gs : List (ExactThresholdGate n))
    (p F w k : ℕ) (rows : List (List Bool)) (tuple : List Bool)
    (pos : ℕ) (out : List Bool) (bound : ℕ) (coefficient : ℤ) : Configuration 49 s :=
  ⟨q,Fin.addCases (m:=48) (n:=1) (motive:=fun _ => ℕ)
      (RowTupleCursorLayout.heads pos out) (fun _ : Fin 1 => 0),
    Fin.addCases (m:=48) (n:=1) (motive:=fun _ => List Bool)
      (fun i => ZeroPadding.pad (RowTupleCursorBody.padding F i)
        (RowTupleCursorLayout.data gs 0 p F w rows.length k rows tuple out bound [] i))
      (fun _ : Fin 1 => frame (MatrixScoreBatch.signMagnitude p coefficient))⟩

noncomputable def input {s n : ℕ} (q : Fin s) (gs : List (ExactThresholdGate n))
    (p F w k : ℕ) (rows : List (List Bool)) (out : List Bool) (coefficient : ℤ) :=
  TapeEmbedding.config (fun _ : Fin 40 => 0)
    (RowTupleEnumeratedEquations.extra w k rows.length)
    (core q gs p F w k rows [] 0 out 0 coefficient)

end NearCubicWires.RepairOrdinary.CloseoutRowsEnumeratedCuts
