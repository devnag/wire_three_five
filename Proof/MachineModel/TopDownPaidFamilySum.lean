import Proof.MachineModel.TopDownPaidFamilyConsumers

/-! A physical reset of the completed raw-family output followed by the
existing mixed-width natural sum. All old tape words are preserved. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace NearCubicWires.P1TopDownPaidFamilySum
open LocalBitMultitape RepairOrdinary RepairRepresentation ExtDecompositionBatch
open RecoveryRootRound RecoveryExecution SignedSortKey
open CloseoutFinalC10RowAnswerWord

def extra (b v N : Nat) : Fin 11→List Bool :=
  ![List.replicate (N*b) true,[],List.replicate b true,List.replicate v true,[],
    List.replicate (2*v+1) false,frame (binary v 0),[],[],
    RepairSource.VerifierDecoding.CompareMachine.word N,[]]
def readSlots {m : Nat} (raw : Fin m) : Fin 3→Fin (m+11) :=
  ![raw.castAdd 11,(0 : Fin 11).natAdd m,(1 : Fin 11).natAdd m]
def sumSlots {m : Nat} (raw : Fin m) : Fin 10→Fin (m+11) :=
  ![raw.castAdd 11,(2 : Fin 11).natAdd m,(3 : Fin 11).natAdd m,(4 : Fin 11).natAdd m,
    (5 : Fin 11).natAdd m,(6 : Fin 11).natAdd m,(7 : Fin 11).natAdd m,
    (8 : Fin 11).natAdd m,(9 : Fin 11).natAdd m,(10 : Fin 11).natAdd m]

noncomputable def first {m : Nat} (raw : Fin m) := RecoveryFocus.machine (readSlots raw) CompetitorRecordRewind.machine
noncomputable def last {m : Nat} (raw : Fin m) := RecoveryFocus.machine (sumSlots raw) sumMachine
noncomputable def machine {m : Nat} (raw : Fin m) := Composition.machine (first raw) (last raw)
def budget (b v N : Nat) := 2*(N*b)+2+1+rowAnswerFuel v N


noncomputable def rewound {m : Nat} (raw : Fin m) (A : Fin m→List Bool) (b v : Nat) (xs : List Nat) :=
  install (readSlots raw) (Fin.addCases A (extra b v xs.length))
    (![CompetitorCountFold.raw b xs,List.replicate (xs.length*b) true,
      List.replicate (xs.length*b) false] : Fin 3→List Bool)
noncomputable def rewoundHeads {m : Nat} (raw : Fin m) (H : Fin m→Nat) :=
  dockH (readSlots raw) (Fin.addCases H (fun _ : Fin 11=>0)) (fun _=>0)
noncomputable def final {m : Nat} (raw : Fin m) (A : Fin m→List Bool) (b v : Nat) (xs : List Nat) (Z : Fin 10→List Bool) :=
  install (sumSlots raw) (rewound raw A b v xs) Z
noncomputable def finalHeads {m : Nat} (raw : Fin m) (H : Fin m→Nat) :=
  dockH (sumSlots raw) (rewoundHeads raw H) (fun _=>0)

end NearCubicWires.P1TopDownPaidFamilySum
