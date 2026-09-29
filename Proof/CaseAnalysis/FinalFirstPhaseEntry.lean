import Proof.CaseAnalysis.FinalWordEngines

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10FirstPhaseEntry

open NearCubicWires.ExtDecompositionBatch RecoveryRootRound

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/- The selected v3 first entry: two copies and two fixed zero-count words.
   Original width218 and nine fresh cells come from AdmittedEntry.run.
   The paid run keeps its actual installed output and every off-map cell. -/

noncomputable def localMachine :=
  Composition.machine
    (RecoveryFocus.machine (![0,1,2,3] : Fin 4 → Fin 10) ClockUnarySum.machine)
    (Composition.machine
      (RecoveryFocus.machine (![0,1,4,5] : Fin 4 → Fin 10) ClockUnarySum.machine)
      (Composition.machine
        (RecoveryFocus.machine (![6,7] : Fin 2 → Fin 10) (HierarchyFixedWord.machine [false]))
        (RecoveryFocus.machine (![8,9] : Fin 2 → Fin 10) (HierarchyFixedWord.machine [false]))))

def firstSlots (L B : Nat) (hL : 301≤L) (hSpace : L+1095<B) : Fin 10 → Fin B :=
  ![⟨218,by omega⟩,⟨L+135,by omega⟩,⟨L+817,by omega⟩,⟨L+136,by omega⟩,
    ⟨L+1095,by omega⟩,⟨L+137,by omega⟩,⟨L+689,by omega⟩,⟨L+124,by omega⟩,
    ⟨L+967,by omega⟩,⟨L+125,by omega⟩]

noncomputable def machine (L B : Nat) (hL : 301≤L) (hSpace : L+1095<B) :=
  RecoveryFocus.machine (firstSlots L B hL hSpace) localMachine

end NearCubicWires.RepairOrdinary.CloseoutFinalC10FirstPhaseEntry
