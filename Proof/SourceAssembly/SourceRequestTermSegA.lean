import Proof.SourceAssembly.SourceRequestTermReader
import Proof.CaseAnalysis.RowsGateHeader
import Proof.CaseAnalysis.CloseoutWitnessTraversalCold
import Proof.CaseAnalysis.RowsTupleSeekFrame
import Proof.Foundations.OrdinaryRewind
import Proof.CaseAnalysis.RowsTouchingFrameSeek
import Proof.Circuits.DecompositionCountPosition

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceRequest.TermSeg
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound

/-! ## Generic seams -/

/-- The framed-word copy, rewound: `[frame w, [], []] ↦ [frame w, frame w, log]`, heads `0`. -/
noncomputable def copyMachine := Rewind.machine (CloseoutRowsTupleSeek.frameMachine true)

/-! ## Segment A, part 1: layout on `Fin 188` -/

/-- `0` witness; `1 + i` the header parser (148); `149` log; `150 + i` the rewound traversal (37); `187` log. -/
def gS (i : Fin 148) : Fin 188 := ⟨1 + i.val, by omega⟩
def tS (i : Fin 37) : Fin 188 := ⟨150 + i.val, by omega⟩
def c1S : Fin 3 → Fin 188 := ![0, 2, 149]
def c2S : Fin 3 → Fin 188 := ![119, 150, 187]


noncomputable def machine :=
  Composition.machine
    (Composition.machine
      (Composition.machine (RecoveryFocus.machine c1S copyMachine)
        (RecoveryFocus.machine gS CloseoutRowsGateHeader.machine))
      (RecoveryFocus.machine c2S copyMachine))
    (RecoveryFocus.machine tS (Rewind.machine CloseoutWitness.TraversalCold.machine))

def cost (n : Nat) : Nat :=
  (((2 * (2 * n + 1) + 2) + 1 + 27000 * (n + 1) ^ 2) + 1 + (2 * (2 * n + 1) + 2)) + 1 +
    (2 * (1048576 * (n + 1) ^ 3) + 2)

/-- The sum codes of the witness family, in order (`tree` = the canonical balanced-list view). -/
noncomputable def sums (bits : List Bool) : List Nat :=
  (PCPPNativeCanonicalTree.tree (RadixSemantics.value (CloseoutWitness.BoundedFields.family bits))).atoms

/-! ## Segment A, part 2: the `j`-th frame of a framed stream (`[stream, word j, out]`, rewound) -/


def sk01 : Fin 2 → Fin 3 := ![0, 1]
def sk02 : Fin 2 → Fin 3 := ![0, 2]

noncomputable def seekCore :=
  Composition.machine (DecompositionCountPosition.move ![HeadMove.stay, HeadMove.right, HeadMove.stay])
    (Composition.machine (RecoveryFocus.machine sk01 CloseoutRowsTouching.FrameSeek.machine)
      (RecoveryFocus.machine sk02 (CloseoutRowsTupleSeek.frameMachine true)))

def seekCost (w j b : Nat) : Nat := 1 + 1 + (CloseoutRowsTouching.FrameSeek.budget w j + 1 + (2 * b + 1))

/-! ## Segment A: the `j`-th sum code of the witness family, on `Fin 191` -/

def coreS (i : Fin 188) : Fin 191 := ⟨i.val, by omega⟩
def seekS : Fin 4 → Fin 191 := ![177, 188, 189, 190]

noncomputable def machineA :=
  Composition.machine (RecoveryFocus.machine coreS machine) (RecoveryFocus.machine seekS (Rewind.machine seekCore))

def costA (n j : Nat) : Nat := cost n + 1 + (2 * seekCost n j n + 2)

end NearCubicWires.SourceRequest.TermSeg


