import Proof.SourceAssembly.SourceRequestTermSegA
import Proof.CaseAnalysis.WitnessPairHeader

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceRequest.TermSegB
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open NearCubicWires.SourceRequest.TermSeg

/-! ## Segment B core: layout on `Fin 189` -/

/-- `0` sum code; `1 + i` the pair parser (149); `150` log; `151 + i` the rewound traversal (37); `188` log. -/
def pS (i : Fin 149) : Fin 189 := ⟨1 + i.val, by omega⟩
def tS (i : Fin 37) : Fin 189 := ⟨151 + i.val, by omega⟩
def c1S : Fin 3 → Fin 189 := ![0, 2, 150]
def c2S : Fin 3 → Fin 189 := ![79, 151, 188]


noncomputable def machine :=
  Composition.machine
    (Composition.machine
      (Composition.machine (RecoveryFocus.machine c1S copyMachine)
        (RecoveryFocus.machine pS CloseoutWitness.PairHeader.machine))
      (RecoveryFocus.machine c2S copyMachine))
    (RecoveryFocus.machine tS (Rewind.machine CloseoutWitness.TraversalCold.machine))

def cost (n : Nat) : Nat :=
  (((2 * (2 * n + 1) + 2) + 1 + 28000 * (n + 1) ^ 2) + 1 + (2 * (2 * n + 1) + 2)) + 1 +
    (2 * (1048576 * (n + 1) ^ 3) + 2)

/-- The terms-list field of a sum code. -/
noncomputable def termsCode (c : List Bool) : List Bool := CloseoutWitness.PairHeader.codeWord c 1

/-- The term codes of a sum code, in order. -/
noncomputable def terms (c : List Bool) : List Nat :=
  (PCPPNativeCanonicalTree.tree (RadixSemantics.value (termsCode c))).atoms

/-! ## Segment B: the `i`-th term code of a sum code, on `Fin 192` -/

def coreS (i : Fin 189) : Fin 192 := ⟨i.val, by omega⟩
def seekS : Fin 4 → Fin 192 := ![178, 189, 190, 191]

noncomputable def machineB :=
  Composition.machine (RecoveryFocus.machine coreS machine) (RecoveryFocus.machine seekS (Rewind.machine seekCore))

def costB (n i : Nat) : Nat := cost n + 1 + (2 * seekCost n i n + 2)

end NearCubicWires.SourceRequest.TermSegB

