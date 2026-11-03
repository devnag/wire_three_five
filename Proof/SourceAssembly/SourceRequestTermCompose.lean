import Proof.SourceAssembly.SourceRequestTermBridge

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false

namespace NearCubicWires.SourceRequest.TermCompose
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open NearCubicWires.SourceRequest.TermSeg

def aS (i : Fin 191) : Fin 1081 := ⟨i.val, by omega⟩
def bS (i : Fin 192) : Fin 1081 :=
  if i.val = 0 then ⟨189, by omega⟩ else if i.val = 189 then ⟨191, by omega⟩ else ⟨191 + i.val, by omega⟩
def cS (i : Fin 155) : Fin 1081 :=
  if i.val = 0 then ⟨381, by omega⟩ else if i.val = 151 then ⟨383, by omega⟩ else ⟨383 + i.val, by omega⟩
def dS (i : Fin 543) : Fin 1081 :=
  if i.val = 0 then ⟨422, by omega⟩ else if i.val = 534 then ⟨538, by omega⟩ else ⟨538 + i.val, by omega⟩



noncomputable def machine :=
  Composition.machine
    (Composition.machine
      (Composition.machine (RecoveryFocus.machine aS machineA) (RecoveryFocus.machine bS TermSegB.machineB))
      (RecoveryFocus.machine cS TermSegC.machine))
    (RecoveryFocus.machine dS TermCoef.machine)

/-- The words the reader reaches (total forms; equal to the indexed ones under the bridge's bounds). -/
noncomputable def cWord (bits : List Bool) (j : Nat) : List Bool :=
  SignedSortKey.binary bits.length ((sums bits).getD j 0)
noncomputable def tWord (bits : List Bool) (j i : Nat) : List Bool :=
  SignedSortKey.binary (cWord bits j).length ((TermSegB.terms (cWord bits j)).getD i 0)

noncomputable def readerCost (bits : List Bool) (j i cwid cw : Nat) : Nat :=
  costA bits.length j + 1 + TermSegB.costB (cWord bits j).length i + 1 +
    TermSegC.cost (tWord bits j i).length cwid + 1 +
    TermCoef.cost (CloseoutWitness.PairHeader.codeWord (tWord bits j i) 0) cw

end NearCubicWires.SourceRequest.TermCompose

