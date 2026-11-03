import Proof.Supplier.RowTupleEnumerationReady
import Proof.CaseAnalysis.RowsModeTuplePolynomial

/-! An actual cold binary subset enumeration is consumed by the ordinary
raw monomial writer. The initial bank contains only the four numeric fields;
its output is appended in the enumerator's positional occurrence order. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeElementary
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extraHeads (out : List Bool) : Fin 4→Nat:=![0,0,0,out.length]
def extraTapes (out : List Bool) : Fin 4→List Bool:=![[],[],[],out]
def heads (out : List Bool) : Fin 45→Nat:=Fin.addCases (m:=41) (n:=4) (motive:=fun _=>Nat) (fun _=>0) (extraHeads out)
def input (w k M : Nat) (out : List Bool) : Fin 45→List Bool:=
  Fin.addCases (m:=41) (n:=4) (motive:=fun _=>List Bool) (RowTupleEnumerationReady.input w k M) (extraTapes out)
def slots : Fin 7→Fin 45:=![17,41,2,42,43,44,12]
noncomputable def first : Σ s,Machine 45 s:=⟨_,TapeEmbedding.machine 4 RowTupleEnumerationReady.machine⟩
noncomputable def last : Σ s,Machine 45 s:=⟨_,RecoveryFocus.machine slots CloseoutRowsModeTuplePolynomial.machine⟩
noncomputable def machine:=Composition.machine first.2 last.2

end NearCubicWires.RepairOrdinary.CloseoutRowsModeElementary
