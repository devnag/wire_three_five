import Proof.CaseAnalysis.RowsEstimatorSubstitutionAppend
import Proof.CaseAnalysis.RowsEstimatorSubstitutionMonomial

/-! A live raw output extends the reusable ten-tape factor bank. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionOuter
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch CloseoutRowsRawPairSeek
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (pos : ℕ) (out : List Bool) : Fin 11 → ℕ:=
  Fin.addCases (m:=10) (n:=1) (motive:=fun _=>ℕ) (SubstitutionFactor.heads pos) (fun _=>out.length)
def data (C : ℕ) (source cache acc out : List Bool) : Fin 11 → List Bool:=
  Fin.addCases (m:=10) (n:=1) (motive:=fun _=>List Bool) (SubstitutionFactor.data C source cache [] acc []) (fun _=>out)
def accSlots : Fin 2 → Fin 11:=![3,8]
def appendSlots : Fin 5 → Fin 11:=![5,3,10,7,8]
noncomputable def init:=RecoveryFocus.machine accSlots SubstitutionAppend.unitMachine
noncomputable def inner:=TapeEmbedding.machine 1 SubstitutionMonomial.machine
noncomputable def append:=RecoveryFocus.machine appendSlots SubstitutionAppend.machine
noncomputable def clear:=RecoveryFocus.machine accSlots SubstitutionErase.reset
def advance : Machine 11 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=1)
  rule:=fun q _=>if q=0 then some ⟨1,fun _=>none,fun i=>if i=0 then .right else .stay⟩ else none

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionOuter
