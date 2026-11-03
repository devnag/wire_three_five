import Proof.CaseAnalysis.RowsEstimatorFramed
import Proof.Hierarchy.CompetitorRecordRewind

/-! Entry from the actual native bank's append cursor. The same retained
C driver pays the rewind before the cold cut/header/frame construction. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Cold
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 3→Fin 70:=![52,68,69]
def input (row : EquationRow.Input) (C : ℕ) : Fin 70→List Bool:=
  fun i=>Fin.addCases (m:=68) (n:=2) (motive:=fun _=>List Bool)
    (Framed.input row) ![List.replicate C true,[]] i
def heads (row : EquationRow.Input) (i : Fin 70):=if i=52 then (Header.stream row).length else 0
noncomputable def first:=RecoveryFocus.machine slots CompetitorRecordRewind.machine
noncomputable def last:=TapeEmbedding.machine 2 Framed.machine
noncomputable def machine:=Composition.machine first last
def budget (row : EquationRow.Input) (C : ℕ):=(2*C+2)+1+Framed.budget row

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Cold
